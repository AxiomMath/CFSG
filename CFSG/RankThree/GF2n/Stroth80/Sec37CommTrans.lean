module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem mk_mem_bar_iff' [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (y : M) : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S ↔ (y : G) ∈ S := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have h1 : s⁻¹ * y ∈ Q.subgroupOf M := QuotientGroup.eq.mp hsy
    have h2 : (s : G)⁻¹ * y ∈ S := hQS h1
    have e : (y : G) = s * ((s : G)⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem hs h2
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

omit [Finite G] in
theorem mk_mem_conj_bar_iff' [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (m y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ↔
      (y : G) ∈ conjSubgroup (m : G) S := by
  rw [mem_conjSubgroup, mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff' hQS]
  rfl

theorem conj_LB_eq_of_bar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x y : M}
    (h : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) x) (bar M Q (LB M Q B)) =
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) y) (bar M Q (LB M Q B))) :
    conjSubgroup (x : G) (LB M Q B) = conjSubgroup (y : G) (LB M Q B) := by
  have hQL : Q ≤ LB M Q B := le_sup_left
  have key : ∀ {a b : M},
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) a) (bar M Q (LB M Q B)) =
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) b) (bar M Q (LB M Q B)) →
      conjSubgroup (a : G) (LB M Q B) ≤ conjSubgroup (b : G) (LB M Q B) := by
    intro a b hab z hz
    have hzM : z ∈ M := conj_le_M hc.LB_le_M a.2 hz
    have h1 := (mk_mem_conj_bar_iff' hQL a ⟨z, hzM⟩).mpr hz
    rw [hab] at h1
    exact (mk_mem_conj_bar_iff' hQL b ⟨z, hzM⟩).mp h1
  exact le_antisymm (key h) (key h.symm)

theorem conj_B_le_of_conj_LB_eq (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (h : conjSubgroup x (LB M Q B) = conjSubgroup y (LB M Q B)) :
    conjSubgroup x B ≤ conjSubgroup y B ⊔ Z := by
  have hyx : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hy) hx
  have h1 : conjSubgroup (y⁻¹ * x) (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_mul, h, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have h3 := (hc.mem_normalizer_LB_iff' hw hn hno hyx).mp (conjSubgroup_eq_self_iff.mp h1)
  have h4 : conjSubgroup (y⁻¹ * x) (B ⊔ Z) = B ⊔ Z := conjSubgroup_eq_self_iff.mpr h3
  have h5 : conjSubgroup x (B ⊔ Z) = conjSubgroup y (B ⊔ Z) := by
    calc conjSubgroup x (B ⊔ Z) = conjSubgroup (y * (y⁻¹ * x)) (B ⊔ Z) := by
          rw [mul_inv_cancel_left]
      _ = conjSubgroup y (B ⊔ Z) := by rw [conjSubgroup_mul, h4]
  calc conjSubgroup x B ≤ conjSubgroup x (B ⊔ Z) := Subgroup.map_mono le_sup_left
    _ = conjSubgroup y B ⊔ Z := by rw [h5, conjSubgroup_sup', hc.conj_Z_eq hy]

theorem comm_of_le_sup_Z (hc : Ctx M Q Z B) {C C' D D' : Subgroup G} (hD : D ≤ Q)
    (hD' : D' ≤ Q) (hDD' : ∀ u ∈ D, ∀ u' ∈ D', u * u' = u' * u)
    (hC : C ≤ D ⊔ Z) (hC' : C' ≤ D' ⊔ Z) : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
  have hcen : ∀ {z w : G}, z ∈ Z → w ∈ Q → w * z = z * w := by
    intro z w hz hw
    have hz' : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
      rw [← cen_eq, ← hc.hyp.hZ]
      exact hz
    exact Subgroup.mem_centralizer_iff.mp hz'.2 w hw
  have hZn : ∀ {E : Subgroup G}, E ≤ Q → E ≤ Subgroup.normalizer (Z : Set G) := fun hE u hu =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hE hu))
  intro x hx y hy
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (hZn hD) (hC hx)
  obtain ⟨u', hu', z', hz', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (hZn hD') (hC' hy)
  have h1 : z * u' = u' * z := (hcen hz (hD' hu')).symm
  have h2 : z' * u = u * z' := (hcen hz' (hD hu)).symm
  have h3 : z * z' = z' * z := hc.Z_comm z hz z' hz'
  have h4 := hDD' u hu u' hu'
  calc u * z * (u' * z') = u * (z * u') * z' := by group
    _ = u * (u' * z) * z' := by rw [h1]
    _ = (u * u') * (z * z') := by group
    _ = (u' * u) * (z' * z) := by rw [h4, h3]
    _ = u' * (u * z') * z := by group
    _ = u' * (z' * u) * z := by rw [h2]
    _ = u' * z' * (u * z) := by group

theorem commuting_of_twoTrans [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (h2 : ConjTwoTransitive (Mbar M Q) (bar M Q (LB M Q B))) {m : G} (hm : m ∈ M)
    (hcomm : ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) : conjSubgroup m B ≤ B ⊔ Z := by
  by_contra hnot
  have corr : ∀ {x y : M},
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) x) (bar M Q (LB M Q B)) =
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) y) (bar M Q (LB M Q B)) →
      conjSubgroup (x : G) B ≤ conjSubgroup (y : G) B ⊔ Z := fun {x y} h =>
    conj_B_le_of_conj_LB_eq hc hw hn hno x.2 y.2 (conj_LB_eq_of_bar hc h)
  have hne : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) 1) (bar M Q (LB M Q B)) ≠
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨m, hm⟩) (bar M Q (LB M Q B)) := by
    intro h
    apply hnot
    have := corr h.symm
    rwa [show ((1 : M) : G) = 1 from rfl, conjSubgroup_one] at this
  have hBQ : ∀ g ∈ M, conjSubgroup g B ≤ Q := fun g hg => (hc.conj_of_mem hg).le
  have hall : ∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ x ∈ conjSubgroup m₁ B, ∀ y ∈ conjSubgroup m₂ B,
      x * y = y * x := by
    intro m₁ hm₁ m₂ hm₂
    by_cases h12 : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨m₁, hm₁⟩)
        (bar M Q (LB M Q B)) =
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨m₂, hm₂⟩) (bar M Q (LB M Q B))
    · have hab : ∀ u ∈ conjSubgroup m₂ B, ∀ u' ∈ conjSubgroup m₂ B, u * u' = u' * u := by
        haveI := (hc.conj_of_mem hm₂).isElemAbelian_B.1
        exact fun u hu u' hu' => setLike_mul_comm hu hu'
      exact comm_of_le_sup_Z hc (hBQ m₂ hm₂) (hBQ m₂ hm₂) hab (corr h12) le_sup_left
    · obtain ⟨gb, hg1, hg2⟩ := h2 _ _ _ _ hne h12
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) gb
      rw [← map_mul, mul_one] at hg1
      rw [← map_mul] at hg2
      have c1 := corr hg1.symm
      have c2 := corr hg2.symm
      have hgm : ((g * ⟨m, hm⟩ : M) : G) = (g : G) * m := rfl
      rw [hgm] at c2
      have hgg : ∀ u ∈ conjSubgroup (g : G) B, ∀ u' ∈ conjSubgroup ((g : G) * m) B,
          u * u' = u' * u := by
        intro u hu u' hu'
        have h1 : (g : G)⁻¹ * u * g ∈ B := mem_conjSubgroup.mp hu
        have h2' : (g : G)⁻¹ * u' * g ∈ conjSubgroup m B := by
          rw [mem_conjSubgroup]
          have := mem_conjSubgroup.mp hu'
          rwa [show ((g : G) * m)⁻¹ * u' * ((g : G) * m) =
            m⁻¹ * ((g : G)⁻¹ * u' * g) * m by group] at this
        have h3 := hcomm _ h2' _ h1
        calc u * u' = (g : G) * (((g : G)⁻¹ * u * g) * ((g : G)⁻¹ * u' * g)) * (g : G)⁻¹ := by
              group
          _ = (g : G) * (((g : G)⁻¹ * u' * g) * ((g : G)⁻¹ * u * g)) * (g : G)⁻¹ := by rw [h3]
          _ = u' * u := by group
      exact comm_of_le_sup_Z hc (hBQ g g.2) (hBQ _ (M.mul_mem g.2 hm)) hgg c1 c2
  apply hc.not_commutative_genB
  set S : Subgroup G := ⨆ (m' : G) (_ : m' ∈ M), conjSubgroup m' B with hS
  have hS1 : ∀ m₁ ∈ M, S ≤ Subgroup.centralizer (conjSubgroup m₁ B : Set G) := fun m₁ hm₁ =>
    iSup₂_le fun m₂ hm₂ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hall m₁ hm₁ m₂ hm₂ x hx y hy
  have hS2 : S ≤ Subgroup.centralizer (S : Set G) :=
    iSup₂_le fun m₁ hm₁ => Subgroup.le_centralizer_iff.mp (hS1 m₁ hm₁)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hS2 hy) x hx

theorem mem_normalizer_of_mk_mem_normalizer' [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M) (y : M)
    (hN : QuotientGroup.mk' (Q.subgroupOf M) y ∈
      Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    (y : G) ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hLM hz⟩ : M) ∈ bar M Q L :=
    (mk_mem_bar_iff' hQL _).mpr hz
  have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  exact (mk_mem_bar_iff' hQL _).mp h2

theorem false_of_meet [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hmeet : ∀ x : Mbar M Q, conjSubgroup x (bar M Q (LB M Q B)) ⊓
      Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) ≠ ⊥) :
    False := by
  have hQL : Q ≤ LB M Q B := le_sup_left
  have h36 : ∀ h ∈ M, ∀ b ∈ B, ∀ c ∈ conjSubgroup h B, b * c = c * b := by
    intro h hh
    refine stroth_3_6 h34 hc hw hn hno hgen hh fun heq => ?_
    obtain ⟨⟨xb, hxb⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (hmeet (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hh⟩))
    obtain ⟨⟨x, hxm⟩, hxe⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (xb : Mbar M Q)
    have hxc := (Subgroup.mem_inf.mp hxb).1
    have hxn := (Subgroup.mem_inf.mp hxb).2
    rw [← hxe] at hxc hxn
    have hx1L : x ∈ conjSubgroup h (LB M Q B) := (mk_mem_conj_bar_iff' hQL ⟨h, hh⟩ ⟨x, hxm⟩).mp hxc
    have hx2L : x ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      mem_normalizer_of_mk_mem_normalizer' hQL hc.LB_le_M ⟨x, hxm⟩ hxn
    have hxQ : x ∈ Q := by
      have : x ∈ conjSubgroup h (LB M Q B) ⊓ Subgroup.normalizer (LB M Q B : Set G) :=
        ⟨hx1L, hx2L⟩
      rwa [heq] at this
    apply hx1
    apply Subtype.ext
    show xb = 1
    rw [← hxe]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (⟨x, hxm⟩ : M)).mpr hxQ
  have hall : ∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ x ∈ conjSubgroup m₁ B, ∀ y ∈ conjSubgroup m₂ B,
      x * y = y * x := by
    intro m₁ hm₁ m₂ hm₂ x hx y hy
    have hb : m₁⁻¹ * x * m₁ ∈ B := mem_conjSubgroup.mp hx
    have hc' : m₁⁻¹ * y * m₁ ∈ conjSubgroup (m₁⁻¹ * m₂) B := by
      rw [mem_conjSubgroup]
      have := mem_conjSubgroup.mp hy
      rwa [show (m₁⁻¹ * m₂)⁻¹ * (m₁⁻¹ * y * m₁) * (m₁⁻¹ * m₂) = m₂⁻¹ * y * m₂ by group]
    have h3 := h36 _ (M.mul_mem (M.inv_mem hm₁) hm₂) _ hb _ hc'
    calc x * y = m₁ * ((m₁⁻¹ * x * m₁) * (m₁⁻¹ * y * m₁)) * m₁⁻¹ := by group
      _ = m₁ * ((m₁⁻¹ * y * m₁) * (m₁⁻¹ * x * m₁)) * m₁⁻¹ := by rw [h3]
      _ = y * x := by group
  apply hc.not_commutative_genB
  set S : Subgroup G := ⨆ (m' : G) (_ : m' ∈ M), conjSubgroup m' B with hS
  have hS1 : ∀ m₁ ∈ M, S ≤ Subgroup.centralizer (conjSubgroup m₁ B : Set G) := fun m₁ hm₁ =>
    iSup₂_le fun m₂ hm₂ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hall m₁ hm₁ m₂ hm₂ x hx y hy
  have hS2 : S ≤ Subgroup.centralizer (S : Set G) :=
    iSup₂_le fun m₁ hm₁ => Subgroup.le_centralizer_iff.mp (hS1 m₁ hm₁)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hS2 hy) x hx

end CFSG.RankThree.GF2n.Stroth80.Tim37
