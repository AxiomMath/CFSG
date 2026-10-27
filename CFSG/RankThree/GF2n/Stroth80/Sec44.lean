module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def ClassicalNonsolvableStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∀ m : ℕ, 2 ≤ m → ¬ Group.IsSolvable ↥(StatedSL m K)) ∧
    (∀ m : ℕ, 1 ≤ m → ¬ Group.IsSolvable ↥(StatedSp m K)) ∧
    (∀ m : ℕ, 2 ≤ m → ¬ Group.IsSolvable ↥(StatedOmega (StatedQuadPlus m K))) ∧
    (∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ¬ Group.IsSolvable ↥(StatedOmega (StatedQuadMinus m K b c)))

section

variable {G : Type} [Group G]

theorem isSolvable_of_naturalRep {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} {R V Z N : Subgroup G} (h : NaturalRep K X R V Z N)
    (hR : Group.IsSolvable ↥R) : Group.IsSolvable ↥X := by
  obtain ⟨φ, hφ, -, -⟩ := h
  rw [← hφ]
  exact solvable_of_surjective φ.rangeRestrict_surjective

theorem not_quotSat_isSLModel_of_solvable (hCL : ClassicalNonsolvableStatement) {S N : Subgroup G}
    {q k : ℕ} (hq4 : 4 ≤ q) (hq2 : ∃ j : ℕ, q = 2 ^ j) (hk : 2 ≤ k)
    (hS : Group.IsSolvable ↥S) : ¬ QuotSat S N (IsSLModel k q) := by
  rintro ⟨hN, K, hF, hFin, hKq, ⟨e⟩⟩
  obtain ⟨j, hj⟩ := hq2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hj)
  haveI : Group.IsSolvable (↥S ⧸ N.subgroupOf S) :=
    solvable_of_surjective (QuotientGroup.mk'_surjective (N.subgroupOf S))
  haveI : Group.IsSolvable ↥(StatedSL k K) :=
    solvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact (hCL K (by rw [hKq]; exact hq4)).1 k hk this

end

theorem not_isSolvable_of_isQuasisimple {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  haveI : Group.IsPerfect X := hq.1
  haveI : Nontrivial X := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable X

@[expose] def ClassicalQuasisimpleStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∀ m : ℕ, 2 ≤ m → CFSG.IsQuasisimple ↥(StatedSL m K)) ∧
    (∀ m : ℕ, 1 ≤ m → CFSG.IsQuasisimple ↥(StatedSp m K)) ∧
    (∀ m : ℕ, 3 ≤ m → CFSG.IsQuasisimple ↥(StatedOmega (StatedQuadPlus m K))) ∧
    (∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      CFSG.IsQuasisimple ↥(StatedOmega (StatedQuadMinus m K b c))) ∧
    Nonempty (↥(StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K))

theorem classicalNonsolvable_of_quasisimple (h : ClassicalQuasisimpleStatement) :
    ClassicalNonsolvableStatement := by
  intro K _ _ _ h4
  obtain ⟨hSL, hSp, hOP, hOM, ⟨e⟩⟩ := h K h4
  refine ⟨fun m hm => not_isSolvable_of_isQuasisimple (hSL m hm),
    fun m hm => not_isSolvable_of_isQuasisimple (hSp m hm), fun m hm hs => ?_,
    fun m b c hm han => not_isSolvable_of_isQuasisimple (hOM m b c hm han)⟩
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · have hm2 : m = 2 := by omega
    subst hm2
    haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) := hs
    haveI : Group.IsSolvable (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) :=
      solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    haveI : Group.IsSolvable ↥(StatedSL 2 K) :=
      solvable_of_solvable_injective (f := MonoidHom.inl ↥(StatedSL 2 K) ↥(StatedSL 2 K))
        (by intro a b h; simpa using congrArg Prod.fst h)
    exact not_isSolvable_of_isQuasisimple (hSL 2 le_rfl) inferInstance
  · exact not_isSolvable_of_isQuasisimple (hOP m h3) hs

section

theorem Ctx.exists_solvable_family {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (A : Subgroup (Mbar M Q)) (hAH : A ≤ bar M Q (H0 M Z))
    (hAN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (A : Set (Mbar M Q)))
    (hodd : Odd (Nat.card A)) (hA : A ≠ ⊥) :
    ∃ t ∈ LB M Q B, t ∉ Q ∧ ∃ 𝓛 : Finset (Subgroup G),
      (∀ L' ∈ 𝓛, (∃ m ∈ M, L' = conjSubgroup m (LB M Q B)) ∧ t ∈ L') ∧ 1 < 𝓛.card ∧
      Group.IsSolvable ↥(⨆ L' ∈ 𝓛, L') ∧ (⨆ L' ∈ 𝓛, L') ≠ LB M Q B := by
  classical
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hc hw hn hno hgen).2.1
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hΛab : IsElemAbelian 2 (bar M Q (LB M Q B)) := hc.isElemAbelian_bar_LB
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hΛcard := hc.card_bar_LB_of_34 h34 hw hn hno hgen
  have hΛ4 := hc.four_le_card_bar_LB h34 hw hn hno hgen
  obtain ⟨Λ₀, hΛ₀le, hΛ₀ne, hD⟩ := exists_ne_bot_centralizer_of_odd hΛab hΛ4 hAN hodd hA
  set D : Subgroup (Mbar M Q) := A ⊓ Subgroup.centralizer (Λ₀ : Set (Mbar M Q)) with hDdef
  have hDA : D ≤ A := inf_le_left
  have hnc : ∃ c ∈ bar M Q (LB M Q B), ∃ d ∈ D, c * d ≠ d * c := by
    by_contra hcon
    push Not at hcon
    refine hD (hc.eq_bot_of_comm_odd h35 D (hDA.trans hAH)
      (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hDA)) ?_)
    intro x hx t ht
    have hmem : (QuotientGroup.mk t : Mbar M Q) ∈ bar M Q (LB M Q B) :=
      Subgroup.mem_map_of_mem _ (show t ∈ (LB M Q B).subgroupOf M from ht)
    exact (hcon _ hmem x hx).symm
  obtain ⟨c, hcΛ, d, hdD, hcd⟩ := hnc
  have hdA : d ∈ A := hDA hdD
  have hΛA : bar M Q (LB M Q B) ⊓ A = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hΛcard, hZ2, ← pow_mul]
    exact (Odd.coprime_two_left hodd).pow_left _
  have hdnorm : d ∉ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) :
      Set (Mbar M Q)) := by
    intro hdN
    apply hcd
    have hcN : c ∈ Subgroup.normalizer (A : Set (Mbar M Q)) := hAN hcΛ
    have h1 : c⁻¹ * d⁻¹ * c * d ∈ bar M Q (LB M Q B) := by
      have h0 : d⁻¹ * c * d ∈ bar M Q (LB M Q B) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) c).mp hcΛ
        simpa [mul_assoc] using this
      have e : c⁻¹ * d⁻¹ * c * d = c⁻¹ * (d⁻¹ * c * d) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcΛ) h0
    have h2 : c⁻¹ * d⁻¹ * c * d ∈ A := by
      have h0 : c⁻¹ * d⁻¹ * c ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) d⁻¹).mp (A.inv_mem hdA)
        simpa [mul_assoc] using this
      exact A.mul_mem h0 hdA
    have h3 : c⁻¹ * d⁻¹ * c * d ∈ bar M Q (LB M Q B) ⊓ A := ⟨h1, h2⟩
    rw [hΛA, Subgroup.mem_bot] at h3
    have h4 : d⁻¹ * c * d = c := by
      have : c⁻¹ * (d⁻¹ * c * d) = 1 := by rw [← h3]; group
      exact (inv_mul_eq_one.mp this).symm
    calc c * d = d * (d⁻¹ * c * d) := by group
      _ = d * c := by rw [h4]
  obtain ⟨tb, htb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hΛ₀ne
  have htbΛ₀ : (tb : Mbar M Q) ∈ Λ₀ := tb.2
  have htbne : (tb : Mbar M Q) ≠ 1 := fun h => htb1 (Subtype.ext h)
  have htbΛ : (tb : Mbar M Q) ∈ bar M Q (LB M Q B) := hΛ₀le tb.2
  obtain ⟨t', ht'LB, ht'mk⟩ := Subgroup.mem_map.mp htbΛ
  have htLB : (t' : G) ∈ LB M Q B := ht'LB
  have htQ : (t' : G) ∉ Q := by
    intro hq
    apply htbne
    rw [← ht'mk]
    exact (QuotientGroup.eq_one_iff t').mpr (Subgroup.mem_subgroupOf.mpr hq)
  obtain ⟨d', hd'H, hd'mk⟩ := Subgroup.mem_map.mp (hAH hdA)
  set L' : Subgroup G := conjSubgroup (d' : G) (LB M Q B) with hL'
  have htL' : (t' : G) ∈ L' := by
    rw [hL', mem_conjSubgroup]
    have hcomm : (d : Mbar M Q)⁻¹ * (tb : Mbar M Q) * d = tb := by
      have := Subgroup.mem_centralizer_iff.mp hdD.2 tb htbΛ₀
      calc (d : Mbar M Q)⁻¹ * (tb : Mbar M Q) * d = d⁻¹ * (d * tb) := by rw [mul_assoc, this]
        _ = tb := by group
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (d'⁻¹ * t' * d') =
        QuotientGroup.mk' (Q.subgroupOf M) t' := by
      rw [map_mul, map_mul, map_inv, hd'mk, ht'mk]
      exact hcomm
    have h2 : t'⁻¹ * (d'⁻¹ * t' * d') ∈ Q.subgroupOf M := QuotientGroup.eq.mp h1.symm
    have e : ((d'⁻¹ * t' * d' : M) : G) = (t' : G) * (((t'⁻¹ * (d'⁻¹ * t' * d')) : M) : G) := by
      simp [mul_assoc]
    rw [show (d' : G)⁻¹ * (t' : G) * (d' : G) = ((d'⁻¹ * t' * d' : M) : G) by simp, e]
    exact (LB M Q B).mul_mem htLB (hQL (Subgroup.mem_subgroupOf.mp h2))
  have hL'ne : L' ≠ LB M Q B := by
    intro hEq
    apply hdnorm
    have hconj : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) d')
        (bar M Q (LB M Q B)) = bar M Q (LB M Q B) := by
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
      rw [mk_mem_conj_bar_iff_sec4 hQL d' y, mk_mem_bar_iff_sec4 hQL y, ← hL', hEq]
    rw [← hd'mk]
    exact conjSubgroup_eq_self_iff.mp hconj
  have hcard : 1 < ({LB M Q B, L'} : Finset (Subgroup G)).card := by
    rw [Finset.card_pair (Ne.symm hL'ne)]
    omega
  have hXeq : (⨆ L'' ∈ ({LB M Q B, L'} : Finset (Subgroup G)), L'') = LB M Q B ⊔ L' := by
    apply le_antisymm
    · refine iSup₂_le fun L'' hL'' => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL''
      rcases hL'' with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · refine sup_le ?_ ?_
      · exact le_iSup₂_of_le (LB M Q B) (by simp) le_rfl
      · exact le_iSup₂_of_le L' (by simp) le_rfl
  set X : Subgroup G := LB M Q B ⊔ L' with hXdef
  have hXM : X ≤ M := sup_le hc.LB_le_M (conj_le_M hc.LB_le_M d'.2)
  have hXsolv : Group.IsSolvable ↥X := by
    let ψ : ↥X →* Mbar M Q := (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hXM)
    have hQ2 : IsPGroup 2 Q := by
      rw [hc.hyp.hQ]
      unfold inSubgroup
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype
    have hker : IsPGroup 2 ψ.ker := by
      have hmem : ∀ x : ψ.ker, ((x : ↥X) : G) ∈ Q := by
        intro x
        have h1 : ψ x = 1 := x.2
        have h2 : QuotientGroup.mk' (Q.subgroupOf M) (Subgroup.inclusion hXM (x : ↥X)) = 1 := h1
        have h3 := (QuotientGroup.eq_one_iff _).mp h2
        exact Subgroup.mem_subgroupOf.mp h3
      let g : ↥ψ.ker →* G := X.subtype.comp ψ.ker.subtype
      let g' : ↥ψ.ker →* ↥Q := g.codRestrict Q hmem
      refine hQ2.of_injective g' ?_
      intro x y hxy
      have h0 := congrArg Subtype.val hxy
      have h1 : ((x : ↥X) : G) = ((y : ↥X) : G) := h0
      exact Subtype.ext (Subtype.ext h1)
    have hrange : ψ.range ≤ bar M Q (LB M Q B) ⊔ A := by
      let P : Subgroup G :=
        ((bar M Q (LB M Q B) ⊔ A).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype
      have hLP : LB M Q B ≤ P := by
        intro l hl
        refine ⟨⟨l, hc.LB_le_M hl⟩, ?_, rfl⟩
        exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _
          (show (⟨l, hc.LB_le_M hl⟩ : ↥M) ∈ (LB M Q B).subgroupOf M from hl))
      have hL'P : L' ≤ P := by
        intro y hy
        have hyM : y ∈ M := conj_le_M hc.LB_le_M d'.2 hy
        refine ⟨⟨y, hyM⟩, ?_, rfl⟩
        have hl : (d' : G)⁻¹ * y * d' ∈ LB M Q B := mem_conjSubgroup.mp hy
        have hl' : QuotientGroup.mk' (Q.subgroupOf M) (d'⁻¹ * ⟨y, hyM⟩ * d') ∈
            bar M Q (LB M Q B) :=
          Subgroup.mem_map_of_mem _ (show (d'⁻¹ * ⟨y, hyM⟩ * d' : ↥M) ∈ (LB M Q B).subgroupOf M
            from hl)
        set lam := QuotientGroup.mk' (Q.subgroupOf M) (d'⁻¹ * ⟨y, hyM⟩ * d') with hlam
        have hy' : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ = d * lam * d⁻¹ := by
          rw [hlam, map_mul, map_mul, map_inv, hd'mk]
          group
        show QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ ∈ bar M Q (LB M Q B) ⊔ A
        rw [hy']
        have hlamN : lam ∈ Subgroup.normalizer (A : Set (Mbar M Q)) := hAN hl'
        have e : d * lam * d⁻¹ = lam * ((lam⁻¹ * d * lam) * d⁻¹) := by group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hl') (Subgroup.mem_sup_right ?_)
        have h0 : lam⁻¹ * d * lam ∈ A := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlamN) d).mp hdA
          simpa [mul_assoc] using this
        exact A.mul_mem h0 (A.inv_mem hdA)
      have hXP : X ≤ P := sup_le hLP hL'P
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hXP x.2
      have : Subgroup.inclusion hXM x = y := Subtype.ext hyx.symm
      show QuotientGroup.mk' (Q.subgroupOf M) (Subgroup.inclusion hXM x) ∈ _
      rw [this]
      exact hy
    haveI : Group.IsSolvable ↥(bar M Q (LB M Q B) ⊔ A) :=
      isSolvable_sup_of_odd (fun a ha b hb =>
        congrArg Subtype.val (hΛab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hAN hodd
    haveI : Group.IsSolvable ↥ψ.range :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hrange)
    exact isSolvable_of_ker_pGroup ψ hker inferInstance
  refine ⟨(t' : G), htLB, htQ, {LB M Q B, L'}, ?_, hcard, ?_, ?_⟩
  · intro L'' hL''
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL''
    rcases hL'' with rfl | rfl
    · exact ⟨⟨1, M.one_mem, (conjSubgroup_one _).symm⟩, htLB⟩
    · exact ⟨⟨d', d'.2, rfl⟩, htL'⟩
  · rw [hXeq]
    exact hXsolv
  · rw [hXeq]
    intro h
    exact hL'ne (Subgroup.eq_of_le_of_card_ge (le_sup_right.trans h.le)
      (card_conjSubgroup _ _).ge)

theorem Ctx.false_of_eq_Rt {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (h310 : Stroth310Statement) (hCL : ClassicalNonsolvableStatement) (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) {t : G} (htLB : t ∈ LB M Q B) (htQ : t ∉ Q) {X : Subgroup G}
    (hXR : X = Rt M (LB M Q B) t) (hXsolv : Group.IsSolvable ↥X) (hXne : X ≠ LB M Q B) :
    False := by
  rcases h310 G M Q Z B hc n hw hn hno hgen t htLB htQ with hRL | ⟨K, hF, hFin, hK, hnat⟩
  · exact hXne (hXR.trans hRL)
  · haveI hRsolv : Group.IsSolvable ↥(Rt M (LB M Q B) t) := by
      rw [← hXR]
      exact hXsolv
    obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    have h4K : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
    obtain ⟨hSL, hSp, hOP, hOM⟩ := hCL K h4K
    rcases hnat with ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, b, cc, hm, han, hn'⟩
    · exact hSL m hm (isSolvable_of_naturalRep hn' hRsolv)
    · exact hSp m hm (isSolvable_of_naturalRep hn' hRsolv)
    · exact hOP m hm (isSolvable_of_naturalRep hn' hRsolv)
    · exact hOM m b cc hm han (isSolvable_of_naturalRep hn' hRsolv)

end

end CFSG.RankThree.GF2n.Stroth80
