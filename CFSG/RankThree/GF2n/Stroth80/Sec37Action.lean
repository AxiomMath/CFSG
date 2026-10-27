module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec34Model

public section

namespace CFSG.RankThree.GF2n.Stroth80.Gl37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem LB_le_H0 (hc : Ctx M Q Z B) : LB M Q B ≤ H0 M Z := fun t ht =>
  ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hc.LB_centralizes_Z ht z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [this]
      _ = t * z := by group⟩

theorem conj_LB_le_H0 (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    conjSubgroup m (LB M Q B) ≤ H0 M Z := by
  rw [← hc.LB_conj hm]
  exact LB_le_H0 (hc.conj_of_mem hm)

theorem conj_mem_Q (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) :
    (∀ x ∈ Q, t * x * t⁻¹ ∈ Q) ∧ ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := by
  refine ⟨fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) x).mp hx,
    fun x hx => ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem htM)) x).mp hx
  simpa using this

theorem exists_conj_not_le_sup (hc : Ctx M Q Z B) : ∃ m ∈ M, ¬ conjSubgroup m B ≤ B ⊔ Z := by
  by_contra hcon
  push Not at hcon
  apply hc.not_commutative_genB
  have hle : (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) ≤ Q ⊓ QB B :=
    iSup₂_le fun m hm => (hcon m hm).trans (sup_comm B Z ▸ hc.ZB_le_inf)
  haveI : IsMulCommutative ↥(Q ⊓ QB B) := hc.inf_QB_elemAbelian.1
  exact fun x hx y hy => setLike_mul_comm (hle hx) (hle hy)

theorem conj_le_of_commute (hc : Ctx M Q Z B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hcomm : ∀ x ∈ conjSubgroup m₂ B, ∀ y ∈ conjSubgroup m₁ B, x * y = y * x) :
    conjSubgroup m₂ B ≤ conjSubgroup m₁ B ⊔ Z := by
  have hm : m₁⁻¹ * m₂ ∈ M := M.mul_mem (M.inv_mem hm₁) hm₂
  have he : conjSubgroup m₁ (conjSubgroup (m₁⁻¹ * m₂) B) = conjSubgroup m₂ B := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  have h1 : conjSubgroup (m₁⁻¹ * m₂) B ≤ B ⊔ Z := by
    refine horth _ hm fun x hx y hy => ?_
    have hx' : m₁ * x * m₁⁻¹ ∈ conjSubgroup m₂ B := by
      rw [← he, mem_conjSubgroup]
      simpa [mul_assoc] using hx
    have hy' : m₁ * y * m₁⁻¹ ∈ conjSubgroup m₁ B := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    have h2 := hcomm _ hx' _ hy'
    have h3 : m₁ * (x * y) * m₁⁻¹ = m₁ * (y * x) * m₁⁻¹ := by
      calc m₁ * (x * y) * m₁⁻¹ = (m₁ * x * m₁⁻¹) * (m₁ * y * m₁⁻¹) := by group
        _ = (m₁ * y * m₁⁻¹) * (m₁ * x * m₁⁻¹) := h2
        _ = m₁ * (y * x) * m₁⁻¹ := by group
    simpa using h3
  have h2 : conjSubgroup m₁ (conjSubgroup (m₁⁻¹ * m₂) B) ≤ conjSubgroup m₁ (B ⊔ Z) :=
    Subgroup.map_mono h1
  rwa [he, conjSubgroup_sup', hc.conj_Z_eq hm₁] at h2

theorem comm_of_mem_inf (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {m : G} (hm : m ∈ M) {t : G} (htL : t ∈ LB M Q B)
    (htN : t ∈ Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G)) (htQ : t ∉ Q) :
    ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x := by
  have hinv : ∀ S : Subgroup G, conjSubgroup m⁻¹ (conjSubgroup m S) = S := fun S => by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hmem : t ∈ conjSubgroup m⁻¹ (LB M Q (conjSubgroup m B)) ⊓
      Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G) := by
    refine ⟨?_, htN⟩
    rw [hc.LB_conj hm, hinv]
    exact htL
  have key := stroth_3_6 h34 (hc.conj_of_mem hm) hw hn (hc.noA2_conj hno hm)
    (hgen.conj_of_mem hm) (M.inv_mem hm) fun heq => htQ (by rw [← heq]; exact hmem)
  intro x hx y hy
  exact key x hx y (by rw [hinv]; exact hy)

theorem comm_of_mem_conj_inf (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {m : G} (hm : m ∈ M) {t : G} (htL : t ∈ conjSubgroup m (LB M Q B))
    (htN : t ∈ Subgroup.normalizer (LB M Q B : Set G)) (htQ : t ∉ Q) :
    ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x := by
  have key := stroth_3_6 h34 hc hw hn hno hgen hm fun heq => htQ (by
    rw [← heq]
    exact ⟨htL, htN⟩)
  exact fun x hx y hy => (key y hy x hx).symm

section Glue

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem img_le_of_le_sup_Z (h : GlobalModelData M Q Z γ M₀) {C D : Subgroup G}
    (hC : C ≤ Q) (hDC : D ≤ C ⊔ Z) : M₀.img D ≤ M₀.img C := by
  have hle : C ⊔ Z ≤ M₀.lift (M₀.img C) := by
    refine sup_le (fun u hu => ⟨hC hu, M₀.pi_mem_img hu (hC hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  rintro _ ⟨x, hxD, -, rfl⟩
  exact (hle (hDC hxD)).2

theorem conj_LB_eq_of_maps_line (hc : Ctx M Q Z B) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {a : G} (haM : a ∈ M)
    {T : M₀.E → M₀.E} (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x))
    (hTb : ∀ s : K, ∃ s' : K, T (s • b) = s' • b) :
    conjSubgroup a (LB M Q B) = LB M Q B := by
  refine hc.conj_LB_eq_of_le_sup_Z haM fun y hy => ?_
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ B, a * u * a⁻¹ = y :=
    ⟨a⁻¹ * y * a, mem_conjSubgroup.mp hy, by group⟩
  have huQ : u ∈ Q := hc.le hu
  have hyQ : a * u * a⁻¹ ∈ Q := (conj_mem_Q hc haM).1 u huQ
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hu huQ)
  obtain ⟨s', hs'⟩ := hTb s
  have hπ : M₀.π (a * u * a⁻¹) ∈ M₀.img B := by
    rw [hT u huQ, hs, hs']
    exact (hB _).mpr ⟨_, rfl⟩
  exact (M₀.mem_img_iff le_sup_right hyQ).mp (M₀.img_mono le_sup_left hπ)

theorem conj_LB_eq_of_fix_line (hc : Ctx M Q Z B) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {a : G} (haM : a ∈ M)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) {μ : K}
    (hTb : T b = μ • b) : conjSubgroup a (LB M Q B) = LB M Q B :=
  conj_LB_eq_of_maps_line hc hB haM hT fun s => ⟨s * μ, by rw [map_smul, hTb, smul_smul]⟩

theorem conj_mem_range_LB (hc : Ctx M Q Z B) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hLB : LB M Q B ≤ H0 M Z) (a : H0 M Z)
    (hmap : Submodule.map (φ a : M₀.E →ₗ[K] M₀.E) (Submodule.span K {b}) = Submodule.span K {b})
    {t : M₀.E ≃ₗ[K] M₀.E} (ht : t ∈ (φ.comp (Subgroup.inclusion hLB)).range) :
    φ a * t * (φ a)⁻¹ ∈ (φ.comp (Subgroup.inclusion hLB)).range := by
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ • b = φ a b := by
    have := Submodule.mem_map_of_mem (f := (φ a : M₀.E →ₗ[K] M₀.E))
      (Submodule.mem_span_singleton_self b)
    rw [hmap] at this
    exact Submodule.mem_span_singleton.mp this
  have haM : (a : G) ∈ M := (a.2 : (a : G) ∈ M ⊓ _).1
  have hLa := conj_LB_eq_of_fix_line hc hB haM (T := (φ a : M₀.E →ₗ[K] M₀.E)) (hφπ a)
    hμ.symm
  obtain ⟨x, rfl⟩ := ht
  have hmem : (a : G) * (x : G) * (a : G)⁻¹ ∈ LB M Q B := by
    have h1 : (a : G) * (x : G) * (a : G)⁻¹ ∈ conjSubgroup (a : G) (LB M Q B) := by
      rw [mem_conjSubgroup,
        show (a : G)⁻¹ * ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) = x by group]
      exact x.2
    rwa [hLa] at h1
  refine ⟨⟨_, hmem⟩, ?_⟩
  show φ (Subgroup.inclusion hLB ⟨_, hmem⟩) = φ a * φ (Subgroup.inclusion hLB x) * (φ a)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem card_range_LB (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 1 ≤ n)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hLB : LB M Q B ≤ H0 M Z) :
    Nat.card (φ.comp (Subgroup.inclusion hLB)).range = Nat.card K ^ (n - 1) := by
  have hkerΦ : (φ.comp (Subgroup.inclusion hLB)).ker = Q.subgroupOf (LB M Q B) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker (Subgroup.inclusion hLB s)
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hcard : Nat.card (LB M Q B) =
      Nat.card Q * Nat.card (φ.comp (Subgroup.inclusion hLB)).range := by
    have h1 : Nat.card (φ.comp (Subgroup.inclusion hLB)).ker = Nat.card Q := by
      rw [hkerΦ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have h33 := (hc.card_of_3_3 hw hn hno (stroth_3_3 hc hw hn)).1
  rw [h33] at hcard
  rw [h.card]
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard).symm

theorem exists_tsing (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 1 ≤ n)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    ∃ W : Submodule K M₀.E, (∀ u ∈ W, M₀.Qf u = 0) ∧ Module.finrank K W = n ∧ b ∈ W := by
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hXQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hUs : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg hXQ).mp hc.inf_QB_elemAbelian
  have hcard33 := (hc.card_of_3_3 hw hn hno (stroth_3_3 hc hw hn)).2
  have hcardU : Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card K ^ n := by
    have h1 := M₀.card_eq hXQ hZX
    rw [h.card]
    have h2 : Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card Z * Nat.card Z ^ n := by
      rw [← h1, hcard33]
      ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  obtain ⟨W, hWU, -⟩ := exists_submodule_of_card_eq M₀ (w := n) (h.finrank_E hw hK) hUs hcardU
  refine ⟨W, fun u hu => hUs u ((hWU u).mp hu), ?_, (hWU b).mpr (M₀.img_mono
    (le_sup_right.trans hc.ZB_le_inf) ((hB b).mpr ⟨1, (one_smul _ b).symm⟩))⟩
  have h1 : Nat.card W = Nat.card (M₀.img (Q ⊓ QB B)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hWU)
  have h2 : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
  rw [hcardU, h2] at h1
  exact Nat.pow_right_injective hK h1

theorem fixed_aux (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hLB : LB M Q B ≤ H0 M Z) (v : M₀.E)
    (hv : ∀ t ∈ (φ.comp (Subgroup.inclusion hLB)).range, t v = v) : ∃ s : K, v = s • b := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
  have hxC : x ∈ CQt Q Z (LB M Q B) := by
    refine ⟨hxQ, fun t ht => ?_⟩
    have htQ := (conj_mem_Q hc (hc.LB_le_M ht)).1 x hxQ
    refine (M₀.comm_mem_iff hxQ htQ).mpr ?_
    have h1 : M₀.π (t * x * t⁻¹) = φ (Subgroup.inclusion hLB ⟨t, ht⟩) (M₀.π x) :=
      hφπ (Subgroup.inclusion hLB ⟨t, ht⟩) x hxQ
    rw [h1]
    exact hv _ ⟨⟨t, ht⟩, rfl⟩
  rw [h35] at hxC
  exact (hB _).mp (img_le_of_le_sup_Z h hc.le le_rfl (M₀.pi_mem_img hxC hxQ))

theorem orth_aux (hc : Ctx M Q Z B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    (h : GlobalModelData M Q Z γ M₀) {p p' : M₀.E} {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hp0 : p ≠ 0) (hp : p ∈ M₀.img (conjSubgroup m₁ B)) (hp' : p' ∈ M₀.img (conjSubgroup m₂ B))
    (hnp : ∀ c : K, p' ≠ c • p) : M₀.B p p' ≠ 0 := by
  intro h0
  have hc₁ := hc.conj_of_mem hm₁
  have hc₂ := hc.conj_of_mem hm₂
  obtain ⟨b₁, -, -, hB₁, -, -⟩ := hc₁.dictB h
  obtain ⟨b₂, -, -, hB₂, -, -⟩ := hc₂.dictB h
  obtain ⟨s₁, rfl⟩ := (hB₁ p).mp hp
  obtain ⟨s₂, rfl⟩ := (hB₂ p').mp hp'
  have hs₁ : s₁ ≠ 0 := fun h' => hp0 (by rw [h', zero_smul])
  have hs₂ : s₂ ≠ 0 := fun h' => hnp 0 (by rw [h', zero_smul, zero_smul])
  have h12 : M₀.B b₁ b₂ = 0 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hs₁, hs₂, false_or]
      using h0
  have hcomm : ∀ x ∈ conjSubgroup m₂ B, ∀ y ∈ conjSubgroup m₁ B, x * y = y * x := by
    rw [M₀.commute_iff h.reg hc₂.le hc₁.le]
    intro e he f hf
    obtain ⟨t₂, rfl⟩ := (hB₂ e).mp he
    obtain ⟨t₁, rfl⟩ := (hB₁ f).mp hf
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Tim79.QuadModel.B_comm b₂ b₁, h12,
      neg_zero, mul_zero]
  have hle := img_le_of_le_sup_Z h hc₁.le (conj_le_of_commute hc horth hm₁ hm₂ hcomm)
  obtain ⟨r, hr⟩ := (hB₁ _).mp (hle hp')
  exact hnp (r * s₁⁻¹) (by rw [hr, smul_smul, mul_assoc, inv_mul_cancel₀ hs₁, mul_one])

theorem conj_mem_img_aux (hc : Ctx M Q Z B) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (a : H0 M Z) {m : G} {p : M₀.E} (hp : p ∈ M₀.img (conjSubgroup m B)) :
    φ a p ∈ M₀.img (conjSubgroup ((a : G) * m) B) := by
  obtain ⟨x, hxB, hxQ, rfl⟩ := hp
  have haM : (a : G) ∈ M := (a.2 : (a : G) ∈ M ⊓ _).1
  rw [← hφπ a x hxQ]
  refine M₀.pi_mem_img ?_ ((conj_mem_Q hc haM).1 x hxQ)
  rw [conjSubgroup_mul, mem_conjSubgroup,
    show (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) = x by group]
  exact hxB

theorem span_aux (hc : Ctx M Q Z B) (hgen : GenByB M Q B) :
    Submodule.span K {p : M₀.E | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)} = ⊤ := by
  set P := {p : M₀.E | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)}
  have hle : (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) ≤
      M₀.lift (Submodule.span K P).toAddSubgroup := by
    refine iSup₂_le fun m hm y hy => ?_
    have hyQ : y ∈ Q := (hc.conj_of_mem hm).le hy
    refine ⟨hyQ, ?_⟩
    by_cases hy0 : M₀.π y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨hy0, m, hm, M₀.pi_mem_img hy hyQ⟩
  refine eq_top_iff.mpr fun e _ => ?_
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  have hgen' : Q = ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := hgen
  have hx' : x ∈ ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := by
    rw [← hgen']
    exact hx
  exact (hle hx').2

theorem semi_aux (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {x : H0 M Z} (hxL : (x : G) ∈ LB M Q B) (hxQ : (x : G) ∉ Q) {m : G} (hm : m ∈ M)
    {p : M₀.E} (hp0 : p ≠ 0) (hpm : p ∈ M₀.img (conjSubgroup m B))
    (hpb : ∀ c : K, p ≠ c • b) (hfix : φ x p ∈ Submodule.span K {p}) : False := by
  have hc' := hc.conj_of_mem hm
  obtain ⟨b', -, -, hB', -, -⟩ := hc'.dictB h
  obtain ⟨s, rfl⟩ := (hB' p).mp hpm
  have hs : s ≠ 0 := fun h' => hp0 (by rw [h', zero_smul])
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hfix
  have e1 : b' = s⁻¹ • (s • b') := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hTb' : φ x b' = μ • b' := by
    calc φ x b' = φ x (s⁻¹ • (s • b')) := by rw [← e1]
      _ = s⁻¹ • (μ • (s • b')) := by rw [map_smul, ← hμ]
      _ = μ • b' := by rw [smul_comm s⁻¹ μ (s • b'), ← e1]
  have hxM : (x : G) ∈ M := (x.2 : (x : G) ∈ M ⊓ _).1
  have hLx := conj_LB_eq_of_fix_line hc' hB' hxM (T := (φ x : M₀.E →ₗ[K] M₀.E)) (hφπ x) hTb'
  have hcomm := comm_of_mem_inf h34 hc hw hn hno hgen hm hxL
    (conjSubgroup_eq_self_iff.mp hLx) hxQ
  obtain ⟨r, hr⟩ := (hB _).mp (img_le_of_le_sup_Z h hc.le (horth m hm hcomm) hpm)
  exact hpb r hr

theorem moves_aux (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧
      ¬ ∃ μ : K, φ x b = μ • b := by
  obtain ⟨m, hm, hmB⟩ := exists_conj_not_le_sup hc
  obtain ⟨t₀, ht₀L, ht₀Q⟩ : ∃ t₀ ∈ LB M Q B, t₀ ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h33 := (hc.card_of_3_3 hw (by omega) hno (stroth_3_3 hc hw (by omega))).1
    have hle := Subgroup.card_le_of_le (show LB M Q B ≤ Q from hcon)
    rw [h33] at hle
    have hZ := hc.hyp.q4
    have hQ : 0 < Nat.card Q := Nat.card_pos
    have h1 : Nat.card Z ≤ Nat.card Z ^ (n - 1) := le_self_pow (by omega) (by omega)
    have h2 : Nat.card Q * 4 ≤ Nat.card Q * Nat.card Z ^ (n - 1) :=
      Nat.mul_le_mul_left _ (hZ.trans h1)
    omega
  have htL : m * t₀ * m⁻¹ ∈ conjSubgroup m (LB M Q B) :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using ht₀L)
  have htQ : m * t₀ * m⁻¹ ∉ Q := fun h' => ht₀Q (by
    simpa [mul_assoc] using (conj_mem_Q hc hm).2 _ h')
  have htH : m * t₀ * m⁻¹ ∈ H0 M Z := conj_LB_le_H0 hc hm htL
  refine ⟨m, hm, ⟨_, htH⟩, htL, ?_⟩
  rintro ⟨μ, hμ⟩
  have htM : m * t₀ * m⁻¹ ∈ M := (htH : m * t₀ * m⁻¹ ∈ M ⊓ _).1
  have hLt := conj_LB_eq_of_fix_line hc hB htM (T := (φ ⟨_, htH⟩ : M₀.E →ₗ[K] M₀.E))
    (hφπ ⟨_, htH⟩) hμ
  exact hmB (horth m hm (comm_of_mem_conj_inf h34 hc hw hn hno hgen hm htL
    (conjSubgroup_eq_self_iff.mp hLt) htQ))

theorem conj_mem_range_of_line (hc : Ctx M Q Z B) {b : M₀.E} (hb0 : b ≠ 0)
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hLB : LB M Q B ≤ H0 M Z) {m : G} (hm : m ∈ M) {b' : M₀.E}
    (hB' : ∀ v : M₀.E, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • b') (a : H0 M Z)
    (hab : Submodule.map (φ a : M₀.E →ₗ[K] M₀.E) (Submodule.span K {b}) =
      Submodule.span K {b'})
    {x : H0 M Z} (hx : (x : G) ∈ conjSubgroup m (LB M Q B)) :
    (φ a)⁻¹ * φ x * φ a ∈ (φ.comp (Subgroup.inclusion hLB)).range := by
  have haM : (a : G) ∈ M := (a.2 : (a : G) ∈ M ⊓ _).1
  have hm' : (a : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem haM) hm
  obtain ⟨ν, hν⟩ : ∃ ν : K, ν • b' = φ a b := by
    have := Submodule.mem_map_of_mem (f := (φ a : M₀.E →ₗ[K] M₀.E))
      (Submodule.mem_span_singleton_self b)
    rw [hab] at this
    exact Submodule.mem_span_singleton.mp this
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at hν
    exact hb0 hν
  have hle : conjSubgroup ((a : G)⁻¹ * m) B ≤ B ⊔ Z := by
    intro y hy
    have hyQ : y ∈ Q := (hc.conj_of_mem hm').le hy
    have hy' : (a : G) * y * (a : G)⁻¹ ∈ conjSubgroup m B := by
      rw [mem_conjSubgroup]
      have := mem_conjSubgroup.mp hy
      rwa [show m⁻¹ * ((a : G) * y * (a : G)⁻¹) * m =
        ((a : G)⁻¹ * m)⁻¹ * y * ((a : G)⁻¹ * m) by group]
    have hy'Q : (a : G) * y * (a : G)⁻¹ ∈ Q := (conj_mem_Q hc haM).1 y hyQ
    obtain ⟨s, hs⟩ := (hB' _).mp (M₀.pi_mem_img hy' hy'Q)
    rw [hφπ a y hyQ] at hs
    have hπy : M₀.π y = (s * ν⁻¹) • b := by
      refine (φ a).injective ?_
      rw [hs, map_smul, ← hν, smul_smul, mul_assoc, inv_mul_cancel₀ hν0, mul_one]
    have hmem : M₀.π y ∈ M₀.img B := (hB _).mpr ⟨_, hπy⟩
    exact (M₀.mem_img_iff le_sup_right hyQ).mp (M₀.img_mono le_sup_left hmem)
  have hLeq := hc.conj_LB_eq_of_le_sup_Z hm' hle
  have hmem : (a : G)⁻¹ * (x : G) * (a : G) ∈ LB M Q B := by
    rw [← hLeq, mem_conjSubgroup]
    have := mem_conjSubgroup.mp hx
    rwa [show ((a : G)⁻¹ * m)⁻¹ * ((a : G)⁻¹ * (x : G) * (a : G)) * ((a : G)⁻¹ * m) =
      m⁻¹ * (x : G) * m by group]
  refine ⟨⟨_, hmem⟩, ?_⟩
  show φ (Subgroup.inclusion hLB ⟨_, hmem⟩) = (φ a)⁻¹ * φ x * φ a
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

end Glue

end CFSG.RankThree.GF2n.Stroth80.Gl37
