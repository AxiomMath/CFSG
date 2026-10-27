module

public import CFSG.Quasithin.H13.L32AKG1468m
public import CFSG.Quasithin.H13.L32AKG1468k

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {Y R M I : Subgroup G}

theorem false_of_alt_small {V : Subgroup G} (hR : R ≤ Subgroup.normalizer (I : Set G))
    (hJV : I ≤ Subgroup.normalizer (V : Set G))
    (hD : I ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 I) {n : ℕ} (hn : n ≤ 6)
    {α : ↥I →* alternatingGroup (Fin n)} (hker : α.ker = CFSG.pCore 2 ↥I) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap)
    (hrel : ∀ (k : G) (hk : k ∈ I) (hk' : t * k * t⁻¹ ∈ I),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ I) V = autOn I V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haB : a ∈ oTwoUpper (I ⊓ M)) (ha5 : orderOf a = 5) : False := by
  obtain ⟨hc5, hc1, hcσ⟩ := SBc17.alt_data_of_five hR hJV hD hker htR htV hrel hMK
    (oTwoUpper_le_inf haB) ha5
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  exact hc1 (eq_one_of_commute_swap_small hn hc5 hxy hcσ)

theorem pCoreOf_le_of_alt_seven {V : Subgroup G} (hR : R ≤ Subgroup.normalizer (I : Set G))
    (hJV : I ≤ Subgroup.normalizer (V : Set G))
    (hD : I ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 I)
    {α : ↥I →* alternatingGroup (Fin 7)} (hker : α.ker = CFSG.pCore 2 ↥I) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin 7)} (hσ : σ.IsSwap)
    (hrel : ∀ (k : G) (hk : k ∈ I) (hk' : t * k * t⁻¹ ∈ I),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin 7)) * σ⁻¹)
    (hMK : autOn (M ⊓ I) V = autOn I V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haB : a ∈ oTwoUpper (I ⊓ M)) (ha5 : orderOf a = 5) :
    pCoreOf 2 (oTwoUpper (I ⊓ M)) ≤ pCoreOf 2 I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := oTwoUpper (I ⊓ M) with hB
  have hBMI : B ≤ M ⊓ I := oTwoUpper_le_inf
  have hBI : B ≤ I := hBMI.trans inf_le_right
  have haM : a ∈ M ⊓ I := hBMI haB
  obtain ⟨hc5, hc1, hcσ⟩ := SBc17.alt_data_of_five hR hJV hD hker htR htV hrel hMK haM ha5
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  let α' : ↥I →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp α
  have hOB : pCoreOf 2 B ≤ I := (CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans hBI
  set N : Subgroup (Equiv.Perm (Fin 7)) := ((pCoreOf 2 B).subgroupOf I).map α' with hN
  have hNp : IsPGroup 2 N :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B).comap_of_injective I.subtype
      I.subtype_injective).map α'
  have hmemN : ∀ ν ∈ N, ∃ d : ↥I, (d : G) ∈ pCoreOf 2 B ∧ α' d = ν := by
    rintro ν ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hNσ : ∀ ν ∈ N, ν * Equiv.swap x y = Equiv.swap x y * ν := by
    intro ν hν
    obtain ⟨d, hd, rfl⟩ := hmemN ν hν
    exact alt_commute_of_mem hR hJV hD hker htR htV hrel hMK
      (hBMI (CFSG.LieType.BorelTits.pCoreOf_le 2 B hd))
  have hNs : ∀ ν ∈ N, Equiv.Perm.sign ν = 1 := by
    intro ν hν
    obtain ⟨d, -, rfl⟩ := hmemN ν hν
    exact Equiv.Perm.mem_alternatingGroup.mp (α d).2
  have hnB : ∀ g ∈ B, ∀ d ∈ pCoreOf 2 B, g * d * g⁻¹ ∈ pCoreOf 2 B := fun g hg d hd =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B hg) d).mp hd
  set aI : ↥I := ⟨a, haM.2⟩ with haI
  have hcN : α' aI ∈ Subgroup.normalizer (N : Set (Equiv.Perm (Fin 7))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨d, hd, rfl⟩ := hmemN h hh
      refine ⟨aI * d * aI⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((aI * d * aI⁻¹ : ↥I) : G) ∈ pCoreOf 2 B
      simpa using hnB a haB d hd
    · intro hh
      obtain ⟨d, hd, hde⟩ := hmemN _ hh
      refine ⟨aI⁻¹ * d * aI, ?_, ?_⟩
      · show ((aI⁻¹ * d * aI : ↥I) : G) ∈ pCoreOf 2 B
        have := hnB a⁻¹ (B.inv_mem haB) d hd
        simpa using this
      · rw [map_mul, map_mul, map_inv, hde]
        group
  have hall := eq_one_of_two_group_seven hNp hxy hNσ hNs hc5 hc1 hcσ hcN
  intro d hd
  have hdI : d ∈ I := hOB hd
  have h1 : α' ⟨d, hdI⟩ = 1 := hall _ ⟨⟨d, hdI⟩, hd, rfl⟩
  have h2 : α ⟨d, hdI⟩ = 1 := Subtype.ext h1
  exact (SBc17.map_eq_one_iff_mem_pCoreOf hker ⟨d, hdI⟩).mp h2

theorem eight_facts : Equiv.Perm.sign (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) = 1 ∧
    Equiv.Perm.sign (List.formPerm [5, 6, 7] : Equiv.Perm (Fin 8)) = 1 ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) * Equiv.swap 0 1 =
      Equiv.swap 0 1 * List.formPerm [2, 3, 4] ∧
    (List.formPerm [5, 6, 7] : Equiv.Perm (Fin 8)) * Equiv.swap 0 1 =
      Equiv.swap 0 1 * List.formPerm [5, 6, 7] ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) * List.formPerm [5, 6, 7] =
      List.formPerm [5, 6, 7] * List.formPerm [2, 3, 4] ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) ^ 3 = 1 ∧
    (List.formPerm [5, 6, 7] : Equiv.Perm (Fin 8)) ^ 3 = 1 ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) ≠ 1 ∧
    (List.formPerm [5, 6, 7] : Equiv.Perm (Fin 8)) ≠ 1 ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) * List.formPerm [5, 6, 7] ≠ 1 ∧
    (List.formPerm [2, 3, 4] : Equiv.Perm (Fin 8)) * (List.formPerm [5, 6, 7])⁻¹ ≠ 1 := by
  decide +kernel

theorem exists_perm_zero_one {x y : Fin 8} (hxy : x ≠ y) :
    ∃ π : Equiv.Perm (Fin 8), π 0 = x ∧ π 1 = y := by
  have hy' : Equiv.swap 0 x y ≠ 0 := by
    intro h
    have := congrArg (Equiv.swap 0 x) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hxy this.symm
  refine ⟨Equiv.swap 0 x * Equiv.swap 1 (Equiv.swap 0 x y), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hy'.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

theorem false_of_alt_eight {V : Subgroup G} (hR : R ≤ Subgroup.normalizer (I : Set G))
    (hJV : I ≤ Subgroup.normalizer (V : Set G))
    (hD : I ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 I)
    (hOC : pCoreOf 2 I ≤ Subgroup.centralizer (V : Set G))
    {α : ↥I →* alternatingGroup (Fin 8)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥I) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hRt : autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩)) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ.IsSwap)
    (hrel : ∀ (k : G) (hk : k ∈ I) (hk' : t * k * t⁻¹ ∈ I),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin 8)) * σ⁻¹)
    (hMK : autOn (M ⊓ I) V = autOn I V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    (e : ↥(oTwoUpper (I ⊓ M)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (I ⊓ M)) ≃*
      alternatingGroup (Fin 5)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := oTwoUpper (I ⊓ M) with hB
  have hBI : B ≤ I := (oTwoUpper_le _).trans inf_le_left
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_zero_one hxy
  have hπσ : MulAut.conj π (Equiv.swap 0 1) = Equiv.swap x y := by
    rw [MulAut.conj_apply, ← Equiv.swap_apply_apply, hπ0, hπ1]
  obtain ⟨s1, s2, c1, c2, c12, p1, p2, n1, n2, n12, n12'⟩ := eight_facts
  set g₁ : Equiv.Perm (Fin 8) := MulAut.conj π (List.formPerm [2, 3, 4]) with hg₁
  set g₂ : Equiv.Perm (Fin 8) := MulAut.conj π (List.formPerm [5, 6, 7]) with hg₂
  have hs : ∀ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 →
      Equiv.Perm.sign (MulAut.conj π g) = 1 := by
    intro g hg
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hg, mul_one, mul_inv_cancel]
  have hc : ∀ g : Equiv.Perm (Fin 8), g * Equiv.swap 0 1 = Equiv.swap 0 1 * g →
      MulAut.conj π g * Equiv.swap x y = Equiv.swap x y * MulAut.conj π g := by
    intro g hg
    rw [← hπσ, ← map_mul, ← map_mul, hg]
  have g12 : g₁ * g₂ = g₂ * g₁ := by rw [hg₁, hg₂, ← map_mul, ← map_mul, c12]
  have g13 : g₁ ^ 3 = 1 := by rw [hg₁, ← map_pow, p1, map_one]
  have g23 : g₂ ^ 3 = 1 := by rw [hg₂, ← map_pow, p2, map_one]
  have gn1 : g₁ ≠ 1 := by rw [hg₁, Ne, map_eq_one_iff _ (MulAut.conj π).injective]; exact n1
  have gn2 : g₂ ≠ 1 := by rw [hg₂, Ne, map_eq_one_iff _ (MulAut.conj π).injective]; exact n2
  have gn3 : g₁ * g₂ ≠ 1 := by
    rw [hg₁, hg₂, ← map_mul, Ne, map_eq_one_iff _ (MulAut.conj π).injective]
    exact n12
  have gn4 : g₁ * g₂⁻¹ ≠ 1 := by
    rw [hg₁, hg₂, ← map_inv, ← map_mul, Ne, map_eq_one_iff _ (MulAut.conj π).injective]
    exact n12'
  set ĝ₁ : alternatingGroup (Fin 8) := ⟨g₁, Equiv.Perm.mem_alternatingGroup.mpr (hs _ s1)⟩
  set ĝ₂ : alternatingGroup (Fin 8) := ⟨g₂, Equiv.Perm.mem_alternatingGroup.mpr (hs _ s2)⟩
  have hlift : ∀ ĝ : alternatingGroup (Fin 8), (ĝ : Equiv.Perm (Fin 8)) ^ 3 = 1 →
      (ĝ : Equiv.Perm (Fin 8)) ≠ 1 →
      (ĝ : Equiv.Perm (Fin 8)) * Equiv.swap x y = Equiv.swap x y * ĝ →
      ∃ b : ↥I, (b : G) ∈ B ∧ α b = ĝ := by
    intro ĝ h3 h1 hcomm
    obtain ⟨m, hm, hmα⟩ := SBc17.exists_lift_mem_M hR hJV hD hOC hα hker htR htV hRt hrel hMK hcomm
    have hodd : Odd (orderOf (α ⟨m, hm.2⟩)) := by
      rw [hmα, ← Subgroup.orderOf_coe,
        orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) h3 h1]
      decide
    obtain ⟨b, hbB, hb⟩ := exists_odd_lift α (X := I ⊓ M) (m := ⟨m, hm.2⟩) ⟨hm.2, hm.1⟩ hodd
    exact ⟨b, hbB, hb.trans hmα⟩
  obtain ⟨b₁, hb₁B, hb₁⟩ := hlift ĝ₁ g13 gn1 (hc _ c1)
  obtain ⟨b₂, hb₂B, hb₂⟩ := hlift ĝ₂ g23 gn2 (hc _ c2)
  let φ : ↥B →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  let αB : ↥B →* alternatingGroup (Fin 8) := α.comp (Subgroup.inclusion hBI)
  have hφ1 : ∀ w : ↥B, αB w = 1 → φ w = 1 := by
    intro w hw
    have h1 : ((w : ↥B) : G) ∈ pCoreOf 2 I :=
      (SBc17.map_eq_one_iff_mem_pCoreOf hker (Subgroup.inclusion hBI w)).mp hw
    have h2 : ((w : ↥B) : G) ∈ pCoreOf 2 B := inf_pCoreOf_le hBI ⟨w.2, h1⟩
    show e (QuotientGroup.mk w) = 1
    rw [(He16.mk_eq_one_iff_mem_pCoreOf' w).mpr h2, map_one]
  have hφ2 : ∀ w : ↥B, φ w = 1 → ∃ k : ℕ, ((αB w : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)) ^ 2 ^ k = 1 := by
    intro w hw
    have h1 : (QuotientGroup.mk w : ↥B ⧸ CFSG.pCore 2 ↥B) = 1 := by
      have : e (QuotientGroup.mk w) = 1 := hw
      rwa [MulEquiv.map_eq_one_iff] at this
    have h2 := (He16.mk_eq_one_iff_mem_pCoreOf' w).mp h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B ⟨_, h2⟩
    have h3 : w ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg (fun z : ↥(pCoreOf 2 B) => (z : G)) hk
      simpa using this
    refine ⟨k, ?_⟩
    rw [← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
  set w₁ : ↥B := ⟨b₁, hb₁B⟩
  set w₂ : ↥B := ⟨b₂, hb₂B⟩
  have hα₁ : αB w₁ = ĝ₁ := hb₁
  have hα₂ : αB w₂ = ĝ₂ := hb₂
  have hne : ∀ w : ↥B, ((αB w : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) ^ 3 = 1 →
      ((αB w : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) ≠ 1 → φ w ≠ 1 := by
    intro w h3 h1 hw
    obtain ⟨k, hk⟩ := hφ2 w hw
    exact h1 (eq_one_of_pow_two_pow_of_pow_three hk h3)
  have hcube : ∀ w : ↥B, ((αB w : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) ^ 3 = 1 →
      φ w ^ 3 = 1 := by
    intro w h3
    rw [← map_pow]
    exact hφ1 _ (Subtype.ext (by rw [map_pow, Subgroup.coe_pow, h3, Subgroup.coe_one]))
  have hcomm : φ w₁ * φ w₂ = φ w₂ * φ w₁ := by
    have h1 : φ (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) = 1 := by
      refine hφ1 _ (Subtype.ext ?_)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hα₁, hα₂]
      show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = 1
      rw [g12, mul_inv_cancel_right, mul_inv_cancel]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hcomm' : Commute g₁ g₂ := g12
  refine a5_three_three (φ w₁) (φ w₂) (hcube w₁ (by rw [hα₁]; exact g13))
    (hcube w₂ (by rw [hα₂]; exact g23)) hcomm (hne w₁ (by rw [hα₁]; exact g13)
    (by rw [hα₁]; exact gn1)) (hne w₂ (by rw [hα₂]; exact g23) (by rw [hα₂]; exact gn2)) ?_ ?_
  · rw [← map_mul]
    refine hne _ ?_ ?_
    · rw [map_mul, Subgroup.coe_mul, hα₁, hα₂]
      show (g₁ * g₂) ^ 3 = 1
      rw [hcomm'.mul_pow, g13, g23, one_mul]
    · rw [map_mul, Subgroup.coe_mul, hα₁, hα₂]
      exact gn3
  · rw [← map_inv, ← map_mul]
    refine hne _ ?_ ?_
    · rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hα₁, hα₂]
      show (g₁ * g₂⁻¹) ^ 3 = 1
      rw [hcomm'.inv_right.mul_pow, g13, inv_pow, g23, inv_one, one_mul]
    · rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hα₁, hα₂]
      exact gn4

end CFSG.Quasithin.H13.KGBlk
