module

public import CFSG.RankThree.PartOne.CTP.StdDescent
public import CFSG.RankThree.PartOne.CTP.StdRigid
public import CFSG.RankThree.PartOne.CTP.IStd
public import CFSG.RankThree.PartOne.CTP.StdData

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL subfieldGL_mem_gramSU coe_subfieldGL subfieldGL_injective
  exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL fixSubfield_unitaryFieldData
  fixSubfield_unitaryFieldData_bar isPerfect_gramSU_one)
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Helpers

variable {e : ℕ} {K : Type} [Field K]

theorem isPerfect_unitarySU_three_of_two_le (h : UnitaryFieldData 2 e K) (he : 2 ≤ e) :
    Group.IsPerfect ↥(unitarySU 2 e K 3) := by
  have hq : ¬(3 = 3 ∧ 2 ^ e = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have h1 := isPerfect_gramSU_one h (le_refl 3) hq
  rw [unitarySU_eq_gramSU h 3]
  exact h1

theorem four_le_two_pow {e : ℕ} (he : 2 ≤ e) : 4 ≤ 2 ^ e :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem glAut_subfieldGL_fix {σ : K ≃+* K} {n : ℕ} (g : GL (Fin n) (fixSubfield σ)) :
    glAut σ (subfieldGL (fixSubfield σ) n g) = subfieldGL (fixSubfield σ) n g := by
  apply Units.ext
  rw [coe_glAut, coe_subfieldGL]
  ext i j
  simp only [Matrix.map_apply, Subfield.coe_subtype]
  exact (g i j).2

end Helpers

section Fixed

variable {f₀ : ℕ} {F : Type} [Field F]

theorem exists_fixData (hF : UnitaryFieldData 2 (5 * f₀) F) {σ : F ≃+* F} (hσ : orderOf σ = 5) :
    ∃ h₀ : UnitaryFieldData 2 f₀ (fixSubfield σ), ∀ x : fixSubfield σ,
      (h₀.bar x : F) = hF.bar x := by
  have h' := fixSubfield_unitaryFieldData hF Nat.prime_five (by norm_num) hσ
  have hb := fixSubfield_unitaryFieldData_bar hF Nat.prime_five (by norm_num) hσ
  have e : 5 * f₀ / 5 = f₀ := by omega
  have key : ∀ g, g = f₀ → ∀ (h'' : UnitaryFieldData 2 g (fixSubfield σ)),
      (∀ x : fixSubfield σ, (h''.bar x : F) = hF.bar x) →
      ∃ h₀ : UnitaryFieldData 2 f₀ (fixSubfield σ), ∀ x : fixSubfield σ,
        (h₀.bar x : F) = hF.bar x := by
    rintro g rfl h'' hb''
    exact ⟨h'', hb''⟩
  exact key _ e h' hb

end Fixed

section Transport

variable {G : Type} [Group G] {I : Subgroup G}

theorem tr_eq_map {H₀ H : Type} [Group H₀] [Group H] {Ψ : ↥I →* H} (ι : H₀ →* H)
    {K Y : Subgroup G} (hKI : K ≤ I) (hYK : Y ≤ K) (ψ' : ↥K → H₀)
    (hψ' : ∀ x : ↥K, Ψ ⟨x, hKI x.2⟩ = ι (ψ' x)) {U T : Subgroup H₀}
    (hsurj : ∀ u ∈ U, ∃ x : ↥K, ψ' x = u) (hTU : T ≤ U)
    (hiff : ∀ x : ↥K, (x : G) ∈ Y ↔ ψ' x ∈ T) : tr I Ψ Y = T.map ι := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxY : (x : G) ∈ Y := hx
    have hxK : (x : G) ∈ K := hYK hxY
    refine ⟨ψ' ⟨x, hxK⟩, (hiff ⟨x, hxK⟩).mp hxY, ?_⟩
    exact (hψ' ⟨x, hxK⟩).symm
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hsurj t (hTU ht)
    refine ⟨⟨x, hKI x.2⟩, ?_, ?_⟩
    · exact (hiff x).mpr (hx ▸ ht)
    · rw [hψ' x, hx]

end Transport

theorem mem_map_conj_iff {H : Type} [Group H] (S : Subgroup H) (A y : H) :
    y ∈ S.map (MulAut.conj A).toMonoidHom ↔ A⁻¹ * y * A ∈ S :=
  Equivariance.mem_conjBy

section Recoord

variable {f f₀ : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData 2 f F) {K₀ : Subfield F}
  (h₀ : UnitaryFieldData 2 f₀ K₀) (hbar : ∀ x : K₀, (h₀.bar x : F) = hF.bar x)

include hbar in
theorem subfieldGL_mem_primeFormUnitary {A : GL (Fin 3) K₀}
    (hA : ((A : Matrix (Fin 3) (Fin 3) K₀).map h₀.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K₀) = 1) :
    subfieldGL K₀ 3 A ∈ primeFormUnitary hF (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [mem_primeFormUnitary, Matrix.mul_one, coe_subfieldGL,
    CFSG.RankThree.Classical.map_subtype_map_bar hF h₀ hbar 3, ← Matrix.transpose_map,
    ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_primeFormUnitary_of_isometry {A : GL (Fin 3) K₀}
    (hA : ((A : Matrix (Fin 3) (Fin 3) K₀).map h₀.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K₀) = 1) :
    A ∈ primeFormUnitary h₀ (1 : Matrix (Fin 3) (Fin 3) K₀) := by
  rw [mem_primeFormUnitary, Matrix.mul_one]
  exact hA

end Recoord

section Main

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I : Subgroup G}

omit [Finite G] in
theorem tr_cent_eq (pre : PreStd c f₀ I) (hc : c ∈ Subgroup.normalizer (I : Set G))
    (h₀ : UnitaryFieldData 2 f₀ (fixSubfield pre.σ))
    (hbar : ∀ x : fixSubfield pre.σ, (h₀.bar x : pre.F) = pre.hF.bar x) :
    tr I pre.Ψ (I ⊓ Subgroup.centralizer ({c} : Set G)) =
      (unitarySU 2 f₀ (fixSubfield pre.σ) 3).map (subfieldGL (fixSubfield pre.σ) 3) := by
  have hnorm : ∀ x : ↥I, c * (x : G) * c⁻¹ ∈ I := fun x =>
    (Subgroup.mem_normalizer_iff.mp hc x).mp x.2
  ext z
  constructor
  ·
    intro hz
    have hzr : z ∈ pre.Ψ.range := tr_le_range inf_le_left hz
    obtain ⟨x, rfl⟩ := hzr
    have hx : (x : G) ∈ I ⊓ Subgroup.centralizer ({c} : Set G) := (mem_tr_iff pre.Ψ_inj x).mp hz
    have hcomm : (x : G) * c = c * (x : G) := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxe : (⟨c * (x : G) * c⁻¹, hnorm x⟩ : ↥I) = x :=
      Subtype.ext (by rw [mul_inv_eq_iff_eq_mul]; exact hcomm.symm)
    have hfix : glAut pre.σ (pre.Ψ x) = pre.Ψ x := by
      rw [← pre.Ψ_c x (hnorm x), hxe]
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed 3 hfix
    refine ⟨g₀, ?_, hg₀⟩
    have hmem : pre.Ψ x ∈ unitarySU 2 (5 * f₀) pre.F 3 := by
      rw [← pre.Ψ_range]
      exact ⟨x, rfl⟩
    rw [unitarySU_eq_gramSU pre.hF 3, ← hg₀] at hmem
    have := mem_gramSU_of_subfieldGL pre.hF 3 h₀ hbar hmem
    rw [unitarySU_eq_gramSU h₀ 3]
    exact this
  · rintro ⟨g₀, hg₀, rfl⟩
    have hg₀' : g₀ ∈ gramSU h₀ (1 : Matrix (Fin 3) (Fin 3) (fixSubfield pre.σ)) := by
      rw [← unitarySU_eq_gramSU h₀ 3]
      exact hg₀
    have hmem : subfieldGL (fixSubfield pre.σ) 3 g₀ ∈ pre.Ψ.range := by
      rw [pre.Ψ_range, unitarySU_eq_gramSU pre.hF 3]
      exact subfieldGL_mem_gramSU pre.hF h₀ hbar 3 hg₀'
    obtain ⟨x, hx⟩ := hmem
    rw [← hx, mem_tr_iff pre.Ψ_inj x]
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : pre.Ψ ⟨c * (x : G) * c⁻¹, hnorm x⟩ = pre.Ψ x := by
      rw [pre.Ψ_c x (hnorm x), hx, glAut_subfieldGL_fix]
    have h2 := congrArg Subtype.val (pre.Ψ_inj h1)
    simp only at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm

theorem isPerfect_S₀ {F : Type} [Field F] {K₀ : Subfield F} (h₀ : UnitaryFieldData 2 f₀ K₀)
    (hf₀ : 2 ≤ f₀) : Group.IsPerfect ↥((unitarySU 2 f₀ K₀ 3).map (subfieldGL K₀ 3)) := by
  have := isPerfect_unitarySU_three_of_two_le h₀ hf₀
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.equivMapOfInjective _ (subfieldGL K₀ 3)
      (subfieldGL_injective K₀ 3)).toMonoidHom)
    (MulEquiv.surjective _)

theorem tr_K_eq (pre : PreStd c f₀ I) (hc : c ∈ Subgroup.normalizer (I : Set G))
    (h₀ : UnitaryFieldData 2 f₀ (fixSubfield pre.σ))
    (hbar : ∀ x : fixSubfield pre.σ, (h₀.bar x : pre.F) = pre.hF.bar x) (hf₀ : 2 ≤ f₀)
    {K : Subgroup G}
    (hK : K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))) :
    tr I pre.Ψ K =
      (unitarySU 2 f₀ (fixSubfield pre.σ) 3).map (subfieldGL (fixSubfield pre.σ) 3) := by
  rw [hK, tr_residual pre.Ψ_inj inf_le_left, tr_cent_eq pre hc h₀ hbar]
  exact inSubgroup_perfectResidual_of_isPerfect (isPerfect_S₀ h₀ hf₀)

theorem coe_equivMapOfInjective_symm {H H' : Type} [Group H] [Group H'] (S : Subgroup H)
    (f : H →* H') (hf : Function.Injective f) (y : ↥(S.map f)) :
    f ((((Subgroup.equivMapOfInjective S f hf).symm y : ↥S)) : H) = (y : H') := by
  have h1 : (((Subgroup.equivMapOfInjective S f hf)
      ((Subgroup.equivMapOfInjective S f hf).symm y) : ↥(S.map f)) : H') =
        f ((((Subgroup.equivMapOfInjective S f hf).symm y : ↥S)) : H) :=
    Subgroup.coe_equivMapOfInjective_apply S f hf _
  rw [← h1, MulEquiv.apply_symm_apply]

@[expose] noncomputable def trEquiv (pre : PreStd c f₀ I) {K : Subgroup G} (hKI : K ≤ I) :
    ↥K ≃* ↥(tr I pre.Ψ K) :=
  (Subgroup.subgroupOfEquivOfLe hKI).symm.trans (Subgroup.equivMapOfInjective _ pre.Ψ pre.Ψ_inj)

@[expose] noncomputable def psiK (pre : PreStd c f₀ I) {K : Subgroup G} (hKI : K ≤ I)
    (htr : tr I pre.Ψ K =
      (unitarySU 2 f₀ (fixSubfield pre.σ) 3).map (subfieldGL (fixSubfield pre.σ) 3)) :
    ↥K ≃* ↥(unitarySU 2 f₀ (fixSubfield pre.σ) 3) :=
  (trEquiv pre hKI).trans ((MulEquiv.subgroupCongr htr).trans
    (Subgroup.equivMapOfInjective _ (subfieldGL (fixSubfield pre.σ) 3)
      (subfieldGL_injective _ 3)).symm)

omit [Finite G] in
theorem psiK_spec (pre : PreStd c f₀ I) {K : Subgroup G} (hKI : K ≤ I)
    (htr : tr I pre.Ψ K =
      (unitarySU 2 f₀ (fixSubfield pre.σ) 3).map (subfieldGL (fixSubfield pre.σ) 3))
    (x : ↥K) : subfieldGL (fixSubfield pre.σ) 3
      ((psiK pre hKI htr x : ↥(unitarySU 2 f₀ (fixSubfield pre.σ) 3)) : GL (Fin 3) _) =
        pre.Ψ ⟨x, hKI x.2⟩ := by
  have h1 := coe_equivMapOfInjective_symm (unitarySU 2 f₀ (fixSubfield pre.σ) 3)
    (subfieldGL (fixSubfield pre.σ) 3) (subfieldGL_injective _ 3)
    (MulEquiv.subgroupCongr htr (trEquiv pre hKI x))
  exact h1.trans rfl

end Main

section Exist

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G}

theorem exists_stdData (hGA : CFSG.Open.GriessAllModelsStatement)
    (cfg : IConfig c f₀ I K BK J) : StdPic c f₀ I K BK J := by
  obtain ⟨pre⟩ := exists_preStd hGA cfg.dvd5 cfg.model cfg.perfect cfg.c_norm cfg.c_pow cfg.c_outer
  obtain ⟨h₀, hbar⟩ := exists_fixData pre.hF pre.σ_order
  have htrK := tr_K_eq pre cfg.c_norm h₀ hbar cfg.f_two cfg.K_eq
  obtain ⟨Kq, _, hq, φ, hJ, hBKle, hBK⟩ := cfg.triangle
  have hgcd : Nat.gcd 3 (2 ^ f₀ + 1) = 1 :=
    coprime_three_two_pow_add_one (even_of_five_dvd cfg.dvd5)
  have : Finite Kq := hq.finite
  set K₀ := fixSubfield pre.σ with hK₀
  let ψ : ↥K ≃* ↥(unitarySU 2 f₀ K₀ 3) := psiK pre cfg.K_le htrK
  let α : ↥(unitarySU 2 f₀ Kq 3) ≃* ↥(unitarySU 2 f₀ K₀ 3) := φ.symm.trans ψ
  obtain ⟨A, hA1, hAblk, hAtor⟩ := rigid_triangle hq h₀ cfg.f_two hgcd α
  have hA : A ∈ primeFormUnitary h₀ (1 : Matrix (Fin 3) (Fin 3) K₀) :=
    mem_primeFormUnitary_of_isometry h₀ hA1
  have hιA : subfieldGL K₀ 3 A ∈ primeFormUnitary pre.hF (1 : Matrix (Fin 3) (Fin 3) pre.F) :=
    subfieldGL_mem_primeFormUnitary pre.hF h₀ hbar hA1
  have hfixA : glAut pre.σ (subfieldGL K₀ 3 A) = subfieldGL K₀ 3 A := glAut_subfieldGL_fix A
  let Ψ : ↥I →* GL (Fin 3) pre.F := (MulAut.conj (subfieldGL K₀ 3 A)⁻¹).toMonoidHom.comp pre.Ψ
  have hΨx : ∀ x : ↥I, Ψ x = (subfieldGL K₀ 3 A)⁻¹ * pre.Ψ x * subfieldGL K₀ 3 A := fun x => by
    simp [Ψ]
  have hΨrange : Ψ.range = unitarySU 2 (5 * f₀) pre.F 3 := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      rw [hΨx, unitarySU_eq_gramSU pre.hF 3]
      have hx : pre.Ψ x ∈ gramSU pre.hF (1 : Matrix (Fin 3) (Fin 3) pre.F) := by
        rw [← unitarySU_eq_gramSU pre.hF 3, ← pre.Ψ_range]
        exact ⟨x, rfl⟩
      have := conj_mem_gramSU pre.hF 1 (inv_mem hιA) hx
      simpa using this
    · intro hg
      rw [unitarySU_eq_gramSU pre.hF 3] at hg
      have h1 := conj_mem_gramSU pre.hF 1 hιA hg
      rw [← unitarySU_eq_gramSU pre.hF 3, ← pre.Ψ_range] at h1
      obtain ⟨x, hx⟩ := h1
      refine ⟨x, ?_⟩
      rw [hΨx, hx]
      group
  have hΨc : ∀ (x : ↥I) (hx : c * (x : G) * c⁻¹ ∈ I),
      Ψ ⟨c * x * c⁻¹, hx⟩ = glAut pre.σ (Ψ x) := by
    intro x hx
    rw [hΨx, hΨx, pre.Ψ_c x hx]
    simp only [map_mul, map_inv, hfixA]
  let ψ' : ↥K → GL (Fin 3) K₀ := fun x =>
    A⁻¹ * ((ψ x : ↥(unitarySU 2 f₀ K₀ 3)) : GL (Fin 3) K₀) * A
  have hψ' : ∀ x : ↥K, Ψ ⟨x, cfg.K_le x.2⟩ = subfieldGL K₀ 3 (ψ' x) := by
    intro x
    have h1 := psiK_spec pre cfg.K_le htrK x
    rw [hΨx, ← h1]
    simp only [ψ', map_mul, map_inv]
    rfl
  have hUconj : ∀ y ∈ unitarySU 2 f₀ K₀ 3, A⁻¹ * y * A ∈ unitarySU 2 f₀ K₀ 3 := by
    intro y hy
    rw [unitarySU_eq_gramSU h₀ 3] at hy ⊢
    have := conj_mem_gramSU h₀ 1 (inv_mem hA) hy
    simpa using this
  have hUconj' : ∀ y ∈ unitarySU 2 f₀ K₀ 3, A * y * A⁻¹ ∈ unitarySU 2 f₀ K₀ 3 := by
    intro y hy
    rw [unitarySU_eq_gramSU h₀ 3] at hy ⊢
    exact conj_mem_gramSU h₀ 1 hA hy
  have hsurj : ∀ u ∈ unitarySU 2 f₀ K₀ 3, ∃ x : ↥K, ψ' x = u := by
    intro u hu
    refine ⟨ψ.symm ⟨A * u * A⁻¹, hUconj' u hu⟩, ?_⟩
    simp only [ψ', MulEquiv.apply_symm_apply]
    group
  have hψ'U : ∀ x : ↥K, ψ' x ∈ unitarySU 2 f₀ K₀ 3 := fun x => hUconj _ (ψ x).2
  have hαφ : ∀ x : ↥K, α (φ x) = ψ x := fun x => by simp [α]
  have hiffJ : ∀ (a b : Fin 3) (hab : a ≠ b) (x : ↥K), (x : G) ∈ J a b ↔ ψ' x ∈ blk h₀ hab := by
    intro a b hab x
    rw [(hJ a b hab).2 x, hAblk a b hab (φ x), hαφ, mem_map_conj_iff]
  have hiffB : ∀ x : ↥K, (x : G) ∈ BK ↔ ψ' x ∈ torusSU 5 3 K₀ := by
    intro x
    rw [hBK x, hAtor (φ x), hαφ, mem_map_conj_iff]
  have trK : tr I Ψ K = (unitarySU 2 f₀ K₀ 3).map (subfieldGL K₀ 3) :=
    tr_eq_map (subfieldGL K₀ 3) cfg.K_le le_rfl ψ' hψ' hsurj le_rfl
      (fun x => ⟨fun _ => hψ'U x, fun _ => x.2⟩)
  have trB : tr I Ψ BK = Bst K₀ :=
    tr_eq_map (subfieldGL K₀ 3) cfg.K_le hBKle ψ' hψ' hsurj (torusSU_le_unitarySU h₀ cfg.dvd5)
      hiffB
  have trJ : ∀ (a b : Fin 3) (hab : a ≠ b), tr I Ψ (J a b) = Jst K₀ h₀ hab := fun a b hab =>
    tr_eq_map (subfieldGL K₀ 3) cfg.K_le (hJ a b hab).1 ψ' hψ' hsurj
      (blk_le_unitarySU (h := h₀) hab) (hiffJ a b hab)
  refine ⟨⟨pre.F, pre.hF, pre.σ, K₀, h₀, Ψ, (MulAut.conj (subfieldGL K₀ 3 A)⁻¹).injective.comp
    pre.Ψ_inj, hΨrange, pre.σ_order, fun x => Iff.rfl, hbar, hΨc, trK, trB, trJ⟩⟩

end Exist

end CFSG.RankThree.PartOne.CTP
