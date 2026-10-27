module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA8
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv Equiv.Perm Item434AltPerm Res423Two
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

@[expose] noncomputable def castGF2 : ZMod 2 →+* GaloisField 2 1 := ZMod.castHom (dvd_refl 2) _

@[expose] noncomputable def a8ToSL : alternatingGroup (Fin 8) →* SL(4, GaloisField 2 1) :=
  (Matrix.SpecialLinearGroup.map castGF2).comp
    ((CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm).toMonoidHom)

theorem a8ToSL_injective : Function.Injective a8ToSL := by
  intro a b h
  have hmap : Function.Injective
      (Matrix.SpecialLinearGroup.map castGF2 : SL(4, ZMod 2) →* SL(4, GaloisField 2 1)) := by
    intro x y hxy
    apply Subtype.ext
    have h' := congrArg (fun m : SL(4, GaloisField 2 1) =>
      (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 1))) hxy
    exact Matrix.map_injective castGF2.injective h'
  rw [a8ToSL, MonoidHom.coe_comp] at h
  exact (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm).injective (hmap h)

theorem card_SL_four_gf2 :
    Nat.card SL(4, GaloisField 2 1) = Nat.card (alternatingGroup (Fin 8)) := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero,
    nat_card_alternatingGroup, Nat.card_fin]
  decide

@[expose] noncomputable def a8EquivSL : alternatingGroup (Fin 8) ≃* SL(4, GaloisField 2 1) :=
  MulEquiv.ofBijective a8ToSL (a8ToSL_injective.bijective_of_nat_card_le card_SL_four_gf2.le)

@[expose] noncomputable def a8EquivProjSL :
    alternatingGroup (Fin 8) ≃* projSL 4 (GaloisField 2 1) :=
  a8EquivSL.trans (Item434SmallTwoOther.slEquivProjSL (by norm_num))

@[expose] def r8 : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5 * swap 4 5

@[expose] def s8 : Perm (Fin 8) := swap 0 1 * swap 6 7

@[expose] def t4 : Fin 4 → Perm (Fin 8) := ![c1 8, c1 8 ^ 2, c2 8, c2 8 ^ 2]

@[expose] def w8 (k : Fin 4) (l : Fin 2) : Perm (Fin 8) := r8 ^ (k : ℕ) * s8 ^ (l : ℕ)

theorem rs_spec : sign r8 = 1 ∧ sign s8 = 1 ∧ r8 * c1 8 * r8⁻¹ = c2 8 ∧
    r8 * c2 8 * r8⁻¹ = (c1 8)⁻¹ ∧ s8 * c1 8 * s8⁻¹ = (c1 8)⁻¹ ∧ s8 * c2 8 * s8⁻¹ = c2 8 ∧
    r8 ^ 4 = 1 ∧ s8 ^ 2 = 1 := by
  decide +kernel

theorem srs_spec : (s8 * r8 * s8⁻¹) * c1 8 * (s8 * r8 * s8⁻¹)⁻¹ = r8⁻¹ * c1 8 * (r8⁻¹)⁻¹ ∧
    (s8 * r8 * s8⁻¹) * c2 8 * (s8 * r8 * s8⁻¹)⁻¹ = r8⁻¹ * c2 8 * (r8⁻¹)⁻¹ := by
  decide +kernel

theorem r_pow_spec : r8 ^ 2 * c1 8 * (r8 ^ 2)⁻¹ ≠ c1 8 ∧
    ∀ k : Fin 4, ¬ (r8 ^ (k : ℕ) * c1 8 * (r8 ^ (k : ℕ))⁻¹ = s8 * c1 8 * s8⁻¹ ∧
      r8 ^ (k : ℕ) * c2 8 * (r8 ^ (k : ℕ))⁻¹ = s8 * c2 8 * s8⁻¹) := by
  decide +kernel

theorem threeCycle_cases : ∀ v : Fin 2 → ZMod 3, (vecPerm2 8 v).support.card = 3 →
    ∃ i : Fin 4, vecPerm2 8 v = t4 i := by
  decide +kernel

theorem words_cover : ∀ i j : Fin 4, t4 j ≠ t4 i → t4 j ≠ t4 i ^ 2 →
    ∃ k : Fin 4, ∃ l : Fin 2, w8 k l * c1 8 * (w8 k l)⁻¹ = t4 i ∧
      w8 k l * c2 8 * (w8 k l)⁻¹ = t4 j := by
  decide +kernel

theorem c_spec : c2 8 ≠ c1 8 ∧ c2 8 ≠ c1 8 ^ 2 ∧ (c1 8).support.card = 3 ∧
    (c2 8).support.card = 3 := by
  decide +kernel

@[expose] def c1F : F08 :=
  ⟨⟨c1 8, signs_eight.1⟩, Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))⟩

@[expose] def c2F : F08 :=
  ⟨⟨c2 8, signs_eight.2.1⟩, Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩

theorem mem_normalizer_F08 {g : alternatingGroup (Fin 8)}
    (h1 : (g : Perm (Fin 8)) * c1 8 * (g : Perm (Fin 8))⁻¹ ∈ F0 8)
    (h2 : (g : Perm (Fin 8)) * c2 8 * (g : Perm (Fin 8))⁻¹ ∈ F0 8) :
    g ∈ Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8))) := by
  have hle : F0 8 ≤ (F0 8).comap (MulAut.conj (g : Perm (Fin 8))).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    · exact h1
    · exact h2
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' : (x : Perm (Fin 8)) ∈ F0 8 := Subgroup.mem_subgroupOf.mp hx
  exact Subgroup.mem_subgroupOf.mpr (hle hx')

@[expose] def rN : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8))) :=
  ⟨⟨r8, rs_spec.1⟩, mem_normalizer_F08 (by
    change r8 * c1 8 * r8⁻¹ ∈ F0 8
    rw [rs_spec.2.2.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (by
    change r8 * c2 8 * r8⁻¹ ∈ F0 8
    rw [rs_spec.2.2.2.1]
    exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))⟩

@[expose] def sN : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8))) :=
  ⟨⟨s8, rs_spec.2.1⟩, mem_normalizer_F08 (by
    change s8 * c1 8 * s8⁻¹ ∈ F0 8
    rw [rs_spec.2.2.2.2.1]
    exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) (by
    change s8 * c2 8 * s8⁻¹ ∈ F0 8
    rw [rs_spec.2.2.2.2.2.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩

@[expose] noncomputable def rho : MulAut F08 := F08.normalizerMonoidHom rN

@[expose] noncomputable def sigma : MulAut F08 := F08.normalizerMonoidHom sN

theorem nmh_apply (h : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8)))) (x : F08) :
    (((F08.normalizerMonoidHom h x : F08) : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      ((h : alternatingGroup (Fin 8)) : Perm (Fin 8)) * ((x : alternatingGroup (Fin 8)) :
        Perm (Fin 8)) * ((h : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ :=
  rfl

theorem nmh_eq (h₁ h₂ : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8))))
    (ha : ((h₁ : alternatingGroup (Fin 8)) : Perm (Fin 8)) * c1 8 *
        ((h₁ : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ =
      ((h₂ : alternatingGroup (Fin 8)) : Perm (Fin 8)) * c1 8 *
        ((h₂ : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹)
    (hb : ((h₁ : alternatingGroup (Fin 8)) : Perm (Fin 8)) * c2 8 *
        ((h₁ : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ =
      ((h₂ : alternatingGroup (Fin 8)) : Perm (Fin 8)) * c2 8 *
        ((h₂ : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹) :
    F08.normalizerMonoidHom h₁ = F08.normalizerMonoidHom h₂ := by
  set a : Perm (Fin 8) := ((h₁ : alternatingGroup (Fin 8)) : Perm (Fin 8)) with ha'
  set b : Perm (Fin 8) := ((h₂ : alternatingGroup (Fin 8)) : Perm (Fin 8)) with hb'
  have hk : ∀ y : Perm (Fin 8), a * y * a⁻¹ = b * y * b⁻¹ ↔ y * (b⁻¹ * a) = (b⁻¹ * a) * y := by
    intro y
    constructor
    · intro h
      calc y * (b⁻¹ * a) = b⁻¹ * (b * y * b⁻¹) * a := by group
        _ = b⁻¹ * (a * y * a⁻¹) * a := by rw [h]
        _ = (b⁻¹ * a) * y := by group
    · intro h
      calc a * y * a⁻¹ = b * ((b⁻¹ * a) * y) * a⁻¹ := by group
        _ = b * (y * (b⁻¹ * a)) * a⁻¹ := by rw [h]
        _ = b * y * b⁻¹ := by group
  have hle : F0 8 ≤ Subgroup.centralizer ({b⁻¹ * a} : Set (Perm (Fin 8))) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact (hk _).mp ha
    · exact (hk _).mp hb
  refine MulEquiv.ext fun x => Subtype.ext (Subtype.ext ?_)
  rw [nmh_apply, nmh_apply]
  have hx : ((x : alternatingGroup (Fin 8)) : Perm (Fin 8)) ∈ F0 8 :=
    Subgroup.mem_subgroupOf.mp x.2
  exact (hk _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hle hx))

theorem rho_mem : rho ∈ autIn ⊤ F08 :=
  mem_autIn_iff.mpr ⟨_, rN.2, Subgroup.mem_top _, rfl⟩

theorem sigma_mem : sigma ∈ autIn ⊤ F08 :=
  mem_autIn_iff.mpr ⟨_, sN.2, Subgroup.mem_top _, rfl⟩

theorem coe_rN_pow (k : ℕ) :
    (((rN ^ k : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8)))) :
      alternatingGroup (Fin 8)) : Perm (Fin 8)) = r8 ^ k := by
  simp [rN]

theorem coe_sN_pow (k : ℕ) :
    (((sN ^ k : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8)))) :
      alternatingGroup (Fin 8)) : Perm (Fin 8)) = s8 ^ k := by
  simp [sN]

theorem coe_w (k : Fin 4) (l : Fin 2) :
    (((rN ^ (k : ℕ) * sN ^ (l : ℕ) : Subgroup.normalizer (F08 : Set (alternatingGroup (Fin 8))))
      : alternatingGroup (Fin 8)) : Perm (Fin 8)) = w8 k l := by
  simp [w8, rN, sN]

theorem mem_autIn_F08 {φ : MulAut F08} (hφ : φ ∈ autIn ⊤ F08) :
    ∃ k : Fin 4, ∃ l : Fin 2, φ = rho ^ (k : ℕ) * sigma ^ (l : ℕ) := by
  obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hφ
  set g' : Perm (Fin 8) := (g : Perm (Fin 8)) with hg'
  have himg : ∀ c : F08, (c : Perm (Fin 8)).support.card = 3 →
      ∃ i : Fin 4, g' * (c : Perm (Fin 8)) * g'⁻¹ = t4 i := by
    intro c hc
    have hmem : g * (c : alternatingGroup (Fin 8)) * g⁻¹ ∈ F08 :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp c.2
    have hmem' : g' * (c : Perm (Fin 8)) * g'⁻¹ ∈ F0 8 := Subgroup.mem_subgroupOf.mp hmem
    rw [F0_eq_range f0Facts_eight] at hmem'
    obtain ⟨v, hv⟩ := hmem'
    change vecPerm2 8 (Multiplicative.toAdd v) = g' * (c : Perm (Fin 8)) * g'⁻¹ at hv
    have hcard : (vecPerm2 8 (Multiplicative.toAdd v)).support.card = 3 := by
      rw [hv, card_support_conj]
      exact hc
    obtain ⟨i, hi⟩ := threeCycle_cases _ hcard
    exact ⟨i, hv ▸ hi⟩
  obtain ⟨i, hi⟩ := himg c1F c_spec.2.2.1
  obtain ⟨j, hj⟩ := himg c2F c_spec.2.2.2
  change g' * c1 8 * g'⁻¹ = t4 i at hi
  change g' * c2 8 * g'⁻¹ = t4 j at hj
  have hji : t4 j ≠ t4 i := by
    intro h
    apply c_spec.1
    have h1 : g' * c2 8 * g'⁻¹ = g' * c1 8 * g'⁻¹ := by rw [hi, hj, h]
    simpa using h1
  have hji2 : t4 j ≠ t4 i ^ 2 := by
    intro h
    apply c_spec.2.1
    have h1 : g' * c2 8 * g'⁻¹ = g' * c1 8 ^ 2 * g'⁻¹ := by
      rw [hj, h, ← hi, conj_pow]
    simpa using h1
  obtain ⟨k, l, hk1, hk2⟩ := words_cover i j hji hji2
  refine ⟨k, l, ?_⟩
  rw [rho, sigma, ← map_pow, ← map_pow, ← map_mul]
  refine nmh_eq _ _ ?_ ?_
  · rw [coe_w, hk1]
    exact hi
  · rw [coe_w, hk2]
    exact hj

theorem rho_pow_four : rho ^ 4 = 1 := by
  have h : rN ^ 4 = 1 := Subtype.ext (Subtype.ext (by
    rw [coe_rN_pow, rs_spec.2.2.2.2.2.2.1]
    rfl))
  rw [rho, ← map_pow, h, map_one]

theorem rho_sq_ne_one : rho ^ 2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : MulAut F08 =>
    (((φ c1F : F08) : alternatingGroup (Fin 8)) : Perm (Fin 8))) h
  simp only [MulAut.one_apply] at h1
  rw [rho, ← map_pow, nmh_apply] at h1
  exact r_pow_spec.1 (by simpa [rN, c1F] using h1)

theorem orderOf_rho : orderOf rho = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : rho ^ 2 ^ (1 + 1) = 1 := rho_pow_four
  have h2 : ¬ rho ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact rho_sq_ne_one
  exact orderOf_eq_prime_pow h2 h4

theorem sigma_sq : sigma ^ 2 = 1 := by
  have h : sN ^ 2 = 1 := Subtype.ext (Subtype.ext (by
    rw [coe_sN_pow, rs_spec.2.2.2.2.2.2.2]
    rfl))
  rw [sigma, ← map_pow, h, map_one]

theorem sigma_rho_sigma : sigma * rho * sigma⁻¹ = rho⁻¹ := by
  rw [rho, sigma, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  refine nmh_eq _ _ ?_ ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact srs_spec.1
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact srs_spec.2

theorem sigma_not_mem : sigma ∉ Subgroup.zpowers rho := by
  classical
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_rho] at h
  obtain ⟨k, hk, hks⟩ := Finset.mem_image.mp h
  have hk4 : k < 4 := Finset.mem_range.mp hk
  have h1 := congrArg (fun φ : MulAut F08 =>
    (((φ c1F : F08) : alternatingGroup (Fin 8)) : Perm (Fin 8))) hks
  have h2 := congrArg (fun φ : MulAut F08 =>
    (((φ c2F : F08) : alternatingGroup (Fin 8)) : Perm (Fin 8))) hks
  rw [rho, sigma, ← map_pow, nmh_apply, nmh_apply, coe_rN_pow] at h1 h2
  exact r_pow_spec.2 ⟨k, hk4⟩ ⟨h1, h2⟩

theorem nonempty_autIn_F08 : Nonempty (autIn ⊤ F08 ≃* DihedralGroup 4) := by
  set ρ' : autIn ⊤ F08 := ⟨rho, rho_mem⟩
  set σ' : autIn ⊤ F08 := ⟨sigma, sigma_mem⟩
  have hgen : (⊤ : Subgroup (autIn ⊤ F08)) = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    obtain ⟨k, l, hkl⟩ := mem_autIn_F08 x.2
    have hx : x = ρ' ^ (k : ℕ) * σ' ^ (l : ℕ) := Subtype.ext (by simpa [ρ', σ'] using hkl)
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers _)) _) (Subgroup.pow_mem _ (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers _)) _)
  have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simpa [σ'] using sigma_sq)
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := Subtype.ext (by simpa [σ', ρ'] using sigma_rho_sigma)
  have hσρ : σ' ∉ Subgroup.zpowers ρ' := by
    intro h
    apply sigma_not_mem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa [ρ', σ'] using congrArg Subtype.val hn⟩
  have hord : orderOf ρ' = 4 := by
    rw [← orderOf_rho]
    exact Subgroup.orderOf_mk rho rho_mem
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rw [hord] at e
  exact ⟨e⟩

theorem nonempty_autIn_alt8 {D : Subgroup (alternatingGroup (Fin 8))} (hD9 : Nat.card D = 9) :
    Nonempty (autIn ⊤ D ≃* DihedralGroup 4) := by
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine factorization_card_alt8 hD9 card_F08
  have f2 := Sporadic.autInTopCongr (MulAut.conj g) D
  rw [show D.map (MulAut.conj g : alternatingGroup (Fin 8) ≃*
    alternatingGroup (Fin 8)).toMonoidHom = F08 from hg] at f2
  obtain ⟨e⟩ := nonempty_autIn_F08
  exact ⟨f2.trans e⟩

theorem k417OutA8_holds : Res417Three.K417OutA8 :=
  ⟨⟨a8EquivProjSL⟩, fun _ _ hD9 => nonempty_autIn_alt8 hD9⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Four
