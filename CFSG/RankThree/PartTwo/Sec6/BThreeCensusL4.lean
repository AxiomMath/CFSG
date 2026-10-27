module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Odd
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

section Frobenius

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem eigenProj_map (τ : K →+* K) {g : Matrix n n K} (hg : g.map τ = g) (c : K) :
    (eigenProj g c).map τ = eigenProj g (τ c) := by
  have h2 : (g ^ 2).map τ = g ^ 2 := by
    rw [show (g ^ 2).map τ = τ.mapMatrix (g ^ 2) from rfl, map_pow]
    exact congrArg (· ^ 2) hg
  ext i j
  have hgij : τ (g i j) = g i j := congrFun (congrFun hg i) j
  have hg2ij : τ ((g ^ 2) i j) = (g ^ 2) i j := congrFun (congrFun h2 i) j
  by_cases hij : i = j
  · subst hij
    simp [eigenProj, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hgij,
      hg2ij]
  · simp [eigenProj, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hgij,
      hg2ij, hij]

theorem finrank_range_eigenProj_le_map (τ : K →+* K) (hτ : Function.Surjective τ)
    {g : Matrix n n K} (hg : g.map τ = g) (c : K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g c))) ≤
      Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g (τ c)))) := by
  set E := LinearMap.range (Matrix.toLin' (eigenProj g c)) with hE
  set E' := LinearMap.range (Matrix.toLin' (eigenProj g (τ c))) with hE'
  have hmem : ∀ v ∈ E, (fun i => τ (v i)) ∈ E' := by
    rintro _ ⟨w, rfl⟩
    refine ⟨fun i => τ (w i), ?_⟩
    funext i
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← eigenProj_map τ hg c]
    exact (RingHom.map_mulVec τ (eigenProj g c) w i).symm
  let j : E →+ E' :=
    { toFun := fun v => ⟨fun i => τ ((v : n → K) i), hmem v v.2⟩
      map_zero' := by
        apply Subtype.ext
        funext i
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        funext i
        simp }
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hab) i
    exact τ.injective this
  have hle := rank_le_of_surjective_injective τ j hτ hj (fun r m => by
    apply Subtype.ext
    funext i
    simp [j])
  exact Module.finrank_le_finrank_of_rank_le_rank (by simpa using hle) (Module.rank_lt_aleph0 _ _)

end Frobenius

theorem eq_bot_of_commute_of_card_mod_three {F : Type} [Field F]
    [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p) (hp : p % 3 = 2)
    {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n ≤ 4) {g : GL n F}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (Y : Subgroup (GL n F)) (hYg : ∀ y ∈ Y, y * g = g * y)
    (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  obtain ⟨K, _, _, φ, ω, hω⟩ := exists_splittingField_cubeRoot F
  have : CharP K p := charP_of_injective_ringHom φ.injective p
  have h3F : (3 : F) ≠ 0 := three_ne_zero_of_charP (by omega)
  have h3K := three_ne_zero_map φ h3F
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h3K
    linear_combination hω
  set τ : K →+* K := frobenius K p with hτ
  have hτs : Function.Surjective τ := Finite.injective_iff_surjective.mp τ.injective
  set g' : Matrix n n K := (g : Matrix n n F).map φ with hg'
  have hg'τ : g'.map τ = g' := by
    have : Fintype F := Fintype.ofFinite F
    ext i j
    simp only [hg', Matrix.map_apply, hτ, frobenius_def]
    rw [← map_pow]
    congr 1
    have h := FiniteField.pow_card ((g : Matrix n n F) i j)
    rwa [← Nat.card_eq_fintype_card, hF] at h
  have hg'3 : g' ^ 3 = 1 := by
    rw [hg', show (g : Matrix n n F).map φ =
        ((Matrix.GeneralLinearGroup.map φ g : GL n K) : Matrix n n K) from rfl,
      ← Units.val_pow_eq_pow_val, ← map_pow, hg3, map_one, Units.val_one]
  have hτω : τ ω = ω ^ 2 := by
    rw [hτ, frobenius_def, ← Nat.div_add_mod p 3, hp, pow_add, pow_mul, hω3, one_pow, one_mul]
  have hτω2 : τ (ω ^ 2) = ω := by
    rw [map_pow, hτω, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hω3, one_mul, pow_one]
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  set E : K → Submodule K (n → K) := fun c => LinearMap.range (Matrix.toLin' (eigenProj g' c))
    with hE
  have hEω : Module.finrank K (E ω) = Module.finrank K (E (ω ^ 2)) := by
    refine le_antisymm ?_ ?_
    · have h := finrank_range_eigenProj_le_map τ hτs hg'τ ω
      rwa [hτω] at h
    · have h := finrank_range_eigenProj_le_map τ hτs hg'τ (ω ^ 2)
      rwa [hτω2] at h
  have hdisj : E ω ⊓ E (ω ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have h1 := mulVec_eq_of_mem_range_eigenProj hg'3 hω3 hv.1
    have h2 := mulVec_eq_of_mem_range_eigenProj hg'3 hω23 hv.2
    have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
    rw [hω4, h1] at h2
    have h3 : (ω ^ 2 - ω) • v = 0 := by rw [sub_smul, h2, sub_self]
    have hne : ω ^ 2 - ω ≠ 0 := by
      intro h0
      have : ω * (ω - 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact hω0 h
      · exact hω1 (sub_eq_zero.mp h)
    exact (smul_eq_zero.mp h3).resolve_left hne
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (E ω) (E (ω ^ 2))
  rw [hdisj, finrank_bot] at hsup
  have hsupn : Module.finrank K ↥(E ω ⊔ E (ω ^ 2)) ≤ Fintype.card n := by
    have := Submodule.finrank_le (E ω ⊔ E (ω ^ 2))
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hker : E ω ⊔ E (ω ^ 2) ≤ LinearMap.ker (Matrix.toLin' (eigenProj g' 1)) := by
    have hk : ∀ c : K, c ^ 3 = 1 → c ^ 2 + c + 1 = 0 → E c ≤
        LinearMap.ker (Matrix.toLin' (eigenProj g' 1)) := by
      intro c hc hc0 v hv
      have h1 := mulVec_eq_of_mem_range_eigenProj hg'3 hc hv
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      have h2 : g' ^ 2 *ᵥ v = (c ^ 2) ^ 2 • v := by
        rw [sq g', ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h1, smul_smul, ← sq]
      have hc4 : (c ^ 2) ^ 2 = c := by
        calc (c ^ 2) ^ 2 = c ^ 3 * c := by ring
          _ = c := by rw [hc, one_mul]
      simp only [eigenProj, one_smul, one_pow, Matrix.add_mulVec, Matrix.one_mulVec, h1, h2, hc4]
      rw [← one_smul K v, smul_smul, smul_smul, ← add_smul, ← add_smul, mul_one, mul_one]
      rw [show (1 : K) + c ^ 2 + c = c ^ 2 + c + 1 by ring, hc0, zero_smul]
    exact sup_le (hk ω hω3 hω) (hk (ω ^ 2) hω23 (by linear_combination (ω ^ 2 - ω + 1) * hω))
  have hkerle := Submodule.finrank_mono hker
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (eigenProj g' 1))
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  change Module.finrank K (E 1) + _ = _ at hrank
  have hpos : 1 ≤ Module.finrank K (E ω) := by
    by_contra h0
    push Not at h0
    have h0' : Module.finrank K (E (ω ^ 2)) = 0 := by omega
    have hz : ∀ c : K, Module.finrank K (E c) = 0 → eigenProj g' c = 0 := by
      intro c hc
      rw [Submodule.finrank_eq_zero, hE, LinearMap.range_eq_bot] at hc
      exact Matrix.toLin'.injective (by rw [hc, map_zero])
    have hP1 : eigenProj g' 1 = (3 : K) • 1 := by
      have h := eigenProj_add_add hω g'
      rwa [hz ω (by omega), hz (ω ^ 2) h0', add_zero, add_zero] at h
    have h1 := mul_eigenProj hg'3 (c := 1) (one_pow 3)
    rw [one_pow, one_smul, hP1, Matrix.mul_smul, mul_one] at h1
    have h2 : g' = 1 := by
      have := congrArg (fun M : Matrix n n K => (3 : K)⁻¹ • M) h1
      simpa only [smul_smul, inv_mul_cancel₀ h3K, one_smul] using this
    apply hg1
    apply map_gl_injective φ
    rw [map_one]
    apply Units.ext
    exact h2
  have hdim : ∀ c : K, c ^ 3 = 1 → Module.finrank K (E c) ≤ 2 := by
    intro c hc
    have hfac : (c - 1) * ((c - ω) * (c - ω ^ 2)) = 0 := by
      linear_combination (c - c ^ 2) * hω + (c - 1) * hω3 + hc
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h]
      omega
    · rcases mul_eq_zero.mp h with h' | h'
      · rw [sub_eq_zero.mp h']
        omega
      · rw [sub_eq_zero.mp h']
        omega
  exact eq_bot_of_commute_of_map h3K φ hω (g := g) hdim Y hYg hYp hY3

theorem pow_eq_one_of_mem_scalars {k : Type} [Field k] {m : ℕ}
    {z : SpecialLinearGroup (Fin m) k} (hz : z ∈ scalars m k) : z ^ m = 1 := by
  obtain ⟨c, hc, hz⟩ := hz
  have h : (z : Matrix (Fin m) (Fin m) k) ^ m = 1 := by
    rw [hz, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  exact Subtype.ext h

theorem exists_pow_three_eq_of_not_three_dvd {F : Type} [Field F] [Finite F]
    (h3 : ¬ 3 ∣ Nat.card F - 1) (d : Fˣ) : ∃ ν : Fˣ, ν ^ 3 = d := by
  have hinj : Function.Injective (fun ν : Fˣ => ν ^ 3) := by
    intro a b hab
    have h1 : (a * b⁻¹) ^ 3 = 1 := by
      rw [mul_pow, inv_pow]
      exact mul_inv_eq_one.mpr hab
    have h2 : ((a * b⁻¹ : Fˣ) : F) = 1 :=
      Sec4.eq_one_of_pow_three_eq_one h3 (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    exact mul_inv_eq_one.mp (Units.ext h2)
  exact Finite.injective_iff_surjective.mp hinj d

theorem threePrimeB3_projectiveSL_four_prime {F : Type} [Field F]
    [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p) (hp : p % 3 = 2) :
    ThreePrimeB3 (projectiveSL 4 F) := by
  have hsimple : IsSimpleGroup (projectiveSL 4 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  have hD : β ∈ linearAutGroup 4 F := by
    by_contra hD
    obtain ⟨σ, hσ3, -⟩ := linear_order_three_field_descent (by norm_num) β hβ hD
    exact orderOf_ne_three_of_card_prime Fact.out hF σ hσ3
  rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
  obtain ⟨A, rfl⟩ := hD
  obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ 3) 1
    (by rw [map_one, mul_one, map_pow, hβ])
  obtain ⟨ν, hν⟩ := exists_pow_three_eq_of_not_three_dvd (F := F) (by rw [hF]; omega) d
  set B : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) ν⁻¹ * A with hB
  have hBA : conjAut 4 F B = conjAut 4 F A := by rw [hB, map_mul, conjAut_scalar, one_mul]
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 4) ν⁻¹) A := by
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 4) ν⁻¹ ∈ Subgroup.center (GL (Fin 4) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz A).symm
  have hB3 : B ^ 3 = 1 := by
    rw [hB, hcomm.mul_pow, ← map_pow, ← hd, ← map_mul, inv_pow, hν, inv_mul_cancel, map_one]
  by_cases hB1 : B = 1
  ·
    have hβ1 : conjAut 4 F A = 1 := by rw [← hBA, hB1, map_one]
    have hCtop : C = ⊤ := by
      ext z
      simp [hC z, hβ1]
    have hsimp : IsSimpleGroup C :=
      ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
    exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
      hRs
  suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
  have : Group.IsPerfect Y := hYp
  set Ŷ := Y.comap (QuotientGroup.mk' (scalars 4 F)) with hŶ
  set D := ⁅Ŷ, Ŷ⁆ with hDdef
  have hDp : Group.IsPerfect D :=
    CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap (scalars_le_center 4 F) Y
  have hDmap : D.map (proj 4 F) = Y := CFSG.RankThree.SubgroupLists.map_commutator_comap Y
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3D
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 3 h3D
    have he3 : (e : SpecialLinearGroup (Fin 4) F) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one e
      rw [he] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hpe : proj 4 F e ∈ Y := hDmap ▸ ⟨e, e.2, rfl⟩
    have hpe1 : proj 4 F e = 1 :=
      eq_one_of_pow_three_of_not_three_dvd hY3 hpe (by rw [← map_pow, he3, map_one])
    rw [proj_eq_one_iff] at hpe1
    have he4 := pow_eq_one_of_mem_scalars hpe1
    have he1 : (e : SpecialLinearGroup (Fin 4) F) = 1 := by
      calc (e : SpecialLinearGroup (Fin 4) F) =
          (e : SpecialLinearGroup (Fin 4) F) ^ 4 * ((e : SpecialLinearGroup (Fin 4) F) ^ 3)⁻¹ := by
            group
        _ = 1 := by rw [he4, he3, inv_one, one_mul]
    rw [show e = 1 from Subtype.ext he1, orderOf_one] at he
    omega
  have hfix : ∀ y ∈ D, slConjugation 4 F B y = y := by
    refine eq_of_mul_inv_mem_center hDp (slConjugation 4 F B).toMonoidHom fun y hy => ?_
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have hyY : proj 4 F y ∈ Y := hDmap ▸ ⟨y, hy, rfl⟩
    have h1 := (hC _).mp (hYC hyY)
    rw [← hBA, conjAut_proj] at h1
    change proj 4 F (slConjugation 4 F B y) * (proj 4 F y)⁻¹ = 1
    rw [h1, mul_inv_cancel]
  set D' : Subgroup (GL (Fin 4) F) := D.map SpecialLinearGroup.toGL with hD'
  have hD'bot : D' = ⊥ := by
    refine eq_bot_of_commute_of_card_mod_three hF hp (by simp) hB3 hB1 D' ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      apply Units.ext
      have h1 := congrArg (fun z : SpecialLinearGroup (Fin 4) F =>
        (z : Matrix (Fin 4) (Fin 4) F)) (hfix y hy)
      simp only [coe_slConjugation] at h1
      change (y : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
        (B : Matrix (Fin 4) (Fin 4) F) * (y : Matrix (Fin 4) (Fin 4) F)
      calc (y : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
          (B : Matrix (Fin 4) (Fin 4) F) * (y : Matrix (Fin 4) (Fin 4) F) *
            ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (B : Matrix (Fin 4) (Fin 4) F) := by rw [h1]
        _ = (B : Matrix (Fin 4) (Fin 4) F) * (y : Matrix (Fin 4) (Fin 4) F) := by
            rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    · exact Group.IsPerfect.map _
    · rwa [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
  have hDbot : D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective D SpecialLinearGroup.toGL_injective).mp hD'bot
  rw [← hDmap, hDbot, Subgroup.map_bot]

open CFSG.Assembly.RankThreeEven (projSL) in
theorem threePrimeB3_projSL_four_prime {p : ℕ} [Fact p.Prime]
    (hp : p % 3 = 2) : ThreePrimeB3 (projSL 4 (GaloisField p 1)) := by
  obtain ⟨τ₀⟩ := nonempty_projSL_mulEquiv 4 (GaloisField p 1)
  exact threePrimeB3_of_mulEquiv τ₀ (threePrimeB3_projectiveSL_four_prime
    (by rw [GaloisField.card p 1 one_ne_zero, pow_one]) hp)

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
