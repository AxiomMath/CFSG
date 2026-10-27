module

public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofWeights
public import CFSG.LieType.Ree.SuzukiUnipotentStructure
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
import CFSG.RankThree.PartTwo.EightActionSmallFixedSpace
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Matrix CFSG.Blueprint CFSG.LieType.Ree

section EightLinear

variable {K : Type} [Field K] [Finite K]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem false_of_elemAbelian_eight (h2 : (2 : K) ≠ 0) {E : Subgroup (GL (Fin 3) K)}
    (hE : CFSG.Assembly.IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1) : False := by
  classical
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => hE.1.is_comm.comm a b }
  have hA2 : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow, hE.2 a a.2, Subgroup.coe_one])
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [hA2]
  let ρ : Representation K E (Fin 3 → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] _).toAlgHom.toRingHom.toMonoidHom.comp
      ((Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp E.subtype)
  have hρ : ∀ a : E, ρ a = Matrix.toLin' ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    fun _ => rfl
  have hinj : Function.Injective ρ := by
    intro a b hab
    rw [hρ, hρ] at hab
    exact Subtype.ext (Units.ext (Matrix.toLin'.injective hab))
  have hfix : ∀ a : E, a ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ a) 1) ≤ 2 := by
    intro a ha
    have hne : Module.End.eigenspace (ρ a) 1 ≠ ⊤ := by
      intro htop
      apply ha
      apply hinj
      rw [map_one]
      apply LinearMap.ext
      intro v
      have hv : v ∈ Module.End.eigenspace (ρ a) 1 := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv
      rw [hv, Module.End.one_apply]
    have h1 := Submodule.finrank_lt hne
    rw [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨-, -, -, -, -, -, -, ⟨a₀, ha₀, -⟩, -⟩ :=
    CFSG.RankThree.PartTwo.eight_action_small_fixed_space hE8 h2 ρ hinj hfix
  have hmat : ((a₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = -1 := by
    apply Matrix.toLin'.injective
    rw [← hρ, ha₀, map_neg, Matrix.toLin'_one]
    rfl
  have h1 := hdet a₀ a₀.2
  rw [hmat, Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at h1
  apply h2
  have : (-1 : K) ^ 3 * 1 = -1 := by ring
  rw [this] at h1
  linear_combination -h1

end EightLinear

section Elements

variable {a : ℕ} {F : Type} [Field F] [Finite F]

@[expose] def s₂ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1]

@[expose] def t₂ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 1, 0, 1]

@[expose] def w₂ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem tw₂_pow_five : (t₂ * w₂) ^ 5 = 1 := by decide

theorem tw₂_ne_one : t₂ * w₂ ≠ 1 := by decide

theorem s₂_mul_tw₂ : s₂ * (t₂ * w₂) = (t₂ * w₂) ^ 2 * s₂ := by decide


@[expose] noncomputable def iota (hF : Nat.card F = 2 ^ (2 * a + 1)) : ZMod 2 →+* F :=
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (suzuki_frob_data a hF).1
  ZMod.castHom (dvd_refl 2) F

theorem iota_injective (hF : Nat.card F = 2 ^ (2 * a + 1)) : Function.Injective (iota hF) :=
  (iota hF).injective

theorem coe_suzukiSElt_one_zero (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    (((suzukiSElt a F 1 0 : suzukiGroup a F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      s₂.map (iota hF) := by
  rw [coe_suzukiSElt, suzukiS_eq_explicit (1 : F) 0 1 0 (one_pow _) (zero_pow (by positivity))]
  have h1 : iota hF 1 = 1 := map_one _
  have h0 : iota hF 0 = 0 := map_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s₂, h1, h0]

theorem coe_suzukiSElt_zero_one (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    (((suzukiSElt a F 0 1 : suzukiGroup a F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      t₂.map (iota hF) := by
  rw [coe_suzukiSElt, suzukiS_eq_explicit (0 : F) 1 0 1 (zero_pow (by positivity)) (one_pow _)]
  have h1 : iota hF 1 = 1 := map_one _
  have h0 : iota hF 0 = 0 := map_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t₂, h1, h0]

theorem coe_suzukiWElt_eq (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    (((suzukiWElt a F : suzukiGroup a F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      w₂.map (iota hF) := by
  rw [coe_suzukiWElt, suzukiW_eq]
  have h1 : iota hF 1 = 1 := map_one _
  have h0 : iota hF 0 = 0 := map_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w₂, h1, h0]

theorem suzuki_order_five_conj (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    ∃ y g : suzukiGroup a F, y ^ 5 = 1 ∧ y ≠ 1 ∧ g * y * g⁻¹ = y ^ 2 := by
  set ι := iota hF with hι
  obtain ⟨y, hy⟩ : ∃ y : suzukiGroup a F, y = suzukiSElt a F 0 1 * suzukiWElt a F := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : suzukiGroup a F, g = suzukiSElt a F 1 0 := ⟨_, rfl⟩
  have hymat : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (t₂ * w₂).map ι := by
    rw [hy, Subgroup.coe_mul, Units.val_mul, coe_suzukiSElt_zero_one hF, coe_suzukiWElt_eq hF,
      Matrix.map_mul]
  have hgmat : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = s₂.map ι := by
    rw [hg]
    exact coe_suzukiSElt_one_zero hF
  have hpow : ∀ n : ℕ, (((y ^ n : suzukiGroup a F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((t₂ * w₂) ^ n).map ι := by
    intro n
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hymat]
    exact (map_pow ι.mapMatrix (t₂ * w₂) n).symm
  have hext : ∀ x x' : suzukiGroup a F,
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((x' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) → x = x' :=
    fun x x' h => Subtype.ext (Units.ext h)
  refine ⟨y, g, ?_, ?_, ?_⟩
  · apply hext
    rw [hpow, tw₂_pow_five, Subgroup.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero ι) (map_one ι)
  · intro h1
    apply tw₂_ne_one
    have h2 := congrArg (fun x : suzukiGroup a F =>
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h1
    simp only [Subgroup.coe_one, Units.val_one] at h2
    rw [hymat, ← Matrix.map_one ι (map_zero ι) (map_one ι)] at h2
    exact Matrix.map_injective (iota_injective hF) h2
  · rw [mul_inv_eq_iff_eq_mul]
    apply hext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hgmat, hymat, hpow,
      ← Matrix.map_mul, ← Matrix.map_mul, s₂_mul_tw₂]

theorem elemAbelian_eight_le_suzukiGroup (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    ∃ E : Subgroup (suzukiGroup a F), CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h2, -⟩ := suzuki_frob_data a hF
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  let φ : Multiplicative F →* suzukiGroup a F :=
    { toFun := fun v => suzukiSElt a F 0 (Multiplicative.toAdd v)
      map_one' := suzukiSElt_zero_zero hF
      map_mul' := fun v w => by
        rw [suzukiSElt_mul hF]
        congr 1 <;> simp [zero_pow hθ0] }
  have hφ : Function.Injective φ := fun v w h =>
    Multiplicative.toAdd.injective ((suzukiSElt_inj.mp h).2)
  have hcard : Nat.card (Multiplicative F) = 2 ^ (2 * a + 1) := hF
  have hdvd : 2 ^ 3 ∣ Nat.card (Multiplicative F) := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨E₀.map φ, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨u, -, hu⟩ := x.2
    obtain ⟨w, -, hw⟩ := y.2
    change (x : suzukiGroup a F) * y = y * x
    rw [← hu, ← hw, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨u, -, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, ← two_mul, h2, zero_mul]
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hφ, hE₀]
    norm_num

end Elements

theorem false_of_suzukiModel {K : Type} [Field K] [Finite K]
    {X : Subgroup (GL (Fin 3) K)} (hXp : Group.IsPerfect X) {p f : ℕ}
    (hSz : SuzukiModel X p f) : False := by
  classical
  obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hSz
  rw [hf] at hF
  have hdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro x hx
    have h1 := Sec6.BThreeCensus.map_eq_one_of_isPerfect hXp
      (Matrix.GeneralLinearGroup.det.comp X.subtype) ⟨x, hx⟩
    have h2 := congrArg Units.val h1
    simpa using h2
  by_cases h2 : (2 : K) = 0
  ·
    obtain ⟨y, g, hy5, hy1, hg⟩ := suzuki_order_five_conj (a := a) hF
    have h5 : (5 : K) ≠ 0 := by
      have : (5 : K) = 2 * 2 + 1 := by norm_num
      rw [this, h2, mul_zero, zero_add]
      exact one_ne_zero
    refine false_of_order_five (y := ((e.symm y : X) : GL (Fin 3) K))
      (g := ((e.symm g : X) : GL (Fin 3) K)) ?_ ?_ h5 ?_
    · rw [← Subgroup.coe_pow, ← map_pow, hy5, map_one, Subgroup.coe_one]
    · intro h
      apply hy1
      apply e.symm.injective
      rw [map_one]
      exact Subtype.ext h
    · rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
        ← map_mul, hg, map_pow, Subgroup.coe_pow]
  ·
    obtain ⟨E, hE, hE8⟩ := elemAbelian_eight_le_suzukiGroup ha hF
    set E' : Subgroup (GL (Fin 3) K) := (E.map e.symm.toMonoidHom).map X.subtype with hE'
    have hinj : Function.Injective (X.subtype.comp e.symm.toMonoidHom) :=
      X.subtype_injective.comp e.symm.injective
    refine false_of_elemAbelian_eight h2 (E := E') ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩ ?_ ?_
    · obtain ⟨_, ⟨u, hu, rfl⟩, hx⟩ := x.2
      obtain ⟨_, ⟨w, hw, rfl⟩, hy⟩ := y.2
      change (x : GL (Fin 3) K) * y = y * x
      rw [← hx, ← hy]
      have huw : u * w = w * u := congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, huw]
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [← Subgroup.coe_pow, ← map_pow, hE.2 u hu, map_one, Subgroup.coe_one]
    · rw [hE', Subgroup.map_map, Subgroup.card_map_of_injective hinj, hE8]
    · rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
      exact hdet _ (e.symm u).2

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
