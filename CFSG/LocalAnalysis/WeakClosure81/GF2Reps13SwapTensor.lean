module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapTensorB
public import CFSG.RankThree.PartOne.S15K.SL2Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem natTensor_of_secMatTensor {K K' : Subgroup (MulAut W)} {U₀ U R : Subgroup W}
    (hKs : K ≤ secStabAll U U₀) (hK's : K' ≤ secStabAll U U₀) (hcomm : ⁅K, K'⁆ = ⊥) (hRU : R ≤ U)
    (hRst : StableUnder (K ⊔ K') R) (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U)
    (hKf : K ⊓ centSub R = ⊥) (hK'f : K' ⊓ centSub R = ⊥) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h : IsMatTensor2 (secImg K U U₀) (secImg K' U U₀) F) :
    NatTensor (K ⊔ K') R ⊥ 2 n := by
  refine ⟨F, ‹Field F›, ‹Finite F›, hF, ?_⟩
  exact w16f_isMatTensor2_realizes (F := F) (n := n) hKs hK's hcomm hRU hRst hinf hsup hKf hK'f
    hF h

theorem isL2_of_secMatTensor {K K' : Subgroup (MulAut W)} {U₀ U R : Subgroup W}
    (hKs : K ≤ secStabAll U U₀) (hK's : K' ≤ secStabAll U U₀) (hRU : R ≤ U)
    (hRst : StableUnder K R) (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U)
    (hKf : K ⊓ centSub R = ⊥) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (h : IsMatTensor2 (secImg K U U₀) (secImg K' U U₀) F) :
    UC22.IsL2 ↥K n := by
  classical
  obtain ⟨φ₁, -, -, -, -⟩ := h
  let ρ : ↥K ≃* ↥(secImg K U U₀) := w16f_secImgEquiv K U U₀ R hKs hRst hRU hinf hKf
  let e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F := ρ.trans φ₁
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨eP⟩ := CFSG.RankThree.PartOne.S15K.nonempty_sl2_mulEquiv_statedProj (F := F)
  refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ?_⟩
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans eP⟩⟩
  · intro hpow
    have h2 : 2 ^ n = 2 := congrArg Prod.snd hpow
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · intro hpow
    have h3 : 2 ^ n = 3 := congrArg Prod.snd hpow
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

end CFSG.LocalAnalysis.WeakClosure81
