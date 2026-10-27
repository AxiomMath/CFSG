module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

section Main


open CFSG.RankThree.PartOne.KE

theorem rootKernel_of_rootKill (hRK : RootKill) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (h2 : ringChar K = 2) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian p A) (h5 : p ^ 5 ≤ Nat.card A)
    (hU : TwNormTwo K σ A) (D : TwLangData K σ q A) :
    ∃ β, IsRoot TwistTag.E6.tag β ∧
      (∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        (∃ x ∈ A, rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0) ↔
          (∀ k, a k ^ p = 1) ∧ rootChar a β = 1) ∧
      (∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ, (∀ k, a k ^ p = 1) →
        rootChar a β = 1 → rootDiagUnit TwistTag.E6.tag a ∈
          twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr)) ∧
      ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, iform γ β = 0 → ∀ ζ : (AlgebraicClosure K)ˣ,
        ζ ^ p = 1 → ∃ x ∈ A, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) =
          D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (two_dvd_of_card hK h2)).mp hpq
    omega
  have hq : ((q : ℕ) : ZMod p) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  haveI : NeZero ((p : ℕ) : K) := ⟨fun h => by
    have h' := (ringChar.spec K p).1 h
    rw [h2] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h').symm⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ p :=
    ⟨_, IsPrimitiveRoot.isUnit_unit hp.ne_zero hζ0⟩
  have hr : p ^ (if p = 3 then 4 else 5) ≤ Nat.card A := by
    refine le_trans ?_ h5
    split_ifs
    · exact Nat.pow_le_pow_right hp.pos (by norm_num)
    · exact le_rfl
  obtain ⟨β, hβ, hkill⟩ := hRK K σ q hK hσ h2 p hp hpq A hAI hA hr hU D
  obtain ⟨k0, hk0⟩ := exists_intCast_ne_zero_of_isRoot hβ p
  have hlog : ∀ x ∈ A, ∃ y : Fin TwistTag.E6.tag.rank → ZMod p,
      rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((y k).val : ℤ)) =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 ∧
      ∑ k, y k * (β k : ZMod p) = 0 := by
    intro x hx
    obtain ⟨y, hy, -⟩ := exists_wkLog D hq hζ hx (hA.2 x hx)
    obtain ⟨a, ha, haβ⟩ := hkill x hx
    have hya : (fun k => ζ ^ ((y k).val : ℤ)) = a :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (hy.trans ha.symm)
    refine ⟨y, hy, (rootChar_val_eq_one_iff_wk hζ y β).1 ?_⟩
    rw [hya]
    exact haβ
  choose y hy1 hy2 using hlog
  let f : A → {z : Fin TwistTag.E6.tag.rank → ZMod p // ∑ k, z k * (β k : ZMod p) = 0} :=
    fun x => ⟨y x.1 x.2, hy2 x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x x' hxx
    have h1 : y x.1 x.2 = y x'.1 x'.2 := congrArg Subtype.val hxx
    have h3 : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x.1 * D.c⁻¹) *
        D.g0 = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x'.1 * D.c⁻¹) * D.g0 := by
      rw [← hy1 x.1 x.2, ← hy1 x'.1 x'.2, h1]
    have h4 := baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      (mul_left_cancel (mul_right_cancel h3))
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h4))
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le ((card_hyperplane_le β hk0).trans h5)
  have hmain : ∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      (∃ x ∈ A, rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0) ↔
        (∀ k, a k ^ p = 1) ∧ rootChar a β = 1 := by
    intro a
    constructor
    · rintro ⟨x, hx, hax⟩
      have ha : a = fun k => ζ ^ ((y x hx k).val : ℤ) :=
        CFSG.LieType.Chevalley.rootDiagUnit_injective (hax.trans (hy1 x hx).symm)
      subst ha
      exact ⟨fun k => zpow_pow_eq_one_rk hζ.pow_eq_one _,
        (rootChar_val_eq_one_iff_wk hζ _ β).2 (hy2 x hx)⟩
    · rintro ⟨hap, haβ⟩
      obtain ⟨z, hz⟩ := exists_zpow_val_eq_rk hζ hap
      have hzβ : ∑ k, z k * (β k : ZMod p) = 0 := by
        rw [← rootChar_val_eq_one_iff_wk hζ z β, hz]
        exact haβ
      obtain ⟨⟨x, hx⟩, hfx⟩ := hbij.2 ⟨z, hzβ⟩
      have hyz : y x hx = z := congrArg Subtype.val hfx
      refine ⟨x, hx, ?_⟩
      rw [← hz, ← hyz]
      exact hy1 x hx
  refine ⟨β, hβ, hmain, fun a hap haβ => ?_, fun γ hγ ζ' hζ' => (hmain _).2 ⟨fun k => ?_, ?_⟩⟩
  ·
    obtain ⟨x, hx, hax⟩ := (hmain a).2 ⟨hap, haβ⟩
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hsz' : D.g0 * s * D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) := hsz
    have hs_eq : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) *
        D.g0 = s := by
      rw [← hsz']
      group
    rw [hax, hs_eq]
    exact hs
  ·
    have h := zpow_pow_eq_one_rk hζ' (∑ l, TwistTag.E6.tag.cartan k l * γ l)
    exact h
  ·
    rw [rootChar_corootTuple, iform_comm, hγ, zpow_zero]

end Main

end CFSG.StandardType.TwE6RootKill

end
