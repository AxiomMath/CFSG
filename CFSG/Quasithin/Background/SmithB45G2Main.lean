module

public import CFSG.Quasithin.Background.SmithB45G2Nat
public import CFSG.Quasithin.Background.SmithB45G2Base
public import CFSG.Quasithin.Background.SmithB45Families

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

namespace B45G2

section A1

variable {F : Type} [Field F] [CharP F 2]

theorem g2Act_injective {g h : ↥(cayleyGroup F)} (hgh : ∀ w, g2Act g w = g2Act h w) : g = h := by
  have h1 : g * h⁻¹ = 1 := cayley_eq_one fun w => by
    rw [g2Act_mul_apply, hgh, g2Act_apply_inv]
  calc g = g * h⁻¹ * h := by group
    _ = h := by rw [h1, one_mul]

theorem g2Act_kE_mul (α p q' α' p' q'' : F) (w : Ix3 → F) :
    g2Act (kE α p q' * kE α' p' q'') w = g2Act (kE (α + α') (p + p') (q' + q'')) w := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [g2Act_mul_apply, q6_eta w, g2Act_A1, g2Act_A1, g2Act_A1]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first | ring1 | linear_combination (-(α * α' * w (.inr 0))) * h2

theorem A1_elem : (∀ γ ∈ A1 F, γ * γ = 1) ∧ ∀ γ ∈ A1 F, ∀ δ ∈ A1 F, γ * δ = δ * γ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩
  · obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
    refine cayley_eq_one fun w => ?_
    change g2Act (kE α p q' * kE α p q') w = w
    rw [g2Act_kE_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, q6_eta w, g2Act_A1]
    simp
  · obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
    obtain ⟨α', p', q'', rfl⟩ := exists_eq_of_mem_A1 hδ
    refine g2Act_injective fun w => ?_
    change g2Act (kE α p q' * kE α' p' q'') w = g2Act (kE α' p' q'' * kE α p q') w
    rw [g2Act_kE_mul, g2Act_kE_mul, add_comm α, add_comm p, add_comm q']

end A1

end B45G2

theorem asB45G2Even_holds : AsB45G2Even := by
  intro V _ _ hV G L hHyp hP hq
  classical
  obtain ⟨A, hA, -, hcard⟩ := exists_cubic_of_qhatOf_le_two hV hq
  obtain ⟨hZ, f, hf, hmodel⟩ := hP
  obtain ⟨-, hLF, -, hirr⟩ := hHyp
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  obtain ⟨-, K, _, _, _, hK, ⟨θL⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_model_center_eq_bot hZ hmodel
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hW' : ∀ w : V, w * w = 1 := fun w => by rw [← pow_two]; exact hV w
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW'
  set ψ := binPsi θ with hψ
  let πM : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M) :=
    ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)
  have hπM : ∀ g, πM g = ψ ((θL.symm g : ↥L) : MulAut V) := fun g => rfl
  have hπinj : Function.Injective πM := fun g g' h => by
    have h1 := ψ.injective h
    exact θL.symm.injective (Subtype.ext h1)
  have hirrW := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hirr
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, πM g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrW U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (θL ⟨l, hl⟩) u hu
    rwa [hπM, MulEquiv.symm_apply_apply] at h1
  have hntM : Nontrivial M := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set A₀ := A.map ψ.toMonoidHom with hA₀
  have hnorm : ∀ a ∈ A₀, ∀ x, ∃ y, a * πM x * a⁻¹ = πM y := by
    rintro _ ⟨a, ha, rfl⟩ x
    have hl : a * ((θL.symm x : ↥L) : MulAut V) * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hGN (hA.1 ha)) _).mp (θL.symm x).2
    refine ⟨θL ⟨_, hl⟩, ?_⟩
    rw [hπM (θL _), MulEquiv.symm_apply_apply, hπM x]
    change ψ a * ψ ((θL.symm x : ↥L) : MulAut V) * (ψ a)⁻¹ =
      ψ (a * ((θL.symm x : ↥L) : MulAut V) * a⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hAe : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θ A).1 hA.2.2
  have hA1 : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff_of_injective A ψ.injective]
    exact hA.2.1
  have hoff : Nat.card M ≤ Nat.card A₀ ^ 2 * Nat.card {m : M // ∀ a ∈ A₀, a m = m} := by
    have h1 : Nat.card A₀ = Nat.card A := Subgroup.card_map_of_injective ψ.injective
    have h2 := natCard_fixGL_map θ A
    rw [natCard_eq θ] at hcard
    calc Nat.card M ≤ Nat.card A ^ 2 * Nat.card (fixV A) := hcard
      _ = _ := by rw [h1, ← h2]; rfl
  obtain ⟨φ, hφ⟩ := B45G2.exists_natural_of_twoF hKf hf πM hπinj hntM hirrM A₀ hnorm hAe hA1 hoff
  set ι : ↥(cayleyGroup K) →* MulAut V := L.subtype.comp θL.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := fun g g' h => θL.symm.injective (Subtype.ext h)
  set E := (A1 K).map ι with hE
  have hEL : E ≤ L := by
    rintro _ ⟨g, -, rfl⟩
    exact (θL.symm g).2
  obtain ⟨hA1sq, hA1c⟩ := B45G2.A1_elem (F := K)
  have hEe : IsElemAbelian2 E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
      rw [← map_mul, ← map_mul, hA1c g hg h hh]
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow, pow_two, hA1sq g hg, map_one]
  have hEcard : Nat.card E = Nat.card K ^ 3 := by
    rw [hE, Subgroup.card_map_of_injective hιinj, card_A1]
  have hEne : E ≠ ⊥ := by
    intro h0
    have h1 : Nat.card E = 1 := by rw [h0, Subgroup.card_bot]
    rw [hEcard, hK] at h1
    have : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  have hEA2 : IsA2 G E := ⟨hEL.trans hLG, hEne, hEe⟩
  have hfixE : Nat.card K ^ 3 ≤ Nat.card (fixV E) := by
    let j : ↥(stdF K 3) → ↥(fixV E) := fun w => ⟨θ.symm (Multiplicative.ofAdd (φ.symm w)), by
      rintro _ ⟨g, hg, rfl⟩
      apply θ.injective
      have h1 := hφ g (φ.symm w)
      rw [AddEquiv.apply_symm_apply, hg w w.2] at h1
      have h2 : πM g (φ.symm w) = φ.symm w := by
        apply φ.injective
        rw [h1, AddEquiv.apply_symm_apply]
      have h3 := B42L2.toAdd_binPsi θ (ι g) (θ.symm (Multiplicative.ofAdd (φ.symm w)))
      rw [MulEquiv.apply_symm_apply] at h3
      change ψ (ι g) (Multiplicative.toAdd (Multiplicative.ofAdd (φ.symm w))) = _ at h3
      rw [toAdd_ofAdd] at h3
      change πM g (φ.symm w) = _ at h3
      rw [h2] at h3
      rw [MulEquiv.apply_symm_apply]
      exact (Multiplicative.toAdd.injective h3).symm⟩
    have hj : Function.Injective j := fun a b h => by
      have h1 := congrArg (fun x : ↥(fixV E) => φ (Multiplicative.toAdd (θ x.1))) h
      simp only [j, MulEquiv.apply_symm_apply, toAdd_ofAdd, AddEquiv.apply_symm_apply] at h1
      exact Subtype.ext h1
    have := Nat.card_le_card_of_injective j hj
    rwa [card_stdF (by norm_num)] at this
  have hVcard : Nat.card V = Nat.card K ^ 6 := by
    rw [natCard_eq θ, Nat.card_congr φ.toEquiv, card_Q]
  have hr : rAV E ≤ 1 := by
    refine (rAV_le_one_iff hV hEA2).2 ?_
    rw [hVcard, hEcard]
    calc Nat.card K ^ 6 = Nat.card K ^ 3 * Nat.card K ^ 3 := by ring
      _ ≤ Nat.card K ^ 3 * Nat.card (fixV E) := Nat.mul_le_mul_left _ hfixE
  exact qhatOf_le_one_of_rAV_le_one hV hEA2 hr

end CFSG.Quasithin
