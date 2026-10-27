module

public import CFSG.Quasithin.Vol2.Ch3yChain
public import CFSG.Quasithin.Vol2.Ch3xD15
public import CFSG.Quasithin.Background.SimsD1Two
public import CFSG.Quasithin.Background.SimsD1Bridge

public section

namespace CFSG.Quasithin.SimsD1.Three

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def secFix (A N L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ N ∧ x ∈ Subgroup.normalizer (L : Set G) ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L}
  one_mem' := ⟨N.one_mem, Subgroup.one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hxL, hx⟩ ⟨hyN, hyL, hy⟩
    refine ⟨N.mul_mem hxN hyN, Subgroup.mul_mem _ hxL hyL, fun a ha => ?_⟩
    have h1 := hx a ha
    have h2 := (Subgroup.mem_normalizer_iff.mp hxL _).mp (hy a ha)
    have : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [this]
    exact L.mul_mem h1 h2
  inv_mem' := by
    rintro x ⟨hxN, hxL, hx⟩
    refine ⟨N.inv_mem hxN, Subgroup.inv_mem _ hxL, fun a ha => ?_⟩
    have h1 := L.inv_mem (hx a ha)
    have h2 := (Subgroup.mem_normalizer_iff''.mp hxL _).mp h1
    have : a * x⁻¹ * a⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
    rw [this]
    exact h2

theorem secFix_eq_centralizerMod (A N L : Subgroup G) : secFix A N L = centralizerMod L N A := by
  ext x
  constructor
  · rintro ⟨hxN, hxL, hx⟩
    refine ⟨hxN, hxL, fun a ha => ?_⟩
    have := L.inv_mem (hx a ha)
    have e : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact this
  · rintro ⟨hxN, hxL, hx⟩
    refine ⟨hxN, hxL, fun a ha => ?_⟩
    have := L.inv_mem (hx a ha)
    have e : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact this

variable [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem twoPrimeResidual_eq_of_normal_sylow {Y S : Subgroup G} (hS : IsSylowTwoOf S Y)
    (hn : Y ≤ Subgroup.normalizer (S : Set G)) : S = twoPrimeResidual Y := by
  obtain ⟨hSY, hS2, hSodd⟩ := hS
  apply le_antisymm
  · exact le_iInf fun N => le_iInf fun hN =>
      B6.le_of_isPGroup_of_odd_relIndex hSY hS2 hN.1 hN.2.1 hN.2.2
  · exact iInf₂_le S ⟨hSY, hn, hSodd⟩

theorem pCoreOf_inf_centralizer_eq (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) :
    pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G) =
      twoPrimeResidual (G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) := by
  have hmp := h.minParabolic hnff
  set U := conjClosure V G₂ with hUdef
  set C := G₂ ⊓ Subgroup.centralizer (U : Set G) with hCdef
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hCn : G₂ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hG₂U hg⟩
  have hK : ¬ twoResidual G₂ ≤ C := by
    intro hle
    apply D15Proof.commutator_ne_bot h
    rw [← F6.twoResidual_eq_oTwoUpper, eq_bot_iff]
    rw [Subgroup.commutator_le]
    intro u hu p hp
    have hpC := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hle hp)).2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hpC u hu
  have hCJ : C ≤ kerIn M₂ G₂ := hmp.le_kerIn_of_not_twoResidual_le inf_le_left hCn hK
  obtain ⟨-, hSyl⟩ := hmp.le_kerIn_and_isSylowTwoOf_of_le hCn (hCJ.trans kerIn_le)
  have hR₂C : pCoreOf 2 G₂ ⊓ C = pCoreOf 2 G₂ ⊓ Subgroup.centralizer (U : Set G) := by
    rw [hCdef, ← inf_assoc, inf_eq_left.mpr (pCoreOf_le 2 G₂)]
  rw [← hR₂C]
  refine twoPrimeResidual_eq_of_normal_sylow hSyl ?_
  intro c hc
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pCoreOf 2 G₂ hc.1, Subgroup.le_normalizer hc⟩

theorem d125_of_isSQTKSub (hN : D125NonsolvableSQTK) (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) (hVR₂ : V ≤ pCoreOf 2 G₂) (hsq : IsSQTKSub G₂) :
    D15Proof.D125 G₂ T (conjClosure V G₂) := by
  have hUe := D15Proof.isElemAbelian_conjClosure h hnff hVR₂
  have hVG₂ : V ≤ G₂ := h.V_le_T.trans h.sylow₂.1
  have hq1 : ¬ qInt G₁ V h.reduced.2.2.1 ≤ 1 := fun hq =>
    hnff ((isFFInt_iff_qInt_le_one _ _ _).mpr hq)
  by_cases hsolv : Group.IsSolvable G₂
  · exact D15Proof.d125_of_isSolvable hsolv h.sylow₂.1
      (conjClosure_le fun g hg v hv => G₂.mul_mem (G₂.mul_mem hg (hVG₂ hv)) (G₂.inv_mem hg)) hUe
  · exact hN G G₁ G₂ T V M₂ h hsq hsolv hq1 hVR₂ hUe


theorem two_mul_padicValNat_eq {a b : ℕ} (h : a ^ 2 = b) :
    2 * padicValNat 2 a = padicValNat 2 b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← h, padicValNat.pow a 2]

theorem three_eq (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (hD125 : D15Proof.D125 G₂ T (conjClosure V G₂))
    (hq2 : qInt G₁ V h.reduced.2.2.1 = 2) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c)
    {A : Subgroup G} (hA : IsMaxElemAbelian (pCoreOf 2 G₁) A)
    (hAq : ⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥) (hAnc : ⁅conjClosure V G₂, A⁆ ≠ ⊥) :
    c = 2 ∧
    (2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
        padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
          (conjClosure V G₂)) ∧
      padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
          (conjClosure V G₂)) =
        2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
          Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex (A ⊓ pCoreOf 2 G₂)) ∧
      (∀ g ∈ G₂, ⁅V.map (MulAut.conj g⁻¹).toMonoidHom, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
        2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
            Subgroup.centralizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
              (A ⊓ pCoreOf 2 G₂)) =
          padicValNat 2 ((V.map (MulAut.conj g⁻¹).toMonoidHom ⊓
            Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)).relIndex
              (V.map (MulAut.conj g⁻¹).toMonoidHom))) ∧
      (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
        padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
          padicValNat 2 ((secFix A N L).relIndex N)) ∧
      conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
        conjClosure V G₂ ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) := by
  set U := conjClosure V G₂ with hUdef
  set R₂ := pCoreOf 2 G₂ with hR₂def
  have hUe : IsElemAbelian 2 U := D15Proof.isElemAbelian_conjClosure h hnff hVR₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hAT' : IsMaxElemAbelian T A :=
    (SimsD1.isMaxElemAbelian_iff_of_thompsonJ_le (h.thompsonJ_le hnff) h.pCoreOf_le_T A).mp hA
  have hAT : A ≤ T := hAT'.1
  have hAnc' : ¬ A ≤ Subgroup.centralizer (U : Set G) := by
    intro hle
    apply hAnc
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  have hq2' : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1 := hq2 ▸ le_rfl
  obtain ⟨hc2, hb, hu, hv, hstep, hconj⟩ := Ch3y.chain_two h hnff hVR₂ hD125 hq2' hc hser hAT
    hAT'.2.1 hAq hAnc' (card_le_relIndex_mul_card hUe hUT hAT')
  have hBA : (A ⊓ R₂).relIndex A = R₂.relIndex A := Subgroup.inf_relIndex_left A R₂
  have hUA : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U =
      (Subgroup.centralizer (A : Set G)).relIndex U := Subgroup.inf_relIndex_left U _
  have hinf : A ⊓ R₂ = R₂ ⊓ A := inf_comm A R₂
  refine ⟨hc2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBA, hUA, hu]
    exact two_mul_padicValNat_eq rfl
  · rw [hUA, hu, Subgroup.inf_relIndex_left (A ⊓ R₂), hinf, hb]
    exact (two_mul_padicValNat_eq rfl).symm
  · intro g hg hW
    set W := V.map (MulAut.conj g⁻¹).toMonoidHom with hWdef
    have hWC : ¬ (R₂ ⊓ A) ≤ Subgroup.centralizer (W : Set G) := by
      intro hle
      apply hW
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hinf]
      exact Subgroup.le_centralizer_iff.mp hle
    have key : ((Subgroup.centralizer (W : Set G)).relIndex (R₂ ⊓ A)) ^ 2 =
        (Subgroup.centralizer ((R₂ ⊓ A : Subgroup G) : Set G)).relIndex W :=
      hconj g⁻¹ (G₂.inv_mem hg) hWC
    rw [Subgroup.inf_relIndex_left (A ⊓ R₂), Subgroup.inf_relIndex_left W, hinf]
    exact two_mul_padicValNat_eq key
  · intro L N hs hnc
    rw [secFix_eq_centralizerMod, (hstep L N hs hnc).1, hBA]
  · have hle : U ⊓ Subgroup.centralizer (A : Set G) ≤
        U ⊓ Subgroup.centralizer ((A ⊓ R₂ : Subgroup G) : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)
    have h1 : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U =
        (U ⊓ Subgroup.centralizer ((A ⊓ R₂ : Subgroup G) : Set G)).relIndex U := by
      rw [hUA, hu, Subgroup.inf_relIndex_left, hinf, hv]
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
    have hne : (U ⊓ Subgroup.centralizer ((A ⊓ R₂ : Subgroup G) : Set G)).relIndex U ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    rw [← h1] at hne
    have h2 : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (U ⊓ Subgroup.centralizer ((A ⊓ R₂ : Subgroup G) : Set G)) = 1 := by
      rw [← h1] at hmul
      exact (Nat.mul_eq_right hne).mp hmul
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)

theorem d13_finite (hN : D125NonsolvableSQTK) (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) (hVR₂ : V ≤ pCoreOf 2 G₂) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    IsElemAbelian 2 (conjClosure V G₂) ∧
    pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G) =
      twoPrimeResidual (G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) ∧
    (CFSG.SectionRank.IsSQTKCat ↥G₂ → qInt G₁ V h.reduced.2.2.1 ≤ 2) ∧
    ((∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ↔ IsMaxElemAbelian T A) ∧
      (∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ∧
        ⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ ∧ ⁅conjClosure V G₂, A⁆ ≠ ⊥) ∧
      (∀ A : Subgroup G, (IsMaxElemAbelian (pCoreOf 2 G₁) A ∧ ¬ A ≤ pCoreOf 2 G₂ ∧
          ∀ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A' → ¬ A' ≤ pCoreOf 2 G₂ →
            A' ⊔ pCoreOf 2 G₂ ≤ A ⊔ pCoreOf 2 G₂ → A' ⊔ pCoreOf 2 G₂ = A ⊔ pCoreOf 2 G₂) →
        ∃ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A' ∧
          A' ⊔ pCoreOf 2 G₂ = A ⊔ pCoreOf 2 G₂ ∧ A' ≤ A ⊔ conjClosure V G₂ ∧
          (⁅⁅conjClosure V G₂, A'⁆, A'⁆ = ⊥ ∧ ⁅conjClosure V G₂, A'⁆ ≠ ⊥))) ∧
    (CFSG.SectionRank.IsSQTKCat ↥G₂ → qInt G₁ V h.reduced.2.2.1 = 2 →
      c = 2 ∧
      ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A →
        (⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ ∧ ⁅conjClosure V G₂, A⁆ ≠ ⊥) →
        2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
            padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) ∧
          padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) =
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
              Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex (A ⊓ pCoreOf 2 G₂)) ∧
          (∀ g ∈ G₂, ⁅V.map (MulAut.conj g⁻¹).toMonoidHom, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
                Subgroup.centralizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
                  (A ⊓ pCoreOf 2 G₂)) =
              padicValNat 2 ((V.map (MulAut.conj g⁻¹).toMonoidHom ⊓
                Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)).relIndex
                  (V.map (MulAut.conj g⁻¹).toMonoidHom))) ∧
          (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
            padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
              padicValNat 2 ((secFix A N L).relIndex N)) ∧
          conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
            conjClosure V G₂ ⊓
              Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) := by
  refine ⟨D15Proof.isElemAbelian_conjClosure h hnff hVR₂, pCoreOf_inf_centralizer_eq h hnff,
    fun hsq => ?_, SimsD1.d13_two h hnff hVR₂, fun hsq hq2 => ?_⟩
  · exact D15Proof.qInt_le_two h hnff hVR₂
      (d125_of_isSQTKSub hN h hnff hVR₂ (SimsD1.isSQTKSub_of_isSQTKCat hsq)) hc hser
  · have hD125 := d125_of_isSQTKSub hN h hnff hVR₂ (SimsD1.isSQTKSub_of_isSQTKCat hsq)
    have hq2' : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1 := hq2 ▸ le_rfl
    refine ⟨Ch3y.c_eq_two h hnff hVR₂ hD125 hq2' hc hser, fun A hA hAq => ?_⟩
    exact (three_eq h hnff hVR₂ hD125 hq2 hc hser hA hAq.1 hAq.2).2

end CFSG.Quasithin.SimsD1.Three
