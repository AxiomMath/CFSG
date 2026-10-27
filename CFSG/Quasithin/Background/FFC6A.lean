module

public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.FFC5Case1

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B1Red
open scoped commutatorElement

namespace B59

section Red

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def W0 (L A : Subgroup (MulAut V)) : Subgroup V := fixV (pCoreOf 2 (L ⊔ A))

abbrev Xr (L A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(W0 L A)) := autSub (L ⊔ A) (W0 L A)

abbrev Kr (L A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(W0 L A)) := autSub L (W0 L A)

abbrev Ar (L A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(W0 L A)) := autSub A (W0 L A)

theorem red_basic (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L) :
    (∀ x ∈ L ⊔ A, ∀ l ∈ L, x * l * x⁻¹ ∈ L) ∧ (∀ x ∈ L ⊔ A, x ^ 2 ∈ L) ∧
      (L ⊔ A) ⊓ centSub (W0 L A) = pCoreOf 2 (L ⊔ A) ∧ L ⊔ A ≤ stabSub (W0 L A) ∧
      ¬ L ≤ centSub (W0 L A) ∧ ¬ A ≤ centSub (W0 L A) := by
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  set H₀ := L ⊔ A with hH₀def
  have hH₀n : ∀ x ∈ H₀, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hx
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq : ∀ x ∈ H₀, x ^ 2 ∈ L := sq_mem_of_mem_sup hAnL hAel.2
  set Q := pCoreOf 2 H₀ with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀
  have hQH : Q ≤ H₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 H₀
  have hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l = l * q := by
    refine commute_of_normal_not_le hLo (fun q hq l hl => hH₀n q (hQH hq) l hl)
      (fun l hl q hq => conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hq) ?_
    intro hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hle).isNilpotent
  have hker : H₀ ⊓ centSub (fixV Q) = Q :=
    kernel_eq_pCoreOf hV (D := L) (fun x hx ho => mem_of_sq_mem_of_odd (hsq x hx) ho)
      (fun x hx q hq => (hQL q hq x hx).symm)
  have hst : H₀ ≤ stabSub (fixV Q) := le_stabSub_fixV_pCoreOf H₀
  have hLnc : ¬ L ≤ centSub (fixV Q) := by
    intro hle
    have hLQ : L ≤ Q := hker ▸ le_inf le_sup_left hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hLQ).isNilpotent
  have hAnc : ¬ A ≤ centSub (fixV Q) := by
    intro hle
    have hAQ : A ≤ Q := hker ▸ le_inf le_sup_right hle
    have h0 : ⁅L, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl a ha
      show ⁅l, a⁆ ∈ (⊥ : Subgroup (MulAut V))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hQL a (hAQ ha) l hl).symm
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt (hLA ▸ h0)
  exact ⟨hH₀n, hsq, hker, hst, hLnc, hAnc⟩


omit [Finite V] in
theorem isFFStarMin_of_le {X Y A : Subgroup (MulAut V)} (hmin : IsFFStarMin X A) (hAY : A ≤ Y)
    (hYX : Y ≤ X) : IsFFStarMin Y A := by
  refine ⟨⟨hAY, hmin.1.2.1, hmin.1.2.2.1, hmin.1.2.2.2⟩, fun B hB hBA => ?_⟩
  refine hmin.2 B ⟨hB.1.trans hYX, hB.2.1, hB.2.2.1, hB.2.2.2⟩ ?_
  obtain ⟨⟨hB1, hB2, hB3⟩, ⟨hA1, hA2, hA3⟩, hle, heq⟩ := hBA
  exact ⟨⟨hB1.trans hYX, hB2, hB3⟩, ⟨hA1.trans hYX, hA2, hA3⟩, hle, heq⟩

omit [Finite V] in
theorem autSub_sup {L A : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U)
    (hA : A ≤ stabSub U) : autSub (L ⊔ A) U = autSub L U ⊔ autSub A U := by
  unfold autSub
  rw [Subgroup.subgroupOf_sup hL hA, Subgroup.map_sup]

theorem red_aut (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L) :
    pCoreOf 2 (Xr L A) = ⊥ ∧ quasithinGenFitting (Xr L A) = Kr L A ∧
      CFSG.Open.IsQuasisimple ↥(Kr L A) ∧ Kr L A ≤ Xr L A ∧
      (∀ g ∈ Xr L A, ∀ l ∈ Kr L A, g * l * g⁻¹ ∈ Kr L A) ∧ (∀ y ∈ Xr L A, y ^ 2 ∈ Kr L A) ∧
      IsFFStarOffender (Xr L A) (Ar L A) ∧ ⁅Kr L A, Ar L A⁆ = Kr L A ∧
      Xr L A = Kr L A ⊔ Ar L A := by
  obtain ⟨hH₀n, hsq, hker, hst, hLnc, hAnc⟩ := red_basic hV hL hA hLA
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hLbq : CFSG.Open.IsQuasisimple ↥(Kr L A) := isQuasisimple_autSub hLU hLo hLnc
  have hLbH : Kr L A ≤ Xr L A := autSub_mono le_sup_left _
  have hO2b : pCoreOf 2 (Xr L A) = ⊥ := pCoreOf_autSub_eq_bot hker
  have hLbn : ∀ g ∈ Xr L A, ∀ l ∈ Kr L A, g * l * g⁻¹ ∈ Kr L A := fun g hg l hl =>
    autSub_conj_mem hH₀n hg hl
  have hHb2 : ∀ y ∈ Xr L A, y ^ 2 ∈ Kr L A := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine mem_autSub.2 ⟨g ^ 2, ?_, by rw [map_pow]⟩
    simpa using hsq _ hgH
  have hFb : quasithinGenFitting (Xr L A) = Kr L A :=
    quasithinGenFitting_eq_of_two_quot hLbH hLbn hLbq hHb2 hO2b
  have hAH₀ : IsFFStarOffender (L ⊔ A) A := ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hoff : IsFFStarOffender (Xr L A) (Ar L A) :=
    B1Red.isFFStarOffender_autSub hAH₀ (fun a ha w hw => (hst (Subgroup.mem_sup_right ha) w).2 hw) hAnc
  have hcomm : ⁅Kr L A, Ar L A⁆ = Kr L A := commutator_autSub_eq hLU hAU hLA
  have hsup : Xr L A = Kr L A ⊔ Ar L A := autSub_sup hLU hAU
  exact ⟨hO2b, hFb, hLbq, hLbH, hLbn, hHb2, hoff, hcomm, hsup⟩

theorem centerOf_le_genFitting {Ω : Type} [Group Ω] (J : Subgroup Ω) :
    centerOf J ≤ quasithinGenFitting J := by
  refine le_sup_of_le_left (le_sSup ⟨fun x hx => hx.1, ⟨fun n hn g => ?_⟩, ?_⟩)
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := Subgroup.mem_centralizer_iff.mp hn.2 (g : Ω) g.2
    refine ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2), ?_⟩
    have e : (g : Ω) * (n : Ω) * (g : Ω)⁻¹ = n := by rw [h1, mul_inv_cancel_right]
    simpa [e] using hn.2
  · let _ : CommGroup ↥(centerOf J) :=
      { (inferInstance : Group ↥(centerOf J)) with
        mul_comm := fun a b => Subtype.ext
          ((Subgroup.mem_centralizer_iff.mp b.2.2 (a : Ω) a.2.1)) }
    exact CommGroup.isNilpotent

theorem sqtk_Kr (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) (hb : B53Hyp G) (hL : CFSG.Open.IsComponentOf L G)
    (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L) : SQTKGroup ↥(Kr L A) := by
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hSL : SQTKGroup ↥L := sqtk_of_le hA21 (isQuotientOfSQTKTauCeti_of_b53 hb) hL.1 hLq
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hA hLA
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hfaith : L ⊓ centSub (W0 L A) = ⊥ := (B55.faithful_on_fixV hV hO2 hL hA hLA).1
  have hinj : Function.Injective ((resHom (W0 L A)).comp (Subgroup.inclusion hLU)) := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : (l : MulAut V) ∈ L ⊓ centSub (W0 L A) := by
      refine ⟨l.2, fun u hu => ?_⟩
      exact congrArg (fun φ : MulAut ↥(W0 L A) => ((φ ⟨u, hu⟩ : ↥(W0 L A)) : V)) hl
    rw [hfaith, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have e : ↥L ≃* ↥(Kr L A) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (autSub_eq_range hLU).symm)
  exact B5.sqtk_of_mulEquiv e.symm hSL

theorem b51Hyp_red (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) (hb : B53Hyp G) (hL : CFSG.Open.IsComponentOf L G)
    (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L) : B51Hyp (Xr L A) (Kr L A) := by
  obtain ⟨hO2b, hFb, hLbq, hLbH, hLbn, hHb2, hoff, hcomm, hsup⟩ := red_aut hV hL hA hLA
  have hZ : centerOf (Xr L A) ≤ Kr L A := hFb ▸ centerOf_le_genFitting _
  have hKJ : Kr L A ≤ ffJ (Xr L A) := B1Red.K_le_ffJ hLbH hoff hcomm
  have hJ : Xr L A = ffJ (Xr L A) :=
    le_antisymm (hsup.le.trans (sup_le hKJ (B6.le_ffJ hoff))) (B6.ffJ_le _)
  exact ⟨by rw [hFb, sup_eq_left.2 hZ], B1Red.isQuasisimple_of_open hLbq,
    sqtk_Kr hA21 hV hO2 hb hL hA hLA, hLbH, ‹_›, hJ⟩

end Red

end B59

end FFC

end CFSG.Quasithin
