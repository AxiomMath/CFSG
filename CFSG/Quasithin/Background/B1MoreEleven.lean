module

public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

theorem mem_stabSub_map_subtype {V : Type*} [CommGroup V] {U : Subgroup V} {h : MulAut V}
    (hU : h ∈ stabSub U) {Ib : Subgroup ↥U} (hI : resHom U ⟨h, hU⟩ ∈ stabSub Ib) :
    h ∈ stabSub (Ib.map U.subtype) := by
  intro v
  constructor
  · intro hv
    have hvU : h v ∈ U := Subgroup.map_subtype_le Ib hv
    have hvU' : v ∈ U := (hU v).1 hvU
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, (u : V) = v := ⟨⟨v, hvU'⟩, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hv
    have : u' = resHom U ⟨h, hU⟩ u := U.subtype_injective hu'e
    exact ⟨u, (hI u).1 (this ▸ hu'), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨resHom U ⟨h, hU⟩ u, (hI u).2 hu, rfl⟩

end B1Red

open B1Red in
theorem B1_11 {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A L : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) (hLG : L ≤ G)
    (hL : CFSG.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) :
    ∃ (H : Subgroup (MulAut V)) (I : Subgroup V), L ≤ H ∧ H ≤ G ∧
      I ∈ IrrPlus L (⊤ : Subgroup V) ∧ H ≤ stabSub I ∧
      IsFFModule (autSec H I (I ⊓ fixV L)) ∧
      H ⊓ centSec I (I ⊓ fixV L) ≤ Subgroup.centralizer (L : Set (MulAut V)) ∧
      ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → I ⊓ fixV L ≤ J → J ≤ I →
        J = I ⊓ fixV L ∨ J = I := by
  have hLo : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_to_open hL
  have hLperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  set H₀ := L ⊔ A with hH₀def
  have hH₀G : H₀ ≤ G := sup_le hLG hA.1
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
  set U := fixV Q with hUdef
  have hst : H₀ ≤ stabSub U := le_stabSub_fixV_pCoreOf H₀
  have hLU : L ≤ stabSub U := le_sup_left.trans hst
  have hLnc : ¬ L ≤ centSub U := by
    intro hle
    have hLQ : L ≤ Q := hker ▸ le_inf le_sup_left hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hLQ).isNilpotent
  have hAnc : ¬ A ≤ centSub U := by
    intro hle
    have hAQ : A ≤ Q := hker ▸ le_inf le_sup_right hle
    have h0 : ⁅L, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl a ha
      show ⁅l, a⁆ ∈ (⊥ : Subgroup (MulAut V))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hQL a (hAQ ha) l hl).symm
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt (hLA ▸ h0)
  set Hb := autSub H₀ U with hHb
  set Lb := autSub L U with hLb
  have hLbq : CFSG.Open.IsQuasisimple ↥Lb := isQuasisimple_autSub hLU hLo hLnc
  have hLbH : Lb ≤ Hb := autSub_mono le_sup_left U
  have hO2b : pCoreOf 2 Hb = ⊥ := pCoreOf_autSub_eq_bot hker
  have hLbn : ∀ g ∈ Hb, ∀ l ∈ Lb, g * l * g⁻¹ ∈ Lb := fun g hg l hl => autSub_conj_mem hH₀n hg hl
  have hHb2 : ∀ y ∈ Hb, y ^ 2 ∈ Lb := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine mem_autSub.2 ⟨g ^ 2, ?_, by rw [map_pow]⟩
    simpa using hsq _ hgH
  have hFb : quasithinGenFitting Hb = Lb :=
    quasithinGenFitting_eq_of_two_quot hLbH hLbn hLbq hHb2 hO2b
  have hAH₀ : IsFFStarOffender H₀ A := ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hPb : ∃ Ab, IsFFStarOffender Hb Ab :=
    ⟨autSub A U, isFFStarOffender_autSub hAH₀ (fun a ha w hw => (hst (Subgroup.mem_sup_right ha) w).2 hw)
      hAnc⟩
  have hV' : ∀ v : ↥U, v ^ 2 = 1 := B1.sq_eq_one_sub hV U
  obtain ⟨Bb, Ib, hBbmin, hLBb, hIb, hBbfix, hFF⟩ :=
    B1_11_core (V := ↥U) hV' hO2b hLbq hLbn hFb hPb
  set Hb₁ := Lb ⊔ Bb with hHb₁
  set H := preimageAut H₀ U Hb₁ with hHdef
  set I := Ib.map U.subtype with hIdef
  have hIrr : I ∈ IrrPlus L (⊤ : Subgroup V) := mem_irrPlus_of_autSub hLU hIb
  have hHL : L ≤ H := by
    intro l hl
    exact mem_preimageAut.2 ⟨Subgroup.mem_sup_left hl, hLU hl,
      Subgroup.mem_sup_left (mem_autSub.2 ⟨⟨l, hLU hl⟩, hl, rfl⟩)⟩
  have hHG : H ≤ G := (preimageAut_le _ _ _).trans hH₀G
  obtain ⟨hLinvIb, -, -, -⟩ := (mem_irrPlus_top_iff).1 hIb
  have hHb₁stab : Hb₁ ≤ stabSub Ib :=
    sup_le (B1.le_stabSub_of_invariant hLinvIb) (B1.le_stabSub_of_invariant hBbfix)
  have hHstab : H ≤ stabSub I := by
    intro h hh
    obtain ⟨hhH₀, hhU, hhm⟩ := mem_preimageAut.1 hh
    exact mem_stabSub_map_subtype hhU (hHb₁stab hhm)
  have hCI : Ib ⊓ fixV Lb ≤ Ib := inf_le_left
  have hHb₁Hb : Hb₁ ≤ Hb := sup_le hLbH hBbmin.1.1
  have hle : Hb₁ ≤ autSub H U := by
    intro φ hφ
    obtain ⟨g, hgH₀, hgφ⟩ := mem_autSub.1 (hHb₁Hb hφ)
    have hgH : (g : MulAut V) ∈ H := by
      refine mem_preimageAut.2 ⟨hgH₀, g.2, ?_⟩
      have : (⟨(g : MulAut V), g.2⟩ : stabSub U) = g := rfl
      rw [this, hgφ]
      exact hφ
    exact mem_autSub.2 ⟨g, hgH, hgφ⟩
  have hFF' : IsFFModule (autSec (autSub H U) Ib (Ib ⊓ fixV Lb)) :=
    isFFModule_mono (autSec_mono hle Ib (Ib ⊓ fixV Lb)) hFF
  have hC : (Ib ⊓ fixV Lb).map U.subtype = I ⊓ fixV L := by
    rw [Subgroup.map_inf _ _ _ U.subtype_injective, map_subtype_fixV_autSub hLU, ← inf_assoc,
      inf_eq_left.2 (Subgroup.map_subtype_le Ib)]
  have hFFfinal : IsFFModule (autSec H I (I ⊓ fixV L)) := by
    have := isFFModule_autSec_of_autSub (X := H) hCI hFF'
    rwa [hC] at this
  obtain ⟨hLinvI, hcommI, hltI, hirr⟩ := (mem_irrPlus_top_iff).1 hIrr
  have hLstabC : L ≤ stabSub (I ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hLinvI (isInv_fixV L))
  have hcent : H ⊓ centSec I (I ⊓ fixV L) ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    set N := H ⊓ centSec I (I ⊓ fixV L) with hN
    have hNH : N ≤ H := inf_le_left
    have hnle : ¬ L ≤ N := by
      intro hle'
      have hcl : commSub I L ≤ I ⊓ fixV L := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨x, hx, w, hw, rfl⟩
        exact ((hle' hx).2).2 w hw
      rw [hcommI] at hcl
      exact not_le_of_gt hltI hcl
    have hNLn : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L := fun n hn l hl =>
      hH₀n n (preimageAut_le _ _ _ (hNH hn)) l hl
    have hLNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := by
      intro l hl n hn
      exact ⟨H.mul_mem (H.mul_mem (hHL hl) (hNH hn)) (H.inv_mem (hHL hl)),
        conj_mem_centSec (hHstab (hHL hl)) (hLstabC hl) hn.2⟩
    have hcomm := commute_of_normal_not_le hLo hNLn hLNn hnle
    exact fun n hn => Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn l hl).symm
  exact ⟨H, I, hHL, hHG, hIrr, hHstab, hFFfinal, hcent, hirr⟩

end CFSG.Quasithin
