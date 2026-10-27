module

public import CFSG.Walter.Bender1970.S4.Restricted
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Walter.Bender1970.S4.Control

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Bender44

omit [Finite G] in
theorem orderOf_eq_two_of_isKleinFour {W : Subgroup G} (hW : IsKleinFour W) {w : G}
    (hw : w ∈ W) (hw1 : w ≠ 1) : orderOf w = 2 := by
  refine orderOf_eq_prime ?_ hw1
  rw [pow_two]
  exact congrArg Subtype.val (IsKleinFour.mul_self (⟨w, hw⟩ : W))

variable (hG : BenderCounterexample G)
include hG

theorem isComponentOf_of_not_isTypeL2Even
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s)
    (htM : t ∈ M) (hsH : s ∈ H) {U₀ V₀ : Subgroup G} (hU₀ : IsKleinFour U₀) (hU₀M : U₀ ≤ M)
    (hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H)
    (hV₀ : IsKleinFour V₀) (hV₀H : V₀ ≤ H)
    (hV₀C : ∀ v ∈ V₀, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ M) {J : Subgroup G}
    (hJ : IsComponentOf J H) (hJ2 : ¬ IsTypeL2Even (J ⧸ Subgroup.center J)) :
    IsComponentOf J M := by
  have hHA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hH)
  have hMA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hM)
  have hJM : J ≤ M := le_of_isComponentOf_of_not_isTypeL2Even hHA hV₀H hV₀ hV₀C hJ hJ2
  obtain ⟨J', hJ', hJJ', h⟩ := exists_isComponentOf_of_le hHA.1 hMA (bender1970_4_3 hG hs hM)
    (mem_of_mem_benderM hH) htM ht (inf_le_right.trans (centralizer_le_of_mem_benderM hH)) hJ hJM
  rcases h with rfl | ⟨hJodd, hJ'JR, -⟩
  · exact hJ'
  · exfalso
    have hJ'H : J' ≤ H := le_of_isComponentOf_of_not_isTypeL2Even hMA hU₀M hU₀ hU₀C hJ'
      (not_isTypeL2Even_of_isTypeJR hJ'JR)
    obtain ⟨J'', hJ'', -, h'⟩ := exists_isComponentOf_of_le hMA.1 hHA (bender1970_4_3 hG ht hH)
      (mem_of_mem_benderM hM) hsH hs (inf_le_right.trans (centralizer_le_of_mem_benderM hM)) hJ'
      hJ'H
    have hJ'c : IsComponentOf J' H := by
      rcases h' with rfl | ⟨hJ'odd, -, -⟩
      · exact hJ''
      · exact absurd hJ'odd (not_isTypeL2Odd_of_isTypeJR hJ'JR)
    have hJJ'eq := eq_of_isComponentOf_of_le hJ hJ'c hJJ'
    subst hJJ'eq
    exact not_isTypeL2Odd_of_isTypeJR hJ'JR hJodd

theorem eq_of_isComponentOf_not_isTypeL2Even
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s)
    (htM : t ∈ M) (hsH : s ∈ H) {U₀ V₀ : Subgroup G} (hU₀ : IsKleinFour U₀) (hU₀M : U₀ ≤ M)
    (hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H)
    (hV₀ : IsKleinFour V₀) (hV₀H : V₀ ≤ H)
    (hV₀C : ∀ v ∈ V₀, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ M) {J₀ : Subgroup G}
    (hJ₀ : IsComponentOf J₀ H) (hJ₀2 : ¬ IsTypeL2Even (J₀ ⧸ Subgroup.center J₀)) : M = H := by
  have := hG.isSimpleGroup
  have hset : {J | IsComponentOf J H ∧ ¬ IsTypeL2Even (J ⧸ Subgroup.center J)} =
      {J | IsComponentOf J M ∧ ¬ IsTypeL2Even (J ⧸ Subgroup.center J)} := by
    ext J
    exact ⟨fun hJ => ⟨isComponentOf_of_not_isTypeL2Even hG ht hH hs hM htM hsH hU₀ hU₀M hU₀C hV₀
        hV₀H hV₀C hJ.1 hJ.2, hJ.2⟩,
      fun hJ => ⟨isComponentOf_of_not_isTypeL2Even hG hs hM ht hH hsH htM hV₀ hV₀H hV₀C hU₀
        hU₀M hU₀C hJ.1 hJ.2, hJ.2⟩⟩
  have h𝒯 : ∀ (J : Subgroup G) (g : G), ¬ IsTypeL2Even (J ⧸ Subgroup.center J) →
      ¬ IsTypeL2Even ((J.map (MulAut.conj g).toMonoidHom) ⧸
        Subgroup.center (J.map (MulAut.conj g).toMonoidHom)) :=
    fun J g hJ h => hJ ((isTypeL2Even_map_conj_iff J g).mp h)
  have hNH := normalizer_sSup_isComponentOf_eq (isCoatom_of_mem_benderM hH) _ h𝒯 hJ₀ hJ₀2
  have hJ₀M := isComponentOf_of_not_isTypeL2Even hG ht hH hs hM htM hsH hU₀ hU₀M hU₀C hV₀ hV₀H
    hV₀C hJ₀ hJ₀2
  have hNM := normalizer_sSup_isComponentOf_eq (isCoatom_of_mem_benderM hM) _ h𝒯 hJ₀M hJ₀2
  rw [← hNM, ← hset, hNH]

theorem eq_of_isComponentOf_of_card_le
    {Y L : Subgroup G} (hY : IsAStar Y) (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ Y) (hL : IsComponentOf L Y)
    (hV : Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤ 8)
    {J₁ J₂ : Subgroup G} (hJ₁ : IsComponentOf J₁ Y) (hJ₂ : IsComponentOf J₂ Y) (h1 : J₁ ≠ L)
    (h2 : J₂ ≠ L) : J₁ = J₂ := by
  by_contra h12
  have hTab := hG.hasAbelianSylowTwo T
  have hQ₁ := bender38Component hY hJ₁ T hTY hTab
  have hQ₂ := bender38Component hY hJ₂ T hTY hTab
  have hQV : ∀ {J : Subgroup G}, IsComponentOf J Y → J ≠ L →
      (T : Subgroup G) ⊓ J ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) :=
    fun hJ hJL => inf_le_inf_left _ (le_centralizer_of_isComponentOf_ne hJ hL hJL)
  have hdisj : Disjoint ((T : Subgroup G) ⊓ J₁) ((T : Subgroup G) ⊓ J₂) := by
    rw [disjoint_iff, eq_bot_iff, ← inf_inf_eq_bot T.isPGroup' hQ₁]
    exact le_inf (inf_le_right.trans (inf_le_inf_left _
      (le_centralizer_of_isComponentOf_ne hJ₂ hJ₁ (Ne.symm h12)))) inf_le_left
  have hcomm : (T : Subgroup G) ⊓ J₂ ≤ Subgroup.normalizer
      (((T : Subgroup G) ⊓ J₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hTab.is_comm.comm ⟨y, hy.1⟩ ⟨x, hx.1⟩))
  have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcomm hdisj
  have hle := Subgroup.card_le_of_le (sup_le (hQV hJ₁ h1) (hQV hJ₂ h2))
  rw [hcard] at hle
  have := hQ₁.four_le_card
  have := hQ₂.four_le_card
  nlinarith

theorem isTypeL2Even
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G) {J₀ : Subgroup G}
    (hJ₀ : IsComponentOf J₀ H) : IsTypeL2Even (J₀ ⧸ Subgroup.center J₀) := by
  by_contra hJ₀2
  have := hG.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHco := isCoatom_of_mem_benderM hH
  have hHA := hG.isAStar_of_isCoatom hHco
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  set U := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hUdef
  have hUp : IsPGroup 2 U := T.isPGroup'.to_le inf_le_left
  have hUab : IsMulCommutative U :=
    ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨U₀, hU₀U, hU₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hUp hUab (not_isCyclic hG ht hH T htT hK)
  have hUC : ∀ u ∈ U, orderOf u = 2 → Subgroup.centralizer ({u} : Set G) ≤ H :=
    fun u hu hu2 => centralizer_le_of_mem_benderM
      (by rw [benderM_eq_singleton hG ht hH T htT hK hres hu hu2]; rfl)
  have hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H :=
    fun u hu hu1 => hUC u (hU₀U hu) (orderOf_eq_two_of_isKleinFour hU₀ hu hu1)
  have hNT := normalizer_le hG ht hH T htT hK hres
  obtain ⟨s, hsT, hs, M, hM, hMH⟩ := hG.exists_mem_benderM_ne_of_mem_benderM ht hH T htT
  have hMco := isCoatom_of_mem_benderM hM
  have hMA := hG.isAStar_of_isCoatom hMco
  have hTM := hG.sylow_le_of_mem_benderM T hsT hM
  have hU₀M : U₀ ≤ M := (hU₀U.trans inf_le_left).trans hTM
  have hEM : ¬ componentLayerOf M ≤ H := by
    intro hE
    have hO : oddCoreOf M ≤ H := le_of_forall_centralizer_le_of_odd hU₀
      (hU₀M.trans (le_normalizer_of_isNormalIn (oddCoreOf_isNormalIn' M)))
      (odd_card_oddCoreOf M) hU₀C
    have hMH' := le_of_oddCoreOf_le hMA (bender1970_4_3 hG hs hM) T hTM hO hE hTH
      (inf_le_right.trans hNT)
    exact hMH ((hMco.le_iff.mp hMH').resolve_left hHco.1).symm
  obtain ⟨Kb, hKb, hKbH⟩ : ∃ Kb : Subgroup G, IsComponentOf Kb M ∧ ¬ Kb ≤ H := by
    by_contra h
    push Not at h
    exact hEM (sSup_le fun J hJ => h J hJ)
  set V := (T : Subgroup G) ⊓ Subgroup.centralizer (Kb : Set G) with hVdef
  have hVp : IsPGroup 2 V := T.isPGroup'.to_le inf_le_left
  have hVab : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨V₀, hV₀V, hV₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hVp hVab (not_isCyclic hG hs hM T hsT hKb)
  have hKbC : ∀ v ∈ V, Kb ≤ Subgroup.centralizer ({v} : Set G) := fun v hv k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hv.2) k hk)
  have hUV : U ⊓ V = ⊥ := by
    by_contra hne
    have : Nontrivial (U ⊓ V : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨k, hk, hcard⟩ :=
      (IsPGroup.nontrivial_iff_card (hUp.to_le (inf_le_left : U ⊓ V ≤ U))).mp inferInstance
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(U ⊓ V)) 2
      (hcard ▸ dvd_pow_self 2 hk.ne')
    have hw2 : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe, hw]
    exact hKbH ((hKbC w w.2.2).trans (hUC w w.2.1 hw2))
  obtain ⟨v, hvV, hv2, hvM⟩ :
      ∃ v ∈ V, orderOf v = 2 ∧ ¬ Subgroup.centralizer ({v} : Set G) ≤ M := by
    by_contra hcon
    push Not at hcon
    exact hMH (eq_of_isComponentOf_not_isTypeL2Even hG ht hH hs hM (hTM htT) (hTH hsT) hU₀ hU₀M
      hU₀C hV₀ ((hV₀V.trans inf_le_left).trans hTH)
      (fun v hv hv1 => hcon v (hV₀V hv) (orderOf_eq_two_of_isKleinFour hV₀ hv hv1)) hJ₀ hJ₀2)
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv2
    omega
  obtain ⟨R, hR⟩ := hG.benderM_nonempty hv1
  have hRco := isCoatom_of_mem_benderM hR
  have hRA := hG.isAStar_of_isCoatom hRco
  have hTR := hG.sylow_le_of_mem_benderM T hvV.1 hR
  have hKbR : Kb ≤ R := (hKbC v hvV).trans (centralizer_le_of_mem_benderM hR)
  have hKbRc : IsComponentOf Kb R := by
    obtain ⟨Kb', hKb', hKbKb', h⟩ := exists_isComponentOf_of_le hMA.1 hRA
      (bender1970_4_3 hG hv2 hR) (mem_of_mem_benderM hM) (hTR hsT) hs
      (inf_le_right.trans (centralizer_le_of_mem_benderM hM)) hKb hKbR
    rcases h with rfl | ⟨-, hKb'JR, -⟩
    · exact hKb'
    · exact absurd (hKbKb'.trans (le_of_isComponentOf_of_not_isTypeL2Even hRA
        ((hU₀U.trans inf_le_left).trans hTR) hU₀ hU₀C hKb'
        (not_isTypeL2Even_of_isTypeJR hKb'JR))) hKbH
  rcases hres with hKJR | hnoJR
  ·
    have h8 := card_inf_eq_eight_of_isTypeJR hHA hK T hTH hTab hKJR
    have hTcard := card_sylow_eq_mul hHA hK T hTH (hG.bender38Component' hH T htT hK)
    have hV8 : Nat.card V ≤ 8 := by
      have hcomm : V ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
          hTc _ hy.1 _ hx.1)
      have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer U V hcomm (disjoint_iff.mpr hUV)
      have hle := Subgroup.card_le_of_le (sup_le (inf_le_left : U ≤ T) (inf_le_left : V ≤ T))
      rw [hcard, hTcard, h8] at hle
      have hUpos := Nat.card_pos (α := U)
      nlinarith
    have hnM : M ≤ Subgroup.normalizer (Kb : Set G) :=
      le_normalizer_of_forall_eq hMA hKb T hTM fun _ _ hJ₁ hJ₂ h1 h2 =>
        eq_of_isComponentOf_of_card_le hG hMA T hTM hKb hV8 hJ₁ hJ₂ h1 h2
    have hnR : R ≤ Subgroup.normalizer (Kb : Set G) :=
      le_normalizer_of_forall_eq hRA hKbRc T hTR fun _ _ hJ₁ hJ₂ h1 h2 =>
        eq_of_isComponentOf_of_card_le hG hRA T hTR hKbRc hV8 hJ₁ hJ₂ h1 h2
    have hNM := hG.normalizer_eq_of_isNormalIn hMco ⟨hKb.1, fun h hh k hk =>
      (Subgroup.mem_normalizer_iff.mp (hnM hh) k).mp hk⟩ (ne_bot_of_isComponentOf hKb)
    have hNR := hG.normalizer_eq_of_isNormalIn hRco ⟨hKbR, fun h hh k hk =>
      (Subgroup.mem_normalizer_iff.mp (hnR hh) k).mp hk⟩ (ne_bot_of_isComponentOf hKb)
    exact hvM ((centralizer_le_of_mem_benderM hR).trans (hNR.symm.trans hNM).le)
  ·
    have hRM := eq_of_le hG hs hM T hsT hKb (Or.inr hnoJR) hvV.1 hv2 hR hKbR
    exact hvM (hRM ▸ centralizer_le_of_mem_benderM hR)

end Bender44

end CFSG.Walter
