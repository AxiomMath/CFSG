module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIsoA
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.SmithD39Two

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_endUnitsTrivial_of_iso {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {P P' : Subgroup Q}
    (hP : XMod.IsInv ↥Λ P) (hiso : XMod.Iso ↥Λ P P')
    (hE : Z391.EndUnitsTrivial Λ P) : Z391.EndUnitsTrivial Λ P' := by
  obtain ⟨φ, hφ⟩ := hiso
  have hφs : ∀ (a : ↥Λ) (l' l₂' : ↥P'), a • (l' : Q) = (l₂' : Q) →
      a • (((φ.symm l' : ↥P) : Q)) = (((φ.symm l₂' : ↥P) : Q)) := by
    intro a l' l₂' hl
    have hx : a • (((φ.symm l' : ↥P) : Q)) ∈ P := hP a _ (φ.symm l').2
    have h1 := hφ a (φ.symm l') ⟨a • (((φ.symm l' : ↥P) : Q)), hx⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h1
    have h3 : φ ⟨a • (((φ.symm l' : ↥P) : Q)), hx⟩ = l₂' := Subtype.ext (h1.symm.trans hl)
    have h4 : (⟨a • (((φ.symm l' : ↥P) : Q)), hx⟩ : ↥P) = φ.symm l₂' := by
      rw [← h3, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h4
  intro φ' hφ'
  have hθ : ∀ (a : ↥Λ) (x y : ↥P), a • (x : Q) = (y : Q) →
      a • (((φ.trans (φ'.trans φ.symm)) x : ↥P) : Q) =
        (((φ.trans (φ'.trans φ.symm)) y : ↥P) : Q) := by
    intro a x y hxy
    have h1 : a • ((φ x : ↥P') : Q) = ((φ y : ↥P') : Q) := hφ a x y hxy
    have h2 : a • ((φ' (φ x) : ↥P') : Q) = ((φ' (φ y) : ↥P') : Q) :=
      hφ' a (φ x) (φ y) h1
    have h3 := hφs a (φ' (φ x)) (φ' (φ y)) h2
    simpa only [MulEquiv.trans_apply] using h3
  have hrefl := hE (φ.trans (φ'.trans φ.symm)) hθ
  apply MulEquiv.ext
  intro y
  have h2 : φ.symm (φ' y) = φ.symm y := by
    have h := congrArg (fun e : ↥P ≃* ↥P => e (φ.symm y)) hrefl
    simpa only [MulEquiv.trans_apply, MulEquiv.refl_apply, MulEquiv.apply_symm_apply] using h
  exact φ.symm.injective h2

private theorem s16t3_isotypicOfLength_sup_two {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {P P' : Subgroup Q} (hP : XMod.IsIrr ↥Λ P) (hP' : XMod.IsIrr ↥Λ P')
    (hne : P ≠ P') (hiso : XMod.Iso ↥Λ P' P) :
    IsotypicOfLength ↥Λ (P ⊔ P') P 2 := by
  refine ⟨hP.1.sup hP'.1, ?_, ?_⟩
  · exact sup_le (le_isoComp hP (XMod.Iso.refl P)) (le_isoComp hP' hiso)
  · have hinf : P ⊓ P' = ⊥ := Z391.v2f_inf_eq_bot hP hP' hne
    have hrk : rk ↥P' = rk ↥P := by
      obtain ⟨e, -⟩ := hiso
      show padicValNat 2 (Nat.card ↥P') = padicValNat 2 (Nat.card ↥P)
      rw [Nat.card_congr e.toEquiv]
    have h1 := rk_sup_add_rk_inf P P'
    rw [hinf, rk_bot, hrk] at h1
    show rk ↥(P ⊔ P') = 2 * rk ↥P
    omega

theorem s16t3_exists_unique_third (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    {x y : Subgroup W} (hx : x ∈ irrSet L) (hy : y ∈ irrSet L) (hxy : x ≠ y) :
    (∃! z : Subgroup W, z ∈ irrSet L ∧ z ≠ x ∧ z ≠ y ∧
      tilde L (⊤ : Subgroup W) z ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y) ∧
    (∀ z : Subgroup W, z ∈ irrSet L → z ≠ x → z ≠ y →
      tilde L (⊤ : Subgroup W) z ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y →
      tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) z =
        tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y) := by
  classical
  have hq := h.quasi
  have htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
    intro I₁ h₁ I₂ h₂
    obtain ⟨g, hg, hgI⟩ := h.trans I₁ h₁ I₂ h₂
    exact ⟨g, hg.2, hgI⟩
  have h7q : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 7 := by
    rw [← s16t3_card_irrSet_eq_quot hq]
    exact h7
  have hiso := s16t3_iso_all_irr_of_seven h.elem hq h.sum htrans h7q
  have hfixV : modFix L (⊤ : Subgroup W) = fixV L := by
    rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
  have hYx : XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) x) :=
    s16t3_isIrr_tilde_of_mem_irrSet hq hx
  have hYy : XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) y) :=
    s16t3_isIrr_tilde_of_mem_irrSet hq hy
  have hinj : ∀ {I J : Subgroup W}, I ∈ irrSet L → J ∈ irrSet L →
      tilde L (⊤ : Subgroup W) I = tilde L (⊤ : Subgroup W) J → I = J := by
    intro I J hI hJ hIJ
    have key : ∀ K ∈ irrSet L,
        XMod.commOf ↥L ((tilde L (⊤ : Subgroup W) K).comap
          (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) = K := by
      intro K hK
      rw [comap_tilde, commOf_eq_commSub, commSub_sup_fixV (by rw [hfixV])]
      exact hK.1
    have h1 := key I hI
    have h2 := key J hJ
    rw [hIJ] at h1
    rw [← h1, h2]
  have hYxy : tilde L (⊤ : Subgroup W) x ≠ tilde L (⊤ : Subgroup W) y :=
    fun hh => hxy (hinj hx hy hh)
  obtain ⟨I, hnat, hIirr, -, -⟩ := s16t3_quot_summands hq h.sum
  have hEndRef : Z391.EndUnitsTrivial (⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I 0)) :=
    s16t3_endUnitsTrivial_tilde hq (hnat 0)
  have hIirr0top : XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I 0)) :=
    (s16t3_isIrr_top_iff (A := ↥L) _).mpr (hIirr 0)
  have hYxtop : XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) x) :=
    (s16t3_isIrr_top_iff (A := ↥L) _).mpr hYx
  have hIsoReftop : XMod.Iso ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) x)
      (tilde L (⊤ : Subgroup W) (I 0)) :=
    (s16t3_iso_top_iff (A := ↥L) _ _).mpr (hiso _ _ hYx (hIirr 0))
  have hEndX : Z391.EndUnitsTrivial (⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) x) :=
    s16t3_endUnitsTrivial_of_iso hIirr0top.1 (XMod.Iso.symm hYxtop.1 hIsoReftop) hEndRef
  have hItop : XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) x) :=
    (s16t3_isIrr_top_iff (A := ↥L) _).mpr hYx
  have hJtop : XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) y) :=
    (s16t3_isIrr_top_iff (A := ↥L) _).mpr hYy
  have hisotop : XMod.Iso ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) y)
      (tilde L (⊤ : Subgroup W) x) :=
    (s16t3_iso_top_iff (A := ↥L) _ _).mpr (hiso _ _ hYy hYx)
  have hQ : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, pow_two, h.elem w, QuotientGroup.mk_one]
  have hEtop : Nat.card (Module.End ↥(XMod.opRing ↥(⊤ : Subgroup ↥L)
      (W ⧸ modFix L (⊤ : Subgroup W))) ↥(XMod.toSubmod hItop.1)) = 2 :=
    s16t3_card_end_eq_two_of_endUnits hItop hEndX
  have hYtop : IsotypicOfLength ↥(⊤ : Subgroup ↥L)
      (tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y)
      (tilde L (⊤ : Subgroup W) x) 2 :=
    s16t3_isotypicOfLength_sup_two hQ hItop hJtop hYxy hisotop
  have hcard_top : Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      J ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y ∧
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) J} = 3 := by
    rw [SmithD321.card_irr_eq (Q := W ⧸ modFix L (⊤ : Subgroup W))
      (Λ := (⊤ : Subgroup ↥L)) hQ hItop hYtop hEtop]
    norm_num
  have hcard : Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      J ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y ∧
      XMod.IsIrr ↥L J} = 3 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun J =>
      and_congr_right (fun _ => (s16t3_isIrr_top_iff (A := ↥L) J).symm)))]
    exact hcard_top
  let S := {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      J ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y ∧ XMod.IsIrr ↥L J}
  haveI : Fintype S := Fintype.ofFinite S
  have hcardS : Fintype.card S = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let xS : S := ⟨tilde L (⊤ : Subgroup W) x, le_sup_left, hYx⟩
  let yS : S := ⟨tilde L (⊤ : Subgroup W) y, le_sup_right, hYy⟩
  have hxyS : xS ≠ yS := by
    intro hh
    exact hYxy (congrArg Subtype.val hh)
  have hU : ({xS, yS} : Finset S).card = 2 := Finset.card_pair hxyS
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({xS, yS} : Finset S)) (t := Finset.univ)
    (by rw [hU, Finset.card_univ, hcardS]; norm_num)
  have hrx : (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≠ tilde L (⊤ : Subgroup W) x := by
    intro hh
    apply hr
    have h1 : r = xS := Subtype.ext (by simpa using hh)
    rw [h1]
    exact Finset.mem_insert_self xS {yS}
  have hry : (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≠ tilde L (⊤ : Subgroup W) y := by
    intro hh
    apply hr
    have h1 : r = yS := Subtype.ext (by simpa using hh)
    rw [h1]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self yS)
  have hRirr : XMod.IsIrr ↥L (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) := r.2.2
  have hRle : (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤
      tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y := r.2.1
  set z : Subgroup W := modComm L ((r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))).comap
      (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) with hzdef
  have hzmem : z ∈ irrSet L := by
    rw [hzdef]
    exact (s16t3_lift hq hRirr).1
  have hzY : tilde L (⊤ : Subgroup W) z = (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) := by
    rw [hzdef]
    exact (s16t3_lift hq hRirr).2
  have hzx : z ≠ x := by
    intro hh
    apply hrx
    rw [← hzY, hh]
  have hzy : z ≠ y := by
    intro hh
    apply hry
    rw [← hzY, hh]
  refine ⟨?_, ?_⟩
  · refine ⟨z, ⟨hzmem, hzx, hzy, ?_⟩, ?_⟩
    · rw [hzY]
      exact hRle
    · intro z' hz'
      obtain ⟨hz'mem, hz'x, hz'y, hz'le⟩ := hz'
      have hYz' : XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) z') :=
        s16t3_isIrr_tilde_of_mem_irrSet hq hz'mem
      have hne_x : tilde L (⊤ : Subgroup W) z' ≠ tilde L (⊤ : Subgroup W) x :=
        fun hh => hz'x (hinj hz'mem hx hh)
      have hne_y : tilde L (⊤ : Subgroup W) z' ≠ tilde L (⊤ : Subgroup W) y :=
        fun hh => hz'y (hinj hz'mem hy hh)
      have hE' : ∀ φ : ↥(tilde L (⊤ : Subgroup W) x) ≃* ↥(tilde L (⊤ : Subgroup W) x),
          Z391.V2fEqv ↥L φ → φ = MulEquiv.refl _ := by
        intro φ hφ
        exact hEndX φ (fun l a b hab => hφ (l : ↥L) a b hab)
      have heq := Z391.v2f_eq_of_le_sup (A := ↥L)
        (P := tilde L (⊤ : Subgroup W) x) (P' := tilde L (⊤ : Subgroup W) y)
        (R := tilde L (⊤ : Subgroup W) z') (R' := (r : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))))
        hYx hYy hE' hYz' hRirr hz'le hRle hne_x hne_y hrx hry
      exact hinj hz'mem hzmem (heq.trans hzY.symm)
  · intro z' hz'mem hz'x hz'y hz'le
    have hYz' : XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) z') :=
      s16t3_isIrr_tilde_of_mem_irrSet hq hz'mem
    have hne_x : tilde L (⊤ : Subgroup W) x ≠ tilde L (⊤ : Subgroup W) z' :=
      fun hh => hz'x (hinj hz'mem hx hh.symm)
    have hinf_xz : tilde L (⊤ : Subgroup W) x ⊓ tilde L (⊤ : Subgroup W) z' = ⊥ :=
      Z391.v2f_inf_eq_bot hYx hYz' hne_x
    have hinf_xy : tilde L (⊤ : Subgroup W) x ⊓ tilde L (⊤ : Subgroup W) y = ⊥ :=
      Z391.v2f_inf_eq_bot hYx hYy hYxy
    have hrk_zx : rk ↥(tilde L (⊤ : Subgroup W) z') = rk ↥(tilde L (⊤ : Subgroup W) x) := by
      obtain ⟨e, -⟩ := hiso _ _ hYz' hYx
      show padicValNat 2 (Nat.card ↥(tilde L (⊤ : Subgroup W) z')) =
        padicValNat 2 (Nat.card ↥(tilde L (⊤ : Subgroup W) x))
      rw [Nat.card_congr e.toEquiv]
    have hrk_yx : rk ↥(tilde L (⊤ : Subgroup W) y) = rk ↥(tilde L (⊤ : Subgroup W) x) := by
      obtain ⟨e, -⟩ := hiso _ _ hYy hYx
      show padicValNat 2 (Nat.card ↥(tilde L (⊤ : Subgroup W) y)) =
        padicValNat 2 (Nat.card ↥(tilde L (⊤ : Subgroup W) x))
      rw [Nat.card_congr e.toEquiv]
    have h1 := rk_sup_add_rk_inf (tilde L (⊤ : Subgroup W) x) (tilde L (⊤ : Subgroup W) z')
    rw [hinf_xz, rk_bot, hrk_zx] at h1
    have h2 := rk_sup_add_rk_inf (tilde L (⊤ : Subgroup W) x) (tilde L (⊤ : Subgroup W) y)
    rw [hinf_xy, rk_bot, hrk_yx] at h2
    exact eq_of_le_of_rk_le hQ (sup_le le_sup_left hz'le) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
