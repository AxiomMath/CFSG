module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Structure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.Quasithin.Background.HTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.Quasithin.Background.FFC12E
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4PlusUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVInvolN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {W : Type} [CommGroup W]

theorem commV_eq_or_exists_two [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) (hsum : IsDirSumOver (conjSet L Y) commV)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    commV L = I ∨ ∃ J ∈ irrSet L, I ⊓ J = ⊥ ∧ 2 * rk ↥I ≤ rk ↥(commV L) ∧
      (rk ↥(commV L) < 3 * rk ↥I → commV L = I ⊔ J) := by
  obtain ⟨s, hIs, hsL, hsind, hsup⟩ := exists_sSupIndep_irrSet hW hO2 hirr hL hfix hsum hI
  have hrk : ∀ J ∈ s, rk ↥J = rk ↥I := fun J hJ =>
    rk_eq_of_mem_irrSet hW hO2 hirr hL hfix hsum hI (hsL hJ)
  by_cases hsI : ∀ J ∈ s, J = I
  · left
    rw [← hsup]
    refine le_antisymm (sSup_le fun J hJ => (hsI J hJ).le) (le_sSup hIs)
  · right
    push Not at hsI
    obtain ⟨J, hJs, hJI⟩ := hsI
    have hIJ : I ⊓ J = ⊥ := by
      have h := hsind hIs
      have hJle : J ≤ sSup (s \ {I}) := le_sSup ⟨hJs, hJI⟩
      exact disjoint_iff.mp (h.mono_right hJle)
    have hIJrk : rk ↥(I ⊔ J) = 2 * rk ↥I := by
      have h := rk_sup_add_rk_inf I J
      rw [hIJ, rk_bot, add_zero, hrk J hJs] at h
      omega
    have hIJle : I ⊔ J ≤ commV L := hsup ▸ sup_le (le_sSup hIs) (le_sSup hJs)
    refine ⟨J, hsL hJs, hIJ, hIJrk ▸ rk_mono hIJle, fun hlt => ?_⟩
    by_contra hne
    have hnle : ¬ sSup s ≤ I ⊔ J := fun h => hne (le_antisymm (hsup ▸ h) hIJle)
    obtain ⟨J', hJ's, hJ'⟩ : ∃ J' ∈ s, ¬ J' ≤ I ⊔ J := by
      by_contra hall
      push Not at hall
      exact hnle (sSup_le hall)
    have hJ'I : J' ≠ I := fun h => hJ' (h ▸ le_sup_left)
    have hJ'J : J' ≠ J := fun h => hJ' (h ▸ le_sup_right)
    have hJ'IJ : J' ⊓ (I ⊔ J) = ⊥ := by
      have h := hsind hJ's
      have hle : I ⊔ J ≤ sSup (s \ {J'}) :=
        sup_le (le_sSup ⟨hIs, hJ'I.symm⟩) (le_sSup ⟨hJs, hJ'J.symm⟩)
      exact disjoint_iff.mp (h.mono_right hle)
    have h3 : rk ↥(J' ⊔ (I ⊔ J)) = 3 * rk ↥I := by
      have h := rk_sup_add_rk_inf J' (I ⊔ J)
      rw [hJ'IJ, rk_bot, add_zero, hrk J' hJ's, hIJrk] at h
      omega
    have hle3 : J' ⊔ (I ⊔ J) ≤ commV L := hsup ▸ sup_le (le_sSup hJ's) (hsup ▸ hIJle)
    have := rk_mono hle3
    omega

theorem le_mParam_autSub_of_natural [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y) {I : Subgroup W} (hI : I ∈ irrSet L)
    (hIfix : I ⊓ fixV L = ⊥)
    (hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W))) {k : ℕ}
    (hnat : IsNaturalClassicalModule (autSub L I) k) : k ≤ E3.mParam (autSub Y I) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite (MulAut ↥I) :=
    Finite.of_injective (fun f : MulAut ↥I => (f : ↥I → ↥I)) DFunLike.coe_injective
  have hLI := le_stabSub_of_mem_irrSet hI
  have hne := not_le_centSub_of_mem_irrSet hI hIfix
  have hq := B1Red.isQuasisimple_autSub hLI hL.2.2 hne
  have hLY : autSub L I ≤ autSub Y I := autSub_mono hL.1 I
  have heven : Even (Nat.card ↥(autSub Y I)) := by
    have h1 : ¬ Odd (Nat.card ↥(autSub L I)) := B69.not_odd_card_quasisimple hq
    rw [Nat.not_odd_iff_even] at h1
    exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp h1).trans (Subgroup.card_dvd_of_le hLY))
  exact le_mParam_of_isNaturalClassicalModule (fun w => Subtype.ext (hW w)) hLY
    (normal_autSub_of_normalizes hnormI) (isIrrOn_autSub_of_mem_irrSet hI hIfix) hnat heven

private theorem map_commV_le (X : Subgroup (MulAut W)) (g : MulAut W) :
    (commV X).map g.toMonoidHom ≤ commV (X.map (MulAut.conj g).toMonoidHom) := by
  rw [commV, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨x, hx, w, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, g w, ?_⟩
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem map_conj_eq_of_secIsoOn {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV) {I J : Subgroup W} (hI : I ∈ irrSet L)
    (hJ : J ∈ irrSet L) (hJfix : J ⊓ fixV L = ⊥) {g : MulAut W} (hg : g ∈ Y)
    (hsec : SecIsoOn L (I.map g.toMonoidHom) ⊥ J ⊥) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  by_contra hne
  obtain ⟨-, -, -, -, -, -, β, hβB, -, hβs, hβe⟩ := hsec
  have hLmem : L ∈ conjSet L Y := ⟨1, Y.one_mem, by ext x; simp⟩
  have hXmem : L.map (MulAut.conj g).toMonoidHom ∈ conjSet L Y := ⟨g, hg, rfl⟩
  have hIc : I ≤ commV L := by
    rw [commV_eq_commSub, ← hI.1]
    exact commSub_mono le_top le_rfl
  have hfixg : ∀ x ∈ L, ∀ a : ↥(I.map g.toMonoidHom), x (a : W) = (a : W) := by
    intro x hx a
    have ha : (a : W) ∈ commV (L.map (MulAut.conj g).toMonoidHom) :=
      map_commV_le L g (Subgroup.map_mono hIc a.2)
    exact apply_eq_of_mem_commV hLY hsum.1 hXmem hLmem hne hx ha
  have hJL : J ≤ fixV L := by
    intro b hb x hx
    obtain ⟨a, ha⟩ := hβs b hb
    rw [Subgroup.mem_bot, mul_inv_eq_one] at ha
    have h := hβe x hx a a (hfixg x hx a).symm
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    rw [← ha, ← h]
  apply WeakClosure81.ne_bot_of_mem_irrSet hJ
  rw [← hJfix]
  exact (inf_eq_left.mpr hJL).symm

theorem exists_mulEquiv_autSub_eq_map {L : Subgroup (MulAut W)} {I J : Subgroup W}
    {g : MulAut W} (hg : L.map (MulAut.conj g).toMonoidHom = L) (hLI : L ≤ stabSub I)
    (hLJ : L ≤ stabSub J) (hsec : SecIsoOn L (I.map g.toMonoidHom) ⊥ J ⊥) :
    ∃ ψ : ↥I ≃* ↥J, autSub L J = (autSub L I).map (H.congrHom ψ) := by
  obtain ⟨-, -, -, -, -, -, β, hβB, hβk, hβs, hβe⟩ := hsec
  let e : ↥I ≃* ↥(I.map g.toMonoidHom) := I.equivMapOfInjective g.toMonoidHom g.injective
  have he : ∀ u : ↥I, ((e u : ↥(I.map g.toMonoidHom)) : W) = g (u : W) := fun _ => rfl
  let f : ↥I →* ↥J := (β.comp e.toMonoidHom).codRestrict J fun _ => hβB _
  have hf : ∀ u : ↥I, ((f u : ↥J) : W) = β (e u) := fun _ => rfl
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : β (e u) ∈ (⊥ : Subgroup W) := by
      rw [Subgroup.mem_bot, ← hf, hu]
      rfl
    rw [hβk, Subgroup.mem_bot, he] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext ((map_eq_one_iff g g.injective).mp h1)
  have hfsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hβs b hb
    rw [Subgroup.mem_bot, mul_inv_eq_one] at ha
    refine ⟨e.symm a, Subtype.ext ?_⟩
    rw [hf, MulEquiv.apply_symm_apply, ha]
  let ψ : ↥I ≃* ↥J := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hψ : ∀ u : ↥I, ((ψ u : ↥J) : W) = β (e u) := fun _ => rfl
  have key : ∀ (l : MulAut W) (hl : l ∈ L) (u : ↥I), (g * l * g⁻¹) ((ψ u : ↥J) : W) =
      ((ψ ⟨l u, (hLI hl u).2 u.2⟩ : ↥J) : W) := by
    intro l hl u
    have hyL : g * l * g⁻¹ ∈ L := by
      rw [← hg]
      exact ⟨l, hl, rfl⟩
    have h := hβe _ hyL (e u) (e ⟨l u, (hLI hl u).2 u.2⟩) (by
      rw [he, he]
      simp [MulAut.mul_apply])
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    rw [hψ, hψ, ← h]
  refine ⟨ψ, ?_⟩
  ext φ
  rw [mem_autSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hyL, rfl⟩
    have hy' : (y : MulAut W) ∈ L.map (MulAut.conj g).toMonoidHom := hg.symm ▸ hyL
    obtain ⟨l, hl, hly⟩ := hy'
    refine ⟨resHom I ⟨l, hLI hl⟩, mem_autSub.mpr ⟨⟨l, hLI hl⟩, hl, rfl⟩, ?_⟩
    refine MulEquiv.ext fun w => Subtype.ext ?_
    obtain ⟨u, rfl⟩ := ψ.surjective w
    rw [H.congrHom_apply, MulEquiv.symm_apply_apply]
    have hyv : (y : MulAut W) = g * l * g⁻¹ := by
      rw [← hly]
      rfl
    change ((ψ ⟨l u, _⟩ : ↥J) : W) = (y : MulAut W) ((ψ u : ↥J) : W)
    rw [hyv, key l hl u]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hx
    have hyL : g * (l : MulAut W) * g⁻¹ ∈ L := by
      rw [← hg]
      exact ⟨l, hl, rfl⟩
    refine ⟨⟨g * (l : MulAut W) * g⁻¹, hLJ hyL⟩, hyL, ?_⟩
    refine MulEquiv.ext fun w => Subtype.ext ?_
    obtain ⟨u, rfl⟩ := ψ.surjective w
    rw [H.congrHom_apply, MulEquiv.symm_apply_apply]
    change (g * (l : MulAut W) * g⁻¹) ((ψ u : ↥J) : W) = ((ψ ⟨(l : MulAut W) u, _⟩ : ↥J) : W)
    exact key l hl u

theorem isNaturalClassicalModule_autSub_of_secIsoOn {L : Subgroup (MulAut W)} {I J : Subgroup W}
    {g : MulAut W} (hg : L.map (MulAut.conj g).toMonoidHom = L) (hLI : L ≤ stabSub I)
    (hLJ : L ≤ stabSub J) (hsec : SecIsoOn L (I.map g.toMonoidHom) ⊥ J ⊥) {k : ℕ}
    (hnat : IsNaturalClassicalModule (autSub L I) k) : IsNaturalClassicalModule (autSub L J) k := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_autSub_eq_map hg hLI hLJ hsec
  refine IsNaturalClassicalModule.of_map_congrHom ψ.symm ?_ hnat
  rw [hψ, Subgroup.map_map, H.LU.congrHom_symm_comp, Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
