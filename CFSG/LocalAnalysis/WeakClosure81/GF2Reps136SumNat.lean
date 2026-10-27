module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Faith
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136RealTwist
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TransIrr
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_mem_stabSub_of_invariant {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U :=
  mem_stabSub_of_invariant h (inv_mem_of_forall_mem g h)

private theorem w1369_mul_inv_mem_iSup {g : MulAut W} {C : Subgroup W} {ι : Type*}
    {A : ι → Subgroup W} (h : ∀ i, ∀ a ∈ A i, g a * a⁻¹ ∈ C) :
    ∀ w ∈ ⨆ i, A i, g w * w⁻¹ ∈ C := by
  let S : Subgroup W :=
    { carrier := {w | g w * w⁻¹ ∈ C}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change g (x * y) * (x * y)⁻¹ ∈ C
        have h : g (x * y) * (x * y)⁻¹ = (g x * x⁻¹) * (g y * y⁻¹) := by
          rw [map_mul, mul_inv]
          ac_rfl
        rw [h]
        exact C.mul_mem hx hy
      inv_mem' := by
        intro x hx
        change g x⁻¹ * (x⁻¹)⁻¹ ∈ C
        have h : g x⁻¹ * (x⁻¹)⁻¹ = (g x * x⁻¹)⁻¹ := by
          rw [map_inv, mul_inv]
        rw [h]
        exact C.inv_mem hx }
  have hS : ⨆ i, A i ≤ S := iSup_le fun i a ha => h i a ha
  intro w hw
  exact hS hw

private theorem w1369_mul_inv_mem_sup {g : MulAut W} {A B C : Subgroup W}
    (hA : ∀ a ∈ A, g a * a⁻¹ ∈ C) (hB : ∀ b ∈ B, g b * b⁻¹ ∈ C) :
    ∀ w ∈ A ⊔ B, g w * w⁻¹ ∈ C := by
  let f : Bool → Subgroup W := fun b => if b then A else B
  have hf : ∀ b, ∀ a ∈ f b, g a * a⁻¹ ∈ C := by
    intro b
    cases b
    · simpa [f] using hB
    · simpa [f] using hA
  have h := w1369_mul_inv_mem_iSup (C := C) (A := f) hf
  have hsup : ⨆ b, f b = A ⊔ B := by
    rw [iSup_bool_eq]
    simp [f]
  rwa [hsup] at h

private theorem w1369_perfect_of_component {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr c.comp.2.2.1)

private theorem w1369_trans_of_fixdec (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L)
    {r : ℕ} {J : Fin r → Subgroup W} (hD : FixDec t L r J) (m : Fin r) :
    ∀ i : Fin r, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      J i = (J m).map g.toMonoidHom := by
  intro i
  have hLp : ⁅L, L⁆ = L := w1369_perfect_of_component c
  have hIi : commSub (J i) L ∈ irrSet L :=
    (sect_to_irr hw2 hLp (hD.2.2.1 i).1 (hD.2.2.1 i).2.1 (hD.2.2.1 i).2.2.1).1
  have hIm : commSub (J m) L ∈ irrSet L :=
    (sect_to_irr hw2 hLp (hD.2.2.1 m).1 (hD.2.2.1 m).2.1 (hD.2.2.1 m).2.2.1).1
  obtain ⟨g, hg, hgIm⟩ := transitive_on_irr hw2 c hfix hT _ hIm _ hIi
  refine ⟨g, hg, ?_⟩
  have hJieq : commSub (J i) L ⊔ Cd L = J i := (hD.2.2.1 i).2.2.2.1
  have hJmeq : commSub (J m) L ⊔ Cd L = J m := (hD.2.2.1 m).2.2.2.1
  have hCdmap : (Cd L).map g.toMonoidHom = Cd L :=
    (irr_stab (Subgroup.mem_inf.mp hg).2).2.1
  calc J i = commSub (J i) L ⊔ Cd L := hJieq.symm
    _ = (commSub (J m) L).map g.toMonoidHom ⊔ Cd L := by rw [hgIm]
    _ = (commSub (J m) L).map g.toMonoidHom ⊔ (Cd L).map g.toMonoidHom := by rw [hCdmap]
    _ = (commSub (J m) L ⊔ Cd L).map g.toMonoidHom := (Subgroup.map_sup _ _ _).symm
    _ = (J m).map g.toMonoidHom := by rw [hJmeq]

private theorem w1369_faithful_on_cost_one (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L)
    {r : ℕ} {J : Fin r → Subgroup W} (hD : FixDec t L r J) (m : Fin r)
    (hcent : Subgroup.centralizer ((secSub (J m) (Cd L) L :
      Subgroup (MulAut (Sect (J m) (Cd L)))) : Set (MulAut (Sect (J m) (Cd L)))) = ⊥) :
    FaithOn L (J m) (Cd L) := by
  classical
  have hIrr := (hD.2.2.1 m).2.2.1
  have hLJm : L ≤ stabSub (J m) := fun l hl =>
    w1369_mem_stabSub_of_invariant fun u hu => hIrr.2.1 l hl u hu
  have hLC : L ≤ stabSub (Cd L) := fun l hl =>
    w1369_mem_stabSub_of_invariant fun u hu => hIrr.2.2.1 l hl u hu
  let ρ : ↥L →* MulAut (Sect (J m) (Cd L)) := B5.secHom L hLJm hLC
  let K : Subgroup ↥L := ρ.ker
  have hq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr c.comp.2.2
  have hKtop_ne : K ≠ ⊤ := by
    intro htop
    have hcomm : commSub (J m) L ≤ Cd L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, u, hu, rfl⟩
      have hmem : (⟨l, hl⟩ : ↥L) ∈ K := by rw [htop]; exact Subgroup.mem_top _
      have hc := (B5.mem_ker_secHom L hLJm hLC ⟨l, hl⟩).mp hmem
      exact (mem_centSec.mp hc).2 u hu
    have hCd_eq : Cd L = J m := by
      rw [← (hD.2.2.1 m).2.2.2.1, sup_eq_right.mpr hcomm]
    exact hIrr.1.ne hCd_eq
  have hKcenter : K ≤ Subgroup.center ↥L := by
    rcases CFSG.Quasithin.H13.Ch4.J4KX.normal_le_center_or_top hq K with h | h
    · exact h
    · exact absurd h hKtop_ne
  intro a ha haTriv
  have hacent : ((⟨a, ha⟩ : ↥L) : MulAut W) ∈ centSec (J m) (Cd L) :=
    mem_centSec.mpr ⟨hLJm ha, haTriv⟩
  have haKer : (⟨a, ha⟩ : ↥L) ∈ K :=
    (B5.mem_ker_secHom L hLJm hLC ⟨a, ha⟩).mpr hacent
  have haCenter : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := hKcenter haKer
  have hzc : ∀ l ∈ L, l * a = a * l := by
    intro l hl
    have h := Subgroup.mem_center_iff.mp haCenter ⟨l, hl⟩
    simpa using h
  have htriv_all : ∀ i : Fin r, ∀ v ∈ J i, a v * v⁻¹ ∈ Cd L := by
    intro i v hv
    obtain ⟨g, hg, hgJ⟩ := w1369_trans_of_fixdec hw2 c hfix hT hD m i
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
    rw [hgJ] at hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    have hgag_comm : ∀ l ∈ L, l * (g⁻¹ * a * g) = (g⁻¹ * a * g) * l := by
      intro l hl
      have hl' : g * l * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hgN l).mp hl
      have h1 := hzc (g * l * g⁻¹) hl'
      calc l * (g⁻¹ * a * g) = g⁻¹ * ((g * l * g⁻¹) * a) * g := by group
        _ = g⁻¹ * (a * (g * l * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * a * g) * l := by group
    have hgagL : g⁻¹ * a * g ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hgN) a).mp ha
    have hcent' : B5.secHom L hLJm hLC ⟨g⁻¹ * a * g, hgagL⟩ ∈
        Subgroup.centralizer (secSub (J m) (Cd L) L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ψ hψ
      have hψ' : ψ ∈ (B5.secHom L hLJm hLC).range := by
        rw [B5.range_secHom]
        exact hψ
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hψ'
      show B5.secHom L hLJm hLC l * B5.secHom L hLJm hLC ⟨g⁻¹ * a * g, hgagL⟩ =
           B5.secHom L hLJm hLC ⟨g⁻¹ * a * g, hgagL⟩ * B5.secHom L hLJm hLC l
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hgag_comm (l : MulAut W) l.2)
    have hx1 : B5.secHom L hLJm hLC ⟨g⁻¹ * a * g, hgagL⟩ = 1 := by
      rw [hcent] at hcent'
      exact Subgroup.mem_bot.mp hcent'
    have hxker : (⟨g⁻¹ * a * g, hgagL⟩ : ↥L) ∈ (B5.secHom L hLJm hLC).ker := by
      rw [MonoidHom.mem_ker]; exact hx1
    have hxcent := (B5.mem_ker_secHom L hLJm hLC ⟨g⁻¹ * a * g, hgagL⟩).mp hxker
    have hgagtriv : (g⁻¹ * a * g) u * u⁻¹ ∈ Cd L := (mem_centSec.mp hxcent).2 u hu
    have heq : a (g u) * (g u)⁻¹ = g ((g⁻¹ * a * g) u * u⁻¹) := by
      simp [MulAut.mul_apply, map_mul, map_inv, mul_assoc]
    have hCdmap : (Cd L).map g.toMonoidHom = Cd L :=
      (irr_stab (Subgroup.mem_inf.mp hg).2).2.1
    change a (g u) * (g u)⁻¹ ∈ Cd L
    rw [heq, ← hCdmap]
    exact Subgroup.mem_map.mpr ⟨(g⁻¹ * a * g) u * u⁻¹, hgagtriv, rfl⟩
  have haWd : ∀ w ∈ Wd L, a w * w⁻¹ ∈ Cd L := by
    intro w hw
    rw [← hD.2.2.2.2.1] at hw
    refine w1369_mul_inv_mem_sup ?_ ?_ w hw
    · intro c hc
      have hcfix : a c = c := hc.2 a ha
      have h1 : a c * c⁻¹ = 1 := by rw [hcfix, mul_inv_cancel]
      rw [h1]
      exact (Cd L).one_mem
    · exact fun v hv => w1369_mul_inv_mem_iSup (C := Cd L) (A := fun i : Fin r => J i)
        (fun i => htriv_all i) v hv
  exact faithful_on_wstar hw2 c hT a ha haWd

private theorem w1369_sumOfNat_realizes (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L)
    {r : ℕ} {J : Fin r → Subgroup W} (hD : FixDec t L r J) (m : Fin r) {D : FFModel}
    (hreal : D.Realizes L (J m) (Cd L)) :
    SumOfNat (fun H U Z => D.Realizes H U Z) L (Wd L) (Cd L) r := by
  refine ⟨J, (fun i => (hD.2.2.1 i).1), (fun i => hD.2.2.2.1 i), hD.2.2.2.2.1, ?_⟩
  intro i
  obtain ⟨g, hg, hgJ⟩ := w1369_trans_of_fixdec hw2 c hfix hT hD m i
  rw [hgJ]
  have hCdmap : (Cd L).map g.toMonoidHom = Cd L :=
    (irr_stab (Subgroup.mem_inf.mp hg).2).2.1
  have h := realizes_twist D (Subgroup.mem_inf.mp hg).2 hreal
  rwa [hCdmap] at h

private theorem w1369_isSpn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n a : ℕ} (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hn, K, hKf, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hKf, hKfin, hcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n : ℕ} (h : IsAlt n X) : IsAlt n Y := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem sum_of_nat (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L)
    (hr : ¬ IsIrrOn L (Wd L) (Cd L)) : SumOfAtMostThreeNat L (Wd L) (Cd L) := by
  classical
  obtain ⟨r, J, hD⟩ := fix_decomp hw2 c hfix
  have hr2 : 2 ≤ r := by
    by_contra h
    have hr1 : r = 1 := by
      have h1r : 1 ≤ r := hD.1
      omega
    have hspan := hD.2.2.2.2.1
    have hJ0 : (⨆ i : Fin r, J i) = J ⟨0, by omega⟩ := by
      apply le_antisymm
      · exact iSup_le fun i => by
          have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
          rw [hi]
      · exact le_iSup J _
    rw [hJ0] at hspan
    have hCdJ : Cd L ≤ J ⟨0, by omega⟩ := (hD.2.2.1 _).1
    have hJ0Wd : J ⟨0, by omega⟩ = Wd L := by
      rw [← hspan]
      exact (sup_eq_right.mpr hCdJ).symm
    have hirr := (hD.2.2.1 ⟨0, by omega⟩).2.2.1
    rw [hJ0Wd] at hirr
    exact hr hirr
  obtain ⟨m, hm⟩ : ∃ m : Fin r, tcost t L (J m) = 1 := by
    by_contra h
    rw [not_exists] at h
    have hge : ∀ i : Fin r, 2 ≤ tcost t L (J i) := by
      intro i
      have h1 : 1 ≤ tcost t L (J i) := (hD.2.2.1 i).2.2.2.2.2
      have hne : tcost t L (J i) ≠ 1 := h i
      omega
    have hsum : 2 * r ≤ ∑ i, tcost t L (J i) := by
      have h1 : (2 : ℕ) * r = ∑ _ : Fin r, 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Nat.mul_comm 2 r
      rw [h1]
      exact Finset.sum_le_sum (fun i _ => hge i)
    have h3 : (∑ i, tcost t L (J i)) ≤ 3 := hD.2.2.2.2.2
    omega
  have hMcLm := cost_one_summand hw2 c (hD.2.2.1 m).1 (hD.2.2.1 m).2.1
    (hD.2.2.1 m).2.2.1 (hD.2.2.1 m).2.2.2.1 (hD.2.2.1 m).2.2.2.2.1 hm
  have hfaith := w1369_faithful_on_cost_one hw2 c hfix hT hD m hMcLm.1
  have hstab : StabPair L (J m) (Cd L) := fun l hl =>
    ⟨(hD.2.2.1 m).2.2.1.2.1 l hl, (hD.2.2.1 m).2.2.1.2.2.1 l hl⟩
  obtain ⟨eL⟩ := mulEquiv_secSub hstab hfaith
  rcases hMcLm.2 with ⟨n, hSLn, hNat⟩ | ⟨n, hSpn, hNat⟩ | ⟨n, hOmegaP, hNat⟩ |
    ⟨n, hOmegaM, hNat⟩ | ⟨n, hAlt, hNat⟩
  ·
    obtain ⟨K, hKf, hKfin, hKcard, hreal_sub⟩ := hNat
    have hreal := (realizes_secSub_iff _ hstab (hD.2.2.1 m).1 hfaith).mp hreal_sub
    refine ⟨r, hD.2.1, n, Or.inl ⟨?_, ?_⟩⟩
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn.of_mulEquiv eL.symm hSLn
    · obtain ⟨I, hZI, hind, hspan, hreal'⟩ :=
        w1369_sumOfNat_realizes hw2 c hfix hT hD m hreal
      exact ⟨I, hZI, hind, hspan, fun i => ⟨K, hKf, hKfin, hKcard, hreal' i⟩⟩
  ·
    obtain ⟨hEven, K, hKf, hKfin, hKcard, hreal_sub⟩ := hNat
    have hreal := (realizes_secSub_iff _ hstab (hD.2.2.1 m).1 hfaith).mp hreal_sub
    refine ⟨r, hD.2.1, n, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · exact w1369_isSpn_of_mulEquiv eL.symm hSpn
    · obtain ⟨I, hZI, hind, hspan, hreal'⟩ :=
        w1369_sumOfNat_realizes hw2 c hfix hT hD m hreal
      exact ⟨I, hZI, hind, hspan, fun i => ⟨hEven, K, hKf, hKfin, hKcard, hreal' i⟩⟩
  ·
    obtain ⟨hEven, K, hKf, hKfin, hKcard, hreal_sub⟩ := hNat
    have hreal := (realizes_secSub_iff _ hstab (hD.2.2.1 m).1 hfaith).mp hreal_sub
    refine ⟨r, hD.2.1, n, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaPlus.of_mulEquiv eL.symm hOmegaP
    · obtain ⟨I, hZI, hind, hspan, hreal'⟩ :=
        w1369_sumOfNat_realizes hw2 c hfix hT hD m hreal
      exact ⟨I, hZI, hind, hspan, fun i => ⟨hEven, K, hKf, hKfin, hKcard, hreal' i⟩⟩
  ·
    obtain ⟨hEven, K, hKf, hKfin, b, c₀, hKcard, hquad, hreal_sub⟩ := hNat
    have hreal := (realizes_secSub_iff _ hstab (hD.2.2.1 m).1 hfaith).mp hreal_sub
    refine ⟨r, hD.2.1, n, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))⟩
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaMinus.of_mulEquiv eL.symm hOmegaM
    · obtain ⟨I, hZI, hind, hspan, hreal'⟩ :=
        w1369_sumOfNat_realizes hw2 c hfix hT hD m hreal
      exact ⟨I, hZI, hind, hspan, fun i => ⟨hEven, K, hKf, hKfin, b, c₀, hKcard, hquad, hreal' i⟩⟩
  ·
    have hreal := (realizes_secSub_iff _ hstab (hD.2.2.1 m).1 hfaith).mp hNat
    refine ⟨r, hD.2.1, n, Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))⟩
    · exact w1369_isAlt_of_mulEquiv eL.symm hAlt
    · obtain ⟨I, hZI, hind, hspan, hreal'⟩ :=
        w1369_sumOfNat_realizes hw2 c hfix hT hD m hreal
      exact ⟨I, hZI, hind, hspan, hreal'⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
