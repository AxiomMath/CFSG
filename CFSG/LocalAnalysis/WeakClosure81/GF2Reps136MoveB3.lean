module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveB1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Faith
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136ZCent
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136RealTwist
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_mul_inv_mem_sup {g : MulAut W} {A B C : Subgroup W}
    (hA : ∀ a ∈ A, g a * a⁻¹ ∈ C) (hB : ∀ b ∈ B, g b * b⁻¹ ∈ C) :
    ∀ w ∈ A ⊔ B, g w * w⁻¹ ∈ C := by
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
  have hle : A ⊔ B ≤ S := sup_le (fun x hx => hA x hx) (fun y hy => hB y hy)
  exact hle

private theorem w1369_move_map_Cd (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W}
    (S : Move136 Y t L I) : (Cd L).map t.toMonoidHom = Cd L := by
  have hfixV : (fixV L).map t.toMonoidHom = fixV L := by
    have h := CFSG.Quasithin.fixV_map_conj_eq L t
    rw [S.ctx.hfix L S.ctx.comp] at h
    exact h.symm
  calc (Cd L).map t.toMonoidHom
      = (I ⊓ fixV L).map t.toMonoidHom := by rw [(move_C hw2 S).1]
    _ = I.map t.toMonoidHom ⊓ (fixV L).map t.toMonoidHom :=
          Subgroup.map_inf I (fixV L) t.toMonoidHom t.injective
    _ = I.map t.toMonoidHom ⊓ fixV L := by rw [hfixV]
    _ = I ⊓ fixV L := (move_C hw2 S).2
    _ = Cd L := ((move_C hw2 S).1).symm

private theorem w1369_move_nontrivial (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W}
    (S : Move136 Y t L I) : ∃ k ∈ L, ∃ u ∈ I, k u * u⁻¹ ∉ Cd L := by
  by_contra h
  have htriv : ∀ k ∈ L, ∀ u ∈ I, k u * u⁻¹ ∈ Cd L := by
    intro k hk u hu
    by_contra hc
    exact h ⟨k, hk, u, hu, hc⟩
  have hle : commSub I L ≤ Cd L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, u, hu, rfl⟩
    exact htriv k hk u hu
  have hle' : I ≤ Cd L := by
    rw [← S.hI.1]
    exact hle
  have hlt : Cd L < I := by
    rw [(move_C hw2 S).1]
    exact S.hI.2.1
  exact (not_le_of_gt hlt) hle'

private theorem w1369_move_faithful_on_I (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W}
    (S : Move136 Y t L I) (hT : Tcl Y L) : FaithOn L I (Cd L) := by
  have hCstable : StableUnder L (Cd L) := by
    rw [(move_C hw2 S).1]
    exact S.hI.2.2.2.1
  have hLI : L ≤ stabSub I := by
    intro l hl
    rw [CFSG.Quasithin.mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := S.hI.2.2.1 l⁻¹ (L.inv_mem hl) (l u) hu
      simpa using h
    · intro hu
      exact S.hI.2.2.1 l hl u hu
  have hLC : L ≤ stabSub (Cd L) := by
    intro l hl
    rw [CFSG.Quasithin.mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := hCstable l⁻¹ (L.inv_mem hl) (l u) hu
      simpa using h
    · intro hu
      exact hCstable l hl u hu
  let ρ : ↥L →* MulAut (Sect I (Cd L)) := B5.secHom L hLI hLC
  let KI : Subgroup ↥L := ρ.ker
  have hq : CFSG.IsQuasisimple ↥L :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr S.ctx.comp.2.2
  have hKtop_ne : KI ≠ ⊤ := by
    intro htop
    obtain ⟨k, hk, u, hu, hku⟩ := w1369_move_nontrivial hw2 S
    have hmem : (⟨k, hk⟩ : ↥L) ∈ KI := by rw [htop]; exact Subgroup.mem_top _
    have hc := (B5.mem_ker_secHom L hLI hLC ⟨k, hk⟩).mp hmem
    have htriv := (mem_centSec.mp hc).2 u hu
    exact hku (by simpa using htriv)
  have hKcenter : KI ≤ Subgroup.center ↥L := by
    rcases CFSG.Quasithin.H13.Ch4.J4KX.normal_le_center_or_top hq KI with h | h
    · exact h
    · exact absurd h hKtop_ne
  intro a ha haTriv
  have hacent : ((⟨a, ha⟩ : ↥L) : MulAut W) ∈ centSec I (Cd L) :=
    mem_centSec.mpr ⟨hLI ha, haTriv⟩
  have haKer : (⟨a, ha⟩ : ↥L) ∈ KI :=
    (B5.mem_ker_secHom L hLI hLC ⟨a, ha⟩).mpr hacent
  have haCenter : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := hKcenter haKer
  have hzc : ∀ l ∈ L, l * a = a * l := by
    intro l hl
    have h := Subgroup.mem_center_iff.mp haCenter ⟨l, hl⟩
    simpa using h
  have htacomm : t * a = a * t := center_cent_t S.ctx ha hzc
  have hCdmap : (Cd L).map t.toMonoidHom = Cd L := w1369_move_map_Cd hw2 S
  have hIt : ∀ v ∈ I.map t.toMonoidHom, a v * v⁻¹ ∈ Cd L := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    change a (t u) * (t u)⁻¹ ∈ Cd L
    have h1 : a (t u) = t (a u) := by
      have h := congrArg (fun f : MulAut W => f u) htacomm
      simpa [MulAut.mul_apply] using h.symm
    have hx : a u * u⁻¹ ∈ Cd L := haTriv u hu
    have htx : t (a u * u⁻¹) ∈ Cd L := by
      rw [← hCdmap]
      exact Subgroup.mem_map.mpr ⟨a u * u⁻¹, hx, rfl⟩
    have heq : a (t u) * (t u)⁻¹ = t (a u * u⁻¹) := by
      rw [h1, ← map_inv t u, ← map_mul t (a u) u⁻¹]
    rw [heq]
    exact htx
  have haWd : ∀ w ∈ Wd L, a w * w⁻¹ ∈ Cd L := by
    intro w hw
    rw [move_W hw2 S] at hw
    exact w1369_mul_inv_mem_sup (g := a) (A := I) (B := I.map t.toMonoidHom)
      (C := Cd L) haTriv hIt w hw
  exact faithful_on_wstar hw2 S.ctx hT a ha haWd

theorem move_isSL3 (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) (hT : Tcl Y L) :
    IsSLn ↥L 3 1 := by
  have hstab : StabPair L I (Cd L) := fun l hl =>
    ⟨S.hI.2.2.1 l hl, by
      rw [(move_C hw2 S).1]
      exact S.hI.2.2.2.1 l hl⟩
  have hf : FaithOn L I (Cd L) := w1369_move_faithful_on_I hw2 S hT
  obtain ⟨eL⟩ := mulEquiv_secSub hstab hf
  have hsub : secSub I (Cd L) L = ⊤ := (move_gl3 hw2 S).1
  have hcard : Nat.card (Sect I (Cd L)) = 2 ^ 3 := (move_gl3 hw2 S).2
  obtain ⟨em⟩ := CFSG.Quasithin.S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (sect_exp_two hw2 I (Cd L)) hcard
  have htop : StatedSL 3 (ZMod 2) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact CFSG.Open.StatedAPI.mem_statedSL_zmod_two g
  let e1 : ↥L ≃* MulAut (Sect I (Cd L)) :=
    (eL.trans (MulEquiv.subgroupCongr hsub)).trans Subgroup.topEquiv
  let e2 : MulAut (Sect I (Cd L)) ≃* GL (Fin 3) (ZMod 2) :=
    (MulAut.congr em).trans (CFSG.Quasithin.S153E58.mulAutPiEquivGL 3)
  let e3 : GL (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod], ⟨e1.trans (e2.trans e3)⟩⟩

theorem move_natural (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) (hT : Tcl Y L) :
    BinaryNaturalSL L I (Cd L) 3 1 := by
  have hL3 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16k_isLn_of_isSLn (n := 3) (by norm_num)
      (move_isSL3 hw2 S hT)
  have hCstable : StableUnder L (Cd L) := by
    rw [(move_C hw2 S).1]
    exact S.hI.2.2.2.1
  have hCI : Cd L ≤ I := by
    rw [(move_C hw2 S).1]
    exact inf_le_left
  have hcard : Nat.card (Sect I (Cd L)) = 8 := by
    have h := (move_gl3 hw2 S).2
    simpa using h
  exact CFSG.LocalAnalysis.WeakClosure81.s134b_natural_of_card_eight hw2 hL3 hCI
    S.hI.2.2.1 hCstable hcard (w1369_move_nontrivial hw2 S)

private theorem w1369_move_natural_twist (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W}
    (S : Move136 Y t L I) (hT : Tcl Y L) :
    BinaryNaturalSL L (I.map t.toMonoidHom) (Cd L) 3 1 := by
  obtain ⟨K, hF, hFin, hcard, hreal⟩ := move_natural hw2 S hT
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact S.ctx.hfix L S.ctx.comp
  have h := realizes_twist (D := FFModel.nat (StatedSL 3 K)) (g := t) htN hreal
  rw [w1369_move_map_Cd hw2 S] at h
  exact ⟨K, hF, hFin, hcard, h⟩

theorem move_sum_of_nat (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) (hT : Tcl Y L) :
    SumOfAtMostThreeNat L (Wd L) (Cd L) := by
  have hC1 : Cd L = I ⊓ fixV L := (move_C hw2 S).1
  have hC2 : I.map t.toMonoidHom ⊓ fixV L = I ⊓ fixV L := (move_C hw2 S).2
  have hCdI : Cd L ≤ I := by rw [hC1]; exact inf_le_left
  have hCdIt : Cd L ≤ I.map t.toMonoidHom := by rw [hC1, ← hC2]; exact inf_le_left
  have hII : I ⊓ I.map t.toMonoidHom = Cd L := by
    apply le_antisymm
    · intro w hw
      rw [hC1]
      exact ⟨hw.1, move_inter hw2 S hw⟩
    · intro w hw
      exact ⟨hCdI hw, hCdIt hw⟩
  have hindep : I ⊓ (Cd L ⊔ I.map t.toMonoidHom) ≤ Cd L := by
    intro w hw
    obtain ⟨hwI, hw⟩ := hw
    obtain ⟨c, hc, v, hv, hcv⟩ := Subgroup.mem_sup.mp hw
    have hcI : c ∈ I := hCdI hc
    have hvI : v ∈ I := by
      have hm : c⁻¹ * w ∈ I := I.mul_mem (I.inv_mem hcI) hwI
      rw [← hcv] at hm
      simpa using hm
    have hvCd : v ∈ Cd L := by
      rw [hC1]
      exact ⟨hvI, move_inter hw2 S ⟨hvI, hv⟩⟩
    rw [← hcv]
    exact (Cd L).mul_mem hc hvCd
  have hindep_t : I.map t.toMonoidHom ⊓ (Cd L ⊔ I) ≤ Cd L := by
    intro w hw
    obtain ⟨hwI, hw⟩ := hw
    obtain ⟨c, hc, v, hv, hcv⟩ := Subgroup.mem_sup.mp hw
    have hcI : c ∈ I.map t.toMonoidHom := hCdIt hc
    have hvI : v ∈ I.map t.toMonoidHom := by
      have hm : c⁻¹ * w ∈ I.map t.toMonoidHom :=
        (I.map t.toMonoidHom).mul_mem ((I.map t.toMonoidHom).inv_mem hcI) hwI
      rw [← hcv] at hm
      simpa using hm
    have hvCd : v ∈ Cd L := by
      rw [hC1]
      exact ⟨hv, move_inter hw2 S ⟨hv, hvI⟩⟩
    rw [← hcv]
    exact (Cd L).mul_mem hc hvCd
  let J : Fin 2 → Subgroup W := ![I, I.map t.toMonoidHom]
  have hJ0 : (⨆ (j : Fin 2) (_ : j ≠ 0), J j) = J 1 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro j
      refine iSup_le ?_
      intro hj
      fin_cases j
      · exact absurd rfl hj
      · exact le_rfl
    · exact le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
  have hJ1 : (⨆ (j : Fin 2) (_ : j ≠ 1), J j) = J 0 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro j
      refine iSup_le ?_
      intro hj
      fin_cases j
      · exact le_rfl
      · exact absurd rfl hj
    · exact le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl)
  have hsupJ : (⨆ i : Fin 2, J i) = J 0 ⊔ J 1 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup J 0) (le_iSup J 1)
  refine ⟨2, by norm_num, 3, Or.inl ⟨move_isSL3 hw2 S hT, ?_⟩⟩
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [J, Matrix.cons_val_zero] using hCdI
    · simpa [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hCdIt
  · intro i
    fin_cases i
    · change J 0 ⊓ (Cd L ⊔ ⨆ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), J j) ≤ Cd L
      rw [hJ0]
      simpa [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hindep
    · change J 1 ⊓ (Cd L ⊔ ⨆ (j : Fin 2) (_ : j ≠ (1 : Fin 2)), J j) ≤ Cd L
      rw [hJ1]
      simpa [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hindep_t
  · change Cd L ⊔ (⨆ i : Fin 2, J i) = Wd L
    rw [hsupJ]
    simp only [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [move_W hw2 S]
    apply le_antisymm
    · exact sup_le (hCdI.trans le_sup_left) le_rfl
    · exact le_sup_right
  · intro i
    fin_cases i
    · simpa [J, Matrix.cons_val_zero] using move_natural hw2 S hT
    · simpa [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        using w1369_move_natural_twist hw2 S hT

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
