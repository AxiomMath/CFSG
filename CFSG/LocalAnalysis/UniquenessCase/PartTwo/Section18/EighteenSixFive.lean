module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.RankThree.PartOne.KS.Plane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_le_stabTil_general {V₀ V X : Subgroup G}
    (hX : X ≤ stabTil V₀ V) : ⁅V, X⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hX.trans (stabTil_le_normalizer V₀ V))

theorem mkTil_commutator_mem_commSub_of_mem {V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil V₀ V) {W : Subgroup (Vtil V₀ V hV)} {v x : G}
    (hv : v ∈ V) (hx : x ∈ X)
    (hW : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈ W) :
    mkTil V₀ V hV (IntMod.mk hV ⟨⁅v, x⁆, commutator_le_of_le_stabTil_general hX
      (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub W (barSub V₀ V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil_general hX
  have hsq : ∀ w : Vtil V₀ V hV, w⁻¹ = w := by
    intro w
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
    have h2 : (mkTil V₀ V hV y) ^ 2 = 1 := by
      rw [← map_pow, IntMod.sq_eq_one y, map_one]
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hmul : ∀ a b : Vtil V₀ V hV, a * b = b * a := fun a b => mul_comm a b
  set xb : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨x, hX hx⟩ with hxb
  set a : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) with ha
  have hmem3 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer V₀ V (hX hx)) v⁻¹).1 (V.inv_mem hv)
  have hc : mkTil V₀ V hV (IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩) = xb a⁻¹ := by
    rw [hxb, ha, ← map_inv, actTil_mk]
    rw [show (actStab V₀ V hV ⟨x, hX hx⟩) (IntMod.mk hV ⟨v, hv⟩)⁻¹ =
        IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ from by
      rw [map_inv]
      congr 1
      apply IntMod.val_injective
      rw [IntMod.val_inv, actStab_apply_val]
      group
      rfl]
  have h1 : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
  have hval : v * (x * v⁻¹ * x⁻¹) ∈ V := V.mul_mem hv hmem3
  have h2 : mkTil V₀ V hV (IntMod.mk hV ⟨⁅v, x⁆, hcommV
      (Subgroup.commutator_mem_commutator hv hx)⟩) = xb a * a⁻¹ := by
    have h3 : IntMod.mk hV ⟨⁅v, x⁆, hcommV
        (Subgroup.commutator_mem_commutator hv hx)⟩ =
        IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ := Subtype.ext h1
    rw [h3]
    have h4 : IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ =
        IntMod.mk hV ⟨v, hv⟩ * IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ := rfl
    rw [h4, map_mul, hc]
    simp only [hsq]
    change a * xb a = xb a * a
    exact hmul a (xb a)
  rw [h2]
  exact Subgroup.subset_closure ⟨xb, actTil_mem_barSub V₀ V hV hx (hX hx), a, hW, rfl⟩

theorem imgTil_commutator_eq_commSub_of_le {V₀ V A X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ V) (hX : X ≤ stabTil V₀ V) :
    imgTil V₀ V hV ⁅A, X⁆ = commSub (imgTil V₀ V hV A) (barSub V₀ V hV X) := by
  classical
  have hcommV : ⁅A, X⁆ ≤ V := (Subgroup.commutator_mono hA le_rfl).trans
    (commutator_le_of_le_stabTil_general hX)
  apply le_antisymm
  · rw [imgTil, Subgroup.map_le_iff_le_comap]
    intro w hw
    rw [Subgroup.mem_comap]
    have hmain : ∀ (a : G) (ha : a ∈ ⁅A, X⁆), mkTil V₀ V hV
        (IntMod.mk hV ⟨a, hcommV ha⟩) ∈
        commSub (imgTil V₀ V hV A) (barSub V₀ V hV X) := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨v, hv, x, hx, rfl⟩ := ha
        have hW : mkTil V₀ V hV (IntMod.mk hV ⟨v, hA hv⟩) ∈ imgTil V₀ V hV A :=
          (mem_imgTil V₀ V hV A _).2 ⟨IntMod.mk hV ⟨v, hA hv⟩, hv, rfl⟩
        exact mkTil_commutator_mem_commSub_of_mem hV hX (hA hv) hx hW
      | one =>
        rw [show IntMod.mk hV ⟨1, hcommV (one_mem _)⟩ = 1 from Subtype.ext rfl, map_one]
        exact one_mem _
      | mul a b ha hb iha ihb =>
        rw [show IntMod.mk hV ⟨a * b, hcommV (mul_mem ha hb)⟩ =
          IntMod.mk hV ⟨a, hcommV ha⟩ * IntMod.mk hV ⟨b, hcommV hb⟩ from Subtype.ext rfl,
          map_mul]
        exact mul_mem iha ihb
      | inv a ha iha =>
        rw [show IntMod.mk hV ⟨a⁻¹, hcommV (inv_mem ha)⟩ =
          (IntMod.mk hV ⟨a, hcommV ha⟩)⁻¹ from Subtype.ext rfl, map_inv]
        exact inv_mem iha
    have hw' : IntMod.mk hV ⟨w.val, hcommV hw⟩ = w := IntMod.val_injective rfl
    have hres := hmain w.val hw
    rwa [hw'] at hres
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨xb, hxb, w, hw, rfl⟩
    change xb w * w⁻¹ ∈ imgTil V₀ V hV ⁅A, X⁆
    rw [mem_imgTil]
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X xb).1 hxb
    obtain ⟨z, hzA, hzw⟩ := (mem_imgTil V₀ V hV A w).1 hw
    rw [← hzw]
    obtain ⟨v, rfl⟩ : ∃ v : ↥V, IntMod.mk hV v = z :=
      ⟨⟨z.val, z.val_mem⟩, IntMod.val_injective rfl⟩
    have hmem2 : (x : G) * (v : G) * (x : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
      (stabTil_le_normalizer V₀ V (hX hxX)) (v : G)).1 v.2
    have hmem3 : (x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹ ∈ V :=
      V.mul_mem hmem2 (V.inv_mem v.2)
    have hcomm : ⁅(x : G), (v : G)⁆ ∈ ⁅A, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hxX hzA
    refine ⟨IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹, hmem3⟩, hcomm, ?_⟩
    have h1 : (actStab V₀ V hV x) (IntMod.mk hV v) =
        IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹, hmem2⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    rw [actTil_mk, h1, ← map_inv, ← map_mul]
    rfl

theorem commutator_barSub_le {V₀ V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    ⁅barSub V₀ V hV A, barSub V₀ V hV B⁆ ≤ barSub V₀ V hV ⁅A, B⁆ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a', ha'A, rfl⟩ := (mem_barSub V₀ V hV A a).1 ha
  obtain ⟨b', hb'B, rfl⟩ := (mem_barSub V₀ V hV B b).1 hb
  refine (mem_barSub V₀ V hV ⁅A, B⁆ _).2
    ⟨⟨(a' : G) * (b' : G) * (a' : G)⁻¹ * (b' : G)⁻¹, ?_⟩, ?_, ?_⟩
  · exact (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem
      (hA ha'A) (hB hb'B)) ((stabTil V₀ V).inv_mem (hA ha'A)))
      ((stabTil V₀ V).inv_mem (hB hb'B))
  · exact Subgroup.commutator_mem_commutator ha'A hb'B
  · change actTil V₀ V hV ⟨(a' : G) * (b' : G) * (a' : G)⁻¹ * (b' : G)⁻¹, _⟩ =
      ⁅actTil V₀ V hV a', actTil V₀ V hV b'⁆
    rw [← map_commutatorElement]
    exact congrArg (actTil V₀ V hV) (Subtype.ext rfl)

theorem commutator_barSub_self {V₀ V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ stabTil V₀ V) (hperf : ⁅A, A⁆ = A) :
    ⁅barSub V₀ V hV A, barSub V₀ V hV A⁆ = barSub V₀ V hV A := by
  have hAs : ⁅A.subgroupOf (stabTil V₀ V), A.subgroupOf (stabTil V₀ V)⁆ =
      A.subgroupOf (stabTil V₀ V) := by
    apply Subgroup.map_injective (stabTil V₀ V).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hA, hperf]
  calc ⁅barSub V₀ V hV A, barSub V₀ V hV A⁆
      = ⁅(A.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV),
          (A.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)⁆ := rfl
    _ = (⁅A.subgroupOf (stabTil V₀ V), A.subgroupOf (stabTil V₀ V)⁆).map
          (actTil V₀ V hV) :=
        (Subgroup.map_commutator (H₁ := A.subgroupOf (stabTil V₀ V))
          (H₂ := A.subgroupOf (stabTil V₀ V)) (f := actTil V₀ V hV)).symm
    _ = (A.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) := by rw [hAs]
    _ = barSub V₀ V hV A := rfl

theorem barSub_commutator_eq_bot_of_mem_conjSetOf {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ conjSetOf D.M L) (hKL : K ≠ L) :
    ⁅barSub V₀ V h.isElemAbelian L, barSub V₀ V h.isElemAbelian K⁆ = ⊥ := by
  set X := UC22.conjClosure D.M L with hX
  obtain ⟨hXM, hMX, hC⟩ := conjSetOf_subset_calC_conjClosure hL
  have hLmem : L ∈ conjSetOf D.M L := self_mem_conjSetOf D.M L
  have hLcX : L ∈ calC X := hC L hLmem
  have hKcX : K ∈ calC X := hC K hK
  have hLX : L ≤ X := CFSG.Quasithin.A3.subnormal_le hLcX.1
  have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hKcX.1
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hcomm : ∀ a ∈ barImage X L, ∀ b ∈ barImage X K, a * b = b * a :=
    uc22p22l_barImage_commute (L := X) hLcX hKcX hKL.symm
  have hpcore : ⁅L, K⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro l hl k hk
    exact uc22p22u_commutator_mem_pCoreOf (hLX hl) (hKX hk)
      (hcomm _ (uc22p21c_mem_barImage.2 ⟨⟨l, hLX hl⟩, hl, rfl⟩)
        _ (uc22p21c_mem_barImage.2 ⟨⟨k, hKX hk⟩, hk, rfl⟩))
  have hXsub : CFSG.Open.IsSubnormal X D.M :=
    CFSG.Quasithin.A3.subnormal_of_normal hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)
  have hpcoreBot : barSub V₀ V h.isElemAbelian (pCoreOf 2 X) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.isElemAbelian hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  have hbarComm : barSub V₀ V h.isElemAbelian ⁅L, K⁆ = ⊥ :=
    le_bot_iff.1 (hpcoreBot ▸ barSub_mono V₀ V h.isElemAbelian hpcore)
  have hLstab : L ≤ stabTil V₀ V := (CFSG.Quasithin.A3.subnormal_le hL.1).trans hMS
  have hKstab : K ≤ stabTil V₀ V := hKX.trans (hXM.trans hMS)
  exact le_bot_iff.1 (hbarComm ▸ commutator_barSub_le h.isElemAbelian hLstab hKstab)

theorem p18_6_5_of_w4_alt4 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥)
    (h4 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠
        barSub V₀ V h.hyp125.isElemAbelian L ∧
      ∀ g : MulAut (Vtil V₀ V h.hyp125.isElemAbelian),
        g ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian →
        g ∉ normIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
          (barSub V₀ V h.hyp125.isElemAbelian L) →
        commSub (commSub (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian))
          (barSub V₀ V h.hyp125.isElemAbelian L))
          ((barSub V₀ V h.hyp125.isElemAbelian L).map
            (MulAut.conj g).toMonoidHom) = ⊥) :
    P18_6_5 D V₀ V p L h := by
  set hV := h.hyp125.isElemAbelian
  have hp := h.hyp125.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLc : L ∈ calC D.M := h.hL.1
  have hLstab : L ≤ stabTil V₀ V := (CFSG.Quasithin.A3.subnormal_le hLc.1).trans hMS
  have hV0card : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hp.elemAbelian₀).1 h.small
  refine ⟨?_, ?_⟩
  ·
    intro hXL
    exact h4.1 (by rw [hXL])
  · intro x hxM hxN
    set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
    have hxS : x⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem (hMS hxM)
    have hKmem : K ∈ conjSetOf D.M L :=
      ⟨x⁻¹, D.M.inv_mem hxM, by rw [hKdef]; rfl⟩
    have hKL : K ≠ L := by
      intro hK
      apply hxN
      have hLK : CFSG.Quasithin.conjSubgroup L x = L := by rw [← hKdef]; exact hK
      rw [Subgroup.mem_normalizer_iff]
      intro h'
      have hmem := CFSG.Quasithin.mem_conjSubgroup_iff (A := L) (g := x) (x := h')
      rwa [hLK] at hmem
    have hcommBar : ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆ = ⊥ :=
      barSub_commutator_eq_bot_of_mem_conjSetOf h.hyp125 hLc hKmem hKL
    have hperf : ⁅barSub V₀ V hV L, barSub V₀ V hV L⁆ = barSub V₀ V hV L :=
      commutator_barSub_self hV hLstab hLc.2.1
    set g : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨x⁻¹, hxS⟩ with hgdef
    have hKbar : barSub V₀ V hV K =
        (barSub V₀ V hV L).map (MulAut.conj g).toMonoidHom := by
      rw [hKdef]
      change barSub V₀ V hV (L.map (MulAut.conj x⁻¹).toMonoidHom) =
        (barSub V₀ V hV L).map (MulAut.conj g).toMonoidHom
      rw [TwelveTwentyThree.barSub_map_conj hV hLstab hxS, ← hgdef]
    have hgMbar : g ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV (D.M.inv_mem hxM) hxS
    have hgnorm : g ∉ normIn (Mbar D.M V₀ V hV) (barSub V₀ V hV L) := by
      intro hg
      have hmap : (barSub V₀ V hV L).map (MulAut.conj g).toMonoidHom =
          barSub V₀ V hV L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 hg.2
      have hsame : barSub V₀ V hV K = barSub V₀ V hV L := by rw [hKbar, hmap]
      rw [hsame] at hcommBar
      exact hLb (hperf.symm.trans hcommBar)
    set X := UC22.conjClosure D.M L with hXdef
    obtain ⟨hXM, -, hC⟩ := conjSetOf_subset_calC_conjClosure hLc
    have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le (hC K hKmem).1
    have hKstab : K ≤ stabTil V₀ V := hKX.trans (hXM.trans hMS)
    have hAieq : imgTil V₀ V hV ⁅V, L⁆ = commSub ⊤ (barSub V₀ V hV L) := by
      rw [imgTil_commutator_eq_commSub_of_le hV le_rfl hLstab, s15_Infra_imgTil_top]
    have himg : imgTil V₀ V hV ⁅⁅V, L⁆, K⁆ ≤
        commSub (commSub ⊤ (barSub V₀ V hV L)) (barSub V₀ V hV K) := by
      calc imgTil V₀ V hV ⁅⁅V, L⁆, K⁆
          ≤ commSub (imgTil V₀ V hV ⁅V, L⁆) (barSub V₀ V hV K) :=
            (imgTil_commutator_eq_commSub_of_le hV
              (commutator_le_of_le_stabTil_general hLstab) hKstab).le
        _ = commSub (commSub ⊤ (barSub V₀ V hV L)) (barSub V₀ V hV K) := by rw [hAieq]
    have himgbot : imgTil V₀ V hV ⁅⁅V, L⁆, K⁆ = ⊥ := by
      refine le_bot_iff.1 (himg.trans (le_of_eq ?_))
      rw [hKbar]
      exact h4.2 g hgMbar hgnorm
    have hUV : ⁅⁅V, L⁆, K⁆ ≤ V :=
      (Subgroup.commutator_mono (commutator_le_of_le_stabTil_general hLstab) le_rfl).trans
        (commutator_le_of_le_stabTil_general hKstab)
    have hA0 : ⁅⁅V, L⁆, K⁆ ≤ V₀ := by
      have h1 : ⁅⁅V, L⁆, K⁆ ⊓ V ≤ preTil V₀ V hV (imgTil V₀ V hV ⁅⁅V, L⁆, K⁆) :=
        le_preTil_imgTil V₀ V hV _
      rw [himgbot, preTil_bot, inf_of_le_left hUV] at h1
      exact h1.trans inf_le_right
    have hV0K : ⁅V₀, K⁆ = ⊥ :=
      CFSG.RankThree.PartOne.commutator_eq_bot_of_card_le_two hV0card
        ((hKX.trans hXM).trans hp.le_normalizer₀)
    have h1 : ⁅⁅K, ⁅V, L⁆⁆, K⁆ = ⊥ := by
      have hcomm : ⁅K, ⁅V, L⁆⁆ ≤ V₀ := by
        rw [Subgroup.commutator_comm K ⁅V, L⁆]
        exact hA0
      exact le_bot_iff.1 ((Subgroup.commutator_mono hcomm le_rfl).trans (le_of_eq hV0K))
    have h2 : ⁅⁅⁅V, L⁆, K⁆, K⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono hA0 le_rfl).trans (le_of_eq hV0K))
    have hrot : ⁅⁅K, K⁆, ⁅V, L⁆⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K)
        (H₃ := ⁅V, L⁆) h1 h2
    have hKperf : ⁅K, K⁆ = K := (hC K hKmem).2.1
    rw [hKperf, Subgroup.commutator_comm] at hrot
    exact hrot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
