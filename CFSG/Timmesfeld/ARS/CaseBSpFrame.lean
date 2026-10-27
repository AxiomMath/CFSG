module

public import CFSG.Timmesfeld.ARS.CaseBSp
public import CFSG.Timmesfeld.ARS.CaseBGen
public import CFSG.Timmesfeld.ARS.CaseMFrame
public import CFSG.Timmesfeld.RankTwo.LevisBSp
public import CFSG.LieType.CurtisTits.Symplectic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Timmesfeld.RankTwo Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (Ψ) in
noncomputable abbrev pi12 [CharP F 2] : G := Ψ (pm (Equiv.swap 1 2))

variable (R Ψ) in
@[expose] noncomputable def spMaps [CharP F 2] [Finite F] (ι : (Fin 1 → F) → G) :
    Fin 12 → F → G :=
  ![xs Ψ ne21, xs Ψ ne12, xs Ψ ne13, xs Ψ ne31, xU R Ψ ι, xU' R Ψ ι, xs Ψ ne23, xs Ψ ne32,
    xs Ψ ne02, xs Ψ ne20, xN R Ψ ι, xN' R Ψ ι]

variable (R Ψ) in
@[expose] noncomputable def wU [CharP F 2] [Finite F] (ι : (Fin 1 → F) → G) : G :=
  xU R Ψ ι 1 * xU' R Ψ ι 1 * xU R Ψ ι 1

variable (Ψ) in
@[expose] noncomputable def spW01 [CharP F 2] : Fin 3 → G := ![pi12 Ψ, pi13 Ψ, 1]

variable (Ψ) in
@[expose] noncomputable def spW12 [CharP F 2] : Fin 3 → G := ![1, pi13 Ψ, piT Ψ]

variable (R Ψ) in
@[expose] noncomputable def spW02 [CharP F 2] [Finite F] (ι : (Fin 1 → F) → G) : Fin 3 → G :=
  ![pi12 Ψ, 1, wU R Ψ ι]

section Frame

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
  {ι : (Fin 1 → F) → G} (hι : LinParamU R Ψ 1 ι)
include h hS hP hι

omit hP in
theorem pi12_conj_xU_and_xU' (t : F) :
    pi12 Ψ * xU R Ψ ι t * (pi12 Ψ)⁻¹ = xU R Ψ ι t ∧
      pi12 Ψ * xU' R Ψ ι t * (pi12 Ψ)⁻¹ = xU' R Ψ ι t := by
  have hmem := pm_swap_mem_sup (Ψ := Ψ) ne12
  have hST := hS.perm σT
  have hc : ∀ {u : G}, (∀ x ∈ xg Ψ 1 2, Commute x u) → (∀ x ∈ xg Ψ 2 1, Commute x u) →
      pi12 Ψ * u * (pi12 Ψ)⁻¹ = u := by
    intro u h1 h2
    have hle : xg Ψ 1 2 ⊔ xg Ψ 2 1 ≤ Subgroup.centralizer {u} :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h1 x hx).eq)
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h2 x hx).eq)
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)]
    group
  have hU' : ∀ {a b : Fin 4} (hab : a ≠ b), (a = 0 ∨ a = 3 ∨ b = 1 ∨ b = 2) →
      ∀ x ∈ xg Ψ (σT a) (σT b), Commute x (xU' R Ψ ι t) := fun {a b} hab hcond x hx => by
    rw [← xg_perm] at hx
    exact (commuting_hU h hST hab hcond _ (xU'_mem h hι t) x hx).symm
  refine ⟨hc (fun x hx => (commuting_hU h hS ne12 (by decide) _ (xU_mem hι t) x hx).symm)
    (fun x hx => (commuting_hU h hS ne21 (by decide) _ (xU_mem hι t) x hx).symm),
    hc (fun x hx => hU' (a := 0) (b := 3) ne03 (by decide) x hx)
    (fun x hx => hU' (a := 3) (b := 0) ne30 (by decide) x hx)⟩

omit hP in
theorem wU_conj_xs21_and_xs12 (c : F) :
    wU R Ψ ι * xs Ψ ne21 c * (wU R Ψ ι)⁻¹ = xs Ψ ne21 c ∧
      wU R Ψ ι * xs Ψ ne12 c * (wU R Ψ ι)⁻¹ = xs Ψ ne12 c := by
  have hcU : ∀ t, Commute (xU R Ψ ι t) (xs Ψ ne21 c) ∧ Commute (xU R Ψ ι t) (xs Ψ ne12 c) :=
    fun t => ⟨commuting_hU h hS ne21 (by decide) _ (xU_mem hι t) _ (xs_mem _ _),
      commuting_hU h hS ne12 (by decide) _ (xU_mem hι t) _ (xs_mem _ _)⟩
  have hcU' : ∀ t, Commute (xU' R Ψ ι t) (xs Ψ ne21 c) ∧ Commute (xU' R Ψ ι t) (xs Ψ ne12 c) := by
    intro t
    have hST := hS.perm σT
    have h1 := commuting_hU h hST (a := 3) (b := 0) ne30 (by decide) _ (xU'_mem h hι t)
    have h2 := commuting_hU h hST (a := 0) (b := 3) ne03 (by decide) _ (xU'_mem h hι t)
    rw [xg_perm] at h1 h2
    exact ⟨h1 _ (xs_mem _ _), h2 _ (xs_mem _ _)⟩
  have key : ∀ y : G, Commute (xU R Ψ ι 1) y → Commute (xU' R Ψ ι 1) y →
      wU R Ψ ι * y * (wU R Ψ ι)⁻¹ = y := by
    intro y h1 h2
    rw [wU, ((h1.mul_left h2).mul_left h1).eq]
    group
  exact ⟨key _ (hcU 1).1 (hcU' 1).1, key _ (hcU 1).2 (hcU' 1).2⟩

theorem wU_conj_xU_and_xU' (c : F) :
    wU R Ψ ι * xU R Ψ ι c * (wU R Ψ ι)⁻¹ = xU' R Ψ ι c ∧
      wU R Ψ ι * xU' R Ψ ι c * (wU R Ψ ι)⁻¹ = xU R Ψ ι c := by
  have e := rankOne_conj h hS hP hι (one_ne_zero (α := F)) c
  rw [show -(1 : F)⁻¹ = 1 by rw [inv_one, CharTwo.neg_eq],
    show -((1 : F) ^ 2)⁻¹ * c = c by rw [one_pow, inv_one, CharTwo.neg_eq, one_mul]] at e
  have e1 : wU R Ψ ι * xU R Ψ ι c * (wU R Ψ ι)⁻¹ = xU' R Ψ ι c := e
  have hinv : (wU R Ψ ι)⁻¹ = wU R Ψ ι := by
    rw [wU, _root_.mul_inv_rev, _root_.mul_inv_rev,
      inv_eq_of_mul_eq_one_left (xU_mul_self hι 1), inv_eq_of_mul_eq_one_left (xU'_mul_self hι 1)]
    group
  refine ⟨e1, ?_⟩
  rw [← e1]
  calc wU R Ψ ι * (wU R Ψ ι * xU R Ψ ι c * (wU R Ψ ι)⁻¹) * (wU R Ψ ι)⁻¹ =
      (wU R Ψ ι * wU R Ψ ι) * xU R Ψ ι c * ((wU R Ψ ι)⁻¹ * (wU R Ψ ι)⁻¹) := by group
    _ = xU R Ψ ι c := by
      rw [hinv, show wU R Ψ ι * wU R Ψ ι = 1 by
        nth_rw 2 [← hinv]
        exact mul_inv_cancel _]
      group

omit hP in
theorem exists_xU'_eq (hP : PtHyp R Ψ) {u : G} (hu : u ∈ hU R (perm Ψ σT)) :
    ∃ t, xU' R Ψ ι t = u := by
  rw [hU_perm_T' h] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  obtain ⟨t, rfl⟩ := exists_xU_eq hι hP h hS hv
  exact ⟨t, rfl⟩

theorem isC3Frame (hB : HypB G R (xg Ψ 0 3)) :
    IsC3Frame (spMaps R Ψ ι) (spW01 Ψ) (spW12 Ψ) (spW02 R Ψ ι) where
  add0 := xs_add ne21
  add2 := xs_add ne13
  add4 := xU_add hι
  add6 := xs_add ne23
  add8 := xs_add ne02
  add10 := xN_add hι
  comm_0_2 s t := by
    change ⁅xs Ψ ne21 s, xs Ψ ne13 t⁆ = xs Ψ ne23 (s * t)
    rw [xs, xs, xs, ← map_commutatorElement, SpecialLinearGroup.commutatorElement_transvection]
  commute_0_6 s t :=
    commuting_xg (Ψ := Ψ) ne21 ne23 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  commute_6_2 s t :=
    commuting_xg (Ψ := Ψ) ne23 ne13 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  comm_2_4 s t := commutator_13_xU h hS hP hι s t
  commute_2_8 s t := commute_13_02 s t
  commute_2_10 s t := commute_13_xN h hS hι s t
  commute_8_10 s t := commute_02_xN h hS hι s t
  commute_8_4 s t := (commute_xU_02 h hS hι t s).symm
  commute_10_4 s t := (commute_xU_xN h hS hι t s).symm
  commute_0_4 s t := (commuting_hU h hS ne21 (by decide) _ (xU_mem hι t) _ (xs_mem _ _)).symm
  w01_0_0 c := pm_conj_xs (Equiv.swap 1 2) ne21 c
  w01_0_1 c := pm_conj_xs (Equiv.swap 1 2) ne12 c
  w01_0_2 c := pm_conj_xs (Equiv.swap 1 2) ne13 c
  w01_0_3 c := pm_conj_xs (Equiv.swap 1 2) ne31 c
  w01_0_6 c := pm_conj_xs (Equiv.swap 1 2) ne23 c
  w01_0_7 c := pm_conj_xs (Equiv.swap 1 2) ne32 c
  w01_1_0 c := pm_conj_xs (Equiv.swap 1 3) ne21 c
  w01_1_1 c := pm_conj_xs (Equiv.swap 1 3) ne12 c
  w01_1_2 c := pm_conj_xs (Equiv.swap 1 3) ne13 c
  w01_1_3 c := pm_conj_xs (Equiv.swap 1 3) ne31 c
  w01_1_6 c := pm_conj_xs (Equiv.swap 1 3) ne23 c
  w01_1_7 c := pm_conj_xs (Equiv.swap 1 3) ne32 c
  w12_1_2 c := pm_conj_xs (Equiv.swap 1 3) ne13 c
  w12_1_3 c := pm_conj_xs (Equiv.swap 1 3) ne31 c
  w12_1_4 c := pi13_conj_xU c
  w12_1_5 c := pi13_conj_xU' c
  w12_1_8 c := pm_conj_xs (Equiv.swap 1 3) ne02 c
  w12_1_9 c := pm_conj_xs (Equiv.swap 1 3) ne20 c
  w12_1_10 c := pi13_conj_xN c
  w12_1_11 c := pi13_conj_xN' c
  w12_2_2 c := piT_conj_xs13 c
  w12_2_3 c := piT_conj_xs ne31 c
  w12_2_4 c := piT_conj_xU c
  w12_2_5 c := piT_conj_xU' c
  w12_2_8 c := piT_conj_xs02 c
  w12_2_9 c := piT_conj_xs ne20 c
  w12_2_10 c := piT_conj_xN h hS hι c
  w12_2_11 c := piT_conj_xN' h hS hι c
  w02_0_0 c := pm_conj_xs (Equiv.swap 1 2) ne21 c
  w02_0_1 c := pm_conj_xs (Equiv.swap 1 2) ne12 c
  w02_0_4 c := (pi12_conj_xU_and_xU' h hS hι c).1
  w02_0_5 c := (pi12_conj_xU_and_xU' h hS hι c).2
  w02_2_0 c := (wU_conj_xs21_and_xs12 h hS hι c).1
  w02_2_1 c := (wU_conj_xs21_and_xs12 h hS hι c).2
  w02_2_4 c := (wU_conj_xU_and_xU' h hS hP hι c).1
  w02_2_5 c := (wU_conj_xU_and_xU' h hS hP hι c).2
  rank0 := ⟨blk Ψ ne21, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact blk_tv01 ne21 c,
    fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact blk_tv10 ne21 c⟩
  rank1 := ⟨blk Ψ ne13, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact blk_tv01 ne13 c,
    fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact blk_tv10 ne13 c⟩
  rank2 := exists_hom_SL2_xU h hS hP hι
  gen := by
    rw [eq_top_iff, ← fundSub_eq_top h hS hB]
    set S := Set.range (spMaps R Ψ ι 0) ∪ Set.range (spMaps R Ψ ι 1) ∪
      Set.range (spMaps R Ψ ι 2) ∪ Set.range (spMaps R Ψ ι 3) ∪ Set.range (spMaps R Ψ ι 4) ∪
        Set.range (spMaps R Ψ ι 5) with hSdef
    have m : ∀ (i : Fin 12) (c : F), i.val < 6 → spMaps R Ψ ι i c ∈ Subgroup.closure S := by
      intro i c hi
      refine Subgroup.subset_closure ?_
      fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue] at hi ⊢ <;>
        first
        | omega
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c, rfl⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))
        | exact Or.inl (Or.inl (Or.inr ⟨c, rfl⟩))
        | exact Or.inl (Or.inr ⟨c, rfl⟩)
        | exact Or.inr ⟨c, rfl⟩
    have hxg : ∀ {a b : Fin 4} (hab : a ≠ b) (i : Fin 12), i.val < 6 →
        (∀ c, spMaps R Ψ ι i c = xs Ψ hab c) → xg Ψ a b ≤ Subgroup.closure S := by
      intro a b hab i hi hc x hx
      obtain ⟨c, rfl⟩ := (mem_xg_iff hab).1 hx
      rw [← hc]
      exact m i c hi
    refine sup_le (sup_le (sup_le (hxg ne21 0 (by decide) fun _ => rfl)
      (hxg ne12 1 (by decide) fun _ => rfl)) (sup_le (hxg ne13 2 (by decide) fun _ => rfl)
        (hxg ne31 3 (by decide) fun _ => rfl))) (sup_le (fun u hu => ?_) (fun u hu => ?_))
    · obtain ⟨t, rfl⟩ := exists_xU_eq hι hP h hS hu
      exact m 4 t (by decide)
    · obtain ⟨t, rfl⟩ := exists_xU'_eq h hS hι hP hu
      exact m 5 t (by decide)
  nt := ⟨1, fun h1 => one_ne_zero (xs_injective hS ne21 (h1.trans (xs_zero ne21).symm))⟩

end Frame

theorem range_xs {a b : Fin 4} (hab : a ≠ b) : Set.range (xs Ψ hab) = (xg Ψ a b : Set G) := by
  ext g
  exact (mem_xg_iff hab).symm

theorem sp6Outcome {f : ℕ} (hf : 1 ≤ f) (h : Hyp G R)
    {Ψ : SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G} (hS : Skel R Ψ)
    (hB : HypB G R (xg Ψ 0 3)) {ι : (Fin 1 → GaloisField 2 f) → G} (hι : LinParamU R Ψ 1 ι) :
    NonSimplyLacedOutcome G ∧ NSLFrame G R := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hP := ptHyp_of_hypB hB
  have hC := isC3Frame h hS hP hι hB
  have hframe : IsCTFrame (Symplectic.rootDatum 3 (GaloisField 2 f)) G
      (phiOf (Symplectic.rootDatum 3 (GaloisField 2 f)) (Sp.x 3 (GaloisField 2 f))
        (c3PsiOf (spMaps R Ψ ι))) :=
    ⟨hC.hcone, hC.hrank, hC.hgen, hC.hnt⟩
  have hadm : StatedLieAdmissible .PSp 3 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, fun e => absurd (congrArg Prod.fst e) (by norm_num)⟩
  have hCT := CurtisTits.curtisTitsConclusion_symplectic (n := 3) (F := GaloisField 2 f) hadm hF
    le_rfl
  have hL := leviConePresented_symplectic 3 (GaloisField 2 f)
  refine ⟨.inl ⟨3, f, le_rfl, hf, hframe.lieModel hCT hL h.center⟩, ?_⟩
  refine hframe.nslFrame hCT hL (Symplectic.isCTGroupDatum 3 (GaloisField 2 f))
    (Symplectic.steinbergExtras 3 (GaloisField 2 f)) rfl (NSLType.symplecticDatum le_rfl _)
    sp3_isPGroup (fun _ i j hij => sp3_commuting i j hij) (hS.mem 2 1 ne21) ?_ ?_
    (hS.opp 2 1 ne21)
  · have e : c3r 0 = (Pi.single (0 : Fin 3) 1 : Fin 3 → ℤ) := by decide
    exact (range_xs ne21).symm.trans
      (IsC3Frame.range_phiOf_c3r (f := spMaps R Ψ ι) _ 0 e).symm
  · have e : c3r 1 = -(Pi.single (0 : Fin 3) 1 : Fin 3 → ℤ) := by decide
    exact (range_xs ne12).symm.trans
      (IsC3Frame.range_phiOf_c3r (f := spMaps R Ψ ι) _ 1 e).symm

end CaseB

end CFSG.Timmesfeld.ARS
