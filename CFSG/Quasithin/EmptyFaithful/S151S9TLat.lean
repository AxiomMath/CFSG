module

public import CFSG.Quasithin.EmptyFaithful.S151S9TModel
public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.Fischer.Pairs
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S8C2C
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151ZF
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB
open scoped commutatorElement

namespace LatAux

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_one_arr : (tab n (1 : Γ)).toArray = idTab n := by
  unfold tab idTab
  rw [← List.toArray_range]
  congr 1
  simp

theorem hel_one {x : Γ} {s : Array ℕ} (hs : s = (tab n x).toArray) :
    ∀ l < (#[x] : Array Γ).size, (#[s] : Array (Array ℕ)).getD l #[] =
      (tab n ((#[x] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l = 0 := by simpa using hl
  subst this
  simpa using hs

theorem hel_two {x y : Γ} {s t : Array ℕ} (hs : s = (tab n x).toArray)
    (ht : t = (tab n y).toArray) :
    ∀ l < (#[x, y] : Array Γ).size, (#[s, t] : Array (Array ℕ)).getD l #[] =
      (tab n ((#[x, y] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 2 := by simpa using hl
  interval_cases l
  · simpa using hs
  · simpa using ht

theorem hel_three {x y z : Γ} {s t u : Array ℕ} (hs : s = (tab n x).toArray)
    (ht : t = (tab n y).toArray) (hu : u = (tab n z).toArray) :
    ∀ l < (#[x, y, z] : Array Γ).size, (#[s, t, u] : Array (Array ℕ)).getD l #[] =
      (tab n ((#[x, y, z] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 3 := by simpa using hl
  interval_cases l
  · simpa using hs
  · simpa using ht
  · simpa using hu

variable [FaithfulSMul Γ (Fin n)]

theorem eq_of_tab_eq {g h : Γ} (e : (tab n g).toArray = (tab n h).toArray) : g = h := by
  have e' : tab n g = tab n h := List.toArray_inj e
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin n) fun i => ?_
  apply Fin.ext
  rw [← tab_getD g i, ← tab_getD h i, e']

theorem evalElt_eq_one_of_wordTabA {els : Array Γ} {tabs : Array (Array ℕ)}
    (hel : ∀ l < els.size, tabs.getD l #[] = (tab n (els.getD l 1)).toArray) {w : List ℕ}
    (hw : ∀ l ∈ w, l < els.size) (h : wordTabA tabs n w = idTab n) : evalElt els w = 1 := by
  rw [wordTabA_eq els tabs hel w hw, ← tab_one_arr (Γ := Γ) (n := n)] at h
  exact eq_of_tab_eq h

end Tables

section Words

variable {Γ : Type} [Group Γ]

theorem dc_word_eq (r x : Γ) (hx : x * x * x = 1) :
    r * (x * (r⁻¹ * (x * (x * (x * (x * (r * (x * (x * (r⁻¹ * (x * (x * 1))))))))))))
      = ⁅⁅r, x⁆, x⁆ := by
  have hxi : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx).symm
  simp only [commutatorElement_def, mul_inv_rev, inv_inv]
  simp only [hxi, mul_assoc, mul_one]

theorem mem_centralizer_single_iff {z g : Γ} :
    g ∈ Subgroup.centralizer ({z} : Set Γ) ↔ z * g = g * z := by
  rw [Subgroup.mem_centralizer_iff]; simp

end Words

section Invariance

variable {Γ : Type} [Group Γ]

theorem eq_one_or_eq_of_mem_zpowers {z h : Γ} (hz2 : orderOf z = 2) (hh : h ∈ Subgroup.zpowers z) :
    h = 1 ∨ h = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [← zpow_mod_orderOf, hz2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem autom_fix_central {S : Subgroup Γ} {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : centerOf S = Subgroup.zpowers z₀) (α : MulAut Γ) (hα : S.map α.toMonoidHom = S) :
    α z₀ = z₀ := by
  have hz₀ : z₀ ∈ centerOf S := hZ ▸ Subgroup.mem_zpowers z₀
  have hS : α z₀ ∈ S := by
    have := Subgroup.mem_map_of_mem α.toMonoidHom hz₀.1
    rwa [hα] at this
  have hc : α z₀ ∈ Subgroup.centralizer (S : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← hα] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have h1 := Subgroup.mem_centralizer_iff.mp hz₀.2 s' hs'
    show α s' * α z₀ = α z₀ * α s'
    rw [← map_mul, ← map_mul, h1]
  have hz1 : z₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hcen : α z₀ ∈ centerOf S := ⟨hS, hc⟩
  rcases eq_one_or_eq_of_mem_zpowers hz2 (hZ ▸ hcen) with h | h
  · exact absurd (α.injective (h.trans (map_one α).symm)) hz1
  · exact h

theorem not_map_le_centralizer {P : Subgroup Γ} {z₀ : Γ} (α : MulAut Γ) (hαz : α z₀ = z₀)
    (h : ¬ P ≤ Subgroup.centralizer ({z₀} : Set Γ)) :
    ¬ P.map α.toMonoidHom ≤ Subgroup.centralizer ({z₀} : Set Γ) := by
  intro hle
  apply h
  intro y hy
  have h1 := mem_centralizer_single_iff.mp (hle (Subgroup.mem_map_of_mem α.toMonoidHom hy))
  refine mem_centralizer_single_iff.mpr (α.injective ?_)
  rw [map_mul, map_mul, hαz]
  exact h1

end Invariance

section Elements

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem exists_xElt (C : LatCtx Γ n Lab) (W : Idx3Wit) (hp : W.p < C.J)
    (hmt1 : (C.D.mt[W.p]!).length = 1) (hxw : ∀ l ∈ W.xw, l < C.D.sTabs.length + 1) :
    ∃ x₀ ∈ C.Y W.p, W.xT n C.D = (tab n x₀).toArray := by
  have hEtabs : genTabs n (C.sg ++ C.gens W.p) = C.D.sTabs ++ C.D.mt[W.p]! := C.Y_letters hp
  have hsize : (C.sg ++ C.gens W.p).toArray.size = C.D.sTabs.length + 1 := by
    have h1 := congrArg List.length hEtabs
    rw [genTabs_length, List.length_append, List.length_append, hmt1] at h1
    simpa using h1
  have hel : ∀ l < (C.sg ++ C.gens W.p).toArray.size, (W.letters C.D).getD l #[] =
      (tab n ((C.sg ++ C.gens W.p).toArray.getD l 1)).toArray := by
    have : W.letters C.D = (genTabs n (C.sg ++ C.gens W.p)).toArray := by rw [hEtabs]; rfl
    rw [this]
    exact genTabs_hel _
  have hw : ∀ l ∈ W.xw, l < (C.sg ++ C.gens W.p).toArray.size := fun l hl => by
    rw [hsize]; exact hxw l hl
  refine ⟨evalElt (C.sg ++ C.gens W.p).toArray W.xw, ?_, ?_⟩
  · refine evalElt_mem _ (fun l hl => ?_) W.xw hw
    exact Subgroup.subset_closure (LatCtx.getD_mem _ hl)
  · exact wordTabA_eq (C.sg ++ C.gens W.p).toArray (W.letters C.D) hel W.xw hw

theorem exists_sElt (C : LatCtx Γ n Lab) {w : List ℕ} (hw : ∀ l ∈ w, l < C.D.sTabs.length) :
    ∃ s ∈ C.S, wordTabA C.D.sTabs.toArray n w = (tab n s).toArray := by
  have hsize : C.sg.toArray.size = C.D.sTabs.length := by
    have := congrArg List.length C.hsg
    rw [genTabs_length] at this
    simpa using this
  have hel : ∀ l < C.sg.toArray.size, C.D.sTabs.toArray.getD l #[] =
      (tab n (C.sg.toArray.getD l 1)).toArray := by
    rw [← C.hsg]
    exact genTabs_hel _
  have hw' : ∀ l ∈ w, l < C.sg.toArray.size := fun l hl => by
    rw [hsize]; exact hw l hl
  refine ⟨evalElt C.sg.toArray w, ?_, wordTabA_eq C.sg.toArray C.D.sTabs.toArray hel w hw'⟩
  exact evalElt_mem _ (fun l hl => C.sg_mem_S _ (LatCtx.getD_mem _ hl)) w hw'

theorem mem_S_of_act_eq (C : LatCtx Γ n Lab) {g : Γ} (h : C.A.act (tab n g).toArray C.Δ = C.Δ) :
    g ∈ C.S := h

theorem lat_cases (C : LatCtx Γ n Lab) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) {Z : Subgroup Γ} (hSZ : C.S ≤ Z) :
    (∃ j < Ls.size, Z = C.Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZj⟩ := lat_all C hL Z hSZ
  by_cases hjL : j < Ls.size
  · exact Or.inl ⟨j, hjL, by rw [hZj]; exact list_member hjL⟩
  · right
    have hjeq : j = Ls.size := by omega
    rw [hZj, hjeq]
    simp [memberOrTop]

theorem eq_member_of_card (C : LatCtx Γ n Lab) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) {q : ℕ} (hq : q < Ls.size)
    (hqu : ∀ j < Ls.size, Ls[j]! = Ls[q]! → j = q) (hqN : Ls[q]! ≠ C.D.O.lbl.size)
    {Z : Subgroup Γ} (hSZ : C.S ≤ Z) (hZc : Nat.card Z = Nat.card (C.Y q)) : Z = C.Y q := by
  rcases lat_cases C hL hSZ with ⟨j, hjL, hZj⟩ | htop
  · have h2 := hZc
    rw [hZj, lat_card C hL j hjL, lat_card C hL q hq] at h2
    rw [hZj, hqu j hjL (Nat.eq_of_mul_eq_mul_right (by positivity) h2)]
  · exfalso
    rw [htop, Subgroup.card_top, C.hΓ, lat_card C hL q hq] at hZc
    exact hqN (Nat.eq_of_mul_eq_mul_right (by positivity) hZc).symm

theorem map_member_eq (C : LatCtx Γ n Lab) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) {q : ℕ} (hq : q < Ls.size)
    (hqu : ∀ j < Ls.size, Ls[j]! = Ls[q]! → j = q) (hqN : Ls[q]! ≠ C.D.O.lbl.size)
    (α : MulAut Γ) (hα : C.S.map α.toMonoidHom = C.S) :
    (C.Y q).map α.toMonoidHom = C.Y q := by
  refine eq_member_of_card C hL hq hqu hqN ?_ (Subgroup.card_map_of_injective α.injective)
  calc C.S = C.S.map α.toMonoidHom := hα.symm
    _ ≤ (C.Y q).map α.toMonoidHom := Subgroup.map_mono (C.S_le_Y q)

end Elements

end LatAux

open LatAux

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem Idx3Wit.sound (C : LatCtx Γ n Lab) {z₀ : Γ} (hz₀ : z₀ ∈ centerOf C.S) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) :
    (∃ x₀ ∈ C.Y W.p, orderOf x₀ = 3 ∧ ∃ r : Fin 5 → Γ, (∀ i, r i ∈ C.S) ∧
      (∀ i, x₀⁻¹ * r i * x₀ ∈ C.S) ∧ (∀ i, x₀ * r i * x₀⁻¹ ∈ C.S) ∧
      Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆) ∧
    ∀ j < C.J, (W.czv[j]! = true ↔ C.Y j ≤ Subgroup.centralizer ({z₀} : Set Γ)) := by
  obtain ⟨hp, hmt1, hxw, hx3, hx1, -, -, hr, hdc, -, hczv⟩ := hok
  obtain ⟨x₀, hx₀Y, hxT⟩ := exists_xElt C W hp hmt1 hxw
  have hrex : ∀ i : Fin 5, ∃ s ∈ C.S, W.rT n C.D i.val = (tab n s).toArray :=
    fun i => exists_sElt C (hr i.val i.isLt).1
  have hriex : ∀ i : Fin 5, ∃ s ∈ C.S, W.riT n C.D i.val = (tab n s).toArray :=
    fun i => exists_sElt C (hr i.val i.isLt).2.1
  choose r hrS hrT using hrex
  choose r' hr'S hr'T using hriex
  have hx0 : x₀ * x₀ * x₀ = 1 := by
    have := evalElt_eq_one_of_wordTabA (hel_one hxT) (w := [0, 0, 0]) (by simp) hx3
    simpa [evalElt, mul_assoc] using this
  have hxx : x₀ * x₀ = x₀⁻¹ := eq_inv_of_mul_eq_one_left hx0
  have hr'i : ∀ i : Fin 5, r' i = (r i)⁻¹ := fun i => by
    have := evalElt_eq_one_of_wordTabA (hel_two (hrT i) (hr'T i)) (w := [0, 1]) (by simp)
      (hr i.val i.isLt).2.2.1
    simp only [evalElt] at this
    simpa using eq_inv_of_mul_eq_one_right (by simpa using this)
  refine ⟨⟨x₀, hx₀Y, ?_, r, hrS, ?_, ?_, ?_⟩, ?_⟩
  · refine orderOf_eq_prime (p := 3) ?_ ?_
    · rw [pow_succ, pow_two]; exact hx0
    · intro h
      apply hx1
      rw [hxT, h, tab_one_arr]
  · intro i
    have h := (hr i.val i.isLt).2.2.2.1
    rw [wordTabA_eq #[x₀, r i] #[W.xT n C.D, W.rT n C.D i.val] (hel_two hxT (hrT i)) [0, 0, 1, 0]
      (by simp)] at h
    have h2 := mem_S_of_act_eq C h
    have e : evalElt #[x₀, r i] [0, 0, 1, 0] = x₀⁻¹ * r i * x₀ := by
      simp only [evalElt]
      simp [mul_assoc, ← hxx]
    rwa [e] at h2
  · intro i
    have h := (hr i.val i.isLt).2.2.2.2
    rw [wordTabA_eq #[x₀, r i] #[W.xT n C.D, W.rT n C.D i.val] (hel_two hxT (hrT i)) [0, 1, 0, 0]
      (by simp)] at h
    have h2 := mem_S_of_act_eq C h
    have e : evalElt #[x₀, r i] [0, 1, 0, 0] = x₀ * r i * x₀⁻¹ := by
      simp only [evalElt]
      simp [mul_assoc, ← hxx]
    rwa [e] at h2
  · intro i i' hii'
    have hdcE : ∀ i : Fin 5, W.dcT n C.D i.val = (tab n ⁅⁅r i, x₀⁆, x₀⁆).toArray := fun i => by
      have h := wordTabA_eq #[r i, x₀, r' i] #[W.rT n C.D i.val, W.xT n C.D, W.riT n C.D i.val]
        (hel_three (hrT i) hxT (hr'T i)) dcWord (by simp [dcWord])
      show wordTabA _ n dcWord = _
      rw [h, ← dc_word_eq (r i) x₀ hx0, hr'i i]
      simp [evalElt, dcWord]
    have h1 : W.dcT n C.D i.val = W.dcT n C.D i'.val := by
      rw [hdcE, hdcE]
      exact congrArg (fun g => (tab n g).toArray) hii'
    exact Fin.ext (hdc i.val i.isLt i'.val i'.isLt h1)
  · intro j hj
    have hjw : j < C.D.mw.size := hj
    rw [hczv j hjw]
    have hgt : genTabs n (C.gens j) = C.D.mt[j]! := C.gens_tabs hj
    have hzc : ∀ s ∈ C.S, z₀ * s = s * z₀ := fun s hs =>
      (Subgroup.mem_centralizer_iff.mp hz₀.2 s hs).symm
    have hcomm : ∀ g : Γ, (wordTabA #[(tab n z₀).toArray, (tab n g).toArray] n [0, 1] =
        wordTabA #[(tab n z₀).toArray, (tab n g).toArray] n [1, 0]) ↔ z₀ * g = g * z₀ := by
      intro g
      rw [wordTabA_eq #[z₀, g] #[(tab n z₀).toArray, (tab n g).toArray] (hel_two rfl rfl) [0, 1]
          (by simp),
        wordTabA_eq #[z₀, g] #[(tab n z₀).toArray, (tab n g).toArray] (hel_two rfl rfl) [1, 0]
          (by simp)]
      constructor
      · intro h
        have := eq_of_tab_eq h
        simpa [evalElt] using this
      · intro h
        simp only [evalElt]
        simpa using congrArg (fun g => (tab n g).toArray) h
    constructor
    · intro h
      rw [LatCtx.Y, Subgroup.closure_le]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact mem_centralizer_single_iff.mpr (hzc x (C.sg_mem_S x hx))
      · refine mem_centralizer_single_iff.mpr ((hcomm x).mp (h _ ?_))
        rw [← hgt]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · intro h t ht
      rw [← hgt] at ht
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
      exact (hcomm g).mpr (mem_centralizer_single_iff.mp (h (C.gens_mem_Y g hg)))

namespace LatAux

theorem not_Y_le_centralizer (C : LatCtx Γ n Lab) {z₀ : Γ} (hz₀ : z₀ ∈ centerOf C.S) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) (hcp : W.czv[W.p]! = false) :
    ¬ C.Y W.p ≤ Subgroup.centralizer ({z₀} : Set Γ) := fun h => by
  have := ((Idx3Wit.sound C hz₀ W hok).2 W.p hok.1).mpr h
  rw [hcp] at this
  exact Bool.false_ne_true this

theorem exists_member_idx3 (C : LatCtx Γ n Lab) {z₀ : Γ} (hz₀ : z₀ ∈ centerOf C.S) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hN : C.D.O.lbl.size ≠ 3)
    {Z : Subgroup Γ} (hSZ : C.S ≤ Z) (hZc : Nat.card Z = 3 * Nat.card C.S)
    (hZn : ¬ Z ≤ Subgroup.centralizer ({z₀} : Set Γ)) :
    ∃ j < Ls.size, Z = C.Y j ∧ Ls[j]! = 3 ∧ W.czv[j]! ≠ true := by
  rcases lat_cases C hL hSZ with ⟨j, hjL, hZj⟩ | htop
  · refine ⟨j, hjL, hZj, ?_, fun hc => hZn ?_⟩
    · have h1 := lat_card C hL j hjL
      rw [← hZj, hZc, C.S_card] at h1
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).symm
    · have := ((Idx3Wit.sound C hz₀ W hok).2 j (by rw [lat_J_eq C hL]; exact hjL)).mp hc
      rwa [hZj]
  · exfalso
    rw [htop, Subgroup.card_top, C.hΓ, C.S_card] at hZc
    exact hN (Nat.eq_of_mul_eq_mul_right (by positivity) hZc)

theorem map_Y_eq_of_unique (C : LatCtx Γ n Lab) {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : centerOf C.S = Subgroup.zpowers z₀) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hp3 : Ls[W.p]! = 3)
    (hcp : W.czv[W.p]! = false) (hN : C.D.O.lbl.size ≠ 3) (T : Subgroup Γ)
    (hT : ∀ α : MulAut Γ, C.S.map α.toMonoidHom = C.S → (C.Y W.p).map α.toMonoidHom ≤ T)
    (huniq : ∀ j < Ls.size, Ls[j]! = 3 → j ≠ W.p → W.czv[j]! = true ∨ ¬ C.Y j ≤ T)
    (α : MulAut Γ) (hα : C.S.map α.toMonoidHom = C.S) :
    (C.Y W.p).map α.toMonoidHom = C.Y W.p := by
  have hz₀ : z₀ ∈ centerOf C.S := hZ ▸ Subgroup.mem_zpowers z₀
  have hpL : W.p < Ls.size := by
    rw [← lat_J_eq C hL]
    exact hok.1
  have hαz := autom_fix_central hz2 hZ α hα
  have hSZ : C.S ≤ (C.Y W.p).map α.toMonoidHom :=
    calc C.S = C.S.map α.toMonoidHom := hα.symm
      _ ≤ (C.Y W.p).map α.toMonoidHom := Subgroup.map_mono (C.S_le_Y W.p)
  have hZc : Nat.card ((C.Y W.p).map α.toMonoidHom) = 3 * Nat.card C.S := by
    rw [Subgroup.card_map_of_injective α.injective, lat_card C hL W.p hpL, hp3, C.S_card]
  obtain ⟨j, hjL, hZj, hj3, hjc⟩ := exists_member_idx3 C hz₀ W hok hL hN hSZ hZc
    (not_map_le_centralizer α hαz (not_Y_le_centralizer C hz₀ W hok hcp))
  have hjp : j = W.p := by
    by_contra hne
    rcases huniq j hjL hj3 hne with h | h
    · exact hjc h
    · exact h (hZj ▸ hT α hα)
  rw [hZj, hjp]

end LatAux

theorem idx3Data_of_lat (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {z₀ : Γ}
    (hz2 : orderOf z₀ = 2) (hZ : centerOf C.S = Subgroup.zpowers z₀) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hp3 : Ls[W.p]! = 3)
    (hcp : W.czv[W.p]! = false) : Idx3Data Γ C.S (C.Y W.p) := by
  have hz₀ : z₀ ∈ centerOf C.S := hZ ▸ Subgroup.mem_zpowers z₀
  have hpL : W.p < Ls.size := by
    rw [← lat_J_eq C hL]
    exact hok.1
  refine ⟨hS, C.S_le_Y W.p, ?_, ⟨z₀, hz2, hZ, not_Y_le_centralizer C hz₀ W hok hcp⟩,
    (Idx3Wit.sound C hz₀ W hok).1⟩
  rw [lat_card C hL W.p hpL, hp3, C.S_card]

theorem idx3Model_of_lat (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {z₀ : Γ}
    (hz2 : orderOf z₀ = 2) (hZ : centerOf C.S = Subgroup.zpowers z₀) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hp3 : Ls[W.p]! = 3)
    (hcp : W.czv[W.p]! = false) (hN : C.D.O.lbl.size ≠ 3)
    (huniq : ∀ j < Ls.size, Ls[j]! = 3 → j ≠ W.p → W.czv[j]! = true) :
    Idx3Model Γ C.S (C.Y W.p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := idx3Data_of_lat C hS hz2 hZ W hok hL hp3 hcp
  exact ⟨h1, h2, h3, h4, h5, map_Y_eq_of_unique C hz2 hZ W hok hL hp3 hcp hN ⊤
    (fun _ _ => le_top) (fun j hj h3 hne => Or.inl (huniq j hj h3 hne))⟩

theorem idx3Model_of_lat_incl (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {z₀ : Γ}
    (hz2 : orderOf z₀ = 2) (hZ : centerOf C.S = Subgroup.zpowers z₀) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hp3 : Ls[W.p]! = 3)
    (hcp : W.czv[W.p]! = false) (hN : C.D.O.lbl.size ≠ 3)
    {q : ℕ} (hq : q < Ls.size) (hqu : ∀ j < Ls.size, Ls[j]! = Ls[q]! → j = q)
    (hqN : Ls[q]! ≠ C.D.O.lbl.size) (hpq : C.Y W.p ≤ C.Y q)
    (huniq : ∀ j < Ls.size, Ls[j]! = 3 → j ≠ W.p → W.czv[j]! = true ∨ ¬ C.Y j ≤ C.Y q) :
    Idx3Model Γ C.S (C.Y W.p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := idx3Data_of_lat C hS hz2 hZ W hok hL hp3 hcp
  exact ⟨h1, h2, h3, h4, h5, map_Y_eq_of_unique C hz2 hZ W hok hL hp3 hcp hN (C.Y q)
    (fun α hα => (Subgroup.map_mono hpq).trans (map_member_eq C hL hq hqu hqN α hα).le) huniq⟩

end Main

end CFSG.Quasithin.S151S9T
