module

public import CFSG.Quasithin.Vol2.KGFactE64Core
public import CFSG.Quasithin.Vol2.KGFactE64Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBRBlockParabolicDInf
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGInsp

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_mul_arr (g h : Γ) :
    (tab n (g * h)).toArray = tMul (tab n g).toArray (tab n h).toArray := by
  rw [tab_mul]
  unfold compTab tMul
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem tab_one_arr : (tab n (1 : Γ)).toArray = tId n := by
  unfold tab tId
  congr 1
  have h1 : (fun i : Fin n => ((1 : Γ) • i).val) = fun i : Fin n => (i : ℕ) := by
    funext i; rw [one_smul]
  rw [h1, List.map_coe_finRange_eq_range]

theorem tab_pow_arr (y : Γ) (k : ℕ) : (tab n (y ^ k)).toArray = tPow n (tab n y).toArray k := by
  induction k with
  | zero => rw [pow_zero, tab_one_arr]; rfl
  | succ k ih => rw [pow_succ', tab_mul_arr, ih]; rfl

theorem powers_getD (t : Array ℕ) {i : ℕ} (hi : i < 8) : (powers n t).getD i #[] = tPow n t i := by
  unfold powers
  simp [Array.getD_eq_getD_getElem?, hi]

theorem ev_map_tab (gs : List Γ) {p : ℕ} (hp : p < n) :
    ev (gs.map fun g => (tab n g).toArray) p = act n gs.prod p := by
  induction gs with
  | nil => simp [ev, act_one hp]
  | cons g gs ih =>
    have h1 : ev ((g :: gs).map fun g => (tab n g).toArray) p =
        img (tab n g).toArray (ev (gs.map fun g => (tab n g).toArray) p) := rfl
    rw [h1, ih, img_tab, List.prod_cons, act_mul _ _ hp]

variable {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
include hB hbase

theorem isId_iff (gs : List Γ) :
    isId B (gs.map fun g => (tab n g).toArray) = true ↔ gs.prod = 1 := by
  unfold isId
  simp only [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact hbase _ fun b hb => by rw [← ev_map_tab gs (hB b hb)]; exact h b hb
  · intro h b hb
    rw [ev_map_tab gs (hB b hb), h, act_one (hB b hb)]

theorem eqOn_iff (us vs : List Γ) :
    eqOn B (us.map fun g => (tab n g).toArray) (vs.map fun g => (tab n g).toArray) = true ↔
      us.prod = vs.prod := by
  unfold eqOn
  simp only [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact eq_of_act_eq_base hB hbase fun b hb => by
      rw [← ev_map_tab us (hB b hb), ← ev_map_tab vs (hB b hb)]; exact h b hb
  · intro h b hb
    rw [ev_map_tab us (hB b hb), ev_map_tab vs (hB b hb), h]

omit hB hbase in
theorem cj_eq {y : Γ} (a : Γ) {i : ℕ} (hi : i ≤ 7) :
    cj (powers n (tab n y).toArray) (tab n a).toArray i =
      [y ^ i, a, y ^ (7 - i)].map fun g => (tab n g).toArray := by
  unfold cj
  rw [powers_getD _ (by omega), powers_getD _ (by omega), ← tab_pow_arr, ← tab_pow_arr]
  rfl

omit hB hbase in
theorem prod_cj {y : Γ} (hy : y ^ 7 = 1) (a : Γ) {i : ℕ} (hi : i ≤ 7) :
    [y ^ i, a, y ^ (7 - i)].prod = conjP y a i := by
  rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
  unfold conjP
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_add, show 7 - i + i = 7 by omega, hy]

theorem bad_tab {y a b : Γ} (hy : y ^ 7 = 1) (h : Bad y a b) :
    condA B (powers n (tab n y).toArray) (tab n a).toArray = true ∧
      condB B (powers n (tab n y).toArray) (tab n b).toArray = true ∧
      commAll B (powers n (tab n y).toArray) (tab n a).toArray (tab n b).toArray = true := by
  obtain ⟨ha, hb, haa, hbb, hfa, hfb, hc⟩ := h
  have hid := isId_iff hB hbase
  have h1 : ∀ g : Γ, [(tab n g).toArray] = [g].map fun g => (tab n g).toArray := fun g => rfl
  have h2 : ∀ g : Γ, [(tab n g).toArray, (tab n g).toArray] =
      [g, g].map fun g => (tab n g).toArray := fun g => rfl
  have hne : ∀ g : Γ, g ≠ 1 → isId B [(tab n g).toArray] = false := fun g hg => by
    rw [Bool.eq_false_iff]
    intro hh
    rw [h1, hid] at hh
    exact hg (by simpa using hh)
  have hsq : ∀ g : Γ, g * g = 1 → isId B [(tab n g).toArray, (tab n g).toArray] = true :=
    fun g hg => by rw [h2, hid]; simpa using hg
  have hA : isId B (cj (powers n (tab n y).toArray) (tab n a).toArray 3 ++
      cj (powers n (tab n y).toArray) (tab n a).toArray 1 ++ [(tab n a).toArray]) = true := by
    rw [cj_eq a (by norm_num), cj_eq a (by norm_num), h1, ← List.map_append, ← List.map_append,
      hid, List.prod_append, List.prod_append, prod_cj hy a (by norm_num),
      prod_cj hy a (by norm_num)]
    simpa [fA] using hfa
  have hBb : isId B (cj (powers n (tab n y).toArray) (tab n b).toArray 3 ++
      cj (powers n (tab n y).toArray) (tab n b).toArray 2 ++ [(tab n b).toArray]) = true := by
    rw [cj_eq b (by norm_num), cj_eq b (by norm_num), h1, ← List.map_append, ← List.map_append,
      hid, List.prod_append, List.prod_append, prod_cj hy b (by norm_num),
      prod_cj hy b (by norm_num)]
    simpa [fB] using hfb
  refine ⟨?_, ?_, ?_⟩
  · unfold condA
    rw [hne a ha, hsq a haa, hA]
    rfl
  · unfold condB
    rw [hne b hb, hsq b hbb, hBb]
    rfl
  · unfold commAll
    simp only [List.all_eq_true, List.mem_range]
    intro i hi j hj
    rw [cj_eq a (by omega), cj_eq b (by omega), ← List.map_append, ← List.map_append,
      eqOn_iff hB hbase, List.prod_append, List.prod_append, prod_cj hy a (by omega),
      prod_cj hy b (by omega)]
    exact hc i hi j hj

end Tables

theorem pairCheck_sound {n : ℕ} {B : List ℕ} {y : Array ℕ} {ts : List (Array ℕ)}
    (h : pairCheck n B y ts = true) {k : ℕ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) {a b : Array ℕ}
    (ha : a ∈ ts) (hb : b ∈ ts) (hA : condA B (powers n (tPow n y k)) a = true)
    (hB : condB B (powers n (tPow n y k)) b = true) :
    commAll B (powers n (tPow n y k)) a b = false := by
  unfold pairCheck at h
  simp only [List.all_eq_true, List.mem_range', List.mem_filter] at h
  have := h k ⟨k - 1, by omega, by omega⟩ a ⟨ha, hA⟩ b ⟨hb, hB⟩
  simpa using this

section Member

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem mem_of_length {P : Subgroup Γ} {E : List Γ} (hE : E.Nodup) (hEP : ∀ x ∈ E, x ∈ P)
    (hlen : E.length = Nat.card P) : ∀ x ∈ P, x ∈ E := by
  classical
  intro x hx
  by_contra hxE
  have h1 : E.toFinset ⊂ (insert x E.toFinset) := Finset.ssubset_insert (by simpa using hxE)
  have h2 : ((insert x E.toFinset : Finset Γ) : Set Γ) ⊆ (P : Set Γ) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact hEP z (List.mem_toFinset.mp hz)
  have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simpa using hxE),
    List.toFinset_card_of_nodup hE, ← Nat.card_coe_set_eq, hlen] at h3
  have : Nat.card ↥P = Nat.card (P : Set Γ) := rfl
  omega

theorem member_ok_of_check (C : LatCtx Γ n Lab) {j : ℕ} (hj : j < C.J)
    (hodd : C.D.Om[j]!.lbl.size % 2 = 1) (h49 : ¬ 49 ∣ Nat.card (C.Y j))
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (labels : List Lab)
    (hlab : ∀ x ∈ C.Λ j, x ∈ labels) (ltabs : Array (Array ℕ))
    (hsz : ltabs.size = (C.sg ++ C.gens j).toArray.size)
    (hlt : ∀ l < (C.sg ++ C.gens j).toArray.size,
      ltabs.getD l #[] = (tab n ((C.sg ++ C.gens j).toArray.getD l 1)).toArray)
    (yw : List ℕ) (ows : List (List ℕ)) (hlen : ows.length = Nat.card (pCoreOf 2 (C.Y j)))
    (hcheck : e64Check n B C.A.act ltabs yw ows labels = true) :
    ∀ y ∈ C.Y j, orderOf y = 7 → ∀ a ∈ pCoreOf 2 (C.Y j), ∀ b ∈ pCoreOf 2 (C.Y j),
      ¬ Bad y a b := by
  set els := (C.sg ++ C.gens j).toArray with hels
  unfold e64Check at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_map] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨hyw, hows⟩, hy7⟩, hy1⟩, hnd⟩, hfix⟩, hpair⟩ := hcheck
  have hwt : ∀ w : List ℕ, (∀ l ∈ w, l < ltabs.size) →
      wordTabA ltabs n w = (tab n (evalElt els w)).toArray := fun w hw =>
    wordTabA_eq els ltabs hlt w (fun l hl => hsz ▸ hw l hl)
  have hmemY : ∀ w : List ℕ, (∀ l ∈ w, l < ltabs.size) → evalElt els w ∈ C.Y j := fun w hw =>
    evalElt_mem els (fun l hl => Subgroup.subset_closure (LatCtx.getD_mem _ hl)) w
      (fun l hl => hsz ▸ hw l hl)
  set y₀ := evalElt els yw with hy₀
  have hty₀ : wordTabA ltabs n yw = (tab n y₀).toArray := hwt yw hyw
  have hid := isId_iff hB hbase (Γ := Γ)
  have hy₀7 : y₀ ^ 7 = 1 := by
    have h7 : List.replicate 7 (wordTabA ltabs n yw) =
        (List.replicate 7 y₀).map fun g => (tab n g).toArray := by
      rw [List.map_replicate, hty₀]
    rw [h7, hid, List.prod_replicate] at hy7
    exact hy7
  have hy₀1 : y₀ ≠ 1 := fun h => by
    have h1 : [wordTabA ltabs n yw] = [y₀].map fun g => (tab n g).toArray := by
      rw [List.map_singleton, hty₀]
    rw [h1, Bool.not_eq_true'] at hy1
    have h2 := (hid [y₀]).mpr (by simpa using h)
    rw [h2] at hy1
    exact Bool.noConfusion hy1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord₀ : orderOf y₀ = 7 := orderOf_eq_prime hy₀7 hy₀1
  have hcore := C.core_eq hj hodd
  have hO2 : ∀ x ∈ pCoreOf 2 (C.Y j), ∃ w ∈ ows, evalElt els w = x := by
    have hE : ∀ x ∈ ows.map (evalElt els), x ∈ pCoreOf 2 (C.Y j) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      rw [hcore, C.mem_tupStab hj]
      intro L hL
      rw [← hwt w (hows w hw)]
      exact hfix _ ⟨w, hw, rfl⟩ L (hlab L hL)
    have hnd' : (ows.map (evalElt els)).Nodup := by
      refine List.Nodup.of_map (fun g : Γ => B.map fun p => (tab n g).toArray.getD p 0) ?_
      rw [List.map_map]
      have : ows.map ((fun g : Γ => B.map fun p => (tab n g).toArray.getD p 0) ∘ evalElt els) =
          (ows.map (wordTabA ltabs n)).map fun t => B.map fun p => t.getD p 0 := by
        rw [List.map_map]
        exact List.map_congr_left fun w hw => by simp [hwt w (hows w hw)]
      rw [this]
      exact hnd
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp
      (mem_of_length hnd' hE (by rw [List.length_map, hlen]) x hx)
    exact ⟨w, hw, rfl⟩
  intro y hy hord a ha b hb hbad
  obtain ⟨h, hh, k, hk1, hk6, rfl⟩ := exists_conj_pow h49 hy (hmemY yw hyw) hord hord₀
  set φ : Γ →* Γ := (MulAut.conj h⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj h⁻¹).injective
  have hbad' := hbad.map hφinj
  have hφy : φ (h * y₀ ^ k * h⁻¹) = y₀ ^ k := by simp [hφ, mul_assoc]
  rw [hφy] at hbad'
  have hmemO : ∀ x ∈ pCoreOf 2 (C.Y j), φ x ∈ pCoreOf 2 (C.Y j) := fun x hx => by
    have := conj_mem_pCoreOf ((C.Y j).inv_mem hh) hx
    simpa [hφ] using this
  obtain ⟨wa, hwa, hwa'⟩ := hO2 _ (hmemO a ha)
  obtain ⟨wb, hwb, hwb'⟩ := hO2 _ (hmemO b hb)
  have hyk : (y₀ ^ k) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy₀7, one_pow]
  obtain ⟨hA, hBc, hC⟩ := bad_tab hB hbase hyk hbad'
  rw [tab_pow_arr, ← hty₀] at hA hBc hC
  have hta : (tab n (φ a)).toArray ∈ ows.map (wordTabA ltabs n) :=
    List.mem_map.mpr ⟨wa, hwa, by rw [hwt wa (hows wa hwa), hwa']⟩
  have htb : (tab n (φ b)).toArray ∈ ows.map (wordTabA ltabs n) :=
    List.mem_map.mpr ⟨wb, hwb, by rw [hwt wb (hows wb hwb), hwb']⟩
  have := pairCheck_sound hpair hk1 hk6 hta htb hA hBc
  rw [hC] at this
  exact Bool.noConfusion this

end Member

theorem false_of_lattice {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)
    (hS : IsSylowTwoOf C.S ⊤)
    (hok : ∀ j < C.J, ∀ y ∈ C.Y j, orderOf y = 7 → ∀ a ∈ pCoreOf 2 (C.Y j),
      ∀ b ∈ pCoreOf 2 (C.Y j), ¬ Bad y a b)
    (h : BadData Γ) : False := by
  obtain ⟨N, y, a, b, hSN, hN, hy, hord, ha, hb, hbad⟩ := h.conj hS
  obtain ⟨j, hj, rfl⟩ := C.complete N hSN
  by_cases hjJ : j < C.J
  · have e : memberOrTop C.J C.Y j = C.Y j := by simp [memberOrTop, hjJ]
    rw [e] at hy ha hb
    exact hok j hjJ y hy hord a ha b hb hbad
  · exact hN (by simp [memberOrTop, hjJ])

end CFSG.Quasithin.H13.KGE64
