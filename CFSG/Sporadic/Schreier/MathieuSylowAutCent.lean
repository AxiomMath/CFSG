module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def sylCentOK (n : ℕ) (pT : Array Table) (z0T bT : Table) (L : List Table) : Bool :=
  !(commT n z0T bT) &&
    L.all fun D => !(pT.all fun p => commT n D p) || tblEq n D (idT n) || tblEq n D z0T

variable {n : ℕ}

theorem centralizerIn_eq_of_reps (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup ∧ orderOf r = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q 1 2) (reps.map toTable) cap = true)
    {r : Equiv.Perm (Fin n)} (hr : r ∈ reps) {K : Subgroup (Equiv.Perm (Fin n))}
    (hK : K ≤ centralizerIn Q.originalSubgroup r)
    (hcard : (conjClosure n gens gensInv (toTable r) cap).1.size * Nat.card K =
      Nat.card Q.originalSubgroup) :
    centralizerIn Q.originalSubgroup r = K := by
  have h := (exists_conj_of_repsOK hn Q hQ hg 1 (fun h hh => by simpa using hh) (by norm_num) reps
    (fun r hr => by simpa using hreps r hr) cap hok).2 r hr
  exact centralizerIn_eq_of_le _ r hK h hcard

theorem sylow_core_of_cent (hn : n < 2 ^ 32) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : Equiv.Perm (Fin n)} (hgen : G = Subgroup.closure {a, b}) {N : ℕ} (hN : Nat.card G = N)
    (hAut : Nat.card (MulAut G) ≤ Nat.card G) (ds exprs : List (List ℤ)) (z0T : Table)
    (cap k : ℕ) (hP : sylowAutOK n (toTable a) (toTable b) ds exprs z0T cap N k = true)
    (C : RawSchreierDatum n) (hC : ValidSchreier C)
    (hCa : centralizerIn G a ≤ C.originalSubgroup)
    (hS : sylCentOK n (sylowGens n (toTable a) (toTable b) ds exprs) z0T (toTable b)
      (allTables C) = true) :
    ∃ P : Sylow 2 G, ∀ α : MulAut G, (∀ t ∈ (P : Subgroup G), α t = t) →
      ∃ z ∈ (P : Subgroup G), (∀ t ∈ (P : Subgroup G), z * t = t * z) ∧
        ∀ g, α g = z * g * z⁻¹ := by
  classical
  have haG : a ∈ G := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbG : b ∈ G := hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hra : Rep n (toTable a) a := rep_toTable hn a
  have hrb : Rep n (toTable b) b := rep_toTable hn b
  simp only [sylowAutOK, Bool.and_eq_true, beq_iff_eq] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hP
  set V := tblSlp n (toTable a) (toTable b) ds with hVdef
  set pT := sylowGens n (toTable a) (toTable b) ds exprs with hpTdef
  have hV : List.Forall₂ (Rep n) V.1 (slpVals a b ds) := rep_tblSlp hn hra hrb ds h1
  let pPerm : ℕ → Equiv.Perm (Fin n) := fun i => slpExpr a b ds (exprs.getD i [])
  have hpTsize : pT.size = exprs.length := by simp [hpTdef, sylowGens]
  have hpT : ∀ i < pT.size, Rep n pT[i]! (pPerm i) := by
    intro i hi
    have hi' : i < exprs.length := hpTsize ▸ hi
    have hget : pT[i]! = (tblWord n V.1 exprs[i]).1 := by
      rw [getElem!_pos pT i hi]
      simp [hpTdef, sylowGens, hVdef]
    have hok := List.all_eq_true.1 h2 exprs[i] (List.getElem_mem hi')
    rw [hget]
    have hpp : pPerm i = wordValue (slpVals a b ds) exprs[i] := by
      simp only [pPerm, slpExpr, List.getD_eq_getElem _ _ hi']
    rw [hpp]
    exact rep_tblWord hn hV _ hok
  have hgs : ∀ l < pT.size, Rep n pT[l]! (pPerm l) ∧ Rep n (pT.map (invT n))[l]! (pPerm l)⁻¹ := by
    intro l hl
    refine ⟨hpT l hl, ?_⟩
    have hinv := List.all_eq_true.1 h3 l (List.mem_range.2 hl)
    exact (hpT l hl).inv_of_invOK hinv
  obtain ⟨-, -, -, hcard⟩ := card_closure_of_mulTree hn hgs h4 h5 h6
  set Pg := Subgroup.closure (pPerm '' {l | l < pT.size}) with hPgdef
  have hmemPg := mem_closure_iff_of_mulTree hn hgs h4 h5
  have hPgcard : Nat.card Pg = 2 ^ k := hcard.trans h7
  have haPg : a ∈ Pg := by
    obtain ⟨j, hj, hjt⟩ := exists_entry_of_any h10
    exact (hmemPg a).2 ⟨j, hj, rep_of_tblEq hra hjt⟩
  obtain ⟨j, hj, hjt⟩ := exists_entry_of_any h11
  obtain ⟨g0, hg0⟩ := exists_rep_of_mulTree hn (fun l hl => (hgs l hl).1) h4 j hj
  have hz0rep : Rep n z0T g0 := rep_of_tblEq hg0 hjt
  have hz0Pg : g0 ∈ Pg := (hmemPg g0).2 ⟨j, hj, hg0⟩
  have hcentPg : ∀ c : Equiv.Perm (Fin n), (∀ l < pT.size, c * pPerm l = pPerm l * c) →
      ∀ x ∈ Pg, c * x = x * c := by
    intro c hc
    have hle : Pg ≤ Subgroup.centralizer {c} := by
      rw [hPgdef, Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hc l hl).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hz0c : ∀ x ∈ Pg, g0 * x = x * g0 := by
    refine hcentPg g0 fun l hl => ?_
    have hpl : pT[l]! ∈ pT := by
      rw [getElem!_pos pT l hl]
      exact Array.getElem_mem hl
    exact eq_of_commT hz0rep (hpT l hl) ((Array.all_eq_true_iff_forall_mem.1 h12) _ hpl)
  have hPgG : Pg ≤ G := by
    rw [hPgdef, Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    exact slpExpr_mem G haG hbG ds _
  simp only [sylCentOK, Bool.and_eq_true, Bool.not_eq_true'] at hS
  obtain ⟨hzb, hL⟩ := hS
  have hkey : ∀ c ∈ G, (∀ l < pT.size, c * pPerm l = pPerm l * c) → c = 1 ∨ c = g0 := by
    intro c hcG hc
    have hca : c * a = a * c := hcentPg c hc a haPg
    have hcC : c ∈ C.originalSubgroup := hCa (mem_centralizerIn.2 ⟨hcG, hca⟩)
    have hcE : c ∈ (enumeration C).reverse := by
      rw [List.mem_reverse, mem_enumeration_iff C hC]
      exact hcC
    obtain ⟨D, hD, hDc⟩ := exists_mem_of_forall₂_left (forall₂_allTables hn C) c hcE
    have hall : (pT.all fun p => commT n D p) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro p hp
      obtain ⟨l, hl, rfl⟩ := Array.getElem_of_mem hp
      have hr := hpT l hl
      rw [getElem!_pos pT l hl] at hr
      exact (commT_iff hDc hr).2 (hc l hl)
    have hD' := List.all_eq_true.1 hL D hD
    simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hD'
    rcases hD' with h | h
    · exact Or.inl (eq_one_of_tblEq_idT hn hDc h)
    · exact Or.inr (rep_unique hDc (rep_of_tblEq hz0rep h))
  have hz0b : g0 * b ≠ b * g0 := fun h => by
    rw [(commT_iff hz0rep hrb).2 h] at hzb
    exact Bool.false_ne_true hzb.symm
  have hpG : ∀ l, pPerm l ∈ G := fun l => slpExpr_mem G haG hbG ds _
  have hcenter : Subgroup.center G = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_center_iff] at hx
    have hcomm : ∀ y ∈ G, (x : Equiv.Perm (Fin n)) * y = y * x := fun y hy =>
      (congrArg Subtype.val (hx ⟨y, hy⟩)).symm
    rcases hkey x x.2 (fun l _ => hcomm _ (hpG l)) with h | h
    · rw [Subgroup.mem_bot]
      exact Subtype.ext h
    · exact absurd (h ▸ hcomm b hbG) hz0b
  set Pc := Pg.subgroupOf G with hPcdef
  have hPccard : Nat.card Pc = 2 ^ k :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPgG).toEquiv).trans hPgcard
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 Pc := IsPGroup.of_card hPccard
  have hidx : ¬ 2 ∣ Pc.index := by
    have hci := Subgroup.card_mul_index Pc
    rw [hPccard, hN] at hci
    have hq : Pc.index = N / 2 ^ k := by
      rw [← hci, Nat.mul_div_cancel_left _ (by positivity)]
    rw [hq]
    omega
  let P : Sylow 2 G := hpg.toSylow hidx
  have hmemP : ∀ x : G, x ∈ (P : Subgroup G) ↔ (x : Equiv.Perm (Fin n)) ∈ Pg := fun x => by
    rw [IsPGroup.toSylow_coe, hPcdef, Subgroup.mem_subgroupOf]
  refine ⟨P, fun α hα => ?_⟩
  have hinner : α ∈ inner G := by
    rw [inner_eq_top_of_card_le hcenter hAut]
    trivial
  obtain ⟨g, rfl⟩ := hinner
  have hgp : ∀ l < pT.size, (g : Equiv.Perm (Fin n)) * pPerm l = pPerm l * g := by
    intro l hl
    have hmem : (⟨pPerm l, hpG l⟩ : G) ∈ (P : Subgroup G) := by
      rw [hmemP]
      exact Subgroup.subset_closure ⟨l, hl, rfl⟩
    have h := congrArg Subtype.val (hα _ hmem)
    rw [MulAut.conj_apply] at h
    have e : (g : Equiv.Perm (Fin n)) * pPerm l * (g : Equiv.Perm (Fin n))⁻¹ = pPerm l := by
      simpa using h
    calc (g : Equiv.Perm (Fin n)) * pPerm l
        = (g * pPerm l * (g : Equiv.Perm (Fin n))⁻¹) * g := by group
      _ = pPerm l * g := by rw [e]
  have hgP : (g : Equiv.Perm (Fin n)) ∈ Pg := by
    rcases hkey g g.2 hgp with h | h
    · rw [h]
      exact Pg.one_mem
    · rw [h]
      exact hz0Pg
  refine ⟨g, (hmemP g).2 hgP, fun t ht => Subtype.ext (hcentPg g hgp _ ((hmemP t).1 ht)),
    fun x => ?_⟩
  rw [MulAut.conj_apply]

theorem sylow_pointwise_inner_of_cent (hn : n < 2 ^ 32) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : Equiv.Perm (Fin n)} (hgen : G = Subgroup.closure {a, b}) {N : ℕ} (hN : Nat.card G = N)
    (hAut : Nat.card (MulAut G) ≤ Nat.card G) (ds exprs : List (List ℤ)) (z0T : Table)
    (cap k : ℕ) (hP : sylowAutOK n (toTable a) (toTable b) ds exprs z0T cap N k = true)
    (C : RawSchreierDatum n) (hC : ValidSchreier C)
    (hCa : centralizerIn G a ≤ C.originalSubgroup)
    (hS : sylCentOK n (sylowGens n (toTable a) (toTable b) ds exprs) z0T (toTable b)
      (allTables C) = true) :
    ∀ (T : Sylow 2 G) (α : MulAut G), (∀ t ∈ (T : Subgroup G), α t = t) →
      ∃ z : (T : Subgroup G), z ∈ Subgroup.center (T : Subgroup G) ∧
        ∀ g : G, α g = (z : G) * g * (z : G)⁻¹ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP'⟩ := sylow_core_of_cent hn G hgen hN hAut ds exprs z0T cap k hP C hC hCa hS
  exact sylow_pointwise_inner_of_one P hP'

end CFSG.Sporadic.Schreier

end
