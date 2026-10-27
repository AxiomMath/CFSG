module

public import CFSG.Sporadic.Schreier.MathieuSylowAutSpec
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open scoped Pointwise

theorem sylow_pointwise_inner_of_one {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (h : ∀ α : MulAut G, (∀ t ∈ (P : Subgroup G), α t = t) →
      ∃ z ∈ (P : Subgroup G), (∀ t ∈ (P : Subgroup G), z * t = t * z) ∧
        ∀ g, α g = z * g * z⁻¹) :
    ∀ (T : Sylow p G) (α : MulAut G), (∀ t ∈ (T : Subgroup G), α t = t) →
      ∃ z : (T : Subgroup G), z ∈ Subgroup.center (T : Subgroup G) ∧
        ∀ g : G, α g = (z : G) * g * (z : G)⁻¹ := by
  intro T α hα
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P T
  have hmem : ∀ x, x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
    intro x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : g⁻¹ * (MulAut.conj g • y) * g = y := by
        rw [MulAut.smul_def, MulAut.conj_apply]
        group
      rwa [e]
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
  set β : MulAut G := (MulAut.conj g)⁻¹ * α * MulAut.conj g with hβdef
  have hβapp : ∀ x, β x = g⁻¹ * α (g * x * g⁻¹) * g := fun x => by
    rw [hβdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hβ : ∀ t ∈ (P : Subgroup G), β t = t := by
    intro t ht
    have hT : g * t * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
      rw [hmem]
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rwa [e]
    rw [hβapp, hα _ hT]
    group
  obtain ⟨z, hzP, hzc, hz⟩ := h β hβ
  have hzT : g * z * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
    rw [hmem]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rwa [e]
  refine ⟨⟨g * z * g⁻¹, hzT⟩, ?_, fun x => ?_⟩
  · rw [Subgroup.mem_center_iff]
    rintro ⟨t, ht⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hc := hzc _ ((hmem t).1 ht)
    calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * t := by group
  · have hx := hz (g⁻¹ * x * g)
    rw [hβapp] at hx
    have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e1] at hx
    have e2 : α x = g * (g⁻¹ * α x * g) * g⁻¹ := by group
    rw [e2, hx]
    group

variable {n : ℕ}

theorem tblEq_of_rep {S T : Table} {g : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T g) :
    tblEq n S T = true :=
  tblEq_iff.2 fun i hi => (hS i hi).trans (hT i hi).symm

theorem exists_entry_of_any {elts : Array Table} {f : Table → Bool}
    (h : elts.any f = true) : ∃ k < elts.size, f elts[k]! = true := by
  rw [Array.any_eq_true] at h
  obtain ⟨k, hk, hf⟩ := h
  exact ⟨k, hk, by rw [getElem!_pos elts k hk]; exact hf⟩

theorem sylow_core_of_checks (hn : n < 2 ^ 32) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : Equiv.Perm (Fin n)} (hgen : G = Subgroup.closure {a, b}) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (hQG : Q.originalSubgroup = G) {N mb r s : ℕ} (hN : Nat.card G = N)
    (hmb : 0 < mb) (hr : 0 < r) (hs : 0 < s) (ha2 : orderOf a = 2) (hbo : orderOf b = mb)
    (hab : orderOf (a * b) = r) (hc : orderOf (a * b * a⁻¹ * b⁻¹) = s)
    (ds exprs : List (List ℤ)) (z0T : Table) (cap k : ℕ)
    (hP : sylowAutOK n (toTable a) (toTable b) ds exprs z0T cap N k = true)
    (hS : survivorsOK n (toTable a) (toTable b) z0T ds exprs r s mb (orderTables Q mb) = true) :
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
  set clo := mulClosure n pT cap with hclodef
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
  have hz0inv : Rep n (invT n z0T) g0⁻¹ := hz0rep.inv_of_invOK h13
  have hz0c : ∀ x ∈ Pg, g0 * x = x * g0 := by
    have hle : Pg ≤ Subgroup.centralizer {g0} := by
      rw [hPgdef, Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      rw [Set.mem_ofPred_eq] at hl
      have hpl : pT[l]! ∈ pT := by
        rw [getElem!_pos pT l hl]
        exact Array.getElem_mem hl
      have hcomm := (Array.all_eq_true_iff_forall_mem.1 h12) _ hpl
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (eq_of_commT hz0rep (hpT l hl) hcomm).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hPgG : Pg ≤ G := by
    rw [hPgdef, Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    exact slpExpr_mem G haG hbG ds _
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
  set a' : G := ⟨a, haG⟩
  set b' : G := ⟨b, hbG⟩
  have ha' : α a' = a' := hα a' ((hmemP a').2 haPg)
  set y : Equiv.Perm (Fin n) := ((α b' : G) : Equiv.Perm (Fin n)) with hydef
  have hyG : y ∈ G := (α b').2
  have hcoe_a : ((α a' : G) : Equiv.Perm (Fin n)) = a := by rw [ha']
  have hyo : orderOf y = mb := by
    rw [hydef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hbo
  have hayo : orderOf (a * y) = r := by
    have e : a * y = ((α (a' * b') : G) : Equiv.Perm (Fin n)) := by
      rw [map_mul, Subgroup.coe_mul, hcoe_a]
    rw [e, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hab
  have hcyo : orderOf (a * y * a⁻¹ * y⁻¹) = s := by
    have e : a * y * a⁻¹ * y⁻¹ = ((α (a' * b' * a'⁻¹ * b'⁻¹) : G) : Equiv.Perm (Fin n)) := by
      rw [hydef]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcoe_a]
    rw [e, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hc
  have hexpr : ∀ i < exprs.length, slpExpr a y ds (exprs.getD i []) = pPerm i := by
    intro i hi
    set φ : G →* Equiv.Perm (Fin n) := G.subtype.comp α.toMonoidHom
    have hφa : φ a' = a := hcoe_a
    have hφb : φ b' = y := rfl
    have h1' := slpExpr_map φ a' b' ds (exprs.getD i [])
    rw [hφa, hφb] at h1'
    rw [h1']
    have hsub := slpExpr_map G.subtype a' b' ds (exprs.getD i [])
    have hval : ((slpExpr a' b' ds (exprs.getD i []) : G) : Equiv.Perm (Fin n)) = pPerm i :=
      hsub.symm
    have hmem : slpExpr a' b' ds (exprs.getD i []) ∈ (P : Subgroup G) := by
      rw [hmemP, hval]
      exact Subgroup.subset_closure ⟨i, by rw [Set.mem_ofPred_eq, hpTsize]; exact hi, rfl⟩
    change ((α (slpExpr a' b' ds (exprs.getD i [])) : G) : Equiv.Perm (Fin n)) = pPerm i
    rw [hα _ hmem, hval]
  have hyQ : y ∈ ((enumeration Q).filter fun h => decide (orderOf h = mb)).reverse := by
    rw [List.mem_reverse, List.mem_filter, mem_enumeration_iff Q hQ, hQG, decide_eq_true_eq]
    exact ⟨hyG, hyo⟩
  obtain ⟨Y, hYmem, hYy⟩ := exists_mem_of_forall₂_left (forall₂_orderTables hn Q hmb) y hyQ
  have hSy := List.all_eq_true.1 hS Y hYmem
  have hpair : pairTest n r s 2 mb (toTable a) Y = true :=
    (pairTest_iff perm_faithful hra hYy hr hs ha2 hyo (by norm_num) hmb).2 ⟨hayo, hcyo⟩
  simp only [hpair, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hSy
  obtain ⟨⟨hV'ok, hws⟩, hfin⟩ := hSy
  have hV' : List.Forall₂ (Rep n) (tblSlp n (toTable a) Y ds).1 (slpVals a y ds) :=
    rep_tblSlp hn hra hYy ds hV'ok
  have htest : ((exprs.map (tblWord n (tblSlp n (toTable a) Y ds).1)).zip
      (sylowGens n (toTable a) (toTable b) ds exprs).toList).all
        (fun q => tblEq n q.1.1 q.2) = true := by
    rw [List.all_eq_true]
    rintro ⟨q1, q2⟩ hq
    obtain ⟨i, hi1, hi2⟩ := List.mem_iff_getElem.1 hq
    simp only [List.length_zip, List.length_map, Array.length_toList, lt_min_iff] at hi1
    rw [List.getElem_zip] at hi2
    simp only [Prod.mk.injEq] at hi2
    obtain ⟨rfl, rfl⟩ := hi2
    simp only [List.getElem_map, Array.getElem_toList]
    have hie : i < exprs.length := hi1.1
    have hok := List.all_eq_true.1 hws _ (List.mem_map.2 ⟨exprs[i], List.getElem_mem hie, rfl⟩)
    have hw := rep_tblWord hn hV' exprs[i] hok
    have hval : wordValue (slpVals a y ds) exprs[i] = pPerm i := by
      rw [← hexpr i hie, slpExpr, List.getD_eq_getElem _ _ hie]
    rw [hval] at hw
    have hpi := hpT i (hpTsize ▸ hie)
    rw [getElem!_pos pT i (hpTsize ▸ hie)] at hpi
    exact tblEq_of_rep hw hpi
  rw [htest] at hfin
  simp only [Bool.not_true, Bool.false_eq_true, false_or] at hfin
  have hzb : Rep n (conjT n z0T (invT n z0T) (toTable b)) (g0 * b * g0⁻¹) :=
    rep_conjT hz0rep hz0inv hrb
  have hgenG : Subgroup.closure ({a', b'} : Set G) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top hgen haG hbG
  have hcase : y = b ∨ y = g0 * b * g0⁻¹ := by
    rcases hfin with h | h
    · exact Or.inl (rep_unique hYy (rep_of_tblEq hrb h))
    · exact Or.inr (rep_unique hYy (rep_of_tblEq hzb h))
  have hg0G : g0 ∈ G := hPgG hz0Pg
  have hag0 : g0 * a = a * g0 := hz0c a haPg
  rcases hcase with hyb | hyb
  · refine ⟨1, (P : Subgroup G).one_mem, fun t _ => by simp, fun g => ?_⟩
    have hαeq : α.toMonoidHom = (MulEquiv.refl G).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense hgenG ?_
      rintro x (rfl | rfl)
      · exact ha'
      · exact Subtype.ext hyb
    have := congrArg (fun f : G →* G => f g) hαeq
    simpa using this
  · set z : G := ⟨g0, hg0G⟩
    refine ⟨z, (hmemP z).2 hz0Pg, fun t ht => Subtype.ext (hz0c _ ((hmemP t).1 ht)), fun g => ?_⟩
    have hαeq : α.toMonoidHom = (MulAut.conj z).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense hgenG ?_
      rintro x (rfl | rfl)
      · change α a' = z * a' * z⁻¹
        rw [ha']
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, z, a']
        rw [hag0, mul_inv_cancel_right]
      · change α b' = z * b' * z⁻¹
        apply Subtype.ext
        exact hyb
    have := congrArg (fun f : G →* G => f g) hαeq
    simpa using this

theorem sylow_pointwise_inner_of_checks (hn : n < 2 ^ 32) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : Equiv.Perm (Fin n)} (hgen : G = Subgroup.closure {a, b}) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (hQG : Q.originalSubgroup = G) {N mb r s : ℕ} (hN : Nat.card G = N)
    (hmb : 0 < mb) (hr : 0 < r) (hs : 0 < s) (ha2 : orderOf a = 2) (hbo : orderOf b = mb)
    (hab : orderOf (a * b) = r) (hc : orderOf (a * b * a⁻¹ * b⁻¹) = s)
    (ds exprs : List (List ℤ)) (z0T : Table) (cap k : ℕ)
    (hP : sylowAutOK n (toTable a) (toTable b) ds exprs z0T cap N k = true)
    (hS : survivorsOK n (toTable a) (toTable b) z0T ds exprs r s mb (orderTables Q mb) = true) :
    ∀ (T : Sylow 2 G) (α : MulAut G), (∀ t ∈ (T : Subgroup G), α t = t) →
      ∃ z : (T : Subgroup G), z ∈ Subgroup.center (T : Subgroup G) ∧
        ∀ g : G, α g = (z : G) * g * (z : G)⁻¹ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP'⟩ := sylow_core_of_checks hn G hgen Q hQ hQG hN hmb hr hs ha2 hbo hab hc ds
    exprs z0T cap k hP hS
  exact sylow_pointwise_inner_of_one P hP'

end CFSG.Sporadic.Schreier
