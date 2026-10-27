module

public import CFSG.YGroups.Y433.Bound
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.DCE.OrbitLower
public import CFSG.YGroups.DCE.B433Check

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open scoped Pointwise

@[expose] noncomputable def J432 : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (yGen 4 3 2 '' {c | c < 10 ∧ c ≠ 4})

@[expose] def J432Enum : Bool :=
  CFSG.YGroups.Native.enumOK (ngen 4 3 2) (yRels 4 3 2)
    [[0], [1], [2], [3], [5], [6], [7], [8], [9]] 20000000 31671

theorem index_J432_le (h : J432Enum = true) : J432.index ≤ 31671 := by
  refine (index_le_of_enumOK (closure_yGen 4 3 2) (yGen_of_le le_rfl) (yGen_mul_self 4 3 2)
    (fun w hw => evalWord_yGen_of_mem hw) ?_ h).2
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have hmem : ∀ c < 10, c ≠ 4 → yGen 4 3 2 c ∈ J432 := fun c hc hc4 =>
    Subgroup.subset_closure ⟨c, ⟨hc, hc4⟩, rfl⟩
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [evalWord_cons, evalWord_nil, mul_one]
      exact hmem _ (by norm_num) (by norm_num)

@[expose] def Pt432 : Type := Fin 31671

@[expose] def toPt (x : Fin 31671) : Pt432 := x

@[expose] def ofPt (ω : Pt432) : Fin 31671 := ω

noncomputable instance :
    MulAction (YGroup 4 3 2) Pt432 :=
  MulAction.compHom (Fin 31671) rho432F

instance : Fintype Pt432 := inferInstanceAs (Fintype (Fin 31671))

instance : Finite Pt432 := inferInstanceAs (Finite (Fin 31671))

theorem smul_toPt
    (e : YGroup 4 3 2) (x : Fin 31671) : e • toPt x = toPt (rho432F e x) := rfl

theorem toPt_ofPt (ω : Pt432) : toPt (ofPt ω) = ω := rfl

theorem toPt_inj {x y : Fin 31671} : toPt x = toPt y ↔ x = y := Iff.rfl

theorem card_pt432 : Nat.card Pt432 = 31671 := Nat.card_fin 31671

@[expose] def pt0 : Pt432 := toPt 0

theorem stabilizer_zero_eq
    (h0 : ∀ c < 10, c ≠ 4 → rho432F (yGen 4 3 2 c) 0 = 0)
    (horb : 31671 ≤ (MulAction.orbit (YGroup 4 3 2) pt0).ncard) (hJ : J432.index ≤ 31671) :
    MulAction.stabilizer (YGroup 4 3 2) pt0 = J432 := by
  have := finite_y432
  have hle : J432 ≤ MulAction.stabilizer (YGroup 4 3 2) pt0 := by
    rw [J432, Subgroup.closure_le]
    rintro _ ⟨c, ⟨hc, hc4⟩, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, pt0, smul_toPt, h0 c hc hc4]
  have hidx : 31671 ≤ (MulAction.stabilizer (YGroup 4 3 2) pt0).index := by
    rw [MulAction.index_stabilizer]
    exact horb
  have hmul := Subgroup.relIndex_mul_index hle
  have h1 : J432.relIndex (MulAction.stabilizer (YGroup 4 3 2) pt0) = 1 := by
    have hpos : 0 < (MulAction.stabilizer (YGroup 4 3 2) pt0).index := by omega
    have : J432.relIndex (MulAction.stabilizer (YGroup 4 3 2) pt0) *
        (MulAction.stabilizer (YGroup 4 3 2) pt0).index ≤
        1 * (MulAction.stabilizer (YGroup 4 3 2) pt0).index := by
      rw [hmul, one_mul]
      omega
    have h2 := Nat.le_of_mul_le_mul_right this hpos
    have h3 : J432.relIndex (MulAction.stabilizer (YGroup 4 3 2) pt0) ≠ 0 := by
      intro h0'
      rw [h0', zero_mul] at hmul
      have := Subgroup.index_ne_zero_of_finite (H := J432)
      omega
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle

@[expose] noncomputable def P333 : Subgroup B433 :=
  Subgroup.closure ((fun l => qB (yGen 4 3 3 l)) '' {l | l < 11 ∧ l ≠ 4})

theorem tB_mem_P333 : tB ∈ P333 :=
  Subgroup.subset_closure ⟨10, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem map_J432_le_P333 : J432.map psi ≤ P333 := by
  rw [J432, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, ⟨hc, hc4⟩, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨c, ⟨by omega, hc4⟩, ?_⟩
  show qB (yGen 4 3 3 c) = psi (yGen 4 3 2 c)
  rw [psi, MonoidHom.comp_apply, psiU_yGen hc]

@[expose] def allSlots (fin : B.NodeFin) : Array ℕ :=
  fin.chain.foldl (fun a lv => a ++ lv.2) fin.fgens

@[expose] def slotGens {E : B.EnvB} (st : B.RSt E) (sl : Array ℕ) : Array (B.WEltB E) :=
  sl.filterMap fun w => B.RSt.get st.ws w

@[expose] def slotRec {E : B.EnvB} (st : B.RSt E) (β : ℕ) (sl : Array ℕ) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  B.orbitRec E.C.n β ((slotGens st sl).map (·.1.2))

@[expose] def recValid (n β : ℕ) (gens : Array ByteArray)
    (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : Bool :=
  decide (β < n) && r.2.1.size == n && r.1.size != 0 && r.1[0]! == β &&
    allLt r.1.size fun t =>
      let x := r.1[t]!
      decide (x < n) && r.2.1[x]! == t &&
        (t == 0 || (decide (r.2.2.2[x]! < gens.size) && decide (r.2.2.1[x]! < n) &&
          decide (r.2.1[r.2.2.1[x]!]! < t) && r.1[r.2.1[r.2.2.1[x]!]!]! == r.2.2.1[x]! &&
          bget gens[r.2.2.2[x]!]! r.2.2.1[x]! == x))

@[expose] def recOK {E : B.EnvB} (st : B.RSt E) (j β : ℕ) (sl : Array ℕ) : Bool :=
  (slotGens st sl).all (fun s => s.1.1 == j) &&
    recValid E.C.n β ((slotGens st sl).map (·.1.2)) (slotRec st β sl)

@[expose] def recMem {E : B.EnvB} (st : B.RSt E) (β : ℕ) (sl : Array ℕ) (w : ℕ) : Bool :=
  let r := slotRec st β sl
  decide (w < E.C.n) && decide (r.2.1[w]! < r.1.size) && r.1[r.2.1[w]!]! == w

@[expose] def exploreOK (E : B.EnvB) (st : B.RSt E) (O : BigOmega) (fins : Array (ℕ × B.NodeFin))
    (labs : Array (ℕ × ℕ)) (moves : Array (ℕ × ℕ × ℕ)) (ord total : ℕ) : Bool :=
  decide (0 < labs.size) && labs[0]! == (0, 0) && moves.size + 1 == labs.size &&
    decide (E.C.n ≤ (slotRec st 0 (allSlots fins[0]!.2)).1.size) &&
    allLt labs.size (fun i => decide (labs[i]!.1 < fins.size) &&
      recOK st fins[labs[i]!.1]!.1 labs[i]!.2 (allSlots fins[labs[i]!.1]!.2)) &&
    allLt labs.size (fun i => allLt i fun i' => labs[i']!.1 != labs[i]!.1) &&
    allLt moves.size (fun m =>
      decide (moves[m]!.1 < m + 1) &&
      match B.RSt.get st.vs moves[m]!.2.1 with
      | some f => f.1.i == fins[labs[moves[m]!.1]!.1]!.1 && f.1.k == fins[labs[m + 1]!.1]!.1 &&
          decide (f.1.p < E.C.N) &&
          recMem st labs[moves[m]!.1]!.2 (allSlots fins[labs[moves[m]!.1]!.1]!.2) moves[m]!.2.2 &&
          (List.range O.m).any (fun k => (O.row f.1.p)[k]! == moves[m]!.2.2) &&
          bget f.1.a moves[m]!.2.2 == labs[m + 1]!.2
      | none => false) &&
    decide (total ≤ (List.range labs.size).foldl (fun a i =>
      a + ord / E.chainBound st fins[labs[i]!.1]!.2 *
        (slotRec st labs[i]!.2 (allSlots fins[labs[i]!.1]!.2)).1.size) 0)

@[expose] def y333Labs : Array (ℕ × ℕ) :=
  #[(0, 0), (1, 0), (2, 1), (3, 1), (4, 3), (8, 4131), (9, 2), (17, 1)]

@[expose] def y333Moves : Array (ℕ × ℕ × ℕ) :=
  #[(0, 0, 0), (1, 10, 1), (1, 11, 1), (1, 31, 3), (1, 4557, 4131), (1, 4869, 2), (3, 31992, 1)]

@[expose] def y333Check :
    Bool :=
  let L := lettersB ()
  let O := omegaB433 L
  let cert := certB433 ()
  if h : bigOK O L fixB = true ∧ smallOK O L cert = true then
    let S : Checked L O cert := ⟨rfl, rfl, h.1, h.2⟩
    let E := env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK
    let R0 := B.orbitRec 31671 0 (L.extract 0 9)
    allLt 10 (fun c => c == 4 || bget L[c]! 0 == 0) &&
      recValid 31671 0 (L.extract 0 9) R0 &&
      x0B.all (fun x => decide (x < 31671) && decide (R0.2.1[x]! < R0.1.size) &&
        R0.1[R0.2.1[x]!]! == x) &&
      exploreOK E (B.replay E cert.prog) O cert.fins y333Labs y333Moves 4089470473293004800
        37543283785728
  else false

theorem recValid_spec
    {β : ℕ} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValid 31671 β gens r = true)
    (K : Subgroup (YGroup 4 3 2))
    (hgens : ∀ i < gens.size, ∃ e ∈ K, RepB 31671 gens[i]! (rho432F e)) :
    ∃ hβ : β < 31671,
      (∀ t < r.1.size, ∃ hx : r.1[t]! < 31671,
        toPt ⟨r.1[t]!, hx⟩ ∈ MulAction.orbit K (toPt ⟨β, hβ⟩)) ∧
      ∀ t < r.1.size, r.2.1[r.1[t]!]! = t := by
  unfold recValid at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hβ, -⟩, -⟩, h0⟩, hall⟩ := h
  have hβ' : β < 31671 := of_decide_eq_true hβ
  have h0' : r.1[0]! = β := beq_iff_eq.1 h0
  have hpt : ∀ t < r.1.size, r.1[t]! < 31671 ∧ r.2.1[r.1[t]!]! = t ∧ (t = 0 ∨
      (r.2.2.2[r.1[t]!]! < gens.size ∧ r.2.2.1[r.1[t]!]! < 31671 ∧
        r.2.1[r.2.2.1[r.1[t]!]!]! < t ∧ r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]! = r.2.2.1[r.1[t]!]! ∧
        bget gens[r.2.2.2[r.1[t]!]!]! r.2.2.1[r.1[t]!]! = r.1[t]!)) := by
    intro t ht
    have := allLt_spec hall ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h3 | ⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h4, h5, h6, h7, h8⟩
  refine ⟨hβ', ?_, fun t ht => (hpt t ht).2.1⟩
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    obtain ⟨hx, -, htree⟩ := hpt t ht
    refine ⟨hx, ?_⟩
    rcases htree with rfl | ⟨htl, htp, hpp, hpe, hg⟩
    · have : (⟨r.1[0]!, hx⟩ : Fin 31671) = ⟨β, hβ'⟩ := Fin.ext h0'
      rw [this]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hy, ⟨⟨k, hk⟩, hkβ⟩⟩ := ih _ hpp (hpp.trans ht)
      obtain ⟨e, heK, hrep⟩ := hgens _ htl
      refine ⟨⟨e * k, K.mul_mem heK hk⟩, ?_⟩
      have hkβ' : k • toPt ⟨β, hβ'⟩ = toPt ⟨r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]!, hy⟩ := hkβ
      show (e * k) • toPt ⟨β, hβ'⟩ = toPt ⟨r.1[t]!, hx⟩
      rw [mul_smul, hkβ', smul_toPt, toPt_inj]
      apply Fin.ext
      have h2 := hrep.2 ⟨r.2.2.1[r.1[t]!]!, htp⟩
      have h3 : (⟨r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]!, hy⟩ : Fin 31671) =
          ⟨r.2.2.1[r.1[t]!]!, htp⟩ := Fin.ext hpe
      rw [h3, ← h2]
      exact hg

theorem le_ncard_orbit_of_recValid
    {β : ℕ} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValid 31671 β gens r = true)
    (K : Subgroup (YGroup 4 3 2))
    (hgens : ∀ i < gens.size, ∃ e ∈ K, RepB 31671 gens[i]! (rho432F e)) (hβ : β < 31671) :
    r.1.size ≤ (MulAction.orbit K (toPt ⟨β, hβ⟩)).ncard := by
  obtain ⟨hβ', hmem, hpos⟩ := recValid_spec h K hgens
  let f : Fin r.1.size → MulAction.orbit K (toPt ⟨β, hβ⟩) := fun t =>
    ⟨toPt ⟨r.1[t.1]!, (hmem t.1 t.2).1⟩, (hmem t.1 t.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : r.1[a.1]! = r.1[b.1]! := by
      have := congrArg (fun x => (ofPt x.1).1) hab
      exact this
    apply Fin.ext
    rw [← hpos a.1 a.2, ← hpos b.1 b.2, h1]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rwa [← Nat.card_coe_set_eq]

@[expose] def ptOf (w : ℕ) : Pt432 := toPt ⟨w % 31671, Nat.mod_lt _ (by norm_num)⟩

theorem ptOf_eq {w : ℕ} (hw : w < 31671) : ptOf w = toPt ⟨w, hw⟩ := by
  unfold ptOf
  rw [toPt_inj]
  exact Fin.ext (Nat.mod_eq_of_lt hw)

theorem exists_smul_of_mem
    (hG : Good x0B)
    (hX : ∀ x : Fin 31671, x ∈ listFinset 31671 x0B → ∃ c ∈ Ctil432, rho432F c 0 = x)
    (q : Pts x0B) {w : Fin 31671} (hw : w ∈ (q : Finset (Fin 31671))) :
    ∃ g : YGroup 4 3 2, g • pt0 = toPt w ∧ g • basePt x0B = q := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 q.2
  have hh' : rho432F h • listFinset 31671 x0B = (q : Finset (Fin 31671)) := hh
  rw [← hh', Finset.mem_smul_finset] at hw
  obtain ⟨x, hx, hxw⟩ := hw
  obtain ⟨c, hc, hcx⟩ := hX x hx
  refine ⟨h * c, ?_, ?_⟩
  · rw [pt0, smul_toPt, map_mul, Equiv.Perm.mul_apply, hcx, toPt_inj]
    exact hxw
  · rw [mul_smul]
    have hcb : c • basePt x0B = basePt x0B := by
      apply Subtype.ext
      exact (ctil_le_stabilizer hG hc : c • listFinset 31671 x0B = listFinset 31671 x0B)
    rw [hcb]
    apply Subtype.ext
    exact hh

theorem x0_orbit
    {L : Array ByteArray} (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)))
    (hLs : L.size = 10)
    (hR : recValid 31671 0 (L.extract 0 9) (B.orbitRec 31671 0 (L.extract 0 9)) = true)
    (hx : x0B.all (fun x => decide (x < 31671) &&
      decide ((B.orbitRec 31671 0 (L.extract 0 9)).2.1[x]! <
        (B.orbitRec 31671 0 (L.extract 0 9)).1.size) &&
      (B.orbitRec 31671 0 (L.extract 0 9)).1[(B.orbitRec 31671 0 (L.extract 0 9)).2.1[x]!]! ==
        x) = true) :
    ∀ x : Fin 31671, x ∈ listFinset 31671 x0B → ∃ c ∈ Ctil432, rho432F c 0 = x := by
  have hgens : ∀ i < (L.extract 0 9).size, ∃ e ∈ Ctil432,
      RepB 31671 (L.extract 0 9)[i]! (rho432F e) := by
    intro i hi
    have hi9 : i < 9 := by simp [hLs] at hi; omega
    refine ⟨yGen 4 3 2 i, yGen_mem_ctil432 (by omega) (by omega), ?_⟩
    have : (L.extract 0 9)[i]! = L[i]! := by
      rw [getElem!_pos _ i hi, getElem!_pos L i (by omega)]
      simp
    rw [this]
    exact hL i (by omega)
  obtain ⟨h0lt, hmem, -⟩ := recValid_spec hR Ctil432 hgens
  intro x hx0
  obtain ⟨k, hk, hkx⟩ := mem_listFinset.1 hx0
  have hall := Array.all_eq_true_iff_forall_mem.1 hx _ (Array.getElem_mem hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  obtain ⟨⟨-, hpos⟩, hpt⟩ := hall
  rw [← getElem!_pos x0B k hk] at hpos hpt
  obtain ⟨hlt, ⟨⟨c, hc⟩, hcx⟩⟩ := hmem _ hpos
  refine ⟨c, hc, ?_⟩
  have hcx' : toPt (rho432F c ⟨0, by norm_num⟩) = toPt ⟨_, hlt⟩ := hcx
  rw [toPt_inj] at hcx'
  apply Fin.ext
  have h1 := congrArg Fin.val hcx'
  simp only at h1
  rw [show (0 : Fin 31671) = ⟨0, by norm_num⟩ from rfl, h1, hpt, hkx]

section Records

variable {L : Array ByteArray} {O : BigOmega} {cert : B.Cert} (S : Checked L O cert)

theorem recOK_spec
    {st : B.RSt (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK)}
    {j β : ℕ} {sl : Array ℕ} (hr : recOK st j β sl = true) :
    ∃ hβ : β < 31671,
      (slotRec st β sl).1.size ≤
        (MulAction.orbit (B.stabSub (setup S.good) (xNode S.good S.pt (ctxB433 O L cert).nodes j))
          (toPt ⟨β, hβ⟩)).ncard ∧
      ∀ w, recMem st β sl w = true → ∃ hw : w < 31671, toPt ⟨w, hw⟩ ∈
        MulAction.orbit (B.stabSub (setup S.good) (xNode S.good S.pt (ctxB433 O L cert).nodes j))
          (toPt ⟨β, hβ⟩) := by
  have hn : (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK).C.n = 31671 :=
    S.ctxGood.n_eq
  unfold recOK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hall, hv⟩ := hr
  rw [hn] at hv
  set K := B.stabSub (setup S.good) (xNode S.good S.pt (ctxB433 O L cert).nodes j)
  have hgens : ∀ i < ((slotGens st sl).map (·.1.2)).size, ∃ e ∈ K,
      RepB 31671 ((slotGens st sl).map (·.1.2))[i]! (rho432F e) := by
    intro i hi
    have hi' : i < (slotGens st sl).size := by simpa using hi
    set w := (slotGens st sl)[i]'hi'
    have hwj : w.1.1 = j := by
      have := Array.all_eq_true_iff_forall_mem.1 hall w (Array.getElem_mem hi')
      simpa using this
    obtain ⟨e, hrep, he⟩ := w.2
    refine ⟨e, (B.mem_stabSub _ _ _).2 ?_, ?_⟩
    · rw [← hwj]
      exact he
    · have : ((slotGens st sl).map (·.1.2))[i]! = w.1.2 := by
        rw [getElem!_pos _ i hi]
        simp [w]
      rw [this]
      exact hrep
  have hrec : slotRec st β sl =
      B.orbitRec 31671 β ((slotGens st sl).map (·.1.2)) := by
    unfold slotRec
    rw [hn]
  rw [hrec] at hv
  obtain ⟨hβ, hmem, hpos⟩ := recValid_spec hv K hgens
  refine ⟨hβ, ?_, ?_⟩
  · rw [hrec]
    exact le_ncard_orbit_of_recValid hv K hgens hβ
  · intro w hw
    unfold recMem at hw
    rw [hrec, hn] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
    obtain ⟨⟨hwn, hwp⟩, hwe⟩ := hw
    obtain ⟨hlt, hmw⟩ := hmem _ hwp
    refine ⟨hwn, ?_⟩
    have : (⟨_, hlt⟩ : Fin 31671) = ⟨w, hwn⟩ := Fin.ext hwe
    rw [← this]
    exact hmw

end Records

private theorem foldl_add_eq_sum (f : ℕ → ℕ) (m : ℕ) :
    (List.range m).foldl (fun a i => a + f i) 0 = ((List.range m).map f).sum := by
  have key : ∀ (l : List ℕ) (init : ℕ),
      l.foldl (fun a i => a + f i) init = init + (l.map f).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ih => intro init; rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring
  rw [key, zero_add]

private theorem foldl_add_eq_finset_sum (f : ℕ → ℕ) (m : ℕ) :
    (List.range m).foldl (fun a i => a + f i) 0 = ∑ i ∈ Finset.range m, f i := by
  rw [foldl_add_eq_sum]
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem index_psi_ge_of_card
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    1015970529280000 ≤ psi.range.index := by
  have := B433_finite_card_le.1
  have hcard := Subgroup.card_mul_index psi.range
  have hH := card_range_psi_le
  by_contra hlt
  rw [not_le] at hlt
  have : Nat.card B433 < 4154781481226426191177580544000000 := by
    rw [← hcard]
    calc Nat.card psi.range * psi.range.index
        ≤ 4089470473293004800 * psi.range.index := Nat.mul_le_mul_right _ hH
      _ < 4089470473293004800 * 1015970529280000 :=
          Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = 4154781481226426191177580544000000 := by norm_num
  omega

theorem card_P333_ge_of_check
    (h : b433Check = true) (hy : y333Check = true) (hJ : J432Enum = true)
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    153064959367549707878400 ≤ Nat.card P333 := by
  classical
  have := finite_y432
  have := B433_finite_card_le.1
  unfold b433Check at h
  unfold y333Check at hy
  dsimp only at h hy
  split at h
  swap
  · cases h
  rename_i hc
  rw [dite_eq_left hc] at hy
  set S : Checked (lettersB ()) (omegaB433 (lettersB ())) (certB433 ()) :=
    ⟨rfl, rfl, hc.1, hc.2⟩ with hS
  set E := env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK with hE
  have hn : E.C.n = 31671 := S.ctxGood.n_eq
  have hfin : E.finalOK (certB433 ()).prog (certB433 ()).fins 4089470473293004800
      1015970529280000 = true := h
  obtain ⟨-, -, hroot, -, hcount⟩ := B.EnvB.finalOK_spec hfin
  set fins := (certB433 ()).fins with hfins
  set st := B.replay E (certB433 ()).prog with hst
  set xN := xNode S.good S.pt (ctxB433 (omegaB433 (lettersB ())) (lettersB ()) (certB433 ())).nodes
    with hxN
  have hx0 : xN 0 ∈ (setup S.good).H := by
    rw [hxN, xNode_zero]
    exact Subgroup.one_mem _
  obtain ⟨hindex, hdisj⟩ := exact_of_finalOK E (setup S.good) (n := 31671) S.ctxGood.n_eq rho432F
    S.pt xN (fun j a hW => hW)
    (fun i p k a hV => ⟨hV.1, by obtain ⟨e, -, he⟩ := hV.2; exact ⟨e, he⟩⟩)
    S.actAllSpec S.ptSurj hx0
    (fun j e he => Subgroup.map_le_range psi rho432F.ker
      (conj_ker_mem (xN j) (MonoidHom.mem_ker.2 he)))
    4089470473293004800 1015970529280000 card_range_rho432F closure_psi_t (certB433 ()).prog fins
    hfin (by rw [foldl_add_eq_finset_sum]; exact hcount.trans (index_psi_ge_of_card hG))
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨⟨hfix0, hR0⟩, hX0⟩, hex⟩ := hy
  unfold exploreOK at hex
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hex
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hn0⟩, hrecs⟩, -⟩, hmoves⟩, htotal⟩ := hex
  have h0 : ∀ c < 10, c ≠ 4 → rho432F (yGen 4 3 2 c) 0 = 0 := by
    intro c hc hc4
    have := allLt_spec hfix0 hc
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h4 | h0c
    · exact absurd h4 hc4
    · apply Fin.ext
      rw [← (S.letters_rep hc).2 0]
      exact h0c
  have hlab : ∀ i < 8, y333Labs[i]!.1 < fins.size ∧
      recOK st fins[y333Labs[i]!.1]!.1 y333Labs[i]!.2
        (allSlots fins[y333Labs[i]!.1]!.2) = true := by
    intro i hi
    have := allLt_spec hrecs (show i < y333Labs.size from hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  have hsub : ∀ (K : Subgroup (YGroup 4 3 2)) (ω : Pt432),
      MulAction.orbit K ω ⊆ MulAction.orbit (YGroup 4 3 2) ω := by
    rintro K ω _ ⟨⟨k, -⟩, rfl⟩
    exact ⟨k, rfl⟩
  have horbE : 31671 ≤ (MulAction.orbit (YGroup 4 3 2) pt0).ncard := by
    have hr := (hlab 0 (by norm_num)).2
    obtain ⟨hβ, hsize, -⟩ := recOK_spec S hr
    have h1 : 31671 ≤ (slotRec st 0 (allSlots fins[0]!.2)).1.size := by
      rw [← hn]
      exact hn0
    calc 31671 ≤ _ := h1
      _ ≤ _ := hsize
      _ ≤ _ := Set.ncard_le_ncard (hsub _ _) (Set.toFinite _)
  have hcardPt : Nat.card Pt432 = 31671 := card_pt432
  have horb_univ : MulAction.orbit (YGroup 4 3 2) pt0 = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, hcardPt]; exact horbE) (Set.toFinite _)
  have hstab := stabilizer_zero_eq h0 horbE (index_J432_le hJ)
  have hJP : ∀ e : YGroup 4 3 2, e • pt0 = pt0 → (setup S.good).ψ e ∈ P333 := by
    intro e he
    have he' : e ∈ J432 := by
      rw [← hstab]
      exact he
    exact map_J432_le_P333 ⟨e, he', rfl⟩
  let lab : ℕ → ℕ × Pt432 := fun i => (y333Labs[i]!.1, ptOf y333Labs[i]!.2)
  let x : ℕ → B433 := fun l => xN fins[l]!.1
  have hlabpt : ∀ i < 8, ∃ hβ : y333Labs[i]!.2 < 31671,
      (lab i).2 = toPt ⟨y333Labs[i]!.2, hβ⟩ ∧
      (slotRec st y333Labs[i]!.2 (allSlots fins[y333Labs[i]!.1]!.2)).1.size ≤
        (MulAction.orbit (B.stabSub (setup S.good) (x (lab i).1)) (lab i).2).ncard ∧
      ∀ w, recMem st y333Labs[i]!.2 (allSlots fins[y333Labs[i]!.1]!.2) w = true →
        ∃ hw : w < 31671, toPt ⟨w, hw⟩ ∈
          MulAction.orbit (B.stabSub (setup S.good) (x (lab i).1)) (lab i).2 := by
    intro i hi
    obtain ⟨hβ, hsize, hmem⟩ := recOK_spec S (hlab i hi).2
    have he : (lab i).2 = toPt ⟨y333Labs[i]!.2, hβ⟩ := ptOf_eq hβ
    refine ⟨hβ, he, ?_, ?_⟩
    · rw [he]
      exact hsize
    · rw [he]
      exact hmem
  have hX := x0_orbit (fun l hl => S.letters_rep hl) S.letters_size hR0 hX0
  have hmove : ∀ i, 0 < i → i < 8 → ∃ i' < i, ∃ (r : Pts x0B) (er : YGroup 4 3 2) (ω'' : Pt432),
      (setup S.good).RCoset (x (lab i').1 * (setup S.good).T r)
        (x (lab i).1 * (setup S.good).ψ er) ∧
      ω'' ∈ MulAction.orbit (B.stabSub (setup S.good) (x (lab i').1)) (lab i').2 ∧
      (∃ g : YGroup 4 3 2, g • pt0 = ω'' ∧ g • (setup S.good).o = r) ∧ (lab i).2 = er • ω'' := by
    intro i hi0 hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hsz : y333Moves.size = 7 := rfl
    have hm := allLt_spec hmoves (show m < y333Moves.size by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hpar, hmatch⟩ := hm
    set i' := y333Moves[m]!.1
    set v := y333Moves[m]!.2.1
    set w := y333Moves[m]!.2.2
    rcases hget : B.RSt.get st.vs v with _ | f
    · rw [hget] at hmatch
      cases hmatch
    rw [hget] at hmatch
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at hmatch
    obtain ⟨⟨⟨⟨⟨hfi, hfk⟩, hfp⟩, hfmem⟩, ⟨k, hk, hrow⟩⟩, hfa⟩ := hmatch
    obtain ⟨-, e, hrep, hrc⟩ := f.2
    obtain ⟨-, -, -, hmem'⟩ := hlabpt i' (by omega)
    obtain ⟨hw, hwo⟩ := hmem' w hfmem
    refine ⟨i', hpar, S.pt f.1.p, e, toPt ⟨w, hw⟩, ?_, hwo, ?_, ?_⟩
    · show (setup S.good).RCoset (xN fins[y333Labs[i']!.1]!.1 * (setup S.good).T (S.pt f.1.p))
        (xN fins[y333Labs[m + 1]!.1]!.1 * (setup S.good).ψ e)
      rw [← hfi, ← hfk]
      exact hrc
    · refine exists_smul_of_mem S.good hX (S.pt f.1.p) ?_
      have hpN : f.1.p < (omegaB433 (lettersB ())).N := hfp
      unfold Checked.pt
      rw [dite_eq_left hpN]
      exact BigOmega.mem_rowFinset.2 ⟨k, hk, hrow⟩
    · obtain ⟨hβ, -, -, -⟩ := hlabpt (m + 1) hi
      have h1 := hrep.2 ⟨w, hw⟩
      have h2 : ((rho432F e ⟨w, hw⟩ : Fin 31671) : ℕ) = y333Labs[m + 1]!.2 := by
        rw [← h1]
        exact hfa
      show ptOf y333Labs[m + 1]!.2 = e • toPt ⟨w, hw⟩
      rw [ptOf_eq hβ, smul_toPt, toPt_inj]
      exact Fin.ext h2.symm
  have hreach := SymGen.Setup.fib_subset_porb_of_moves hJP tB_mem_P333 x lab 8
    (by
      show xN fins[y333Labs[0]!.1]!.1 ∈ (setup S.good).H
      have : y333Labs[0]!.1 = 0 := rfl
      rw [this, hroot]
      exact hx0)
    (by
      have h00 : y333Labs[0]!.2 = 0 := rfl
      show ptOf y333Labs[0]!.2 = pt0
      rw [h00]
      exact ptOf_eq (by norm_num)) hmove
  let labels : List (ℕ × Pt432) := (List.range 8).map lab
  let sv : ℕ → ℕ := fun l => 4089470473293004800 / E.chainBound st fins[l]!.2
  have hsum := SymGen.Setup.sum_le_ncard_porb (S := setup S.good) (P := P333) (ω₀ := pt0) x labels
    (by decide)
    (by
      intro u hu u' hu' a b hab
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
      obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hu'
      exact hdisj _ (hlab i (List.mem_range.1 hi)).1 _ (hlab i' (List.mem_range.1 hi')).1 a b hab)
    (by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
      exact hreach i (List.mem_range.1 hi))
    sv
    (by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
      exact (hindex _ (hlab i (List.mem_range.1 hi)).1).ge)
    (by
      intro u _
      rw [horb_univ]
      trivial)
  have hlow : 37543283785728 ≤ (labels.map fun lab => sv lab.1 *
      (MulAction.orbit (B.stabSub (setup S.good) (x lab.1)) lab.2).ncard).sum := by
    refine htotal.trans ?_
    rw [foldl_add_eq_sum, List.map_map]
    refine List.sum_le_sum fun i hi => ?_
    obtain ⟨-, -, hsize, -⟩ := hlabpt i (List.mem_range.1 hi)
    exact Nat.mul_le_mul_left _ hsize
  have hporb : 1185415168 ≤ ((setup S.good).porb P333).ncard := by
    have h1 : (MulAction.orbit (YGroup 4 3 2) pt0).ncard = 31671 := by
      rw [horb_univ, Set.ncard_univ, hcardPt]
    rw [h1] at hsum
    omega
  rw [SymGen.Setup.ncard_porb] at hporb
  have hHP : psi.range = (setup S.good).H := rfl
  have hJmap : J432.map psi ≤ psi.range ⊓ P333 := le_inf (Subgroup.map_le_range _ _)
    map_J432_le_P333
  have hcardJ : 129123503308800 ≤ Nat.card (J432.map psi) := by
    have hrel := relIndex_map_range_le psi J432
    have hJidx := index_J432_le hJ
    have hmulrel := Subgroup.relIndex_mul_card (H := J432.map psi) (K := psi.range)
    rw [inf_of_le_left (Subgroup.map_le_range psi J432)] at hmulrel
    have hpsi : 4089470473293004800 ≤ Nat.card psi.range := by
      have hcard := Subgroup.card_mul_index psi.range
      have hidx := (index_psi_le_of_finalOK S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK
        S.actAllSpec S.ptSurj 1015970529280000 (certB433 ()).prog fins hfin).2
      by_contra hlt
      rw [not_le] at hlt
      have : Nat.card B433 < 4154781481226426191177580544000000 := by
        rw [← hcard]
        calc Nat.card psi.range * psi.range.index ≤ Nat.card psi.range * 1015970529280000 :=
            Nat.mul_le_mul_left _ hidx
          _ < 4089470473293004800 * 1015970529280000 :=
            Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
          _ = _ := by norm_num
      omega
    have h2 : (J432.map psi).relIndex psi.range * Nat.card (J432.map psi) ≤
        31671 * Nat.card (J432.map psi) := Nat.mul_le_mul_right _ (hrel.trans hJidx)
    rw [hmulrel] at h2
    omega
  have hle : Nat.card (J432.map psi) ≤ Nat.card ((setup S.good).H.subgroupOf P333) := by
    rw [← hHP]
    have hJP' : J432.map psi ≤ P333 := map_J432_le_P333
    calc Nat.card (J432.map psi) = Nat.card ((J432.map psi).subgroupOf P333) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJP').toEquiv).symm
      _ ≤ Nat.card (psi.range.subgroupOf P333) :=
          Subgroup.card_le_of_le (Subgroup.subgroupOf_mono P333 (Subgroup.map_le_range _ _))
  have hPcard := Subgroup.card_mul_index ((setup S.good).H.subgroupOf P333)
  calc 153064959367549707878400 = 129123503308800 * 1185415168 := by norm_num
    _ ≤ Nat.card ((setup S.good).H.subgroupOf P333) * ((setup S.good).H.subgroupOf P333).index :=
        Nat.mul_le_mul (hcardJ.trans hle) hporb
    _ = Nat.card P333 := hPcard

end CFSG.YGroups.DCE.B433
