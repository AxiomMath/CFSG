module

public import CFSG.YGroups.DCE.OmegaSpec
public import CFSG.YGroups.SymmetricGenerators
public import CFSG.YGroups.Chain233
public import Certificates.Data.CFSGNative.YGroups.DCE.Y333Data
public import CFSG.YGroups.CosetAction233
public import CFSG.YGroups.Model233FBase

public section

namespace CFSG.YGroups.DCE.Y333

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Pointwise
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem size_foldl_setIfInBounds (t : Array ℕ) (l : List ℕ) (r : Array ℕ) :
    (List.foldl (fun b a => b.setIfInBounds t[a]! a) r l).size = r.size := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih, Array.size_setIfInBounds]

theorem size_invCand (n : ℕ) (t : Array ℕ) : (invCand n t).size = n := by
  unfold invCand
  simp only [Array.set!_eq_setIfInBounds, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure, size_foldl_setIfInBounds,
    Array.size_replicate]

theorem size_idA (n : ℕ) : (idA n).size = n := by
  simp only [idA, Array.size_ofFn]

theorem size_pcomp (t u : Array ℕ) : (pcomp t u).size = u.size := by
  simp only [pcomp, Array.size_map]

theorem pcomp_getElem {t u : Array ℕ} {x : ℕ} (hx : x < u.size) :
    (pcomp t u)[x]! = t[u[x]!]! := by
  simp only [pcomp, Array.size_map, hx, getElem!_pos, Array.getElem_map]

theorem rep_pcomp {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (hs : u.size = n) : Rep n (pcomp t u) (g * h) := fun x => by
  rw [pcomp_getElem (by rw [hs]; exact x.2), hu x, ht (h x), Equiv.Perm.mul_apply]

theorem rep_congr {n : ℕ} {t : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g) (e : g = h) :
    Rep n t h := e ▸ ht

@[expose] noncomputable def psi233 : YGroup 2 3 3 →* YGroup 3 3 3 :=
  yHom (shiftAt 2) rels_y233_y333

theorem psi233_yGen {l : ℕ} (hl : l < 9) :
    psi233 (yGen 2 3 3 l) = yGen 3 3 3 (shiftAt 2 l) :=
  yHom_yGen (shiftAt 2) rels_y233_y333 (by exact hl)

@[expose] noncomputable def t333 : YGroup 3 3 3 := yGen 3 3 3 3

@[expose] noncomputable def c233 : YGroup 2 3 3 := yGen 2 3 3 2

theorem pairWord_mem {p q r s t : ℕ} (hst : s < t) (ht : t < ngen p q r) :
    pairWord p q r s t ∈ yRels p q r := by
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter]
  exact Or.inl (Or.inr ⟨s, by omega, t, ⟨ht, by simpa using hst⟩, rfl⟩)

theorem yGen_pair_two {s t : ℕ} (hst : s < t) (ht : t < ngen 3 3 3) (h : pairExp 3 3 3 s t = 2) :
    yGen 3 3 3 s * (yGen 3 3 3 t * (yGen 3 3 3 s * yGen 3 3 3 t)) = 1 := by
  have h1 := evalWord_yGen_of_mem (pairWord_mem hst ht)
  simp only [pairWord, h, List.reduceReplicate, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, evalWord_cons, evalWord_nil,
    mul_one] at h1
  exact h1

theorem yGen_pair_three {s t : ℕ} (hst : s < t) (ht : t < ngen 3 3 3) (h : pairExp 3 3 3 s t = 3) :
    yGen 3 3 3 s * (yGen 3 3 3 t * (yGen 3 3 3 s * (yGen 3 3 3 t *
      (yGen 3 3 3 s * yGen 3 3 3 t)))) = 1 := by
  have h1 := evalWord_yGen_of_mem (pairWord_mem hst ht)
  simp only [pairWord, h, List.reduceReplicate, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, evalWord_cons, evalWord_nil,
    mul_one] at h1
  exact h1

theorem comm_of_pair_two {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * (y * (x * y)) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y = (x * y)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    calc x * y * (x * y) = x * (y * (x * y)) := by group
      _ = 1 := h
  calc x * y = (x * y)⁻¹ := h1
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hx', hy']

theorem cube_swap {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * (y * (x * (y * (x * y))))= 1) : (y * x) ^ 3 = 1 := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : (x * y) ^ 3 = 1 := by
    calc (x * y) ^ 3 = (x * y) * ((x * y) * (x * y)) := pow_three _
      _ = x * (y * (x * (y * (x * y)))) := by simp only [mul_assoc]
      _ = 1 := h
  have h2 : y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hx', hy']
  rw [h2, inv_pow, h1, inv_one]

theorem yGen_comm_t333 {m : ℕ} (hm : m < 10) (h2 : m ≠ 2) (h3 : m ≠ 3) :
    yGen 3 3 3 m * t333 = t333 * yGen 3 3 3 m := by
  rcases Nat.lt_or_gt_of_ne h3 with h | h
  · have hp : pairExp 3 3 3 m 3 = 2 := by
      interval_cases m <;> first | decide | omega
    exact comm_of_pair_two (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _)
      (yGen_pair_two h (by decide) hp)
  · have hp : pairExp 3 3 3 3 m = 2 := by
      interval_cases m <;> decide
    exact (comm_of_pair_two (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _)
      (yGen_pair_two h hm hp)).symm

theorem psi233_commute_t333 {g : YGroup 2 3 3} (hg : g ∈ Ctil) :
    psi233 g * t333 = t333 * psi233 g := by
  have key : Commute (psi233 g) t333 := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, ⟨hl, hl2⟩, rfl⟩ := hx
      rw [psi233_yGen hl]
      refine yGen_comm_t333 ?_ ?_ ?_ <;> unfold shiftAt <;> split_ifs <;> omega
    | one => simp only [map_one, Commute.one_left]
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  exact key

theorem psi233_c233 : psi233 c233 = yGen 3 3 3 2 := by
  rw [c233, psi233_yGen (by norm_num)]
  rfl

theorem psi233_c233_mul_self : psi233 c233 * psi233 c233 = 1 := by
  rw [psi233_c233]
  exact yGen_mul_self _ _ _ _

theorem t333_mul_self : t333 * t333 = 1 := yGen_mul_self _ _ _ _

theorem t333_psi233_c233_cube : (t333 * psi233 c233) ^ 3 = 1 := by
  rw [psi233_c233]
  have h := yGen_pair_three (s := 2) (t := 3) (by norm_num)
    (by decide) (by decide)
  exact cube_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) h

theorem c233_mul_self : c233 * c233 = 1 := yGen_mul_self _ _ _ _

noncomputable instance finsetAction233 :
    MulAction (YGroup 2 3 3) (Finset (Fin 3510)) :=
  MulAction.compHom _ rho233F

theorem smul_finset233
    (e : YGroup 2 3 3) (s : Finset (Fin 3510)) :
    e • s = rho233F e • s := rfl

structure Good (D : XData) (X0 : Array ℕ) : Prop where
  xt : xtOK D letters233 X0 fix233 = true
  n_eq : D.n = 3510
  N_eq : D.N = 694980
  sizes : lettersSizeOK = true

theorem letters233_eq : letters233 = CFSG.YGroups.y233FArrays := rfl

theorem letters233_size {D : XData} {X0 : Array ℕ} (hG : Good D X0) :
    letters233.size = 9 ∧ ∀ l < 9, letters233[l]!.size = 3510 := by
  have h := hG.sizes
  simp only [lettersSizeOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun l hl => ?_⟩
  have := allLt_iff.1 h.2 l hl
  simpa using this

@[expose] noncomputable def gperm
    (l : ℕ) : Equiv.Perm (Fin 3510) := rho233F (yGen 2 3 3 l)

theorem gperm_spec {D : XData} {X0 : Array ℕ} (hG : Good D X0) :
    ∀ l < letters233.size, gperm l ∈ rho233F.range ∧ Rep 3510 letters233[l]! (gperm l) := by
  intro l hl
  have hl9 : l < 9 := by have := (letters233_size hG).1; omega
  exact ⟨⟨yGen 2 3 3 l, rfl⟩, rho233F_rep hl9⟩

theorem orbit_eq
    (s : Finset (Fin 3510)) :
    MulAction.orbit (YGroup 2 3 3) s = MulAction.orbit rho233F.range s := by
  ext t
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨⟨rho233F e, e, rfl⟩, rfl⟩
  · rintro ⟨⟨γ, e, rfl⟩, rfl⟩
    exact ⟨e, rfl⟩

theorem rowFinset_zero {n : ℕ} {D : XData} {gens : Array (Array ℕ)} {X0 : Array ℕ} {fix : List ℕ}
    (h : xtOK D gens X0 fix = true) : rowFinset n D 0 = listFinset n X0 := by
  have F := xtFacts h
  ext x
  rw [mem_rowFinset, mem_listFinset]
  simp only [Nat.mul_zero, Nat.zero_add]
  constructor
  · rintro ⟨k, hk, hkx⟩
    exact ⟨k, F.m_eq ▸ hk, by rw [← F.row0 k hk]; exact hkx⟩
  · rintro ⟨k, hk, hkx⟩
    exact ⟨k, F.m_eq ▸ hk, by rw [F.row0 k (F.m_eq ▸ hk)]; exact hkx⟩

section Good

variable {D : XData} {X0 : Array ℕ}

theorem ctil_le_stabilizer_X0
    (hG : Good D X0) :
    Ctil ≤ MulAction.stabilizer (YGroup 2 3 3) (listFinset 3510 X0) := by
  rw [Ctil, Subgroup.closure_le]
  rintro _ ⟨l, ⟨hl, hl2⟩, rfl⟩
  have hlf : l ∈ fix233 := by
    simp only [fix233, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have := fix_smul_listFinset rho233F.range gperm (gperm_spec hG) hG.xt l hlf
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact this

theorem ncard_orbit_le
    (hG : Good D X0) :
    (MulAction.orbit rho233F.range (listFinset 3510 X0)).ncard ≤ D.N := by
  rw [← orbit_eq, ← MulAction.index_stabilizer]
  have h1 := Subgroup.index_dvd_of_le (ctil_le_stabilizer_X0 hG)
  rw [index_ctil] at h1
  rw [hG.N_eq]
  exact Nat.le_of_dvd (by norm_num) h1

theorem stabilizer_eq_ctil
    (hG : Good D X0) :
    MulAction.stabilizer (YGroup 2 3 3) (listFinset 3510 X0) = Ctil := by
  have hle := ctil_le_stabilizer_X0 hG
  have hge : D.N ≤ (MulAction.orbit rho233F.range (listFinset 3510 X0)).ncard :=
    card_orbit_ge rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq
  have hle' := ncard_orbit_le hG
  have hidx : (MulAction.stabilizer (YGroup 2 3 3) (listFinset 3510 X0)).index = 694980 := by
    rw [MulAction.index_stabilizer, orbit_eq]
    have := hG.N_eq
    omega
  have h := Subgroup.relIndex_mul_index hle
  rw [hidx, index_ctil] at h
  have h1 : Ctil.relIndex (MulAction.stabilizer (YGroup 2 3 3) (listFinset 3510 X0)) = 1 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (one_mul _).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle

end Good

abbrev Pts (X0 : Array ℕ) : Type :=
  ↥(MulAction.orbit (YGroup 2 3 3) (listFinset 3510 X0))

@[expose] def basePt
    (X0 : Array ℕ) : Pts X0 := ⟨listFinset 3510 X0, MulAction.mem_orbit_self _⟩

@[expose] noncomputable def transv
    (X0 : Array ℕ) (p : Pts X0) : YGroup 2 3 3 :=
  Classical.choose (MulAction.mem_orbit_iff.1 p.2)

theorem transv_smul
    (X0 : Array ℕ) (p : Pts X0) : transv X0 p • basePt X0 = p :=
  Subtype.ext (Classical.choose_spec (MulAction.mem_orbit_iff.1 p.2))

variable {D : XData} {X0 : Array ℕ}

@[expose] noncomputable def setup233
    (hG : Good D X0) :
    SymGen.Setup (YGroup 3 3 3) (YGroup 2 3 3) (Pts X0) where
  t := t333
  ψ := psi233
  o := basePt X0
  w := transv X0
  t_mul_t := t333_mul_self
  w_smul := transv_smul X0
  stab_comm := fun c hc => by
    have h1 : c ∈ MulAction.stabilizer (YGroup 2 3 3) (listFinset 3510 X0) := by
      rw [MulAction.mem_stabilizer_iff]
      exact congrArg Subtype.val hc
    rw [stabilizer_eq_ctil hG] at h1
    exact psi233_commute_t333 h1

@[expose] noncomputable def pt
    (hG : Good D X0) (p : ℕ) : Pts X0 :=
  if hp : p < D.N then
    ⟨rowFinset 3510 D p, by
      rw [orbit_eq]
      exact rowFinset_mem_orbit rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq p hp⟩
  else basePt X0

theorem pt_coe
    (hG : Good D X0) {p : ℕ} (hp : p < D.N) : (pt hG p).1 = rowFinset 3510 D p := by
  unfold pt
  rw [dite_eq_left hp]

theorem pt_zero
    (hG : Good D X0) : pt hG 0 = basePt X0 := by
  have h0 : 0 < D.N := by rw [hG.N_eq]; norm_num
  apply Subtype.ext
  rw [pt_coe hG h0, rowFinset_zero hG.xt]
  rfl

theorem smul_pt
    (hG : Good D X0) {a : Array ℕ} {e : YGroup 2 3 3} (ha : Rep 3510 a (rho233F e))
    {p : ℕ} (hp : p < D.N) : act D a p < D.N ∧ e • pt hG p = pt hG (act D a p) := by
  obtain ⟨h1, h2⟩ := act_spec rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq
    (ncard_orbit_le hG) (σ := a) (e := ⟨rho233F e, e, rfl⟩) ha hp
  refine ⟨h1, Subtype.ext ?_⟩
  rw [pt_coe hG h1]
  show rho233F e • (pt hG p).1 = _
  rw [pt_coe hG hp]
  exact h2.symm

theorem pt_injOn
    (hG : Good D X0) {p q : ℕ} (hp : p < D.N) (hq : q < D.N)
    (h : pt hG p = pt hG q) : p = q := by
  have h1 := congrArg Subtype.val h
  rw [pt_coe hG hp, pt_coe hG hq] at h1
  exact rowFinset_injOn rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq p hp q hq h1

theorem pt_surj
    (hG : Good D X0) (p : Pts X0) : ∃ q < D.N, pt hG q = p := by
  have hT : (↑((Finset.range D.N).image (rowFinset 3510 D)) : Set (Finset (Fin 3510))) =
      MulAction.orbit rho233F.range (listFinset 3510 X0) :=
    Set.eq_of_subset_of_ncard_le
      (rows_subset_orbit rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq)
      (by
        rw [Set.ncard_coe_finset,
          rows_card rho233F.range gperm (gperm_spec hG) hG.xt hG.n_eq]
        exact ncard_orbit_le hG)
      (Set.toFinite _)
  have hp : p.1 ∈ MulAction.orbit rho233F.range (listFinset 3510 X0) := by
    rw [← orbit_eq]
    exact p.2
  rw [← hT] at hp
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
  have hqN := Finset.mem_range.1 hq
  exact ⟨q, hqN, Subtype.ext (by rw [pt_coe hG hqN]; exact hqp)⟩

@[expose] noncomputable def xNode
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) (j : ℕ) :
    YGroup 3 3 3 :=
  if _h : 0 < j ∧ j < nodes.size ∧ (nodes[j]!).1 < j then
    xNode hG nodes (nodes[j]!).1 * (setup233 hG).T (pt hG (nodes[j]!).2)
  else 1
termination_by j
decreasing_by exact _h.2.2

theorem xNode_zero
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) : xNode hG nodes 0 = 1 := by
  rw [xNode]
  simp only [lt_self_iff_false, not_lt_zero, and_false, and_self, ↓reduceDIte]

theorem nodes_get {nodes : Array (ℕ × ℕ)} {j i p : ℕ} (hn : nodes[j]? = some (i, p)) :
    j < nodes.size ∧ nodes[j]! = (i, p) := by
  have hjs : j < nodes.size := (Array.getElem?_eq_some_iff.1 hn).1
  refine ⟨hjs, ?_⟩
  rw [getElem!_pos nodes j hjs]
  exact Option.some.inj ((Array.getElem?_eq_getElem hjs).symm.trans hn)

theorem xNode_eq
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {j i p : ℕ} (hj : 0 < j)
    (hn : nodes[j]? = some (i, p)) (hi : i < j) :
    xNode hG nodes j = xNode hG nodes i * (setup233 hG).T (pt hG p) := by
  obtain ⟨hjs, hv⟩ := nodes_get hn
  have hc : 0 < j ∧ j < nodes.size ∧ (nodes[j]!).1 < j := ⟨hj, hjs, by rw [hv]; exact hi⟩
  rw [xNode, dite_eq_left hc, hv]

section Cores

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω] (S : SymGen.Setup G E Ω)

theorem core1 {xi xk : G} {p : Ω} {e : E} (h : S.RCoset (xi * S.T p) (xk * S.ψ e)) :
    S.RCoset (xk * S.T (e • p)) (xi * S.ψ e⁻¹) := by
  have h2 := h.symm.mul_right (S.T p * (S.ψ e)⁻¹)
  have e1 : xk * S.T (e • p) = xk * S.ψ e * (S.T p * (S.ψ e)⁻¹) := by
    rw [← S.conj_T e p]; group
  have e2 : xi * S.T p * (S.T p * (S.ψ e)⁻¹) = xi * S.ψ e⁻¹ := by
    calc xi * S.T p * (S.T p * (S.ψ e)⁻¹) = xi * (S.T p * S.T p) * (S.ψ e)⁻¹ := by group
      _ = xi * S.ψ e⁻¹ := by rw [S.T_mul_self, map_inv]; group
  rw [e1, ← e2]
  exact h2

theorem core2 {x y : G} {p q : Ω} {ea es : E} (hent : S.RCoset (x * S.T p) (y * S.ψ ea))
    (hs : x * S.ψ es * x⁻¹ ∈ S.H) (hsp : es • q = p) :
    S.RCoset (x * S.T q) (y * S.ψ (ea * es)) := by
  have hs' : x * S.ψ es⁻¹ * x⁻¹ ∈ S.H := by
    have := S.H.inv_mem hs
    rwa [show (x * S.ψ es * x⁻¹)⁻¹ = x * S.ψ es⁻¹ * x⁻¹ by rw [map_inv]; group] at this
  have hsp' : es⁻¹ • p = (1 : E) • q := by rw [one_smul, ← hsp, inv_smul_smul]
  have := S.act_spec hent hs' hsp'
  simpa using this

theorem core3 {xi xk : G} {p : Ω} {ea eb : E} (ha : S.RCoset (xi * S.T p) (xk * S.ψ ea))
    (hb : S.RCoset (xi * S.T p) (xk * S.ψ eb)) : xk * S.ψ (ea * eb⁻¹) * xk⁻¹ ∈ S.H := by
  have h := ha.symm.trans hb
  unfold SymGen.Setup.RCoset at h
  rwa [show xk * S.ψ ea * (xk * S.ψ eb)⁻¹ = xk * S.ψ (ea * eb⁻¹) * xk⁻¹ by
    rw [map_mul, map_inv]; group] at h

theorem core4_aux {p q : Ω} {n : E} (hnp : n • p = q) (rel : S.T p * S.T q = S.ψ n * S.T p)
    {xi xj xk : G} {ea eb : E} (h1 : S.RCoset (xi * S.T p) (xj * S.ψ ea))
    (h2 : S.RCoset (xj * S.T (ea • q)) (xk * S.ψ eb)) :
    S.RCoset (xi * S.T q) (xk * S.ψ (eb * ea * n)) := by
  have hTq : S.T q = S.T p * (S.ψ n * S.T p) := by
    rw [← rel, ← mul_assoc, S.T_mul_self, one_mul]
  have e1 : xi * S.T q = xi * S.T p * (S.ψ n * S.T p) := by rw [hTq]; group
  have e2 : xj * S.ψ ea * (S.ψ n * S.T p) = xj * S.T (ea • q) * S.ψ (ea * n) := by
    have := S.mul_T (ea * n) p
    rw [mul_smul, hnp, map_mul] at this
    calc xj * S.ψ ea * (S.ψ n * S.T p) = xj * (S.ψ ea * S.ψ n * S.T p) := by group
      _ = xj * (S.T (ea • q) * (S.ψ ea * S.ψ n)) := by rw [this]
      _ = _ := by rw [map_mul]; group
  have e3 : xk * S.ψ eb * S.ψ (ea * n) = xk * S.ψ (eb * ea * n) := by
    simp only [map_mul]; group
  have step1 := h1.mul_right (S.ψ n * S.T p)
  have step2 := h2.mul_right (S.ψ (ea * n))
  rw [← e1, e2] at step1
  rw [e3] at step2
  exact step1.trans step2

theorem core5_aux {p q : Ω} {n : E} (hnp : n • p = q) (hnn : n * n = 1)
    (rel : S.T p * S.T q = S.ψ n * S.T p) {xi xj xk : G} {ea eb : E}
    (h1 : S.RCoset (xi * S.T p) (xj * S.ψ ea)) (h3 : S.RCoset (xi * S.T q) (xk * S.ψ eb)) :
    S.RCoset (xj * S.T (ea • q)) (xk * S.ψ (eb * n * ea⁻¹)) := by
  have hTq : S.T q = S.T p * (S.ψ n * S.T p) := by
    rw [← rel, ← mul_assoc, S.T_mul_self, one_mul]
  have e1 : xi * S.T q = xi * S.T p * (S.ψ n * S.T p) := by rw [hTq]; group
  have step1 := h1.symm.mul_right (S.ψ n * S.T p)
  rw [← e1] at step1
  have step3 := (step1.trans h3).mul_right (S.ψ (ea * n))⁻¹
  have e3 : xj * S.ψ ea * (S.ψ n * S.T p) * (S.ψ (ea * n))⁻¹ = xj * S.T (ea • q) := by
    have := S.conj_T (ea * n) p
    rw [mul_smul, hnp] at this
    calc xj * S.ψ ea * (S.ψ n * S.T p) * (S.ψ (ea * n))⁻¹
        = xj * (S.ψ (ea * n) * S.T p * (S.ψ (ea * n))⁻¹) := by rw [map_mul]; group
      _ = xj * S.T (ea • q) := by rw [this]
  have e4 : xk * S.ψ eb * (S.ψ (ea * n))⁻¹ = xk * S.ψ (eb * n * ea⁻¹) := by
    have hinv : (ea * n)⁻¹ = n * ea⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hnn]
    rw [← map_inv, hinv]
    simp only [map_mul]
    group
  rw [e3, e4] at step3
  exact step3

theorem core4 {c : E} (hc2 : S.ψ c * S.ψ c = 1) (hc3 : (S.t * S.ψ c) ^ 3 = 1) (g : E)
    {xi xj xk : G} {ea eb : E} (h1 : S.RCoset (xi * S.T (g • S.o)) (xj * S.ψ ea))
    (h2 : S.RCoset (xj * S.T (ea • (g * c) • S.o)) (xk * S.ψ eb)) :
    S.RCoset (xi * S.T ((g * c) • S.o)) (xk * S.ψ (eb * ea * (g * c * g⁻¹))) :=
  core4_aux S (by rw [← mul_smul]; congr 1; group) (S.T_mul_T_rel hc2 hc3 g) h1 h2

theorem core5 {c : E} (hcc : c * c = 1) (hc2 : S.ψ c * S.ψ c = 1) (hc3 : (S.t * S.ψ c) ^ 3 = 1)
    (g : E) {xi xj xk : G} {ea eb : E} (h1 : S.RCoset (xi * S.T (g • S.o)) (xj * S.ψ ea))
    (h3 : S.RCoset (xi * S.T ((g * c) • S.o)) (xk * S.ψ eb)) :
    S.RCoset (xj * S.T (ea • (g * c) • S.o)) (xk * S.ψ (eb * (g * c * g⁻¹) * ea⁻¹)) :=
  core5_aux S (by rw [← mul_smul]; congr 1; group)
    (by calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
          _ = 1 := by rw [hcc]; group)
    (S.T_mul_T_rel hc2 hc3 g) h1 h3

theorem stab_mul {x : G} {ea eb : E} (ha : x * S.ψ ea * x⁻¹ ∈ S.H)
    (hb : x * S.ψ eb * x⁻¹ ∈ S.H) : x * S.ψ (ea * eb) * x⁻¹ ∈ S.H := by
  have := S.H.mul_mem ha hb
  rwa [show x * S.ψ ea * x⁻¹ * (x * S.ψ eb * x⁻¹) = x * S.ψ (ea * eb) * x⁻¹ by
    rw [map_mul]; group] at this

theorem stab_inv {x : G} {e : E} (h : x * S.ψ e * x⁻¹ ∈ S.H) : x * S.ψ e⁻¹ * x⁻¹ ∈ S.H := by
  have := S.H.inv_mem h
  rwa [show (x * S.ψ e * x⁻¹)⁻¹ = x * S.ψ e⁻¹ * x⁻¹ by rw [map_inv]; group] at this

end Cores

@[expose] def PE (a : Array ℕ) : Prop :=
  a.size = 3510 ∧ ∃ e : YGroup 2 3 3, Rep 3510 a (rho233F e)

@[expose] def W
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) (j : ℕ) (a : Array ℕ) : Prop :=
  a.size = 3510 ∧ ∃ e : YGroup 2 3 3, Rep 3510 a (rho233F e) ∧
    xNode hG nodes j * (setup233 hG).ψ e * (xNode hG nodes j)⁻¹ ∈ (setup233 hG).H

@[expose] def V
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) (i p k : ℕ) (a : Array ℕ) : Prop :=
  p < D.N ∧ a.size = 3510 ∧ ∃ e : YGroup 2 3 3, Rep 3510 a (rho233F e) ∧
    (setup233 hG).RCoset (xNode hG nodes i * (setup233 hG).T (pt hG p))
      (xNode hG nodes k * (setup233 hG).ψ e)

theorem pe_of_letter
    (hG : Good D X0) {l : ℕ} (hl : l < letters233.size) : PE letters233[l]! := by
  have hl9 : l < 9 := by have := (letters233_size hG).1; omega
  exact ⟨(letters233_size hG).2 l hl9, yGen 2 3 3 l, rho233F_rep hl9⟩

theorem pe_mul
    {a b : Array ℕ} (ha : PE a) (hb : PE b) : PE (pcomp a b) := by
  obtain ⟨ha1, ea, hea⟩ := ha
  obtain ⟨hb1, eb, heb⟩ := hb
  refine ⟨by rw [size_pcomp]; exact hb1, ea * eb, ?_⟩
  rw [map_mul]
  exact rep_pcomp hea heb hb1

theorem pe_inv
    {a : Array ℕ} (ha : PE a) (h : isInvA 3510 a (invCand 3510 a) = true) :
    PE (invCand 3510 a) := by
  obtain ⟨-, ea, hea⟩ := ha
  refine ⟨size_invCand _ _, ea⁻¹, ?_⟩
  rw [map_inv]
  exact rep_inv_of_isInvA hea h

theorem w_pe
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {j : ℕ} {a : Array ℕ}
    (h : W hG nodes j a) : PE a := by
  obtain ⟨h1, e, he, -⟩ := h
  exact ⟨h1, e, he⟩

theorem w_root
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {a : Array ℕ} (h : PE a) :
    W hG nodes 0 a := by
  obtain ⟨h1, e, he⟩ := h
  refine ⟨h1, e, he, ?_⟩
  rw [xNode_zero, one_mul, inv_one, mul_one]
  exact ⟨e, rfl⟩

theorem w_mul
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {j : ℕ} {a b : Array ℕ}
    (ha : W hG nodes j a) (hb : W hG nodes j b) : W hG nodes j (pcomp a b) := by
  obtain ⟨ha1, ea, hea, hxa⟩ := ha
  obtain ⟨hb1, eb, heb, hxb⟩ := hb
  refine ⟨by rw [size_pcomp]; exact hb1, ea * eb, ?_, stab_mul (setup233 hG) hxa hxb⟩
  rw [map_mul]
  exact rep_pcomp hea heb hb1

theorem w_inv
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {j : ℕ} {a : Array ℕ}
    (ha : W hG nodes j a) (h : isInvA 3510 a (invCand 3510 a) = true) :
    W hG nodes j (invCand 3510 a) := by
  obtain ⟨-, ea, hea, hxa⟩ := ha
  refine ⟨size_invCand _ _, ea⁻¹, ?_, stab_inv (setup233 hG) hxa⟩
  rw [map_inv]
  exact rep_inv_of_isInvA hea h

theorem w_id
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) (j : ℕ) : W hG nodes j (idA 3510) := by
  refine ⟨size_idA _, 1, rep_congr rep_idA (map_one _).symm, ?_⟩
  rw [map_one, mul_one, mul_inv_cancel]
  exact (setup233 hG).H.one_mem

theorem rule_r0
    (hG : Good D X0) (nodes : Array (ℕ × ℕ))
    (hnodes : ∀ j, 0 < j → j < nodes.size → (nodes[j]!).1 < j) {j i p : ℕ} (hj : 0 < j)
    (hn : nodes[j]? = some (i, p)) (hp : p < D.N) : V hG nodes i p j (idA 3510) := by
  obtain ⟨hjs, hv⟩ := nodes_get hn
  have hij : i < j := by
    have := hnodes j hj hjs
    rwa [hv] at this
  refine ⟨hp, size_idA _, 1, rep_congr rep_idA (map_one _).symm, ?_⟩
  rw [map_one, mul_one, xNode_eq hG nodes hj hn hij]
  exact SymGen.Setup.RCoset.refl _ _

theorem rule_r1
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {i p k : ℕ} {a : Array ℕ}
    (h : V hG nodes i p k a) (hinv : isInvA 3510 a (invCand 3510 a) = true) :
    V hG nodes k (act D a p) i (invCand 3510 a) := by
  obtain ⟨hp, -, e, he, hc⟩ := h
  obtain ⟨hlt, hsm⟩ := smul_pt hG he hp
  refine ⟨hlt, size_invCand _ _, e⁻¹, ?_, ?_⟩
  · rw [map_inv]; exact rep_inv_of_isInvA he hinv
  · rw [← hsm]; exact core1 (setup233 hG) hc

theorem rule_r2
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {j p k q : ℕ} {a s : Array ℕ}
    (h : V hG nodes j p k a) (hs : W hG nodes j s) (hq : q < D.N) (hact : act D s q = p) :
    V hG nodes j q k (pcomp a s) := by
  obtain ⟨-, -, ea, hea, hc⟩ := h
  obtain ⟨hs1, es, hes, hxs⟩ := hs
  obtain ⟨-, hsm⟩ := smul_pt hG hes hq
  refine ⟨hq, by rw [size_pcomp]; exact hs1, ea * es, ?_, ?_⟩
  · rw [map_mul]; exact rep_pcomp hea hes hs1
  · rw [hact] at hsm
    exact core2 (setup233 hG) hc hxs hsm

theorem rule_r3
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {i p k : ℕ} {a b : Array ℕ}
    (ha : V hG nodes i p k a) (hb : V hG nodes i p k b)
    (hinv : isInvA 3510 b (invCand 3510 b) = true) :
    W hG nodes k (pcomp a (invCand 3510 b)) := by
  obtain ⟨-, -, ea, hea, hca⟩ := ha
  obtain ⟨-, -, eb, heb, hcb⟩ := hb
  refine ⟨by rw [size_pcomp]; exact size_invCand _ _, ea * eb⁻¹, ?_, core3 (setup233 hG) hca hcb⟩
  rw [map_mul, map_inv]
  exact rep_pcomp hea (rep_inv_of_isInvA heb hinv) (size_invCand _ _)

theorem rule45_data
    (hG : Good D X0) {g : Array ℕ} (hg : PE g)
    (hginv : isInvA 3510 g (invCand 3510 g) = true) :
    ∃ eg : YGroup 2 3 3, Rep 3510 g (rho233F eg) ∧
      Rep 3510 (pcomp g letters233[2]!) (rho233F (eg * c233)) ∧
      act D g 0 < D.N ∧ eg • pt hG 0 = pt hG (act D g 0) ∧
      act D (pcomp g letters233[2]!) 0 < D.N ∧
      (eg * c233) • pt hG 0 = pt hG (act D (pcomp g letters233[2]!) 0) ∧
      Rep 3510 (pcomp (pcomp g letters233[2]!) (invCand 3510 g))
        (rho233F (eg * c233 * eg⁻¹)) := by
  obtain ⟨-, eg, heg⟩ := hg
  have h0 : 0 < D.N := by rw [hG.N_eq]; norm_num
  have hcRep : Rep 3510 letters233[2]! (rho233F c233) := rho233F_rep (c := 2) (by norm_num)
  have hcSize : letters233[2]!.size = 3510 := (letters233_size hG).2 2 (by norm_num)
  have hgc : Rep 3510 (pcomp g letters233[2]!) (rho233F (eg * c233)) := by
    rw [map_mul]; exact rep_pcomp heg hcRep hcSize
  obtain ⟨hlt0, hsm0⟩ := smul_pt hG heg h0
  obtain ⟨hltc, hsmc⟩ := smul_pt hG hgc h0
  refine ⟨eg, heg, hgc, hlt0, hsm0, hltc, hsmc, ?_⟩
  have hginvRep : Rep 3510 (invCand 3510 g) (rho233F eg)⁻¹ := rep_inv_of_isInvA heg hginv
  refine rep_congr (rep_pcomp hgc hginvRep (size_invCand _ _)) ?_
  simp only [map_mul, map_inv]

theorem rule_r4
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {g a b : Array ℕ} {i j k : ℕ}
    (hg : PE g) (hginv : isInvA 3510 g (invCand 3510 g) = true)
    (h1 : V hG nodes i (act D g 0) j a)
    (h2 : V hG nodes j (act D a (act D (pcomp g letters233[2]!) 0)) k b) :
    V hG nodes i (act D (pcomp g letters233[2]!) 0) k
      (pcomp (pcomp b a) (pcomp (pcomp g letters233[2]!) (invCand 3510 g))) := by
  obtain ⟨eg, heg, hgc, -, hsm0, hltc, hsmc, hconj⟩ := rule45_data hG hg hginv
  obtain ⟨-, ha1, ea, hea, hc1⟩ := h1
  obtain ⟨-, hb1, eb, heb, hc2⟩ := h2
  obtain ⟨-, hsma⟩ := smul_pt hG hea hltc
  refine ⟨hltc, ?_, eb * ea * (eg * c233 * eg⁻¹), ?_, ?_⟩
  · rw [size_pcomp, size_pcomp]; exact size_invCand _ _
  · refine rep_congr (rep_pcomp (rep_pcomp heb hea ha1) hconj
      (by rw [size_pcomp]; exact size_invCand _ _)) ?_
    simp only [map_mul]
  · rw [pt_zero] at hsm0 hsmc
    rw [← hsmc]
    rw [← hsm0] at hc1
    rw [← hsma, ← hsmc] at hc2
    exact core4 (setup233 hG) psi233_c233_mul_self t333_psi233_c233_cube eg hc1 hc2

theorem rule_r5
    (hG : Good D X0) (nodes : Array (ℕ × ℕ)) {g a b : Array ℕ} {i j k : ℕ}
    (hg : PE g) (hginv : isInvA 3510 g (invCand 3510 g) = true)
    (hainv : isInvA 3510 a (invCand 3510 a) = true)
    (h1 : V hG nodes i (act D g 0) j a) (h3 : V hG nodes i (act D (pcomp g letters233[2]!) 0) k b) :
    V hG nodes j (act D a (act D (pcomp g letters233[2]!) 0)) k
      (pcomp (pcomp b (pcomp (pcomp g letters233[2]!) (invCand 3510 g))) (invCand 3510 a)) := by
  obtain ⟨eg, heg, hgc, -, hsm0, hltc, hsmc, hconj⟩ := rule45_data hG hg hginv
  obtain ⟨-, ha1, ea, hea, hc1⟩ := h1
  obtain ⟨-, hb1, eb, heb, hc3⟩ := h3
  obtain ⟨hlta, hsma⟩ := smul_pt hG hea hltc
  refine ⟨hlta, ?_, eb * (eg * c233 * eg⁻¹) * ea⁻¹, ?_, ?_⟩
  · rw [size_pcomp]; exact size_invCand _ _
  · refine rep_congr (rep_pcomp (rep_pcomp heb hconj (by rw [size_pcomp]; exact size_invCand _ _))
      (rep_inv_of_isInvA hea hainv) (size_invCand _ _)) ?_
    simp only [map_mul, map_inv]
  · rw [pt_zero] at hsm0 hsmc
    rw [← hsma, ← hsmc]
    rw [← hsm0] at hc1
    rw [← hsmc] at hc3
    exact core5 (setup233 hG) c233_mul_self psi233_c233_mul_self t333_psi233_c233_cube eg hc1 hc3

theorem rules
    (hG : Good D X0) (nodes : Array (ℕ × ℕ))
    (hnodes : ∀ j, 0 < j → j < nodes.size → (nodes[j]!).1 < j) :
    Rules { n := 3510, letters := letters233, cl := 2, D := D, nodes := nodes, discover := false,
            one := idA 3510 } PE (W hG nodes) (V hG nodes) where
  letter := fun _ hl => pe_of_letter hG hl
  mul := fun _ _ ha hb => pe_mul ha hb
  inv := fun _ ha h => pe_inv ha h
  wpe := fun _ _ h => w_pe hG nodes h
  wroot := fun _ ha => w_root hG nodes ha
  wmul := fun _ _ _ ha hb => w_mul hG nodes ha hb
  winv := fun _ _ ha h => w_inv hG nodes ha h
  wid := fun j => by
    dsimp only
    exact w_id hG nodes j
  r0 := fun _ _ _ hj hnode hp => rule_r0 hG nodes hnodes hj (by simpa [Ctx.nodeOK] using hnode) hp
  r1 := fun _ _ _ _ h hinv => rule_r1 hG nodes h hinv
  r2 := fun _ _ _ _ _ _ h hs hq hact => rule_r2 hG nodes h hs hq hact
  r3 := fun _ _ _ _ _ ha hb hinv => rule_r3 hG nodes ha hb hinv
  r4 := fun _ _ _ _ _ _ hg hginv h1 h2 => rule_r4 hG nodes hg hginv h1 h2
  r5 := fun _ _ _ _ _ _ hg hginv hainv h1 h3 => rule_r5 hG nodes hg hginv hainv h1 h3

theorem rules_ctx233
    {X0 : Array ℕ} (hG : Good (xdata233 ()) X0) (nodes : Array (ℕ × ℕ))
    (hnodes : ∀ j, 0 < j → j < nodes.size → (nodes[j]!).1 < j) :
    Rules (ctx233 nodes false) PE (W hG nodes) (V hG nodes) :=
  rules hG nodes hnodes

end CFSG.YGroups.DCE.Y333
