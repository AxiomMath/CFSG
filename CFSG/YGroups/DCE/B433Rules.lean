module

public import CFSG.YGroups.DCE.Y333Rules
public import CFSG.YGroups.DCE.OutSpecB
public import CFSG.YGroups.Model432F
public import CFSG.YGroups.Y433.TwoCentral

public section

namespace CFSG.YGroups.DCE.B433

open Pointwise

theorem rels_y432_y433 : ∀ w ∈ yRels 4 3 2, w.map (shiftAt 9) ∈ yRels 4 3 3 := by decide

@[expose] noncomputable def psiU : YGroup 4 3 2 →* U433 := yHom (shiftAt 9) rels_y432_y433

theorem psiU_yGen {l : ℕ} (hl : l < 10) : psiU (yGen 4 3 2 l) = yGen 4 3 3 l := by
  rw [psiU, yHom_yGen _ _ (by exact hl)]
  simp only [shiftAt, show l ≤ 9 by omega, ↓reduceIte]

@[expose] noncomputable def qB : U433 →* B433 :=
  QuotientGroup.mk' (Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433))

theorem qB_surjective : Function.Surjective qB := QuotientGroup.mk'_surjective _

theorem qB_F433_213 : qB (F433 2 1 3) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure (Or.inl rfl))

theorem qB_F433_312 : qB (F433 3 1 2) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure (Or.inr rfl))

@[expose] noncomputable def psi : YGroup 4 3 2 →* B433 := qB.comp psiU

theorem psi_yGen {l : ℕ} (hl : l < 10) : psi (yGen 4 3 2 l) = qB (yGen 4 3 3 l) := by
  rw [psi, MonoidHom.comp_apply, psiU_yGen hl]

@[expose] noncomputable def tB : B433 := qB (yGen 4 3 3 10)

theorem tB_mul_self : tB * tB = 1 := by
  rw [tB, ← map_mul, yGen_mul_self, map_one]

theorem closure_psi_t : Subgroup.closure ((psi.range : Set B433) ∪ {tB}) = ⊤ := by
  rw [eq_top_iff]
  rintro b -
  obtain ⟨u, rfl⟩ := qB_surjective b
  have hu : u ∈ Subgroup.closure (yGen 4 3 3 '' Set.Iio (ngen 4 3 3)) := by
    rw [closure_yGen]
    exact Subgroup.mem_top u
  have hmap : qB u ∈ (Subgroup.closure (yGen 4 3 3 '' Set.Iio (ngen 4 3 3))).map qB := ⟨u, hu, rfl⟩
  rw [MonoidHom.map_closure, Set.image_image] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨c, hc, rfl⟩
  by_cases h10 : c = 10
  · subst h10
    exact Or.inr rfl
  · have hc10 : c < 10 := by
      have : c < ngen 4 3 3 := hc
      simp only [ngen] at this
      omega
    exact Or.inl ⟨yGen 4 3 2 c, psi_yGen hc10⟩

theorem yGen_commute_D3 {c : ℕ} (hc : c < 9) : Commute (yGen 4 3 3 c) (yGen 4 3 3 10) := by
  have h : ∀ c < 9, (c, 10) ∉ yEdges 4 3 3 ∧ (10, c) ∉ yEdges 4 3 3 := by decide
  exact Relabel.commute_yGen_of_not_edge (by simp only [ngen]; omega) (by decide) (by omega)
    (h c hc).1 (h c hc).2

theorem psi_commute_t
    {g : YGroup 4 3 2} (hg : g ∈ Ctil432) : psi g * tB = tB * psi g := by
  have key : Commute (psi g) tB := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, ⟨hl, hl9⟩, rfl⟩ := hx
      rw [psi_yGen hl]
      exact (yGen_commute_D3 (by omega)).map qB
    | one => simp only [map_one, Commute.one_left]
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  exact key

theorem tB_psi_c_cube : (tB * psi (yGen 4 3 2 9)) ^ 3 = 1 := by
  have h1 : (yGen 4 3 3 9 * yGen 4 3 3 10) ^ 3 = 1 := by
    have := Y443.yGen_pair_pow (p := 4) (q := 3) (r := 3) (s := 9) (t := 10) (by norm_num)
      (by decide)
    rwa [show pairExp 4 3 3 9 10 = 3 by decide] at this
  have h2 : (yGen 4 3 3 10 * yGen 4 3 3 9) ^ 3 = 1 :=
    Y443.pow_eq_one_of_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) h1
  rw [psi_yGen (by norm_num), tB, ← map_mul, ← map_pow, h2, map_one]

@[expose] noncomputable def gRel : YGroup 4 3 2 :=
  yGen 4 3 2 1 * yGen 4 3 2 2 * yGen 4 3 2 5 * yGen 4 3 2 0 * yGen 4 3 2 8 * yGen 4 3 2 9

theorem tB_psi_gRel_pow_nine : (tB * psi gRel) ^ 9 = 1 := by
  have hF : qB (F433 3 1 2) = (qB (yGen 4 3 3 0 * yGen 4 3 3 8 * yGen 4 3 3 9) * tB *
      (qB (yGen 4 3 3 1 * yGen 4 3 3 2 * yGen 4 3 3 5))) ^ 9 := by
    simp only [F433, tB, map_pow, map_mul, U433.A, U433.B, U433.C, U433.D, U433.armStart,
      mul_assoc]
  have h1 := Relabel.pow_eq_one_rotate (n := 9) (by rw [← hF]; exact qB_F433_312)
  have h3 : tB * psi gRel = tB * qB (yGen 4 3 3 1 * yGen 4 3 3 2 * yGen 4 3 3 5) *
      qB (yGen 4 3 3 0 * yGen 4 3 3 8 * yGen 4 3 3 9) := by
    simp only [gRel, map_mul, psi_yGen (show 0 < 10 by norm_num),
      psi_yGen (show 1 < 10 by norm_num), psi_yGen (show 2 < 10 by norm_num),
      psi_yGen (show 5 < 10 by norm_num), psi_yGen (show 8 < 10 by norm_num),
      psi_yGen (show 9 < 10 by norm_num), mul_assoc]
  rw [h3]
  exact h1

theorem psiU_F432 : psiU F432 = F433 2 3 1 := by
  have hy : ∀ l < 10, psiU (yGen 4 3 2 l) = yGen 4 3 3 l := fun l hl => psiU_yGen hl
  simp only [F432, F433, map_pow, map_mul, hy 0 (by norm_num), hy 1 (by norm_num),
    hy 5 (by norm_num), hy 6 (by norm_num), hy 7 (by norm_num), hy 8 (by norm_num),
    hy 9 (by norm_num), U433.A, U433.B, U433.C, U433.D, U433.armStart]

theorem psi_F432 :
    psi F432 = 1 := by
  rw [psi, MonoidHom.comp_apply, psiU_F432, F433_231_eq_213]
  exact qB_F433_213

theorem ker_rho432F_le_ker_psi :
    rho432F.ker ≤ psi.ker := by
  rw [ker_rho432F_eq, Subgroup.zpowers_le]
  exact MonoidHom.mem_ker.2 psi_F432

theorem card_range_psi_le :
    Nat.card psi.range ≤ 4089470473293004800 := by
  have h1 := Subgroup.index_dvd_of_le ker_rho432F_le_ker_psi
  rw [Subgroup.index_ker, Subgroup.index_ker, card_range_rho432F] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem conj_ker_mem
    (g : B433) {e : YGroup 4 3 2} (he : e ∈ rho432F.ker) :
    g * psi e * g⁻¹ ∈ rho432F.ker.map psi := by
  set N := rho432F.ker.map psi with hN
  have hgenN : ∀ u ∈ (psi.range : Set B433) ∪ {tB}, ∀ n ∈ N, u * n * u⁻¹ ∈ N := by
    intro u hu n hn
    obtain ⟨k, hk, rfl⟩ := hn
    rcases hu with ⟨y, rfl⟩ | rfl
    · rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨y * k * y⁻¹, (inferInstance : rho432F.ker.Normal).conj_mem k hk y, rfl⟩
    · have := psi_commute_t (ker_rho432F_le_ctil hk)
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨k, hk, rfl⟩
  have hnorm : ∀ g : B433, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g
    have hg : g ∈ Subgroup.closure ((psi.range : Set B433) ∪ {tB}) := by
      rw [closure_psi_t]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction'' with
    | mem x hx => exact hgenN x hx
    | inv_mem x hx =>
      intro n hn
      rcases hx with ⟨y, rfl⟩ | rfl
      · have := hgenN (psi y⁻¹) (Or.inl ⟨y⁻¹, rfl⟩) n hn
        rwa [map_inv] at this
      · have := hgenN tB (Or.inr rfl) n hn
        have hti : tB⁻¹ = tB := inv_eq_of_mul_eq_one_right tB_mul_self
        rwa [hti]
    | one => intro n hn; simpa using hn
    | mul x y _ _ ihx ihy =>
      intro n hn
      have := ihx _ (ihy n hn)
      rwa [show x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ by group]
  exact hnorm g _ ⟨e, he, rfl⟩

noncomputable instance finsetAction432 :
    MulAction (YGroup 4 3 2) (Finset (Fin 31671)) :=
  MulAction.compHom _ rho432F

theorem smul_finset432
    (e : YGroup 4 3 2) (s : Finset (Fin 31671)) : e • s = rho432F e • s := rfl

theorem orbit_eq
    (s : Finset (Fin 31671)) :
    MulAction.orbit (YGroup 4 3 2) s = MulAction.orbit rho432F.range s := by
  ext t
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨⟨rho432F e, e, rfl⟩, rfl⟩
  · rintro ⟨⟨γ, e, rfl⟩, rfl⟩
    exact ⟨e, rfl⟩

structure Good
    (X0 : Array ℕ) : Prop where
  fix : ∀ l < 9, rho432F (yGen 4 3 2 l) • listFinset 31671 X0 = listFinset 31671 X0
  card : 86316516 ≤ (MulAction.orbit (YGroup 4 3 2) (listFinset 31671 X0)).ncard

section Points

variable {X0 : Array ℕ}

theorem ctil_le_stabilizer
    (hG : Good X0) :
    Ctil432 ≤ MulAction.stabilizer (YGroup 4 3 2) (listFinset 31671 X0) := by
  rw [Ctil432, Subgroup.closure_le]
  rintro _ ⟨l, ⟨hl, hl9⟩, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact hG.fix l (by omega)

theorem ncard_orbit_le
    (hG : Good X0) :
    (MulAction.orbit (YGroup 4 3 2) (listFinset 31671 X0)).ncard ≤ 86316516 := by
  rw [← MulAction.index_stabilizer]
  have h1 := Subgroup.index_dvd_of_le (ctil_le_stabilizer hG)
  rw [index_ctil432] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem stabilizer_eq_ctil
    (hG : Good X0) :
    MulAction.stabilizer (YGroup 4 3 2) (listFinset 31671 X0) = Ctil432 := by
  have hle := ctil_le_stabilizer hG
  have hidx : (MulAction.stabilizer (YGroup 4 3 2) (listFinset 31671 X0)).index = 86316516 := by
    rw [MulAction.index_stabilizer]
    exact le_antisymm (ncard_orbit_le hG) hG.card
  have h := Subgroup.relIndex_mul_index hle
  rw [hidx, index_ctil432] at h
  have h1 : Ctil432.relIndex (MulAction.stabilizer (YGroup 4 3 2) (listFinset 31671 X0)) = 1 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (one_mul _).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle

end Points

abbrev Pts
    (X0 : Array ℕ) : Type := ↥(MulAction.orbit (YGroup 4 3 2) (listFinset 31671 X0))

@[expose] def basePt
    (X0 : Array ℕ) : Pts X0 := ⟨listFinset 31671 X0, MulAction.mem_orbit_self _⟩

@[expose] noncomputable def transv
    (X0 : Array ℕ) (p : Pts X0) : YGroup 4 3 2 :=
  Classical.choose (MulAction.mem_orbit_iff.1 p.2)

theorem transv_smul
    (X0 : Array ℕ) (p : Pts X0) : transv X0 p • basePt X0 = p :=
  Subtype.ext (Classical.choose_spec (MulAction.mem_orbit_iff.1 p.2))

variable {X0 : Array ℕ}

@[expose] noncomputable def setup
    (hG : Good X0) :
    SymGen.Setup B433 (YGroup 4 3 2) (Pts X0) where
  t := tB
  ψ := psi
  o := basePt X0
  w := transv X0
  t_mul_t := tB_mul_self
  w_smul := transv_smul X0
  stab_comm := fun c hc => by
    have h1 : c ∈ MulAction.stabilizer (YGroup 4 3 2) (listFinset 31671 X0) := by
      rw [MulAction.mem_stabilizer_iff]
      exact congrArg Subtype.val hc
    rw [stabilizer_eq_ctil hG] at h1
    exact psi_commute_t h1

@[expose] noncomputable def xNode
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ))
    (j : ℕ) : B433 :=
  if _h : 0 < j ∧ j < nodes.size ∧ (nodes[j]!).1 < j then
    xNode hG pt nodes (nodes[j]!).1 * (setup hG).T (pt (nodes[j]!).2)
  else 1
termination_by j
decreasing_by exact _h.2.2

theorem xNode_zero
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) :
    xNode hG pt nodes 0 = 1 := by
  rw [xNode]
  simp only [lt_self_iff_false, not_lt_zero, and_false, and_self, ↓reduceDIte]

theorem xNode_eq
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) {j i p : ℕ}
    (hj : 0 < j) (hn : nodes[j]? = some (i, p)) (hi : i < j) :
    xNode hG pt nodes j = xNode hG pt nodes i * (setup hG).T (pt p) := by
  obtain ⟨hjs, hv⟩ := Y333.nodes_get hn
  have hc : 0 < j ∧ j < nodes.size ∧ (nodes[j]!).1 < j := ⟨hj, hjs, by rw [hv]; exact hi⟩
  rw [xNode, dite_eq_left hc, hv]

@[expose] def PE
    (a : ByteArray) : Prop := ∃ e : YGroup 4 3 2, RepB 31671 a (rho432F e)

@[expose] def W
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) (j : ℕ)
    (a : ByteArray) : Prop :=
  ∃ e : YGroup 4 3 2, RepB 31671 a (rho432F e) ∧
    xNode hG pt nodes j * (setup hG).ψ e * (xNode hG pt nodes j)⁻¹ ∈ (setup hG).H

@[expose] def V
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) (N : ℕ)
    (i p k : ℕ) (a : ByteArray) : Prop :=
  p < N ∧ ∃ e : YGroup 4 3 2, RepB 31671 a (rho432F e) ∧
    (setup hG).RCoset (xNode hG pt nodes i * (setup hG).T (pt p))
      (xNode hG pt nodes k * (setup hG).ψ e)

@[expose] noncomputable def tProd (η : ℕ → YGroup 4 3 2) (m : ℕ) : B433 :=
  ((List.range m).map fun s => psi (η s) * tB * (psi (η s))⁻¹).prod

theorem tProd_zero (η : ℕ → YGroup 4 3 2) : tProd η 0 = 1 := rfl

theorem tProd_succ (η : ℕ → YGroup 4 3 2) (m : ℕ) :
    tProd η (m + 1) = tProd η m * (psi (η m) * tB * (psi (η m))⁻¹) := by
  simp only [tProd, List.range_succ, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem tProd_pow (g : YGroup 4 3 2) (m : ℕ) :
    tProd (fun s => g ^ s) m = (tB * psi g) ^ m * ((psi g) ^ m)⁻¹ := by
  induction m with
  | zero => simp [tProd_zero]
  | succ m ih =>
    rw [tProd_succ, ih, map_pow, pow_succ (tB * psi g), pow_succ (psi g), mul_inv_rev]
    group

@[expose] def RelOK (hs : Array ByteArray) (π : ByteArray) : Prop :=
  ∃ (η : ℕ → YGroup 4 3 2) (ρ : YGroup 4 3 2), (∀ s < hs.size, RepB 31671 hs[s]! (rho432F (η s))) ∧
    RepB 31671 π (rho432F ρ) ∧ tProd η hs.size = psi ρ

theorem relOK_gRel
    {hs : Array ByteArray} {π : ByteArray} (hsz : hs.size = 9)
    (hhs : ∀ s < 9, RepB 31671 hs[s]! (rho432F (gRel ^ s)))
    (hπ : RepB 31671 π (rho432F (gRel⁻¹ ^ 9))) : RelOK hs π := by
  refine ⟨fun s => gRel ^ s, gRel⁻¹ ^ 9, fun s hs' => hhs s (hsz ▸ hs'), hπ, ?_⟩
  rw [hsz, tProd_pow, tB_psi_gRel_pow_nine, one_mul, map_pow, map_inv, inv_pow]

structure CtxGood (C : B.CtxB) : Prop where
  n_eq : C.n = 31671
  N_pos : 0 < C.N
  letters_size : C.letters.size = 10
  letters_rep : ∀ l < 10, RepB 31671 C.letters[l]! (rho432F (yGen 4 3 2 l))
  cl_eq : C.cl = 9
  one_rep : RepB 31671 C.one 1
  rels_ok : ∀ r < C.rels.size, RelOK C.rels[r]!.1 C.rels[r]!.2

theorem rels_ok_single
    {C : B.CtxB} {hs : Array ByteArray} {π : ByteArray}
    (hC : C.rels = #[(hs, π)]) (hsz : hs.size = 9)
    (hhs : ∀ s < 9, RepB 31671 hs[s]! (rho432F (gRel ^ s)))
    (hπ : RepB 31671 π (rho432F (gRel⁻¹ ^ 9))) :
    ∀ r < C.rels.size, RelOK C.rels[r]!.1 C.rels[r]!.2 := by
  intro r hr
  have hsz1 : C.rels.size = 1 := by rw [hC]; rfl
  obtain rfl : r = 0 := by omega
  rw [hC]
  exact relOK_gRel hsz hhs hπ

@[expose] def ActSpec
    (C : B.CtxB) (pt : ℕ → Pts X0) : Prop :=
  ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) → ∀ p < C.N,
    C.act σ p < C.N ∧ pt (C.act σ p) = e • pt p

@[expose] def NodesOK (C : B.CtxB) : Prop :=
  ∀ j i p, C.nodes[j]? = some (i, p) → 0 < j → i < j

theorem repB_congr {n : ℕ} {b : ByteArray} {g h : Equiv.Perm (Fin n)} (hb : RepB n b g)
    (e : g = h) : RepB n b h :=
  e ▸ hb

section Rules

variable {C : B.CtxB}

theorem pe_letter
    (hC : CtxGood C) {l : ℕ} (hl : l < C.letters.size) : PE C.letters[l]! := by
  have hl10 : l < 10 := by rw [← hC.letters_size]; exact hl
  exact ⟨yGen 4 3 2 l, hC.letters_rep l hl10⟩

theorem pe_mul
    (hC : CtxGood C) {a b : ByteArray} (ha : PE a) (hb : PE b) :
    PE (bcomp C.n a b) := by
  obtain ⟨ea, hea⟩ := ha
  obtain ⟨eb, heb⟩ := hb
  rw [hC.n_eq]
  exact ⟨ea * eb, by rw [map_mul]; exact repB_bcomp (by norm_num) hea heb⟩

theorem pe_inv (hC : CtxGood C) {a : ByteArray} (ha : PE a)
    (h : bisInv C.n a (binvCand C.n a) = true) : PE (binvCand C.n a) := by
  obtain ⟨ea, hea⟩ := ha
  rw [hC.n_eq] at h ⊢
  exact ⟨ea⁻¹, by rw [map_inv]; exact repB_binv hea h⟩

theorem w_pe
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) {j : ℕ} {a : ByteArray}
    (h : W hG pt nodes j a) : PE a := by
  obtain ⟨e, he, -⟩ := h
  exact ⟨e, he⟩

theorem v_pe
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) (N : ℕ) {i p k : ℕ}
    {a : ByteArray} (h : V hG pt nodes N i p k a) : PE a := by
  obtain ⟨-, e, he, -⟩ := h
  exact ⟨e, he⟩

theorem w_root
    (hG : Good X0) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ)) {a : ByteArray}
    (h : PE a) : W hG pt nodes 0 a := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, he, ?_⟩
  rw [xNode_zero, one_mul, inv_one, mul_one]
  exact ⟨e, rfl⟩

theorem w_mul
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ))
    {j : ℕ} {a b : ByteArray} (ha : W hG pt nodes j a) (hb : W hG pt nodes j b) :
    W hG pt nodes j (bcomp C.n a b) := by
  obtain ⟨ea, hea, hxa⟩ := ha
  obtain ⟨eb, heb, hxb⟩ := hb
  rw [hC.n_eq]
  exact ⟨ea * eb, by rw [map_mul]; exact repB_bcomp (by norm_num) hea heb,
    Y333.stab_mul (setup hG) hxa hxb⟩

theorem w_inv
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ))
    {j : ℕ} {a : ByteArray} (ha : W hG pt nodes j a)
    (h : bisInv C.n a (binvCand C.n a) = true) : W hG pt nodes j (binvCand C.n a) := by
  obtain ⟨ea, hea, hxa⟩ := ha
  rw [hC.n_eq] at h ⊢
  exact ⟨ea⁻¹, by rw [map_inv]; exact repB_binv hea h, Y333.stab_inv (setup hG) hxa⟩

theorem w_id
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (nodes : Array (ℕ × ℕ))
    (j : ℕ) : W hG pt nodes j C.one := by
  refine ⟨1, repB_congr hC.one_rep (map_one _).symm, ?_⟩
  rw [map_one, mul_one, mul_inv_cancel]
  exact (setup hG).H.one_mem

theorem rule_r0
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hnodes : NodesOK C)
    {j i p : ℕ} (hj : 0 < j) (hn : C.nodes[j]? = some (i, p)) (hp : p < C.N) :
    V hG pt C.nodes C.N i p j C.one := by
  have hij : i < j := hnodes j i p hn hj
  refine ⟨hp, 1, repB_congr hC.one_rep (map_one _).symm, ?_⟩
  rw [map_one, mul_one, xNode_eq hG pt C.nodes hj hn hij]
  exact SymGen.Setup.RCoset.refl _ _

theorem rule_r1
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hact : ActSpec C pt)
    {i p k : ℕ} {a : ByteArray} (h : V hG pt C.nodes C.N i p k a)
    (hinv : bisInv C.n a (binvCand C.n a) = true) :
    V hG pt C.nodes C.N k (C.act a p) i (binvCand C.n a) := by
  obtain ⟨hp, e, he, hc⟩ := h
  obtain ⟨hlt, hsm⟩ := hact a e he p hp
  rw [hC.n_eq] at hinv ⊢
  refine ⟨hlt, e⁻¹, by rw [map_inv]; exact repB_binv he hinv, ?_⟩
  rw [hsm]
  exact Y333.core1 (setup hG) hc

theorem rule_r2
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hact : ActSpec C pt)
    {j p k q : ℕ} {a s : ByteArray} (h : V hG pt C.nodes C.N j p k a)
    (hs : W hG pt C.nodes j s) (hq : q < C.N) (hs' : C.act s q = p) :
    V hG pt C.nodes C.N j q k (bcomp C.n a s) := by
  obtain ⟨-, ea, hea, hc⟩ := h
  obtain ⟨es, hes, hxs⟩ := hs
  obtain ⟨-, hsm⟩ := hact s es hes q hq
  rw [hs'] at hsm
  rw [hC.n_eq]
  exact ⟨hq, ea * es, by rw [map_mul]; exact repB_bcomp (by norm_num) hea hes,
    Y333.core2 (setup hG) hc hxs hsm.symm⟩

theorem rule_r3
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) {i p k : ℕ}
    {a b : ByteArray} (ha : V hG pt C.nodes C.N i p k a) (hb : V hG pt C.nodes C.N i p k b)
    (hinv : bisInv C.n b (binvCand C.n b) = true) :
    W hG pt C.nodes k (bcomp C.n a (binvCand C.n b)) := by
  obtain ⟨-, ea, hea, hca⟩ := ha
  obtain ⟨-, eb, heb, hcb⟩ := hb
  rw [hC.n_eq] at hinv ⊢
  refine ⟨ea * eb⁻¹, ?_, Y333.core3 (setup hG) hca hcb⟩
  rw [map_mul, map_inv]
  exact repB_bcomp (by norm_num) hea (repB_binv heb hinv)

theorem rule45_data
    (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) {g : ByteArray} (hg : PE g)
    (hginv : bisInv 31671 g (binvCand 31671 g) = true) :
    ∃ eg : YGroup 4 3 2, RepB 31671 g (rho432F eg) ∧
      RepB 31671 (bcomp 31671 g C.c) (rho432F (eg * yGen 4 3 2 9)) ∧
      C.act g 0 < C.N ∧ pt (C.act g 0) = eg • basePt X0 ∧
      C.act (bcomp 31671 g C.c) 0 < C.N ∧
      pt (C.act (bcomp 31671 g C.c) 0) = (eg * yGen 4 3 2 9) • basePt X0 ∧
      RepB 31671 (bcomp 31671 (bcomp 31671 g C.c) (binvCand 31671 g))
        (rho432F (eg * yGen 4 3 2 9 * eg⁻¹)) := by
  obtain ⟨eg, heg⟩ := hg
  have hcRep : RepB 31671 C.c (rho432F (yGen 4 3 2 9)) := by
    rw [B.CtxB.c, hC.cl_eq]
    exact hC.letters_rep 9 (by norm_num)
  have hgc : RepB 31671 (bcomp 31671 g C.c) (rho432F (eg * yGen 4 3 2 9)) := by
    rw [map_mul]; exact repB_bcomp (by norm_num) heg hcRep
  obtain ⟨hlt0, hsm0⟩ := hact g eg heg 0 hC.N_pos
  obtain ⟨hltc, hsmc⟩ := hact _ _ hgc 0 hC.N_pos
  rw [hpt0] at hsm0 hsmc
  refine ⟨eg, heg, hgc, hlt0, hsm0, hltc, hsmc, ?_⟩
  refine repB_congr (repB_bcomp (by norm_num) hgc (repB_binv heg hginv)) ?_
  simp only [map_mul, map_inv]

theorem c3_mul_self : yGen 4 3 2 9 * yGen 4 3 2 9 = 1 := yGen_mul_self 4 3 2 9

theorem psi_c3_mul_self : psi (yGen 4 3 2 9) * psi (yGen 4 3 2 9) = 1 := by
  rw [← map_mul, c3_mul_self, map_one]

theorem rule_r4
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) {g a b : ByteArray} {i j k : ℕ} (hg : PE g)
    (hginv : bisInv C.n g (binvCand C.n g) = true)
    (h1 : V hG pt C.nodes C.N i (C.act g 0) j a)
    (h2 : V hG pt C.nodes C.N j (C.act a (C.act (bcomp C.n g C.c) 0)) k b) :
    V hG pt C.nodes C.N i (C.act (bcomp C.n g C.c) 0) k
      (bcomp C.n (bcomp C.n b a) (bcomp C.n (bcomp C.n g C.c) (binvCand C.n g))) := by
  rw [hC.n_eq] at hginv h2 ⊢
  obtain ⟨eg, heg, hgc, -, hsm0, hltc, hsmc, hconj⟩ := rule45_data hC pt hpt0 hact hg hginv
  obtain ⟨-, ea, hea, hc1⟩ := h1
  obtain ⟨-, eb, heb, hc2⟩ := h2
  obtain ⟨-, hsma⟩ := hact a ea hea _ hltc
  refine ⟨hltc, eb * ea * (eg * yGen 4 3 2 9 * eg⁻¹), ?_, ?_⟩
  · refine repB_congr (repB_bcomp (by norm_num) (repB_bcomp (by norm_num) heb hea) hconj) ?_
    simp only [map_mul]
  · rw [hsm0] at hc1
    rw [hsma, hsmc] at hc2
    rw [hsmc]
    exact Y333.core4 (setup hG) psi_c3_mul_self tB_psi_c_cube eg hc1 hc2

theorem rule_r5
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) {g a b : ByteArray} {i j k : ℕ} (hg : PE g)
    (hginv : bisInv C.n g (binvCand C.n g) = true)
    (hainv : bisInv C.n a (binvCand C.n a) = true)
    (h1 : V hG pt C.nodes C.N i (C.act g 0) j a)
    (h3 : V hG pt C.nodes C.N i (C.act (bcomp C.n g C.c) 0) k b) :
    V hG pt C.nodes C.N j (C.act a (C.act (bcomp C.n g C.c) 0)) k
      (bcomp C.n (bcomp C.n b (bcomp C.n (bcomp C.n g C.c) (binvCand C.n g)))
        (binvCand C.n a)) := by
  rw [hC.n_eq] at hginv hainv h3 ⊢
  obtain ⟨eg, heg, hgc, -, hsm0, hltc, hsmc, hconj⟩ := rule45_data hC pt hpt0 hact hg hginv
  obtain ⟨-, ea, hea, hc1⟩ := h1
  obtain ⟨-, eb, heb, hc3⟩ := h3
  obtain ⟨hlta, hsma⟩ := hact a ea hea _ hltc
  refine ⟨hlta, eb * (eg * yGen 4 3 2 9 * eg⁻¹) * ea⁻¹, ?_, ?_⟩
  · refine repB_congr (repB_bcomp (by norm_num) (repB_bcomp (by norm_num) heb hconj)
      (repB_binv hea hainv)) ?_
    simp only [map_mul, map_inv]
  · rw [hsm0] at hc1
    rw [hsmc] at hc3
    rw [hsma, hsmc]
    exact Y333.core5 (setup hG) c3_mul_self psi_c3_mul_self tB_psi_c_cube eg hc1 hc3

end Rules

section Abstract

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω] (S : SymGen.Setup G E Ω)

theorem rcoset_shift {xk xk' : G} {ea eb ec : E}
    (h : S.RCoset (xk * S.ψ ea) (xk' * S.ψ eb)) :
    S.RCoset (xk * S.ψ ec) (xk' * S.ψ (eb * ea⁻¹ * ec)) := by
  have := h.mul_right (S.ψ ea⁻¹ * S.ψ ec)
  rwa [show xk * S.ψ ea * (S.ψ ea⁻¹ * S.ψ ec) = xk * S.ψ ec by rw [map_inv]; group,
    show xk' * S.ψ eb * (S.ψ ea⁻¹ * S.ψ ec) = xk' * S.ψ (eb * ea⁻¹ * ec) by
      simp only [map_mul, map_inv]; group] at this

theorem stab_conj {xk xk' : G} {ea eb es : E} (h : S.RCoset (xk * S.ψ ea) (xk' * S.ψ eb))
    (hs : xk * S.ψ es * xk⁻¹ ∈ S.H) :
    xk' * S.ψ (eb * ea⁻¹ * es * (eb * ea⁻¹)⁻¹) * xk'⁻¹ ∈ S.H := by
  have h' : xk * S.ψ ea * (xk' * S.ψ eb)⁻¹ ∈ S.H := h
  have := S.H.mul_mem (S.H.mul_mem (S.H.inv_mem h') hs) h'
  rwa [show (xk * S.ψ ea * (xk' * S.ψ eb)⁻¹)⁻¹ * (xk * S.ψ es * xk⁻¹) *
      (xk * S.ψ ea * (xk' * S.ψ eb)⁻¹) = xk' * S.ψ (eb * ea⁻¹ * es * (eb * ea⁻¹)⁻¹) * xk'⁻¹ by
    simp only [map_mul, map_inv]; group] at this

theorem chain_step {γ η ea : E} {x₀ xi xk Q : G} {p : Ω} (hp : p = (γ * η) • S.o)
    (hinv : S.RCoset (x₀ * Q) (xi * S.ψ γ)) (hf : S.RCoset (xi * S.T p) (xk * S.ψ ea)) :
    S.RCoset (x₀ * (Q * S.T (η • S.o))) (xk * S.ψ (ea * γ)) := by
  have h1 := hinv.mul_right (S.T (η • S.o))
  have h2 := hf.mul_right (S.ψ γ)
  have e1 : xi * S.ψ γ * S.T (η • S.o) = xi * S.T p * S.ψ γ := by
    rw [mul_assoc, S.mul_T γ (η • S.o), ← mul_smul, ← hp, ← mul_assoc]
  have e2 : xk * S.ψ ea * S.ψ γ = xk * S.ψ (ea * γ) := by rw [map_mul, mul_assoc]
  rw [mul_assoc, e1] at h1
  rw [e2] at h2
  exact h1.trans h2

theorem chain_final {γ₀ γ η ρ : E} {x₀ xi P : G} (hrel : P * S.T (η • S.o) = S.ψ ρ)
    (h : S.RCoset (x₀ * (S.ψ γ₀ * P)) (xi * S.ψ γ)) :
    S.RCoset (xi * S.T ((γ * η) • S.o)) (x₀ * S.ψ (γ₀ * ρ * γ⁻¹)) := by
  have hT : S.T ((γ * η) • S.o) = S.ψ γ * S.T (η • S.o) * (S.ψ γ)⁻¹ := by
    rw [mul_smul, ← S.conj_T γ (η • S.o)]
  have h' := h.symm.mul_right (S.T (η • S.o) * (S.ψ γ)⁻¹)
  have e1 : xi * S.ψ γ * (S.T (η • S.o) * (S.ψ γ)⁻¹) = xi * S.T ((γ * η) • S.o) := by
    rw [hT]; group
  have e2 : x₀ * (S.ψ γ₀ * P) * (S.T (η • S.o) * (S.ψ γ)⁻¹) = x₀ * S.ψ (γ₀ * ρ * γ⁻¹) := by
    calc x₀ * (S.ψ γ₀ * P) * (S.T (η • S.o) * (S.ψ γ)⁻¹)
        = x₀ * S.ψ γ₀ * (P * S.T (η • S.o)) * (S.ψ γ)⁻¹ := by simp only [mul_assoc]
      _ = x₀ * S.ψ (γ₀ * ρ * γ⁻¹) := by
        rw [hrel]
        simp only [map_mul, map_inv]
        group
  rw [e1, e2] at h'
  exact h'

end Abstract

section Chain

variable {C : B.CtxB}

theorem chain_spec
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) {η : ℕ → YGroup 4 3 2} {γ₀ : YGroup 4 3 2} {j₀ : ℕ} :
    ∀ (fs : List B.CFB) (hs : List ByteArray) (s₀ i₀ : ℕ) (c₀ : ByteArray) (γ : YGroup 4 3 2),
      (∀ f ∈ fs, V hG pt C.nodes C.N f.i f.p f.k f.a) → fs.length ≤ hs.length →
      (∀ t < hs.length, RepB 31671 hs[t]! (rho432F (η (s₀ + t)))) →
      RepB 31671 c₀ (rho432F γ) →
      (setup hG).RCoset (xNode hG pt C.nodes j₀ * (psi γ₀ * tProd η s₀))
        (xNode hG pt C.nodes i₀ * psi γ) →
      ∀ i c, (fs.zip hs).foldl (B.chainStep C) (some (i₀, c₀)) = some (i, c) →
      ∃ γ' : YGroup 4 3 2, RepB 31671 c (rho432F γ') ∧
        (setup hG).RCoset (xNode hG pt C.nodes j₀ * (psi γ₀ * tProd η (s₀ + fs.length)))
          (xNode hG pt C.nodes i * psi γ') := by
  have hnone : ∀ l : List (B.CFB × ByteArray), l.foldl (B.chainStep C) none = none := by
    intro l
    induction l with
    | nil => rfl
    | cons f l ih => exact ih
  intro fs
  induction fs with
  | nil =>
    intro hs s₀ i₀ c₀ γ _ _ _ hc₀ hinv i c hend
    simp only [List.zip_nil_left, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hend
    obtain ⟨rfl, rfl⟩ := hend
    exact ⟨γ, hc₀, by simpa using hinv⟩
  | cons f fs ih =>
    intro hs s₀ i₀ c₀ γ hfs hlen hhs hc₀ hinv i c hend
    cases hs with
    | nil => simp at hlen
    | cons h hs' =>
      rw [List.zip_cons_cons, List.foldl_cons] at hend
      by_cases hcond : (f.i == i₀ && f.p == C.act (bcomp C.n c₀ h) 0) = true
      · have hs : B.chainStep C (some (i₀, c₀)) (f, h) = some (f.k, bcomp C.n f.a c₀) := by
          simp only [B.chainStep, hcond, ↓reduceIte]
        rw [hs] at hend
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hfi, hfp⟩ := hcond
        obtain ⟨-, ea, hea, hcos⟩ := hfs f List.mem_cons_self
        have hh : RepB 31671 h (rho432F (η s₀)) := by simpa using hhs 0 (by simp)
        have hbc : RepB 31671 (bcomp C.n c₀ h) (rho432F (γ * η s₀)) := by
          rw [hC.n_eq, map_mul]
          exact repB_bcomp (by norm_num) hc₀ hh
        obtain ⟨-, hsm⟩ := hact _ _ hbc 0 hC.N_pos
        rw [hpt0] at hsm
        have hptf : pt f.p = (γ * η s₀) • (setup hG).o := by rw [hfp]; exact hsm
        rw [hfi] at hcos
        have hnew := chain_step (setup hG) hptf hinv hcos
        have hT : (setup hG).T (η s₀ • (setup hG).o) = psi (η s₀) * tB * (psi (η s₀))⁻¹ := by
          rw [← (setup hG).conj_T (η s₀) (setup hG).o, (setup hG).T_o]
          rfl
        rw [hT, mul_assoc (psi γ₀), ← tProd_succ] at hnew
        have hrep : RepB 31671 (bcomp C.n f.a c₀) (rho432F (ea * γ)) := by
          rw [hC.n_eq, map_mul]
          exact repB_bcomp (by norm_num) hea hc₀
        have hhs' : ∀ t < hs'.length, RepB 31671 hs'[t]! (rho432F (η (s₀ + 1 + t))) := by
          intro t ht
          have := hhs (t + 1) (by simpa using Nat.succ_lt_succ ht)
          rwa [show s₀ + (t + 1) = s₀ + 1 + t by omega, List.getElem!_cons_succ] at this
        obtain ⟨γ', hγ', hR⟩ := ih hs' (s₀ + 1) f.k _ (ea * γ)
          (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) (by simpa using hlen) hhs' hrep
          hnew i c hend
        refine ⟨γ', hγ', ?_⟩
        rw [List.length_cons, show s₀ + (fs.length + 1) = s₀ + 1 + fs.length by omega]
        exact hR
      · have hs : B.chainStep C (some (i₀, c₀)) (f, h) = none := by
          simp [B.chainStep, hcond]
        rw [hs, hnone] at hend
        exact absurd hend (by simp)

theorem rule_r6
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) {r : ℕ} (hr : r < C.rels.size) {j₀ : ℕ} {c₀ : ByteArray}
    {fs : List B.CFB} {i : ℕ} {c : ByteArray} (hc₀ : PE c₀)
    (hfs : ∀ f ∈ fs, V hG pt C.nodes C.N f.i f.p f.k f.a)
    (hlen : fs.length + 1 = C.rels[r]!.1.size)
    (hend : B.chainEnd C j₀ c₀ fs C.rels[r]!.1.toList = some (i, c))
    (hcinv : bisInv C.n c (binvCand C.n c) = true) :
    V hG pt C.nodes C.N i (C.act (bcomp C.n c C.rels[r]!.1[fs.length]!) 0) j₀
      (bcomp C.n (bcomp C.n c₀ C.rels[r]!.2) (binvCand C.n c)) := by
  obtain ⟨η, ρ, hη, hρ, hrel⟩ := hC.rels_ok r hr
  obtain ⟨γ₀, hγ₀⟩ := hc₀
  have hlt' : fs.length < C.rels[r]!.1.size := by omega
  obtain ⟨γ, hγ, hR⟩ := chain_spec hG hC pt hpt0 hact (η := η) (γ₀ := γ₀) (j₀ := j₀) fs
    C.rels[r]!.1.toList 0 j₀ c₀ γ₀ hfs (by simp; omega)
    (fun t ht => by
      rw [zero_add, Array.getElem!_toList]
      exact hη t (by simpa using ht))
    hγ₀ (by rw [tProd_zero, mul_one]; exact SymGen.Setup.RCoset.refl _ _) i c hend
  rw [zero_add] at hR
  have hηm : RepB 31671 C.rels[r]!.1[fs.length]! (rho432F (η fs.length)) := hη _ hlt'
  have hbc : RepB 31671 (bcomp 31671 c C.rels[r]!.1[fs.length]!) (rho432F (γ * η fs.length)) := by
    rw [map_mul]
    exact repB_bcomp (by norm_num) hγ hηm
  have hrel' : tProd η fs.length * (setup hG).T (η fs.length • (setup hG).o) = psi ρ := by
    rw [← hlen, tProd_succ] at hrel
    rw [← (setup hG).conj_T (η fs.length) (setup hG).o, (setup hG).T_o]
    exact hrel
  rw [hC.n_eq] at hcinv ⊢
  obtain ⟨hlt, hsm⟩ := hact _ _ hbc 0 hC.N_pos
  rw [hpt0] at hsm
  refine ⟨hlt, γ₀ * ρ * γ⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact repB_bcomp (by norm_num) (repB_bcomp (by norm_num) hγ₀ hρ) (repB_binv hγ hcinv)
  · have hptc : pt (C.act (bcomp 31671 c C.rels[r]!.1[fs.length]!) 0) =
        (γ * η fs.length) • (setup hG).o := hsm
    rw [hptc]
    exact chain_final (setup hG) hrel' hR

theorem rule_r7
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) {i p k k' m q : ℕ}
    {a b c : ByteArray} (ha : V hG pt C.nodes C.N i p k a) (hb : V hG pt C.nodes C.N i p k' b)
    (hainv : bisInv C.n a (binvCand C.n a) = true) (hc : V hG pt C.nodes C.N m q k c) :
    V hG pt C.nodes C.N m q k' (bcomp C.n (B.coinc C a b) c) := by
  obtain ⟨-, ea, hea, hca⟩ := ha
  obtain ⟨-, eb, heb, hcb⟩ := hb
  obtain ⟨hq, ec, hec, hcc⟩ := hc
  unfold B.coinc
  rw [hC.n_eq] at hainv ⊢
  refine ⟨hq, eb * ea⁻¹ * ec, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact repB_bcomp (by norm_num) (repB_bcomp (by norm_num) heb (repB_binv hea hainv)) hec
  · exact hcc.trans (rcoset_shift (setup hG) (hca.symm.trans hcb))

theorem rule_r8
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) {i p k k' : ℕ}
    {a b s : ByteArray} (ha : V hG pt C.nodes C.N i p k a) (hb : V hG pt C.nodes C.N i p k' b)
    (hainv : bisInv C.n a (binvCand C.n a) = true)
    (hcoinv : bisInv C.n (B.coinc C a b) (binvCand C.n (B.coinc C a b)) = true)
    (hs : W hG pt C.nodes k s) :
    W hG pt C.nodes k'
      (bcomp C.n (bcomp C.n (B.coinc C a b) s) (binvCand C.n (B.coinc C a b))) := by
  obtain ⟨-, ea, hea, hca⟩ := ha
  obtain ⟨-, eb, heb, hcb⟩ := hb
  obtain ⟨es, hes, hxs⟩ := hs
  unfold B.coinc at hcoinv ⊢
  rw [hC.n_eq] at hainv hcoinv ⊢
  have hκ : RepB 31671 (bcomp 31671 b (binvCand 31671 a)) (rho432F (eb * ea⁻¹)) := by
    rw [map_mul, map_inv]
    exact repB_bcomp (by norm_num) heb (repB_binv hea hainv)
  refine ⟨eb * ea⁻¹ * es * (eb * ea⁻¹)⁻¹, ?_, stab_conj (setup hG) (hca.symm.trans hcb) hxs⟩
  refine repB_congr (repB_bcomp (by norm_num) (repB_bcomp (by norm_num) hκ hes)
    (repB_binv hκ hcoinv)) ?_
  simp only [map_mul, map_inv]

end Chain

section Main

variable {C : B.CtxB}

theorem rules
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0)
    (hact : ActSpec C pt) (hnodes : NodesOK C) :
    B.RulesB C PE (W hG pt C.nodes) (V hG pt C.nodes C.N) where
  letter := fun _ hl => pe_letter hC hl
  mul := fun _ _ ha hb => pe_mul hC ha hb
  inv := fun _ ha h => pe_inv hC ha h
  wpe := fun _ _ h => w_pe hG pt C.nodes h
  vpe := fun _ _ _ _ h => v_pe hG pt C.nodes C.N h
  wroot := fun _ ha => w_root hG pt C.nodes ha
  wmul := fun _ _ _ ha hb => w_mul hG hC pt C.nodes ha hb
  winv := fun _ _ ha h => w_inv hG hC pt C.nodes ha h
  wid := fun j => w_id hG hC pt C.nodes j
  r0 := fun _ _ _ hj hn hp => rule_r0 hG hC pt hnodes hj hn hp
  r1 := fun _ _ _ _ h hinv => rule_r1 hG hC pt hact h hinv
  r2 := fun _ _ _ _ _ _ h hs hq hs' => rule_r2 hG hC pt hact h hs hq hs'
  r3 := fun _ _ _ _ _ ha hb hinv => rule_r3 hG hC pt ha hb hinv
  r4 := fun _ _ _ _ _ _ _ hg hginv h1 h2 => rule_r4 hG hC pt hpt0 hact hg hginv h1 h2
  r5 := fun _ _ _ _ _ _ _ hg hginv hainv h1 h3 => rule_r5 hG hC pt hpt0 hact hg hginv hainv h1 h3
  r6 := fun _ hr _ _ _ _ _ hc₀ hfs hlen hend hcinv =>
    rule_r6 hG hC pt hpt0 hact hr hc₀ hfs hlen hend hcinv
  r7 := fun _ _ _ _ _ _ _ _ _ ha hb hainv hc => rule_r7 hG hC pt ha hb hainv hc
  r8 := fun _ _ _ _ _ _ _ ha hb hainv hcoinv hs => rule_r8 hG hC pt ha hb hainv hcoinv hs

@[expose] def env
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0)
    (hpt0 : pt 0 = basePt X0) (hact : ActSpec C pt) (hnodes : NodesOK C) : B.EnvB where
  C := C
  PE := PE
  W := W hG pt C.nodes
  V := V hG pt C.nodes C.N
  rules := rules hG hC pt hpt0 hact hnodes

theorem index_psi_le_of_finalOK
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0)
    (hpt0 : pt 0 = basePt X0) (hact : ActSpec C pt) (hnodes : NodesOK C)
    (hactAll : ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) → ∀ p < C.N,
      B.u32get (C.actAll σ) p < C.N ∧ pt (B.u32get (C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Pts X0, ∃ p < C.N, pt p = ω) (bound : ℕ) (prog : Array B.Ins)
    (fins : Array (ℕ × B.NodeFin))
    (h : (env hG hC pt hpt0 hact hnodes).finalOK prog fins 4089470473293004800 bound = true) :
    psi.range.FiniteIndex ∧ psi.range.index ≤ bound := by
  have := finite_y432
  exact index_le_of_finalOK (env hG hC pt hpt0 hact hnodes) (setup hG) (n := 31671) hC.n_eq
    (by norm_num) rho432F pt (xNode hG pt C.nodes)
    (fun j a hW => hW)
    (fun i p k a hV => ⟨hV.1, by obtain ⟨e, -, he⟩ := hV.2; exact ⟨e, he⟩⟩)
    hactAll hpt (by rw [xNode_zero]; exact Subgroup.one_mem _)
    (fun j e he => Subgroup.map_le_range psi rho432F.ker
      (conj_ker_mem (xNode hG pt C.nodes j) (MonoidHom.mem_ker.2 he)))
    4089470473293004800 bound card_range_rho432F closure_psi_t prog fins h

theorem card_B433_le_of_finalOK
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0)
    (hpt0 : pt 0 = basePt X0) (hact : ActSpec C pt) (hnodes : NodesOK C)
    (hactAll : ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) → ∀ p < C.N,
      B.u32get (C.actAll σ) p < C.N ∧ pt (B.u32get (C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Pts X0, ∃ p < C.N, pt p = ω) (bound : ℕ) (prog : Array B.Ins)
    (fins : Array (ℕ × B.NodeFin))
    (h : (env hG hC pt hpt0 hact hnodes).finalOK prog fins 4089470473293004800 bound = true) :
    Finite B433 ∧ Nat.card B433 ≤ bound * 4089470473293004800 := by
  have := finite_y432
  obtain ⟨hfi, hle⟩ := index_psi_le_of_finalOK hG hC pt hpt0 hact hnodes hactAll hpt bound prog
    fins h
  have : Finite psi.range := Finite.of_surjective _ psi.rangeRestrict_surjective
  have hcard := Subgroup.card_mul_index psi.range
  have hHpos : 0 < Nat.card psi.range := Nat.card_pos
  have hipos : 0 < psi.range.index := Nat.pos_of_ne_zero hfi.index_ne_zero
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard, Nat.mul_comm bound]
  exact Nat.mul_le_mul card_range_psi_le hle

theorem Q343N_half : Q343N / 2 = 1015970529280000 * 4089470473293004800 := by
  unfold Q343N
  norm_num

theorem Q343_bound_of_finalOK
    (hG : Good X0) (hC : CtxGood C) (pt : ℕ → Pts X0)
    (hpt0 : pt 0 = basePt X0) (hact : ActSpec C pt) (hnodes : NodesOK C)
    (hactAll : ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) → ∀ p < C.N,
      B.u32get (C.actAll σ) p < C.N ∧ pt (B.u32get (C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Pts X0, ∃ p < C.N, pt p = ω) (bound : ℕ) (hbound : bound ≤ 1015970529280000)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : (env hG hC pt hpt0 hact hnodes).finalOK prog fins 4089470473293004800 bound = true) :
    Finite Q343 ∧ Nat.card Q343 ≤ Q343N := by
  obtain ⟨hfin, hle⟩ := card_B433_le_of_finalOK hG hC pt hpt0 hact hnodes hactAll hpt bound prog
    fins h
  refine Q343_bound_of_B433 ⟨hfin, hle.trans ?_⟩
  rw [Q343N_half]
  exact Nat.mul_le_mul_right _ hbound

end Main

end CFSG.YGroups.DCE.B433
