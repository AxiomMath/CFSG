module

public import CFSG.Sporadic.Presentation.Fi22ExactWalks
public import CFSG.Certificates.KernelOrder
public import CFSG.Certificates.CosetTableAction
public import Certificates.Certificate9108
public import Certificates.Certificate9110
public meta import CFSG.Sporadic.Presentation.Fi22ExactWalks
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.Sporadic.Presentation.Fi22Exact

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration

abbrev GG : Type := PG gc W0

abbrev rels0 : Set (FreeGroup (Fin gc)) := {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}

noncomputable def aG : GG := PresentedGroup.of ga

noncomputable def bG : GG := PresentedGroup.of gb

theorem evalWord_replicate_one (g : ℕ → GG) (y k : ℕ) :
    evalWord g (List.replicate k y) = g y ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, evalWord_cons, ih, pow_succ']

theorem gen0_zero : presLetter rels0 0 = aG := presLetter_even rels0 ga
theorem gen0_two : presLetter rels0 2 = bG := presLetter_even rels0 gb
theorem gen0_three : presLetter rels0 3 = bG⁻¹ := presLetter_odd rels0 gb

theorem rel_a2 : aG * aG = 1 := by
  have h : [0, 0] ∈ codes W0 := Certificates.certificate9108.1
  have := evalWord_codes_eq_one h
  rw [evalWord_cons, evalWord_cons, evalWord_nil, mul_one, gen0_zero] at this
  exact this

theorem rel_b13 : bG ^ 13 = 1 := by
  have h : List.replicate 13 2 ∈ codes W0 := Certificates.certificate9108.2.1
  have := evalWord_codes_eq_one h
  rwa [evalWord_replicate_one, gen0_two] at this

theorem rel_ab11 : (aG * bG) ^ 11 = 1 := by
  have h : (List.replicate 11 [0, 2]).flatten ∈ codes W0 := Certificates.certificate9108.2.2.1
  have := evalWord_codes_eq_one h
  rw [evalWord_flatten_replicate, evalWord_cons, evalWord_cons, evalWord_nil, mul_one, gen0_zero,
    gen0_two] at this
  exact this

theorem rel_ab2_21 : (aG * bG ^ 2) ^ 21 = 1 := by
  have h : (List.replicate 21 [0, 2, 2]).flatten ∈ codes W0 :=
    Certificates.certificate9108.2.2.2.1
  have := evalWord_codes_eq_one h
  rw [evalWord_flatten_replicate, evalWord_cons, evalWord_cons, evalWord_cons, evalWord_nil,
    mul_one, gen0_zero, gen0_two] at this
  rw [pow_two]
  exact this

noncomputable def xG (k : ℕ) : GG := (bG ^ k)⁻¹ * aG * bG ^ k

noncomputable def cprod (c : List (Fin 6)) : GG := (c.map fun l => xG l.val).prod

noncomputable def gG (n : ℕ) (c : List (Fin 6)) : GG := bG ^ n * cprod c

theorem evalWord_xW (k : ℕ) : evalWord (presLetter rels0) (xW k) = xG k := by
  unfold xW xG
  rw [evalWord_append', evalWord_replicate_one, evalWord_cons, evalWord_replicate_one, gen0_three,
    gen0_zero, gen0_two, inv_pow]
  simp only [mul_assoc]

theorem evalWord_gW (n : ℕ) (c : List (Fin 6)) :
    evalWord (presLetter rels0) (gW n c) = gG n c := by
  unfold gW gG
  rw [evalWord_append', evalWord_replicate_one, gen0_two]
  congr 1
  induction c with
  | nil => simp [cprod]
  | cons l c ih =>
    rw [List.flatMap_cons, evalWord_append', evalWord_xW, ih]
    simp [cprod]

theorem letters_xW (k : ℕ) : ∀ y ∈ xW k, y < 2 * gc := by
  intro y hy
  simp only [xW, List.mem_append, List.mem_replicate, List.mem_cons] at hy
  rw [gc_eq]
  omega

theorem letters_gW (n : ℕ) (c : List (Fin 6)) : ∀ y ∈ gW n c, y < 2 * gc := by
  intro y hy
  simp only [gW, List.mem_append, List.mem_replicate, List.mem_flatMap] at hy
  rcases hy with ⟨-, rfl⟩ | ⟨l, -, hl⟩
  · rw [gc_eq]; norm_num
  · exact letters_xW _ y hl

theorem conjEq_of_walk {pp : Conj × Conj} (hpp : pp ∈ allPairs) :
    (gG pp.1.1 pp.1.2)⁻¹ * aG * gG pp.1.1 pp.1.2 =
      (gG pp.2.1 pp.2.2)⁻¹ * aG * gG pp.2.1 pp.2.2 := by
  have h := pairs_agree hpp
  rwa [evalWord_gW, evalWord_gW, gen0_zero] at h

theorem lift_conjW (i : Fin 6) (c : List (Fin 6)) :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk (conjW i c)) =
      (cprod c)⁻¹ * xG i.val * cprod c := by
  unfold conjW
  rw [FreeGroup.lift_mk]
  simp only [List.map_append, List.prod_append, List.map_map, List.map_reverse, cprod]
  simp [Function.comp_def, List.prod_inv_reverse]

theorem xG_conj (i : ℕ) (c : List (Fin 6)) :
    (cprod c)⁻¹ * xG i * cprod c = (gG i c)⁻¹ * aG * gG i c := by
  unfold gG xG
  group

theorem lift_qWord (q : Fin 6 × List (Fin 6) × Fin 6 × List (Fin 6)) :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk (qWord q)) =
      (gG q.1.val q.2.1)⁻¹ * aG * gG q.1.val q.2.1 *
        ((gG q.2.2.1.val q.2.2.2)⁻¹ * aG * gG q.2.2.1.val q.2.2.2)⁻¹ := by
  unfold qWord
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv, lift_conjW, lift_conjW,
    xG_conj, xG_conj]

theorem qWord_rel {q : Fin 6 × List (Fin 6) × Fin 6 × List (Fin 6)}
    (h : (gG q.1.val q.2.1)⁻¹ * aG * gG q.1.val q.2.1 =
      (gG q.2.2.1.val q.2.2.2)⁻¹ * aG * gG q.2.2.1.val q.2.2.2) :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk (qWord q)) = 1 := by
  rw [lift_qWord, h]
  exact mul_inv_cancel _

theorem xG_sq (k : ℕ) : xG k * xG k = 1 := by
  have h := rel_a2
  unfold xG
  calc (bG ^ k)⁻¹ * aG * bG ^ k * ((bG ^ k)⁻¹ * aG * bG ^ k)
      = (bG ^ k)⁻¹ * (aG * aG) * bG ^ k := by group
    _ = 1 := by rw [h]; group

theorem qPair_mem_allPairs {q : Fin 6 × List (Fin 6) × Fin 6 × List (Fin 6)} (hq : q ∈ qrels) :
    qPair q ∈ allPairs :=
  List.mem_append_left _ (List.mem_map_of_mem hq)

theorem xPair_mem_allPairs {d : ℕ × Fin 6 × List (Fin 6)} (hd : d ∈ xdefs) :
    xPair d ∈ allPairs :=
  List.mem_append_right _ (List.mem_map_of_mem hd)

theorem hrel_holds :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk},
      FreeGroup.lift (fun j : Fin 6 => xG j.val) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map, wsF, List.mem_append] at hr
  obtain ⟨w, hw', rfl⟩ := hr
  rcases hw' with hw' | hw'
  · simp only [List.mem_finRange, true_and] at hw'
    obtain ⟨i, rfl⟩ := hw'
    rw [FreeGroup.lift_mk]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.cond_true, mul_one]
    exact xG_sq _
  · obtain ⟨q, hq, rfl⟩ := hw'
    exact qWord_rel (conjEq_of_walk (qPair_mem_allPairs hq))

noncomputable def thetaHom :
    PG 6 wsF →* GG :=
  PresentedGroup.toGroup (f := fun j : Fin 6 => xG j.val) hrel_holds

theorem thetaHom_of
    (j : Fin 6) : thetaHom (PresentedGroup.of j) = xG j.val := by
  unfold thetaHom
  rw [PresentedGroup.toGroup.of]

theorem toGroup_mk {α G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (u : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels u) = FreeGroup.lift f u := by
  have h' : (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels) = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro a
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of h
  exact DFunLike.congr_fun h' u

theorem thetaHom_mk
    (u : FreeGroup (Fin 6)) :
    thetaHom (PresentedGroup.mk _ u) = FreeGroup.lift (fun j : Fin 6 => xG j.val) u := by
  unfold thetaHom
  exact toGroup_mk _ u

noncomputable def Pn (n : ℕ) : GG := (aG * bG) ^ n * (bG ^ n)⁻¹

theorem Pn_zero : Pn 0 = 1 := by simp [Pn]

theorem Pn_succ (n : ℕ) : Pn (n + 1) = Pn n * (bG ^ n * aG * (bG ^ n)⁻¹) := by
  unfold Pn
  rw [pow_succ, pow_succ]
  group

theorem cj_xG
    (j k : ℕ) (hjk : j + k = 13) : bG ^ j * aG * (bG ^ j)⁻¹ = xG k := by
  have h : bG ^ k * bG ^ j = 1 := by
    rw [← pow_add, add_comm, hjk]; exact rel_b13
  have h2 : bG ^ j = (bG ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h
  unfold xG
  rw [h2, inv_inv]

theorem xG_zero : xG 0 = aG := by simp [xG]

theorem Pn_eleven :
    Pn 11 = xG 0 * xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 *
    xG 4 * xG 3 := by
  have h1 : Pn 1 = xG 0 := by
    have := Pn_succ 0
    rw [Pn_zero, one_mul] at this
    rw [show (1 : ℕ) = 0 + 1 from rfl, this]
    simp [xG]
  have h2 : Pn 2 = Pn 1 * xG 12 := by
    have := Pn_succ 1
    rw [cj_xG 1 12 rfl] at this; exact this
  have h3 : Pn 3 = Pn 2 * xG 11 := by
    have := Pn_succ 2
    rw [cj_xG 2 11 rfl] at this; exact this
  have h4 : Pn 4 = Pn 3 * xG 10 := by
    have := Pn_succ 3
    rw [cj_xG 3 10 rfl] at this; exact this
  have h5 : Pn 5 = Pn 4 * xG 9 := by
    have := Pn_succ 4
    rw [cj_xG 4 9 rfl] at this; exact this
  have h6 : Pn 6 = Pn 5 * xG 8 := by
    have := Pn_succ 5
    rw [cj_xG 5 8 rfl] at this; exact this
  have h7 : Pn 7 = Pn 6 * xG 7 := by
    have := Pn_succ 6
    rw [cj_xG 6 7 rfl] at this; exact this
  have h8 : Pn 8 = Pn 7 * xG 6 := by
    have := Pn_succ 7
    rw [cj_xG 7 6 rfl] at this; exact this
  have h9 : Pn 9 = Pn 8 * xG 5 := by
    have := Pn_succ 8
    rw [cj_xG 8 5 rfl] at this; exact this
  have h10 : Pn 10 = Pn 9 * xG 4 := by
    have := Pn_succ 9
    rw [cj_xG 9 4 rfl] at this; exact this
  have h11 : Pn 11 = Pn 10 * xG 3 := by
    have := Pn_succ 10
    rw [cj_xG 10 3 rfl] at this; exact this
  rw [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]

theorem Pn_eleven_eq : Pn 11 = (bG ^ 11)⁻¹ := by
  unfold Pn
  rw [rel_ab11, one_mul]

theorem bG_eq : bG = Pn 11 ^ 7 := by
  rw [Pn_eleven_eq, inv_pow, ← pow_mul]
  have h : bG ^ (11 * 7) * bG = 1 := by
    rw [← pow_succ, show 11 * 7 + 1 = 13 * 6 by norm_num, pow_mul, rel_b13, one_pow]
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem xG_eq_conj {d : ℕ × Fin 6 × List (Fin 6)} (hd : d ∈ xdefs) :
    xG d.1 = (cprod d.2.2)⁻¹ * xG d.2.1.val * cprod d.2.2 := by
  have h := conjEq_of_walk (pp := xPair d) (xPair_mem_allPairs hd)
  have e1 : (gG d.1 [])⁻¹ * aG * gG d.1 [] = xG d.1 := by simp [gG, cprod, xG]
  have e2 := xG_conj d.2.1.val d.2.2
  simp only [xPair] at h
  rw [e1] at h
  rw [e2]
  exact h

theorem cprod_mem_range
    (c : List (Fin 6)) : cprod c ∈ thetaHom.range := by
  unfold cprod
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨l, -, rfl⟩ := hx
  exact ⟨PresentedGroup.of l, thetaHom_of l⟩

theorem xG_mem_range
    {k : ℕ} (hk : k ≤ 12) : xG k ∈ thetaHom.range := by
  by_cases h6 : k < 6
  · exact ⟨PresentedGroup.of ⟨k, h6⟩, thetaHom_of ⟨k, h6⟩⟩
  · obtain ⟨d, hd, hdk⟩ := xdefs_exists ⟨k - 6, by omega⟩
    have hk' : k = d.1 := by simp only at hdk; omega
    subst hk'
    rw [xG_eq_conj hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (cprod_mem_range _))
      ⟨PresentedGroup.of d.2.1, thetaHom_of d.2.1⟩) (cprod_mem_range _)

theorem thetaHom_surjective :
    Function.Surjective thetaHom := by
  rw [← MonoidHom.range_eq_top]
  have hPn : Pn 11 ∈ thetaHom.range := by
    have h : Pn 11 = ([0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3].map xG).prod := by
      rw [Pn_eleven]; simp [mul_assoc]
    rw [h]
    apply Subgroup.list_prod_mem
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    refine xG_mem_range ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hb : bG ∈ thetaHom.range := by
    rw [bG_eq]; exact Subgroup.pow_mem _ hPn 7
  have ha : aG ∈ thetaHom.range := by
    rw [← xG_zero]; refine xG_mem_range ?_; norm_num
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hgc : gc = 2 := gc_eq
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · have : i = ga := Fin.ext hi
    rw [this]; exact ha
  · have : i = gb := Fin.ext hi
    rw [this]; exact hb

theorem lift_xhat {k : ℕ} (hk : k ≤ 12) :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk (xhat k)) = xG k := by
  unfold xhat
  split_ifs with h
  · simp [FreeGroup.lift_mk]
  · have hj : k - 6 < 7 := by omega
    have hd := xdefs_getD_mem ⟨k - 6, hj⟩
    have hf := xdefs_fst ⟨k - 6, hj⟩
    simp only at hd hf
    rw [lift_conjW, ← xG_eq_conj hd, hf]
    exact congrArg xG (by omega)

theorem mk_flatten {α : Type*} (L : List (List (α × Bool))) :
    FreeGroup.mk L.flatten = (L.map FreeGroup.mk).prod := by
  induction L with
  | nil => rfl
  | cons u L ih => rw [List.flatten_cons, ← FreeGroup.mul_mk, ih]; simp

theorem lift_Qw :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk Qw) =
      xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 * xG 4 * xG 3 := by
  unfold Qw
  rw [mk_flatten, map_list_prod]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [lift_xhat (k := 12) (by norm_num), lift_xhat (k := 11) (by norm_num),
    lift_xhat (k := 10) (by norm_num), lift_xhat (k := 9) (by norm_num),
    lift_xhat (k := 8) (by norm_num), lift_xhat (k := 7) (by norm_num),
    lift_xhat (k := 6) (by norm_num), lift_xhat (k := 5) (by norm_num),
    lift_xhat (k := 4) (by norm_num), lift_xhat (k := 3) (by norm_num)]
  simp only [mul_assoc]

theorem lift_Pw :
    FreeGroup.lift (fun j : Fin 6 => xG j.val) (FreeGroup.mk Pw) = Pn 11 := by
  unfold Pw
  rw [← FreeGroup.mul_mk, map_mul, lift_Qw, lift_xhat (k := 0) (by norm_num), Pn_eleven]
  simp only [mul_assoc]

theorem Qprod_eq :
    xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 * xG 4 * xG 3 =
    aG * bG ^ 2 := by
  have h := Pn_eleven
  have hb2 : (bG ^ 11)⁻¹ = bG ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]; exact rel_b13
  rw [Pn_eleven_eq, hb2, xG_zero] at h
  calc xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 * xG 4 * xG 3
      = (aG * aG) * (xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 * xG 4 * xG 3) := by
        rw [rel_a2, one_mul]
    _ = aG * (aG * xG 12 * xG 11 * xG 10 * xG 9 * xG 8 * xG 7 * xG 6 * xG 5 * xG 4 * xG 3) := by
        simp only [mul_assoc]
    _ = aG * bG ^ 2 := by rw [← h]

theorem thetaHom_g1 :
    thetaHom (PresentedGroup.mk _ (FreeGroup.mk g1w)) = 1 := by
  rw [thetaHom_mk, g1w, mk_flatten_replicate, map_pow, lift_Pw, Pn_eleven_eq, inv_pow, ← pow_mul,
    show 11 * 91 = 13 * 77 by norm_num, pow_mul, rel_b13, one_pow, inv_one]

theorem thetaHom_g2 :
    thetaHom (PresentedGroup.mk _ (FreeGroup.mk g2w)) = 1 := by
  rw [thetaHom_mk, g2w, mk_flatten_replicate, map_pow, lift_Qw, Qprod_eq]
  exact rel_ab2_21

theorem lift_sign_mk {m : ℕ} (u : List (Fin m × Bool)) :
    FreeGroup.lift (fun _ : Fin m => Multiplicative.ofAdd (1 : ZMod 2)) (FreeGroup.mk u) =
      Multiplicative.ofAdd (u.length : ZMod 2) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨i, b⟩ := x
    have h : FreeGroup.mk ((i, b) :: u) = FreeGroup.mk [(i, b)] * FreeGroup.mk u := rfl
    rw [h, map_mul, ih]
    cases b
    · have h1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
      rw [h1, map_inv, FreeGroup.lift_apply_of, List.length_cons, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      push_cast
      have : (-1 : ZMod 2) = 1 := by decide
      rw [this, add_comm]
    · have h1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      rw [h1, FreeGroup.lift_apply_of, List.length_cons, ← ofAdd_add]
      congr 1
      push_cast
      rw [add_comm]

theorem evenRels : wsF.all (fun w => w.length % 2 == 0) = true := by
  exact Certificates.certificate9108.2.2.2.2.1

noncomputable def signHom : PG 6 wsF →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ : Fin 6 => Multiplicative.ofAdd (1 : ZMod 2)) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_sign_mk]
    have h := (List.all_eq_true.mp evenRels) w hw
    simp only [beq_iff_eq] at h
    have : (w.length : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; omega
    rw [this]; rfl)

theorem signHom_mk (u : List (Fin 6 × Bool)) :
    signHom (PresentedGroup.mk _ (FreeGroup.mk u)) = Multiplicative.ofAdd (u.length : ZMod 2) := by
  unfold signHom
  rw [toGroup_mk, lift_sign_mk]

theorem len_g1w : g1w.length = 11011 := by
  exact Certificates.certificate9108.2.2.2.2.2.1
theorem len_g2w : g2w.length = 2520 := by
  exact Certificates.certificate9108.2.2.2.2.2.2

theorem signHom_g1 :
    signHom (PresentedGroup.mk _ (FreeGroup.mk g1w)) ≠ 1 := by
  rw [signHom_mk, len_g1w]; decide

theorem signHom_g2 :
    signHom (PresentedGroup.mk _ (FreeGroup.mk g2w)) = 1 := by
  rw [signHom_mk, len_g2w]; decide

theorem twelve_mul_card_le
    [Finite (PG 6 wsF)]
    (h6 : 6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}
      (FreeGroup.mk g1w)))
    (h2 : 2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}
      (FreeGroup.mk g2w))) :
    Finite GG ∧ 12 * Nat.card GG ≤ Nat.card (PG 6 wsF) := by
  have hk := twelve_le_card_ker thetaHom signHom thetaHom_g1 thetaHom_g2 signHom_g1 signHom_g2 h6 h2
  exact ⟨Finite.of_surjective _ thetaHom_surjective,
    mul_card_le_of_surjective thetaHom thetaHom_surjective hk⟩

end CFSG.Sporadic.Presentation.Fi22Exact
