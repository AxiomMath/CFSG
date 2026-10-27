module

public import CFSG.Quasithin.Background.Harris.R1.L28Gens
public import CFSG.Quasithin.Background.Harris.R1.L28Borel
public import CFSG.Quasithin.Background.Harris.R1.L28Q4

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.Background.Harris.R1.L28Q4 CFSG.Quasithin.Background.Harris.R1.L28Gens
open D4Vert

theorem gf8_sub_eq_add (x y : GF8) : x - y = x + y := by
  rw [sub_eq_add_neg]
  rfl

@[expose] def toQ (g : Matrix.SpecialLinearGroup (Fin 2) GF8) : Q4 :=
  ⟨g.1 0 0, g.1 0 1, g.1 1 0, g.1 1 1⟩

theorem toQ_mul (g h : Matrix.SpecialLinearGroup (Fin 2) GF8) :
    toQ (g * h) = (toQ g).mul (toQ h) := by
  simp only [toQ, Q4.mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem toQ_inv (g : Matrix.SpecialLinearGroup (Fin 2) GF8) :
    toQ g⁻¹ = (toQ g).adj := by
  unfold toQ Q4.adj
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rfl

theorem toQ_one : toQ 1 = Q4.one := by
  simp [toQ, Q4.one]

theorem toQ_injective : Function.Injective toQ := by
  intro g h hgh
  simp only [toQ, Q4.mk.injEq] at hgh
  obtain ⟨h1, h2, h3, h4⟩ := hgh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem toQ_det (g : Matrix.SpecialLinearGroup (Fin 2) GF8) :
    (toQ g).a * (toQ g).d + (toQ g).b * (toQ g).c = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two, gf8_sub_eq_add] at h
  exact h

theorem toQ_surj (q : Q4) (hq : q.a * q.d + q.b * q.c = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) GF8, toQ g = q := by
  refine ⟨⟨!![q.a, q.b; q.c, q.d], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of, gf8_sub_eq_add]
    exact hq
  · cases q
    rfl

theorem foldl_toQ (g : Fin 2 → Matrix.SpecialLinearGroup (Fin 2) GF8) (w : List (Fin 2 × Bool))
    (x : Matrix.SpecialLinearGroup (Fin 2) GF8) :
    toQ (x * (w.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod) =
      w.foldl (fun acc p => acc.mul (if p.2 then toQ (g p.1) else (toQ (g p.1)).adj)) (toQ x) := by
  induction w generalizing x with
  | nil => simp
  | cons p w ih =>
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih, List.foldl_cons]
    congr 1
    obtain ⟨i, b⟩ := p
    cases b <;> simp [toQ_mul, toQ_inv]

theorem toQ_evalWord (g : Fin 2 → Matrix.SpecialLinearGroup (Fin 2) GF8) (w : List (Fin 2 × Bool)) :
    toQ (evalWord g w) = wordQ (fun i => toQ (g i)) w := by
  have h := foldl_toQ g w 1
  rw [one_mul, toQ_one] at h
  exact h

theorem evalWord_mem {X : Type*} [Group X] (H : Subgroup X) (g : Fin 2 → X) (hg : ∀ i, g i ∈ H)
    (w : List (Fin 2 × Bool)) : evalWord g w ∈ H := by
  unfold evalWord
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact hg _
  · exact H.inv_mem (hg _)

@[expose] def bSub : Subgroup (Matrix.SpecialLinearGroup (Fin 2) GF8) where
  carrier := {g | toQ g ∈ bQ}
  mul_mem' {g h} hg hh := by
    show toQ (g * h) ∈ bQ
    rw [toQ_mul]
    exact bQ_mul _ hg _ hh
  one_mem' := by
    show toQ 1 ∈ bQ
    rw [toQ_one]
    exact bQ_one
  inv_mem' {g} hg := by
    show toQ g⁻¹ ∈ bQ
    rw [toQ_inv]
    exact bQ_adj _ hg

@[expose] def e0Sub : Subgroup (Matrix.SpecialLinearGroup (Fin 2) GF8) where
  carrier := {g | toQ g ∈ eQ}
  mul_mem' {g h} hg hh := by
    show toQ (g * h) ∈ eQ
    rw [toQ_mul]
    exact eQ_mul _ hg _ hh
  one_mem' := by
    show toQ 1 ∈ eQ
    rw [toQ_one]
    exact one_mem_eQ
  inv_mem' {g} hg := by
    show toQ g⁻¹ ∈ eQ
    rw [toQ_inv]
    exact eQ_adj _ hg

theorem l28Borel_gen_eq : l28Borel gA gB = bSub := by
  have hv : (fun i => toQ (![gA, gB] i)) = ![gAq, gBq] := by
    funext i
    fin_cases i <;> rfl
  have hu : toQ (evalWord ![gA, gB] D4Vert.l28U) = uQ := by
    rw [toQ_evalWord, hv]
    rfl
  have hc : toQ (evalWord ![gA, gB] D4Vert.l28C) = cQ := by
    rw [toQ_evalWord, hv]
    rfl
  apply le_antisymm
  · unfold l28Borel
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · show toQ _ ∈ bQ
      rw [hu]
      exact bQ_u
    · show toQ _ ∈ bQ
      rw [hc]
      exact bQ_c
  · intro g hg
    have hg' : toQ g ∈ bTabQ.map Prod.fst := hg
    obtain ⟨p, hp, hpq⟩ := List.mem_map.1 hg'
    have hv2 : (fun i => toQ (![evalWord ![gA, gB] D4Vert.l28U,
        evalWord ![gA, gB] D4Vert.l28C] i)) = ![uQ, cQ] := by
      funext i
      fin_cases i
      · exact hu
      · exact hc
    have hmem : evalWord ![evalWord ![gA, gB] D4Vert.l28U, evalWord ![gA, gB] D4Vert.l28C] p.2 ∈
        l28Borel gA gB := by
      apply evalWord_mem
      intro i
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have heq : evalWord ![evalWord ![gA, gB] D4Vert.l28U, evalWord ![gA, gB] D4Vert.l28C] p.2 = g := by
      apply toQ_injective
      rw [toQ_evalWord, hv2]
      exact (bTabQ_words p hp).trans hpq
    rw [← heq]
    exact hmem

theorem bQ_det : ∀ q ∈ bQ, q.a * q.d + q.b * q.c = 1 := by decide +kernel

theorem eQ_det : ∀ q ∈ eQ, q.a * q.d + q.b * q.c = 1 := by decide +kernel

theorem natCard_eq_length (l : List Q4) (hl : l.Nodup)
    (hdet : ∀ q ∈ l, q.a * q.d + q.b * q.c = 1)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) GF8)) (hH : ∀ g, g ∈ H ↔ toQ g ∈ l) :
    Nat.card H = l.length := by
  let f : H → {q : Q4 // q ∈ l} := fun g => ⟨toQ g.1, (hH g.1).1 g.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g h hgh
      apply Subtype.ext
      apply toQ_injective
      exact congrArg Subtype.val hgh
    · intro q
      obtain ⟨g, hg⟩ := toQ_surj q.1 (hdet q.1 q.2)
      exact ⟨⟨g, (hH g).2 (by rw [hg]; exact q.2)⟩, Subtype.ext hg⟩
  have e2 : Nat.card {q : Q4 // q ∈ l} = l.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun q => List.mem_toFinset.symm)
  calc Nat.card H = Nat.card {q : Q4 // q ∈ l} := Nat.card_congr (Equiv.ofBijective f hf)
    _ = l.toFinset.card := e2
    _ = l.length := List.toFinset_card_of_nodup hl

theorem card_bSub : Nat.card bSub = 56 := by
  rw [natCard_eq_length bQ bQ_nodup bQ_det bSub (fun _ => Iff.rfl), bQ_length]

theorem card_e0Sub : Nat.card e0Sub = 8 := by
  rw [natCard_eq_length eQ eQ_nodup eQ_det e0Sub (fun _ => Iff.rfl), eQ_length]

theorem toQ_gA : toQ gA = gAq := rfl

theorem toQ_gB : toQ gB = gBq := rfl

theorem toQ_gens : (fun i => toQ (![gA, gB] i)) = ![gAq, gBq] := by
  funext i
  fin_cases i <;> rfl

theorem toQ_word (w : List (Fin 2 × Bool)) :
    toQ (evalWord ![gA, gB] w) = wordQ ![gAq, gBq] w := by
  rw [toQ_evalWord, toQ_gens]

theorem normalizer_e0Sub :
    Subgroup.normalizer (e0Sub : Set (Matrix.SpecialLinearGroup (Fin 2) GF8)) = bSub := by
  have hP : ∀ h ∈ bSub, ∀ n ∈ e0Sub, h * n * h⁻¹ ∈ e0Sub := by
    intro h hh n hn
    show toQ (h * n * h⁻¹) ∈ eQ
    rw [toQ_mul, toQ_mul, toQ_inv]
    exact eQ_normal (toQ h) hh (toQ n) hn
  ext g
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    show toQ g ∈ bQ
    refine normaliser_eQ (toQ g).a (allG_mem _) (toQ g).b (allG_mem _) (toQ g).c (allG_mem _)
      (toQ g).d (allG_mem _) (toQ_det g) ?_
    intro e he
    obtain ⟨n, hn⟩ := toQ_surj e (eQ_det e he)
    have hnS : n ∈ e0Sub := by
      show toQ n ∈ eQ
      rw [hn]
      exact he
    have h3 : toQ (g * n * g⁻¹) ∈ eQ := (hg n).1 hnS
    rw [toQ_mul, toQ_mul, toQ_inv, hn] at h3
    exact h3
  · intro hg n
    constructor
    · intro hn
      exact hP g hg n hn
    · intro hn
      have hinv : g⁻¹ ∈ bSub := bSub.inv_mem hg
      have h4 := hP g⁻¹ hinv _ hn
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [e] at h4
      exact h4

theorem phi_eq_one {g : Matrix.SpecialLinearGroup (Fin 2) GF8} (h : phi g = 1) : g = 1 := by
  rw [phi_apply] at h
  have h1 : (QuotientGroup.mk g : Matrix.SpecialLinearGroup (Fin 2) GF8 ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) GF8)) = 1 := by
    have := congrArg psiIso.symm h
    rw [MulEquiv.symm_apply_apply, map_one] at this
    exact this
  have hc : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) GF8) :=
    (QuotientGroup.eq_one_iff g).1 h1
  have hcen := Subgroup.mem_center_iff.1 hc
  have hA : (toQ g).mul gAq = gAq.mul (toQ g) := by
    have := congrArg toQ (hcen gA)
    rw [toQ_mul, toQ_mul, toQ_gA] at this
    exact this.symm
  have hB : (toQ g).mul gBq = gBq.mul (toQ g) := by
    have := congrArg toQ (hcen gB)
    rw [toQ_mul, toQ_mul, toQ_gB] at this
    exact this.symm
  have hcomm := commute_central (toQ g).a (allG_mem _) (toQ g).b (allG_mem _) (toQ g).c
    (allG_mem _) (toQ g).d (allG_mem _) (toQ_det g) hA hB
  apply toQ_injective
  rw [toQ_one]
  exact hcomm

theorem phi_inj : Function.Injective phi :=
  (injective_iff_map_eq_one phi).2 fun _ h => phi_eq_one h

theorem phi_bij : Function.Bijective phi := ⟨phi_inj, phi_surj⟩

theorem evalWord_phi (w : List (Fin 2 × Bool)) :
    evalWord ![phi gA, phi gB] w = phi (evalWord ![gA, gB] w) := by
  unfold evalWord
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact (phi_vec p).symm

theorem l28Borel_phi : l28Borel (phi gA) (phi gB) = (l28Borel gA gB).map phi := by
  unfold l28Borel
  rw [MonoidHom.map_closure, Set.image_pair, evalWord_phi, evalWord_phi]

theorem hcos : ∀ i j : Fin 9, i ≠ j →
    (evalWord ![gA, gB] (D4Vert.l28H.getD i.val []))⁻¹ *
      evalWord ![gA, gB] (D4Vert.l28H.getD j.val []) ∉ bSub := by
  intro i j hij h
  have h2 : toQ ((evalWord ![gA, gB] (D4Vert.l28H.getD i.val []))⁻¹ *
      evalWord ![gA, gB] (D4Vert.l28H.getD j.val [])) ∈ bQ := h
  rw [toQ_mul, toQ_inv, toQ_word, toQ_word] at h2
  exact hQ_coset_idx i j hij h2

theorem l28BorelModel_holds : L28BorelModel := by
  refine ⟨phi gA, phi gB, fun r hr => ?_, closure_top, ?_, ⟨e0Sub.map phi, ?_, ?_⟩, ?_, ?_⟩
  · unfold evalWord
    exact rels_phi r hr
  · rw [l28Borel_phi, Subgroup.card_map_of_injective phi_inj, l28Borel_gen_eq, card_bSub]
  · rw [Subgroup.card_map_of_injective phi_inj, card_e0Sub]
  · rw [← Subgroup.map_normalizer_eq_of_bijective e0Sub phi_bij, normalizer_e0Sub,
      l28Borel_phi, l28Borel_gen_eq]
  · rw [l28Borel_phi, Subgroup.mem_map_iff_mem phi_inj, l28Borel_gen_eq]
    intro h
    have h' : toQ gA ∈ bQ := h
    rw [toQ_gA] at h'
    exact gAq_not_mem h'
  · intro i j hij
    rw [evalWord_phi, evalWord_phi, ← map_inv phi, ← map_mul phi, l28Borel_phi,
      Subgroup.mem_map_iff_mem phi_inj, l28Borel_gen_eq]
    exact hcos i j hij

end CFSG.Quasithin.Background.Harris.R1
