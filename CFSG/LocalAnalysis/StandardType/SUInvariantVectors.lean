module

public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.StandardType.SUTransvection

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (aform aform_apply map_aform)

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {k : ℕ}

open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree in
omit [CharP F 2] in
private theorem aform_single_right {n : ℕ} (x : Fin n → F) (i : Fin n) (c : F) :
    aform σ x (Pi.single i c) = σ (x (Fin.rev i)) * c := by
  rw [aform_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [Fin.rev_rev, Pi.single_eq_same]
  · intro a _ ha
    have h : Fin.rev a ≠ i := fun h' => ha (by rw [← Fin.rev_rev a, h'])
    rw [Pi.single_eq_of_ne h, mul_zero]
  · simp

open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree in
omit [CharP F 2] in
private theorem aform_single_left {n : ℕ} (i : Fin n) (c : F) (y : Fin n → F) :
    aform σ (Pi.single i c) y = σ c * y (Fin.rev i) := by
  rw [aform_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro a _ ha
    rw [Pi.single_eq_of_ne ha, map_zero, zero_mul]
  · simp

private theorem eq_of_rev_eq {n : ℕ} {a b : Fin n} (ha : Fin.rev a = a) (hb : Fin.rev b = b) :
    a = b := by
  apply Fin.ext
  have ha' : n - (a.val + 1) = a.val := by
    simpa [Fin.val_rev] using congrArg Fin.val ha
  have hb' : n - (b.val + 1) = b.val := by
    simpa [Fin.val_rev] using congrArg Fin.val hb
  omega

open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree in
private theorem aform_heisenberg_mulVec {n : ℕ} {i o : Fin n} (ho : Fin.rev o = o) {b : F}
    (v : Fin n → F) :
    aform σ v (heisenbergMatrix σ i o 1 b *ᵥ v) =
      aform σ v v + (σ (v (Fin.rev i)) * v o + σ (v o) * v (Fin.rev i)) +
        b * (σ (v (Fin.rev i)) * v (Fin.rev i)) := by
  have hsum : v + Pi.single i (1 * v o) - Pi.single o (σ 1 * v (Fin.rev i)) +
        Pi.single i (b * v (Fin.rev i)) =
      v + (Pi.single i (v o) + Pi.single i (b * v (Fin.rev i)) +
        -Pi.single o (v (Fin.rev i))) := by
    simp only [map_one, one_mul]
    abel
  rw [heisenbergMatrix_mulVec, hsum]
  simp only [aform_add_right, aform_neg_right, aform_single_right, ho]
  rw [CharTwo.neg_eq]
  ring

omit [CharP F 2] in
private theorem heisenbergMatrix_mulVec_sub_single {n : ℕ} {i o : Fin n} {b : F} {v : Fin n → F}
    (hvi : v (Fin.rev i) = 0) :
    heisenbergMatrix σ i o 1 b *ᵥ v - v = Pi.single i (v o) := by
  rw [heisenbergMatrix_mulVec, map_one, one_mul, hvi]
  simp

omit [CharP F 2] in
private theorem exists_mat_rootMatrix (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : F) :
    ∃ g : SU σ n, mat σ n g = rootMatrix σ i j c := by
  refine ⟨rootHom σ hσ hij hi hj (Multiplicative.ofAdd c), ?_⟩
  rw [mat_apply, coe_rootHom]
  simp

omit [CharP F 2] in
private theorem exists_mat_longRootMatrix {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) {c : F}
    (hc : c + σ c = 0) :
    ∃ g : SU σ n, mat σ n g = longRootMatrix i c := by
  refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), ?_⟩
  rw [mat_apply, coe_longRootHom]
  simp

omit [CharP F 2] in
private theorem exists_mat_heisenbergMatrix (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i o : Fin n}
    (hi : i ≠ Fin.rev i) (hio : i ≠ o) (ho : Fin.rev o = o) {a b : F}
    (hab : b + σ b + σ a * a = 0) :
    ∃ g : SU σ n, mat σ n g = heisenbergMatrix σ i o a b := by
  refine ⟨⟨⟨heisenbergMatrix σ i o a b, heisenbergMatrix σ i o (-a) (-b - a * σ a),
      ?_, ?_⟩, det_heisenbergMatrix σ hi hio ho a b,
    heisenbergMatrix_isometry σ hσ hi hio ho hab⟩, ?_⟩
  · rw [heisenbergMatrix_mul σ hi hio ho, map_neg, add_neg_cancel,
      show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero]
  · rw [heisenbergMatrix_mul σ hi hio ho, neg_add_cancel,
      show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]
  · rw [mat_apply]

private theorem heisenberg_coord_zero (hσ : IsUnitaryInvolution σ) {n : ℕ} {i o : Fin n}
    (hio : i ≠ o) (ho : Fin.rev o = o) {b : F} (hb : b + σ b = 1)
    {V : AddSubgroup (Fin n → F)} (hV : ∀ g : SU σ n, ∀ v ∈ V, mat σ n g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v)
    {v : Fin n → F} (hv : v ∈ V) : v (Fin.rev i) = 0 := by
  have hi : i ≠ Fin.rev i := fun h => hio (eq_of_rev_eq h.symm ho)
  have hab : b + σ b + σ (1 : F) * 1 = 0 := by
    rw [map_one, one_mul, hb]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨g, hg⟩ := exists_mat_heisenbergMatrix hσ.invol hi hio ho (a := 1) (b := b) hab
  have hHv : mat σ n g *ᵥ v ∈ V := hV g v hv
  have hfix : aform σ v (mat σ n g *ᵥ v) = σ (aform σ v (mat σ n g *ᵥ v)) := by
    rw [map_aform σ hσ.invol, hVV v hv (mat σ n g *ᵥ v) hHv]
  rw [hg] at hfix
  set N : F := σ (v (Fin.rev i)) * v (Fin.rev i) with hNdef
  set Tr : F := σ (v (Fin.rev i)) * v o + σ (v o) * v (Fin.rev i) with hTrdef
  have hcomp := aform_heisenberg_mulVec (σ := σ) (i := i) (ho := ho) (b := b) v
  have hvv : σ (aform σ v v) = aform σ v v := map_aform σ hσ.invol v v
  have hTr : σ Tr = Tr := by
    rw [hTrdef, map_add, map_mul, map_mul, hσ.invol, hσ.invol]
    ring
  have hN : σ N = N := by
    rw [hNdef, map_mul, hσ.invol]
    ring
  have h1 : aform σ v (heisenbergMatrix σ i o 1 b *ᵥ v) = aform σ v v + Tr + b * N := by
    rw [hcomp, ← hTrdef, ← hNdef]
  have h2 : aform σ v (heisenbergMatrix σ i o 1 b *ᵥ v) =
      aform σ v v + Tr + σ b * N := by
    calc aform σ v (heisenbergMatrix σ i o 1 b *ᵥ v)
        = σ (aform σ v (heisenbergMatrix σ i o 1 b *ᵥ v)) := hfix
      _ = σ (aform σ v v + Tr + b * N) := by rw [h1]
      _ = σ (aform σ v v) + σ Tr + σ (b * N) := by rw [map_add, map_add]
      _ = aform σ v v + Tr + σ b * N := by rw [hvv, hTr, map_mul, hN]
  have hbN : b * N = σ b * N := by
    rw [h1] at h2
    exact add_left_cancel h2
  have hN0 : N = 0 := by
    calc N = 1 * N := (one_mul N).symm
      _ = (b + σ b) * N := by rw [hb]
      _ = b * N + σ b * N := add_mul b (σ b) N
      _ = b * N + b * N := by rw [hbN]
      _ = 0 := CharTwo.add_self_eq_zero _
  by_contra hne
  apply mul_ne_zero ((map_ne_zero σ).mpr hne) hne
  rwa [← hNdef]

omit [CharP F 2] in
private theorem rootMatrix_sub_coord {n : ℕ} {q p : Fin n} (hq' : q ≠ Fin.rev p) (μ : F)
    (v : Fin n → F) :
    (rootMatrix σ q p μ *ᵥ v - v) q = μ * v p := by
  rw [rootMatrix_mulVec]
  simp [Pi.single_eq_of_ne hq']

omit [CharP F 2] in
private theorem longRootMatrix_mulVec_sub_single {n : ℕ} {q : Fin n} (w : Fin n → F) :
    longRootMatrix (Fin.rev q) 1 *ᵥ w - w = Pi.single (Fin.rev q) (w q) := by
  rw [longRootMatrix_mulVec, one_mul, Fin.rev_rev]
  simp

omit [CharP F 2] in
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree in
private theorem aform_rootMatrix_sub_left {n : ℕ} {q p : Fin n} (hq' : q ≠ Fin.rev p)
    (μ : F) (v : Fin n → F) :
    aform σ (rootMatrix σ q p μ *ᵥ v - v) (Pi.single (Fin.rev q) (v p)) =
      σ (μ * v p) * v p := by
  rw [aform_single_right, Fin.rev_rev, rootMatrix_sub_coord hq' μ v]

omit [CharP F 2] in
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree in
private theorem aform_rootMatrix_sub_right {n : ℕ} {q p : Fin n} (hq' : q ≠ Fin.rev p)
    (μ : F) (v : Fin n → F) :
    aform σ (Pi.single (Fin.rev q) (v p)) (rootMatrix σ q p μ *ᵥ v - v) =
      μ * (σ (v p) * v p) := by
  rw [aform_single_left, Fin.rev_rev, rootMatrix_sub_coord hq' μ v]
  ring

private theorem exists_ne_of_rev_ne (hk : 3 ≤ k) {p : Fin k} :
    ∃ q : Fin k, q ≠ p ∧ q ≠ Fin.rev p := by
  by_contra h
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ {p, Fin.rev p} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx : x = p
    · exact Or.inl hx
    · refine Or.inr (by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩)
  have hcard : k ≤ 2 := by
    have h1 : (Finset.univ : Finset (Fin k)).card ≤ ({p, Fin.rev p} : Finset (Fin k)).card :=
      Finset.card_le_card hsub
    have h2 : ({p, Fin.rev p} : Finset (Fin k)).card ≤ 2 := by
      have := Finset.card_insert_le p ({Fin.rev p} : Finset (Fin k))
      simpa using this
    simpa using h1.trans h2
  omega

private theorem even_coord_zero (hσ : IsUnitaryInvolution σ) (heven : Even k) (hk : 3 ≤ k)
    {V : AddSubgroup (Fin k → F)} (hV : ∀ g : SU σ k, ∀ v ∈ V, mat σ k g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v)
    {v : Fin k → F} (hv : v ∈ V) (p : Fin k) : v p = 0 := by
  obtain ⟨μ, hμ⟩ := hσ.exists_ne
  have hp : p ≠ Fin.rev p := (rev_ne_self_of_even heven p).symm
  obtain ⟨q, hqp, hqp'⟩ := exists_ne_of_rev_ne (k := k) hk (p := p)
  have hq : q ≠ Fin.rev q := (rev_ne_self_of_even heven q).symm
  have hq'rev : Fin.rev q ≠ q := rev_ne_self_of_even heven q
  obtain ⟨gμ, hgμ⟩ := exists_mat_rootMatrix hσ.invol hqp hq hp μ
  obtain ⟨g1, hg1⟩ := exists_mat_rootMatrix hσ.invol hqp hq hp 1
  have hc1 : (1 : F) + σ 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨gΛ, hgΛ⟩ := exists_mat_longRootMatrix (σ := σ) (i := Fin.rev q)
    (by simpa using hq'rev) (c := 1) hc1
  set wμ : Fin k → F := mat σ k gμ *ᵥ v - v with hwμdef
  set w1 : Fin k → F := mat σ k g1 *ᵥ v - v with hw1def
  set u : Fin k → F := mat σ k gΛ *ᵥ w1 - w1 with hudef
  have hwμ : wμ ∈ V := AddSubgroup.sub_mem V (hV gμ v hv) hv
  have hw1 : w1 ∈ V := AddSubgroup.sub_mem V (hV g1 v hv) hv
  have hu : u ∈ V := AddSubgroup.sub_mem V (hV gΛ w1 hw1) hw1
  have hu_eq : u = Pi.single (Fin.rev q) (v p) := by
    rw [hudef, hw1def, hgΛ, hg1, longRootMatrix_mulVec_sub_single,
      rootMatrix_sub_coord hqp' 1 v, one_mul]
  have h1 : aform σ wμ u = σ (μ * v p) * v p := by
    rw [hu_eq, hwμdef, hgμ, aform_rootMatrix_sub_left hqp' μ v]
  have h2 : aform σ u wμ = μ * (σ (v p) * v p) := by
    rw [hu_eq, hwμdef, hgμ, aform_rootMatrix_sub_right hqp' μ v]
  have hs : aform σ wμ u = aform σ u wμ := hVV wμ hwμ u hu
  have heq : σ (μ * v p) * v p = μ * (σ (v p) * v p) := by rw [← h1, hs, h2]
  have hμsum : σ μ + μ ≠ 0 := by
    intro h
    exact hμ (by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this)
  have hN : σ (v p) * v p = 0 := by
    have hμN : σ μ * (σ (v p) * v p) = μ * (σ (v p) * v p) := by
      rw [← heq, map_mul]
      ring
    have hzero : (σ μ + μ) * (σ (v p) * v p) = 0 := by
      rw [add_mul, hμN, CharTwo.add_self_eq_zero]
    by_contra hne
    exact mul_ne_zero hμsum hne hzero
  by_contra hp0
  exact mul_ne_zero ((map_ne_zero σ).mpr hp0) hp0 hN

private theorem eq_bot_of_odd (hσ : IsUnitaryInvolution σ) (hodd : ¬ Even k) (hk : 3 ≤ k)
    (V : AddSubgroup (Fin k → F)) (hV : ∀ g : SU σ k, ∀ v ∈ V, mat σ k g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v) : V = ⊥ := by
  obtain ⟨b, hb⟩ := hσ.trace_surj 1 (map_one σ)
  have ho : Fin.rev (midIdx k hodd) = midIdx k hodd := rev_midIdx hodd
  let i0 : Fin k := ⟨0, by omega⟩
  have h0 : i0 ≠ Fin.rev i0 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, Fin.val_rev] at this
    omega
  have h0o : i0 ≠ midIdx k hodd := by
    intro h
    exact h0 (calc i0 = midIdx k hodd := h
      _ = Fin.rev (midIdx k hodd) := ho.symm
      _ = Fin.rev i0 := by rw [h])
  have hsupp : ∀ v ∈ V, ∀ j, j ≠ midIdx k hodd → v j = 0 := by
    intro v hv j hj
    have hio : Fin.rev j ≠ midIdx k hodd := fun h =>
      hj (by rw [← Fin.rev_rev j, h, ho])
    have := heisenberg_coord_zero (σ := σ) hσ (i := Fin.rev j) hio ho hb hV hVV hv
    rwa [Fin.rev_rev] at this
  have hmid : ∀ v ∈ V, v (midIdx k hodd) = 0 := by
    intro v hv
    have hi : i0 ≠ Fin.rev i0 := h0
    have hab : b + σ b + σ (1 : F) * 1 = 0 := by
      rw [map_one, one_mul, hb]
      exact CharTwo.add_self_eq_zero 1
    obtain ⟨g, hg⟩ := exists_mat_heisenbergMatrix hσ.invol hi h0o ho (a := 1) (b := b) hab
    have hw : mat σ k g *ᵥ v - v ∈ V := AddSubgroup.sub_mem V (hV g v hv) hv
    have hw_eq : mat σ k g *ᵥ v - v = Pi.single i0 (v (midIdx k hodd)) := by
      rw [hg, heisenbergMatrix_mulVec_sub_single (i := i0) (o := midIdx k hodd)
        (hsupp v hv (Fin.rev i0) (fun h => h0o (by rw [← Fin.rev_rev i0, h, ho])))]
    have h0v := hsupp (mat σ k g *ᵥ v - v) hw i0 h0o
    rwa [hw_eq, Pi.single_eq_same] at h0v
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
  funext j
  by_cases hj : j = midIdx k hodd
  · subst hj
    exact hmid v hv
  · exact hsupp v hv j hj

private theorem eq_bot_of_even (hσ : IsUnitaryInvolution σ) (heven : Even k) (hk : 3 ≤ k)
    (V : AddSubgroup (Fin k → F)) (hV : ∀ g : SU σ k, ∀ v ∈ V, mat σ k g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v) : V = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
  funext p
  exact even_coord_zero (σ := σ) hσ heven hk hV hVV hv p

theorem eq_bot_of_forall_aform_comm (hσ : IsUnitaryInvolution σ) (hk : 3 ≤ k)
    (V : AddSubgroup (Fin k → F)) (hV : ∀ g : SU σ k, ∀ v ∈ V, mat σ k g *ᵥ v ∈ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v) : V = ⊥ := by
  by_cases heven : Even k
  · exact eq_bot_of_even hσ heven hk V hV hVV
  · exact eq_bot_of_odd hσ heven hk V hV hVV

end CFSG.StandardType.SUTransvection
