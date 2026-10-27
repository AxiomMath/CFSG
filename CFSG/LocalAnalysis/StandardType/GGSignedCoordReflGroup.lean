module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType

open SpCoord
open Multiplicative

private def pSwap {n : ℕ} (p : ℕ) (a b : Fin n) : MulAut (Fin n → Multiplicative (ZMod p)) :=
  permAut (Equiv.swap a b)

private def nSwap {n : ℕ} (p : ℕ) (a b : Fin n) : MulAut (Fin n → Multiplicative (ZMod p)) :=
  sgnAut a * sgnAut b * pSwap p a b

private def tw {n : ℕ} (p : ℕ) (a b i : Fin n) : ZMod p := if i = a ∨ i = b then -1 else 1

private def diagTw {n : ℕ} (p : ℕ) (a b : Fin n) :
    MulAut (Fin n → Multiplicative (ZMod p)) :=
  diagAut (tw p a b) (fun i => by rw [tw]; by_cases h : i = a ∨ i = b <;> simp [h])

private lemma pSwap_apply {n p : ℕ} (a b : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    pSwap p a b f i = f (Equiv.swap a b i) := by
  rw [pSwap, permAut_apply, Function.comp_apply, Equiv.swap_inv]

private lemma nSwap_apply {n p : ℕ} {a b : Fin n} (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    nSwap p a b f i = if i = a then (f b)⁻¹ else if i = b then (f a)⁻¹ else f i := by
  rw [nSwap, pSwap, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply, sgnAut_apply,
    SpCoord.permAut_apply]
  simp only [Function.update_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hia : i = a
  · simp only [if_pos hia, if_neg hab, Equiv.swap_apply_left]
  · by_cases hib : i = b
    · simp only [if_neg hia, if_pos hib, Equiv.swap_apply_right]
    · simp only [if_neg hia, if_neg hib, Equiv.swap_apply_of_ne_of_ne hia hib]

private lemma pSwap_mulSingle {n p : ℕ} (a b i : Fin n) (c : ZMod p) :
    pSwap p a b (Pi.mulSingle i (Multiplicative.ofAdd c) :
      Fin n → Multiplicative (ZMod p)) =
      Pi.mulSingle (Equiv.swap a b i) (Multiplicative.ofAdd c) := by
  rw [pSwap, permAut_mulSingle]

private lemma tw_self {n p : ℕ} (a b i : Fin n) : tw p a b i * tw p a b i = 1 := by
  rw [tw]
  by_cases h : i = a ∨ i = b <;> simp [h]

private lemma tw_invariant {n p : ℕ} (a b i : Fin n) :
    tw p a b (Equiv.swap a b i) = tw p a b i := by
  by_cases hia : i = a
  · rw [hia, Equiv.swap_apply_left]; simp [tw]
  · by_cases hib : i = b
    · rw [hib, Equiv.swap_apply_right]; simp [tw]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

private lemma diagTw_eq_sgn_mul {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    diagTw p a b = sgnAut a * sgnAut b := by
  refine MulEquiv.ext fun f => funext fun i => ?_
  rw [MulAut.mul_apply, diagTw, diagAut_apply, sgnAut_apply, sgnAut_apply]
  simp only [Function.update_apply]
  by_cases hia : i = a
  · subst hia
    simp_all [tw]
  · by_cases hib : i = b
    · subst hib
      simp_all [tw]
    · simp_all [tw]

private lemma nSwap_eq_diagTw {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    nSwap p a b = diagTw p a b * pSwap p a b := by
  rw [nSwap, diagTw_eq_sgn_mul hab]

private lemma nSwap_mulSingle {n p : ℕ} {a b : Fin n} (hab : a ≠ b) (i : Fin n) (c : ZMod p) :
    nSwap p a b (Pi.mulSingle i (Multiplicative.ofAdd c) :
      Fin n → Multiplicative (ZMod p)) =
      Pi.mulSingle (Equiv.swap a b i) (Multiplicative.ofAdd (tw p a b i * c)) := by
  rw [nSwap_eq_diagTw hab, MulAut.mul_apply, pSwap_mulSingle, diagTw, diagAut_mulSingle,
    tw_invariant]

private lemma mulAut_ext_basis {n p : ℕ} [NeZero p]
    {u v : MulAut (Fin n → Multiplicative (ZMod p))}
    (h : ∀ i : Fin n, u (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      v (Pi.mulSingle i (Multiplicative.ofAdd 1))) : u = v := by
  have h' : u.toMonoidHom = v.toMonoidHom := by
    refine hom_ext_mulSingle fun i => ?_
    exact h i
  exact MulEquiv.ext fun f =>
    congrArg (fun F : (Fin n → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) =>
      F f) h'

private lemma mulAut_mul_self_eq_one_of_basis {n p : ℕ} [NeZero p]
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (h : ∀ i : Fin n, u (u (Pi.mulSingle i (Multiplicative.ofAdd 1))) =
      Pi.mulSingle i (Multiplicative.ofAdd 1)) : u * u = 1 := by
  refine mulAut_ext_basis fun i => ?_
  rw [MulAut.mul_apply]
  exact h i

private lemma sgnAut_mul_self {n p : ℕ} (i : Fin n) :
    (sgnAut i : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i = 1 := by
  rw [← sq]
  exact sgnAut_sq i

private lemma sgnAut_inv {n p : ℕ} (i : Fin n) :
    (sgnAut i : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut i := by
  rw [inv_eq_iff_mul_eq_one]
  exact sgnAut_mul_self i

private lemma pSwap_mul_self {n p : ℕ} (a b : Fin n) : pSwap p a b * pSwap p a b = 1 := by
  rw [pSwap, ← sq]
  exact permAut_swap_sq a b

private lemma pSwap_inv {n p : ℕ} (a b : Fin n) :
    (pSwap p a b : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = pSwap p a b := by
  rw [inv_eq_iff_mul_eq_one]
  exact pSwap_mul_self a b

private lemma pSwap_comm {n p : ℕ} (a b : Fin n) : pSwap p a b = pSwap p b a := by
  rw [pSwap, pSwap, Equiv.swap_comm]

private lemma nSwap_comm {n p : ℕ} (a b : Fin n) : nSwap p a b = nSwap p b a := by
  rw [nSwap, nSwap, pSwap_comm, sgnAut_mul_comm]

private lemma nSwap_mul_self {n p : ℕ} [NeZero p] {a b : Fin n} (hab : a ≠ b) :
    nSwap p a b * nSwap p a b = 1 := by
  refine mulAut_mul_self_eq_one_of_basis fun m => ?_
  rw [nSwap_mulSingle hab, nSwap_mulSingle hab, tw_invariant,
    show Equiv.swap a b (Equiv.swap a b m) = m from Equiv.swap_apply_self a b m,
    Pi.mulSingle_inj]
  simp only [mul_one, tw_self]

private lemma nSwap_inv {n p : ℕ} [NeZero p] {a b : Fin n} (hab : a ≠ b) :
    (nSwap p a b : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = nSwap p a b := by
  rw [inv_eq_iff_mul_eq_one]
  exact nSwap_mul_self hab

private lemma permAut_mul {n p : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permAut (σ * τ) = (permAut σ : MulAut (Fin n → Multiplicative (ZMod p))) * permAut τ := by
  refine MulEquiv.ext fun f => ?_
  rw [MulAut.mul_apply, permAut_apply, permAut_apply, permAut_apply]
  rfl

private lemma spData_pSwap {n p : ℕ} (a b : Fin n) :
    ∀ (f : Fin n → Multiplicative (ZMod p)) (i : Fin n),
      toAdd (pSwap p a b f (Equiv.swap a b i)) = (1 : ZMod p) * toAdd (f i) := by
  intro f i
  rw [pSwap_apply, Equiv.swap_apply_self, one_mul]

private lemma spData_nSwap {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ∀ (f : Fin n → Multiplicative (ZMod p)) (i : Fin n),
      toAdd (nSwap p a b f (Equiv.swap a b i)) = tw p a b i * toAdd (f i) := by
  intro f i
  rw [nSwap_apply hab]
  rcases eq_or_ne i a with rfl | hia
  · rw [Equiv.swap_apply_left, if_neg (Ne.symm hab), if_pos rfl, toAdd_inv, tw,
      if_pos (Or.inl rfl)]
    ring
  · rcases eq_or_ne i b with rfl | hib
    · rw [Equiv.swap_apply_right, if_pos rfl, toAdd_inv, tw, if_pos (Or.inr rfl)]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, if_neg hia, if_neg hib, tw,
        if_neg (fun h => h.elim hia hib)]
      ring

private lemma pSwap_mul_sgnAut {n p : ℕ} {a b : Fin n} (i : Fin n) :
    (pSwap p a b : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i =
      sgnAut (Equiv.swap a b i) * pSwap p a b :=
  IsSignedPerm.mul_sgnAut (spData_pSwap a b) i

private lemma nSwap_mul_sgnAut {n p : ℕ} {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    (nSwap p a b : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i =
      sgnAut (Equiv.swap a b i) * nSwap p a b :=
  IsSignedPerm.mul_sgnAut (spData_nSwap hab) i

private lemma pSwap_conj_sgn {n p : ℕ} (a b i : Fin n) :
    pSwap p a b * sgnAut i * pSwap p a b = sgnAut (Equiv.swap a b i) := by
  have h := pSwap_mul_sgnAut (p := p) (a := a) (b := b) i
  calc pSwap p a b * sgnAut i * pSwap p a b
      = (sgnAut (Equiv.swap a b i) * pSwap p a b) * pSwap p a b := by rw [h]
    _ = sgnAut (Equiv.swap a b i) * (pSwap p a b * pSwap p a b) := by rw [mul_assoc]
    _ = sgnAut (Equiv.swap a b i) := by rw [pSwap_mul_self, mul_one]

private lemma nSwap_conj_sgn {n p : ℕ} [NeZero p] {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    nSwap p a b * sgnAut i * nSwap p a b = sgnAut (Equiv.swap a b i) := by
  have h := nSwap_mul_sgnAut (p := p) hab i
  calc nSwap p a b * sgnAut i * nSwap p a b
      = (sgnAut (Equiv.swap a b i) * nSwap p a b) * nSwap p a b := by rw [h]
    _ = sgnAut (Equiv.swap a b i) * (nSwap p a b * nSwap p a b) := by rw [mul_assoc]
    _ = sgnAut (Equiv.swap a b i) := by rw [nSwap_mul_self (p := p) hab, mul_one]

private lemma pSwap_conj_sgn_conj {n p : ℕ} (a b i : Fin n) :
    MulAut.conj (pSwap p a b) (sgnAut i) = sgnAut (Equiv.swap a b i) := by
  rw [MulAut.conj_apply, pSwap_inv, pSwap_conj_sgn]

private lemma conj_pSwap_pSwap_conj {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (_hbc : b ≠ c)
    (hac : a ≠ c) :
    MulAut.conj (pSwap p b c) (pSwap p a b) = pSwap p a c := by
  rw [MulAut.conj_apply, pSwap_inv]
  rw [pSwap, pSwap, pSwap, ← permAut_mul, ← permAut_mul,
    Equiv.swap_mul_swap_mul_swap hab hac, Equiv.swap_comm]

private lemma conj_pp {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    pSwap p b c * pSwap p a b * pSwap p b c = pSwap p a c := by
  have h := conj_pSwap_pSwap_conj (p := p) hab hbc hac
  rwa [MulAut.conj_apply, pSwap_inv] at h

private lemma sgn_conj_sgn_conj {n p : ℕ} (i j : Fin n) :
    MulAut.conj (sgnAut (p := p) i) (sgnAut j) = sgnAut j := by
  rw [MulAut.conj_apply, sgnAut_inv]
  calc sgnAut (p := p) i * sgnAut j * sgnAut i =
        sgnAut j * (sgnAut (p := p) i * sgnAut i) := by
        rw [sgnAut_mul_comm i j]; group
    _ = sgnAut j := by rw [sgnAut_mul_self, mul_one]

private lemma sgn_conj_pSwap_of_ne {n p : ℕ} {i a b : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) :
    sgnAut i * pSwap p a b * sgnAut i = pSwap p a b := by
  have h := pSwap_conj_sgn (p := p) a b i
  rw [show Equiv.swap a b i = i from Equiv.swap_apply_of_ne_of_ne hia hib] at h
  have h2 : pSwap p a b * sgnAut i = sgnAut i * pSwap p a b := by
    have h' := congrArg (· * pSwap p a b) h
    simpa [mul_assoc, pSwap_mul_self] using h'
  calc sgnAut i * pSwap p a b * sgnAut i
      = sgnAut i * (pSwap p a b * sgnAut i) := by rw [mul_assoc]
    _ = sgnAut i * (sgnAut i * pSwap p a b) := by rw [h2]
    _ = (sgnAut i * sgnAut i) * pSwap p a b := by rw [mul_assoc]
    _ = pSwap p a b := by rw [sgnAut_mul_self, one_mul]

private lemma sgn_conj_pSwap_left {n p : ℕ} {a b : Fin n} (_hab : a ≠ b) :
    sgnAut a * pSwap p a b * sgnAut a = nSwap p a b := by
  have h2 : pSwap p a b * sgnAut a = sgnAut b * pSwap p a b := by
    have h := pSwap_mul_sgnAut (p := p) (a := a) (b := b) a
    rwa [show Equiv.swap a b a = b from Equiv.swap_apply_left a b] at h
  calc sgnAut a * pSwap p a b * sgnAut a
      = sgnAut a * (pSwap p a b * sgnAut a) := by rw [mul_assoc]
    _ = sgnAut a * (sgnAut b * pSwap p a b) := by rw [h2]
    _ = nSwap p a b := by rw [nSwap, mul_assoc]

private lemma sgn_conj_pSwap_right {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    sgnAut b * pSwap p a b * sgnAut b = nSwap p a b := by
  have h := sgn_conj_pSwap_left (p := p) (a := b) (b := a) (Ne.symm hab)
  rwa [pSwap_comm, nSwap_comm] at h

private lemma sgn_conj_nSwap_left {n p : ℕ} {a b : Fin n} (_hab : a ≠ b) :
    sgnAut a * nSwap p a b * sgnAut a = pSwap p a b := by
  have h2 : pSwap p a b * sgnAut a = sgnAut b * pSwap p a b := by
    have h := pSwap_mul_sgnAut (p := p) (a := a) (b := b) a
    rwa [show Equiv.swap a b a = b from Equiv.swap_apply_left a b] at h
  calc sgnAut a * nSwap p a b * sgnAut a
      = (sgnAut a * sgnAut a) * sgnAut b * (pSwap p a b * sgnAut a) := by
        rw [nSwap]; group
    _ = (sgnAut a * sgnAut a) * sgnAut b * (sgnAut b * pSwap p a b) := by rw [h2]
    _ = (sgnAut a * sgnAut a) * (sgnAut b * sgnAut b) * pSwap p a b := by group
    _ = pSwap p a b := by rw [sgnAut_mul_self, sgnAut_mul_self, one_mul, one_mul]

private lemma sgn_conj_nSwap_right {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    sgnAut b * nSwap p a b * sgnAut b = pSwap p a b := by
  have h := sgn_conj_nSwap_left (p := p) (a := b) (b := a) (Ne.symm hab)
  rwa [nSwap_comm, pSwap_comm] at h

private lemma sgn_conj_pSwap_of_ne_conj {n p : ℕ} {i a b : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) :
    MulAut.conj (sgnAut i) (pSwap p a b) = pSwap p a b := by
  rw [MulAut.conj_apply, sgnAut_inv, sgn_conj_pSwap_of_ne hia hib]

private lemma sgn_conj_pSwap_right_conj {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    MulAut.conj (sgnAut b) (pSwap p a b) = nSwap p a b := by
  rw [MulAut.conj_apply, sgnAut_inv, sgn_conj_pSwap_right hab]

private lemma sgn_conj_nSwap_right_conj {n p : ℕ} {a b : Fin n} (hab : a ≠ b) :
    MulAut.conj (sgnAut b) (nSwap p a b) = pSwap p a b := by
  rw [MulAut.conj_apply, sgnAut_inv, sgn_conj_nSwap_right hab]

private lemma sgn_conj_nSwap_of_ne_conj {n p : ℕ} {i a b : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) :
    MulAut.conj (sgnAut i) (nSwap p a b) = nSwap p a b := by
  rw [nSwap, map_mul, map_mul, sgn_conj_sgn_conj, sgn_conj_sgn_conj,
    sgn_conj_pSwap_of_ne_conj hia hib]

private lemma conj_pn_conj {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    MulAut.conj (pSwap p b c) (nSwap p a b) = nSwap p a c := by
  rw [nSwap, map_mul, map_mul, pSwap_conj_sgn_conj, pSwap_conj_sgn_conj,
    conj_pSwap_pSwap_conj hab hbc hac]
  rw [show Equiv.swap b c a = a from Equiv.swap_apply_of_ne_of_ne hab hac,
    show Equiv.swap b c b = c from Equiv.swap_apply_left b c]
  rw [nSwap]

private lemma conj_np_conj {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    MulAut.conj (nSwap p b c) (pSwap p a b) = nSwap p a c := by
  have hn : MulAut.conj (nSwap p b c) = MulAut.conj (sgnAut b) * MulAut.conj (sgnAut c) *
      MulAut.conj (pSwap p b c) := by
    rw [nSwap, map_mul, map_mul]
  rw [hn, MulAut.mul_apply, MulAut.mul_apply, conj_pSwap_pSwap_conj hab hbc hac,
    sgn_conj_pSwap_right_conj (a := a) (b := c) hac,
    sgn_conj_nSwap_of_ne_conj (i := b) (Ne.symm hab) hbc]

private lemma conj_nn_conj {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    MulAut.conj (nSwap p b c) (nSwap p a b) = pSwap p a c := by
  have hn : MulAut.conj (nSwap p b c) = MulAut.conj (sgnAut b) * MulAut.conj (sgnAut c) *
      MulAut.conj (pSwap p b c) := by
    rw [nSwap, map_mul, map_mul]
  rw [hn, MulAut.mul_apply, MulAut.mul_apply, conj_pn_conj hab hbc hac,
    sgn_conj_nSwap_right_conj (a := a) (b := c) hac,
    sgn_conj_pSwap_of_ne_conj (i := b) (Ne.symm hab) hbc]

private lemma conj_pn {n p : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    pSwap p b c * nSwap p a b * pSwap p b c = nSwap p a c := by
  have h := conj_pn_conj (p := p) hab hbc hac
  rwa [MulAut.conj_apply, pSwap_inv] at h

private lemma conj_np {n p : ℕ} [NeZero p] {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    nSwap p b c * pSwap p a b * nSwap p b c = nSwap p a c := by
  have h := conj_np_conj (p := p) hab hbc hac
  rwa [MulAut.conj_apply, nSwap_inv (p := p) hbc] at h

private lemma conj_nn {n p : ℕ} [NeZero p] {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    nSwap p b c * nSwap p a b * nSwap p b c = pSwap p a c := by
  have h := conj_nn_conj (p := p) hab hbc hac
  rwa [MulAut.conj_apply, nSwap_inv (p := p) hbc] at h

private lemma diagAut_mul_self {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) :
    diagAut d hd * diagAut d hd = 1 := by
  refine mulAut_mul_self_eq_one_of_basis fun m => ?_
  rw [diagAut_mulSingle, diagAut_mulSingle, Pi.mulSingle_inj, ← mul_assoc, hd m, one_mul]

private lemma diagAut_inv {n p : ℕ} [NeZero p] {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1) :
    (diagAut d hd : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = diagAut d hd := by
  rw [inv_eq_iff_mul_eq_one]
  exact diagAut_mul_self hd

private lemma diag_conj_pSwap_of_mul_eq_one {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (h : d a * d b = 1) :
    diagAut d hd * pSwap p a b * (diagAut d hd)⁻¹ = pSwap p a b := by
  rw [diagAut_inv]
  refine mulAut_ext_basis fun m => ?_
  simp only [MulAut.mul_apply, pSwap_mulSingle, diagAut_mulSingle]
  by_cases hma : m = a
  · rw [hma, Equiv.swap_apply_left, Pi.mulSingle_inj, mul_one, mul_comm (d b) (d a), h]
  · by_cases hmb : m = b
    · rw [hmb, Equiv.swap_apply_right, Pi.mulSingle_inj, mul_one, h]
    · rw [show Equiv.swap a b m = m from Equiv.swap_apply_of_ne_of_ne hma hmb,
        Pi.mulSingle_inj, mul_one, hd m]

private lemma diag_conj_pSwap_of_mul_eq_neg_one {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (h : d a * d b = -1) :
    diagAut d hd * pSwap p a b * (diagAut d hd)⁻¹ = nSwap p a b := by
  rw [diagAut_inv]
  refine mulAut_ext_basis fun m => ?_
  simp only [MulAut.mul_apply, pSwap_mulSingle, diagAut_mulSingle,
    nSwap_mulSingle (p := p) hab]
  by_cases hma : m = a
  · rw [hma, Equiv.swap_apply_left, Pi.mulSingle_inj, mul_one, mul_comm (d b) (d a), h,
      show tw p a b a = -1 by simp [tw], mul_one]
  · by_cases hmb : m = b
    · rw [hmb, Equiv.swap_apply_right, Pi.mulSingle_inj, mul_one, h,
        show tw p a b b = -1 by simp [tw], mul_one]
    · rw [show Equiv.swap a b m = m from Equiv.swap_apply_of_ne_of_ne hma hmb,
        Pi.mulSingle_inj, mul_one, hd m]
      simp [tw, hma, hmb]

private lemma nSwap_eq_conj {n p : ℕ} {a b : Fin n} (_hab : a ≠ b) :
    nSwap p a b = sgnAut a * pSwap p a b * (sgnAut a)⁻¹ := by
  have h2 : pSwap p a b * sgnAut a = sgnAut b * pSwap p a b := by
    have h := pSwap_mul_sgnAut (p := p) (a := a) (b := b) a
    rwa [show Equiv.swap a b a = b from Equiv.swap_apply_left a b] at h
  calc nSwap p a b = sgnAut a * (sgnAut b * pSwap p a b) := by rw [nSwap, mul_assoc]
    _ = sgnAut a * (pSwap p a b * sgnAut a) := by rw [← h2]
    _ = sgnAut a * pSwap p a b * sgnAut a := by rw [mul_assoc]
    _ = sgnAut a * pSwap p a b * (sgnAut a)⁻¹ := by rw [sgnAut_inv]

private lemma comm_sgn_pSwap {n p : ℕ} {i a b : Fin n} (hia : i ≠ a) (hib : i ≠ b) :
    sgnAut i * pSwap p a b = pSwap p a b * sgnAut i := by
  have h := pSwap_mul_sgnAut (p := p) (a := a) (b := b) i
  rw [show Equiv.swap a b i = i from Equiv.swap_apply_of_ne_of_ne hia hib] at h
  exact h.symm

private lemma comm_sgn_nSwap {n p : ℕ} {i a b : Fin n} (hia : i ≠ a) (hib : i ≠ b)
    (hab : a ≠ b) :
    sgnAut i * nSwap p a b = nSwap p a b * sgnAut i := by
  have h := nSwap_mul_sgnAut (p := p) hab i
  rw [show Equiv.swap a b i = i from Equiv.swap_apply_of_ne_of_ne hia hib] at h
  exact h.symm

private lemma comm_pSwap_pSwap {n p : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    pSwap p a b * pSwap p c d = pSwap p c d * pSwap p a b := by
  have hcomm : Commute (Equiv.swap a b) (Equiv.swap c d) :=
    (Equiv.Perm.disjoint_swap_swap (x := a) (y := b) (z := c) (t := d)
      (by simp [hab, hcd, hac, had, hbc, hbd])).commute
  unfold pSwap
  rw [← permAut_mul, ← permAut_mul, hcomm.eq]

private lemma comm_pSwap_nSwap {n p : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    pSwap p a b * nSwap p c d = nSwap p c d * pSwap p a b := by
  have hp : Commute (pSwap p a b) (pSwap p c d) :=
    comm_pSwap_pSwap hab hcd hac had hbc hbd
  have h1 : Commute (pSwap p a b) (sgnAut c) :=
    (comm_sgn_pSwap (p := p) (i := c) (a := a) (b := b) (Ne.symm hac) (Ne.symm hbc)).symm
  have h2 : Commute (pSwap p a b) (sgnAut d) :=
    (comm_sgn_pSwap (p := p) (i := d) (a := a) (b := b) (Ne.symm had) (Ne.symm hbd)).symm
  have h12 : Commute (pSwap p a b) (sgnAut c * sgnAut d) := h1.mul_right h2
  rw [nSwap]
  exact (h12.mul_right hp).eq

private lemma comm_nSwap_nSwap {n p : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    nSwap p a b * nSwap p c d = nSwap p c d * nSwap p a b := by
  have hp : Commute (pSwap p a b) (pSwap p c d) :=
    comm_pSwap_pSwap hab hcd hac had hbc hbd
  have h1 : Commute (sgnAut a) (sgnAut c) := sgnAut_mul_comm (p := p) a c
  have h2 : Commute (sgnAut a) (sgnAut d) := sgnAut_mul_comm (p := p) a d
  have h3 : Commute (sgnAut b) (sgnAut c) := sgnAut_mul_comm (p := p) b c
  have h4 : Commute (sgnAut b) (sgnAut d) := sgnAut_mul_comm (p := p) b d
  have h5 : Commute (sgnAut a) (pSwap p c d) :=
    comm_sgn_pSwap (p := p) (i := a) (a := c) (b := d) hac had
  have h6 : Commute (sgnAut b) (pSwap p c d) :=
    comm_sgn_pSwap (p := p) (i := b) (a := c) (b := d) hbc hbd
  have h7 : Commute (pSwap p a b) (sgnAut c) :=
    (comm_sgn_pSwap (p := p) (i := c) (a := a) (b := b) (Ne.symm hac) (Ne.symm hbc)).symm
  have h8 : Commute (pSwap p a b) (sgnAut d) :=
    (comm_sgn_pSwap (p := p) (i := d) (a := a) (b := b) (Ne.symm had) (Ne.symm hbd)).symm
  have hL : Commute (sgnAut a * sgnAut b * pSwap p a b) (sgnAut c * sgnAut d) :=
    ((h1.mul_right h2).mul_left (h3.mul_right h4)).mul_left (h7.mul_right h8)
  have hR : Commute (sgnAut a * sgnAut b * pSwap p a b) (pSwap p c d) :=
    ((h5.mul_left h6)).mul_left hp
  rw [nSwap]
  exact (hL.mul_right hR).eq

private def IsSupp {n p : ℕ} (u : MulAut (Fin n → Multiplicative (ZMod p))) (x : Fin n) : Prop :=
  u (Pi.mulSingle x (Multiplicative.ofAdd (1 : ZMod p))) ≠
    Pi.mulSingle x (Multiplicative.ofAdd (1 : ZMod p))

private lemma coord_one_ne_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (1 : ZMod p) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have h' := congrArg (fun x : ZMod p => x + 1) h
    simpa [one_add_one_eq_two] using h'
  exact coord_two_ne_zero hp hp2 h2

private lemma isSupp_sgn_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i x : Fin n) :
    IsSupp (sgnAut (p := p) i) x ↔ x = i := by
  constructor
  · intro h
    by_contra hx
    refine h ?_
    rw [sgnAut_mulSingle_of_ne hx]
  · rintro hxi
    rw [hxi]
    intro h
    rw [sgnAut_mulSingle_self] at h
    have h' := congrArg (fun v : Fin n → Multiplicative (ZMod p) => toAdd (v i)) h
    simp only [Pi.inv_apply, Pi.mulSingle_eq_same, toAdd_inv, toAdd_ofAdd] at h'
    exact coord_one_ne_neg_one hp hp2 h'.symm

private lemma isSupp_pSwap_iff {n p : ℕ} (hp : p.Prime) {a b : Fin n} (hab : a ≠ b)
    (x : Fin n) : IsSupp (pSwap p a b) x ↔ x = a ∨ x = b := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    refine h ?_
    rw [pSwap_mulSingle,
      show Equiv.swap a b x = x from Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]
  · rintro (hx | hx)
    · rw [hx]
      intro h
      rw [pSwap_mulSingle, Equiv.swap_apply_left] at h
      exact hab ((mulSingle_ofAdd_eq_iff (hx := (coord_zero_ne_one hp).symm) h).1).symm
    · rw [hx]
      intro h
      rw [pSwap_mulSingle, Equiv.swap_apply_right] at h
      exact hab ((mulSingle_ofAdd_eq_iff (hx := (coord_zero_ne_one hp).symm) h).1)

private lemma isSupp_nSwap_iff {n p : ℕ} (hp : p.Prime) {a b : Fin n} (hab : a ≠ b)
    (x : Fin n) : IsSupp (nSwap p a b) x ↔ x = a ∨ x = b := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    refine h ?_
    rw [nSwap_mulSingle hab,
      show Equiv.swap a b x = x from Equiv.swap_apply_of_ne_of_ne hx.1 hx.2,
      tw, if_neg (fun h => h.elim hx.1 hx.2), one_mul]
  · rintro (hx | hx)
    · rw [hx]
      intro h
      rw [nSwap_mulSingle hab, Equiv.swap_apply_left,
        show tw p a b a * 1 = -1 by simp [tw]] at h
      exact hab ((mulSingle_ofAdd_eq_iff (hx := coord_sign_ne_zero hp (Or.inr rfl)) h).1).symm
    · rw [hx]
      intro h
      rw [nSwap_mulSingle hab, Equiv.swap_apply_right,
        show tw p a b b * 1 = -1 by simp [tw]] at h
      exact hab ((mulSingle_ofAdd_eq_iff (hx := coord_sign_ne_zero hp (Or.inr rfl)) h).1)

private lemma isSupp_sgn {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {i : Fin n} (h : u = sgnAut i) :
    IsSupp u i := by
  rw [h]
  exact (isSupp_sgn_iff hp hp2 i i).2 rfl

private lemma isSupp_pSwap {n p : ℕ} (hp : p.Prime)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {a b : Fin n} (hab : a ≠ b)
    (h : u = pSwap p a b) : IsSupp u a ∧ IsSupp u b := by
  constructor
  · rw [h]
    exact (isSupp_pSwap_iff hp hab a).2 (Or.inl rfl)
  · rw [h]
    exact (isSupp_pSwap_iff hp hab b).2 (Or.inr rfl)

private lemma isSupp_nSwap {n p : ℕ} (hp : p.Prime)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {a b : Fin n} (hab : a ≠ b)
    (h : u = nSwap p a b) : IsSupp u a ∧ IsSupp u b := by
  constructor
  · rw [h]
    exact (isSupp_nSwap_iff hp hab a).2 (Or.inl rfl)
  · rw [h]
    exact (isSupp_nSwap_iff hp hab b).2 (Or.inr rfl)

private lemma isSupp_of_pair {n p : ℕ} (hp : p.Prime)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} {a b x : Fin n} (hab : a ≠ b)
    (hu : u = pSwap p a b ∨ u = nSwap p a b) (hx : x = a ∨ x = b) : IsSupp u x := by
  rcases hu with rfl | rfl
  · rcases hx with rfl | rfl
    · exact (isSupp_pSwap hp hab rfl).1
    · exact (isSupp_pSwap hp hab rfl).2
  · rcases hx with rfl | rfl
    · exact (isSupp_nSwap hp hab rfl).1
    · exact (isSupp_nSwap hp hab rfl).2

private noncomputable def genSet {n p : ℕ} {κ : Type*}
    (r : κ → MulAut (Fin n → Multiplicative (ZMod p))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ k, IsSupp (r k) x)

private lemma mem_genSet {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))} {x : Fin n} :
    x ∈ genSet r ↔ ∃ k, IsSupp (r k) x := by
  classical
  rw [genSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

private lemma hr_norm {n p : ℕ} {κ : Type*} {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = permAut (Equiv.swap a b) ∨
        r k = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹)) (k : κ) :
    (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧ (r k = pSwap p a b ∨ r k = nSwap p a b) := by
  rcases hr k with h | ⟨a, b, hab, h | h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, hab, Or.inl h⟩
  · refine Or.inr ⟨a, b, hab, Or.inr ?_⟩
    rw [h, nSwap_eq_conj hab, pSwap]

private lemma exists_isSupp {n p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {κ : Type*} {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b)) (k : κ) : ∃ x, IsSupp (r k) x := by
  rcases hr k with ⟨i, hk⟩ | ⟨a, b, hab, h | h⟩
  · exact ⟨i, isSupp_sgn hp hp2 hk⟩
  · exact ⟨a, (isSupp_pSwap hp hab h).1⟩
  · exact ⟨a, (isSupp_nSwap hp hab h).1⟩

private lemma gen_mem {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))} {k : κ} :
    r k ∈ Subgroup.closure (Set.range r) :=
  Subgroup.subset_closure ⟨k, rfl⟩

private lemma apply_eq_of_notMem_genSet {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ Subgroup.closure (Set.range r)) {j : Fin n} (hj : j ∉ genSet r) :
    ∀ f : Fin n → Multiplicative (ZMod p), u f j = f j := by
  refine Subgroup.closure_induction (p := fun u _ => ∀ f, u f j = f j) ?_ ?_ ?_ ?_ hu
  · rintro u ⟨k, rfl⟩ f
    rcases hr k with ⟨i, hk⟩ | ⟨a, b, hab, hp' | hp'⟩
    · have hji : j ≠ i := by
        rintro rfl
        exact hj (mem_genSet.mpr ⟨k, isSupp_sgn hp hp2 hk⟩)
      rw [hk, sgnAut_apply, Function.update_of_ne hji]
    · have hja : j ≠ a := by
        rintro rfl
        exact hj (mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hp').1⟩)
      have hjb : j ≠ b := by
        rintro rfl
        exact hj (mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hp').2⟩)
      rw [hp', pSwap_apply, Equiv.swap_apply_of_ne_of_ne hja hjb]
    · have hja : j ≠ a := by
        rintro rfl
        exact hj (mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hp').1⟩)
      have hjb : j ≠ b := by
        rintro rfl
        exact hj (mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hp').2⟩)
      rw [hp', nSwap_apply hab, if_neg hja, if_neg hjb]
  · intro f
    rfl
  · intro x y _ _ hx hy f
    rw [MulAut.mul_apply, hx (y f), hy f]
  · intro x _ hx f
    have h2 : x (x⁻¹ f) j = (x⁻¹ f) j := hx (x⁻¹ f)
    rw [show x (x⁻¹ f) = f from MulEquiv.apply_symm_apply x f] at h2
    exact h2.symm

private def Adj {n p : ℕ} (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (a b : Fin n) : Prop :=
  a ≠ b ∧ (pSwap p a b ∈ R ∨ nSwap p a b ∈ R)

private def Link {n p : ℕ} (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (x y : Fin n) : Prop :=
  x = y ∨ Adj R x y

private lemma adj_trans {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {a b c : Fin n} (hab : Adj R a b) (hbc : Adj R b c) (hac : a ≠ c) : Adj R a c := by
  obtain ⟨hab', h1⟩ := hab
  obtain ⟨hbc', h2⟩ := hbc
  refine ⟨hac, ?_⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (by
      rw [← conj_pp hab' hbc' hac]
      exact R.mul_mem (R.mul_mem h2 h1) h2)
  · exact Or.inr (by
      rw [← conj_np hab' hbc' hac]
      exact R.mul_mem (R.mul_mem h2 h1) h2)
  · exact Or.inr (by
      rw [← conj_pn hab' hbc' hac]
      exact R.mul_mem (R.mul_mem h2 h1) h2)
  · exact Or.inl (by
      rw [← conj_nn hab' hbc' hac]
      exact R.mul_mem (R.mul_mem h2 h1) h2)

private lemma link_trans {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {x y z : Fin n} (h1 : Link R x y) (h2 : Link R y z) : Link R x z := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  rcases eq_or_ne x z with rfl | hxz
  · exact Or.inl rfl
  · exact Or.inr (adj_trans h1 h2 hxz)

private lemma notCommute_iff_disjoint {n p : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    {u v : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u = pSwap p a b ∨ u = nSwap p a b)
    (hv : v = pSwap p c d ∨ v = nSwap p c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : u * v = v * u := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact comm_pSwap_pSwap hab hcd hac had hbc hbd
  · exact comm_pSwap_nSwap hab hcd hac had hbc hbd
  · exact (comm_pSwap_nSwap (p := p) (a := c) (b := d) (c := a) (d := b) hcd hab
      (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd)).symm
  · exact comm_nSwap_nSwap hab hcd hac had hbc hbd

private lemma supp_link {n p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {κ : Type*} {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (hR : ∀ k, r k ∈ R) {k : κ} {x y : Fin n}
    (hx : IsSupp (r k) x) (hy : IsSupp (r k) y) : Link R x y := by
  rcases hr k with ⟨i, hk⟩ | ⟨a, b, hab, hk | hk⟩
  · rw [hk] at hx hy
    exact Or.inl (by
      rw [(isSupp_sgn_iff hp hp2 i x).1 hx, (isSupp_sgn_iff hp hp2 i y).1 hy])
  · rw [hk] at hx hy
    have hx' := (isSupp_pSwap_iff hp hab x).1 hx
    have hy' := (isSupp_pSwap_iff hp hab y).1 hy
    have hmem : pSwap p a b ∈ R := by
      rw [← hk]
      exact hR k
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨hab, Or.inl hmem⟩
    · exact Or.inr ⟨Ne.symm hab, Or.inl (by rwa [pSwap_comm])⟩
    · exact Or.inl rfl
  · rw [hk] at hx hy
    have hx' := (isSupp_nSwap_iff hp hab x).1 hx
    have hy' := (isSupp_nSwap_iff hp hab y).1 hy
    have hmem : nSwap p a b ∈ R := by
      rw [← hk]
      exact hR k
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨hab, Or.inr hmem⟩
    · exact Or.inr ⟨Ne.symm hab, Or.inr (by rwa [nSwap_comm])⟩
    · exact Or.inl rfl

private lemma exists_common_supp_sgn_left {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    {k l : κ} {i : Fin n} (hk : r k = sgnAut i)
    (h : r k * r l ≠ r l * r k) : ∃ x, IsSupp (r k) x ∧ IsSupp (r l) x := by
  rcases hr l with ⟨j, hl⟩ | ⟨c, d, hcd, hl | hl⟩
  · rw [hk, hl] at h
    exact absurd (sgnAut_mul_comm (p := p) i j) h
  · rw [hk, hl] at h
    by_cases hic : i = c
    · exact ⟨i, isSupp_sgn hp hp2 hk, by
        rw [hic]
        exact (isSupp_pSwap hp hcd hl).1⟩
    · by_cases hid : i = d
      · exact ⟨i, isSupp_sgn hp hp2 hk, by
          rw [hid]
          exact (isSupp_pSwap hp hcd hl).2⟩
      · exact absurd (comm_sgn_pSwap (p := p) (i := i) (a := c) (b := d) hic hid) h
  · rw [hk, hl] at h
    by_cases hic : i = c
    · exact ⟨i, isSupp_sgn hp hp2 hk, by
        rw [hic]
        exact (isSupp_nSwap hp hcd hl).1⟩
    · by_cases hid : i = d
      · exact ⟨i, isSupp_sgn hp hp2 hk, by
          rw [hid]
          exact (isSupp_nSwap hp hcd hl).2⟩
      · exact absurd (comm_sgn_nSwap (p := p) (i := i) (a := c) (b := d) hic hid hcd) h

private lemma exists_common_supp_transp {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) {k l : κ}
    (hk : ∃ a b, a ≠ b ∧ (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hl : ∃ a b, a ≠ b ∧ (r l = pSwap p a b ∨ r l = nSwap p a b))
    (h : r k * r l ≠ r l * r k) : ∃ x, IsSupp (r k) x ∧ IsSupp (r l) x := by
  obtain ⟨a, b, hab, hk'⟩ := hk
  obtain ⟨c, d, hcd, hl'⟩ := hl
  by_cases hdisj : a = c ∨ a = d ∨ b = c ∨ b = d
  · rcases hdisj with hac | had | hbc | hbd
    · exact ⟨a, isSupp_of_pair hp hab hk' (Or.inl rfl), by
        rw [hac]
        exact isSupp_of_pair hp hcd hl' (Or.inl rfl)⟩
    · exact ⟨a, isSupp_of_pair hp hab hk' (Or.inl rfl), by
        rw [had]
        exact isSupp_of_pair hp hcd hl' (Or.inr rfl)⟩
    · exact ⟨b, isSupp_of_pair hp hab hk' (Or.inr rfl), by
        rw [hbc]
        exact isSupp_of_pair hp hcd hl' (Or.inl rfl)⟩
    · exact ⟨b, isSupp_of_pair hp hab hk' (Or.inr rfl), by
        rw [hbd]
        exact isSupp_of_pair hp hcd hl' (Or.inr rfl)⟩
  · push Not at hdisj
    obtain ⟨hac, had, hbc, hbd⟩ := hdisj
    exact absurd (notCommute_iff_disjoint hab hcd hk' hl' hac had hbc hbd) h

private lemma exists_common_supp {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    {k l : κ} (h : r k * r l ≠ r l * r k) :
    ∃ x, IsSupp (r k) x ∧ IsSupp (r l) x := by
  rcases hr k with ⟨i, hk⟩ | ⟨a, b, hab, hk⟩
  · exact exists_common_supp_sgn_left hp hp2 hr hk h
  · rcases hr l with ⟨j, hl⟩ | ⟨c, d, hcd, hl⟩
    · obtain ⟨x, hx1, hx2⟩ :=
        exists_common_supp_sgn_left hp hp2 hr hl (fun hh => h hh.symm)
      exact ⟨x, hx2, hx1⟩
    · exact exists_common_supp_transp hp ⟨a, b, hab, hk⟩ ⟨c, d, hcd, hl⟩ h

private def Noncomm {n p : ℕ} {κ : Type*}
    (r : κ → MulAut (Fin n → Multiplicative (ZMod p))) (a b : κ) : Prop :=
  r a * r b ≠ r b * r a

private lemma linkable_of_reflTransGen {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (hR : ∀ k, r k ∈ R) {k l : κ}
    (h : Relation.ReflTransGen (Noncomm r) k l) :
    ∀ x y, IsSupp (r k) x → IsSupp (r l) y → Link R x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro x y hx hy; exact supp_link hp hp2 hr R hR hx hy
  | head h' _ ih =>
      intro x y hx hy
      obtain ⟨z, hz1, hz2⟩ := exists_common_supp hp hp2 hr h'
      exact link_trans (supp_link hp hp2 hr R hR hx hz1) (ih z y hz2 hy)

private lemma adj_of_mem_genSet {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (hR : ∀ k, r k ∈ R)
    (hconn : ∀ k k', Relation.ReflTransGen (Noncomm r) k k')
    {x y : Fin n} (hx : x ∈ genSet r) (hy : y ∈ genSet r) (hxy : x ≠ y) : Adj R x y := by
  obtain ⟨k, hkx⟩ := mem_genSet.mp hx
  obtain ⟨l, hyl⟩ := mem_genSet.mp hy
  rcases linkable_of_reflTransGen hp hp2 hr R hR (hconn k l) x y hkx hyl with h | h
  · exact absurd h hxy
  · exact h

private def blockB {n p : ℕ} (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {u | (∃ i ∈ I, u = sgnAut i) ∨
    (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ u = pSwap p a b)}

private def blockD {n p : ℕ} (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {u | (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ u = pSwap p a b) ∨
    (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ u = nSwap p a b)}

private def blockS {n p : ℕ} (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {u | ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ u = pSwap p a b}

private lemma blockB_erase {n p : ℕ} (i0 : Fin n) :
    blockB (p := p) (Finset.univ.erase i0) = bCoordinateBlock n p i0 := by
  rw [blockB, bCoordinateBlock]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true, pSwap]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨a, b, hab, ha, hb, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, hab, rfl⟩

private lemma blockD_erase {n p : ℕ} (i0 : Fin n) :
    blockD (p := p) (Finset.univ.erase i0) = dCoordinateBlock n p i0 := by
  rw [blockD, dCoordinateBlock]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true, pSwap]
  constructor
  · rintro (⟨a, ha, b, hb, hab, h⟩ | ⟨a, ha, b, hb, hab, h⟩)
    · exact Or.inl ⟨a, b, hab, ha, hb, h⟩
    · refine Or.inr ⟨a, b, hab, ha, hb, ?_⟩
      rw [h, nSwap_eq_conj hab, pSwap]
  · rintro (⟨a, b, hab, ha, hb, h⟩ | ⟨a, b, hab, ha, hb, h⟩)
    · exact Or.inl ⟨a, ha, b, hb, hab, h⟩
    · refine Or.inr ⟨a, ha, b, hb, hab, ?_⟩
      rw [nSwap_eq_conj hab, pSwap]
      exact h

private lemma blockS_univ {n p : ℕ} :
    blockS (p := p) (Finset.univ : Finset (Fin n)) = aPermutationFull n p := by
  rw [blockS, aPermutationFull]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
  tauto

private def stab {n p : ℕ} (f : Fin n → Multiplicative (ZMod p)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) where
  carrier := {u | u f = f}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    show (x * y) f = f
    rw [MulAut.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    show x⁻¹ f = f
    refine x.injective ?_
    rw [show x (x⁻¹ f) = f from MulEquiv.apply_symm_apply x f]
    exact hx.symm

private lemma fix_closure_iff {n p : ℕ} {S : Set (MulAut (Fin n → Multiplicative (ZMod p)))}
    {f : Fin n → Multiplicative (ZMod p)} :
    (∀ u ∈ Subgroup.closure S, u f = f) ↔ ∀ u ∈ S, u f = f := by
  constructor
  · intro h u hu
    exact h u (Subgroup.subset_closure hu)
  · intro h u hu
    exact (Subgroup.closure_le (K := stab f)).mpr h hu

private lemma sgnAut_eq_self_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : Fin n → Multiplicative (ZMod p)} {i : Fin n} :
    (sgnAut (p := p) i) f = f ↔ f i = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun v : Fin n → Multiplicative (ZMod p) => toAdd (v i)) h
    rw [sgnAut_apply, Function.update_self, toAdd_inv] at h'
    have h'' : toAdd (f i) = -toAdd (f i) := h'.symm
    have h3 := coord_eq_zero_of_eq_neg hp hp2 h''
    exact Multiplicative.toAdd.injective (by rw [h3]; rfl)
  · intro h
    funext j
    by_cases hj : j = i
    · subst hj
      rw [sgnAut_apply, Function.update_self, h, inv_one]
    · rw [sgnAut_apply, Function.update_of_ne hj]

private lemma pSwap_eq_self_iff {n p : ℕ} {f : Fin n → Multiplicative (ZMod p)} {a b : Fin n} :
    pSwap p a b f = f ↔ f a = f b := by
  constructor
  · intro h
    have h1 := congrArg (fun v : Fin n → Multiplicative (ZMod p) => v a) h
    rw [pSwap_apply, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext j
    rw [pSwap_apply]
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left, h]
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

private lemma sgn_mul_sgn_mul_pSwap {n p : ℕ} (a b : Fin n) :
    sgnAut a * sgnAut b * pSwap p a b = nSwap p a b := rfl

private lemma sgn_mul_sgn_mul_nSwap {n p : ℕ} {a b : Fin n} (_hab : a ≠ b) :
    sgnAut a * sgnAut b * nSwap p a b = pSwap p a b := by
  rw [nSwap]
  rw [show sgnAut (p := p) a * sgnAut b * (sgnAut a * sgnAut b * pSwap p a b) =
      sgnAut a * (sgnAut b * sgnAut a) * sgnAut b * pSwap p a b by group]
  rw [sgnAut_mul_comm b a]
  rw [show sgnAut (p := p) a * (sgnAut a * sgnAut b) * sgnAut b * pSwap p a b =
      (sgnAut a * sgnAut a) * (sgnAut b * sgnAut b) * pSwap p a b by group]
  rw [sgnAut_mul_self, sgnAut_mul_self, one_mul, one_mul]

private lemma fix_blockB {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I : Finset (Fin n)}
    {f : Fin n → Multiplicative (ZMod p)} :
    (∀ u ∈ blockB (p := p) I, u f = f) ↔ ∀ i ∈ I, f i = 1 := by
  rw [blockB, fix_closure_iff]
  constructor
  · rintro h i hi
    exact (sgnAut_eq_self_iff hp hp2).1 (h (sgnAut i) (Or.inl ⟨i, hi, rfl⟩))
  · rintro h u (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact (sgnAut_eq_self_iff hp hp2).2 (h i hi)
    · exact (pSwap_eq_self_iff).2 (by rw [h a ha, h b hb])

private lemma exists_ne_of_two_le_card {α : Type*} [DecidableEq α] {s : Finset α}
    (h : 2 ≤ s.card) {i : α} (_hi : i ∈ s) : ∃ j ∈ s, j ≠ i := by
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (s := s) (a := i) (by omega)
  exact ⟨j, hj, hji⟩

private lemma fix_blockD {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) {f : Fin n → Multiplicative (ZMod p)} :
    (∀ u ∈ blockD (p := p) I, u f = f) ↔ ∀ i ∈ I, f i = 1 := by
  rw [blockD, fix_closure_iff]
  constructor
  · intro h i hi
    obtain ⟨j, hj, hji⟩ := exists_ne_of_two_le_card hI hi
    have hP : pSwap p i j f = f := h (pSwap p i j) (Or.inl ⟨i, hi, j, hj, Ne.symm hji, rfl⟩)
    have hN : nSwap p i j f = f := h (nSwap p i j) (Or.inr ⟨i, hi, j, hj, Ne.symm hji, rfl⟩)
    have heq : f i = f j := (pSwap_eq_self_iff).1 hP
    have hN' := congrArg (fun v : Fin n → Multiplicative (ZMod p) => toAdd (v i)) hN
    rw [nSwap_apply (Ne.symm hji), if_pos rfl, toAdd_inv] at hN'
    have hsum : toAdd (f i) = -toAdd (f i) := by
      rw [← heq] at hN'
      exact hN'.symm
    have hzero := coord_eq_zero_of_eq_neg hp hp2 hsum
    exact Multiplicative.toAdd.injective (by rw [hzero, toAdd_one])
  · rintro h u (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact (pSwap_eq_self_iff).2 (by rw [h a ha, h b hb])
    · rw [nSwap, MulAut.mul_apply, MulAut.mul_apply,
        (pSwap_eq_self_iff).2 (by rw [h a ha, h b hb]),
        (sgnAut_eq_self_iff hp hp2).2 (h b hb),
        (sgnAut_eq_self_iff hp hp2).2 (h a ha)]

private lemma fix_blockS {n p : ℕ} {I : Finset (Fin n)}
    {f : Fin n → Multiplicative (ZMod p)} :
    (∀ u ∈ blockS (p := p) I, u f = f) ↔ ∀ i ∈ I, ∀ j ∈ I, f i = f j := by
  rw [blockS, fix_closure_iff]
  constructor
  · intro h i hi j hj
    by_cases hij : i = j
    · subst hij; rfl
    · exact (pSwap_eq_self_iff).1 (h (pSwap p i j) ⟨i, hi, j, hj, hij, rfl⟩)
  · rintro h u ⟨a, ha, b, hb, hab, rfl⟩
    exact (pSwap_eq_self_iff).2 (h a ha b hb)

private noncomputable def extendOff {n p : ℕ} (I : Finset (Fin n))
    (g : {i : Fin n // i ∉ I} → Multiplicative (ZMod p)) :
    Fin n → Multiplicative (ZMod p) :=
  fun i => if h : i ∈ I then 1 else g ⟨i, h⟩

private lemma extendOff_of_mem {n p : ℕ} {I : Finset (Fin n)}
    {g : {i : Fin n // i ∉ I} → Multiplicative (ZMod p)} {i : Fin n} (h : i ∈ I) :
    extendOff I g i = 1 := by
  rw [extendOff]
  simp only [dif_pos h]

private lemma extendOff_of_notMem {n p : ℕ} {I : Finset (Fin n)}
    {g : {i : Fin n // i ∉ I} → Multiplicative (ZMod p)} {i : Fin n} (h : i ∉ I) :
    extendOff I g i = g ⟨i, h⟩ := by
  rw [extendOff]
  simp only [dif_neg h]

private lemma card_compl {n : ℕ} (I : Finset (Fin n)) :
    Nat.card {i : Fin n // i ∉ I} = n - I.card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe,
    Fintype.card_fin]

private lemma card_multiplicative {p : ℕ} : Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private noncomputable def fixBEquiv {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Finset (Fin n)) :
    {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockB (p := p) I, u f = f} ≃
      ({i : Fin n // i ∉ I} → Multiplicative (ZMod p)) where
  toFun f := fun i => f.1 i.1
  invFun g := ⟨extendOff I g, (fix_blockB hp hp2).2 (fun i hi => extendOff_of_mem hi)⟩
  left_inv f := by
    ext i
    change extendOff I (fun j => f.1 j.1) i = f.1 i
    by_cases hi : i ∈ I
    · rw [extendOff_of_mem hi]
      exact ((fix_blockB hp hp2).1 f.2 i hi).symm
    · rw [extendOff_of_notMem hi]
  right_inv g := by
    funext i
    exact extendOff_of_notMem (p := p) i.2

private lemma card_fixB {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (I : Finset (Fin n)) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockB (p := p) I, u f = f} =
      p ^ (n - I.card) := by
  rw [Nat.card_congr (fixBEquiv hp hp2 I), Nat.card_fun, card_multiplicative, card_compl]

private noncomputable def fixDEquiv {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Finset (Fin n)) (hI : 2 ≤ I.card) :
    {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockD (p := p) I, u f = f} ≃
      ({i : Fin n // i ∉ I} → Multiplicative (ZMod p)) where
  toFun f := fun i => f.1 i.1
  invFun g := ⟨extendOff I g, (fix_blockD hp hp2 hI).2 (fun i hi => extendOff_of_mem hi)⟩
  left_inv f := by
    ext i
    change extendOff I (fun j => f.1 j.1) i = f.1 i
    by_cases hi : i ∈ I
    · rw [extendOff_of_mem hi]
      exact ((fix_blockD hp hp2 hI).1 f.2 i hi).symm
    · rw [extendOff_of_notMem hi]
  right_inv g := by
    funext i
    exact extendOff_of_notMem (p := p) i.2

private lemma card_fixD {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (I : Finset (Fin n))
    (hI : 2 ≤ I.card) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockD (p := p) I, u f = f} =
      p ^ (n - I.card) := by
  rw [Nat.card_congr (fixDEquiv hp hp2 I hI), Nat.card_fun, card_multiplicative, card_compl]

private noncomputable def fixSEquiv {n p : ℕ} (I : Finset (Fin n)) (z : Fin n) (hz : z ∈ I) :
    {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockS (p := p) I, u f = f} ≃
      (Multiplicative (ZMod p) ×
        ({i : Fin n // i ∉ I} → Multiplicative (ZMod p))) where
  toFun f := (f.1 z, fun i => f.1 i.1)
  invFun cg :=
    ⟨fun i => if h : i ∈ I then cg.1 else cg.2 ⟨i, h⟩, by
      refine (fix_blockS (p := p) (I := I)).2 (fun i hi j hj => ?_)
      rw [dif_pos hi, dif_pos hj]⟩
  left_inv f := by
    ext i
    change (if h : i ∈ I then f.1 z else f.1 (⟨i, h⟩ : {j : Fin n // j ∉ I})) = f.1 i
    by_cases hi : i ∈ I
    · rw [dif_pos hi]
      exact (fix_blockS (p := p) (I := I)).1 f.2 z hz i hi
    · rw [dif_neg hi]
  right_inv cg := by
    refine Prod.ext ?_ ?_
    · exact dif_pos hz
    · funext i
      exact dif_neg i.2

private lemma card_fixS {n p : ℕ} (I : Finset (Fin n)) (z : Fin n) (hz : z ∈ I) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ blockS (p := p) I, u f = f} =
      p ^ (n - I.card + 1) := by
  rw [Nat.card_congr (fixSEquiv I z hz), Nat.card_prod, Nat.card_fun,
    card_multiplicative, card_compl, pow_succ']

private noncomputable def fixConjEquiv {n p : ℕ}
    (δ : MulAut (Fin n → Multiplicative (ZMod p)))
    (H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) :
    {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ H.map (MulAut.conj δ).toMonoidHom, u f = f} ≃
      {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ H, u f = f} where
  toFun f :=
    ⟨δ⁻¹ f.1, fun u hu => by
      have h := f.2 (δ * u * δ⁻¹) (by
        rw [Subgroup.mem_map]
        exact ⟨u, hu, rfl⟩)
      rw [MulAut.mul_apply, MulAut.mul_apply] at h
      refine δ.injective ?_
      rw [show δ (u (δ⁻¹ f.1)) = f.1 from h]
      exact (MulEquiv.apply_symm_apply δ f.1).symm⟩
  invFun g :=
    ⟨δ g.1, fun u hu => by
      rw [Subgroup.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      show δ (v (δ⁻¹ (δ g.1))) = δ g.1
      rw [MulAut.inv_apply_self, g.2 v hv]⟩
  left_inv f := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)

private lemma card_fix_map_conj {n p : ℕ}
    (δ : MulAut (Fin n → Multiplicative (ZMod p)))
    (H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ H.map (MulAut.conj δ).toMonoidHom, u f = f} =
      Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ H, u f = f} :=
  Nat.card_congr (fixConjEquiv δ H)

private lemma card_coord (n p : ℕ) :
    Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
  rw [Nat.card_fun, card_multiplicative, Nat.card_eq_fintype_card, Fintype.card_fin]

private lemma map_conj_one {n p : ℕ}
    (H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) :
    H.map (MulAut.conj (1 : MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simpa using hv
  · intro u hu
    rw [Subgroup.mem_map]
    exact ⟨u, hu, by simp⟩

private lemma bCoordinateBlock_one (p : ℕ) (i0 : Fin 1) :
    bCoordinateBlock 1 p i0 = ⊥ := by
  rw [bCoordinateBlock]
  have hS : {r : MulAut (Fin 1 → Multiplicative (ZMod p)) |
      (∃ i : Fin 1, i ≠ i0 ∧ r = SpCoord.sgnAut i) ∨
      (∃ a b : Fin 1, a ≠ b ∧ a ≠ i0 ∧ b ≠ i0 ∧
        r = SpCoord.permAut (Equiv.swap a b))} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_or]
    constructor
    · rintro ⟨i, hi, _⟩
      exact hi (Subsingleton.elim i i0)
    · rintro ⟨a, b, hab, _⟩
      exact hab (Subsingleton.elim a b)
  rw [hS, Subgroup.closure_empty]

private lemma both_of_both_of_adj {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hboth : pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hy : pSwap p b c ∈ R ∨ nSwap p b c ∈ R) :
    pSwap p a c ∈ R ∧ nSwap p a c ∈ R := by
  constructor
  · rcases hy with hy | hy
    · rw [← conj_pp (p := p) hab hbc hac]
      exact R.mul_mem (R.mul_mem hy hboth.1) hy
    · rw [← conj_nn (p := p) hab hbc hac]
      exact R.mul_mem (R.mul_mem hy hboth.2) hy
  · rcases hy with hy | hy
    · rw [← conj_pn (p := p) hab hbc hac]
      exact R.mul_mem (R.mul_mem hy hboth.2) hy
    · rw [← conj_np (p := p) hab hbc hac]
      exact R.mul_mem (R.mul_mem hy hboth.1) hy

private lemma both_of_adj_of_sgn {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {a b : Fin n} (hab : a ≠ b)
    (hsa : sgnAut a ∈ R) (hsb : sgnAut b ∈ R)
    (h : pSwap p a b ∈ R ∨ nSwap p a b ∈ R) :
    pSwap p a b ∈ R ∧ nSwap p a b ∈ R := by
  constructor
  · rcases h with h | h
    · exact h
    · rw [← sgn_mul_sgn_mul_nSwap hab]
      exact R.mul_mem (R.mul_mem hsa hsb) h
  · rcases h with h | h
    · rw [← sgn_mul_sgn_mul_pSwap a b]
      exact R.mul_mem (R.mul_mem hsa hsb) h
    · exact h

private lemma both_of_P {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {I : Finset (Fin n)}
    (hP : ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R) :
    ∀ a ∈ I, ∀ b ∈ I, a ≠ b → pSwap p a b ∈ R ∧ nSwap p a b ∈ R := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀, hboth₀⟩ := hP
  have hswap : pSwap p b₀ a₀ ∈ R ∧ nSwap p b₀ a₀ ∈ R :=
    ⟨by simpa only [pSwap_comm (p := p) b₀ a₀] using hboth₀.1,
      by simpa only [nSwap_comm (p := p) b₀ a₀] using hboth₀.2⟩
  have hstep : ∀ c ∈ I, c ≠ a₀ → c ≠ b₀ → pSwap p b₀ c ∈ R ∧ nSwap p b₀ c ∈ R := by
    intro c hc hca hcb
    exact both_of_both_of_adj (Ne.symm hab₀) (Ne.symm hca) (Ne.symm hcb) hswap
      (hadj a₀ ha₀ c hc (Ne.symm hca))
  have hbase : ∀ x ∈ I, x ≠ b₀ → pSwap p b₀ x ∈ R ∧ nSwap p b₀ x ∈ R := by
    intro x hx hxb
    by_cases hxa : x = a₀
    · rw [hxa]
      exact hswap
    · exact hstep x hx hxa hxb
  intro a ha b hb hab
  by_cases hab₀' : a = b₀
  · subst a
    exact hbase b hb (Ne.symm hab)
  · by_cases hbb₀ : b = b₀
    · subst b
      exact ⟨by simpa only [pSwap_comm (p := p) b₀ a] using (hbase a ha hab₀').1,
        by simpa only [nSwap_comm (p := p) b₀ a] using (hbase a ha hab₀').2⟩
    · have hboth : pSwap p a b₀ ∈ R ∧ nSwap p a b₀ ∈ R :=
        ⟨by simpa only [pSwap_comm (p := p) b₀ a] using (hbase a ha hab₀').1,
          by simpa only [nSwap_comm (p := p) b₀ a] using (hbase a ha hab₀').2⟩
      exact both_of_both_of_adj hab₀' (Ne.symm hbb₀) hab hboth
        (hadj b₀ hb₀ b hb (Ne.symm hbb₀))

private noncomputable def pSign {n p : ℕ} (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (a b : Fin n) : ZMod p := by
  classical
  exact if pSwap p a b ∈ R then 1 else -1

private lemma pSign_eq_one_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {a b : Fin n} :
    pSign R a b = 1 ↔ pSwap p a b ∈ R := by
  constructor
  · intro h
    by_contra hc
    rw [pSign, if_neg hc] at h
    exact coord_one_ne_neg_one hp hp2 h.symm
  · intro h
    rw [pSign, if_pos h]

private lemma pSign_eq_neg_one_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {a b : Fin n} :
    pSign R a b = -1 ↔ pSwap p a b ∉ R := by
  constructor
  · intro h hc
    rw [pSign_eq_one_iff hp hp2 |>.2 hc] at h
    exact coord_one_ne_neg_one hp hp2 h
  · intro h
    rw [pSign, if_neg h]

private lemma pSign_sign {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (a b : Fin n) :
    pSign R a b = 1 ∨ pSign R a b = -1 := by
  rw [pSign]
  split_ifs <;> simp

private lemma pSign_symm {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (a b : Fin n) :
    pSign R a b = pSign R b a := by
  rw [pSign, pSign, pSwap_comm]

private lemma pSwap_self {n p : ℕ} (a : Fin n) : pSwap p a a = 1 := by
  rw [pSwap, Equiv.swap_self]
  refine MulEquiv.ext fun f => ?_
  simp [permAut_apply]

private lemma pSign_self {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (a : Fin n) :
    pSign R a a = 1 := by
  rw [pSign, if_pos (by rw [pSwap_self]; exact R.one_mem)]

private lemma pSign_mul_neg {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)}
    (hP : ¬ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    {a b c : Fin n} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (h1 : pSwap p a b ∉ R) :
    pSign R a c = pSign R a b * pSign R b c := by
  have hT : ∀ {x y : Fin n}, x ∈ I → y ∈ I → x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R :=
    fun {x y} hx hy hxy => hadj x hx y hy hxy
  have hnac : nSwap p a c ∈ R → pSign R a c = -1 := by
    intro h
    exact (pSign_eq_neg_one_iff hp hp2).2
      (fun hT' => hP ⟨a, ha, c, hc, hac, hT', h⟩)
  have h1n : nSwap p a b ∈ R := by
    rcases hT ha hb hab with h | h
    · exact absurd h h1
    · exact h
  have h1s : pSign R a b = -1 := by
    rw [pSign, if_neg h1]
  by_cases h2 : pSwap p b c ∈ R
  · have h2s : pSign R b c = 1 := by
      rw [pSign, if_pos h2]
    rw [hnac (by
      rw [← conj_pn hab hbc hac]
      exact R.mul_mem (R.mul_mem h2 h1n) h2), h1s, h2s]
    ring
  · have h2n : nSwap p b c ∈ R := by
      rcases hT hb hc hbc with h | h
      · exact absurd h h2
      · exact h
    have h2s : pSign R b c = -1 := by
      rw [pSign, if_neg h2]
    rw [(pSign_eq_one_iff hp hp2).2 (by
      rw [← conj_nn hab hbc hac]
      exact R.mul_mem (R.mul_mem h2n h1n) h2n), h1s, h2s]
    ring

private lemma pSign_mul {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)}
    (hP : ¬ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    {a b c : Fin n} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    pSign R a c = pSign R a b * pSign R b c := by
  have hT : ∀ {x y : Fin n}, x ∈ I → y ∈ I → x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R :=
    fun {x y} hx hy hxy => hadj x hx y hy hxy
  have hpac : pSwap p a c ∈ R → pSign R a c = 1 := fun h => (pSign_eq_one_iff hp hp2).2 h
  have hnac : nSwap p a c ∈ R → pSign R a c = -1 := by
    intro h
    exact (pSign_eq_neg_one_iff hp hp2).2
      (fun hT' => hP ⟨a, ha, c, hc, hac, hT', h⟩)
  by_cases h1 : pSwap p a b ∈ R
  · have h1s : pSign R a b = 1 := (pSign_eq_one_iff hp hp2).2 h1
    by_cases h2 : pSwap p b c ∈ R
    · have h2s : pSign R b c = 1 := (pSign_eq_one_iff hp hp2).2 h2
      rw [(pSign_eq_one_iff hp hp2).2 (by
        rw [← conj_pp hab hbc hac]
        exact R.mul_mem (R.mul_mem h2 h1) h2), h1s, h2s, mul_one]
    · have h2n : nSwap p b c ∈ R := by
        rcases hT hb hc hbc with h | h
        · exact absurd h h2
        · exact h
      have h2s : pSign R b c = -1 := by
        rw [pSign, if_neg h2]
      rw [hnac (by
        rw [← conj_np hab hbc hac]
        exact R.mul_mem (R.mul_mem h2n h1) h2n), h1s, h2s]
      ring
  · exact pSign_mul_neg hp hp2 hP hadj ha hb hc hab hbc hac h1

private noncomputable def dSign {n p : ℕ}
    (R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) (I : Finset (Fin n))
    (z : Fin n) (i : Fin n) : ZMod p := by
  classical
  exact if i ∈ I then pSign R z i else 1

private lemma dSign_of_mem {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)} {z i : Fin n}
    (hi : i ∈ I) : dSign R I z i = pSign R z i := by
  rw [dSign, if_pos hi]

private lemma dSign_self {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)} {z : Fin n}
    (hz : z ∈ I) : dSign R I z z = 1 := by
  rw [dSign_of_mem hz, pSign_self]

private lemma dSign_sign {n p : ℕ}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (I : Finset (Fin n)) (z : Fin n)
    (i : Fin n) : dSign R I z i = 1 ∨ dSign R I z i = -1 := by
  rw [dSign]
  split_ifs with hi
  · exact pSign_sign z i
  · exact Or.inl rfl

private lemma dSign_pair {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)}
    (hP : ¬ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    {z a b : Fin n} (hz : z ∈ I) (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    dSign R I z a * dSign R I z b = pSign R a b := by
  by_cases haz : a = z
  · rw [haz]
    rw [dSign_self hz, dSign_of_mem hb, one_mul]
  · by_cases hbz : b = z
    · rw [hbz]
      rw [dSign_of_mem ha, dSign_self hz, mul_one, pSign_symm]
    · rw [dSign_of_mem ha, dSign_of_mem hb,
        pSign_mul hp hp2 hP hadj ha hz hb haz (Ne.symm hbz) hab, pSign_symm z a]

private lemma diagAut_mul_sgnAut_comm {n p : ℕ} {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (i : Fin n) :
    diagAut d hd * sgnAut (p := p) i = sgnAut i * diagAut d hd := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply, sgnAut_apply, diagAut_apply]
  simp only [Function.update_apply, diagAut_apply]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, toAdd_inv, if_pos rfl, ← ofAdd_neg]
    congr 1
    exact mul_neg (d j) (toAdd (f j))
  · simp only [if_neg hji]

private lemma conj_diag_sgn {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (i : Fin n) :
    MulAut.conj (diagAut d hd) (sgnAut (p := p) i) = sgnAut i := by
  rw [MulAut.conj_apply, diagAut_inv]
  calc diagAut d hd * sgnAut i * diagAut d hd
      = sgnAut i * (diagAut d hd * diagAut d hd) := by
        rw [diagAut_mul_sgnAut_comm hd i]; group
    _ = sgnAut i := by rw [diagAut_mul_self hd, mul_one]

private lemma diag_conj_pSwap_one_conj {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (h : d a * d b = 1) :
    MulAut.conj (diagAut d hd) (pSwap p a b) = pSwap p a b := by
  rw [MulAut.conj_apply, diagAut_inv]
  exact diag_conj_pSwap_of_mul_eq_one hd h

private lemma diag_conj_pSwap_neg_conj {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (h : d a * d b = -1) :
    MulAut.conj (diagAut d hd) (pSwap p a b) = nSwap p a b := by
  rw [MulAut.conj_apply, diagAut_inv]
  exact diag_conj_pSwap_of_mul_eq_neg_one hd hab h

private lemma diag_conj_nSwap_conj {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (h : d a * d b = -1) :
    MulAut.conj (diagAut d hd) (nSwap p a b) = pSwap p a b := by
  rw [nSwap, map_mul, map_mul, conj_diag_sgn hd, conj_diag_sgn hd,
    diag_conj_pSwap_neg_conj hd hab h, sgn_mul_sgn_mul_nSwap hab]

private lemma coord_of_card {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    (h : n - (genSet r).card = 1) :
    ∃ i0 : Fin n, genSet r = Finset.univ.erase i0 := by
  have hcompl : (Finset.univ \ genSet r).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (genSet r)), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hcompl
  have hi0not : i0 ∉ genSet r := by
    have hmem : i0 ∈ Finset.univ \ genSet r := by
      rw [hi0]
      exact Finset.mem_singleton.mpr rfl
    exact (Finset.mem_sdiff.mp hmem).2
  refine ⟨i0, ?_⟩
  ext x
  rw [Finset.mem_erase]
  constructor
  · intro hx
    refine ⟨?_, Finset.mem_univ x⟩
    exact fun h => by rw [h] at hx; exact hi0not hx
  · rintro ⟨hxne, _⟩
    by_contra hxI
    have hmem : x ∈ Finset.univ \ genSet r := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxI⟩
    rw [hi0] at hmem
    exact hxne (Finset.mem_singleton.mp hmem)

private lemma main_empty {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hRdef : R = Subgroup.closure (Set.range r))
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ R, u f = f} = p)
    (hκ : IsEmpty κ) :
    ∃ δ ∈ bSignedFull n p, ∃ i0 : Fin n,
      R.map (MulAut.conj δ).toMonoidHom = bCoordinateBlock n p i0 := by
  have hrange : Set.range r = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨k, rfl⟩
    exact hκ.elim k
  have hbot : R = ⊥ := by
    rw [hRdef, hrange, Subgroup.closure_empty]
  have hfixE : Nat.card (Fin n → Multiplicative (ZMod p)) = p := by
    have h := hfix
    rw [hbot] at h
    rw [← Nat.card_congr (Equiv.subtypeUnivEquiv
      (p := fun f : Fin n → Multiplicative (ZMod p) =>
        ∀ u ∈ (⊥ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))), u f = f) (by
      intro f u hu
      rw [Subgroup.mem_bot] at hu
      rw [hu]
      rfl))]
    exact h
  have hn : n = 1 := by
    have h1 : p ^ n = p ^ 1 := by
      rw [← card_coord n p, hfixE, pow_one]
    exact Nat.pow_right_injective hp.two_le h1
  subst n
  refine ⟨1, (bSignedFull 1 p).one_mem, ⟨0, Nat.zero_lt_one⟩, ?_⟩
  rw [hbot, map_conj_one, bCoordinateBlock_one]

private lemma main_hadj {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hrn : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hconn : ∀ k k', Relation.ReflTransGen (fun a b => r a * r b ≠ r b * r a) k k')
    (hRmem : ∀ k, r k ∈ R) (x : Fin n) (hx : x ∈ genSet r) (y : Fin n) (hy : y ∈ genSet r)
    (hxy : x ≠ y) :
    pSwap p x y ∈ R ∨ nSwap p x y ∈ R :=
  (adj_of_mem_genSet hp hp2 hrn R hRmem hconn hx hy hxy).2

private lemma main_Q_sgn {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hrn : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hRdef : R = Subgroup.closure (Set.range r))
    (hQ : ∃ i, sgnAut i ∈ R)
    (hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
      pSwap p x y ∈ R ∨ nSwap p x y ∈ R) :
    ∀ i ∈ genSet r, sgnAut i ∈ R := by
  obtain ⟨s₀, hs₀R⟩ := hQ
  have hs₀R' : sgnAut s₀ ∈ Subgroup.closure (Set.range r) := by rwa [hRdef] at hs₀R
  have hs₀I : s₀ ∈ genSet r := by
    by_contra hcon
    have h := apply_eq_of_notMem_genSet hp hp2 hrn hs₀R' hcon
      (Pi.mulSingle s₀ (Multiplicative.ofAdd (1 : ZMod p)))
    simp only [sgnAut_mulSingle_self, Pi.inv_apply, Pi.mulSingle_eq_same] at h
    have h2 := congrArg (fun x : Multiplicative (ZMod p) => toAdd x) h
    simp only [toAdd_inv, toAdd_ofAdd] at h2
    exact coord_one_ne_neg_one hp hp2 h2.symm
  intro i hi
  by_cases hii : i = s₀
  · rwa [hii]
  · rcases hadj s₀ hs₀I i hi (Ne.symm hii) with hT | hT
    · have hconj : pSwap p s₀ i * sgnAut s₀ * pSwap p s₀ i = sgnAut i := by
        rw [pSwap_conj_sgn, Equiv.swap_apply_left]
      rw [← hconj]
      exact R.mul_mem (R.mul_mem hT hs₀R) hT
    · have hconj : nSwap p s₀ i * sgnAut s₀ * nSwap p s₀ i = sgnAut i := by
        rw [nSwap_conj_sgn (p := p) (Ne.symm hii), Equiv.swap_apply_left]
      rw [← hconj]
      exact R.mul_mem (R.mul_mem hT hs₀R) hT

private lemma main_Q_pair {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
      pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    (hsgn : ∀ i ∈ genSet r, sgnAut i ∈ R) :
    ∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b → pSwap p a b ∈ R := by
  intro a ha b hb hab
  by_cases hP' : ∃ x ∈ genSet r, ∃ y ∈ genSet r, x ≠ y ∧
      pSwap p x y ∈ R ∧ nSwap p x y ∈ R
  · exact (both_of_P hP' hadj a ha b hb hab).1
  · exfalso
    have hc : (genSet r).card ≤ 1 := by
      by_contra hc
      have hc' : 1 < (genSet r).card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc'
      exact hP' ⟨x, hx, y, hy, hxy,
        both_of_adj_of_sgn hxy (hsgn x hx) (hsgn y hy) (hadj x hx y hy hxy)⟩
    have h2 : 1 < (genSet r).card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega

private lemma main_Q_block {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hrn : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hRdef : R = Subgroup.closure (Set.range r))
    (hsgn : ∀ i ∈ genSet r, sgnAut i ∈ R)
    (hpair : ∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b → pSwap p a b ∈ R) :
    R = blockB (p := p) (genSet r) := by
  refine le_antisymm ?_ ?_
  · rw [hRdef, Subgroup.closure_le]
    rintro u ⟨k, rfl⟩
    rcases hrn k with ⟨i, hk⟩ | ⟨a, b, hab, hk | hk⟩
    · have hi : i ∈ genSet r := mem_genSet.mpr ⟨k, isSupp_sgn hp hp2 hk⟩
      rw [hk]
      exact Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩)
    · have ha : a ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hk).1⟩
      have hb : b ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hk).2⟩
      rw [hk]
      exact Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩)
    · have ha : a ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hk).1⟩
      have hb : b ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hk).2⟩
      rw [hk, nSwap]
      exact (blockB (p := p) (genSet r)).mul_mem
        ((blockB (p := p) (genSet r)).mul_mem
          (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))
          (Subgroup.subset_closure (Or.inl ⟨b, hb, rfl⟩)))
        (Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩))
  · rw [blockB, Subgroup.closure_le]
    rintro u (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact hsgn i hi
    · exact hpair a ha b hb hab

private lemma main_Q_coord {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ R, u f = f} = p)
    (hR_eq : R = blockB (p := p) (genSet r)) :
    ∃ i0 : Fin n,
      R.map (MulAut.conj (1 : MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom =
        bCoordinateBlock n p i0 := by
  have hfixB : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ blockB (p := p) (genSet r), u f = f} = p := by
    rw [← hR_eq]
    exact hfix
  rw [card_fixB hp hp2 (genSet r)] at hfixB
  have hexp : n - (genSet r).card = 1 := by
    have h1 : p ^ (n - (genSet r).card) = p ^ 1 := by rw [hfixB, pow_one]
    exact Nat.pow_right_injective hp.two_le h1
  obtain ⟨i0, hIeq⟩ := coord_of_card (r := r) hexp
  refine ⟨i0, ?_⟩
  calc R.map (MulAut.conj (1 : MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom
      = R := map_conj_one R
    _ = blockB (p := p) (genSet r) := hR_eq
    _ = blockB (p := p) (Finset.univ.erase i0) := by rw [hIeq]
    _ = bCoordinateBlock n p i0 := blockB_erase i0

private lemma main_D_block {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime)
    (hrn : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hRdef : R = Subgroup.closure (Set.range r)) (hRmem : ∀ k, r k ∈ R)
    (hQ : ¬ ∃ i, sgnAut i ∈ R)
    (hP : ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
      pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
      pSwap p x y ∈ R ∨ nSwap p x y ∈ R) :
    R = blockD (p := p) (genSet r) := by
  have hnoSgn : ∀ k, ¬ ∃ i, r k = sgnAut i := by
    intro k ⟨i, hk⟩
    exact hQ ⟨i, by rw [← hk]; exact hRmem k⟩
  have hR_le : R ≤ blockD (p := p) (genSet r) := by
    rw [hRdef, Subgroup.closure_le]
    rintro u ⟨k, rfl⟩
    rcases hrn k with ⟨i, hk⟩ | ⟨a, b, hab, hk | hk⟩
    · exact absurd ⟨i, hk⟩ (hnoSgn k)
    · have ha : a ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hk).1⟩
      have hb : b ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_pSwap hp hab hk).2⟩
      rw [hk]
      exact Subgroup.subset_closure (Or.inl ⟨a, ha, b, hb, hab, rfl⟩)
    · have ha : a ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hk).1⟩
      have hb : b ∈ genSet r := mem_genSet.mpr ⟨k, (isSupp_nSwap hp hab hk).2⟩
      rw [hk]
      exact Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩)
  have hblockD_le : blockD (p := p) (genSet r) ≤ R := by
    rw [blockD, Subgroup.closure_le]
    rintro u (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact (both_of_P hP hadj a ha b hb hab).1
    · exact (both_of_P hP hadj a ha b hb hab).2
  exact le_antisymm hR_le hblockD_le

private lemma main_D_coord {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ R, u f = f} = p)
    (hP : ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
      pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hR_eq : R = blockD (p := p) (genSet r)) :
    ∃ i0 : Fin n,
      R.map (MulAut.conj (1 : MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom =
        dCoordinateBlock n p i0 := by
  have hIcard2 : 2 ≤ (genSet r).card := by
    obtain ⟨a, ha, b, hb, hab, _⟩ := hP
    have h2 : 1 < (genSet r).card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega
  have hfixD : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ blockD (p := p) (genSet r), u f = f} = p := by
    rw [← hR_eq]
    exact hfix
  rw [card_fixD hp hp2 (genSet r) hIcard2] at hfixD
  have hexp : n - (genSet r).card = 1 := by
    have h1 : p ^ (n - (genSet r).card) = p ^ 1 := by rw [hfixD, pow_one]
    exact Nat.pow_right_injective hp.two_le h1
  obtain ⟨i0, hIeq⟩ := coord_of_card (r := r) hexp
  refine ⟨i0, ?_⟩
  calc R.map (MulAut.conj (1 : MulAut (Fin n → Multiplicative (ZMod p)))).toMonoidHom
      = R := map_conj_one R
    _ = blockD (p := p) (genSet r) := hR_eq
    _ = blockD (p := p) (Finset.univ.erase i0) := by rw [hIeq]
    _ = dCoordinateBlock n p i0 := blockD_erase i0

private lemma main_S_data {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hrn : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hRmem : ∀ k, r k ∈ R)
    (hQ : ¬ ∃ i, sgnAut i ∈ R)
    (hP : ¬ ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
      pSwap p a b ∈ R ∧ nSwap p a b ∈ R)
    (hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
      pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    {z : Fin n} (hzI : z ∈ genSet r) :
    ∃ d : Fin n → ZMod p, (∀ i, d i = 1 ∨ d i = -1) ∧
      (∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b → d a * d b = pSign R a b) ∧
      (∀ k, ∃ a b, a ≠ b ∧ (r k = pSwap p a b ∨ r k = nSwap p a b)) := by
  have hnoSgn : ∀ k, ¬ ∃ i, r k = sgnAut i := by
    intro k ⟨i, hk⟩
    exact hQ ⟨i, by rw [← hk]; exact hRmem k⟩
  have hgenpair : ∀ k, ∃ a b, a ≠ b ∧ (r k = pSwap p a b ∨ r k = nSwap p a b) := by
    intro k
    rcases hrn k with ⟨i, hk⟩ | h
    · exact absurd ⟨i, hk⟩ (hnoSgn k)
    · exact h
  set d : Fin n → ZMod p := dSign R (genSet r) z with hd_def
  have hd_sign : ∀ i, d i = 1 ∨ d i = -1 := fun i => dSign_sign (genSet r) z i
  have hd_pair : ∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b →
      d a * d b = pSign R a b :=
    fun a ha b hb hab => dSign_pair hp hp2 hP hadj hzI ha hb hab
  exact ⟨d, hd_sign, hd_pair, hgenpair⟩

private lemma main_S_delta_mem {n p : ℕ} {d : Fin n → ZMod p}
    (hd_sign : ∀ i, d i = 1 ∨ d i = -1) :
    diagAut d (fun i => coord_sign_mul_self (hd_sign i)) ∈ bSignedFull n p :=
  mem_of_diag (H := bSignedFull n p)
    (hs := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
    Finset.univ _ d hd_sign (fun i hi => absurd (Finset.mem_univ i) hi)
    (fun f i => by rw [diagAut_apply, toAdd_ofAdd])

private lemma main_S_le {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hRdef : R = Subgroup.closure (Set.range r)) (hRmem : ∀ k, r k ∈ R)
    {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1)
    (hd_pair : ∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b → d a * d b = pSign R a b)
    (hgenpair : ∀ k, ∃ a b, a ≠ b ∧ (r k = pSwap p a b ∨ r k = nSwap p a b))
    (hP : ¬ ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
      pSwap p a b ∈ R ∧ nSwap p a b ∈ R) :
    R.map (MulAut.conj (diagAut d hd)).toMonoidHom ≤ blockS (p := p) (genSet r) := by
  rw [hRdef, MonoidHom.map_closure, Subgroup.closure_le]
  rintro u ⟨v, ⟨k, rfl⟩, rfl⟩
  obtain ⟨a, b, hab, hk⟩ := hgenpair k
  have ha : a ∈ genSet r := mem_genSet.mpr ⟨k, by
    rcases hk with hk | hk
    · exact (isSupp_pSwap hp hab hk).1
    · exact (isSupp_nSwap hp hab hk).1⟩
  have hb : b ∈ genSet r := mem_genSet.mpr ⟨k, by
    rcases hk with hk | hk
    · exact (isSupp_pSwap hp hab hk).2
    · exact (isSupp_nSwap hp hab hk).2⟩
  change MulAut.conj (diagAut d hd) (r k) ∈ blockS (p := p) (genSet r)
  rcases hk with hk | hk
  · have hT : pSwap p a b ∈ R := by rw [← hk]; exact hRmem k
    have hdd : d a * d b = 1 := by
      rw [hd_pair a ha b hb hab, (pSign_eq_one_iff hp hp2).2 hT]
    rw [hk, diag_conj_pSwap_one_conj hd hdd]
    exact Subgroup.subset_closure ⟨a, ha, b, hb, hab, rfl⟩
  · have hN : nSwap p a b ∈ R := by rw [← hk]; exact hRmem k
    have hpT : pSwap p a b ∉ R := fun hT => hP ⟨a, ha, b, hb, hab, hT, hN⟩
    have hdd : d a * d b = -1 := by
      rw [hd_pair a ha b hb hab, (pSign_eq_neg_one_iff hp hp2).2 hpT]
    rw [hk, diag_conj_nSwap_conj hd hab hdd]
    exact Subgroup.subset_closure ⟨a, ha, b, hb, hab, rfl⟩

private lemma main_S_ge {n p : ℕ} [NeZero p] {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1)
    (hd_pair : ∀ a ∈ genSet r, ∀ b ∈ genSet r, a ≠ b → d a * d b = pSign R a b)
    (hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
      pSwap p x y ∈ R ∨ nSwap p x y ∈ R)
    (hP : ¬ ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
      pSwap p a b ∈ R ∧ nSwap p a b ∈ R) :
    blockS (p := p) (genSet r) ≤ R.map (MulAut.conj (diagAut d hd)).toMonoidHom := by
  rw [blockS, Subgroup.closure_le]
  rintro u ⟨a, ha, b, hb, hab, rfl⟩
  rcases hadj a ha b hb hab with hT | hN
  · refine Subgroup.mem_map.mpr ⟨pSwap p a b, hT, ?_⟩
    change MulAut.conj (diagAut d hd) (pSwap p a b) = pSwap p a b
    have hdd : d a * d b = 1 := by
      rw [hd_pair a ha b hb hab, (pSign_eq_one_iff hp hp2).2 hT]
    exact diag_conj_pSwap_one_conj hd hdd
  · refine Subgroup.mem_map.mpr ⟨nSwap p a b, hN, ?_⟩
    change MulAut.conj (diagAut d hd) (nSwap p a b) = pSwap p a b
    have hpT : pSwap p a b ∉ R := fun hT' => hP ⟨a, ha, b, hb, hab, hT', hN⟩
    have hdd : d a * d b = -1 := by
      rw [hd_pair a ha b hb hab, (pSign_eq_neg_one_iff hp hp2).2 hpT]
    exact diag_conj_nSwap_conj hd hab hdd

private lemma main_S_final {n p : ℕ} {κ : Type*}
    {r : κ → MulAut (Fin n → Multiplicative (ZMod p))}
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hp : p.Prime)
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ R, u f = f} = p)
    {z : Fin n} (hzI : z ∈ genSet r) {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1)
    (himage : R.map (MulAut.conj (diagAut d hd)).toMonoidHom = blockS (p := p) (genSet r)) :
    R.map (MulAut.conj (diagAut d hd)).toMonoidHom = aPermutationFull n p := by
  have hfixS : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ blockS (p := p) (genSet r), u f = f} = p := by
    rw [← himage]
    rw [card_fix_map_conj (diagAut d hd) R]
    exact hfix
  rw [card_fixS (genSet r) z hzI] at hfixS
  have hexp : n - (genSet r).card + 1 = 1 := by
    have h1 : p ^ (n - (genSet r).card + 1) = p ^ 1 := by rw [hfixS, pow_one]
    exact Nat.pow_right_injective hp.two_le h1
  have hle : (genSet r).card ≤ n := by
    simpa [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (genSet r))
  have hcard : (genSet r).card = n := by omega
  have hIuniv : genSet r = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    by_contra hx
    have hssub : genSet r ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, fun h => hx (h ▸ Finset.mem_univ x)⟩
    have hlt := Finset.card_lt_card hssub
    rw [Finset.card_univ, Fintype.card_fin] at hlt
    omega
  rw [himage, hIuniv, blockS_univ]

theorem exists_conj_eq_block_of_connected {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {κ : Type*}
    (r : κ → MulAut (Fin n → Multiplicative (ZMod p)))
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = permAut (Equiv.swap a b) ∨
        r k = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹))
    (hconn : ∀ k k', Relation.ReflTransGen (fun a b => r a * r b ≠ r b * r a) k k')
    (hfix : Nat.card {f // ∀ u ∈ Subgroup.closure (Set.range r), u f = f} = p) :
    ∃ δ ∈ bSignedFull n p, ∃ i0 : Fin n,
      (Subgroup.closure (Set.range r)).map (MulAut.conj δ).toMonoidHom = bCoordinateBlock n p i0 ∨
        (Subgroup.closure (Set.range r)).map (MulAut.conj δ).toMonoidHom =
          dCoordinateBlock n p i0 ∨
        (Subgroup.closure (Set.range r)).map (MulAut.conj δ).toMonoidHom = aPermutationFull n p := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hrn := hr_norm (p := p) hr
  set R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
    Subgroup.closure (Set.range r) with hRdef
  have hRmem : ∀ k, r k ∈ R := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · obtain ⟨δ, hδ, i0, hi0⟩ := main_empty hp hRdef hfix hκ
    exact ⟨δ, hδ, i0, Or.inl hi0⟩
  · obtain ⟨k₀⟩ := hκ
    obtain ⟨z, hz⟩ := exists_isSupp hp hp2 hrn k₀
    have hzI : z ∈ genSet r := mem_genSet.mpr ⟨k₀, hz⟩
    have hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
        pSwap p x y ∈ R ∨ nSwap p x y ∈ R :=
      fun x hx y hy hxy => main_hadj hp hp2 hrn hconn hRmem x hx y hy hxy
    by_cases hQ : ∃ i, sgnAut i ∈ R
    · have hsgn := main_Q_sgn hp hp2 hrn hRdef hQ hadj
      obtain ⟨i0, hi0⟩ := main_Q_coord hp hp2 hfix
        (main_Q_block hp hp2 hrn hRdef hsgn (main_Q_pair hadj hsgn))
      exact ⟨1, (bSignedFull n p).one_mem, i0, Or.inl hi0⟩
    · by_cases hP : ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
          pSwap p a b ∈ R ∧ nSwap p a b ∈ R
      · obtain ⟨i0, hi0⟩ := main_D_coord hp hp2 hfix hP
          (main_D_block hp hrn hRdef hRmem hQ hP hadj)
        exact ⟨1, (bSignedFull n p).one_mem, i0, Or.inr (Or.inl hi0)⟩
      · obtain ⟨d, hd_sign, hd_pair, hgenpair⟩ := main_S_data hp hp2 hrn hRmem hQ hP hadj hzI
        let hd : ∀ i, d i * d i = 1 := fun i => coord_sign_mul_self (hd_sign i)
        have hδ_mem : diagAut d hd ∈ bSignedFull n p := main_S_delta_mem hd_sign
        have himage : R.map (MulAut.conj (diagAut d hd)).toMonoidHom =
            blockS (p := p) (genSet r) :=
          le_antisymm (main_S_le hp hp2 hRdef hRmem hd hd_pair hgenpair hP)
            (main_S_ge hp hp2 hd hd_pair hadj hP)
        have hfinal := main_S_final hp hfix hzI hd himage
        exact ⟨diagAut d hd, hδ_mem, z, Or.inr (Or.inr hfinal)⟩

private lemma blockB_eq_bBlockOn {n p : ℕ} (I : Finset (Fin n)) :
    blockB (p := p) I = bBlockOn n p I := rfl

private lemma blockD_eq_dBlockOn {n p : ℕ} (I : Finset (Fin n)) :
    blockD (p := p) I = dBlockOn n p I := by
  rw [blockD, dBlockOn]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact Or.inl ⟨a, ha, b, hb, hab, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, hab, by simpa only [pSwap] using nSwap_eq_conj hab⟩
  · rintro (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact Or.inl ⟨a, ha, b, hb, hab, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, hab, by simpa only [pSwap] using (nSwap_eq_conj hab).symm⟩

private lemma blockS_eq_aPermutationOn {n p : ℕ} (I : Finset (Fin n)) :
    blockS (p := p) I = aPermutationOn n p I := rfl

private lemma bBlockOn_empty (n p : ℕ) : bBlockOn n p (∅ : Finset (Fin n)) = ⊥ := by
  rw [bBlockOn]
  have h : {r : MulAut (Fin n → Multiplicative (ZMod p)) |
      (∃ i ∈ (∅ : Finset (Fin n)), r = sgnAut i) ∨
      (∃ a ∈ (∅ : Finset (Fin n)), ∃ b ∈ (∅ : Finset (Fin n)), a ≠ b ∧
        r = permAut (Equiv.swap a b))} = ∅ := by
    ext r
    simp
  rw [h, Subgroup.closure_empty]

private lemma conj_diagAut_involutive {n p : ℕ} [NeZero p] {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (u : MulAut (Fin n → Multiplicative (ZMod p))) :
    MulAut.conj (diagAut d hd) (MulAut.conj (diagAut d hd) u) = u := by
  rw [MulAut.conj_apply, MulAut.conj_apply, diagAut_inv hd]
  calc diagAut d hd * (diagAut d hd * u * diagAut d hd) * diagAut d hd
      = (diagAut d hd * diagAut d hd) * u * (diagAut d hd * diagAut d hd) := by group
    _ = u := by rw [diagAut_mul_self hd]; group

private lemma eq_map_conj_of_map_conj_eq {n p : ℕ} [NeZero p]
    {R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {I : Finset (Fin n)}
    {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1)
    (himage : R.map (MulAut.conj (diagAut d hd)).toMonoidHom = aPermutationOn n p I) :
    R = (aPermutationOn n p I).map (MulAut.conj (diagAut d hd)).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro u hu
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (diagAut d hd) u, ?_,
      conj_diagAut_involutive hd u⟩
    rw [← himage]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← himage] at hv
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
    rw [← hwv]
    change MulAut.conj (diagAut d hd) (MulAut.conj (diagAut d hd) w) ∈ R
    rw [conj_diagAut_involutive hd w]
    exact hw

theorem bBlockOn_univ_erase (n p : ℕ) (i0 : Fin n) :
    bBlockOn n p (Finset.univ.erase i0) = bCoordinateBlock n p i0 := by
  rw [← blockB_eq_bBlockOn, blockB_erase]

theorem aPermutationOn_univ (n p : ℕ) : aPermutationOn n p Finset.univ = aPermutationFull n p := by
  rw [← blockS_eq_aPermutationOn, blockS_univ]

theorem forall_bBlockOn_fix_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ bBlockOn n p I, u f = f) ↔ ∀ i ∈ I, f i = 1 := by
  rw [← blockB_eq_bBlockOn]
  exact fix_blockB hp hp2

theorem forall_dBlockOn_fix_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ dBlockOn n p I, u f = f) ↔ ∀ i ∈ I, f i = 1 := by
  rw [← blockD_eq_dBlockOn]
  exact fix_blockD hp hp2 hI

theorem forall_aPermutationOn_fix_iff {n p : ℕ} (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    (∀ u ∈ aPermutationOn n p I, u f = f) ↔ ∀ i ∈ I, ∀ j ∈ I, f i = f j := by
  rw [← blockS_eq_aPermutationOn]
  exact fix_blockS

theorem card_fix_bBlockOn {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (I : Finset (Fin n)) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ bBlockOn n p I, u f = f} =
      p ^ (n - I.card) := by
  have hcard : Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ bBlockOn n p I, u f = f} =
      Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ blockB (p := p) I, u f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun f => by rw [blockB_eq_bBlockOn])
  rw [hcard]
  exact card_fixB hp hp2 I

theorem card_fix_dBlockOn {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ dBlockOn n p I, u f = f} =
      p ^ (n - I.card) := by
  have hcard : Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ dBlockOn n p I, u f = f} =
      Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ blockD (p := p) I, u f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun f => by rw [blockD_eq_dBlockOn])
  rw [hcard]
  exact card_fixD hp hp2 I hI

theorem card_fix_aPermutationOn {n p : ℕ} {I : Finset (Fin n)} (hI : I.Nonempty) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ aPermutationOn n p I, u f = f} =
      p ^ (n - I.card + 1) := by
  obtain ⟨z, hz⟩ := hI
  have hcard : Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ aPermutationOn n p I, u f = f} =
      Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ blockS (p := p) I, u f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun f => by rw [blockS_eq_aPermutationOn])
  rw [hcard]
  exact card_fixS I z hz

theorem closure_isSignedBlockOn_of_connected {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {κ : Type*}
    (r : κ → MulAut (Fin n → Multiplicative (ZMod p)))
    (hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = permAut (Equiv.swap a b) ∨
        r k = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹))
    (hconn : ∀ k k', Relation.ReflTransGen (fun a b => r a * r b ≠ r b * r a) k k') :
    ∃ I : Finset (Fin n), IsSignedBlockOn n p I (Subgroup.closure (Set.range r)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hrn := hr_norm (p := p) hr
  set R : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
    Subgroup.closure (Set.range r) with hRdef
  have hRmem : ∀ k, r k ∈ R := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have hrange : Set.range r = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨k, rfl⟩
      exact hκ.elim k
    refine ⟨∅, Or.inl ?_⟩
    rw [hRdef, hrange, Subgroup.closure_empty, bBlockOn_empty]
  · obtain ⟨k₀⟩ := hκ
    obtain ⟨z, hz⟩ := exists_isSupp hp hp2 hrn k₀
    have hzI : z ∈ genSet r := mem_genSet.mpr ⟨k₀, hz⟩
    have hadj : ∀ x ∈ genSet r, ∀ y ∈ genSet r, x ≠ y →
        pSwap p x y ∈ R ∨ nSwap p x y ∈ R :=
      fun x hx y hy hxy => main_hadj hp hp2 hrn hconn hRmem x hx y hy hxy
    by_cases hQ : ∃ i, sgnAut i ∈ R
    · have hsgn := main_Q_sgn hp hp2 hrn hRdef hQ hadj
      have hB : R = blockB (p := p) (genSet r) :=
        main_Q_block hp hp2 hrn hRdef hsgn (main_Q_pair hadj hsgn)
      exact ⟨genSet r, Or.inl (by rw [hB, blockB_eq_bBlockOn])⟩
    · by_cases hP : ∃ a ∈ genSet r, ∃ b ∈ genSet r, a ≠ b ∧
          pSwap p a b ∈ R ∧ nSwap p a b ∈ R
      · have hD : R = blockD (p := p) (genSet r) :=
          main_D_block hp hrn hRdef hRmem hQ hP hadj
        have hI2 : 2 ≤ (genSet r).card := by
          obtain ⟨a, ha, b, hb, hab, _⟩ := hP
          have h2 : 1 < (genSet r).card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
          omega
        exact ⟨genSet r, Or.inr (Or.inl ⟨hI2, by rw [hD, blockD_eq_dBlockOn]⟩)⟩
      · obtain ⟨d, hd_sign, hd_pair, hgenpair⟩ :=
          main_S_data hp hp2 hrn hRmem hQ hP hadj hzI
        have hd : ∀ i, d i * d i = 1 := fun i => coord_sign_mul_self (hd_sign i)
        have himage : R.map (MulAut.conj (diagAut d hd)).toMonoidHom =
            blockS (p := p) (genSet r) :=
          le_antisymm (main_S_le hp hp2 hRdef hRmem hd hd_pair hgenpair hP)
            (main_S_ge hp hp2 hd hd_pair hadj hP)
        rw [blockS_eq_aPermutationOn] at himage
        exact ⟨genSet r, Or.inr (Or.inr ⟨d, hd, eq_map_conj_of_map_conj_eq hd himage⟩)⟩

end CFSG.StandardType

end
