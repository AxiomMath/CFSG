
module

public import CFSG.Sporadic.Schreier.J4SFrattiniBase1
import all CFSG.Sporadic.Schreier.J4SFrattiniBase
import all CFSG.Sporadic.Schreier.J4SFrattiniBase1

public import CFSG.Sporadic.Schreier.J4SSylowNode
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def idxU (g : J) : ℕ := by
  classical
  exact if h : ∃ e < 1024, uElt e = g then Classical.choose h else 0

@[expose] def cU
    (g : J) : Fin 4 → ZMod 2 := toVecD 4 cTable[idxU g]!

@[expose] def fVec
    (s : J) : Fin 5 → ZMod 2 := Fin.cons (ellV (nfA s)) (cU (uElt (nfE s)))

theorem etaV_add
    (a b : Fin 11 → ZMod 2) : etaV (a + b) = etaV a * etaV b := by
  rw [etaV_eq, etaV_eq, etaV_eq, ofAdd_add, map_mul]

theorem η_binOf_eq (a : Fin 11 → ZMod 2) : η (binOf a) = etaV a := by
  rw [η_binOf, etaV_eq]

theorem conj_etaV
    {g : J} {C : Array ℕ} (hg : ActsBy g C) (a : Fin 11 → ZMod 2) :
    g * etaV a * g⁻¹ = etaV (colsMatrix C *ᵥ a) := by
  rw [← η_binOf_eq, hg, ← etaV_toVecD, ← colsMatrix_mulVec, toVecD_binOf]

theorem etaV_mem_N (a : Fin 11 → ZMod 2) : etaV a ∈ N := by
  rw [← η_binOf_eq]
  exact η_mem_N _

theorem nf_unique
    {a a' : Fin 11 → ZMod 2} {e e' : ℕ} (he : e < 1024) (he' : e' < 1024)
    (h : etaV a * uElt e = etaV a' * uElt e') : a = a' ∧ e = e' := by
  obtain ⟨h1, h2⟩ := mul_unique (etaV_mem_N a) (etaV_mem_N a') (uElt_mem_U e) (uElt_mem_U e') h
  exact ⟨etaV_injective h1, uElt_injOn he he' h2⟩

theorem exists_nf
    {s : J} (hs : s ∈ S0) :
    ∃ a : Fin 11 → ZMod 2, ∃ e < 1024, s = etaV a * uElt e := by
  obtain ⟨n, hn, u, hu, rfl⟩ := exists_mul_of_mem_S0 hs
  obtain ⟨a, rfl⟩ := exists_etaV hn
  obtain ⟨e, he, rfl⟩ := mem_U_iff.1 hu
  exact ⟨a, e, he, rfl⟩

theorem idxU_spec
    {g : J} (hg : g ∈ U) : idxU g < 1024 ∧ uElt (idxU g) = g := by
  classical
  have h := mem_U_iff.1 hg
  unfold idxU
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem idxU_uElt
    {e : ℕ} (he : e < 1024) : idxU (uElt e) = e :=
  uElt_injOn (idxU_spec (uElt_mem_U e)).1 he (idxU_spec (uElt_mem_U e)).2

theorem cU_uElt
    {e : ℕ} (he : e < 1024) : cU (uElt e) = toVecD 4 cTable[e]! := by
  rw [cU, idxU_uElt he]

theorem cU_one :
    cU 1 = 0 := by
  rw [← uElt_zero, cU_uElt (by norm_num), c_zero, toVecD_zero]

theorem cU_mul_kgen
    {g : J} (hg : g ∈ U) {i : ℕ} (hi : i < 4) :
    cU (g * kgen i) = cU g + toVecD 4 (2 ^ i) := by
  obtain ⟨he, hge⟩ := idxU_spec hg
  rw [← hge, uElt_mul_kgen he hi, cU_uElt ((elem_all _ he).2.2.2 i hi).1, cU_uElt he,
    (c_all _ he).2 i hi, toVecD_xor]

theorem cU_mul
    {g h : J} (hg : g ∈ U) (hh : h ∈ U) : cU (g * h) = cU g + cU h := by
  have hh' : h ∈ Submonoid.closure (Set.range fun i : Fin 4 => kgen i) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hh
  clear hh
  induction hh' using Submonoid.closure_induction_right with
  | one => rw [mul_one, cU_one, add_zero]
  | mul_right h hh s hs ih =>
    obtain ⟨i, rfl⟩ := hs
    have hhU : h ∈ (U : Subgroup J).toSubmonoid := by
      rw [U, Subgroup.closure_toSubmonoid_of_finite]
      exact hh
    beta_reduce
    rw [← mul_assoc, cU_mul_kgen (U.mul_mem hg hhU) i.isLt, cU_mul_kgen hhU i.isLt, ih,
      add_assoc]

theorem nf_spec
    {s : J} (hs : s ∈ S0) : nfE s < 1024 ∧ s = etaV (nfA s) * uElt (nfE s) := by
  classical
  have h := exists_nf hs
  unfold nfA nfE
  rw [dite_eq_left h, dite_eq_left h]
  exact Classical.choose_spec (Classical.choose_spec h)

theorem nf_eq
    {a : Fin 11 → ZMod 2} {e : ℕ} (he : e < 1024) :
    nfA (etaV a * uElt e) = a ∧ nfE (etaV a * uElt e) = e := by
  have hs : etaV a * uElt e ∈ S0 := S0.mul_mem (N_le_S0 (etaV_mem_N a)) (U_le_S0 (uElt_mem_U e))
  obtain ⟨h1, h2⟩ := nf_spec hs
  obtain ⟨e1, e2⟩ := nf_unique h1 he h2.symm
  exact ⟨e1, e2⟩

theorem nf_mul
    (a b : Fin 11 → ZMod 2) {e e' : ℕ} (he : e < 1024) :
    etaV a * uElt e * (etaV b * uElt e') =
      etaV (a + colsMatrix elementColumns[e]! *ᵥ b) * uElt (idxU (uElt e * uElt e')) := by
  rw [(idxU_spec (U.mul_mem (uElt_mem_U e) (uElt_mem_U e'))).2, etaV_add,
    ← conj_etaV (uElt_acts he) b]
  group

theorem fVec_nf
    (a : Fin 11 → ZMod 2) {e : ℕ} (he : e < 1024) :
    fVec (etaV a * uElt e) = Fin.cons (ellV a) (toVecD 4 cTable[e]!) := by
  rw [fVec, (nf_eq he).1, (nf_eq he).2, cU_uElt he]

theorem fVec_mul
    {s t : J} (hs : s ∈ S0) (ht : t ∈ S0) : fVec (s * t) = fVec s + fVec t := by
  obtain ⟨he, hse⟩ := nf_spec hs
  obtain ⟨he', hte⟩ := nf_spec ht
  have hU := U.mul_mem (uElt_mem_U (nfE s)) (uElt_mem_U (nfE t))
  rw [hse, hte, nf_mul _ _ he, fVec_nf _ (idxU_spec hU).1, fVec_nf _ he, fVec_nf _ he',
    ellV_add, ellV_colsMatrix he, ← cU_uElt (idxU_spec hU).1, (idxU_spec hU).2,
    cU_mul (uElt_mem_U _) (uElt_mem_U _), cU_uElt he, cU_uElt he']
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

theorem one_eq_nf :
    (1 : J) = etaV 0 * uElt 0 := by
  rw [← η_binOf_eq, show binOf 0 = 0 by
    apply toVecD_injective (binOf_lt _) (by norm_num)
    rw [toVecD_binOf, toVecD_zero], η_zero, uElt_zero, mul_one]

theorem fVec_one :
    fVec 1 = 0 := by
  rw [one_eq_nf, fVec_nf 0 (by norm_num), c_zero, toVecD_zero]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [ellV]
  · simp

@[expose] def fS0 :
    S0 →* Multiplicative (Fin 5 → ZMod 2) where
  toFun s := Multiplicative.ofAdd (fVec s)
  map_one' := by
    rw [OneMemClass.coe_one, fVec_one, ofAdd_zero]
  map_mul' s t := by
    rw [Subgroup.coe_mul, fVec_mul s.2 t.2, ofAdd_add]

theorem fS0_apply
    (s : S0) : fS0 s = Multiplicative.ofAdd (fVec s) := rfl

theorem vS_eq_nf :
    vS = etaV (toVecD 11 4) * uElt 0 := by
  rw [uElt_zero, mul_one, etaV_toVecD]
  rfl

theorem kgen_eq_nf
    {i : ℕ} (hi : i < 4) : kgen i = etaV 0 * uElt (rightEdges[0]!)[i]! := by
  rw [etaV_zero, one_mul, ← uElt_mul_kgen (by norm_num) hi, uElt_zero, one_mul]

theorem fVec_vS :
    fVec vS = toVecD 5 1 := by
  rw [vS_eq_nf, fVec_nf _ (by norm_num), c_zero, toVecD_zero]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]
    rw [ellV]
    decide
  · simp only [Fin.cons_succ, Pi.zero_apply, toVecD_apply]
    rw [ite_eq_right]
    simp [Nat.testBit_succ]

theorem fVec_kgen
    {i : ℕ} (hi : i < 4) : fVec (kgen i) = toVecD 5 (2 ^ (i + 1)) := by
  rw [kgen_eq_nf hi, fVec_nf _ ((elem_all 0 (by norm_num)).2.2.2 i hi).1,
    (c_all 0 (by norm_num)).2 i hi,
    c_zero, Nat.zero_xor]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]
    rw [ellV, dotProduct_zero, toVecD_apply, ite_eq_right (by simp)]
  · simp only [Fin.cons_succ, toVecD_apply, Fin.val_succ, Nat.testBit_two_pow]
    by_cases h : i = j.val
    · simp [h]
    · simp [h]

theorem fS0_gensS
    (i : Fin 5) : fS0 (gensS i) = Multiplicative.ofAdd (toVecD 5 (2 ^ i.val)) := by
  rw [fS0_apply, show ((gensS i : S0) : J) = gens5 i from rfl]
  congr 1
  have hv := vec5_apply vS (kgen 0) (kgen 1) (kgen 2) (kgen 3)
  fin_cases i
  · exact (congrArg fVec hv.1).trans fVec_vS
  · exact (congrArg fVec hv.2.1).trans (fVec_kgen (i := 0) (by norm_num))
  · exact (congrArg fVec hv.2.2.1).trans (fVec_kgen (i := 1) (by norm_num))
  · exact (congrArg fVec hv.2.2.2.1).trans (fVec_kgen (i := 2) (by norm_num))
  · exact (congrArg fVec hv.2.2.2.2).trans (fVec_kgen (i := 3) (by norm_num))

theorem fS0_surjective :
    Function.Surjective fS0 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro a _
  have key : ∀ m : ℕ, ∀ a : Multiplicative (Fin 5 → ZMod 2),
      (∀ j : Fin 5, m ≤ j.val → Multiplicative.toAdd a j = 0) → a ∈ fS0.range := by
    intro m
    induction m with
    | zero =>
      intro a ha
      have : a = 1 := by
        apply Multiplicative.toAdd.injective
        funext j
        exact ha j (Nat.zero_le _)
      rw [this]
      exact Subgroup.one_mem _
    | succ m ih =>
      intro a ha
      by_cases hm : m < 5
      · let b : Multiplicative (Fin 5 → ZMod 2) :=
          a * (fS0 (gensS ⟨m, hm⟩)) ^ (Multiplicative.toAdd a ⟨m, hm⟩).val
        have hb : b ∈ fS0.range := by
          refine ih b fun j hj => ?_
          simp only [b, toAdd_mul, toAdd_pow, fS0_gensS, toAdd_ofAdd, Pi.add_apply, Pi.smul_apply]
          rw [toVecD_apply, Nat.testBit_two_pow]
          by_cases hjm : m = j.val
          · have hj' : j = ⟨m, hm⟩ := Fin.ext hjm.symm
            subst hj'
            simp only [decide_true, ite_true, nsmul_eq_mul, mul_one]
            rcases zmod_two_cases (Multiplicative.toAdd a ⟨m, hm⟩) with h | h
            · rw [h]; rfl
            · rw [h]; rfl
          · simp only [hjm, decide_false, Bool.false_eq_true, ite_false, smul_zero, add_zero]
            exact ha j (by omega)
        exact (fS0.range.mul_mem_cancel_right
          (fS0.range.pow_mem ⟨gensS ⟨m, hm⟩, rfl⟩ _)).1 hb
      · exact ih a fun j hj => ha j (by omega)
  exact key 5 a fun j hj => absurd j.isLt (by omega)

theorem frattini_le_ker :
    frattini S0 ≤ fS0.ker := by
  have h := frattini_le_comap_frattini_of_surjective fS0_surjective
  rwa [frattini_F2five] at h

theorem isPGroup_S0 :
    IsPGroup 2 S0 := IsPGroup.of_card card_S0

theorem card_quot_frattini_le :
    Nat.card (S0 ⧸ frattini S0) ≤ 2 ^ 5 := by
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient isPGroup_S0
  let _ : CommGroup (S0 ⧸ frattini S0) := IsMulCommutative.instCommGroup
  let w : Fin 5 → S0 ⧸ frattini S0 := fun i => QuotientGroup.mk' _ (gensS i)
  have hgen : Subgroup.closure (Set.range w) = ⊤ := by
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (frattini S0))) closure_gensS
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), ← Set.range_comp] at h2
    exact h2
  exact card_le_of_closure_two w (fun i => hpow _) hgen

theorem card_ker_fS0 :
    Nat.card fS0.ker = 2 ^ 16 := by
  have h := card_ker_mul_card_range fS0
  rw [MonoidHom.range_eq_top.2 fS0_surjective, Subgroup.card_top, card_S0,
    Nat.card_eq_fintype_card (α := Multiplicative (Fin 5 → ZMod 2))] at h
  simp only [Fintype.card_multiplicative, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  omega

theorem ker_fS0 :
    fS0.ker = frattini S0 := by
  refine (Subgroup.eq_of_le_of_card_ge frattini_le_ker ?_).symm
  have h1 := card_quot_frattini_le
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini S0)
  rw [card_S0] at h2
  rw [card_ker_fS0]
  by_contra hlt
  push Not at hlt
  have : Nat.card (S0 ⧸ frattini S0) * Nat.card (frattini S0) < 2 ^ 5 * 2 ^ 16 :=
    Nat.mul_lt_mul_of_le_of_lt h1 hlt (by norm_num)
  omega

theorem card_fiber
    (a : Multiplicative (Fin 5 → ZMod 2)) :
    Nat.card {s : S0 // fS0 s = a} = 65536 := by
  obtain ⟨s₀, hs₀⟩ := fS0_surjective a
  have e : {s : S0 // fS0 s = a} ≃ fS0.ker :=
    { toFun := fun s => ⟨s₀⁻¹ * s, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hs₀, s.2]
        exact inv_mul_cancel a⟩
      invFun := fun k => ⟨s₀ * k, by rw [map_mul, hs₀, MonoidHom.mem_ker.1 k.2, mul_one]⟩
      left_inv := fun s => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun k => Subtype.ext (inv_mul_cancel_left _ _) }
  rw [Nat.card_congr e, card_ker_fS0]
  norm_num

theorem fS0_unique
    (g : S0 →* Multiplicative (Fin 5 → ZMod 2))
    (hg : ∀ i, g (gensS i) = fS0 (gensS i)) : g = fS0 :=
  MonoidHom.eq_of_eqOn_dense closure_gensS fun _ ⟨i, hi⟩ => hi ▸ hg i

theorem R3E_J4_exact_Sylow_two_Frattini_coordinates :
    ∃ f : S0 →* Multiplicative (Fin 5 → ZMod 2),
      (f ⟨vS, vS_mem_S0⟩ = Multiplicative.ofAdd (toVecD 5 1) ∧
        ∀ i : Fin 4, f ⟨kgen i, kgen_mem_S0 i⟩ =
          Multiplicative.ofAdd (toVecD 5 (2 ^ (i.val + 1)))) ∧
      (∀ g : S0 →* Multiplicative (Fin 5 → ZMod 2),
        g ⟨vS, vS_mem_S0⟩ = Multiplicative.ofAdd (toVecD 5 1) →
        (∀ i : Fin 4, g ⟨kgen i, kgen_mem_S0 i⟩ =
          Multiplicative.ofAdd (toVecD 5 (2 ^ (i.val + 1)))) → g = f) ∧
      Function.Surjective f ∧ f.ker = frattini S0 ∧
      (∀ a, Nat.card {s : S0 // f s = a} = 65536) ∧
      Nonempty (S0 ⧸ frattini S0 ≃* Multiplicative (Fin 5 → ZMod 2)) := by
  have hv : fS0 ⟨vS, vS_mem_S0⟩ = Multiplicative.ofAdd (toVecD 5 1) := fS0_gensS 0
  have hk : ∀ i : Fin 4, fS0 ⟨kgen i, kgen_mem_S0 i⟩ =
      Multiplicative.ofAdd (toVecD 5 (2 ^ (i.val + 1))) := by
    intro i
    fin_cases i
    · exact fS0_gensS 1
    · exact fS0_gensS 2
    · exact fS0_gensS 3
    · exact fS0_gensS 4
  refine ⟨fS0, ⟨hv, hk⟩, fun g hgv hgk => fS0_unique g fun i => ?_, fS0_surjective, ker_fS0,
    card_fiber, ⟨(QuotientGroup.quotientMulEquivOfEq ker_fS0.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fS0 fS0_surjective)⟩⟩
  fin_cases i
  · exact hgv.trans hv.symm
  · exact (hgk 0).trans (hk 0).symm
  · exact (hgk 1).trans (hk 1).symm
  · exact (hgk 2).trans (hk 2).symm
  · exact (hgk 3).trans (hk 3).symm

end CFSG.Sporadic.J4Schreier
