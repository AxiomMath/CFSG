
module

public import CFSG.Sporadic.Co1.Module.OddFactsBase
public import Certificates.Data.CFSGNative.Co1.OddCent
public import CFSG.Sporadic.Co1.Module.OddCentCardInputs
public meta import CFSG.Sporadic.Co1.Module.OddChecksBase
public meta import Certificates.Data.CFSGNative.Co1.OddCent
public meta import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.OddBuildBase
public import CFSG.Sporadic.Co1.Module.OddChecksBase
public meta import CFSG.Sporadic.Co1.Module.OddChecksInputs
public import CFSG.Sporadic.Co1.Module.OddLit
public meta import CFSG.Sporadic.Co1.Module.OddLitInputs
public meta import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.Setup
public meta import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Suz.W64Spec

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.OddCentNative Matrix

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows

section Counting

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]

theorem card_mul_card_stab_le (C : Subgroup G) (ω : Ω) (n : ℕ) (t : ℕ → G)
    (ht : ∀ i < n, t i ∈ C) (hdist : ∀ i < n, ∀ j < n, t i • ω = t j • ω → i = j) :
    n * Nat.card ↥(MulAction.stabilizer G ω ⊓ C) ≤ Nat.card ↥C := by
  let S : Subgroup G := MulAction.stabilizer G ω ⊓ C
  let F : Fin n × ↥S → ↥C := fun p =>
    ⟨t p.1 * (p.2 : G), C.mul_mem (ht p.1 p.1.2) (Subgroup.mem_inf.1 p.2.2).2⟩
  have hF : Function.Injective F := by
    rintro ⟨i, h⟩ ⟨j, h'⟩ e
    have e1 : t i * (h : G) = t j * (h' : G) := congrArg Subtype.val e
    have hh : (h : G) • ω = ω := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h.2).1
    have hh' : (h' : G) • ω = ω := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h'.2).1
    have e2 : t i • ω = t j • ω := by
      have := congrArg (fun g => g • ω) e1
      simpa only [mul_smul, hh, hh'] using this
    have hij : i = j := Fin.ext (hdist i i.2 j j.2 e2)
    subst hij
    have : (h : G) = h' := mul_left_cancel e1
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  exact this

theorem card_ge_of_conj_orbit (K : Subgroup G) (s : G) (I : Set ℕ) (m : ℕ) (g z : ℕ → G)
    (hg : ∀ i ∈ I, ∃ c ∈ K, g i = c * s * c⁻¹)
    (hginj : ∀ i ∈ I, ∀ j ∈ I, g i = g j → i = j)
    (hz : ∀ j < m, z j ∈ K ⊓ Subgroup.centralizer ({s} : Set G))
    (hzinj : ∀ i < m, ∀ j < m, z i = z j → i = j) :
    I.ncard * m ≤ Nat.card ↥K := by
  classical
  choose! c hcK hcg using hg
  let Φ : ℕ × ℕ → G := fun p => c p.1 * z p.2
  have hzK : ∀ j < m, z j ∈ K := fun j hj => (Subgroup.mem_inf.1 (hz j hj)).1
  have hzs : ∀ j < m, z j * s = s * z j := fun j hj =>
    comm_of_mem_centralizer (Subgroup.mem_inf.1 (hz j hj)).2
  have hmaps : ∀ p ∈ I ×ˢ Set.Iio m, Φ p ∈ (K : Set G) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    exact K.mul_mem (hcK i hi) (hzK j hj)
  have hinj : Set.InjOn Φ (I ×ˢ Set.Iio m) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩ ⟨i', j'⟩ ⟨hi', hj'⟩ e
    have e1 : c i * z j = c i' * z j' := e
    have hconj : ∀ (a b : ℕ), a ∈ I → b < m → (c a * z b) * s * (c a * z b)⁻¹ = g a := by
      intro a b ha hb
      calc (c a * z b) * s * (c a * z b)⁻¹ = c a * (z b * s * (z b)⁻¹) * (c a)⁻¹ := by group
        _ = c a * s * (c a)⁻¹ := by rw [hzs b hb]; group
        _ = g a := (hcg a ha).symm
    have hgg : g i = g i' := by
      rw [← hconj i j hi hj, ← hconj i' j' hi' hj', e1]
    have hii : i = i' := hginj i hi i' hi' hgg
    subst hii
    have : z j = z j' := mul_left_cancel e1
    have hjj : j = j' := hzinj j hj j' hj' this
    rw [hjj]
  have hle := Set.ncard_le_ncard_of_injOn Φ hmaps hinj (Set.toFinite _)
  rw [Set.ncard_prod, Set.ncard_Iio_nat] at hle
  have e : Nat.card ↥K = (K : Set G).ncard := Nat.card_coe_set_eq (K : Set G)
  rw [e]
  exact hle

end Counting

noncomputable def regsG3 :
    List NativeSporadic.Co1 := runEval [eA, eB, rho3] prog3

noncomputable def reg3
    (i : ℕ) : NativeSporadic.Co1 := regsG3.getD i 1

theorem initRows3_two : initRows3[2]?.getD (idRows 24) = rr 27 := by simp [initRows3]

theorem getD_two :
    [eA, eB, rho3].getD 2 (1 : NativeSporadic.Co1) = rho3 := rfl

theorem regs_rel3 : RegsRel mat regsG3 regsRows3 := by
  refine runRows_spec mat prog3 ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact mat_eA
  | 1 => exact mat_eB
  | 2 =>
    rw [initRows3_two, getD_two]
    exact mat_reg 27
  | i + 3 => simp [rowsMatrix_idRows, initRows3]

theorem mat_reg3
    (i : ℕ) : mat (reg3 i) = rowsMatrix 24 (rr3 i) := regs_rel3.2 i

theorem map_toArray_get3 (f : ℕ → Array ℕ) (L : List ℕ) {l : ℕ} (hl : l < L.length) :
    (L.map f).toArray[l]! = f (L[l]!) := by
  rw [getElem!_pos (L.map f).toArray l (by simpa using hl), getElem!_pos L l hl]
  simp

theorem reg3_mem_centralizer {i : ℕ}
    (h : mulRows 24 (rr3 i) (rr 27) = mulRows 24 (rr 27) (rr3 i)) :
    reg3 i ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  show mat (reg3 i * reg 27) = mat (reg 27 * reg3 i)
  simp only [map_mul, mat_reg, mat_reg3]
  rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows, h]

theorem arr_map_get (f : Array ℕ → Array ℕ) (a : Array (Array ℕ)) {l : ℕ} (hl : l < a.size) :
    (a.map f)[l]! = f a[l]! := by
  rw [getElem!_pos (a.map f) l (by simpa using hl), getElem!_pos a l hl]
  simp

theorem vtree_step (Gr : Array (Array ℕ)) (yy : ℕ → NativeSporadic.Co1) (l : ℕ)
    (hl : l < Gr.size) (hy : ∀ l < Gr.size, mat (yy l) = rowsMatrix 24 Gr[l]!)
    (x' : NativeSporadic.Co1) (root p q : ℕ) (hxe : co1Act x' (toVecD 24 root) = toVecD 24 p)
    (hpt : q = vecMulN 24 (transposeRows 24 Gr[l]!) p) :
    co1Act (yy l * x') (toVecD 24 root) = toVecD 24 q := by
  have e1 : co1Act (yy l * x') (toVecD 24 root) = co1Act (yy l) (co1Act x' (toVecD 24 root)) :=
    co1Act_mul' _ _ _
  rw [e1, hxe, co1Act_eq_mulVec, hy l hl, rowsMatrix_mulVec, hpt]

theorem vtreeOK_sound {Gr : Array (Array ℕ)} {root : ℕ} {T : VTree}
    (h : vtreeOK Gr root T = true) (yy : ℕ → NativeSporadic.Co1)
    (hy : ∀ l < Gr.size, mat (yy l) = rowsMatrix 24 Gr[l]!)
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < Gr.size, yy l ∈ K) :
    ∃ t : ℕ → NativeSporadic.Co1,
      (∀ i < T.pts.size, t i ∈ K ∧ co1Act (t i) (toVecD 24 root) = toVecD 24 T.pts[i]!) ∧
      ∀ i < T.pts.size, ∀ j < T.pts.size, toVecD 24 T.pts[i]! = toVecD 24 T.pts[j]! → i = j := by
  unfold vtreeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hpos, hpar⟩, hlab⟩, hall⟩, hdist⟩ := h
  have hlt : ∀ i < T.pts.size, T.pts[i]! < 16777216 := by
    intro i hi
    have hp := hall i hi
    simp only [vtreePointOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1
  have hmain : ∀ i, i < T.pts.size → ∃ x ∈ K,
      co1Act x (toVecD 24 root) = toVecD 24 T.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hall i hi
      simp only [vtreePointOK, Bool.and_eq_true] at hp
      obtain ⟨-, hp2⟩ := hp
      by_cases hi0 : i = 0
      · subst hi0
        simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq] at hp2
        refine ⟨1, K.one_mem, ?_⟩
        rw [hp2]
        exact co1Act_one' _
      · simp only [beq_iff_eq, hi0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hp2
        obtain ⟨⟨hpar', hlab'⟩, hpt⟩ := hp2
        have hl : T.lab[i]! < Gr.size := by simpa using hlab'
        obtain ⟨x', hx', hxe⟩ := ih (T.par[i]!) hpar' (by omega)
        have hpt' : T.pts[i]! = vecMulN 24 (transposeRows 24 Gr[T.lab[i]!]!) T.pts[T.par[i]!]! := by
          rw [hpt, arr_map_get (transposeRows 24) Gr hl]
        exact ⟨yy (T.lab[i]!) * x', K.mul_mem (hK _ hl) hx',
          vtree_step Gr yy (T.lab[i]!) hl hy x' root _ _ hxe hpt'⟩
  choose! x hx using hmain
  refine ⟨x, fun i hi => hx i hi, ?_⟩
  intro i hi j hj hij
  have h1 : T.pts[i]! = T.pts[j]! :=
    toVecD_injective (lt_of_lt_of_eq (hlt i hi) (by norm_num)) (lt_of_lt_of_eq (hlt j hj)
      (by norm_num)) hij
  have hnd := distinctKeys_nodup hdist
  have hgi : T.pts.toList[i]'(by simpa using hi) = T.pts[i]! := by
    simp [getElem!_pos T.pts i hi]
  have hgj : T.pts.toList[j]'(by simpa using hj) = T.pts[j]! := by
    simp [getElem!_pos T.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans (h1.trans hgj.symm))

end CFSG.Sporadic.Co1.Module.Odd
