module

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase

public import CFSG.Sporadic.Schreier.J4SNoCompCheckBase
public import CFSG.Sporadic.Schreier.J4SKernelBase1
public import CFSG.Sporadic.Schreier.J4SOddLocalBase1
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFormData
public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native MulAction
open scoped Matrix

theorem etaV_foldl (s a : ℕ) (L : List (Fin 11)) :
    toVecD 112 (L.foldl (fun acc j => if a.testBit j.val then O.vmul acc unMats[j.val]! else acc)
      s) = toVecD 112 s ᵥ* φ ((L.map fun j => if a.testBit j.val then u j else 1).prod) := by
  induction L generalizing s with
  | nil => rw [List.foldl_nil, List.map_nil, List.prod_nil, map_one, Matrix.vecMul_one]
  | cons j L ih =>
    have e : toVecD 112 (if a.testBit j.val then O.vmul s unMats[j.val]! else s) =
        toVecD 112 s ᵥ* φ (if a.testBit j.val then u j else 1) := by
      split_ifs
      · rw [unMats_get, ← (rep_u matFacts j).2.2.1]
        exact Sp.toVec_vmul trivial (rep_u matFacts j).1
      · rw [map_one, Matrix.vecMul_one]
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, map_mul, ← Matrix.vecMul_vecMul, e]

theorem etaV_spec
    (s a : ℕ) : toVecD 112 (etaV unMats s a) = toVecD 112 s ᵥ* φ (η a) := by
  rw [etaV, etaV_foldl, η, List.ofFn_eq_map]

theorem η_inv
    (a : ℕ) : (η a)⁻¹ = η a := inv_eq_of_mul_eq_one_right (η_mul_self a)

theorem η_smul_toRow (s a : ℕ) :
    η a • toRow (toVecD 112 s) = toRow (toVecD 112 (etaV unMats s a)) := by
  rw [← ofRow_inj, smul_row, η_inv, ← φ_apply, etaV_spec]
  rfl

theorem rep_mRep (l : ℕ) : Rep Sp φ (mRep l) (repPair l) :=
  rep_wordP (rep_a matFacts) (rep_b matFacts) _

theorem mRep_inv_smul_v {l : ℕ} (hl : l < 7) :
    (mRep l)⁻¹ • v = toRow (toVecD 112 repVecs[l]!) := by
  rw [repVecs_get hl, v, inv_smul_toRow (rep_mRep l)]

theorem fixCard_smul
    {h : J} (hh : h ∈ H) (w : Row) : fixCard (h • w) = fixCard w := by
  unfold fixCard
  refine Nat.card_congr
    { toFun := fun s => ⟨h⁻¹ * s * h, ?_⟩
      invFun := fun s => ⟨h * s * h⁻¹, ?_⟩
      left_inv := fun s => Subtype.ext (by simp only; group)
      right_inv := fun s => Subtype.ext (by simp only; group) }
  · obtain ⟨hsN, hsw⟩ := Subgroup.mem_inf.1 s.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := conj_mem_N_of_mem_H h⁻¹ (H.inv_mem hh) s hsN
      rwa [inv_inv] at this
    · rw [mem_stabilizer_iff] at hsw ⊢
      rw [mul_smul, mul_smul, hsw, inv_smul_smul]
  · obtain ⟨hsN, hsw⟩ := Subgroup.mem_inf.1 s.2
    refine Subgroup.mem_inf.2 ⟨conj_mem_N_of_mem_H h hh s hsN, ?_⟩
    rw [mem_stabilizer_iff] at hsw ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hsw]

theorem fixCard_eq_card (w : Row) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a < 2048, η a • w = w ↔ P a) :
    fixCard w = ((Finset.range 2048).filter P).card := by
  unfold fixCard
  have hmem : ∀ a, a < 2048 → (η a ∈ (N ⊓ stabilizer J w : Subgroup J) ↔ P a) := by
    intro a ha
    rw [Subgroup.mem_inf, mem_stabilizer_iff, ← hP a ha]
    exact ⟨fun h => h.2, fun h => ⟨η_mem_N a, h⟩⟩
  let f : {a // a ∈ (Finset.range 2048).filter P} → (N ⊓ stabilizer J w : Subgroup J) := fun a =>
    ⟨η a.1, (hmem a.1 (Finset.mem_range.1 (Finset.mem_filter.1 a.2).1)).2
      (Finset.mem_filter.1 a.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' := Subtype.ext_iff.1 h
      dsimp only [f] at h'
      exact Subtype.ext (η_injOn (by simpa using (Finset.mem_filter.1 ha).1)
        (by simpa using (Finset.mem_filter.1 hb).1) h')
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, rfl⟩ := exists_η_eq (Subgroup.mem_inf.1 hn).1
      exact ⟨⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, (hmem a ha).1 hn⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem polar_vecMul
    (g : J) (x y : Fin 112 → ZMod 2) :
    QuadraticMap.polar jq (x ᵥ* φ g) (y ᵥ* φ g) = QuadraticMap.polar jq x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.add_vecMul, jq_vecMul, jq_vecMul,
    jq_vecMul]

theorem bilV_smul
    {h : J} (hh : h ∈ H) (w : Row) : bilV (h • w) = bilV w := by
  have hv : h • v = v := mem_stabilizer_iff.1 (H_le_stabilizer_v hh)
  unfold bilV
  rw [← polar_jq, ← polar_jq]
  conv_lhs => rw [← hv]
  rw [smul_row, smul_row]
  exact polar_vecMul h⁻¹ (ofRow v) (ofRow w)

theorem rep_conjPair (l : ℕ) (j : Fin 11) :
    Rep Sp φ ((mRep l)⁻¹ * u j * mRep l) (conjPair l j) :=
  rep_mulP (rep_mulP (rep_invP (rep_mRep l)) (rep_u matFacts j)) (rep_mRep l)

theorem ncommE_sound
    {a : ℕ} {g : J} {Y : Array ℕ} (hY : Sp.WF Y) (hg : Sp.toMat Y = φ g)
    (h : ncommE unMats a Y = true) : η a * g ≠ g * η a := by
  intro hc
  unfold ncommE at h
  obtain ⟨t, -, ht⟩ := List.any_eq_true.1 h
  have e1 : toVecD 112 (O.vmul (etaV unMats (O.unit t) a) Y) =
      toVecD 112 (O.unit t) ᵥ* φ (η a * g) := by
    rw [show toVecD 112 (O.vmul (etaV unMats (O.unit t) a) Y) =
        toVecD 112 (etaV unMats (O.unit t) a) ᵥ* Sp.toMat Y from Sp.toVec_vmul trivial hY,
      etaV_spec, hg, Matrix.vecMul_vecMul, ← map_mul]
  have e2 : toVecD 112 (etaV unMats (O.vmul (O.unit t) Y) a) =
      toVecD 112 (O.unit t) ᵥ* φ (g * η a) := by
    rw [etaV_spec, show toVecD 112 (O.vmul (O.unit t) Y) = toVecD 112 (O.unit t) ᵥ* Sp.toMat Y
        from Sp.toVec_vmul trivial hY, hg, Matrix.vecMul_vecMul, ← map_mul]
  apply Sp.toVec_ne ht
  show toVecD 112 _ = toVecD 112 _
  rw [e1, e2, hc]

theorem η_fourteen_ne_one : η 14 ≠ 1 := by
  intro h
  have := η_injOn (i := 14) (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm)
  omega
