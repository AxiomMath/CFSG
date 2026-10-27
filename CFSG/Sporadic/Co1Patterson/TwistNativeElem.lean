module

public import CFSG.Sporadic.Co1Patterson.TwistNativeSys
public import CFSG.Sporadic.Co1Patterson.TwistNativeIota

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (ind)

theorem conjOK_spec
    {h : Native.Rows} {g : GL24} (hg : MRep h g) {m : List ℕ}
    (hc : conjOK h m = true) : ∀ k < 8, g * yG k * g⁻¹ = yprodG (m.getD k 0) ∨
      g * yG k * g⁻¹ = yprodG (m.getD k 0) * aG := by
  simp only [conjOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hc
  obtain ⟨hinv, hk⟩ := hc
  have hgi : MRep (Native.inv h) g⁻¹ := hg.inv hinv
  intro k hk8
  have hx := (hg.mul (rep_yG k)).mul hgi
  rcases hk k hk8 with h1 | h1 <;> rw [h1] at hx
  · exact Or.inl (hx.eq (rep_yprodG _))
  · exact Or.inr (hx.eq ((rep_yprodG _).mul rep_iotaA))

theorem comm_of_rows {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (he : Native.mul X Y = Native.mul Y X) : g * h = h * g :=
  (hX.mul hY).eq (he ▸ hY.mul hX)

theorem bv_colsApply_two_pow (m : List ℕ) {k : ℕ} (hk : k < 8) :
    bv (colsApply m (2 ^ k)) = bv (m.getD k 0) := by
  rw [bv_colsApply, Finset.sum_eq_single ⟨k, hk⟩]
  · rw [Nat.testBit_two_pow_self]
    simp [ind]
  · intro i _ hi
    have : (2 ^ k).testBit i = false := by
      rw [Nat.testBit_two_pow]
      exact decide_eq_false fun h => hi (Fin.ext h.symm)
    rw [this]
    simp [ind]
  · simp

theorem elemsOK_parts :
    (∀ i < 6, conjOK (twRow (hIdx.getD i 0)) (wordCols (uWords.getD i [])) = true ∧
      Native.mul (twRow (hIdx.getD i 0)) iotaARows =
        Native.mul iotaARows (twRow (hIdx.getD i 0)) ∧
      Native.mul (twRow (hIdx.getD i 0)) (yRow 0) =
        Native.mul (yRow 0) (twRow (hIdx.getD i 0))) ∧
    (∀ i < 2, conjOK (twRow (kIdx.getD i 0)) (kCols.getD i []) = true ∧
      Native.mul (twRow (kIdx.getD i 0)) iotaARows =
        Native.mul iotaARows (twRow (kIdx.getD i 0)) ∧
      Native.mul (twRow (kIdx.getD i 0)) (yRow 0) =
        Native.mul (yRow 0) (twRow (kIdx.getD i 0))) ∧
    (conjOK (twRow h4Idx) h4Cols = true ∧
      Native.mul (twRow h4Idx) iotaARows = Native.mul iotaARows (twRow h4Idx)) ∧
    (conjOK (twRow h4pIdx) (colsMul (colsMul betaCols h4Cols) betaCols) = true ∧
      Native.mul (twRow h4pIdx) iotaARows = Native.mul iotaARows (twRow h4pIdx)) := by
  have h := tw_elems_check
  simp only [elemsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨fun i hi => ⟨(h.1.1.1 i hi).1.1, (h.1.1.1 i hi).1.2, (h.1.1.1 i hi).2⟩,
    fun i hi => ⟨(h.1.1.2 i hi).1.1, (h.1.1.2 i hi).1.2, (h.1.1.2 i hi).2⟩, h.1.2, h.2⟩

theorem uWords_lt : ∀ i < 6, ∀ j ∈ uWords.getD i [], j < 8 := by decide

section Rows


theorem twG_mem_cent {j : ℕ}
    (h : Native.mul (twRow j) iotaARows = Native.mul iotaARows (twRow j)) :
    twG j ∈ GA ⊓ centralizer {aG} :=
  mem_inf.2 ⟨twG_mem_GA j, mem_centralizer_singleton_iff.2
    (comm_of_rows (rep_twG j) rep_iotaA h)⟩

noncomputable irreducible_def twH
    (j : ℕ) :
    centralizer ({aNC} : Set NativeSporadic.Co1) :=
  if h : Native.mul (twRow j) iotaARows = Native.mul iotaARows (twRow j) then
    toH (twG j) (twG_mem_cent h) else 1

theorem centEmb_twH {j : ℕ}
    (h : Native.mul (twRow j) iotaARows = Native.mul iotaARows (twRow j)) :
    centEmb (twH j) = twG j := by
  rw [twH_def, dite_eq_left h, centEmb_toH]

end Rows


theorem twH_conj {j : ℕ}
    (h : Native.mul (twRow j) iotaARows = Native.mul iotaARows (twRow j)) {m : List ℕ}
    (hc : conjOK (twRow j) m = true) :
    ∀ k < 8, twH j * yH k * (twH j)⁻¹ = yprodH (m.getD k 0) ∨
      twH j * yH k * (twH j)⁻¹ = yprodH (m.getD k 0) * typeSystemC.z := by
  intro k hk
  have hz : centEmb typeSystemC.z = aG := centEmb_zM
  rcases conjOK_spec (rep_twG j) hc k hk with h1 | h1
  · left
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_twH h, centEmb_yH, centEmb_yprodH, h1]
  · right
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_twH h, centEmb_yH, map_mul, centEmb_yprodH, hz, h1]

theorem hasCols_twH {j : ℕ}
    (h : Native.mul (twRow j) iotaARows = Native.mul iotaARows (twRow j)) {m : List ℕ}
    (hc : conjOK (twRow j) m = true) :
    HasCols (((typeSystemC.φ (twH j) : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) m := fun k hk =>
  (phi_bv_of_conj (twH j) m (twH_conj h hc) (2 ^ k)).trans (bv_colsApply_two_pow m hk)

@[expose] noncomputable def hH (i : ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  twH (hIdx.getD i 0)

@[expose] noncomputable def kH (i : ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  twH (kIdx.getD i 0)

@[expose] noncomputable def h4H : centralizer ({aNC} : Set NativeSporadic.Co1) := twH h4Idx

@[expose] noncomputable def h4pH : centralizer ({aNC} : Set NativeSporadic.Co1) := twH h4pIdx

theorem centEmb_hH {i : ℕ} (hi : i < 6) : centEmb (hH i) = twG (hIdx.getD i 0) :=
  centEmb_twH (elemsOK_parts.1 i hi).2.1

theorem phi_hH {i : ℕ} (hi : i < 6) : typeSystemC.φ (hH i) = eichWord (uWords.getD i []) :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (HasCols.ext
    (hasCols_twH (elemsOK_parts.1 i hi).2.1 (elemsOK_parts.1 i hi).1)
    (hasCols_eichWord _ (uWords_lt i hi))))

theorem hH_comm {i : ℕ} (hi : i < 6) : hH i * yH 0 = yH 0 * hH i := by
  apply centEmb_injective
  rw [map_mul, map_mul, centEmb_hH hi, centEmb_yH]
  exact comm_of_rows (rep_twG _) (rep_yG 0) (elemsOK_parts.1 i hi).2.2

theorem kH_comm {i : ℕ} (hi : i < 2) : kH i * yH 0 = yH 0 * kH i := by
  apply centEmb_injective
  rw [map_mul, map_mul, kH, centEmb_twH (elemsOK_parts.2.1 i hi).2.1, centEmb_yH]
  exact comm_of_rows (rep_twG _) (rep_yG 0) (elemsOK_parts.2.1 i hi).2.2

theorem hasCols_kH {i : ℕ} (hi : i < 2) :
    HasCols (((typeSystemC.φ (kH i) : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (kCols.getD i []) :=
  hasCols_twH (elemsOK_parts.2.1 i hi).2.1 (elemsOK_parts.2.1 i hi).1

theorem hasCols_h4H :
    HasCols (((typeSystemC.φ h4H : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) h4Cols := by
  have e : h4H = twH h4Idx := rfl
  rw [e]
  exact hasCols_twH elemsOK_parts.2.2.1.2 elemsOK_parts.2.2.1.1

theorem hasCols_h4pH :
    HasCols (((typeSystemC.φ h4pH : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2))
      (colsMul (colsMul betaCols h4Cols) betaCols) :=
  hasCols_twH elemsOK_parts.2.2.2.2 elemsOK_parts.2.2.2.1

@[expose] noncomputable def hcH (c : ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  (List.range 6).foldl (fun acc i => if c.testBit i then acc * hH i else acc) 1

theorem rep_hcH (c : ℕ) : MRep (hprodRow c) (centEmb (hcH c)) := by
  rw [hcH, map_foldl_if, map_one]
  have e : (List.range 6).foldl (fun b i => if c.testBit i then b * centEmb (hH i) else b) 1 =
      (List.range 6).foldl (fun b i => if c.testBit i then b * twG (hIdx.getD i 0) else b) 1 :=
    List.foldl_ext _ _ _ fun b i hi => by rw [centEmb_hH (List.mem_range.1 hi)]
  rw [e]
  exact rep_foldl_if _ _ _ _ (fun i _ => rep_twG _) MRep.one

theorem valid_hprodRow (c : ℕ) : CFSG.Sporadic.Co1.InvNative.validRows (hprodRow c) = true :=
  valid_foldl_if _ _ _ (fun i hi => dagOK_parts.2.2.2.2 _ (by
    have hi' := List.mem_range.1 hi
    interval_cases i <;> decide)) validRows_one

theorem phi_hcH (c : ℕ) : typeSystemC.φ (hcH c) =
    (List.range 6).foldl (fun acc i => if c.testBit i then acc * eichWord (uWords.getD i [])
      else acc) 1 := by
  rw [hcH, map_foldl_if, map_one]
  exact List.foldl_ext _ _ _ fun b i hi => by rw [phi_hH (List.mem_range.1 hi)]

theorem hcH_mem_centralizer (c : ℕ) :
    hcH c ∈ centralizer ({yH 0} : Set (centralizer ({aNC} : Set NativeSporadic.Co1))) := by
  unfold hcH
  refine foldl_if_mem (H := centralizer ({yH 0} : Set (centralizer ({aNC} :
    Set NativeSporadic.Co1)))) (List.range 6) (fun i => c.testBit i) hH (fun i hi => ?_)
    (one_mem _)
  exact mem_centralizer_singleton_iff.2 (hH_comm (List.mem_range.1 hi))

@[expose] noncomputable def aElt (p : ℕ × ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  if p.2 = 1 then yprodH p.1 * typeSystemC.z else yprodH p.1

theorem rep_aElt (p : ℕ × ℕ) : MRep (aRowOf p) (centEmb (aElt p)) := by
  rw [aElt, aRowOf]
  split_ifs
  · have hz : centEmb typeSystemC.z = aG := centEmb_zM
    rw [map_mul, centEmb_yprodH, hz]
    exact (rep_yprodG _).mul rep_iotaA
  · rw [centEmb_yprodH]
    exact rep_yprodG _

theorem valid_aRowOf {p : ℕ × ℕ} (hp : p.1 < 256) :
    CFSG.Sporadic.Co1.InvNative.validRows (aRowOf p) = true := by
  rw [aRowOf]
  split_ifs
  · exact valid_mul (dagOK_parts.2.2.2.1 _ hp) dagOK_parts.2.1
  · exact dagOK_parts.2.2.2.1 _ hp

end CFSG.Sporadic.Co1Patterson.TwistNative
