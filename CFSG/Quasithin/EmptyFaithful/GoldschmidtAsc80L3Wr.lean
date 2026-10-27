module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Mono
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Abs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Mod

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def diagHom (p : ℕ) [Fact p.Prime] :
    (ZMod p)ˣ × (ZMod p)ˣ →* SL(3, ZMod p) where
  toFun xy := diagMat xy.1 xy.2 (xy.1 * xy.2)⁻¹ (mul_inv_cancel _)
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagMat]
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagMat, coe_diagMat, coe_diagMat,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    have h3 : (((a * b).1 * (a * b).2)⁻¹ : (ZMod p)ˣ) = (a.1 * a.2)⁻¹ * (b.1 * b.2)⁻¹ := by
      rw [Prod.fst_mul, Prod.snd_mul, mul_mul_mul_comm, mul_inv]
    fin_cases i
    · rfl
    · rfl
    · show (((a * b).1 * (a * b).2)⁻¹ : (ZMod p)ˣ).val = _
      rw [h3, Units.val_mul]
      rfl

theorem diagHom_mem (xy : (ZMod p)ˣ × (ZMod p)ˣ) : diagHom p xy ∈ diagT p :=
  diagMat_mem xy.1 xy.2 _ (mul_inv_cancel _)

@[expose] def fourK (p : ℕ) [Fact p.Prime] : Subgroup ((ZMod p)ˣ × (ZMod p)ˣ) :=
  (powMonoidHom 4 : (ZMod p)ˣ × (ZMod p)ˣ →* (ZMod p)ˣ × (ZMod p)ˣ).ker

theorem isPGroup_fourK : IsPGroup 2 (fourK p) := fun g =>
  ⟨2, Subtype.ext (by simpa using (MonoidHom.mem_ker.mp g.2))⟩

@[expose] noncomputable def evenC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  ((fourK p).map (diagHom p)).map (piL p)

theorem isPGroup_evenC : IsPGroup 2 (evenC p) :=
  (isPGroup_fourK.map (diagHom p)).map (piL p)

@[expose] noncomputable def diagC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  (diagT p).map (piL p)

@[expose] noncomputable def monoC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  (monoT p).map (piL p)

theorem evenC_le_diagC : evenC p ≤ diagC p :=
  Subgroup.map_mono (fun _ ⟨xy, _, h⟩ => h ▸ diagHom_mem xy)

theorem diagC_le_monoC : diagC p ≤ monoC p := Subgroup.map_mono diagT_le_monoT

theorem monoC_le_leviC : monoC p ≤ leviC p := Subgroup.map_mono monoT_le_leviBlock

theorem ker_piL_le_diagT : (piL p).ker ≤ diagT p := by
  rw [ker_piL]
  exact center_le_diagT

theorem ker_piL_le_monoT : (piL p).ker ≤ monoT p := ker_piL_le_diagT.trans diagT_le_monoT

theorem odd_index_monoC (hp : p % 4 = 1) : Odd (monoC p).index := by
  rw [monoC, Subgroup.index_map_eq _ piL_surjective ker_piL_le_monoT]
  exact odd_index_monoT hp

theorem relIndex_diagC_monoC : (diagC p).relIndex (monoC p) = 2 := by
  have h1 := Subgroup.relIndex_mul_index (diagT_le_monoT (p := p))
  rw [relIndex_diagT_monoT] at h1
  have h2 := Subgroup.relIndex_mul_index (diagC_le_monoC (p := p))
  rw [diagC, monoC, Subgroup.index_map_eq _ piL_surjective ker_piL_le_diagT,
    Subgroup.index_map_eq _ piL_surjective ker_piL_le_monoT, ← h1] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2

theorem exists_wreathed_sylow (hp : p % 4 = 1) :
    ∃ U : Subgroup (PSL3 p), IsSylowTwoOf U ⊤ ∧ U ≤ monoC p ∧ evenC p ≤ U ∧ ¬ U ≤ diagC p := by
  obtain ⟨S, hS, hES⟩ := exists_isSylowTwoOf_ge (isPGroup_evenC (p := p))
    (evenC_le_diagC.trans diagC_le_monoC)
  refine ⟨S, isSylowTwoOf_top_of_odd_index (odd_index_monoC hp) hS, hS.1, hES, fun hSD => ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S (diagC p) (monoC p) hSD diagC_le_monoC
  rw [relIndex_diagC_monoC] at h
  exact hS.2.2 (Dvd.intro_left _ h)

end CFSG.Quasithin.E2P.Asc80
