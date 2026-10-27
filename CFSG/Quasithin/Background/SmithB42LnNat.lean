module

public import CFSG.Quasithin.Background.SmithB42LnBase
public import CFSG.Quasithin.Background.SmithB51LnChief
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.B3Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace B42Ln

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln Matrix Module
open scoped Matrix

variable {n : ℕ}

@[expose] def axisVec (j : Fin n) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) j)

theorem mem_axisVec {j : Fin n} {x : Fin n → ZMod 2} : x ∈ axisVec j ↔ x j = 0 := Iff.rfl

@[expose] def tvMat (j : Fin n) (w : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  1 + vecMulVec w (Pi.single j 1)

theorem tvMat_mulVec (j : Fin n) (w x : Fin n → ZMod 2) :
    tvMat j w *ᵥ x = x + x j • w := by
  rw [tvMat, add_mulVec, one_mulVec]
  congr 1
  ext i
  simp [vecMulVec, mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem tvMat_mul {j : Fin n} (w : Fin n → ZMod 2) {v : Fin n → ZMod 2} (hv : v j = 0) :
    tvMat j w * tvMat j v = tvMat j (w + v) := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← mulVec_mulVec, tvMat_mulVec, tvMat_mulVec, tvMat_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, hv, smul_eq_mul, mul_zero, add_zero, smul_add]
  abel

theorem tvMat_zero (j : Fin n) : tvMat j 0 = 1 := by
  simp [tvMat]

theorem tvMat_mul_self {j : Fin n} {w : Fin n → ZMod 2} (hw : w j = 0) :
    tvMat j w * tvMat j w = 1 := by
  rw [tvMat_mul _ hw, ← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul,
    tvMat_zero]

@[expose] def tv (j : Fin n) (w : ↥(axisVec j)) : ↥(StatedSL n (ZMod 2)) :=
  ofGL ⟨tvMat j w, tvMat j w, tvMat_mul_self w.2, tvMat_mul_self w.2⟩

theorem mat_tv (j : Fin n) (w : ↥(axisVec j)) : mat (tv j w) = tvMat j w := rfl

@[expose] def tvHom (j : Fin n) : Multiplicative ↥(axisVec j) →* ↥(StatedSL n (ZMod 2)) where
  toFun w := tv j (Multiplicative.toAdd w)
  map_one' := by
    apply mat_injective
    rw [mat_tv, mat_one]
    exact tvMat_zero j
  map_mul' w v := by
    apply mat_injective
    rw [mat_mul, mat_tv, mat_tv, mat_tv, tvMat_mul _ (Multiplicative.toAdd v).2]
    rfl

theorem tvHom_injective (j : Fin n) : Function.Injective (tvHom j) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h1 := congrArg mat hw
  rw [mat_one] at h1
  have h2 := congrArg (· *ᵥ (Pi.single j 1 : Fin n → ZMod 2)) h1
  simp only [tvHom, MonoidHom.coe_mk, OneHom.coe_mk, mat_tv, tvMat_mulVec, one_mulVec,
    Pi.single_eq_same, one_smul, add_eq_left] at h2
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact Subtype.ext h2

@[expose] def axisGrp (j : Fin n) : Subgroup ↥(StatedSL n (ZMod 2)) := (tvHom j).range

theorem mem_axisGrp {j : Fin n} {γ : ↥(StatedSL n (ZMod 2))} :
    γ ∈ axisGrp j ↔ ∃ w : ↥(axisVec j), tv j w = γ := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨Multiplicative.toAdd w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨Multiplicative.ofAdd w, rfl⟩

theorem finrank_axisVec (j : Fin n) : finrank (ZMod 2) (axisVec j) = n - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) j)
  have h2 : LinearMap.range (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) j) =
      ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single j c, by simp⟩
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  unfold axisVec
  omega

theorem card_axisGrp (j : Fin n) : Nat.card (axisGrp j) = 2 ^ (n - 1) := by
  rw [axisGrp, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (tvHom_injective j),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_axisVec]

theorem axisGrp_comm {j : Fin n} {γ δ : ↥(StatedSL n (ZMod 2))} (hγ : γ ∈ axisGrp j)
    (hδ : δ ∈ axisGrp j) : γ * δ = δ * γ := by
  obtain ⟨w, rfl⟩ := hγ
  obtain ⟨v, rfl⟩ := hδ
  rw [← map_mul, ← map_mul, mul_comm]

theorem axisGrp_sq {j : Fin n} {γ : ↥(StatedSL n (ZMod 2))} (hγ : γ ∈ axisGrp j) :
    γ * γ = 1 := by
  obtain ⟨w, rfl⟩ := hγ
  rw [← map_mul, ← map_one (tvHom j)]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem fixN_axisGrp (hn : 2 ≤ n) (j : Fin n) : fixN (axisGrp j) = axisVec j := by
  ext x
  rw [mem_fixN, mem_axisVec]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ j := by
      by_cases h0 : j = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
    have hw : (Pi.single k 1 : Fin n → ZMod 2) ∈ axisVec j := by
      rw [mem_axisVec, Pi.single_apply, ite_eq_right_iff.2 fun h => absurd h (Ne.symm hk)]
    have h1 := hx (tv j ⟨_, hw⟩) (mem_axisGrp.2 ⟨_, rfl⟩)
    rw [mat_tv, tvMat_mulVec, add_eq_left] at h1
    have h2 := congrFun h1 k
    simpa using h2
  · intro hx γ hγ
    obtain ⟨w, rfl⟩ := mem_axisGrp.1 hγ
    rw [mat_tv, tvMat_mulVec, hx, zero_smul, add_zero]

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem case9_core (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4HypCore G L)
    (hZ : Subgroup.center ↥L = ⊥) (hn : n = 4 ∨ n = 5) (hnat : BinaryNaturalSL L ⊤ ⊥ n 1)
    (hA : IsFFStarOffender G A) : B42Case9 G L := by
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hLtop : L = ⊤ := G64.BinaryNaturalSL.eq_top hnat
  have hGL : G = L := le_antisymm (fun g _ => by rw [hLtop]; trivial) (le_G_core hHyp)
  have hJ : ffJ G = L := le_antisymm (hGL ▸ B6.ffJ_le G) (le_ffJ_of_center_core hHyp hZ hA)
  obtain ⟨π, hπ⟩ := realM_of_binaryNaturalSL hnat
  have hπb : Function.Bijective π := ⟨hπ.injective (Or.inl rfl), hπ.1⟩
  refine ⟨hJ, n, hn, hnat, ?_⟩
  have hs : (1 / ((n : ℚ) - 1)) ≤ 1 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    rw [div_le_one (by linarith)]
    linarith
  refine qOf_eq_of_offenders hV hs (fun B hB => ?_) ?_
  · exact one_div_le_rAV hπ (Or.inl rfl) hn2 (hGL ▸ hB.1) hB.2.2.1.isPGroup hB.2.1
  ·
    set j : Fin n := ⟨0, by omega⟩
    set B₀ : Subgroup (MulAut V) := (axisGrp j).map (L.subtype.comp π) with hB₀
    have hB₀L : B₀ ≤ L := by
      rintro _ ⟨γ, -, rfl⟩
      exact (π γ).2
    have hpre : pre π B₀ = axisGrp j := by
      ext γ
      rw [mem_pre]
      constructor
      · rintro ⟨δ, hδ, hδγ⟩
        have : δ = γ := hπb.1 (Subtype.ext hδγ)
        exact this ▸ hδ
      · intro hγ
        exact ⟨γ, hγ, rfl⟩
    have hcard : Nat.card B₀ = 2 ^ (n - 1) := by
      rw [← card_pre hπb hB₀L, hpre, card_axisGrp]
    have hne : B₀ ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hcard
      have : 1 < 2 ^ (n - 1) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have hel : IsElemAbelian2 B₀ := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
        have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (axisGrp_comm hγ hδ)
        simpa only [map_mul, Subgroup.coe_mul, MonoidHom.comp_apply, Subgroup.coe_subtype]
          using this
      · rintro _ ⟨γ, hγ, rfl⟩
        have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (axisGrp_sq hγ)
        simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at this
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [pow_two]
        exact this
    have hLG : L ≤ G := le_G_core hHyp
    have hA2 : IsA2 G B₀ := ⟨hB₀L.trans hLG, hne, hel⟩
    have hrk : rk ↥B₀ = n - 1 := by
      unfold rk
      rw [hcard, padicValNat.prime_pow]
    have hidx : rkIdx (fixV B₀) = 1 := by
      rw [← rkSub_top, ← rkIdx_fixV_autSec_bot (hB₀L.trans hπ.hLW), hπ.rkIdx_fixV_autSec hB₀L,
        hpre, fixM_mat, fixN_axisGrp hn2, finrank_axisVec]
      omega
    have hr : rAV B₀ = 1 / ((n : ℚ) - 1) := by
      unfold rAV
      rw [hrk, hidx, Nat.cast_sub (by omega)]
      simp
    obtain ⟨B, -, hB, hBr⟩ := exists_offender_rAV_le hV hA2 (by rw [hr]; exact hs)
    exact ⟨B, hB, hBr.trans hr.le⟩

theorem case9 (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hn : n = 4 ∨ n = 5) (hnat : BinaryNaturalSL L ⊤ ⊥ n 1) (hA : IsFFStarOffender G A) :
    B42Case9 G L :=
  case9_core hV hHyp.core hZ hn hnat hA

end B42Ln

end CFSG.Quasithin
