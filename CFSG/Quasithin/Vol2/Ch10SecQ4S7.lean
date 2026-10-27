module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S6
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_commV {V B : Subgroup G} (hel : IsElemAbelian 2 V)
    (hVB : V ≤ Subgroup.normalizer (B : Set G)) {z : IntMod V hel}
    (hz : z ∈ commV (autI hel B)) : z.val ∈ B := by
  let S : Subgroup (IntMod V hel) :=
    { carrier := {v | v.val ∈ B}
      mul_mem' := fun {a b} ha hb => by
        show (a * b).val ∈ B
        rw [IntMod.val_mul]
        exact B.mul_mem ha hb
      one_mem' := by
        show (1 : IntMod V hel).val ∈ B
        rw [IntMod.val_one]
        exact B.one_mem
      inv_mem' := fun {a} ha => by
        show (a⁻¹).val ∈ B
        rw [IntMod.val_inv]
        exact B.inv_mem ha }
  have hle : commV (autI hel B) ≤ S := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, v, rfl⟩
    obtain ⟨g, hgB, rfl⟩ := (mem_autI hel).1 ha
    show (convI hel g v * v⁻¹).val ∈ B
    rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv]
    have h1 : v.val * (g : G)⁻¹ * v.val⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hVB v.val_mem) _).mp (B.inv_mem hgB)
    have e : (g : G) * v.val * (g : G)⁻¹ * v.val⁻¹ = (g : G) * (v.val * (g : G)⁻¹ * v.val⁻¹) := by
      group
    rw [e]
    exact B.mul_mem hgB h1
  exact hle hz

omit [Finite G] in
theorem inf_le_blockQ {V B : Subgroup G} (hel : IsElemAbelian 2 V)
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) : B ⊓ V ≤ blockQ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(B ⊓ V) := fun g => ⟨1, Subtype.ext (by
    simpa using hel.2 (g : G) (Subgroup.mem_inf.mp g.2).2)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hBN hx⟩) h2

theorem false_of_isLin2Type {H B V : Subgroup G} (hel : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hVO : V ≤ pCoreOf 2 H)
    (hO : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G)) (hB : B ∈ cComp H)
    {K : Subgroup (MulAut (IntMod V hel))} (hK : E2.IsA5Module K)
    (hle : oTwoUpper K ≤ autI hel B) {n : ℕ} (hn : 1 ≤ n) (hlin : IsLin2Type B n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkk, d, hd, z, hz, hkw, hdw⟩ := exists_fix_of_isA5Module' hK
  obtain ⟨gx, hgxB, rfl⟩ := (mem_autI hel).1 (hle hk)
  obtain ⟨gy, hgyB, rfl⟩ := (mem_autI hel).1 (hle hd)
  have hVB : V ≤ Subgroup.normalizer (B : Set G) :=
    hVO.trans (P134.pCoreOf_le_normalizer_of_mem_cComp hB)
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hB).trans hHN
  have hzB : z.val ∈ B :=
    mem_of_mem_commV hel hVB (commV_mono (hle.trans le_rfl) hz)
  have hzQ : z.val ∈ blockQ B := inf_le_blockQ hel hBN ⟨hzB, z.val_mem⟩
  set w := convI hel gy z * z⁻¹ with hw
  have hwv : w.val = (gy : G) * z.val * (gy : G)⁻¹ * z.val⁻¹ := by
    rw [hw, IntMod.val_mul, convI_apply_val, IntMod.val_inv]
  have hwU : w.val ∈ blockU B := by
    rw [hwv, blockU, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hgyB hzQ
    rwa [commutatorElement_def] at this
  have hxw : (gx : G) * w.val * (gx : G)⁻¹ = w.val := by
    rw [← convI_apply_val, hkw]
  have hyw : (gy : G) * w.val * (gy : G)⁻¹ ≠ w.val := fun h => hdw
    (IntMod.val_injective (by rw [convI_apply_val]; exact h))
  obtain ⟨F, _, _, hF, α, -, hαk, β, -, hβk, hβe⟩ := hlin
  have hβw : Multiplicative.toAdd (β ⟨w.val, hwU⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w.val, hwU⟩ = 1 := Multiplicative.toAdd.injective h0
    have h3 : (⟨w.val, hwU⟩ : ↥(blockU B)) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h3
    apply hyw
    have h4 := Subgroup.mem_centralizer_iff.mp h3.2 _ hgyB
    rw [h4]
    group
  have hfix := hβe ⟨(gx : G), hgxB⟩ ⟨w.val, hwU⟩ ⟨w.val, hwU⟩ hxw.symm
  have h2F : (2 : F) = 0 := SecE.two_eq_zero_of_card hn (by rw [Nat.card_eq_fintype_card, hF])
  have hsq := SecE.mul_self_eq_one_of_mulVec_eq h2F (α ⟨(gx : G), hgxB⟩).2 hβw hfix.symm
  have hα : α (⟨(gx : G), hgxB⟩ * ⟨(gx : G), hgxB⟩) = 1 := by
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hsq]
    rfl
  have hker : (⟨(gx : G), hgxB⟩ * ⟨(gx : G), hgxB⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := by
    rw [← hαk]
    exact hα
  have hxx : (gx : G) * gx ∈ pCoreOf 2 B := Subgroup.mem_map_of_mem B.subtype hker
  have hxxH := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hB) hxx
  apply hkk
  rw [← map_mul]
  exact (convI_eq_one_iff hel (gx * gx)).mpr (hO hxxH)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
