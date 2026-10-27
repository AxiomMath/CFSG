module

public import CFSG.Quasithin.Background.ElemAbTransport
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Quasithin

section Conj

variable {W : Type} [CommGroup W]

theorem congr_eq (m x : MulAut W) : MulAut.congr m x = m * x * m⁻¹ := by
  ext v
  rfl

theorem mem_fixV_zpowers {x : MulAut W} {v : W} : v ∈ fixV (Subgroup.zpowers x) ↔ x v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem mQuot_map_congr (m : MulAut W) (A B : Subgroup (MulAut W)) :
    E3.mQuot (A.map (MulAut.congr m).toMonoidHom) (B.map (MulAut.congr m).toMonoidHom) =
      E3.mQuot A B := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.congr m).injective]

theorem isElemAbelian2_map_congr {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (m : MulAut W) : IsElemAbelian2 (A.map (MulAut.congr m).toMonoidHom) :=
  (CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff_of_injective (MulAut.congr m).injective).2 hA

theorem aSet_map_congr {k : ℕ} {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet k X)
    (m : MulAut W) {Y : Subgroup (MulAut W)} (hY : A.map (MulAut.congr m).toMonoidHom ≤ Y) :
    A.map (MulAut.congr m).toMonoidHom ∈ E3.aSet k Y := by
  obtain ⟨-, hA1, hAe, hAc⟩ := hA
  have hinj : Function.Injective (MulAut.congr m).toMonoidHom := (MulAut.congr m).injective
  refine ⟨hY, fun h => hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h),
    isElemAbelian2_map_congr hAe m, fun B' hB' hm => ?_⟩
  set B := B'.comap (MulAut.congr m).toMonoidHom with hB
  have hBA : B ≤ A := fun b hb => (Subgroup.mem_map_iff_mem hinj).1 (hB' hb)
  have hB'e : B.map (MulAut.congr m).toMonoidHom = B' :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.congr m).surjective _
  rw [← hB'e] at hm ⊢
  rw [mQuot_map_congr] at hm
  rw [E3.fixV_map_congr, E3.fixV_map_congr, hAc B hBA hm]

end Conj

theorem exists_conj_le {K : Type} [Group K] [Finite K] {H S A : Subgroup K} (hSH : S ≤ H)
    (hS : IsPGroup 2 S) (hi : ¬ 2 ∣ (S.subgroupOf H).index) (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    ∃ m ∈ H, ∀ a ∈ A, m * a * m⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hA' : IsPGroup 2 (A.subgroupOf H) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  let Q := hS'.toSylow hi
  obtain ⟨P, hP⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) P Q
  refine ⟨g, g.2, fun a ha => ?_⟩
  have h1 : (⟨a, hAH ha⟩ : ↥H) ∈ (P : Subgroup ↥H) := hP (Subgroup.mem_subgroupOf.2 ha)
  have h2 : g * ⟨a, hAH ha⟩ * g⁻¹ ∈ ((g • P : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    simpa [mul_assoc] using h1
  rw [hg] at h2
  exact Subgroup.mem_subgroupOf.1 h2

theorem mQuot_bot {K : Type} [Group K] {A : Subgroup K} {n : ℕ} (hA : Nat.card A = 2 ^ n) :
    E3.mQuot A ⊥ = n := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_bot_left, hA, padicValNat.prime_pow]

end CFSG.Quasithin.H13.S127.Mod

end
