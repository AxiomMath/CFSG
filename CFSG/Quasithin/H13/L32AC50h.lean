module

public import CFSG.Quasithin.H13.L32NSet14Idx
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup'' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer (A : Set G) →
      y ∈ Subgroup.normalizer (B : Set G) → ∀ z ∈ A ⊔ B, y * z * y⁻¹ ∈ A ⊔ B := by
    intro y hyA hyB z hz
    have hle : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (fun _ ⟨a, ha, hae⟩ => hae ▸ (Subgroup.mem_normalizer_iff.mp hyA a).mp ha)
        (fun _ ⟨b, hb, hbe⟩ => hbe ▸ (Subgroup.mem_normalizer_iff.mp hyB b).mp hb)
    exact hle ⟨z, hz, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key x hA hB z, fun h => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ h
  simpa [mul_assoc] using this

theorem sl2_facts : (∀ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), s ^ 6 = 1) ∧
    ∀ s r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), s ^ 2 = 1 → r ^ 3 = 1 → s ≠ 1 →
      s * r * s⁻¹ * r = 1 := by
  decide +kernel

theorem exists_T_L_not_triv {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S' : L32NSet14.Setting G T L V V₂) (hNV : Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    ∃ t ∈ T, t ∈ L ∧ t ∉ L32NSet14.trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S'.exists_basis
  obtain ⟨y, hyL, hy2, hyz, hya⟩ := S'.exists_swap hz ha haV hb hbV
  have hyX : y ∈ L32NSet14.nX T V := ⟨S'.LV hyL, S'.mem_g1 hz hz1 hyz⟩
  have hy_not : y ∉ L32NSet14.trivSub V (fsuV1 T V) := fun h => by
    have h1 := h.2.2 a (S'.hV2.2.1 ha)
    rw [hya] at h1
    apply hbV
    have h2 := Subgroup.mul_mem _ (S'.hV2.1 h1) ha
    rwa [inv_mul_cancel_right] at h2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ 2 ^ m = 1 := by
    have hc : y ^ 2 ∈ pCoreOf 2 L := by
      rw [← S'.cent_eq]
      exact ⟨L.pow_mem hyL 2, hy2⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hc⟩
    refine ⟨k + 1, ?_⟩
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at this
    rw [pow_succ', pow_mul]
    exact this
  have hTp : IsPGroup 2 ↥(T.subgroupOf (L32NSet14.nX T V)) := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := S'.hH.sylow.1 ⟨t, Subgroup.mem_subgroupOf.mp ht⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hTidx : ¬ 2 ∣ (T.subgroupOf (L32NSet14.nX T V)).index := by
    have h1 := Subgroup.relIndex_mul_index S'.T_le_X
    intro h2
    apply S'.hH.sylow.2
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hyX⟩ : ↥(L32NSet14.nX T V))) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨m, Subtype.ext ?_⟩
    have hm' : (⟨y, hyX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hm)
    show ((⟨y, hyX⟩ : ↥(L32NSet14.nX T V)) ^ n) ^ 2 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm', one_zpow]
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(L32NSet14.nX T V) Q (hTp.toSylow hTidx)
  have hmem : g * ⟨y, hyX⟩ * g⁻¹ ∈ g • Q := L32NSet14.mem_smul_sylow.mpr (by
    rw [show g⁻¹ * (g * ⟨y, hyX⟩ * g⁻¹) * g = ⟨y, hyX⟩ by group]
    exact hQ (Subgroup.mem_zpowers _))
  rw [hg] at hmem
  have hmem' : g * ⟨y, hyX⟩ * g⁻¹ ∈ T.subgroupOf (L32NSet14.nX T V) := hmem
  refine ⟨(g : G) * y * (g : G)⁻¹, Subgroup.mem_subgroupOf.mp hmem',
    (Subgroup.mem_normalizer_iff.mp (hNV g.2.1) y).mp hyL, fun h => hy_not ?_⟩
  have := L32NSet14.conj_mem_trivSub (Subgroup.inv_mem _ g.2.1) (Subgroup.inv_mem _ g.2.2) h
  rwa [show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = y by group] at this

end CFSG.Quasithin.H13.L32A.C
