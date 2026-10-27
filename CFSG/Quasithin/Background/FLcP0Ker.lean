module

public import CFSG.Quasithin.Background.FLcP0Mat

public section

namespace CFSG.Quasithin.FLc

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem not_isPGroup_SLt {n : ℕ} (hn : 2 ≤ n) : ¬ IsPGroup 2 (SLt n) := by
  intro hp
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (by omega : 1 ≤ n)
  obtain ⟨k, hk⟩ := hp.index (P : Subgroup (SLt n))
  have hk0 : k = 0 := by
    by_contra hne
    exact P.not_dvd_index (hk ▸ dvd_pow_self 2 hne)
  have htop : (P : Subgroup (SLt n)) = ⊤ := by
    rw [← Subgroup.index_eq_one, hk, hk0, pow_zero]
  have hr : reflection n (ZMod 2) 1 le_rfl (by omega) ∈ Ut n := by
    show _ ∈ unitriangular n (ZMod 2)
    rw [← hP, htop]
    trivial
  exact reflection_notMem_stab hn ((mem_flagStabilizer.1 (Ut_le_QI n {1} hr)) 1 rfl)

theorem kernel_isPGroup {G : Type} [Group G] [Finite G] {L UL : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (α : ↥L →* SLt n) (hαs : Function.Surjective α)
    (hker : ∀ a : ↥L, α a = 1 ↔ (a : G) ∈ Subgroup.centralizer (UL : Set G))
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (UL : Set G)) := by
  have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnorm : (α.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hker2 : IsPGroup 2 ↥α.ker := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (α.ker.map π) with h | h
    · have h1 : α.ker ≤ π.ker := (Subgroup.map_eq_bot_iff _).1 h
      rw [QuotientGroup.ker_mk'] at h1
      exact hpc.to_le h1
    · exfalso
      have hall : ∀ g : SLt n, ∃ c ∈ CFSG.pCore 2 ↥L, α c = g := by
        intro g
        obtain ⟨l, rfl⟩ := hαs g
        have hl : π l ∈ α.ker.map π := by rw [h]; trivial
        obtain ⟨k, hk, hkl⟩ := hl
        refine ⟨k⁻¹ * l, ?_, ?_⟩
        · have h1 : π (k⁻¹ * l) = 1 := by rw [map_mul, map_inv, hkl, inv_mul_cancel]
          have h2 : k⁻¹ * l ∈ π.ker := h1
          rwa [QuotientGroup.ker_mk'] at h2
        · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
      apply not_isPGroup_SLt hn
      intro g
      obtain ⟨c, hc, rfl⟩ := hall g
      obtain ⟨k, hk⟩ := hpc ⟨c, hc⟩
      refine ⟨k, ?_⟩
      have h1 : c ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [← map_pow, h1, map_one]
  have hK : α.ker = (L ⊓ Subgroup.centralizer (UL : Set G)).subgroupOf L := by
    ext a
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  rw [hK] at hker2
  exact hker2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

end CFSG.Quasithin.FLc
