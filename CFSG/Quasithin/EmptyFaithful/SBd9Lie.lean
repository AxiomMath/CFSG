module

public import CFSG.Quasithin.EmptyFaithful.SBd9LieB
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.Quasithin.EmptyFaithful.SBd9LieDef

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

theorem centerOf_eq_map {G : Type} [Group G] (L : Subgroup G) :
    centerOf L = (Subgroup.center ↥L).map L.subtype := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hx.1⟩, (mem_centerOf_iff (x := ⟨x, hx.1⟩)).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact mem_centerOf_iff.mpr hy

theorem lieL3_of_psl {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = CFSG.Open.pCoreOf 2 L)
    (hQ : IsSylowTwoOf Q L) (hmodel : IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) :
    LieL3 L Q (2 ^ n) := by
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := hmodel
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    have h4 : 4 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
      (by simpa using h4)
    exact ⟨s, hs⟩
  let e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  let ρ₀ : ↥L →* projectiveSL 3 K := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hsurj₀ : Function.Surjective ρ₀ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ρ₀.ker = Subgroup.center ↥L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective, QuotientGroup.ker_mk']
  have hZp : IsPGroup 2 (Subgroup.center ↥L) := by
    have h1 : IsPGroup 2 ↥(centerOf L) := by
      rw [hZ]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    rw [centerOf_eq_map] at h1
    exact h1.of_equiv ((Subgroup.center ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm
  have hT : IsSylowTwoOf ((Q.subgroupOf L).map ρ₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hQ) ρ₀ hsurj₀
  obtain ⟨φ, hφ⟩ := SzN2.exists_mulEquiv_map_eq isSylowTwoOf_projUnitriangular hT
  have hmod : IsBorelModel L Q (φ.toMonoidHom.comp ρ₀) :=
    { surj := φ.surjective.comp hsurj₀
      ker_eq := by rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, hker₀]
      two := by
        rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, hker₀]
        exact hZp
      map_eq := by rw [← Subgroup.map_map]; exact hφ }
  have hperf : Group.IsPerfect ↥L := hq.1
  have hA : K1.SylowCentralizingAutInner (↥L ⧸ Subgroup.center ↥L) :=
    K1.SylowCentralizingAutInner.of_mulEquiv e' (K1.sylowCentralizingAutInner_projectiveSL (by norm_num))
  have hsub : (L.subgroupOf L).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.Normal.isSubnormal inferInstance
  refine ⟨hmod.center_le hQ, hmod.solv hQ hK4, hmod.cent hQ, ?_, ?_, ?_, ?_⟩
  · intro W hW _ hWZ m hm
    have := hmod.exp_dvd hQ W hW hWZ m hm
    rwa [hcard] at this
  · intro W hW hWZ
    exact (hmod.card_le W hW hWZ).trans hcard.le
  · intro hq4 y hy hy3 x hx hxy
    exact hmod.reg4 hQ (hcard.trans hq4) hy.1 hy.2 hy3 hx.1 hx.2 hxy
  · intro w hwN hwQ
    exact K1.exists_inner_of_sylowCentralizing hQ le_rfl hsub hperf hA hwN hwQ

end CFSG.Quasithin.SBd9
