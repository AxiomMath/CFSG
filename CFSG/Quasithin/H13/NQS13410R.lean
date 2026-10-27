module

public import CFSG.Quasithin.H13.NQS13410Q

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem centralizer_Z_le_L1T (S : A6.Setting134 G T L V) (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V) :
    centralizer (quasithinOmegaOneCenter T : Set G) ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  intro g hg
  have hZV : V ⊓ centralizer (L : Set G) ≤ quasithinOmegaOneCenter T :=
    S.ZV_le_ZL.trans inf_le_left
  have hgM : g ∈ normalizer (L : Set G) :=
    S.centralizer_ZV_le (centralizer_le (SetLike.coe_subset_coe.mpr hZV) hg)
  rw [hM] at hgM
  have hgN : g ∈ normalizer (fsuV1 T V : Set G) := by
    rw [← hZV1]
    exact centralizer_le_normalizer _ hg
  rw [U3.s134_L1T_eq_NLTV1 S]
  exact mem_inf.2 ⟨hgM, hgN⟩

omit [Finite G] in
theorem eq_sup_of_forall_conj {H K U : Subgroup G} (hKTH : K ⊔ T ≤ H)
    (hconj : ∀ h ∈ H, ∃ x ∈ K ⊔ T, x⁻¹ * h ∈ centralizer (U : Set G))
    (hC : H ⊓ centralizer (U : Set G) ≤ K ⊔ T) : H = K ⊔ T := by
  refine le_antisymm (fun h hh => ?_) hKTH
  obtain ⟨x, hx, hxh⟩ := hconj h hh
  have h1 : x⁻¹ * h ∈ K ⊔ T := hC (mem_inf.2 ⟨mul_mem (inv_mem (hKTH hx)) hh, hxh⟩)
  have e : h = x * (x⁻¹ * h) := by group
  rw [e]
  exact mul_mem hx h1

omit [Finite G] in
theorem exists_mem_sup_of_l32 {K U : Subgroup G} (htop : autOn K U = ⊤) {h : G}
    (hh : h ∈ normalizer (U : Set G)) : ∃ x ∈ K ⊔ T, x⁻¹ * h ∈ centralizer (U : Set G) := by
  obtain ⟨k, hk, hkh⟩ := exists_mem_eq_conj htop hh
  refine ⟨k, mem_sup_left hk, mem_centralizer_iff.2 fun u hu => ?_⟩
  have h1 := hkh u hu
  calc u * (k⁻¹ * h) = k⁻¹ * (k * u * k⁻¹) * k * k⁻¹ * h := by group
    _ = k⁻¹ * (h * u * h⁻¹) * k * k⁻¹ * h := by rw [h1]
    _ = k⁻¹ * h * u := by group

omit [Finite G] in
theorem exists_mem_sup_of_perm {K H U : Subgroup G} (hHU : H ≤ normalizer (U : Set G))
    (hTsyl : IsSylowTwoOf T H) (ρ : ↥(normalizer (U : Set G)) →* Perm (Fin 6))
    (hker : ∀ g, ρ g = 1 → (g : G) ∈ centralizer (U : Set G))
    (himg : ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ K ∧
      ρ g = σ) {h : G} (hh : h ∈ H) :
    ∃ x ∈ K ⊔ T, x⁻¹ * h ∈ centralizer (U : Set G) := by
  classical
  set f : ↥H →* ℤˣ := Perm.sign.comp (ρ.comp (Subgroup.inclusion hHU)) with hf
  have hfH : ∀ (y : G) (hy : y ∈ H), f ⟨y, hy⟩ = Perm.sign (ρ ⟨y, hHU hy⟩) := fun _ _ => rfl
  have heven : ∀ (y : G) (hy : y ∈ H), Perm.sign (ρ ⟨y, hHU hy⟩) = 1 →
      ∃ k ∈ K, k⁻¹ * y ∈ centralizer (U : Set G) := by
    intro y hy hs
    obtain ⟨g, hgK, hg⟩ := himg _ (Perm.mem_alternatingGroup.2 hs)
    refine ⟨g, hgK, ?_⟩
    have h1 : ρ (g⁻¹ * ⟨y, hHU hy⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
    exact hker _ h1
  rcases Int.units_eq_one_or (Perm.sign (ρ ⟨h, hHU hh⟩)) with hs | hs
  · obtain ⟨k, hk, hkh⟩ := heven h hh hs
    exact ⟨k, mem_sup_left hk, hkh⟩
  ·
    have ht : ∃ (t : G) (ht : t ∈ T), Perm.sign (ρ ⟨t, hHU (hTsyl.1 ht)⟩) = -1 := by
      by_contra hno
      push Not at hno
      have hTker : T.subgroupOf H ≤ f.ker := by
        intro t ht
        rw [MonoidHom.mem_ker]
        have ht' : (t : G) ∈ T := mem_subgroupOf.1 ht
        have h0 := hno t ht'
        have e : f t = Perm.sign (ρ ⟨t, hHU (hTsyl.1 ht')⟩) := rfl
        rw [e]
        rcases Int.units_eq_one_or (Perm.sign (ρ ⟨t, hHU (hTsyl.1 ht')⟩)) with h1 | h1
        · exact h1
        · exact absurd h1 h0
      have hrange : Nat.card f.range = 2 := by
        have htop : f.range = ⊤ := by
          rw [eq_top_iff]
          intro u _
          rcases Int.units_eq_one_or u with rfl | rfl
          · exact one_mem _
          · exact ⟨⟨h, hh⟩, hs⟩
        rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
      have h2 : f.ker.index = 2 := by rw [Subgroup.index_ker, hrange]
      have h3 : f.ker.index ∣ (T.subgroupOf H).index := Subgroup.index_dvd_of_le hTker
      rw [h2] at h3
      exact hTsyl.2.2 h3
    obtain ⟨t, htT, hts⟩ := ht
    have htH : t ∈ H := hTsyl.1 htT
    have hs' : Perm.sign (ρ ⟨t⁻¹ * h, hHU (mul_mem (inv_mem htH) hh)⟩) = 1 := by
      have e : (⟨t⁻¹ * h, hHU (mul_mem (inv_mem htH) hh)⟩ : ↥(normalizer (U : Set G))) =
          (⟨t, hHU htH⟩)⁻¹ * ⟨h, hHU hh⟩ := rfl
      rw [e, map_mul, map_inv, map_mul, map_inv, hts, hs]
      decide
    obtain ⟨k, hk, hkh⟩ := heven _ (mul_mem (inv_mem htH) hh) hs'
    refine ⟨t * k, mul_mem (mem_sup_right htT) (mem_sup_left hk), ?_⟩
    have e : (t * k)⁻¹ * h = k⁻¹ * (t⁻¹ * h) := by group
    rw [e]
    exact hkh

theorem eq_sup_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    {z : G} {H K U : Subgroup G} (hTH : T ≤ H) (hL1H : L₁Of L (fsuV1 T V) ≤ H)
    (hO2H : pCoreOf 2 H ≠ ⊥) (hHz : H ≤ centralizer ({z} : Set G)) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hKf : quasithinIsFaithfulLocal T K)
    (hKM : ¬ K ≤ normalizer (L : Set G)) (hL1K : L₁Of L (fsuV1 T V) ≤ K)
    (hJ : ⁅K, thompsonJ T⁆ = K)
    (hK : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    [IsMulCommutative ↥U] (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hUK : ⁅U, K⁆ = U) (hU1 : U ≠ ⊥)
    (hUcl : U ≤ conjClosure (quasithinOmegaOneCenter T ⊓ U) K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (U : Set G))
    (hnat : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 →
      BinaryNaturalSL (V := ↥U) (autOn K U) ⊤ ⊥ 3 1)
    (hZ : quasithinOmegaOneCenter T ≤ U ⊔ U3.cZ T K) (hcZ : U3.cZ T K = zpowers z)
    (hact : H ≤ normalizer (U : Set G) →
      ∀ h ∈ H, ∃ x ∈ K ⊔ T, x⁻¹ * h ∈ centralizer (U : Set G)) :
    H = K ⊔ T := by
  have hcl := conjClosure_eq_of_a6 hC137 h1332 h1228 h56 S he hTH hL1H hO2H hKH hHK hKf hKM
    hL1K hJ hK hKU hTU hUK hU1 hUcl ho2Z hnat hZ
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hcl]
    exact le_normalizer_conjClosure _ H
  have hC : H ⊓ centralizer (U : Set G) ≤ K ⊔ T := by
    intro h hh
    obtain ⟨hhH, hhU⟩ := mem_inf.1 hh
    have hzC : U3.cZ T K ≤ centralizer ({h} : Set G) := by
      rw [hcZ, zpowers_le, mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp (hHz hhH)).symm
    have hUC : U ≤ centralizer ({h} : Set G) := fun u hu => by
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hhU u hu
    have hZC := hZ.trans (sup_le hUC hzC)
    have hhZ : h ∈ centralizer (quasithinOmegaOneCenter T : Set G) :=
      mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.mp (hZC hx)
    exact (sup_le_sup_right hL1K T) (centralizer_Z_le_L1T S hM hZV1 hhZ)
  exact eq_sup_of_forall_conj (sup_le hKH hTH) (hact hHU) hC

end CFSG.Quasithin.H13.NQS134
