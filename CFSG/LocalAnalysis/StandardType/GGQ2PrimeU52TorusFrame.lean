module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Bridge
public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

private theorem exists_unit_cubeRoot_of_unitaryFieldData {K : Type} [Field K]
    (hU : UnitaryFieldData 2 1 K) : ∃ u : Kˣ, u ^ 3 = 1 ∧ u ^ 2 ≠ 1 := by
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card]
    norm_num
  have := hU.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨u, by rw [← hu]; exact pow_orderOf_eq_one u,
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hu]; norm_num)⟩

theorem torusSU_three_char_distinct {K : Type} [Field K] (hU : UnitaryFieldData 2 1 K) :
    ∀ i j : Fin 5, i ≠ j → ∃ x ∈ torusSU 3 5 K, ent x i i ≠ ent x j j := by
  obtain ⟨u, hu, hu2⟩ := exists_unit_cubeRoot_of_unitaryFieldData hU
  exact fun i j hij => torus_char_distinct hu hu2 i j hij

@[expose] def U52TorusCarried {G : Type} [Group G] {K : Type} [Field K] (X T : Subgroup G)
    (ψ : unitarySU 2 1 K 5 ≃* X) : Prop :=
  ∀ g : unitarySU 2 1 K 5, ((ψ g : X) : G) ∈ T ↔ (g : GL (Fin 5) K) ∈ torusSU 3 5 K

theorem exists_torusFrame_of_U52 {G : Type} [Group G] {X T : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hT : IsElemAbelian 3 T) (hTX : T ≤ X)
    (hcard : Nat.card T = 3 ^ 4) :
    ∃ (K : Type) (_ : Field K), UnitaryFieldData 2 1 K ∧
      ∃ ψ : unitarySU 2 1 K 5 ≃* X, U52TorusCarried X T ψ := by
  classical
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hX
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hgcd : Nat.gcd 5 (2 ^ 1 + 1) = 1 := by norm_num
  let ψ₀ : unitarySU 2 1 K 5 ≃* X :=
    (projEquivOfBot (scalars_subgroupOf_eq_bot hK (by norm_num : 1 ≤ 5) hgcd)).symm.trans e.symm
  have hFexp : ∀ x ∈ T.subgroupOf X, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hT.2 _ hx)
  have hFcomm : ∀ x ∈ T.subgroupOf X, ∀ y ∈ T.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    have h1 := hT.1.is_comm.comm (⟨x, hx⟩ : T) ⟨y, hy⟩
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  obtain ⟨ψ, hsub⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three (by norm_num) ψ₀
    (T.subgroupOf X) hFexp hFcomm
  refine ⟨K, hF, hU, ψ, ?_⟩
  set Ft : Subgroup (unitarySU 2 1 K 5) := (T.subgroupOf X).comap (ψ : unitarySU 2 1 K 5 →* X)
    with hFt
  have hFtle : Ft.map (unitarySU 2 1 K 5).subtype ≤ torusSU 3 5 K := by
    rintro _ ⟨g, hg, rfl⟩
    exact hsub g hg
  have hc : Nat.card (Ft.map (unitarySU 2 1 K 5).subtype) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (unitarySU 2 1 K 5).subtype_injective, hFt,
      Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective (MulEquiv.injective _),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hcard]
  have heq : Ft.map (unitarySU 2 1 K 5).subtype = torusSU 3 5 K :=
    Subgroup.eq_of_le_of_card_ge hFtle (by rw [hc]; exact card_torusSU_le (by norm_num) 4)
  intro g
  constructor
  · exact hsub g
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp hg
    have : g' = g := Subtype.ext hgg
    rw [← this]
    exact hg'

theorem U52TorusCarried.mem_normalizer_torus_iff {G : Type} [Group G] {K : Type} [Field K]
    {X T : Subgroup G} {ψ : unitarySU 2 1 K 5 ≃* X} (hU : UnitaryFieldData 2 1 K) (hTX : T ≤ X)
    (hψ : U52TorusCarried X T ψ) (s : unitarySU 2 1 K 5) :
    ((ψ s : X) : G) ∈ normalizer (T : Set G) ↔ (s : GL (Fin 5) K) ∈
      normalizer ((torusSU 3 5 K : Subgroup (GL (Fin 5) K)) : Set (GL (Fin 5) K)) := by
  have hTS : torusSU 3 5 K ≤ unitarySU 2 1 K 5 := torusSU_le_unitarySU hU (by norm_num)
  have hconj : ∀ x : unitarySU 2 1 K 5, ((ψ s : X) : G) * ((ψ x : X) : G) * ((ψ s : X) : G)⁻¹ =
      ((ψ (s * x * s⁻¹) : X) : G) := fun x => by simp
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have hxS := hTS hx
      have h1 := (h ((ψ ⟨x, hxS⟩ : X) : G)).1 ((hψ ⟨x, hxS⟩).2 hx)
      rw [hconj ⟨x, hxS⟩] at h1
      exact (hψ _).1 h1
    · intro hsx
      have hxS : x ∈ unitarySU 2 1 K 5 := by
        have e : x = (s : GL (Fin 5) K)⁻¹ * (s * x * (s : GL (Fin 5) K)⁻¹) * s := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem s.2) (hTS hsx)) s.2
      have h1 : ((ψ (s * ⟨x, hxS⟩ * s⁻¹) : X) : G) ∈ T := (hψ _).2 hsx
      rw [← hconj ⟨x, hxS⟩] at h1
      exact (hψ ⟨x, hxS⟩).1 ((h _).2 h1)
  · intro h b
    constructor
    · intro hb
      set b' := ψ.symm ⟨b, hTX hb⟩ with hb'
      have hb'ψ : ((ψ b' : X) : G) = b := by simp [hb']
      have hmem : (b' : GL (Fin 5) K) ∈ torusSU 3 5 K := (hψ b').1 (by rw [hb'ψ]; exact hb)
      have h1 : ((ψ (s * b' * s⁻¹) : X) : G) ∈ T := (hψ _).2 ((h _).1 hmem)
      rw [← hconj b', hb'ψ] at h1
      exact h1
    · intro hyb
      have hbX : b ∈ X := by
        have e : b = ((ψ s : X) : G)⁻¹ * (((ψ s : X) : G) * b * ((ψ s : X) : G)⁻¹) *
            ((ψ s : X) : G) := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem (ψ s).2) (hTX hyb)) (ψ s).2
      set b' := ψ.symm ⟨b, hbX⟩ with hb'
      have hb'ψ : ((ψ b' : X) : G) = b := by simp [hb']
      have h1 : ((s * b' * s⁻¹ : unitarySU 2 1 K 5) : GL (Fin 5) K) ∈ torusSU 3 5 K :=
        (hψ (s * b' * s⁻¹)).1 (by rw [← hconj b', hb'ψ]; exact hyb)
      have h3 := (hψ b').2 ((h _).2 h1)
      rwa [hb'ψ] at h3

theorem U52TorusCarried.conj_torus_eq_iff {G : Type} [Group G] {K : Type} [Field K]
    {X T : Subgroup G} {ψ : unitarySU 2 1 K 5 ≃* X} (hU : UnitaryFieldData 2 1 K) (hTX : T ≤ X)
    (hψ : U52TorusCarried X T ψ) (s₁ s₂ : unitarySU 2 1 K 5) :
    (∀ b : T, ((ψ s₁ : X) : G) * (b : G) * ((ψ s₁ : X) : G)⁻¹ =
        ((ψ s₂ : X) : G) * (b : G) * ((ψ s₂ : X) : G)⁻¹) ↔
      ∀ g ∈ torusSU 3 5 K, (s₁ : GL (Fin 5) K) * g * (s₁ : GL (Fin 5) K)⁻¹ =
        (s₂ : GL (Fin 5) K) * g * (s₂ : GL (Fin 5) K)⁻¹ := by
  have hTS : torusSU 3 5 K ≤ unitarySU 2 1 K 5 := torusSU_le_unitarySU hU (by norm_num)
  have hconj : ∀ s x : unitarySU 2 1 K 5, ((ψ s : X) : G) * ((ψ x : X) : G) * ((ψ s : X) : G)⁻¹ =
      ((ψ (s * x * s⁻¹) : X) : G) := fun s x => by simp
  constructor
  · intro h g hg
    have hgS := hTS hg
    have h1 := h ⟨_, (hψ ⟨g, hgS⟩).2 hg⟩
    simp only [hconj] at h1
    exact congrArg Subtype.val (ψ.injective (Subtype.ext h1))
  · intro h b
    set g := ψ.symm ⟨b, hTX b.2⟩ with hg
    have hgψ : ((ψ g : X) : G) = b := by simp [hg]
    have h1 := h g ((hψ g).1 (by rw [hgψ]; exact b.2))
    have h2 : s₁ * g * s₁⁻¹ = s₂ * g * s₂⁻¹ := Subtype.ext h1
    have h3 := congrArg (fun z => ((ψ z : X) : G)) h2
    simp only [← hconj, hgψ] at h3
    exact h3

end CFSG.GGQ2Prime
