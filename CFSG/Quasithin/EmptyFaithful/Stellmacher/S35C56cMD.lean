module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cMC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.C56

open Equiv S35.Fin

theorem zc_mem_of_normal {D N : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hND : N ≤ D)
    (hN : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (h1 : N ≠ ⊥) : zc D ∈ N := by
  have hpD : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  have : Group.IsNilpotent ↥D := hpD.isNilpotent
  have hn : (N.subgroupOf D).Normal :=
    ⟨fun n hn g => by
      have := hN g.1 g.2 n.1 (Subgroup.mem_subgroupOf.mp hn)
      exact Subgroup.mem_subgroupOf.mpr (by simpa using this)⟩
  have hne : N.subgroupOf D ≠ ⊥ := by
    intro h
    apply h1
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hND hn⟩ : ↥D) ∈ N.subgroupOf D := Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp this)
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hcN, hcz⟩ := Subgroup.mem_inf.mp c.2
  have hc1 : (c : ↥D) ≠ 1 := fun h => hc (Subtype.ext h)
  have hcent : IsCentInv D (c : ↥D).1 :=
    ⟨(c : ↥D).2, fun h => hc1 (Subtype.ext h), fun d hd =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hcz ⟨d, hd⟩)⟩
  rw [zc_eq hD hcent]
  exact Subgroup.mem_subgroupOf.mp hcN

theorem card_fixW_zc {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (fixW orth (Subgroup.zpowers (zc D))) = 4 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hz : zc (cj g S5Syl) = g * zStd * g⁻¹ := zc_eq hD (isCentInv_cj_std_iff.mpr rfl)
  rw [hz, ← cj_zpowers, card_fixW_conj]
  exact congrArg (fun p => p.2.1) (profile_orth.2.1 : _ = (4, 4, 1))

theorem card_map_sylow {G : Type} [Group G] [Finite G] {X S : Subgroup G}
    (θ : ↥X →* Perm (Fin 5)) (hθs : Function.Surjective θ) (hS : IsSylowTwoOf S X) :
    Nat.card ((S.subgroupOf X).map θ) = 8 := by
  have hK' : IsPGroup 2 (S.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let Sy : Sylow 2 ↥X := hK'.toSylow hS.2.2
  have h1 := Sylow.card_eq_multiplicity (Sy.mapSurjective hθs)
  have h2 : ((Sy.mapSurjective hθs : Sylow 2 (Perm (Fin 5))) : Subgroup (Perm (Fin 5))) =
      (S.subgroupOf X).map θ := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : Nat.card (Perm (Fin 5)) = 2 ^ 3 * 15 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  rw [h2] at h1
  rw [h1, h3, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_four {X E F : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (h : IsOrthSec X E F) {Y A : Subgroup G}
    (hY : Y ≤ X) (hA : A ≤ Y) (hAY : Y ≤ Subgroup.normalizer (A : Set G))
    (hsyl : IsSylowTwoOf (Y ⊔ pCoreOf 2 X) X) (hA1 : ¬ A ≤ pCoreOf 2 X) {U : Subgroup G}
    (hEU : E ≤ U) (hUF : U ≤ F)
    (hc : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ E) : E.relIndex U ≤ 4 := by
  have hEF : E ≤ F := hEU.trans hUF
  have hcS := IsModelSec.cSecIn_eq_pCoreOf h hq
  have hs := IsModelSec.isSec h hEF
  obtain ⟨θ, ρ, hθs, hθk, hρK, -, hρconj⟩ := exists_secHom h
  have hpX : pCoreOf 2 X ≤ X := LieType.BorelTits.pCoreOf_le 2 X
  have hAX : A ≤ X := hA.trans hY
  have hDe : ((Y ⊔ pCoreOf 2 X).subgroupOf X).map θ = (Y.subgroupOf X).map θ := by
    rw [Subgroup.subgroupOf_sup hY hpX, Subgroup.map_sup]
    have : ((pCoreOf 2 X).subgroupOf X).map θ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hθk, ← hcS]
    rw [this, sup_bot_eq]
  set D : Subgroup (Equiv.Perm (Fin 5)) := (Y.subgroupOf X).map θ with hDdef
  have hD8 : Nat.card D = 8 := by
    have := card_map_sylow θ hθs hsyl
    rw [hDe] at this
    exact this
  set N : Subgroup (Equiv.Perm (Fin 5)) := (A.subgroupOf X).map θ with hNdef
  have hND : N ≤ D := Subgroup.map_mono (Subgroup.comap_mono hA)
  have hNn : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N := by
    rintro d ⟨y, hy, rfl⟩ n ⟨a, ha, rfl⟩
    refine ⟨y * a * y⁻¹, ?_, by simp⟩
    have := (Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp hy)) a.1).mp
      (Subgroup.mem_subgroupOf.mp ha)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  have hN1 : N ≠ ⊥ := by
    intro hN
    apply hA1
    intro a ha
    rw [hNdef, Subgroup.map_eq_bot_iff] at hN
    have hle := hN
    rw [hθk] at hle
    have := hle (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hAX ha⟩ : ↥X) ∈ A.subgroupOf X)
    rw [Subgroup.mem_subgroupOf, hcS] at this
    exact this
  obtain ⟨a', ha', hz⟩ : zc D ∈ N := zc_mem_of_normal hD8 hND hNn hN1
  have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'
  let f : ↥U →* orth.W := ρ.comp (Subgroup.inclusion hUF)
  have hker : f.ker = E.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hρK ⟨u, hUF u.2⟩
  have hrange : f.range ≤ fixW orth (Subgroup.zpowers (zc D)) := by
    rintro _ ⟨u, rfl⟩
    rw [mem_fixW_zpowers, ← hz]
    have hu : (u : G) ∈ F := hUF u.2
    have hky : (a' : G) * (u : G) * (a' : G)⁻¹ ∈ F := by
      have := hs.normN a'.2
      exact (Subgroup.mem_normalizer_iff.mp this _).mp hu
    have h1 : ρ ⟨(a' : G) * u * (a' : G)⁻¹, hky⟩ = orth.act (θ a') (ρ ⟨u, hu⟩) :=
      hρconj a' ⟨u, hu⟩ hky
    have hcm : (a' : G) * u * (a' : G)⁻¹ * (u : G)⁻¹ ∈ E := hc _ haA u u.2
    have h2 : (⟨(a' : G) * u * (a' : G)⁻¹, hky⟩ : ↥F) =
        ⟨(a' : G) * u * (a' : G)⁻¹ * (u : G)⁻¹, hEF hcm⟩ * ⟨u, hu⟩ := by
      apply Subtype.ext
      simp
    rw [h2, map_mul, (hρK _).mpr hcm, one_mul] at h1
    exact h1.symm
  have : E.relIndex U = Nat.card f.range := by
    rw [← Subgroup.index_ker, hker]; rfl
  rw [this]
  calc Nat.card f.range ≤ Nat.card (fixW orth (Subgroup.zpowers (zc D))) :=
        Subgroup.card_le_of_le hrange
    _ = 4 := card_fixW_zc hD8

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
