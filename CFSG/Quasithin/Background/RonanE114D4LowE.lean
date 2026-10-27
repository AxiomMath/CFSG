module

public import CFSG.Quasithin.Background.E3Bar

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

private theorem isSolvable_of_map_le {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (N : Subgroup X) {S : Subgroup Y} (hS : Group.IsSolvable S)
    (h : N.map f ≤ S) : Group.IsSolvable N := by
  have hNS : Group.IsSolvable (N.map f) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective f hf).toMonoidHom) (N.equivMapOfInjective f hf).injective

private theorem isSolvable_map_of_solvable {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (N : Subgroup X) (hN : Group.IsSolvable N) :
    Group.IsSolvable (N.map f) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective f hf).symm.toMonoidHom) (N.equivMapOfInjective f hf).symm.injective

private theorem map_solvableRadical_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.solvableRadical A).map e.toMonoidHom ≤ CFSG.solvableRadical B := by
  unfold CFSG.solvableRadical
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup ⟨hN.1.map e.toMonoidHom e.surjective,
    isSolvable_map_of_solvable e.toMonoidHom e.injective N hN.2⟩

private theorem solvableRadical_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.solvableRadical A).map e.toMonoidHom = CFSG.solvableRadical B := by
  refine le_antisymm (map_solvableRadical_le e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_solvableRadical_le e.symm)
  rw [Subgroup.map_map] at h
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
    ext x
    simp
  rwa [hid, Subgroup.map_id] at h

theorem pCoreOf_inf_le [Finite G] {K L : Subgroup G}
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (K ⊓ L) ≤ pCoreOf 2 K := by
  have hKn : K ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
    intro k hk
    show k ∈ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show x ∈ K ⊓ L ↔ k * x * k⁻¹ ∈ K ⊓ L
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.le_normalizer : K ≤ Subgroup.normalizer (K : Set G)) hk) x)
      (Subgroup.mem_normalizer_iff.mp (hKL hk) x)
  have hN : pCoreOf 2 (K ⊓ L) ≤ K := (pCoreOf_le 2 (K ⊓ L)).trans inf_le_left
  have hK' : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊓ L) : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 (K ⊓ L))
  exact le_pCoreOf_of_le_normalizer 2 hN hK' (pCoreOf_isPGroup 2 (K ⊓ L))

theorem solvableRadical_inf_le [Finite G] {K L : Subgroup G}
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) :
    (CFSG.solvableRadical ↥K).map K.subtype ⊓ L ≤
      (CFSG.solvableRadical ↥(K ⊓ L)).map (K ⊓ L).subtype := by
  let ψ : ↥(K ⊓ L) →* ↥K := Subgroup.inclusion inf_le_left
  have hPn : ((CFSG.solvableRadical ↥K).comap ψ).Normal :=
    Subgroup.Normal.comap inferInstance ψ
  have hPs : Group.IsSolvable ↥((CFSG.solvableRadical ↥K).comap ψ) :=
    isSolvable_of_map_le ψ (Subgroup.inclusion_injective inf_le_left)
      ((CFSG.solvableRadical ↥K).comap ψ) (S := CFSG.solvableRadical ↥K)
      (A3.solvableRadical_isSolvable (G := ↥K)) (Subgroup.map_comap_le ψ _)
  have hPle : (CFSG.solvableRadical ↥K).comap ψ ≤ CFSG.solvableRadical ↥(K ⊓ L) :=
    A3.le_solvableRadical hPn hPs
  rintro x ⟨hxR, hxL⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxR
  have hmem : (⟨(y : G), Subgroup.mem_inf.mpr ⟨y.2, hxL⟩⟩ : ↥(K ⊓ L)) ∈
      (CFSG.solvableRadical ↥K).comap ψ :=
    Subgroup.mem_comap.mpr hy
  exact Subgroup.mem_map.mpr ⟨_, hPle hmem, rfl⟩

theorem map_pCoreOf_of_injective {X : Type*} [Group X] (ι : X →* G) (hι : Function.Injective ι)
    (H : Subgroup X) : (pCoreOf 2 H).map ι = pCoreOf 2 (H.map ι) := by
  let e : ↥H ≃* ↥(H.map ι) := H.equivMapOfInjective ι hι
  have hcore := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_solvableRadical_of_injective {X : Type*} [Group X] (ι : X →* G)
    (hι : Function.Injective ι) (H : Subgroup X) :
    ((CFSG.solvableRadical ↥H).map H.subtype).map ι =
      (CFSG.solvableRadical ↥(H.map ι)).map (H.map ι).subtype := by
  let e : ↥H ≃* ↥(H.map ι) := H.equivMapOfInjective ι hι
  rw [← solvableRadical_map_mulEquiv e, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem not_isE_of_inf_solvableRadical [Finite G] {j : ℕ} {H T A K : Subgroup G} (hAK : A ≤ K)
    (hA : A ⊓ (CFSG.solvableRadical ↥K).map K.subtype = ⊥) (hcard : 2 ^ j < Nat.card A) :
    ¬ E1.IsE j H T A K := by
  intro hE
  have hBA : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hRB : CFSG.solvableRadical ↥K ⊓ A.subgroupOf K = ⊥ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_inf _ _ _ K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hAK,
      Subgroup.map_bot, inf_comm]
    exact hA
  have hO2 : CFSG.Open.pCore 2 ↥K ≤ CFSG.solvableRadical ↥K :=
    A3.le_solvableRadical inferInstance
      (E1.isSolvable_of_isPGroup_two (CFSG.LieType.BorelTits.pCore_isPGroup 2))
  have hPB : CFSG.Open.pCore 2 ↥K ⊓ A.subgroupOf K = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hO2).trans hRB.le)
  obtain ⟨-, -, -, hrank⟩ := hE
  rcases hrank with ⟨-, hle⟩ | ⟨-, hle⟩
  · rw [E1.card_barO2_eq_relIndex] at hle
    have h3 := Subgroup.relIndex_mul_card (H := CFSG.Open.pCore 2 ↥K) (K := A.subgroupOf K)
    rw [hPB, Subgroup.card_bot, mul_one, hBA] at h3
    rw [h3] at hle
    exact absurd hle (not_le.mpr hcard)
  · rw [E3.card_barRad_eq_relIndex] at hle
    have h3 := Subgroup.relIndex_mul_card (H := CFSG.solvableRadical ↥K) (K := A.subgroupOf K)
    rw [hRB, Subgroup.card_bot, mul_one, hBA] at h3
    rw [h3] at hle
    exact absurd hle (not_le.mpr hcard)

end CFSG.Quasithin.RonanE114Low
