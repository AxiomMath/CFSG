module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.H13.A7BlkAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore)

variable {G : Type} [Group G]

theorem uc22s206o_isSylowOf_top {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p Y) : CFSG.ABGLocalTools.IsSylowOf p (Q : Subgroup Y) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
  exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩

theorem uc22s206o_mk_eq {Y : Type*} [Group Y] {C : Subgroup Y} {c c' : C}
    (h : ∀ m ∈ C, (c : Y) * m * (c : Y)⁻¹ = c' * m * (c' : Y)⁻¹) :
    (c : C ⧸ Subgroup.center C) = (c' : C ⧸ Subgroup.center C) := by
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  show (m : Y) * ((c : Y)⁻¹ * c') = (c : Y)⁻¹ * c' * m
  calc (m : Y) * ((c : Y)⁻¹ * c') = (c : Y)⁻¹ * ((c : Y) * m * (c : Y)⁻¹) * c' := by group
    _ = (c : Y)⁻¹ * (c' * m * (c' : Y)⁻¹) * c' := by rw [h m m.2]
    _ = (c : Y)⁻¹ * c' * m := by group

theorem uc22s206o_exists_hom {Y X : Type*} [Group Y] [Group X] {C : Subgroup Y} (φ : X →* Y)
    (h : ∀ k, ∃ c ∈ C, ∀ m ∈ C, φ k * m * (φ k)⁻¹ = c * m * c⁻¹) :
    ∃ ψ : X →* C ⧸ Subgroup.center C, ∀ k, ∃ c : C, ψ k = c ∧
      ∀ m ∈ C, φ k * m * (φ k)⁻¹ = c * m * (c : Y)⁻¹ := by
  choose impl himplC himpl using h
  let f : X → C ⧸ Subgroup.center C := fun k =>
    ((⟨impl k, himplC k⟩ : C) : C ⧸ Subgroup.center C)
  have hf : ∀ a b, f (a * b) = f a * f b := fun a b => by
    refine (uc22s206o_mk_eq (c := ⟨impl (a * b), himplC (a * b)⟩)
      (c' := (⟨impl a, himplC a⟩ : C) * ⟨impl b, himplC b⟩) fun m hm => ?_).trans
        (QuotientGroup.mk_mul _ _ _)
    have hb : impl b * m * (impl b)⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (himplC b) hm) (C.inv_mem (himplC b))
    show impl (a * b) * m * (impl (a * b))⁻¹ = impl a * impl b * m * (impl a * impl b)⁻¹
    rw [← himpl (a * b) m hm, map_mul]
    calc φ a * φ b * m * (φ a * φ b)⁻¹ = φ a * (φ b * m * (φ b)⁻¹) * (φ a)⁻¹ := by group
      _ = φ a * (impl b * m * (impl b)⁻¹) * (φ a)⁻¹ := by rw [himpl b m hm]
      _ = impl a * (impl b * m * (impl b)⁻¹) * (impl a)⁻¹ := himpl a _ hb
      _ = impl a * impl b * m * (impl a * impl b)⁻¹ := by group
  exact ⟨MonoidHom.mk' f hf, fun k => ⟨⟨impl k, himplC k⟩, rfl, himpl k⟩⟩

theorem uc22s206o_mem_centralizer {Y X : Type*} [Group Y] [Group X] {C : Subgroup Y}
    {φ : X →* Y} {ψ : X →* C ⧸ Subgroup.center C}
    (hψ : ∀ k, ∃ c : C, ψ k = c ∧ ∀ m ∈ C, φ k * m * (φ k)⁻¹ = c * m * (c : Y)⁻¹)
    {k : X} (hk : ψ k = 1) : φ k ∈ centralizer (C : Set Y) := by
  obtain ⟨c, hc, hcm⟩ := hψ k
  rw [hk, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hc
  rw [mem_centralizer_iff]
  intro m hm
  have h2 : (c : Y) * m = m * c := (congrArg Subtype.val (hc ⟨m, hm⟩)).symm
  have h1 : φ k * m * (φ k)⁻¹ = m := by rw [hcm m hm, h2, mul_inv_cancel_right]
  calc m * φ k = φ k * m * (φ k)⁻¹ * φ k := by rw [h1]
    _ = φ k * m := by group

theorem uc22s206o_conj {Y X : Type*} [Group Y] [Group X] {C : Subgroup Y} {φ : X →* Y}
    {ψ : X →* C ⧸ Subgroup.center C}
    (hψ : ∀ k, ∃ c : C, ψ k = c ∧ ∀ m ∈ C, φ k * m * (φ k)⁻¹ = c * m * (c : Y)⁻¹)
    (g : C) {k k' : X} (hk : (g : Y) * φ k * (g : Y)⁻¹ = φ k') :
    ψ k' = (g : C ⧸ Subgroup.center C) * ψ k * (g : C ⧸ Subgroup.center C)⁻¹ := by
  obtain ⟨c, hc, hcm⟩ := hψ k
  obtain ⟨c', hc', hc'm⟩ := hψ k'
  rw [hc, hc']
  refine (uc22s206o_mk_eq (c := c') (c' := g * c * g⁻¹) fun m hm => ?_).trans rfl
  have hgm : (g : Y)⁻¹ * m * g ∈ C := C.mul_mem (C.mul_mem (C.inv_mem g.2) hm) g.2
  show (c' : Y) * m * (c' : Y)⁻¹ = (g : Y) * c * (g : Y)⁻¹ * m * ((g : Y) * c * (g : Y)⁻¹)⁻¹
  rw [← hc'm m hm, ← hk]
  calc (g : Y) * φ k * (g : Y)⁻¹ * m * ((g : Y) * φ k * (g : Y)⁻¹)⁻¹
      = (g : Y) * (φ k * ((g : Y)⁻¹ * m * g) * (φ k)⁻¹) * (g : Y)⁻¹ := by group
    _ = (g : Y) * (c * ((g : Y)⁻¹ * m * g) * (c : Y)⁻¹) * (g : Y)⁻¹ := by rw [hcm _ hgm]
    _ = (g : Y) * c * (g : Y)⁻¹ * m * ((g : Y) * c * (g : Y)⁻¹)⁻¹ := by group

theorem uc22s206o_exists_component {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y)
    [Group.IsPerfect P] (hP : P ≠ ⊥) (hF : ⁅P, CFSG.fittingSubgroup Y⁆ = ⊥)
    (hN : ∀ J : Subgroup Y, IsComponentOf J ⊤ → P ≤ normalizer (J : Set Y))
    (hout : ∀ J : Subgroup Y, IsComponentOf J ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (J ⧸ Subgroup.center J))) :
    ∃ C : Subgroup Y, IsComponentOf C ⊤ ∧ ¬ P ≤ centralizer (C : Set Y) := by
  by_contra hcon
  push Not at hcon
  apply hP
  have hE :=
    CFSG.ComponentClassification.GeneralizedFitting.perfect_normalizer_enters_layer P hF hN hout
  have hC : CFSG.ComponentClassification.Layer.subgroup Y ≤ centralizer (P : Set Y) := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    exact sSup_le fun C hC => le_centralizer_iff.mp (hcon C hC)
  exact Subgroup.commutator_eq_self.symm.trans
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hE.trans hC))

theorem uc22s206o_sylow [Finite G] {M K T : Subgroup G} (hKM : K ≤ M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hTK : T ≤ normalizer (K : Set G))
    {C : Subgroup (Bar2 M)} (hC : IsComponentOf C ⊤) {φ : ↥K →* Bar2 M}
    (hφ : ∀ k, φ k = QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hKM k))
    {ψ : ↥K →* C ⧸ Subgroup.center C}
    (hψ : ∀ k, ∃ c : C, ψ k = c ∧ ∀ m ∈ C, φ k * m * (φ k)⁻¹ = c * m * (c : Bar2 M)⁻¹) :
    ∃ TS : Subgroup (C ⧸ Subgroup.center C), CFSG.ABGLocalTools.IsSylowOf 2 TS ⊤ ∧
      TS ≤ normalizer (ψ.range : Set (C ⧸ Subgroup.center C)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  have hTb := uc22s206o_isSylowOf_top
    (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)))
  rw [Sylow.coe_mapSurjective, hQ] at hTb
  obtain ⟨Q₂, hQ₂⟩ := (uc22p22r_fo_sylow_inf hTb hC.2.1).exists_sylow_eq_subgroupOf
  obtain ⟨TS, hS, hTS⟩ : ∃ TS : Subgroup (C ⧸ Subgroup.center C),
      CFSG.ABGLocalTools.IsSylowOf 2 TS ⊤ ∧ ∀ x ∈ TS, ∃ c : C, x = c ∧
        (c : Bar2 M) ∈ (T.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    refine ⟨_, uc22s206o_isSylowOf_top
      (Q₂.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center C))), fun x hx => ?_⟩
    rw [Sylow.coe_mapSurjective, hQ₂] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, rfl, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).1⟩
  have hconj : ∀ x ∈ TS, ∀ y ∈ ψ.range, x * y * x⁻¹ ∈ ψ.range := by
    rintro x hx _ ⟨k, rfl⟩
    obtain ⟨c, rfl, t, ht, htc⟩ := hTS x hx
    have htK : (t : G) * k * (t : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht)) k).mp k.2
    refine ⟨⟨_, htK⟩, uc22s206o_conj hψ c ?_⟩
    rw [hφ, hφ, ← htc, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨TS, hS, fun x hx => mem_normalizer_iff.mpr fun y => ⟨hconj x hx y, fun h => ?_⟩⟩
  have h1 := hconj x⁻¹ (inv_mem hx) _ h
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
