module

import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUCenter
import CFSG.RankThree.Transfer.PGroup
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def rootGroupsIn {L : Type} [Group L] (R Sy : Subgroup L) : Set (Subgroup L) :=
  {X | (∃ g : L, X = conjSubgroup R g) ∧ X ≤ Sy}

structure RootParabolic {L : Type} [Group L] (R Sy X₂ Pα : Subgroup L) (e : ℕ) : Prop where
  mem : X₂ ∈ rootGroupsIn R Sy
  index : (Subgroup.normalizer (X₂ : Set L)).relIndex Sy ≤ (Nat.card R) ^ e
  one_le : 1 ≤ e
  le : Sy ≤ Pα
  isPGroup : IsPGroup 2 ↥(Sy ⊓ Subgroup.normalizer (X₂ : Set L))
  normal : ((Sy ⊓ Subgroup.normalizer (X₂ : Set L)).subgroupOf Pα).Normal
  largest : ∀ N : Subgroup L, N ≤ Pα → (N.subgroupOf Pα).Normal → IsPGroup 2 N →
    N ≤ Sy ⊓ Subgroup.normalizer (X₂ : Set L)
  not_le : ¬ Pα ≤ Subgroup.normalizer (R : Set L)
  maximal : ∀ M : Subgroup L, Subgroup.normalizer (R : Set L) ≤ M →
    M = Subgroup.normalizer (R : Set L) ∨ M = ⊤
  invariant : ∀ α : MulAut L, Subgroup.map α.toMonoidHom Sy = Sy →
    Subgroup.map α.toMonoidHom R = R → Subgroup.map α.toMonoidHom Pα = Pα

structure RootLieFacts (L : Type) [Group L] (R Sy : Subgroup L) (e : ℕ) : Prop where
  center : Subgroup.center L = ⊥
  out : ∀ α β : MulAut L, α * α = 1 → β * β = 1 → α * β = β * α →
    Subgroup.map α.toMonoidHom R = R → Subgroup.map β.toMonoidHom R = R →
    α ∉ (MulAut.conj : L →* MulAut L).range → β ∉ (MulAut.conj : L →* MulAut L).range →
    α * β ∈ (MulAut.conj : L →* MulAut L).range
  fix : ∀ (α : MulAut L) (g : L), g ∈ Sy → g * g = 1 → α * α = 1 →
    α * MulAut.conj g = MulAut.conj g * α → Subgroup.map α.toMonoidHom Sy = Sy →
    Subgroup.map α.toMonoidHom R = R →
    (∀ X ∈ rootGroupsIn R Sy, Subgroup.map α.toMonoidHom X = X ↔ conjSubgroup X g = X) →
    α ∈ (MulAut.conj : L →* MulAut L).range
  parabolic : ∃ X₂ Pα : Subgroup L, RootParabolic R Sy X₂ Pα e

@[expose] def SpRootSetup (L : Type) [Group L] (m n : ℕ) (R Sy : Subgroup L) : Prop :=
  4 ≤ m ∧ IsSpGp L m n ∧ IsSymplecticRootGroup L m n R ∧
    (∃ P : Sylow 2 L, (P : Subgroup L) = Sy) ∧ Sy ≤ Subgroup.normalizer (R : Set L) ∧ R ≤ Sy

@[expose] def PSURootSetup (L : Type) [Group L] (m n : ℕ) (R Sy : Subgroup L) : Prop :=
  4 ≤ m ∧ IsPSUGp L m n ∧ IsUnitaryRootGroup L m n R ∧
    (∃ P : Sylow 2 L, (P : Subgroup L) = Sy) ∧ Sy ≤ Subgroup.normalizer (R : Set L) ∧ R ≤ Sy

@[expose] def SpPSUOutFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (m n : ℕ), 4 ≤ m → (IsSpGp L m n ∨ IsPSUGp L m n) →
    ∀ α β : MulAut L, α * α = 1 → β * β = 1 → α * β = β * α →
      α ∉ (MulAut.conj : L →* MulAut L).range → β ∉ (MulAut.conj : L →* MulAut L).range →
      α * β ∈ (MulAut.conj : L →* MulAut L).range

@[expose] def SpPSUFixFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (m n : ℕ) (R Sy : Subgroup L),
    (SpRootSetup L m n R Sy ∨ PSURootSetup L m n R Sy) →
    ∀ (α : MulAut L) (g : L), g ∈ Sy → g * g = 1 → α * α = 1 →
      α * MulAut.conj g = MulAut.conj g * α → Subgroup.map α.toMonoidHom Sy = Sy →
      Subgroup.map α.toMonoidHom R = R →
      (∀ X ∈ rootGroupsIn R Sy, Subgroup.map α.toMonoidHom X = X ↔ conjSubgroup X g = X) →
      α ∈ (MulAut.conj : L →* MulAut L).range

@[expose] def SpPSUParabolicFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (m n : ℕ) (R Sy : Subgroup L),
    (SpRootSetup L m n R Sy → ∃ X₂ Pα : Subgroup L, RootParabolic R Sy X₂ Pα 1) ∧
    (PSURootSetup L m n R Sy → ∃ X₂ Pα : Subgroup L, RootParabolic R Sy X₂ Pα 2)

structure SpPSULieFacts : Prop where
  out : SpPSUOutFact
  fix : SpPSUFixFact
  parabolic : SpPSUParabolicFact

theorem rootLieFacts_sp (hLie : SpPSULieFacts) {L : Type} [Group L] [Finite L] {m n : ℕ}
    (hm : 4 ≤ m) (hL : IsSpGp L m n) {R Sy : Subgroup L} (hR : IsSymplecticRootGroup L m n R)
    (hSy : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) (hRSy : Sy ≤ Subgroup.normalizer (R : Set L))
    (hle : R ≤ Sy) : RootLieFacts L R Sy 1 where
  center := center_eq_bot_of_isSpGp hL
  out α β hα hβ hcomm _ _ hα' hβ' := hLie.out L m n hm (Or.inl hL) α β hα hβ hcomm hα' hβ'
  fix α g hg hg2 hα hc hS hR' hX :=
    hLie.fix L m n R Sy (Or.inl ⟨hm, hL, hR, hSy, hRSy, hle⟩) α g hg hg2 hα hc hS hR' hX
  parabolic := (hLie.parabolic L m n R Sy).1 ⟨hm, hL, hR, hSy, hRSy, hle⟩

theorem rootLieFacts_psu (hLie : SpPSULieFacts) {L : Type} [Group L] [Finite L] {m n : ℕ}
    (hm : 4 ≤ m) (hL : IsPSUGp L m n) {R Sy : Subgroup L} (hR : IsUnitaryRootGroup L m n R)
    (hSy : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) (hRSy : Sy ≤ Subgroup.normalizer (R : Set L))
    (hle : R ≤ Sy) : RootLieFacts L R Sy 2 where
  center := center_eq_bot_of_isPSUGp hm hL
  out α β hα hβ hcomm _ _ hα' hβ' := hLie.out L m n hm (Or.inr hL) α β hα hβ hcomm hα' hβ'
  fix α g hg hg2 hα hc hS hR' hX :=
    hLie.fix L m n R Sy (Or.inr ⟨hm, hL, hR, hSy, hRSy, hle⟩) α g hg hg2 hα hc hS hR' hX
  parabolic := (hLie.parabolic L m n R Sy).2 ⟨hm, hL, hR, hSy, hRSy, hle⟩

private theorem w85g_mem_normalizer_of_conj_eq {L : Type} [Group L] {Sy : Subgroup L}
    {x : L} {σ : MulAut L} (hx : MulAut.conj x = σ)
    (hσ : Subgroup.map σ.toMonoidHom Sy = Sy) :
    x ∈ Subgroup.normalizer (Sy : Set L) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hx]
  exact hσ

private theorem w85g_mem_sylow_of_mem_normalizer {L : Type} [Group L] [Finite L]
    {Sy : Subgroup L} (hSyl : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy)
    {x : L} (hxN : x ∈ Subgroup.normalizer (Sy : Set L)) (hx2 : x * x = 1) :
    x ∈ Sy := by
  obtain ⟨P, rfl⟩ := hSyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.RankThree.Transfer.mem_of_pow_eq_one_of_mem_normalizer P hxN (k := 1)
    (by rw [pow_one, pow_two]; exact hx2)

private theorem w85g_map_conj_eq_iff_conjSubgroup {G : Type*} [Group G] (X : Subgroup G) (g : G) :
    Subgroup.map (MulAut.conj g).toMonoidHom X = X ↔ conjSubgroup X g = X :=
  (Subgroup.mem_normalizer_iff_map_conj_eq (H := X) (g := g)).symm.trans
    (conjSubgroup_eq_iff_mem_normalizer (A := X) (g := g)).symm

private theorem w85g_sq_eq_one_of_conj_eq {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    {U : Type} [Group U] (α : U →* MulAut L) (hexp : ∀ u : U, u * u = 1) {x : L} {u : U}
    (hx : MulAut.conj x = α u) : x * x = 1 := by
  have h : MulAut.conj (x * x) = 1 := by
    rw [map_mul, hx, ← map_mul, hexp u, map_one]
  have hc : x * x ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : x * x * y * (x * x)⁻¹ = y := by
      have hx' := congrArg (fun f : MulAut L => f y) h
      rw [MulAut.conj_apply] at hx'
      exact hx'
    have : x * x * y = y * (x * x) := by
      calc x * x * y = (x * x * y * (x * x)⁻¹) * (x * x) := by group
        _ = y * (x * x) := by rw [hy]
    exact this.symm
  rwa [hZ, Subgroup.mem_bot] at hc

private theorem w85g_comm_of_exp {U : Type} [Group U] (hexp : ∀ u : U, u * u = 1) :
    ∀ u v : U, u * v = v * u := by
  intro u v
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hexp u)
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hexp v)
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right (hexp (u * v))).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by rw [hu, hv]

private theorem w85g_mem_sylow_of_conj_eq {L : Type} [Group L] [Finite L]
    {Sy : Subgroup L} (hSyl : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy)
    (hZ : Subgroup.center L = ⊥) {U : Type} [Group U] (α : U →* MulAut L)
    (hexp : ∀ u : U, u * u = 1)
    (hSy : ∀ u : U, Subgroup.map (α u).toMonoidHom Sy = Sy)
    {x : L} {u : U} (hx : MulAut.conj x = α u) : x ∈ Sy :=
  w85g_mem_sylow_of_mem_normalizer hSyl (w85g_mem_normalizer_of_conj_eq hx (hSy u))
    (w85g_sq_eq_one_of_conj_eq hZ α hexp hx)

private theorem w85g_exists_inner_of_two_lt_card {L : Type} [Group L] [Finite L]
    {R Sy X₂ Pα : Subgroup L} {e : ℕ}
    (hL : RootLieFacts L R Sy e) (hP : RootParabolic R Sy X₂ Pα e)
    (hSyl : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) {U : Type} [Group U]
    [Finite U] (α : U →* MulAut L) (hexp : ∀ u : U, u * u = 1)
    (hSy : ∀ u : U, Subgroup.map (α u).toMonoidHom Sy = Sy)
    (hR : ∀ u : U, Subgroup.map (α u).toMonoidHom R = R)
    (hU : 2 < Nat.card U) :
    ∃ u₀ : U, u₀ ≠ 1 ∧ α u₀ ∈ (MulAut.conj : L →* MulAut L).range := by
  by_contra h
  have hcomm : ∀ u v : U, u * v = v * u := w85g_comm_of_exp hexp
  have houter : ∀ w : U, w ≠ 1 → α w ∉ (MulAut.conj : L →* MulAut L).range := by
    intro w hw hmem
    exact h ⟨w, hw, hmem⟩
  haveI : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card] at hU
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hU
  have htwo : ∃ u v : U, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
    by_cases ha : a = 1
    · exact ⟨b, c, by rintro rfl; exact hab ha, by rintro rfl; exact hac ha, hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, by rintro rfl; exact hbc hb, hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨u, v, hu, hv, huv⟩ := htwo
  have huv1 : u * v ≠ 1 := by
    intro h1
    exact huv (by rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (hexp u)])
  refine houter (u * v) huv1 ?_
  rw [map_mul]
  exact hL.out (α u) (α v) (by rw [← map_mul, hexp u, map_one])
    (by rw [← map_mul, hexp v, map_one])
    (by rw [← map_mul, ← map_mul, hcomm u v]) (hR u) (hR v) (houter u hu) (houter v hv)

private theorem w85g_steps_four_five_core {L : Type} [Group L] [Finite L]
    {R Sy X₂ Pα : Subgroup L} {e : ℕ}
    (hL : RootLieFacts L R Sy e) (hP : RootParabolic R Sy X₂ Pα e)
    (hSyl : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) {U : Type} [Group U]
    [Finite U] (α : U →* MulAut L) (hexp : ∀ u : U, u * u = 1)
    (hSy : ∀ u : U, Subgroup.map (α u).toMonoidHom Sy = Sy)
    (hR : ∀ u : U, Subgroup.map (α u).toMonoidHom R = R)
    (hcard : (Nat.card R) ^ e < Nat.card U)
    (hstar : ∀ u : U, u ≠ 1 → ∀ X ∈ rootGroupsIn R Sy,
      Subgroup.map (α u).toMonoidHom X = X → ∀ u' : U, Subgroup.map (α u').toMonoidHom X = X)
    (hu₀ : ∃ u₀ : U, u₀ ≠ 1 ∧ α u₀ ∈ (MulAut.conj : L →* MulAut L).range) :
    ∀ u : U, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set L), α u = MulAut.conj g := by
  classical
  obtain ⟨u₀, hu₀ne, g₀, hg₀⟩ := hu₀
  have hg₀_sy : g₀ ∈ Sy := w85g_mem_sylow_of_conj_eq hSyl hL.center α hexp hSy hg₀
  have hinner : ∀ u : U, α u ∈ (MulAut.conj : L →* MulAut L).range := by
    intro u
    by_cases hu : u = 1
    · subst hu
      exact ⟨1, by simp⟩
    · refine hL.fix (α u) g₀ hg₀_sy (w85g_sq_eq_one_of_conj_eq hL.center α hexp hg₀) ?_ ?_
        (hSy u) (hR u) ?_
      · rw [← map_mul, hexp u, map_one]
      · rw [hg₀, ← map_mul, ← map_mul, w85g_comm_of_exp hexp u u₀]
      · intro X hX
        rw [← w85g_map_conj_eq_iff_conjSubgroup, hg₀]
        exact ⟨fun h => hstar u hu X hX h u₀, fun h => hstar u₀ hu₀ne X hX h u⟩
  choose g hg using hinner
  have hg_sy : ∀ u : U, g u ∈ Sy := fun u =>
    w85g_mem_sylow_of_conj_eq hSyl hL.center α hexp hSy (hg u)
  intro u
  by_cases hcase : ∀ u' : U, Subgroup.map (α u').toMonoidHom X₂ = X₂
  · refine ⟨g u, ⟨hg_sy u, ?_⟩, (hg u).symm⟩
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := X₂) (g := g u)).mpr
      (by rw [hg u]; exact hcase u)
  · exfalso
    obtain ⟨u₁, hu₁⟩ := not_forall.mp hcase
    have hu₁ne : u₁ ≠ 1 := by
      rintro rfl
      exact hu₁ (by rw [map_one]; exact Subgroup.map_id X₂)
    have hnone : ∀ u : U, u ≠ 1 → Subgroup.map (α u).toMonoidHom X₂ ≠ X₂ := by
      intro u hu h
      exact hu₁ (hstar u hu X₂ hP.mem h u₁)
    let N' : Subgroup ↥Sy := (Sy ⊓ Subgroup.normalizer (X₂ : Set L)).subgroupOf Sy
    let f : U → ↥Sy ⧸ N' := fun u => QuotientGroup.mk ⟨g u, hg_sy u⟩
    have hf : Function.Injective f := by
      intro u v huv
      have hmem : (⟨g u, hg_sy u⟩ : ↥Sy)⁻¹ * ⟨g v, hg_sy v⟩ ∈ N' :=
        QuotientGroup.eq.mp huv
      have hmem' : (g u)⁻¹ * g v ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set L) :=
        Subgroup.mem_subgroupOf.mp hmem
      have hN : (g u)⁻¹ * g v ∈ Subgroup.normalizer (X₂ : Set L) :=
        (Subgroup.mem_inf.mp hmem').2
      have hconj : MulAut.conj ((g u)⁻¹ * g v) = α (u * v) := by
        rw [map_mul, map_inv, hg u, hg v, ← map_inv, ← map_mul]
        congr 1
        rw [inv_eq_of_mul_eq_one_right (hexp u)]
      have hmap : Subgroup.map (α (u * v)).toMonoidHom X₂ = X₂ := by
        rw [← hconj]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
      have huv1 : u * v = 1 := by
        by_contra hne
        exact hnone (u * v) hne hmap
      rw [eq_inv_of_mul_eq_one_right huv1, inv_eq_of_mul_eq_one_right (hexp u)]
    have hidx : Nat.card (↥Sy ⧸ N') = (Subgroup.normalizer (X₂ : Set L)).relIndex Sy := by
      rw [← Subgroup.index_eq_card]
      change (Sy ⊓ Subgroup.normalizer (X₂ : Set L)).relIndex Sy = _
      exact Subgroup.inf_relIndex_left Sy (Subgroup.normalizer (X₂ : Set L))
    have hle : Nat.card U ≤ (Subgroup.normalizer (X₂ : Set L)).relIndex Sy := by
      calc Nat.card U ≤ Nat.card (↥Sy ⧸ N') := Nat.card_le_card_of_injective f hf
        _ = (Subgroup.normalizer (X₂ : Set L)).relIndex Sy := hidx
    exact (lt_irrefl _) (lt_of_le_of_lt (le_trans hle hP.index) hcard)

theorem steps_four_five {L : Type} [Group L] [Finite L] {R Sy X₂ Pα : Subgroup L} {e : ℕ}
    (hL : RootLieFacts L R Sy e) (hP : RootParabolic R Sy X₂ Pα e)
    (hSyl : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) {U : Type} [Group U]
    [Finite U] (α : U →* MulAut L) (hexp : ∀ u : U, u * u = 1)
    (hSy : ∀ u : U, Subgroup.map (α u).toMonoidHom Sy = Sy)
    (hR : ∀ u : U, Subgroup.map (α u).toMonoidHom R = R)
    (hcard : (Nat.card R) ^ e < Nat.card U)
    (hstar : ∀ u : U, u ≠ 1 → ∀ X ∈ rootGroupsIn R Sy,
      Subgroup.map (α u).toMonoidHom X = X → ∀ u' : U, Subgroup.map (α u').toMonoidHom X = X) :
    ∀ u : U, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set L), α u = MulAut.conj g := by
  have hRne : R ≠ ⊥ := by
    intro hbot
    exact hP.not_le (by rw [hbot, Subgroup.normalizer_eq_top]; exact le_top)
  have hRcard : 2 ≤ Nat.card R := by
    have h := (Subgroup.one_lt_card_iff_ne_bot (H := R)).mpr hRne
    omega
  have hRpow : 2 ≤ (Nat.card R) ^ e := by
    calc 2 ≤ Nat.card R := hRcard
      _ = (Nat.card R) ^ 1 := (pow_one _).symm
      _ ≤ (Nat.card R) ^ e := Nat.pow_le_pow_right Nat.card_pos hP.one_le
  have hU : 2 < Nat.card U := lt_of_le_of_lt hRpow hcard
  exact w85g_steps_four_five_core hL hP hSyl α hexp hSy hR hcard hstar
    (w85g_exists_inner_of_two_lt_card hL hP hSyl α hexp hSy hR hU)

end CFSG.LocalAnalysis.WeakClosure81

end
