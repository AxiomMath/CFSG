module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G]

noncomputable abbrev rOmega189 (M H : Subgroup G) (c : G) : Subgroup G :=
  omegaOneTwo189 (s189 M H) ⊔ (s189 M H ⊓ theta189 M H c)

theorem rOmega189_le_s189 (M H : Subgroup G) (c : G) : rOmega189 M H c ≤ s189 M H :=
  sup_le (omegaOneTwo189_le _) inf_le_left

theorem conj_mem_omegaOneTwo189 {S : Subgroup G} {s x : G} (hs : s ∈ S)
    (hx : x ∈ omegaOneTwo189 S) : s * x * s⁻¹ ∈ omegaOneTwo189 S := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact Subgroup.subset_closure
      ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs),
        by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩
  | one => simpa using (omegaOneTwo189 S).one_mem
  | mul y z _ _ hy hz =>
    have h : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
    rw [h]
    exact (omegaOneTwo189 S).mul_mem hy hz
  | inv y _ hy =>
    have h : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
    rw [h]
    exact (omegaOneTwo189 S).inv_mem hy

theorem le_normalizer_omegaOneTwo189 (S : Subgroup G) :
    S ≤ Subgroup.normalizer (omegaOneTwo189 S : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_omegaOneTwo189 hs, fun hx => ?_⟩
  have h := conj_mem_omegaOneTwo189 (S.inv_mem hs) hx
  have he : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
  rwa [he] at h

theorem mem_normalizer_inf189 {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX x, hY x]

section Helpers

variable {Y : Type*} [Group Y]

theorem mem_normalizer_zpowers189 {a g : Y} (h1 : g * a * g⁻¹ ∈ Subgroup.zpowers a)
    (h2 : g⁻¹ * a * g ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 n
  · intro hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    have he : h = (g⁻¹ * a * g⁻¹⁻¹) ^ n := by
      rw [conj_zpow, hn]
      group
    rw [he, inv_inv]
    exact Subgroup.zpow_mem _ h2 n

theorem mem_normalizer_of_mem_centralizer189 {X Z : Subgroup Y} {g : Y} (hXZ : X ≤ Z)
    (hg : g ∈ Subgroup.centralizer (Z : Set Y)) :
    g ∈ Subgroup.normalizer (X : Set Y) := by
  have hc : ∀ x ∈ X, g * x * g⁻¹ = x := fun x hx => by
    rw [← Subgroup.mem_centralizer_iff.mp hg x (hXZ hx), mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => by rwa [hc x hx], fun hx => ?_⟩
  have h1 := hc _ hx
  have h2 : g * x * g⁻¹ = x := by
    calc g * x * g⁻¹ = g⁻¹ * (g * (g * x * g⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = x := by group
  rwa [h2] at hx

end Helpers

theorem imAlpha189_zpowers (M H : Subgroup G) (c : G) (hcSK : c ∈ sk189 M H c) :
    imAlpha189 M H c (Subgroup.zpowers c) = Subgroup.zpowers (alpha189 M H c ⟨c, hcSK⟩) := by
  have hmap : (Subgroup.zpowers (⟨c, hcSK⟩ : ↥(sk189 M H c))).map (sk189 M H c).subtype =
      Subgroup.zpowers c :=
    MonoidHom.map_zpowers _ _
  have hsub : (Subgroup.zpowers c).subgroupOf (sk189 M H c) =
      Subgroup.zpowers (⟨c, hcSK⟩ : ↥(sk189 M H c)) := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [imAlpha189, hsub, MonoidHom.map_zpowers]

variable [Finite G]

theorem normalizer_rOmega189_le_fourChar (M H : Subgroup G) (c : G) (i : Fin 4) (hi : i ≠ 0) :
    Subgroup.normalizer (rOmega189 M H c : Set G) ≤
      Subgroup.normalizer (fourChar (s189 M H) i : Set G) := by
  rw [fourChar_eq_of_le189 (rOmega189_le_s189 M H c)
    (fun E hE => by exact (map_le_omegaOneTwo189 (S := s189 M H) (E := E)).trans le_sup_left)
    i hi]
  exact Sec20.normalizer_le_normalizer_fourChar _ i

theorem isSylowOf_rOmega189 (h186 : Item186H) {A M H : Subgroup G} {c : G}
    (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    CFSG.ABGLocalTools.IsSylowOf 2 (rOmega189 M H c) (rOmega189 M H c ⊔ theta189 M H c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRS := rOmega189_le_s189 M H c
  have hSθ : s189 M H ≤ Subgroup.normalizer (theta189 M H c : Set G) :=
    (le_sup_left : s189 M H ≤ sk189 M H c).trans (sk189_le_normalizer_theta189 M H c)
  have hSR : s189 M H ≤ Subgroup.normalizer (rOmega189 M H c : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_omegaOneTwo189 _ hs,
        mem_normalizer_inf189 (Subgroup.le_normalizer hs) (hSθ hs)⟩
  have hN : s189 M H ⊔ theta189 M H c ≤
      Subgroup.normalizer ((rOmega189 M H c ⊔ theta189 M H c : Subgroup G) : Set G) :=
    sup_le (fun s hs => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hSR hs, hSθ hs⟩)
      ((le_sup_right : theta189 M H c ≤ rOmega189 M H c ⊔ theta189 M H c).trans
        Subgroup.le_normalizer)
  have hsyl := (isSylowOf_s189 h186 h h7).inf_of_le_normalizer (sup_le_sup_right hRS _) hN
  have heq : s189 M H ⊓ (rOmega189 M H c ⊔ theta189 M H c) = rOmega189 M H c := by
    refine le_antisymm ?_ (le_inf hRS le_sup_left)
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxRθ⟩ := hx
    have hxRθ' : x ∈ ((rOmega189 M H c ⊔ theta189 M H c : Subgroup G) : Set G) := hxRθ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hRS.trans hSθ)] at hxRθ'
    obtain ⟨r, hr, t, ht, rfl⟩ := Set.mem_mul.mp hxRθ'
    have htS : t ∈ s189 M H := by
      have he : t = r⁻¹ * (r * t) := by group
      rw [he]
      exact (s189 M H).mul_mem ((s189 M H).inv_mem (hRS hr)) hxS
    exact (rOmega189 M H c).mul_mem hr
      ((le_sup_right : s189 M H ⊓ theta189 M H c ≤ rOmega189 M H c) ⟨htS, ht⟩)
  rwa [heq] at hsyl

theorem mem_n189_of_mem_normalizer_omegaAlpha189 (h186 : Item186H) (h187 : Item187)
    {A M H : Subgroup G} {c : G} (h : Sec18H G A M H c) (h7 : Hyp187 A M H c)
    (hthree : Subgroup.normalizer (fourChar (s189 M H) 1 : Set G) ≤ n189 H ∨
      Subgroup.normalizer (fourChar (s189 M H) 2 : Set G) ≤ n189 H)
    {x : ↥(sk189 M H c)}
    (hx : alpha189 M H c x ∈ Subgroup.normalizer
      (imAlpha189 M H c (omegaOneTwo189 (s189 M H)) : Set (SKAlpha189 M H c))) :
    (x : G) ∈ n189 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩSK : omegaOneTwo189 (s189 M H) ≤ sk189 M H c :=
    (omegaOneTwo189_le _).trans le_sup_left
  have hYSK : rOmega189 M H c ⊔ theta189 M H c ≤ sk189 M H c :=
    sup_le ((rOmega189_le_s189 M H c).trans le_sup_left) (theta189_le M H c)
  have hRθ : rOmega189 M H c ⊔ theta189 M H c = omegaOneTwo189 (s189 M H) ⊔ theta189 M H c :=
    le_antisymm (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hpre : (imAlpha189 M H c (omegaOneTwo189 (s189 M H))).comap (alpha189 M H c) =
      (rOmega189 M H c ⊔ theta189 M H c).subgroupOf (sk189 M H c) := by
    rw [hRθ, imAlpha189, Subgroup.comap_map_eq, alpha189, QuotientGroup.ker_mk',
      Subgroup.subgroupOf_sup hΩSK (theta189_le M H c)]
    congr 1
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  have hxN : x ∈ Subgroup.normalizer
      (((rOmega189 M H c ⊔ theta189 M H c).subgroupOf (sk189 M H c) : Subgroup _) : Set _) := by
    rw [← hpre, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hx
  have hxG := Sec20.mem_normalizer_of_mem_normalizer_subgroupOf hYSK hxN
  obtain ⟨n, hn, m, hm, hnm⟩ := exists_mul_of_isSylowOf (isSylowOf_rOmega189 h186 h h7)
    (Subgroup.zpowers_le.mpr hxG) (Subgroup.mem_zpowers _)
  rw [hnm]
  refine (n189 H).mul_mem ((sup_le ((rOmega189_le_s189 M H c).trans (s189_le_n189 M H))
    (theta189_le_n189 h187 h h7)) hn) ?_
  rcases hthree with h1 | h2
  · exact h1 (normalizer_rOmega189_le_fourChar M H c 1 (by decide) hm)
  · exact h2 (normalizer_rOmega189_le_fourChar M H c 2 (by decide) hm)

end CFSG.RankThree.PartTwo.Sec18
