module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructInduces
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem okEq_mem_bs_decomp {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {b : G} (hb : b ∈ Bs) :
    ∃ (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) (c : G),
      c ∈ Bs ⊓ Subgroup.centralizer (K : Set G) ∧
        ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c = b := by
  have hcomm : ∀ s ∈ (halfTorus n).map ψ,
      ∀ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), Commute s c := by
    intro s hs c hc
    have hsK : s ∈ K := by
      rw [← hψ.range]
      obtain ⟨t, _ht, htψ⟩ := Subgroup.mem_map.mp hs
      exact ⟨t, htψ⟩
    exact Subgroup.mem_centralizer_iff.mp hc.2 s hsK
  rw [hprod] at hb
  obtain ⟨s, hs, c, hc, hsc⟩ := (CFSG.mem_sup_of_commute hcomm).mp hb
  obtain ⟨t, ht, htψ⟩ := Subgroup.mem_map.mp hs
  obtain ⟨a, ha⟩ := Φ.surjective ⟨t, ht⟩
  have hΦa : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = t := congrArg Subtype.val ha
  refine ⟨a, c, hc, ?_⟩
  rw [hΦa, htψ]
  exact hsc

theorem okEq_eq_one_of_mem_centralizer {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : ψ t ∈ Subgroup.centralizer (K : Set G)) : t = 1 := by
  apply eq_one_of_commute_range hψ.inj
  intro u
  exact (Subgroup.mem_centralizer_iff.mp ht (ψ u) (by rw [← hψ.range]; exact ⟨u, rfl⟩)).symm

theorem okEq_decomp_unique {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {a a' : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)} {c c' : G}
    (hc : c ∈ Bs ⊓ Subgroup.centralizer (K : Set G))
    (hc' : c' ∈ Bs ⊓ Subgroup.centralizer (K : Set G))
    (h : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c =
      ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c') :
    a = a' ∧ c = c' := by
  have h2 : (ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ *
      ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = c' * c⁻¹ := by
    apply mul_right_cancel (b := c)
    calc ((ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ *
            ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2)) * c
        = (ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ *
            (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c) := by group
      _ = (ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ *
            (ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c') := by rw [h]
      _ = (c' * c⁻¹) * c := by group
  have hcC : c' * c⁻¹ ∈ Bs ⊓ Subgroup.centralizer (K : Set G) :=
    (Bs ⊓ Subgroup.centralizer (K : Set G)).mul_mem hc'
      ((Bs ⊓ Subgroup.centralizer (K : Set G)).inv_mem hc)
  have ht : (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2)⁻¹ *
      (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = 1 := by
    apply okEq_eq_one_of_mem_centralizer hψ
    rw [map_mul, map_inv, h2]
    exact hcC.2
  have hΦeq : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) =
      (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) := by
    calc (Φ a : SpecialLinearGroup (Fin (n + 1)) F2)
        = (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) *
            ((Φ a' : SpecialLinearGroup (Fin (n + 1)) F2)⁻¹ *
              (Φ a : SpecialLinearGroup (Fin (n + 1)) F2)) := by group
      _ = (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * 1 := by rw [ht]
      _ = (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) := by group
  have ha : a = a' := Φ.injective (Subtype.ext hΦeq)
  have hcc : c = c' := by
    rw [hΦeq] at h
    exact mul_left_cancel h
  exact ⟨ha, hcc⟩

theorem okEq_psi_Phi_injective {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)} :
    Function.Injective
      (fun a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) =>
        ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2)) := by
  intro a a' h
  exact Φ.injective (Subtype.ext (hψ.inj h))

theorem okEq_card_coords (k : ℕ) :
    Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
  rw [Nat.card_fun, Nat.card_fin]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end CFSG.StandardType

end
