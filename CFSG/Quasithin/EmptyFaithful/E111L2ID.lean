module

public import CFSG.Quasithin.EmptyFaithful.E111RMemB

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

@[expose] def conjFam (R Z : Subgroup G) : Set (Subgroup G) :=
  Set.range fun k : ↥R => A1b.conjSub (k : G) Z

theorem conj_mem_conjFam {R Z : Subgroup G} {k : G} (hk : k ∈ R) :
    A1b.conjSub k Z ∈ conjFam R Z :=
  ⟨⟨k, hk⟩, rfl⟩

theorem conj_conjFam {R Z Z' : Subgroup G} {r : G} (hr : r ∈ R) (hZ' : Z' ∈ conjFam R Z) :
    A1b.conjSub r Z' ∈ conjFam R Z := by
  obtain ⟨k, rfl⟩ := hZ'
  rw [← A1b.conjSub_mul]
  exact conj_mem_conjFam (R.mul_mem hr k.2)

theorem le_normalizer_sSup [Finite G] {𝒵 : Set (Subgroup G)} {Y : Subgroup G}
    (hY : ∀ y ∈ Y, ∀ Z ∈ 𝒵, A1b.conjSub y Z ∈ 𝒵) :
    Y ≤ Subgroup.normalizer ((sSup 𝒵 : Subgroup G) : Set G) := by
  have key : ∀ y ∈ Y, A1b.conjSub y (sSup 𝒵) ≤ sSup 𝒵 := by
    intro y hy
    conv_lhs => rw [sSup_eq_iSup', E111R.conjSub_iSup]
    exact iSup_le fun Z => le_sSup (hY y hy Z Z.2)
  exact fun y hy => mem_normalizer_of_conjSub_le (key y hy) (key _ (Y.inv_mem hy))

theorem le_normalizer_conjFam [Finite G] (R Z : Subgroup G) :
    R ≤ Subgroup.normalizer ((sSup (conjFam R Z) : Subgroup G) : Set G) :=
  le_normalizer_sSup fun _ hr _ hZ' => conj_conjFam hr hZ'

theorem conjSub_inv_conjSub (g : G) (Z : Subgroup G) :
    A1b.conjSub g⁻¹ (A1b.conjSub g Z) = Z := by
  rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]

theorem conjSub_normalizer (g : G) (Z : Subgroup G) :
    A1b.conjSub g (Subgroup.normalizer (Z : Set G)) =
      Subgroup.normalizer ((A1b.conjSub g Z : Subgroup G) : Set G) := by
  unfold A1b.conjSub
  exact Subgroup.map_equiv_normalizer_eq Z (MulAut.conj g)

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

theorem conj_le_normalizer [Finite G] {Z₁ Z₂ : Subgroup G} (hZ₁ : Z₁ ≤ diagSub S C h.diagComm)
    (hZ₂ : Z₂ ≤ diagSub S C h.diagComm)
    (hinv₁ : ∀ k ∈ T ⊓ Subgroup.centralizer (A : Set G),
      A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm → A1b.conjSub k Z₁ = Z₁)
    (hN : Z₁ ≤ Subgroup.normalizer (Z₂ : Set G)) {k k' : G}
    (hk : k ∈ T ⊓ Subgroup.centralizer (A : Set G))
    (hk' : k' ∈ T ⊓ Subgroup.centralizer (A : Set G)) :
    A1b.conjSub k Z₁ ≤ Subgroup.normalizer ((A1b.conjSub k' Z₂ : Subgroup G) : Set G) := by
  set m := k'⁻¹ * k with hm
  have hmR : m ∈ T ⊓ Subgroup.centralizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk') hk
  have hkm : k = k' * m := by rw [hm]; group
  rw [hkm, A1b.conjSub_mul, ← conjSub_normalizer]
  refine A1b.conjSub_mono k' ?_
  rcases h.eq_or_commute_conj hmR.2 with hD | hc
  · rw [hinv₁ m hmR hD]
    exact hN
  · intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc x (A1b.conjSub_mono m hZ₁ hx) y (hZ₂ hy)).symm

theorem conj_commute_of_ne [Finite G] {Z : Subgroup G} (hZ : Z ≤ diagSub S C h.diagComm)
    (hinv : ∀ k ∈ T ⊓ Subgroup.centralizer (A : Set G),
      A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm → A1b.conjSub k Z = Z)
    {k k' : G} (hk : k ∈ T ⊓ Subgroup.centralizer (A : Set G))
    (hk' : k' ∈ T ⊓ Subgroup.centralizer (A : Set G))
    (hne : A1b.conjSub k Z ≠ A1b.conjSub k' Z) :
    ∀ x ∈ A1b.conjSub k Z, ∀ y ∈ A1b.conjSub k' Z, x * y = y * x := by
  set m := k'⁻¹ * k with hm
  have hmR : m ∈ T ⊓ Subgroup.centralizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk') hk
  have hkm : k = k' * m := by rw [hm]; group
  rcases h.eq_or_commute_conj hmR.2 with hD | hc
  · exact absurd (by rw [hkm, A1b.conjSub_mul, hinv m hmR hD]) hne
  · intro x hx y hy
    rw [hkm, A1b.conjSub_mul, A1b.mem_conjSub_iff] at hx
    rw [A1b.mem_conjSub_iff] at hy
    have h1 := hc _ (A1b.conjSub_mono m hZ hx) _ (hZ hy)
    calc x * y = k' * ((k'⁻¹ * x * k') * (k'⁻¹ * y * k')) * k'⁻¹ := by group
      _ = k' * ((k'⁻¹ * y * k') * (k'⁻¹ * x * k')) * k'⁻¹ := by rw [h1]
      _ = y * x := by group

theorem sSup_le_normalizer [Finite G] {Z₁ Z₂ : Subgroup G} (hZ₁ : Z₁ ≤ diagSub S C h.diagComm)
    (hZ₂ : Z₂ ≤ diagSub S C h.diagComm)
    (hinv₁ : ∀ k ∈ T ⊓ Subgroup.centralizer (A : Set G),
      A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm → A1b.conjSub k Z₁ = Z₁)
    (hN : Z₁ ≤ Subgroup.normalizer (Z₂ : Set G)) :
    sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) Z₁) ≤
      Subgroup.normalizer ((sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) Z₂) :
        Subgroup G) : Set G) := by
  refine sSup_le fun Z₁' hZ₁' => le_normalizer_sSup fun y hy Z₂' hZ₂' => ?_
  obtain ⟨k, rfl⟩ := hZ₁'
  obtain ⟨k', rfl⟩ := hZ₂'
  have hyN := conj_le_normalizer h hZ₁ hZ₂ hinv₁ hN k.2 k'.2 hy
  rw [conjSub_eq_of_mem_normalizer hyN]
  exact conj_mem_conjFam k'.2

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
