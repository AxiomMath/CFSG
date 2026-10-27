module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import Mathlib

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

section Helpers

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)

theorem q2nPE_cell_eq_mul (w : W) :
    bruhatCell hct w = (borel D H : Set K) * {nrep hct w} * (borel D H : Set K) := by
  ext g
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact Set.mem_mul.2 ⟨b₁ * nrep hct w,
      Set.mem_mul.2 ⟨b₁, hb₁, nrep hct w, rfl, rfl⟩, b₂, hb₂, rfl⟩
  · intro hg
    obtain ⟨x, hx, b₂, hb₂, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨b₁, hb₁, y, hy, rfl⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩

private theorem q2nPE_n_mem_simple_cell (i : Fin D.rank) :
    n i ∈ bruhatCell hct ((cs).simple i) := by
  rw [← nrep_simple hct i]
  exact nrep_mem_bruhatCell hct _

private theorem q2nPE_borel_mul_cell (w : W) :
    (borel D H : Set K) * bruhatCell hct w = bruhatCell hct w := by
  apply le_antisymm
  · intro g hg
    obtain ⟨b, hb, x, hx, rfl⟩ := Set.mem_mul.1 hg
    exact mul_mem_bruhatCell hct hb hx
  · intro g hg
    exact Set.mem_mul.2 ⟨1, one_mem _, g, hg, one_mul g⟩

private theorem q2nPE_cell_mul_borel (w : W) :
    bruhatCell hct w * (borel D H : Set K) = bruhatCell hct w := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx, b, hb, rfl⟩ := Set.mem_mul.1 hg
    exact mul_mem_bruhatCell_right hct hx hb
  · intro g hg
    exact Set.mem_mul.2 ⟨g, hg, 1, one_mem _, mul_one g⟩

private theorem q2nPE_borel_sub_simple_cell_mul_self (i : Fin D.rank) :
    (borel D H : Set K) ⊆
      bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i) := by
  intro b hb
  have hni := q2nPE_n_mem_simple_cell hct i
  have hT : n i * n i ∈ (borel D H : Set K) :=
    iSup_le_borel (by rw [← pow_two]; exact sq_n_mem_iSup hct i)
  have hsq : n i * n i ∈
      bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i) :=
    Set.mul_mem_mul hni hni
  have hleft : ∀ c ∈ (borel D H : Set K),
      ∀ g ∈ bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i),
      c * g ∈ bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i) := by
    intro c hc g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
    exact Set.mem_mul.2 ⟨c * x, mul_mem_bruhatCell hct hc hx, y, hy, by group⟩
  have h := hleft (b * (n i * n i)⁻¹) (mul_mem hb (inv_mem hT)) (n i * n i) hsq
  rwa [show (b * (n i * n i)⁻¹) * (n i * n i) = b by group] at h

variable (hext : SteinbergExtras D n H)
include hext

theorem q2nPE_inv_cell (w : W) : (bruhatCell hct w)⁻¹ = bruhatCell hct w⁻¹ := by
  have hx : (nrep hct w)⁻¹ ∈ weylN n H := inv_mem (nrep_mem_weylN hct w)
  have hact : ActsAs D ((nrep hct w)⁻¹) w⁻¹ := (actsAs_nrep hct w).inv
  rw [bruhatCell_eq_of_actsAs hct hext hx hact]
  ext g
  constructor
  · intro hg
    rw [Set.mem_inv] at hg
    obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hg
    refine ⟨b₂⁻¹, inv_mem hb₂, b₁⁻¹, inv_mem hb₁, ?_⟩
    rw [show g = (b₁ * nrep hct w * b₂)⁻¹ by rw [← he, inv_inv]]
    group
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    rw [Set.mem_inv]
    exact ⟨b₂⁻¹, inv_mem hb₂, b₁⁻¹, inv_mem hb₁, by group⟩

private theorem q2nPE_simple_cell_sub_mul_self (i : Fin D.rank) :
    bruhatCell hct ((cs).simple i) ⊆
      bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i) := by
  let S : Set K := bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)
  have hni := q2nPE_n_mem_simple_cell hct i
  have hsqS : n i * n i ∈ S := Set.mul_mem_mul hni hni
  have hbi : ∀ c ∈ (borel D H : Set K), ∀ d ∈ (borel D H : Set K),
      ∀ g ∈ S, c * g * d ∈ S := by
    intro c hc d hd g hg
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Set.mem_mul.1 (show g ∈ bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)
        from hg)
    exact Set.mem_mul.2 ⟨c * x, mul_mem_bruhatCell hct hc hx, y * d,
      mul_mem_bruhatCell_right hct hy hd, by group⟩
  have hsub : S ⊆ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Set.mem_mul.1 (show g ∈ bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)
        from hg)
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hx
    obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := hy
    rw [nrep_simple hct i]
    have h := n_mul_mul_nrep_mem hct hext ((cs).simple i) i (mul_mem hb₂ hb₃)
    rw [nrep_simple hct i, (cs).simple_mul_simple_self i] at h
    rw [Set.union_comm] at h
    rw [show (b₁ * n i * b₂) * (b₃ * n i * b₄)
        = b₁ * (n i * (b₂ * b₃) * n i) * b₄ by group]
    rcases h with h | h
    · exact Or.inl (mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hb₁ h) hb₄)
    · exact Or.inr (mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hb₁ h) hb₄)
  by_contra hcon
  have hDisj : Disjoint (bruhatCell hct ((cs).simple i)) S := by
    rw [Set.disjoint_left]
    intro g hg hgS
    exact hcon fun h hh => by
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hh
      rw [show c₁ * nrep hct ((cs).simple i) * c₂
          = (c₁ * b₁⁻¹) * (b₁ * nrep hct ((cs).simple i) * b₂) * (b₂⁻¹ * c₂) by group]
      exact hbi _ (mul_mem hc₁ (inv_mem hb₁)) _ (mul_mem (inv_mem hb₂) hc₂) _ hgS
  have hBeq : S = (borel D H : Set K) := by
    apply le_antisymm
    · intro g hgS
      rcases hsub hgS with h | h
      · exact bruhatCell_one hct ▸ h
      · exact (Set.disjoint_left.1 hDisj h hgS).elim
    · intro b hb
      show b ∈ bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)
      exact q2nPE_borel_sub_simple_cell_mul_self hct i hb
  have hnx : ∀ x ∈ D.rootGroup (Pi.single i 1), n i * x * n i ∈ (borel D H : Set K) := by
    intro x hx
    have h1 : n i * x ∈ bruhatCell hct ((cs).simple i) :=
      mul_mem_bruhatCell_right hct hni
        (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hx)
    have h2 : (n i * x) * n i ∈ S :=
      Set.mem_mul.2 ⟨n i * x, h1, n i, hni, rfl⟩
    rw [hBeq] at h2
    exact h2
  have hneg : D.rootGroup (-Pi.single i 1) ≤ (borel D H : Set K) := by
    rintro y hy
    have hmap : (D.rootGroup (Pi.single i 1)).map (MulAut.conj (n i)).toMonoidHom =
        D.rootGroup (-Pi.single i 1) := by
      rw [(actsAs_n hct i) _ ((Φ).single_mem i), weylAction_simple_single]
    have hy' : y ∈ (D.rootGroup (Pi.single i 1)).map (MulAut.conj (n i)).toMonoidHom := by
      rwa [hmap]
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy'
    rw [← hxy]
    change n i * x * (n i)⁻¹ ∈ (borel D H : Set K)
    have h3 := hnx x hx
    have e : n i * x * (n i)⁻¹ = (n i * x * n i) * (n i ^ 2)⁻¹ := by group
    rw [e]
    exact mul_mem h3 (inv_mem (iSup_le_borel (sq_n_mem_iSup hct i)))
  have hrank : rankOne D.rootGroup i ≤ (borel D H : Set K) :=
    sup_le (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i)) hneg
  have hniB : n i ∈ (borel D H : Set K) := hrank (hct.n_mem i)
  have h1 : (cs).simple i = 1 :=
    (nrep_mem_borel_iff hct hext).1 (by rw [nrep_simple hct i]; exact hniB)
  exact (cs).simple_ne_one i h1

theorem q2nPE_simple_cell_mul_add {w : W} {i : Fin D.rank} (hw : ¬ (cs).IsLeftDescent w i) :
    bruhatCell hct ((cs).simple i) * bruhatCell hct w = bruhatCell hct ((cs).simple i * w) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hx
    rw [nrep_simple hct i]
    obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := hy
    obtain ⟨b', hb', z, hz, he⟩ := exists_n_mul_mul_nrep hct hext hw (mul_mem hb₂ hb₃)
    refine ⟨b₁ * b', mul_mem hb₁ hb', z * b₄, mul_mem ?_ hb₄, ?_⟩
    · exact rootGroup_le_borel (weylAction_mem_roots D.isFiniteType w⁻¹ ((Φ).single_mem i))
        (ht_weylAction_inv_single_pos hw) hz
    · rw [show (b₁ * n i * b₂) * (b₃ * nrep hct w * b₄)
          = b₁ * (n i * (b₂ * b₃) * nrep hct w) * b₄ by group, he]
      group
  · intro g hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
    rw [nrep_simple_mul hct hw]
    refine Set.mem_mul.2 ⟨b₁ * n i, ?_, nrep hct w * b₂, ?_, ?_⟩
    · exact mul_mem_bruhatCell hct hb₁ (q2nPE_n_mem_simple_cell hct i)
    · exact mul_mem_bruhatCell_right hct (nrep_mem_bruhatCell hct w) hb₂
    · group

theorem q2nPE_simple_cell_mul_sub {w : W} {i : Fin D.rank} (hw : (cs).IsLeftDescent w i) :
    bruhatCell hct ((cs).simple i) * bruhatCell hct w =
      bruhatCell hct ((cs).simple i * w) ∪ bruhatCell hct w := by
  have hw' : ¬ (cs).IsLeftDescent ((cs).simple i * w) i :=
    (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hw
  have hsw : (cs).simple i * ((cs).simple i * w) = w := (cs).simple_mul_simple_cancel_left i
  have hasc : bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i * w) =
      bruhatCell hct w := by
    have h := q2nPE_simple_cell_mul_add hct hext hw'
    rwa [hsw] at h
  have hB := q2nPE_borel_sub_simple_cell_mul_self hct i
  have hS := q2nPE_simple_cell_sub_mul_self hct hext i
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hx
    rw [nrep_simple hct i]
    obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := hy
    have h := n_mul_mul_nrep_mem hct hext w i (mul_mem hb₂ hb₃)
    rw [show (b₁ * n i * b₂) * (b₃ * nrep hct w * b₄)
        = b₁ * (n i * (b₂ * b₃) * nrep hct w) * b₄ by group]
    rcases h with h | h
    · exact Or.inr (mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hb₁ h) hb₄)
    · exact Or.inl (mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hb₁ h) hb₄)
  · intro g hg
    rcases hg with hg | hg
    · have h1 : bruhatCell hct ((cs).simple i * w) ⊆
          bruhatCell hct ((cs).simple i) * bruhatCell hct w := by
        calc bruhatCell hct ((cs).simple i * w)
            = (borel D H : Set K) * bruhatCell hct ((cs).simple i * w) :=
              (q2nPE_borel_mul_cell hct _).symm
          _ ⊆ (bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)) *
                bruhatCell hct ((cs).simple i * w) := Set.mul_subset_mul_right hB
          _ = bruhatCell hct ((cs).simple i) *
                (bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i * w)) := by
              rw [mul_assoc]
          _ = bruhatCell hct ((cs).simple i) * bruhatCell hct w := by rw [hasc]
      exact h1 hg
    · have h1 : bruhatCell hct w ⊆ bruhatCell hct ((cs).simple i) * bruhatCell hct w := by
        calc bruhatCell hct w
            = bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i * w) := hasc.symm
          _ ⊆ (bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i)) *
                bruhatCell hct ((cs).simple i * w) := Set.mul_subset_mul_right hS
          _ = bruhatCell hct ((cs).simple i) *
                (bruhatCell hct ((cs).simple i) * bruhatCell hct ((cs).simple i * w)) := by
              rw [mul_assoc]
          _ = bruhatCell hct ((cs).simple i) * bruhatCell hct w := by rw [hasc]
      exact h1 hg

theorem q2nPE_cell_mul_simple_add {w : W} {i : Fin D.rank}
    (h : (cs).length (w * (cs).simple i) = (cs).length w + 1) :
    bruhatCell hct w * bruhatCell hct ((cs).simple i) = bruhatCell hct (w * (cs).simple i) := by
  have hw' : ¬ (cs).IsLeftDescent w⁻¹ i := by
    rw [(cs).isLeftDescent_inv_iff, (cs).isRightDescent_iff]
    omega
  calc bruhatCell hct w * bruhatCell hct ((cs).simple i)
      = ((bruhatCell hct ((cs).simple i) * bruhatCell hct w⁻¹)⁻¹) := by
        rw [mul_inv_rev, q2nPE_inv_cell hct hext w⁻¹, q2nPE_inv_cell hct hext ((cs).simple i),
          (cs).inv_simple, inv_inv]
    _ = (bruhatCell hct ((cs).simple i * w⁻¹))⁻¹ := by
        rw [q2nPE_simple_cell_mul_add hct hext hw']
    _ = bruhatCell hct (w * (cs).simple i) := by
        rw [q2nPE_inv_cell hct hext ((cs).simple i * w⁻¹), mul_inv_rev, inv_inv, (cs).inv_simple]

theorem q2nPE_cell_mul_simple_sub {w : W} {i : Fin D.rank}
    (h : (cs).length (w * (cs).simple i) + 1 = (cs).length w) :
    bruhatCell hct w * bruhatCell hct ((cs).simple i) =
      bruhatCell hct (w * (cs).simple i) ∪ bruhatCell hct w := by
  have hw' : (cs).IsLeftDescent w⁻¹ i := by
    rw [(cs).isLeftDescent_inv_iff, (cs).isRightDescent_iff]
    omega
  calc bruhatCell hct w * bruhatCell hct ((cs).simple i)
      = ((bruhatCell hct ((cs).simple i) * bruhatCell hct w⁻¹)⁻¹) := by
        rw [mul_inv_rev, q2nPE_inv_cell hct hext w⁻¹, q2nPE_inv_cell hct hext ((cs).simple i),
          (cs).inv_simple, inv_inv]
    _ = (bruhatCell hct ((cs).simple i * w⁻¹) ∪ bruhatCell hct w⁻¹)⁻¹ := by
        rw [q2nPE_simple_cell_mul_sub hct hext hw']
    _ = (bruhatCell hct ((cs).simple i * w⁻¹))⁻¹ ∪ (bruhatCell hct w⁻¹)⁻¹ := by
        rw [Set.union_inv]
    _ = bruhatCell hct (w * (cs).simple i) ∪ bruhatCell hct w := by
        rw [q2nPE_inv_cell hct hext ((cs).simple i * w⁻¹), q2nPE_inv_cell hct hext w⁻¹,
          mul_inv_rev, inv_inv, (cs).inv_simple]

end Helpers

theorem isBruhatPartition_bruhatCell
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    IsBruhatPartition (coxeterMatrix D.isFiniteType).toCoxeterSystem (borel D H)
      (bruhatCell hct) where
  doubleCoset w := ⟨nrep hct w, q2nPE_cell_eq_mul hct w⟩
  partition g := existsUnique_mem_bruhatCell hct hext g
  one := bruhatCell_one hct
  inv w := q2nPE_inv_cell hct hext w
  mul_of_length_add w i h := q2nPE_cell_mul_simple_add hct hext h
  mul_of_length_sub w i h := q2nPE_cell_mul_simple_sub hct hext h

end CFSG.ClassicalInvolution.Phan.PhanE
