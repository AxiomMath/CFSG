module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {P Q : Subgroup G}

omit [Finite G] in
theorem parabolicFacts_normal_subgroupOf (hF : ParabolicFacts P Q) :
    (Q.subgroupOf (perfectCore P)).Normal := by
  refine ⟨fun n hn b => ?_⟩
  have hb : (b : G) ∈ Subgroup.normalizer (Q : Set G) := hF.normalizes (perfectCore_le P b.2)
  exact (Subgroup.mem_normalizer_iff.1 hb n).1 hn

theorem noA5Block_of_perfectCore_le (hF : ParabolicFacts P Q) (hle : perfectCore P ≤ Q) :
    NoA5Block ↥(perfectCore P) :=
  noA5Block_of_isPGroup (hF.pGroup.to_le hle)

theorem noA5Block_of_parabolicFacts_sl2 (hF : ParabolicFacts P Q) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hFn : Nat.card F = 2 ^ n) (g : ↥(perfectCore P) →* SL(2, F))
    (hg : Function.Surjective g) (hker : ∀ x, g x = 1 → (x : G) ∈ Q) :
    NoA5Block ↥(perfectCore P) := by
  rcases hF.levi with hle | ⟨hQB, -⟩
  · exact noA5Block_of_perfectCore_le hF hle
  have hPn : P ≤ Subgroup.normalizer (perfectCore P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hQle : Q ≤ perfectCore P := by
    refine hQB.trans (Subgroup.commutator_le.2 fun q hq b hb => ?_)
    have hqP : q ∈ P := hF.le hq
    have h1 : q * b * q⁻¹ ∈ perfectCore P := (Subgroup.mem_normalizer_iff.1 (hPn hqP) b).1 hb
    have : ⁅q, b⁆ = (q * b * q⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hb)
  have hQab : ∃ x ∈ Q.subgroupOf (perfectCore P), ∃ y ∈ Q.subgroupOf (perfectCore P),
      x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    refine ⟨⟨x, hQle hx⟩, hx, ⟨y, hQle hy⟩, hy, fun h => hxy ?_⟩
    exact congrArg Subtype.val h
  have hQB' : Q.subgroupOf (perfectCore P) ≤ ⁅Q.subgroupOf (perfectCore P), ⊤⁆ := by
    intro x hx
    have h1 : (x : G) ∈ ⁅Q, perfectCore P⁆ := hQB hx
    have h2 : (⁅Q.subgroupOf (perfectCore P), (⊤ : Subgroup ↥(perfectCore P))⁆).map
        (perfectCore P).subtype = ⁅Q, perfectCore P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hQle]
    rw [← h2] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    exact (Subtype.ext hyx : y = x) ▸ hy
  exact noA5Block_of_levi_sl2 hn hFn (parabolicFacts_normal_subgroupOf hF)
    (hF.pGroup.comap_subtype) hQab hQB' g hg fun x hx => Subgroup.mem_subgroupOf.2 (hker x hx)

omit [Finite G] in
theorem noA5Block_of_parabolicFacts_not_three (hF : ParabolicFacts P Q) {T : Type} [Group T]
    [Finite T] (h3 : ¬ 3 ∣ Nat.card T) (g : ↥(perfectCore P) →* T)
    (hker : ∀ x, g x = 1 → (x : G) ∈ Q) : NoA5Block ↥(perfectCore P) :=
  noA5Block_of_levi_not_three (parabolicFacts_normal_subgroupOf hF) (hF.pGroup.comap_subtype) h3 g
    fun x hx => Subgroup.mem_subgroupOf.2 (hker x hx)

end CFSG.Quasithin.H13.CTK
