module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenHomocyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusGenR_of_forall_torusIrred {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (h : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      (∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) →
      (∀ x ∈ Subgroup.centralizer (E : Set R), ∀ y ∈ Subgroup.centralizer (E : Set R),
          (∃ k : ℕ, x ^ p ^ k = 1) → (∃ k : ℕ, y ^ p ^ k = 1) → x * y = y * x) ∧
      (∀ Q : Subgroup R, Q ≤ E →
        Subgroup.normalizer (E : Set R) ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = E) ∧
      ∃ e : ℕ, (∀ y ∈ Subgroup.centralizer (E : Set R), (∃ k : ℕ, y ^ p ^ k = 1) →
          y ^ p ^ e = 1) ∧
        ∀ x ∈ E, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
          ∃ s ∈ J, s ∈ Subgroup.centralizer (E : Set R) ∧ orderOf s = p ^ e) :
    GGTorusGenR p r R := by
  have : Fact p.Prime := ⟨hp⟩
  intro E hE hr hmax x hx hx1 J hJ c hc hcp
  obtain ⟨hcomm, hirr, e, hexp, hcomp⟩ := h E hE hr hmax
  obtain ⟨s, hsJ, hsC, hsord⟩ := hcomp x hx hx1 J hJ
  have hP : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by have := Nat.one_le_pow r p hp.pos; omega)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  let P : Set R := {y | y ∈ Subgroup.centralizer (E : Set R) ∧ ∃ k : ℕ, y ^ p ^ k = 1}
  have hTC : Subgroup.closure P ≤ Subgroup.centralizer (E : Set R) :=
    (Subgroup.closure_le _).mpr fun y hy => hy.1
  have : IsMulCommutative (Subgroup.closure P) := by
    refine Subgroup.isMulCommutative_closure ?_
    intro y hy z hz _
    exact hcomm y hy.1 z hz.1 hy.2 hz.2
  have hconjP : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ z ∈ P, g * z * g⁻¹ ∈ P := by
    rintro g hg z ⟨hzC, k, hzk⟩
    refine ⟨?_, k, by rw [conj_pow, hzk, mul_one, mul_inv_cancel]⟩
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro a ha
    have hga : g⁻¹ * a * g ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) a).mp ha
    calc a * (g * z * g⁻¹) = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by rw [hzC _ hga]
      _ = g * z * g⁻¹ * a := by group
  have hNT : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ y ∈ Subgroup.closure P,
      g * y * g⁻¹ ∈ Subgroup.closure P := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact Subgroup.subset_closure (hconjP g hg z hz)
    | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  have hsT : s ∈ Subgroup.closure P :=
    Subgroup.subset_closure ⟨hsC, e, by rw [← hsord]; exact pow_orderOf_eq_one s⟩
  have hSp : IsPGroup p (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hsord])
  refine ⟨Subgroup.zpowers s, Subgroup.normalizer (E : Set R), hSp,
    (Subgroup.zpowers_le).mpr hsC, (Subgroup.zpowers_le).mpr hsJ, subset_rfl, ?_⟩
  exact mem_closure_conj_of_torusIrred_of_conj (n := n) (A := E) (T := Subgroup.closure P)
    (N := Subgroup.normalizer (E : Set R))
    (fun y hy z hz => Subgroup.mul_comm_of_mem_isMulCommutative _ hy hz) hNT
    (fun y hy hyp => hmax y (fun z hz => (Subgroup.mem_centralizer_iff.mp (hTC hy) z hz).symm) hyp)
    hirr hn (fun y hy hk => hexp y (hTC hy) hk) ((Subgroup.zpowers_le).mpr hsT)
    ⟨s, Subgroup.mem_zpowers s, hsord⟩ c (Subgroup.subset_closure ⟨hc, hcp⟩) hcp

end CFSG.StandardType
