module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyPreserve
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyNoOutsider
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyOuter
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomySylow
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.forall_isConj_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = 1)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) :
    ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  obtain ⟨P, hPC⟩ := h.exists_sylow_le_of_outer_outer hi₁ hi₂ hn hnK hn2 hact
  have key : ∀ a : G, orderOf a = 2 → IsConj a t := by
    intro a ha
    have hzpow : IsPGroup 2 (Subgroup.zpowers a) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, ha]
      norm_num
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hzpow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
    have hgset : (MulAut.conj g : G ≃* G) • (Q : Set G) = (P : Set G) := by
      have h' := congrArg (fun S : Sylow 2 G => (S : Set G)) hg
      rwa [Sylow.coe_smul] at h'
    have haQ : a ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers a)
    have hbP : g * a * g⁻¹ ∈ (P : Subgroup G) := by
      have hmem : g * a * g⁻¹ ∈ (MulAut.conj g : G ≃* G) • (Q : Set G) :=
        Set.mem_smul_set.mpr ⟨a, haQ, by simp [MulAut.conj_apply]⟩
      rwa [hgset] at hmem
    have hbC : g * a * g⁻¹ ∈ centralizer ({t} : Set G) := hPC hbP
    have hb2 : orderOf (g * a * g⁻¹) = 2 := by
      have h1 : orderOf (g * a * g⁻¹) = orderOf a :=
        (SemiconjBy.orderOf_eq g (show SemiconjBy g a (g * a * g⁻¹) by
          unfold SemiconjBy; group)).symm
      rw [h1, ha]
    have hbsq : (g * a * g⁻¹) ^ 2 = 1 := by
      have hpow := pow_orderOf_eq_one (g * a * g⁻¹)
      rwa [hb2] at hpow
    have hconj : IsConj a (g * a * g⁻¹) := by
      rw [isConj_iff]
      exact ⟨g, rfl⟩
    have hbt : IsConj (g * a * g⁻¹) t := by
      by_cases hbK : g * a * g⁻¹ ∈ i₁.range ⊔ i₂.range
      · by_cases hb_eq : g * a * g⁻¹ = t
        · refine ⟨1, ?_⟩
          simpa [SemiconjBy] using hb_eq
        · obtain ⟨k, _, hk⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hbK hb2 hb_eq
          exact ((isConj_iff).mpr ⟨k, hk⟩).symm.trans
            ((h.isConj_x_of_outer_outer hi₁ hi₂ hn hnK hn2 hact).symm)
      · exact (IsConj.symm
            (h.isConj_n_of_outer_outer hi₁ hi₂ hn hnK hn2 hact hbC hbK hbsq)).trans
          (IsConj.symm (h.isConj_t_n_of_outer_outer hi₁ hi₂ hn hnK hn2 hact))
    exact hconj.trans hbt
  intro a b ha hb
  exact (key a ha).trans (key b hb).symm

theorem WongHyp.map_conj_eq_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    {n : G} (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) :
    ∀ c ∈ centralizer ({t} : Set G), i₁.range.map (MulAut.conj c).toMonoidHom = i₁.range ∧
      i₂.range.map (MulAut.conj c).toMonoidHom = i₂.range := by
  have hnN₁ : n ∈ normalizer (i₁.range : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨deltaAut x, (hact x).1.symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨deltaAut.symm x, ?_⟩
      have h1 : n⁻¹ * i₁ (deltaAut.symm x) * n = i₁ x := by
        have hh := (hact (deltaAut.symm x)).1
        rwa [MulEquiv.apply_symm_apply] at hh
      have h2 : n⁻¹ * i₁ (deltaAut.symm x) * n = n⁻¹ * y * n := by rw [h1, hx]
      exact mul_left_cancel (mul_right_cancel h2)
  have hnN₂ : n ∈ normalizer (i₂.range : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨deltaAut x, (hact x).2.symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨deltaAut.symm x, ?_⟩
      have h1 : n⁻¹ * i₂ (deltaAut.symm x) * n = i₂ x := by
        have hh := (hact (deltaAut.symm x)).2
        rwa [MulEquiv.apply_symm_apply] at hh
      have h2 : n⁻¹ * i₂ (deltaAut.symm x) * n = n⁻¹ * y * n := by rw [h1, hx]
      exact mul_left_cancel (mul_right_cancel h2)
  have hKN₁ : i₁.range ⊔ i₂.range ≤ normalizer (i₁.range : Set G) := by
    refine sup_le le_normalizer ?_
    have hcent : i₂.range ≤ centralizer (i₁.range : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (h.commute a ha b hb).eq
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hKN₂ : i₁.range ⊔ i₂.range ≤ normalizer (i₂.range : Set G) := by
    refine sup_le ?_ le_normalizer
    have hcent : i₁.range ≤ centralizer (i₂.range : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (h.commute a ha b hb).symm.eq
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hC₁ : centralizer ({t} : Set G) ≤ normalizer (i₁.range : Set G) := by
    rw [← h.sup_zpowers_eq_centralizer hn hnK]
    exact sup_le hKN₁ (Subgroup.zpowers_le.mpr hnN₁)
  have hC₂ : centralizer ({t} : Set G) ≤ normalizer (i₂.range : Set G) := by
    rw [← h.sup_zpowers_eq_centralizer hn hnK]
    exact sup_le hKN₂ (Subgroup.zpowers_le.mpr hnN₂)
  intro c hc
  refine ⟨?_, ?_⟩
  · simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC₁ hc)
  · simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC₂ hc)

theorem WongHyp.local_dichotomy [Finite G] {L₁ L₂ : Subgroup G} (h : WongHyp t L₁ L₂) :
    ((∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
      ∀ x ∈ centralizer ({t} : Set G),
        L₁.map (MulAut.conj x).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj x).toMonoidHom = L₂) ∨
    ∃ u : G, orderOf u = 2 ∧ u ∉ L₁ ⊔ L₂ ∧ L₁ ⊔ L₂ ⊔ zpowers u = centralizer ({t} : Set G) ∧
      L₁.map (MulAut.conj u).toMonoidHom = L₂ := by
  obtain ⟨i₁, i₂, n, hi₁, hi₂, hlab, hnC, hnK, hsup, hn2, hact⟩ := h.exists_normalForm
  have h' : WongHyp t i₁.range i₂.range := by
    rcases hlab with ⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩
    · rwa [hr₁, hr₂]
    · rw [hr₁, hr₂]; exact h.symm
  have hnK' : n ∉ i₁.range ⊔ i₂.range := by
    rcases hlab with ⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩
    · rwa [hr₁, hr₂]
    · rw [hr₁, hr₂]
      rw [sup_comm L₂ L₁]
      exact hnK
  have hsup' : i₁.range ⊔ i₂.range ⊔ zpowers n = centralizer ({t} : Set G) := by
    rcases hlab with ⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩
    · rwa [hr₁, hr₂]
    · rw [hr₁, hr₂]
      rw [sup_comm L₂ L₁]
      exact hsup
  have key : ((∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
      ∀ c ∈ centralizer ({t} : Set G),
        i₁.range.map (MulAut.conj c).toMonoidHom = i₁.range ∧
        i₂.range.map (MulAut.conj c).toMonoidHom = i₂.range) ∨
      ∃ u : G, orderOf u = 2 ∧ u ∉ i₁.range ⊔ i₂.range ∧
        i₁.range ⊔ i₂.range ⊔ zpowers u = centralizer ({t} : Set G) ∧
        i₁.range.map (MulAut.conj u).toMonoidHom = i₂.range := by
    rcases hact with hact | hact | hact | hact
    · exact (h'.false_of_trivial hi₁ hi₂ hnC hnK' hn2 hact).elim
    · exact (h'.false_of_outer_one hi₁ hi₂ hnC hnK' hn2 hact).elim
    · rcases hn2 with hn2 | hn2
      · exact Or.inl ⟨h'.forall_isConj_of_outer_outer hi₁ hi₂ hnC hnK' hn2 hact,
          h'.map_conj_eq_of_outer_outer hnC hnK' hact⟩
      · exact (h'.false_of_forall_sq_ne_one hi₁ hi₂ fun v hvC hvK =>
          h'.sq_ne_one_of_outer_outer hi₁ hi₂ hnC hnK' hn2 hact hvC hvK).elim
    · rcases hn2 with hn2 | hn2
      · refine Or.inr ⟨n, ?_, hnK', hsup', ?_⟩
        · have hn1 : n ≠ 1 := fun h1 => hnK' (by rw [h1]; exact Subgroup.one_mem _)
          exact orderOf_eq_prime hn2 hn1
        · have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hn2)
          apply le_antisymm
          · rintro y ⟨a, ha, rfl⟩
            obtain ⟨x, rfl⟩ := ha
            exact ⟨x, by
              change i₂ x = n * i₁ x * n⁻¹
              simpa [hninv] using (hact x).1.symm⟩
          · rintro y ⟨x, rfl⟩
            exact ⟨i₁ x, ⟨x, rfl⟩, by
              change n * i₁ x * n⁻¹ = i₂ x
              simpa [hninv] using (hact x).1⟩
      · exact (h'.false_of_forall_sq_ne_one hi₁ hi₂ fun v hvC hvK =>
          h'.sq_ne_one_of_swap hi₁ hi₂ hnC hnK' hn2 hact hvC hvK).elim
  rcases hlab with ⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩
  · simpa only [hr₁, hr₂] using key
  · rw [hr₁, hr₂] at key
    rcases key with ⟨hp, hc⟩ | ⟨u, hu2, huK, hsupu, humap⟩
    · exact Or.inl ⟨hp, fun c hc' => ⟨(hc c hc').2, (hc c hc').1⟩⟩
    · refine Or.inr ⟨u, hu2, ?_, ?_, ?_⟩
      · rwa [sup_comm L₂ L₁] at huK
      · rwa [sup_comm L₂ L₁] at hsupu
      · have husq : u * u = 1 := by
          have hpow := pow_orderOf_eq_one u
          rw [hu2] at hpow
          rwa [pow_two] at hpow
        have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
            MonoidHom.id G := by
          ext x
          change (MulAut.conj u) ((MulAut.conj u) x) = x
          rw [MulAut.conj_apply, MulAut.conj_apply,
            show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group, husq, one_mul,
            inv_one, mul_one]
        have hmap2 : (L₂.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u).toMonoidHom =
            L₁.map (MulAut.conj u).toMonoidHom := by rw [humap]
        rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap2
        exact hmap2.symm

end CFSG.OddTranspositions.PartThree.Wong
