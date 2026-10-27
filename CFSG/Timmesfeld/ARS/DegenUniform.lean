module

public import CFSG.Timmesfeld.ARS.Sec8HypDegen

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem mul_self_ne_one_of_opposite [Finite G] (hR : IsRootClass R) {D₁ D₂ : Subgroup G}
    (hD₂ : D₂ ∈ R) (hop : Opposite D₂ D₁) {d₁ d₂ : G} (hd₁ : d₁ ∈ D₁) (hd₁1 : d₁ ≠ 1)
    (hd₂ : d₂ ∈ D₂) (hd₂1 : d₂ ≠ 1) : d₂ * d₁ * (d₂ * d₁) ≠ 1 := by
  intro h
  have hodd : Odd (orderOf (d₂ * d₁)) :=
    hop.odd_orderOf_mul (hR.mul_self D₂ hD₂) hd₂ hd₂1 hd₁ hd₁1
  have hdvd : orderOf (d₂ * d₁) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h1 : orderOf (d₂ * d₁) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd; exact absurd hodd (Nat.not_odd_iff_even.2 even_two)
  have he : d₂ = d₁⁻¹ := eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.1 h1)
  have hmem : d₂ ∈ D₂ ⊓ D₁ := Subgroup.mem_inf.2 ⟨hd₂, by rw [he]; exact D₁.inv_mem hd₁⟩
  rw [hop.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact hd₂1 hmem

namespace Degen

variable {Δ : Set (Subgroup G)}

theorem gen_cl_le_stabSet_of_commuting {C D : Subgroup G} (hC : C ∈ Δ) (hCD : Commuting C D) :
    gen (cl Δ C) ≤ stabSet (cl Δ D) := by
  intro y hy
  have hc : ∀ D' ∈ cl Δ D, conjSub D' y = D' := by
    intro D' hD'
    have hCD' : Commuting C D' := ((hD'.2 C hC).1 hCD.symm).symm
    have hle : gen (cl Δ C) ≤ Subgroup.centralizer (D' : Set G) :=
      gen_le fun Y hY => commuting_iff_le_centralizer.1 (((hY.2 D' hD'.1).1 hCD').symm)
    exact conjSub_of_forall_commute fun d hd =>
      ((Subgroup.mem_centralizer_iff.1 (hle hy)) d hd).symm
  refine Set.Subset.antisymm ?_ fun D' hD' => ⟨D', hD', hc D' hD'⟩
  rintro _ ⟨D', hD', rfl⟩
  show conjSub D' y ∈ cl Δ D
  rw [hc D' hD']
  exact hD'

section Basic
variable (hR : IsRootClass R) (hΔR : Δ ⊆ R)
include hR hΔR

theorem inf_gen_cl_le_normCl (E F : Subgroup G) :
    gen (cl Δ E) ⊓ gen (cl Δ F) ≤ normCl Δ E F :=
  inf_le_inf_left _ (gen_cl_le_stabSet hR hΔR F)
end Basic

section Center
variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hΔR : Δ ⊆ R)
  (hΔconj : ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ) (hdeg : ∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y)
include hR hΔR hΔconj hdeg

include hiso in
theorem mem_inf_of_commute_of_mem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {m a : G} (hm : m ∈ normCl Δ F E) (ha : a ∈ E) (ha1 : a ≠ 1)
    (hc : Commute m a) : m ∈ gen (cl Δ E) ⊓ gen (cl Δ F) := by
  have hER : E ∈ R := hΔR hE
  have hmF : m ∈ gen (cl Δ F) := (Subgroup.mem_inf.1 hm).1
  have hEm : conjSub E m = E := by
    by_contra hne
    have hmem : a ∈ E ⊓ conjSub E m := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [mem_conjSub, mul_assoc, ← hc.eq, inv_mul_cancel_left]
      exact ha
    rw [inf_eq_bot hR hiso hER (hR.conjSub_mem hER m) (Ne.symm hne), Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hcE : ∀ a' ∈ E, Commute m a' := by
    intro a' ha'
    have h1 : ⁅m, a'⁆ ∈ E := by
      rw [commutatorElement_def]
      refine E.mul_mem ?_ (E.inv_mem ha')
      rw [← hEm]
      exact conj_mem_conjSub m ha'
    have h2 := commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm ha'
    exact commutatorElement_eq_one_iff_mul_comm.1
      (eq_one_of_mem_normCl hR hΔR hΔconj hdeg hE hF hEF h1 h2)
  exact Subgroup.mem_inf.2
    ⟨mem_gen_cl_of_forall_commute hR hΔR hΔconj hdeg hE hF hEF hmF hcE, hmF⟩

theorem commutatorElement_eq_one_of_mem_inf {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {m a : G} (hm : m ∈ normCl Δ F E) (ha : a ∈ E) (ha1 : a ≠ 1)
    (hz : ⁅m, a⁆ ∈ gen (cl Δ E) ⊓ gen (cl Δ F)) : ⁅m, a⁆ = 1 := by
  have hmN := commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm ha
  by_cases hEm : conjSub E m = E
  · refine eq_one_of_mem_normCl hR hΔR hΔconj hdeg hE hF hEF ?_ hmN
    rw [commutatorElement_def]
    refine E.mul_mem ?_ (E.inv_mem ha)
    rw [← hEm]
    exact conj_mem_conjSub m ha
  exfalso
  obtain ⟨hmF, hmE⟩ := Subgroup.mem_inf.1 hm
  have hE' : conjSub E m ∈ cl Δ E :=
    ⟨hΔconj E hE m (gen_cl_le F hmF), equiv_of_mem_stabSet_cl hE hmE⟩
  have hEF' : Opposite E F := opposite_of_not_commuting hR hΔR hdeg hE hF hEF
  have hE'F : Opposite (conjSub E m) F := opposite_of_mem_cl hR hΔR hdeg hE' hF hEF
  have hb : m * a * m⁻¹ ∈ conjSub E m := conj_mem_conjSub m ha
  have hb1 : m * a * m⁻¹ ≠ 1 := fun h => ha1 (conj_eq_one_iff.1 h)
  have hza : Commute ⁅m, a⁆ a :=
    commute_of_mem_gen_cl hR hΔR (mem_cl_self hE) (Subgroup.mem_inf.1 hz).1 ha
  have hFz : conjSub F ⁅m, a⁆ = F :=
    conjSub_eq_of_mem_gen_cl hR hΔR (mem_cl_self hF) (Subgroup.mem_inf.1 hz).2
  have e : m * a * m⁻¹ = a * ⁅m, a⁆ := by
    rw [← hza.eq, commutatorElement_def, inv_mul_cancel_right]
  have hFb : conjSub F (m * a * m⁻¹) = conjSub F a := by rw [e, conjSub_mul, hFz]
  obtain ⟨c, hc, -, hEc⟩ := hEF'.2.1 a ha ha1
  obtain ⟨c₂, hc₂, -, hEc₂⟩ := hE'F.2.1 _ hb hb1
  have hEeq : conjSub (conjSub E m) (c⁻¹ * c₂) = E := by
    rw [conjSub_mul, hEc₂, hFb, ← hEc, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  by_cases hcc : c⁻¹ * c₂ = 1
  · rw [hcc, conjSub_one] at hEeq; exact hEm hEeq
  have hop := opposite_conjSub_of_opposite hR (hΔR hF) (hΔR hE'.1) hE'F.symm
    (F.mul_mem (F.inv_mem hc) hc₂) hcc
  rw [hEeq] at hop
  exact hop.not_commuting (hR.ne_bot _ (hΔR hE'.1))
    (commuting_of_mem_cl hR hΔR hE' (mem_cl_self hE))

include hiso in
theorem inv_mul_mem_inf_iff {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) {m m' : G}
    (hm : m ∈ normCl Δ F E) (hm' : m' ∈ normCl Δ F E) :
    m⁻¹ * m' ∈ gen (cl Δ E) ⊓ gen (cl Δ F) ↔
      ⁅m, a⁆⁻¹ * ⁅m', a⁆ ∈ gen (cl Δ E) ⊓ gen (cl Δ F) := by
  constructor
  · intro hn
    have hc : Commute (m⁻¹ * m') a :=
      commute_of_mem_gen_cl hR hΔR (mem_cl_self hE) (Subgroup.mem_inf.1 hn).1 ha
    have e : ⁅m', a⁆ = ⁅m, a⁆ := by
      have h1 : m' * a = m * a * m⁻¹ * m' := by
        calc m' * a = m * (m⁻¹ * m' * a) := by group
          _ = m * (a * (m⁻¹ * m')) := by rw [hc.eq]
          _ = m * a * m⁻¹ * m' := by group
      simp only [commutatorElement_def]
      rw [h1]
      group
    rw [e, inv_mul_cancel]
    exact one_mem _
  · intro hw
    have hn : m⁻¹ * m' ∈ normCl Δ F E := mul_mem (inv_mem hm) hm'
    have hcm : ⁅m, a⁆ ∈ gen (cl Δ E) :=
      (Subgroup.mem_inf.1 (commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm ha)).1
    have hcm' : ⁅m', a⁆ ∈ gen (cl Δ E) :=
      (Subgroup.mem_inf.1 (commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm' ha)).1
    have hab : ⁅m', a⁆ * ⁅m, a⁆⁻¹ = ⁅m, a⁆⁻¹ * ⁅m', a⁆ :=
      (commuting_gen_cl hR hΔR E _ hcm' _ (inv_mem hcm)).eq
    have hmw : Commute m (⁅m, a⁆⁻¹ * ⁅m', a⁆) :=
      commuting_gen_cl hR hΔR F m (Subgroup.mem_inf.1 hm).1 _ (Subgroup.mem_inf.1 hw).2
    have e : ⁅m⁻¹ * m', a⁆ = ⁅m, a⁆⁻¹ * ⁅m', a⁆ := by
      have hc1 : ⁅m⁻¹ * m', a⁆ = m⁻¹ * (⁅m', a⁆ * ⁅m, a⁆⁻¹) * m := by
        simp only [commutatorElement_def]; group
      rw [hc1, hab, mul_assoc, ← hmw.eq, inv_mul_cancel_left]
    have h1 := commutatorElement_eq_one_of_mem_inf hR hΔR hΔconj hdeg hE hF hEF hn ha ha1
      (by rw [e]; exact hw)
    exact mem_inf_of_commute_of_mem_normCl hR hiso hΔR hΔconj hdeg hE hF hEF hn ha ha1
      (commutatorElement_eq_one_iff_mul_comm.1 h1)

include hiso in
private theorem exists_injective_quot {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) :
    ∃ ψ : ↥(normCl Δ F E) ⧸ (gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf (normCl Δ F E) →
        ↥(normCl Δ E F) ⧸ (gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf (normCl Δ E F),
      Function.Injective ψ ∧ ∀ q, ∃ m ∈ normCl Δ F E, ∃ n : ↥(normCl Δ E F),
        (n : G) = ⁅m, a⁆ ∧ ψ q = QuotientGroup.mk n := by
  let c : ↥(normCl Δ F E) → ↥(normCl Δ E F) := fun m =>
    ⟨⁅(m : G), a⁆, commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF m.2 ha⟩
  refine ⟨fun q => QuotientGroup.mk (c q.out), ?_, fun q => ⟨q.out, q.out.2, c q.out, rfl, rfl⟩⟩
  intro q q' h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have h' := QuotientGroup.eq.1 h
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h'
  exact (inv_mul_mem_inf_iff hR hiso hΔR hΔconj hdeg hE hF hEF ha ha1 q.out.2 q'.out.2).2 h'

include hiso in
theorem natCard_normCl_le {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) : Nat.card (normCl Δ F E) ≤ Nat.card (normCl Δ E F) := by
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hΔR hE)
  obtain ⟨ψ, hψ, -⟩ := exists_injective_quot hR hiso hΔR hΔconj hdeg hE hF hEF ha ha1
  have hZ₁ : gen (cl Δ E) ⊓ gen (cl Δ F) ≤ normCl Δ F E := by
    rw [inf_comm]; exact inf_gen_cl_le_normCl hR hΔR F E
  have hZ₂ : gen (cl Δ E) ⊓ gen (cl Δ F) ≤ normCl Δ E F := inf_gen_cl_le_normCl hR hΔR E F
  rw [((gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf
      (normCl Δ F E)).card_eq_card_quotient_mul_card_subgroup,
    ((gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf
      (normCl Δ E F)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₁).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₂).toEquiv]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective ψ hψ)

include hiso in
theorem exists_commutatorElement_mul_eq {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) {n : G}
    (hn : n ∈ normCl Δ E F) :
    ∃ m ∈ normCl Δ F E, ∃ z ∈ gen (cl Δ E) ⊓ gen (cl Δ F), n = ⁅m, a⁆ * z := by
  obtain ⟨ψ, hψ, hψm⟩ := exists_injective_quot hR hiso hΔR hΔconj hdeg hE hF hEF ha ha1
  have hZ₁ : gen (cl Δ E) ⊓ gen (cl Δ F) ≤ normCl Δ F E := by
    rw [inf_comm]; exact inf_gen_cl_le_normCl hR hΔR F E
  have hZ₂ : gen (cl Δ E) ⊓ gen (cl Δ F) ≤ normCl Δ E F := inf_gen_cl_le_normCl hR hΔR E F
  have hle := natCard_normCl_le hR hiso hΔR hΔconj hdeg hF hE (fun h => hEF h.symm)
  rw [((gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf
      (normCl Δ F E)).card_eq_card_quotient_mul_card_subgroup,
    ((gen (cl Δ E) ⊓ gen (cl Δ F)).subgroupOf
      (normCl Δ E F)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₁).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₂).toEquiv] at hle
  have hpos : 0 < Nat.card ↥(gen (cl Δ E) ⊓ gen (cl Δ F)) := Nat.card_pos
  have hbij := hψ.bijective_of_nat_card_le (Nat.le_of_mul_le_mul_right hle hpos)
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk (⟨n, hn⟩ : ↥(normCl Δ E F)))
  obtain ⟨m, hm, n', hn', hψq⟩ := hψm q
  rw [hψq, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    hn'] at hq
  exact ⟨m, hm, ⁅m, a⁆⁻¹ * n, hq, by group⟩

include hiso in
theorem exists_mul_eq_of_notMem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {x : G} (hx : x ∈ gen (cl Δ E)) (hxN : x ∉ normCl Δ E F) :
    ∃ D ∈ cl Δ E, ∃ d ∈ D, d ≠ 1 ∧ ∃ z ∈ gen (cl Δ E) ⊓ gen (cl Δ F), x = d * z := by
  obtain ⟨a, ha, hxa⟩ := exists_mul_mem_normCl_of_mem_gen hR hΔR hΔconj hdeg hE hF hEF hx
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxa
    exact hxN hxa
  obtain ⟨m, hm, z, hz, hxz⟩ :=
    exists_commutatorElement_mul_eq hR hiso hΔR hΔconj hdeg hE hF hEF ha ha1 hxa
  have hmΔ : m ∈ gen Δ := gen_cl_le F (Subgroup.mem_inf.1 hm).1
  have hza : Commute z a :=
    commute_of_mem_gen_cl hR hΔR (mem_cl_self hE) (Subgroup.mem_inf.1 hz).1 ha
  have haa : a * a = 1 := hR.mul_self E (hΔR hE) a ha
  refine ⟨conjSub E m, ⟨hΔconj E hE m hmΔ, equiv_of_mem_stabSet_cl hE (Subgroup.mem_inf.1 hm).2⟩,
    m * a * m⁻¹, conj_mem_conjSub m ha, fun h => ha1 (conj_eq_one_iff.1 h), z, hz, ?_⟩
  calc x = x * a * a := by rw [mul_assoc, haa, mul_one]
    _ = ⁅m, a⁆ * z * a := by rw [hxz]
    _ = m * a * m⁻¹ * (a⁻¹ * (z * a)) := by rw [commutatorElement_def]; group
    _ = m * a * m⁻¹ * z := by rw [hza.eq, inv_mul_cancel_left]

include hiso in
theorem inf_gen_cl_le_normCl_of_not_commuting {E C F : Subgroup G} (hE : E ∈ Δ) (hC : C ∈ Δ)
    (hF : F ∈ Δ) (hEC : ¬ Commuting E C) (hEF : ¬ Commuting E F) :
    gen (cl Δ E) ⊓ gen (cl Δ C) ≤ normCl Δ E F := by
  intro z hz
  obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
  by_cases hCF : Commuting C F
  · exact Subgroup.mem_inf.2 ⟨hzE, gen_cl_le_stabSet_of_commuting hC hCF hzC⟩
  by_contra hzN
  have hzN' : z ∉ normCl Δ C F :=
    fun h => hzN (Subgroup.mem_inf.2 ⟨hzE, (Subgroup.mem_inf.1 h).2⟩)
  obtain ⟨D₁, hD₁, d₁, hd₁, hd₁1, z₁, hz₁, e₁⟩ :=
    exists_mul_eq_of_notMem_normCl hR hiso hΔR hΔconj hdeg hE hF hEF hzE hzN
  obtain ⟨D₂, hD₂, d₂, hd₂, hd₂1, z₂, hz₂, e₂⟩ :=
    exists_mul_eq_of_notMem_normCl hR hiso hΔR hΔconj hdeg hC hF hCF hzC hzN'
  have h₁ : d₁ = z * z₁⁻¹ := by rw [e₁, mul_inv_cancel_right]
  have h₂ : d₂ = z₂ * z⁻¹ := by
    rw [← hR.inv_eq (hΔR hD₂.1) hd₂, e₂]; group
  have hmem : d₂ * d₁ ∈ gen (cl Δ F) := by
    have e : d₂ * d₁ = z₂ * z₁⁻¹ := by rw [h₁, h₂]; group
    rw [e]
    exact mul_mem (Subgroup.mem_inf.1 hz₂).2 (inv_mem (Subgroup.mem_inf.1 hz₁).2)
  have hsq := mul_self_of_mem_gen_cl hR hΔR hmem
  have hop : Opposite D₂ D₁ := opposite_of_mem_cl hR hΔR hdeg hD₂ hD₁.1
    (fun hCD₁ => hEC ((hD₁.2 C hC).2 hCD₁.symm))
  exact mul_self_ne_one_of_opposite hR (hΔR hD₂.1) hop hd₁ hd₁1 hd₂ hd₂1 hsq

include hiso in
theorem normCl_le_normCl {E F C : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ) (hC : C ∈ Δ)
    (hEF : ¬ Commuting E F) (hEC : ¬ Commuting E C) : normCl Δ E F ≤ normCl Δ E C := by
  intro x hx
  by_contra hxN
  obtain ⟨D, hD, d, hd, hd1, z, hz, rfl⟩ :=
    exists_mul_eq_of_notMem_normCl hR hiso hΔR hΔconj hdeg hE hC hEC (Subgroup.mem_inf.1 hx).1 hxN
  have hzN : z ∈ normCl Δ E F :=
    inf_gen_cl_le_normCl_of_not_commuting hR hiso hΔR hΔconj hdeg hE hC hF hEC hEF hz
  have hdN : d ∈ normCl Δ E F := by
    have := mul_mem hx (inv_mem hzN)
    rwa [mul_inv_cancel_right] at this
  have hcl : cl Δ D = cl Δ E := cl_eq_of_equiv fun C' hC' => (hD.2 C' hC').symm
  have hDF : ¬ Commuting D F := fun h => hEF ((hD.2 F hF).2 h)
  have hdN' : d ∈ normCl Δ D F := by unfold normCl; rw [hcl]; exact hdN
  exact hd1 (eq_one_of_mem_normCl hR hΔR hΔconj hdeg hD.1 hF hDF hd hdN')

end Center
end Degen
end CFSG.Timmesfeld.ARS
