module

public import CFSG.Quasithin.EmptyFaithful.SBc17Out
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace SBc17

@[expose] def Out5Inner (Γ : Type*) [Group Γ] : Prop :=
  ∀ φ : MulAut Γ, φ ^ 5 = 1 → ∃ g : Γ, ∀ x, φ x = g * x * g⁻¹

theorem Out5Inner.of_mulEquiv {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (h : Out5Inner Γ) : Out5Inner Γ' := by
  intro φ hφ
  have h1 : ((MulAut.congr e).symm φ) ^ 5 = 1 := by
    rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ := h _ h1
  refine ⟨e g, fun y => ?_⟩
  have h2 : e.symm (φ y) = g * e.symm y * g⁻¹ := by
    have h2 := hg (e.symm y)
    rwa [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      e.apply_symm_apply] at h2
  have h3 : φ y = e (g * e.symm y * g⁻¹) := by
    rw [← h2, e.apply_symm_apply]
  rw [h3, map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem out5Inner_of_card_outer_le_four {Γ : Type*} [Group Γ] [Finite Γ]
    (h : Nat.card (Outer Γ) ≤ 4) : Out5Inner Γ := by
  intro φ hφ
  have : Finite (MulAut Γ) := inferInstance
  have : Finite (Outer Γ) := inferInstance
  set q := QuotientGroup.mk' (inner Γ) φ with hq
  have hqp : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [hq, ← map_pow, hφ, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans h
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hqp with h1 | h1
    · exact h1
    · omega
  have hq2 : q = 1 := orderOf_eq_one_iff.mp hq1
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).mp hq2
  exact ⟨g, fun x => by rw [← hg]; rfl⟩

theorem out5Inner_of_card_mulAut_le {Γ : Type*} [Group Γ] [Finite Γ]
    (hZ : Subgroup.center Γ = ⊥) (hA : Nat.card (MulAut Γ) ≤ 4 * Nat.card Γ) : Out5Inner Γ := by
  apply out5Inner_of_card_outer_le_four
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center Γ := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut Γ => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner Γ) = Nat.card Γ :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx := (inner Γ).index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card Γ := Nat.card_pos
  have h1 : (inner Γ).index * Nat.card Γ ≤ 4 * Nat.card Γ := hidx ▸ hA
  have h2 : (inner Γ).index ≤ 4 := Nat.le_of_mul_le_mul_right h1 hpos
  exact h2

theorem out5Inner_alternating {n : ℕ} (hn : 5 ≤ n) : Out5Inner (alternatingGroup (Fin n)) := by
  apply out5Inner_of_card_outer_le_four
  by_cases h6 : n = 6
  · subst h6
    exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
  · have h : n = 5 ∨ 7 ≤ n := by omega
    exact (Nat.le_of_dvd (by norm_num)
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup h).2).trans (by norm_num)

section Block

variable {G : Type} [Group G]

theorem mem_innerSub_of_exists_conj {L : Subgroup G} {S : Type*} [Group S] {α : ↥L →* S}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G))
    (h : ∃ g : S, ∀ x : ↥L, α (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ x) = g * α x * g⁻¹) :
    k ∈ innerSub L := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨ℓ, hℓ⟩ := hα g
  have hcM : (ℓ : G)⁻¹ * k ∈ cMod L := by
    refine mem_cMod.mpr ⟨mul_mem (inv_mem (Subgroup.le_normalizer ℓ.2)) hk, fun x hx => ?_⟩
    have hY : α (⟨x, hx⟩ * ℓ⁻¹ * (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩)⁻¹ * ℓ) = 1 := by
      have h1 : α (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩) = g * α ⟨x, hx⟩ * g⁻¹ :=
        hg ⟨x, hx⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hℓ, h1]
      group
    have h2 := (map_eq_one_iff_mem_pCoreOf hker _).mp hY
    have e : ⁅x, (ℓ : G)⁻¹ * k⁆ =
        ((⟨x, hx⟩ * ℓ⁻¹ * (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩)⁻¹ * ℓ : ↥L) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, commutatorElement_def]
      group
    rw [e]
    exact h2
  exact mem_innerSub_iff.mpr ⟨ℓ, ℓ.2, _, hcM, (mul_inv_cancel_left (ℓ : G) k).symm⟩

theorem mem_innerSub_of_out5 {L : Subgroup G} {S : Type*} [Group S] {α : ↥L →* S}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) (hS : Out5Inner S) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hk5 : k ^ 5 = 1) : k ∈ innerSub L := by
  obtain ⟨φ, hφ⟩ := exists_mulAut_comp α hα (Subgroup.normalizerMonoidHom L ⟨k, hk⟩)
    (map_normalizerMonoidHom_eq_one_iff hker hk)
  set c := Subgroup.normalizerMonoidHom L ⟨k, hk⟩ with hc
  have hpow : ∀ (n : ℕ) (x : ↥L), (φ ^ n) (α x) = α ((c ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  have hc5 : c ^ 5 = 1 := by
    rw [hc, ← map_pow]
    have : (⟨k, hk⟩ : Subgroup.normalizer (L : Set G)) ^ 5 = 1 := Subtype.ext hk5
    rw [this, map_one]
  have hφ5 : φ ^ 5 = 1 := by
    ext s
    obtain ⟨x, rfl⟩ := hα s
    rw [hpow, hc5]
    rfl
  obtain ⟨g, hg⟩ := hS φ hφ5
  exact mem_innerSub_of_exists_conj hα hker hk ⟨g, fun x => by rw [← hφ, hg]⟩

end Block

end SBc17

end CFSG.Quasithin
