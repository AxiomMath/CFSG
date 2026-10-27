module

public import CFSG.Quasithin.Vol2.Ch10SecB3Odd
public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conjAct_apply_coe (U : Subgroup G) (g : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    ((conjAct U g u : ↥U) : G) = g * u * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply U g u

theorem autOn_comm {U A L : Subgroup G}
    (hc : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ Subgroup.centralizer (U : Set G)) :
    ∀ x ∈ autOn A U, ∀ h ∈ autOn L U, x * h = h * x := by
  intro x hx h hh
  obtain ⟨a, ha, rfl⟩ := SecB.mem_autOn_iff.mp hx
  obtain ⟨l, hl, rfl⟩ := SecB.mem_autOn_iff.mp hh
  refine MulEquiv.ext fun u => Subtype.ext ?_
  simp only [MulAut.mul_apply, conjAct_apply_coe]
  set a' : G := (a : G) with ha'
  set l' : G := (l : G) with hl'
  have hm : l' * (a' * u * a'⁻¹) * l'⁻¹ ∈ U := by
    have h1 : a' * u * a'⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp a.2 u).mp u.2
    exact (Subgroup.mem_normalizer_iff.mp l.2 _).mp h1
  have hcU := Subgroup.mem_centralizer_iff.mp (hc a' ha l' hl) _ hm
  have key : a' * (l' * u * l'⁻¹) * a'⁻¹ = a' * l' * a'⁻¹ * l'⁻¹ *
      (l' * (a' * u * a'⁻¹) * l'⁻¹) * (a' * l' * a'⁻¹ * l'⁻¹)⁻¹ := by group
  rw [key, ← hcU, mul_inv_cancel_right]

theorem card_autOn_dvd [Finite G] (L U : Subgroup G) : Nat.card (autOn L U) ∣ Nat.card L :=
  CFSG.Quasithin.AutOn.card_autOn_dvd _ _

theorem isPGroup_autOn {p : ℕ} {A U : Subgroup G} (hA : IsPGroup p A) :
    IsPGroup p (autOn A U) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hA

variable {T L I : Subgroup G}

theorem L_le_normalizer_fsuVM (T L I : Subgroup G) :
    L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)).trans (SecA.fsuM_le_normalizer_fsuVM T L I)

theorem fsuUL_le' (T L I : Subgroup G) : fsuUL T L I ≤ fsuVM T L I :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (L_le_normalizer_fsuVM T L I)

theorem cenL0_le_normalizer_fsuUL [Finite G] (T L I : Subgroup G) :
    cenL0 T L I ≤ Subgroup.normalizer (fsuUL T L I : Set G) := by
  intro a ha
  obtain ⟨haM, hac⟩ := mem_cenL0.mp ha
  have haV : a ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I haM
  refine SecB.mem_normalizer_of_conj_mem fun u hu => ?_
  have hmap : (fsuUL T L I).map (MulAut.conj a).toMonoidHom ≤ fsuUL T L I := by
    rw [Subgroup.map_commutator]
    have hV : (fsuVM T L I).map (MulAut.conj a).toMonoidHom = fsuVM T L I := by
      rw [MulEquiv.toMonoidHom_eq_coe]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp haV
    rw [hV, Subgroup.commutator_le]
    rintro v hv _ ⟨l, hl, rfl⟩
    have hlL0 := SecA.le_fsuL0 T L hl
    set c := a * l * a⁻¹ * l⁻¹ with hc
    have hcV := hac l hlL0
    have hvl : v * l * v⁻¹ * l⁻¹ ∈ fsuVM T L I := by
      have h1 : l * v⁻¹ * l⁻¹ ∈ fsuVM T L I :=
        (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_fsuVM T L I hl) _).mp
          (Subgroup.inv_mem _ hv)
      have := Subgroup.mul_mem _ hv h1
      simpa [mul_assoc] using this
    have e : ⁅v, (MulAut.conj a).toMonoidHom l⁆ = c * (v * l * v⁻¹ * l⁻¹) * c⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.mp hcV v hv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def, hc]
      calc v * (a * l * a⁻¹) * v⁻¹ * (a * l * a⁻¹)⁻¹
          = v * (a * l * a⁻¹ * l⁻¹) * l * v⁻¹ * l⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ := by group
        _ = a * l * a⁻¹ * l⁻¹ * v * l * v⁻¹ * l⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ := by
            rw [h1]
        _ = a * l * a⁻¹ * l⁻¹ * (v * l * v⁻¹ * l⁻¹) * (a * l * a⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    have h2 := Subgroup.mem_centralizer_iff.mp hcV _ hvl
    rw [← h2, mul_inv_cancel_right]
    exact Subgroup.commutator_mem_commutator hv hl
  exact hmap ⟨u, hu, by simp [MulAut.conj_apply]⟩

variable [Finite G]

omit [Finite G] in
theorem autOn_mem_cV1 {A : Subgroup G} (hA : A ≤ cenL0 T L I) :
    ∀ x ∈ autOn A (fsuUL T L I), ∀ z ∈ cV1 T L I, x z ∈ cV1 T L I := by
  intro x hx z hz
  obtain ⟨a, ha, rfl⟩ := SecB.mem_autOn_iff.mp hx
  rw [Ch10.cV1, Subgroup.mem_subgroupOf, conjAct_apply_coe]
  exact (conj_mem_centralizer_iff ((mem_cenL0.mp (hA ha)).1)).mpr hz

theorem comm_mem_of_autOn {A : Subgroup G} (hA : A ≤ cenL0 T L I)
    (h : ∀ x ∈ autOn A (fsuUL T L I), ∀ v : ↥(fsuUL T L I), x v * v⁻¹ ∈ cV1 T L I) :
    ∀ a ∈ A, ∀ u ∈ fsuUL T L I,
      a * u * a⁻¹ * u⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  intro a ha u hu
  have haN := cenL0_le_normalizer_fsuUL T L I (hA ha)
  have hx : conjAct (fsuUL T L I) ⟨a, haN⟩ ∈ autOn A (fsuUL T L I) :=
    SecB.mem_autOn_iff.mpr ⟨⟨a, haN⟩, ha, rfl⟩
  have h1 := h _ hx ⟨u, hu⟩
  rw [Ch10.cV1, Subgroup.mem_subgroupOf, Subgroup.coe_mul, conjAct_apply_coe] at h1
  simpa using h1

theorem commutator_fsuUL_eq_bot (hyp : Hyp10 G T L I) {A : Subgroup G} (hA : A ≤ cenL0 T L I)
    (h : ∀ a ∈ A, ∀ u ∈ fsuUL T L I,
      a * u * a⁻¹ * u⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) :
    ⁅fsuUL T L I, A⁆ = ⊥ := by
  have h1 : ⁅⁅L, A⁆, fsuUL T L I⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_le]
    intro l hl a ha
    have hc := (mem_cenL0.mp (hA ha)).2 l (SecA.le_fsuL0 T L hl)
    have hcU : a * l * a⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuUL T L I : Set G) :=
      Subgroup.centralizer_le (fsuUL_le' T L I) hc
    have e : ⁅l, a⁆ = (a * l * a⁻¹ * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ hcU
  have h2 : ⁅⁅A, fsuUL T L I⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro a ha u hu
    rw [commutatorElement_def]
    exact Subgroup.centralizer_le (SecA.le_fsuL0 T L) (h a ha u hu)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [SecC.commutator_fsuUL_eq hyp] at h3

theorem not_dvd_card_autOn_L {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) (U : Subgroup G) :
    ¬ p ∣ Nat.card (autOn L U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  have hdL := hd.trans (card_autOn_dvd L U)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)] at hdL
  rcases (Nat.Prime.dvd_mul hp).mp hdL with h | h
  · exact hpL h
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

end CFSG.Quasithin.Vol2.Ch10.SecB
