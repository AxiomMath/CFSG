module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggNormalizer_le_normalizer_pPrimeCoreOf (p : ℕ) (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (LargeEvenPPrimeCoreOf p A : Set G) := by
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  rw [← largeEvenPPrimeCoreOf_map_conj, map_conj_eq_of_mem_normalizer hg]

theorem ggPPrimeCoreOf_coprime {p : ℕ} [Fact p.Prime] (A : Subgroup G) :
    Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p A)) := by
  rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective A.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

omit [Finite G] in
theorem ggLe_pPrimeCoreOf {p : ℕ} {M E : Subgroup G} (hEM : E ≤ M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) (hcop : Nat.Coprime p (Nat.card E)) :
    E ≤ LargeEvenPPrimeCoreOf p M := by
  have hle : E.subgroupOf M ≤ LargeEvenPPrimeCore p ↥M := by
    apply le_sSup
    refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hEM).mpr hME, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
    exact hcop
  calc E = (E.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hEM).symm
    _ ≤ LargeEvenPPrimeCoreOf p M := Subgroup.map_mono hle

theorem ggPPrimeCoreOf_le_of_isSubnormal {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsSubnormal A X) : LargeEvenPPrimeCoreOf p A ≤ LargeEvenPPrimeCoreOf p X := by
  induction hA with
  | refl => exact le_rfl
  | @step A M X hAM hn _ ih =>
    refine le_trans ?_ ih
    have hOA : LargeEvenPPrimeCoreOf p A ≤ M := (Subgroup.map_subtype_le _).trans hAM
    refine ggLe_pPrimeCoreOf hOA ?_ (ggPPrimeCoreOf_coprime A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn).trans
      (ggNormalizer_le_normalizer_pPrimeCoreOf p A)

omit [Finite G] in
theorem ggMap_eq_bot_of_le_pPrimeCoreOf (p : ℕ) {X W : Subgroup G}
    (hW : W ≤ LargeEvenPPrimeCoreOf p X) :
    (W.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro w hw
  obtain ⟨v, hv, hvw⟩ := hW (Subgroup.mem_subgroupOf.mp hw)
  have : v = w := Subtype.ext hvw
  exact this ▸ hv

theorem ggOdd_card_pPrimeCoreOf {p : ℕ} (hp : p.Prime) {X A K : Subgroup G}
    (hA : LargeEvenPComponent p X A) (hK : CFSG.Assembly.IsQuasisimple ↥K) (hKA : K ≤ A)
    (hAeq : A = K ⊔ LargeEvenPPrimeCoreOf p A) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hY : Odd (Nat.card (⁅K, LargeEvenPPrimeCoreOf p X⁆ : Subgroup G))) :
    Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) := by
  have : Fact p.Prime := ⟨hp⟩
  set E := LargeEvenPPrimeCoreOf p A with hEdef
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X) with hπ
  have hAX : A ≤ X := hA.1
  have hEX : E ≤ LargeEvenPPrimeCoreOf p X := ggPPrimeCoreOf_le_of_isSubnormal hA.2.1
  have hEA : E ≤ A := Subgroup.map_subtype_le _
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.le_normalizer.trans (ggNormalizer_le_normalizer_pPrimeCoreOf p A)
  set Y : Subgroup G := ⁅K, E⁆ with hYdef
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat hY (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hEX))
  have hYE : Y ≤ E := Subgroup.le_normalizer_iff_commutator_le_right.mp (hKA.trans hAE)
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := Subgroup.normalizer_commutator_ge_left K E
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := Subgroup.normalizer_commutator_ge_right K E
  have hconjK : ∀ e ∈ E, K.map (MulAut.conj e).toMonoidHom ≤ K ⊔ Y := by
    rintro e he _ ⟨k, hk, rfl⟩
    have h1 : ⁅k, e⁆ ∈ Y := Subgroup.commutator_mem_commutator hk he
    have h2 : (MulAut.conj e).toMonoidHom k = ⁅k, e⁆⁻¹ * k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Y.inv_mem h1)) (Subgroup.mem_sup_left hk)
  have hEKY : E ≤ Subgroup.normalizer ((K ⊔ Y : Subgroup G) : Set G) := by
    intro e he
    have key : ∀ e ∈ E, (K ⊔ Y).map (MulAut.conj e).toMonoidHom ≤ K ⊔ Y := by
      intro e he
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hEY he)]
      exact sup_le (hconjK e he) le_sup_right
    exact CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (key e he)
      (key e⁻¹ (E.inv_mem he))
  have hKKY : K ≤ Subgroup.normalizer ((K ⊔ Y : Subgroup G) : Set G) := fun k hk =>
    ggMem_normalizer_sup (Subgroup.le_normalizer hk) (hKY hk)
  have hAKY : A ≤ Subgroup.normalizer ((K ⊔ Y : Subgroup G) : Set G) := by
    rw [hAeq]
    exact sup_le hKKY hEKY
  have hKYA : K ⊔ Y ≤ A := sup_le hKA (hYE.trans hEA)
  have hKYsn : IsSubnormal (K ⊔ Y) X :=
    IsSubnormal.step hKYA ((Subgroup.normal_subgroupOf_iff_le_normalizer hKYA).mpr hAKY) hA.2.1
  have hKX : K ≤ X := hKA.trans hAX
  have hYX : Y ≤ X := (hYE.trans hEA).trans hAX
  have hEX' : E ≤ X := hEA.trans hAX
  have himg : ((K ⊔ Y).subgroupOf X).map π = (A.subgroupOf X).map π := by
    conv_rhs => rw [hAeq]
    rw [Subgroup.subgroupOf_sup hKX hYX, Subgroup.subgroupOf_sup hKX hEX', Subgroup.map_sup,
      Subgroup.map_sup, ggMap_eq_bot_of_le_pPrimeCoreOf p (hYE.trans hEX),
      ggMap_eq_bot_of_le_pPrimeCoreOf p hEX]
  have hKYeq : K ⊔ Y = A := by
    by_contra hne
    exact hA.2.2.2 (K ⊔ Y) (lt_of_le_of_ne hKYA hne) hKYsn himg
  have hEKc : E ⊓ K ≤ Subgroup.centralizer (K : Set G) := by
    have hKn : K ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := fun k hk =>
      mem_normalizer_inf (hAE (hKA hk)) (Subgroup.le_normalizer hk)
    rcases ggLe_center_or_eq_of_normalized hK inf_le_right hKn with h | h
    · exact h
    · exfalso
      have hKE : K ≤ E := h ▸ inf_le_left
      have hAE' : A ≤ LargeEvenPPrimeCoreOf p X := by
        rw [hAeq]
        exact sup_le (hKE.trans hEX) hEX
      have hbot := ggMap_eq_bot_of_le_pPrimeCoreOf p hAE'
      exact ne_bot_of_isComponentOf' hA.2.2.1 hbot
  have hEKodd : Odd (Nat.card (E ⊓ K : Subgroup G)) := by
    have hle : E ⊓ K ≤ ggCenterOf K := by
      intro z hz
      refine ⟨⟨z, hz.2⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEKc hz) w w.2)
    have hcard := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hcard
    exact Odd.of_dvd_nat hZ hcard
  have hord : ∀ e ∈ E, Odd (orderOf e) := by
    intro e he
    have heKY : e ∈ ((K ⊔ Y : Subgroup G) : Set G) := hKYeq ▸ hEA he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K Y hKY] at heKY
    obtain ⟨k, hk, y, hy, hky⟩ := heKY
    have hkE : k ∈ E := by
      have : k = e * y⁻¹ := by rw [← hky]; group
      rw [this]
      exact E.mul_mem he (E.inv_mem (hYE hy))
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hEKodd ((E ⊓ K).orderOf_dvd_natCard ⟨hkE, hk⟩)
    have hpow : ∀ n : ℕ, ∃ y' ∈ Y, (k * y) ^ n = k ^ n * y' := by
      intro n
      induction n with
      | zero => exact ⟨1, Y.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨y', hy', h⟩ := ih
        have hc : k⁻¹ * y' * k⁻¹⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hKY (K.inv_mem hk)) y').mp hy'
        refine ⟨k⁻¹ * y' * k⁻¹⁻¹ * y, Y.mul_mem hc hy, ?_⟩
        rw [pow_succ, h, pow_succ]
        group
    obtain ⟨y', hy', h⟩ := hpow (orderOf k)
    rw [pow_orderOf_eq_one, one_mul] at h
    have h1 : (k * y) ^ (orderOf k * Nat.card Y) = 1 := by
      rw [pow_mul, h]
      exact orderOf_dvd_iff_pow_eq_one.mp (Y.orderOf_dvd_natCard hy')
    rw [← hky]
    exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hkodd, hYodd⟩) (orderOf_dvd_of_pow_eq_one h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ Nat.card E := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 2 h2'
  have := hord g g.2
  rw [Subgroup.orderOf_coe, hg] at this
  exact (Nat.not_even_iff_odd.mpr this) even_two

end General

end CFSG.StandardType
