module

public import CFSG.RankThree.Chevalley.G2CyclotomicTori

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem odd_of_eq_sq_add_mul_add_one {q : ℕ} {ε : ℤ} (hε : ε = -1 ∨ ε = 1) {d : ℕ}
    (hd : (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) : Odd d := by
  have hev : Even ((q : ℤ) ^ 2 + ε * q) := by
    rcases hε with rfl | rfl
    · have : (q : ℤ) ^ 2 + -1 * q = (q : ℤ) * ((q : ℤ) - 1) := by ring
      rw [this]
      exact Int.even_mul_pred_self _
    · have : (q : ℤ) ^ 2 + 1 * q = (q : ℤ) * ((q : ℤ) + 1) := by ring
      rw [this]
      exact Int.even_mul_succ_self _
  have hdZ : Odd (d : ℤ) := by
    rw [hd]
    exact hev.add_one
  exact (Int.odd_coe_nat d).1 hdZ

theorem even_G2_cyclotomic_three_six_tori_and_prime_centralizers (K : Type) [Field K] [Finite K]
    [CharP K 2] (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) :
    ∃ T : Subgroup (adjointGroup .G2 K), IsCyclic T ∧ Nat.card T = d ∧
      (∃ S : Sylow p (adjointGroup .G2 K), (S : Subgroup (adjointGroup .G2 K)) ≤ T) ∧
      (∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P → IsCyclic P) ∧
      ∀ x : adjointGroup .G2 K, orderOf x = p →
        (∃ g : adjointGroup .G2 K, g * x * g⁻¹ ∈ T) ∧
        (∃ g : adjointGroup .G2 K,
          (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T) ∧
        IsCyclic (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) ∧
        Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) = d ∧ Odd d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  obtain ⟨T, hcyc, hcard, hcent, hidx⟩ : ∃ T : Subgroup (adjointGroup .G2 K), IsCyclic T ∧
      Nat.card T = d ∧ (∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T) ∧
      ¬ p ∣ T.index := by
    rcases hε with rfl | rfl
    · obtain ⟨T, h1, h2, h3⟩ := cyclotomic_core K (Or.inl rfl) g2rot_one_g2a g2rot_one_g2r d
        (by rw [hd]; ring) hp hp3
      exact ⟨T, h1, h2, h3,
        not_dvd_index_of_card_eq K (Or.inl rfl) d (by rw [hd]; ring) hp hp3 hpd T h2⟩
    · obtain ⟨T, h1, h2, h3⟩ := cyclotomic_core K (Or.inr rfl) g2rot_two_g2a g2rot_two_g2r d
        (by rw [hd]; ring) hp hp3
      exact ⟨T, h1, h2, h3,
        not_dvd_index_of_card_eq K (Or.inr rfl) d (by rw [hd]; ring) hp hp3 hpd T h2⟩
  have hdodd : Odd d := odd_of_eq_sq_add_mul_add_one hε hd
  have hconjT : ∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P →
      ∃ g : adjointGroup .G2 K, P.map (MulAut.conj g).toMonoidHom ≤ T := fun P hP =>
    exists_conj_map_le_of_not_dvd_index hidx hP
  refine ⟨T, hcyc, hcard, ?_, fun P hP => ?_, fun x hx => ?_⟩
  · obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
    have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
    have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
      rw [Subgroup.index_map_subtype]
      exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
    exact ⟨hS.toSylow hSi, by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _⟩
  · obtain ⟨g, hg⟩ := hconjT P hP
    exact isCyclic_of_injective
      (MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp P.subtype) T
        fun y => hg ⟨y, y.2, rfl⟩)
      fun y z h => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  · have hPx : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨g, hg⟩ := hconjT _ hPx
    have hxT : g * x * g⁻¹ ∈ T := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hto : orderOf (g * x * g⁻¹) = p := by
      rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
        orderOf_injective _ (MulAut.conj g).injective x, hx]
    have hmap : (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T := by
      rw [map_conj_centralizer_singleton_eq, hcent _ hxT hto]
    have e : Subgroup.centralizer ({x} : Set (adjointGroup .G2 K)) ≃* T :=
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact ⟨⟨g, hxT⟩, ⟨g, hmap⟩, isCyclic_of_injective e.toMonoidHom e.injective,
      by rw [Nat.card_congr e.toEquiv, hcard], hdodd⟩

end CFSG.RankThree.Chevalley
