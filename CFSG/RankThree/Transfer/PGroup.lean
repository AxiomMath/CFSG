module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.RankThree.Transfer

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem card_multiplicative_zmod : Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_surjective_zmod_of_ne_top {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    {R : Subgroup Q} (hR : R ≠ ⊤) :
    ∃ φ : Q →* Multiplicative (ZMod p), Function.Surjective φ ∧ R ≤ φ.ker := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨n, hn, hRn⟩ := (Nat.dvd_prime_pow hp.out).mp (hm ▸ R.card_subgroup_dvd_card)
  have hnm : n < m := by
    refine lt_of_le_of_ne hn ?_
    rintro rfl
    exact hR ((Subgroup.card_eq_iff_eq_top R).mp (hRn.trans hm.symm))
  obtain ⟨K, hK, hRK⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := Q) p (n := n) (m := m - 1)
    (hm ▸ pow_dvd_pow p (Nat.sub_le m 1)) R hRn (by omega)
  have hindex : K.index = p := by
    have h := K.card_mul_index
    rw [hK, hm] at h
    have h' : p ^ (m - 1) * K.index = p ^ (m - 1) * p := by
      rw [h, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h'
  have hKn : K.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hindex, hm, hp.out.pow_minFac (by omega)]
  have hcard : Nat.card (Q ⧸ K) = p := by rw [← Subgroup.index_eq_card, hindex]
  let e : Q ⧸ K ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcard card_multiplicative_zmod
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective K)
  · intro r hr
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
    exact hRK hr

variable {G : Type*} [Group G]

omit hp in
theorem le_of_isPGroup_of_le_normalizer (P : Sylow p G) {H : Subgroup G} (hH : IsPGroup p H)
    (hHN : H ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) : H ≤ P := by
  have h := P.is_maximal' (hH.to_sup_of_normal_right' P.isPGroup' hHN) le_sup_right
  rw [← h]
  exact le_sup_left

theorem mem_of_pow_eq_one_of_mem_normalizer (P : Sylow p G) {g : G}
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) {k : ℕ} (hk : g ^ p ^ k = 1) :
    g ∈ P := by
  have hpg : IsPGroup p (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card ((Nat.card_zpowers g).trans hj)
  exact le_of_isPGroup_of_le_normalizer P hpg
    ((Subgroup.zpowers_le (H := Subgroup.normalizer ((P : Subgroup G) : Set G))).mpr hg)
    (Subgroup.mem_zpowers g)

omit hp in
theorem mem_normalizer_of_forall_conj_mem_normalizer [Finite G] (P : Sylow p G) {g : G}
    (hg : ∀ c ∈ (P : Subgroup G),
      g⁻¹ * c * g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  let Q : Subgroup G := (P : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom
  have hQ : IsPGroup p Q := P.isPGroup'.map _
  have hQN : Q ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply] using hg c hc
  have hQP : Q ≤ P := le_of_isPGroup_of_le_normalizer P hQ hQN
  have hcard : Nat.card Q = Nat.card (P : Subgroup G) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hQeq : Q = P := Subgroup.eq_of_le_of_card_ge hQP hcard.ge
  have hinv : g⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have : g⁻¹ * c * g⁻¹⁻¹ ∈ Q := ⟨c, hc, by simp⟩
      rwa [hQeq] at this
    · intro hc
      rw [← hQeq] at hc
      obtain ⟨c', hc', hcc'⟩ := hc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hcc'
      have : c' = c := by
        have := congrArg (fun x => g * x * g⁻¹) hcc'
        simpa [mul_assoc] using this
      exact this ▸ hc'
  simpa using Subgroup.inv_mem _ hinv

end CFSG.RankThree.Transfer

end
