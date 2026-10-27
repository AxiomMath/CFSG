module

public import CFSG.Quasithin.Vol2.Ch10SecASL2OverAux
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable def quotConjEquiv (L : Subgroup G) (t : G) :
    (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr _ _ (conjugateEquiv L t) (CFSG.pCore_map_iso 2 _)

theorem eq_of_isSylowTwoOf_le {Q : Type*} [Group Q] [Finite Q] {P R : Subgroup Q}
    (hP : IsSylowTwoOf P ⊤) (hR : IsPGroup 2 R) (hPR : P ≤ R) : P = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP2, hidx⟩ := hP
  rw [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right _] at hidx
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR
  have hodd : Odd P.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  have hRd : Nat.card R ∣ Nat.card P * P.index := by
    rw [P.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card R
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hP2
  rw [ha, hb] at hRd
  have hab := le_of_two_pow_dvd hodd hRd
  refine Subgroup.eq_of_le_of_card_ge hPR ?_
  rw [ha, hb]
  exact Nat.pow_le_pow_right (by norm_num) hab

theorem mem_normalizer_of_map {Q : Type*} [Group Q] {A H : Subgroup G} (hAH : A ≤ H)
    (φ : ↥H →* Q) (hker : φ.ker ≤ A.subgroupOf H) {x : ↥H}
    (hx : φ x ∈ Subgroup.normalizer (((A.subgroupOf H).map φ : Subgroup Q) : Set Q)) :
    (x : G) ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ y : ↥H, φ y ∈ Subgroup.normalizer (((A.subgroupOf H).map φ : Subgroup Q) : Set Q) →
      ∀ a ∈ A, (y : G) * a * (y : G)⁻¹ ∈ A := by
    intro y hy a ha
    have hmem : φ (y * ⟨a, hAH ha⟩ * y⁻¹) ∈ (A.subgroupOf H).map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp ⟨⟨a, hAH ha⟩, ha, rfl⟩
    obtain ⟨a', ha', he⟩ := hmem
    have hk : a'⁻¹ * (y * ⟨a, hAH ha⟩ * y⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have h1 := (A.subgroupOf H).mul_mem ha' (hker hk)
    rw [mul_inv_cancel_left, Subgroup.mem_subgroupOf] at h1
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => key x hx a ha, fun ha => ?_⟩
  have hx' : φ x⁻¹ ∈ Subgroup.normalizer (((A.subgroupOf H).map φ : Subgroup Q) : Set Q) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have := key x⁻¹ hx' _ ha
  simpa [mul_assoc] using this

variable [Finite G] {T L I : Subgroup G}

theorem exists_SL_two_of_cases12
    (hshape : Stmt7_0_1_shape) (hyp : Ch10.Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  rcases h12 with ⟨n, hn, ⟨K, _, _, hK, he⟩, -⟩ | ⟨⟨eA⟩, -⟩
  · exact ⟨K, inferInstance, inferInstance, n, hn, hK, he⟩
  · have h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
      rw [Nat.card_congr eA.toEquiv, card_alt 5 (by norm_num)]
      decide
    rcases isShapeGroup_of_shape701 (hshape G T L I hyp.fsu hyp.lt hyp.three) with
      ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨m, -, a, -, K, _, _, hf, hK, ⟨e⟩⟩ | he
    · exact ⟨K, inferInstance, inferInstance, n, hn, hK, ⟨e⟩⟩
    · exfalso
      subst hf
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at h60
      exact three_not_dvd_card_suzuki a (h60 ▸ (by norm_num : 3 ∣ 60))
    · exfalso
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, card_SL_three_zmod_two] at h60
      norm_num at h60

end CFSG.Quasithin.Vol2.Ch10.SecA
