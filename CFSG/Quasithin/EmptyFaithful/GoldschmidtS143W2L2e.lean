module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen
public import CFSG.Quasithin.EmptyFaithful.S143SC
public import CFSG.Quasithin.EmptyFaithful.S143SD

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.K1 CFSG.GorensteinWalter
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace S143

namespace InspW2

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section EvenCore

variable {L : Type} [Group L] [Finite L] {Gc : Type} [Group Gc] [Finite Gc] {ρ : Gc →* MulAut L}

omit [Finite L] in
theorem card_inner_eq (hZ : Subgroup.center L = ⊥) : Nat.card (Inn L) = Nat.card L := by
  have h1 : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card (L ⧸ Subgroup.center L) := by
    rw [← Insp7.ker_conj_eq_center]
    exact (Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  rw [hZ] at h1
  rw [Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv] at h1
  exact h1

omit [Finite L] [Finite Gc] in
theorem evenCore_sq (hZ : Subgroup.center L = ⊥)
    (hl2 : ∀ z' : L, z' * z' = 1 → z' ≠ 1 → ∀ l : L, l * z' = z' * l → l * l = 1)
    {z : L} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hρ : Function.Injective ρ) {ž : Gc}
    (hž : ρ ž = MulAut.conj z) {b : Gc} (hbH : ρ b ∈ Inn L)
    (hbC : b ∈ Subgroup.centralizer ({ž} : Set Gc)) : b * b = 1 := by
  obtain ⟨l, hl⟩ := hbH
  have hbž : b * ž = ž * b := Subgroup.mem_centralizer_singleton_iff.mp hbC
  have hcomm : MulAut.conj l * MulAut.conj z = MulAut.conj z * MulAut.conj l := by
    rw [hl, ← hž, ← map_mul, ← map_mul, hbž]
  have h3 : MulAut.conj (l * z * (z * l)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, hcomm]
    simp
  have h4 : l * z * (z * l)⁻¹ ∈ Subgroup.center L := by
    rw [← Insp7.ker_conj_eq_center]
    exact h3
  rw [hZ, Subgroup.mem_bot] at h4
  have h5 : l * z = z * l := mul_inv_eq_one.mp h4
  apply hρ
  rw [map_mul, map_one, show ρ b = MulAut.conj l from hl.symm, ← map_mul,
    hl2 z hz2 hz1 l h5, map_one]

omit [Finite L] in
theorem evenCore_three_dvd (hZ : Subgroup.center L = ⊥)
    (hl2 : ∀ z' : L, z' * z' = 1 → z' ≠ 1 → ∀ l : L, l * z' = z' * l → l * l = 1)
    {z : L} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hρ : Function.Injective ρ)
    (hinn : ∀ l : L, MulAut.conj l ∈ ρ.range) {ž : Gc} (hž : ρ ž = MulAut.conj z) {f : ℕ}
    (hf : (Inn L).index = f) {Ŝ : Subgroup Gc}
    (hC3 : Nat.card (Subgroup.centralizer ({ž} : Set Gc)) = 3 * Nat.card Ŝ) : 3 ∣ f := by
  have hinn' : Inn L ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hinn l
  set C : Subgroup Gc := Subgroup.centralizer ({ž} : Set Gc) with hC
  set H : Subgroup Gc := (Inn L).comap ρ with hH
  have hHn : H.Normal := Subgroup.normal_comap ρ
  set B : Subgroup Gc := H ⊓ C with hB
  have hBC : B ≤ C := inf_le_right
  have hBp : IsPGroup 2 B := fun g =>
    ⟨1, Subtype.ext (by simpa [sq] using evenCore_sq hZ hl2 hz2 hz1 hρ hž g.2.1 g.2.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hBp
  have hCB : Nat.card C = Nat.card B * B.relIndex C := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv] at h1
    exact h1.symm
  have hrel : B.relIndex C ∣ f := by
    have h1 : B.relIndex C = H.relIndex C := Subgroup.inf_relIndex_right H C
    have h2 : H.relIndex C ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H C
    have h3 : H.index = (Inn L).relIndex ρ.range := Subgroup.index_comap (Inn L) ρ
    have h4 : (Inn L).relIndex ρ.range ∣ (Inn L).index :=
      Subgroup.relIndex_dvd_index_of_le hinn'
    rw [h1, ← hf]
    exact h2.trans (h3 ▸ h4)
  have h3 : 3 ∣ Nat.card C := ⟨Nat.card Ŝ, hC3⟩
  rw [hCB, hk] at h3
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact (hcop.dvd_of_dvd_mul_left h3).trans hrel

omit [Finite L] [Finite Gc] in
theorem evenCore_f3 (hρ : Function.Injective ρ) (hZ : Subgroup.center L = ⊥)
    (hf : (Inn L).index = 3) (hN : Nat.card L = 504) {Ŝ : Subgroup Gc}
    (hcard : Nat.card Ŝ = 2 ^ 5 ∨ Nat.card Ŝ = 2 ^ 6) : False := by
  have hAut : Nat.card (MulAut L) = Nat.card L * 3 := by
    rw [← Subgroup.card_mul_index (Inn L), hf, card_inner_eq hZ]
  have hGcAut : Nat.card Gc ∣ Nat.card (MulAut L) := by
    rw [← Nat.card_range_of_injective hρ]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hŜGc : Nat.card Ŝ ∣ Nat.card Gc := Subgroup.card_subgroup_dvd_card Ŝ
  have h5 : 2 ^ 5 ∣ Nat.card Ŝ := by
    rcases hcard with h | h
    · rw [h]
    · rw [h]
      exact pow_dvd_pow 2 (by norm_num)
  have h6 := h5.trans (hŜGc.trans hGcAut)
  rw [hAut, hN] at h6
  omega

theorem odd_index_aux {N s x y n : ℕ} (hx : N * x = n) (hy : s * y = n)
    (hs : s = 2 ^ 5 ∨ s = 2 ^ 6) (hN : N = 262080) (hodd : y % 2 = 1) : x % 2 = 1 := by
  subst hN
  rcases hs with rfl | rfl <;> omega

omit [Finite Gc] in
theorem evenCore_f6 (hρ : Function.Injective ρ) (hZ : Subgroup.center L = ⊥)
    (hl2 : ∀ z' : L, z' * z' = 1 → z' ≠ 1 → ∀ l : L, l * z' = z' * l → l * l = 1)
    (hinn : ∀ l : L, MulAut.conj l ∈ ρ.range) (hN : Nat.card L = 262080) {Ŝ : Subgroup Gc}
    (hŜ2 : IsPGroup 2 Ŝ) (hŜodd : ¬ 2 ∣ Ŝ.index)
    (hcard : Nat.card Ŝ = 2 ^ 5 ∨ Nat.card Ŝ = 2 ^ 6) (h4 : ∃ e ∈ Ŝ, orderOf e = 4) : False := by
  have hinn' : Inn L ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hinn l
  set H : Subgroup Gc := (Inn L).comap ρ with hH
  have hHn : H.Normal := Subgroup.normal_comap ρ
  have hHcard : Nat.card H = 262080 := by
    have h1 : H.map ρ = Inn L := by
      rw [hH, Subgroup.map_comap_eq]
      exact inf_of_le_right hinn'
    rw [← hN, ← card_inner_eq hZ, ← h1]
    exact (Subgroup.card_map_of_injective hρ).symm
  have hGc1 : Nat.card H * H.index = Nat.card Gc := Subgroup.card_mul_index H
  have hGc2 : Nat.card Ŝ * Ŝ.index = Nat.card Gc := Subgroup.card_mul_index Ŝ
  have hSodd : Ŝ.index % 2 = 1 := by omega
  have hHodd : H.index % 2 = 1 := odd_index_aux hGc1 hGc2 hcard hHcard hSodd
  have hSH : Ŝ ≤ H := by
    obtain ⟨n, hn⟩ := hŜ2.index (H.subgroupOf Ŝ)
    have h1 : H.relIndex Ŝ ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H Ŝ
    have h2 : H.relIndex Ŝ = 2 ^ n := hn
    rw [h2] at h1
    have hn0 : n = 0 := by
      by_contra hne
      have h3 : 2 ∣ H.index := (dvd_pow_self 2 hne).trans h1
      omega
    rw [hn0] at h2
    exact Subgroup.relIndex_eq_one.mp (by simpa using h2)
  obtain ⟨e4, he4S, he4⟩ := h4
  obtain ⟨l, hl⟩ := hSH he4S
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  have hol : orderOf l = 4 := by
    rw [← orderOf_injective _ hinj l, hl, orderOf_injective _ hρ e4, he4]
  have hl4 : l ^ 4 = 1 := by
    have := pow_orderOf_eq_one l
    rwa [hol] at this
  have hl2' : l ^ 2 * l ^ 2 = 1 := by rw [← pow_add]; exact hl4
  have hl21 : l ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hol] at this
    omega
  have hcomm : l * l ^ 2 = l ^ 2 * l := by rw [← pow_succ, ← pow_succ']
  apply hl21
  rw [pow_two]
  exact hl2 (l ^ 2) hl2' hl21 l hcomm

end EvenCore

theorem evenL2_facts {L : Type} [Group L] {f : ℕ} (hf2 : 2 ≤ f)
    (hmodel : StatedClassicalModel L .PSL 2 2 f) :
    Subgroup.center L = ⊥ ∧
      (∀ z' : L, z' * z' = 1 → z' ≠ 1 → ∀ l : L, l * z' = z' * l → l * l = 1) ∧
      (Inn L).index = f ∧ Nat.card L = CFSG.Open.ordA 1 (2 ^ f) := by
  have hmodel' := hmodel
  obtain ⟨-, K, _, hfin, hKcard, ⟨e0⟩⟩ := hmodel
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hKcard
  let e : L ≃* SL(2, K) :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans sl2EquivPSL2.symm
  have hZSL : Subgroup.center SL(2, K) = ⊥ := by
    have h1 : (Subgroup.center SL(2, K)).map (sl2EquivPSL2 (F := K)).toMonoidHom =
        Subgroup.center (PSL2 K) := Subgroup.map_center_eq (sl2EquivPSL2 (F := K))
    rw [psl2_center_eq_bot K] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (sl2EquivPSL2 (F := K)).injective).mp h1
  have hZ : Subgroup.center L = ⊥ := by
    have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center SL(2, K) :=
      Subgroup.map_center_eq e
    rw [hZSL] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  refine ⟨hZ, ?_, ?_, (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel').1 rfl⟩
  · intro z' hz'2 hz'1 l hl
    have hez1 : e z' ≠ 1 := fun h => hz'1 (e.injective (by rw [h, map_one]))
    have hez2 : e z' * e z' = 1 := by rw [← map_mul, hz'2, map_one]
    have h1 := Insp7.sl2_sq_eq_one_of_commute (e z') (e l) hez2 hez1
      (by rw [← map_mul, ← map_mul, hl])
    apply e.injective
    rw [map_mul, map_one]
    exact h1
  · have h6 : Nat.card (Outer L) = Nat.card (Outer SL(2, K)) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    have h7 := (even_SL2_full_automorphism_semilinear_model (F := K) (n := f) (by omega)
      hKcard).2.2.2.1
    have h8 : (Inn L).index = Nat.card (Outer L) := rfl
    rw [h8, h6, h7]

theorem numFactW_evenL2 : NumFactW Insp7.EvenL2Fam := by
  intro L _ _ _ hF z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard h4 hC3
  obtain ⟨f, hf2, hf8, hmodel⟩ := hF
  obtain ⟨hZ, hl2, hidx, hcardL⟩ := evenL2_facts hf2 hmodel
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have h3f : 3 ∣ f := evenCore_three_dvd hZ hl2 hz2 hz1 hρ hinn hž hidx hC3
  have hf36 : f = 3 ∨ f = 6 := by omega
  rcases hf36 with rfl | rfl
  · exact evenCore_f3 hρ hZ hidx (by rw [hcardL]; decide +kernel) hcard
  · exact evenCore_f6 hρ hZ hl2 hinn (by rw [hcardL]; decide +kernel) hŜ2 hŜodd hcard h4

end InspW2

end S143

end CFSG.Quasithin
