module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.NZeroCube
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CubeKernel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_of_isLnTwoQuot {L : Subgroup G} (hq : IsLnTwoQuot L 3) :
    3 ∣ Nat.card ↥L := by
  have h168 := SBd5.card_quot_of_isLnTwoQuot hq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [h168] at h1
  exact (by norm_num : 3 ∣ 168).trans (Dvd.intro _ h1.symm)

omit [Finite G] in
theorem center_trivial_of_modO2Surj {L : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : IsModO2Surj L α) :
    ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L := by
  intro x hx hcomm
  let x' : ↥L := ⟨x, hx⟩
  have hker : ∀ c : ↥L, (c : G) ∈ pCoreOf 2 L → α c = 1 := by
    intro c hc
    obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp hc
    have : o = c := Subtype.ext hoe
    subst this
    have : o ∈ α.ker := by rw [hα.2]; exact ho
    exact this
  have hcomm' : ∀ g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F,
      moduleAct false g * ((α x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((α x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * moduleAct false g := by
    intro g hg
    obtain ⟨l, hl⟩ := hα.1 ⟨g, hg⟩
    have h1 : α ⟨x * l * x⁻¹ * (l : G)⁻¹, by
        exact L.mul_mem (L.mul_mem (L.mul_mem hx l.2) (L.inv_mem hx)) (L.inv_mem l.2)⟩ = 1 :=
      hker _ (hcomm l l.2)
    have h2 : ⁅α x', α l⁆ = 1 := by
      rw [commutatorElement_def]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    have h3 : α x' * α l = α l * α x' := commutatorElement_eq_one_iff_mul_comm.mp h2
    have h4 := congrArg (fun u : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =>
      ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h3
    rw [hl] at h4
    simp only [Subgroup.coe_mul, Units.val_mul] at h4
    simp only [moduleAct, Bool.false_eq_true, ite_false]
    exact h4.symm
  rcases end_scalar_of_commutes hF false _ hcomm' with h | h
  · exfalso
    have h1 := (α x' : GL (Fin 3) F).val_inv
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  · have h1 : α x' = 1 := Subtype.ext (Units.ext h)
    have h2 : x' ∈ α.ker := h1
    rw [hα.2] at h2
    exact Subgroup.mem_map.mpr ⟨x', h2, rfl⟩

end General

section Case4

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

omit [Finite G] in
theorem c134CQ_card_four (hq : IsLnTwoQuot L 3) (h4 : MS93.IsC134Case4Corr (L ⊔ S) S L) :
    Nat.card ↥(c134CQ (L ⊔ S) L) = 4 ∧ ∀ c ∈ c134CQ (L ⊔ S) L, c * c = 1 := by
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hE2, -⟩, -⟩ := h4
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  obtain ⟨hC4', hCsq'⟩ := isE2_card_sq hE2
  exact ⟨by rw [hC4']; norm_num, fun c hc => congrArg Subtype.val (hCsq' ⟨c, hc⟩)⟩

theorem N0_le_normalizer (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (h4 : MS93.IsC134Case4Corr (L ⊔ S) S L) :
    N0 L ≤ Subgroup.normalizer ((c134Q (L ⊔ S) L : Subgroup G) : Set G) ⊓
      Subgroup.normalizer ((c134CQ (L ⊔ S) L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQeq : c134Q (L ⊔ S) L = ⁅pCoreOf 2 L, L⁆ :=
    Stellmacher.CD.L3YC.c134Q_eq_of_comm_self hSL
      (Stellmacher.CD.L3YC.comm_self_of_case4Corr h4)
  intro z hz
  refine ⟨?_, Stellmacher.CD.L3YC.normalizer_le_normalizer_c134CQ_of_case4 hSL h4 hz.1⟩
  rw [hQeq]
  exact SBd5.mem_normalizer_commutator_of (normalizer_le_normalizer_pCoreOf 2 L hz.1) hz.1

theorem cyclic_three_subgroup_N0 (hev : evenRank G ≤ 2) (hq : IsLnTwoQuot L 3)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (h4 : MS93.IsC134Case4Corr (L ⊔ S) S L)
    {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPN : P ≤ N0 L) : IsCyclic ↥P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  have hQL : c134Q (L ⊔ S) L ≤ pCoreOf 2 L := Stellmacher.CD.L3YC.c134Q_le_pCoreOf hSL
  have hVQ : c134CQ (L ⊔ S) L ≤ c134Q (L ⊔ S) L := inf_le_left
  have hVne : c134CQ (L ⊔ S) L ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hC4
    omega
  have hM : IsTwoLocal (Subgroup.normalizer ((c134CQ (L ⊔ S) L : Subgroup G) : Set G)) :=
    ⟨c134CQ (L ⊔ S) L, hVne, (pCoreOf_isPGroup 2 L).to_le (hVQ.trans hQL), rfl⟩
  have hLM := Stellmacher.CD.L3YC.normalizer_le_normalizer_c134CQ_of_case4 hSL h4
  obtain ⟨⟨n, F, _, _, α, hFc, hα, -⟩, -⟩ := h4
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  exact cyclic_of_three_subgroup_N0 hev hM hLM (three_dvd_card_of_isLnTwoQuot hq)
    (center_trivial_of_modO2Surj hF hα) hP hPN

theorem centralizes_c134Q_of_N0_of_moved (hev : evenRank G ≤ 2) (hq : IsLnTwoQuot L 3)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (h4 : MS93.IsC134Case4Corr (L ⊔ S) S L)
    {y : G} (hyN : y ∈ N0 L) {a : ℕ} (hya : y ^ 3 ^ a = 1)
    (hmove : ∃ x ∈ c134CQ (L ⊔ S) L, y * x * y⁻¹ ≠ x)
    {g : G} (hg : g ∈ N0 L) {m : ℕ} (hgm : g ^ 3 ^ m = 1)
    (hgV : ∀ v ∈ c134CQ (L ⊔ S) L, g * v * g⁻¹ = v) :
    ∀ q ∈ c134Q (L ⊔ S) L, g * q * g⁻¹ = q :=
  centralizes_of_cube_kernel (H := N0 L) (V := c134CQ (L ⊔ S) L) (Q := c134Q (L ⊔ S) L)
    (fun _ hx => (N0_le_normalizer hSL h4 hx).2) (fun _ hx => (N0_le_normalizer hSL h4 hx).1)
    (c134CQ_card_four hq h4).1 (c134CQ_card_four hq h4).2
    (fun _ hPN hP3 => cyclic_three_subgroup_N0 hev hq hSL h4 hP3 hPN)
    (fun _ hz _ hzm => cube_centralizes_c134Q hq hSL h4 hz hzm)
    hyN hya hmove hg hgm hgV

end Case4

end Stellmacher.L3YC

end CFSG.Quasithin
