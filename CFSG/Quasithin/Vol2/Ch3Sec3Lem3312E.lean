module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312C
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace L3312

theorem isL2_five_of_alt5 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : F6.IsL2 5 1 X := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (ZMod 5) = 5 ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (ZMod 5) (Or.inr (by rw [Nat.card_zmod]))
  exact ⟨⟨by norm_num, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, hK, ⟨e.trans e5.symm⟩⟩

theorem le_of_normalizes {Q : Type} [Group Q] [Finite Q] {P B : Subgroup Q}
    (hP : IsSylowTwoOf P ⊤) (hP4 : Nat.card P = 4) (hB : Nat.card B = 60)
    (hPB : P ≤ Subgroup.normalizer (B : Set Q)) : P ≤ B := by
  have : (B.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPB
  have : (B.subgroupOf (P ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient P B hPB
  have h1 : B.relIndex P = B.relIndex (P ⊔ B) := Nat.card_congr e.toEquiv
  have h2 : B.relIndex P ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hP4]
    exact Subgroup.relIndex_dvd_card B P
  have h3 : B.relIndex (P ⊔ B) * Nat.card B = Nat.card ↥(P ⊔ B) := by
    have := Subgroup.relIndex_mul_card (H := B) (K := P ⊔ B)
    rwa [inf_of_le_left le_sup_right] at this
  have h4 : Nat.card ↥(P ⊔ B) ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
  have h5 : Nat.card Q = 4 * P.index := by
    rw [← hP4, Subgroup.card_mul_index]
  have hodd : ¬ 2 ∣ P.index := by
    have h6 := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at h6
  rw [← h3, hB, ← h1, h5] at h4
  obtain ⟨i, hi, hri⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hr : B.relIndex P = 1 := by
    interval_cases i
    · simpa using hri
    · exfalso
      rw [hri] at h4
      apply hodd
      obtain ⟨c, hc⟩ := h4
      exact ⟨15 * c, by omega⟩
    · exfalso
      rw [hri] at h4
      apply hodd
      obtain ⟨c, hc⟩ := h4
      exact ⟨30 * c, by omega⟩
  exact Subgroup.relIndex_eq_one.mp hr

theorem card_of_isAlt_five {X : Type} [Group X] (h : IsAlt 5 X) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem oddNorm_psl2_alt5 (hNorm : FactL2pSylowNorm)
    (hFour : FactL2pSylowFour) (hOut : FactAutL2pOuter) {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hQ : IsPSL 2 p 1 Q)
    {B : Subgroup Q} (hB : IsAlt 5 ↥B) : OddNorm Q B := by
  intro A S hInn hS hSB d hd hodd
  by_cases hA : A = (MulAut.conj : Q →* MulAut Q).range
  swap
  · rw [eq_one_of_odd_of_mem hS.2.1 (hOut p hp hp3 hp8 Q hQ A S hInn hA hS hd) hodd]
    exact Subgroup.one_mem _
  subst hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsQ : IsSimpleGroup Q := (CFSG.LieType.Simplicity.fam_PSL_simplicity Q 2 p 1 hQ).2
  let P₀ : Sylow 2 Q := default
  have hP₀ : IsSylowTwoOf (P₀ : Subgroup Q) ⊤ := by
    refine ⟨le_top, P₀.isPGroup', fun h2 => ?_⟩
    have h3 := P₀.not_dvd_index
    rw [show ((P₀ : Subgroup Q).subgroupOf ⊤).index = (P₀ : Subgroup Q).index from
      Subgroup.relIndex_top_right _] at h2
    exact h3 h2
  have hP₀4 := hFour p hp hp8 Q hQ _ hP₀
  have hcenter : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative Q := Subgroup.center_eq_top_iff.mp h
      have hpr := Group.is_simple_iff_prime_card.mp hsQ
      have h4 : 4 ∣ Nat.card Q := hP₀4 ▸ Subgroup.card_subgroup_dvd_card _
      have h2 : 2 ∣ Nat.card Q := (by norm_num : (2 : ℕ) ∣ 4).trans h4
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2
      rw [← this] at h4
      omega
  have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have hqc : q ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun f : MulAut Q => f g) (MonoidHom.mem_ker.mp hq)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * q = q * g * q⁻¹ * q := by rw [h1]
        _ = q * g := by group
    rwa [hcenter] at hqc
  set S₀ := S.comap (MulAut.conj : Q →* MulAut Q) with hS₀def
  have hS₀ : IsSylowTwoOf S₀ ⊤ := by
    refine ⟨le_top, hS.2.1.comap_of_injective _ hinj, fun h2 => hS.2.2 ?_⟩
    have h3 := Subgroup.relIndex_map_map_of_injective S₀ ⊤ hinj
    rw [Subgroup.map_comap_eq_self hS.1, ← MonoidHom.range_eq_map] at h3
    show 2 ∣ S.relIndex _
    rw [h3]
    exact h2
  have hS₀4 : Nat.card S₀ = 4 := hFour p hp hp8 Q hQ S₀ hS₀
  have hS₀B : S₀ ≤ Subgroup.normalizer (B : Set Q) := fun s hs =>
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (hSB hs)
  have hBc : Nat.card B = 60 := card_of_isAlt_five hB
  have hle := le_of_normalizes hS₀ hS₀4 hBc hS₀B
  obtain ⟨q, rfl⟩ := hd.2
  have hq : q ∈ Subgroup.normalizer (S₀ : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 := (Subgroup.mem_normalizer_iff.mp hd.1) (MulAut.conj s)
    rw [← map_mul, ← map_inv, ← map_mul] at h1
    exact h1
  have hNQ : Nat.card ↥(Subgroup.normalizer (S₀ : Set Q)) = 12 := hNorm p hp hp3 hp8 Q hQ S₀ hS₀
  obtain ⟨eB⟩ := hB
  set S₀' := S₀.subgroupOf B with hS₀'def
  have hS₀'4 : Nat.card S₀' = 4 := by
    rw [hS₀'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hS₀4]
  have hS₀' : IsSylowTwoOf S₀' ⊤ := by
    refine ⟨le_top, hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm, fun h2 => ?_⟩
    rw [show (S₀'.subgroupOf ⊤).index = S₀'.index from Subgroup.relIndex_top_right _] at h2
    have h3 := Subgroup.card_mul_index S₀'
    rw [hS₀'4, hBc] at h3
    omega
  have hNB : Nat.card ↥(Subgroup.normalizer (S₀' : Set ↥B)) = 12 :=
    hNorm 5 (by norm_num) (by norm_num) (Or.inr rfl) ↥B (isL2_five_of_alt5 eB) S₀' hS₀'
  have hNle : (Subgroup.normalizer (S₀' : Set ↥B)).map B.subtype ≤
      Subgroup.normalizer (S₀ : Set Q) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    by_cases hsB : s ∈ B
    · have h1 := (Subgroup.mem_normalizer_iff.mp hx) ⟨s, hsB⟩
      simpa [hS₀'def, Subgroup.mem_subgroupOf] using h1
    · constructor
      · intro hs
        exact absurd (hle hs) hsB
      · intro hs
        exfalso
        apply hsB
        have h1 : (x : Q) * s * (x : Q)⁻¹ ∈ B := hle hs
        have h2 := B.mul_mem (B.mul_mem (B.inv_mem x.2) h1) x.2
        simpa [mul_assoc] using h2
  have heq : (Subgroup.normalizer (S₀' : Set ↥B)).map B.subtype =
      Subgroup.normalizer (S₀ : Set Q) :=
    Subgroup.eq_of_le_of_card_ge hNle (by
      rw [Subgroup.card_map_of_injective B.subtype_injective, hNB, hNQ])
  have hqB : q ∈ B := by
    rw [← heq] at hq
    obtain ⟨x, -, rfl⟩ := hq
    exact x.2
  rw [mem_stabilizer_subgroup_iff]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hqB)

end L3312

end CFSG.Quasithin.H13
