module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

open CFSG.Quasithin.RonanE43 in
theorem exists_permutes_three_of_lift {Y : Type} [Group Y] [Finite Y] {K S Z : Subgroup Y}
    [hK : K.Normal] [hZn : Z.Normal] (hKidx : ∃ a : ℕ, K.index = 2 ^ a)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hZK : Z ≤ K) (hZ3 : Nat.card Z = 3)
    (hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z) (h9 : ∀ x ∈ K, x ^ 3 ∈ Z → x ^ 3 = 1)
    {Hb : Subgroup (Y ⧸ Z)} (hSHb : S.map (QuotientGroup.mk' Z) ≤ Hb)
    (hHb : Nat.card Hb = 3 * Nat.card S) :
    ∃ X : Subgroup Y, X ≤ K ∧ X ≤ Hb.comap (QuotientGroup.mk' Z) ∧ Nat.card X = 3 ∧
      Permutes X S ∧ X ⊓ Z = ⊥ ∧ Nat.card ↥(X ⊔ S) = 3 * Nat.card S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hS2 : IsPGroup 2 S := hS.2.1
  set H : Subgroup Y := Hb.comap (QuotientGroup.mk' Z) with hHdef
  have hSH : S ≤ H := fun s hs => hSHb (Subgroup.mem_map_of_mem _ hs)
  have hZH : Z ≤ H := fun z hz => by
    show QuotientGroup.mk' Z z ∈ Hb
    rw [show QuotientGroup.mk' Z z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact Hb.one_mem
  have hHc : Nat.card H = 9 * Nat.card S := by
    rw [hHdef, card_comap_of_surjective _ hπ, hker, hZ3, hHb]
    ring
  set K' : Subgroup Y := H ⊓ K with hK'def
  have hKS : K ⊔ S = ⊤ := by
    have hidx : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
    exact CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top K hKidx (hS2.toSylow hidx)
  have hKnorm : ∀ L : Subgroup Y, L ≤ Subgroup.normalizer (K : Set Y) := fun L x _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (hKnorm H)
  have h2 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (hKnorm S)
  have hHK : H ⊔ K = ⊤ := by
    rw [eq_top_iff, ← hKS]
    exact sup_le le_sup_right (hSH.trans le_sup_left)
  have hK'c : Nat.card K' = 9 * Nat.card ↥(S ⊓ K) := by
    rw [hHK, Subgroup.card_top, hHc] at h1
    rw [show S ⊔ K = ⊤ by rw [sup_comm]; exact hKS, Subgroup.card_top] at h2
    have hY0 : 0 < Nat.card Y := Nat.card_pos
    have h3 : Nat.card Y * Nat.card K' = Nat.card Y * (9 * Nat.card ↥(S ⊓ K)) := by
      calc Nat.card Y * Nat.card K' = 9 * Nat.card S * Nat.card K := h1
        _ = 9 * (Nat.card S * Nat.card K) := by ring
        _ = 9 * (Nat.card Y * Nat.card ↥(S ⊓ K)) := by rw [h2]
        _ = Nat.card Y * (9 * Nat.card ↥(S ⊓ K)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hY0 h3
  have hm3 : ¬ 3 ∣ Nat.card ↥(S ⊓ K) := by
    obtain ⟨k, hk⟩ := (hS2.to_le inf_le_left).exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hZK' : Z ≤ K' := le_inf hZH hZK
  have hK'K : K' ≤ K := inf_le_right
  have hZT : S ≤ Subgroup.normalizer (Z : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]; exact le_top
  have hTK' : S ≤ Subgroup.normalizer (K' : Set Y) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hsH : s ∈ H := hSH hs
    constructor
    · rintro ⟨hxH, hxK⟩
      exact ⟨H.mul_mem (H.mul_mem hsH hxH) (H.inv_mem hsH), hK.conj_mem x hxK s⟩
    · rintro ⟨hxH, hxK⟩
      have e1 : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      refine ⟨?_, ?_⟩
      · rw [e1]
        exact H.mul_mem (H.mul_mem (H.inv_mem hsH) hxH) hsH
      · rw [e1]
        have := hK.conj_mem _ hxK s⁻¹
        simpa using this
  obtain ⟨C, hCK', hCZ, hCsup, hCn, hC2⟩ := exists_invariant_complement hZK' hZ3
    (fun z hz k hk => hZc z hz k (hK'K hk)) hZT hTK' hS2 hK'c hm3
    (fun x hx hx3 => h9 x (hK'K hx) hx3)
  have hCc : Nat.card C = 3 * Nat.card ↥(S ⊓ K) := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C) (K := Z) (by rw [Subgroup.normalizer_eq_top_iff.mpr hZn]; exact le_top)
    rw [hCsup, hCZ, Subgroup.card_bot, mul_one, hK'c, hZ3] at h
    omega
  have hSKC : S ⊓ K ≤ C := by
    intro x hx
    have hxK' : x ∈ K' := ⟨hSH hx.1, hx.2⟩
    obtain ⟨n, hn⟩ := hS2 ⟨x, hx.1⟩
    exact hC2 x hxK' n (by simpa using congrArg Subtype.val hn)
  have hSC : S ⊓ C = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ (hCK'.trans hK'K)) (le_inf inf_le_left hSKC)
  have hH'c : Nat.card ↥(S ⊔ C) = 3 * Nat.card S := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hCn
    rw [hSC, hCc] at h
    have hm0 : 0 < Nat.card ↥(S ⊓ K) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hm0 (by rw [h]; ring)
  obtain ⟨X, hXH', hXK, hXc, -, hXsup, hXP⟩ := exists_permutes_of_overgroup hK hKidx hS2
    (le_sup_left : S ≤ S ⊔ C) (p := 3) (n := 1) (by norm_num) (by rw [hH'c]; ring)
  refine ⟨X, hXK, hXH'.trans (sup_le hSH (hCK'.trans inf_le_left)), by rw [hXc]; norm_num,
    hXP, ?_, by rw [hXsup, hH'c]⟩
  by_contra hne
  have hXZle : X ≤ Z := by
    have hc : Nat.card ↥(X ⊓ Z) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : X ⊓ Z ≤ X)
      rwa [hXc, pow_one] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hc with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
    · have : X ⊓ Z = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hXc, pow_one])
      rw [← this]
      exact inf_le_right
  have hXZ : X = Z := Subgroup.eq_of_le_of_card_ge hXZle (by rw [hZ3, hXc, pow_one])
  have hZSC : Z ≤ S ⊔ C := hXZ ▸ hXH'
  have hK'le : K' ≤ S ⊔ C := by
    rw [← hCsup]
    exact sup_le le_sup_right hZSC
  have hle : S ⊔ K' ≤ S ⊔ C := sup_le le_sup_left hK'le
  have h3 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hTK'
  have hSK'inf : S ⊓ K' = S ⊓ K := by
    rw [hK'def, ← inf_assoc, inf_eq_left.mpr hSH]
  rw [hSK'inf, hK'c] at h3
  have hm0 : 0 < Nat.card ↥(S ⊓ K) := Nat.card_pos
  have hSK'c : Nat.card ↥(S ⊔ K') = 9 * Nat.card S :=
    Nat.eq_of_mul_eq_mul_right hm0 (by rw [h3]; ring)
  have h4 := Subgroup.card_le_of_le hle
  rw [hSK'c, hH'c] at h4
  have hS0 : 0 < Nat.card S := Nat.card_pos
  omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
