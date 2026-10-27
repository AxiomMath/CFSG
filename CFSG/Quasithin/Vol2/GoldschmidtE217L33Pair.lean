module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L33E9
public import CFSG.Quasithin.Vol2.GoldschmidtE217L33Aut

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.GH74.KGroups

namespace E217R4

theorem l33_pair
    {Y : Type} [Group Y] [Finite Y]
    {K T : Subgroup Y} (hKn : K.Normal) (hCK : Subgroup.centralizer (K : Set Y) = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hK : CFSG.GH74.E2.ShapeL33 ↥K) {v : Y} (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hvT : ∀ t ∈ T, t * v = v * t) :
    ∃ A T₀ : Subgroup Y, Nat.card A = 9 ∧ T₀ ≤ T ∧ T₀ ≤ Subgroup.normalizer (A : Set Y) ∧
      (∀ C : Subgroup Y, C ≤ A → T₀ ≤ Subgroup.normalizer (C : Set Y) → C = ⊥ ∨ C = A) ∧
      v ∈ T₀ ∧ ∀ a ∈ A, v * a * v⁻¹ * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨P, hP⟩ := exists_sylow_eq_subgroupOf_of_normal (hT.2.1.toSylow hTi) K
  have hPT : (P : Subgroup ↥K) = T.subgroupOf K := by
    rw [hP]
    rfl
  have hQ : IsPGroup 2 (T.subgroupOf K) := hPT ▸ P.isPGroup'
  have hQi : ¬ 2 ∣ (T.subgroupOf K).index := hPT ▸ P.not_dvd_index
  have hQcard : Nat.card (T.subgroupOf K) = 16 := by
    have h1 : Nat.card (T.subgroupOf K) = Nat.card (P : Subgroup ↥K) := by rw [← hPT]
    rw [h1, P.card_eq_multiplicity, L33.card_K e, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 351 by norm_num)]
  obtain ⟨s, hsQ, hs2, hsc, hα⟩ := eq_of_centralizes_sylow_L33 hK _ hQ hQi
  have hvα : MulAut.conjNormal v = MulAut.conj s := by
    refine hα _ ?_ (fun h => hv1 ?_) fun q hq => ?_
    · rw [← map_pow, pow_two, hv2, map_one]
    · have hc : v ∈ Subgroup.centralizer (K : Set Y) := fun k hk => by
        have := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : Y)) h
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        calc k * v = (v * k * v⁻¹) * v := by rw [this]
          _ = v * k := by group
      rwa [hCK, Subgroup.mem_bot] at hc
    · apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := hvT (q : Y) hq
      calc v * (q : Y) * v⁻¹ = (q : Y) * v * v⁻¹ := by rw [← this]
        _ = q := by group
  have hvs : v = (s : Y) := by
    have hc : (s : Y)⁻¹ * v ∈ Subgroup.centralizer (K : Set Y) := fun k hk => by
      have := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : Y)) hvα
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at this
      show k * ((s : Y)⁻¹ * v) = ((s : Y)⁻¹ * v) * k
      calc k * ((s : Y)⁻¹ * v) = (s : Y)⁻¹ * ((s : Y) * k * (s : Y)⁻¹) * v := by group
        _ = (s : Y)⁻¹ * (v * k * v⁻¹) * v := by rw [this]; rfl
        _ = ((s : Y)⁻¹ * v) * k := by group
    rw [hCK, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  obtain ⟨E, hE9, hEinv, hEN, hEirr⟩ := l33_e9 e hs2
  have hsT : (s : Y) ∈ T := hsQ
  refine ⟨E.map K.subtype, T ⊓ K, ?_, inf_le_left, ?_, ?_, ⟨hvs ▸ hsT, hvs ▸ s.2⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hE9
  · intro c hc
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype
      (hEN ⟨c, hc.2⟩ (hsc ⟨c, hc.2⟩ hc.1)))
  · intro C hCA hCN
    have hCK' : C ≤ K := hCA.trans (Subgroup.map_subtype_le E)
    set F : Subgroup ↥K := C.comap K.subtype with hF
    have hFE : F ≤ E := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hCA hx
      rwa [← Subtype.ext hyx]
    have hCF : F.map K.subtype = C := by
      rw [hF, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right]
      exact hCK'
    have hdvd : Nat.card F ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hFE
    have hpos : 0 < Nat.card F := Nat.card_pos
    have hcases : ∀ n : ℕ, 0 < n → n ∣ 9 → n = 1 ∨ n = 3 ∨ n = 9 := by
      intro n hn hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases n <;> omega
    rcases hcases _ hpos hdvd with h | h | h
    · left
      rw [← hCF, Subgroup.eq_bot_of_card_eq F h, Subgroup.map_bot]
    · exfalso
      have := hEirr F hFE h _ (fun q hq => hsc q hq) (fun q hq => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        exact Subgroup.mem_normalizer_iff.1 (hCN ⟨hq, q.2⟩) (x : Y))
      omega
    · right
      have hFE' : F = E := Subgroup.eq_of_le_of_card_ge hFE (by omega)
      rw [← hCF, hFE']
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have h := congrArg (Subtype.val : ↥K → Y) (hEinv x hx)
    have h' : (s : Y) * (x : Y) * (s : Y)⁻¹ = (x : Y)⁻¹ := h
    rw [hvs]
    show (s : Y) * (x : Y) * (s : Y)⁻¹ * (x : Y) = 1
    rw [h', inv_mul_cancel]

end E217R4

end CFSG.Quasithin
