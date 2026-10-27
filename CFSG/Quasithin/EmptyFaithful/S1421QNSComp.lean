module

public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421NS

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_normal {X : Type} [Group X] [Finite X] (A L : Subgroup X)
    [L.Normal] :
    Nat.card (A ⊔ L : Subgroup X) * Nat.card (A ⊓ L : Subgroup X) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

omit [Finite G] in
theorem map_conj_eq_iff {t : G} {K : Subgroup G} :
    K.map (MulAut.conj t).toMonoidHom = K ↔ t ∈ Subgroup.normalizer (K : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

omit [Finite G] in
theorem map_conj_mem_cComp_of_mem {H L : Subgroup G} (hL : L ∈ cComp H) {t : G} (ht : t ∈ H) :
    L.map (MulAut.conj t).toMonoidHom ∈ cComp H := by
  have h := cComp_map_mulEquiv (MulAut.conj t) hL
  rwa [map_conj_eq_iff.mpr (Subgroup.le_normalizer ht)] at h

theorem sq_dvd_card_of_conj_component {H K K1 : Subgroup G} {t : G}
    (hK1 : K1 ∈ cComp H) (ht : t ∈ H) (htn : t ∉ Subgroup.normalizer (K1 : Set G))
    (hK1K : K1 ≤ K) (hK : H ≤ Subgroup.normalizer (K : Set G))
    (hrad : solvRad K1 ≤ pCoreOf 2 K1)
    {m : ℕ} (hm : Odd m) (hmK1 : m ∣ Nat.card K1) : m ^ 2 ∣ Nat.card K := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K1' : Subgroup G := K1.map (MulAut.conj t).toMonoidHom with hK1'def
  have hK1' : K1' ∈ cComp H := map_conj_mem_cComp_of_mem hK1 ht
  have hne : K1 ≠ K1' := fun h => htn (map_conj_eq_iff.mp h.symm)
  have hK1'K : K1' ≤ K := by
    have h := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hK1K
    rwa [map_conj_eq_iff.mpr (hK ht)] at h
  have hn1 : K1' ≤ Subgroup.normalizer (K1 : Set G) := le_normalizer_of_mem_cComp hK1 hK1'
  have hn2 : K1 ≤ Subgroup.normalizer (K1' : Set G) := le_normalizer_of_mem_cComp hK1' hK1
  have hcard : Nat.card K1' = Nat.card K1 :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hprod := card_sup_mul_card_inf_of_le_normalizer hn1
  have hD : Nat.card (K1 ⊔ K1' : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le (sup_le hK1K hK1'K)
  have hWnorm : K1 ≤ Subgroup.normalizer ((K1 ⊓ K1' : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hn2 hx⟩
  have hWN : ((K1 ⊓ K1').subgroupOf K1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hWnorm
  have hWrad : K1 ⊓ K1' ≤ solvRad K1 := by
    rcases normal_eq_top_or_map_le_solvRad hK1 ((K1 ⊓ K1').subgroupOf K1) with h | h
    · exfalso
      have hle : K1 ≤ K1 ⊓ K1' := Subgroup.subgroupOf_eq_top.mp h
      exact hne (Subgroup.eq_of_le_of_card_ge (hle.trans inf_le_right) hcard.le)
    · rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h
  have hWp : IsPGroup 2 (K1 ⊓ K1' : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K1).to_le (hWrad.trans hrad)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp hWp
  have hsq : m ^ 2 ∣ Nat.card (K1 ⊔ K1' : Subgroup G) * 2 ^ b := by
    have h1 : m ^ 2 ∣ Nat.card K1 * Nat.card K1' := by
      rw [hcard, ← pow_two]
      exact pow_dvd_pow_of_dvd hmK1 2
    rw [← hprod, hb] at h1
    exact h1
  have hcop : Nat.Coprime (m ^ 2) (2 ^ b) :=
    Nat.Coprime.pow_right b (Nat.Coprime.pow_left 2 (Nat.coprime_two_right.mpr hm))
  exact (hcop.dvd_of_dvd_mul_right hsq).trans hD

end S1421NS

end CFSG.Quasithin
