module

public import CFSG.Quasithin.Vol2.Ch10SecE9N
public import CFSG.Quasithin.Vol2.Ch10SecE9O
public import CFSG.Quasithin.Vol2.Ch10SecE9M

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

omit [Finite G] in
theorem le_pRank_of_card' {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H] (B : Subgroup H)
    (hB : IsElementaryAbelian p B) {k : ℕ} (hk : Nat.card B = p ^ k) : k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨B, hB, hk⟩
  rintro r ⟨B', -, hB'⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B' := hB'.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B'

theorem false_of_normalizes_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E)
    (hD2 : ParData2 K E) {y : G} (hy3 : orderOf y = 3)
    (hyT : y ∈ Subgroup.normalizer (T1 T L : Set G))
    (hyX : y ∈ Subgroup.normalizer (XOf T L Ψ A : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXL0 := XOf_le_fsuL0 h hD
  set X := XOf T L Ψ A with hXdef
  set R := pCoreOf 2 X with hR
  have hyn : y ∉ X := fun hy =>
    not_mem_sup_of_orderOf_three h hy3 hyT (Subgroup.mem_sup_left (hXL0 hy))
  have hcomm : ∀ x ∈ X, ∀ x' ∈ X, x * x' * x⁻¹ * x'⁻¹ ∈ R := fun x hx x' hx' =>
    commutator_le_pCoreOf h hD (Subgroup.commutator_mem_commutator hx hx')
  obtain ⟨B, hBH, hBA, k, hk3, hcardB⟩ := exists_elemAbelian_of_centralizes
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) (relIndex_XOf h hD)
    (fun x hx => pow_three_mem h hD hx) hcomm hyX
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX) hy3 hyn
    (fun x hx => conj_mem_pCoreOf_of_normalizes h hD hD2 hy3 hyT hyX hx)
  set N := Subgroup.normalizer (R : Set G) with hN
  have hBN : B ≤ N := hBH.trans (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    (Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX)))
  have hR1 : R ≠ ⊥ := by
    intro hR0
    rw [hR] at hR0
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X), relIndex_XOf h hD, hR0,
      Subgroup.card_bot] at h1
    have h2 : Nat.card (K.prod K) ≤ Nat.card X := by
      rw [← imgIn_XOf h hD]
      calc Nat.card (imgIn Ψ X) ≤ Nat.card (X.subgroupOf (fsuL0 T L)) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (X.subgroupOf (fsuL0 T L)) Ψ)
        _ = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL0).toEquiv
    rw [card_prod_self, hD.cardK] at h2
    omega
  have hRN : R ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hON : pCoreOf 2 N ≠ ⊥ := fun h0 => hR1 (eq_bot_iff.mpr (h0 ▸ hRN))
  have := h.hyp.fsu.simple
  have hKl : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  have hrank := (hKl N hON).1 3 Nat.prime_three (by norm_num)
  have hBA' : IsElementaryAbelian 3 ↥(B.subgroupOf N) := IsElementaryAbelian.subgroupOf hBN
  have hcard' : Nat.card ↥(B.subgroupOf N) = 3 ^ k := by
    rw [← hcardB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have := le_pRank_of_card' (by norm_num) (B.subgroupOf N) hBA' hcard'
  omega

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
