module

public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.EmptyFaithful.S152He9R

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isPGroup {T P : Subgroup G} (hT : quasithinIsSylowTwo T) (hP : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  let T' : Sylow 2 G := hT.1.toSylow hT.2
  have h1 : Nat.card Q = Nat.card T' := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  calc Nat.card P ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = Nat.card T' := h1
    _ = Nat.card T := rfl

theorem normalizer_le_of_sylow {M Y T P O : Subgroup G}
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) (hU : IsUniqueM (Y ⊔ T) M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hPM : IsSylowTwoOf P M) (hO2 : IsPGroup 2 O) (hO1 : O ≠ ⊥)
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hPO : P ≤ Subgroup.normalizer (O : Set G)) :
    Subgroup.normalizer (O : Set G) ≤ M := by
  obtain ⟨x, hxM, hTx⟩ := F7.isSylowTwoOf_exists_conj_le hPM hTM hT2
  set O' : Subgroup G := O.map (MulAut.conj x).toMonoidHom with hO'
  have hN : Subgroup.normalizer (O' : Set G) = (Subgroup.normalizer (O : Set G)).map
      (MulAut.conj x).toMonoidHom := (Subgroup.map_equiv_normalizer_eq O (MulAut.conj x)).symm
  have hmem : ∀ g, g ∈ Subgroup.normalizer (O' : Set G) ↔ x⁻¹ * g * x ∈ Subgroup.normalizer (O : Set G) := by
    intro g
    rw [hN, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hTO : T ≤ Subgroup.normalizer (O' : Set G) := by
    intro t ht
    rw [hmem]
    obtain ⟨p, hp, hpt⟩ := hTx ht
    have : x⁻¹ * t * x = p := by
      rw [← hpt]
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hPO hp
  have hYO' : Y ≤ Subgroup.normalizer (O' : Set G) := by
    intro y hy
    rw [hmem]
    have hy' : x⁻¹ * y * x ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hMY (M.inv_mem hxM)) y).mp hy
      simpa [mul_assoc] using this
    exact hYO hy'
  have hO1' : O' ≠ ⊥ := by
    rwa [hO', Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x).injective]
  obtain ⟨M'', hM'', hNM''⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (O' : Set G)) ⟨O', hO1', hO2.map _, rfl⟩
  have hEq : M'' = M := hU.2 M'' ⟨hM'', (sup_le hYO' hTO).trans hNM''⟩
  have hNle : Subgroup.normalizer (O' : Set G) ≤ M := hEq ▸ hNM''
  intro g hg
  have h1 : x * g * x⁻¹ ∈ Subgroup.normalizer (O' : Set G) := by
    rw [hmem]
    simpa [mul_assoc] using hg
  have h2 := hNle h1
  have : g = x⁻¹ * (x * g * x⁻¹) * x := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hxM) h2) hxM

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem not_K₁_le_M : ¬ K₁ ≤ M := by
  intro hK
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    c.hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe c.hT.1).symm
  obtain ⟨t, ht, hπt⟩ := exists_not_mem_base c.wr.data hT2' c.hT.2.2
  have htH : (t : G) ∈ H := t.2
  have htT : (t : G) ∈ T := ht
  have hconj := c.wr.conj_eq₁ htH hπt
  have hK₂ : K₂ ≤ M := by
    intro y hy
    rw [← hconj] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact M.mul_mem (M.mul_mem (c.y.data.T_le htT) (hK hz)) (M.inv_mem (c.y.data.T_le htT))
  apply c.hH.2.1
  rw [← c.wr.sup_eq c.hT]
  exact sup_le (sup_le hK hK₂) c.y.data.T_le

theorem sylow_normalizer (hJ : thompsonJ T ≤ sOf T K₁) (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M)
    {O : Subgroup G} (hO2 : IsPGroup 2 O) (hO1 : O ≠ ⊥)
    (hYO : yOf152 T Mc M ≤ Subgroup.normalizer (O : Set G))
    (hKO : K₁ ≤ Subgroup.normalizer (O : Set G))
    (hSO : sOf T K₁ ≤ Subgroup.normalizer (O : Set G)) :
    IsSylowTwoOf (sOf T K₁) (Subgroup.normalizer (O : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPN, hSP⟩ := A4.exists_isSylowTwoOf_ge hSO c.S_pgroup
  suffices hPS : P = sOf T K₁ by rw [← hPS]; exact hPN
  by_contra hne'
  have hne : sOf T K₁ ≠ P := fun h => hne' h.symm
  have hcardT : Nat.card T = 2 * Nat.card (sOf T K₁) := by
    have h1 := Subgroup.card_mul_index ((sOf T K₁).subgroupOf T)
    have h2 : Nat.card ↥((sOf T K₁).subgroupOf T) = Nat.card ↥(sOf T K₁) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S_le_T)).toEquiv
    have h3 : ((sOf T K₁).subgroupOf T).index = 2 := c.wr.relIndex_S c.hT
    rw [h2, h3] at h1
    omega
  have hPcard : Nat.card P ≤ Nat.card T := card_le_of_isPGroup c.hs.qtfe.sylow hPN.2.1
  have hlt : Nat.card (sOf T K₁) < Nat.card P :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hSP hne)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSP
  have hSpos : 0 < Nat.card (sOf T K₁) := Nat.card_pos
  have hk2 : k = 2 := by
    have hle : Nat.card (sOf T K₁) * k ≤ Nat.card (sOf T K₁) * 2 := by
      rw [← hk]
      omega
    have hk_le : k ≤ 2 := Nat.le_of_mul_le_mul_left hle hSpos
    have hk_gt : 1 < k := by
      by_contra h
      push Not at h
      interval_cases k <;> omega
    omega
  have hcardP : Nat.card P = 2 * Nat.card (sOf T K₁) := by rw [hk, hk2]; ring
  have hidx : ((sOf T K₁).subgroupOf P).index = 2 := by
    have h1 := Subgroup.card_mul_index ((sOf T K₁).subgroupOf P)
    have h2 : Nat.card ↥((sOf T K₁).subgroupOf P) = Nat.card ↥(sOf T K₁) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
    rw [h2, hcardP] at h1
    have h3 : Nat.card ↥(sOf T K₁) * ((sOf T K₁).subgroupOf P).index =
        Nat.card ↥(sOf T K₁) * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hSpos h3
  have hnormal : ((sOf T K₁).subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx
  have hPS : P ≤ Subgroup.normalizer (sOf T K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).1 hnormal
  have hT1 : T ≠ ⊥ := c.hs.qtfe.ne_bot
  have hJT : thompsonJ (sOf T K₁) = thompsonJ T := B6.thompsonJ_eq_of_le hJ S_le_T
  have hPM : P ≤ M := by
    have h1 : P ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
      rw [← hJT]
      exact hPS.trans (normalizer_le_normalizer_thompsonJ _)
    exact (h1.trans (S1414.normalizer_thompsonJ_le_CGS c.hs.qtfe.sylow.1 hT1)).trans
      c.h1519.one_cgs
  have hTMsyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.y.data.T_le
  have hPsyl : IsSylowTwoOf P M := by
    refine ⟨hPM, hPN.2.1, ?_⟩
    have h1 := Subgroup.card_mul_index (P.subgroupOf M)
    have h2 := Subgroup.card_mul_index (T.subgroupOf M)
    have h3 : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    have h4 : Nat.card ↥(T.subgroupOf M) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.y.data.T_le).toEquiv
    have h5 : Nat.card P = Nat.card T := by omega
    rw [h3, h5] at h1
    rw [h4] at h2
    have hpos : 0 < Nat.card T := Nat.card_pos
    have : (P.subgroupOf M).index = (T.subgroupOf M).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [this]
    exact hTMsyl.2.2
  have hN : Subgroup.normalizer (O : Set G) ≤ M :=
    normalizer_le_of_sylow c.y.normal hU c.y.data.T_le c.hs.qtfe.sylow.1 hPsyl hO2 hO1 hYO
      (hPN.1)
  exact c.not_K₁_le_M (hKO.trans hN)

end Ctx15204

end CFSG.Quasithin.He9
