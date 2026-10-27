module

public import CFSG.Quasithin.Recognition.Stroth.BenderSylow
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.Quasithin.Recognition.GoldschmidtF112ROmega4

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_two_Kb {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    ∃ Kb : Subgroup G, Kb ≤ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) ∧
      Kb ≤ bigB L1 L2 S ∧ IsCyclic ↥Kb ∧ Nat.card ↥Kb = 2 ^ m - 1 ∧
      Kb ⊓ pCoreOf 2 (L2 ⊔ S) = ⊥ ∧
      (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) = S ⊔ Kb ∧
      (∀ d ∈ Kb, Odd (orderOf d)) := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  obtain ⟨D, hDcart, -, hDsup⟩ := F1.exists_cartan hF.1.h2.sylow
  have hDL2 : D ≤ L2 := hDcart.1.trans (F1.borelOf_le L2 S)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    le_sup_right.trans hS2.symm.le
  have hH_eq : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have hS_le : S ≤ L2 ⊔ Q2 L1 L2 S :=
      (le_of_eq hS2).trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    exact le_antisymm (sup_le le_sup_left hS_le)
      (sup_le le_sup_left (hQ2S.trans le_sup_right))
  have hP2NQ2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hbigN2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le (sup_le hF.1.h2.borel_le
      ((F1.borelOf_le L2 S).trans Subgroup.le_normalizer)) hF.1.h2.normalizes
  have hQ2N_L2 : Q2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)).trans
      (sup_le Subgroup.le_normalizer hbigN2)
  have hborelN : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) := by
    have h1 : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
      F1.borelOf_le_normalizer L2 S
    have h2 : borelOf L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      ((F1.borelOf_le L2 S).trans le_sup_left).trans hP2NQ2
    have h3 := F1.le_normalizer_sup h1 h2
    rwa [hS2.symm] at h3
  have hNHS : (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) =
      borelOf L2 S ⊔ Q2 L1 L2 S := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxH, hxN⟩
      rw [hH_eq] at hxH
      obtain ⟨l, hl, q, hq, hxq⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N_L2).mp hxH
      have hqN : q ∈ Subgroup.normalizer (S : Set G) :=
        Subgroup.le_normalizer (hQ2S hq)
      have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
        have hl_eq : l = x * q⁻¹ := by rw [hxq]; group
        rw [hl_eq]
        exact Subgroup.mul_mem (Subgroup.normalizer (S : Set G)) hxN
          (Subgroup.inv_mem (Subgroup.normalizer (S : Set G)) hqN)
      have hlNinf : l ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff] at hlN ⊢
        intro y
        constructor
        · rintro ⟨hyS, hyL⟩
          exact ⟨(hlN y).mp hyS, L2.mul_mem (L2.mul_mem hl hyL) (L2.inv_mem hl)⟩
        · rintro ⟨hyS, hyL⟩
          have hyS' : y ∈ S := (hlN y).mpr hyS
          have hyL' : y ∈ L2 := by
            have h := L2.mul_mem (L2.mul_mem (L2.inv_mem hl) hyL) hl
            simpa [mul_assoc] using h
          exact ⟨hyS', hyL'⟩
      have hlB : l ∈ borelOf L2 S := Subgroup.mem_inf.mpr ⟨hl, hlNinf⟩
      have hx : x = l * q := hxq
      rw [hx]
      exact Subgroup.mul_mem (borelOf L2 S ⊔ Q2 L1 L2 S)
        (Subgroup.mem_sup_left hlB) (Subgroup.mem_sup_right hq)
    · refine sup_le ?_ ?_
      · exact le_inf ((F1.borelOf_le L2 S).trans le_sup_left) hborelN
      · exact le_inf (hQ2S.trans le_sup_right)
          (hQ2S.trans Subgroup.le_normalizer)
  have hKbsup : (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) = S ⊔ D := by
    rw [hNHS, ← hDsup]
    conv_rhs => rw [hS2]
    ac_rfl
  let π : ↥L2 →* oTwoQuot ↥L2 := QuotientGroup.mk' (pCore 2 ↥L2)
  let D' : Subgroup ↥L2 := D.subgroupOf L2
  let Dbar : Subgroup (oTwoQuot ↥L2) := D'.map π
  let Sbar : Subgroup (oTwoQuot ↥L2) := ((S ⊓ L2).subgroupOf L2).map π
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  have hSbarSyl : IsSylowTwoOf Sbar ⊤ := by
    have hrel : Sbar.relIndex ⊤ = Sbar.index := by
      have h := Subgroup.relIndex_mul_index (H := Sbar) (K := ⊤) le_top
      rwa [Subgroup.index_top, mul_one] at h
    refine ⟨le_top, hmapB.1, ?_⟩
    show ¬ 2 ∣ Sbar.relIndex ⊤
    rw [hrel]
    exact hmapB.2.1
  have hDbarN : Dbar ≤ Subgroup.normalizer (Sbar : Set (oTwoQuot ↥L2)) := by
    calc Dbar ≤ ((borelOf L2 S).subgroupOf L2).map π :=
          Subgroup.map_mono (Subgroup.subgroupOf_mono L2 hDcart.1)
      _ = Subgroup.normalizer (Sbar : Set (oTwoQuot ↥L2)) := by
          simpa [Sbar, π] using hmapB.2.2
  have hcD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL2).toEquiv
  have hD'odd : Odd (Nat.card D') := hcD' ▸ hDcart.2.1
  have hDbarOdd : Odd (Nat.card Dbar) :=
    hD'odd.of_dvd_nat (Subgroup.card_map_dvd D' π)
  have hDbarInf : Dbar ⊓ Sbar = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hmapB.1
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hDbarOdd)
  have hDbarSup : Dbar ⊔ Sbar = Subgroup.normalizer (Sbar : Set (oTwoQuot ↥L2)) := by
    calc Dbar ⊔ Sbar
        = (D.subgroupOf L2).map π ⊔ ((S ⊓ L2).subgroupOf L2).map π := rfl
      _ = ((D.subgroupOf L2 ⊔ (S ⊓ L2).subgroupOf L2) : Subgroup ↥L2).map π :=
          (Subgroup.map_sup _ _ _).symm
      _ = (((S ⊓ L2).subgroupOf L2 ⊔ D.subgroupOf L2) : Subgroup ↥L2).map π := by
          rw [sup_comm]
      _ = ((borelOf L2 S).subgroupOf L2).map π := by
          rw [← Subgroup.subgroupOf_sup (A := S ⊓ L2) (A' := D)
            inf_le_right hDL2, hDsup]
      _ = Subgroup.normalizer (Sbar : Set (oTwoQuot ↥L2)) := by
          simpa [Sbar, π] using hmapB.2.2
  obtain ⟨hDbarCyc, hDbarCard⟩ :=
    CFSG.Quasithin.H13.l2TorusFact (oTwoQuot ↥L2) m hm
      (lieModel_of_isL2Quot hm hL2) Sbar Dbar hSbarSyl hDbarN hDbarInf hDbarSup
  have hDP : D' ⊓ pCore 2 ↥L2 = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L2))
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hD'odd)
  have hinj : Function.Injective (π.comp D'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : ↥L2) ∈ D' ⊓ pCore 2 ↥L2 := ⟨x.2, hx⟩
    rw [hDP, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  have hrange : (π.comp D'.subtype).range = Dbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eD : ↥D ≃* ↥Dbar :=
    ((Subgroup.subgroupOfEquivOfLe hDL2).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hrange)
  have hDcyc : IsCyclic ↥D :=
    isCyclic_of_surjective eD.symm.toMonoidHom eD.symm.surjective
  have hDcard : Nat.card ↥D = 2 ^ m - 1 := by
    rw [Nat.card_congr eD.toEquiv, hDbarCard]
  have hDinfP : D ⊓ pCoreOf 2 (L2 ⊔ S) = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_card).mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L2 ⊔ S))
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hDcart.2.1)
  refine ⟨D, ?_, ?_, hDcyc, hDcard, hDinfP, hKbsup, ?_⟩
  · exact hDcart.1.trans
      ((le_sup_left : borelOf L2 S ≤ borelOf L2 S ⊔ Q2 L1 L2 S).trans
        (le_of_eq hNHS.symm))
  · exact hDcart.1.trans
      ((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left)
  · intro d hd
    exact hDcart.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hd)

end CFSG.Quasithin.Stroth
