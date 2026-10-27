module

public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

theorem comap_pPrimeCore_eq {L : Subgroup H} (hL : IsSubnormal L ⊤)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣ 3)
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (CFSG.pPrimeCore 3 H).comap L.subtype = CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set N := (CFSG.pPrimeCore 3 H).comap L.subtype
    have hNn : N.Normal := Subgroup.Normal.comap CFSG.pPrimeCore_normal _
    set M := N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    have hMn : M.Normal := Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
    have hNc : Nat.card N ∣ Nat.card (CFSG.pPrimeCore 3 H) := by
      have : N.map L.subtype ≤ CFSG.pPrimeCore 3 H := Subgroup.map_comap_le _ _
      rw [← Subgroup.card_map_of_injective L.subtype_injective]
      exact Subgroup.card_dvd_of_le this
    have hMc : Nat.Coprime 3 (Nat.card M) :=
      CFSG.pPrimeCore_coprime_card.coprime_dvd_right ((Subgroup.card_map_dvd _ _).trans hNc)
    have hMt : M ≠ ⊤ := by
      intro ht
      rw [ht, Subgroup.card_top] at hMc
      exact absurd (Nat.Coprime.eq_one_of_dvd hMc h3) (by norm_num)
    have hMZ := Ch11.SecA.le_center_of_normal_ne_top hQ hMt
    have hMb : M = ⊥ := by
      have h1 : Nat.card M ∣ 3 := (Subgroup.card_dvd_of_le hMZ).trans hZ
      exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hMc.symm h1)
    intro x hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ M := ⟨x, hx, rfl⟩
    rwa [hMb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  · intro x hx
    have h1 : (x : H) ∈ pCoreOf 2 L := by
      exact ⟨x, hx, rfl⟩
    have h2 : (x : H) ∈ pCoreOf 2 (⊤ : Subgroup H) := A4.pCoreOf_le_of_subnormal 2 hL h1
    have hP : pCoreOf 2 (⊤ : Subgroup H) ≤ CFSG.pPrimeCore 3 H := by
      have hn : (pCoreOf 2 (⊤ : Subgroup H)).Normal := by
        constructor
        intro n hn g
        exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤
            (Subgroup.mem_top g)) n).mp hn
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (⊤ : Subgroup H))
      refine le_sSup ⟨hn, ?_⟩
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact hP h2

omit [Finite H] in
theorem starImage_equiv' {L : Subgroup H}
    (hO : (CFSG.pPrimeCore 3 H).comap L.subtype = CFSG.pCore 2 ↥L) :
    Nonempty (↥(starImage 3 L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  set f : ↥L →* PStar 3 H := (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp L.subtype with hf
  have hker : f.ker = CFSG.pCore 2 ↥L := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hO]
  have hrange : f.range = starImage 3 L := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange f).symm).trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
