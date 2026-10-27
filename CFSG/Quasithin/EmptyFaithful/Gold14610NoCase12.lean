module

public import CFSG.Quasithin.EmptyFaithful.Gold14610NoCase12Lift
public import CFSG.Quasithin.EmptyFaithful.Gold14610NoCase12TwoCases
public import CFSG.Quasithin.EmptyFaithful.Gold14610Props

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace Gold14610

namespace NC12

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_of_imgMod3 {I I₁ I₂ : Subgroup G} (h : F6.IsGoldschmidtTripleIn I I₁ I₂)
    (h1 : pCoreOf 2 (imgMod3 I I₁) = ⊥) (h2 : pCoreOf 2 (imgMod3 I I₂) = ⊥) :
    pCoreOf 2 I₁ = pCoreOf 2 I₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI₁ : I₁ ≤ I := h.1 ▸ le_sup_left
  have hI₂ : I₂ ≤ I := h.1 ▸ le_sup_right
  have ht := h.subgroupOf
  have key : ∀ {J' : Subgroup ↥I}, J' ⊓ CFSG.pPrimeCore 3 ↥I = Open.pCore 2 ↥I →
      Open.pCore 2 ↥I ≤ J' →
      pCoreOf 2 (J'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) = ⊥ →
      pCoreOf 2 J' = Open.pCore 2 ↥I := by
    intro J' hJX hQJ hJ
    apply le_antisymm
    · have hle : (pCoreOf 2 J').map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ≤
          pCoreOf 2 (J'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) :=
        le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono (pCoreOf_le 2 J'))
          ((Subgroup.map_mono (le_normalizer_pCoreOf 2 J')).trans
            (Subgroup.le_normalizer_map _))
          ((pCoreOf_isPGroup 2 J').map _)
      rw [hJ, le_bot_iff] at hle
      have hX : pCoreOf 2 J' ≤ CFSG.pPrimeCore 3 ↥I := by
        intro x hx
        have : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) x ∈
            (pCoreOf 2 J').map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) :=
          Subgroup.mem_map_of_mem _ hx
        rw [hle, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).mp this
      rw [← hJX]
      exact le_inf (pCoreOf_le 2 J') hX
    · refine le_pCoreOf_of_le_normalizer 2 hQJ ?_ (CFSG.LieType.BorelTits.pCore_isPGroup 2)
      exact le_top.trans (Subgroup.normalizer_eq_top_iff.mpr
        (CFSG.LieType.BorelTits.pCore_normal 2)).ge
  have e₁ := key (J' := I₁.subgroupOf I) (F6.inf_pPrimeCore_eq_pCore_left ht)
    (ht.pCore_le_inf.trans inf_le_left) h1
  have e₂ := key (J' := I₂.subgroupOf I) (F6.inf_pPrimeCore_eq_pCore_right ht)
    (ht.pCore_le_inf.trans inf_le_right) h2
  rw [← F6.map_pCoreOf_subgroupOf hI₁, ← F6.map_pCoreOf_subgroupOf hI₂, e₁, e₂]

end NC12

theorem gold14610NoCase12_proved : Gold14610NoCase12 := by
  intro G _ _ T M H u I I₂ hF hS hY h
  have hI₁ : i1Of1469 T M I ≤ I := le_sup_left.trans h.1.le
  have hI₂ : I₂ ≤ I := le_sup_right.trans h.1.le
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, h1, h2, -⟩
    exact hF.c2 (NC12.pCoreOf_eq_of_imgMod3 h h1 h2)
  · rintro ⟨-, h1, h2, -⟩
    exact hF.c2 (NC12.pCoreOf_eq_of_imgMod3 h h2 h1)
  · intro hC2
    have hTM : T ≤ M := hF.setting.hyp.m_max.1.2
    have hlI : lI T M I ≤ I := ((oTwoUpper_le _).trans inf_le_right)
    have hI₁M : i1Of1469 T M I ≤ M := by
      refine sup_le ?_ (inf_le_left.trans hTM)
      exact ((oTwoUpper_le _).trans inf_le_left).trans (yOfL22_le T M)
    rcases h.goldschmidt_mod_pPrimeCore with ⟨hinf, hA, -⟩ | ⟨e₁, e₂, -⟩
    · have hT3 := hA.toIsGoldschmidtTriple
      obtain ⟨Pb, hPb, hP₂, hP₁⟩ := NC12.exists_normal_of_isF618CaseTwo hT3 hC2
      have hPbn : Pb.Normal := hPb
      let P : Subgroup G := (Pb.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).map I.subtype
      have hPI : P ≤ I := Subgroup.map_subtype_le _
      have hnorm : ∀ g ∈ I, ∀ z ∈ P, g * z * g⁻¹ ∈ P := by
        rintro g hg z ⟨y, hy, rfl⟩
        exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
          (inferInstance : (Pb.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).Normal).conj_mem
            y hy ⟨g, hg⟩, rfl⟩
      have hI₁N : i1Of1469 T M I ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
        B6.mem_normalizer_of_forall_mem (hnorm g (hI₁ hg)) fun z hz => by
          simpa using hnorm g⁻¹ (I.inv_mem (hI₁ hg)) z hz
      have hc3 := hF.c3 P hPI hI₁N
      have hc3' : (lI T M I).subgroupOf I ≤ Pb.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∨
          Pb.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ≤ M.subgroupOf I := by
        rcases hc3 with hl | hr
        · left
          intro x hx
          obtain ⟨y, hy, hyx⟩ := hl (show (x : G) ∈ lI T M I from hx)
          have : y = x := Subtype.ext hyx
          exact this ▸ hy
        · right
          intro y hy
          exact (hr (Subgroup.mem_map_of_mem I.subtype hy)).1
      have hlift := NC12.lift_le (CFSG.pPrimeCore 3 ↥I) (J₁ := (i1Of1469 T M I).subgroupOf I)
        (J₂ := I₂.subgroupOf I) (L := (lI T M I).subgroupOf I) (T' := (T ⊓ I).subgroupOf I)
        (W := M.subgroupOf I) (Subgroup.subgroupOf_sup hlI inf_le_right)
        (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm) hT3 hinf hP₂ hP₁
        (fun x hx => hI₁M hx) hc3'
      have hI₂M : I₂ ≤ M := fun x hx => hlift (show (⟨x, hI₂ hx⟩ : ↥I) ∈ I₂.subgroupOf I from hx)
      exact hF.hI.1.2.2 ((le_of_eq h.1.symm).trans (sup_le hI₁M hI₂M))
    · exact hF.c2 (by
        rw [← F6.map_pCoreOf_subgroupOf hI₁, ← F6.map_pCoreOf_subgroupOf hI₂, e₁, e₂])

end Gold14610

end CFSG.Quasithin
