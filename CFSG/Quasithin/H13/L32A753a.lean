module

public import CFSG.Quasithin.H13.L32ASk3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace L32A

variable {G : Type} [Group G] [Finite G]

structure Ctx753 (T L V K : Subgroup G) : Prop where
  hyp : Hyp147 G T L V
  setting : Setting147 G T L V (hz T V)
  cComp_eq : cComp (hz T V) = {K}
  eq_sup : hz T V = K ⊔ T
  conjClosure_eq : conjClosure V (hz T V) = fsuU T V
  comm_eq : fsuU T V = ⁅fsuU T V, K⁆
  psu : IsPSU 3 3 1 (cStar K)
  f918 : HypF918 T V L (fsuV1 T V) V (hz T V) K

namespace Ctx753

variable {T L V K : Subgroup G}

theorem mem_cComp (C : Ctx753 T L V K) : K ∈ cComp (hz T V) := by
  rw [C.cComp_eq]
  rfl

theorem le_normalizer (C : Ctx753 T L V K) : hz T V ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_cComp_eq C.cComp_eq

theorem le_hz (C : Ctx753 T L V K) : K ≤ hz T V :=
  C.eq_sup ▸ le_sup_left

theorem T_le (C : Ctx753 T L V K) : T ≤ hz T V :=
  C.eq_sup ▸ le_sup_right

theorem isPGroup_T (C : Ctx753 T L V K) : IsPGroup 2 T :=
  C.hyp.fsu.sylow.1

theorem kz_eq (C : Ctx753 T L V K) : kz T V = K :=
  oTwoUpper_eq_of_cComp_eq C.cComp_eq C.eq_sup C.isPGroup_T

theorem hF98 (C : Ctx753 T L V K) : HypF98 T V L (fsuV1 T V) V (hz T V) :=
  C.f918.toHypF98

theorem card_V1 (C : Ctx753 T L V K) : Nat.card (fsuV1 T V) = 2 :=
  C.hF98.toHypF91.card_V₁

theorem exists_not1471 (C : Ctx753 T L V K) (h38 : Lemma14_7_38) :
    ∃ (γ γ' : F8.Geom T L (hz T V)) (g h : ↥((L ⊔ T) ⊔ hz T V)),
      Not1471 T L V (hz T V) γ γ' g h := by
  obtain ⟨γ, γ', g, s⟩ := C.hF98.exists_F8Setup
  exact L32A.exists_not1471 C.hF98 s (h38 G T L V (hz T V) C.setting γ γ' g s)

end Ctx753

theorem ctx753_of (h30 : Lemma14_7_30) (h48 : Lemma14_7_48) (h52 : Thm14_7_52)
    {T L V H K : Subgroup G} (S : Setting147 G T L V H) (hK : K ∈ cComp H)
    (hU3 : IsPSU 3 3 1 (cStar K)) : H = hz T V ∧ Ctx753 T L V K := by
  obtain ⟨hKT, hG1, -, hU, -⟩ := h52 G T L V H S K hK
  obtain ⟨K', hC, -, hUK⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have : K ∈ ({K'} : Set (Subgroup G)) := hC ▸ hK
    exact this
  subst hKK'
  obtain ⟨-, -, -, hF⟩ := h30 G T L V H S K hK
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_cComp_eq hC
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hcl : conjClosure K T = K := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hHN (hTH ht)) k).mp hk
  have hH' : conjClosure K T ⊔ (L32A.l1 T L V ⊔ T) = H := by
    rw [hcl]
    refine le_antisymm (sup_le hKH (sup_le (le_sup_left.trans S.hz.1.1) hTH)) ?_
    rw [hKT]
    exact sup_le_sup_left le_sup_right K
  rw [hH'] at hF
  have hV1 : Nat.card (fsuV1 T V) = 2 := hF.toHypF98.toHypF91.card_V₁
  have hHz : H = hz T V := by
    rw [hG1, A6.g1, normalizer_eq_centralizer_of_card_two hV1]
  subst hHz
  exact ⟨rfl, ⟨S.hyp, S, hC, hKT, hU, hU ▸ hUK, hU3, hF⟩⟩

end L32A

end CFSG.Quasithin.H13
