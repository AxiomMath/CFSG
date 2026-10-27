module

public import CFSG.Quasithin.H13.GoldschmidtC137MS

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem msA_of_baumann [Finite G] {X T V L P : Subgroup G} {hV : IsElemAbelian 2 V}
    (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (hn : X ≤ normalizer (L : Set G)) (hTP : T ≤ P) (hPX : P < X)
    (hXN : X ≤ normalizer (V : Set G))
    (hCV : IsSylowTwoOf (baum (pCoreOf 2 P) ⊓ centralizer (V : Set G))
      ((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G)))
    (hRS : autI hV (pCoreOf 2 P) ≤ autI hV (baum (pCoreOf 2 P))) :
    P ⊓ (L ⊔ baum (pCoreOf 2 P)) < L ⊔ baum (pCoreOf 2 P) ∧
      ¬ 2 ∣ (P ⊓ (L ⊔ baum (pCoreOf 2 P))).relIndex (L ⊔ baum (pCoreOf 2 P)) ∧
      baum (pCoreOf 2 P) = pCoreOf 2 (P ⊓ (L ⊔ baum (pCoreOf 2 P))) := by
  set R := pCoreOf 2 P with hRdef
  set S := baum R with hSdef
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hPnR : P ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hPnS : P ≤ normalizer (S : Set G) := hPnR.trans (normalizer_le_normalizer_baum R)
  have hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
    have h3 := Subgroup.relIndex_mul_relIndex T P X hTP hPX.le
    have h4 : 2 ∣ T.relIndex X := by
      rw [← h3]
      exact Dvd.dvd.mul_right h2 _
    exact hT.2.2 h4
  have hRT : R ≤ T := pCoreOf_two_le_of_sylowIn hTP hT.2.1 hTodd
  have hSR : S ≤ R := inf_le_left
  have hST : S ≤ T := hSR.trans hRT
  have hS2 : IsPGroup 2 S := hT.2.1.to_le hST
  have hSX : S ≤ X := hST.trans hT.1
  have hLSX : L ⊔ S ≤ X := sup_le hLX hSX
  have hSnL : S ≤ normalizer (L : Set G) := hSX.trans hn
  have hTnL : T ≤ normalizer (L : Set G) := hT.1.trans hn
  have hTnS : T ≤ normalizer (S : Set G) := hTP.trans hPnS
  have hTnLS : T ≤ normalizer ((L ⊔ S : Subgroup G) : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_sup hTnL hTnS
  have hLnLS : L ≤ normalizer ((L ⊔ S : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hXnLS : X ≤ normalizer ((L ⊔ S : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
    exact Subgroup.mul_mem _ (hLnLS hl) (hTnLS ht)
  have hLS_set : ((L ⊔ S : Subgroup G) : Set G) = (L : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L S hSnL
  have hLcomp : L ∈ cComp (L ⊔ S) :=
    mem_cComp_of_le_normal hL le_sup_left hLSX hXnLS (sup_le Subgroup.le_normalizer hSnL)
  set H' := P ⊓ (L ⊔ S) with hH'
  have hH'LS : H' ≤ L ⊔ S := inf_le_right
  have hH'P : H' ≤ P := inf_le_left
  have hSH' : S ≤ H' := le_inf (hSR.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)) le_sup_right
  refine ⟨lt_of_le_of_ne hH'LS ?_, ?_, ?_⟩
  · intro heq
    have hLP : L ≤ P := (heq ▸ (le_sup_left : L ≤ L ⊔ S) : L ≤ H').trans hH'P
    have hXP : X ≤ P := by
      intro x hx
      obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
      exact P.mul_mem (hLP hl) (hTP ht)
    exact hPX.not_ge hXP
  · have hSyl : IsSylowTwoOf (T ⊓ (L ⊔ S)) (L ⊔ S) :=
      A4.isSylowTwoOf_inf_normal hT hLSX hXnLS
    have hle : T ⊓ (L ⊔ S) ≤ H' := le_inf (inf_le_left.trans hTP) inf_le_right
    intro h2
    exact hSyl.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left (L ⊔ S) hle))
  · have hSK : S ≤ pCoreOf 2 H' :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSH' (hH'P.trans hPnS) hS2
    refine le_antisymm hSK ?_
    set K := pCoreOf 2 H' with hK
    have hKH' : K ≤ H' := CFSG.LieType.BorelTits.pCoreOf_le 2 H'
    have hK2 : IsPGroup 2 K := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H'
    have hTnH' : T ≤ normalizer (H' : Set G) :=
      CFSG.Quasithin.B2F.le_normalizer_inf (hTP.trans Subgroup.le_normalizer) hTnLS
    have hPnK : P ≤ normalizer (K : Set G) := by
      intro x hx
      obtain ⟨l, hl, t, ht, rfl⟩ := hprod x (hPX.le hx)
      have hlP : l ∈ P := by
        have := P.mul_mem hx (P.inv_mem (hTP ht))
        simpa using this
      have hlH' : l ∈ H' := ⟨hlP, (le_sup_left : L ≤ L ⊔ S) hl⟩
      exact Subgroup.mul_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H' hlH')
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H' (hTnH' ht))
    have hKR : K ≤ R :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hKH'.trans hH'P) hPnK hK2
    have hCeq : K ⊓ centralizer (V : Set G) = S ⊓ centralizer (V : Set G) :=
      eq_of_isSylowTwoOf_le hCV (inf_le_inf_right _ hSK)
        (inf_le_inf_right _ (hKH'.trans hH'LS)) (hK2.to_le inf_le_left)
    intro k hk
    have hkX : k ∈ X := hPX.le (hH'P (hKH' hk))
    have hkN : k ∈ normalizer (V : Set G) := hXN hkX
    obtain ⟨g, hgS, hg⟩ := (mem_autI hV).1 (hRS (convI_mem_autI hV (hKR hk) hkN))
    have h1 : convI hV (g⁻¹ * ⟨k, hkN⟩) = 1 := by
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have h2 : (g : G)⁻¹ * k ∈ centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have h3 : (g : G)⁻¹ * k ∈ K ⊓ centralizer (V : Set G) :=
      ⟨K.mul_mem (K.inv_mem (hSK hgS)) hk, h2⟩
    rw [hCeq] at h3
    have h4 : (g : G) * ((g : G)⁻¹ * k) ∈ S := S.mul_mem hgS h3.1
    simpa using h4

end CFSG.Quasithin.H13.U3.GC137
