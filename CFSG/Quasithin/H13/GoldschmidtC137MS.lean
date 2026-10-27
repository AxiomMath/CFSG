module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S1412
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_cComp_of_le_normal [Finite G] {X L K : Subgroup G} (hL : L ∈ cComp X) (hLK : L ≤ K)
    (hKX : K ≤ X) (hKn : X ≤ normalizer (K : Set G)) (hLn : K ≤ normalizer (L : Set G)) :
    L ∈ cComp K := by
  have hsubK : IsSubnormal K X :=
    A3.subnormal_of_normal hKX ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hKn)
  refine ⟨hL.1, hL.2.1, A3.subnormal_of_normal hLK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLK).2 hLn), ?_⟩
  intro K' hK'L hK'ne hK'perf hK'sub
  exact hL.2.2.2 K' hK'L hK'ne hK'perf (A3.subnormal_trans hK'sub hsubK)

theorem eq_of_isSylowTwoOf_le {A B D : Subgroup G} [Finite G] (hA : IsSylowTwoOf A D)
    (hAB : A ≤ B) (hBD : B ≤ D) (hB : IsPGroup 2 B) : B = A := by
  have h1 := Subgroup.relIndex_mul_relIndex A B D hAB hBD
  have hodd : ¬ 2 ∣ A.relIndex B := fun h2 => hA.2.2 (by
    show 2 ∣ A.relIndex D
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _)
  have hp : IsPGroup 2 ↥B := hB
  obtain ⟨n, hn⟩ := hp.index (A.subgroupOf B)
  have hn0 : n = 0 := by
    by_contra h
    exact hodd (by
      show 2 ∣ (A.subgroupOf B).index
      rw [hn]
      exact dvd_pow_self 2 h)
  have : A.relIndex B = 1 := by
    show (A.subgroupOf B).index = 1
    rw [hn, hn0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.1 this) hAB

theorem isMSPair_of_baumann [Finite G] {X T V L P : Subgroup G} {hV : IsElemAbelian 2 V}
    (hSQ : SQTKGroup ↥X) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X) (hL2 : CharTwo L)
    (hn : X ≤ normalizer (L : Set G)) (hTP : T ≤ P) (hPX : P < X)
    (hXN : X ≤ normalizer (V : Set G))
    (hLie : IsRankTwoLie2Derived
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
    (hCV : IsSylowTwoOf (baum (pCoreOf 2 P) ⊓ centralizer (V : Set G))
      ((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G)))
    (hRS : autI hV (pCoreOf 2 P) ≤ autI hV (baum (pCoreOf 2 P))) :
    IsMSPair (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) ∧
      L ∈ cComp (L ⊔ baum (pCoreOf 2 P)) ∧
      ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) =
        (L : Set G) * (baum (pCoreOf 2 P) : Set G) := by
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
  refine ⟨⟨⟨CFSG.Quasithin.B5.sqtk_of_le hSQ hLSX, ?_, L, hLcomp, hLS_set, hLie⟩, ?_, ?_⟩, hLcomp,
    hLS_set⟩
  · exact charTwo_sup_of_normalizes hS2 hSnL hL2
  · left
    set H' := P ⊓ (L ⊔ S) with hH'
    have hH'LS : H' ≤ L ⊔ S := inf_le_right
    have hH'P : H' ≤ P := inf_le_left
    have hSH' : S ≤ H' := le_inf (hSR.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)) le_sup_right
    refine ⟨H', lt_of_le_of_ne hH'LS ?_, ?_, ?_⟩
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
  · intro C hCS hC0 hCchar hCn
    have hXC : X ≤ normalizer (C : Set G) := by
      intro x hx
      obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
      refine Subgroup.mul_mem _ (hCn ((le_sup_left : L ≤ L ⊔ S) hl)) ?_
      exact (normalizer_le_normalizer_of_characteristic_subgroupOf hCS hCchar) (hTnS ht)
    exact hn1 C hCS hC0 hCchar hXC

end CFSG.Quasithin.H13.U3.GC137
