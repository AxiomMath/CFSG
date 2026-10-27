module

public import CFSG.Quasithin.Background.RonanE51One
public import CFSG.Quasithin.Background.RonanE51Two

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e5_1 {P : Subgroup G} {i j : ℕ} (hP : IsSylowIn 2 P ⊤) {A K : Subgroup G}
    (hA : IsElemAbelianCorank P i A) (hK : E1.IsE j ⊤ P A K)
    (h1 : E1.EOne ↥K (A.subgroupOf K) →
      twoResidual K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤
        ((frattiniIn (CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype)
    (h2 : E1.ETwo ↥K ((P ⊓ K).subgroupOf K) (A.subgroupOf K) →
      twoResidual K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ solvRad K)
    {W : Subgroup G}
    (hW : W = ⨆ (B : Subgroup G) (_ : IsElemAbelianCorank P (i + j) B ∧ B ≤ pCoreOf 2 K), B) :
    omegaOneCenterOf (thompsonJi P (i + j)) ≤ omegaOneCenterOf W ∧
      K ≤ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hnm : i + j < CFSG.Open.pRank 2 P
  swap
  ·
    have hJ : thompsonJi P (i + j) = ⊥ := VolI.E54.thompsonJi_eq_bot_of_le (not_lt.1 hnm)
    have hWle : W ≤ thompsonJi P (i + j) := by
      rw [hW]
      exact iSup₂_le fun B hB =>
        le_iSup₂_of_le (f := fun B (_ : IsElemAbelianCorank P (i + j) B) => B) B hB.1 le_rfl
    rw [hJ] at hWle
    have hW0 : W = ⊥ := le_bot_iff.1 hWle
    rw [hJ, hW0, VolI.E54.omegaOneCenterOf_bot_eq]
    refine ⟨bot_le, fun k _ => ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.2 (Subgroup.normal_bot)]
    exact Subgroup.mem_top k
  obtain ⟨-, hAcard⟩ := E3.card_le_of_isE hP hA.1 hA.2.1 hK
  set Q := pCoreOf 2 K with hQdef
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQP : Q ≤ P := pCoreOf_le_of_isSylow hK.2.2.1
  have hA₁ : A ⊓ Q ∈ E5.wFam (i + j) P Q := inf_mem_wFam hA hAcard
  have hWeq : W = E5.wGen (i + j) P Q := hW.trans (iSup_corank_eq_wGen hQP hnm)
  have hJeq : thompsonJi P (i + j) = H13.thompsonJk (i + j) P :=
    VolI.E54.thompsonJi_eq_thompsonJk hnm
  rw [hJeq, hWeq]
  set J := H13.thompsonJk (i + j) P with hJdef
  set D := omegaOneCenterOf J with hDdef
  set W' := E5.wGen (i + j) P Q with hW'def
  have hKW : K ≤ Subgroup.normalizer (W' : Set G) := E5.le_normalizer_wGen (i + j) hKQ
  refine ⟨?_, hKW⟩
  have hWQ : W' ≤ Q := E5.wGen_le (i + j) P Q
  have hWJ : W' ≤ J := E5.wGen_le_thompsonJk hQP
  have hAJ : A ≤ J := le_thompsonJk_of_corank (Nat.le_add_right i j) hA
  have hDK : D ≤ K := omegaOneCenter_le_of_tau hAJ hK.2.1
  have hDW : D ≤ Subgroup.centralizer (W' : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw)
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hDA : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := fun d hd a ha =>
    (mem_centralizer_of_mem_omegaOneCenterOf hd (hAJ ha)).symm
  have hDQW : D ⊓ Q ≤ W' :=
    le_wGen_of_commute hA₁ (B2F.isElemAbelian_mono inf_le_left hDel) inf_le_right
      fun v hv a ha => hDA v hv.1 a ha.1
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    (hQP.trans (E5.le_normalizer_thompsonJk (i + j) P)).trans
      (normalizer_le_normalizer_omegaOneCenterOf _)
  obtain ⟨hDS, hKS, hres⟩ := stabilizer_facts hKQ hKW hWQ hQ2 hDK hDW hQD hDQW
  set S := K ⊓ Subgroup.centralizer (W' : Set G) ⊓ E5.quotStab Q W' with hSdef
  have hSK : S ≤ K := inf_le_left.trans inf_le_left
  have hSres : twoResidual S ≤ twoResidual K ⊓ Subgroup.centralizer (Q : Set G) :=
    le_inf (E1.twoResidual_mono hSK) hres
  have hDQ : D ≤ Q := by
    have hD2 : IsPGroup 2 D := B2F.isPGroup_of_isElemAbelian hDel
    rcases hK.2.2.2 with ⟨hE, -⟩ | ⟨hE, -⟩
    ·
      have hSR := hSres.trans (h1 hE)
      have hSn : (S.subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).2 hKS
      have hD2' : IsPGroup 2 (D.subgroupOf K) :=
        hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
      have hRΓ : twoResidual (S.subgroupOf K) ≤
          (frattiniIn (CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K))).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        intro y hy
        have hy' : (y : G) ∈ twoResidual S := by
          have h1 : (twoResidual (S.subgroupOf K)).map K.subtype = twoResidual S := by
            rw [E1.map_twoResidual, Subgroup.map_subgroupOf_eq_of_le hSK]
          rw [← h1]
          exact Subgroup.mem_map_of_mem _ hy
        obtain ⟨z, hz, hzy⟩ := hSR hy'
        have hzy' : z = y := Subtype.ext hzy
        rw [← hzy']
        exact hz
      have hDΓ := le_pCore_of_eOne hE hD2' (Subgroup.subgroupOf_mono K hDS) hRΓ
      intro d hd
      exact ⟨⟨d, hDK hd⟩, hDΓ (show (⟨d, hDK hd⟩ : ↥K) ∈ D.subgroupOf K from hd), rfl⟩
    · exact le_pCoreOf_of_isTwoClosed hE.1 hSK hKS hD2 hDS (hSres.trans (h2 hE))
  have hDW' : D ≤ W' := fun d hd => hDQW ⟨hd, hDQ hd⟩
  intro d hd
  exact mem_omegaOneCenterOf (hDW' hd) (fun w hw => Subgroup.mem_centralizer_iff.1 (hDW hd) w hw)
    (hDel.2 d hd)

end CFSG.Quasithin.RonanE51
