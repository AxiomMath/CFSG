module

public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.E3Nlow

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Prop319

variable {G : Type u} [Group G] [Finite G] {V H S : Subgroup G}

theorem e3_19_comm (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ}
    (hij : i + j < sParam hV) {A K : Subgroup G} (hA : A ∈ gammaSet V i S)
    (hK : E1.IsE j H S A K) : ⁅twoResidual K, cClos V (i + j) S⁆ = ⊥ := by
  by_contra hne
  obtain ⟨hAS, g, hAg, hmg⟩ := hA
  have hVg := isElemAbelian_conjSubgroup hV g
  have hsg : sParam hVg = sParam hV := sParam_conj hV g hVg
  have hr : ((i + j : ℕ) : ℕ∞) < rParam (conjSubgroup V g) := by
    rw [rParam_conj]
    exact lt_of_lt_of_le (by exact_mod_cast hij) (coe_sParam_le_rParam hV)
  have hk : i + j < rk ↥(conjSubgroup V g) := by
    rw [rk_conjSubgroup]
    exact lt_of_lt_of_le hij (sParam_le_rk hV)
  have hne' : ⁅twoResidual K, cClos (conjSubgroup V g) (i + j) S⁆ ≠ ⊥ := by
    rwa [cClos_conjV]
  have h1 := (e3_17_comm_ne hVg hS le_rfl hr hk hAS hAg hmg.le hK hne').2
  have h2 := e3_17_comm_eq_bot hVg hS le_rfl hk hAS hAg hmg.le hK (by rwa [hsg])
  simp only [cClos_conjV] at h1 h2
  exact h1 h2

theorem e3_19 (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ}
    (hj : E1.nParam H = j) (hij : i + j < sParam hV) :
    (H ⊓ Subgroup.centralizer (cClos V (i + j) S : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (wClos V i S : Set G)) = H := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hInE := inE_of_nParam_eq hj
  have hEF := (E1.inE_iff_inEFor hS).1 hInE (gammaSet V i H) (isInvColl_gammaSet hV i H)
  rw [weakClosure_gammaSet hS.le] at hEF
  have hE : E1.eGen j H S (gammaSet V i H) ≤
      (H ⊓ Subgroup.centralizer (cClos V (i + j) S : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (wClos V i S : Set G)) := by
    refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
    have hAΓ : A ∈ gammaSet V i S := ⟨hAS, hA.2⟩
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    have hKH : K ≤ H := hK.1
    have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
    have hcomm := e3_19_comm hV hS hij hAΓ hK
    have hSN : S ≤ Subgroup.normalizer (wClos V i S : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_wClos S)
    have h1 : S ⊓ K ≤ H ⊓ Subgroup.normalizer (wClos V i S : Set G) :=
      le_inf (inf_le_right.trans hKH) (inf_le_left.trans hSN)
    have h2 : twoResidual K ≤ H ⊓ Subgroup.centralizer (cClos V (i + j) S : Set G) :=
      le_inf ((twoResidual_le K).trans hKH) (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    rw [hKeq]
    exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)
  calc H = E1.eGen j H S (gammaSet V i H) ⊔
        (H ⊓ Subgroup.normalizer (wClos V i S : Set G)) := hEF.symm
    _ ≤ _ := sup_le hE le_sup_right

end Prop319

section Lemma320

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

omit [Finite G] in
theorem omegaOneCenter_le_inf_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem e3_20 (hV : IsElemAbelian 2 V) {T : Sylow 2 G} {M H : Subgroup G}
    (hH : IsHStar (T : Subgroup G) M H)
    (hZ : ⁅quasithinOmegaOneCenter (T : Subgroup G), H⁆ ≠ ⊥)
    (hW : ¬ wClos V 0 (T : Subgroup G) ≤ pCoreOf 2 H) :
    (sParam hV : ℕ∞) ≤ E1.nParam H := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  have hjs : j < sParam hV := by
    rw [← hj] at hlt
    exact_mod_cast hlt
  have hTH : (T : Subgroup G) ≤ H := hH.1.1
  have hTS : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨hTH, T.isPGroup', fun h2 => T.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have h19 := e3_19 hV hTS (i := 0) hj.symm (by simpa using hjs)
  have key : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < H → Y ≤ M := by
    intro Y hTY hYH
    by_contra hYM
    exact hYH.ne (hH.2.2 Y (inH_of_le T hTY hYH.le hH.1) hYH.le hYM)
  apply hH.2.1
  rw [← h19]
  refine sup_le ?_ ?_
  ·
    set Z := quasithinOmegaOneCenter (T : Subgroup G) with hZdef
    have hZT := omegaOneCenter_le_inf_centralizer (T : Subgroup G)
    have hZC : Z ≤ cClos V (0 + j) (T : Subgroup G) :=
      le_inf (hZT.trans inf_le_left) (fun z hz => Subgroup.mem_centralizer_iff.2 fun x hx => by
        have hxT : x ∈ (T : Subgroup G) := wClos_le (V := V) (0 + j) _ hx
        exact (Subgroup.mem_centralizer_iff.1 (hZT hz).2) x hxT)
    have hTZ : (T : Subgroup G) ≤ H ⊓ Subgroup.centralizer (Z : Set G) :=
      le_inf hTH (fun t ht => Subgroup.mem_centralizer_iff.2 fun z hz =>
        ((Subgroup.mem_centralizer_iff.1 (hZT hz).2) t ht).symm)
    have hlt' : H ⊓ Subgroup.centralizer (Z : Set G) < H := by
      refine lt_of_le_of_ne inf_le_left fun h => hZ ?_
      have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := by
        rw [← h]
        exact inf_le_right
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hHZ
    exact (inf_le_inf_left H (Subgroup.centralizer_le hZC)).trans (key _ hTZ hlt')
  ·
    have hTN : (T : Subgroup G) ≤ Subgroup.normalizer (wClos V 0 (T : Subgroup G) : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_wClos _)
    have hlt' : H ⊓ Subgroup.normalizer (wClos V 0 (T : Subgroup G) : Set G) < H := by
      refine lt_of_le_of_ne inf_le_left fun h => hW ?_
      have hHN : H ≤ Subgroup.normalizer (wClos V 0 (T : Subgroup G) : Set G) := by
        rw [← h]
        exact inf_le_right
      have hWH : wClos V 0 (T : Subgroup G) ≤ H := (wClos_le (V := V) _ _).trans hTH
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 hWH ?_ (T.isPGroup'.to_le (wClos_le (V := V) _ _))
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).2 hHN
    exact key _ (le_inf hTH hTN) hlt'

end Lemma320

end E3

end CFSG.Quasithin
