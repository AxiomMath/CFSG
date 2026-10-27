module

public import CFSG.Quasithin.H13.L32AC30a
public import CFSG.Quasithin.H13.L32A74
public import CFSG.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem conjClosure_T_eq_H (h37 : A37ForSQTK) (h38 : A38ForSQTK) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) : conjClosure K T = conjClosure K H := by
  have h := S.hyp
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hpc : pCoreOf 2 H ≠ ⊥ := S.hz.1.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  have hKH : K ≤ H := le_of_mem_cComp hK
  refine le_antisymm (conjClosure_mono le_rfl hTH) ?_
  by_cases hKT : ∀ t ∈ T, t ∈ Subgroup.normalizer (K : Set G)
  · have hn := lemma_1_2_4_normal h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h38 hpc hTsyl
      (cComp_subset_lFamily hTH hK) le_rfl hK hKT
    have hHK := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn
    refine conjClosure_le fun g hg k hk => le_conjClosure K T ?_
    exact (Subgroup.mem_normalizer_iff.mp (hHK hg) k).mp hk
  · push Not at hKT
    obtain ⟨t, ht, htn⟩ := hKT
    rcases lemma_1_2_1_three h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h38 hpc hK with
      hKn | ⟨hcard, -⟩
    · exact absurd (((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn) (hTH ht)) htn
    · set Kt := K.map (MulAut.conj t).toMonoidHom with hKt
      have hne : Kt ≠ K := by
        intro he
        apply htn
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hx' : t * x * t⁻¹ ∈ Kt := ⟨x, hx, rfl⟩
          rwa [he] at hx'
        · intro hx
          rw [← he] at hx
          obtain ⟨y, hy, hye⟩ := hx
          have hyx : y = x := by
            have e : t * y * t⁻¹ = t * x * t⁻¹ := hye
            simpa using e
          rwa [← hyx]
      have hK₁ : K ∈ conjSubgroupsBy H K := by
        refine ⟨1, H.one_mem, ?_⟩
        rw [map_one]
        exact (Subgroup.map_id K).symm
      have hK₂ : Kt ∈ conjSubgroupsBy H K := ⟨t, hTH ht, rfl⟩
      have hpair : ({K, Kt} : Set (Subgroup G)) = conjSubgroupsBy H K := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
        · rintro x (rfl | rfl)
          · exact hK₁
          · exact hK₂
        · rw [Set.ncard_pair hne.symm, hcard]
      refine conjClosure_le fun g hg k hk => ?_
      have hmem : K.map (MulAut.conj g).toMonoidHom ∈ ({K, Kt} : Set (Subgroup G)) := by
        rw [hpair]
        exact ⟨g, hg, rfl⟩
      have hgk : g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨k, hk, rfl⟩
      rcases hmem with h1 | h1
      · rw [h1] at hgk
        exact le_conjClosure K T hgk
      · rw [h1] at hgk
        obtain ⟨k', hk', hk'e⟩ := hgk
        have e : t * k' * t⁻¹ = g * k * g⁻¹ := hk'e
        rw [← e]
        exact mem_conjClosure ht hk'

theorem le_normalizer_conjClosure_T (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) :
    H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  rw [conjClosure_T_eq_H h37 h38 S hK]
  exact le_normalizer_conjClosure K H

theorem relIndex_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h : Hyp147 G T L V) : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have e : l1 T L V = L₁Of L (fsuV1 T V) := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  rw [e]
  exact (h.set14 h1222 h1332 h1334 hV2).Lp3

theorem hypF918_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h28 : Lemma14_7_28) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (S' : Setting147 G T L V (conjClosure K T ⊔ (l1 T L V ⊔ T))) :
    HypF918 T V L (fsuV1 T V) V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have hF := L1286.hypF98_of_abelian h1222 h37 h38 h39 (S'.hyp.hyp1281One h13322 hMod)
    (S'.hyp.isTSub_V1 hMod) S'.hyp.abelian S'.hz
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hK0H : conjClosure K T ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
  have hH'H : conjClosure K T ⊔ (l1 T L V ⊔ T) ≤ H := sup_le hK0H S.hz.1.1
  have hKH' : K ≤ conjClosure K T ⊔ (l1 T L V ⊔ T) := (le_conjClosure K T).trans le_sup_left
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  refine ⟨hF, cComp_mem_of_le hK hKH' hH'H,
    isQuasisimple_cStar h36 h28 S (relIndex_l1 h1222 h1332 h1334 S.hyp) hK, ?_,
    hH'H.trans (le_normalizer_conjClosure_T h37 h38 S hK)⟩
  exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right
    (le_inf (sup_le_sup_right hl1L T) le_sup_right))) (sup_le le_sup_left inf_le_right)

theorem lemma14_7_30_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h28 : Lemma14_7_28) (h519 : Lemma14_5_19) : Lemma14_7_30 := by
  intro G _ _ T L V H S K hK
  obtain ⟨hnot, S'⟩ := h519 G T L V H S K hK
  exact ⟨isQuasisimple_cStar h36 h28 S (relIndex_l1 h1222 h1332 h1334 S.hyp) hK, hnot, S',
    hypF918_of h1222 h1332 h1334 h36 h37 h38 h39 h28 S hK S'⟩

end CFSG.Quasithin.H13.L32A.C
