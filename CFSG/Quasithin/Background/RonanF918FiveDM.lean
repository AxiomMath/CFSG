module

public import CFSG.Quasithin.Background.RonanF918FiveDH
public import CFSG.Quasithin.Background.RonanF918FiveO2

public section

namespace CFSG.Quasithin.RonanF918

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.RonanD321.SL2Model
open scoped Pointwise commutatorElement Matrix

section Cases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem multCases (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    {F : Type} [Field F] [Finite F]
    (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
    (hCent : ∀ (x : G) (hxC : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _))
    (hKer : ∀ (k : G) (hk : k ∈ K),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        ⟨k, le_of_mem_cComp h.K_cComp hk⟩ = 1 → k ∈ pCoreOf 2 H) :
    MultCasesU (multData h hIU hV₁I D hCent hKer) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLMp : autIH V₁ I H K ≤ autIH V₁ I H (conjClosure K T) := autIH_K_le_K₀ (V₁ := V₁) I hKH T
  by_cases hex : ∃ line : Submodule F (Fin 2 → F),
      multLineFixedU F (multData h hIU hV₁I D hCent hKer).multiplicity.range line
  · left
    obtain ⟨line, hfl⟩ := hex
    refine ⟨line, hfl, V₁ ⊔ ⁅Spre h hIU hV₁I D line, K⁆, le_sup_left,
      Jline_le_Jg h hIU hV₁I D line, isIrrPlusTilde_Jline h hIU hV₁I D line hfl.1, rfl, ?_, ?_⟩
    · intro x hxC
      have hxH := centralizerMod_le_left _ _ _ hxC
      refine mem_normalizer_Jline h hIU hV₁I D line
        (Subgroup.inclusion (centralizer_le_NLM hLMp) (cHom h hCent ⟨x, hxC⟩)) ⟨x, hxH⟩ rfl ?_
      intro Y hY
      obtain ⟨v, rfl⟩ := (multData h hIU hV₁I D hCent hKer).coordinates_surjective Y
      have hw : x * (v : G) * x⁻¹ ∈ V₁ ⊔ ⁅conjClosure I H, K⁆ :=
        (Subgroup.mem_normalizer_iff.mp
          ((multData h hIU hV₁I D hCent hKer).centralizer_normalizes hxC) (v : G)).mp v.2
      have e1 := (multData h hIU hV₁I D hCent hKer).multiplicity_equivariance ⟨x, hxC⟩ v
        ⟨_, hw⟩ rfl
      have e2 := bq_Jt_conj h hIU hV₁I D
        (Subgroup.inclusion (centralizer_le_NLM hLMp) (cHom h hCent ⟨x, hxC⟩)) ⟨x, hxH⟩ rfl v
        ⟨_, hw⟩ rfl
      have e3 : psi D (Subgroup.inclusion (centralizer_le_NLM hLMp) (cHom h hCent ⟨x, hxC⟩))
          ((multData h hIU hV₁I D hCent hKer).coordinates v) =
          multOpU F ((multData h hIU hV₁I D hCent hKer).multiplicity ⟨x, hxC⟩)
            ((multData h hIU hV₁I D hCent hKer).coordinates v) := e2.symm.trans e1
      rw [e3]
      exact multOpU_mem_multLineModuleU (hfl.2 _ ⟨⟨x, hxC⟩, rfl⟩) hY
    · intro element hpres
      exact mem_normalizer_Jline h hIU hV₁I D line (gHom h element) ⟨(element : G), element.2.1⟩ rfl
        hpres
  · right
    intro line hrank hfix
    exact hex ⟨line, hfix⟩

end Cases

section Final

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem multData_of_iiiD (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU) (hD : F918IiiD h hIU) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
      ∃ data : MultDataU V₁ Vp H K T I F, MultCasesU data := by
  haveI := factElem h hIU
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  obtain ⟨n, F, hF, hFin, hcard, hn, -, ⟨D⟩⟩ := coordData_of_d321Three hD
  have hCent : ∀ (x : G) (hxC : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _) := by
    intro x hxC
    have hC₀H := centralizerMod_le_left (pCoreOf 2 H) H (conjClosure K T)
    have hmem : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        autIH V₁ I H (centralizerMod (pCoreOf 2 H) H (conjClosure K T)) := by
      rw [autIH_eq_map h hC₀H]
      exact ⟨⟨x, centralizerMod_le_left _ _ _ hxC⟩, Subgroup.mem_subgroupOf.mpr hxC, rfl⟩
    rw [autIH_centralizerMod_eq h hH hA37 hA38 hK hIU hnt] at hmem
    exact hmem.2
  have hKer : ∀ (k : G) (hk : k ∈ K),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, hKH hk⟩ = 1 →
        k ∈ pCoreOf 2 H := by
    intro k hk hact
    obtain ⟨hA38K, -⟩ := five_group_data h hH hA37 hA38 hK
    have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
    have hne : autIH V₁ I H K ≠ ⊥ := by
      rw [autIH_eq_map h hKH]
      exact map_K_ne_bot h hIU hnt
    exact mem_pCoreOf_of_mem_K_of_actH_eq_one h hIU hS hne hk hact
  exact ⟨n, F, hF, hFin, hn, hcard, multData h hIU hV₁I D hCent hKer,
    multCases h hIU hV₁I D hCent hKer⟩

end Final

end CFSG.Quasithin.RonanF918
