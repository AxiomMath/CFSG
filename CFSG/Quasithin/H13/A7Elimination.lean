module

public import CFSG.Quasithin.H13.A7EscapeProducer
public import CFSG.Quasithin.H13.FiveQuotients
public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.Quasithin.SteinbergBSCommutingModuleObstruction
import CFSG.Quasithin.SteinbergCFFullLocalSylowIntermediates

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

section Bridges

variable {G : Type*} [Group G]

theorem quasithinOmegaOneCenter_eq_centerTorsion (T : Subgroup G) :
    quasithinOmegaOneCenter T = centerTorsion 2 T :=
  (omegaOneCenterOf_eq T).symm.trans (omegaOneCenterOf_eq_centerTorsion T)

theorem thompsonJ_eq_iSup_isElementaryAbelian (T : Subgroup G) :
    thompsonJ T = ⨆ (A : Subgroup G) (_ : A ≤ T ∧ IsElementaryAbelian 2 A ∧
      ∀ B : Subgroup G, B ≤ T → IsElementaryAbelian 2 B → Nat.card B ≤ Nat.card A), A := by
  simp only [thompsonJ, IsMaxElemAbelian, isElemAbelian_iff_isElementaryAbelian]

theorem VZ_eq_closure (T Y : Subgroup G) :
    VZ T Y = closure {x | ∃ y ∈ Y, ∃ z ∈ quasithinOmegaOneCenter T, x = y * z * y⁻¹} := by
  simp only [VZ, CFSG.Quasithin.conjClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, h⟩
    exact ⟨y, hy, z, hz, h.symm⟩
  · rintro ⟨y, hy, z, hz, h⟩
    exact ⟨y, hy, z, hz, h.symm⟩

end Bridges

theorem isEvenCharacteristic_of_quasithinIsQTKECat {G : Type} [Group G] [Finite G]
    (h : QuasithinUnique.quasithinIsQTKECat G) : CFSG.IsEvenCharacteristic G :=
  CFSG.Quasithin.SteinbergCF.isEvenCharacteristic_of_quasithinEvenCharacteristic h.2.1

@[expose] def StmtA7FinalModuleWitness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ (U K D : Subgroup G) (v : G), IsElemAbelian 2 U ∧
      K ≤ normalizer (U : Set G) ∧ D ≤ normalizer (U : Set G) ∧ v ≠ 1 ∧ v ∈ ⁅U, D⁆ ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ⁅K, D⁆ ≤ centralizer (U : Set G) ∧
      ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ ∧ centralizer ({v} : Set G) ≤ normalizer (L : Set G)

theorem A7_final_module_witness_of_data {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hQTKE : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : ∃ (e : G) (Y K D : Subgroup G) (v : G),
      e ∈ T ∧ (∀ t ∈ T, t * e = e * t) ∧ orderOf e = 2 ∧
      T ≤ Y ∧ Y ≤ centralizer ({e} : Set G) ∧ K ≤ Y ∧ D ≤ Y ∧
      ¬ K ≤ normalizer (L : Set G) ∧ D = ⁅D, thompsonJ T⁆ ∧
      v ≠ 1 ∧ v ∈ ⁅quasithinOmegaOneCenter T, D⁆ ∧
      centralizer ({v} : Set G) ≤ normalizer (L : Set G) ∧
      ∃ ρ : Y →* Perm (Fin 5) × Perm (Fin 3), Function.Surjective ρ ∧
        ρ.ker = (centralizer (VZ T Y : Set G)).subgroupOf Y ∧
        (K.subgroupOf Y).map ρ = (alternatingGroup (Fin 5)).prod ⊥ ∧
        (D.subgroupOf Y).map ρ =
          (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3))) :
    ∃ (U K D : Subgroup G) (v : G), IsElemAbelian 2 U ∧
      K ≤ normalizer (U : Set G) ∧ D ≤ normalizer (U : Set G) ∧ v ≠ 1 ∧ v ∈ ⁅U, D⁆ ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ⁅K, D⁆ ≤ centralizer (U : Set G) ∧
      ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ ∧ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, Y, K, D, v, heT, heTc, he2, hTY, hYe, hKY, hDY, hKM, hDJ, hv1, hvZD, hvM, hρ⟩ := h
  obtain ⟨Ts, rfl⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hT.1 hT.2⟩
  obtain ⟨hUel, hKU, hDU, hvUD, hKD, hUKD⟩ :=
    A7_involution_local_action_data_gives_split_witness
      (isEvenCharacteristic_of_quasithinIsQTKECat hQTKE) Ts heT heTc he2 hTY hYe hKY hDY
      (thompsonJ_eq_iSup_isElementaryAbelian _) (quasithinOmegaOneCenter_eq_centerTorsion _)
      (VZ_eq_closure _ _) hKM hDJ hρ hv1 hvZD hvM
  exact ⟨VZ Ts Y, K, D, v, hUel, hKU, hDU, hv1, hvUD, hKM, hKD, hUKD, hvM⟩

theorem A7_final_module_witness_producer (hesc : StmtA7EscapingLocalActionData) :
    StmtA7FinalModuleWitness :=
  fun G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7 =>
    A7_final_module_witness_of_data hQTKE hT (hesc G T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7)

theorem false_of_A7_final_module_witness {G : Type} [Group G] {L : Subgroup G}
    (h : ∃ (U K D : Subgroup G) (v : G), IsElemAbelian 2 U ∧
      K ≤ normalizer (U : Set G) ∧ D ≤ normalizer (U : Set G) ∧ v ≠ 1 ∧ v ∈ ⁅U, D⁆ ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ⁅K, D⁆ ≤ centralizer (U : Set G) ∧
      ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ ∧ centralizer ({v} : Set G) ≤ normalizer (L : Set G)) : False := by
  obtain ⟨U, K, D, v, hU, hKU, hDU, hv1, hvUD, hKM, hKD, hUKD, hvM⟩ := h
  have : IsElementaryAbelian 2 U := (isElemAbelian_iff_isElementaryAbelian 2).1 hU
  exact hKM ((SteinbergBS.five_commuting_module_centralizer_obstruction (p := 2) hKU hDU hKD
    hUKD).2 _ v hvUD hv1 hvM)

theorem five_A7_local_quotient_elimination (hW : StmtA7FinalModuleWitness) : StmtFiveA7Elim :=
  fun G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7 =>
    false_of_A7_final_module_witness (hW G T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7)

theorem stmtFiveA7Elim_of_inputs
    (hG10 : StmtA7NaturalModuleConfig) (h12213 : Stmt12_2_13)
    (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h331 : Stmt3_3_1) :
    StmtFiveA7Elim :=
  five_A7_local_quotient_elimination (A7_final_module_witness_producer
    (A7_escaping_local_action_data_producer hG10 h12213 h1227 h1228 h1229 h331))

@[expose] def StmtA7NaturalModuleConfigHyp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ ψ : V ≃* Multiplicative (evenWeight 7), A7NatConfig T L V ψ

theorem stmtA7NaturalModuleConfig_of_hyp (h1222 : Stmt12_2_2)
    (hG10 : StmtA7NaturalModuleConfigHyp) : StmtA7NaturalModuleConfig := by
  intro G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7
  have hnalt : ¬ Alt12_2_2 G := fun h' => hnex (qt13Excluded_of_alt12_2_2 h')
  rcases h1222 G T hs hnab hQTKE hT with hAlt | h3
  · exact absurd hAlt hnalt
  obtain ⟨hTL, ⟨V, hV⟩, -⟩ := h3 L hLmax hLf hLq
  obtain ⟨ψ, hψ⟩ := hG10 G T L V ⟨hs, hnab, hQTKE, hT, hnalt, hLmax, hLf, hLq, hTL, hV⟩ hA7
  exact ⟨V, ψ, hψ⟩

theorem stmt12_3_1_of_inputs
    (hG10 : StmtA7NaturalModuleConfigHyp) (h12213 : Stmt12_2_13)
    (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h331 : Stmt3_3_1) :
    Stmt12_3_1 := by
  intro G _ _ T L V hyp hA7
  obtain ⟨ψ, hcfg⟩ := hG10 G T L V hyp hA7
  exact false_of_A7_final_module_witness (A7_final_module_witness_of_data hyp.qtke hyp.sylow
    (A7_escaping_local_action_data_of_hyp1223 h12213 h1227 h1228 h1229 h331 hyp hcfg hA7))

end CFSG.Quasithin.H13.A7
