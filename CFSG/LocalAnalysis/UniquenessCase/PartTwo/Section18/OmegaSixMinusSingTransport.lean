module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def SingConcl (G : Type) [Group G] [Finite G] (n : ℕ) (Q : Subgroup G) : Prop :=
  IsParabolicTwo G Q ∧ pCoreOf 2 Q ≠ ⊥ ∧ IsL2 (Bar2 (F07.DerInf Q)) (2 * n) ∧
    pCoreOf 2 (F07.DerInf Q) ≠ ⊥ ∧
    (Even n → ∃ B P₃ : Subgroup G, Nat.card B = 3 ∧ B ≤ P₃ ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P₃ ⊤ ∧ P₃ ≤ Subgroup.centralizer (B : Set G) ∧ P₃ ≤ Q ∧
      F08.KOf8103 ⊤ B ≤ Q ∧ IsL2 (Bar2 (F08.KOf8103 ⊤ B)) (2 * n))

private theorem isL2_bar2_map_T2J1 {G G' : Type} [Group G] [Group G'] (A : Subgroup G)
    (e : G ≃* G') {m : ℕ} (h : IsL2 (Bar2 A) m) : IsL2 (Bar2 (A.map e.toMonoidHom)) m := by
  unfold IsL2 at h ⊢
  obtain ⟨e'⟩ := nonempty_bar2_mulEquiv_map A e
  exact CFSG.Blueprint.LieModel.of_mulEquiv e' h

private theorem centralizer_map_T2J1 {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (B : Subgroup G) :
    Subgroup.centralizer ((B.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (B : Set G)).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := e.surjective x
    have hg' : e.toMonoidHom g = x := hg
    rw [← hg'] at hx ⊢
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro b hb
    have hb' : e.toMonoidHom b ∈ B.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    have hcomm := hx (e.toMonoidHom b) hb'
    rw [← map_mul, ← map_mul] at hcomm
    exact e.injective hcomm
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg e.toMonoidHom (Subgroup.mem_centralizer_iff.mp hc b hb)

private theorem kOf8103_map_T2J1 {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') (B : Subgroup G) :
    F08.KOf8103 ⊤ (B.map e.toMonoidHom) = (F08.KOf8103 ⊤ B).map e.toMonoidHom := by
  have hcen := centralizer_map_T2J1 e B
  unfold F08.KOf8103
  rw [show (⊤ ⊓ Subgroup.centralizer ((B.map e.toMonoidHom : Subgroup G') : Set G')) =
        (⊤ ⊓ Subgroup.centralizer (B : Set G)).map e.toMonoidHom from by
      rw [top_inf_eq, top_inf_eq, hcen]]
  change Hinf ((⊤ ⊓ Subgroup.centralizer (B : Set G)).map e.toMonoidHom) =
      (Hinf (⊤ ⊓ Subgroup.centralizer (B : Set G))).map e.toMonoidHom
  exact (Hinf_map e.toMonoidHom (⊤ ⊓ Subgroup.centralizer (B : Set G))).symm

theorem SingConcl.map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') {n : ℕ} {Q : Subgroup G} (h : SingConcl G n Q) :
    SingConcl G' n (Q.map e.toMonoidHom) := by
  obtain ⟨hP, hpc, hL2, hpcInf, heven⟩ := h
  have hder : (F07.DerInf Q).map e.toMonoidHom = F07.DerInf (Q.map e.toMonoidHom) := by
    rw [← hinf_eq_derInf, ← hinf_eq_derInf]
    exact Hinf_map e.toMonoidHom Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hP.map e.toMonoidHom e.surjective
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e Q]
    exact fun hbot => hpc (Subgroup.map_eq_bot_iff_of_injective (pCoreOf 2 Q)
      (f := e.toMonoidHom) e.injective |>.mp hbot)
  · have := isL2_bar2_map_T2J1 (F07.DerInf Q) e hL2
    rwa [hder] at this
  · have hpc' : pCoreOf 2 (F07.DerInf (Q.map e.toMonoidHom)) =
        (pCoreOf 2 (F07.DerInf Q)).map e.toMonoidHom := by
      rw [← hder]
      exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e (F07.DerInf Q)
    rw [hpc']
    exact fun hbot => hpcInf (Subgroup.map_eq_bot_iff_of_injective (pCoreOf 2 (F07.DerInf Q))
      (f := e.toMonoidHom) e.injective |>.mp hbot)
  · intro hn
    obtain ⟨B, P₃, hBcard, hBP, hSyl, hC, hPQ, hK, hL⟩ := heven hn
    refine ⟨B.map e.toMonoidHom, P₃.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (K := B) e.injective, hBcard]
    · exact Subgroup.map_mono hBP
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      refine CFSG.ABGLocalTools.isSylowOf_of_card (P := P₃.map e.toMonoidHom)
        (K := ⊤) le_top ?_
      rw [Subgroup.card_map_of_injective (K := P₃) e.injective, hSyl.card_eq,
        Subgroup.card_top, Subgroup.card_top, Nat.card_congr e.toEquiv]
    · rintro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hC hp) b hb]
    · exact Subgroup.map_mono hPQ
    · rw [kOf8103_map_T2J1 e B]
      exact Subgroup.map_mono hK
    · have := isL2_bar2_map_T2J1 (F08.KOf8103 ⊤ B) e hL
      rwa [← kOf8103_map_T2J1 e B] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
