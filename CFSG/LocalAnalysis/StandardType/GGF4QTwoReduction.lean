module

public import CFSG.LocalAnalysis.StandardType.GGF4QTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGF4SmallFFDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4
public import CFSG.LocalAnalysis.StandardType.GGSLTwoAutBound
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoHypA
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
public import CFSG.RankThree.PartOne.K133H.F4Weyl
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreDeltaTransfer
import CFSG.LocalAnalysis.StandardType.GGF4QTwoFFBridge
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType.FrameRoute

theorem exists_conj_of_mem_join {G : Type} [Group G] {L K Bs : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ∃ g : G, ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | ∃ g : G, ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹}
      mul_mem' := by
        rintro a c ⟨g, hg⟩ ⟨h, hh⟩
        refine ⟨g * h, fun b => ?_⟩
        rw [MulAut.mul_apply, hg, hh]
        group
      one_mem' := ⟨1, fun b => by simp⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        refine ⟨g⁻¹, fun b => ?_⟩
        have h1 := hg (a⁻¹ b)
        rw [MulAut.apply_inv_self] at h1
        rw [h1]
        group }
  have hle : ∀ H : Subgroup G, ggAutomizer H Bs ≤ S := fun H =>
    (Subgroup.closure_le _).mpr (by rintro ψ ⟨g, -, -, hg⟩; exact ⟨g, hg⟩)
  exact sup_le (hle L) (hle K) hφ

theorem card_bstar_F4 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hAt : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.F₄) : Nat.card Bs = 3 ^ 4 := by
  obtain ⟨⟨-, -, -, -, -, hβ, hS, -⟩, hBs, -⟩ := hR.1
  obtain ⟨y, K, hN, hM⟩ := hAt
  have hup : Nat.card Bs ≤ 3 ^ 4 := by
    have h := SpJoinRefl.card_le_pow_of_weylOfType hM (eq_one_of_fix_join hTBF hWI hR hW hN)
    simpa using h
  have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
  have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
  have hlow : 3 ^ 4 ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right (by norm_num) h4).trans (hB ▸ Subgroup.card_le_of_le hBs.1)
  omega

theorem ggSecFiveData_of_ff81b_typeA
        (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hAt : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.F₄)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) {n : ℕ} (hn : n = 5 ∨ n = 6)
    (hmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) :
    GGSecFiveData 3 B x L D J := by
  obtain ⟨⟨hsimp, hna, hKP, hchar, -, -, hS, -⟩, hBs, -⟩ := hR.1
  haveI := hsimp
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hox : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hx1
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hN := le_normalizer_of_sstar_markingA hS (by omega) hmark
  have hZ : Subgroup.center L = ⊥ :=
    center_eq_bot_of_f4EndMarking
      (P := fun lab => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)
      (fun lab hl => ⟨by
        rcases hn with rfl | rfl
        · exact Or.inl ⟨hl.1, hl.2.1⟩
        · exact Or.inr (Or.inl ⟨hl.1, hl.2.1⟩), hl.2.2⟩) hmark
  have hM := statedClassicalModel_of_markingA hmark hZ
  have hA2 : ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)), IsCyclic P := fun P =>
    isCyclic_sylow_of_le_centralizer_of_forall hS.2.2.2.2 le_rfl P
  have hA3 := (twoLocalPrimeRank_centralizer_eq_of_config hR.1).symm
  have hA4 := ffNotWeaklyClosed_of_conj
    (FrameRoute.ggFrameA4Input_F4 hTBF hWI G B Bs x L D J hR hW hAt hq x hxB hx1)
  rcases hFF G hna hchar hKP n hn x hox L hLC hN hM hA2 hA3 hA4 with hPSL | ⟨hn5, hlab⟩
  · exfalso
    have hcard : Nat.card Bs = 3 ^ 4 := card_bstar_F4 hTBF hWI hR hW hAt
    obtain ⟨y, K, hNb, f, hf⟩ := hAt
    have hle := card_automizer_le_384_of_slTwo hPSL hBs.2.1 hcard hBs.2.2.2
      (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) (fun φ hφ => exists_conj_of_mem_join hφ)
    have h1152 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1152 := by
      rw [← Nat.card_congr f.toEquiv, FrameRoute.coxeterF4_eq]
      exact CFSG.RankThree.PartOne.K133H.card_weylGroup_F4
    omega
  · subst hn5
    obtain ⟨e⟩ := nonempty_mulEquiv_ggU_E6_one_of_label hna hlab
    obtain ⟨y, K, hNb, hWK⟩ := hAt
    have hadm : StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl⟩
    have hrange : (e.symm.toMonoidHom).range = ggG0 3 B x L D J := by
      rw [hG0 G B Bs x L D J hR hW hq y K hNb hWK (Or.inl hmark) ⟨e⟩]
      exact MonoidHom.range_eq_top.mpr e.symm.surjective
    have hker : (e.symm.toMonoidHom).ker ≤ Subgroup.center (ggU .E6 0 1).K := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective]
      exact bot_le
    exact Or.inr (Or.inr ⟨.E6, 0, 1,
      ggSecFivePres_of_psi_of_admissible hadm (by decide) e.symm.toMonoidHom hker hrange⟩)

theorem not_isCyclic_of_isElemAbelian_three_pow {G : Type} [Group G] {E : Subgroup G}
    {k : ℕ}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hk : 2 ≤ k) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (g : G) g.2)
  have hle : Nat.card E ≤ 3 := by
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hg3)
  have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem ggSecFiveData_of_ff81b_nbr
        (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) {y : G} {K : Subgroup G} (hNb : GGNbr 3 B x D J y K)
    (hWK : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hmarkK : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)) :
    GGSecFiveData 3 B x L D J := by
  have hAt : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.F₄ := ⟨y, K, hNb, hWK⟩
  obtain ⟨⟨hsimp, hna, hKP, hchar, -, hβ, hS, -⟩, hBs, -⟩ := hR.1
  haveI := hsimp
  obtain ⟨hBmax, hyB, hy1, hKy, hPC, -⟩ := hNb.1
  have hy3 : y ^ 3 = 1 := hS.1.1.2 y hyB
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcardBs : Nat.card Bs = 3 ^ 4 := card_bstar_F4 hTBF hWI hR hW hAt
  have hm4 : twoLocalPrimeRank 3 G ≤ 4 := by
    have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
    have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    rw [hB, hcardBs] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_f4EndMarking
      (P := fun lab => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)
      (fun lab hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hmarkK
  obtain ⟨U, E, hUK, hEK, hU, hU2, hEU, hE, hEcard⟩ :=
    exists_torus_of_markingA (n := 5) le_rfl hmarkK
  have hcycK : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S →
      IsCyclic S := fun S hS hS3 =>
    isCyclic_of_le_centralizer_of_torus hZ hUK hEK hU hU2 hEU hE hEcard
      (by omega) hS hS3
  have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKy, hPC.2.1, isQuasisimple_of_largeEvenMarking hmarkK⟩
  have hN := le_normalizer_of_isComponentOf_cyclic hcomp (fun S _ hSK hS3 => hcycK S hSK hS3)
    ⟨E, hEK, (haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩; IsPGroup.of_card hEcard),
      not_isCyclic_of_isElemAbelian_three_pow hE hEcard (by norm_num)⟩
  have hM := statedClassicalModel_of_markingA hmarkK hZ
  have hA2 : ∀ P : Sylow 3 ↥(Subgroup.centralizer (K : Set G)), IsCyclic P := fun P =>
    isCyclic_sylow_of_le_centralizer_of_forall hcycK le_rfl P
  have hyK : y ∉ K := by
    intro hyK'
    have : (⟨y, hyK'⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKy k.2) y (Set.mem_singleton y)).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact hy1 (congrArg Subtype.val this)
  have hA3 : twoLocalPrimeRank 3 G =
      twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) := by
    have h1 := le_twoLocalPrimeRank_centralizer_of_torus hy3 hy1 hKy hyK hUK hEK
      hU hU2 hEU hE hEcard
    have h2 : twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ twoLocalPrimeRank 3 G :=
      CFSG.LargeEvenClassification.Helpers.twoLocalPRank_subgroup_le
        (by norm_num : 1 < 3) (Subgroup.centralizer ({y} : Set G))
    have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
    omega
  have hA4 := ffNotWeaklyClosed_of_conj
    (FrameRoute.ggFrameA4Input_F4 hTBF hWI G B Bs x L D J hR hW hAt hq y hyB hy1)
  rcases hFF G hna hchar hKP 5 (Or.inl rfl) y hoy K hKy hN hM hA2 hA3 hA4 with hPSL | ⟨-, hlab⟩
  · exfalso
    obtain ⟨f, hf⟩ := hWK
    have hle := card_automizer_le_384_of_slTwo hPSL hBs.2.1 hcardBs hBs.2.2.2
      (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) (fun φ hφ => exists_conj_of_mem_join hφ)
    have h1152 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1152 := by
      rw [← Nat.card_congr f.toEquiv, FrameRoute.coxeterF4_eq]
      exact CFSG.RankThree.PartOne.K133H.card_weylGroup_F4
    omega
  · obtain ⟨e⟩ := nonempty_mulEquiv_ggU_E6_one_of_label hna hlab
    have hadm : StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl⟩
    have hrange : (e.symm.toMonoidHom).range = ggG0 3 B x L D J := by
      rw [hG0 G B Bs x L D J hR hW hq y K hNb hWK (Or.inr hmarkK) ⟨e⟩]
      exact MonoidHom.range_eq_top.mpr e.symm.surjective
    have hker : (e.symm.toMonoidHom).ker ≤ Subgroup.center (ggU .E6 0 1).K := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective]
      exact bot_le
    exact Or.inr (Or.inr ⟨.E6, 0, 1,
      ggSecFivePres_of_psi_of_admissible hadm (by decide) e.symm.toMonoidHom hker hrange⟩)

theorem ggF4QTwoEndsInput_of_split (hL : GGF4QTwoEndsLInput) (hK : GGF4QTwoEndsKInput) :
    ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
        GGInnerDiagOnLabel GGLabSp6 3 Bs L ∨
        (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
          LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1) := by
  intro G _ _ B Bs x L D J hR hW hq y K hN hF
  rcases hL G B Bs x L D J hR hW hq y K hN hF with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hK G B Bs x L D J hR hW hq y K hN hF h))

theorem ggSecFiveData_F4_qTwo
        (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input) (hEndsL : GGF4QTwoEndsLInput)
    (hEndsK : GGF4QTwoEndsKInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase p B Bs x D J)
    (hAt : GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄)
    (hq : GGInnerDiagOnLabel GGLabQTwo p Bs L) : GGSecFiveData p B x L D J := by
  have hp : p = 3 := p_eq_three_of_qTwo hR.1 hq
  subst hp
  obtain ⟨y, K, hNb, hWK⟩ := hAt
  rcases ggF4QTwoEndsInput_of_split hEndsL hEndsK G B Bs x L D J hR hW hq y K hNb hWK with
    hsp | ⟨n, hn, hmark⟩ | hmarkK
  · exact absurd hsp (not_ggInnerDiagOnLabel_sp6 hR.1)
  · exact ggSecFiveData_of_ff81b_typeA hFF hG0 hTBF hWI hR hW ⟨y, K, hNb, hWK⟩ hq hn hmark
  · exact ggSecFiveData_of_ff81b_nbr hFF hG0 hTBF hWI hR hW hq hNb hWK hmarkK

end CFSG.StandardType

end
