module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorOverlap
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalPairs
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.Permutation.SymmetricCoxeter
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.GroupTheory.CentralizerMap
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorExt

public section

namespace CFSG.StandardType

private theorem oaP_isComponentOf_map_conj {G : Type} [Group G] {L : Subgroup G} {x w : G}
    (hQ : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) :
    CFSG.Open.IsComponentOf (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({w * x * w⁻¹} : Set G)) := by
  have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj w) hQ
  rw [CFSG.centralizer_singleton_map] at h
  exact h

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.Permutation.SymmetricCoxeter

section Context

theorem exists_permHom_of_qTwoOrth {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {k : ℕ}
    (eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod p))) {i0 : Fin (k + 4)}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (k + 4) p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel (k + 4) p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull (k + 4) p)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G)) {j : Fin (k + 4)} (hj : j ≠ i0)
    (hact : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap i0 j)) :
    p = 3 ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt F K (unitaryInvolution K 2 1)), Nat.card F = 2 ∧
        ∃ (π : Fin (k + 4) ≃ Fin (k + 4)) (κ₁ κ₂ : normOmega E (k + 3) →* G)
          (χ : Multiplicative (ZMod p) →* Kˣ) (t : Equiv.Perm (Fin (k + 4)) →* G),
          π (Fin.last (k + 3)) = i0 ∧ π 0 = j ∧
          GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ ∧
          GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
            ((finRotate (k + 4)).trans π) κ₂ χ ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
            κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)) ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
            κ₂.comp (normPerm E (by omega : 3 ≤ k + 3)) ∧
          ∀ y : normOmega E (k + 2),
            κ₁ (normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3)) *
                normOmegaCast E (by omega : k + 2 ≤ k + 3) y *
                (normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3)))⁻¹) =
              κ₂ (normOmegaCast E (by omega : k + 2 ≤ k + 3) y) := by
  classical
  obtain ⟨hp3, hZ, hN, F, K, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2, π', hπ', κ, χ,
    hframe⟩ := exists_omKFrame_of_qTwoOrth hcfg (by omega : 4 ≤ k + 4) eta hL hLab
  obtain rfl : p = 3 := hp3
  have hπ'' : π' (Fin.last (k + 3)) = i0 := hπ'
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      (hcfg.1.2.2.2.2.2.2.1.2.2.2.1 : CFSG.Assembly.IsComponentOf L
        (Subgroup.centralizer ({x} : Set G)))
  have hcut : ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) :=
    ggBstar_mem_iff_coord_eq_one hcfg hZ hN eta i0 hL
  have hBmap : Bs.map (MulAut.conj w).toMonoidHom = Bs :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hy₂ : w * x * w⁻¹ ∈ Bs := by
    rw [← hBmap]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hxBs
  have hLwc : CFSG.Open.IsComponentOf (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({w * x * w⁻¹} : Set G)) :=
    oaP_isComponentOf_map_conj hLc
  have hframe₂ : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
      (π'.trans (Equiv.swap i0 j)) ((MulAut.conj w).toMonoidHom.comp κ) χ :=
    hframe.conj_transporter hw hact
  have hX₁ : ∀ b : ↥Bs, (b : G) ∈ L → eta b (π' (Fin.last (k + 3))) = 1 := by
    intro b hb
    simpa [hπ''] using (hcut b).mp hb
  have hX₂ : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom →
      eta b ((π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3))) = 1 := by
    intro b hb
    have hbj : eta b (Equiv.swap i0 j i0) = 1 :=
      (mem_map_conj_iff_coord_eq_one hw hact hcut b).mp hb
    simpa [Equiv.trans_apply, hπ'', Equiv.swap_apply_left] using hbj
  have hne : π' (Fin.last (k + 3)) ≠
      (π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3)) := by
    rw [Equiv.trans_apply, hπ'', Equiv.swap_apply_left]
    exact fun h => hj h.symm
  obtain ⟨π₁', π₂', κ₁', κ₂', h₁', h₂', hπ₁'_last, hπ₂'_last, hπ₂'_eq, hpoint, hperm⟩ :=
    GGSecFiveBPermOmKFrame.exists_overlap_calibration_of_component
      (E := E) (k := k) (n := k + 4) (X₁ := L)
      (X₂ := L.map (MulAut.conj w).toMonoidHom) (y₁ := x) (y₂ := w * x * w⁻¹)
      hframe hframe₂ hSC hxBs hLc hy₂ hLwc hX₁ hX₂ hne
  have hπ₁'_last' : π₁' (Fin.last (k + 3)) = i0 := hπ₁'_last.trans hπ''
  have hπ₂_last : (π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3)) = j := by
    simp [Equiv.trans_apply, hπ'']
  have hπ₁'_zero : π₁' 0 = j := by
    have h := hπ₂'_last
    rw [hπ₂'_eq, Equiv.trans_apply, finRotate_last, hπ₂_last] at h
    exact h
  have hrot_u : finRotate (k + 4) (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))) =
      (⟨k + 2, by omega⟩ : Fin (k + 4)) := by
    simpa using finRotate_of_lt (n := k + 3) (k := k + 1) (by omega : k + 1 < k + 3)
  have hrot_v : finRotate (k + 4) (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3))) =
      (⟨k + 3, by omega⟩ : Fin (k + 4)) := by
    simpa using finRotate_of_lt (n := k + 3) (k := k + 2) (by omega : k + 2 < k + 3)
  have hπ₂'_u : π₂' (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))) =
      π₁' (⟨k + 2, by omega⟩ : Fin (k + 4)) := by
    rw [hπ₂'_eq, Equiv.trans_apply, hrot_u]
  have hπ₂'_v : π₂' (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3))) =
      π₁' (⟨k + 3, by omega⟩ : Fin (k + 4)) := by
    rw [hπ₂'_eq, Equiv.trans_apply, hrot_v]
  have hdisj : Disjoint
      ({π₁' (Fin.castSucc (⟨0, by omega⟩ : Fin (k + 3))),
        π₁' (Fin.castSucc (⟨1, by omega⟩ : Fin (k + 3)))} : Finset (Fin (k + 4)))
      ({π₂' (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))),
        π₂' (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3)))} : Finset (Fin (k + 4))) := by
    rw [hπ₂'_u, hπ₂'_v, Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with hb | hb
    all_goals
      have h := congrArg Fin.val (π₁'.injective hb)
      simp only [Fin.val_castSucc] at h
      omega
  have h01 : (⟨0, by omega⟩ : Fin (k + 3)) ≠ ⟨1, by omega⟩ := by
    intro h
    have h' := congrArg Fin.val h
    simp only at h'
    omega
  have hk12 : (⟨k + 1, by omega⟩ : Fin (k + 3)) ≠ ⟨k + 2, by omega⟩ := by
    intro h
    have h' := congrArg Fin.val h
    simp only at h'
    omega
  have hcomm := GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_componentFrame
    (F := F) (K := K) (E := E) (G := G) (B := B) (Bs := Bs) (L := L) (D := D) (J := J)
    (x := x) (n := k + 4) (r := k + 3) hF2 (by omega : 3 ≤ k + 3) hcfg hZ hN
    (eta := eta) (i0 := i0) hL (π := π₁') hπ₁'_last' h₁' h𝒦 hG0 (by omega : 4 ≤ k + 4)
    (F' := F) (K' := K) (E' := E) (f' := 1) (X := L.map (MulAut.conj w).toMonoidHom)
    (s := k + 3) (by omega : 3 ≤ k + 3) hy₂ hLwc h₂'
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) h01
    (u := ⟨k + 1, by omega⟩) (v := ⟨k + 2, by omega⟩) hk12 hdisj
  let f : Equiv.Perm (Fin (k + 3)) →* G := κ₁'.comp (normPerm E (by omega : 3 ≤ k + 3))
  let g : Equiv.Perm (Fin (k + 3)) →* G := κ₂'.comp (normPerm E (by omega : 3 ≤ k + 3))
  have hCross : Commute (f (adjSwap (k + 2) 0)) (g (adjSwap (k + 2) (k + 1))) := by
    rw [adjSwap_of_lt (by omega : 0 < k + 2),
      adjSwap_of_lt (by omega : k + 1 < k + 2)]
    simpa only [f, g, MonoidHom.comp_apply] using hcomm
  obtain ⟨t, ht₁, ht₂⟩ :=
    CFSG.Permutation.SymmetricCoxeter.exists_hom_perm_of_overlap (m := k) f g hperm hCross
  refine ⟨rfl, hZ, hN, F, K, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2,
    π₁', κ₁', κ₂', χ, t, hπ₁'_last', hπ₁'_zero, h₁', ?_, ?_, ?_, hpoint⟩
  · simpa [hπ₂'_eq] using h₂'
  · simpa only [f] using ht₁
  · simpa only [g] using ht₂

theorem exists_normOmega_hom_of_qTwoOrth {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {k : ℕ}
    (hk : 1 ≤ k) (eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod p))) {i0 : Fin (k + 4)}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (k + 4) p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel (k + 4) p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull (k + 4) p)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G)) {j : Fin (k + 4)} (hj : j ≠ i0)
    (hact : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap i0 j)) :
    p = 3 ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt F K (unitaryInvolution K 2 1)), Nat.card F = 2 ∧
        ∃ (π : Fin (k + 4) ≃ Fin (k + 4)) (κ₁ κ₂ : normOmega E (k + 3) →* G)
          (χ : Multiplicative (ZMod p) →* Kˣ) (t : Equiv.Perm (Fin (k + 4)) →* G)
          (Ψ : normOmega E (k + 4) →* G),
          π (Fin.last (k + 3)) = i0 ∧ π 0 = j ∧
          GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ ∧
          GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
            ((finRotate (k + 4)).trans π) κ₂ χ ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
            κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)) ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
            κ₂.comp (normPerm E (by omega : 3 ≤ k + 3)) ∧
          (∀ y : normOmega E (k + 2),
            κ₁ (normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3)) *
                normOmegaCast E (by omega : k + 2 ≤ k + 3) y *
                (normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3)))⁻¹) =
              κ₂ (normOmegaCast E (by omega : k + 2 ≤ k + 3) y)) ∧
          (∀ (σ : Equiv.Perm (Fin (k + 3)))
            (hσ : κ₁ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ Subgroup.normalizer (Bs : Set G)),
            MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
              ((Fin.castSuccEmb (n := k + 3)).trans π.toEmbedding) σ)) ∧
          (∀ (σ : Equiv.Perm (Fin (k + 3)))
            (hσ : κ₂ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ Subgroup.normalizer (Bs : Set G)),
            MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
              ((Fin.castSuccEmb (n := k + 3)).trans ((finRotate (k + 4)).trans π).toEmbedding)
              σ)) ∧
          Function.Injective Ψ ∧
          (∀ a, Ψ (normOmegaCast E (Nat.le_succ (k + 3)) a) = κ₁ a) ∧
          (∀ σ, Ψ (normPerm E (by omega : 3 ≤ k + 4) σ) = t σ) ∧ Ψ.range = L ⊔ t.range := by
  obtain ⟨hp3, hZ, hN, F, K, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2, π, κ₁, κ₂,
    χ, t, hlast, hzero, h₁, h₂, ht₁, ht₂, hpoint⟩ :=
    exists_permHom_of_qTwoOrth hcfg eta hL hLab h𝒦 hG0 hw hj hact
  obtain rfl : p = 3 := hp3
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      (hcfg.1.2.2.2.2.2.2.1.2.2.2.1 : CFSG.Assembly.IsComponentOf L
        (Subgroup.centralizer ({x} : Set G)))
  have hcut : ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) :=
    ggBstar_mem_iff_coord_eq_one hcfg hZ hN eta i0 hL
  have hX₁ : ∀ b : ↥Bs, (b : G) ∈ L → eta b (π (Fin.last (k + 3))) = 1 := by
    intro b hb
    rw [hlast]
    exact (hcut b).mp hb
  have hX₂ : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom → eta b (π 0) = 1 := by
    intro b hb
    have hbj := (mem_map_conj_iff_coord_eq_one hw hact hcut b).mp hb
    rw [hzero]
    simpa only [Equiv.swap_apply_left] using hbj
  obtain ⟨Ψ, hΨinj, hΨcast, hΨperm, hΨrange⟩ :=
    GGSecFiveBPermOmKFrame.exists_normOmega_hom_of_permHom (E := E) hk hSC h₁ hxBs hLc h₂ hX₂
      ht₁ ht₂
  refine ⟨rfl, hZ, hN, F, K, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2,
    π, κ₁, κ₂, χ, t, Ψ, hlast, hzero, h₁, h₂, ht₁, ht₂, hpoint, ?_, ?_, hΨinj, hΨcast,
    hΨperm, hΨrange⟩
  · intro σ hσ
    exact GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last (E := E) h₁ (by omega) hSC hX₁
      σ hσ
  · intro σ hσ
    have hX₂' : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom →
        eta b (((finRotate (k + 4)).trans π) (Fin.last (k + 3))) = 1 := by
      intro b hb
      rw [Equiv.trans_apply, finRotate_last]
      exact hX₂ b hb
    exact GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last (E := E) h₂ (by omega) hSC hX₂'
      σ hσ

end Context

end CFSG.StandardType

end
