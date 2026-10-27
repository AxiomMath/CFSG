module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.Quasithin.Background.E3Transport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauPair)
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem tauSp_torusHom (s : Fin 2 → Kˣ) :
    tauSp (torusHom s) = torusHom ![s 0 * s 1, s 0 * (s 1)⁻¹] := by
  apply statedSp_ext
  rw [CFSG.QuasithinUnique.Lin2.Five.coe_tauSp, coe_torusHom, coe_torusHom]
  ext r c
  rw [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply]
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauPair, mul_comm]

theorem tauPair_exists_not_mem {r k : Fin 2 ⊕ Fin 2} (hk : k ≠ r) :
    ¬ ((tauPair k).1 = (tauPair r).1 ∨ (tauPair k).1 = (tauPair r).2) ∨
      ¬ ((tauPair k).2 = (tauPair r).1 ∨ (tauPair k).2 = (tauPair r).2) := by
  rcases r with r | r <;> rcases k with k | k <;> fin_cases r <;> fin_cases k <;>
    simp_all [tauPair]

theorem tauSp_apply_eq_zero_of_stab_pair {g : StatedSp 2 K} {r : Fin 2 ⊕ Fin 2}
    (hg : ∀ j k : Fin 2 ⊕ Fin 2, (j = (tauPair r).1 ∨ j = (tauPair r).2) →
      ¬ (k = (tauPair r).1 ∨ k = (tauPair r).2) → (spMat g) k j = 0)
    {k : Fin 2 ⊕ Fin 2} (hk : k ≠ r) : (spMat (tauSp g)) k r = 0 := by
  rw [CFSG.QuasithinUnique.Lin2.Five.coe_tauSp, CFSG.QuasithinUnique.Lin2.Five.tauMat_apply]
  rcases tauPair_exists_not_mem hk with h | h
  · have h1 : (spMat g) (tauPair k).1 (tauPair r).1 = 0 :=
      hg _ _ (Or.inl rfl) h
    have h2 : (spMat g) (tauPair k).1 (tauPair r).2 = 0 :=
      hg _ _ (Or.inr rfl) h
    rw [h1, h2]
    simp
  · have h1 : (spMat g) (tauPair k).2 (tauPair r).2 = 0 :=
      hg _ _ (Or.inr rfl) h
    have h2 : (spMat g) (tauPair k).2 (tauPair r).1 = 0 :=
      hg _ _ (Or.inl rfl) h
    rw [h1, h2]
    simp

theorem tauSp_apply_eq_zero_of_fixes {g : StatedSp 2 K} {x : Fin 2 ⊕ Fin 2}
    (hg : ∀ k : Fin 2 ⊕ Fin 2, k ≠ x → (spMat g) k x = 0) {r k : Fin 2 ⊕ Fin 2}
    (hr : x = (tauPair r).1 ∨ x = (tauPair r).2)
    (hk : ¬ (x = (tauPair k).1 ∨ x = (tauPair k).2)) : (spMat (tauSp g)) k r = 0 := by
  rw [CFSG.QuasithinUnique.Lin2.Five.coe_tauSp, CFSG.QuasithinUnique.Lin2.Five.tauMat_apply]
  rcases hr with h | h
  · rw [← h]
    have h1 : (spMat g) (tauPair k).1 x = 0 :=
      hg _ fun h' => hk (Or.inl h'.symm)
    have h2 : (spMat g) (tauPair k).2 x = 0 :=
      hg _ fun h' => hk (Or.inr h'.symm)
    rw [h1, h2]
    simp
  · rw [← h]
    have h1 : (spMat g) (tauPair k).2 x = 0 :=
      hg _ fun h' => hk (Or.inr h'.symm)
    have h2 : (spMat g) (tauPair k).1 x = 0 :=
      hg _ fun h' => hk (Or.inl h'.symm)
    rw [h1, h2]
    simp

variable [Finite K]

theorem tauSp_tauSp_apply (g : StatedSp 2 K) (k j : Fin 2 ⊕ Fin 2) :
    (spMat (tauSp (tauSp g))) k j = (spMat g) k j ^ 2 := by
  rw [CFSG.QuasithinUnique.Lin2.Five.tauSp_tauSp,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp, Matrix.map_apply,
    CFSG.QuasithinUnique.Lin2.Five.frobAut_apply]

theorem map_tauSp_torus : (torus 2 K).map tauSp = torus 2 K := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_comap]
    exact ⟨![s 0 * s 1, s 0 * (s 1)⁻¹], (tauSp_torusHom s).symm⟩
  · rw [Subgroup.card_map_of_injective CFSG.QuasithinUnique.Lin2.Five.tauSp_bijective.1]

theorem torus_le_normalizer_map_tauSp {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) :
    torus 2 K ≤ Subgroup.normalizer ((H.map tauSp : Subgroup (StatedSp 2 K)) :
      Set (StatedSp 2 K)) := by
  calc torus 2 K = (torus 2 K).map tauSp := map_tauSp_torus.symm
    _ ≤ (Subgroup.normalizer (H : Set (StatedSp 2 K))).map tauSp :=
        Subgroup.map_mono hT
    _ ≤ Subgroup.normalizer ((H.map tauSp : Subgroup (StatedSp 2 K)) :
        Set (StatedSp 2 K)) := Subgroup.le_normalizer_map tauSp

theorem pRank_map_tauSp {p : ℕ} (hp : p.Prime) (H : Subgroup (StatedSp 2 K)) :
    CFSG.Open.pRank p (H.map tauSp) = CFSG.Open.pRank p H := by
  have h : (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := K)).toMonoidHom = tauSp :=
    MonoidHom.ext fun _ => rfl
  rw [← h]
  exact CFSG.Quasithin.E3.pRank_map_mulEquiv'
    (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := K)) hp H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
