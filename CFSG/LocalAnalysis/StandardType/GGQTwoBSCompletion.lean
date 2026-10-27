module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDefs
import all CFSG.LocalAnalysis.StandardType.GGQTwoPhanDefs
public import Certificates.Certificate1649001
public import Certificates.Certificate725008
import CFSG.LocalAnalysis.StandardType.GGQTwoBSFamily
import CFSG.LocalAnalysis.StandardType.GGQTwoBSFive
import CFSG.LocalAnalysis.StandardType.GGQTwoBSStep
import CFSG.LocalAnalysis.StandardType.GGQTwoBSGen
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoPhanUniversalAt
    (hK : Nat.card K = 4) {n : ℕ} (hn : 5 ≤ n) : QTwoPhanUniversalAt K n := by
  induction n, hn using Nat.le_induction with
  | base => exact qTwoPhanUniversalAt_five hK
  | succ n hn ih => exact qTwoPhanUniversalAt_succ hK hn ih

private theorem bsc_rotSU_ne_one {F : Type} [Field F] (σ : F ≃+* F) :
    rotSU σ ≠ (1 : CFSG.LieType.Universal.Unitary.SUid σ 2) := by
  intro h
  have h' : (0 : F) = 1 := by
    simpa [rotSU, rotMat] using congrArg
      (fun g : CFSG.LieType.Universal.Unitary.SUid σ 2 =>
        (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)) h
  exact zero_ne_one h'

private theorem bsc_isQuasisimple (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n) :
    CFSG.IsQuasisimple (Su K 2 1 n) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) hF (n := n) (by omega) (by
      intro hcon
      have h1 : n = 3 := (Prod.mk.inj hcon).1
      omega)).1
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
      (p := 2) (f := 1) hF n)).symm h

private theorem bsc_exists_ne_one {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) (F : QTwoPhanFamily K G n)
    (ψ : Su K 2 1 (n + 1) →* G)
    (hFι : ∀ i, (F.ι i).range = U i)
    (hψι : ∀ i, ψ.comp (blockEmb2 K 2 1 n i) = F.ι i)
    (hn : 1 ≤ n) : ∃ k, ψ k ≠ 1 := by
  obtain ⟨e⟩ := hS.iso ⟨0, by omega⟩
  have hrot : rotSU (unitaryInvolution K 2 1) ≠ 1 :=
    bsc_rotSU_ne_one (unitaryInvolution K 2 1)
  let x : G := (e (rotSU (unitaryInvolution K 2 1)) : G)
  have hne : x ≠ 1 := by
    intro he
    change (e (rotSU (unitaryInvolution K 2 1)) : G) = 1 at he
    apply hrot
    have h1 : e (rotSU (unitaryInvolution K 2 1)) = e 1 := by
      apply Subtype.ext
      simpa using he
    exact e.injective h1
  have hmem : x ∈ U ⟨0, by omega⟩ :=
    (e (rotSU (unitaryInvolution K 2 1))).2
  rw [← hFι ⟨0, by omega⟩] at hmem
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨blockEmb2 K 2 1 n ⟨0, by omega⟩ k, ?_⟩
  rw [← MonoidHom.comp_apply, hψι ⟨0, by omega⟩, hk]
  exact hne

private theorem bsc_range_eq {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) (hK : Nat.card K = 4)
    (F : QTwoPhanFamily K G n) (ψ : Su K 2 1 (n + 1) →* G)
    (hFι : ∀ i, (F.ι i).range = U i)
    (hFθ : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), (F.θ i).range = W i ⟨i + 1, h⟩)
    (hψι : ∀ i, ψ.comp (blockEmb2 K 2 1 n i) = F.ι i)
    (hψθ : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ψ.comp (blockEmb3 K 2 1 n i h) = F.θ i)
    (hn : 5 ≤ n) : ψ.range = H := by
  have htop : (⊤ : Subgroup (Su K 2 1 (n + 1))) =
      ⨆ (i : ℕ) (h : i + 3 ≤ n + 1), (blockEmb K 2 1 (n + 1) 3 i h).range :=
    (iSup_range_blockEmb_three hK (by omega)).symm
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, htop]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => iSup_le fun hi => ?_
    have hin : i < n := by omega
    have hlt : i + 1 < n := by omega
    have hW : W ⟨i, hin⟩ ⟨i + 1, hlt⟩ ≤ H := by
      rw [← hS.gen]
      exact le_iSup₂_of_le ⟨i, hin⟩ ⟨i + 1, hlt⟩
        (le_iSup (fun _ : (⟨i, hin⟩ : Fin n) < ⟨i + 1, hlt⟩ => W _ _) (by simp))
    have hψ3 : ψ.comp (blockEmb K 2 1 (n + 1) 3 i hi) = F.θ ⟨i, hin⟩ := by
      simpa [blockEmb3] using hψθ ⟨i, hin⟩ hlt
    calc (blockEmb K 2 1 (n + 1) 3 i hi).range.map ψ
        = (F.θ ⟨i, hin⟩).range := by
          rw [← MonoidHom.range_comp, hψ3]
      _ = W ⟨i, hin⟩ ⟨i + 1, hlt⟩ := hFθ ⟨i, hin⟩ hlt
      _ ≤ H := hW
  · rw [← hS.gen]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    by_cases hsucc : (j : ℕ) = (i : ℕ) + 1
    · have hlt : (i : ℕ) + 1 < n := by
        have := j.isLt
        omega
      have hji : j = ⟨(i : ℕ) + 1, hlt⟩ := Fin.ext hsucc
      rw [hji, ← hFθ i hlt, ← hψθ i hlt, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    · have hfar : (i : ℕ) + 1 < (j : ℕ) := by
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega
      rw [hS.join i j hij hfar]
      refine sup_le ?_ ?_
      · rw [← hFι i, ← hψι i, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
      · rw [← hFι j, ← hψι j, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _

theorem bsCompletion_holds :
    BSCompletion := by
  intro K _ _ _ n G _ _ H U W hn hS
  have hK : Nat.card K = 4 := hS.card_four
  obtain ⟨F, hFι, hFθ⟩ := hS.exists_qTwoPhanFamily
  obtain ⟨ψ, hψι, hψθ⟩ := qTwoPhanUniversalAt hK hn F
  have hquasi : CFSG.IsQuasisimple (Su K 2 1 (n + 1)) :=
    bsc_isQuasisimple hK (by omega)
  have hnontriv : ∃ k, ψ k ≠ 1 := bsc_exists_ne_one hS F ψ hFι hψι (by omega)
  refine ⟨ψ, bsc_range_eq hS hK F ψ hFι hFθ hψι hψθ hn, ?_⟩
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hquasi hnontriv

end CFSG.StandardType.QTwo

end
