module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniSpChart
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJoinTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoSUThreeDiagonalComm
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenRestrictedTriples
import CFSG.LocalAnalysis.StandardType.GGSecFiveDataSpSpTwo
import CFSG.ClassicalInvolution.WeakCT.SpSpGlue

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed)
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem exists_enum_of_card_three {n r : ℕ} (hr : 3 ≤ r) {π : Fin (r + 2) ≃ Fin n}
    {S : Finset (Fin n)} (hS : S.card = 3) (h0 : π 0 ∉ S) :
    ∃ σ : Fin 3 → Fin (r + 1), Function.Injective σ ∧ ¬ Function.Surjective σ ∧
      (Set.range fun l => π (σ l).succ) = (S : Set (Fin n)) := by
  classical
  let e : Fin 3 ≃ S := (Fin.castOrderIso hS.symm).toEquiv.trans S.equivFin.symm
  have hne : ∀ l, π.symm (e l : Fin n) ≠ 0 := by
    intro l h
    apply h0
    rw [← h, Equiv.apply_symm_apply]
    exact (e l).2
  let σ : Fin 3 → Fin (r + 1) := fun l => (π.symm (e l : Fin n)).pred (hne l)
  have hσ : ∀ l, π (σ l).succ = (e l : Fin n) := by
    intro l
    simp [σ]
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro l m hlm
    have h := congrArg (fun i => π i.succ) hlm
    simp only [hσ] at h
    exact e.injective (Subtype.ext h)
  · intro hsurj
    have := Fintype.card_le_of_surjective σ hsurj
    simp only [Fintype.card_fin] at this
    omega
  · ext x
    simp only [Set.mem_range, hσ, Finset.mem_coe]
    constructor
    · rintro ⟨l, rfl⟩
      exact (e l).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩

theorem GGSecFiveBPermSpPlaneFrame.ggBlockComm_le_of_card_three [Finite G] {p n r : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hr : 3 ≤ r)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {S : Finset (Fin n)} (hS : S.card = 3) (h0 : π 0 ∉ S) :
    ggBlockComm Bs eta (S : Set (Fin n)) ≤ K := by
  obtain ⟨σ, hσ, hσs, hrange⟩ := exists_enum_of_card_three hr hS h0
  rw [← hrange, ggSecFiveBPermZeta_commutator_centralizer_eq_of_or (k := 2) hp2
    (Or.inr le_rfl) hBs hyB hK hκ σ hσ hσs, MonoidHom.range_comp]
  exact (Subgroup.map_le_range _ _).trans hκ.2.1.le

section Assembly

open CFSG.ClassicalGroups.UnitaryFlag


theorem ggSecFiveBPermUniQTwoSpInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermUniQTwoSpInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5 eta _ hAfull _ _ _ hZ K i0 hcell hLK
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  obtain ⟨y, hyBs, hKc, π, _, ⟨κ, ζ, hκ⟩, F, _, _, σ, χ, hUF, hLF⟩ :=
    GGSecFiveBPermUniSpCell.exists_frames hMp hR (r := s + 1) (by omega) hAfull le_rfl
      (fun _ => hZ) hcell
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have h01 : π 0 ≠ π 1 := π.injective.ne (Fin.ne_of_val_ne (by simp))
  have h03 : π 0 ≠ π 3 := π.injective.ne (Fin.ne_of_val_ne (by
    rw [Fin.val_zero]
    show 0 ≠ 3 % (s + 1 + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega))
  obtain ⟨g, hgL, hg, hgη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h01
  obtain ⟨w, -, hw, hwη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h03
  obtain ⟨κ₂, hκ₂, hκ₂r, hov, hlong, hcross⟩ :=
    ggSecFiveBPermZeta_overlap_of_swap_charTwo (s := s) hp2 (by omega) hBsC hyBs hKc hκ hg hgη
      hw hwη
  obtain ⟨κ₂', hκ₂', hκ₂'r, hsh, hlo, hc1, hc2⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_spSpCharts_of_overlap (s := s) (by omega) hκ.1 hκ₂
      hov hlong hcross
  have hjoin : K ⊔ K.map (MulAut.conj g).toMonoidHom = L ⊔ K :=
    hLF.sup_map_conj_eq_of_triples
      (SuNsRootGen.iSup_blockSU_triples_avoid_pair hUF (by omega) _ _ (π.symm.injective.ne h01))
      (fun S hS => hLF.map_blockSU_triple_le_ggBlockComm hUF hp S hS) hgL hg hgη
      (fun S hS h0 => hκ.ggBlockComm_le_of_card_three hp2 (by omega) hBsC hyBs hKc hS h0)
  exact ggSecFiveData_of_spSpCharts_two (s := s) (by omega) κ κ₂' hκ.1 hκ₂' hsh hlo hc1 hc2
    (by rw [hLK, ← hjoin, hκ.2.1, hκ₂'r, hκ₂r])

end Assembly

end CFSG.StandardType

end
