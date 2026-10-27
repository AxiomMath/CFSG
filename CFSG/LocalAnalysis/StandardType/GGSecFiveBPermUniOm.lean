module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKCalib
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Extension

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot (permSUHom)

theorem ggUniOmRecognition_holds :
    ∀ (f : ℕ) (F K : Type) [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
      (E : QuadExt F K (unitaryInvolution K 2 f)) (h : UnitaryFieldData 2 f K) (m : ℕ)
      (hm : 4 ≤ m) (H : Type) [Group H] (π : ↥(unitarySU 2 f K (m + 1)) →* H)
      (κ : normOmega E m →* H), Function.Injective κ →
      (∀ g, κ (uniEmb E h m g) = π (uniCast h m g)) →
      (∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
        π (permSUHom h (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))) * y *
            (π (permSUHom h (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))))⁻¹ ∈
          (anchorBlock E (by omega : 2 ≤ m)).map κ) →
      ∃ Ψ : normOmega E (m + 1) →* H, Function.Injective Ψ ∧
        (∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a) ∧
        (∀ g, Ψ (uniEmb E h (m + 1) g) = π g) ∧ Ψ.range = κ.range ⊔ π.range := by
  intro f F K _ _ _ _ _ E h m hm H _ π κ hκ hU1 hU2
  exact exists_normOmega_hom_of_unitary E h hm π κ hκ hU1 hU2

theorem ggSecFiveBPermUniOm_of_frames {G : Type} [Group G] [Finite G]
    {p f m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hm : 4 ≤ m)
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs L X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p)
    {π : Equiv.Perm (Fin (m + 1))}
    {σ : ↥(unitarySU 2 f K (m + 1)) →* G} {χL : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs L eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χK)
    (hJK : (σ.comp (uniCast hK m)).range ≤ X) :
    ∃ Ψ : normOmega E (m + 1) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ X := by
  have hRec := ggUniOmRecognition_holds
  have hp : p.Prime := Fact.out
  have hq : ¬(m = 3 ∧ 2 ^ f = 2) := fun h => absurd h.1 (by omega)
  obtain ⟨σ', hσ', hU1⟩ := exists_uniLFrame_calibrated hpq hK (by omega) hq hσ hκ
    (hσ.range_comp_uniCast_eq hp2 hK hpq (by omega) hq hκ hJK)
  obtain ⟨hu, huη⟩ := hσ'.permSUHom_swap_mem_normalizer hK hp hBs hAL (by omega)
    (⟨m - 2, by omega⟩ : Fin (m + 1)) (Fin.last m)
  have hnorm := hκ.map_anchorBlock_conj hBs hyB hX (by omega) hu huη
    (π.injective.ne (Fin.ne_of_val_ne (by simp only; omega)))
    (π.injective.ne (Fin.ne_of_val_ne (by simp only; omega)))
    (π.injective.ne (Fin.ne_of_val_ne (by simp only [Fin.val_last]; omega)))
    (π.injective.ne (Fin.ne_of_val_ne (by simp only [Fin.val_last]; omega)))
  have hU2 : ∀ z ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      σ' (permSUHom hK (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))) * z *
          (σ' (permSUHom hK (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ := by
    intro z hz
    rw [← hnorm]
    exact ⟨z, hz, rfl⟩
  obtain ⟨Ψ, hΨ, -, -, hΨr⟩ := hRec f F K E hK m hm G σ' κ hκ.1 hU1 hU2
  rw [hκ.2.1, hσ'.1, sup_comm] at hΨr
  exact ⟨Ψ, hΨ, hΨr⟩

private theorem ker_range_comp_mulEquiv_normOmega {G : Type} [Group G] {f m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (GaloisField 2 f) K]
    {E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)} {Ψ : normOmega E (m + 1) →* G}
    (hΨ : Function.Injective Ψ) {S : Type} [Group S] (eS : S ≃* normOmega E (m + 1)) :
    (Ψ.comp eS.toMonoidHom).ker ≤ Subgroup.center S ∧
      (Ψ.comp eS.toMonoidHom).range = Ψ.range := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have hz1 : z = 1 := by
      apply hΨ.comp eS.injective
      simp only [Function.comp_apply, map_one]
      exact hz
    rw [hz1]
    exact Subgroup.one_mem _
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eS.surjective,
      ← MonoidHom.range_eq_map]

section Spin


theorem exists_ggU_POmegaPlus_of_injective_normOmega {G : Type} [Group G] {f m : ℕ} (hm : 2 ≤ m)
    (hmo : Odd m) {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (GaloisField 2 f) K]
    {E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)} {Ψ : normOmega E (m + 1) →* G}
    (hΨ : Function.Injective Ψ) :
    ∃ ψ : (ggU .POmegaPlus (m + 1 + 1) f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (m + 1 + 1) f).K ∧ ψ.range = Ψ.range := by
  obtain ⟨eS⟩ := nonempty_spinPlus_mulEquiv_normOmega E hmo.add_one (by omega)
  have hgg : ggU .POmegaPlus (m + 1 + 1) f =
      ⟨spinGroup (Spin.quadPlus (m + 1 + 1) (GaloisField 2 f)),
        Spin.plusDatum (m + 1 + 1) (GaloisField 2 f) (by omega)⟩ := by
    simp only [ggU, lieUniversal, show 3 ≤ m + 1 + 1 by omega, ↓reduceDIte]
  rw [hgg]
  exact ⟨Ψ.comp eS.toMonoidHom, ker_range_comp_mulEquiv_normOmega hΨ eS⟩

theorem exists_ggU_POmegaMinus_of_injective_normOmega {G : Type} [Group G] {f m : ℕ} (hm : 2 ≤ m)
    (hme : Even m) {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (GaloisField 2 f) K]
    {E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)} {Ψ : normOmega E (m + 1) →* G}
    (hΨ : Function.Injective Ψ) :
    ∃ ψ : (ggU .POmegaMinus (m + 1 + 1) f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .POmegaMinus (m + 1 + 1) f).K ∧ ψ.range = Ψ.range := by
  obtain ⟨eS⟩ := nonempty_spinMinus_mulEquiv_normOmega E hme.add_one (by omega)
    (minusCoeffs_irr 2 f)
  exact ⟨Ψ.comp eS.toMonoidHom, ker_range_comp_mulEquiv_normOmega hΨ eS⟩

theorem exists_ggU_POmega_of_injective_normOmega {G : Type} [Group G] {f m : ℕ} (hm : 2 ≤ m)
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (GaloisField 2 f) K]
    {E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)} {Ψ : normOmega E (m + 1) →* G}
    (hΨ : Function.Injective Ψ) :
    (∃ ψ : (ggU .POmegaPlus (m + 1 + 1) f).K →* G,
        ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (m + 1 + 1) f).K ∧ ψ.range = Ψ.range) ∨
      ∃ ψ : (ggU .POmegaMinus (m + 1 + 1) f).K →* G,
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus (m + 1 + 1) f).K ∧ ψ.range = Ψ.range := by
  rcases Nat.even_or_odd m with hme | hmo
  · exact .inr (exists_ggU_POmegaMinus_of_injective_normOmega hm hme hΨ)
  · exact .inl (exists_ggU_POmegaPlus_of_injective_normOmega hm hmo hΨ)

end Spin


theorem ggSecFiveBPermUniOmInput_of_recognition (hMp : GGInnerDiagMpInput)
    : GGSecFiveBPermUniOmInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5 eta _ hAfull _ _ _ f K i0 hf hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hpq, y, hyBs, hKc, Kf, _, _, _, _, E, hKf, π, rfl, ⟨κ, χK, hκ⟩, σ, χL, hσ⟩ :=
    hcell.exists_frames hMp hR (by omega) hAfull fun h => absurd h (by omega)
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hJK : (σ.comp (uniCast hKf m)).range ≤ K :=
    hσ.range_comp_uniCast_le hKf hf hp (by omega) fun c d hcd hc hd =>
      hκ.ggBlockComm_le hBsC hyBs hKc (by omega) hcd hc hd
  obtain ⟨Ψ, hΨ, hΨr⟩ :=
    ggSecFiveBPermUniOm_of_frames hp2 hpq (by omega) hKf hBsC hyBs hKc hAfull hσ hκ hJK
  rw [← hΨr]
  exact exists_ggU_POmega_of_injective_normOmega (by omega) hΨ

theorem ggSecFiveBPermUniOmInput_of_mp (hMp : GGInnerDiagMpInput) : GGSecFiveBPermUniOmInput :=
  ggSecFiveBPermUniOmInput_of_recognition hMp

theorem ggSecFiveBPermUniQTwoOmInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermUniQTwoOmInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5 eta _ hAfull _ _ _ hz K i0 hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hpq, y, hyBs, hKc, Kf, _, _, _, _, E, hKf, π, rfl, ⟨κ, χK, hκ⟩, σ, χL, hσ⟩ :=
    hcell.exists_frames hMp hR (by omega) hAfull fun _ => hz
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨Ψ, hΨ, hΨr⟩ := ggSecFiveBPermUniOm_of_frames hp2 hpq
    (by omega) hKf hBsC hyBs hKc hAfull hσ hκ
    (hσ.range_comp_uniCast_le_of_omKFrame hBsC hyBs hKc hκ hKf (by omega))
  rw [← hΨr]
  exact exists_ggU_POmega_of_injective_normOmega (by omega) hΨ

end CFSG.StandardType

end
