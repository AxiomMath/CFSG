module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.E6Model
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRootO2

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.SeitzReduction CFSG.StandardType.GGSixE6Two CFSG.StandardType.GGHalf
open CFSG.Timmesfeld.LieEmbed
open CFSG.RankThree.GF2n.Smith81

private lemma map_centralizer_singleton_eq {G H : Type} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map φ =
      Subgroup.centralizer ({φ x} : Set H) ⊓ φ.range := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨by rw [← map_mul, ← map_mul, hh], ⟨h, rfl⟩⟩
  · rintro ⟨hy, ⟨h, rfl⟩⟩
    refine ⟨h, ?_, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact hy

private lemma equivMapOfInjective_symm_coe {G H : Type} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) {L : Subgroup G} (q : ↥(L.map φ)) :
    φ (((L.equivMapOfInjective φ hφ).symm q : ↥L) : G) = (q : H) := by
  conv_rhs => rw [← MulEquiv.apply_symm_apply (L.equivMapOfInjective φ hφ) q]
  rw [Subgroup.coe_equivMapOfInjective_apply]

private theorem radGeom_map {G H : Type} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ)
    {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)}
    {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (h : RadGeom t Q L eL π b) :
    RadGeom (φ t) (Q.map φ) (L.map φ)
      ((L.equivMapOfInjective φ hφ).symm.trans eL)
      (π.comp (Q.equivMapOfInjective φ hφ).symm.toMonoidHom)
      (φ b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h.t_mul_self, map_one]
  · intro h1
    exact h.t_ne_one (hφ (h1.trans (map_one φ).symm))
  · exact Subgroup.mem_map_of_mem φ h.t_mem
  · exact h.isPGroup.map φ
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hq' : t * q = q * t := (Subgroup.mem_centralizer_iff.mp (h.le_cen_Q hq)) t rfl
    rw [← map_mul, ← map_mul, hq']
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hl' : t * l = l * t := (Subgroup.mem_centralizer_iff.mp (h.le_cen_L hl)) t rfl
    rw [← map_mul, ← map_mul, hl']
  · rintro _ ⟨l, hl, rfl⟩ _ ⟨q, hq, rfl⟩
    have hq' : l * q * l⁻¹ ∈ Q := h.conj_mem l hl q hq
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem φ hq'
  · rw [← Subgroup.map_inf L Q φ hφ, h.inf_eq_bot, Subgroup.map_bot]
  · exact h.surj.comp (Q.equivMapOfInjective φ hφ).symm.surjective
  · intro q
    let q₀ : ↥Q := (Q.equivMapOfInjective φ hφ).symm q
    have hq₀ : φ (q₀ : G) = (q : H) := equivMapOfInjective_symm_coe φ hφ q
    change π q₀ = 1 ↔ (q : H) ∈ Subgroup.zpowers (φ t)
    rw [h.ker_iff q₀]
    have hmapz : (Subgroup.zpowers t).map φ = Subgroup.zpowers (φ t) := MonoidHom.map_zpowers φ t
    rw [← hmapz]
    constructor
    · intro hq0; exact ⟨q₀, hq0, hq₀⟩
    · rintro ⟨s, hs, hsq⟩
      have hsr : s = (q₀ : G) := hφ (hsq.trans hq₀.symm)
      simpa [hsr] using hs
  · intro l q hq
    let l₀ : ↥L := (L.equivMapOfInjective φ hφ).symm l
    let q₀ : ↥Q := (Q.equivMapOfInjective φ hφ).symm q
    have hl₀ : φ (l₀ : G) = (l : H) := equivMapOfInjective_symm_coe φ hφ l
    have hq₀ : φ (q₀ : G) = (q : H) := equivMapOfInjective_symm_coe φ hφ q
    have hmem : (l₀ : G) * (q₀ : G) * (l₀ : G)⁻¹ ∈ Q := h.conj_mem l₀ l₀.2 q₀ q₀.2
    have hval : φ ((⟨(l₀ : G) * (q₀ : G) * (l₀ : G)⁻¹, hmem⟩ : ↥Q) : G) =
        (l : H) * (q : H) * (l : H)⁻¹ := by
      rw [Subgroup.coe_mk, map_mul, map_mul, map_inv, hl₀, hq₀]
    have hsymm : (Q.equivMapOfInjective φ hφ).symm
        (⟨(l : H) * (q : H) * (l : H)⁻¹, hq⟩ : ↥(Q.map φ)) =
        ⟨(l₀ : G) * (q₀ : G) * (l₀ : G)⁻¹, hmem⟩ := by
      apply (Q.equivMapOfInjective φ hφ).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_equivMapOfInjective_apply, hval]
    change Multiplicative.toAdd (π ((Q.equivMapOfInjective φ hφ).symm
        (⟨(l : H) * (q : H) * (l : H)⁻¹, hq⟩ : ↥(Q.map φ)))) =
      cubeAct (((L.equivMapOfInjective φ hφ).symm.trans eL) l)
        (Multiplicative.toAdd (π ((Q.equivMapOfInjective φ hφ).symm q)))
    rw [hsymm]
    change Multiplicative.toAdd (π (⟨(l₀ : G) * (q₀ : G) * (l₀ : G)⁻¹, hmem⟩ : ↥Q)) =
      cubeAct (eL l₀) (Multiplicative.toAdd (π q₀))
    exact h.equivariant l₀ q₀ hmem
  · exact Subgroup.mem_map_of_mem φ h.b_mem
  · show eL ((L.equivMapOfInjective φ hφ).symm ⟨φ b, _⟩) = bStd
    rw [show (L.equivMapOfInjective φ hφ).symm ⟨φ b, _⟩ = ⟨b, h.b_mem⟩ from by
      apply (L.equivMapOfInjective φ hφ).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_equivMapOfInjective_apply]]
    exact h.b_mark

theorem exists_radGeom_of_embedding
    {G : Type} [Group G] (φ : EC →* G) (hφ : Function.Injective φ) {Q : Subgroup G}
    (hQ : Q = pCoreOf 2 (Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range))
    (hQL : Q ⊓ lE.map φ = ⊥ ∧ Q ⊔ lE.map φ =
      Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range) :
    ∃ (eL : ↥(lE.map φ) ≃* SL(6, ZMod 2))
      (π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))) (b' : G),
      RadGeom (φ (xr (highRoot .E6))) Q (lE.map φ) eL π b' ∧
      ∃ c : EC, φ c * φ zE * (φ c)⁻¹ = b' := by
  classical
  obtain ⟨eL₀, π₀, hRad, hsup, hconj⟩ := exists_radGeom_model
  let R : Subgroup EC := EPilot.highRadical .E6 F2
  let C₀ : Subgroup EC := Subgroup.centralizer ({xr (highRoot .E6)} : Set EC)
  let HY : Subgroup G :=
    Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range
  have hQ' : Q = pCoreOf 2 HY := hQ
  have hQL' : Q ⊓ lE.map φ = ⊥ ∧ Q ⊔ lE.map φ = HY := hQL
  have hHYmap : C₀.map φ = HY := map_centralizer_singleton_eq φ hφ (xr (highRoot .E6))
  have hmL : R.map φ ⊔ lE.map φ = HY := by
    rw [← Subgroup.map_sup R lE φ, hsup, hHYmap]
  have hC₀norm : C₀ ≤ Subgroup.normalizer (R : Set EC) := by
    rw [show C₀ = R ⊔ lE from hsup.symm]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.le_normalizer_iff]
    intro l hl q hq
    exact hRad.conj_mem l hl q hq
  have hm0HY : R.map φ ≤ HY := by
    rw [← hHYmap]
    exact Subgroup.map_mono (le_sup_left.trans hsup.le)
  have hHYnorm : HY ≤ Subgroup.normalizer (R.map φ : Set G) := by
    rw [← hHYmap]
    exact (Subgroup.map_mono hC₀norm).trans (Subgroup.le_normalizer_map φ)
  have hm0Q : R.map φ ≤ Q := by
    rw [hQ']
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hm0HY hHYnorm
      (hRad.isPGroup.map φ)
  have hL'norm : lE.map φ ≤ Subgroup.normalizer (R.map φ : Set G) := by
    have hlE : lE ≤ Subgroup.normalizer (R : Set EC) :=
      (le_sup_right.trans hsup.le).trans hC₀norm
    exact (Subgroup.map_mono hlE).trans (Subgroup.le_normalizer_map φ)
  have hQeq : Q = R.map φ := by
    have hmod := Subgroup.inf_sup_assoc_of_le (H := lE.map φ) (K := Q) (N := R.map φ)
      hL'norm hm0Q
    rw [hQL'.1, sup_comm (lE.map φ) (R.map φ), hmL] at hmod
    rw [bot_sup_eq, inf_eq_left.mpr (le_sup_left.trans hQL'.2.le)] at hmod
    exact hmod.symm
  have hRad' : RadGeom (xr (highRoot .E6)) R lE eL₀ π₀ (eL₀.symm bStd : EC) := hRad
  subst hQeq
  let eL : ↥(lE.map φ) ≃* SL(6, ZMod 2) :=
    (Subgroup.equivMapOfInjective lE φ hφ).symm.trans eL₀
  let π : ↥(R.map φ) →* Multiplicative (A5Cube.Cube (ZMod 2)) :=
    π₀.comp (Subgroup.equivMapOfInjective R φ hφ).symm.toMonoidHom
  let b' : G := φ (eL₀.symm bStd : EC)
  refine ⟨eL, π, b', radGeom_map φ hφ hRad', ?_⟩
  obtain ⟨c, hc⟩ := hconj
  exact ⟨c, by
    have h := congrArg φ hc
    simpa only [map_mul, map_inv] using h⟩

private theorem pCoreOf_map_injective {G G' : Type*} [Group G] [Group G'] (r : ℕ) (f : G →* G')
    (hf : Function.Injective f) (H : Subgroup G) :
    pCoreOf r (H.map f) = (pCoreOf r H).map f := by
  unfold pCoreOf
  let φ : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv r φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem pCoreOf_inf_eq_bot_and_sup_eq_of_embedding
    {G : Type} [Group G] (φ : EC →* G) (hφ : Function.Injective φ) :
    pCoreOf 2 (Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range) ⊓ lE.map φ = ⊥ ∧
      pCoreOf 2 (Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range) ⊔ lE.map φ =
        Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range := by
  classical
  let R : Subgroup EC := EPilot.highRadical .E6 F2
  let C₀ : Subgroup EC := Subgroup.centralizer ({xr (highRoot .E6)} : Set EC)
  obtain ⟨-, hsup, hinf, -⟩ :=
    EPilot.isTwoRadicalDecomp_highRoot (τ := .E6) (K := F2) (Or.inl rfl) (c := 1) one_ne_zero
  have hlE : lE = EPilot.perpLevi .E6 F2 := rfl
  have hC₀sup : R ⊔ lE = C₀ := by
    rw [hlE]
    simpa [C₀, R, xr, EPilot.pinnedElt] using hsup
  have hC₀inf : R ⊓ lE = ⊥ := by
    rw [hlE]
    simpa [R] using hinf
  have hpc : pCoreOf 2 C₀ = R := by
    simpa [C₀, R] using pCoreOf_centralizer_xr_highRoot
  have hmapC : C₀.map φ =
      Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range := by
    simpa [C₀] using map_centralizer_singleton_eq φ hφ (xr (highRoot .E6))
  have hpcHY : pCoreOf 2
      (Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) ⊓ φ.range) = R.map φ := by
    rw [← hmapC, pCoreOf_map_injective 2 φ hφ, hpc]
  refine ⟨?_, ?_⟩
  · rw [hpcHY, ← Subgroup.map_inf R lE φ hφ, hC₀inf, Subgroup.map_bot]
  · rw [hpcHY, ← Subgroup.map_sup R lE φ, hC₀sup, hmapC]

end CFSG.StandardType.FF81.CentE6
