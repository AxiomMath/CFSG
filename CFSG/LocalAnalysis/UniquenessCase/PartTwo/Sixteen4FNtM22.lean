module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtTwoGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtM22Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtM22Class
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate2195
public import Certificates.Certificate260402
public import Certificates.Certificate260403
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.G9GolayM22
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.J1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem w183_m22_fix_eq_zero {Γ : Type} [Group Γ] {Q : Type} [AddCommGroup Q]
    [Module (ZMod 2) Q] (ρ : Representation (ZMod 2) Γ Q) (hρ : ρ.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) Q = 10) :
    ∀ q : Q, (∀ g : Γ, ρ g q = q) → q = 0 := by
  intro q hq
  by_contra hq0
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span (ZMod 2) ({q} : Set Q)
      apply_mem_toSubmodule := by
        intro g v hv
        have hmap : (Submodule.span (ZMod 2) ({q} : Set Q)).map (ρ g) ≤
            Submodule.span (ZMod 2) ({q} : Set Q) := by
          rw [Submodule.map_span]
          apply Submodule.span_le.mpr
          rintro x ⟨y, hy, rfl⟩
          rw [Set.mem_singleton_iff] at hy
          rw [hy, hq g]
          exact Submodule.subset_span (Set.mem_singleton q)
        exact hmap (Submodule.mem_map.mpr ⟨v, hv, rfl⟩) }
  rcases hρ.eq_bot_or_eq_top S with hbot | htop
  · have hqmem : q ∈ S := Submodule.subset_span (Set.mem_singleton q)
    rw [hbot] at hqmem
    have hq0' : q ∈ (⊥ : Submodule (ZMod 2) Q) := hqmem
    exact hq0 ((Submodule.mem_bot (ZMod 2)).mp hq0')
  · have hspan : Submodule.span (ZMod 2) ({q} : Set Q) = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule htop
      change Submodule.span (ZMod 2) ({q} : Set Q) = ⊤ at h
      exact h
    have h1 : Module.finrank (ZMod 2) Q = 1 := by
      rw [← finrank_top (ZMod 2) Q, ← hspan, finrank_span_singleton hq0]
    omega

private theorem w183_m22_finrank_range_norm_congr {Q Q' : Type} [AddCommGroup Q]
    [Module (ZMod 2) Q] [AddCommGroup Q'] [Module (ZMod 2) Q'] (L : Q ≃ₗ[ZMod 2] Q')
    {A : Q →ₗ[ZMod 2] Q} {B : Q' →ₗ[ZMod 2] Q'} (h : ∀ x, L (A x) = B (L x)) (n : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range n, A ^ i)) =
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range n, B ^ i)) := by
  have key : ∀ x : Q, (L : Q →ₗ[ZMod 2] Q') (A x) = B ((L : Q →ₗ[ZMod 2] Q') x) :=
    fun x => h x
  have hpow : ∀ i : ℕ, ∀ x : Q,
      (L : Q →ₗ[ZMod 2] Q') ((A ^ i) x) = (B ^ i) ((L : Q →ₗ[ZMod 2] Q') x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
        intro x
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih (A x), key x]
  have hcomp : ∀ x : Q, (L : Q →ₗ[ZMod 2] Q') ((∑ i ∈ Finset.range n, A ^ i) x) =
      (∑ i ∈ Finset.range n, B ^ i) ((L : Q →ₗ[ZMod 2] Q') x) := by
    intro x
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hpow i x
  have hmap : (LinearMap.range (∑ i ∈ Finset.range n, A ^ i)).map
      (L : Q →ₗ[ZMod 2] Q') = LinearMap.range (∑ i ∈ Finset.range n, B ^ i) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := hx
      rw [hcomp z]
      exact ⟨(L : Q →ₗ[ZMod 2] Q') z, rfl⟩
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(∑ i ∈ Finset.range n, A ^ i) (L.symm z), ⟨L.symm z, rfl⟩, ?_⟩
      rw [hcomp]
      congr 1
      exact L.apply_symm_apply z
  have h := LinearEquiv.finrank_map_eq L (LinearMap.range (∑ i ∈ Finset.range n, A ^ i))
  rw [hmap] at h
  exact h.symm

theorem s16nt_h1_m22
    {Γ : Type} [Group Γ] [Finite Γ]
    (e : Γ ≃* ↥CFSG.Blueprint.NativeSporadic.M22) {Q : Type} [AddCommGroup Q]
    [Module (ZMod 2) Q] [Finite Q] (ρ : Representation (ZMod 2) Γ Q) (hρ : ρ.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) Q = 10) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) ≤ 4 := by
  classical
  obtain ⟨Q₀, hQ₀add, hQ₀mod, hQ₀fin, ρ₀, a, b, hρ₀, hdim₀, hn₀, hgen, ha2, hb4, hra, hrb⟩ :=
    s16nt_m22_module
  letI : AddCommGroup Q₀ := hQ₀add
  letI : Module (ZMod 2) Q₀ := hQ₀mod
  letI : Finite Q₀ := hQ₀fin
  have hfix : ∀ q : Q, (∀ g : Γ, ρ g q = q) → q = 0 := w183_m22_fix_eq_zero ρ hρ hdim
  have hn : ∃ g : Γ, ρ g ≠ 1 := by
    by_contra hcon
    rw [not_exists] at hcon
    have htriv : ∀ g : Γ, ρ g = 1 := fun g => not_not.mp (hcon g)
    haveI : Nontrivial Q :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hdim]; norm_num)
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    exact hq (w183_m22_fix_eq_zero ρ hρ hdim q fun g => by rw [htriv g]; rfl)
  obtain ⟨ψ, hL⟩ := s16nt_m22_two_irr (e₁ := MulEquiv.refl _) (e₂ := e)
    (ρ₁ := ρ₀) (ρ₂ := ρ) hρ₀ hρ hdim₀ hdim hn₀ hn
  let a' : Γ := ψ.symm a
  let b' : Γ := ψ.symm b
  have hψa : ψ a' = a := ψ.apply_symm_apply a
  have hψb : ψ b' = b := ψ.apply_symm_apply b
  have hgen' : Subgroup.closure ({a', b'} : Set Γ) = ⊤ := by
    have hmap := MonoidHom.map_closure (ψ.symm : ↥CFSG.Blueprint.NativeSporadic.M22 →* Γ)
      ({a, b} : Set ↥CFSG.Blueprint.NativeSporadic.M22)
    have himg : (ψ.symm : ↥CFSG.Blueprint.NativeSporadic.M22 →* Γ) ''
        ({a, b} : Set ↥CFSG.Blueprint.NativeSporadic.M22) = ({a', b'} : Set Γ) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨a, Or.inl rfl, rfl⟩
        · exact ⟨b, Or.inr rfl, rfl⟩
    rw [hgen, Subgroup.map_top_of_surjective _ (MulEquiv.surjective ψ.symm), himg] at hmap
    exact hmap.symm
  have ha' : a' ^ 2 = 1 := by
    change (ψ.symm a) ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  have hb' : b' ^ 4 = 1 := by
    change (ψ.symm b) ^ 4 = 1
    rw [← map_pow, hb4, map_one]
  have hbound := s16nt_h1_le_of_two_gen ρ hgen' ha' hb' hfix
  rcases hL with ⟨L, hL⟩ | ⟨L, hL⟩
  · have hra' : Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range 2, ρ a' ^ i)) = 4 := by
      have hL' : ∀ x : Q, L (ρ a' x) = ρ₀ a (L x) := by
        intro x
        have hx := hL a' x
        rwa [hψa] at hx
      rw [w183_m22_finrank_range_norm_congr L (A := ρ a') (B := ρ₀ a) hL' 2, hra]
    have hrb' : Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range 4, ρ b' ^ i)) = 2 := by
      have hL' : ∀ x : Q, L (ρ b' x) = ρ₀ b (L x) := by
        intro x
        have hx := hL b' x
        rwa [hψb] at hx
      rw [w183_m22_finrank_range_norm_congr L (A := ρ b') (B := ρ₀ b) hL' 4, hrb]
    rw [hra', hrb', hdim] at hbound
    omega
  · have hra' : Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range 2, ρ a' ^ i)) = 4 := by
      have hL' : ∀ x : Q, L (ρ a' x) = Representation.dual ρ₀ a (L x) := by
        intro x
        have hx := hL a' x
        rwa [hψa] at hx
      rw [w183_m22_finrank_range_norm_congr L (A := ρ a')
          (B := Representation.dual ρ₀ a) hL' 2,
        s16nt_rank_norm_dual (ρ := ρ₀) (r := 2) ha2, hra]
    have hrb' : Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range 4, ρ b' ^ i)) = 2 := by
      have hL' : ∀ x : Q, L (ρ b' x) = Representation.dual ρ₀ b (L x) := by
        intro x
        have hx := hL b' x
        rwa [hψb] at hx
      rw [w183_m22_finrank_range_norm_congr L (A := ρ b')
          (B := Representation.dual ρ₀ b) hL' 4,
        s16nt_rank_norm_dual (ρ := ρ₀) (r := 4) hb4, hrb]
    rw [hra', hrb', hdim] at hbound
    omega

theorem s16nt_row_m22
    {W : Type} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hirr : commSub ⊤ L ∈ irrSet L)
    (h : IsSpor ↥L .M22 ∧ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 10) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨e⟩ := h.1
  exact s16nt_goal_of_irr_h1 (d := 10) (c := 4) hW2 hirr h.2 (by norm_num)
    (fun Q _ _ _ ρ hρ hdim => s16nt_h1_m22 e ρ hρ hdim)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
