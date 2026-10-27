module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsExt
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Lie

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

section Perf

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem U_le_perfectCore_rad (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2) :
    antiUnipotent F ≤ perfectCore (Subgroup.normalizer (Rrad F j : Set (antiSp F))) := by
  rw [← rootA_axisOf j, axis_perfectCore_normalizer (hS_axis hn hF j)]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((mem_centerOf_iff.mp (rootU_le_center j hz)).2 u hu).symm

end Perf

theorem extFacts_sp {G : Type} [Group G] {M₁ M₂ : Subgroup G} {Y : Type} [Group Y] {f : ℕ}
    (hY : LieModel Y .PSp 2 2 f) (E : LieExt Y M₁ M₂) : ExtFacts E := by
  have hfinY : Finite Y := finite_of_lieModel_psp hY
  obtain ⟨hf, F, hFf, hFfin, hFchar, e, R, i, hFcard, hRi, hDd, h1, h2⟩ :=
    spAmalgam_data_out hY E.toLieAmalgamExt
  have hfinX : Finite (antiSp F) := Finite.of_equiv Y e.toEquiv
  set θ : MulAut Y ≃* MulAut (antiSp F) := MulAut.congr e with hθ
  have hθapp : ∀ (α : MulAut Y) (x : antiSp F), θ α x = e (α (e.symm x)) := fun α x => rfl
  have hθconj : ∀ d : Y, θ (MulAut.conj d) = MulAut.conj (e d) := by
    intro d
    refine MulEquiv.ext fun x => ?_
    rw [hθapp, MulAut.conj_apply, MulAut.conj_apply]
    simp
  have hstab : ∀ (P : Subgroup Y) (r : Subgroup (antiSp F)),
      P.map e.toMonoidHom = Subgroup.normalizer (r : Set (antiSp F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (antiSp F))) = r →
      ∀ β : MulAut Y, β ∈ CFSG.Quasithin.autStab P → ∀ x, θ β x ∈ r ↔ x ∈ r := by
    intro P r hP hcore β hβ
    have h1 : θ β ∈ CFSG.Quasithin.autStab (Subgroup.normalizer (r : Set (antiSp F))) := by
      intro x
      rw [← hP, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, hθapp]
      simpa using hβ (e.symm x)
    exact fun x => ((mem_autStab_iff_of_normalizer hcore (θ β)).mp h1 x).symm
  have hStabRad : ∀ β ∈ E.N1 ⊓ E.N2, StabRad (θ β) := by
    intro β hβ
    have a0 := hstab _ (R 0) h1 hDd.borel.core₁ β hβ.1.2
    have a1 := hstab _ (R 1) h2 hDd.borel.core₂ β hβ.2.2
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a0, a1⟩
    · exact ⟨a1, a0⟩
  have hborN : ∀ j : Fin 2, bor F ≤ Subgroup.normalizer (R j : Set (antiSp F)) := by
    intro j
    fin_cases j
    · exact hDd.borel.lt₁.le
    · exact hDd.borel.lt₂.le
  have hUperf : ∀ j : Fin 2, antiUnipotent F ≤
      perfectCore (Subgroup.normalizer (R j : Set (antiSp F))) := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun j => U_le_perfectCore_rad hf hFcard j
    · intro j
      fin_cases j
      · exact U_le_perfectCore_rad hf hFcard 1
      · exact U_le_perfectCore_rad hf hFcard 0
  set Nsub : Subgroup (MulAut (antiSp F)) := (E.N1 ⊓ E.N2).map θ.toMonoidHom with hNsub
  have hN1 : ∀ α ∈ Nsub, StabRad α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact hStabRad β hβ
  have hN2 : ∀ g ∈ bor F, (MulAut.conj g : MulAut (antiSp F)) ∈ Nsub := by
    intro g hg
    have hp1 : e.symm g ∈ E.P1 := by
      have : g ∈ E.P1.map e.toMonoidHom := by rw [h1]; exact hborN 0 hg
      rwa [Subgroup.mem_map_equiv] at this
    have hp2 : e.symm g ∈ E.P2 := by
      have : g ∈ E.P2.map e.toMonoidHom := by rw [h2]; exact hborN 1 hg
      rwa [Subgroup.mem_map_equiv] at this
    refine ⟨MulAut.conj (e.symm g), ⟨map_conj_le_N1 E.toLieAmalgamExt ⟨_, hp1, rfl⟩,
      map_conj_le_N2 E.toLieAmalgamExt ⟨_, hp2, rfl⟩⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hθconj]
    simp
  have hinjX := conj_injective_sp (F := F) hf hFcard
  have hinjY : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro d d' hdd
    have := congrArg θ hdd
    rw [hθconj, hθconj] at this
    exact e.injective (hinjX this)
  refine ⟨?_, ?_⟩
  · have hs := isSolvable_of_stabRad hf hFcard Nsub hN1
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (E.N1 ⊓ E.N2) θ.toMonoidHom θ.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (E.N1 ⊓ E.N2) θ.toMonoidHom θ.injective).injective
  · intro φ hφ
    have hmap : pCoreOf 2 Nsub = (pCoreOf 2 (E.N1 ⊓ E.N2)).map θ.toMonoidHom :=
      pCoreOf_map_of_injective θ.toMonoidHom θ.injective _
    have hθφ : θ φ ∈ pCoreOf 2 Nsub := by
      rw [hmap]
      exact ⟨φ, hφ, rfl⟩
    obtain ⟨u, hu, hue⟩ := pCoreOf_le_innU hf hFcard Nsub hN1 hN2 hθφ
    have hφe : φ = MulAut.conj (e.symm u) := by
      apply θ.injective
      rw [hθconj, e.apply_symm_apply]
      exact hue.symm
    have hu1 : u ∈ perfectCore (E.P1.map e.toMonoidHom) := by
      rw [h1]
      exact hUperf 0 hu
    rw [perfectCore_map_of_injective e.toMonoidHom e.injective, Subgroup.mem_map_equiv] at hu1
    have hmem : (MulAut.conj (e.symm u) : MulAut Y) ∈
        (perfectCore E.P1).map (MulAut.conj : Y →* MulAut Y) := ⟨_, hu1, rfl⟩
    rw [← perfectCore_map_of_injective (MulAut.conj : Y →* MulAut Y) hinjY E.P1] at hmem
    rw [hφe]
    exact perfectCore_mono (map_conj_le_N1 E.toLieAmalgamExt) hmem

end CFSG.Quasithin.H13.Sec53F
