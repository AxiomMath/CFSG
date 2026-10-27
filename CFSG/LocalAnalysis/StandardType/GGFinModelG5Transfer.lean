module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Transfer

private theorem g5_mulAut_conj_conj {G : Type*} [Group G] (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  show φ (g * (φ⁻¹ : MulAut G) x * g⁻¹) = φ g * x * (φ g)⁻¹
  rw [map_mul, map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem ggG5_conj_injective
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} {D : LangDatum (langTag t) GGL}
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcomm : ∀ x : C, ι₀ c * ι₀ x = ι₀ x * ι₀ c := by
    intro x
    have h := DFunLike.congr_fun hc x
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have h' := congrArg ι₀ h
    rw [map_mul, map_mul, map_inv] at h'
    calc ι₀ c * ι₀ x = (ι₀ c * ι₀ x * (ι₀ c)⁻¹) * ι₀ c := by group
      _ = ι₀ x * ι₀ c := by rw [h']
  have hfix : ι₀ c ∈ D.fix := hT.pkg.desc.range_le ⟨c, rfl⟩
  have hmem : ι₀ c ∈ adjointGroup (langTag t) GGL := ((LangDatum.mem_fix D).mp hfix).1
  have hone : ι₀ c = 1 := hT.pkg.cent_triv (ι₀ c) hmem fun x => hcomm x
  apply hT.pkg.inj
  rw [hone, map_one]

theorem ggG5_normalizer_iff
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} {D : LangDatum (langTag t) GGL}
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    (z : Multiplicative (ggFixAdd p (piB t p f))) (S : Subgroup C) :
    hT.ggBetaHom z ∈ Subgroup.normalizer
        ((S.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) : Set (MulAut C)) ↔
      hT.uMap z ∈ Subgroup.normalizer
        ((S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) := ggG5_conj_injective (ht := ht) hT
  have hcc : ∀ g : C, hT.ggBetaHom z * MulAut.conj g * (hT.ggBetaHom z)⁻¹ =
      MulAut.conj (hT.ggBetaHom z g) := fun g => g5_mulAut_conj_conj _ g
  have key : ∀ c : C, hT.uMap z * ι₀ c * (hT.uMap z)⁻¹ = ι₀ (hT.ggBetaHom z c) :=
    fun c => (hT.ggBetaHom_apply z c).symm
  have hcondB : (∀ x : MulAut C, x ∈ (S.map (MulAut.conj : C →* MulAut C) :
        Subgroup (MulAut C)) ↔
      hT.ggBetaHom z * x * (hT.ggBetaHom z)⁻¹ ∈
        (S.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C))) ↔
      ∀ c : C, c ∈ S ↔ hT.ggBetaHom z c ∈ S := by
    constructor
    · intro hx c
      constructor
      · intro hc
        have hx1 : MulAut.conj c ∈ (S.map (MulAut.conj : C →* MulAut C) :
            Subgroup (MulAut C)) := ⟨c, hc, rfl⟩
        obtain ⟨d, hd, hd'⟩ := (hx (MulAut.conj c)).mp hx1
        have hd2 : d = hT.ggBetaHom z c := hinj (by rw [hd', hcc c])
        exact hd2 ▸ hd
      · intro hc
        have hx1 : MulAut.conj c ∈ (S.map (MulAut.conj : C →* MulAut C) :
            Subgroup (MulAut C)) :=
          (hx (MulAut.conj c)).mpr ⟨hT.ggBetaHom z c, hc, (hcc c).symm⟩
        obtain ⟨d, hd, hd'⟩ := hx1
        have hd2 : d = c := hinj hd'
        exact hd2 ▸ hd
    · intro hx x
      constructor
      · intro hxH
        obtain ⟨c, hc, hcx⟩ := hxH
        refine ⟨hT.ggBetaHom z c, (hx c).mp hc, ?_⟩
        rw [← hcx, hcc c]
      · intro hxH
        obtain ⟨c, hc, hcx⟩ := hxH
        have hx1 : hT.ggBetaHom z ((hT.ggBetaHom z)⁻¹ c) = c :=
          MulEquiv.apply_symm_apply (hT.ggBetaHom z) c
        have hb1 : (hT.ggBetaHom z)⁻¹ c ∈ S := (hx _).mpr (by rw [hx1]; exact hc)
        have hxeq : x = MulAut.conj ((hT.ggBetaHom z)⁻¹ c) := by
          calc x = (hT.ggBetaHom z)⁻¹ * (hT.ggBetaHom z * x * (hT.ggBetaHom z)⁻¹) *
                hT.ggBetaHom z := by group
            _ = (hT.ggBetaHom z)⁻¹ * MulAut.conj c * hT.ggBetaHom z := by rw [← hcx]
            _ = MulAut.conj ((hT.ggBetaHom z)⁻¹ c) := g5_mulAut_conj_conj _ c
        exact ⟨(hT.ggBetaHom z)⁻¹ c, hb1, hxeq.symm⟩
  have hcondU : (∀ y : ModGL (langTag t) GGL, y ∈ (S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) ↔
      hT.uMap z * y * (hT.uMap z)⁻¹ ∈
        (S.map ι₀ : Subgroup (ModGL (langTag t) GGL))) ↔
      ∀ c : C, c ∈ S ↔ hT.ggBetaHom z c ∈ S := by
    constructor
    · intro hy c
      constructor
      · intro hc
        have hy1 : ι₀ c ∈ (S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) := ⟨c, hc, rfl⟩
        obtain ⟨d, hd, hd'⟩ := (hy (ι₀ c)).mp hy1
        have hd2 : d = hT.ggBetaHom z c := hT.pkg.inj (by rw [hd', key c])
        exact hd2 ▸ hd
      · intro hc
        have hy1 : ι₀ c ∈ (S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) :=
          (hy (ι₀ c)).mpr ⟨hT.ggBetaHom z c, hc, (key c).symm⟩
        obtain ⟨d, hd, hd'⟩ := hy1
        have hd2 : d = c := hT.pkg.inj hd'
        exact hd2 ▸ hd
    · intro hx y
      constructor
      · intro hyH
        obtain ⟨c, hc, hcy⟩ := hyH
        refine ⟨hT.ggBetaHom z c, (hx c).mp hc, ?_⟩
        rw [← key c, hcy]
      · intro hyH
        obtain ⟨c, hc, hcy⟩ := hyH
        have hkey : ∀ d : C, (hT.uMap z)⁻¹ * ι₀ d * hT.uMap z =
            ι₀ ((hT.ggBetaHom z)⁻¹ d) := by
          intro d
          have h := hT.ggBetaHom_apply (z⁻¹) d
          simp only [map_inv, inv_inv] at h
          exact h.symm
        have hx1 : hT.ggBetaHom z ((hT.ggBetaHom z)⁻¹ c) = c :=
          MulEquiv.apply_symm_apply (hT.ggBetaHom z) c
        have hb1 : (hT.ggBetaHom z)⁻¹ c ∈ S :=
          (hx ((hT.ggBetaHom z)⁻¹ c)).mpr (by rw [hx1]; exact hc)
        refine ⟨(hT.ggBetaHom z)⁻¹ c, hb1, ?_⟩
        have hy : y = ι₀ ((hT.ggBetaHom z)⁻¹ c) := by
          calc y = (hT.uMap z)⁻¹ * (hT.uMap z * y * (hT.uMap z)⁻¹) * hT.uMap z := by
                group
            _ = (hT.uMap z)⁻¹ * ι₀ c * hT.uMap z := by rw [hcy]
            _ = ι₀ ((hT.ggBetaHom z)⁻¹ c) := hkey c
        rw [hy]
  constructor
  · intro hb
    rw [Subgroup.mem_normalizer_iff] at hb
    rw [Subgroup.mem_normalizer_iff]
    exact hcondU.mpr (hcondB.mp hb)
  · intro hu
    rw [Subgroup.mem_normalizer_iff] at hu
    rw [Subgroup.mem_normalizer_iff]
    exact hcondB.mpr (hcondU.mp hu)

theorem ggG5_centralizer_iff
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} {D : LangDatum (langTag t) GGL}
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    (z : Multiplicative (ggFixAdd p (piB t p f))) (S : Subgroup C) :
    hT.ggBetaHom z ∈ Subgroup.centralizer
        ((S.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) : Set (MulAut C)) ↔
      hT.uMap z ∈ Subgroup.centralizer
        ((S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) := ggG5_conj_injective (ht := ht) hT
  have hcc : ∀ g : C, hT.ggBetaHom z * MulAut.conj g * (hT.ggBetaHom z)⁻¹ =
      MulAut.conj (hT.ggBetaHom z g) := fun g => g5_mulAut_conj_conj _ g
  have hbc : ∀ g : C, hT.ggBetaHom z * MulAut.conj g =
      MulAut.conj (hT.ggBetaHom z g) * hT.ggBetaHom z := by
    intro g
    calc hT.ggBetaHom z * MulAut.conj g =
        (hT.ggBetaHom z * MulAut.conj g * (hT.ggBetaHom z)⁻¹) * hT.ggBetaHom z := by group
      _ = MulAut.conj (hT.ggBetaHom z g) * hT.ggBetaHom z := by rw [hcc g]
  have key : ∀ c : C, hT.uMap z * ι₀ c * (hT.uMap z)⁻¹ = ι₀ (hT.ggBetaHom z c) :=
    fun c => (hT.ggBetaHom_apply z c).symm
  have key2 : ∀ c : C, hT.uMap z * ι₀ c = ι₀ (hT.ggBetaHom z c) * hT.uMap z := by
    intro c
    calc hT.uMap z * ι₀ c =
        (hT.uMap z * ι₀ c * (hT.uMap z)⁻¹) * hT.uMap z := by group
      _ = ι₀ (hT.ggBetaHom z c) * hT.uMap z := by rw [key c]
  have hcondB : (∀ x ∈ (S.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)),
      x * hT.ggBetaHom z = hT.ggBetaHom z * x) ↔
      ∀ c ∈ S, hT.ggBetaHom z c = c := by
    constructor
    · intro hx c hc
      have h1 : MulAut.conj c ∈ (S.map (MulAut.conj : C →* MulAut C) :
          Subgroup (MulAut C)) := ⟨c, hc, rfl⟩
      have h2 := hx (MulAut.conj c) h1
      rw [hbc c] at h2
      exact (hinj (mul_right_cancel h2)).symm
    · intro hx x hxH
      obtain ⟨c, hc, rfl⟩ := hxH
      rw [hbc c, hx c hc]
  have hcondU : (∀ y ∈ (S.map ι₀ : Subgroup (ModGL (langTag t) GGL)),
      y * hT.uMap z = hT.uMap z * y) ↔
      ∀ c ∈ S, hT.ggBetaHom z c = c := by
    constructor
    · intro hy c hc
      have h1 : ι₀ c ∈ (S.map ι₀ : Subgroup (ModGL (langTag t) GGL)) := ⟨c, hc, rfl⟩
      have h2 := hy (ι₀ c) h1
      have h3 : ι₀ c = ι₀ (hT.ggBetaHom z c) := by
        calc ι₀ c = ι₀ c * hT.uMap z * (hT.uMap z)⁻¹ := by group
          _ = hT.uMap z * ι₀ c * (hT.uMap z)⁻¹ := by rw [h2]
          _ = ι₀ (hT.ggBetaHom z c) := key c
      exact (hT.pkg.inj h3).symm
    · intro hx y hyH
      obtain ⟨c, hc, rfl⟩ := hyH
      exact (by rw [key2 c, hx c hc])
  constructor
  · intro hb
    rw [Subgroup.mem_centralizer_iff] at hb
    rw [Subgroup.mem_centralizer_iff]
    exact hcondU.mpr (hcondB.mp hb)
  · intro hu
    rw [Subgroup.mem_centralizer_iff] at hu
    rw [Subgroup.mem_centralizer_iff]
    exact hcondB.mpr (hcondU.mp hu)

end Transfer

end CFSG.StandardType.GGFinModel.G5
