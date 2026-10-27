module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6

section Bridge

private theorem g5_not_ggTwistedTag {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) : ¬ GGTwistedTag t := by
  rcases ht with rfl | rfl | rfl | rfl <;>
    (rintro (h | h | h) <;> exact absurd h (by decide))

private theorem g5_neg_mem_roots
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    -δ ∈ (ggU t n f).D.roots := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact (mem_roots_F4 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_F4 n f δ).mp hδ))))
  · exact (mem_roots_E6 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E6 n f δ).mp hδ))))
  · exact (mem_roots_E7 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E7 n f δ).mp hδ))))
  · exact (mem_roots_E8 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E8 n f δ).mp hδ))))

private theorem g5_isRoot_reidx
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    IsRoot (langTag t) (ggLangReidx (ggRank_untw ht n f) δ) := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact mem_rootFinset.mp ((mem_roots_F4 n f δ).mp hδ)
  · exact mem_rootFinset.mp ((mem_roots_E6 n f δ).mp hδ)
  · exact mem_rootFinset.mp ((mem_roots_E7 n f δ).mp hδ)
  · exact mem_rootFinset.mp ((mem_roots_E8 n f δ).mp hδ)

private theorem g5_bridge_untw_eq
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) (hf : 1 ≤ f)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map (ggIotaK t n f hf)) =
      ratRankOne t f (ggLangReidx (ggRank_untw ht n f) δ) := by
  have hne : -δ ∈ (ggU t n f).D.roots := g5_neg_mem_roots ht n f hδ
  have hneg : ggLangReidx (ggRank_untw ht n f) (-δ) =
      -(ggLangReidx (ggRank_untw ht n f) δ) := rfl
  rw [Subgroup.map_sup, ggBC_untw ht n f hf δ hδ, ggBC_untw ht n f hf (-δ) hne, hneg,
    ratRankOne]

private theorem g5_bridge_actual_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) (hf : 1 ≤ f)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    ∃ β : Fin (langTag t).rank → ℤ, IsRoot (langTag t) β ∧ ggGraphLat t β = β ∧
      (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map (ggIotaK t n f hf)) =
        ratRankOne t f β := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨ggLangReidx (ggRank_untw (Or.inl rfl) n f) δ,
      g5_isRoot_reidx (Or.inl rfl) n f hδ, rfl,
      g5_bridge_untw_eq (Or.inl rfl) n f hf hδ⟩
  · exact ⟨ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) δ,
      g5_isRoot_reidx (Or.inr (Or.inl rfl)) n f hδ, rfl,
      g5_bridge_untw_eq (Or.inr (Or.inl rfl)) n f hf hδ⟩
  · exact ⟨ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) δ,
      g5_isRoot_reidx (Or.inr (Or.inr (Or.inl rfl))) n f hδ, rfl,
      g5_bridge_untw_eq (Or.inr (Or.inr (Or.inl rfl))) n f hf hδ⟩
  · exact ⟨ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) δ,
      g5_isRoot_reidx (Or.inr (Or.inr (Or.inr rfl))) n f hδ, rfl,
      g5_bridge_untw_eq (Or.inr (Or.inr (Or.inr rfl))) n f hf hδ⟩

private theorem g5_bridge_lang_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) (hf : 1 ≤ f)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) :
    ∃ δ : Fin (ggU t n f).D.rank → ℤ, GGRootClass (ggU t n f).D t δ ∧
      (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map (ggIotaK t n f hf)) =
        ratRankOne t f β := by
  rcases ht with rfl | rfl | rfl | rfl
  · have hmem : β ∈ (ggU .F4 n f).D.roots := (mem_roots_F4 n f β).mpr (mem_rootFinset.mpr hβ)
    let δ : Fin (ggU .F4 n f).D.rank → ℤ := β
    have hδ : δ ∈ (ggU .F4 n f).D.roots := hmem
    have hne : -δ ∈ (ggU .F4 n f).D.roots := g5_neg_mem_roots (Or.inl rfl) n f hδ
    have hre : ggLangReidx (ggRank_untw (Or.inl rfl) n f) δ = δ := by
      funext j; exact congrArg δ (Fin.ext rfl)
    have hre' : ggLangReidx (ggRank_untw (Or.inl rfl) n f) (-δ) = -δ := by
      funext j; exact congrArg (-δ) (Fin.ext rfl)
    refine ⟨δ, ⟨hδ, fun h => absurd h (g5_not_ggTwistedTag (Or.inl rfl))⟩, ?_⟩
    rw [Subgroup.map_sup, ggBC_untw (Or.inl rfl) n f hf δ hδ,
      ggBC_untw (Or.inl rfl) n f hf (-δ) hne, hre, hre', ratRankOne]
    dsimp only [δ]
    rfl
  · have hmem : β ∈ (ggU .E6 n f).D.roots := (mem_roots_E6 n f β).mpr (mem_rootFinset.mpr hβ)
    let δ : Fin (ggU .E6 n f).D.rank → ℤ := β
    have hδ : δ ∈ (ggU .E6 n f).D.roots := hmem
    have hne : -δ ∈ (ggU .E6 n f).D.roots := g5_neg_mem_roots (Or.inr (Or.inl rfl)) n f hδ
    have hre : ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) δ = δ := by
      funext j; exact congrArg δ (Fin.ext rfl)
    have hre' : ggLangReidx (ggRank_untw (Or.inr (Or.inl rfl)) n f) (-δ) = -δ := by
      funext j; exact congrArg (-δ) (Fin.ext rfl)
    refine ⟨δ, ⟨hδ, fun h => absurd h (g5_not_ggTwistedTag (Or.inr (Or.inl rfl)))⟩, ?_⟩
    rw [Subgroup.map_sup, ggBC_untw (Or.inr (Or.inl rfl)) n f hf δ hδ,
      ggBC_untw (Or.inr (Or.inl rfl)) n f hf (-δ) hne, hre, hre', ratRankOne]
    dsimp only [δ]
    rfl
  · have hmem : β ∈ (ggU .E7 n f).D.roots := (mem_roots_E7 n f β).mpr (mem_rootFinset.mpr hβ)
    let δ : Fin (ggU .E7 n f).D.rank → ℤ := β
    have hδ : δ ∈ (ggU .E7 n f).D.roots := hmem
    have hne : -δ ∈ (ggU .E7 n f).D.roots :=
      g5_neg_mem_roots (Or.inr (Or.inr (Or.inl rfl))) n f hδ
    have hre : ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) δ = δ := by
      funext j; exact congrArg δ (Fin.ext rfl)
    have hre' : ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f) (-δ) = -δ := by
      funext j; exact congrArg (-δ) (Fin.ext rfl)
    refine ⟨δ, ⟨hδ, fun h => absurd h (g5_not_ggTwistedTag (Or.inr (Or.inr (Or.inl rfl))))⟩, ?_⟩
    rw [Subgroup.map_sup, ggBC_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf δ hδ,
      ggBC_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf (-δ) hne, hre, hre', ratRankOne]
    dsimp only [δ]
    rfl
  · have hmem : β ∈ (ggU .E8 n f).D.roots := (mem_roots_E8 n f β).mpr (mem_rootFinset.mpr hβ)
    let δ : Fin (ggU .E8 n f).D.rank → ℤ := β
    have hδ : δ ∈ (ggU .E8 n f).D.roots := hmem
    have hne : -δ ∈ (ggU .E8 n f).D.roots :=
      g5_neg_mem_roots (Or.inr (Or.inr (Or.inr rfl))) n f hδ
    have hre : ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) δ = δ := by
      funext j; exact congrArg δ (Fin.ext rfl)
    have hre' : ggLangReidx (ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f) (-δ) = -δ := by
      funext j; exact congrArg (-δ) (Fin.ext rfl)
    refine ⟨δ, ⟨hδ, fun h => absurd h (g5_not_ggTwistedTag (Or.inr (Or.inr (Or.inr rfl))))⟩, ?_⟩
    rw [Subgroup.map_sup, ggBC_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf δ hδ,
      ggBC_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf (-δ) hne, hre, hre', ratRankOne]
    dsimp only [δ]
    rfl


private def g5_f4Highest : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private def g5_f4LongData :
    List ((Fin (Tag.rank .E6) → ℤ) × List (Fin (Tag.rank .F4))) :=
  [
    ((![-1, -2, -2, -3, -2, -1] : Fin (Tag.rank .E6) → ℤ), [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![-1, -1, -2, -3, -2, -1] : Fin (Tag.rank .E6) → ℤ), [1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![-1, -1, -2, -2, -2, -1] : Fin (Tag.rank .E6) → ℤ), [2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![-1, -1, -1, -2, -1, -1] : Fin (Tag.rank .E6) → ℤ), [3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![-1, -1, -1, -1, -1, -1] : Fin (Tag.rank .E6) → ℤ), [3, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![-1, 0, -1, -1, -1, -1] : Fin (Tag.rank .E6) → ℤ), [3, 2, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, -1, -1, -2, -1, 0] : Fin (Tag.rank .E6) → ℤ), [1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, -1, -1, -1, -1, 0] : Fin (Tag.rank .E6) → ℤ), [2, 0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, -1, 0, -1, 0, 0] : Fin (Tag.rank .E6) → ℤ), [0, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, -1, 0, 0, 0, 0] : Fin (Tag.rank .E6) → ℤ), [0, 1, 2, 3, 1, 2, 1, 0]),
    ((![0, 0, -1, -1, -1, 0] : Fin (Tag.rank .E6) → ℤ), [2, 1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, 0, 0, -1, 0, 0] : Fin (Tag.rank .E6) → ℤ), [1, 2, 3, 0, 1, 2, 1, 0]),
    ((![0, 0, 0, 1, 0, 0] : Fin (Tag.rank .E6) → ℤ), [2, 3, 0, 1, 2, 1, 0]),
    ((![0, 0, 1, 1, 1, 0] : Fin (Tag.rank .E6) → ℤ), [3, 0, 1, 2, 1, 0]),
    ((![0, 1, 0, 0, 0, 0] : Fin (Tag.rank .E6) → ℤ), [1, 2, 3, 1, 2, 1, 0]),
    ((![0, 1, 0, 1, 0, 0] : Fin (Tag.rank .E6) → ℤ), [2, 3, 1, 2, 1, 0]),
    ((![0, 1, 1, 1, 1, 0] : Fin (Tag.rank .E6) → ℤ), [3, 1, 2, 1, 0]),
    ((![0, 1, 1, 2, 1, 0] : Fin (Tag.rank .E6) → ℤ), [3, 2, 1, 0]),
    ((![1, 0, 1, 1, 1, 1] : Fin (Tag.rank .E6) → ℤ), [0, 1, 2, 1, 0]),
    ((![1, 1, 1, 1, 1, 1] : Fin (Tag.rank .E6) → ℤ), [1, 2, 1, 0]),
    ((![1, 1, 1, 2, 1, 1] : Fin (Tag.rank .E6) → ℤ), [2, 1, 0]),
    ((![1, 1, 2, 2, 2, 1] : Fin (Tag.rank .E6) → ℤ), [1, 0]),
    ((![1, 1, 2, 3, 2, 1] : Fin (Tag.rank .E6) → ℤ), [0]),
    ((![1, 2, 2, 3, 2, 1] : Fin (Tag.rank .E6) → ℤ), [])
  ]

private def g5_f4LongRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  g5_f4LongData.map fun p => proj p.1

private theorem g5_f4LongData_spec :
    ∀ p ∈ g5_f4LongData,
      p.1 ∈ rootFinset Tag.E6 ∧ rho p.1 = p.1 ∧
        proj p.1 = p.2.foldr (reflect Tag.F4) g5_f4Highest := by
  decide +kernel

private theorem g5_f4LongRoots_reflect :
    ∀ v ∈ g5_f4LongRoots, ∀ i : Fin (Tag.rank .F4),
      reflect Tag.F4 i v ∈ g5_f4LongRoots := by
  decide +kernel

private theorem g5_f4Highest_mem_longRoots : g5_f4Highest ∈ g5_f4LongRoots := by
  decide +kernel

private theorem g5_f4_height_le :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) ≤ 11 := by
  decide +kernel

private theorem g5_f4_height_eq_max :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) = 11 → v = g5_f4Highest := by
  decide +kernel

private theorem g5_f4Highest_sum : (∑ i : Fin (Tag.rank .F4), g5_f4Highest i) = 11 := by
  decide +kernel

private theorem g5_f4Highest_mem_rootFinset :
    g5_f4Highest ∈ rootFinset Tag.F4 := by
  decide +kernel

private theorem g5_wordProd_smul_foldr (ω : List (Fin (Tag.rank .F4)))
    (v : Fin (Tag.rank .F4) → ℤ) :
    (coxeterSystem Tag.F4).wordProd ω • v = ω.foldr (reflect Tag.F4) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

private theorem g5_f4LongRoots_word (ω : List (Fin (Tag.rank .F4))) :
    ω.foldr (reflect Tag.F4) g5_f4Highest ∈ g5_f4LongRoots := by
  induction ω with
  | nil => exact g5_f4Highest_mem_longRoots
  | cons i ω ih => exact g5_f4LongRoots_reflect _ ih i

private theorem g5_f4LongRoots_complete
    (n f : ℕ)
    {v : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hv : v ∈ (ggU .twistedE6 n f).D.roots)
    (hlong : GGLongRoot (ggU .twistedE6 n f).D v) : v ∈ g5_f4LongRoots := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hlong
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.F4).wordProd_surjective w
  have hγ₀root : γ₀ ∈ rootFinset Tag.F4 := (mem_roots_twistedE6 n f γ₀).mp hγ₀
  have hle : (∑ i, γ₀ i) ≤ 11 := g5_f4_height_le γ₀ hγ₀root
  have hsum : (∑ i : Fin (ggU .twistedE6 n f).D.rank, g5_f4Highest i) = 11 := by
    change (∑ i : Fin 4, g5_f4Highest i) = 11
    decide +kernel
  have hge : 11 ≤ (∑ i, γ₀ i) := by
    have h := hmax g5_f4Highest
      ((mem_roots_twistedE6 n f g5_f4Highest).mpr g5_f4Highest_mem_rootFinset)
    rwa [hsum] at h
  have heq : (∑ i, γ₀ i) = 11 := le_antisymm hle hge
  have hγeq : γ₀ = g5_f4Highest := g5_f4_height_eq_max γ₀ hγ₀root heq
  rw [hγeq]
  change (coxeterSystem Tag.F4).wordProd ω • g5_f4Highest ∈ g5_f4LongRoots
  rw [g5_wordProd_smul_foldr]
  exact g5_f4LongRoots_word ω

private theorem g5_f4LongRoots_long
    (n f : ℕ)
    {v : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hv : v ∈ g5_f4LongRoots) : GGLongRoot (ggU .twistedE6 n f).D v := by
  obtain ⟨p, hp, hproj⟩ := List.mem_map.mp hv
  obtain ⟨hpRoot, hprho, hpword⟩ := g5_f4LongData_spec p hp
  refine ⟨(coxeterSystem Tag.F4).wordProd p.2, g5_f4Highest, ?_, ?_, ?_⟩
  · exact (mem_roots_twistedE6 n f g5_f4Highest).mpr g5_f4Highest_mem_rootFinset
  · intro δ hδ
    have hδ' : δ ∈ rootFinset Tag.F4 := (mem_roots_twistedE6 n f δ).mp hδ
    calc (∑ i, δ i) ≤ 11 := g5_f4_height_le δ hδ'
      _ = (∑ i, g5_f4Highest i) := g5_f4Highest_sum.symm
  · rw [← hproj, hpword]
    change p.2.foldr (reflect Tag.F4) g5_f4Highest =
      (coxeterSystem Tag.F4).wordProd p.2 • g5_f4Highest
    exact (g5_wordProd_smul_foldr p.2 g5_f4Highest).symm

private theorem g5_f4LongRoots_proj_fixed :
    ∀ β ∈ rootFinset Tag.E6, rho β = β → proj β ∈ g5_f4LongRoots := by
  decide +kernel

private theorem g5_tw_long_iff_proj
    (n f : ℕ)
    {v : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hv : v ∈ (ggU .twistedE6 n f).D.roots) :
    GGLongRoot (ggU .twistedE6 n f).D v ↔
      ∃ β : Fin (langTag .twistedE6).rank → ℤ,
        IsRoot (langTag .twistedE6) β ∧ rho β = β ∧ proj β = v := by
  constructor
  · intro hlong
    obtain ⟨p, hp, hproj⟩ := List.mem_map.mp (g5_f4LongRoots_complete n f hv hlong)
    obtain ⟨hpRoot, hprho, -⟩ := g5_f4LongData_spec p hp
    exact ⟨p.1, mem_rootFinset.mp hpRoot, hprho, hproj⟩
  · rintro ⟨β, hβ, hfix, hproj⟩
    rw [← hproj]
    exact g5_f4LongRoots_long n f
      (g5_f4LongRoots_proj_fixed β (mem_rootFinset.mpr hβ) hfix)

private theorem g5_iSup_twisted_eq {ι κ G : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] [Group G]
    (Φ : Set (ι → ℤ)) (o : ι → κ) (X : (ι → ℤ) → Subgroup G) (β : κ → ℤ)
    {b : ι → ℤ} (hb : b ∈ Φ) (ho : orbitSum o b = β)
    (huniq : ∀ α ∈ Φ, ∀ c : ℕ, 0 < c → orbitSum o α = c • β → X α ≤ X b) :
    (⨆ α ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum o α = c • β), X α) = X b := by
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    refine iSup_le fun hc => ?_
    obtain ⟨c, hc0, hco⟩ := hc
    exact huniq α hα c hc0 hco
  · refine le_iSup₂_of_le
      (f := fun α (_ : α ∈ Φ) =>
        ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum o α = c • β), X α) b hb ?_
    exact le_iSup_of_le ⟨1, Nat.one_pos, by simpa [ho]⟩ le_rfl

private theorem g5_twistedRootSubgroup_eq_singleton {ι κ G : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ] [Group G]
    (Φ : Set (ι → ℤ)) (o : ι → κ) (X : (ι → ℤ) → Subgroup G) (σ : G →* G) (β : κ → ℤ)
    {b : ι → ℤ} (hb : b ∈ Φ) (ho : orbitSum o b = β)
    (huniq : ∀ α ∈ Φ, ∀ c : ℕ, 0 < c → orbitSum o α = c • β → X α ≤ X b) :
    twistedRootSubgroup Φ o X σ β = X b ⊓ MonoidHom.eqLocus σ (MonoidHom.id G) := by
  rw [twistedRootSubgroup, g5_iSup_twisted_eq Φ o X β hb ho huniq]

private theorem g5_inf_adjoint_eq {G : Type*} [Group G] {A E X : Subgroup G} (h : X ≤ A) :
    X ⊓ E = (A ⊓ E) ⊓ X := by
  apply le_antisymm
  · exact le_inf (le_inf (inf_le_left.trans h) inf_le_right) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

private theorem g5_twistedRootSubgroup_proj
    (n f : ℕ)
    {δ : Fin (Tag.rank .F4) → ℤ}
    {β : Fin (Tag.rank .E6) → ℤ}
    (hδ : proj β = δ)
    (hβ : IsRoot Tag.E6 β) (hfix : rho β = β) :
    twistedRootSubgroup {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a} orbitMap
      (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL)
      (ggPhi .twistedE6 f) δ =
    ggFixGp .twistedE6 f ⊓
      CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL β := by
  rw [← hδ]
  have hXle : CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL β ≤
      adjointGroup Tag.E6 GGL :=
    CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup β
  have hsup := g5_twistedRootSubgroup_eq_singleton
    (Φ := {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a})
    (o := orbitMap) (X := CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL)
    (σ := ggPhi .twistedE6 f) (β := proj β) (b := β) hβ rfl ?_
  · rw [hsup, ggFixGp]
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans hXle) inf_le_right) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  · intro α hα c hc0 hco
    have hcproj : proj α = c • proj β := by rw [proj_apply]; exact hco
    have hc1 : c = 1 := eq_one_of_proj_eq_nsmul hα hβ hc0 hcproj
    have hprojα : proj α = proj β := by simpa [hc1] using hcproj
    have hαβ : α = β := by
      rcases (proj_eq_proj_iff hα hβ).mp hprojα with h | h
      · exact h.symm
      · have h' : rho β = rho (rho α) := by rw [h]
        have h'' : rho β = α := by rwa [rho_rho] at h'
        rw [← h'', hfix]
    rw [hαβ]

private theorem g5_bridge_twistedE6_eq
    (n f : ℕ) (hf : 1 ≤ f)
    {δ : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hδ : δ ∈ (ggU .twistedE6 n f).D.roots)
    {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot Tag.E6 β) (hfix : rho β = β) (hproj : proj β = δ) :
    (((ggU .twistedE6 n f).D.rootGroup δ ⊔ (ggU .twistedE6 n f).D.rootGroup (-δ)).map
      (ggIotaK .twistedE6 n f hf)) = ratRankOne .twistedE6 f β := by
  have hne : -δ ∈ (ggU .twistedE6 n f).D.roots :=
    (mem_roots_twistedE6 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_twistedE6 n f δ).mp hδ))))
  rw [Subgroup.map_sup, ggBC_twistedE6 n f hf δ hδ, ggBC_twistedE6 n f hf (-δ) hne]
  dsimp only [langTag] at *
  let σ' : (Module.End GGL (RootModule Tag.E6 GGL))ˣ →*
      (Module.End GGL (RootModule Tag.E6 GGL))ˣ := ggPhi .twistedE6 f
  rw [← hproj]
  change (twistedRootSubgroup {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a} orbitMap
        (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL) σ' (proj β) ⊔
      twistedRootSubgroup {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a} orbitMap
        (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL) σ' (-proj β)) =
    ratRankOne .twistedE6 f β
  unfold twistedRootSubgroup
  have hfiber : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → rho γ = γ →
      ∀ α ∈ {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a}, ∀ c : ℕ, 0 < c →
        orbitSum orbitMap α = c • proj γ →
        CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL α ≤
          CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL γ := by
    intro γ hγ hγfix α hα c hc0 hco
    have hcproj : proj α = c • proj γ := by rw [proj_apply]; exact hco
    have hc1 : c = 1 := eq_one_of_proj_eq_nsmul hα hγ hc0 hcproj
    have hprojα : proj α = proj γ := by simpa [hc1] using hcproj
    have hαγ : α = γ := by
      rcases (proj_eq_proj_iff hα hγ).mp hprojα with h | h
      · exact h.symm
      · have h' : rho γ = rho (rho α) := by rw [h]
        have h'' : rho γ = α := by rwa [rho_rho] at h'
        rw [← h'', hγfix]
    rw [hαγ]
  have hfixneg : rho (-β) = -β := by
    have hneg := congrArg Neg.neg hfix
    simpa [rho, permLattice_neg] using hneg
  rw [g5_iSup_twisted_eq (Φ := {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a})
    (o := orbitMap) (X := CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL)
    (β := proj β) (b := β) hβ rfl (hfiber β hβ hfix)]
  have hfiber_neg : ∀ α ∈ {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a},
      ∀ c : ℕ, 0 < c → orbitSum orbitMap α = c • (-proj β) →
        CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL α ≤
          CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL (-β) := by
    intro α hα c hc0 hco
    exact hfiber (-β) (IsRoot.neg hβ) hfixneg α hα c hc0 (by simpa [map_neg] using hco)
  rw [g5_iSup_twisted_eq (Φ := {a : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 a})
    (o := orbitMap) (X := CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL)
    (β := -proj β) (b := -β) (IsRoot.neg hβ)
    (by rw [← proj_apply, map_neg]) hfiber_neg]
  unfold ratRankOne ggFixGp
  have hXle : CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL β ≤ adjointGroup Tag.E6 GGL :=
    CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup β
  have hXle' : CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 GGL (-β) ≤ adjointGroup Tag.E6 GGL :=
    CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (-β)
  rw [g5_inf_adjoint_eq hXle, g5_inf_adjoint_eq hXle']
  rfl

private theorem g5_bridge_twistedE6_core
    (n f : ℕ) (hf : 1 ≤ f) :
    (∀ δ : Fin (ggU .twistedE6 n f).D.rank → ℤ,
        GGRootClass (ggU .twistedE6 n f).D .twistedE6 δ →
      ∃ β : Fin (langTag .twistedE6).rank → ℤ, IsRoot (langTag .twistedE6) β ∧
        ggGraphLat .twistedE6 β = β ∧
        (((ggU .twistedE6 n f).D.rootGroup δ ⊔ (ggU .twistedE6 n f).D.rootGroup (-δ)).map
          (ggIotaK .twistedE6 n f hf)) = ratRankOne .twistedE6 f β) ∧
    (∀ β : Fin (langTag .twistedE6).rank → ℤ, IsRoot (langTag .twistedE6) β →
        ggGraphLat .twistedE6 β = β →
      ∃ δ : Fin (ggU .twistedE6 n f).D.rank → ℤ,
        GGRootClass (ggU .twistedE6 n f).D .twistedE6 δ ∧
        (((ggU .twistedE6 n f).D.rootGroup δ ⊔ (ggU .twistedE6 n f).D.rootGroup (-δ)).map
          (ggIotaK .twistedE6 n f hf)) = ratRankOne .twistedE6 f β) := by
  constructor
  · intro δ hδclass
    have hδ : δ ∈ (ggU .twistedE6 n f).D.roots := hδclass.1
    have hlong : GGLongRoot (ggU .twistedE6 n f).D δ := hδclass.2 (Or.inr (Or.inr rfl))
    obtain ⟨β, hβ, hfix, hproj⟩ := (g5_tw_long_iff_proj n f hδ).mp hlong
    exact ⟨β, hβ, hfix, g5_bridge_twistedE6_eq n f hf hδ hβ hfix hproj⟩
  · intro β hβ hfix
    have hδmem : proj β ∈ (ggU .twistedE6 n f).D.roots :=
      (mem_roots_twistedE6 n f (proj β)).mpr (mem_rootFinset.mpr (isRoot_proj hβ))
    refine ⟨proj β, ⟨hδmem, ?_⟩, ?_⟩
    · exact fun _ => (g5_tw_long_iff_proj n f hδmem).mpr ⟨β, hβ, hfix, rfl⟩
    · exact g5_bridge_twistedE6_eq n f hf hδmem hβ hfix rfl

theorem ggG5_bridge_actual
    {t : StatedLieTag} (ht : GGExcFive t) (n f : ℕ) (hf : 1 ≤ f)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : GGRootClass (ggU t n f).D t δ) :
    ∃ β : Fin (langTag t).rank → ℤ, IsRoot (langTag t) β ∧ ggGraphLat t β = β ∧
      (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map (ggIotaK t n f hf)) =
        ratRankOne t f β := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact g5_bridge_actual_untw (Or.inl rfl) n f hf hδ.1
  · exact g5_bridge_actual_untw (Or.inr (Or.inl rfl)) n f hf hδ.1
  · exact g5_bridge_actual_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf hδ.1
  · exact g5_bridge_actual_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf hδ.1
  · exact (g5_bridge_twistedE6_core n f hf).1 δ hδ

theorem ggG5_bridge_lang
    {t : StatedLieTag} (ht : GGExcFive t) (n f : ℕ) (hf : 1 ≤ f)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) (hfix : ggGraphLat t β = β) :
    ∃ δ : Fin (ggU t n f).D.rank → ℤ, GGRootClass (ggU t n f).D t δ ∧
      (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map (ggIotaK t n f hf)) =
        ratRankOne t f β := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact g5_bridge_lang_untw (Or.inl rfl) n f hf hβ
  · exact g5_bridge_lang_untw (Or.inr (Or.inl rfl)) n f hf hβ
  · exact g5_bridge_lang_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf hβ
  · exact g5_bridge_lang_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf hβ
  · exact (g5_bridge_twistedE6_core n f hf).2 β hβ hfix

end Bridge

end CFSG.StandardType.GGFinModel.G5
