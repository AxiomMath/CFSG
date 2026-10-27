module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5CWGamma

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Plain

private theorem g5_weylElt_eq_pinnedX_prod
    (t : StatedLieTag) (i : Fin (langTag t).rank) :
    weylElt (langTag t) GGL i 1 =
      pinnedX (langTag t) GGL (Pi.single i 1) 1 *
        pinnedX (langTag t) GGL (-Pi.single i 1) 1 *
          pinnedX (langTag t) GGL (Pi.single i 1) 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, pinnedX_single, pinnedX_neg_single]
  rw [show (-↑(1 : GGLˣ)⁻¹ : GGL) = 1 from by
    rw [CharTwo.neg_eq, inv_one, Units.val_one]]
  rfl

private theorem g5_pinnedX_mem_range_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) (hf : 1 ≤ f)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) :
    pinnedX (langTag t) GGL β 1 ∈ (ggIota t n f hf).range := by
  rcases ht with rfl | rfl | rfl | rfl
  · have hβroot : β ∈ (ggU .F4 n f).D.roots :=
      (mem_roots_F4 n f β).mpr (mem_rootFinset.mpr hβ)
    have hmem : pinnedX (langTag .F4) GGL β 1 ∈
        (((ggU .F4 n f).D.rootGroup β).map (ggIotaK .F4 n f hf) : Set (ModGL (langTag .F4) GGL)) := by
      rw [ggBC_untw_param (Or.inl rfl) n f hf β hβroot]
      exact ⟨1, by dsimp only; rw [map_one]; rfl⟩
    obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨QuotientGroup.mk' _ y, hyeq⟩
  · have hβroot : β ∈ (ggU .E6 n f).D.roots :=
      (mem_roots_E6 n f β).mpr (mem_rootFinset.mpr hβ)
    have hmem : pinnedX (langTag .E6) GGL β 1 ∈
        (((ggU .E6 n f).D.rootGroup β).map (ggIotaK .E6 n f hf) : Set (ModGL (langTag .E6) GGL)) := by
      rw [ggBC_untw_param (Or.inr (Or.inl rfl)) n f hf β hβroot]
      exact ⟨1, by dsimp only; rw [map_one]; rfl⟩
    obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨QuotientGroup.mk' _ y, hyeq⟩
  · have hβroot : β ∈ (ggU .E7 n f).D.roots :=
      (mem_roots_E7 n f β).mpr (mem_rootFinset.mpr hβ)
    have hmem : pinnedX (langTag .E7) GGL β 1 ∈
        (((ggU .E7 n f).D.rootGroup β).map (ggIotaK .E7 n f hf) : Set (ModGL (langTag .E7) GGL)) := by
      rw [ggBC_untw_param (Or.inr (Or.inr (Or.inl rfl))) n f hf β hβroot]
      exact ⟨1, by dsimp only; rw [map_one]; rfl⟩
    obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨QuotientGroup.mk' _ y, hyeq⟩
  · have hβroot : β ∈ (ggU .E8 n f).D.roots :=
      (mem_roots_E8 n f β).mpr (mem_rootFinset.mpr hβ)
    have hmem : pinnedX (langTag .E8) GGL β 1 ∈
        (((ggU .E8 n f).D.rootGroup β).map (ggIotaK .E8 n f hf) : Set (ModGL (langTag .E8) GGL)) := by
      rw [ggBC_untw_param (Or.inr (Or.inr (Or.inr rfl))) n f hf β hβroot]
      exact ⟨1, by dsimp only; rw [map_one]; rfl⟩
    obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨QuotientGroup.mk' _ y, hyeq⟩

private theorem g5_phi_pinnedX_twisted_apply
    (f : ℕ)
    {γ : Fin (langTag .twistedE6).rank → ℤ} (hγ : IsRoot (langTag .twistedE6) γ) (c : GGL) :
    ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL γ c) =
      pinnedX (langTag .twistedE6) GGL (ggGraphLat .twistedE6 γ) (c ^ 2 ^ f) := by
  rw [ggPhi_pinnedX_twistedE6 f hγ c]
  rfl

private theorem g5_ggGraphLat_single {a b : Fin (langTag .twistedE6).rank}
    (h : (TwistTag.perm .E6) a = b) :
    ggGraphLat .twistedE6 (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) := by
  have h1 := permLattice_single (TwistTag.perm .E6) a
  exact (show ggGraphLat .twistedE6 (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      permLattice (TwistTag.perm .E6)
        (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) from rfl).trans
    (h1.trans (congrArg (fun x => (Pi.single x 1 : Fin (langTag .twistedE6).rank → ℤ)) h))

private theorem g5_ggGraphLat_neg_single {a b : Fin (langTag .twistedE6).rank}
    (h : (TwistTag.perm .E6) a = b) :
    ggGraphLat .twistedE6 (-Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (-Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) := by
  exact (show ggGraphLat .twistedE6 (-Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      -ggGraphLat .twistedE6 (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) from rfl).trans
    (congrArg Neg.neg (g5_ggGraphLat_single h))

private theorem g5_pinnedX_mem_range_twisted
    {n f : ℕ} (hf : 1 ≤ f)
    {α : Fin (langTag .twistedE6).rank → ℤ} (hα : IsRoot (langTag .twistedE6) α)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hsum : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = β)
    (hfix : ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL α 1) =
      pinnedX (langTag .twistedE6) GGL α 1) :
    pinnedX (langTag .twistedE6) GGL α 1 ∈ (ggIota .twistedE6 n f hf).range := by
  have hmem : pinnedX (langTag .twistedE6) GGL α 1 ∈
      CFSG.LieType.Steinberg.twistedRootSubgroup
        {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a}
        CFSG.LieType.Steinberg.TwistedE6.orbitMap
        (rootSubgroup (langTag .twistedE6) GGL) (ggPhi .twistedE6 f) β := by
    refine Subgroup.mem_inf.mpr ⟨?_, hfix⟩
    refine Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα
      (Subgroup.mem_iSup_of_mem ⟨1, Nat.one_pos, by rw [one_smul]; exact hsum⟩
        (mem_rootSubgroup.mpr ⟨1, rfl⟩)))
  rw [← ggBC_twistedE6 n f hf β hβ] at hmem
  obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
  exact ⟨QuotientGroup.mk' _ y, hyeq⟩

private theorem g5_pinnedX_fixed_mem_range_twisted
    {n f : ℕ} (hf : 1 ≤ f)
    {α : Fin (langTag .twistedE6).rank → ℤ} (hα : IsRoot (langTag .twistedE6) α)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hsum : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = β)
    (hperm : ggGraphLat .twistedE6 α = α) :
    pinnedX (langTag .twistedE6) GGL α 1 ∈ (ggIota .twistedE6 n f hf).range := by
  refine g5_pinnedX_mem_range_twisted hf hα hβ hsum ?_
  rw [g5_phi_pinnedX_twisted_apply f hα, hperm]
  simp only [one_pow]

private theorem g5_pinnedX_mul_mem_range_twisted
    {n f : ℕ} (hf : 1 ≤ f)
    {α α' : Fin (langTag .twistedE6).rank → ℤ}
    (hα : IsRoot (langTag .twistedE6) α) (hα' : IsRoot (langTag .twistedE6) α')
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hsum : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = β)
    (hsum' : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α' = β)
    (hfix : ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL α 1 *
      pinnedX (langTag .twistedE6) GGL α' 1) =
        pinnedX (langTag .twistedE6) GGL α 1 * pinnedX (langTag .twistedE6) GGL α' 1) :
    pinnedX (langTag .twistedE6) GGL α 1 * pinnedX (langTag .twistedE6) GGL α' 1 ∈
      (ggIota .twistedE6 n f hf).range := by
  have hmem : pinnedX (langTag .twistedE6) GGL α 1 * pinnedX (langTag .twistedE6) GGL α' 1 ∈
      CFSG.LieType.Steinberg.twistedRootSubgroup
        {a : Fin (langTag .twistedE6).rank → ℤ | IsRoot (langTag .twistedE6) a}
        CFSG.LieType.Steinberg.TwistedE6.orbitMap
        (rootSubgroup (langTag .twistedE6) GGL) (ggPhi .twistedE6 f) β := by
    refine Subgroup.mem_inf.mpr ⟨?_, hfix⟩
    refine mul_mem
      (Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα
        (Subgroup.mem_iSup_of_mem ⟨1, Nat.one_pos, by rw [one_smul]; exact hsum⟩
          (mem_rootSubgroup.mpr ⟨1, rfl⟩))))
      (Subgroup.mem_iSup_of_mem α' (Subgroup.mem_iSup_of_mem hα'
        (Subgroup.mem_iSup_of_mem ⟨1, Nat.one_pos, by rw [one_smul]; exact hsum'⟩
          (mem_rootSubgroup.mpr ⟨1, rfl⟩))))
  rw [← ggBC_twistedE6 n f hf β hβ] at hmem
  obtain ⟨y, -, hyeq⟩ := Subgroup.mem_map.mp hmem
  exact ⟨QuotientGroup.mk' _ y, hyeq⟩

private theorem g5_pinnedX_pair_mem_range_twisted
    {n f : ℕ} (hf : 1 ≤ f)
    {a b : Fin (langTag .twistedE6).rank}
    (hαa : IsRoot (langTag .twistedE6) (Pi.single a 1))
    (hαb : IsRoot (langTag .twistedE6) (Pi.single b 1))
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (ha : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap
      (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) = β)
    (hb : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap
      (Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) = β)
    (hperma : ggGraphLat .twistedE6 (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ))
    (hpermb : ggGraphLat .twistedE6 (Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ))
    (hcomm : pinnedX (langTag .twistedE6) GGL (Pi.single a 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single b 1) 1 =
      pinnedX (langTag .twistedE6) GGL (Pi.single b 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single a 1) 1) :
    pinnedX (langTag .twistedE6) GGL (Pi.single a 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single b 1) 1 ∈
      (ggIota .twistedE6 n f hf).range := by
  refine g5_pinnedX_mul_mem_range_twisted hf hαa hαb hβ ha hb ?_
  rw [map_mul, g5_phi_pinnedX_twisted_apply f hαa, g5_phi_pinnedX_twisted_apply f hαb,
    hperma, hpermb]
  simp only [one_pow]
  exact hcomm.symm

private theorem g5_pinnedX_pair_mem_range_twisted_neg
    {n f : ℕ} (hf : 1 ≤ f)
    {a b : Fin (langTag .twistedE6).rank}
    (hαa : IsRoot (langTag .twistedE6) (-Pi.single a 1))
    (hαb : IsRoot (langTag .twistedE6) (-Pi.single b 1))
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : -β ∈ (ggU .twistedE6 n f).D.roots)
    (ha : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap
      (-Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) = -β)
    (hb : CFSG.LieType.Steinberg.orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap
      (-Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) = -β)
    (hperma : ggGraphLat .twistedE6 (-Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (-Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ))
    (hpermb : ggGraphLat .twistedE6 (-Pi.single b 1 : Fin (langTag .twistedE6).rank → ℤ) =
      (-Pi.single a 1 : Fin (langTag .twistedE6).rank → ℤ))
    (hcomm : pinnedX (langTag .twistedE6) GGL (-Pi.single a 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single b 1) 1 =
      pinnedX (langTag .twistedE6) GGL (-Pi.single b 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single a 1) 1) :
    pinnedX (langTag .twistedE6) GGL (-Pi.single a 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single b 1) 1 ∈
      (ggIota .twistedE6 n f hf).range := by
  refine g5_pinnedX_mul_mem_range_twisted hf hαa hαb hβ ha hb ?_
  rw [map_mul, g5_phi_pinnedX_twisted_apply f hαa, g5_phi_pinnedX_twisted_apply f hαb,
    hperma, hpermb]
  simp only [one_pow]
  exact hcomm.symm

private theorem g5_mul_rearrange {G : Type*} [Group G] {x2 y2 x4 y4 : G}
    (h1 : x2 * x4 = x4 * x2) (h2 : x2 * y4 = y4 * x2)
    (h3 : y2 * x4 = x4 * y2) (h4 : y2 * y4 = y4 * y2) :
    (x2 * y2 * x2) * (x4 * y4 * x4) = (x2 * x4) * (y2 * y4) * (x2 * x4) := by
  calc (x2 * y2 * x2) * (x4 * y4 * x4)
      = x2 * y2 * (x2 * x4) * y4 * x4 := by group
    _ = x2 * y2 * (x4 * x2) * y4 * x4 := by rw [h1]
    _ = x2 * (y2 * x4) * x2 * y4 * x4 := by group
    _ = x2 * (x4 * y2) * x2 * y4 * x4 := by rw [h3]
    _ = x2 * x4 * y2 * (x2 * y4) * x4 := by group
    _ = x2 * x4 * y2 * (y4 * x2) * x4 := by rw [h2]
    _ = (x2 * x4) * (y2 * y4) * (x2 * x4) := by group

theorem ggG5_plain_mem_range
    {t : StatedLieTag} (ht : GGExcFive t) (n f : ℕ) (hf : 1 ≤ f)
    (u : WeylGroup (langTag t))
    (hu : ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
      canonicalRep (coxeterSystem (langTag t)) GGL u) :
    canonicalRep (coxeterSystem (langTag t)) GGL u ∈ (ggIota t n f hf).range := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · refine (Subgroup.closure_le _).mpr ?_
      (canonicalRep_mem_closure (coxeterSystem (langTag .F4)) GGL u)
    rintro x ⟨i, rfl⟩
    dsimp only
    rw [g5_weylElt_eq_pinnedX_prod]
    exact mul_mem (mul_mem
      (g5_pinnedX_mem_range_untw (Or.inl rfl) n f hf (IsRoot.basis i))
      (g5_pinnedX_mem_range_untw (Or.inl rfl) n f hf (IsRoot.neg (IsRoot.basis i))))
      (g5_pinnedX_mem_range_untw (Or.inl rfl) n f hf (IsRoot.basis i))
  · refine (Subgroup.closure_le _).mpr ?_
      (canonicalRep_mem_closure (coxeterSystem (langTag .E6)) GGL u)
    rintro x ⟨i, rfl⟩
    dsimp only
    rw [g5_weylElt_eq_pinnedX_prod]
    exact mul_mem (mul_mem
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inl rfl)) n f hf (IsRoot.basis i))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inl rfl)) n f hf (IsRoot.neg (IsRoot.basis i))))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inl rfl)) n f hf (IsRoot.basis i))
  · refine (Subgroup.closure_le _).mpr ?_
      (canonicalRep_mem_closure (coxeterSystem (langTag .E7)) GGL u)
    rintro x ⟨i, rfl⟩
    dsimp only
    rw [g5_weylElt_eq_pinnedX_prod]
    exact mul_mem (mul_mem
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf (IsRoot.basis i))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf
        (IsRoot.neg (IsRoot.basis i))))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inl rfl))) n f hf (IsRoot.basis i))
  · refine (Subgroup.closure_le _).mpr ?_
      (canonicalRep_mem_closure (coxeterSystem (langTag .E8)) GGL u)
    rintro x ⟨i, rfl⟩
    dsimp only
    rw [g5_weylElt_eq_pinnedX_prod]
    exact mul_mem (mul_mem
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf (IsRoot.basis i))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf
        (IsRoot.neg (IsRoot.basis i))))
      (g5_pinnedX_mem_range_untw (Or.inr (Or.inr (Or.inr rfl))) n f hf (IsRoot.basis i))
  ·
    have hu' : weylTwist TwistTag.E6 u = u := by
      have h1 : canonicalRep (coxeterSystem TwistTag.E6.tag) GGL (weylTwist TwistTag.E6 u) =
          canonicalRep (coxeterSystem TwistTag.E6.tag) GGL u := by
        rw [← CFSG.LieType.Chevalley.twistHom_canonicalRep (t := TwistTag.E6) (K := GGL)
          (σ := ggFrobT f) u]
        change ggPhi .twistedE6 f (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL u) = _
        exact hu
      exact CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_injective TwistTag.E6.tag GGL h1
    have hgen := ggG5_cwgamma_gen u hu'
    let T : Subgroup (WeylGroup TwistTag.E6.tag) :=
      { carrier := {v | canonicalRep (coxeterSystem TwistTag.E6.tag) GGL v ∈
          (ggIota .twistedE6 n f hf).range}
        one_mem' := by
          change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL 1 ∈
            (ggIota .twistedE6 n f hf).range
          rw [canonicalRep_one]
          exact Subgroup.one_mem _
        mul_mem' := by
          intro a b ha hb
          change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL (a * b) ∈
            (ggIota .twistedE6 n f hf).range
          rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
          exact Subgroup.mul_mem _ ha hb
        inv_mem' := by
          intro a ha
          change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL a⁻¹ ∈
            (ggIota .twistedE6 n f hf).range
          rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]
          exact Subgroup.inv_mem _ ha }
    have hx1 : pinnedX (langTag .twistedE6) GGL (Pi.single (1 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_fixed_mem_range_twisted hf (IsRoot.basis 1)
        (β := (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.basis 0))
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (1 : Fin 6) = 1 from by decide))
    have hy1 : pinnedX (langTag .twistedE6) GGL (-Pi.single (1 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_fixed_mem_range_twisted hf (IsRoot.neg (IsRoot.basis 1))
        (β := (-Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.neg (IsRoot.basis 0)))
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (1 : Fin 6) = 1 from by decide))
    have hx3 : pinnedX (langTag .twistedE6) GGL (Pi.single (3 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_fixed_mem_range_twisted hf (IsRoot.basis 3)
        (β := (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.basis 1))
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (3 : Fin 6) = 3 from by decide))
    have hy3 : pinnedX (langTag .twistedE6) GGL (-Pi.single (3 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_fixed_mem_range_twisted hf (IsRoot.neg (IsRoot.basis 3))
        (β := (-Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.neg (IsRoot.basis 1)))
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (3 : Fin 6) = 3 from by decide))
    have hcomm24 : pinnedX (langTag .twistedE6) GGL (Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (4 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (Pi.single (4 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (2 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.basis 2) (IsRoot.basis 4)
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm24b : pinnedX (langTag .twistedE6) GGL (Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (4 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (-Pi.single (4 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (2 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.basis 2) (IsRoot.neg (IsRoot.basis 4))
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm24c : pinnedX (langTag .twistedE6) GGL (-Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (4 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (Pi.single (4 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (2 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.neg (IsRoot.basis 2)) (IsRoot.basis 4)
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm24d : pinnedX (langTag .twistedE6) GGL (-Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (4 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (-Pi.single (4 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (2 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.neg (IsRoot.basis 2))
        (IsRoot.neg (IsRoot.basis 4)) (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hx24 : pinnedX (langTag .twistedE6) GGL (Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (4 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_pair_mem_range_twisted hf (IsRoot.basis 2) (IsRoot.basis 4)
        (β := (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.basis 2))
        (by funext c; fin_cases c <;> decide)
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (2 : Fin 6) = 4 from by decide))
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (4 : Fin 6) = 2 from by decide))
        hcomm24
    have hy24 : pinnedX (langTag .twistedE6) GGL (-Pi.single (2 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (4 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_pair_mem_range_twisted_neg hf (IsRoot.neg (IsRoot.basis 2))
        (IsRoot.neg (IsRoot.basis 4))
        (β := (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.neg (IsRoot.basis 2)))
        (by funext c; fin_cases c <;> decide)
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (2 : Fin 6) = 4 from by decide))
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (4 : Fin 6) = 2 from by decide))
        hcomm24d
    have hcomm05 : pinnedX (langTag .twistedE6) GGL (Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (5 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (Pi.single (5 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (0 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.basis 0) (IsRoot.basis 5)
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm05b : pinnedX (langTag .twistedE6) GGL (Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (5 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (-Pi.single (5 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (0 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.basis 0) (IsRoot.neg (IsRoot.basis 5))
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm05c : pinnedX (langTag .twistedE6) GGL (-Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (5 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (Pi.single (5 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (0 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.neg (IsRoot.basis 0)) (IsRoot.basis 5)
        (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hcomm05d : pinnedX (langTag .twistedE6) GGL (-Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (5 : Fin 6) 1) 1 =
      pinnedX (langTag .twistedE6) GGL (-Pi.single (5 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (0 : Fin 6) 1) 1 :=
      pinnedX_commute_of_iform_eq_zero GGL (IsRoot.neg (IsRoot.basis 0))
        (IsRoot.neg (IsRoot.basis 5)) (by decide +kernel) (by rw [← mem_rootFinset]; decide +kernel) 1 1
    have hx05 : pinnedX (langTag .twistedE6) GGL (Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (Pi.single (5 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_pair_mem_range_twisted hf (IsRoot.basis 0) (IsRoot.basis 5)
        (β := (Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.basis 3))
        (by funext c; fin_cases c <;> decide)
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (0 : Fin 6) = 5 from by decide))
        (g5_ggGraphLat_single (show (TwistTag.perm .E6) (5 : Fin 6) = 0 from by decide))
        hcomm05
    have hy05 : pinnedX (langTag .twistedE6) GGL (-Pi.single (0 : Fin 6) 1) 1 *
        pinnedX (langTag .twistedE6) GGL (-Pi.single (5 : Fin 6) 1) 1 ∈
        (ggIota .twistedE6 n f hf).range :=
      g5_pinnedX_pair_mem_range_twisted_neg hf (IsRoot.neg (IsRoot.basis 0))
        (IsRoot.neg (IsRoot.basis 5))
        (β := (Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ))
        (isRoot_iff_mem_roots.mp (IsRoot.neg (IsRoot.basis 3)))
        (by funext c; fin_cases c <;> decide)
        (by funext c; fin_cases c <;> decide)
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (0 : Fin 6) = 5 from by decide))
        (g5_ggGraphLat_neg_single (show (TwistTag.perm .E6) (5 : Fin 6) = 0 from by decide))
        hcomm05d
    have hS : ({(coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6)} :
          Set (WeylGroup TwistTag.E6.tag)) ⊆ T := by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
          ((coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6)) ∈
            (ggIota .twistedE6 n f hf).range
        rw [show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
            ((coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6)) =
            weylElt (langTag .twistedE6) GGL (1 : Fin 6) 1 from
          canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (1 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (1 : Fin 6)]
        exact mul_mem (mul_mem hx1 hy1) hx1
      · change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
          ((coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6)) ∈
            (ggIota .twistedE6 n f hf).range
        rw [show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
            ((coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6)) =
            weylElt (langTag .twistedE6) GGL (3 : Fin 6) 1 from
          canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (3 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (3 : Fin 6)]
        exact mul_mem (mul_mem hx3 hy3) hx3
      · change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
          ((coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6) *
            (coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6)) ∈
            (ggIota .twistedE6 n f hf).range
        rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
          show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
              ((coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6)) =
              weylElt (langTag .twistedE6) GGL (2 : Fin 6) 1 from
            canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (2 : Fin 6),
          show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
              ((coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6)) =
              weylElt (langTag .twistedE6) GGL (4 : Fin 6) 1 from
            canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (4 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (2 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (4 : Fin 6)]
        have hprod24 := mul_mem (mul_mem hx24 hy24) hx24
        convert hprod24 using 1
        rw [(g5_mul_rearrange hcomm24 hcomm24b hcomm24c hcomm24d).symm]
        exact Iff.rfl
      · change canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
          ((coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6) *
            (coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6)) ∈
            (ggIota .twistedE6 n f hf).range
        rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
          show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
              ((coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6)) =
              weylElt (langTag .twistedE6) GGL (0 : Fin 6) 1 from
            canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (0 : Fin 6),
          show canonicalRep (coxeterSystem TwistTag.E6.tag) GGL
              ((coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6)) =
              weylElt (langTag .twistedE6) GGL (5 : Fin 6) 1 from
            canonicalRep_simple (coxeterSystem TwistTag.E6.tag) GGL (5 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (0 : Fin 6),
          g5_weylElt_eq_pinnedX_prod .twistedE6 (5 : Fin 6)]
        have hprod05 := mul_mem (mul_mem hx05 hy05) hx05
        convert hprod05 using 1
        rw [(g5_mul_rearrange hcomm05 hcomm05b hcomm05c hcomm05d).symm]
        exact Iff.rfl
    exact (Subgroup.closure_le _).mpr hS hgen

end Plain

end CFSG.StandardType.GGFinModel.G5
