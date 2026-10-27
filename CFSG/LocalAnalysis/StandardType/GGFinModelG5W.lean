module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5WeylDict
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Theta
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Plain
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Conj

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section W

private theorem g5_latChar_single {N p : ℕ} (z : Fin N → ZMod p) (i : Fin N) :
    latChar p z (Pi.single i 1) = z i := by
  simp only [latChar]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]; ring
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem g5_ggLangReidx_cast {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (fun i => v (Fin.cast h i)) = v := by
  subst h; rfl

private theorem g5_ggIota_psiU
    {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f)
    (k : (ggU t n f).K) (x : GGKb t n f) :
    ggIota t n f hf (ggPsiU t n f k x) =
      ggIotaK t n f hf k * ggIota t n f hf x * (ggIotaK t n f hf k)⁻¹ := by
  simp only [ggPsiU, ggIotaK, MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem g5_GGCommPi_inv
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {w : WeylGroup (langTag t)} (h : GGCommPi t p f ht w) : GGCommPi t p f ht w⁻¹ := by
  intro v
  have h1 := h (w⁻¹ • v)
  rw [smul_inv_smul] at h1
  calc w⁻¹ • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) v
      = w⁻¹ • (w • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f))
          (w⁻¹ • v)) := by rw [← h1]
    _ = permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) (w⁻¹ • v) := by
          rw [inv_smul_smul]

private theorem g5_commpi_transfer
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    (e : GGWeyl (ggU (absTag t) 6 f).D →* WeylGroup (langTag t))
    (he : ∀ (u : GGWeyl (ggU (absTag t) 6 f).D) (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ),
      ggLangReidx (rank_eq_langTag f ht) (weylAction (ggU (absTag t) 6 f).D.isFiniteType u v) =
        e u • ggLangReidx (rank_eq_langTag f ht) v)
    (u : GGWeyl (ggU (absTag t) 6 f).D)
    (hcomm : ∀ α, weylAction (ggU (absTag t) 6 f).D.isFiniteType u (latPerm (piB t p f) α) =
      latPerm (piB t p f) (weylAction (ggU (absTag t) 6 f).D.isFiniteType u α)) :
    GGCommPi t p f ht (e u) := by
  intro v
  let hR := rank_eq_langTag f ht
  let π' : Equiv.Perm (Fin (langTag t).rank) := (finCongr hR).permCongr (piB t p f)
  let v₀ : Fin (ggU (absTag t) 6 f).D.rank → ℤ := fun i => v (Fin.cast hR i)
  have hv₀ : ggLangReidx hR v₀ = v := g5_ggLangReidx_cast hR v
  have h1 : ggLangReidx hR (latPerm (piB t p f) v₀) = permLattice π' v := by
    rw [ggReidx_latPerm_permLattice hR (piB t p f) v₀, hv₀]
  calc (e u) • permLattice π' v
      = (e u) • ggLangReidx hR (latPerm (piB t p f) v₀) := by rw [h1]
    _ = ggLangReidx hR
          (weylAction (ggU (absTag t) 6 f).D.isFiniteType u (latPerm (piB t p f) v₀)) := by
          rw [he u (latPerm (piB t p f) v₀)]
    _ = ggLangReidx hR
          (latPerm (piB t p f) (weylAction (ggU (absTag t) 6 f).D.isFiniteType u v₀)) := by
          rw [hcomm v₀]
    _ = permLattice π'
          (ggLangReidx hR (weylAction (ggU (absTag t) 6 f).D.isFiniteType u v₀)) := by
          rw [ggReidx_latPerm_permLattice hR (piB t p f)]
    _ = permLattice π' ((e u) • v) := by rw [he u v₀, hv₀]

private theorem g5_transfer
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] {ht : GGExcFive t}
    (hf : 1 ≤ f) (F : GGLangFrame t p f ht) {ζ : GGLˣ}
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D (ggIota t n f hf) ζ)
    (k : (ggU t n f).K) (z z' : Multiplicative (ggFixAdd p (piB t p f)))
    (h : ggIotaK t n f hf k * hT.uMap z * (ggIotaK t n f hf k)⁻¹ = hT.uMap z') :
    ggPsiU t n f k * hT.ggBetaHom z * (ggPsiU t n f k)⁻¹ = hT.ggBetaHom z' := by
  ext c
  apply hT.pkg.inj
  rw [hT.ggBetaHom_apply]
  let y := (ggPsiU t n f k)⁻¹ c
  have hy : ggPsiU t n f k y = c := by
    simp only [y, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hstep : (ggPsiU t n f k * hT.ggBetaHom z * (ggPsiU t n f k)⁻¹) c =
      ggPsiU t n f k (hT.ggBetaHom z y) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
  rw [hstep, g5_ggIota_psiU hf k (hT.ggBetaHom z y), hT.ggBetaHom_apply]
  rw [← hy, g5_ggIota_psiU hf k y, ← h]
  group

theorem ggG5_w
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] {ht : GGExcFive t} (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (F : GGLangFrame t p f ht) :
    GGClauseW t n f p (ggPsiU t n f) (F.M.torusData (n := n) hf hp hp2 hreg).ggBfull (piB t p f)
      (F.M.torusData (n := n) hf hp hp2 hreg).ggCoord := by
  classical
  let hT := F.M.torusData (n := n) hf hp hp2 hreg
  intro u hcomm
  obtain ⟨e, he⟩ := ggG5_weyl_dict (t := t) ht f
  have hcomm_e : GGCommPi t p f ht (e u) :=
    g5_commpi_transfer (ht := ht) e he u hcomm
  have hcomm_e1 : GGCommPi t p f ht (e (u⁻¹)) := by
    rw [map_inv]
    exact g5_GGCommPi_inv hcomm_e
  have hYmem : F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL (e (u⁻¹)) * F.M.D.g0⁻¹ ∈
      (ggIota t n f hf).range := ggG5_Y_mem_range n hf hp hp2 hreg F (e (u⁻¹)) hcomm_e1
  obtain ⟨c₀, hc₀⟩ := MonoidHom.mem_range.mp hYmem
  obtain ⟨k₁, hk₁⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center (ggU t n f).K) c₀
  have hιk₁ : ggIotaK t n f hf k₁ =
      F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL (e (u⁻¹)) * F.M.D.g0⁻¹ := by
    rw [ggIotaK, MonoidHom.comp_apply, hk₁, hc₀]
  let m : GGAutU t n f := ggPsiU t n f k₁⁻¹
  have hm_range : m ∈ (ggPsiU t n f).range := ⟨k₁⁻¹, rfl⟩
  have hconj : ∀ z : Multiplicative (ggFixAdd p (piB t p f)),
      ∃ z' : Multiplicative (ggFixAdd p (piB t p f)),
        m * hT.ggBetaHom z * m⁻¹ = hT.ggBetaHom z' ∧
        (∀ γ γ' : Fin (ggU (absTag t) 6 f).D.rank → ℤ,
          ggLangReidx (rank_eq_langTag f ht) γ' =
            (e (u⁻¹)) • ggLangReidx (rank_eq_langTag f ht) γ →
          latChar p (Multiplicative.toAdd z').1 γ =
            latChar p (Multiplicative.toAdd z).1 γ') := by
    intro z
    obtain ⟨z', hz'eq, hz'char⟩ := ggG5_Y_conj_uMap (ht := ht) F hT (e (u⁻¹)) hcomm_e1 z
    refine ⟨z', ?_, hz'char⟩
    have hrel : ggIotaK t n f hf k₁⁻¹ * hT.uMap z * (ggIotaK t n f hf k₁⁻¹)⁻¹ =
        hT.uMap z' := by
      rw [map_inv, hιk₁, inv_inv]
      exact hz'eq
    have := g5_transfer (ht := ht) hf F hT (k₁⁻¹) z z' hrel
    simpa [m] using this
  have hfwd : ∀ x : hT.ggBfull, m * (x : GGAutU t n f) * m⁻¹ ∈ hT.ggBfull := by
    intro x
    obtain ⟨z, hz⟩ := (x.2 : (x : GGAutU t n f) ∈ hT.ggBfull)
    obtain ⟨z', hz'eq, -⟩ := hconj z
    rw [← hz, hz'eq]
    exact MonoidHom.mem_range.mpr ⟨z', rfl⟩
  haveI hfin : Finite hT.ggBfull :=
    Finite.of_injective hT.ggCoord hT.ggCoord_injective
  have hm_normalizer : m ∈ Subgroup.normalizer (hT.ggBfull : Set (GGAutU t n f)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hfwd ⟨b, hb⟩
    · intro hb
      let φ : hT.ggBfull → hT.ggBfull := fun x => ⟨m * (x : GGAutU t n f) * m⁻¹, hfwd x⟩
      have hφinj : Function.Injective φ := by
        intro x y hxy
        apply Subtype.ext
        have h1 := congrArg (fun y : hT.ggBfull => (y : GGAutU t n f)) hxy
        simp only [φ] at h1
        exact mul_left_cancel (mul_right_cancel h1)
      have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
      let b' : hT.ggBfull := ⟨m * b * m⁻¹, hb⟩
      obtain ⟨x, hx⟩ := hφsurj b'
      have hxb : (x : GGAutU t n f) = b := by
        have h1 := congrArg (fun y : hT.ggBfull => (y : GGAutU t n f)) hx
        simp only [φ, b'] at h1
        exact mul_left_cancel (mul_right_cancel h1)
      rw [← hxb]
      exact x.2
  refine ⟨m, Subgroup.mem_inf.mpr ⟨hm_range, hm_normalizer⟩, ?_⟩
  intro b b' hbb' i
  obtain ⟨z, hz⟩ := (b.2 : (b : GGAutU t n f) ∈ hT.ggBfull)
  have hb : b = ⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
  obtain ⟨z', hz'eq, hz'char⟩ := hconj z
  have hb' : b' = ⟨hT.ggBetaHom z', ⟨z', rfl⟩⟩ := by
    apply Subtype.ext
    rw [hbb', ← hz, hz'eq]
  have hcoordb : Multiplicative.toAdd (hT.ggCoord b) = (Multiplicative.toAdd z).1 := by
    rw [hb, hT.ggCoord_apply z]
    rfl
  have hcoordb' : Multiplicative.toAdd (hT.ggCoord b') = (Multiplicative.toAdd z').1 := by
    rw [hb', hT.ggCoord_apply z']
    rfl
  rw [hcoordb', hcoordb, ← g5_latChar_single (Multiplicative.toAdd z').1 i]
  exact hz'char (Pi.single i 1)
    (weylAction (ggU (absTag t) 6 f).D.isFiniteType u⁻¹ (Pi.single i 1))
    (he (u⁻¹) (Pi.single i 1))

end W

end CFSG.StandardType.GGFinModel.G5
