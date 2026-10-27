module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairOneAssembly
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTw
import all CFSG.LocalAnalysis.StandardType.GGFinModelG5Bridge
import all CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Orbit

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.GGFinModel.G5

private theorem postd_pow_f_aux {f : ℕ} (hf : 1 ≤ f) (c : GaloisField 2 f) : c ^ 2 ^ f = c := by
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp hf)
  calc c ^ 2 ^ f = c ^ Fintype.card (GaloisField 2 f) := by
        rw [← hcard, Nat.card_eq_fintype_card]
    _ = c := FiniteField.pow_card c

private theorem postd_ggRootSub_one {U : Type} [Group U] {G : Type} [Group G]
    (D : UniversalRootDatum U) (ψ : U →* G) (γ : Fin D.rank → ℤ) :
    ggRootSub D ψ γ 1 = (D.rootGroup γ).map ψ := by
  have hconj : (MulAut.conj (1 : U)).toMonoidHom = MonoidHom.id U := by
    ext x
    simp [MulAut.conj_apply]
  unfold ggRootSub
  rw [hconj, Subgroup.map_id]

private theorem postd_ggRootSub_map_eta
    {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hB : TwE6BaseCompat n f p ψ B) (hψr : ψ.range = G₀)
    (S : Subgroup (ggU .twistedE6 n f).K) :
    ((S.map ψ).subgroupOf G₀).map B.η =
      (S.map (ggIotaK .twistedE6 n f B.one_le_f)).map
        (MulAut.conj B.Δ.g0⁻¹).toMonoidHom := by
  let ψ' : (ggU .twistedE6 n f).K →* ↥G₀ :=
    { toFun := fun k => ⟨ψ k, by rw [← hψr]; exact ⟨k, rfl⟩⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun k l => Subtype.ext (map_mul ψ k l) }
  let ι : (ggU .twistedE6 n f).K →* ModGL Tag.E6 (ExcOmega f) :=
    show (ggU .twistedE6 n f).K →* ModGL Tag.E6 (ExcOmega f) from
      ggIotaK .twistedE6 n f B.one_le_f
  have hηψ' : B.η.comp ψ' = (MulAut.conj B.Δ.g0⁻¹).toMonoidHom.comp ι := by
    apply MonoidHom.ext
    intro k
    have h := hB.η_psi k (ψ' k).2
    have h' : B.η (ψ' k) = (MulAut.conj B.Δ.g0⁻¹).toMonoidHom (ι k) := h
    exact h'
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hkS, hk⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_map.mpr ⟨ι k, Subgroup.mem_map.mpr ⟨k, hkS, rfl⟩, ?_⟩
    have hx' : x = ψ' k := Subtype.ext (by rw [← hk]; rfl)
    rw [hx']
    exact (DFunLike.congr_fun hηψ' k).symm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hkS, hk⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨ψ' k, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map.mpr ⟨k, hkS, rfl⟩), ?_⟩
    rw [← hk]
    exact DFunLike.congr_fun hηψ' k

private theorem postd_step_conj_apply
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) (x : ModGL τ L) :
    D.step (D.g0⁻¹ * x * D.g0) = D.g0⁻¹ * D.Φ x * D.g0 := by
  unfold LangDatum.step
  change D.n * D.Φ (D.g0⁻¹ * x * D.g0) * D.n⁻¹ = D.g0⁻¹ * D.Φ x * D.g0
  simp only [map_mul, map_inv, D.lang]
  group

private theorem postd_map_step_conj
    {f : ℕ} {a : Fin (langTag .twistedE6).rank → ℤ}
    (ha : IsRoot (langTag .twistedE6) a) (hfix : rho a = a)
    (D : LangDatum (langTag .twistedE6) GGL) (hΦ : D.Φ = ggPhi .twistedE6 f) :
    (excCurve a D.g0⁻¹).map D.step = excCurve a D.g0⁻¹ := by
  have hfix' : ggGraphLat .twistedE6 a = a := hfix
  have hmapΦ : (rootSubgroup (langTag .twistedE6) GGL a).map D.Φ =
      rootSubgroup (langTag .twistedE6) GGL a := by
    rw [hΦ, lk0xu7a_ggPhi_map_rootSubgroup_twistedE6 (f := f) ha, hfix']
  have hstep : ∀ z, D.step ((MulAut.conj D.g0⁻¹).toMonoidHom z) =
      (MulAut.conj D.g0⁻¹).toMonoidHom (D.Φ z) := fun z =>
    postd_step_conj_apply D z
  rw [excCurve]
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [hstep x]
    exact Subgroup.mem_map.mpr ⟨D.Φ x, hmapΦ ▸ Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hx' : x ∈ (rootSubgroup (langTag .twistedE6) GGL a).map D.Φ := by
      rw [hmapΦ]; exact hx
    obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hx'
    refine Subgroup.mem_map.mpr
      ⟨(MulAut.conj D.g0⁻¹).toMonoidHom x',
        Subgroup.mem_map.mpr ⟨x', hx'mem, rfl⟩, ?_⟩
    rw [hstep x', hx'eq]

private theorem postd_card_fix_long
    {f : ℕ} (hf : 1 ≤ f) {a : Fin (Tag.rank .E6) → ℤ}
    (ha : IsRoot Tag.E6 a) (hfix : rho a = a) :
    Nat.card ↥(ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL a) =
      Nat.card (GaloisField 2 f) := by
  have hfix' : permLattice (TwistTag.perm .E6) a = a := hfix
  let g : GaloisField 2 f →
      ↥(ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL a) := fun c =>
    ⟨pinnedX (langTag .twistedE6) GGL a (ggRatEmb f c), by
      have hroot : pinnedX (langTag .twistedE6) GGL a (ggRatEmb f c) ∈
          rootSubgroup (langTag .twistedE6) GGL a :=
        (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL) (α := a)).2
          ⟨ggRatEmb f c, rfl⟩
      unfold ggFixGp
      refine Subgroup.mem_inf.mpr ⟨?_, hroot⟩
      refine Subgroup.mem_inf.mpr ⟨rootSubgroup_le_adjointGroup a hroot, ?_⟩
      refine MonoidHom.mem_eqLocusM.2 ?_
      change ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a (ggRatEmb f c)) =
        pinnedX (langTag .twistedE6) GGL a (ggRatEmb f c)
      have hp := ggPhi_pinnedX_twistedE6 (f := f) (γ := a) ha (ggRatEmb f c)
      rw [hp.trans (congrArg (fun z => pinnedX (langTag .twistedE6) GGL z
        ((ggRatEmb f c) ^ 2 ^ f)) hfix'), ← map_pow, postd_pow_f_aux hf c]⟩
  have hg : Function.Bijective g := by
    constructor
    · intro c d hcd
      apply (ggRatEmb f).injective
      apply pinnedX_injective (τ := langTag .twistedE6) (R := GGL) a
      exact congrArg Subtype.val hcd
    · intro x
      obtain ⟨d, hd⟩ :=
        (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL) (α := a)).1 x.2.2
      have hxPhi : ggPhi .twistedE6 f x.1 = x.1 := by
        have hxmem : x.1 ∈ adjointGroup (langTag .twistedE6) GGL ⊓
            (ggPhi .twistedE6 f).eqLocus
              (MonoidHom.id (ModGL (langTag .twistedE6) GGL)) := x.2.1
        exact MonoidHom.mem_eqLocusM.1 (Subgroup.mem_inf.1 hxmem).2
      have hp' : ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d) =
          pinnedX (langTag .twistedE6) GGL a (d ^ 2 ^ f) :=
        (ggPhi_pinnedX_twistedE6 (f := f) (γ := a) ha d).trans
          (congrArg (fun z => pinnedX (langTag .twistedE6) GGL z (d ^ 2 ^ f)) hfix')
      have hp : d ^ 2 ^ f = d := by
        apply pinnedX_injective (τ := langTag .twistedE6) (R := GGL) a
        calc pinnedX (langTag .twistedE6) GGL a (d ^ 2 ^ f)
            = ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d) := hp'.symm
          _ = ggPhi .twistedE6 f x.1 := by rw [hd]
          _ = x.1 := hxPhi
          _ = pinnedX (langTag .twistedE6) GGL a d := hd.symm
      have hdmem : d ∈ Set.range (ggRatEmb f) := by
        rw [ggRatEmb_range hf]
        exact hp
      obtain ⟨c, hc⟩ := hdmem
      exact ⟨c, Subtype.ext (by
        change pinnedX (langTag .twistedE6) GGL a (ggRatEmb f c) =
          (x : ModGL (langTag .twistedE6) GGL)
        rw [hc, hd])⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem exists_longRoot_twE6
    (n f : ℕ) :
    ∃ β : Fin (ggU .twistedE6 n f).D.rank → ℤ, β ∈ (ggU .twistedE6 n f).D.roots ∧
      (-β) ∈ (ggU .twistedE6 n f).D.roots ∧ GGLongRoot (ggU .twistedE6 n f).D β := by
  classical
  have hnon : (rootFinset Tag.F4).Nonempty :=
    ⟨Pi.single (0 : Fin Tag.F4.rank) 1, mem_rootFinset.mpr (IsRoot.basis _)⟩
  obtain ⟨β, hβF, hmax⟩ :=
    Finset.exists_max_image (rootFinset Tag.F4) (fun γ => ∑ i, γ i) hnon
  have hβmem : β ∈ (ggU .twistedE6 n f).D.roots := (mem_roots_twistedE6 n f β).mpr hβF
  refine ⟨β, hβmem, ?_, ?_⟩
  · exact (mem_roots_twistedE6 n f (-β)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp hβF)))
  · refine ⟨1, β, hβmem, ?_, ?_⟩
    · intro δ hδ
      exact hmax δ ((mem_roots_twistedE6 n f δ).mp hδ)
    · rfl

theorem twE6_stdPair
    {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hB : TwE6BaseCompat n f p ψ B) (hψr : ψ.range = G₀)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hβn : (-β) ∈ (ggU .twistedE6 n f).D.roots) (hlong : GGLongRoot (ggU .twistedE6 n f).D β) :
    ∃ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a ∧
      (excCurve a B.Δ.g0⁻¹).map B.Δ.step = excCurve a B.Δ.g0⁻¹ ∧
      (excCurve (-a) B.Δ.g0⁻¹).map B.Δ.step = excCurve (-a) B.Δ.g0⁻¹ ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ β 1).subgroupOf G₀).map B.η =
        excCurve a B.Δ.g0⁻¹ ⊓ B.Δ.model ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ (-β) 1).subgroupOf G₀).map B.η =
        excCurve (-a) B.Δ.g0⁻¹ ⊓ B.Δ.model ∧
      Nat.card ↥(excCurve a B.Δ.g0⁻¹ ⊓ B.Δ.model) = Nat.card (GaloisField 2 f) ∧
      Nat.card ↥(excCurve (-a) B.Δ.g0⁻¹ ⊓ B.Δ.model) = Nat.card (GaloisField 2 f) := by
  obtain ⟨a', ha', hfix', hproj'⟩ := (g5_tw_long_iff_proj n f hβ).mp hlong
  let a : Fin (Tag.rank .E6) → ℤ := a'
  have ha : IsRoot Tag.E6 a := ha'
  have hfix : rho a = a := hfix'
  have hproj : proj a = β := hproj'
  let Δ : LangDatum (langTag .twistedE6) GGL := B.Δ
  have hΔΦ : Δ.Φ = ggPhi .twistedE6 f := hB.Φ_eq
  have hbridge : (((ggU .twistedE6 n f).D.rootGroup β).map
        (ggIotaK .twistedE6 n f B.one_le_f)) =
      ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL a := by
    rw [ggBC_twistedE6 n f B.one_le_f β hβ]
    exact g5_twistedRootSubgroup_proj (n := n) (f := f) (δ := β) (β := a) hproj ha hfix
  have hmapβ := postd_ggRootSub_map_eta B hB hψr ((ggU .twistedE6 n f).D.rootGroup β)
  have hfix_eq : Δ.fix = ggFixGp .twistedE6 f :=
    ggFixGp_eq_fix (t := .twistedE6) (f := f) Δ hΔΦ
  have hR : excCurve a Δ.g0⁻¹ ⊓ Δ.model =
      ((ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL a).map
        (MulAut.conj Δ.g0⁻¹).toMonoidHom) := by
    rw [LangDescent.model_eq Δ, hfix_eq]
    rw [Subgroup.map_inf (ggFixGp .twistedE6 f)
      (rootSubgroup (langTag .twistedE6) GGL a)
      (MulAut.conj Δ.g0⁻¹).toMonoidHom (MulAut.conj Δ.g0⁻¹).injective]
    exact inf_comm _ _
  have h1 : ((ggRootSub (ggU .twistedE6 n f).D ψ β 1).subgroupOf G₀).map B.η =
      excCurve a Δ.g0⁻¹ ⊓ Δ.model := by
    rw [postd_ggRootSub_one (ggU .twistedE6 n f).D ψ β, hmapβ, hbridge]
    exact hR.symm
  have hfix_neg : rho (-a) = -a := by
    have h1 : rho (-a) = -rho a := map_neg rhoHom a
    rw [h1, hfix]
  have hproj_neg : proj (-a) = -β := by
    rw [map_neg proj a]
    exact congrArg Neg.neg hproj
  have hbridge_neg : (((ggU .twistedE6 n f).D.rootGroup (-β)).map
        (ggIotaK .twistedE6 n f B.one_le_f)) =
      ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL (-a) := by
    rw [ggBC_twistedE6 n f B.one_le_f (-β) hβn]
    exact g5_twistedRootSubgroup_proj (n := n) (f := f) (δ := -β) (β := -a) hproj_neg
      (IsRoot.neg ha) hfix_neg
  have hmapβn := postd_ggRootSub_map_eta B hB hψr ((ggU .twistedE6 n f).D.rootGroup (-β))
  have hR_neg : excCurve (-a) Δ.g0⁻¹ ⊓ Δ.model =
      ((ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL (-a)).map
        (MulAut.conj Δ.g0⁻¹).toMonoidHom) := by
    rw [LangDescent.model_eq Δ, hfix_eq]
    rw [Subgroup.map_inf (ggFixGp .twistedE6 f)
      (rootSubgroup (langTag .twistedE6) GGL (-a))
      (MulAut.conj Δ.g0⁻¹).toMonoidHom (MulAut.conj Δ.g0⁻¹).injective]
    exact inf_comm _ _
  have h2 : ((ggRootSub (ggU .twistedE6 n f).D ψ (-β) 1).subgroupOf G₀).map B.η =
      excCurve (-a) Δ.g0⁻¹ ⊓ Δ.model := by
    rw [postd_ggRootSub_one (ggU .twistedE6 n f).D ψ (-β), hmapβn, hbridge_neg]
    exact hR_neg.symm
  have hstep : (excCurve a Δ.g0⁻¹).map Δ.step = excCurve a Δ.g0⁻¹ :=
    postd_map_step_conj ha hfix Δ hΔΦ
  have hstepn : (excCurve (-a) Δ.g0⁻¹).map Δ.step = excCurve (-a) Δ.g0⁻¹ :=
    postd_map_step_conj (IsRoot.neg ha) hfix_neg Δ hΔΦ
  have hcard : Nat.card ↥(excCurve a Δ.g0⁻¹ ⊓ Δ.model) =
      Nat.card (GaloisField 2 f) := by
    rw [hR]
    exact (Subgroup.card_map_of_injective
      (f := (MulAut.conj Δ.g0⁻¹).toMonoidHom) (MulAut.conj Δ.g0⁻¹).injective
      (K := ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL a)).trans
        (postd_card_fix_long B.one_le_f ha hfix)
  have hcardn : Nat.card ↥(excCurve (-a) Δ.g0⁻¹ ⊓ Δ.model) =
      Nat.card (GaloisField 2 f) := by
    rw [hR_neg]
    exact (Subgroup.card_map_of_injective
      (f := (MulAut.conj Δ.g0⁻¹).toMonoidHom) (MulAut.conj Δ.g0⁻¹).injective
      (K := ggFixGp .twistedE6 f ⊓ rootSubgroup (langTag .twistedE6) GGL (-a))).trans
        (postd_card_fix_long B.one_le_f (IsRoot.neg ha) hfix_neg)
  exact ⟨a, ha, hstep, hstepn, h1, h2, hcard, hcardn⟩

end CFSG.StandardType.LieKnownR2.ExcPos

end
