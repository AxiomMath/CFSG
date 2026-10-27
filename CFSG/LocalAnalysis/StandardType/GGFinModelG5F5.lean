module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RankOne
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Transfer
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Bridge
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameRank
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5WeylDict
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Theta
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Plain
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Conj
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndCompat

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section F5

private theorem g5_ratSL2_eq_range (f : ℕ) (hf : 1 ≤ f) :
    ratSL2 f = (Matrix.SpecialLinearGroup.map (ggRatEmb f)).range := by
  apply le_antisymm
  · intro A hA
    have hentry : ∀ i j, ggFrobT f ((A : Matrix (Fin 2) (Fin 2) GGL) i j) =
        (A : Matrix (Fin 2) (Fin 2) GGL) i j := by
      intro i j
      have h := congrArg (fun B : SL2 GGL =>
        (B : Matrix (Fin 2) (Fin 2) GGL) i j) hA
      simpa using h
    choose a ha using fun i j => (Set.ext_iff.mp (ggRatEmb_range hf)
      ((A : Matrix (Fin 2) (Fin 2) GGL) i j)).mpr
      (show ((A : Matrix (Fin 2) (Fin 2) GGL) i j) ^ 2 ^ f =
        (A : Matrix (Fin 2) (Fin 2) GGL) i j by
        rw [← ggFrobT_apply]; exact hentry i j)
    let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) := fun i j => a i j
    have hmapdet : ggRatEmb f M.det = (A : Matrix (Fin 2) (Fin 2) GGL).det := by
      change ggRatEmb f (Matrix.det M) = (A : Matrix (Fin 2) (Fin 2) GGL).det
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact ha i j
    have hdet : M.det = 1 := by
      apply RingHom.injective (ggRatEmb f)
      rw [hmapdet, A.2, map_one]
    refine MonoidHom.mem_range.mpr ⟨(⟨M, hdet⟩ : SL2 (GaloisField 2 f)), ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change ggRatEmb f (M i j) = (A : Matrix (Fin 2) (Fin 2) GGL) i j
    exact ha i j
  · intro A hA
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hA
    show Matrix.SpecialLinearGroup.map (ggFrobT f)
        (Matrix.SpecialLinearGroup.map (ggRatEmb f) B) =
      Matrix.SpecialLinearGroup.map (ggRatEmb f) B
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show ggFrobT f (ggRatEmb f (B i j)) = ggRatEmb f (B i j)
    rw [ggFrobT_apply]
    exact (Set.ext_iff.mp (ggRatEmb_range hf) (ggRatEmb f (B i j))).mp ⟨B i j, rfl⟩

private def g5_zpProp {G : Type*} [Group G] (p : ℕ) (S : Subgroup G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, orderOf x = p → orderOf y = p →
    ∃ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers x

private theorem g5_zp_transport {A B M : Type*} [Group A] [Group B] [Group M]
    (φ₁ : A →* B) (φ₂ : A →* M) (h₁ : Function.Injective φ₁)
    (h₂ : Function.Injective φ₂) {p : ℕ} (S : Subgroup A)
    (h : g5_zpProp p (S.map φ₂)) : g5_zpProp p (S.map φ₁) := by
  intro x hx y hy hpx hpy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hap : orderOf a = p := by
    rw [← orderOf_injective φ₁ h₁ a]; exact hpx
  have hbp : orderOf b = p := by
    rw [← orderOf_injective φ₁ h₁ b]; exact hpy
  have ha₂ : orderOf (φ₂ a) = p := by
    rw [orderOf_injective φ₂ h₂ a]; exact hap
  have hb₂ : orderOf (φ₂ b) = p := by
    rw [orderOf_injective φ₂ h₂ b]; exact hbp
  obtain ⟨s, hs, hsrel⟩ := h (φ₂ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    (φ₂ b) (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩) ha₂ hb₂
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hsrel
  have htb : t * b * t⁻¹ = a ^ m := by
    apply h₂
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact hm.symm
  refine ⟨φ₁ t, Subgroup.mem_map.mpr ⟨t, ht, rfl⟩, Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩⟩
  rw [← map_zpow, ← htb, map_mul, map_mul, map_inv]

private theorem g5_sl2_zp_top (p f : ℕ) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) :
    g5_zpProp p (⊤ : Subgroup (SL2 (GaloisField 2 f))) := by
  haveI : Finite (GaloisField 2 f) := by
    apply Nat.finite_of_card_ne_zero
    rw [GaloisField.card 2 f (by omega : (f : ℕ) ≠ 0)]
    exact pow_ne_zero f (by norm_num : (2 : ℕ) ≠ 0)
  intro x _ y _ hx hy
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; exact hp.ne_one hx.symm
  have hy1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy; exact hp.ne_one hy.symm
  have hxp : x ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; exact hx ▸ dvd_rfl
  have hyp : y ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; exact hy ▸ dvd_rfl
  obtain ⟨s, hs⟩ := spEnd_exists_conj_mem_zpowers hp hp2 hxp hx1 hyp hy1
  exact ⟨s, Subgroup.mem_top _, hs⟩


private theorem g5_map_inj (f : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (ggRatEmb f)) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h' := congrArg (fun C : SL2 GGL =>
    (C : Matrix (Fin 2) (Fin 2) GGL) i j) h
  change ggRatEmb f (A i j) = ggRatEmb f (B i j) at h'
  exact RingHom.injective (ggRatEmb f) h'

private theorem g5_ratRankOne_zp
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β)
    (hfix : ggGraphLat t β = β) :
    g5_zpProp p (ratRankOne t f β) := by
  have h1 : g5_zpProp p (⊤ : Subgroup (SL2 (GaloisField 2 f))) :=
    g5_sl2_zp_top p f hf hp hp2
  have h2 : g5_zpProp p (ratSL2 f) := by
    have h := g5_zp_transport (Matrix.SpecialLinearGroup.map (n := Fin 2) (ggRatEmb f))
      (MonoidHom.id _) (g5_map_inj f) Function.injective_id (p := p) (S := ⊤) (by simpa using h1)
    rw [g5_ratSL2_eq_range f hf]
    rw [MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.map (n := Fin 2) (ggRatEmb f))]
    exact h
  have h3 : g5_zpProp p ((ratSL2 f).map (rootSL2 (langTag t) GGL β)) :=
    g5_zp_transport (rootSL2 (langTag t) GGL β) (MonoidHom.id _)
      (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two
        (CharP.cast_eq_zero GGL 2) β)
      Function.injective_id (p := p) (S := ratSL2 f) (by simpa using h2)
  rw [ggG5_ratRankOne_eq ht f hβ hfix]
  exact h3

private theorem g5_rankOne_zp
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) {C : Type} [Group C]
    {D : LangDatum (langTag t) GGL} {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ}
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β)
    (hfix : ggGraphLat t β = β) {S : Subgroup C}
    (hSι : S.map ι₀ = ratRankOne t f β) :
    g5_zpProp p (S.map (MulAut.conj : C →* MulAut C)) := by
  have hz : g5_zpProp p (S.map ι₀) := by
    rw [hSι]
    exact g5_ratRankOne_zp (t := t) (p := p) (f := f) (ht := ht) hf hp hp2 hβ hfix
  exact g5_zp_transport (MulAut.conj : C →* MulAut C) ι₀
    (ggG5_conj_injective (ht := ht) hT) hT.pkg.inj (p := p) (S := S) hz

private theorem g5_conj_conj_map {C : Type*} [Group C] (S : Subgroup C) (a : C) :
    (S.map (MulAut.conj : C →* MulAut C)).map (MulAut.conj (MulAut.conj a)).toMonoidHom
      = (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj : C →* MulAut C) :=
  (Subgroup.map_map_conj S (MulAut.conj : C →* MulAut C) a).symm

private theorem g5_map_conj_map {C M : Type*} [Group C] [Group M] (ι : C →* M)
    (S : Subgroup C) (a : C) :
    (S.map (MulAut.conj a).toMonoidHom).map ι =
      (S.map ι).map (MulAut.conj (ι a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv]

private theorem g5_neg_mem_roots
    {t : StatedLieTag} (ht : GGExcFive t) (n f : ℕ)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    -δ ∈ (ggU t n f).D.roots := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact (mem_roots_F4 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_F4 n f δ).mp hδ))))
  · exact (mem_roots_E6 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E6 n f δ).mp hδ))))
  · exact (mem_roots_E7 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E7 n f δ).mp hδ))))
  · exact (mem_roots_E8 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_E8 n f δ).mp hδ))))
  · exact (mem_roots_twistedE6 n f (-δ)).mpr
      (mem_rootFinset.mpr (IsRoot.neg (mem_rootFinset.mp ((mem_roots_twistedE6 n f δ).mp hδ))))

private theorem g5_innDiag_conj_rankOne
    {t : StatedLieTag} {n f p : ℕ} [NeZero p]
    {ht : GGExcFive t} {κ : GGAutU t n f} (hκ : GGInnDiagU t n f κ)
    {δ : Fin (ggU t n f).D.rank → ℤ} (hδ : δ ∈ (ggU t n f).D.roots) :
    ∃ g ∈ (ggPsiU t n f).range,
      ∀ y ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ,
        (κ * g)⁻¹ * y * (κ * g) ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ := by
  obtain ⟨g, hg, hconj⟩ := hκ
  have hδneg : -δ ∈ (ggU t n f).D.roots := g5_neg_mem_roots ht n f hδ
  obtain ⟨haT, hhaT, hconja⟩ := hconj δ hδ
  obtain ⟨hbT, hhbT, hconjb⟩ := hconj (-δ) hδneg
  have haN : ∀ a ∈ (ggU t n f).D.rootGroup δ,
      haT * a * haT⁻¹ ∈ (ggU t n f).D.rootGroup δ := by
    intro a ha
    have hhaN : haT ∈ Subgroup.normalizer ((ggU t n f).D.rootGroup δ : Set _) :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hhaT δ) hδ
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hhaN]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hbN : ∀ b ∈ (ggU t n f).D.rootGroup (-δ),
      hbT * b * hbT⁻¹ ∈ (ggU t n f).D.rootGroup (-δ) := by
    intro b hb
    have hhbN : hbT ∈ Subgroup.normalizer ((ggU t n f).D.rootGroup (-δ) : Set _) :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hhbT (-δ)) hδneg
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hhbN]
    exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  refine ⟨g, hg, ?_⟩
  intro y hy
  have hJinv : (MulAut.conj (κ * g)⁻¹).toMonoidHom y ∈
      ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ := by
    have hJle : ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ ≤
        Subgroup.comap (MulAut.conj (κ * g)⁻¹).toMonoidHom
          (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ) := by
      rw [show ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ =
          ((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map
            (ggPsiU t n f) from rfl, Subgroup.map_le_iff_le_comap]
      apply sup_le
      · intro z hz
        change (MulAut.conj (κ * g)⁻¹) (ggPsiU t n f z) ∈
          ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ
        rw [show (MulAut.conj (κ * g)⁻¹) (ggPsiU t n f z) =
            ggPsiU t n f (haT * z * haT⁻¹) from by
          rw [MulAut.conj_apply]; simpa only [inv_inv] using hconja z hz]
        exact Subgroup.mem_map.mpr ⟨haT * z * haT⁻¹, Subgroup.mem_sup_left (haN z hz), rfl⟩
      · intro z hz
        change (MulAut.conj (κ * g)⁻¹) (ggPsiU t n f z) ∈
          ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ
        rw [show (MulAut.conj (κ * g)⁻¹) (ggPsiU t n f z) =
            ggPsiU t n f (hbT * z * hbT⁻¹) from by
          rw [MulAut.conj_apply]; simpa only [inv_inv] using hconjb z hz]
        exact Subgroup.mem_map.mpr ⟨hbT * z * hbT⁻¹, Subgroup.mem_sup_right (hbN z hz), rfl⟩
    exact hJle hy
  have hy' : (MulAut.conj (κ * g)⁻¹) y ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ := by
    simpa only [MulEquiv.coe_toMonoidHom] using hJinv
  simpa only [MulAut.conj_apply, inv_inv] using hy'

private theorem g5_beta_eq_conj
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    {C : Type} [Group C] {D : LangDatum (langTag t) GGL} {ι₀ : C →* ModGL (langTag t) GGL}
    {ζ : GGLˣ} (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    {z : Multiplicative (ggFixAdd p (piB t p f))} {c : C}
    (hc : ι₀ c = hT.uMap z) :
    hT.ggBetaHom z = MulAut.conj c := by
  apply MulEquiv.ext
  intro x
  apply hT.pkg.inj
  rw [hT.ggBetaHom_apply z x, MulAut.conj_apply, map_mul, map_mul, map_inv, hc]


private theorem g5_main
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] {ht : GGExcFive t}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (F : GGLangFrame t p f ht) :
    GGModelF5 t n f p (F.M.torusData (n := n) hf hp hp2 hreg).ggBfull (gram t f) (piB t p f)
      (F.M.torusData (n := n) hf hp hp2 hreg).ggCoord := by
  classical
  let hT := F.M.torusData (n := n) hf hp hp2 hreg
  intro κ hκ α hα hαclass
  obtain ⟨βL, hβLroot, hβLgraph, hβLR⟩ := ggG5_bridge_actual (t := t) ht n f hf hαclass
  obtain ⟨β₀, hβ₀F, u, huΦ, huβ⟩ := F.cover_f5 βL hβLroot hβLgraph
  have hβ₀abs : β₀ ∈ (ggU (absTag t) 6 f).D.roots := F.frame_root β₀ hβ₀F
  have hβ₀' : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β₀) :=
    (mem_roots_iff_isRoot f ht β₀).mp hβ₀abs
  have hfix₀ : ggGraphLat t (ggLangReidx (rank_eq_langTag f ht) β₀) =
      ggLangReidx (rank_eq_langTag f ht) β₀ := F.frame_graph β₀ hβ₀F
  have hnu_mem : canonicalRep (coxeterSystem (langTag t)) GGL u ∈ (ggIota t n f hf).range :=
    ggG5_plain_mem_range (t := t) ht n f hf u huΦ
  obtain ⟨c_u, hc_u⟩ := hnu_mem
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center (ggU t n f).K) c_u
  have hιh₀ : ggIotaK t n f hf h₀ = canonicalRep (coxeterSystem (langTag t)) GGL u := by
    rw [ggIotaK, MonoidHom.comp_apply, hh₀, hc_u]
  obtain ⟨δ₀, hδ₀class, hδ₀R⟩ := ggG5_bridge_lang (t := t) ht n f hf hβ₀' hfix₀
  have hconj_u : (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β₀)).map
      (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom =
      ratRankOne t f (u • ggLangReidx (rank_eq_langTag f ht) β₀) :=
    ggG5_ratRankOne_conj (t := t) ht f u huΦ hβ₀'
  let R : Subgroup (ggU t n f).K :=
    (ggU t n f).D.rootGroup δ₀ ⊔ (ggU t n f).D.rootGroup (-δ₀)
  let S₀ : Subgroup (GGKb t n f) := R.map (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))
  let a : GGKb t n f := QuotientGroup.mk' (Subgroup.center (ggU t n f).K) h₀
  have hιa : ggIota t n f hf a = canonicalRep (coxeterSystem (langTag t)) GGL u := by
    change ggIota t n f hf (QuotientGroup.mk' _ h₀) = _
    rw [← hιh₀]; rfl
  have hS₀ι : S₀.map (ggIota t n f hf) =
      ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β₀) := by
    change (R.map (QuotientGroup.mk' _)).map (ggIota t n f hf) = _
    rw [Subgroup.map_map]
    change R.map (ggIotaK t n f hf) = _
    exact hδ₀R
  have hJ₀ : ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀ =
      S₀.map (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) := by
    change ((ggU t n f).D.rootGroup δ₀ ⊔ (ggU t n f).D.rootGroup (-δ₀)).map
      (ggPsiU t n f) = _
    rw [show ggPsiU t n f = (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)).comp
        (QuotientGroup.mk' _) from rfl, ← Subgroup.map_map]
  have hcomp : (ggIota t n f hf).comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (ggIota t n f hf a)).toMonoidHom.comp (ggIota t n f hf) := by
    apply MonoidHom.ext
    intro x
    show ggIota t n f hf (a * x * a⁻¹) =
      ggIota t n f hf a * ggIota t n f hf x * (ggIota t n f hf a)⁻¹
    simp only [map_mul, map_inv]
  have hRαeq : ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
      (QuotientGroup.mk' (Subgroup.center (ggU t n f).K)) =
      S₀.map (MulAut.conj a).toMonoidHom := by
    apply Subgroup.map_injective hT.pkg.inj
    calc (((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
            (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))).map (ggIota t n f hf)
        = ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
            ((ggIota t n f hf).comp (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))) :=
          Subgroup.map_map _ _ _
      _ = ratRankOne t f βL := hβLR
      _ = ratRankOne t f (u • ggLangReidx (rank_eq_langTag f ht) β₀) := by rw [huβ]
      _ = (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β₀)).map
            (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom :=
          hconj_u.symm
      _ = (S₀.map (ggIota t n f hf)).map
            (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom := by
          rw [hS₀ι]
      _ = (S₀.map (MulAut.conj a).toMonoidHom).map (ggIota t n f hf) := by
          rw [← hιa]
          exact (g5_map_conj_map (ggIota t n f hf) S₀ a).symm
  have hαconj : ggRankOneSub (ggU t n f).D (ggPsiU t n f) α =
      (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀).map
        (MulAut.conj (ggPsiU t n f h₀)).toMonoidHom := by
    calc ggRankOneSub (ggU t n f).D (ggPsiU t n f) α
        = ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
            (ggPsiU t n f) := rfl
      _ = (((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map
            (QuotientGroup.mk' _)).map
            (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) := by
          rw [show (ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α) = _ from rfl]
          rw [show ggPsiU t n f = (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)).comp
              (QuotientGroup.mk' _) from rfl, ← Subgroup.map_map]
      _ = (S₀.map (MulAut.conj a).toMonoidHom).map
            (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) := by rw [hRαeq]
      _ = (S₀.map (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f))).map
            (MulAut.conj (MulAut.conj a)).toMonoidHom := (g5_conj_conj_map S₀ a).symm
      _ = (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀).map
            (MulAut.conj (ggPsiU t n f h₀)).toMonoidHom := by
          rw [← hJ₀]
          rfl
  obtain ⟨z₀, hz₀coord, hz₀mem, hz₀ord⟩ := ggG5_frame_pelt (ht := ht) F hT hβ₀F
  have hzc : hT.uMap z₀ ∈ S₀.map (ggIota t n f hf) := by rw [hS₀ι]; exact hz₀mem
  obtain ⟨c₀, hc₀S, hc₀ι⟩ := Subgroup.mem_map.mp hzc
  have hβz : hT.ggBetaHom z₀ = MulAut.conj c₀ := g5_beta_eq_conj (ht := ht) hT hc₀ι
  have hβzmem : hT.ggBetaHom z₀ ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀ := by
    rw [hJ₀, hβz]
    exact Subgroup.mem_map.mpr ⟨c₀, hc₀S, rfl⟩
  have hβzord : orderOf (hT.ggBetaHom z₀) = p := by
    rw [hβz]
    calc orderOf (MulAut.conj c₀)
        = orderOf c₀ := orderOf_injective
            (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f))
            (ggG5_conj_injective (ht := ht) hT) c₀
      _ = orderOf (ggIota t n f hf c₀) :=
            (orderOf_injective (ggIota t n f hf) hT.pkg.inj c₀).symm
      _ = orderOf (hT.uMap z₀) := by rw [hc₀ι]
      _ = p := hz₀ord
  have hx₁mem : (MulAut.conj (ggPsiU t n f h₀)).toMonoidHom (hT.ggBetaHom z₀) ∈
      ggRankOneSub (ggU t n f).D (ggPsiU t n f) α := by
    rw [hαconj]
    exact Subgroup.mem_map.mpr ⟨hT.ggBetaHom z₀, hβzmem, rfl⟩
  have hx₁ord : orderOf ((MulAut.conj (ggPsiU t n f h₀)).toMonoidHom
      (hT.ggBetaHom z₀)) = p := by
    rw [orderOf_injective (MulAut.conj (ggPsiU t n f h₀)).toMonoidHom
      (MulAut.conj (ggPsiU t n f h₀)).injective]
    exact hβzord
  constructor
  · exact ⟨_, hx₁mem, hx₁ord⟩
  · intro x' hx' hx'ord
    rw [hαconj] at hx'
    obtain ⟨j, hjJ, hxj⟩ := Subgroup.mem_map.mp hx'
    have hjord : orderOf j = p := by
      have h := orderOf_injective (MulAut.conj (ggPsiU t n f h₀)).toMonoidHom
        (MulAut.conj (ggPsiU t n f h₀)).injective j
      rw [hxj] at h
      exact h.symm.trans hx'ord
    obtain ⟨g, hg, hJinv⟩ := g5_innDiag_conj_rankOne (t := t) (n := n) (f := f) (p := p)
      (ht := ht) (κ := κ) hκ (δ := δ₀) hδ₀class.1
    let c : GGAutU t n f := κ * g
    let x : GGAutU t n f := c⁻¹ * hT.ggBetaHom z₀ * c
    have hxJ : x ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀ :=
      hJinv (hT.ggBetaHom z₀) hβzmem
    have hxord : orderOf x = p := by
      have hconjeq : x = (MulAut.conj c⁻¹).toMonoidHom (hT.ggBetaHom z₀) := by
        change c⁻¹ * hT.ggBetaHom z₀ * c = _
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hconjeq, orderOf_injective (MulAut.conj c⁻¹).toMonoidHom
        (MulAut.conj c⁻¹).injective]
      exact hβzord
    have hzp : g5_zpProp p (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ₀) := by
      rw [hJ₀]
      exact g5_rankOne_zp (t := t) (p := p) (f := f) (ht := ht) hf hp hp2
        (D := F.M.D) (ι₀ := ggIota t n f hf) (ζ := ggZeta p hp hp2) hT hβ₀' hfix₀ hS₀ι
    obtain ⟨s, hsJ, hsrel⟩ := hzp x hxJ j hjJ hxord hjord
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hsrel
    let z₀m : Multiplicative (ggFixAdd p (piB t p f)) := z₀ ^ m
    let b : hT.ggBfull := ⟨hT.ggBetaHom z₀m, ⟨z₀m, rfl⟩⟩
    have hbp : (b : GGAutU t n f) = (hT.ggBetaHom z₀) ^ m := by
      change hT.ggBetaHom z₀m = _
      rw [show z₀m = z₀ ^ m from rfl]
      exact map_zpow hT.ggBetaHom z₀ m
    have hcrel : c⁻¹ * (b : GGAutU t n f) * c = s * j * s⁻¹ := by
      rw [hbp]
      have h1 : c⁻¹ * (hT.ggBetaHom z₀ ^ m) * c =
          (MulAut.conj c⁻¹) (hT.ggBetaHom z₀ ^ m) := by rw [MulAut.conj_apply, inv_inv]
      have h2 : c⁻¹ * hT.ggBetaHom z₀ * c =
          (MulAut.conj c⁻¹) (hT.ggBetaHom z₀) := by rw [MulAut.conj_apply, inv_inv]
      rw [h1, map_zpow (MulAut.conj c⁻¹), ← h2]
      exact hm
    have hsψ : s ∈ (ggPsiU t n f).range := by
      obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hsJ
      exact MonoidHom.mem_range.mpr ⟨u₀, rfl⟩
    have hkne : ((m : ZMod p)) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdvd
      have hxm : x ^ m = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hxord]
        exact hdvd
      have hsj : s * j * s⁻¹ = 1 := by rw [← hm, hxm]
      have hj1 : j = 1 := by
        calc j = s⁻¹ * (s * j * s⁻¹) * s := by group
          _ = s⁻¹ * 1 * s := by rw [hsj]
          _ = 1 := by group
      rw [hj1, orderOf_one] at hjord
      exact hp.ne_one hjord.symm
    have hcoord : Multiplicative.toAdd (hT.ggCoord b) =
        (m : ZMod p) • corootCoord p (gram t f) β₀ := by
      have h1 : Multiplicative.toAdd (hT.ggCoord b) = (Multiplicative.toAdd z₀m).1 := by
        rw [hT.ggCoord_apply z₀m]
        rfl
      have h2 : (Multiplicative.toAdd z₀m).1 = m • (Multiplicative.toAdd z₀).1 := by
        change (Multiplicative.toAdd (z₀ ^ m)).1 = m • (Multiplicative.toAdd z₀).1
        rw [toAdd_zpow]
        rfl
      rw [h1, h2, hz₀coord]
      exact (Int.cast_smul_eq_zsmul (R := ZMod p) m (corootCoord p (gram t f) β₀)).symm
    have hbmem : (b : GGAutU t n f) ∈ (ggPsiU t n f).range := by
      rw [hbp]
      have hcm : (hT.ggBetaHom z₀) ^ m = MulAut.conj (c₀ ^ m) := by
        rw [hβz]
        exact (map_zpow (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) c₀ m).symm
      rw [hcm]
      obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective
        (N := Subgroup.center (ggU t n f).K) (c₀ ^ m)
      exact ⟨k₀, by rw [show ggPsiU t n f k₀ =
          (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f))
            (QuotientGroup.mk' _ k₀) from rfl, hk₀]⟩
    have hrel : κ⁻¹ * (b : GGAutU t n f) * κ =
        (g * s * (ggPsiU t n f h₀)⁻¹) * x' * (g * s * (ggPsiU t n f h₀)⁻¹)⁻¹ := by
      have h1 : κ⁻¹ * (b : GGAutU t n f) * κ =
          g * (c⁻¹ * (b : GGAutU t n f) * c) * g⁻¹ := by
        rw [show c = κ * g from rfl]
        group
      have h2 : (g * s * (ggPsiU t n f h₀)⁻¹) * x' *
          (g * s * (ggPsiU t n f h₀)⁻¹)⁻¹ = g * (s * j * s⁻¹) * g⁻¹ := by
        have hxj' : j = (ggPsiU t n f h₀)⁻¹ * x' * ggPsiU t n f h₀ := by
          rw [← hxj, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
        rw [hxj']
        group
      rw [h1, hcrel, ← h2]
    refine ⟨g * s * (ggPsiU t n f h₀)⁻¹, ?_, β₀, F.frame_root β₀ hβ₀F,
      F.frame_fixed β₀ hβ₀F, (m : ZMod p), hkne, b, hbmem, hrel, hcoord⟩
    exact (ggPsiU t n f).range.mul_mem
      ((ggPsiU t n f).range.mul_mem hg hsψ)
      ((ggPsiU t n f).range.inv_mem (MonoidHom.mem_range.mpr ⟨h₀, rfl⟩))

theorem ggG5_f5
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] {ht : GGExcFive t} (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (F : GGLangFrame t p f ht) :
    GGModelF5 t n f p (F.M.torusData (n := n) hf hp hp2 hreg).ggBfull (gram t f) (piB t p f)
      (F.M.torusData (n := n) hf hp hp2 hreg).ggCoord := by
  exact g5_main hf hp hp2 hreg F

end F5

end CFSG.StandardType.GGFinModel.G5
