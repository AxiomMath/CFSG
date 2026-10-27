module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldFix
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalFieldSp

public section

namespace CFSG.StandardType

namespace OrdPFieldNsSp

open Matrix CFSG.Assembly.LowTwoRank

variable {n : ℕ}

theorem spJ_map {K L : Type} [Field K] [Field L] (ι : K →+* L) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map ι =
      fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_map]
  congr 1
  · exact Matrix.map_zero _ (map_zero ι)
  · exact Matrix.map_one _ (map_zero ι) (map_one ι)
  · rw [Matrix.map_neg _ (map_neg ι), Matrix.map_one _ (map_zero ι) (map_one ι)]
  · exact Matrix.map_zero _ (map_zero ι)

theorem mem_statedSp_map_iff {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (x : GL (Fin n ⊕ Fin n) K) :
    Matrix.GeneralLinearGroup.map ι x ∈ StatedSp n L ↔ x ∈ StatedSp n K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  have hinj : Function.Injective fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K => M.map ι :=
    Matrix.map_injective ι.injective
  have hc : ((Matrix.GeneralLinearGroup.map ι x : GL (Fin n ⊕ Fin n) L) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) =
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map ι := rfl
  have he : ((x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).map ι =
      ((x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map ι)ᵀ * fromBlocks 0 1 (-1) 0 *
        (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map ι := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, spJ_map]
  rw [hc, ← he, ← spJ_map ι (n := n)]
  exact hinj.eq_iff

section Fixed

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_fixed_elemAb {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (hpS : p ∣ Nat.card (StatedSp n F)) :
    ∃ E : Subgroup (StatedSp n F), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧
      (∀ a ∈ E, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n F σ a = a) ∧
      p ^ ((n + n) / Nat.lcm 2 (OrdPNS.ordQ F p)) ≤ Nat.card E := by
  classical
  set K₀ := FixedPoints.subfield (Subgroup.zpowers σ) F with hK₀
  set ι : K₀ →+* F := K₀.subtype with hι
  have hιinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) ι) := by
    intro a b hab
    apply Units.ext
    exact Matrix.map_injective Subtype.val_injective
      (congrArg (fun g : GL (Fin n ⊕ Fin n) F => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
        hab)
  set Φ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n F σ with hΦ
  have hΦp : Φ ^ p = 1 := by rw [hΦ, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  obtain ⟨x, hxo, hxΦ⟩ :=
    OrdPFieldNs.exists_orderOf_eq_fixed (v := 1) hp Φ (by rwa [pow_one]) hpS
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) (x : GL (Fin n ⊕ Fin n) F) = x := by
    apply Units.ext
    have h1 := congrArg (fun g : StatedSp n F =>
      ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hxΦ
    simp only [hΦ, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp] at h1
    exact h1
  obtain ⟨x₀, hx₀⟩ := OrdPFieldNs.exists_gl_map_eq (x : GL (Fin n ⊕ Fin n) F) hxσ
  have hx₀S : x₀ ∈ StatedSp n K₀ := (mem_statedSp_map_iff ι x₀).mp (hx₀ ▸ x.2)
  have hx₀p : x₀ ^ p = 1 := hιinj (by
    have h1 : ((x ^ p : StatedSp n F) : GL (Fin n ⊕ Fin n) F) = 1 := by rw [hxp]; rfl
    rw [Subgroup.coe_pow] at h1
    rw [map_pow, hx₀, map_one, h1])
  have hx₀1 : x₀ ≠ 1 := fun h1 => by
    have h2 : (x : GL (Fin n ⊕ Fin n) F) = 1 := by rw [← hx₀, h1, map_one]
    have hx1 : x = 1 := Subtype.ext h2
    rw [hx1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  set u₀ := OrdPNsSp.spReindex n K₀ x₀ with hu₀def
  have hu₀ : u₀ ∈ OrdPNsGen.isoGL (OrdPNsSp.spFormD n K₀) :=
    (OrdPNsSp.spReindex_mem_isoGL_iff x₀).mpr hx₀S
  have hu₀p : u₀ ^ p = 1 := by rw [hu₀def, ← map_pow, hx₀p, map_one]
  have hu₀1 : u₀ ≠ 1 := fun h1 => hx₀1 ((OrdPNsSp.spReindex n K₀).injective (by rw [← hu₀def, h1,
    map_one]))
  obtain ⟨E₀, hE₀, hu₀E⟩ := OrdPNsGen.exists_genMax_mem OrdPNsSp.spFormD_isSymm
    OrdPNsSp.spFormD_sep hp hp2 hu₀ hu₀p
  have hcard₀ := OrdPNsGen.pow_lcm_le_card OrdPNsSp.spFormD_isAlt hE₀ (fun g hg => hg)
    ⟨u₀, hu₀E, hu₀1⟩
  rw [OrdPFieldNs.ordQ_fixed (v := 1) hp (hσ.trans (pow_one p).symm)] at hcard₀
  have hmem : ∀ g : OrdPNsGen.isoGL (OrdPNsSp.spFormD n K₀),
      Matrix.GeneralLinearGroup.map ι ((OrdPNsSp.spReindex n K₀).symm g) ∈ StatedSp n F := by
    intro g
    rw [mem_statedSp_map_iff, ← OrdPNsSp.spReindex_mem_isoGL_iff, MulEquiv.apply_symm_apply]
    exact g.2
  set κ : OrdPNsGen.isoGL (OrdPNsSp.spFormD n K₀) →* StatedSp n F :=
    MonoidHom.codRestrict (((Matrix.GeneralLinearGroup.map ι).comp
      (OrdPNsSp.spReindex n K₀).symm.toMonoidHom).comp
        (OrdPNsGen.isoGL (OrdPNsSp.spFormD n K₀)).subtype) (StatedSp n F) hmem with hκdef
  have hκ : ∀ g, ((κ g : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      Matrix.GeneralLinearGroup.map ι ((OrdPNsSp.spReindex n K₀).symm g) := fun g => rfl
  have hκinj : Function.Injective κ := by
    intro a b hab
    have h1 := congrArg (fun z : StatedSp n F => (z : GL (Fin n ⊕ Fin n) F)) hab
    simp only [hκ] at h1
    exact Subtype.ext ((OrdPNsSp.spReindex n K₀).symm.injective (hιinj h1))
  refine ⟨(E₀.subgroupOf (OrdPNsGen.isoGL (OrdPNsSp.spFormD n K₀))).map κ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE₀.comm _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have h1 : a ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hE₀.pow _ (Subgroup.mem_subgroupOf.mp ha))
    rw [h1, map_one]
  · rintro _ ⟨a, -, rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp, hκ]
    exact congrArg (fun g : GL (Fin n ⊕ Fin n) F => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
      (OrdPFieldNs.gl_map_fixed ((OrdPNsSp.spReindex n K₀).symm a))
  · rw [Subgroup.card_map_of_injective hκinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀.le).toEquiv]
    exact hcard₀

end Fixed

section Bound

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic

theorem card_bstar_le {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs G₀ : Subgroup G}
    {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ) :
    Nat.card Bs ≤ p ^ ((n + n) / Nat.lcm 2 (OrdPNS.ordQ (GaloisField 2 f) p)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n := hrank
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hinner : ∀ c : G, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := F) hrk ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  set B := OrdPNsSp.spFormD n F with hB
  set φ : StatedSp n F →* GL (Fin (n + n)) F :=
    (OrdPNsSp.spReindex n F).toMonoidHom.comp (StatedSp n F).subtype with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext ((OrdPNsSp.spReindex n F).injective hab)
  have hφiso : ∀ s : StatedSp n F, φ s ∈ OrdPNsGen.isoGL B := fun s =>
    (OrdPNsSp.spReindex_mem_isoGL_iff (s : GL (Fin n ⊕ Fin n) F)).mpr s.2
  have hφsurj : ∀ g ∈ OrdPNsGen.isoGL B, ∃ s : StatedSp n F, φ s = g := by
    intro g hg
    refine ⟨⟨(OrdPNsSp.spReindex n F).symm g, ?_⟩, ?_⟩
    · rw [← OrdPNsSp.spReindex_mem_isoGL_iff, MulEquiv.apply_symm_apply]
      exact hg
    · change OrdPNsSp.spReindex n F ((OrdPNsSp.spReindex n F).symm g) = g
      exact MulEquiv.apply_symm_apply _ g
  have hBs : B.IsSymm := OrdPNsSp.spFormD_isSymm
  have hBsep : ∀ v, (∀ w, B v w = 0) → v = 0 := OrdPNsSp.spFormD_sep
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hBsψ : Bs ≤ ψ.range := fun b hb => hinner b (hS.innerDiag b hb)
  set A := (Bs.comap ψ).map φ with hA
  have hAmax : NoOffOm.GenMax B (OrdPNsGen.isoGL B) p A := by
    refine ⟨hBs, hBsep, hpp, hp2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      exact hφiso s
    · rintro _ ⟨s, hs, rfl⟩
      rw [← map_pow]
      have h1 : s ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hS.elem.2 _ hs)
      rw [h1, map_one]
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul]
      have h1 : s * t = t * s :=
        hinj (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hS.elem hs ht)
      rw [h1]
    · intro g hg hgp hgA
      obtain ⟨s, rfl⟩ := hφsurj g hg
      have hsp : s ^ p = 1 := hφinj (by rw [map_pow, hgp, map_one])
      have hsc : ψ s ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨t, rfl⟩ := hBsψ hb
        have h1 := hgA (φ t) ⟨t, hb, rfl⟩
        rw [← map_mul, ← map_mul] at h1
        rw [← map_mul, ← map_mul, hφinj h1]
      exact ⟨s, hS.omega _ hsc (by rw [← map_pow, hsp, map_one]), rfl⟩
    · intro g hg v w
      obtain ⟨s, -, rfl⟩ := hg
      exact hφiso s v w
    · intro c hc W hW hWA
      have hcp : NoOffOm.glin c ^ p = 1 := by
        obtain ⟨s, hs, rfl⟩ := hc
        have h1 : s ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hS.elem.2 _ hs)
        rw [← NoOffOm.glin_pow, ← map_pow, h1, map_one, NoOffOm.glin_one]
      have hciso : c ∈ OrdPNsGen.isoGL B := by
        obtain ⟨s, -, rfl⟩ := hc
        exact hφiso s
      have hzp := SUTB.restrictElt_pow_eq_one hW (hWA c hc) hcp
      obtain ⟨g, hg⟩ := OrdPNsGen.exists_gl_of_pow hp1 hzp
      refine ⟨g, ?_, hg⟩
      intro v w
      rw [hg]
      exact SUTB.restrictElt_isometry hW _ hBs hciso v w
  have hAcard : Nat.card A = Nat.card Bs := by
    rw [hA, Subgroup.card_map_of_injective hφinj]
    have h1 : (Bs.comap ψ).map ψ = Bs := Subgroup.map_comap_eq_self hBsψ
    rw [← Subgroup.card_map_of_injective hinj, h1]
  rw [← hAcard]
  exact OrdPNsGen.card_le_pow_lcm OrdPNsSp.spFormD_isAlt hAmax

end Bound

section Setting

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem exists_conj_mem_centralizer {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs G₀ : Subgroup G} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n := hrank
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hpp⟩
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hπker : (proj n (GaloisField 2 f)).ker = Subgroup.center (StatedSp n (GaloisField 2 f)) := by
    rw [ker_proj]
    exact (Symplectic.center_eq n _).symm
  have hk : (proj n (GaloisField 2 f)).ker = ψ.ker :=
    hπker.trans (AutSt.ker_eq_center hker hC).symm
  set Θ : StatedProj (StatedSp n (GaloisField 2 f)) ≃* ψ.range :=
    AutSt.modelEquiv ψ (proj n (GaloisField 2 f)) proj_surjective hk with hΘdef
  have hΘ : ∀ x, ((Θ (proj n (GaloisField 2 f) x) : ψ.range) : G) = ψ x :=
    AutSt.modelEquiv_apply ψ _ proj_surjective hk
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hyM
  set a : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : ψ.range, ((a x : ψ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (StatedProj (StatedSp n (GaloisField 2 f))) := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ x x' : StatedSp n (GaloisField 2 f),
      β (proj n (GaloisField 2 f) x) = proj n (GaloisField 2 f) x' → y⁻¹ * ψ x * y = ψ x' := by
    intro x x' hxx'
    have e := congrArg (fun z => ((Θ z : ψ.range) : G)) hxx'
    simp only [hβ, ha, hΘ] at e
    exact e
  obtain ⟨A, σ, hAσ⟩ : ∃ (A : gsp n (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
      β = conjAut n (GaloisField 2 f) A * fieldAut n (GaloisField 2 f) σ := by
    rcases (show 3 ≤ n ∨ n = 2 by omega) with h3 | rfl
    · exact (automorphism_generation (K := GaloisField 2 f) h3).2 β
    · exact RootDetectSp.sp_two_form_of_pow_eq_one (hpp.odd_of_ne_two hp2) β hβp
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hAσ
    obtain ⟨g, hg⟩ := RootDetectSp.exists_sp_conj_eq A
    apply hyI
    have hcent : y * ψ g ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have e := hrel x (g * x * g⁻¹) (by rw [hAσ, conjAut_proj, hg])
      rw [map_mul, map_mul, map_inv] at e
      calc ψ x * (y * ψ g) = y * (y⁻¹ * ψ x * y) * ψ g := by group
        _ = y * (ψ g * ψ x * (ψ g)⁻¹) * ψ g := by rw [e]
        _ = y * ψ g * ψ x := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hy : y = ψ g⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hcent
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨g⁻¹, hy.symm⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨hσo, H, hH⟩ := RecipeFieldSpU.conjAut_mul_fieldAut_of_pow_eq_one
    (K := GaloisField 2 f) (by omega) hpp A σ hσ1 (by rw [← hAσ]; exact hβp)
  obtain ⟨h, hh⟩ := RootDetectSp.exists_sp_conj_eq H
  by_cases hB1 : ∀ b ∈ Bs, b = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hB1 b hb]
    simp
  push Not at hB1
  obtain ⟨b, hb, hb1⟩ := hB1
  obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker
    (hS.innerDiag b hb)
  rw [hC, Subgroup.mem_bot] at hcg
  obtain ⟨s, hs⟩ : b ∈ ψ.range := by
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hsp : s ^ p = 1 := hinj (by rw [map_pow, hs, map_one]; exact hS.elem.2 b hb)
  have hs1 : s ≠ 1 := fun h1 => hb1 (by rw [← hs, h1, map_one])
  have hpS : p ∣ Nat.card (StatedSp n (GaloisField 2 f)) := by
    rw [← orderOf_eq_prime hsp hs1]
    exact orderOf_dvd_natCard s
  obtain ⟨E, hEc, hEp, hEσ, hEcard⟩ := exists_fixed_elemAb hpp hp2 hσo hpS
  have hinj' : Function.Injective (ψ.comp (MulAut.conj h).toMonoidHom) :=
    hinj.comp (MulAut.conj h).injective
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS
    (E := E.map (ψ.comp (MulAut.conj h).toMonoidHom)) ?_ ?_ ?_ ?_
  · rintro _ ⟨t, -, rfl⟩
    exact Subgroup.le_normalizer (hrange ▸ ⟨_, rfl⟩)
  · refine ⟨⟨⟨fun c d => ?_⟩⟩, ?_⟩
    · obtain ⟨_, t, ht, rfl⟩ := c
      obtain ⟨_, u, hu, rfl⟩ := d
      apply Subtype.ext
      change (ψ.comp (MulAut.conj h).toMonoidHom) t * (ψ.comp (MulAut.conj h).toMonoidHom) u =
        (ψ.comp (MulAut.conj h).toMonoidHom) u * (ψ.comp (MulAut.conj h).toMonoidHom) t
      rw [← map_mul, ← map_mul, hEc t ht u hu]
    · rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow, hEp t ht, map_one]
  · rw [Subgroup.card_map_of_injective hinj']
    exact (card_bstar_le hS).trans hEcard
  · rintro _ ⟨t, ht, rfl⟩
    have hfix : β (proj n (GaloisField 2 f) (h * t * h⁻¹)) =
        proj n (GaloisField 2 f) (h * t * h⁻¹) := by
      have e0 : conjAut n (GaloisField 2 f) H (proj n (GaloisField 2 f) t) =
          proj n (GaloisField 2 f) (h * t * h⁻¹) := by
        rw [conjAut_proj, hh]
      have e1 : (conjAut n (GaloisField 2 f) H)⁻¹ (proj n (GaloisField 2 f) (h * t * h⁻¹)) =
          proj n (GaloisField 2 f) t := by
        rw [← e0, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rw [hAσ, hH, MulAut.mul_apply, MulAut.mul_apply, e1, fieldAut_proj, hEσ t ht, e0]
    have h2 := hrel _ _ hfix
    change y * ψ (MulAut.conj h t) = ψ (MulAut.conj h t) * y
    rw [MulAut.conj_apply]
    calc y * ψ (h * t * h⁻¹) = y * (y⁻¹ * ψ (h * t * h⁻¹) * y) := by rw [h2]
      _ = ψ (h * t * h⁻¹) * y := by group

end Setting

end OrdPFieldNsSp

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggOrdPFieldConjPSpNonsplit_holds : GGOrdPFieldConjPSpNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ _ y hyM hyo _ hyI
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPFieldNsSp.exists_conj_mem_centralizer hS hyM hyp hyI

theorem ggOrdPFieldConjAt_PSp : GGOrdPFieldConjAt .PSp :=
  ggOrdPFieldConjAt_PSp_of_nonsplit ggOrdPFieldConjPSpNonsplit_holds

end Family

end CFSG.StandardType
