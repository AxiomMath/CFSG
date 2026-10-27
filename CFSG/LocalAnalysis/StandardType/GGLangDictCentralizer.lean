module

public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraic
public import CFSG.LocalAnalysis.StandardType.GGLangDictChar
public import CFSG.LocalAnalysis.StandardType.GGLangDictTransport
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGLangDetects
public import CFSG.LocalAnalysis.StandardType.GGLangReidx

public section

namespace CFSG.StandardType

section DictCentralizer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem dictCen_conj_psiBar {K : Type*} [Group K] (u : MulAut K) (k : K) :
    u * MulAut.conj k * u⁻¹ = MulAut.conj (u k) := by
  have hux : ∀ y : K, u ((u⁻¹) y) = y := fun y => MulEquiv.apply_symm_apply u y
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [hux]

private theorem dictCen_exists_preimage {M N : Type*} [Group M] [Group N] {ι : M →* N}
    {Γ R : Subgroup N} (hR : R ≤ Γ) (hrange : ι.range = Γ) {r : N} (hr : r ∈ R) :
    ∃ k, ι k = r := by
  have hr' : r ∈ ι.range := by rw [hrange]; exact hR hr
  exact MonoidHom.mem_range.1 hr'

private theorem dictCen_ggLangReidx_right_inv {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm v) = v := by
  subst h
  rfl

theorem ggPsi_mem_centralizer_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {R : Subgroup (ModGL B.τ L)} (hR : R ≤ B.setup.Γ)
    (b' : Bs) :
    (b' : GGAutU t n f) ∈ Subgroup.centralizer (((R.comap B.ι).map (ggPsiBar t n f) : Subgroup (GGAutU t n f)) : Set (GGAutU t n f)) ↔
      R ≤ Subgroup.centralizer {rootDiagUnit B.τ (B.a b')} := by
  set d : ModGL B.τ L := rootDiagUnit B.τ (B.a b') with hd
  constructor
  · intro hb r hr
    obtain ⟨k, hk⟩ := dictCen_exists_preimage (ι := B.ι) hR B.ι_range hr
    have hmem : ggPsiBar t n f k ∈ (R.comap B.ι).map (ggPsiBar t n f) :=
      Subgroup.mem_map.2 ⟨k, by rw [Subgroup.mem_comap, hk]; exact hr, rfl⟩
    have hc : MulAut.conj k * (b' : GGAutU t n f) = (b' : GGAutU t n f) * MulAut.conj k := by
      simpa only [ggPsiBar] using (Subgroup.mem_centralizer_iff.1 hb) _ hmem
    have hfix : (b' : GGAutU t n f) k = k := by
      apply ggPsiBar_injective t n f B.center_bot
      show MulAut.conj ((b' : GGAutU t n f) k) = MulAut.conj k
      rw [← dictCen_conj_psiBar (b' : GGAutU t n f) k, ← hc]
      group
    have hact := B.a_act b' k
    rw [hfix] at hact
    rw [← hk]
    exact CFSG.LieType.Chevalley.conj_eq_iff_mem_centralizer.1 hact.symm
  · intro hRle
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    have hcomm : B.ι k * d = d * B.ι k :=
      Subgroup.mem_centralizer_singleton_iff.1 (hRle (Subgroup.mem_comap.1 hk))
    have hfix : (b' : GGAutU t n f) k = k := by
      apply B.ι_inj
      rw [B.a_act b' k, ← hd, ← hcomm]
      group
    show MulAut.conj k * (b' : GGAutU t n f) = (b' : GGAutU t n f) * MulAut.conj k
    have hconj : (b' : GGAutU t n f) * MulAut.conj k * (b' : GGAutU t n f)⁻¹ = MulAut.conj k := by
      rw [dictCen_conj_psiBar (b' : GGAutU t n f) k, hfix]
    calc MulAut.conj k * (b' : GGAutU t n f)
        = ((b' : GGAutU t n f) * MulAut.conj k * (b' : GGAutU t n f)⁻¹) *
            (b' : GGAutU t n f) := by rw [hconj]
      _ = (b' : GGAutU t n f) * MulAut.conj k := by group

theorem ggPsi_mem_normalizer_of_conj
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {R : Subgroup (ModGL B.τ L)}
    (b' : Bs)
    (hN : R.map (MulAut.conj (rootDiagUnit B.τ (B.a b'))).toMonoidHom = R) :
    (b' : GGAutU t n f) ∈ Subgroup.normalizer (((R.comap B.ι).map (ggPsiBar t n f) : Subgroup (GGAutU t n f)) : Set (GGAutU t n f)) := by
  set d : ModGL B.τ L := rootDiagUnit B.τ (B.a b') with hd
  have hconj_iff : ∀ x : ModGL B.τ L, (MulAut.conj d) x ∈ R ↔ x ∈ R := by
    intro x
    constructor
    · intro hx
      have hx' : (MulAut.conj d) x ∈ Subgroup.map (MulAut.conj d).toMonoidHom R := by
        rw [hN]; exact hx
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.1 hx'
      have hrx' : r = x := (MulAut.conj d).injective hrx
      rwa [hrx'] at hr
    · intro hx
      have hx' : (MulAut.conj d) x ∈ Subgroup.map (MulAut.conj d).toMonoidHom R :=
        Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rwa [hN] at hx'
  have hcomap : Subgroup.map (b' : GGAutU t n f).toMonoidHom (R.comap B.ι) = R.comap B.ι := by
    ext k
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨k₀, hk₀, rfl⟩
      rw [Subgroup.mem_comap] at hk₀ ⊢
      change B.ι ((b' : GGAutU t n f) k₀) ∈ R
      rw [B.a_act b' k₀, ← MulAut.conj_apply]
      exact (hconj_iff (B.ι k₀)).2 hk₀
    · intro hk
      rw [Subgroup.mem_comap] at hk
      refine ⟨(b' : GGAutU t n f)⁻¹ k, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have happ : (b' : GGAutU t n f) ((b' : GGAutU t n f)⁻¹ k) = k :=
          MulEquiv.apply_symm_apply _ _
        have hact := B.a_act b' ((b' : GGAutU t n f)⁻¹ k)
        rw [happ] at hact
        have hcd : (MulAut.conj d) (B.ι ((b' : GGAutU t n f)⁻¹ k)) ∈ R := by
          rw [MulAut.conj_apply, ← hact]
          exact hk
        exact (hconj_iff (B.ι ((b' : GGAutU t n f)⁻¹ k))).1 hcd
      · exact MulEquiv.apply_symm_apply _ _
  have hcomp : (↑(MulAut.conj (b' : GGAutU t n f)) : GGAutU t n f →* GGAutU t n f).comp (ggPsiBar t n f)
      = (ggPsiBar t n f).comp (b' : GGAutU t n f).toMonoidHom := by
    ext k
    simp only [MonoidHom.comp_apply, ggPsiBar]
    simpa [MulAut.conj_apply] using dictCen_conj_psiBar (b' : GGAutU t n f) k
  have hmap_eq : (Subgroup.map (ggPsiBar t n f) (R.comap B.ι)).map
      (↑(MulAut.conj (b' : GGAutU t n f)) : GGAutU t n f →* GGAutU t n f) =
        Subgroup.map (ggPsiBar t n f) (R.comap B.ι) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hcomap]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap_eq

theorem ggPsi_mem_of_rootDiagUnit_mem
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {R : Subgroup (ModGL B.τ L)} (hR : R ≤ B.setup.Γ)
    (b' : Bs) (h : rootDiagUnit B.τ (B.a b') ∈ R) :
    (b' : GGAutU t n f) ∈ (R.comap B.ι).map (ggPsiBar t n f) := by
  obtain ⟨k₀, hk₀⟩ := dictCen_exists_preimage (ι := B.ι) hR B.ι_range h
  have hact : ∀ c, B.ι ((b' : GGAutU t n f) c) = B.ι (k₀ * c * k₀⁻¹) := by
    intro c
    rw [B.a_act b' c, ← hk₀, ← map_inv, ← map_mul, ← map_mul]
  refine Subgroup.mem_map.2 ⟨k₀, ?_, ?_⟩
  · rw [Subgroup.mem_comap, hk₀]
    exact h
  · ext c
    simp only [ggPsiBar, MulAut.conj_apply]
    exact (B.ι_inj (hact c)).symm

theorem ggPsiImage_mulEquiv
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {R : Subgroup (ModGL B.τ L)} (hR : R ≤ B.setup.Γ) :
    Nonempty (↥((R.comap B.ι).map (ggPsiBar t n f)) ≃* ↥R) := by
  have hmapι : (R.comap B.ι).map B.ι = R := by
    apply Subgroup.map_comap_eq_self
    rw [B.ι_range]
    exact hR
  let e1 := Subgroup.equivMapOfInjective (R.comap B.ι) B.ι B.ι_inj
  let e2 := Subgroup.equivMapOfInjective (R.comap B.ι) (ggPsiBar t n f)
    (ggPsiBar_injective t n f B.center_bot)
  let e3 := MulEquiv.subgroupCongr hmapι
  exact ⟨e2.symm.trans (e1.trans e3)⟩

theorem rootDiagUnit_ne_one_of_ne_one
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {b : Bs} (hb : b ≠ 1) :
    rootDiagUnit B.τ (B.a b) ≠ 1 := by
  intro hd
  apply hb
  apply Subtype.ext
  show (b : GGAutU t n f) = 1
  ext c
  have hact := B.a_act b c
  rw [hd] at hact
  have : B.ι ((b : GGAutU t n f) c) = B.ι c := by
    rw [hact]
    simp
  simpa using B.ι_inj this

theorem ggLang_exists_rationalComponent_of_isComponentOf
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (hp2 : p ≠ 2) {b : Bs} (hb : b ≠ 1)
    {Lg : Subgroup (GGAutU t n f)}
    (hL : CFSG.Assembly.IsComponentOf Lg
      ((ggPsiU t n f).range ⊓ Subgroup.centralizer {(b : GGAutU t n f)})) :
    ∃ i : KernelComponent (rootCharHom (B.a b)),
      CFSG.IsQuasisimple ↥(rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i) ∧
        Lg = ((rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i).comap B.ι).map
          (ggPsiBar t n f) := by
  obtain ⟨R, hRcomp, hLg⟩ := (isComponentOf_psi_range_centralizer_iff B b Lg).1 hL
  have hτG2 : B.τ ≠ .G2 := by
    rcases B.tag_five with h | h | h | h <;> rw [h] <;> decide
  have hpL : (p : L) ≠ 0 := ggLang_natCast_ne_zero B hp hp2
  have hT : rootDiagUnit B.τ (B.a b) ∈ B.setup.D.torus := B.a_torus b
  have hap : ∀ i, B.a b i ^ p = 1 := ggLang_a_pow_eq_one B b
  have h1 : rootDiagUnit B.τ (B.a b) ≠ 1 := rootDiagUnit_ne_one_of_ne_one B hb
  obtain ⟨i, hq, hEq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      B.setup hτG2 hp hpL hT hap h1 hRcomp
  exact ⟨i, hq, by rw [hLg, hEq]⟩

theorem ggLang_isComponentOf_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {b : Bs}
    (i : KernelComponent (rootCharHom (B.a b)))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i)) :
    CFSG.Assembly.IsComponentOf
      (((rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i).comap B.ι).map
        (ggPsiBar t n f))
      ((ggPsiU t n f).range ⊓ Subgroup.centralizer {(b : GGAutU t n f)}) := by
  refine (isComponentOf_psi_range_centralizer_iff B b _).2 ⟨_, ?_, rfl⟩
  exact CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent B.setup
    (B.a_torus b) i hq

theorem ggLang_mem_centralizer_rationalComponent_iff
    {L : Type} [Field L] [IsAlgClosed L] [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : LangRat.LangRatCentralizerDetectsP) {b : Bs}
    (i : KernelComponent (rootCharHom (B.a b)))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i))
    (b' : Bs) :
    (b' : GGAutU t n f) ∈ Subgroup.centralizer
        ((((rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i).comap B.ι).map
          (ggPsiBar t n f) : Subgroup (GGAutU t n f)) : Set (GGAutU t n f)) ↔
      ∀ α ∈ ggLangReidx B.rank_eq ⁻¹' rationalRoots B.setup.ρ (rootCharHom (B.a b)) i,
        latChar p (Multiplicative.toAdd (coord b')) α = 0 := by
  set R : Subgroup (ModGL B.τ L) :=
    rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i with hRdef
  have hR : R ≤ B.setup.Γ := (Subgroup.commutator_le_self _).trans inf_le_right
  constructor
  · intro hcent
    have hRle : R ≤ Subgroup.centralizer {rootDiagUnit B.τ (B.a b')} :=
      (ggPsi_mem_centralizer_iff B hR b').1 hcent
    have hpε : (p : ℤ) ∣ ((B.setup.D.q : ℕ) : ℤ) - B.ε := by
      have h := B.p_dvd
      rw [B.q_eq]
      simpa using h
    have hkillT : ∀ γ ∈ rationalRoots B.setup.ρ (rootCharHom (B.a b)) i,
        rootChar (B.a b') γ = 1 :=
      hZ B.τ L B.p₀ p f B.setup B.tag_five hp hp2 (ggLang_natCast_ne_zero B hp hp2) B.q_eq
        (ggLangPerm B.rank_eq π) (ggLang_cartan_perm B) B.ε B.ε_cases
        (fun γ hγ => ggLang_rho_eq_perm B hγ) hpε
        (langSetup_isAlgebraic_of_zmod_two B.setup B.q_eq)
        (B.a b) (B.a b') (B.a_torus b) (B.a_torus b') (ggLang_a_pow_eq_one B b)
        (ggLang_a_pow_eq_one B b') i hq hRle
    intro α hα
    exact (latChar_eq_zero_iff_rootChar_eq_one B hp b' α).2 (hkillT _ hα)
  · intro hkill
    apply (ggPsi_mem_centralizer_iff B hR b').2
    have hsub : rationalRoots B.setup.ρ (rootCharHom (B.a b)) i ⊆ rootCharKernel (B.a b') := by
      intro γ hγ
      refine ⟨CFSG.StandardType.LangRat.isRoot_of_mem_rationalRoots B.setup i hγ, ?_⟩
      have hmem : ggLangReidx B.rank_eq (ggLangReidx B.rank_eq.symm γ) ∈
          rationalRoots B.setup.ρ (rootCharHom (B.a b)) i := by
        rwa [dictCen_ggLangReidx_right_inv B.rank_eq γ]
      have hk := hkill _ hmem
      have hrc := (latChar_eq_zero_iff_rootChar_eq_one B hp b'
        (ggLangReidx B.rank_eq.symm γ)).1 hk
      rwa [dictCen_ggLangReidx_right_inv B.rank_eq γ] at hrc
    have hle : rootSpan B.τ L (rationalRoots B.setup.ρ (rootCharHom (B.a b)) i) ≤
        Subgroup.centralizer {rootDiagUnit B.τ (B.a b')} :=
      CFSG.LieType.Chevalley.rootSpan_le_centralizer (B.a b') hsub
    have hspan : rationalSpan B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i ≤
        Subgroup.centralizer {rootDiagUnit B.τ (B.a b')} :=
      inf_le_left.trans hle
    exact (Subgroup.commutator_le_self _).trans hspan

end DictCentralizer

end CFSG.StandardType
