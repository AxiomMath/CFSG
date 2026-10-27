module

public import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TwE6Lang


variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem nm_sq (i : Fin Tag.E6.rank) : e6Data_valid.nm K i ^ 2 = 1 := by
  rw [e6Data_valid.nm_sq K i]
  have h1 : (-1 : Kˣ) = 1 := Units.ext (CharTwo.neg_eq (1 : K))
  rw [h1, e6Data_valid.hm_one]

theorem nm_isLiftable :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6)).IsLiftable
      (e6Data_valid.nm K) := by
  intro i j
  by_cases hij : i = j
  · subst j
    have hm : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) i i = 1 := by
      simp only [CFSG.LieType.RootSystem.coxeterMatrix,
        TauCeti.coxeterMatrixOfCartanMatrix_apply, Tag.cartan_self]
      norm_num [TauCeti.coxeterOrder_four]
    rw [hm, pow_one, ← pow_two, nm_sq K i]
  by_cases h0 : Tag.E6.cartan i j = 0
  · have h0' : Tag.E6.cartan j i = 0 :=
      (isFiniteType_cartan .E6).apply_eq_zero_iff.mp h0
    have hm : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) i j = 2 := by
      simp only [CFSG.LieType.RootSystem.coxeterMatrix,
        TauCeti.coxeterMatrixOfCartanMatrix_apply, h0, h0', zero_mul]
      exact TauCeti.coxeterOrder_zero
    rw [hm, (show Commute (e6Data_valid.nm K i) (e6Data_valid.nm K j) from
      e6Data_valid.nm_comm K hij h0).mul_pow, nm_sq, nm_sq, one_mul]
  · have hc : Tag.E6.cartan i j * Tag.E6.cartan j i = 1 :=
      e6Data_valid.cartan_mul_cartan hij h0
    have hm : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) i j = 3 := by
      simp only [CFSG.LieType.RootSystem.coxeterMatrix,
        TauCeti.coxeterMatrixOfCartanMatrix_apply, hc]
      exact TauCeti.coxeterOrder_one
    rw [hm]
    have hi := nm_sq K i
    have hj := nm_sq K j
    have hbraid := e6Data_valid.nm_braid K hij h0
    calc (e6Data_valid.nm K i * e6Data_valid.nm K j) ^ 3
        = (e6Data_valid.nm K i * e6Data_valid.nm K j * e6Data_valid.nm K i) *
          (e6Data_valid.nm K j * e6Data_valid.nm K i * e6Data_valid.nm K j) := by
          rw [pow_succ, pow_two]
          group
      _ = (e6Data_valid.nm K j * e6Data_valid.nm K i * e6Data_valid.nm K j) *
          (e6Data_valid.nm K j * e6Data_valid.nm K i * e6Data_valid.nm K j) := by rw [hbraid]
      _ = 1 := by
        have hi' : e6Data_valid.nm K i * e6Data_valid.nm K i = 1 := by simpa [pow_two] using hi
        have hj' : e6Data_valid.nm K j * e6Data_valid.nm K j = 1 := by simpa [pow_two] using hj
        calc _ = e6Data_valid.nm K j * e6Data_valid.nm K i *
            (e6Data_valid.nm K j * e6Data_valid.nm K j) * e6Data_valid.nm K i *
              e6Data_valid.nm K j := by group
          _ = 1 := by
            rw [hj']
            calc e6Data_valid.nm K j * e6Data_valid.nm K i * 1 * e6Data_valid.nm K i *
                e6Data_valid.nm K j = e6Data_valid.nm K j *
                  (e6Data_valid.nm K i * e6Data_valid.nm K i) * e6Data_valid.nm K j := by group
              _ = 1 := by rw [hi', mul_one, hj']

def weylHom : WeylGroup .E6 →* e6Data_valid.minGroup K :=
  (coxeterSystem .E6).lift ⟨e6Data_valid.nm K, nm_isLiftable K⟩

@[simp] theorem weylHom_simple (i : Fin Tag.E6.rank) :
    weylHom K (simple .E6 i) = e6Data_valid.nm K i :=
  (coxeterSystem .E6).lift_apply_simple (nm_isLiftable K) i

theorem weylHom_isogeny (w : WeylGroup .E6) :
    (e6Isogeny K (weylHom K w) : ModGL .E6 K) = canonicalRep (coxeterSystem .E6) K w := by
  let f : WeylGroup .E6 →* ModGL .E6 K :=
    (adjointGroup .E6 K).subtype.comp ((e6Isogeny K).comp (weylHom K))
  let g : WeylGroup .E6 →* ModGL .E6 K :=
    MonoidHom.mk' (canonicalRep (coxeterSystem .E6) K)
      (fun a b => CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo a b)
  have he : f = g := by
    apply (coxeterSystem .E6).ext_simple
    intro i
    change (e6Isogeny K (weylHom K (simple .E6 i)) : ModGL .E6 K) =
      canonicalRep (coxeterSystem .E6) K (simple .E6 i)
    rw [weylHom_simple, canonicalRep_simple]
    rw [← show e6Data_valid.nt K i 1 = e6Data_valid.nm K i by
      rw [e6Data_valid.nt_eq_hm_mul, e6Data_valid.hm_one, one_mul]]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_nt_eq i 1
  exact DFunLike.congr_fun he w

theorem sigma_weylHom (θ : K →+* K) (w : WeylGroup .E6) :
    sigma K θ (weylHom K w) = weylHom K (weylTwist TwistTag.E6 w) := by
  have he : (sigma K θ).comp (weylHom K) =
      (weylHom K).comp (weylTwist TwistTag.E6).toMonoidHom := by
    apply (coxeterSystem .E6).ext_simple
    intro i
    change sigma K θ (weylHom K (simple .E6 i)) =
      weylHom K (weylTwist TwistTag.E6 (simple .E6 i))
    have hs := weylTwist_simple TwistTag.E6 i
    change weylTwist TwistTag.E6 (simple .E6 i) = simple .E6 (rhoPerm i) at hs
    rw [weylHom_simple, hs, weylHom_simple, sigma_nm]
  exact DFunLike.congr_fun he w

theorem weylHom_conj_xm (w : WeylGroup .E6) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) (c : K) :
    weylHom K w * e6Data_valid.xm K γ c * (weylHom K w)⁻¹ =
      e6Data_valid.xm K (w • γ) c := by
  have hw : w ∈ Subgroup.closure (Set.range (simple .E6)) := by
    rw [(coxeterSystem .E6).subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  suffices h : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ → ∀ c : K,
      weylHom K w * e6Data_valid.xm K γ c * (weylHom K w)⁻¹ =
        e6Data_valid.xm K (w • γ) c by exact h γ hγ c
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro γ hγ c
      obtain ⟨ε, hε, he⟩ := e6Data_valid.nm_conj_xm K hγ i
      have hε1 : ε = 1 := by
        rcases hε with h | h
        · exact h
        · rw [h, CharTwo.neg_eq]
      rw [weylHom_simple, he, hε1, one_mul, simple_smul]
  | one =>
      intro γ hγ c
      simp
  | mul x y hx hy ihx ihy =>
      intro γ hγ c
      rw [map_mul, mul_inv_rev, mul_smul]
      calc _ = weylHom K x *
          (weylHom K y * e6Data_valid.xm K γ c * (weylHom K y)⁻¹) *
            (weylHom K x)⁻¹ := by group
        _ = _ := by rw [ihy γ hγ c, ihx _ (IsRoot.smul hγ y) c]
  | inv x hx ih =>
      intro γ hγ c
      rw [map_inv]
      have he := ih (x⁻¹ • γ) (IsRoot.smul hγ x⁻¹) c
      rw [← mul_smul, mul_inv_cancel, one_smul] at he
      rw [← he]
      group

private def foldedWeyl (i : Fin Tag.F4.rank) : WeylGroup .E6 :=
  ![simple .E6 (nd 1), simple .E6 (nd 3),
    simple .E6 (nd 2) * simple .E6 (nd 4),
    simple .E6 (nd 0) * simple .E6 (nd 5)] i

private theorem weylHom_foldedWeyl (i : Fin Tag.F4.rank) :
    weylHom K (foldedWeyl i) = nHatE K i := by
  fin_cases i
  · exact weylHom_simple K (nd 1)
  · exact weylHom_simple K (nd 3)
  · change weylHom K (simple .E6 (nd 2) * simple .E6 (nd 4)) = _
    rw [map_mul, weylHom_simple, weylHom_simple]
    rfl
  · change weylHom K (simple .E6 (nd 0) * simple .E6 (nd 5)) = _
    rw [map_mul, weylHom_simple, weylHom_simple]
    rfl

private def foldedWord (ω : List (Fin Tag.F4.rank)) : WeylGroup .E6 :=
  (ω.map foldedWeyl).prod

private theorem weylHom_foldedWord (ω : List (Fin Tag.F4.rank)) :
    weylHom K (foldedWord ω) = nWord K ω := by
  induction ω with
  | nil => simp [foldedWord, nWord]
  | cons i ω ih =>
      rw [foldedWord, List.map_cons, List.prod_cons, map_mul, weylHom_foldedWeyl,
        nWord_cons]
      exact congrArg (nHatE K i * ·) ih

private theorem foldedWeyl_smul (i : Fin Tag.F4.rank) (v : Fin Tag.E6.rank → ℤ) :
    foldedWeyl i • v = twReflectHom i v := by
  fin_cases i
  · exact simple_smul (τ := .E6) (nd 1) v
  · exact simple_smul (τ := .E6) (nd 3) v
  · change (simple .E6 (nd 2) * simple .E6 (nd 4)) • v = _
    rw [mul_smul, simple_smul, simple_smul]
    rfl
  · change (simple .E6 (nd 0) * simple .E6 (nd 5)) • v = _
    rw [mul_smul, simple_smul, simple_smul]
    rfl

private theorem foldedWord_smul (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.E6.rank → ℤ) :
    foldedWord ω • v = wAct ω v := by
  induction ω with
  | nil => simp [foldedWord, wAct]
  | cons i ω ih =>
      rw [foldedWord, List.map_cons, List.prod_cons, mul_smul, foldedWeyl_smul]
      change twReflectHom i (foldedWord ω • v) = twReflectHom i (wAct ω v)
      rw [ih]

private def frameReflection (j : Fin 4) : WeylGroup .E6 :=
  foldedWord (frameWord j) * simple .E6 (nd 1) * (foldedWord (frameWord j))⁻¹

private theorem foldedWord_inv_smul (ω : List (Fin Tag.F4.rank))
    (v : Fin Tag.E6.rank → ℤ) : (foldedWord ω)⁻¹ • v = wActInv ω v := by
  induction ω generalizing v with
  | nil => simp [foldedWord, wActInv]
  | cons i ω ih =>
      have hi : (foldedWeyl i)⁻¹ • v = twReflectHom i v := by
        rw [inv_smul_eq_iff, foldedWeyl_smul, twReflectHom_twReflectHom]
      rw [foldedWord, List.map_cons, List.prod_cons, mul_inv_rev, mul_smul, hi]
      exact ih _

private theorem frameReflection_smul (j : Fin 4) (v : Fin Tag.E6.rank → ℤ) :
    frameReflection j • v = frameAct j v := by
  rw [frameReflection, mul_smul, mul_smul, foldedWord_inv_smul, simple_smul,
    foldedWord_smul]
  rfl

def frameLongest : WeylGroup .E6 :=
  frameReflection 0 * frameReflection 1 * frameReflection 2 * frameReflection 3

theorem frameLongest_smul (v : Fin Tag.E6.rank → ℤ) :
    frameLongest • v = frameW v := by
  simp only [frameLongest, mul_smul, frameReflection_smul]
  rfl

theorem frameLongest_rho (v : Fin Tag.E6.rank → ℤ) :
    frameLongest • rho v = -v := by
  rw [frameLongest_smul]
  exact frameW_rho v

theorem langMM_one : langMM K 1 = weylHom K frameLongest := by
  have hj : ∀ j : Fin 4, frameM K 1 j = weylHom K (frameReflection j) := by
    intro j
    rw [frameM, langM, e6Data_valid.hm_one, mul_one, frameReflection,
      map_mul, map_mul, map_inv, weylHom_simple, weylHom_foldedWord]
  rw [langMM, frameLongest, map_mul, map_mul, map_mul, ← hj 0, ← hj 1, ← hj 2, ← hj 3]

private def graphWeyl : WeylGroup .E6 →* WeylGroup .E6 :=
  (weylTwist TwistTag.E6).toMonoidHom

private theorem frameLongest_conj_weylTwist (w : WeylGroup .E6) :
    frameLongest * graphWeyl w * frameLongest⁻¹ = w := by
  have hn : ∀ v : Fin Tag.E6.rank → ℤ, frameLongest • v = -rho v := by
    intro v
    simpa only [rho_rho] using frameLongest_rho (rho v)
  have hinv : ∀ v : Fin Tag.E6.rank → ℤ, frameLongest⁻¹ • v = -rho v := by
    intro v
    rw [inv_smul_eq_iff, smul_neg, hn, rho_rho, neg_neg]
  have hp : ∀ v : Fin Tag.E6.rank → ℤ, permLattice TwistTag.E6.perm v = rho v :=
    fun _ => rfl
  have hps : ∀ v : Fin Tag.E6.rank → ℤ, permLattice TwistTag.E6.perm.symm v = rho v :=
    fun v => by
      rw [show TwistTag.E6.perm.symm = TwistTag.E6.perm from by decide]
      exact hp v
  apply CFSG.LieType.Chevalley.ext_single
  intro i
  have ht := weylTwist_smul TwistTag.E6 w (-rho (Pi.single i 1))
  change graphWeyl w • (-rho (Pi.single i 1)) = _ at ht
  have ht' : graphWeyl w • (-rho (Pi.single i 1)) =
      rho (w • rho (-rho (Pi.single i 1))) := by
    calc _ = _ := ht
      _ = _ := by
        exact (hp _).trans (congrArg (fun v : Fin Tag.E6.rank → ℤ => rho (w • v))
          (hps _))
  rw [mul_smul, mul_smul, hinv, ht', hn]
  have hneg : ∀ v : Fin Tag.E6.rank → ℤ, rho (-v) = -rho v := fun _ => rfl
  simp only [hneg, rho_rho, smul_neg, neg_neg]

theorem langConj_weylHom_mem_fixedGroup (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    {l : K} (hl : θ l = l + 1) (w : WeylGroup .E6) :
    langG K θ l * weylHom K w * (langG K θ l)⁻¹ ∈ fixedGroup K θ := by
  have hln : θ l ≠ l := by rw [hl]; exact add_ne_left.mpr one_ne_zero
  have hd : negDelta θ hln = 1 := by
    apply Units.ext
    change -(l - θ l) = (1 : K)
    rw [hl]
    ring
  rw [mem_fixedGroup, map_mul, map_mul, map_inv, sigma_langG θ hθ hln,
    hd, langMM_one, sigma_weylHom]
  calc _ = langG K θ l *
        (weylHom K frameLongest * weylHom K (weylTwist TwistTag.E6 w) *
          (weylHom K frameLongest)⁻¹) * (langG K θ l)⁻¹ := by group
    _ = _ := by
      have he := congrArg (weylHom K) (frameLongest_conj_weylTwist w)
      simp only [map_mul, map_inv] at he
      change weylHom K frameLongest * weylHom K (weylTwist TwistTag.E6 w) *
        (weylHom K frameLongest)⁻¹ = weylHom K w at he
      rw [he]

def langWeylHom (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c) {l : K}
    (hl : θ l = l + 1) : WeylGroup .E6 →* fixedGroup K θ :=
  ((MulAut.conj (langG K θ l)).toMonoidHom.comp (weylHom K)).codRestrict
    (fixedGroup K θ) (langConj_weylHom_mem_fixedGroup K θ hθ hl)

theorem langWeylHom_apply (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c) {l : K}
    (hl : θ l = l + 1) (w : WeylGroup .E6) :
    (langWeylHom K θ hθ hl w : e6Data_valid.minGroup K) =
      langG K θ l * weylHom K w * (langG K θ l)⁻¹ := by
  exact rfl

end CFSG.StandardType.TBE6IndTwist
