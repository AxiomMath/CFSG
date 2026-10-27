module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistWeyl
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRank
public import CFSG.LieType.Chevalley.GraphFixedSchreier

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TwE6Lang
  CFSG.LocalAnalysis.StandardType.GGTBE6Cover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (n : ℕ) (hK : Nat.card K = 2 ^ n)

theorem diagonalHom_xm (b : Fin Tag.E6.rank → Kˣ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) (c : K) :
    diagonalHom K n hK b (e6Data_valid.xm K γ c) =
      e6Data_valid.xm K γ ((rootChar b γ : K) * c) := by
  have hker : (e6Isogeny K).ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  have hodd : Nat.Coprime 2 (Nat.card (e6Isogeny K).ker) := by
    obtain ⟨hc, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, hc]
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (Nat.gcd_dvd_left _ _)
  have hx : ∀ t : K, e6Data_valid.xm K γ t ^ 2 = 1 := by
    intro t
    rw [pow_two, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
  apply CFSG.StandardType.OrthRest.eq_of_lift_of_coprime hker hodd
  · apply Subtype.ext
    rw [diagonalHom_isogeny]
    change rootDiagUnit .E6 b *
      (e6Isogeny K (e6Data_valid.xm K γ c) : ModGL .E6 K) * (rootDiagUnit .E6 b)⁻¹ = _
    rw [CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hγ c,
      CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hγ _, rootDiagUnit_conj_pinnedX b hγ]
  · rw [← map_pow, hx, map_one]
  · exact hx _

private theorem sigma_xm_charTwo (θ : K →+* K) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) (c : K) :
    sigma K θ (e6Data_valid.xm K γ c) = e6Data_valid.xm K (rho γ) (θ c) := by
  rw [sigma_xm θ hγ]
  have hs : (twistSign γ : K) = 1 := by
    rcases twistSign_eq_one_or γ with h | h <;> rw [h] <;> simp [CharTwo.neg_eq]
  rw [hs, one_mul]

private def longestSigma (θ : K →+* K) :
    e6Data_valid.minGroup K →* e6Data_valid.minGroup K :=
  (MulAut.conj (weylHom K frameLongest)).toMonoidHom.comp (sigma K θ)

private theorem longestSigma_xm (θ : K →+* K) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) (c : K) :
    longestSigma K θ (e6Data_valid.xm K γ c) = e6Data_valid.xm K (-γ) (θ c) := by
  change weylHom K frameLongest * sigma K θ (e6Data_valid.xm K γ c) *
      (weylHom K frameLongest)⁻¹ = _
  rw [sigma_xm_charTwo K θ hγ c, weylHom_conj_xm K frameLongest (isRoot_rho hγ),
    frameLongest_rho]

private theorem map_rootChar_of_norm (θ : K →+* K) (b : Fin Tag.E6.rank → Kˣ)
    (hb : ∀ i, Units.map θ.toMonoidHom (b i) = (b i)⁻¹) (γ : Fin Tag.E6.rank → ℤ) :
    Units.map θ.toMonoidHom (rootChar b γ) = rootChar b (-γ) := by
  simp only [rootChar, map_prod, map_zpow, hb, Pi.neg_apply, inv_zpow, zpow_neg]

private theorem longestSigma_diagonalHom (θ : K →+* K) (b : Fin Tag.E6.rank → Kˣ)
    (hb : ∀ i, Units.map θ.toMonoidHom (b i) = (b i)⁻¹)
    (x : e6Data_valid.minGroup K) :
    longestSigma K θ (diagonalHom K n hK b x) =
      diagonalHom K n hK b (longestSigma K θ x) := by
  have hroot : ∀ (γ : Fin Tag.E6.rank → ℤ), IsRoot .E6 γ → ∀ c : K,
      longestSigma K θ (diagonalHom K n hK b (e6Data_valid.xm K γ c)) =
        diagonalHom K n hK b (longestSigma K θ (e6Data_valid.xm K γ c)) := by
    intro γ hγ c
    rw [diagonalHom_xm K n hK b hγ,
      longestSigma_xm K θ hγ, longestSigma_xm K θ hγ,
      diagonalHom_xm K n hK b (IsRoot.neg hγ)]
    congr 1
    rw [map_mul]
    have h := congrArg (fun z : Kˣ => (z : K)) (map_rootChar_of_norm K θ b hb γ)
    change θ (rootChar b γ : K) = (rootChar b (-γ) : K) at h
    exact congrArg (· * θ c) h
  have he : (longestSigma K θ).comp (diagonalHom K n hK b).toMonoidHom =
      (diagonalHom K n hK b).toMonoidHom.comp (longestSigma K θ) := by
    apply MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid K)
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact hroot _ (isRoot_single .E6 i) c
    · exact hroot _ (isRoot_neg_single .E6 i) c
  exact DFunLike.congr_fun he x

section Lang

variable (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)

private def langDiagonal (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    MulAut (e6Data_valid.minGroup K) :=
  MulAut.conj (langG K θ.toRingHom l) *
    diagonalHom K n hK (fun i => (b i : Kˣ)) *
      (MulAut.conj (langG K θ.toRingHom l))⁻¹

include hθ hl

private theorem langG_sigma :
    sigma K θ.toRingHom (langG K θ.toRingHom l) =
      langG K θ.toRingHom l * weylHom K frameLongest := by
  have hln : θ.toRingHom l ≠ l := by rw [hl]; exact add_ne_left.mpr one_ne_zero
  have hd : negDelta θ.toRingHom hln = 1 := by
    apply Units.ext
    change -(l - θ.toRingHom l) = (1 : K)
    rw [hl]
    ring
  rw [sigma_langG θ.toRingHom hθ hln, hd, langMM_one]

private theorem langDiagonal_sigma
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    (x : e6Data_valid.minGroup K) :
    sigma K θ.toRingHom (langDiagonal K n hK θ l b x) =
      langDiagonal K n hK θ l b (sigma K θ.toRingHom x) := by
  let g := langG K θ.toRingHom l
  let M := weylHom K frameLongest
  let δ := diagonalHom K n hK (fun i => (b i : Kˣ))
  have hb : ∀ i, Units.map θ.toMonoidHom (b i : Kˣ) = (b i : Kˣ)⁻¹ := by
    intro i
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    exact (b i).2
  have hσg : sigma K θ.toRingHom g = g * M := langG_sigma K θ hθ l hl
  have he := longestSigma_diagonalHom K n hK θ.toRingHom (fun i => (b i : Kˣ)) hb
    (g⁻¹ * x * g)
  change M * sigma K θ.toRingHom (δ (g⁻¹ * x * g)) * M⁻¹ =
    δ (M * sigma K θ.toRingHom (g⁻¹ * x * g) * M⁻¹) at he
  have hin : M * sigma K θ.toRingHom (g⁻¹ * x * g) * M⁻¹ =
      g⁻¹ * sigma K θ.toRingHom x * g := by
    rw [map_mul, map_mul, map_inv, hσg]
    group
  rw [hin] at he
  change sigma K θ.toRingHom (g * δ (g⁻¹ * x * g) * g⁻¹) =
    g * δ (g⁻¹ * sigma K θ.toRingHom x * g) * g⁻¹
  rw [map_mul, map_mul, map_inv, hσg]
  calc _ = g * (M * sigma K θ.toRingHom (δ (g⁻¹ * x * g)) * M⁻¹) * g⁻¹ := by group
    _ = _ := by rw [he]

omit hθ hl in
private theorem langDiagonal_one : langDiagonal K n hK θ l 1 = 1 := by
  unfold langDiagonal
  change MulAut.conj (langG K θ.toRingHom l) * diagonalHom K n hK 1 *
    (MulAut.conj (langG K θ.toRingHom l))⁻¹ = 1
  rw [map_one, mul_one, mul_inv_cancel]

omit hθ hl in
private theorem langDiagonal_mul
    (b c : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    langDiagonal K n hK θ l (b * c) =
      langDiagonal K n hK θ l b * langDiagonal K n hK θ l c := by
  unfold langDiagonal
  change MulAut.conj (langG K θ.toRingHom l) *
      diagonalHom K n hK ((fun i => (b i : Kˣ)) * (fun i => (c i : Kˣ))) *
        (MulAut.conj (langG K θ.toRingHom l))⁻¹ = _
  rw [map_mul]
  group

omit hθ hl in
private theorem langDiagonal_inv
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    langDiagonal K n hK θ l b⁻¹ = (langDiagonal K n hK θ l b)⁻¹ := by
  unfold langDiagonal
  change MulAut.conj (langG K θ.toRingHom l) *
    diagonalHom K n hK (fun i => (b i : Kˣ))⁻¹ *
      (MulAut.conj (langG K θ.toRingHom l))⁻¹ = _
  rw [map_inv]
  group

private theorem langDiagonal_mem_fixed
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    {x : e6Data_valid.minGroup K} (hx : x ∈ fixedGroup K θ.toRingHom) :
    langDiagonal K n hK θ l b x ∈ fixedGroup K θ.toRingHom := by
  rw [mem_fixedGroup, langDiagonal_sigma K n hK θ hθ l hl]
  rw [(mem_fixedGroup θ.toRingHom).mp hx]

theorem langCoroot_mem_fixed (i : Fin Tag.E6.rank) (s : CFSG.LieType.Steinberg.normOne θ) :
    langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
      (langG K θ.toRingHom l)⁻¹ ∈ fixedGroup K θ.toRingHom := by
  have hln : θ.toRingHom l ≠ l := by rw [hl]; exact add_ne_left.mpr one_ne_zero
  have hs : Units.map θ.toMonoidHom (s : Kˣ) = (s : Kˣ) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    exact s.2
  have he : torusPow (s : Kˣ) (Pi.single i 1) = e6Data_valid.hm K i (s : Kˣ) := by
    rw [torusPow, ← torusHom_mulSingle]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [← he, mem_fixedGroup, sigma_langG_conj_torusPow θ.toRingHom hθ hln hs]
  simp only [neg_one_smul, neg_neg]

@[expose] def langCoroot (i : Fin Tag.E6.rank) :
    CFSG.LieType.Steinberg.normOne θ →* fixedGroup K θ.toRingHom :=
  (((MulAut.conj (langG K θ.toRingHom l)).toMonoidHom.comp (e6Data_valid.hHom K i)).comp
    (CFSG.LieType.Steinberg.normOne θ).subtype).codRestrict
      (fixedGroup K θ.toRingHom) (langCoroot_mem_fixed K θ hθ l hl i)

theorem langCoroot_apply (i : Fin Tag.E6.rank) (s : CFSG.LieType.Steinberg.normOne θ) :
    (langCoroot K θ hθ l hl i s : e6Data_valid.minGroup K) =
      langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
        (langG K θ.toRingHom l)⁻¹ := rfl

omit hθ hl in
private def langDiagonalHom :
    (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →*
      MulAut (e6Data_valid.minGroup K) where
  toFun := langDiagonal K n hK θ l
  map_one' := langDiagonal_one K n hK θ l
  map_mul' := langDiagonal_mul K n hK θ l

private theorem map_fixed_langDiagonalHom
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    (fixedGroup K θ.toRingHom).map (langDiagonalHom K n hK θ l b).toMonoidHom =
      fixedGroup K θ.toRingHom := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact langDiagonal_mem_fixed K n hK θ hθ l hl b hx
  · intro x hx
    refine ⟨langDiagonal K n hK θ l b⁻¹ x,
      langDiagonal_mem_fixed K n hK θ hθ l hl b⁻¹ hx, ?_⟩
    change langDiagonal K n hK θ l b (langDiagonal K n hK θ l b⁻¹ x) = x
    rw [langDiagonal_inv K n hK θ l]
    exact MulEquiv.apply_symm_apply _ _

def fixedDiagonalHom :
    (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →*
      MulAut (fixedGroup K θ.toRingHom) :=
  restrictMulAut (langDiagonalHom K n hK θ l) (fixedGroup K θ.toRingHom)
    (map_fixed_langDiagonalHom K n hK θ hθ l hl)

theorem fixedDiagonalHom_apply
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    (x : fixedGroup K θ.toRingHom) :
    (fixedDiagonalHom K n hK θ hθ l hl b x : e6Data_valid.minGroup K) =
      langG K θ.toRingHom l * diagonalHom K n hK (fun j => (b j : Kˣ))
        ((langG K θ.toRingHom l)⁻¹ * x * langG K θ.toRingHom l) *
      (langG K θ.toRingHom l)⁻¹ := by
  exact coe_restrictMulAut_apply (langDiagonalHom K n hK θ l)
    (fixedGroup K θ.toRingHom) (map_fixed_langDiagonalHom K n hK θ hθ l hl) b x

theorem fixedDiagonalHom_langCoroot
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    (i : Fin Tag.E6.rank) (s : CFSG.LieType.Steinberg.normOne θ) :
    fixedDiagonalHom K n hK θ hθ l hl b (langCoroot K θ hθ l hl i s) =
      langCoroot K θ hθ l hl i s := by
  apply Subtype.ext
  change langDiagonal K n hK θ l b
    (langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
      (langG K θ.toRingHom l)⁻¹) = _
  change langG K θ.toRingHom l *
    diagonalHom K n hK (fun j => (b j : Kˣ))
      ((langG K θ.toRingHom l)⁻¹ *
        (langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
          (langG K θ.toRingHom l)⁻¹) * langG K θ.toRingHom l) *
    (langG K θ.toRingHom l)⁻¹ = _
  rw [show (langG K θ.toRingHom l)⁻¹ *
      (langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
        (langG K θ.toRingHom l)⁻¹) * langG K θ.toRingHom l =
      e6Data_valid.hm K i (s : Kˣ) by group,
    diagonalHom_hm K n hK]
  rfl

theorem fixedDiagonalHom_langWeyl_simple
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    (i : Fin Tag.E6.rank) :
    fixedDiagonalHom K n hK θ hθ l hl b
        (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) =
      langCoroot K θ hθ l hl i (b i) *
        langWeylHom K θ.toRingHom hθ hl (simple .E6 i) := by
  apply Subtype.ext
  rw [fixedDiagonalHom_apply]
  simp only [Subgroup.coe_mul, langWeylHom_apply, langCoroot_apply]
  rw [show (langG K θ.toRingHom l)⁻¹ *
      (langG K θ.toRingHom l * weylHom K (simple .E6 i) *
        (langG K θ.toRingHom l)⁻¹) * langG K θ.toRingHom l =
        weylHom K (simple .E6 i) by group, weylHom_simple]
  have hnm : e6Data_valid.nm K i = e6Data_valid.nt K i 1 := by
    rw [e6Data_valid.nt_eq_hm_mul, e6Data_valid.hm_one, one_mul]
  rw [hnm, diagonalHom_nt K n hK, mul_one, e6Data_valid.nt_eq_hm_mul]
  rw [← hnm]
  group

omit hθ hl in
private theorem diagonalHom_eq_conj_hm (i : Fin Tag.E6.rank) (s : Kˣ) :
    diagonalHom K n hK (fun j => s ^ Tag.E6.cartan i j) =
      MulAut.conj (e6Data_valid.hm K i s) := by
  have hker : (e6Isogeny K).ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect (e6Data_valid.minGroup K) := CFSG.LieType.CurtisTits.isPerfect_e6 K
  apply MulEquiv.toMonoidHom_injective
  apply CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, diagonalHom_isogeny]
  apply Subtype.ext
  change rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan i j) *
      (e6Isogeny K x : ModGL .E6 K) *
        (rootDiagUnit .E6 (fun j => s ^ Tag.E6.cartan i j))⁻¹ =
      (e6Isogeny K (e6Data_valid.hm K i s * x * (e6Data_valid.hm K i s)⁻¹) : ModGL .E6 K)
  have hh := CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq (k := K) i s
  rw [map_mul, map_mul, map_inv]
  change _ = (e6Isogeny K (e6Data_valid.hm K i s) : ModGL .E6 K) *
    (e6Isogeny K x : ModGL .E6 K) * (e6Isogeny K (e6Data_valid.hm K i s) : ModGL .E6 K)⁻¹
  rw [hh]

theorem fixedDiagonalHom_eq_conj_langCoroot (i : Fin Tag.E6.rank)
    (s : CFSG.LieType.Steinberg.normOne θ) :
    fixedDiagonalHom K n hK θ hθ l hl (fun j => s ^ Tag.E6.cartan i j) =
      MulAut.conj (langCoroot K θ hθ l hl i s) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [fixedDiagonalHom_apply]
  have hb : (fun j => ((s ^ Tag.E6.cartan i j : CFSG.LieType.Steinberg.normOne θ) : Kˣ)) =
      fun j => (s : Kˣ) ^ Tag.E6.cartan i j := by
    funext j
    exact Subgroup.coe_zpow _ _ _
  rw [hb, diagonalHom_eq_conj_hm K n hK]
  change langG K θ.toRingHom l *
      (e6Data_valid.hm K i (s : Kˣ) *
        ((langG K θ.toRingHom l)⁻¹ * x * langG K θ.toRingHom l) *
          (e6Data_valid.hm K i (s : Kˣ))⁻¹) * (langG K θ.toRingHom l)⁻¹ =
    (langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
      (langG K θ.toRingHom l)⁻¹) * x *
        (langG K θ.toRingHom l * e6Data_valid.hm K i (s : Kˣ) *
          (langG K θ.toRingHom l)⁻¹)⁻¹
  group


end Lang

end CFSG.StandardType.TBE6IndTwist
