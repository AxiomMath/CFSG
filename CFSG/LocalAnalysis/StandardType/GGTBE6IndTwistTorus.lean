module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistDescent
public import CFSG.LocalAnalysis.StandardType.GGTBE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenHomocyclic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcG2Three
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCLiftP
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)

theorem langCoroot_commute (i j : Fin Tag.E6.rank)
    (s t : CFSG.LieType.Steinberg.normOne θ) :
    Commute (langCoroot K θ hθ l hl i s) (langCoroot K θ hθ l hl j t) := by
  have h := (hm_commute (k := K) i j (s : Kˣ) (t : Kˣ)).map
    (MulAut.conj (langG K θ.toRingHom l)).toMonoidHom
  change langCoroot K θ hθ l hl i s * langCoroot K θ hθ l hl j t =
    langCoroot K θ hθ l hl j t * langCoroot K θ hθ l hl i s
  apply Subtype.ext
  exact h.eq

def langTorusHom :
    (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* fixedGroup K θ.toRingHom :=
  MonoidHom.noncommPiCoprod (langCoroot K θ hθ l hl)
    (fun i j _ s t => langCoroot_commute K θ hθ l hl i j s t)

theorem langTorusHom_mulSingle (i : Fin Tag.E6.rank)
    (s : CFSG.LieType.Steinberg.normOne θ) :
    langTorusHom K θ hθ l hl (Pi.mulSingle i s) = langCoroot K θ hθ l hl i s := by
  exact MonoidHom.noncommPiCoprod_mulSingle (langCoroot K θ hθ l hl) i s

theorem range_langTorusHom : (langTorusHom K θ hθ l hl).range =
    ⨆ i, (langCoroot K θ hθ l hl i).range :=
  MonoidHom.noncommPiCoprod_range _

theorem langTorusHom_apply (u : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    (langTorusHom K θ hθ l hl u : e6Data_valid.minGroup K) =
      langG K θ.toRingHom l * minTorus e6Data_valid K (fun i => (u i : Kˣ)) *
        (langG K θ.toRingHom l)⁻¹ := by
  let f : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* e6Data_valid.minGroup K :=
    (fixedGroup K θ.toRingHom).subtype.comp (langTorusHom K θ hθ l hl)
  let g : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* e6Data_valid.minGroup K :=
    (MulAut.conj (langG K θ.toRingHom l)).toMonoidHom.comp
      ((minTorus e6Data_valid K).comp
        (MonoidHom.compLeft (CFSG.LieType.Steinberg.normOne θ).subtype _))
  have hg : ∀ u, g u = langG K θ.toRingHom l *
      minTorus e6Data_valid K (fun i => (u i : Kˣ)) * (langG K θ.toRingHom l)⁻¹ := fun _ => rfl
  have he : f = g := by
    apply MonoidHom.pi_ext
    intro i s
    change (langTorusHom K θ hθ l hl (Pi.mulSingle i s) : e6Data_valid.minGroup K) =
      g (Pi.mulSingle i s)
    rw [hg]
    rw [langTorusHom_mulSingle, langCoroot_apply]
    have hu : (fun j => (((Pi.mulSingle i s : Fin Tag.E6.rank →
        CFSG.LieType.Steinberg.normOne θ) j) : Kˣ)) =
        Pi.mulSingle i (s : Kˣ) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hu, minTorus_mulSingle]
  exact DFunLike.congr_fun he u

theorem langTorusHom_injective : Function.Injective (langTorusHom K θ hθ l hl) := by
  intro u v h
  have he := congrArg (fun x : fixedGroup K θ.toRingHom => (x : e6Data_valid.minGroup K)) h
  rw [langTorusHom_apply, langTorusHom_apply] at he
  have ht := minTorus_injective e6Data_valid K
    ((MulAut.conj (langG K θ.toRingHom l)).injective he)
  funext i
  exact Subtype.ext (congrFun ht i)

private theorem longest_conj_hm (i : Fin Tag.E6.rank) (s : Kˣ) :
    weylHom K frameLongest * e6Data_valid.hm K i s * (weylHom K frameLongest)⁻¹ =
      e6Data_valid.hm K (rhoPerm i) s⁻¹ := by
  have hsingle : torusPow s (Pi.single i 1) = e6Data_valid.hm K i s := by
    rw [torusPow, ← torusHom_mulSingle]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [← hsingle, ← langMM_one, langMM_conj_torusPow]
  have hw : frameW (Pi.single i 1) = -Pi.single (rhoPerm i) 1 := by
    have h := frameW_rho (rho (Pi.single i 1))
    rw [rho_rho, rho_single] at h
    exact h
  rw [hw, torusPow, ← torusHom_mulSingle]
  have ht : (fun j => s ^ (-Pi.single (rhoPerm i) 1 : Fin Tag.E6.rank → ℤ) j) =
      Pi.mulSingle (rhoPerm i) s⁻¹ := by
    funext j
    by_cases hj : j = rhoPerm i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [ht]

private def normTwistTuple : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ) where
  toFun u j := (Units.map θ.toMonoidHom (u j))⁻¹
  map_one' := funext fun j => by simp
  map_mul' u v := funext fun j => by simp [mul_inv, mul_comm]

include hθ hl in
theorem sigma_langConj_minTorus (u : Fin Tag.E6.rank → Kˣ) :
    sigma K θ.toRingHom (langG K θ.toRingHom l * minTorus e6Data_valid K u *
      (langG K θ.toRingHom l)⁻¹) =
    langG K θ.toRingHom l * minTorus e6Data_valid K (fun i => (Units.map θ.toMonoidHom (u i))⁻¹) *
      (langG K θ.toRingHom l)⁻¹ := by
  let f : (Fin Tag.E6.rank → Kˣ) →* e6Data_valid.minGroup K :=
    (sigma K θ.toRingHom).comp ((MulAut.conj (langG K θ.toRingHom l)).toMonoidHom.comp
      (minTorus e6Data_valid K))
  let g : (Fin Tag.E6.rank → Kˣ) →* e6Data_valid.minGroup K :=
    (MulAut.conj (langG K θ.toRingHom l)).toMonoidHom.comp
      ((minTorus e6Data_valid K).comp (normTwistTuple K θ))
  have hf : ∀ u, f u = sigma K θ.toRingHom (langG K θ.toRingHom l *
      minTorus e6Data_valid K u * (langG K θ.toRingHom l)⁻¹) := fun _ => rfl
  have hg : ∀ u, g u = langG K θ.toRingHom l * minTorus e6Data_valid K
      (fun i => (Units.map θ.toMonoidHom (u i))⁻¹) * (langG K θ.toRingHom l)⁻¹ := fun _ => rfl
  have he : f = g := by
    apply MonoidHom.pi_ext
    intro i s
    rw [hf, hg, minTorus_mulSingle]
    have hln : θ.toRingHom l ≠ l := by rw [hl]; exact add_ne_left.mpr one_ne_zero
    have hd : negDelta θ.toRingHom hln = 1 := by
      apply Units.ext
      change -(l - θ.toRingHom l) = (1 : K)
      rw [hl]
      ring
    rw [map_mul, map_mul, map_inv, sigma_langG θ.toRingHom hθ hln, hd, langMM_one,
      sigma_hm θ.toRingHom i s]
    have htuple : (fun j => (Units.map θ.toMonoidHom ((Pi.mulSingle i s : Fin Tag.E6.rank → Kˣ) j))⁻¹) =
        Pi.mulSingle i (Units.map θ.toMonoidHom s)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [htuple, minTorus_mulSingle]
    have hm : Units.map (θ.toRingHom : K →* K) s = Units.map θ.toMonoidHom s := rfl
    rw [hm]
    calc _ = langG K θ.toRingHom l *
        (weylHom K frameLongest * e6Data_valid.hm K (rhoPerm i) (Units.map θ.toMonoidHom s) *
          (weylHom K frameLongest)⁻¹) * (langG K θ.toRingHom l)⁻¹ := by group
      _ = _ := by
        rw [longest_conj_hm, show rhoPerm (rhoPerm i) = i from by
          change TwistTag.E6.perm (TwistTag.E6.perm i) = i
          fin_cases i <;> rfl]
  exact (hf u).symm.trans ((DFunLike.congr_fun he u).trans (hg u))

theorem mem_range_langTorusHom {x : fixedGroup K θ.toRingHom}
    (hx : (langG K θ.toRingHom l)⁻¹ * (x : e6Data_valid.minGroup K) *
      langG K θ.toRingHom l ∈ (minTorus e6Data_valid K).range) :
    x ∈ (langTorusHom K θ hθ l hl).range := by
  obtain ⟨u, hu⟩ := hx
  have hxu : (x : e6Data_valid.minGroup K) = langG K θ.toRingHom l *
      minTorus e6Data_valid K u * (langG K θ.toRingHom l)⁻¹ := by rw [hu]; group
  have hfix := (mem_fixedGroup θ.toRingHom).mp x.2
  rw [hxu, sigma_langConj_minTorus K θ hθ l hl] at hfix
  have ht := minTorus_injective e6Data_valid K
    ((MulAut.conj (langG K θ.toRingHom l)).injective hfix)
  let v : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ := fun i =>
    ⟨u i, by
      have he := inv_eq_iff_eq_inv.mp (congrFun ht i)
      have hc := congrArg (fun z : Kˣ => (z : K)) he
      change θ (u i : K) = ((u i)⁻¹ : Kˣ) at hc
      change θ (u i : K) * (u i : K) = 1
      rw [hc]
      exact congrArg (fun z : Kˣ => (z : K)) (inv_mul_cancel (u i))⟩
  refine ⟨v, Subtype.ext ?_⟩
  rw [langTorusHom_apply, hxu]

theorem fixedDiagonalHom_langTorusHom {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (b u : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    fixedDiagonalHom K n hK θ hθ l hl b (langTorusHom K θ hθ l hl u) =
      langTorusHom K θ hθ l hl u := by
  have he : (fixedDiagonalHom K n hK θ hθ l hl b).toMonoidHom.comp
      (langTorusHom K θ hθ l hl) = langTorusHom K θ hθ l hl := by
    apply MonoidHom.pi_ext
    intro i s
    rw [MonoidHom.comp_apply, langTorusHom_mulSingle, MulEquiv.coe_toMonoidHom]
    exact fixedDiagonalHom_langCoroot K n hK θ hθ l hl b i s
  exact DFunLike.congr_fun he u

theorem langTorusHom_commute (u v : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    Commute (langTorusHom K θ hθ l hl u) (langTorusHom K θ hθ l hl v) := by
  change langTorusHom K θ hθ l hl u * langTorusHom K θ hθ l hl v =
    langTorusHom K θ hθ l hl v * langTorusHom K θ hθ l hl u
  rw [← map_mul, ← map_mul, mul_comm]

theorem weylHom_conj_torusPow_simple (ζ : Kˣ) (i : Fin Tag.E6.rank)
    (v : Fin Tag.E6.rank → ℤ) :
    weylHom K (simple .E6 i) * torusPow ζ v * (weylHom K (simple .E6 i))⁻¹ =
      torusPow ζ (reflect .E6 i v) := by
  rw [weylHom_simple]
  exact nm_conj_torusPow ζ i v

theorem weylHom_conj_torusPow (w : WeylGroup .E6) (ζ : Kˣ)
    (v : Fin Tag.E6.rank → ℤ) :
    weylHom K w * torusPow ζ v * (weylHom K w)⁻¹ = torusPow ζ (w • v) := by
  have hw : w ∈ Subgroup.closure (Set.range (simple .E6)) := by
    rw [(coxeterSystem .E6).subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  suffices h : ∀ v, weylHom K w * torusPow ζ v * (weylHom K w)⁻¹ =
      torusPow ζ (w • v) by exact h v
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro v
      rw [weylHom_conj_torusPow_simple, simple_smul]
  | one => intro v; simp
  | mul x y hx hy ihx ihy =>
      intro v
      rw [map_mul, mul_inv_rev, mul_smul]
      calc _ = weylHom K x *
            (weylHom K y * torusPow ζ v * (weylHom K y)⁻¹) * (weylHom K x)⁻¹ := by group
        _ = _ := by rw [ihy, ihx]
  | inv x hx ih =>
      intro v
      rw [map_inv]
      have he := ih (x⁻¹ • v)
      rw [smul_inv_smul] at he
      rw [← he]
      group

variable {L : Type} [Group L]

@[expose] def langPFrame {p : ℕ} [NeZero p] (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod p) →* fixedGroup K θ.toRingHom :=
  (langTorusHom K θ hθ l hl).comp
    ((MonoidHom.compLeft (zmodPowHom ζ hζ) _).comp (MulEquiv.funMultiplicative _ _).toMonoidHom)

theorem langPFrame_injective {p : ℕ} [NeZero p] (ζ : CFSG.LieType.Steinberg.normOne θ)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (langPFrame K θ hθ l hl ζ hζ) := by
  intro u v h
  change langTorusHom K θ hθ l hl
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd u i))) =
    langTorusHom K θ hθ l hl
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd v i))) at h
  have hv := langTorusHom_injective K θ hθ l hl h
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrFun hv i
  exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ hi)

theorem cover_langPFrame_injective {f p : ℕ} [NeZero p] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3)
    (φ : fixedGroup K θ.toRingHom →* L)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (φ.comp (langPFrame K θ hθ l hl ζ hζ)) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hZ : Nat.card (Subgroup.center (fixedGroup K θ.toRingHom)) ∣ 3 := by
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK
      (fun c => hθq c)).1]
    exact Nat.gcd_dvd_left _ _
  have hk : Nat.card φ.ker ∣ 3 := (Subgroup.card_dvd_of_le hφc).trans hZ
  have hc : Nat.Coprime p (Nat.card φ.ker) :=
    ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right hk
  have hx : langPFrame K θ hθ l hl ζ hζ u ^ p = 1 := by
    rw [← map_pow]
    have hup : u ^ p = 1 := CFSG.RankThree.CentralCover.pow_eq_one_of_zmod u
    rw [hup, map_one]
  have hd : orderOf (langPFrame K θ hθ l hl ζ hζ u) ∣ Nat.card φ.ker :=
    Subgroup.orderOf_dvd_natCard φ.ker hu
  have he : langPFrame K θ hθ l hl ζ hζ u = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hx) hd)
  exact langPFrame_injective K θ hθ l hl ζ hζ hζo (he.trans (map_one _).symm)

theorem cover_langCoroot_injective {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (φ : fixedGroup K θ.toRingHom →* L)
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hφ : ∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
      (fun c => hθq c) x) (i : Fin Tag.E6.rank) :
    Function.Injective (φ.comp (langCoroot K θ hθ l hl i)) := by
  intro s t h
  have he := congrArg (fun x : L => (ψ x : ModGL TwistTag.E6.tag K)) h
  change (ψ (φ (langCoroot K θ hθ l hl i s)) : ModGL TwistTag.E6.tag K) =
    (ψ (φ (langCoroot K θ hθ l hl i t)) : ModGL TwistTag.E6.tag K) at he
  rw [hφ, hφ] at he
  have hcoe : ∀ v : fixedGroup K θ.toRingHom,
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
        (fun c => hθq c) v : ModGL TwistTag.E6.tag K) =
      (e6Isogeny K (v : e6Data_valid.minGroup K) : ModGL .E6 K) := fun _ => rfl
  rw [hcoe, hcoe, langCoroot_apply, langCoroot_apply] at he
  have he' : e6Isogeny K (e6Data_valid.hm K i (s : Kˣ)) =
      e6Isogeny K (e6Data_valid.hm K i (t : Kˣ)) := by
    apply Subtype.ext
    have hg := congrArg (fun x : ModGL .E6 K =>
      (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K)⁻¹ * x *
        (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K)) he
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hg
  have hsd := congrArg (fun x : adjointGroup .E6 K => (x : ModGL .E6 K)) he'
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq] at hsd
  have hu := rootDiagUnit_injective hsd
  obtain ⟨j, hj⟩ := neighbour_E6 i
  have hij : Tag.E6.cartan i j = -1 := by rw [cartan_E6_symm]; exact hj
  have hv := congrFun hu j
  rw [hij, zpow_neg_one, zpow_neg_one] at hv
  exact Subtype.ext (inv_injective hv)

end CFSG.StandardType.TBE6IndTwist
