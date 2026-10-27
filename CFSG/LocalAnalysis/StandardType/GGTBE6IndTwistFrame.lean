module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCFive
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCSeven
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcSplit

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)

theorem langPFrame_apply {p : ℕ} [NeZero p] (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (a : Multiplicative (Fin Tag.E6.rank → ZMod p)) :
    langPFrame K θ hθ l hl ζ hζ a = langTorusHom K θ hθ l hl
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd a i))) := rfl

private theorem isogeny_minTorus_coordHom (u : Fin Tag.E6.rank → Kˣ) :
    (e6Isogeny K (minTorus e6Data_valid K u) : ModGL .E6 K) =
      (torusCoordHom .E6 K u : ModGL .E6 K) := by
  let f : (Fin Tag.E6.rank → Kˣ) →* ModGL .E6 K :=
    ((adjointGroup .E6 K).subtype.comp (e6Isogeny K)).comp (minTorus e6Data_valid K)
  let g : (Fin Tag.E6.rank → Kˣ) →* ModGL .E6 K :=
    (torusGroup .E6 K).subtype.comp (torusCoordHom .E6 K)
  have hf : ∀ u, f u = (e6Isogeny K (minTorus e6Data_valid K u) : ModGL .E6 K) := fun _ => rfl
  have hg : ∀ u, g u = (torusCoordHom .E6 K u : ModGL .E6 K) := fun _ => rfl
  have he : f = g := by
    apply MonoidHom.pi_ext
    intro i s
    rw [hf, hg, minTorus_mulSingle, coe_torusCoordHom_mulSingle]
    have hh := CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq (k := K) i s
    rw [torusElt_eq_rootDiagUnit]
    exact hh
  exact (hf u).symm.trans ((DFunLike.congr_fun he u).trans (hg u))

private theorem isogeny_minTorus_chevTorus {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (a : Multiplicative (Fin Tag.E6.rank → ZMod p)) :
    (e6Isogeny K (minTorus e6Data_valid K
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd a i)))) : ModGL .E6 K) =
      (chevTorus .E6 ζ hζ a : ModGL .E6 K) :=
  isogeny_minTorus_coordHom K (chevTorusExp .E6 ζ hζ a)

theorem isogeny_langPFrame {f p : ℕ} (hf : 1 ≤ f) [NeZero p]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (a : Multiplicative (Fin Tag.E6.rank → ZMod p)) :
    (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
      (fun c => hθq c) (langPFrame K θ hθ l hl ζ hζ a) : ModGL TwistTag.E6.tag K) =
    (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K) *
      (chevTorus .E6 (ζ : Kˣ) (congrArg Subtype.val hζ) a : ModGL .E6 K) *
        (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K)⁻¹ := by
  rw [langPFrame_apply]
  have hcoe : ∀ x : fixedGroup K θ.toRingHom,
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
        (fun c => hθq c) x : ModGL TwistTag.E6.tag K) =
      (e6Isogeny K (x : e6Data_valid.minGroup K) : ModGL .E6 K) := fun _ => rfl
  rw [hcoe, langTorusHom_apply, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have he : (fun i => (zmodPowHom ζ hζ
      (Multiplicative.ofAdd (Multiplicative.toAdd a i)) : Kˣ)) =
      fun i => zmodPowHom (ζ : Kˣ) (congrArg Subtype.val hζ)
        (Multiplicative.ofAdd (Multiplicative.toAdd a i)) := by
    funext i
    exact Subgroup.coe_pow _ _ _
  rw [he, isogeny_minTorus_chevTorus K (ζ : Kˣ) (congrArg Subtype.val hζ) a]

theorem exists_isogeny_langPFrame {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hp3 : p ≠ 3) [NeZero p] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ c = c ^ (2 ^ f)) (ζ : CFSG.LieType.Steinberg.normOne θ)
    (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {y : adjointGroup .E6 K} (hy : y ∈ TableBExc.torusPow .E6 K p) :
    ∃ a : Multiplicative (Fin Tag.E6.rank → ZMod p),
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
        (fun c => hθq c) (langPFrame K θ hθ l hl ζ hζ a) : ModGL TwistTag.E6.tag K) =
      (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K) * (y : ModGL .E6 K) *
        (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K)⁻¹ := by
  have hζ' : (ζ : Kˣ) ^ p = 1 := congrArg Subtype.val hζ
  have hpK : p ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    rw [← hζo]
    exact orderOf_dvd_natCard (ζ : Kˣ)
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  have hr := TableBExc.range_chevTorus_eq_torusPow hζo hζ' hdet
    (TableBExc.card_torusPow_E6 hp hp3 hpK)
  rw [← hr] at hy
  obtain ⟨a, rfl⟩ := hy
  exact ⟨a, isogeny_langPFrame K θ hθ l hl hf hK hθq ζ hζ a⟩

theorem centralizer_langPFrame_le {f p : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p) :
    Subgroup.centralizer ((langPFrame K θ hθ l hl ζ hζ).range :
      Set (fixedGroup K θ.toRingHom)) ≤ (langTorusHom K θ hθ l hl).range := by
  intro x hx
  let g : adjointGroup .E6 K := e6Isogeny K (langG K θ.toRingHom l)
  let z : adjointGroup .E6 K := g⁻¹ * e6Isogeny K (x : e6Data_valid.minGroup K) * g
  have hz : (z : ModGL .E6 K) ∈ torusGroup .E6 K := by
    have hpK : p ∣ Nat.card Kˣ := hζo ▸ orderOf_dvd_natCard (ζ : Kˣ)
    have hfullp := TableBExc.fullp_E6 hp.one_lt
      ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)) (K := K)
    rw [← TableBExc.adjointGroup_inf_centralizer_torusPow_of_ne_two hp hp2 hpK hfullp]
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    let y' : adjointGroup .E6 K :=
      ⟨y, CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hy.1⟩
    have hy' : y' ∈ TableBExc.torusPow .E6 K p := ⟨hy.1, Subtype.ext hy.2⟩
    obtain ⟨a, ha⟩ := exists_isogeny_langPFrame K θ hθ l hl hf hp hp3 hK hθq ζ hζ hζo hy'
    have hc := Subgroup.mem_centralizer_iff.mp hx
      (langPFrame K θ hθ l hl ζ hζ a) ⟨a, rfl⟩
    have hc' := congrArg (fun t : fixedGroup K θ.toRingHom =>
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
        (fun c => hθq c) t : ModGL TwistTag.E6.tag K)) hc
    simp only [map_mul, Subgroup.coe_mul] at hc'
    rw [ha] at hc'
    change (g : ModGL .E6 K) * y * (g : ModGL .E6 K)⁻¹ *
        (e6Isogeny K (x : e6Data_valid.minGroup K) : ModGL .E6 K) =
      (e6Isogeny K (x : e6Data_valid.minGroup K) : ModGL .E6 K) *
        ((g : ModGL .E6 K) * y * (g : ModGL .E6 K)⁻¹) at hc'
    have he := congrArg (fun t : ModGL .E6 K => (g : ModGL .E6 K)⁻¹ * t *
      (g : ModGL .E6 K)) hc'
    change y * (z : ModGL .E6 K) = (z : ModGL .E6 K) * y
    convert he using 1 <;> simp only [z, Subgroup.coe_mul, Subgroup.coe_inv] <;> group
  apply mem_range_langTorusHom K θ hθ l hl
  apply TBE6.mem_minTorus_range_of_isogeny_mem_torus
  simpa only [z, g, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hz

theorem cover_centralizer_langPFrame_le {f p : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {L : Type} [Group L] (φ : fixedGroup K θ.toRingHom →* L) (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom)) :
    Subgroup.centralizer ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range : Set L) ≤
      (φ.comp (langTorusHom K θ hθ l hl)).range := by
  intro x hx
  obtain ⟨x₀, rfl⟩ := hφs x
  have hk : Nat.card φ.ker ∣ 3 := by
    apply (Subgroup.card_dvd_of_le hφc).trans
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK
      (fun c => hθq c)).1]
    exact Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime p (Nat.card φ.ker) :=
    ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right hk
  have hc : x₀ ∈ Subgroup.centralizer ((langPFrame K θ hθ l hl ζ hζ).range :
      Set (fixedGroup K θ.toRingHom)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨a, rfl⟩
    have hy : langPFrame K θ hθ l hl ζ hζ a ^ p = 1 := by
      rw [← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
    have he := Subgroup.mem_centralizer_iff.mp hx (φ (langPFrame K θ hθ l hl ζ hζ a))
      ⟨a, rfl⟩
    have hmap : φ (x₀ * langPFrame K θ hθ l hl ζ hζ a * x₀⁻¹) =
        φ (langPFrame K θ hθ l hl ζ hζ a) := by
      rw [map_mul, map_mul, map_inv, ← he, mul_inv_cancel_right]
    have hconj : (x₀ * langPFrame K θ hθ l hl ζ hζ a * x₀⁻¹) ^ p = 1 := by
      rw [conj_pow, hy, mul_one, mul_inv_cancel]
    have h := CFSG.StandardType.OrthRest.eq_of_lift_of_coprime hφc hcop hmap hconj hy
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨u, hu⟩ := centralizer_langPFrame_le K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo hc
  refine ⟨u, ?_⟩
  rw [MonoidHom.comp_apply, hu]

theorem cover_langTorusHom_torsion {f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {L : Type} [Group L] (φ : fixedGroup K θ.toRingHom →* L)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    {x : L} (hx : x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range) (hxp : x ^ p = 1) :
    x ∈ (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range := by
  obtain ⟨u, hu⟩ := hx
  have hz : langTorusHom K θ hθ l hl u ^ p ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    change (φ.comp (langTorusHom K θ hθ l hl) u) ^ p = 1
    rw [hu, hxp]
  have hZ : Nat.card (Subgroup.center (fixedGroup K θ.toRingHom)) ∣ 3 := by
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK
      (fun c => hθq c)).1]
    exact Nat.gcd_dvd_left _ _
  have hz3 : (langTorusHom K θ hθ l hl u ^ p) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ (hφc hz)).trans hZ)
  have hu3 : (u ^ p) ^ 3 = 1 := by
    apply langTorusHom_injective K θ hθ l hl
    rw [map_pow, map_pow, map_one]
    exact hz3
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)) hp.one_lt
  let v := u ^ (3 * k)
  have hvp : ∀ i, v i ^ p = 1 := by
    intro i
    have h := congrFun hu3 i
    change (u i ^ p) ^ 3 = 1 at h
    change (u i ^ (3 * k)) ^ p = 1
    calc _ = ((u i ^ p) ^ 3) ^ k := by rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [h, one_pow]
  have hprim : IsPrimitiveRoot (ζ : Kˣ) p := hζo ▸ IsPrimitiveRoot.orderOf (ζ : Kˣ)
  have hav : ∀ i, ∃ a : ZMod p, zmodPowHom ζ hζ (Multiplicative.ofAdd a) = v i := by
    intro i
    have hvp' : (v i : Kˣ) ^ p = 1 := by
      exact congrArg (fun z : CFSG.LieType.Steinberg.normOne θ => (z : Kˣ)) (hvp i)
    obtain ⟨j, hj, he⟩ := hprim.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity p (v i : Kˣ)).mpr hvp')
    refine ⟨(j : ZMod p), Subtype.ext ?_⟩
    rw [zmodPowHom_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hj, Subgroup.coe_pow]
    exact he
  choose a ha using hav
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  rw [MonoidHom.comp_apply, langPFrame_apply]
  change φ (langTorusHom K θ hθ l hl
    (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (a i)))) = x
  rw [show
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (a i))) = v from funext ha]
  change φ (langTorusHom K θ hθ l hl (u ^ (3 * k))) = x
  rw [map_pow, map_pow]
  change (φ.comp (langTorusHom K θ hθ l hl) u) ^ (3 * k) = x
  rw [hu]
  exact TableBExc.pow_mul_eq_self_of_mod hk hxp

private theorem torusPow_redMod {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (v : Fin Tag.E6.rank → ℤ) :
    torusPow ζ v = minTorus e6Data_valid K
      (fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (TableBExc.redMod .E6 p v i))) := by
  change minTorus e6Data_valid K (fun i => ζ ^ v i) = _
  congr 1
  funext i
  have hm : (v i - (TableBExc.redMod .E6 p v i).val : ℤ) % p = 0 := by
    apply Int.emod_eq_zero_of_dvd
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [TableBExc.redMod]
  rw [zmodPowHom_apply, ← zpow_natCast]
  have hd : (p : ℤ) ∣ v i - (TableBExc.redMod .E6 p v i).val := Int.dvd_of_emod_eq_zero hm
  obtain ⟨k, hk⟩ := hd
  have he : v i = ((TableBExc.redMod .E6 p v i).val : ℤ) + (p : ℤ) * k := by omega
  have hζz : ζ ^ (p : ℤ) = 1 := by simpa only [zpow_natCast] using hζ
  rw [he, zpow_add, zpow_mul, hζz, one_zpow, mul_one]

theorem langWeylHom_conj_langPFrame {p : ℕ} [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (w : WeylGroup .E6) (a : Fin Tag.E6.rank → ZMod p) :
    langWeylHom K θ.toRingHom hθ hl w * langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd a) *
      (langWeylHom K θ.toRingHom hθ hl w)⁻¹ =
    langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p w a)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, langWeylHom_apply]
  rw [langPFrame_apply, langPFrame_apply, langTorusHom_apply, langTorusHom_apply]
  let u : Fin Tag.E6.rank → Kˣ := fun i => (ζ : Kˣ) ^ (a i).val
  have hu : (fun i => (zmodPowHom ζ hζ (Multiplicative.ofAdd (a i)) : Kˣ)) = u := by
    funext i
    exact Subgroup.coe_pow _ _ _
  simp only [toAdd_ofAdd]
  rw [hu]
  have htor : minTorus e6Data_valid K u = torusPow (ζ : Kˣ) (TableBExc.liftMod .E6 p a) := rfl
  rw [htor]
  calc _ = langG K θ.toRingHom l *
        (weylHom K w * torusPow (ζ : Kˣ) (TableBExc.liftMod .E6 p a) * (weylHom K w)⁻¹) *
          (langG K θ.toRingHom l)⁻¹ := by group
    _ = _ := by
      rw [weylHom_conj_torusPow K, torusPow_redMod K (congrArg Subtype.val hζ)]
      have htup : (fun i => zmodPowHom (ζ : Kˣ) (congrArg Subtype.val hζ)
          (Multiplicative.ofAdd (TableBExc.redMod .E6 p (w • TableBExc.liftMod .E6 p a) i))) =
        fun i => (zmodPowHom ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p w a i)) : Kˣ) := by
        funext i
        exact (Subgroup.coe_pow _ _ _).symm
      rw [htup]

end CFSG.StandardType.TBE6IndTwist
