module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistFrame

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc


variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)

theorem normalizer_langPFrame {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {x : fixedGroup K θ.toRingHom}
    (hx : x ∈ Subgroup.normalizer ((langPFrame K θ hθ l hl ζ hζ).range :
      Set (fixedGroup K θ.toRingHom))) :
    ∃ w : WeylGroup .E6, ∀ a : Fin Tag.E6.rank → ZMod p,
      x * langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd a) * x⁻¹ =
        langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p w a)) := by
  let g : adjointGroup .E6 K := e6Isogeny K (langG K θ.toRingHom l)
  let z : adjointGroup .E6 K := g⁻¹ * e6Isogeny K (x : e6Data_valid.minGroup K) * g
  have hqcoe : ∀ v : fixedGroup K θ.toRingHom,
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq v : ModGL TwistTag.E6.tag K) =
      (e6Isogeny K (v : e6Data_valid.minGroup K) : ModGL .E6 K) := fun _ => rfl
  have hζ' : (ζ : Kˣ) ^ p = 1 := congrArg Subtype.val hζ
  have hpK : p ∣ Nat.card K - 1 := by
    rw [← Nat.card_units, ← hζo]
    exact orderOf_dvd_natCard (ζ : Kˣ)
  have hdet := isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  have hr := range_chevTorus_eq_torusPow hζo hζ' hdet (card_torusPow_E6 hp hp3 hpK)
  have hnorm : ∀ y : adjointGroup .E6 K, y ∈ torusPow .E6 K p →
      z * y * z⁻¹ ∈ torusPow .E6 K p := by
    intro y hy
    rw [← hr] at hy
    obtain ⟨a, rfl⟩ := hy
    have hm := (Subgroup.mem_normalizer_iff.mp hx
      (langPFrame K θ hθ l hl ζ hζ a)).mp ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := hm
    have he := congrArg (fun v : fixedGroup K θ.toRingHom =>
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
        (fun c => hθq c) v : ModGL TwistTag.E6.tag K)) ha'
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at he
    rw [isogeny_langPFrame K θ hθ l hl hf hK hθq, isogeny_langPFrame K θ hθ l hl hf hK hθq] at he
    rw [hqcoe] at he
    have he' := congrArg (fun v : ModGL .E6 K => (g : ModGL .E6 K)⁻¹ * v *
      (g : ModGL .E6 K)) he
    have hzy : z * chevTorus .E6 (ζ : Kˣ) hζ' a * z⁻¹ =
        chevTorus .E6 (ζ : Kˣ) hζ' a' := by
      apply Subtype.ext
      convert he'.symm using 1 <;> simp only [z, g, Subgroup.coe_mul, Subgroup.coe_inv] <;> group
    rw [hzy, ← hr]
    exact ⟨a', rfl⟩
  have hnorm' : z ∈ Subgroup.normalizer ((torusPow .E6 K p : Subgroup (adjointGroup .E6 K)) : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact hnorm y hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective]
  obtain ⟨u, hu, hzu⟩ := ExcWeylGen.exists_mem_closure_reflections_of_normalizes
    (ζ : Kˣ) hζ' hr (Subgroup.mem_normalizer_iff.mp hnorm')
  have hu' : u ∈ (ExcWeylOuter.torusMulAut .E6 p).range := by
    rw [ExcWeylOuter.range_torusMulAut cartan_E6_symm]
    exact hu
  obtain ⟨w, rfl⟩ := hu'
  refine ⟨w, ?_⟩
  intro a
  have he := hzu (Multiplicative.ofAdd a)
  have he' := congrArg (fun y : adjointGroup .E6 K => g * y * g⁻¹) he
  have hqeq : CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom (fun c => hθq c)
      (x * langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd a) * x⁻¹) =
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom (fun c => hθq c)
      (langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd (torusAct .E6 p w a))) := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [isogeny_langPFrame K θ hθ l hl hf hK hθq, isogeny_langPFrame K θ hθ l hl hf hK hθq]
    rw [hqcoe]
    have he'' := congrArg (fun y : adjointGroup .E6 K => (y : ModGL .E6 K)) he'
    simp only [ExcWeylOuter.torusMulAut_apply] at he''
    simp only [z, g, Subgroup.coe_mul, Subgroup.coe_inv] at he''
    have hζsame : (chevTorus .E6 (ζ : Kˣ) hζ').toFun =
      (chevTorus .E6 (ζ : Kˣ) (congrArg Subtype.val hζ)).toFun := rfl
    have hcSame : (chevTorus .E6 (ζ : Kˣ) (congrArg Subtype.val hζ) (Multiplicative.ofAdd a) :
        ModGL .E6 K) = (chevTorus .E6 (ζ : Kˣ) hζ' (Multiplicative.ofAdd a) : ModGL .E6 K) := rfl
    rw [hcSame]
    have hgg : g * z * g⁻¹ = e6Isogeny K (x : e6Data_valid.minGroup K) := by
      dsimp only [z]
      group
    have he0 : e6Isogeny K (x : e6Data_valid.minGroup K) *
        (g * chevTorus .E6 (ζ : Kˣ) hζ' (Multiplicative.ofAdd a) * g⁻¹) *
          (e6Isogeny K (x : e6Data_valid.minGroup K))⁻¹ =
      g * chevTorus .E6 (ζ : Kˣ) hζ' (Multiplicative.ofAdd (torusAct .E6 p w a)) * g⁻¹ := by
      rw [← hgg]
      calc _ = g * (z * chevTorus .E6 (ζ : Kˣ) hζ' (Multiplicative.ofAdd a) * z⁻¹) * g⁻¹ := by group
        _ = _ := by rw [he, ExcWeylOuter.torusMulAut_apply]
    have he0val := congrArg (fun y : adjointGroup .E6 K => (y : ModGL .E6 K)) he0
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at he0val
    exact he0val
  have hc : Nat.Coprime p (Nat.card (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK
      θ.toRingHom (fun c => hθq c)).ker) := by
    rw [CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq]
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK
      (fun c => hθq c)).1]
    exact ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right
      (Nat.gcd_dvd_left _ _)
  have hk : (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom
      (fun c => hθq c)).ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom (fun c => hθq c)).le
  apply CFSG.StandardType.OrthRest.eq_of_lift_of_coprime hk hc hqeq
  · rw [conj_pow, ← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one,
      mul_one, mul_inv_cancel]
  · rw [← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]

theorem cover_normalizer_langPFrame {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {L : Type} [Group L] (φ : fixedGroup K θ.toRingHom →* L) (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    {x : L} (hx : x ∈ Subgroup.normalizer ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range : Set L)) :
    ∃ w : WeylGroup .E6, ∀ a : Fin Tag.E6.rank → ZMod p,
      x * φ (langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd a)) * x⁻¹ =
        φ (langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd (torusAct .E6 p w a))) := by
  obtain ⟨x₀, rfl⟩ := hφs x
  have hk : Nat.card φ.ker ∣ 3 := by
    apply (Subgroup.card_dvd_of_le hφc).trans
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK hθq).1]
    exact Nat.gcd_dvd_left _ _
  have hc : Nat.Coprime p (Nat.card φ.ker) :=
    ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right hk
  have hn : x₀ ∈ Subgroup.normalizer ((langPFrame K θ hθ l hl ζ hζ).range :
      Set (fixedGroup K θ.toRingHom)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, ⟨a, rfl⟩, rfl⟩
      have he := (Subgroup.mem_normalizer_iff.mp hx
        (φ (langPFrame K θ hθ l hl ζ hζ a))).mp ⟨a, rfl⟩
      obtain ⟨a', ha'⟩ := he
      have hmap : φ (x₀ * langPFrame K θ hθ l hl ζ hζ a * x₀⁻¹) =
          φ (langPFrame K θ hθ l hl ζ hζ a') := by
        rw [map_mul, map_mul, map_inv]
        exact ha'.symm
      have heq := CFSG.StandardType.OrthRest.eq_of_lift_of_coprime hφc hc hmap
        (by rw [conj_pow, ← map_pow, pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel])
        (by rw [← map_pow, pow_eq_one_of_zmod, map_one])
      change x₀ * langPFrame K θ hθ l hl ζ hζ a * x₀⁻¹ ∈ (langPFrame K θ hθ l hl ζ hζ).range
      rw [heq]
      exact ⟨a', rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj x₀).injective]
  obtain ⟨w, hw⟩ := normalizer_langPFrame K θ hθ l hl hf hK hθq hp hp3 ζ hζ hζo hn
  refine ⟨w, fun a => ?_⟩
  have he := congrArg φ (hw a)
  simpa only [map_mul, map_inv] using he

theorem cover_marked_langPFrame {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    {L : Type} [Group L] (φ : fixedGroup K θ.toRingHom →* L) (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom)) :
    ∃ hn : ∀ i : Fin Tag.E6.rank, φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) ∈
      Subgroup.normalizer ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range : Set L),
      ∃ eW : WeylGroup .E6 ≃* ↥(ggAutomizer (⊤ : Subgroup L)
        (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range),
        ∀ i, (eW (simple .E6 i) : MulAut ↥(φ.comp (langPFrame K θ hθ l hl ζ hζ)).range) =
          ggConjAut (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range (hn i) := by
  let : Fact p.Prime := ⟨hp⟩
  have hζo' : orderOf ζ = p := by
    rw [← Subgroup.orderOf_coe ζ]
    exact hζo
  have hι := cover_langPFrame_injective K θ hθ l hl hK hθq hp hp3 φ hφc ζ hζ hζo'
  obtain ⟨hn, -, eW, heW⟩ := exists_markedWeyl_ggAutomizer (hp.odd_of_ne_two hp2)
    (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range (φ.comp (langPFrame K θ hθ l hl ζ hζ)) hι rfl
    (fun i => φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)))
    (fun i a => by
      simpa only [MonoidHom.comp_apply, map_mul, map_inv] using
        congrArg φ (langWeylHom_conj_langPFrame K θ hθ l hl ζ hζ (simple .E6 i) a))
    (fun x hx => cover_normalizer_langPFrame K θ hθ l hl hf hK hθq hp hp3 ζ hζ hζo φ hφs hφc hx)
  exact ⟨hn, eW, heW⟩

end CFSG.StandardType.TBE6IndTwist
