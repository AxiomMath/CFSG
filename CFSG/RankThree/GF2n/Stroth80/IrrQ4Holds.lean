module

public import CFSG.RankThree.GF2n.Stroth80.Sec717PairingCore
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.GroupTheory.AutPrimitiveDivisor
public import CFSG.RankThree.GF2n.Stroth80.IrrQ4Torus

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

theorem sec717_rho_one {H X : Type} [Group H] [Group X] (ρ : H → MulAut X)
    (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k) : ρ 1 = 1 := by
  have h : ρ 1 = ρ 1 * ρ 1 := by simpa using hmul 1 1
  have h1 : ρ 1 * 1 = ρ 1 * ρ 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h1).symm

theorem sec717_rho_eq_of_phi_eq {H X M : Type} [Group H] [Group X] [Group M]
    (φ : H →* M) (ρ : H → MulAut X) (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k)
    (hker : ∀ h : H, φ h = 1 → ρ h = 1) {h k : H} (hφ : φ h = φ k) : ρ h = ρ k := by
  have h1 : φ (h * k⁻¹) = 1 := by rw [map_mul, map_inv, hφ, mul_inv_cancel]
  have h2 : ρ h * ρ k⁻¹ = 1 := by
    have := hker _ h1
    rwa [hmul] at this
  have h3 : ρ k * ρ k⁻¹ = 1 := by
    have := hmul k k⁻¹
    rw [mul_inv_cancel, sec717_rho_one ρ hmul] at this
    exact this.symm
  exact mul_right_cancel (by rw [h2, h3])

theorem sec717_rho_pow {H X : Type} [Group H] [Group X] (ρ : H → MulAut X)
    (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k) (h : H) (n : ℕ) :
    ρ (h ^ n) = (ρ h) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact sec717_rho_one ρ hmul
  | succ n ih => rw [pow_succ, pow_succ, hmul, ih]

theorem sec717_exp_two {H X : Type} [Group H] [CommGroup X] [Finite X] (n : ℕ) (ρ : H → MulAut X)
    (hirr : ∀ S : Subgroup X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hcard : Nat.card X = 2 ^ n) (hn : n ≠ 0) : ∀ x : X, x ^ 2 = 1 := by
  let S : Subgroup X := (powMonoidHom 2 : X →* X).range
  have hSinv : ∀ h : H, ∀ x ∈ S, ρ h x ∈ S := by
    intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨ρ h y, by change (ρ h y) ^ 2 = (ρ h) (y ^ 2); rw [map_pow]⟩
  rcases hirr S hSinv with hbot | htop
  · intro x
    have hx : x ^ 2 ∈ S := ⟨x, rfl⟩
    rw [hbot] at hx
    simpa using hx
  · exfalso
    have hsurj : Function.Surjective (powMonoidHom 2 : X →* X) := by
      intro y
      have hy : y ∈ S := by rw [htop]; exact Subgroup.mem_top y
      exact hy
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ∣ Nat.card X := by
      rw [hcard]
      exact dvd_pow_self 2 hn
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz
      omega
    have hinj : Function.Injective (powMonoidHom 2 : X →* X) :=
      Finite.injective_iff_surjective.mpr hsurj
    have hcontra : (powMonoidHom 2 : X →* X) z = (powMonoidHom 2 : X →* X) 1 := by
      show z ^ 2 = 1 ^ 2
      rw [one_pow, hz2]
    exact hz1 (hinj hcontra)

theorem sec717_forall_rho_one_of_ne {K : Type} [Field K] [Finite K] [CharP K 2]
    {H X : Type} [Group H] [Group X]
    (φ : H →* GL (Fin 3 ⊕ Fin 3) K) (ρ : H → MulAut X)
    (hφr : φ.range = StatedOmega (StatedQuadPlus 3 K))
    (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k)
    (hker : ∀ h : H, φ h = 1 → ρ h = 1)
    {h : H} (hρ : ρ h = 1) (hφh : φ h ≠ 1) :
    ∀ g : H, ρ g = 1 := by
  let ρhom : H →* MulAut X := MonoidHom.mk' ρ hmul
  have ρhom_apply : ∀ h : H, ρhom h = ρ h := fun h => rfl
  let φ' : H →* ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    φ.codRestrict (StatedOmega (StatedQuadPlus 3 K)) (fun h => by
      rw [← hφr]
      exact MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have φ'_apply : ∀ h : H, (φ' h : GL (Fin 3 ⊕ Fin 3) K) = φ h := fun h => rfl
  have hφ'surj : Function.Surjective φ' := by
    intro a
    have ha : (a : GL (Fin 3 ⊕ Fin 3) K) ∈ φ.range := by
      rw [hφr]
      exact a.2
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp ha
    exact ⟨h, Subtype.ext hh⟩
  let M : Subgroup ↥(StatedOmega (StatedQuadPlus 3 K)) := ρhom.ker.map φ'
  haveI hMnorm : M.Normal :=
    Subgroup.Normal.map (inferInstance : ρhom.ker.Normal) φ' hφ'surj
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    isSimpleGroup_statedOmega_quadPlus_three_of_charTwo (K := K)
  have hmemK : h ∈ ρhom.ker := by
    rw [MonoidHom.mem_ker, ρhom_apply]
    exact hρ
  have hmemM : φ' h ∈ M := Subgroup.mem_map.mpr ⟨h, hmemK, rfl⟩
  have hMne : M ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmemM
    have h1 : φ' h = 1 := by simpa using hmemM
    apply hφh
    have h2 := congrArg Subtype.val h1
    rw [φ'_apply] at h2
    simpa using h2
  have hMtop : M = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top M with h | h
    · exact absurd h hMne
    · exact h
  intro g
  have hg : φ' g ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  obtain ⟨m, hmK, hmφ⟩ := Subgroup.mem_map.mp hg
  have hmρ : ρ m = 1 := by
    rw [MonoidHom.mem_ker, ρhom_apply] at hmK
    exact hmK
  have hφmg : φ m = φ g := by
    have h2 := congrArg Subtype.val hmφ
    rw [φ'_apply, φ'_apply] at h2
    exact h2
  have h := sec717_rho_eq_of_phi_eq φ ρ hmul hker hφmg
  rw [hmρ] at h
  exact h.symm

theorem sec717_phi_eq_one_of_rho_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {H X : Type} [Group H] [Group X] [Finite X] (n : ℕ)
    (φ : H →* GL (Fin 3 ⊕ Fin 3) K) (ρ : H → MulAut X)
    (hφr : φ.range = StatedOmega (StatedQuadPlus 3 K))
    (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k)
    (hker : ∀ h : H, φ h = 1 → ρ h = 1)
    (hirr : ∀ S : Subgroup X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hcard : Nat.card X = 2 ^ n) (hn : 2 ≤ n) :
    ∀ h : H, ρ h = 1 → φ h = 1 := by
  intro h hρ
  by_contra hφh
  have hall : ∀ g : H, ρ g = 1 :=
    sec717_forall_rho_one_of_ne φ ρ hφr hmul hker hρ hφh
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hinv : ∀ g : H, ∀ x ∈ Subgroup.zpowers z, ρ g x ∈ Subgroup.zpowers z := by
    intro g x hx
    rw [hall g, MulAut.one_apply]
    exact hx
  rcases hirr (Subgroup.zpowers z) hinv with hbot | htop
  · have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hbot] at hzmem
    have hz1 : z = 1 := by simpa using hzmem
    rw [hz1, orderOf_one] at hz
    omega
  · have hcardS : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, hz]
    rw [htop, Subgroup.card_top] at hcardS
    have h4 : 2 ^ 2 ≤ Nat.card X := by
      rw [hcard]
      exact pow_le_pow_right' (by norm_num) hn
    omega

theorem sec717_beta_ker {X Y : Type} [CommGroup X] [CommGroup Y] (β : X → X → Y)
    (hβL : ∀ x x' y : X, β (x * x') y = β x y * β x' y)
    (hβR : ∀ x y y' : X, β x (y * y') = β x y * β x y')
    (hexp : ∀ x : X, x ^ 2 = 1) :
    (∀ y : X, β 1 y = 1) ∧ (∀ x : X, β x 1 = 1) ∧
      (∀ x y : X, β x y ∈ (powMonoidHom 2 : Y →* Y).ker) := by
  have h1L : ∀ y : X, β 1 y = 1 := by
    intro y
    have h : β 1 y = β 1 y * β 1 y := by simpa using hβL 1 1 y
    have h' : β 1 y * 1 = β 1 y * β 1 y := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have h1R : ∀ x : X, β x 1 = 1 := by
    intro x
    have h : β x 1 = β x 1 * β x 1 := by simpa using hβR x 1 1
    have h' : β x 1 * 1 = β x 1 * β x 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  refine ⟨h1L, h1R, fun x y => ?_⟩
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  calc (β x y) ^ 2 = β x y * β x y := pow_two _
    _ = β (x * x) y := (hβL x x y).symm
    _ = β 1 y := by rw [← pow_two, hexp x]
    _ = 1 := h1L y

@[instance_reducible] def sec717Module (X : Type) [CommGroup X] (hexp : ∀ x : X, x ^ 2 = 1) :
    Module (ZMod 2) (Additive X) :=
  AddCommGroup.zmodModule (n := 2) (fun z => by
    have hz : z.toMul * z.toMul = 1 := by
      have h := hexp z.toMul
      rw [pow_two] at h
      exact h
    calc (2 : ℕ) • z = z + z := two_nsmul z
      _ = Additive.ofMul (z.toMul * z.toMul) := rfl
      _ = Additive.ofMul 1 := by rw [hz]
      _ = 0 := rfl)

theorem sec717_badd {X Y : Type} [CommGroup X] [CommGroup Y] (β : X → X → Y)
    (hβL : ∀ x x' y : X, β (x * x') y = β x y * β x' y)
    (hβR : ∀ x y y' : X, β x (y * y') = β x y * β x y')
    (h1L : ∀ y : X, β 1 y = 1) (h1R : ∀ x : X, β x 1 = 1)
    (K : Subgroup Y) (hY2 : ∀ x y : X, β x y ∈ K) :
    ∃ badd : Additive X →+ Additive X →+ Additive ↥K,
      ∀ x y : Additive X,
        badd x y = Additive.ofMul ⟨β x.toMul y.toMul, hY2 x.toMul y.toMul⟩ := by
  let badd : Additive X →+ Additive X →+ Additive ↥K :=
    { toFun := fun x =>
        { toFun := fun y => Additive.ofMul ⟨β x.toMul y.toMul, hY2 x.toMul y.toMul⟩
          map_zero' := by
            apply Additive.ext
            exact Subtype.ext (h1R x.toMul)
          map_add' := fun y y' => by
            apply Additive.ext
            exact Subtype.ext (hβR x.toMul y.toMul y'.toMul) }
      map_zero' := by
        apply AddMonoidHom.ext
        intro y
        apply Additive.ext
        exact Subtype.ext (h1L y.toMul)
      map_add' := fun x x' => by
        apply AddMonoidHom.ext
        intro y
        apply Additive.ext
        exact Subtype.ext (hβL x.toMul x'.toMul y.toMul) }
  exact ⟨badd, fun x y => rfl⟩

theorem sec717_form_construct {X Y : Type} [CommGroup X] [CommGroup Y]
    [Module (ZMod 2) (Additive X)] (β : X → X → Y)
    (hβL : ∀ x x' y : X, β (x * x') y = β x y * β x' y)
    (hβR : ∀ x y y' : X, β x (y * y') = β x y * β x y')
    (hexp : ∀ x : X, x ^ 2 = 1) {x0 y0 : X} (hne : β x0 y0 ≠ 1) :
    ∃ β' : Additive X →ₗ[ZMod 2] Additive X →ₗ[ZMod 2] ZMod 2,
      β' (Additive.ofMul x0) (Additive.ofMul y0) ≠ 0 ∧
      (∀ (σ : MulAut X), (∀ x y : X, β (σ x) (σ y) = β x y) →
        ∀ x y : Additive X,
          β' (Additive.ofMul (σ x.toMul)) (Additive.ofMul (σ y.toMul)) = β' x y) := by
  obtain ⟨h1L, h1R, hker⟩ := sec717_beta_ker β hβL hβR hexp
  let K : Subgroup Y := (powMonoidHom 2 : Y →* Y).ker
  have hY2 : ∀ x y, β x y ∈ K := hker
  letI : Module (ZMod 2) (Additive ↥K) := sec717Module ↥K (fun z => by
    apply Subtype.ext
    rw [pow_two]
    have h := MonoidHom.mem_ker.mp z.2
    rw [powMonoidHom_apply, pow_two] at h
    exact h)
  have hne0 : Additive.ofMul (⟨β x0 y0, hY2 x0 y0⟩ : ↥K) ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg (fun z : Additive ↥K => (z : ↥K)) h
    simpa using h'
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hne0
  obtain ⟨badd, hbadd⟩ := sec717_badd β hβL hβR h1L h1R K hY2
  let g : Additive X →+ (Additive X →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun x => χ.comp ((badd x).toZModLinearMap 2)
      map_zero' := by ext y; simp
      map_add' := fun x x' => by ext y; simp [map_add] }
  let β' : Additive X →ₗ[ZMod 2] Additive X →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => χ.comp ((badd x).toZModLinearMap 2)
      map_add' := fun x x' => by
        ext y
        simp only [LinearMap.add_apply, LinearMap.comp_apply,
          AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.add_apply]
        rw [badd.map_add]
        simp
      map_smul' := fun c x => by
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hc with rfl | rfl
        · rw [zero_smul]
          simp only [RingHom.id_apply, zero_smul]
          change χ.comp ((badd 0).toZModLinearMap 2) = 0
          rw [badd.map_zero]
          exact LinearMap.comp_zero χ
        · rw [one_smul]
          simp }
  have hβ'apply : ∀ x y : Additive X,
      β' x y = χ (Additive.ofMul ⟨β x.toMul y.toMul, hY2 x.toMul y.toMul⟩) := by
    intro x y
    change χ (badd x y) =
      χ (Additive.ofMul ⟨β x.toMul y.toMul, hY2 x.toMul y.toMul⟩)
    rw [hbadd]
  refine ⟨β', ?_, ?_⟩
  · rw [hβ'apply]
    exact hχ
  · intro σ hσ x y
    rw [hβ'apply, hβ'apply]
    congr 1
    apply Subtype.ext
    exact hσ x.toMul y.toMul

theorem sec717_radical_right {H X : Type} [Group H] [CommGroup X]
    [Module (ZMod 2) (Additive X)] (ρ : H → MulAut X)
    (hirr : ∀ S : Subgroup X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hexp : ∀ x : X, x ^ 2 = 1)
    (β' : Additive X →ₗ[ZMod 2] Additive X →ₗ[ZMod 2] ZMod 2)
    (hβ'inv : ∀ h : H, ∀ x y : X,
      β' (Additive.ofMul (ρ h x)) (Additive.ofMul (ρ h y)) =
        β' (Additive.ofMul x) (Additive.ofMul y))
    {x0 y0 : X} (hne : β' (Additive.ofMul x0) (Additive.ofMul y0) ≠ 0) :
    ∀ y : Additive X, (∀ x, β' x y = 0) → y = 0 := by
  let Rr : Subgroup X :=
    { carrier := {v | ∀ x : Additive X, β' x (Additive.ofMul v) = 0}
      one_mem' := by intro x; simp
      mul_mem' := by
        intro u v hu hv x
        have h : Additive.ofMul (u * v) =
            Additive.ofMul u + Additive.ofMul v := rfl
        rw [h, map_add, hu x, hv x, add_zero]
      inv_mem' := by
        intro u hu x
        have hu' : u⁻¹ = u := by
          have h : u * u = 1 := by rw [← pow_two, hexp u]
          exact (eq_inv_of_mul_eq_one_right h).symm
        rw [hu']
        exact hu x }
  have hRrinv : ∀ h : H, ∀ v ∈ Rr, ρ h v ∈ Rr := by
    intro h v hv x
    have hx : x = Additive.ofMul ((ρ h) ((ρ h)⁻¹ x.toMul)) := by simp
    rw [hx, hβ'inv h ((ρ h)⁻¹ x.toMul) v]
    exact hv _
  have hRrne : Rr ≠ ⊤ := by
    intro htop
    have hmem : y0 ∈ Rr := by rw [htop]; exact Subgroup.mem_top _
    exact hne (hmem (Additive.ofMul x0))
  have hRrbot : Rr = ⊥ := by
    rcases hirr Rr hRrinv with h | h
    · exact h
    · exact absurd h hRrne
  intro y hy
  have hv : y.toMul ∈ Rr := fun x => by simpa using hy x
  rw [hRrbot] at hv
  have h1 : y.toMul = 1 := by simpa using hv
  apply Additive.ext
  simpa using h1

theorem sec717_finish {K : Type} [Field K] [Finite K] [CharP K 2]
    {H X : Type} [Group H] [CommGroup X] [Finite X] [Module (ZMod 2) (Additive X)]
    (φ : H →* GL (Fin 3 ⊕ Fin 3) K) (ρ : H → MulAut X)
    (hmul : ∀ h k : H, ρ (h * k) = ρ h * ρ k)
    (hker : ∀ h : H, φ h = 1 → ρ h = 1)
    (hphi : ∀ h : H, ρ h = 1 → φ h = 1)
    {f r : ℕ} (hr : r.Prime) (hord : orderOf (2 : ZMod r) = 4 * f)
    (hcardX : Nat.card X = 2 ^ (4 * f))
    {a0 b0 : ↥(StatedOmega (StatedQuadPlus 3 K))}
    (hab : a0 * b0 = b0 * a0) (haord : orderOf a0 = r) (hbne : b0 ≠ 1)
    (hbpow : b0 ^ (2 ^ f + 1) = 1)
    {ha hb : H}
    (hha : φ ha = (a0 : GL (Fin 3 ⊕ Fin 3) K))
    (hhb : φ hb = (b0 : GL (Fin 3 ⊕ Fin 3) K))
    (β' : Additive X →ₗ[ZMod 2] Additive X →ₗ[ZMod 2] ZMod 2)
    (hright : ∀ y : Additive X, (∀ x, β' x y = 0) → y = 0)
    (hβ'inv : ∀ h : H, ∀ x y : X,
      β' (Additive.ofMul (ρ h x)) (Additive.ofMul (ρ h y)) =
        β' (Additive.ofMul x) (Additive.ofMul y)) :
    False := by
  haveI : IsMulCommutative X := ⟨⟨mul_comm⟩⟩
  set A : Additive X ≃ₗ[ZMod 2] Additive X := CFSG.GroupTheory.mulAutLinearHom X (ρ ha) with hA
  set B : Additive X ≃ₗ[ZMod 2] Additive X := CFSG.GroupTheory.mulAutLinearHom X (ρ hb) with hB
  have hAB : A * B = B * A := by
    have hφ : φ (ha * hb) = φ (hb * ha) := by
      rw [map_mul, map_mul, hha, hhb]
      exact congrArg Subtype.val hab
    have hρ : ρ (ha * hb) = ρ (hb * ha) :=
      sec717_rho_eq_of_phi_eq φ ρ hmul hker hφ
    calc A * B = CFSG.GroupTheory.mulAutLinearHom X (ρ ha * ρ hb) := by rw [hA, hB, map_mul]
      _ = CFSG.GroupTheory.mulAutLinearHom X (ρ (ha * hb)) := by rw [hmul]
      _ = CFSG.GroupTheory.mulAutLinearHom X (ρ (hb * ha)) := by rw [hρ]
      _ = CFSG.GroupTheory.mulAutLinearHom X (ρ hb * ρ ha) := by rw [hmul]
      _ = B * A := by rw [hA, hB, map_mul]
  have hAr : A ^ r = 1 := by
    rw [hA, ← map_pow, ← sec717_rho_pow ρ hmul ha r]
    have hφar : φ (ha ^ r) = 1 := by
      rw [map_pow, hha, ← Subgroup.coe_pow, ← haord, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [hker _ hφar, map_one]
  have hBpow : B ^ (2 ^ f + 1) = 1 := by
    rw [hB, ← map_pow, ← sec717_rho_pow ρ hmul hb (2 ^ f + 1)]
    have hφbq : φ (hb ^ (2 ^ f + 1)) = 1 := by
      rw [map_pow, hhb, ← Subgroup.coe_pow, hbpow, Subgroup.coe_one]
    rw [hker _ hφbq, map_one]
  have hAne : A ≠ 1 := by
    rw [hA]
    intro hA1
    have hρa : ρ ha = 1 :=
      CFSG.GroupTheory.mulAutLinearHom_injective X (by rw [hA1, map_one])
    have hφa : φ ha = 1 := hphi ha hρa
    have ha1 : a0 = 1 := by
      apply Subtype.ext
      rw [← hha, hφa]
      rfl
    have h1 : orderOf a0 = 1 := by rw [ha1, orderOf_one]
    exact (Nat.ne_of_gt hr.one_lt) (by rwa [haord] at h1)
  have hcardAX : Nat.card (Additive X) = 2 ^ (4 * f) := by
    rw [Nat.card_congr Additive.toMul]; exact hcardX
  have hB1 : B = 1 :=
    CFSG.LinearAlgebra.PpdSelfDual.eq_one_of_ppd_selfDual (X := Additive X) (f := f) (r := r)
      (a := A) (b := B) hcardAX hr hord hAB hAr hAne hBpow β' hright
      (fun x y => by
        rw [hA, CFSG.GroupTheory.mulAutLinearHom_apply, CFSG.GroupTheory.mulAutLinearHom_apply]
        simpa using hβ'inv ha x.toMul y.toMul)
      (fun x y => by
        rw [hB, CFSG.GroupTheory.mulAutLinearHom_apply, CFSG.GroupTheory.mulAutLinearHom_apply]
        simpa using hβ'inv hb x.toMul y.toMul)
  have hρb : ρ hb = 1 :=
    CFSG.GroupTheory.mulAutLinearHom_injective X (by simpa [map_one, ← hB] using hB1)
  have hφb : φ hb = 1 := hphi hb hρb
  have hb1 : b0 = 1 := by
    apply Subtype.ext
    rw [← hhb, hφb]
    rfl
  exact hbne hb1

theorem irrQ4NoPairing_holds : IrrQ4NoPairingStatement := by
  unfold IrrQ4NoPairingStatement
  intro K _ _ _ H _ φ X _ ρ hφr hmul hker hcard hirr Y _ β hβL hβR hβinv x0 y0
  by_contra hne
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hXpos : 0 < Nat.card X := by
    rw [hcard]
    exact pow_pos hKpos 4
  haveI : Finite X := Nat.finite_of_card_ne_zero (ne_of_gt hXpos)
  obtain ⟨f, hfcard⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨(n : ℕ), by rw [Nat.card_eq_fintype_card, hn]⟩
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hfcard
    have h2 : 1 < Nat.card K := by
      letI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have hcardX : Nat.card X = 2 ^ (4 * f) := by
    rw [hcard, hfcard, ← pow_mul, Nat.mul_comm]
  have hexp : ∀ x : X, x ^ 2 = 1 := sec717_exp_two (4 * f) ρ hirr hcardX (by omega)
  letI : Module (ZMod 2) (Additive X) := sec717Module X hexp
  have hphi : ∀ h : H, ρ h = 1 → φ h = 1 :=
    sec717_phi_eq_one_of_rho_eq_one (n := 4 * f) φ ρ hφr hmul hker hirr hcardX (by omega)
  have he : 2 ≤ 4 * f := by omega
  have he6 : 4 * f ≠ 6 := by omega
  obtain ⟨r, hr, -, hord⟩ := exists_prime_orderOf_two_eq (e := 4 * f) he he6
  obtain ⟨a0, b0, hab, haord, hbne, hbpow⟩ :=
    exists_commuting_ppd_statedOmega_quadPlus_three hfcard hr hord
  have ha0mem : (a0 : GL (Fin 3 ⊕ Fin 3) K) ∈ φ.range := by
    rw [hφr]
    exact a0.2
  obtain ⟨ha, hha⟩ := MonoidHom.mem_range.mp ha0mem
  have hb0mem : (b0 : GL (Fin 3 ⊕ Fin 3) K) ∈ φ.range := by
    rw [hφr]
    exact b0.2
  obtain ⟨hb, hhb⟩ := MonoidHom.mem_range.mp hb0mem
  obtain ⟨β', hβ'ne, hβ'invσ⟩ := sec717_form_construct β hβL hβR hexp hne
  have hβ'inv : ∀ h : H, ∀ x y : X,
      β' (Additive.ofMul (ρ h x)) (Additive.ofMul (ρ h y)) =
        β' (Additive.ofMul x) (Additive.ofMul y) :=
    fun h => hβ'invσ (ρ h) (hβinv h)
  have hright := sec717_radical_right ρ hirr hexp β' hβ'inv hβ'ne
  exact sec717_finish φ ρ hmul hker hphi hr hord hcardX hab haord hbne hbpow hha hhb
    β' hright hβ'inv

end CFSG.RankThree.GF2n.Stroth80
