module

public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.GF2n

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS NaturalModule
open scoped commutatorElement

private theorem fixed_eq_zero_of_irreducible {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (hirr : ∀ U : AddSubgroup V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v) :
    ∀ v : V, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
  intro v hv
  let U : AddSubgroup V :=
    { carrier := {u | ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • u = u}
      zero_mem' := fun x => smul_zero x
      add_mem' := fun {a b} ha hb x => by rw [smul_add, ha x, hb x]
      neg_mem' := fun {a} ha x => by rw [smul_neg, ha x] }
  have hUinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ u ∈ U, g • u ∈ U := by
    intro g u hu x
    rw [← mul_smul, hu (x * g), hu g]
  have hUne : U ≠ ⊤ := by
    intro htop
    obtain ⟨g, w, hw⟩ := hnt
    exact hw (by
      have hwU : w ∈ U := by rw [htop]; exact AddSubgroup.mem_top w
      exact hwU g)
  rcases hirr U hUinv with h | h
  · have hvU : v ∈ U := hv
    rw [h] at hvU
    exact AddSubgroup.mem_bot.mp hvU
  · exact absurd h hUne

private theorem exists_upper_smul_ne {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v) :
    ∃ a ∈ upperUnipotent K, ∃ v : V, a • v ≠ v := by
  by_contra h
  push Not at h
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    { carrier := {g | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul _ v
      mul_mem' := fun {g h} hg hh v => by rw [mul_smul, hh v, hg v]
      inv_mem' := fun {g} hg v => by
        have h' := hg (g⁻¹ • v)
        rw [← mul_smul, mul_inv_cancel, one_smul] at h'
        exact h'.symm }
  have hU : upperUnipotent K ≤ S := fun a ha v => h a ha v
  have hL : lowerUnipotent K ≤ S := by
    intro g hg
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).1 hg
    intro v
    rw [NaturalModule.lowerElt_smul,
      h (upperElt K t) ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩) (NaturalModule.weylElt K • v),
      NaturalModule.weylElt_smul_weylElt_smul]
  have htop : S = ⊤ := by
    rw [eq_top_iff, ← NaturalModule.upperUnipotent_sup_lowerUnipotent]
    exact sup_le hU hL
  obtain ⟨g, w, hw⟩ := hnt
  exact hw (by
    have hgS : g ∈ S := by rw [htop]; exact Subgroup.mem_top g
    exact hgS w)

private theorem exists_addEquiv_of_upper_quadratic {K V : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (hirr : ∀ U : AddSubgroup V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v) :
    ∃ θ : (Fin 2 → K) ≃+ V, ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : Fin 2 → K),
      θ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u) = g • θ u := by
  have hfix := fixed_eq_zero_of_irreducible hirr hnt
  obtain ⟨a, ha, v₀, hv₀⟩ := exists_upper_smul_ne hnt
  let w : V := a • v₀ - v₀
  have hw : w ≠ 0 := sub_ne_zero.mpr hv₀
  have hwfix : ∀ a' ∈ upperUnipotent K, a' • w = w := fun a' ha' => hquad a ha a' ha' v₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hinj, -, he, hθ⟩ :=
    CFSG.Timmesfeld.ARS.exists_natural_of_quadratic hfix hquad hwfix hw
  have hrangeInv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ y ∈ θ.range, g • y ∈ θ.range := by
    intro g y hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ u, hθ g u⟩
  have htop : θ.range = ⊤ := by
    rcases hirr θ.range hrangeInv with h | h
    · exfalso
      have hwmem : w ∈ θ.range := ⟨![1, 0], he⟩
      rw [h] at hwmem
      exact hw (AddSubgroup.mem_bot.mp hwmem)
    · exact h
  exact ⟨AddEquiv.ofBijective θ ⟨hinj, AddMonoidHom.range_eq_top.mp htop⟩, hθ⟩

theorem exists_addEquiv_of_quadratic {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hU : Nat.card U = Nat.card K)
    (hirr : ∀ W : AddSubgroup V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v)
    (hquad : ∀ a ∈ U, ∀ a' ∈ U, ∀ v : V, a' • (a • v - v) = a • v - v) :
    ∃ θ : (Fin 2 → K) ≃+ V, ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : Fin 2 → K),
      θ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u) = g • θ u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcardK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem
    (F := K) (p := 2) (f := (n : ℕ)) Nat.prime_two hcardK hU
  have huni : ∀ t : K, CFSG.SL2MinimalFaithful.unipotent t = upperElt K t :=
    fun t => Subtype.ext rfl
  have hle : (upperUnipotent K).map (MulAut.conj g).toMonoidHom ≤ U := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 hz
    change (MulAut.conj g) (upperElt K t) ∈ U
    rw [MulAut.conj_apply]
    simpa [huni] using hg t
  have hUeq : (upperUnipotent K).map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, card_upperUnipotent, hU])
  let ρ := DistribMulAction.toAddMonoidEnd (Matrix.SpecialLinearGroup (Fin 2) K) V
  let e₀ : V ≃+ V := DistribMulAction.toAddEquiv V g⁻¹
  let ρ' := ρ.comp (MulAut.conj g).toMonoidHom
  letI : DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V := DistribMulAction.compHom _ ρ'
  have hirr' : ∀ W : AddSubgroup V,
      (∀ h : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, h • v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro h v hv
    change ρ h v ∈ W
    have hh : ρ h = ρ' (MulAut.conj g⁻¹ h) := by
      change ρ h = ρ (MulAut.conj g (MulAut.conj g⁻¹ h))
      rw [show MulAut.conj g (MulAut.conj g⁻¹ h) = h from by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group]
    rw [hh]
    exact hW (MulAut.conj g⁻¹ h) v hv
  have hquad' : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    have haU : MulAut.conj g a ∈ U := by
      rw [← hUeq]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have ha'U : MulAut.conj g a' ∈ U := by
      rw [← hUeq]
      exact Subgroup.mem_map.mpr ⟨a', ha', rfl⟩
    change ρ (MulAut.conj g a') (ρ (MulAut.conj g a) v - v) =
      ρ (MulAut.conj g a) v - v
    exact hquad _ haU _ ha'U v
  have hnt' : ∃ (h : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), h • v ≠ v := by
    obtain ⟨h, v, hv⟩ := hnt
    refine ⟨MulAut.conj g⁻¹ h, v, ?_⟩
    intro hfix
    apply hv
    change ρ (MulAut.conj g (MulAut.conj g⁻¹ h)) v = v at hfix
    rwa [show MulAut.conj g (MulAut.conj g⁻¹ h) = h from by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group] at hfix
  obtain ⟨θ', hθ'⟩ := exists_addEquiv_of_upper_quadratic hirr' hnt' hquad'
  refine ⟨θ'.trans e₀, ?_⟩
  intro h u
  change e₀ (θ' ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ u)) = ρ h (e₀ (θ' u))
  rw [hθ']
  change e₀ (ρ (MulAut.conj g h) (θ' u)) = ρ h (e₀ (θ' u))
  change ρ g⁻¹ (ρ (MulAut.conj g h) (θ' u)) = ρ h (ρ g⁻¹ (θ' u))
  calc
    ρ g⁻¹ (ρ (MulAut.conj g h) (θ' u))
        = ρ (g⁻¹ * MulAut.conj g h) (θ' u) := by rw [map_mul]; rfl
    _ = ρ (h * g⁻¹) (θ' u) := by
      congr 1
      rw [MulAut.conj_apply]
      group
    _ = ρ h (ρ g⁻¹ (θ' u)) := by rw [map_mul]; rfl

theorem eq_zero_of_smul_eq_self_of_quadratic {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hU : Nat.card U = Nat.card K)
    (hirr : ∀ W : AddSubgroup V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v)
    (hquad : ∀ a ∈ U, ∀ a' ∈ U, ∀ v : V, a' • (a • v - v) = a • v - v)
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : g ≠ 1) (hodd : Odd (orderOf g))
    {v : V} (hv : g • v = v) : v = 0 := by
  obtain ⟨θ, hθ⟩ := exists_addEquiv_of_quadratic hU hirr hnt hquad
  by_contra hv0
  obtain ⟨u, hu⟩ := θ.surjective v
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact hv0 hu.symm
  have hgu : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    apply θ.injective
    calc θ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u) = g • θ u := hθ g u
      _ = g • v := by rw [hu]
      _ = v := hv
      _ = θ u := hu.symm
  have hsq : g ^ 2 = 1 :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.sq_eq_one_of_fix g hu0 hgu
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hone : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      omega
  exact hg (orderOf_eq_one_iff.mp hone)

theorem exists_smul_ne_of_quadratic {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hU : Nat.card U = Nat.card K)
    (hirr : ∀ W : AddSubgroup V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V), g • v ≠ v)
    (hquad : ∀ a ∈ U, ∀ a' ∈ U, ∀ v : V, a' • (a • v - v) = a • v - v)
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : g ≠ 1) :
    ∃ v : V, g • v ≠ v := by
  obtain ⟨θ, hθ⟩ := exists_addEquiv_of_quadratic hU hirr hnt hquad
  have hvec : ∃ u : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u ≠ u := by
    by_contra h
    push Not at h
    exact hg (NaturalModule.eq_one_of_forall_mulVec_eq h)
  obtain ⟨u, hu⟩ := hvec
  refine ⟨θ u, ?_⟩
  intro hfix
  apply hu
  apply θ.injective
  rw [hθ, hfix]

universe u

structure SectionModule {G : Type u} [Group G] {K : Type*} [Field K]
    (A X C : Subgroup G) (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K) where
  W : Type u
  [addCommGroup : AddCommGroup W]
  [distribMulAction : DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) W]
  π : ↥X → W
  map_mul : ∀ x y, π (x * y) = π x + π y
  surjective : Function.Surjective π
  eq_zero_iff : ∀ x, π x = 0 ↔ (x : G) ∈ C
  smul_eq : ∀ (a : ↥A) (x y : ↥X), (y : G) = a * x * (a : G)⁻¹ → φ a • π x = π y

attribute [instance] SectionModule.addCommGroup SectionModule.distribMulAction

private theorem exists_conjEnd {G : Type*} [Group G] {K : Type*} [Field K]
    {A X C : Subgroup G} {N : Subgroup ↥X}
    (hmemN : ∀ y : ↥X, y ∈ N ↔ (y : G) ∈ C)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hAC : ∀ a ∈ A, ∀ x ∈ C, a * x * a⁻¹ ∈ C) :
    ∃ cX : ↥A → ↥X →* ↥X,
      (∀ (b : ↥A) (y : ↥X), ((cX b y : ↥X) : G) = (b : G) * y * (b : G)⁻¹) ∧
      (∀ y : ↥X, cX 1 y = y) ∧
      (∀ (b b' : ↥A) (y : ↥X), cX (b * b') y = cX b (cX b' y)) ∧
      (∀ b : ↥A, N ≤ N.comap (cX b)) := by
  let cX : ↥A → ↥X →* ↥X := fun b =>
    { toFun := fun y => ⟨(b : G) * y * (b : G)⁻¹, hAX b b.2 y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y z => Subtype.ext (by
        show (b : G) * ((y : G) * z) * (b : G)⁻¹ =
          ((b : G) * y * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹)
        group) }
  have hcX : ∀ (b : ↥A) (y : ↥X), ((cX b y : ↥X) : G) = (b : G) * y * (b : G)⁻¹ :=
    fun _ _ => rfl
  refine ⟨cX, hcX, ?_, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    rw [hcX]
    simp
  · intro b b' y
    apply Subtype.ext
    simp only [hcX]
    simp only [Subgroup.coe_mul]
    group
  · intro b y hy
    rw [Subgroup.mem_comap, hmemN, hcX]
    exact hAC b b.2 (y : G) ((hmemN y).mp hy)

private theorem exists_sectionEnd {G : Type*} [Group G] {K : Type*} [Field K]
    {A X C : Subgroup G} (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K)
    {N : Subgroup ↥X} [N.Normal]
    (cX : ↥A → ↥X →* ↥X)
    (hcX : ∀ (b : ↥A) (y : ↥X), ((cX b y : ↥X) : G) = (b : G) * y * (b : G)⁻¹)
    (hcX_one : ∀ y : ↥X, cX 1 y = y)
    (hcX_mul : ∀ (b b' : ↥A) (y : ↥X), cX (b * b') y = cX b (cX b' y))
    (hcN : ∀ b : ↥A, N ≤ N.comap (cX b))
    (hmemN : ∀ y : ↥X, y ∈ N ↔ (y : G) ∈ C)
    (hker : ∀ a : ↥A, φ a = 1 → ∀ x ∈ X, ⁅(a : G), x⁆ ∈ C) :
    ∃ ρ₀ : ↥A →* AddMonoid.End (Additive (↥X ⧸ N)),
      (∀ (b : ↥A) (y : ↥X), ρ₀ b (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk (cX b y))) ∧
      φ.ker ≤ ρ₀.ker := by
  let ρ₀ : ↥A →* AddMonoid.End (Additive (↥X ⧸ N)) :=
    { toFun := fun b => MonoidHom.toAdditive (QuotientGroup.map N N (cX b) (hcN b))
      map_one' := by
        refine AddMonoidHom.ext fun v => ?_
        obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        change Additive.ofMul (QuotientGroup.mk (cX 1 y)) =
          Additive.ofMul (QuotientGroup.mk y)
        rw [hcX_one y]
      map_mul' := fun b b' => by
        refine AddMonoidHom.ext fun v => ?_
        obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        change Additive.ofMul (QuotientGroup.mk (cX (b * b') y)) =
          Additive.ofMul (QuotientGroup.mk (cX b (cX b' y)))
        rw [hcX_mul b b' y] }
  have hsmul₀ : ∀ (b : ↥A) (y : ↥X),
      ρ₀ b (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk (cX b y)) := fun _ _ => rfl
  refine ⟨ρ₀, hsmul₀, ?_⟩
  intro b hb
  rw [MonoidHom.mem_ker] at hb
  rw [MonoidHom.mem_ker]
  refine AddMonoidHom.ext fun v => ?_
  obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  change Additive.ofMul (QuotientGroup.mk (cX b y)) =
    Additive.ofMul (QuotientGroup.mk y)
  apply Additive.ofMul.injective
  apply (QuotientGroup.eq_iff_div_mem).mpr
  rw [hmemN, Subgroup.coe_div, hcX, div_eq_mul_inv]
  simpa [commutatorElement_def] using hker b hb (y : G) y.2

theorem exists_sectionModule {G : Type*} [Group G] {K : Type*} [Field K]
    {A X C : Subgroup G} (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφ : Function.Surjective φ) (hCX : C ≤ X)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ C)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hAC : ∀ a ∈ A, ∀ x ∈ C, a * x * a⁻¹ ∈ C)
    (hker : ∀ a : ↥A, φ a = 1 → ∀ x ∈ X, ⁅(a : G), x⁆ ∈ C) :
    Nonempty (SectionModule A X C φ) := by
  classical
  have hCN : (C.subgroupOf X).Normal := by
    refine ⟨fun c hc y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    change ((y : G) * (c : G) * (y : G)⁻¹) ∈ C
    rw [show (y : G) * (c : G) * (y : G)⁻¹ = ⁅(y : G), (c : G)⁆ * (c : G) by
      rw [commutatorElement_def]; group]
    exact mul_mem (hXX (y : G) y.2 (c : G) (hCX hc)) hc
  let N : Subgroup ↥X := C.subgroupOf X
  letI : N.Normal := hCN
  let W := ↥X ⧸ N
  have hWcomm : IsMulCommutative W := by
    refine IsMulCommutative.of_comm fun u v => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
      Subgroup.mem_subgroupOf, Subgroup.coe_div, div_eq_mul_inv]
    simpa [commutatorElement_def, mul_assoc] using hXX (y : G) y.2 (z : G) z.2
  letI : CommGroup W := IsMulCommutative.instCommGroup
  have hmemN : ∀ y : ↥X, y ∈ N ↔ (y : G) ∈ C := fun y => Subgroup.mem_subgroupOf
  obtain ⟨cX, hcX, hcX_one, hcX_mul, hcN⟩ :=
    exists_conjEnd (K := K) (N := N) hmemN hAX hAC
  obtain ⟨ρ₀, hsmul₀, hker_le⟩ :=
    exists_sectionEnd φ cX hcX hcX_one hcX_mul hcN hmemN hker
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K →* AddMonoid.End (Additive W) :=
    (QuotientGroup.lift φ.ker ρ₀ hker_le).comp e.symm.toMonoidHom
  have hρ : ∀ b : ↥A, ρ (φ b) = ρ₀ b := by
    intro b
    have h1 : e.symm (φ b) = (b : ↥A ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift φ.ker ρ₀ hker_le (e.symm (φ b)) = ρ₀ b
    rw [h1]
    rfl
  letI : DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Additive W) :=
    DistribMulAction.compHom _ ρ
  have hsmul : ∀ (b : ↥A) (y : ↥X),
      ρ (φ b) (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk (cX b y)) := fun b y => by
    rw [hρ]
    exact hsmul₀ b y
  refine ⟨{ W := Additive W
            π := fun x => Additive.ofMul (QuotientGroup.mk x)
            map_mul := ?_
            surjective := ?_
            eq_zero_iff := ?_
            smul_eq := ?_ }⟩
  · intro x y
    rw [QuotientGroup.mk_mul, ofMul_mul]
  · intro w
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  · intro x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp
        (Additive.ofMul.injective (by rw [ofMul_one]; exact h)))
    · rw [(QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr h), ofMul_one]
  · intro a x y hy
    change ρ (φ a) (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk y)
    rw [hsmul, show cX a x = y from Subtype.ext (by rw [hcX, hy])]

namespace SectionModule

variable {G : Type*} [Group G] {K : Type*} [Field K] {A X C : Subgroup G}
  {φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K} (S : SectionModule A X C φ)

theorem map_one : S.π (1 : ↥X) = 0 := by
  have h := S.map_mul (1 : ↥X) 1
  rw [mul_one] at h
  exact (add_left_cancel (by rw [add_zero]; exact h)).symm

theorem map_inv (x : ↥X) : S.π x⁻¹ = - S.π x := by
  have h := S.map_mul x x⁻¹
  rw [mul_inv_cancel, S.map_one] at h
  have h' : S.π x⁻¹ + S.π x = 0 := by rw [add_comm]; exact h.symm
  exact eq_neg_of_add_eq_zero_left h'

theorem irreducible
    (hCX : C ≤ X) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hirr : ∀ Y : Subgroup G, C ≤ Y → Y ≤ X →
      (∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = C ∨ Y = X) :
    ∀ W : AddSubgroup S.W,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let Y : Subgroup G :=
    { carrier := {y | ∃ x : ↥X, (x : G) = y ∧ S.π x ∈ W}
      one_mem' := ⟨1, rfl, by rw [S.map_one]; exact W.zero_mem⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨x₁, rfl, hx₁⟩ ⟨x₂, rfl, hx₂⟩
        exact ⟨x₁ * x₂, rfl, by rw [S.map_mul]; exact W.add_mem hx₁ hx₂⟩
      inv_mem' := by
        rintro y ⟨x, rfl, hx⟩
        exact ⟨x⁻¹, rfl, by rw [S.map_inv]; exact W.neg_mem hx⟩ }
  have hCY : C ≤ Y := by
    intro c hc
    refine ⟨⟨c, hCX hc⟩, rfl, ?_⟩
    have h0 : S.π ⟨c, hCX hc⟩ = 0 := (S.eq_zero_iff _).mpr hc
    rw [h0]
    exact W.zero_mem
  have hYX : Y ≤ X := by
    rintro y ⟨x, rfl, -⟩
    exact x.2
  have hAY : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
    intro a ha y hy
    obtain ⟨x, rfl, hx⟩ := hy
    let y' : ↥X := ⟨(a : G) * x * (a : G)⁻¹, hAX a ha x x.2⟩
    exact ⟨y', rfl, by
      rw [← S.smul_eq ⟨a, ha⟩ x y' rfl]
      exact hW (φ ⟨a, ha⟩) (S.π x) hx⟩
  rcases hirr Y hCY hYX hAY with hY | hY
  · left
    apply le_antisymm
    · intro u hu
      rw [AddSubgroup.mem_bot]
      obtain ⟨x, rfl⟩ := S.surjective u
      have hxY : (x : G) ∈ Y := ⟨x, rfl, hu⟩
      rw [hY] at hxY
      exact (S.eq_zero_iff x).mpr hxY
    · exact bot_le
  · right
    rw [eq_top_iff]
    intro u _
    obtain ⟨x, rfl⟩ := S.surjective u
    have hxY : (x : G) ∈ Y := by rw [hY]; exact x.2
    obtain ⟨z, hzX, hz⟩ := hxY
    have hzx : z = x := Subtype.ext hzX
    rwa [hzx] at hz

theorem smul_eq_iff_commutator_mem (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (a : ↥A) (x : ↥X) :
    φ a • S.π x = S.π x ↔ ⁅(a : G), (x : G)⁆ ∈ C := by
  let y : ↥X := ⟨(a : G) * x * (a : G)⁻¹, hAX a a.2 x x.2⟩
  have hsm : φ a • S.π x = S.π y := S.smul_eq a x y rfl
  have hval : ((y * x⁻¹ : ↥X) : G) = ⁅(a : G), (x : G)⁆ := by
    simp [y, commutatorElement_def, mul_assoc]
  have hsub : S.π (y * x⁻¹) = S.π y - S.π x := by
    rw [S.map_mul, S.map_inv, sub_eq_add_neg]
  rw [hsm]
  constructor
  · intro h
    have h0 : ((y * x⁻¹ : ↥X) : G) ∈ C :=
      (S.eq_zero_iff _).mp (by rw [hsub, h, sub_self])
    rwa [hval] at h0
  · intro h
    have h0 : S.π (y * x⁻¹) = 0 :=
      (S.eq_zero_iff _).mpr (by rwa [hval])
    rw [hsub] at h0
    exact sub_eq_zero.mp h0

theorem exists_smul_ne (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hker : ∀ a : ↥A, φ a = 1 → ∀ x ∈ X, ⁅(a : G), x⁆ ∈ C)
    (hnt : ∃ a ∈ A, ∃ x ∈ X, ⁅a, x⁆ ∉ C) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : S.W), g • v ≠ v := by
  obtain ⟨a, ha, x, hx, hne⟩ := hnt
  have hφa : φ ⟨a, ha⟩ ≠ 1 := by
    intro h1
    exact hne (hker ⟨a, ha⟩ h1 x hx)
  refine ⟨φ ⟨a, ha⟩, S.π ⟨x, hx⟩, ?_⟩
  intro hfix
  exact hne ((S.smul_eq_iff_commutator_mem hAX ⟨a, ha⟩ ⟨x, hx⟩).mp hfix)

theorem quadratic (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    {Q : Subgroup G} (hQA : Q ≤ A)
    (hquad : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ x ∈ X, ⁅q', ⁅q, x⁆⁆ ∈ C) :
    ∀ a ∈ (Q.subgroupOf A).map φ, ∀ a' ∈ (Q.subgroupOf A).map φ, ∀ v : S.W,
      a' • (a • v - v) = a • v - v := by
  intro a ha a' ha' v
  obtain ⟨qA, hqA, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨qA', hqA', rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨x, rfl⟩ := S.surjective v
  let y : ↥X := ⟨(qA : G) * x * (qA : G)⁻¹, hAX qA qA.2 x x.2⟩
  have hsm : φ qA • S.π x = S.π y := S.smul_eq qA x y rfl
  have hsub : φ qA • S.π x - S.π x = S.π (y * x⁻¹) := by
    rw [hsm, S.map_mul, S.map_inv, sub_eq_add_neg]
  rw [hsub]
  let z : ↥X :=
    ⟨(qA' : G) * (y * x⁻¹) * (qA' : G)⁻¹, hAX qA' qA'.2 (y * x⁻¹) (y * x⁻¹).2⟩
  have hsm' : φ qA' • S.π (y * x⁻¹) = S.π z := S.smul_eq qA' (y * x⁻¹) z rfl
  rw [hsm']
  have hval : ((z * (y * x⁻¹)⁻¹ : ↥X) : G) = ⁅(qA' : G), ⁅(qA : G), (x : G)⁆⁆ := by
    simp [z, y, commutatorElement_def, mul_assoc]
  have hC : ⁅(qA' : G), ⁅(qA : G), (x : G)⁆⁆ ∈ C :=
    hquad (qA : G) (Subgroup.mem_subgroupOf.mp hqA) (qA' : G)
      (Subgroup.mem_subgroupOf.mp hqA') (x : G) x.2
  have hzero : S.π (z * (y * x⁻¹)⁻¹) = 0 :=
    (S.eq_zero_iff _).mpr (by rwa [hval])
  have hz : S.π z = S.π (y * x⁻¹) := by
    have h := S.map_mul z (y * x⁻¹)⁻¹
    rw [S.map_inv, hzero] at h
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h.symm)
  rw [hz]

end SectionModule

theorem mem_of_commutator_mem_of_quadratic {G : Type*} [Group G] {K : Type*}
    [Field K] [Finite K] [CharP K 2] {A X C Q : Subgroup G}
    (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K) (hφ : Function.Surjective φ)
    (hCX : C ≤ X)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ C)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hAC : ∀ a ∈ A, ∀ x ∈ C, a * x * a⁻¹ ∈ C)
    (hker : ∀ a : ↥A, φ a = 1 → ∀ x ∈ X, ⁅(a : G), x⁆ ∈ C)
    (hirr : ∀ Y : Subgroup G, C ≤ Y → Y ≤ X →
      (∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = C ∨ Y = X)
    (hnt : ∃ a ∈ A, ∃ x ∈ X, ⁅a, x⁆ ∉ C)
    (hQA : Q ≤ A) (hQ : Nat.card ↥((Q.subgroupOf A).map φ) = Nat.card K)
    (hquad : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ x ∈ X, ⁅q', ⁅q, x⁆⁆ ∈ C)
    {a : G} (ha : a ∈ A) (hφa : φ ⟨a, ha⟩ ≠ 1) (hodd : Odd (orderOf a))
    {x : G} (hx : x ∈ X) (hxa : ⁅a, x⁆ ∈ C) : x ∈ C := by
  obtain ⟨S⟩ := exists_sectionModule φ hφ hCX hXX hAX hAC hker
  let U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (Q.subgroupOf A).map φ
  have hU : Nat.card U = Nat.card K := hQ
  have hirrS := S.irreducible hCX hAX hirr
  have hntS := S.exists_smul_ne hAX hker hnt
  have hquadS := S.quadratic hAX hQA hquad
  have hoddφ : Odd (orderOf (φ ⟨a, ha⟩)) := by
    refine Odd.of_dvd_nat hodd ?_
    have h := orderOf_map_dvd φ ⟨a, ha⟩
    rwa [← Subgroup.orderOf_coe] at h
  have hv : φ ⟨a, ha⟩ • S.π ⟨x, hx⟩ = S.π ⟨x, hx⟩ :=
    (S.smul_eq_iff_commutator_mem hAX ⟨a, ha⟩ ⟨x, hx⟩).mpr hxa
  have hzero := eq_zero_of_smul_eq_self_of_quadratic hU hirrS hntS hquadS hφa hoddφ hv
  exact (S.eq_zero_iff ⟨x, hx⟩).mp hzero

theorem exists_commutator_not_mem_of_quadratic {G : Type*} [Group G] {K : Type*}
    [Field K] [Finite K] [CharP K 2] {A X C Q : Subgroup G}
    (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K) (hφ : Function.Surjective φ)
    (hCX : C ≤ X)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ C)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hAC : ∀ a ∈ A, ∀ x ∈ C, a * x * a⁻¹ ∈ C)
    (hker : ∀ a : ↥A, φ a = 1 → ∀ x ∈ X, ⁅(a : G), x⁆ ∈ C)
    (hirr : ∀ Y : Subgroup G, C ≤ Y → Y ≤ X →
      (∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = C ∨ Y = X)
    (hnt : ∃ a ∈ A, ∃ x ∈ X, ⁅a, x⁆ ∉ C)
    (hQA : Q ≤ A) (hQ : Nat.card ↥((Q.subgroupOf A).map φ) = Nat.card K)
    (hquad : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ x ∈ X, ⁅q', ⁅q, x⁆⁆ ∈ C)
    {a : G} (ha : a ∈ A) (hφa : φ ⟨a, ha⟩ ≠ 1) :
    ∃ x ∈ X, ⁅a, x⁆ ∉ C := by
  obtain ⟨S⟩ := exists_sectionModule φ hφ hCX hXX hAX hAC hker
  let U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (Q.subgroupOf A).map φ
  have hU : Nat.card U = Nat.card K := hQ
  have hirrS := S.irreducible hCX hAX hirr
  have hntS := S.exists_smul_ne hAX hker hnt
  have hquadS := S.quadratic hAX hQA hquad
  obtain ⟨v, hv⟩ := exists_smul_ne_of_quadratic hU hirrS hntS hquadS hφa
  obtain ⟨x, rfl⟩ := S.surjective v
  refine ⟨x, x.2, ?_⟩
  intro hC
  exact hv ((S.smul_eq_iff_commutator_mem hAX ⟨a, ha⟩ x).mpr hC)

end CFSG.RankThree.GF2n
