module

public import CFSG.Quasithin.Background.C35InspSmall
public import CFSG.Quasithin.Background.C35InspNat
public import CFSG.Quasithin.Background.C48AsmLine
public import CFSG.Quasithin.Background.F918Z4c1Sz

public section

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique C35Pf

variable {A : Type} [Group A] {K : Subgroup A} {G' : Type} [Group G']

@[expose] def LeviConcl (K Y : Subgroup A) : Prop :=
  CharTwo (perfectCore Y) ∧
    ((∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (ModO2 (perfectCore Y))) ∨
      (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m (ModO2 (perfectCore Y))) ∨
      IsPSL 3 2 1 (ModO2 (perfectCore Y)) ∨ IsPSL 4 2 1 (ModO2 (perfectCore Y))) ∧
    (IsPSL 4 2 1 (ModO2 (perfectCore Y)) →
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K) ∧ IsMaxParabolic2 K Y ∧
        ∀ g ∈ Subgroup.normalizer (K : Set A) ⊓ Subgroup.normalizer (Y : Set A),
          ∃ k ∈ K, ∀ x ∈ K, (g * x * g⁻¹)⁻¹ * (k * x * k⁻¹) ∈ centerOf K)

@[expose] def SmallLevi (T : Type) [Group T] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m T) ∨ (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m T) ∨ IsPSL 3 2 1 T

theorem SmallLevi.of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : SmallLevi T) : SmallLevi T' := by
  rcases h with ⟨m, hm, h⟩ | ⟨m, hm, hm3, h⟩ | h
  · exact Or.inl ⟨m, hm, h.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨m, hm, hm3, h.of_mulEquiv e⟩)
  · exact Or.inr (Or.inr (h.of_mulEquiv e))

theorem card_ne_of_smallLevi {T : Type} [Group T] (h : SmallLevi T) : Nat.card T ≠ 20160 := by
  rcases h with ⟨m, -, h⟩ | ⟨m, -, hm3, h⟩ | h
  · rw [C48.card_psl_two_two h]
    intro he
    have hle : 2 ^ m ≤ 20160 := Nat.le_of_dvd (by norm_num) ⟨_, he.symm⟩
    have hm : m < 15 := by
      by_contra hm'
      have : 2 ^ 15 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m <;> norm_num at he
  · rw [card_of_isSz h]
    intro he
    have hle : (2 ^ m) ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num)
      ⟨((2 ^ m) ^ 2 + 1) * (2 ^ m - 1), by rw [← he]; ring⟩
    have hm : m < 8 := by
      by_contra hm'
      have : 2 ^ 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 8 * 2 ^ 8 ≤ (2 ^ m) ^ 2 := by rw [sq]; exact Nat.mul_le_mul this this
      omega
    interval_cases m <;> norm_num at he
  · rw [(C48Pf.FMod.card_of_isPSL_two_one (Or.inl rfl) h).1 rfl]
    norm_num

theorem leviConcl_of_small {Y : Subgroup A} (hc : CharTwo (perfectCore Y))
    (hs : SmallLevi (ModO2 (perfectCore Y))) : LeviConcl K Y := by
  refine ⟨hc, ?_, fun h4 => ?_⟩
  · rcases hs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact absurd ((C48Pf.FMod.card_of_isPSL_two_one (Or.inr rfl) h4).2 rfl)
      (card_ne_of_smallLevi hs)

theorem smallLevi_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m) : SmallLevi (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h2m : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine Or.inl ⟨m, hm, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance,
    inferInstance, hF, ⟨CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem exists_overgroup [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX : perfectCore Y ≠ ⊥) {φ : ↥K →* G'}
    (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ) :
    ∃ T : Subgroup G', IsSylowTwoOf T ⊤ ∧ T ≤ img φ Y ∧
      Subgroup.normalizer (T : Set G') ≤ img φ Y ∧ img φ Y ≠ ⊤ ∧
        ¬ Group.IsSolvable ↥(img φ Y) := by
  obtain ⟨hYK, S, hS, hNS⟩ := hpar
  have hZS : centerOf K ≤ S := centerOf_le_of_sylow hZ hS
  have hSY : S ≤ Y := fun s hs => hNS ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  refine ⟨img φ S, isSylowTwoOf_img hker hφ hS hZS, Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSY (Subgroup.mem_subgroupOf.1 hx)),
    normalizer_img_le hker hφ hS.1 hZS hNS,
    img_ne_top hker hYK (hZS.trans hSY) hne, fun hsolv => ?_⟩
  exact hX ((isSolvable_iff_perfectCore_eq_bot Y).1 (isSolvable_of_img hker hYK hsolv))

theorem false_of_solvOver [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX : perfectCore Y ≠ ⊥)
    (h : SolvOver (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨T, hT, hTY, -, hne', hns⟩ := exists_overgroup hZ hpar hne hX
    (φ := QuotientGroup.mk' (Subgroup.center ↥K)) (by rw [QuotientGroup.ker_mk'])
    (QuotientGroup.mk'_surjective _)
  exact hns (h T _ hT hTY hne')

theorem exists_conj_normalizer [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX : perfectCore Y ≠ ⊥) [Finite G']
    (φ : ↥K →* G') (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ)
    {U₀ : Subgroup G'} (hU₀ : IsSylowTwoOf U₀ ⊤) :
    ∃ g : G', Subgroup.normalizer (U₀ : Set G') ≤
        img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y ≠ ⊤ ∧
      ¬ Group.IsSolvable ↥(img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y) := by
  obtain ⟨T, hT, -, hNT, hne', hns⟩ := exists_overgroup hZ hpar hne hX hker hφ
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hU₀ hT
  have himg : img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y =
      (img φ Y).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [img, img, Subgroup.map_map]
  refine ⟨g, ?_⟩
  rw [himg]
  refine ⟨fun x hx => ?_, fun htop => hne' ?_, fun hs => hns ?_⟩
  · have hx' : (MulAut.conj g).toMonoidHom x ∈ Subgroup.normalizer (T : Set G') := by
      rw [← hg, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨x, hx, rfl⟩
    refine ⟨_, hNT hx', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) htop
    rwa [Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective,
      show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G' by
        ext y
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group,
      Subgroup.map_id] at this
  · exact Group.isSolvable_of_isSolvable_injective
      (f := ((img φ Y).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).toMonoidHom)
      ((img φ Y).equivMapOfInjective _ (MulAut.conj g⁻¹).injective).injective

theorem ker_conj_comp (φ : ↥K →* G') (g : G') :
    ((MulAut.conj g⁻¹).toMonoidHom.comp φ).ker = φ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem le_ker_of_isPGroup {N T : Type*} [Group N] [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) (g : N →* T) (hg : Function.Surjective g)
    {R : Subgroup N} [R.Normal] (hR : IsPGroup 2 R) : R ≤ g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (R.map g).Normal := Subgroup.Normal.map inferInstance g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map g) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h2 : IsPGroup 2 T := by
      have := hR.map g
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    have := h2.isNilpotent
    obtain ⟨a, b, hab⟩ := hT
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

theorem charTwo_of_simple [Finite A] {X : Subgroup A} (hX : ⁅X, X⁆ = X)
    {T : Type} [Group T] [IsSimpleGroup T]
    (α : ↥X →* T) (hα : Function.Surjective α) (hker : IsPGroup 2 α.ker)
    (hnc : ∃ r x : ↥X, α r = 1 ∧ x * r ≠ r * x) : CharTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := α.ker with hR
  have hRO : R ≤ CFSG.Open.pCore 2 ↥X :=
    CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker α) hker
  set C : Subgroup ↥X := Subgroup.centralizer (R : Set ↥X) with hC
  have hRn : R.Normal := MonoidHom.normal_ker α
  have hCn : C.Normal := Subgroup.normal_centralizer (H := R)
  by_cases hbot : C ≤ R
  · rintro a ⟨haX, haC⟩
    have hx : (⟨a, haX⟩ : ↥X) ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro r hr
      apply Subtype.ext
      have hrO : ((r : ↥X) : A) ∈ pCoreOf 2 X := ⟨r, hRO hr, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp haC _ hrO
    exact ⟨⟨a, haX⟩, hRO (hbot hx), rfl⟩
  · exfalso
    obtain ⟨r, x, hr, hxr⟩ := hnc
    have hCT : C.map α = ⊤ := by
      have : (C.map α).Normal := Subgroup.Normal.map hCn α hα
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map α) with h | h
      · exact absurd (fun c hc => (Subgroup.map_eq_bot_iff C).mp h hc) hbot
      · exact h
    have hp : IsPGroup 2 (↥X ⧸ C) := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective C y
      obtain ⟨c, hc, hcz⟩ : α z ∈ C.map α := by rw [hCT]; trivial
      have hk : c⁻¹ * z ∈ R := by
        rw [hR, MonoidHom.mem_ker, map_mul, map_inv, hcz, inv_mul_cancel]
      obtain ⟨j, hj⟩ := hker ⟨_, hk⟩
      refine ⟨j, ?_⟩
      have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).2 hc
      have h1 : QuotientGroup.mk' C z = QuotientGroup.mk' C (c⁻¹ * z) := by
        rw [map_mul, map_inv, hc1, inv_one, one_mul]
      have h2 : (c⁻¹ * z) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      rw [h1, ← map_pow, h2, map_one]
    have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
    have : Group.IsPerfect (↥X ⧸ C) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
    have := C48Pf.FMod.subsingleton_of_perfect_of_isPGroup hp
    have hxC : x ∈ C := by
      have h1 : QuotientGroup.mk' C x = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 h1
    exact hxr (Subgroup.mem_centralizer_iff.mp hxC r hr).symm

theorem levi_of_model [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K)) (hYK : Y ≤ K)
    {G'' : Type} [Group G''] (θ : ↥K →* G') (hθ : θ.ker ≤ Subgroup.center ↥K)
    (π : G'' →* G') {N : Subgroup G''} (hinj : Set.InjOn π (N : Set G''))
    (himg : img θ (perfectCore Y) = N.map π)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a)
    (g : ↥N →* T) (hg : Function.Surjective g) (hgker : IsPGroup 2 g.ker)
    (hnc : ∃ r x : ↥N, g r = 1 ∧ x * r ≠ r * x) :
    CharTwo (perfectCore Y) ∧ Nonempty (ModO2 (perfectCore Y) ≃* T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : perfectCore Y ≤ K := (perfectCore_le Y).trans hYK
  set ν := liftHom hXK θ π N hinj himg with hν
  have hνs := liftHom_surjective hXK θ π N hinj himg
  have hνker : IsPGroup 2 ν.ker := by
    rintro ⟨x, hx⟩
    have h1 : θ ⟨x, hXK x.2⟩ = 1 := (liftHom_eq_one_iff hXK θ π N hinj himg x).1 hx
    have hxZ : (⟨x, hXK x.2⟩ : ↥K) ∈ Subgroup.center ↥K := hθ h1
    obtain ⟨k, hk⟩ := isPGroup_center hZ ⟨_, hxZ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hk
    simpa using this
  set α := g.comp ν with hα
  have hαs : Function.Surjective α := hg.comp hνs
  have hαker : IsPGroup 2 α.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hgker ⟨ν x, hx⟩
    have hk' : ν (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    obtain ⟨l, hl⟩ := hνker ⟨x ^ 2 ^ k, hk'⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    have hl' : (x ^ 2 ^ k) ^ 2 ^ l = 1 := congrArg Subtype.val hl
    show x ^ 2 ^ (k + l) = 1
    rw [pow_add, pow_mul, hl']
  refine ⟨charTwo_of_simple (perfectCore_perfect Y) α hαs hαker ?_,
    ⟨CFSG.QuasithinUnique.Vol2Native.A312L.modO2EquivOfHom hT α hαs hαker⟩⟩
  obtain ⟨r, x, hr, hxr⟩ := hnc
  obtain ⟨r', rfl⟩ := hνs r
  obtain ⟨x', rfl⟩ := hνs x
  refine ⟨r', x', hr, fun h => hxr ?_⟩
  rw [← map_mul, ← map_mul, h]

theorem exists_noncomm_of_le_commutator {H : Type*} [Group H] {N Q : Subgroup H}
    (hQ : Q ≤ ⁅Q, N⁆) (hQ1 : Q ≠ ⊥) :
    ∃ q ∈ Q, ∃ x ∈ N, x * q ≠ q * x := by
  by_contra hcon
  push Not at hcon
  apply hQ1
  rw [eq_bot_iff]
  refine hQ.trans ?_
  rw [Subgroup.commutator_le]
  intro q hq x hx
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (hcon q hq x hx).symm

end CFSG.Quasithin.C35Levi
