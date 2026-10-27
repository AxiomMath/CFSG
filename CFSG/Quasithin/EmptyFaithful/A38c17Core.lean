module

public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3
public import CFSG.Quasithin.EmptyFaithful.A38c17Defs

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A38c15
open CFSG.Assembly.LowTwoRank

@[expose] def SylowCoreWith (p : ℕ) (E : ∀ (Y : Type) [Group Y], Prop) (Γ : Type) [Group Γ] :
    Prop :=
  ∀ M : Subgroup Γ, Odd M.index → M ≠ ⊤ →
    Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) ∨ (p = 5 ∧ E ↥(perfectCore M))

@[expose] def SylowCoreSU (p : ℕ) (Γ : Type) [Group Γ] : Prop :=
  SylowCoreWith p (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) Γ

@[expose] def SylowCorePSU (p : ℕ) (Γ : Type) [Group Γ] : Prop :=
  SylowCoreWith p (fun Y _ => IsAlt 6 Y) Γ

theorem SylowCoreWith.of_mulEquiv {p : ℕ} {E : ∀ (Y : Type) [Group Y], Prop}
    (hE : ∀ (Y Y' : Type) [Group Y] [Group Y'], (Y ≃* Y') → E Y → E Y') {Γ Γ' : Type}
    [Group Γ] [Group Γ'] [Finite Γ] [Finite Γ'] (e : Γ ≃* Γ') (h : SylowCoreWith p E Γ') :
    SylowCoreWith p E Γ := by
  intro M hodd hne
  have hodd' : Odd (M.map e.toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective M]
  have hne' : M.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  have ecore : ↥(perfectCore (M.map e.toMonoidHom)) ≃* ↥(perfectCore M) :=
    ((MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom M)).symm.trans
      ((perfectCore M).equivMapOfInjective e.toMonoidHom e.injective).symm)
  rcases h _ hodd' hne' with hs | hl | ⟨h5, hh⟩
  · left
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (MulEquiv.injective _)
  · exact Or.inr (Or.inl (IsSL2.of_mulEquiv ecore hl))
  · exact Or.inr (Or.inr ⟨h5, hE _ _ ecore hh⟩)

theorem isHat_a6_of_mulEquiv (Y Y' : Type) [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsHat Y (alternatingGroup (Fin 6))) : IsHat Y' (alternatingGroup (Fin 6)) :=
  IsHat.of_mulEquiv e h

theorem isAlt_six_of_mulEquiv (Y Y' : Type) [Group Y] [Group Y'] (e : Y ≃* Y') (h : IsAlt 6 Y) :
    IsAlt 6 Y' :=
  IsAlt.of_mulEquiv e h

theorem SylowCoreSU.of_mulEquiv {p : ℕ} {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ]
    [Finite Γ'] (e : Γ ≃* Γ') (h : SylowCoreSU p Γ') : SylowCoreSU p Γ :=
  SylowCoreWith.of_mulEquiv isHat_a6_of_mulEquiv e h

theorem SylowCorePSU.of_mulEquiv {p : ℕ} {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ]
    [Finite Γ'] (e : Γ ≃* Γ') (h : SylowCorePSU p Γ') : SylowCorePSU p Γ :=
  SylowCoreWith.of_mulEquiv isAlt_six_of_mulEquiv e h


theorem sylowCorePSU_of_quotient {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Γ : Type} [Group Γ]
    [Finite Γ] (Z : Subgroup Γ) [hZn : Z.Normal] (hZc : Z ≤ Subgroup.center Γ)
    (hZ : Nat.Coprime (Nat.card Z) (2 * p)) (hZ3 : p = 5 → Nat.card Z = 3)
    (h : ∀ M : Subgroup Γ, Odd M.index → M ≠ ⊤ →
      Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) ∨
        (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧ Z ≤ perfectCore M)) :
    SylowCorePSU p (Γ ⧸ Z) := by
  intro M' hodd hne
  let π : Γ →* Γ ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  let M : Subgroup Γ := M'.comap π
  have hMidx : M.index = M'.index := Subgroup.index_comap_of_surjective M' hπ
  have hMmap : M.map π = M' := Subgroup.map_comap_eq_self_of_surjective hπ M'
  have hMne : M ≠ ⊤ := by
    intro htop
    apply hne
    rw [← hMmap, htop, Subgroup.map_top_of_surjective _ hπ]
  rcases h M (by rwa [hMidx]) hMne with hs | hl | ⟨h5, hHat, hZM⟩
  · left
    rw [← hMmap]
    exact isSolvable_map_hom π M hs
  · right
    left
    have hinj : ∀ x ∈ perfectCore M, ∀ y ∈ perfectCore M, π x = π y → x = y := by
      intro x hx y hy hxy
      have hzm : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
      let w : ↥(perfectCore M) := ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
      have hw : w = 1 := by
        refine IsLeviBlock.eq_one_of_central hp2 (Or.inl hl) ?_ ?_
        · intro k
          apply Subtype.ext
          exact (Subgroup.mem_center_iff.mp (hZc hzm) k.1)
        · have h1 : orderOf w = orderOf (x⁻¹ * y) := (Subgroup.orderOf_coe w).symm
          rw [h1]
          exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard Z hzm) hZ
      have : x⁻¹ * y = 1 := congrArg Subtype.val hw
      exact inv_mul_eq_one.mp this
    exact IsSL2.of_mulEquiv
      ((perfectCoreMapEquiv π M hinj).trans (MulEquiv.subgroupCongr (by rw [hMmap]))) hl
  · right
    right
    refine ⟨h5, ?_⟩
    obtain ⟨-, hcard, ⟨e⟩⟩ := hHat
    set Y := perfectCore M with hY
    let ψ₀ : ↥Y →* ↥(Y.map π) := π.subgroupMap Y
    let c : ↥(Y.map π) ≃* ↥(perfectCore M') :=
      (MulEquiv.subgroupCongr (map_perfectCore π M)).trans
        (MulEquiv.subgroupCongr (by rw [hMmap]))
    let ψ : ↥Y →* ↥(perfectCore M') := c.toMonoidHom.comp ψ₀
    have hψ : Function.Surjective ψ := c.surjective.comp (π.subgroupMap_surjective Y)
    have hker : ψ.ker = Z.subgroupOf Y := by
      ext y
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hy
        have h1 : ψ₀ y = 1 := c.injective (by rw [map_one]; exact hy)
        have h2 : π y.1 = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      · intro hy
        have h2 : π y.1 = 1 := (QuotientGroup.eq_one_iff _).mpr hy
        have h1 : ψ₀ y = 1 := Subtype.ext h2
        show c (ψ₀ y) = 1
        rw [h1, map_one]
    have hle : Z.subgroupOf Y ≤ Subgroup.center ↥Y := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (hZc hy) k.1
    have hcardZ : Nat.card (Z.subgroupOf Y) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv]
      exact hZ3 h5
    have heq : Z.subgroupOf Y = Subgroup.center ↥Y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardZ])
    have e1 : (↥Y ⧸ ψ.ker) ≃* ↥(perfectCore M') :=
      QuotientGroup.quotientKerEquivOfSurjective ψ hψ
    have e2 : (↥Y ⧸ ψ.ker) ≃* (↥Y ⧸ Subgroup.center ↥Y) :=
      QuotientGroup.quotientMulEquivOfEq (by rw [hker, heq])
    exact ⟨e1.symm.trans (e2.trans e)⟩


theorem isSimpleGroup_alt_six : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt_six_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have := isSimpleGroup_alt_six
  have : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => h a b⟩⟩
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
  have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hc] at hp
  exact absurd hp (by norm_num)

theorem exists_hom_alt_six_of_isAlt {Y : Type} [Group Y] [Finite Y] (h : IsAlt 6 Y) :
    ∃ f : Y →* alternatingGroup (Fin 6), Function.Surjective f ∧ Group.IsSolvable f.ker := by
  obtain ⟨e⟩ := h
  refine ⟨e.toMonoidHom, e.surjective, ?_⟩
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [this]
  infer_instance

theorem exists_hom_alt_six_of_isHat {Y : Type} [Group Y] [Finite Y]
    (h : IsHat Y (alternatingGroup (Fin 6))) :
    ∃ f : Y →* alternatingGroup (Fin 6), Function.Surjective f ∧ Group.IsSolvable f.ker := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))).ker =
      Subgroup.center Y := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  rw [hker]
  infer_instance

theorem lFamily_core_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) {E : ∀ (Y : Type) [Group Y], Prop}
    (hE : ∀ (Y : Type) [Group Y] [Finite Y], E Y →
      ∃ f : Y →* alternatingGroup (Fin 6), Function.Surjective f ∧ Group.IsSolvable f.ker)
    (hEiso : ∀ (Y Y' : Type) [Group Y] [Group Y'], (Y ≃* Y') → E Y → E Y')
    (hc : SylowCoreWith p E X) {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T)
    (hBtop : B ≠ ⊤) : (3 < p ∧ IsSL2 p ↥B) ∨ (p = 5 ∧ E ↥B) := by
  have : Fact p.Prime := ⟨hp⟩
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hMne : B ⊔ T ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hodd : Odd (B ⊔ T).index := odd_index_of_le_isSylowTwoOf hT le_sup_right
  rcases hc (B ⊔ T) hodd hMne with hsolv | hSL2 | ⟨h5, hEM⟩
  · exfalso
    exact not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T))
        (Subgroup.inclusion_injective _))
  · left
    have hperf : Group.IsPerfect ↥(perfectCore (B ⊔ T)) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect (B ⊔ T))
    have hp3 : p ≠ 3 := ne_three_of_leviBlock (Or.inl hSL2)
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    obtain ⟨f, hf, hker⟩ := exists_hom_psl2_of_leviBlock (Or.inl hSL2)
    have hS : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2
        (ZMod p) le_rfl (Or.inr (by rw [Nat.card_zmod]; omega))
        (Or.inr (by rw [Nat.card_zmod]; omega))
    have hnab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p), a * b ≠ b * a :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        (ZMod p) (by rw [Nat.card_zmod]; omega) (by rw [Nat.card_zmod]; omega)
    have hBeq : B = perfectCore (B ⊔ T) := lFamily_eq_perfectCore hB hnab f hf hker
    exact ⟨hp5, IsSL2.of_mulEquiv (MulEquiv.subgroupCongr hBeq.symm) hSL2⟩
  · right
    obtain ⟨f, hf, hker⟩ := hE _ hEM
    have := isSimpleGroup_alt_six
    have hBeq : B = perfectCore (B ⊔ T) := lFamily_eq_perfectCore hB alt_six_nonabelian f hf hker
    exact ⟨h5, hEiso _ _ (MulEquiv.subgroupCongr hBeq.symm) hEM⟩

theorem a312For_of_sylowCoreSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] (hq : CFSG.IsQuasisimple X) (hX : IsSU3 p X) (hc : SylowCoreSU p X) :
    A312For X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = T at hTsyl
  refine A312For.of_sylow T hTsyl fun B hB hBtop => ?_
  have hLtop : IsSU3 p ↥(⊤ : Subgroup X) := IsSU3.of_mulEquiv Subgroup.topEquiv.symm hX
  rcases lFamily_core_cases hp hp2 hq
      (fun Y _ _ h => exists_hom_alt_six_of_isHat h)
      (fun Y Y' _ _ e h => IsHat.of_mulEquiv e h) hc hTsyl hB hBtop with ⟨hp5, hSL2⟩ | ⟨h5, hHat⟩
  · iterate 7 right
    left
    left
    exact ⟨false, p, hp, hp5, hSL2, Or.inr hLtop⟩
  · iterate 7 right
    left
    right
    right
    subst h5
    exact ⟨hHat, hLtop⟩

theorem a312For_of_sylowCorePSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] (hq : CFSG.IsQuasisimple X) (hX : IsPSU 3 p 1 X) (hc : SylowCorePSU p X) :
    A312For X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = T at hTsyl
  refine A312For.of_sylow T hTsyl fun B hB hBtop => ?_
  have hLtop : IsPSU 3 p 1 ↥(⊤ : Subgroup X) := IsPSU.of_mulEquiv Subgroup.topEquiv.symm hX
  rcases lFamily_core_cases hp hp2 hq
      (fun Y _ _ h => exists_hom_alt_six_of_isAlt h)
      (fun Y Y' _ _ e h => IsAlt.of_mulEquiv e h) hc hTsyl hB hBtop with ⟨hp5, hSL2⟩ | ⟨h5, hAlt⟩
  · iterate 7 right
    left
    left
    exact ⟨false, p, hp, hp5, hSL2, Or.inl hLtop⟩
  · iterate 7 right
    left
    right
    left
    subst h5
    exact ⟨hAlt, hLtop⟩


@[expose] def SU3OddIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ M : Subgroup ↥(StatedSU 3 p K), Odd M.index → IsIrreducibleSU3 M →
      M = ⊤ ∨ Group.IsSolvable ↥M ∨
        (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
          (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K) ≤ perfectCore M)

@[expose] def SU3ReducibleOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ M : Subgroup ↥(StatedSU 3 p K), Odd M.index → ¬ IsIrreducibleSU3 M →
      Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M)

theorem sylowCoreSUZ_of (hred : SU3ReducibleOdd) (hirr : SU3OddIrr) {p q : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hqp : q = p) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(StatedSU 3 q K)) (hodd : Odd M.index) (hne : M ≠ ⊤) :
    Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) ∨
      (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
        (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) ≤ perfectCore M) := by
  subst hqp
  by_cases hI : IsIrreducibleSU3 M
  · rcases hirr q hp2 K hK M hodd hI with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases hred q hp2 K hK M hodd hI with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem scalars_le_center {q : ℕ} {K : Type} [Field K] :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) ≤ Subgroup.center ↥(StatedSU 3 q K) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  obtain ⟨c, hc⟩ := hz
  have hcz : Matrix.GeneralLinearGroup.scalar (Fin 3) c = (z : GL (Fin 3) K) := hc
  have hcen : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← hcz, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hcen (k : GL (Fin 3) K)

theorem scalars_card {p : ℕ} (hp : p.Prime) {K : Type} [Field K] (hK : Nat.card K = (p ^ 1) ^ 2) :
    Nat.Coprime (Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K))) (2 * p) ∧
      (p = 5 → Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K)) = 3) := by
  have hcard := (CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2
  rw [hcard, pow_one]
  refine ⟨?_, ?_⟩
  · have hd : Nat.gcd 3 (p + 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · rw [h]
      exact Nat.coprime_one_left _
    · rw [h]
      have h3 : 3 ∣ p + 1 := by
        have := Nat.gcd_dvd_right 3 (p + 1)
        rwa [h] at this
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hdvd => ?_
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h2 | h2
      · omega
      · have hp3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h2
        subst hp3
        omega
  · rintro rfl
    norm_num

theorem famSl3oddMinus_of (hred : SU3ReducibleOdd) (hirr : SU3OddIrr) : FamSl3oddMinus := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := id hX
  have hc : SylowCoreSU p ↥(StatedSU 3 p K) := fun M hodd hne => by
    rcases sylowCoreSUZ_of hred hirr hp2 rfl hK M hodd hne with h | h | ⟨h5, hh, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h5, hh⟩)
  exact a312For_of_sylowCoreSU hp hp2 hq hX (hc.of_mulEquiv e)

theorem famU3odd_of (hred : SU3ReducibleOdd) (hirr : SU3OddIrr) : FamU3odd := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hX
  have hK' : Nat.card K = p ^ 2 := by simpa using hK
  obtain ⟨hZ, hZ5⟩ := scalars_card hp hK
  have hc : SylowCorePSU p (StatedProj (StatedSU 3 (p ^ 1) K)) :=
    sylowCorePSU_of_quotient hp2 _ scalars_le_center hZ hZ5 fun M hodd hne =>
      sylowCoreSUZ_of hred hirr hp2 (pow_one p) hK' M hodd hne
  exact a312For_of_sylowCorePSU hp hp2 hq hX (hc.of_mulEquiv e)

end CFSG.Quasithin.A38c17
