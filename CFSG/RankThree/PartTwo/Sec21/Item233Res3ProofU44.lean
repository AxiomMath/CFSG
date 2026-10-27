module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofRefl

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor permGL_mem_SU exists_conj_into_d8Tor_su d8Comb_four
  d8Vec_mem_SU mem_d8Tor_iff card_center_mulEquiv)
open U4Lines (torusD coe_torusD weyl₁ conj_weyl₁ shortSL perfectResidual_short
  nonempty_shortSL_mulEquiv_galois mapL perfectResidualEquiv)

namespace Item233Res3Proof

variable {G : Type} [Group G]

theorem exists_reflection_of_model [Finite G] {M : Type*} [Group M] {A Z : Subgroup G}
    (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 3 ^ 3) (hZc : Subgroup.center Z = ⊥)
    (hF9 : Nat.card (A ⊓ Z : Subgroup G) = 9)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (θ : M →* G) (hθZ : ∀ x, θ x ∈ Z) {T : Subgroup M} (hT3 : ∀ t ∈ T, t ^ 3 = 1)
    (hθA : ∀ t ∈ T, θ t ∈ A) (hF : ∀ f ∈ A ⊓ Z, ∃ t ∈ T, f = θ t)
    (hθinj : ∀ x y : M, x ^ 3 = 1 → y ^ 3 = 1 → θ x = θ y → x = y)
    {w : M} (hw2 : w * w = 1) (hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T)
    {x0 x1 : M} (hx0 : x0 ∈ T) (hx1 : x1 ∈ T) (hx0w : w * x0 * w⁻¹ = x0)
    (hx1w : w * x1 * w⁻¹ ≠ x1) (hx01 : x0 ≠ 1) :
    ∃ ρ ∈ starOf A Z, IsReflectionOn ρ ∧ Subgroup.zpowers (θ x0) ≤ fixedInG A ρ ∧
      Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G) =
        Z ⊓ Subgroup.centralizer ((Subgroup.zpowers (θ x0) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAZ := inf_sup_inf_centralizer_eq hA27 hZc hF9 hC3
  have hdecomp := exists_mul_of_inf_sup_eq hAZ
  set wG := θ w with hwG
  have hwGZ : wG ∈ Z := hθZ w
  have hwconj : ∀ t ∈ T, wG * θ t * wG⁻¹ = θ (w * t * w⁻¹) := by
    intro t _
    rw [hwG, map_mul, map_mul, map_inv]
  have hwC : ∀ c ∈ A ⊓ Subgroup.centralizer (Z : Set G), wG * c * wG⁻¹ = c := by
    intro c hc
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 wG hwGZ
    rw [h1, mul_inv_cancel_right]
  have hwN : wG ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    obtain ⟨f, hf, c, hc, rfl⟩ := hdecomp x hx
    obtain ⟨t, ht, rfl⟩ := hF f hf
    have e : wG * (θ t * c) * wG⁻¹ = (wG * θ t * wG⁻¹) * (wG * c * wG⁻¹) := by group
    rw [e, hwconj t ht, hwC c hc]
    exact A.mul_mem (hθA _ (hwT t ht)) (Subgroup.mem_inf.mp hc).1
  set ρ : MulAut A := A.normalizerMonoidHom ⟨wG, hwN⟩ with hρdef
  have hρapp : ∀ x : A, ((ρ x : A) : G) = wG * x * wG⁻¹ := fun x => rfl
  have hρZ : ρ ∈ starOf A Z := ⟨⟨wG, hwN⟩, Subgroup.mem_subgroupOf.mpr hwGZ, rfl⟩
  have hw2G : wG * wG = 1 := by rw [hwG, ← map_mul, hw2, map_one]
  have hρ2 : ρ * ρ = 1 := by
    ext x
    change ((ρ (ρ x) : A) : G) = x
    rw [hρapp, hρapp]
    calc wG * (wG * (x : G) * wG⁻¹) * wG⁻¹ = (wG * wG) * x * (wG * wG)⁻¹ := by group
      _ = x := by rw [hw2G]; group
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hx1A : θ x1 ∈ A := hθA _ hx1
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨_, hx1A⟩ : A) : G)) h
    simp only [MulAut.one_apply] at h1
    rw [hρapp, hwconj x1 hx1] at h1
    exact hx1w (hθinj _ _ (hT3 _ (hwT x1 hx1)) (hT3 _ hx1) h1)
  have hρord : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq, hρ2]) hρ1
  set y0 := θ x0 with hy0
  have hy0A : y0 ∈ A := hθA _ hx0
  have hy0Z : y0 ∈ Z := hθZ _
  have hy0fix : wG * y0 * wG⁻¹ = y0 := by rw [hy0, hwconj x0 hx0, hx0w]
  have hy01 : y0 ≠ 1 := by
    intro h
    apply hx01
    exact hθinj _ _ (hT3 _ hx0) (one_pow 3) (by rw [← hy0, h, map_one])
  set C := A ⊓ Subgroup.centralizer (Z : Set G) with hCdef
  set B := fixedInG A ρ with hBdef
  have hmemB : ∀ x (hx : x ∈ A), wG * x * wG⁻¹ = x → x ∈ B := by
    intro x hx h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf]
    exact Subtype.ext h
  set J := Subgroup.zpowers y0 ⊔ C with hJdef
  have hJB : J ≤ B := sup_le (Subgroup.zpowers_le.mpr (hmemB y0 hy0A hy0fix))
    fun c hc => hmemB c (Subgroup.mem_inf.mp hc).1 (hwC c hc)
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBne : B ≠ A := by
    intro h
    apply hρ1
    ext x
    have hx : (x : G) ∈ B := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx', MulAut.one_apply]
    exact congrArg Subtype.val ((mem_fixedSubgroupOf ρ y).mp hy)
  have hy03 : Nat.card (Subgroup.zpowers y0) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 y0 hy0A) hy01
  have hCZ : ¬ C ≤ Subgroup.zpowers y0 := by
    intro h
    have h1 : C ≤ Z ⊓ Subgroup.centralizer (Z : Set G) :=
      le_inf (h.trans (Subgroup.zpowers_le.mpr hy0Z)) inf_le_right
    rw [inf_centralizer_self_eq_bot hZc] at h1
    have h2 := Subgroup.card_le_of_le h1
    rw [hC3, Subgroup.card_bot] at h2
    omega
  have hJ3 : 3 < Nat.card J := by
    rw [← hy03]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hCZ (h ▸ le_sup_right))
  have hB27 : Nat.card B < 27 := by
    have := Subgroup.card_lt_of_lt (lt_of_le_of_ne hBA hBne)
    rwa [hA27] at this
  have hJdvd : Nat.card J ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le (hJB.trans hBA)
  have hBdvd : Nat.card B ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le hBA
  have hJBle := Subgroup.card_le_of_le hJB
  have hB9 : Nat.card B = 9 := by
    rcases eq_of_dvd_twentySeven hJdvd with h | h | h | h <;>
      rcases eq_of_dvd_twentySeven hBdvd with h' | h' | h' | h' <;> omega
  have hJeq : J = B := Subgroup.eq_of_le_of_card_ge hJB (by
    rw [hB9]
    rcases eq_of_dvd_twentySeven hJdvd with h | h | h | h <;> omega)
  have hfix9 : Nat.card (fixedSubgroupOf ρ) = 9 := by
    rw [← hB9, hBdef, fixedInG, Subgroup.card_map_of_injective A.subtype_injective]
  have hcomm3 : Nat.card (commOf ρ) = 3 := by
    have h := card_eq_card_fixed_mul_card_commOf hAc ρ
    rw [hA27, hfix9] at h
    omega
  refine ⟨ρ, hρZ, ⟨hρord, hcomm3⟩, le_sup_left.trans hJB, ?_⟩
  change Z ⊓ Subgroup.centralizer (B : Set G) = _
  rw [← hJeq, hJdef, inf_centralizer_sup_eq (inf_le_right : C ≤ _)]

abbrev SU44 : Type := ↥(SU σ16 4)

@[expose] noncomputable def tD (v : D8Mod 3 K16) : SU44 :=
  ⟨torusD v, d8Vec_mem_SU (Or.inl rfl) d8Comb_four σ16 σ16_mu3 v⟩

noncomputable abbrev T44 : Subgroup SU44 := (d8Tor 3 K16 4).subgroupOf (SU σ16 4)

theorem tD_mem (v : D8Mod 3 K16) : tD v ∈ T44 := ⟨v, rfl⟩

theorem exists_tD {t : SU44} (ht : t ∈ T44) : ∃ v, t = tD v := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
  exact ⟨v, Subtype.ext hv.symm⟩

theorem tD_pow_three (v : D8Mod 3 K16) : tD v ^ 3 = 1 := by
  have h : v ^ 3 = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card (D8Mod 3 K16) = 9 := by
      rw [Nat.card_prod, card_mu3]
    have h9 := pow_card_eq_one' (G := D8Mod 3 K16) (x := v)
    rw [hcard] at h9
    have h1 : v.1 ^ 3 = 1 := by
      have := v.1.2
      exact Subtype.ext ((mem_rootsOfUnity 3 _).mp this)
    have h2 : v.2 ^ 3 = 1 := by
      have := v.2.2
      exact Subtype.ext ((mem_rootsOfUnity 3 _).mp this)
    exact Prod.ext h1 h2
  apply Subtype.ext
  change torusD v ^ 3 = 1
  rw [← map_pow, h, map_one]

theorem card_T44_le : Nat.card T44 ≤ 9 := by
  have hsurj : Function.Surjective (fun v : D8Mod 3 K16 => (⟨tD v, tD_mem v⟩ : T44)) := by
    rintro ⟨t, ht⟩
    obtain ⟨v, rfl⟩ := exists_tD ht
    exact ⟨v, rfl⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, card_mu3] at h

@[expose] noncomputable def w44 : SU44 := ⟨weyl₁, permGL_mem_SU σ16 _ (by decide)⟩

theorem w44_conj (v : D8Mod 3 K16) : w44 * tD v * w44⁻¹ = tD (v.2, v.1) :=
  Subtype.ext (conj_weyl₁ v)

theorem w44_mul_self : w44 * w44 = 1 := by
  apply Subtype.ext
  change weyl₁ * weyl₁ = (1 : GL (Fin 4) K16)
  rw [weyl₁, ← map_mul, show (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) *
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 1 by decide, map_one]

theorem tD_injective {v v' : D8Mod 3 K16} (h : tD v = tD v') : v = v' := by
  have h' := congrArg (fun x : SU44 => ((x : GL (Fin 4) K16) : Matrix (Fin 4) (Fin 4) K16)) h
  simp only [tD, coe_torusD] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  exact Prod.ext (Subtype.ext (Units.ext h0)) (Subtype.ext (Units.ext h1))

theorem exists_model_U44 [Finite G] {A Z : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G))
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (eZ : Z ≃* projSU 4 2 2) :
    Subgroup.center Z = ⊥ ∧ Nat.card (A ⊓ Z : Subgroup G) = 9 ∧
      ∃ e : Z ≃* SU44, (∀ t ∈ T44, ((e.symm t : Z) : G) ∈ A) ∧
        ∀ f (hf : f ∈ A ⊓ Z), e ⟨f, (Subgroup.mem_inf.mp hf).2⟩ ∈ T44 := by
  have hAe : IsElemAbelian 3 A := hA.prop
  have hZc : Subgroup.center Z = ⊥ := by
    have h := card_center_mulEquiv eZ
    rw [center_U44, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have h27 : ¬ 27 ∣ Nat.card Z := by
    rw [Nat.card_congr eZ.toEquiv]
    exact not_twentySeven_dvd_card_U44
  have hF9 := card_inf_eq_nine hA hA27 hAN hZc (cubeInner_U44.of_mulEquiv eZ) hC3 h27
  refine ⟨hZc, hF9, ?_⟩
  obtain ⟨e₄⟩ := U4Lines.nonempty_projSU_mulEquiv_SU 2 (by norm_num)
  set e₀ : Z ≃* SU44 := eZ.trans e₄
  set X : Subgroup SU44 := ((A ⊓ Z).subgroupOf Z).map e₀.toMonoidHom with hX
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ 3 = 1 := Subtype.ext (by
      simpa using hAe.2 _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1)
    rw [this, map_one]
  have hX9 : Nat.card X = 9 := by
    rw [hX, Subgroup.card_map_of_injective e₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ Z ≤ Z)).toEquiv, hF9]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four card_K16
    Nat.prime_three (by norm_num) (by norm_num) X hX3
  have hXT : X.map (MulAut.conj g).toMonoidHom = T44 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hX9]
      exact card_T44_le
  set e : Z ≃* SU44 := e₀.trans (MulAut.conj g)
  refine ⟨e, ?_, ?_⟩
  · intro t ht
    rw [← hXT] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : e.symm ((MulAut.conj g).toMonoidHom (e₀.toMonoidHom y)) = y := by
      change e.symm (e y) = y
      exact e.symm_apply_apply y
    rw [h1]
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
  · intro f hf
    rw [← hXT]
    exact ⟨e₀ ⟨f, (Subgroup.mem_inf.mp hf).2⟩, ⟨⟨f, (Subgroup.mem_inf.mp hf).2⟩,
      Subgroup.mem_subgroupOf.mpr hf, rfl⟩, rfl⟩

theorem u44ShortRoot :
    ∀ (G : Type) [Group G] [Finite G] (A Z : Subgroup G),
      Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
      A ≤ Subgroup.normalizer (Z : Set G) →
      Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3 →
      Nonempty (Z ≃* projSU 4 2 2) →
      ∃ ρ ∈ starOf A Z, IsReflectionOn ρ ∧
        Nonempty (inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G)) ≃*
          projSL 2 (GaloisField 2 4)) := by
  intro G _ _ A Z hA hA27 hAN hC3 ⟨eZ⟩
  have hAe : IsElemAbelian 3 A := hA.prop
  obtain ⟨hZc, hF9, e, hT1, hT2⟩ := exists_model_U44 hA hA27 hAN hC3 eZ
  set θ : SU44 →* G := Z.subtype.comp e.symm.toMonoidHom with hθ
  have hθZ : ∀ x, θ x ∈ Z := fun x => (e.symm x).2
  have hθinj : ∀ x y : SU44, x ^ 3 = 1 → y ^ 3 = 1 → θ x = θ y → x = y := fun x y _ _ h =>
    e.symm.injective (Subtype.ext h)
  have hF : ∀ f ∈ A ⊓ Z, ∃ t ∈ T44, f = θ t := by
    intro f hf
    refine ⟨e ⟨f, (Subgroup.mem_inf.mp hf).2⟩, hT2 f hf, ?_⟩
    change f = ((e.symm (e ⟨f, _⟩) : Z) : G)
    rw [MulEquiv.symm_apply_apply]
  have hT3 : ∀ t ∈ T44, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, rfl⟩ := exists_tD ht
    exact tD_pow_three v
  have hwT : ∀ t ∈ T44, w44 * t * w44⁻¹ ∈ T44 := by
    intro t ht
    obtain ⟨v, rfl⟩ := exists_tD ht
    rw [w44_conj]
    exact tD_mem _
  obtain ⟨ζ, hζ⟩ := exists_mu3_ne_one
  have hx0w : w44 * tD (ζ, ζ) * w44⁻¹ = tD (ζ, ζ) := w44_conj _
  have hx1w : w44 * tD (ζ, 1) * w44⁻¹ ≠ tD (ζ, 1) := by
    rw [w44_conj]
    intro h
    have h1 : (1 : rootsOfUnity 3 K16) = ζ := congrArg Prod.fst (tD_injective h)
    exact hζ h1.symm
  have hx01 : tD (ζ, ζ) ≠ 1 := by
    intro h
    have h1 : tD (ζ, ζ) = tD 1 := by
      rw [h]
      exact Subtype.ext (by simp [tD])
    have := tD_injective h1
    exact hζ (congrArg Prod.fst this)
  obtain ⟨ρ, hρZ, hρ, -, hcent⟩ := exists_reflection_of_model hAe hA27 hZc hF9 hC3 θ hθZ hT3
    hT1 hF hθinj w44_mul_self hwT (tD_mem (ζ, ζ)) (tD_mem (ζ, 1)) hx0w hx1w hx01
  refine ⟨ρ, hρZ, hρ, ?_⟩
  have hx0Z : θ (tD (ζ, ζ)) ∈ Z := hθZ _
  have hℓ : Subgroup.zpowers (θ (tD (ζ, ζ))) ≤ Z := Subgroup.zpowers_le.mpr hx0Z
  have e₁ := perfectResidualEquiv e hℓ
  have hsub : (Subgroup.zpowers (θ (tD (ζ, ζ)))).subgroupOf Z =
      Subgroup.zpowers ⟨θ (tD (ζ, ζ)), hx0Z⟩ := by
    apply Subgroup.map_injective Z.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hℓ, MonoidHom.map_zpowers]
    rfl
  have hx0e : ((e ⟨θ (tD (ζ, ζ)), hx0Z⟩ : SU44) : GL (Fin 4) K16) = torusD (ζ, ζ) := by
    have h1 : (⟨θ (tD (ζ, ζ)), hx0Z⟩ : Z) = e.symm (tD (ζ, ζ)) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
    rfl
  have hmapL : mapL e (Subgroup.zpowers (θ (tD (ζ, ζ)))) = Subgroup.zpowers (torusD (ζ, ζ)) := by
    rw [mapL, hsub, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hx0e
  rw [hmapL] at e₁
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ16 (b := 2) (by norm_num) card_K16
  have hperf : ⁅shortSL σ16, shortSL σ16⁆ = shortSL σ16 :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL (by norm_num) eS)
  have hζ1 : ((ζ : K16ˣ) : K16) ≠ (((ζ : K16ˣ)⁻¹ : K16ˣ) : K16) := by
    intro h
    have h' : (ζ : K16ˣ) = (ζ : K16ˣ)⁻¹ := Units.ext h
    have h3 : (ζ : K16ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ζ.2
    have h2 : (ζ : K16ˣ) * ζ = 1 := by
      calc (ζ : K16ˣ) * ζ = ζ * (ζ : K16ˣ)⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel _
    apply hζ
    apply Subtype.ext
    calc (ζ : K16ˣ) = (ζ : K16ˣ) ^ 3 * ((ζ : K16ˣ) * ζ)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have ht : ((torusD ((ζ, ζ) : D8Mod 3 K16) : GL (Fin 4) K16) : Matrix (Fin 4) (Fin 4) K16) =
      diagonal ![((ζ : K16ˣ) : K16), ((ζ : K16ˣ) : K16), (((ζ : K16ˣ)⁻¹ : K16ˣ) : K16),
        (((ζ : K16ˣ)⁻¹ : K16ˣ) : K16)] := by
    rw [coe_torusD]
  rw [perfectResidual_short σ16 σ16_involutive ht hζ1 hperf] at e₁
  have hcent' : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G)) =
      inSubgroup perfectResidual
        (Z ⊓ Subgroup.centralizer ((Subgroup.zpowers (θ (tD (ζ, ζ))) : Subgroup G) : Set G)) := by
    rw [hcent]
  exact ⟨(MulEquiv.subgroupCongr hcent').trans (e₁.trans eS)⟩

end Item233Res3Proof

open Item233Res3Proof

theorem item233ZNotU44_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h2130 : Item2130)
    (h222 : Item222) (hKW : KOfWellDefinedAll) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
        IsEmpty (Z ≃* projSU 4 2 2) := by
  intro G _ _ A E U c L hpair hconc hA27 φ hφ Z hZ hKZ hR
  refine ⟨fun eZ => ?_⟩
  have hK := hKW G A E U c L hpair
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  obtain ⟨z, hzA, hz1, hZz⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hAN : A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hzA hz1
      Z hZz
  have hC3 := Item221ResProof.card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hZ
  obtain ⟨ρ, hρZ, hρ, ⟨eP⟩⟩ := u44ShortRoot G A Z hAmax hA27 hAN hC3 ⟨eZ⟩
  have hρD : ρ ∈ dStar A := hR ρ hρZ hρ
  obtain ⟨eK⟩ := Item222Proof.nonempty_kOf_mulEquiv_projSL hAF hzA hZz hρZ hρ.1
    (by norm_num : 2 ≤ 4) eP
  have hKI : kOf A ρ ≤ iGroup A := kOf_le_iGroup hρD
  have hKC : kOf A ρ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) :=
    (kOf_le_kZero hK hρD).trans (kZero_le_centralizer A ρ)
  have hKp : Group.IsPerfect (kOf A ρ) := isPerfect_of_mulEquiv_projSL (by norm_num) eK
  have hAI : A ≤ iGroup A := le_iGroup h2130 h222 hpair hK
  have hBA : fixedInG A ρ ≤ A := Subgroup.map_subtype_le _
  have hB9 := Item228ResProof.card_fixedInG_eq_nine hAc hA27 hρ
  have hI : Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∨
      Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) := by
    rcases hconc with ⟨-, -, h81⟩ | ⟨hI, -, -⟩ | ⟨hI, -, -⟩
    · rw [hA27] at h81
      norm_num at h81
    · exact Or.inl hI
    · exact Or.inr hI
  have h60 := terminalRootSmall G (iGroup A) A (fixedInG A ρ) (kOf A ρ) hAI hAe hA27 hI hBA hB9
    hKI hKC hKp
  rw [Nat.card_congr eK.toEquiv, Item228ResProof.card_projSL_two_sixteen] at h60
  norm_num at h60

end CFSG.RankThree.PartTwo.Sec21
