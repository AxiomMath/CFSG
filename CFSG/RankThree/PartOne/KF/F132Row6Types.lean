module

public import CFSG.RankThree.PartOne.KF.F132Row5
public import CFSG.RankThree.PartOne.KF.F132Row6
public import CFSG.RankThree.PartOne.KF.F132LayerData
public import CFSG.RankThree.PartOne.KF.F132KZeroQs
public import CFSG.RankThree.PartOne.KF.R6LeviA

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Engine

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {c : G} {L E F : Subgroup G}

theorem exists_weylE_reflection (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (i : ZMod 4) :
    ∃ (t : MulAut E) (ht : t ∈ torusImage E L), IsAutReflection p E t ∧
      weylE S R hp hp2 hζ ⟨t, ht⟩ = DihedralGroup.sr i := by
  set γ : ↥(torusImage E L) := (weylE S R hp hp2 hζ).symm (DihedralGroup.sr i) with hγ
  have hw : weylE S R hp hp2 hζ γ = DihedralGroup.sr i := (weylE S R hp hp2 hζ).apply_symm_apply _
  exact ⟨(γ : MulAut E), γ.2, (isAutReflection_weylE_iff S R hp hp2 hζ γ).2 ⟨i, hw⟩, hw⟩

theorem fix_of_weylE_fix (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (γ : ↥(torusImage E L)) (d : D8Mod p K)
    (hd : d8Act (weylE S R hp hp2 hζ γ) d = d) :
    ((((γ : MulAut E) ⟨((S.tor d : F) : G), R.F_le_E (S.tor d).2⟩ : E)) : G) =
      ((S.tor d : F) : G) := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage γ.2
  have hxF : x ∈ Subgroup.normalizer (F : Set G) := R.inf_normalizer_le ⟨hxL, hxE⟩
  have hγ : γ = ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr ⟨x, hxL, hxE, rfl⟩⟩ :=
    Subtype.ext hx
  have hA := actF_weylE S R hp hp2 hζ hxL hxE hxF
  rw [← hγ] at hA
  have h1 : S.actF (weylE S R hp hp2 hζ γ) (S.tor d) = S.tor d := by
    rw [S.actF_apply, hd]
  rw [hA] at h1
  have h2 := congrArg (fun e : F => (e : G)) h1
  have h3 : x * ((S.tor d : F) : G) * x⁻¹ = ((S.tor d : F) : G) := h2
  rw [hx]
  exact h3

end Engine

section Exceptional

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {c : G} {L E F : Subgroup G}

theorem kExceptional_conj_of_normalizer {f : ℕ} {t : MulAut E}
    (h : kExceptional p (kZero p E t) f) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    kExceptional p (kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹)) f := by
  rw [kZero_conj p t hw]
  exact (Equivariance.kExceptional_conjBy_iff p f w (kZero p E t)).2 h

variable (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime) (hp2 : p ≠ 2)
  (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)

include S R hp hp2 hζ in
theorem kExceptional_of_parity {g : ℕ} {t₀ t : MulAut E} {ht₀ : t₀ ∈ torusImage E L}
    {ht : t ∈ torusImage E L} {i₀ i : ZMod 4}
    (h₀ : weylE S R hp hp2 hζ ⟨t₀, ht₀⟩ = DihedralGroup.sr i₀)
    (h : weylE S R hp hp2 hζ ⟨t, ht⟩ = DihedralGroup.sr i) (hpar : i₀.val % 2 = i.val % 2)
    (hK : kExceptional p (kZero p E t₀) g) : kExceptional p (kZero p E t) g := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conj_of_parity S R hp hp2 hζ h₀ h hpar
  rw [hx]
  exact kExceptional_conj_of_normalizer hK hxE

end Exceptional

section Layer

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem statedModel_psu_three_of_layer {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {X Y : Type} [Group X] [Group Y] {D : Subgroup Y}
    {ι : ↥(SU (unitaryInvolution K 2 f) 3) →* Y} (hι : Function.Injective ι) (hD : D = ι.range)
    (e : X ⧸ Subgroup.center X ≃* ↥D ⧸ Subgroup.center ↥D) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f := by
  obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hD)
  obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv (MonoidHom.ofInjective hι).symm
  exact Equivariance.statedClassicalModel_of_mulEquiv (e.trans (e₃.trans e₄)).symm
    (statedModel_SU_three hK hf)

theorem row6_layerA (h : Sec12Hyp G p A c L E) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {P : Type} [Group P] [Finite P] (ε : ↥L →* P)
    (q : ↥(SU (unitaryInvolution K 2 f) 5) →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 (unitaryInvolution K 2 f) p).map q)
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L)
    (hb : q (bA6 (unitaryInvolution K 2 f) ζ (hfix ζ hζ.pow_eq_one)) = ε ⟨x, hxL⟩) :
    x ≠ 1 ∧ IsQuasisimple ↥(kLayer L x) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kLayer L x)) ∧
      Nat.card ↥(A ⊓ kLayer L x) = p ∧
      StatedClassicalModel (↥(kLayer L x) ⧸ Subgroup.center ↥(kLayer L x)) .PSU 3 2 f ∧
      ((kLayer L x).subgroupOf L).map ε =
        (su3Emb (unitaryInvolution K 2 f)).range.map q := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : unitaryInvolution K 2 f (ζ : K) = ζ := hfix ζ hζp
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt (by norm_num)
    omega
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hbmem : bA6 (unitaryInvolution K 2 f) ζ hσζ ∈ torus6 (unitaryInvolution K 2 f) p :=
    mem_torus6_iff.2 ⟨1, ζ, one_pow p, hζp, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : q (bA6 (unitaryInvolution K 2 f) ζ hσζ) = q 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    have hbMne : bA6 (unitaryInvolution K 2 f) ζ hσζ ≠ 1 := by
      intro h1'
      have := congrArg (fun x : ↥(SU (unitaryInvolution K 2 f) 5) => gu5 x 1 1) h1'
      simp only [gu5_one, Matrix.one_apply_eq] at this
      have h11 : gu5 (bA6 (unitaryInvolution K 2 f) ζ hσζ) 1 1 = (ζ : K) := by
        show ((diagU (dvec5 1 ζ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 1 = _
        simp [diagU_val, dvec5]
      exact hζ1 (Units.ext (by rw [← h11]; exact this))
    exact hbMne (hq.eq_of_map_eq (torus6_pow_eq_one hbmem) (one_pow p) h2)
  have hKM := perfectResidual_centralizer_bA6 hK (by omega) hσζ hζ1 hζ2
  have hKq := isQuasisimple_perfectResidual_centralizer_bA6 hK (by omega) hσζ hζ1 hζ2
  have hKz : ¬ p ∣ Nat.card (Subgroup.center ↥(inSubgroup perfectResidual (Subgroup.centralizer
      ({bA6 (unitaryInvolution K 2 f) ζ hσζ} :
        Set ↥(SU (unitaryInvolution K 2 f) 5))))) := by
    rw [hKM]
    exact not_dvd_card_center_range_su3Emb hK (by omega) (by omega)
  have hTK : Nat.card ↥(torus6 (unitaryInvolution K 2 f) p ⊓ inSubgroup perfectResidual
      (Subgroup.centralizer ({bA6 (unitaryInvolution K 2 f) ζ hσζ} :
        Set ↥(SU (unitaryInvolution K 2 f) 5)))) = p := by
    rw [hKM]
    exact card_torus6_inf_range_su3 hp.pos hfix hζex
  obtain ⟨K₀, hK₀eq, hqs, hz', hAK, ⟨e⟩, -⟩ := layerData_of_cover hp h.A_elem ε q hε hq hxA hxL
    (torus6_pow_eq_one hbmem) hb.symm (fun t ht => torus6_pow_eq_one ht) hAT hKq hKz hTK
  subst hK₀eq
  have := h.A_elem
  have hbp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hxA
  refine ⟨hx1, hqs, hz', hAK, ?_, ?_⟩
  · exact statedModel_psu_three_of_layer hK (by omega) (su3Emb_injective _) hKM e
  · rw [map_kLayer_eq_of_cover ε q hε hq hxL hbp (torus6_pow_eq_one hbmem) hb.symm hKq, hKM]

end Layer

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row6_main_ext (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) 5)),
      (m : GL (Fin 5) K) = diagU (d8Vec 5 d) →
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = suQ 5 hK m) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L →
      kExceptional p (kZero p E s) f ∨ KFAt p E (2 * f) s) ∧
      ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
        r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ kExceptional p (kZero p E r₀) f ∧
        KFAt p E (2 * f) r₁ ∧
        ((kZero p E r₀).subgroupOf L).map ε =
          (su3Emb (unitaryInvolution K 2 f)).range.map (suQ 5 hK) ∧
        ((kZero p E r₁).subgroupOf L).map ε =
          (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
            (suQ 5 hK) ∧
        (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
          s' ∈ torusImage E L → orderOf (s * s') = 4 →
            ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
              (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
              (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹)) ∧
        (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
          ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
            s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) ∧
        (kZero p E r₀ ≤ L ∧ autMovedInG E r₀ ≤ kZero p E r₀ ∧
          ∃ (z : G) (hzE : z ∈ E), z ∈ kZero p E r₀ ∧ orderOf z = p ∧
            E ⊓ kZero p E r₀ = Subgroup.zpowers z ∧ ((r₀ ⟨z, hzE⟩ : E) : G) = z⁻¹ ∧
            E = autFixedInG E r₀ ⊔ Subgroup.zpowers z) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by omega
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : σ (ζ : K) = ζ := hfix ζ hζp
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hζ1 (congrArg Subtype.val h1)
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h1)
  set d₀ : D8Mod p K := ((1 : rootsOfUnity p K), z) with hd₀
  set d₁ : D8Mod p K := (z, z) with hd₁
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  set x₁ : G := ((S.tor d₁ : ↥(E ⊓ L)) : G) with hx₁
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hx₁E : x₁ ∈ E := (S.tor d₁).2.1
  have hx₁L : x₁ ∈ L := (S.tor d₁).2.2
  have hm₀ : ((bA6 σ ζ hσζ : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (d8Vec 5 d₀) := by
    rw [d8Vec_five]
    rfl
  have hm₁ : ((b6 σ ζ hσζ : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (d8Vec 5 d₁) := by
    rw [d8Vec_five]
    rfl
  have hb₀ : suQ 5 hK (bA6 σ ζ hσζ) = ε ⟨x₀, hx₀L⟩ := (hS d₀ _ hm₀).symm
  have hb₁ : suQ 5 hK (b6 σ ζ hσζ) = ε ⟨x₁, hx₁L⟩ := (hS d₁ _ hm₁).symm
  obtain ⟨hx₀1, hqs, hz', hAK, hmodA, himgA⟩ := row6_layerA h hf3 hK hfix hζ ε (suQ 5 hK) hε hq hAT
    (hEA ▸ hx₀E) hx₀L hb₀
  obtain ⟨t₀, ht₀L, hr₀, hw₀⟩ := exists_weylE_reflection S R hp hp2 hζex 0
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hfix₀ := fix_of_weylE_fix S R hp hp2 hζex ⟨t₀, ht₀L⟩ d₀
    (by rw [hw₀, d8Act_sr_zero, inv_one])
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hAK' : Nat.card ↥(E ⊓ kLayer L x₀) = p := by rw [hEA]; exact hAK
  have hK1 := kZero_eq_of_layer_qs h hE3 h.L_le_centralizer hcL hr₀ ht₀L (hF13.reflection t₀ hrs₀)
    hx₀E hx₀L hx₀1 hfix₀ hAK' hqs hz'
  have hK0 : kZero p E t₀ = kLayer L x₀ := hK1.1
  have hex₀ : kExceptional p (kZero p E t₀) f := ⟨hf1, hpq, by rw [hK0]; exact hmodA⟩
  obtain ⟨t₁, ht₁L, hr₁, hfix₁, hKF₁, hmap₁⟩ := row6_classB hGA h hEA hcL hA hf3 σ hσσ hK' hfix hζ
    ε (suQ 5 hK) hε hq hAT (hEA ▸ hx₁E) hx₁L hb₁
  have hW₁ : weylE S R hp hp2 hζex ⟨t₁, ht₁L⟩ = DihedralGroup.sr 3 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₁L hr₁ (d := d₁) (i₀ := 3) (hfix₁ hx₁E)
      (fun i hi => eq_three_of_sr_fix_same hz2 hi)
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hv0 : (0 : ZMod 4).val = 0 := rfl
  have hv3 : (3 : ZMod 4).val = 3 := rfl
  have hall : ∀ s ∈ reflectionSet p E, s ∈ torusImage E L →
      kExceptional p (kZero p E s) f ∨ KFAt p E (2 * f) s := by
    intro s hs hsL
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact Or.inl (kExceptional_of_parity S R hp hp2 hζex hw₀ hi (by rw [hv0]; omega) hex₀)
    · exact Or.inr (kfAt_of_parity S R hp hp2 hζex hW₁ hi (by rw [hv3]; omega) hKF₁)
  refine ⟨hall, t₀, t₁, hrs₀, ht₀L, hrs₁, ht₁L, ?_, hex₀, hKF₁, ?_, hmap₁, ?_, ?_, ?_⟩
  · have h1 : orderOf ((⟨t₀, ht₀L⟩ : ↥(torusImage E L)) * ⟨t₁, ht₁L⟩) = orderOf (t₀ * t₁) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [← h1, ← MulEquiv.orderOf_eq (weylE S R hp hp2 hζex), map_mul, hw₀, hW₁,
      DihedralGroup.sr_mul_sr, DihedralGroup.orderOf_r]
    decide
  · rw [hK0]
    exact himgA
  · intro s hs hsL s' hs' hs'L hord
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    obtain ⟨j, hj⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s', hs'L⟩).1 hs'.1
    have hne := parity_ne_of_pair S R hp hp2 hζex hi hj hord
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hw₀ hW₁ hi hj
        (by rw [hv0]; omega) (by rw [hv3]; omega) hne
      exact ⟨x, hxL, hxE, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₁ hw₀ hi hj
        (by rw [hv3]; omega) (by rw [hv0]; omega) hne
      exact ⟨x, hxL, hxE, Or.inr ⟨h1, h2⟩⟩
  · intro s hs hsL hexc
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact exists_conj_of_parity S R hp hp2 hζex hw₀ hi (by rw [hv0]; omega)
    · exfalso
      have hKFs := kfAt_of_parity S R hp hp2 hζex hW₁ hi (by rw [hv3]; omega) hKF₁
      exact hKFs.1 ⟨f, hexc⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hK0]
      exact (Subgroup.map_subtype_le _ : kLayer L x₀ ≤ L ⊓ Subgroup.centralizer ({x₀} : Set G)).trans
        inf_le_left
    · rw [hK0]
      exact hK1.2.1
    · obtain ⟨z, hzE, hzK, hzord, hEK, htz, hEeq⟩ := hK1.2.2
      refine ⟨z, hzE, ?_, hzord, ?_, htz, hEeq⟩
      · rw [hK0]
        exact hzK
      · rw [hK0]
        exact hEK

theorem row6_main (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) 5)),
      (m : GL (Fin 5) K) = diagU (d8Vec 5 d) →
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = suQ 5 hK m) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L →
      kExceptional p (kZero p E s) f ∨ KFAt p E (2 * f) s) ∧
      ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
        r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ kExceptional p (kZero p E r₀) f ∧
        KFAt p E (2 * f) r₁ ∧
        ((kZero p E r₀).subgroupOf L).map ε =
          (su3Emb (unitaryInvolution K 2 f)).range.map (suQ 5 hK) ∧
        ((kZero p E r₁).subgroupOf L).map ε =
          (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
            (suQ 5 hK) ∧
        ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
          s' ∈ torusImage E L → orderOf (s * s') = 4 →
            ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
              (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
              (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  obtain ⟨hall, r₀, r₁, a1, a2, a3, a4, a5, a6, a7, a8, a9, hpairs, -, -⟩ :=
    row6_main_ext hGA h hF13 hEA hG hf3 hpq hK hfix hζ ε hε hq hAT S hS
  exact ⟨hall, r₀, r₁, a1, a2, a3, a4, a5, a6, a7, a8, a9, hpairs⟩

theorem kf132Row6_frame (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L →
      kExceptional p (kZero p E s) f ∨ KFAt p E (2 * f) s) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ f) ^ 2)
        (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)), IsCentralPQuot p ε ∧
        ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
          r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ kExceptional p (kZero p E r₀) f ∧
          KFAt p E (2 * f) r₁ ∧
          ((kZero p E r₀).subgroupOf L).map ε =
            (su3Emb (unitaryInvolution K 2 f)).range.map (suQ 5 hK) ∧
          ((kZero p E r₁).subgroupOf L).map ε =
            (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
              (suQ 5 hK) ∧
          ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
            s' ∈ torusImage E L → orderOf (s * s') = 4 →
              ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
                (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
                (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_row6 hGA hF hpq hmod
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of (n := 5) (Or.inr rfl) d8Comb_five hcore hf1 hpq hmod
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = u := by rw [h2, one_mul]
    rw [this]
  have hAT : ((A ⊓ L).subgroupOf L).map ε =
      (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := rowSU_S (n := 5) (Or.inr rfl) d8Comb_five d8Comb2_five hp hp2 hK hf1 hpq
    ⟨ζ₀, hζ₀⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  obtain ⟨hall, hrest⟩ := row6_main hGA h hF13 hEA hG hf3 hpq hK hfix hζ₀ ε hε hq hAT S hS
  exact ⟨hall, K, hKf, hKfin, hchar, hK, ε, hε, hrest⟩

theorem kf132Row6_dichotomy (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f)
    {s s' : MulAut E} (hs : s ∈ reflectionSet p E) (hsL : s ∈ torusImage E L)
    (hs' : s' ∈ reflectionSet p E) (hs'L : s' ∈ torusImage E L) (hord : orderOf (s * s') = 4) :
    (kExceptional p (kZero p E s) f ∧ KFAt p E (2 * f) s') ∨
      (KFAt p E (2 * f) s ∧ kExceptional p (kZero p E s') f) := by
  obtain ⟨-, K, -, -, -, hK, ε, hε, r₀, r₁, -, -, -, -, -, hK₀, hK₁, -, -, hpairs⟩ :=
    kf132Row6_frame hGA h hF hF13 hEA hf1 hpq hmod
  obtain ⟨x, hxL, hxE, hx⟩ := hpairs s hs hsL s' hs' hs'L hord
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ kExceptional_conj_of_normalizer hK₀ hxE, h2 ▸ hK₁.conj hxE⟩
  · exact Or.inr ⟨h1 ▸ hK₁.conj hxE, h2 ▸ kExceptional_conj_of_normalizer hK₀ hxE⟩

end Main

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem kf132Types_row6 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 6 := by
  intro G _ _ p A c L E h hF hF13 hT hrow hrA hr9 t ht htL K hK
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  obtain ⟨hall, -⟩ := CFSG.RankThree.PartOne.KF132.kf132Row6_frame hGA h hF hF13 hEA hf1 hpq hmod
  refine ⟨f, ⟨hf1, hpq, hmod⟩, ?_, fun _ => ?_⟩
  · rcases hall t ht htL with hEx | hKF
    · obtain ⟨-, hmodK, -⟩ := hK.1 f hEx
      exact Or.inl hmodK
    · have hKeq : K = kZero p E t := hK.2 hKF.1
      right
      rw [hKeq]
      exact hKF.2.1
  · rcases hall t ht htL with hEx | hKF
    · obtain ⟨-, -, hmov⟩ := hK.1 f hEx
      exact hmov
    · have hKeq : K = kZero p E t := hK.2 hKF.1
      rw [hKeq]
      exact hKF.2.2.2.1

end CFSG.RankThree.PartOne.S13K
