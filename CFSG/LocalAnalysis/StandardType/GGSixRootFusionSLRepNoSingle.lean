module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepWit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLRep

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F]

theorem ratio_eq_of_act_eq {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    {D D' : GL (Fin n) F} {t t' : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hD' : (D' : Matrix (Fin n) (Fin n) F) = diagonal t')
    (h : ∀ s, φ (slConj n F D s) = φ (slConj n F D' s)) (a c : Fin n) :
    t a * (t c)⁻¹ = t' a * (t' c)⁻¹ := by
  by_cases hac : a = c
  · subst hac
    rw [mul_inv_cancel₀ (ne_zero_of_diagonal hD a), mul_inv_cancel₀ (ne_zero_of_diagonal hD' a)]
  have h1 := h (Matrix.SpecialLinearGroup.transvection hac 1)
  rw [slConj_transvection hD hac, slConj_transvection hD' hac] at h1
  simpa using eq_of_map_transvection_eq hker hac h1

theorem card_le_of_frame_of_not_single [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {X : Subgroup G}
    (hXp : ∀ b ∈ X, b ^ p = 1) (hframe : ∀ b ∈ X, GGFrameDiag φ b) {S : Finset (Fin n)}
    {i₀ : Fin n}
    (hXS : ∀ b ∈ X, ∀ (D : GL (Fin n) F) (t : Fin n → F),
      (D : Matrix (Fin n) (Fin n) F) = diagonal t → (∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) →
        ∀ i ∈ S, t i = t i₀)
    (hns : ∀ b ∈ X, ¬ GGFrameSingle φ b) {j₀ : Fin n} (hj₀ : j₀ ∉ S) :
    Nat.card X ≤ p ^ (Sᶜ.card - 1) := by
  classical
  choose D t hD hb using fun x : X => hframe x.1 x.2
  have ht0 : ∀ x k, t x k ≠ 0 := fun x k => ne_zero_of_diagonal (hD x) k
  have hroot : ∀ (x : X) (j : Fin n), (Units.mk0 (t x j / t x i₀)
      (div_ne_zero (ht0 x j) (ht0 x i₀))) ∈ rootsOfUnity p F := by
    intro x j
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow,
      pow_eq_pow_of_frame hker (hXp x.1 x.2) (hD x) (hb x) j i₀,
      div_self (pow_ne_zero _ (ht0 x i₀)), Units.val_one]
  let r : X → (↥Sᶜ → rootsOfUnity p F) := fun x j =>
    ⟨Units.mk0 (t x j / t x i₀) (div_ne_zero (ht0 x j) (ht0 x i₀)), hroot x j⟩
  have hrval : ∀ x (j : ↥Sᶜ), (((r x j : rootsOfUnity p F) : Fˣ) : F) = t x j / t x i₀ :=
    fun _ _ => rfl
  have hrmul : ∀ x y, r (x * y) = r x * r y := by
    intro x y
    funext j
    apply Subtype.ext
    apply Units.ext
    change t (x * y) j / t (x * y) i₀ = (t x j / t x i₀) * (t y j / t y i₀)
    have hxy : ((D x * D y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        diagonal (fun k => t x k * t y k) := by
      rw [Units.val_mul, hD x, hD y, diagonal_mul_diagonal]
    have hact : ∀ s, φ (slConj n F (D (x * y)) s) = φ (slConj n F (D x * D y) s) := by
      intro s
      rw [← hb (x * y), ← mul_act (hb x) (hb y) s]
      rfl
    have he := ratio_eq_of_act_eq hker (hD (x * y)) hxy hact j i₀
    rw [div_eq_mul_inv, he, mul_inv]
    field_simp [ht0 x i₀, ht0 y i₀]
  let R : X →* (↥Sᶜ → rootsOfUnity p F) :=
    { toFun := r
      map_one' := by
        funext j
        apply Subtype.ext
        apply Units.ext
        change t 1 j / t 1 i₀ = 1
        have h1 : slConj n F 1 = 1 :=
          map_one (ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F)
        have hact : ∀ s, φ (slConj n F (D 1) s) = φ (slConj n F 1 s) := by
          intro s
          rw [← hb 1, h1, MulAut.one_apply]
          simp
        have he := ratio_eq_of_act_eq hker (hD 1) (by simp : ((1 : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) = diagonal (fun _ => 1)) hact j i₀
        rw [div_eq_mul_inv, he, inv_one, mul_one]
      map_mul' := hrmul }
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hk : ∀ k, t x k / t x i₀ = 1 := by
      intro k
      by_cases hkS : k ∈ S
      · rw [hXS x.1 x.2 _ _ (hD x) (hb x) k hkS, div_self (ht0 x i₀)]
      · have h1 := congrArg (fun g => (((g ⟨k, by simpa using hkS⟩ : rootsOfUnity p F) : Fˣ) : F))
          hx
        simpa [R, r] using h1
    have hall : ∀ a c, t x a = t x c := fun a c => by
      have ha := hk a
      have hc := hk c
      rw [div_eq_one_iff_eq (ht0 x i₀)] at ha hc
      rw [ha, hc]
    exact Subtype.ext (eq_of_act_eq hcent fun s => by
      rw [hb x, slConj_eq_self_of_const (hD x) hall]
      simp)
  have hcod : Nat.card (↥Sᶜ → rootsOfUnity p F) = p ^ Sᶜ.card := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpF, Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hcardR : Nat.card R.range = Nat.card X := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hnt : R.range ≠ ⊤ := by
    intro htop
    obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have hζu : Units.mk0 ζ hζ0 ∈ rootsOfUnity p F := by
      rw [mem_rootsOfUnity]
      ext
      simp [hζ.pow_eq_one]
    set j₁ : ↥Sᶜ := ⟨j₀, by simpa using hj₀⟩ with hj₁
    set v : ↥Sᶜ → rootsOfUnity p F := Pi.mulSingle j₁ ⟨Units.mk0 ζ hζ0, hζu⟩ with hv
    obtain ⟨x, hx⟩ : v ∈ R.range := htop ▸ Subgroup.mem_top _
    have hxv : ∀ j : ↥Sᶜ, t x j / t x i₀ = (((v j : rootsOfUnity p F) : Fˣ) : F) := by
      intro j
      rw [← hx]
      rfl
    have hvj₀ : t x j₀ / t x i₀ = ζ := by
      have := hxv j₁
      rw [hv, Pi.mulSingle_eq_same] at this
      simpa using this
    have hvo : ∀ k, k ≠ j₀ → t x k = t x i₀ := by
      intro k hk
      by_cases hkS : k ∈ S
      · exact hXS x.1 x.2 _ _ (hD x) (hb x) k hkS
      · have h1 := hxv ⟨k, by simpa using hkS⟩
        rw [hv, Pi.mulSingle_eq_of_ne
          (fun h => hk (by rw [hj₁] at h; exact congrArg Subtype.val h))] at h1
        have h2 : t x k / t x i₀ = 1 := by simpa using h1
        exact (div_eq_one_iff_eq (ht0 x i₀)).mp h2
    apply hns x.1 x.2
    refine ⟨?_, D x, t x, j₀, hD x, hb x, fun i i' hi hi' => by rw [hvo i hi, hvo i' hi']⟩
    have hne : t x j₀ ≠ t x i₀ := by
      intro h
      rw [h, div_self (ht0 x i₀)] at hvj₀
      exact hζ.ne_one hp.one_lt hvj₀.symm
    exact ne_one_of_frame hker (hD x) (hb x) hne
  have hdvd : Nat.card R.range ∣ p ^ Sᶜ.card := hcod ▸ Subgroup.card_subgroup_dvd_card R.range
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjS : j ≠ Sᶜ.card := by
    rintro rfl
    exact hnt (Subgroup.eq_top_of_card_eq _ (by rw [hjeq, hcod]))
  rw [← hcardR, hjeq]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem ggRootFusionWitnessAlt_of_frame_bound [Finite F] [CharP F 2] {p : ℕ}
    {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
    {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}
    (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M) {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1)
    {Dm : GL (Fin n) F} {τ : Fin n → F} (hDm : (Dm : Matrix (Fin n) (Fin n) F) = diagonal τ)
    (hb : ∀ s, b * ggFrame ψ A₀ s * b⁻¹ = ggFrame ψ A₀ (slConj n F Dm s))
    {S : Finset (Fin n)} {μ : F} (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ)
    (hcard : Sᶜ.card < S.card) (hS2 : 2 ≤ S.card) {i₁ : Fin n} (hi₁ : i₁ ∉ S)
    (hbound : Nat.card (Bs ⊓ Subgroup.centralizer
      (((coordBlockSL F S).map (ggFrame ψ A₀) : Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2)
    {l : ℕ} (σ : Equiv.Perm (Fin n))
    (hpair : ∀ a c : Fin n, (σ c : ℕ) < l → (σ a : ℕ) = σ c + (n - l) → τ a = τ c) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hrangeφ : (ggFrame ψ A₀).range = G₀ := (range_ggFrame ψ A₀).trans hc.range
  have hcomp := isComponentOf_map_coordBlockSL hc.four (ker_ggFrame_le hc.ker A₀) hDm hb hS hSc
    hcard hS2 hi₁
  rw [hrangeφ] at hcomp
  have hW : GGSixFusionWitness p Bs D E G₀ t f b :=
    ⟨hb1, Or.inr (Or.inr ⟨hbBs, _, hcomp, Or.inl hbound⟩)⟩
  set P : Matrix.SpecialLinearGroup (Fin n) F := ggPermSL σ with hP
  set u := ggInvSL n l F with hu
  have hfix : P * u * P⁻¹ ∈ ggFix (slConj n F Dm) := by
    rw [TypeA.mem_ggFix_slConjugation_iff hDm]
    intro a c hac
    rw [hP, coe_ggPermSL_conj, Matrix.submatrix_apply, hu, coe_ggInvSL, ggInvMatrix,
      Matrix.add_apply, ggInvNil_apply]
    have hac' : a ≠ c := by
      rintro rfl
      exact hac rfl
    rw [Matrix.one_apply_ne (fun h => hac' (σ.injective h)), zero_add]
    split_ifs with h
    · exact absurd (hpair a c h.1 h.2.1) hac
    · rfl
  have hwG : ψ (A₀ * P) ∈ G₀ := hc.range ▸ (⟨A₀ * P, rfl⟩ : ψ (A₀ * P) ∈ ψ.range)
  refine ggRootFusionWitnessAlt_of_conj_comm ψ (w := A₀ * P) ?_ (hle hwG) hW
  have he : A₀ * P * u * (A₀ * P)⁻¹ = A₀ * (P * u * P⁻¹) * A₀⁻¹ := by group
  have h1 : b * ggFrame ψ A₀ (P * u * P⁻¹) * b⁻¹ = ggFrame ψ A₀ (P * u * P⁻¹) := by
    rw [hb, mem_ggFix.mp hfix]
  rw [he, ← ggFrame_apply]
  calc b * ggFrame ψ A₀ (P * u * P⁻¹) = b * ggFrame ψ A₀ (P * u * P⁻¹) * b⁻¹ * b := by group
    _ = ggFrame ψ A₀ (P * u * P⁻¹) * b := by rw [h1]

theorem prod_update_update_update_one {M₀ : Type} [CommMonoid M₀] {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y z : M₀) :
    ∏ i, Function.update (Function.update (Function.update (fun _ => (1 : M₀)) a x) b y) c z i =
      z * (y * x) := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ c), Finset.prod_update_of_mem
    (by simpa using hbc : b ∈ Finset.univ \ {c}), Finset.prod_update_of_mem
    (by simp [hab, hac] : a ∈ (Finset.univ \ {c}) \ {b}), Finset.prod_const_one, mul_one]

theorem ggRootFusionWitnessAlt_odd_nosingle [Finite F] [CharP F 2] {p : ℕ}
    {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
    {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}
    (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ}
    (hl2 : 2 ≤ l) (hn : n = 2 * l + 1) (h7 : 7 ≤ n)
    (hns : ∀ b ∈ Bs, ¬ GGFrameSingle (ggFrame ψ A₀) b) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hp := hc.prime
  have hp3 : 3 ≤ p := by have := hp.two_le; have := hc.odd; omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζ2 : ζ⁻¹ ^ 2 ≠ 1 := by
    rw [inv_pow, inv_ne_one]
    intro h
    have := (hζ.pow_eq_one_iff_dvd 2).mp h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set l1 : Fin n := ⟨l + 1, by omega⟩ with hl1
  have hol : o' ≠ l' := by
    intro h; have := congrArg Fin.val h; simp only [ho', hl'] at this; omega
  have ho1 : o' ≠ l1 := by
    intro h; have := congrArg Fin.val h; simp only [ho', hl1] at this; omega
  have hl11 : l' ≠ l1 := by
    intro h; have := congrArg Fin.val h; simp only [hl', hl1] at this; omega
  set δ : Fin n → F := Function.update (Function.update (Function.update (fun _ => (1 : F)) o' ζ)
    l' (ζ⁻¹ ^ 2)) l1 ζ with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, prod_update_update_update_one hol ho1 hl11, inv_pow]
    field_simp
  have hδ1 : δ l1 = ζ := by rw [hδdef, Function.update_self]
  have hδl : δ l' = ζ⁻¹ ^ 2 := by
    rw [hδdef, Function.update_of_ne hl11, Function.update_self]
  have hδo : δ o' = ζ := by
    rw [hδdef, Function.update_of_ne ho1, Function.update_of_ne hol, Function.update_self]
  have hval : ∀ i, i ≠ o' → i ≠ l' → i ≠ l1 → δ i = 1 := fun i hio hil hi1 => by
    rw [hδdef, Function.update_of_ne hi1, Function.update_of_ne hil, Function.update_of_ne hio]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hi1 : i = l1
    · rw [hi1, hδ1, hζ.pow_eq_one]
    by_cases hil : i = l'
    · rw [hil, hδl]
      exact inv_pow_pow_eq_one hζ 2
    by_cases hio : i = o'
    · rw [hio, hδo, hζ.pow_eq_one]
    · rw [hval i hio hil hi1, one_pow]
  set T : Finset (Fin n) := {o', l', l1} with hT
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hol, ho1]), Finset.card_pair hl11]
  have hcS : Tᶜ.card = n - 3 := by rw [Finset.card_compl, Fintype.card_fin, hTc]
  have hmemT : ∀ i, i ∉ Tᶜ ↔ (i = o' ∨ i = l' ∨ i = l1) := fun i => by
    rw [Finset.mem_compl, not_not, hT, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨i₀, hi₀⟩ : Tᶜ.Nonempty := Finset.card_pos.mp (by rw [hcS]; omega)
  have hi₀' : i₀ ≠ o' ∧ i₀ ≠ l' ∧ i₀ ≠ l1 := by simpa [hT] using hi₀
  set d := ggDiagSL δ hδ with hd
  have hdδ : (d : Matrix (Fin n) (Fin n) F) = diagonal δ := rfl
  have hb := act_map (ggFrame ψ A₀) d
  have hbBs := mem_of_frame_diagonal_inner hc.bstar hc.frame hdδ (ggDiagSL_pow_eq_one hδ hδp)
  have hb1 := ne_one_of_frame (ker_ggFrame_le hc.ker A₀) hdδ hb (i := o') (j := i₀)
    (by rw [hδo, hval i₀ hi₀'.1 hi₀'.2.1 hi₀'.2.2]; exact hζ1)
  have hcent' : Subgroup.centralizer ((ggFrame ψ A₀).range : Set G) = ⊥ := by
    rw [range_ggFrame, hc.range]
    exact hc.cent
  have hbound := card_le_of_frame_of_not_single hp hc.dvd (ker_ggFrame_le hc.ker A₀) hcent'
    (X := Bs ⊓ Subgroup.centralizer
      (((coordBlockSL F Tᶜ).map (ggFrame ψ A₀) : Subgroup G) : Set G))
    (fun c hc' => hc.bstar.2.1.2 c hc'.1) (fun c hc' => hc.frame c hc'.1) (S := Tᶜ) (i₀ := i₀)
    (fun c hc' D' t' hD' hc'' i hi =>
      eq_of_mem_centralizer_coordBlockSL (ker_ggFrame_le hc.ker A₀) hc'.2 hD' hc'' hi₀ i hi)
    (fun c hc' => hns c hc'.1) (j₀ := o') (by simp [hT])
  rw [compl_compl, hTc] at hbound
  refine ggRootFusionWitnessAlt_of_frame_bound hc hle hbBs hb1 hdδ hb (S := Tᶜ) (μ := 1)
    (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ (i₁ := o') (by simp [hT]) hbound 1 ?_
  · have hi' : i ≠ o' ∧ i ≠ l' ∧ i ≠ l1 := by simpa [hT] using hi
    exact hval i hi'.1 hi'.2.1 hi'.2.2
  · rcases (hmemT i).mp hi with rfl | rfl | rfl
    · rw [hδo]; exact hζ1
    · rw [hδl]; exact hζ2
    · rw [hδ1]; exact hζ1
  · rw [compl_compl, hTc, hcS]
    omega
  · rw [hcS]
    omega
  · intro a c hc' ha
    simp only [Equiv.Perm.one_apply] at hc' ha
    by_cases hc0 : (c : ℕ) = 0
    · have hco : c = o' := Fin.ext hc0
      have hal : a = l1 := Fin.ext (by simp only [hl1]; omega)
      rw [hco, hal, hδo, hδ1]
    · rw [hval a (fun h => by rw [h] at ha; simp only [ho'] at ha; omega)
          (fun h => by rw [h] at ha; simp only [hl'] at ha; omega)
          (fun h => by rw [h] at ha; simp only [hl1] at ha; omega),
        hval c (fun h => by rw [h] at hc0; exact hc0 rfl)
          (fun h => by rw [h] at hc'; simp only [hl'] at hc'; omega)
          (fun h => by rw [h] at hc'; simp only [hl1] at hc'; omega)]

end SLRep

end CFSG.StandardType
