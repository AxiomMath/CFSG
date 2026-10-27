module

public import CFSG.Timmesfeld.Bridge.RootStructWTIQuot
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS.NaturalModule

@[expose] noncomputable def diagEltHom (K : Type*) [Field K] :
    Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := diagElt
  map_one' := diagElt_one
  map_mul' c c' := (diagElt_mul_diagElt c c').symm

theorem diagEltHom_injective (K : Type*) [Field K] : Function.Injective (diagEltHom K) := by
  intro c c' h
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [diagEltHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_diagElt, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at this
  exact Units.ext this

section Generic

variable {G : Type*} [Group G]

theorem exists_lift_orderOf {R : Subgroup G} {N : Subgroup R} [N.Normal] [Finite G]
    (hN : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1) (z : R ⧸ N) (hz : Odd (orderOf z)) :
    ∃ r : R, orderOf r = orderOf z ∧ z ∈ Subgroup.zpowers (QuotientGroup.mk' N r) ∧
      QuotientGroup.mk' N r ∈ Subgroup.zpowers z := by
  obtain ⟨r₀, rfl⟩ := QuotientGroup.mk'_surjective N z
  set o := orderOf (QuotientGroup.mk' N r₀) with ho
  have hr₀ : r₀ ^ o ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, ho, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := hN _ hr₀
  have hco : Nat.Coprime o (2 ^ j) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hz)
  refine ⟨r₀ ^ 2 ^ j, ?_, ?_, ?_⟩
  · apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hj]
    · have h1 : orderOf (QuotientGroup.mk' N (r₀ ^ 2 ^ j)) = o := by
        rw [map_pow, Nat.Coprime.orderOf_pow (ho ▸ hco)]
      rw [← h1]
      exact orderOf_map_dvd _ _
  · rw [map_pow]
    exact mem_zpowers_pow_iff.2 (by rw [Nat.gcd_comm]; exact hco)
  · rw [map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end Generic

section RankTwo

theorem toPermHom_bijective_of_card_eq_two {X : Type*} [Group X] [Finite X]
    {A B : Subgroup X} (h : IsElemAbRankOne A B) (hA : Nat.card A = 2) :
    Function.Bijective (MulAction.toPermHom X (RankOne.Point A)) := by
  have hinj : Function.Injective (MulAction.toPermHom X (RankOne.Point A)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    have := h.pointKernel_le
    rw [h.normalizer_inf_eq_hua, h.hua_eq_bot_of_card_eq_two hA] at this
    exact this
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_perm, h.card_point, hA, h.card_eq_six hA]
  decide

theorem nonempty_mulEquiv_of_card_eq_two {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] {A B : Subgroup X} {A' B' : Subgroup Y} (h : IsElemAbRankOne A B)
    (h' : IsElemAbRankOne A' B') (hA : Nat.card A = 2) (hA' : Nat.card A' = 2) :
    Nonempty (X ≃* Y) := by
  have e : RankOne.Point A ≃ RankOne.Point A' :=
    (Finite.equivFin _).trans ((finCongr (by rw [h.card_point, h'.card_point, hA, hA'])).trans
      (Finite.equivFin _).symm)
  exact ⟨((MulEquiv.ofBijective _ (toPermHom_bijective_of_card_eq_two h hA)).trans
    (Equiv.permCongrHom e)).trans
    (MulEquiv.ofBijective _ (toPermHom_bijective_of_card_eq_two h' hA')).symm⟩

theorem isElemAbRankOne_SL2_two :
    IsElemAbRankOne (upperUnipotent (GaloisField 2 1)) (lowerUnipotent (GaloisField 2 1)) := by
  set K := GaloisField 2 1
  have hK : ∀ t : K, t ≠ 0 → t = 1 := by
    intro t ht
    have h1 : Nat.card Kˣ = 1 := by
      rw [Nat.card_units, GaloisField.card 2 1 one_ne_zero]
      rfl
    have : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.1 h1.le
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 t ht) 1)
  have hω : weylElt K = RankOne.upperElt K 1 * RankOne.lowerElt K 1 * RankOne.upperElt K 1 :=
    (upperElt_one_mul_lowerElt_one_mul_upperElt_one).symm
  have hu2 : ∀ t : K, RankOne.upperElt K t * RankOne.upperElt K t = 1 := fun t => by
    rw [RankOne.upperElt_mul, CharTwo.add_self_eq_zero, RankOne.upperElt_zero]
  have hl2 : ∀ t : K, RankOne.lowerElt K t * RankOne.lowerElt K t = 1 := fun t => by
    rw [RankOne.lowerElt_mul, CharTwo.add_self_eq_zero, RankOne.lowerElt_zero]
  have hωU : (upperUnipotent K).map (MulAut.conj (weylElt K)).toMonoidHom = lowerUnipotent K := by
    ext g
    rw [RankOne.mem_map_conj, (inv_eq_of_mul_eq_one_right (weylElt_mul_self (K := K))),
      RankOne.mem_upperUnipotent_iff, RankOne.mem_lowerUnipotent_iff]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← weylElt_mul_upperElt_mul_weylElt, ← ht]
      calc g = weylElt K * weylElt K * g * (weylElt K * weylElt K) := by
            rw [weylElt_mul_self, one_mul, mul_one]
        _ = weylElt K * (weylElt K * g * weylElt K) * weylElt K := by group
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [← weylElt_mul_upperElt_mul_weylElt]
      simp only [← mul_assoc, weylElt_mul_self, one_mul]
      rw [mul_assoc, weylElt_mul_self, mul_one]
  have hmouf : (upperUnipotent K).map (MulAut.conj (RankOne.lowerElt K 1)).toMonoidHom =
      (lowerUnipotent K).map (MulAut.conj (RankOne.upperElt K 1)).toMonoidHom := by
    have hl : RankOne.lowerElt K 1 =
        RankOne.upperElt K 1 * weylElt K * RankOne.upperElt K 1 := by
      rw [hω]
      calc RankOne.lowerElt K 1 = (RankOne.upperElt K 1 * RankOne.upperElt K 1) *
            RankOne.lowerElt K 1 * (RankOne.upperElt K 1 * RankOne.upperElt K 1) := by
            rw [hu2, one_mul, mul_one]
        _ = _ := by group
    rw [hl, RankOne.map_conj_mul, RankOne.map_conj_mul,
      RankOne.map_conj_of_mem ((RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩), hωU]
  refine ⟨upperUnipotent_sup_lowerUnipotent, RankOne.upperUnipotent_ne_lowerUnipotent K,
    fun x hx y hy => ?_, fun x hx => ?_, fun x hx hx1 => ?_, fun y hy hy1 => ?_⟩
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hy
    rw [Commute, SemiconjBy, RankOne.upperElt_mul, RankOne.upperElt_mul, add_comm]
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    exact hu2 s
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    have hs : s = 1 := hK s (fun h0 => hx1 (by rw [h0, RankOne.upperElt_zero]))
    subst hs
    refine ⟨RankOne.lowerElt K 1, (RankOne.mem_lowerUnipotent_iff K).2 ⟨1, rfl⟩, fun h' => ?_,
      hmouf⟩
    rw [← RankOne.lowerElt_zero] at h'
    exact one_ne_zero (RankOne.lowerElt_injective K h')
  · obtain ⟨s, rfl⟩ := (RankOne.mem_lowerUnipotent_iff K).1 hy
    have hs : s = 1 := hK s (fun h0 => hy1 (by rw [h0, RankOne.lowerElt_zero]))
    subst hs
    refine ⟨RankOne.upperElt K 1, (RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩, fun h' => ?_,
      hmouf.symm⟩
    rw [← RankOne.upperElt_zero] at h'
    exact one_ne_zero (RankOne.upperElt_injective K h')

end RankTwo

theorem exists_perm_of_three {α : Type*} (hα : Nat.card α = 3) {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) (h12' : y₁ ≠ y₂) (h13' : y₁ ≠ y₃)
    (h23' : y₂ ≠ y₃) : ∃ σ : Equiv.Perm α, σ x₁ = y₁ ∧ σ x₂ = y₂ ∧ σ x₃ = y₃ := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have hinj : ∀ {z₁ z₂ z₃ : α}, z₁ ≠ z₂ → z₁ ≠ z₃ → z₂ ≠ z₃ →
      Function.Bijective (![z₁, z₂, z₃] : Fin 3 → α) := by
    intro z₁ z₂ z₃ h1 h2 h3
    have hi : Function.Injective (![z₁, z₂, z₃] : Fin 3 → α) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    exact hi.bijective_of_nat_card_le (by rw [hα, Nat.card_eq_fintype_card, Fintype.card_fin])
  set eX := Equiv.ofBijective _ (hinj h12 h13 h23)
  set eY := Equiv.ofBijective _ (hinj h12' h13' h23')
  refine ⟨eX.symm.trans eY, ?_, ?_, ?_⟩
  · have : eX 0 = x₁ := rfl
    rw [Equiv.trans_apply, ← this, Equiv.symm_apply_apply]; rfl
  · have : eX 1 = x₂ := rfl
    rw [Equiv.trans_apply, ← this, Equiv.symm_apply_apply]; rfl
  · have : eX 2 = x₃ := rfl
    rw [Equiv.trans_apply, ← this, Equiv.symm_apply_apply]; rfl

namespace LineSetting

section TypeZero

variable {G : Type} [Group G] {D : Set G} (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha
variable {d : G} [((nCore D a).subgroupOf (lineGroup D a d)).Normal]

theorem lineGroupBarAction_apply_eq_of_normalizes {L : Subgroup G} (hL' : L ∈ rootLines D a)
    {a₀ : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (ha₀ : a₀ ∈ lineRadicalBar D a d L) (ha₀1 : a₀ ≠ 1)
    {h : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (hh : h⁻¹ * a₀ * h ∈ lineRadicalBar D a d L) :
    hL.lineGroupBarAction ha d h ⟨L, hL'⟩ = ⟨L, hL'⟩ := by
  set ψ := hL.lineGroupBarAction ha d
  by_contra hne
  have h1 : ψ a₀ (ψ h ⟨L, hL'⟩) = ψ h ⟨L, hL'⟩ := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, show a₀ * h = h * (h⁻¹ * a₀ * h) by group, map_mul,
      Equiv.Perm.mul_apply, hL.lineGroupBarAction_apply_self ha hL' hh]
  exact ha₀1 (hL.eq_one_of_lineGroupBarAction_apply_eq ha hL' (ψ h ⟨L, hL'⟩).2
    (fun h' => hne (Subtype.ext h')) ha₀ h1)

theorem lineGroupBar_torus {n : ℕ} {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ rootLines D a)
    (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard)
    (φ : (lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ1 : (lineRadicalBar D a d L₁).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n))
    (hφ2 : (lineRadicalBar D a d L₂).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n)) :
    (∀ c : (GaloisField 2 n)ˣ,
      hL.lineGroupBarAction ha d (φ.symm (diagElt c)) ⟨L₁, h₁⟩ = ⟨L₁, h₁⟩ ∧
      hL.lineGroupBarAction ha d (φ.symm (diagElt c)) ⟨L₂, h₂⟩ = ⟨L₂, h₂⟩) ∧
    (∀ L (hL' : L ∈ rootLines D a), L ≠ L₁ → L ≠ L₂ → ∃ s : GaloisField 2 n, s ≠ 0 ∧
      hL.lineGroupBarAction ha d (φ.symm (RankOne.lowerElt _ s)) ⟨L₁, h₁⟩ = ⟨L, hL'⟩) ∧
    (∀ (c : (GaloisField 2 n)ˣ) (s : GaloisField 2 n),
      hL.lineGroupBarAction ha d (φ.symm (diagElt c))
          (hL.lineGroupBarAction ha d (φ.symm (RankOne.lowerElt _ s)) ⟨L₁, h₁⟩) =
        hL.lineGroupBarAction ha d
          (φ.symm (RankOne.lowerElt _ (((c⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ 2 * s)))
          ⟨L₁, h₁⟩) := by
  set K := GaloisField 2 n
  set ψ := hL.lineGroupBarAction ha d
  have hmem1 : ∀ x, x ∈ lineRadicalBar D a d L₁ ↔ φ x ∈ upperUnipotent K := fun x => by
    rw [← hφ1, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmem2 : ∀ x, x ∈ lineRadicalBar D a d L₂ ↔ φ x ∈ lowerUnipotent K := fun x => by
    rw [← hφ2, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hu1 : φ.symm (RankOne.upperElt K 1) ∈ lineRadicalBar D a d L₁ := by
    rw [hmem1, MulEquiv.apply_symm_apply]
    exact (RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩
  have hl1 : φ.symm (RankOne.lowerElt K 1) ∈ lineRadicalBar D a d L₂ := by
    rw [hmem2, MulEquiv.apply_symm_apply]
    exact (RankOne.mem_lowerUnipotent_iff K).2 ⟨1, rfl⟩
  have hu1' : φ.symm (RankOne.upperElt K 1) ≠ 1 := fun h' => by
    have := congrArg φ h'
    rw [MulEquiv.apply_symm_apply, map_one, ← RankOne.upperElt_zero] at this
    exact one_ne_zero (RankOne.upperElt_injective K this)
  have hl1' : φ.symm (RankOne.lowerElt K 1) ≠ 1 := fun h' => by
    have := congrArg φ h'
    rw [MulEquiv.apply_symm_apply, map_one, ← RankOne.lowerElt_zero] at this
    exact one_ne_zero (RankOne.lowerElt_injective K this)
  refine ⟨fun c => ⟨?_, ?_⟩, fun L hL' hL1 hL2 => ?_, fun c s => ?_⟩
  · refine hL.lineGroupBarAction_apply_eq_of_normalizes ha h₁ hu1 hu1' ?_
    rw [hmem1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have := (Subgroup.mem_normalizer_iff.1 (diagElt_mem_normalizer_upperUnipotent c⁻¹)
      (RankOne.upperElt K 1)).1 ((RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩)
    rwa [← diagElt_inv, inv_inv] at this
  · refine hL.lineGroupBarAction_apply_eq_of_normalizes ha h₂ hl1 hl1' ?_
    rw [hmem2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have := (Subgroup.mem_normalizer_iff.1 (diagElt_mem_normalizer_lowerUnipotent c⁻¹)
      (RankOne.lowerElt K 1)).1 ((RankOne.mem_lowerUnipotent_iff K).2 ⟨1, rfl⟩)
    rwa [← diagElt_inv, inv_inv] at this
  · obtain ⟨w, hw, hwL⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 h₂ h₁ hL'
      h12 hL2
    obtain ⟨t, ht⟩ := (RankOne.mem_lowerUnipotent_iff K).1 ((hmem2 w).1 hw)
    have hwt : w = φ.symm (RankOne.lowerElt K t) := by rw [← ht, MulEquiv.symm_apply_apply]
    refine ⟨t, fun h0 => hL1 ?_, by rw [← hwt]; exact hwL⟩
    rw [hwt, h0, RankOne.lowerElt_zero, map_one, map_one, Equiv.Perm.one_apply] at hwL
    exact (congrArg Subtype.val hwL).symm
  · have hfix := (hL.lineGroupBarAction_apply_eq_of_normalizes ha h₁ hu1 hu1' (by
      rw [hmem1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      have := (Subgroup.mem_normalizer_iff.1 (diagElt_mem_normalizer_upperUnipotent c⁻¹)
        (RankOne.upperElt K 1)).1 ((RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩)
      rwa [← diagElt_inv, inv_inv] at this) : ψ (φ.symm (diagElt c)) ⟨L₁, h₁⟩ = ⟨L₁, h₁⟩)
    have e : φ.symm (diagElt c) * φ.symm (RankOne.lowerElt K s) =
        φ.symm (RankOne.lowerElt K (((c⁻¹ : Kˣ) : K) ^ 2 * s)) * φ.symm (diagElt c) := by
      rw [← map_mul, ← map_mul, diagElt_mul_lowerElt]
    rw [← Equiv.Perm.mul_apply, ← map_mul, e, map_mul, Equiv.Perm.mul_apply, hfix]

theorem exists_lineGroupBar_apply_eq_apply_eq (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard)
    {L₁ L₂ L₁' L₂' : Subgroup G} (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a)
    (h₁' : L₁' ∈ rootLines D a) (h₂' : L₂' ∈ rootLines D a) (h12 : L₁ ≠ L₂)
    (h12' : L₁' ≠ L₂') :
    ∃ z, hL.lineGroupBarAction ha d z ⟨L₁, h₁⟩ = ⟨L₁', h₁'⟩ ∧
      hL.lineGroupBarAction ha d z ⟨L₂, h₂⟩ = ⟨L₂', h₂'⟩ := by
  set ψ := hL.lineGroupBarAction ha d
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, ψ z₁ ⟨L₁, h₁⟩ = ⟨L₁', h₁'⟩ := by
    by_cases hLL : L₁ = L₁'
    · exact ⟨1, by rw [map_one, Equiv.Perm.one_apply]; exact Subtype.ext hLL⟩
    obtain ⟨L₃, hL₃, h31, h31'⟩ := exists_mem_rootLines_ne_ne (L₁ := L₁) (L₂ := L₁') h3
    obtain ⟨z, -, hz⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 hL₃ h₁ h₁'
      (Ne.symm h31) (Ne.symm h31')
    exact ⟨z, hz⟩
  have hne : (ψ z₁ ⟨L₂, h₂⟩).1 ≠ L₁' := fun h' => h12 (by
    have : ψ z₁ ⟨L₂, h₂⟩ = ψ z₁ ⟨L₁, h₁⟩ := by rw [hz₁]; exact Subtype.ext h'
    exact (congrArg Subtype.val ((ψ z₁).injective this)).symm)
  obtain ⟨z₂, hz₂m, hz₂⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 h₁'
    (ψ z₁ ⟨L₂, h₂⟩).2 h₂' hne (Ne.symm h12')
  refine ⟨z₂ * z₁, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hz₁, hL.lineGroupBarAction_apply_self ha h₁' hz₂m]
  · rw [map_mul, Equiv.Perm.mul_apply]
    exact hz₂

theorem exists_lineGroupBar_apply_eq₃ (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h5 : 5 ≤ (rootLines D a).ncard)
    {L₁ L₂ L₃ L₁' L₂' L₃' : Subgroup G} (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a)
    (h₃ : L₃ ∈ rootLines D a) (h₁' : L₁' ∈ rootLines D a) (h₂' : L₂' ∈ rootLines D a)
    (h₃' : L₃' ∈ rootLines D a) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (h12' : L₁' ≠ L₂') (h13' : L₁' ≠ L₃') (h23' : L₂' ≠ L₃') :
    ∃ z, hL.lineGroupBarAction ha d z ⟨L₁, h₁⟩ = ⟨L₁', h₁'⟩ ∧
      hL.lineGroupBarAction ha d z ⟨L₂, h₂⟩ = ⟨L₂', h₂'⟩ ∧
      hL.lineGroupBarAction ha d z ⟨L₃, h₃⟩ = ⟨L₃', h₃'⟩ := by
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  set ψ := hL.lineGroupBarAction ha d
  obtain ⟨z₁, hz₁, hz₂⟩ := hL.exists_lineGroupBar_apply_eq_apply_eq ha hd had hadD hdT h3 h₁ h₂ h₁'
    h₂' h12 h12'
  obtain ⟨n, -, -, φ, hφ1, hφ2⟩ :=
    hL.exists_mulEquiv_lineGroupBar ha hd had hadD hdT h₁' h₂' h12' h5
  obtain ⟨hfix, hlines, hconj⟩ := hL.lineGroupBar_torus ha h₁' h₂' h12' hd had hadD hdT h3 φ hφ1 hφ2
  set L₃'' := ψ z₁ ⟨L₃, h₃⟩ with hL₃''
  have hne1 : L₃''.1 ≠ L₁' := fun h' => h13 (by
    have : ψ z₁ ⟨L₃, h₃⟩ = ψ z₁ ⟨L₁, h₁⟩ := by rw [hz₁]; exact Subtype.ext h'
    exact (congrArg Subtype.val ((ψ z₁).injective this)).symm)
  have hne2 : L₃''.1 ≠ L₂' := fun h' => h23 (by
    have : ψ z₁ ⟨L₃, h₃⟩ = ψ z₁ ⟨L₂, h₂⟩ := by rw [hz₂]; exact Subtype.ext h'
    exact (congrArg Subtype.val ((ψ z₁).injective this)).symm)
  obtain ⟨s, hs, hsL⟩ := hlines L₃''.1 L₃''.2 hne1 hne2
  obtain ⟨s', hs', hs'L⟩ := hlines L₃' h₃' (Ne.symm h13') (Ne.symm h23')
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : GaloisField 2 n, c₀ ^ 2 = s * s'⁻¹ := by
    refine ⟨(frobeniusEquiv (GaloisField 2 n) 2).symm (s * s'⁻¹), ?_⟩
    have := (frobeniusEquiv (GaloisField 2 n) 2).apply_symm_apply (s * s'⁻¹)
    rwa [frobeniusEquiv_apply, frobenius_def] at this
  have hc₀0 : c₀ ≠ 0 := fun h' => by
    rw [h', zero_pow two_ne_zero] at hc₀
    exact mul_ne_zero hs (inv_ne_zero hs') hc₀.symm
  obtain ⟨c, hc⟩ : ∃ c : (GaloisField 2 n)ˣ, (c : GaloisField 2 n) = c₀ := ⟨Units.mk0 c₀ hc₀0, rfl⟩
  have hcs : ((c⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ 2 * s = s' := by
    rw [Units.val_inv_eq_inv_val, hc, inv_pow, hc₀, mul_inv, inv_inv, mul_comm s⁻¹, mul_assoc,
      inv_mul_cancel₀ hs, mul_one]
  refine ⟨φ.symm (diagElt c) * z₁, ?_, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hz₁, (hfix c).1]
  · rw [map_mul, Equiv.Perm.mul_apply, hz₂, (hfix c).2]
  · rw [map_mul, Equiv.Perm.mul_apply, ← hL₃'', ← Subtype.coe_eta L₃'' L₃''.2, ← hsL, hconj c s,
      hcs, hs'L]

theorem exists_lineGroupBar_torus_elt (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h5 : 5 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) :
    ∃ z, orderOf z + 2 = (rootLines D a).ncard ∧
      hL.lineGroupBarAction ha d z ⟨L₁, h₁⟩ = ⟨L₁, h₁⟩ ∧
      hL.lineGroupBarAction ha d z ⟨L₂, h₂⟩ = ⟨L₂, h₂⟩ ∧
      ∀ L (hL' : L ∈ rootLines D a), L ≠ L₁ → L ≠ L₂ → ∀ L' (hL'' : L' ∈ rootLines D a),
        L' ≠ L₁ → L' ≠ L₂ → ∃ i < orderOf z,
          hL.lineGroupBarAction ha d (z ^ i) ⟨L, hL'⟩ = ⟨L', hL''⟩ := by
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  obtain ⟨n, hn2, hncard, φ, hφ1, hφ2⟩ := hL.exists_mulEquiv_lineGroupBar ha hd had hadD hdT h₁ h₂
    h12 h5
  obtain ⟨hfix, hlines, hconj⟩ := hL.lineGroupBar_torus ha h₁ h₂ h12 hd had hadD hdT h3 φ hφ1 hφ2
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := (GaloisField 2 n)ˣ)
  have hoc : orderOf c = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, Nat.card_units, hK]
  have hz : orderOf (φ.symm (diagElt c)) = orderOf c := by
    rw [MulEquiv.orderOf_eq, show diagElt c = diagEltHom _ c from rfl,
      orderOf_injective _ (diagEltHom_injective _)]
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨φ.symm (diagElt c), by rw [hz, hoc, hncard]; omega, (hfix c).1, (hfix c).2,
    fun L hL' hL1 hL2 L' hL'' hL1' hL2' => ?_⟩
  obtain ⟨s, hs, hsL⟩ := hlines L hL' hL1 hL2
  obtain ⟨s', hs', hs'L⟩ := hlines L' hL'' hL1' hL2'
  set g : (GaloisField 2 n)ˣ := c⁻¹ ^ 2 with hg
  have hodd : Nat.Coprime (orderOf c⁻¹) 2 := by
    rw [orderOf_inv, hoc, Nat.coprime_two_right]
    exact Nat.Even.sub_odd hpos (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hog : orderOf g = orderOf c := by rw [hg, Nat.Coprime.orderOf_pow hodd, orderOf_inv]
  have hgen : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    have htop : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, hog, orderOf_eq_card_of_forall_mem_zpowers hc])
    rw [htop]
    exact Subgroup.mem_top x
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2
    (hgen (Units.mk0 (s' * s⁻¹) (mul_ne_zero hs' (inv_ne_zero hs)))))
  set i := k % orderOf g with hidef
  have hi : i < orderOf g := Nat.mod_lt _ (orderOf_pos g)
  have hgi : g ^ i = Units.mk0 (s' * s⁻¹) (mul_ne_zero hs' (inv_ne_zero hs)) := by
    rw [hidef, pow_mod_orderOf, hk]
  refine ⟨i, by rw [hz, ← hog]; exact hi, ?_⟩
  have hdi : φ.symm (diagElt c) ^ i = φ.symm (diagElt (c ^ i)) := by
    rw [← map_pow]
    congr 1
    exact (map_pow (diagEltHom _) c i).symm
  rw [hdi, ← Subtype.coe_eta (⟨L, hL'⟩ : rootLines D a) hL', ← hsL, hconj, ← hs'L]
  congr 3
  have h1 : (((c ^ i)⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ 2 =
      ((g ^ i : (GaloisField 2 n)ˣ) : GaloisField 2 n) := by
    rw [hg, ← Units.val_pow_eq_pow_val, inv_pow, ← pow_mul, ← pow_mul, mul_comm, inv_pow]
  rw [h1, hgi, Units.val_mk0, mul_assoc, inv_mul_cancel₀ hs, mul_one]

omit ha in
theorem pow_two_pow_eq_one_of_mem_subgroupOf (d : G) :
    ∀ n ∈ (nCore D a).subgroupOf (lineGroup D a d), ∃ k : ℕ, n ^ 2 ^ k = 1 := by
  have := hL.hyp.finite
  intro n hn
  obtain ⟨k, hk⟩ := isPGroup_nCore D a ⟨n, Subgroup.mem_subgroupOf.1 hn⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem rootLinesL2_of_five_le (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h5 : 5 ≤ (rootLines D a).ncard) :
    ∃ m : ℕ, 1 ≤ m ∧ (rootLines D a).ncard = 2 ^ m + 1 ∧ nCore D a ≤ lineGroup D a d ∧
      (∀ g ∈ lineGroup D a d,
        (∀ L ∈ rootLines D a, L.map (MulAut.conj g).toMonoidHom = L) ↔ g ∈ nCore D a) ∧
      (∃ f : lineGroup D a d →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m),
        Function.Surjective f ∧ f.ker = (nCore D a).subgroupOf (lineGroup D a d)) ∧
      ∀ L₁ ∈ rootLines D a, ∀ L₂ ∈ rootLines D a, ∀ L₃ ∈ rootLines D a,
      ∀ L₁' ∈ rootLines D a, ∀ L₂' ∈ rootLines D a, ∀ L₃' ∈ rootLines D a,
        L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → L₁' ≠ L₂' → L₁' ≠ L₃' → L₂' ≠ L₃' →
        ∃ g ∈ lineGroup D a d, L₁.map (MulAut.conj g).toMonoidHom = L₁' ∧
          L₂.map (MulAut.conj g).toMonoidHom = L₂' ∧
          L₃.map (MulAut.conj g).toMonoidHom = L₃' := by
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  have hR := hL.nCore_le_lineGroup ha hd had hadD hdT h3
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  obtain ⟨n, hn2, hncard, φ, -, -⟩ := hL.exists_mulEquiv_lineGroupBar ha hd had hadD hdT hT hT'
    (Ne.symm hne) h5
  have hinj := hL.lineGroupBarAction_injective ha hd had hadD hdT h5
  refine ⟨n, by omega, hncard, hR, fun g hg => ⟨fun hgL => ?_, fun hgM L hL' =>
    hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hgM) hL'⟩,
    ⟨φ.toMonoidHom.comp (QuotientGroup.mk' _), φ.surjective.comp (QuotientGroup.mk'_surjective _),
      ?_⟩, fun L₁ h₁ L₂ h₂ L₃ h₃ L₁' h₁' L₂' h₂' L₃' h₃' h12 h13 h23 h12' h13' h23' => ?_⟩
  · have h1 : hL.lineGroupBarAction ha d (QuotientGroup.mk' _ ⟨g, hg⟩) = 1 := by
      ext L : 2
      rw [lineGroupBarAction_mk, Equiv.Perm.one_apply]
      exact hgL L.1 L.2
    have h2 := hinj (h1.trans (map_one _).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · obtain ⟨z, hz1, hz2, hz3⟩ := hL.exists_lineGroupBar_apply_eq₃ ha hd had hadD hdT h5 h₁ h₂ h₃
      h₁' h₂' h₃' h12 h13 h23 h12' h13' h23'
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ z
    refine ⟨r, r.2, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hz1; rwa [lineGroupBarAction_mk] at this
    · have := congrArg Subtype.val hz2; rwa [lineGroupBarAction_mk] at this
    · have := congrArg Subtype.val hz3; rwa [lineGroupBarAction_mk] at this

theorem rootLinesTorus_of_five_le (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h5 : 5 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) :
    ∃ h ∈ lineGroup D a d, orderOf h + 2 = (rootLines D a).ncard ∧
      L₁.map (MulAut.conj h).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj h).toMonoidHom = L₂ ∧
      ∀ L ∈ rootLines D a, ∀ L' ∈ rootLines D a, L ≠ L₁ → L ≠ L₂ → L' ≠ L₁ → L' ≠ L₂ →
        ∃ i < orderOf h, L.map (MulAut.conj (h ^ i)).toMonoidHom = L' := by
  have := hL.hyp.finite
  set ψ := hL.lineGroupBarAction ha d
  obtain ⟨z, hzo, hz1, hz2, hztr⟩ := hL.exists_lineGroupBar_torus_elt ha hd had hadD hdT h5 h₁ h₂
    h12
  obtain ⟨m, hm⟩ := hL.exists_ncard_rootLines ha
  have hodd : Odd (orderOf z) := by
    have h1 : orderOf z = 2 ^ m - 1 := by omega
    have hm1 : 1 ≤ m := by
      by_contra h0
      push Not at h0
      interval_cases m
      omega
    rw [h1]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  obtain ⟨r, hro, hzr, hrz⟩ := exists_lift_orderOf (hL.pow_two_pow_eq_one_of_mem_subgroupOf d)
    z hodd
  have hfix : ∀ L (hL' : L ∈ rootLines D a), ψ z ⟨L, hL'⟩ = ⟨L, hL'⟩ →
      L.map (MulAut.conj (r : G)).toMonoidHom = L := by
    intro L hL' hzL
    have hst : ψ z ∈ MulAction.stabilizer (Equiv.Perm (rootLines D a))
        (⟨L, hL'⟩ : rootLines D a) := hzL
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hrz
    have := Subgroup.zpow_mem _ hst j
    rw [← map_zpow, hj, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this
    have := congrArg Subtype.val this
    rwa [lineGroupBarAction_mk] at this
  refine ⟨r, r.2, by rw [Subgroup.orderOf_coe, hro]; exact hzo, hfix L₁ h₁ hz1, hfix L₂ h₂ hz2,
    fun L hL' L' hL'' hL1 hL2 hL1' hL2' => ?_⟩
  obtain ⟨i, -, hi⟩ := hztr L hL' hL1 hL2 L' hL'' hL1' hL2'
  have hzi : z ^ i ∈ Submonoid.powers (QuotientGroup.mk' _ r) :=
    mem_powers_iff_mem_zpowers.2 (Subgroup.pow_mem _ hzr i)
  obtain ⟨k₀, hk₀⟩ := (Submonoid.mem_powers_iff _ _).1 hzi
  set o := orderOf (QuotientGroup.mk' ((nCore D a).subgroupOf (lineGroup D a d)) r) with ho
  have hk : (QuotientGroup.mk' ((nCore D a).subgroupOf (lineGroup D a d)) r) ^ (k₀ % o) =
      z ^ i := by rw [ho, pow_mod_orderOf, hk₀]
  have hle : o ≤ orderOf r := Nat.le_of_dvd (orderOf_pos r) (orderOf_map_dvd _ _)
  refine ⟨k₀ % o, by rw [Subgroup.orderOf_coe]; exact (Nat.mod_lt _ (orderOf_pos _)).trans_le hle,
    ?_⟩
  have := congrArg Subtype.val hi
  rwa [← hk, ← map_pow, lineGroupBarAction_mk, Subgroup.coe_pow] at this

theorem rootLinesL2_of_eq_three (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : (rootLines D a).ncard = 3) :
    nCore D a ≤ lineGroup D a d ∧
      (∀ g ∈ lineGroup D a d,
        (∀ L ∈ rootLines D a, L.map (MulAut.conj g).toMonoidHom = L) ↔ g ∈ nCore D a) ∧
      (∃ f : lineGroup D a d →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
        Function.Surjective f ∧ f.ker = (nCore D a).subgroupOf (lineGroup D a d)) ∧
      ∀ L₁ ∈ rootLines D a, ∀ L₂ ∈ rootLines D a, ∀ L₃ ∈ rootLines D a,
      ∀ L₁' ∈ rootLines D a, ∀ L₂' ∈ rootLines D a, ∀ L₃' ∈ rootLines D a,
        L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → L₁' ≠ L₂' → L₁' ≠ L₃' → L₂' ≠ L₃' →
        ∃ g ∈ lineGroup D a d, L₁.map (MulAut.conj g).toMonoidHom = L₁' ∧
          L₂.map (MulAut.conj g).toMonoidHom = L₂' ∧
          L₃.map (MulAut.conj g).toMonoidHom = L₃' := by
  have := hL.hyp.finite
  have h3' : 3 ≤ (rootLines D a).ncard := h3.ge
  have hR := hL.nCore_le_lineGroup ha hd had hadD hdT h3'
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  have hro := hL.isElemAbRankOne_lineRadicalBar ha hd had hadD hdT h3' hT hT' (Ne.symm hne)
  have hcard : Nat.card (lineRadicalBar D a d (rootGroup D a ⊔ rootGroup D d)) = 2 := by
    have := hL.card_lineRadicalBar ha hd had hadD hdT h3' hT
    omega
  have hinj : Function.Injective (hL.lineGroupBarAction ha d) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have hzc := hL.ker_lineGroupBarAction_le_center ha hd had hadD hdT h3' hT hT' (Ne.symm hne) hz
    have hzn : ∀ H : Subgroup (lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)),
        z ∈ Subgroup.normalizer (H : Set _) := fun H => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [(Subgroup.mem_center_iff.1 hzc y).symm, mul_inv_cancel_right]
    have := Subgroup.mem_inf.2 ⟨hzn (lineRadicalBar D a d (rootGroup D a ⊔ rootGroup D d)),
      hzn (lineRadicalBar D a d T')⟩
    rw [hro.normalizer_inf_eq_hua, hro.hua_eq_bot_of_card_eq_two hcard] at this
    exact this
  have hcardR : Nat.card (lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)) = 6 :=
    hro.card_eq_six hcard
  have hbij : Function.Bijective (hL.lineGroupBarAction ha d) := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_perm, Nat.card_coe_set_eq, h3, hcardR]
    decide
  refine ⟨hR, fun g hg => ⟨fun hgL => ?_, fun hgM L hL' =>
    hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hgM) hL'⟩, ?_,
    fun L₁ h₁ L₂ h₂ L₃ h₃ L₁' h₁' L₂' h₂' L₃' h₃' h12 h13 h23 h12' h13' h23' => ?_⟩
  · have h1 : hL.lineGroupBarAction ha d (QuotientGroup.mk' _ ⟨g, hg⟩) = 1 := by
      ext L : 2
      rw [lineGroupBarAction_mk, Equiv.Perm.one_apply]
      exact hgL L.1 L.2
    have h2 := hinj (h1.trans (map_one _).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · have hU : Nat.card (upperUnipotent (GaloisField 2 1)) = 2 := by
      rw [RankOne.card_upperUnipotent, GaloisField.card 2 1 one_ne_zero]
      rfl
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_card_eq_two hro isElemAbRankOne_SL2_two hcard hU
    refine ⟨φ.toMonoidHom.comp (QuotientGroup.mk' _),
      φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · have hΛ : Nat.card (rootLines D a) = 3 := by rw [Nat.card_coe_set_eq, h3]
    obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_perm_of_three hΛ (x₁ := ⟨L₁, h₁⟩) (x₂ := ⟨L₂, h₂⟩)
      (x₃ := ⟨L₃, h₃⟩) (y₁ := ⟨L₁', h₁'⟩) (y₂ := ⟨L₂', h₂'⟩) (y₃ := ⟨L₃', h₃'⟩)
      (fun h' => h12 (congrArg Subtype.val h')) (fun h' => h13 (congrArg Subtype.val h'))
      (fun h' => h23 (congrArg Subtype.val h')) (fun h' => h12' (congrArg Subtype.val h'))
      (fun h' => h13' (congrArg Subtype.val h')) (fun h' => h23' (congrArg Subtype.val h'))
    obtain ⟨z, hz⟩ := hbij.2 σ
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ z
    refine ⟨r, r.2, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val ((congrArg (fun τ => τ ⟨L₁, h₁⟩) hz).trans hσ1)
      rwa [lineGroupBarAction_mk] at this
    · have := congrArg Subtype.val ((congrArg (fun τ => τ ⟨L₂, h₂⟩) hz).trans hσ2)
      rwa [lineGroupBarAction_mk] at this
    · have := congrArg Subtype.val ((congrArg (fun τ => τ ⟨L₃, h₃⟩) hz).trans hσ3)
      rwa [lineGroupBarAction_mk] at this

end TypeZero

end LineSetting

theorem ncard_rootLines_eq_three_of_lt_five {G : Type*} [Group G] {D : Set G}
    (hL : LineSetting G D) {a : G} (ha : a ∈ D) (h3 : 3 ≤ (rootLines D a).ncard)
    (h5 : ¬ 5 ≤ (rootLines D a).ncard) : (rootLines D a).ncard = 3 := by
  obtain ⟨m, hm⟩ := hL.exists_ncard_rootLines ha
  rcases m with _ | _ | m
  · simp at hm; omega
  · simpa using hm
  · have : 4 ≤ 2 ^ (m + 2) := by
      rw [pow_add]
      exact le_mul_of_one_le_left (by norm_num) Nat.one_le_two_pow
    omega

theorem rootLinesL2Step :
    ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
      ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a → 3 ≤ (rootLines D a).ncard →
        ∃ m : ℕ, 1 ≤ m ∧ (rootLines D a).ncard = 2 ^ m + 1 ∧ nCore D a ≤ lineGroup D a d ∧
          (∀ g ∈ lineGroup D a d,
            (∀ L ∈ rootLines D a, L.map (MulAut.conj g).toMonoidHom = L) ↔ g ∈ nCore D a) ∧
          (∃ f : lineGroup D a d →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m),
            Function.Surjective f ∧ f.ker = (nCore D a).subgroupOf (lineGroup D a d)) ∧
          ∀ L₁ ∈ rootLines D a, ∀ L₂ ∈ rootLines D a, ∀ L₃ ∈ rootLines D a,
          ∀ L₁' ∈ rootLines D a, ∀ L₂' ∈ rootLines D a, ∀ L₃' ∈ rootLines D a,
            L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → L₁' ≠ L₂' → L₁' ≠ L₃' → L₂' ≠ L₃' →
            ∃ g ∈ lineGroup D a d, L₁.map (MulAut.conj g).toMonoidHom = L₁' ∧
              L₂.map (MulAut.conj g).toMonoidHom = L₂' ∧ L₃.map (MulAut.conj g).toMonoidHom = L₃' := by
  intro G _ D hL a ha d hd had hadD hdT h3
  have := hL.nCore_subgroupOf_lineGroup_normal (a := a) d
  by_cases h5 : 5 ≤ (rootLines D a).ncard
  · exact hL.rootLinesL2_of_five_le ha hd had hadD hdT h5
  · have h3' := ncard_rootLines_eq_three_of_lt_five hL ha h3 h5
    obtain ⟨hR, hker, hf, htr⟩ := hL.rootLinesL2_of_eq_three ha hd had hadD hdT h3'
    exact ⟨1, le_rfl, by rw [h3']; rfl, hR, hker, hf, htr⟩

theorem rootLinesTorusStep : RootLinesTorusStep := by
  intro G _ D hL a ha d hd had hadD hdT h3 L₁ h₁ L₂ h₂ h12
  have := hL.nCore_subgroupOf_lineGroup_normal (a := a) d
  by_cases h5 : 5 ≤ (rootLines D a).ncard
  · exact hL.rootLinesTorus_of_five_le ha hd had hadD hdT h5 h₁ h₂ h12
  have h3' := ncard_rootLines_eq_three_of_lt_five hL ha h3 h5
  have h01 : 0 < orderOf (1 : G) := by rw [orderOf_one]; exact zero_lt_one
  refine ⟨1, Subgroup.one_mem _, by rw [orderOf_one, h3'], RankOne.map_conj_one L₁,
    RankOne.map_conj_one L₂, fun L hL' L' hL'' hL1 hL2 hL1' hL2' => ⟨0, h01, ?_⟩⟩
  rw [pow_zero, RankOne.map_conj_one]
  by_contra hLL
  have hsub : ({L₁, L₂, L, L'} : Set (Subgroup G)) ⊆ rootLines D a := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact hL'
    · exact hL''
  have h4 : ({L₁, L₂, L, L'} : Set (Subgroup G)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hLL]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hL2, Ne.symm hL2'⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, Ne.symm hL1, Ne.symm hL1'⟩
  have := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero (by omega))
  omega

end CFSG.Timmesfeld.Bridge
