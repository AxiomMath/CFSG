module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QJ
public import CFSG.Quasithin.Vol2.Ch6NatLift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Campbell (slPerm slPerm_apply)
open CFSG.QuasithinUnique.Setup.Offender (IsSemilinearWith)
open scoped MatrixGroups

variable {G : Type} [Group G]

namespace QCoord

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

omit [Group G] in
theorem slPerm_mulVec_ch615 (A : SL(2, F)) (w : Fin 2 → F) :
    slPerm F A w = (A : Matrix (Fin 2) (Fin 2) F).mulVec w := by
  rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  rfl

noncomputable abbrev permKer615 (hc : QCoord L N S F ψ Y) : Subgroup G :=
  hc.permHom.ker.map (normNL N L).subtype

theorem mem_permKer615_iff (hc : QCoord L N S F ψ Y) {g : G} :
    g ∈ hc.permKer615 ↔ ∃ h : g ∈ normNL N L, hc.permHom ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem normNL_le_normalizer_permKer615 [Finite G] (hc : QCoord L N S F ψ Y) :
    normNL N L ≤ Subgroup.normalizer (hc.permKer615 : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem_ch6 fun k hk => ?_
  obtain ⟨hkN, hk1⟩ := hc.mem_permKer615_iff.mp hk
  refine hc.mem_permKer615_iff.mpr ⟨(normNL N L).mul_mem ((normNL N L).mul_mem hg hkN)
    ((normNL N L).inv_mem hg), ?_⟩
  have e : (⟨g * k * g⁻¹, (normNL N L).mul_mem ((normNL N L).mul_mem hg hkN)
      ((normNL N L).inv_mem hg)⟩ : ↥(normNL N L)) = ⟨g, hg⟩ * ⟨k, hkN⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel]

theorem inf_permKer615_le (hc : QCoord L N S F ψ Y) :
    L ⊓ hc.permKer615 ≤ Subgroup.centralizer (N : Set G) := by
  rintro g ⟨hgL, hgK⟩
  obtain ⟨hgN, hg1⟩ := hc.mem_permKer615_iff.mp hgK
  rw [hc.permHom_of_mem g hgN hgL] at hg1
  have h1 : ψ (autHom hc.le_normalizer ⟨g, hgL⟩) = 1 := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun π : Equiv.Perm (Fin 2 → F) => π (Pi.single j 1) i) hg1
    simp only [slPerm_mulVec_ch615, Equiv.Perm.one_apply] at this
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  have h2 : autHom hc.le_normalizer ⟨g, hgL⟩ = 1 := ψ.injective (by rw [h1, map_one])
  exact mem_centralizer_of_autHom_eq_one hc.le_normalizer h2

theorem permHom_normalizes_ch615 (hc : QCoord L N S F ψ Y) (y : ↥(normNL N L))
    (g : SL(2, F)) :
    ∃ g' : SL(2, F), (hc.permHom y)⁻¹ * slPerm F g * hc.permHom y = slPerm F g' := by
  have hLN := hc.le_normalizer
  obtain ⟨l₀, hl₀L, hl₀⟩ := mem_autOn_iff.mp (ψ.symm g).2
  have hlNL : (l₀ : G) ∈ normNL N L := ⟨l₀.2, Subgroup.le_normalizer hl₀L⟩
  have hψl : ψ (autHom hLN ⟨l₀, hl₀L⟩) = g := by
    have : autHom hLN ⟨l₀, hl₀L⟩ = ψ.symm g := Subtype.ext hl₀
    rw [this, MulEquiv.apply_symm_apply]
  have hyL : (y : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ y.2.2
  have hyl : (y : G)⁻¹ * l₀ * (y : G)⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hyL _).mp hl₀L
  have hyl' : (y : G)⁻¹ * l₀ * y ∈ L := by simpa using hyl
  have hylNL : (y : G)⁻¹ * l₀ * y ∈ normNL N L :=
    (normNL N L).mul_mem ((normNL N L).mul_mem ((normNL N L).inv_mem y.2) hlNL) y.2
  refine ⟨ψ (autHom hLN ⟨_, hyl'⟩), ?_⟩
  rw [← hψl, ← hc.permHom_of_mem _ hlNL hl₀L, ← hc.permHom_of_mem _ hylNL hyl', ← map_inv,
    ← map_mul, ← map_mul]
  rfl

theorem isSemilinearWith_refl_ch615 [Finite G] [Finite F] {T D : Subgroup G}
    (hc : QCoord L N (T ⊓ L) F ψ Y) (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T)
    (hS : IsSylowTwoOf (T ⊓ L) L) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {z : G}
    (hzN : z ∈ N) (hz1 : Multiplicative.toAdd (Y ⟨z, hzN⟩) 1 = 0)
    (hz0 : Multiplicative.toAdd (Y ⟨z, hzN⟩) ≠ 0) (y : ↥(normNL N L))
    (hyz : (y : G) * z * (y : G)⁻¹ = z)
    (hyD : ∀ δ ∈ D, (y : G) * δ * (y : G)⁻¹ * δ⁻¹ * z = z * ((y : G) * δ * (y : G)⁻¹ * δ⁻¹)) :
    IsSemilinearWith (hc.permHom y) (RingEquiv.refl F) := by
  obtain ⟨σ, hσ⟩ := CFSG.CGT.PushingUpLit.BHS.exists_isSemilinearWith_of_normalizes
    (hc.permHom y) (hc.permHom_add y) (hc.permHom_normalizes_ch615 y)
  have hLN := hc.le_normalizer
  set v₀ := Multiplicative.toAdd (Y ⟨z, hzN⟩) with hv₀
  have hyv : hc.permHom y v₀ = v₀ := by
    rw [hv₀, ← hc.permHom_spec]
    congr 2
    exact Subtype.ext (by rw [conjAct_apply_coe]; exact hyz)
  have hyz' : (y : G)⁻¹ * z * y = z := by
    calc (y : G)⁻¹ * z * y = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * y := by rw [hyz]
      _ = z := by group
  have hσc : ∀ c : F, σ c = c := by
    intro c
    by_cases hc0 : c = 0
    · rw [hc0, map_zero]
    obtain ⟨δ, hδD, hδc⟩ := hc.exists_mem_D hC hS hD hc0
    have hδL : δ ∈ L := (Subgroup.mem_inf.mp (hD.1 hδD)).1
    have hδN : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp (hD.1 hδD)).2
    set w : ↥N := ((autHom hLN ⟨δ, hδL⟩ : ↥(autOn L N)) : MulAut ↥N) ⟨z, hzN⟩ with hw
    have hYw : Multiplicative.toAdd (Y w) = c • v₀ := by
      rw [hw, hc.toAdd_Y_line hδL hδN _ hz1, hδc]
    set e : G := (y : G) * δ * (y : G)⁻¹ * δ⁻¹ with he
    have heL : e ∈ L := by
      have h1 : (y : G) * δ * (y : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp y.2.2 δ).mp hδL
      exact L.mul_mem h1 (L.inv_mem hδL)
    have h1 : hc.permHom y (Multiplicative.toAdd (Y w)) = σ c • v₀ := by
      rw [hYw, hσ, hyv]
    have h2 : hc.permHom y (Multiplicative.toAdd (Y w)) = c • v₀ := by
      rw [← hc.permHom_spec]
      have e1 : conjAct N ⟨y, y.2.1⟩ w =
          ((autHom hLN ⟨e, heL⟩ : ↥(autOn L N)) : MulAut ↥N) w := by
        apply Subtype.ext
        rw [conjAct_apply_coe, autHom_apply_coe, hw, autHom_apply_coe]
        show (y : G) * (δ * z * δ⁻¹) * (y : G)⁻¹ =
          (y : G) * δ * (y : G)⁻¹ * δ⁻¹ * (δ * z * δ⁻¹) * ((y : G) * δ * (y : G)⁻¹ * δ⁻¹)⁻¹
        calc (y : G) * (δ * z * δ⁻¹) * (y : G)⁻¹ =
            (y : G) * δ * ((y : G)⁻¹ * z * y) * δ⁻¹ * (y : G)⁻¹ := by rw [hyz']; group
          _ = (y : G) * δ * (y : G)⁻¹ * δ⁻¹ * (δ * z * δ⁻¹) *
              ((y : G) * δ * (y : G)⁻¹ * δ⁻¹)⁻¹ := by group
      have hez : ((autHom hLN ⟨e, heL⟩ : ↥(autOn L N)) : MulAut ↥N) ⟨z, hzN⟩ = ⟨z, hzN⟩ := by
        apply Subtype.ext
        rw [autHom_apply_coe]
        show e * z * e⁻¹ = z
        rw [hyD δ hδD, mul_inv_cancel_right]
      rw [e1, hc.intertwine, hYw, Matrix.mulVec_smul, ← hc.intertwine, hez]
    have h3 : σ c • v₀ = c • v₀ := h1.symm.trans h2
    exact smul_left_injective F hz0 h3
  have hσ1 : σ = RingEquiv.refl F := RingEquiv.ext hσc
  rw [← hσ1]
  exact hσ

theorem permHom_single_ch615 [Finite G] [Finite F] {T D : Subgroup G}
    (hc : QCoord L N (T ⊓ L) F ψ Y) (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T)
    (hS : IsSylowTwoOf (T ⊓ L) L) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {z : G}
    (hzN : z ∈ N) (hz1 : Multiplicative.toAdd (Y ⟨z, hzN⟩) 1 = 0)
    (hz0 : Multiplicative.toAdd (Y ⟨z, hzN⟩) ≠ 0) (y : ↥(normNL N L))
    (hyz : (y : G) * z * (y : G)⁻¹ = z)
    (hyD : ∀ δ ∈ D, (y : G) * δ * (y : G)⁻¹ * δ⁻¹ * z = z * ((y : G) * δ * (y : G)⁻¹ * δ⁻¹)) :
    hc.permHom y (Pi.single 0 1) = Pi.single 0 1 := by
  have hlin := hc.isSemilinearWith_refl_ch615 hC hS hD hzN hz1 hz0 y hyz hyD
  set v₀ := Multiplicative.toAdd (Y ⟨z, hzN⟩) with hv₀
  have hyv : hc.permHom y v₀ = v₀ := by
    rw [hv₀, ← hc.permHom_spec]
    congr 2
    exact Subtype.ext (by rw [conjAct_apply_coe]; exact hyz)
  have ha : v₀ 0 ≠ 0 := by
    intro h0
    apply hz0
    funext i
    fin_cases i
    · exact h0
    · exact hz1
  have hv : v₀ = v₀ 0 • Pi.single 0 1 := by
    funext i
    fin_cases i
    · simp
    · simp [hz1]
  have h1 : v₀ 0 • hc.permHom y (Pi.single 0 1) = v₀ 0 • Pi.single 0 1 := by
    have := hlin (v₀ 0) (Pi.single 0 1)
    rw [← hv, hyv] at this
    rw [← hv]
    exact this.symm
  exact smul_right_injective _ ha h1

end QCoord

omit [Group G] in
theorem eq_one_of_pow_prime_ch615 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b : Equiv.Perm (Fin 2 → F)}
    (hadd : ∀ w w' : Fin 2 → F, b (w + w') = b w + b w')
    (hlin : IsSemilinearWith b (RingEquiv.refl F)) (he₀ : b (Pi.single 0 1) = Pi.single 0 1)
    {p : ℕ} (hp2 : Odd p) (hpF : Nat.Coprime p (Nat.card F - 1)) (hb : b ^ p = 1) : b = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set u := b (Pi.single 1 1) with hu
  have hbw : ∀ w : Fin 2 → F, b w = w 0 • Pi.single 0 1 + w 1 • u := by
    intro w
    have := CFSG.CGT.PushingUpLit.BHS.apply_eq_of_isSemilinearWith hadd hlin w
    rw [this, he₀]
    rfl
  have h2 : ∀ (k : ℕ) (w : Fin 2 → F), (b ^ k) w 1 = u 1 ^ k * w 1 := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hbw]
      simp [pow_succ]
      ring
  have hγp : u 1 ^ p = 1 := by
    have := h2 p (Pi.single 1 1)
    rw [hb] at this
    simpa using this.symm
  have hγ0 : u 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.pos_of_ne_zero (fun h => by simp [h] at hp2)).ne'] at hγp
    exact zero_ne_one hγp
  have hγq : u 1 ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hγ0
  have hγ : u 1 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hγp, hγq⟩
    rwa [hpF, pow_one] at this
  have h1 : ∀ (k : ℕ) (w : Fin 2 → F), (b ^ k) w 0 = w 0 + (k : F) * w 1 * u 0 := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hbw]
      simp [hγ]
      ring
  have hp1 : (p : F) = 1 := by
    rw [CharP.cast_eq_mod F 2, Nat.odd_iff.mp hp2, Nat.cast_one]
  have hu0 : u 0 = 0 := by
    have := h1 p (Pi.single 1 1)
    rw [hb, hp1] at this
    simpa using this.symm
  refine Equiv.ext fun w => ?_
  rw [hbw, Equiv.Perm.one_apply]
  funext i
  fin_cases i <;> simp [hu0, hγ]

namespace QCoord

variable {L N : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

omit [Group G] in
theorem upper_pow_ch615 {A : Matrix (Fin 2) (Fin 2) F} (hA : A 1 0 = 0) (k : ℕ) :
    (A ^ k) 0 0 = A 0 0 ^ k ∧ (A ^ k) 1 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, ih.1,
      ih.2, hA]
    constructor <;> ring

theorem exists_orderOf_eq_ch615 [Finite G] [Finite F] {T D : Subgroup G}
    (hc : QCoord L N (T ⊓ L) F ψ Y) (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T)
    (hS : IsSylowTwoOf (T ⊓ L) L) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card F - 1) : ∃ d ∈ D, orderOf d = p := by
  have hLN := hc.le_normalizer
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [Nat.card_units]; exact hp)
  obtain ⟨δ, hδD, hδc⟩ := hc.exists_mem_D hC hS hD (Units.ne_zero c₀)
  have hδL : δ ∈ L := (Subgroup.mem_inf.mp (hD.1 hδD)).1
  have hδN : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (hD.1 hδD)).2
  set m := orderOf δ with hm
  have hm0 : m ≠ 0 := (orderOf_pos δ).ne'
  have hpow : (⟨δ, hδL⟩ : ↥L) ^ m = 1 := Subtype.ext (by simp [hm, pow_orderOf_eq_one])
  have hψ : (ψ (autHom hLN ⟨δ, hδL⟩)) ^ m = 1 := by
    rw [← map_pow, ← map_pow, hpow, map_one, map_one]
  have hup := upper_pow_ch615 (hc.upper hδL hδN) m
  have h1 : ((ψ (autHom hLN ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F) ^ m) 0 0 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hψ]
    simp
  rw [hup.1, hδc] at h1
  have hc₀m : c₀ ^ m = 1 := Units.ext (by simpa using h1)
  have hpm : p ∣ m := hc₀ ▸ orderOf_dvd_of_pow_eq_one hc₀m
  exact ⟨δ ^ (m / p), D.pow_mem hδD _, orderOf_pow_orderOf_div hm0 hpm⟩

theorem permHom_eq_one_ch615 [Finite G] [Finite F] [CharP F 2] {T D : Subgroup G}
    (hc : QCoord L N (T ⊓ L) F ψ Y) (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T)
    (hS : IsSylowTwoOf (T ⊓ L) L) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {z : G}
    (hzN : z ∈ N) (hz1 : Multiplicative.toAdd (Y ⟨z, hzN⟩) 1 = 0)
    (hz0 : Multiplicative.toAdd (Y ⟨z, hzN⟩) ≠ 0) (y : ↥(normNL N L))
    (hyz : (y : G) * z * (y : G)⁻¹ = z)
    (hyD : ∀ δ ∈ D, (y : G) * δ * (y : G)⁻¹ * δ⁻¹ * z = z * ((y : G) * δ * (y : G)⁻¹ * δ⁻¹))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F - 1) (hyp : y ^ p = 1) :
    hc.permHom y = 1 := by
  refine eq_one_of_pow_prime_ch615 (hc.permHom_add y)
    (hc.isSemilinearWith_refl_ch615 hC hS hD hzN hz1 hz0 y hyz hyD)
    (hc.permHom_single_ch615 hC hS hD hzN hz1 hz0 y hyz hyD) (hp.odd_of_ne_two hp2)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpF) ?_
  rw [← map_pow, hyp, map_one]

end QCoord

end CFSG.Quasithin.H13
