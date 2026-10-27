module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreS3

public section
namespace CFSG.Quasithin.F53Push
open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin CFSG.Quasithin.F53Mod
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]

theorem perm3_prod_pow_three : ∀ t u : Equiv.Perm (Fin 3), t * t = 1 → u * u = 1 → t ≠ 1 → u ≠ 1 →
    t ≠ u → (t * u) ^ 3 = 1 := by
  decide

theorem perm3_prod_ne_one : ∀ t u : Equiv.Perm (Fin 3), t * t = 1 → u * u = 1 → t ≠ 1 → u ≠ 1 →
    t ≠ u → t * u ≠ 1 := by
  decide

theorem perm3_prod_order_three {t u : Equiv.Perm (Fin 3)} (ht : t * t = 1) (hu : u * u = 1)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) : (t * u) ^ 3 = 1 ∧ t * u ≠ 1 :=
  ⟨perm3_prod_pow_three t u ht hu ht1 hu1 htu, perm3_prod_ne_one t u ht hu ht1 hu1 htu⟩

theorem mem_core_of_mem_ker_s3 {X P Z : Subgroup G} (h : PushHyp X P Z)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : ↥X} (hx : (isSec_zZero h).conjHom x = 1) :
    (x : G) ∈ pCoreOf 2 X := by
  have two : ∀ y : ↥X, (isSec_zZero h).conjHom y = 1 → ∃ k : ℕ, toS3 e y ^ 2 ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_ker h hy
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  rw [← toS3_eq_one_iff e x.2]
  by_contra hne
  obtain ⟨k, hk⟩ := two x hx
  have ht : toS3 e x * toS3 e x = 1 := (perm3_eq_one_or_involution hk).resolve_left hne
  obtain ⟨u, hu⟩ := toS3_surjective e cyc3
  set x' : ↥X := u * x * u⁻¹ with hx'
  have hx'k : (isSec_zZero h).conjHom x' = 1 := by rw [hx', map_mul, map_mul, hx]; simp
  have hθx' : toS3 e x' = cyc3 * toS3 e x * cyc3⁻¹ := by rw [hx', map_mul, map_mul, map_inv, hu]
  have hne' : toS3 e x' ≠ toS3 e x := by
    rw [hθx']
    exact perm3_conj_ne _ _ ht hne cyc3_pow_three cyc3_ne_one
  have ht1' : toS3 e x' ≠ 1 := by
    intro h1
    apply hne
    rw [hθx'] at h1
    have := congrArg (fun a => cyc3⁻¹ * a * cyc3) h1
    simpa [mul_assoc] using this
  obtain ⟨k', hk'⟩ := two x' hx'k
  have ht' : toS3 e x' * toS3 e x' = 1 := (perm3_eq_one_or_involution hk').resolve_left ht1'
  obtain ⟨h3, hne3⟩ := perm3_prod_order_three ht ht' hne ht1' hne'.symm
  have hxx' : (isSec_zZero h).conjHom (x * x') = 1 := by rw [map_mul, hx, hx'k, mul_one]
  obtain ⟨k'', hk''⟩ := two (x * x') hxx'
  rw [map_mul] at hk''
  exact hne3 (perm3_eq_one_of_pow h3 hk'')


open Module in
theorem exists_mulEquiv_pi_zmod_two {W : Type} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hsq : ∀ w : W, w * w = 1) {n : ℕ} (hcard : Nat.card W = 2 ^ n) :
    Nonempty (W ≃* Multiplicative (Fin n → ZMod 2)) := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    have := hsq (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [two_nsmul, pow_two] using this
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive W) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    have h3 : Nat.card (Additive W) = 2 ^ n := hcard
    rw [h3, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  let l : Additive W ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hfr).equivFun
  exact ⟨AddEquiv.toMultiplicative l.toAddEquiv⟩

theorem perm_zmod2_aux : ∀ g : Equiv.Perm (Fin 2 → ZMod 2), (∀ x y, g (x + y) = g x + g y) →
    (!![g ![1, 0] 0, g ![0, 1] 0; g ![1, 0] 1, g ![0, 1] 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)).det
      = 1 ∧
    ∀ w, g w = (!![g ![1, 0] 0, g ![0, 1] 0; g ![1, 0] 1, g ![0, 1] 1] :
      Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec w := by
  decide +kernel

theorem additive_perm_eq_slPerm (g : Equiv.Perm (Fin 2 → ZMod 2))
    (hg : ∀ x y, g (x + y) = g x + g y) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), g = slPerm (ZMod 2) A := by
  obtain ⟨hdet, hmul⟩ := perm_zmod2_aux g hg
  refine ⟨(⟨!![g ![1, 0] 0, g ![0, 1] 0; g ![1, 0] 1, g ![0, 1] 1], hdet⟩ :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)), ?_⟩
  ext w : 1
  exact hmul w

theorem card_specialLinear_zmod2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem s3_relIndex {X P Z : Subgroup G} (h : PushHyp X P Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    P ≠ ⊥ ∧ P.relIndex X = 3 := by
  have h2 := relIndex_core_sylow h e
  have h6 := relIndex_core_eq_six e
  constructor
  · rintro rfl
    have : pCoreOf 2 X = ⊥ := le_bot_iff.mp h.core_le
    rw [this] at h2
    simp at h2
  · have := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) P X h.core_le h.le_self
    rw [h2, h6] at this
    omega

theorem card_secW_s3 {X P Z : Subgroup G} (h : PushHyp X P Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hnc : NoCharNormal P X) : Nat.card (isSec_zZero h).W = 2 ^ 2 := by
  obtain ⟨hP, -⟩ := s3_relIndex h e
  have h4 := (pu1_s3 h ⟨e⟩ (not_le_core_of_noCharNormal h hP hnc)).2.2
  have : Nat.card (isSec_zZero h).W = (zZero X Z).relIndex Z := by
    show Nat.card (↥Z ⧸ (zZero X Z).subgroupOf Z) = ((zZero X Z).subgroupOf Z).index
    exact (Subgroup.index_eq_card _).symm
  rw [this]
  exact h4

theorem exists_alpha_s3 {X P Z : Subgroup G} (h : PushHyp X P Z)
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (hnc : NoCharNormal P X) :
    ∃ (c : (isSec_zZero h).W ≃* Multiplicative (Fin 2 → ZMod 2))
      (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      (∀ g, coordActHom c ((isSec_zZero h).conjHom g) = slPerm (ZMod 2) (α g)) ∧
      Function.Surjective α ∧ ∀ g : ↥X, α g = 1 ↔ (g : G) ∈ pCoreOf 2 X := by
  have hs := isSec_zZero h
  have hsq : ∀ w : hs.W, w * w = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_mul, hs.proj_eq_one_iff]
    simpa [pow_two] using hs.sq x x.2
  have hfin : Finite hs.W := by
    have := hs.normal_subgroupOf
    exact (inferInstance : Finite (↥Z ⧸ (zZero X Z).subgroupOf Z))
  obtain ⟨c⟩ := exists_mulEquiv_pi_zmod_two (W := hs.W) (fun a b => mul_comm a b) hsq
    (card_secW_s3 h e hnc)
  let a : ↥X →* Equiv.Perm (Fin 2 → ZMod 2) := (coordActHom c).comp hs.conjHom
  obtain ⟨α, hα⟩ := exists_hom_sl2 a (fun g => additive_perm_eq_slPerm _ (coordAct_add c _))
  have hker : ∀ g : ↥X, α g = 1 ↔ (g : G) ∈ pCoreOf 2 X := by
    intro g
    have h1 : α g = 1 ↔ hs.conjHom g = 1 := by
      constructor
      · intro hg
        have h2 : coordActHom c (hs.conjHom g) = 1 := by
          have := hα g
          rw [hg, map_one] at this
          exact this
        ext w
        have h5 : Multiplicative.toAdd (c (hs.conjHom g (c.symm
            (Multiplicative.ofAdd (Multiplicative.toAdd (c w)))))) = Multiplicative.toAdd (c w) :=
          congrArg (fun f => f (Multiplicative.toAdd (c w))) h2
        simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h5
        rw [MulAut.one_apply]
        exact c.injective (Multiplicative.toAdd.injective h5)
      · intro hg
        apply slPerm_injective (k := ZMod 2)
        rw [← hα g]
        show coordActHom c (hs.conjHom g) = _
        rw [hg, map_one, map_one]
    rw [h1]
    constructor
    · exact mem_core_of_mem_ker_s3 h e
    · intro hg
      rw [mem_ker_conjHom_iff h]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hg) x hx
      have e1 : (g : G) * x * (g : G)⁻¹ * x⁻¹ = 1 := by
        rw [← this]; group
      rw [e1]
      exact (zZero X Z).one_mem
  refine ⟨c, α, hα, ?_, hker⟩
  have hk : α.ker = (pCoreOf 2 X).subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hrange : Nat.card α.range = 6 := by
    rw [← Subgroup.index_ker, hk]
    exact relIndex_core_eq_six e
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ (by rw [hrange, card_specialLinear_zmod2])

omit [Finite G] in
theorem index_three_max {H : Type*} [Group H] {R : Subgroup H} (h3 : R.index = 3) :
    R < ⊤ ∧ ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ R := by
  refine ⟨lt_top_iff_ne_top.mpr fun h => ?_, fun Y hRY hY => ?_⟩
  · rw [h, Subgroup.index_top] at h3
    omega
  · have hdvd : Y.index ∣ R.index := Subgroup.index_dvd_of_le hRY
    rw [h3] at hdvd
    have hY1 : Y.index ≠ 1 := fun h1 => (lt_top_iff_ne_top.mp hY) (Subgroup.index_eq_one.mp h1)
    have hY3 : Y.index = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hY1
    have := Subgroup.relIndex_mul_index hRY
    rw [hY3, h3] at this
    have h1 : R.relIndex Y = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp h1)

theorem baumann_c_s3 {X P Z : Subgroup G} (h : PushHyp X P Z)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) (hnc : NoCharNormal P X) :
    BaumannC X Z := by
  obtain ⟨e⟩ := hq
  obtain ⟨hP, hidx⟩ := s3_relIndex h e
  obtain ⟨c, α, hα, hαs, hαk⟩ := exists_alpha_s3 h e hnc
  have hR3 : (P.subgroupOf X).index = 3 := hidx
  obtain ⟨hlt, hmax⟩ := index_three_max hR3
  exact baumannC_of_coords h hP hnc ⟨P.subgroupOf X, le_rfl, hlt, hmax⟩ c α hα hαs hαk

theorem baumannS3_holds (G : Type) [Group G] [Finite G] : BaumannS3 G :=
  fun _ _ _ h hq hnc => baumann_c_s3 h hq hnc

end CFSG.Quasithin.F53Push
