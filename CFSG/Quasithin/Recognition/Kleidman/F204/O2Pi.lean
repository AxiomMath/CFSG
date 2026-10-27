module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Frat
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Form

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.OrderReductions.FrattiniAutomorphisms CFSG
  CFSG.QuasithinUnique.A5.Delta5

open scoped IsMulCommutative commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G}

abbrev TT (L1 L2 S Z : Subgroup G) (x0 : G) := ↥(Tsub L1 L2 S Z x0)

abbrev CC (L1 L2 S Z : Subgroup G) (x0 : G) := ↥(_root_.commutator (TT L1 L2 S Z x0))

section Pi

variable (F : Frame L1 L2 S D X) {x0 : G} (hx0 : x0 ∈ X)
include F hx0

theorem comm_le_PhiG (c : CC L1 L2 S Z x0) : (c : TT L1 L2 S Z x0).1 ∈ PhiG L1 L2 S := by
  let ι : TT L1 L2 S Z x0 →* ↥(Q1 L1 L2 S) := Subgroup.inclusion Tsub_le_Q1
  have hle : _root_.commutator (TT L1 L2 S Z x0) ≤ (frattini ↥(Q1 L1 L2 S)).comap ι := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    show ι ⁅g1, g2⁆ ∈ frattini ↥(Q1 L1 L2 S)
    rw [map_commutatorElement]
    refine CFSG.commutator_le_frattini_of_isPGroup (R := ↥(Q1 L1 L2 S)) (p := 2) ?_
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact ⟨ι c, hle c.2, rfl⟩

variable (hZ : ZData L1 L2 S Z) {a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
  (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1)
include hZ ha haQ hx05 hx01

theorem x0_centralizes_CC (c : CC L1 L2 S Z x0) :
    x0 * ((c : TT L1 L2 S Z x0) : G) * x0⁻¹ = ((c : TT L1 L2 S Z x0) : G) :=
  x0_centralizes_frattini hZ ha haQ hx0 hx05 F (comm_le_PhiG F hx0 c)

theorem CC_central (c : CC L1 L2 S Z x0) (σ : TT L1 L2 S Z x0) :
    (c : TT L1 L2 S Z x0) * σ = σ * (c : TT L1 L2 S Z x0) := by
  have hker : _root_.commutator (TT L1 L2 S Z x0) ≤ (psiT (Z := Z) F hx0).ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    exact comm_mem_ker (psiT (Z := Z) F hx0) g1 g2
  exact psiT_ker_central hZ ha haQ hx0 hx05 hx01 F _ (hker c.2) σ

theorem isElemAb_CC : IsElementaryAbelian 2 (CC L1 L2 S Z x0) := by
  have hcent := CC_central F hx0 hZ ha haQ hx05 hx01
  refine { toIsMulCommutative := ⟨⟨fun c1 c2 => Subtype.ext (hcent c1 c2)⟩⟩
           exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro c
  let K : Subgroup (TT L1 L2 S Z x0) :=
    { carrier := {t | (∀ σ : TT L1 L2 S Z x0, t * σ = σ * t) ∧ t * t = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun σ => ?_, ?_⟩
        · calc a * b * σ = a * (b * σ) := by group
            _ = a * (σ * b) := by rw [hb1]
            _ = (a * σ) * b := by group
            _ = (σ * a) * b := by rw [ha1]
            _ = σ * (a * b) := by group
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← ha1 b]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨fun σ => by simp, by simp⟩
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨fun σ => ?_, ?_⟩
        · have h := ha1 σ
          calc a⁻¹ * σ = a⁻¹ * (σ * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * σ) * a⁻¹ := by rw [h]
            _ = σ * a⁻¹ := by group
        · have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
          rw [this, ha2] }
  have hKn : K.Normal := ⟨fun n hn g => by
    have hc := hn.1 g
    have : g * n * g⁻¹ = n := by rw [← hc]; group
    rw [this]; exact hn⟩
  have hle : _root_.commutator (TT L1 L2 S Z x0) ≤ K := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    have hz : ∀ σ : TT L1 L2 S Z x0, ⁅g1, g2⁆ * σ = σ * ⁅g1, g2⁆ := fun σ =>
      hcent ⟨⁅g1, g2⁆, by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ σ
    refine ⟨hz, ?_⟩
    have hsq : psiT (Z := Z) F hx0 (g1 * g1) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      simp [toAdd_mul, O2Alg.add_self_eq_zero]
    have hg1 : ⁅g1 * g1, g2⁆ = ⁅g1, g2⁆ * ⁅g1, g2⁆ := comm_mul_mul_left hz
    rw [← hg1, commutatorElement_def]
    have := psiT_ker_central hZ ha haQ hx0 hx05 hx01 F (g1 * g1) hsq g2
    calc g1 * g1 * g2 * (g1 * g1)⁻¹ * g2⁻¹ = (g1 * g1 * g2) * (g1 * g1)⁻¹ * g2⁻¹ := rfl
      _ = (g2 * (g1 * g1)) * (g1 * g1)⁻¹ * g2⁻¹ := by rw [this]
      _ = 1 := by group
  have h2 := (hle c.2).2
  apply Subtype.ext
  show (c : TT L1 L2 S Z x0) ^ 2 = 1
  rw [pow_two]; exact h2

theorem d_mem_normalizer_Tsub {d : G} (hd : d ∈ D) :
    d ∈ Subgroup.normalizer ((Tsub L1 L2 S Z x0 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => d_conj_Tsub F hx0 hZ hd hh, fun hh => ?_⟩
  have := d_conj_Tsub F hx0 hZ (D.inv_mem hd) hh
  simpa [mul_assoc] using this

@[expose] noncomputable def dT {d : G} (hd : d ∈ D) : MulAut (TT L1 L2 S Z x0) :=
  (Tsub L1 L2 S Z x0).normalizerMonoidHom ⟨d, d_mem_normalizer_Tsub F hx0 hZ ha haQ hx05 hx01 hd⟩

@[expose] noncomputable def cdC {d : G} (hd : d ∈ D) : CC L1 L2 S Z x0 →* CC L1 L2 S Z x0 :=
  ((dT F hx0 hZ ha haQ hx05 hx01 hd).toMonoidHom.comp
    (_root_.commutator (TT L1 L2 S Z x0)).subtype).codRestrict _ (fun c => by
      have hfix := (inferInstance : (_root_.commutator (TT L1 L2 S Z x0)).Characteristic).fixed
        (dT F hx0 hZ ha haQ hx05 hx01 hd)
      have : (c : TT L1 L2 S Z x0) ∈
          (_root_.commutator (TT L1 L2 S Z x0)).comap
            (dT F hx0 hZ ha haQ hx05 hx01 hd).toMonoidHom := by rw [hfix]; exact c.2
      exact this)

theorem cdC_apply {d : G} (hd : d ∈ D) (c : CC L1 L2 S Z x0) :
    (((cdC F hx0 hZ ha haQ hx05 hx01 hd c : CC L1 L2 S Z x0) : TT L1 L2 S Z x0) : G) =
      d * ((c : TT L1 L2 S Z x0) : G) * d⁻¹ := rfl

theorem cdC_cube {d : G} (hd : d ∈ D) (c : CC L1 L2 S Z x0) :
    cdC F hx0 hZ ha haQ hx05 hx01 hd (cdC F hx0 hZ ha haQ hx05 hx01 hd
      (cdC F hx0 hZ ha haQ hx05 hx01 hd c)) = c := by
  apply Subtype.ext
  apply Subtype.ext
  rw [cdC_apply, cdC_apply, cdC_apply]
  have h3 : d ^ 3 = 1 := pow_three_of_mem_D F hd
  have h3' : d * d * d = 1 := by rw [← pow_three']; exact h3
  have : d * (d * (d * ((c : TT L1 L2 S Z x0) : G) * d⁻¹) * d⁻¹) * d⁻¹ =
      (d * d * d) * ((c : TT L1 L2 S Z x0) : G) * (d * d * d)⁻¹ := by group
  rw [this, h3']; simp

theorem exists_pi {d : G} (hd : d ∈ D) (h0 : CC L1 L2 S Z x0) (hh0 : h0 ≠ 1)
    (hfix : cdC F hx0 hZ ha haQ hx05 hx01 hd h0 = h0) :
    ∃ π : CC L1 L2 S Z x0 →* Multiplicative (ZMod 2), π h0 ≠ 1 ∧
      ∀ c, π (cdC F hx0 hZ ha haQ hx05 hx01 hd c) = π c := by
  have := isElemAb_CC F hx0 hZ ha haQ hx05 hx01
  have hne : (Additive.ofMul h0 : Additive (CC L1 L2 S Z x0)) ≠ 0 := by
    intro h; exact hh0 (by simpa using h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) (Additive (CC L1 L2 S Z x0)),
      f (Additive.ofMul h0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hcon)
  let π0 : CC L1 L2 S Z x0 →* Multiplicative (ZMod 2) :=
    { toFun := fun c => Multiplicative.ofAdd (f (Additive.ofMul c))
      map_one' := by simp
      map_mul' := fun a b => by simp [ofMul_mul] }
  let cd := cdC F hx0 hZ ha haQ hx05 hx01 hd
  refine ⟨π0 * π0.comp cd * π0.comp (cd.comp cd), ?_, fun c => ?_⟩
  · have h1 : π0 h0 ≠ 1 := by
      intro h
      apply hf
      have := congrArg Multiplicative.toAdd h
      simpa [π0] using this
    show π0 h0 * π0 (cd h0) * π0 (cd (cd h0)) ≠ 1
    have hcd : cd h0 = h0 := hfix
    rw [hcd, hcd]
    have hsq : ∀ z : Multiplicative (ZMod 2), z * z = 1 := by decide
    intro h
    apply h1
    calc π0 h0 = π0 h0 * (π0 h0 * π0 h0) := by rw [hsq, mul_one]
      _ = π0 h0 * π0 h0 * π0 h0 := by rw [mul_assoc]
      _ = 1 := h
  · show π0 (cd c) * π0 (cd (cd c)) * π0 (cd (cd (cd c))) = π0 c * π0 (cd c) * π0 (cd (cd c))
    have := cdC_cube F hx0 hZ ha haQ hx05 hx01 hd c
    rw [this, mul_comm (π0 (cd c) * π0 (cd (cd c))), mul_assoc]

end Pi

end CFSG.Quasithin.Kleidman.F204
