module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique.B113Lie.Sp
  CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

private lemma spForm_sigma {n : ℕ} {F : Type} [Field F] (c : F) :
    (spForm n F).σ c = c := rfl

private lemma one_add_mul_inv_form {E : Type*} [Ring E] (X : E) :
    (1 + X) * (1 - X + X * X) = 1 + X * X * X := by
  noncomm_ring

private lemma rad_sub_one_mem_perp {n : ℕ} {F : Type} [Field F]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {q : StatedSp n F} (hq : q ∈ sprad (Submodule.span F {a₁, a₂}) hW)
    (v : Fin n ⊕ Fin n → F) :
    (natRep (StatedSp n F) q - 1) v ∈
      (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
  rw [(spForm n F).mem_perp]
  intro w hw
  have hqinv : (natRep (StatedSp n F) q⁻¹) w = w := (inv_mem hq).1 w hw
  have hiso := isIsometric_natRep_statedSp n F q ((natRep (StatedSp n F) q⁻¹) w) v
  have hgg : natRep (StatedSp n F) q (natRep (StatedSp n F) q⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hgg, hqinv] at hiso
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  rw [(spForm n F).β_sub_right, hiso, sub_self]

private lemma rad_sub_one_mem_of_mem_perp {n : ℕ} {F : Type} [Field F]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {q : StatedSp n F} (hq : q ∈ sprad (Submodule.span F {a₁, a₂}) hW)
    (v : Fin n ⊕ Fin n → F)
    (hv : v ∈ (spForm n F).perp (Submodule.span F {a₁, a₂})) :
    (natRep (StatedSp n F) q - 1) v ∈ Submodule.span F {a₁, a₂} := by
  simpa only [LinearMap.sub_apply, Module.End.one_apply] using hq.2 v hv

private lemma rad_sub_one_eq_zero_of_mem {n : ℕ} {F : Type} [Field F]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {q : StatedSp n F} (hq : q ∈ sprad (Submodule.span F {a₁, a₂}) hW)
    (v : Fin n ⊕ Fin n → F) (hv : v ∈ Submodule.span F {a₁, a₂}) :
    (natRep (StatedSp n F) q - 1) v = 0 := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, hq.1 v hv, sub_self]

private lemma mul_three_eq_zero {n : ℕ} {F : Type} [Field F]
    {A : Submodule F (Fin n ⊕ Fin n → F)} {U W Z : Module.End F (Fin n ⊕ Fin n → F)}
    (hU : ∀ a ∈ A, U a = 0)
    (hW : ∀ v ∈ (spForm n F).perp A, W v ∈ A)
    (hZ : ∀ v, Z v ∈ (spForm n F).perp A) :
    U * W * Z = 0 := by
  refine LinearMap.ext fun v => ?_
  exact hU _ (hW _ (hZ v))

private lemma natRep_inv_eq {n : ℕ} {F : Type} [Field F]
    (q : StatedSp n F) (X : Module.End F (Fin n ⊕ Fin n → F))
    (hq : natRep (StatedSp n F) q = 1 + X) (hX : X * X * X = 0) :
    natRep (StatedSp n F) q⁻¹ = 1 - X + X * X := by
  have hmul : natRep (StatedSp n F) q * (1 - X + X * X) = 1 := by
    rw [hq]
    have h : (1 + X) * (1 - X + X * X) = 1 + X * X * X := one_add_mul_inv_form X
    rw [h, hX, add_zero]
  calc natRep (StatedSp n F) q⁻¹
      = natRep (StatedSp n F) q⁻¹ * 1 := (mul_one _).symm
    _ = natRep (StatedSp n F) q⁻¹ * (natRep (StatedSp n F) q * (1 - X + X * X)) := by
          rw [hmul]
    _ = (natRep (StatedSp n F) q⁻¹ * natRep (StatedSp n F) q) * (1 - X + X * X) := by
          rw [mul_assoc]
    _ = 1 * (1 - X + X * X) := by rw [← map_mul, inv_mul_cancel, map_one]
    _ = 1 - X + X * X := one_mul _

private theorem commutator_expansion {E : Type*} [Ring E] (X Y : E)
    (hXXX : X * X * X = 0) (hXXY : X * X * Y = 0) (hXYX : X * Y * X = 0)
    (hXYY : X * Y * Y = 0) (hYXX : Y * X * X = 0) (hYXY : Y * X * Y = 0)
    (hYYY : Y * Y * Y = 0) :
    (1 + X) * (1 + Y) * (1 - X + X * X) * (1 - Y + Y * Y) = 1 + (X * Y - Y * X) := by
  set T : E := 1 - X + X * X with hT
  set S : E := 1 - Y + Y * Y with hS
  have hXT : (1 + X) * T = 1 := by
    rw [hT]
    have : (1 + X) * (1 - X + X * X) = 1 + X * X * X := by noncomm_ring
    rw [this, hXXX, add_zero]
  have hYS : (1 + Y) * S = 1 := by
    rw [hS]
    have : (1 + Y) * (1 - Y + Y * Y) = 1 + Y * Y * Y := by noncomm_ring
    rw [this, hYYY, add_zero]
  have hYT : (1 + Y) * T = T * (1 + Y) + (X * Y - Y * X) := by
    rw [hT]
    have h : (1 + Y) * (1 - X + X * X)
        = (1 - X + X * X) * (1 + Y) + (X * Y - Y * X) + (Y * X * X - X * X * Y) := by
      noncomm_ring
    rw [h, hYXX, hXXY]
    abel
  have hXZ : (1 + X) * (X * Y - Y * X) = X * Y - Y * X := by
    have h : (1 + X) * (X * Y - Y * X)
        = (X * Y - Y * X) + (X * X * Y - X * Y * X) := by noncomm_ring
    rw [h, hXXY, hXYX, sub_zero, add_zero]
  have hZS : (X * Y - Y * X) * S = X * Y - Y * X := by
    rw [hS]
    have h : (X * Y - Y * X) * (1 - Y + Y * Y)
        = (X * Y - Y * X) - (X * Y - Y * X) * Y + (X * Y - Y * X) * Y * Y := by
      noncomm_ring
    have h1 : (X * Y - Y * X) * Y = 0 := by
      have : (X * Y - Y * X) * Y = X * Y * Y - Y * X * Y := by noncomm_ring
      rw [this, hXYY, hYXY, sub_zero]
    have h2 : (X * Y - Y * X) * Y * Y = 0 := by rw [h1, zero_mul]
    rw [h, h2, h1, sub_zero, add_zero]
  have hA : (1 + X) * T * (1 + Y) * S = 1 := by
    have h : (1 + X) * T * (1 + Y) * S = ((1 + X) * T) * ((1 + Y) * S) := by noncomm_ring
    rw [h, hXT, hYS, mul_one]
  have hB : (1 + X) * (X * Y - Y * X) * S = X * Y - Y * X := by rw [hXZ, hZS]
  calc (1 + X) * (1 + Y) * (1 - X + X * X) * (1 - Y + Y * Y)
      = (1 + X) * ((1 + Y) * T) * S := by rw [hT, hS]; noncomm_ring
    _ = (1 + X) * (T * (1 + Y) + (X * Y - Y * X)) * S := by rw [hYT]
    _ = (1 + X) * T * (1 + Y) * S + (1 + X) * (X * Y - Y * X) * S := by noncomm_ring
    _ = 1 + (X * Y - Y * X) := by rw [hA, hB]

private lemma isometry_relation {n : ℕ} {F : Type} [Field F]
    (q : StatedSp n F) (p r : Fin n ⊕ Fin n → F) :
    (spForm n F).β ((natRep (StatedSp n F) q - 1) p) r +
      (spForm n F).β p ((natRep (StatedSp n F) q - 1) r) +
      (spForm n F).β ((natRep (StatedSp n F) q - 1) p) ((natRep (StatedSp n F) q - 1) r)
      = 0 := by
  set T : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) q - 1 with hT
  have hp : natRep (StatedSp n F) q p = p + T p := by
    rw [hT]; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
  have hr : natRep (StatedSp n F) q r = r + T r := by
    rw [hT]; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
  have h := isIsometric_natRep_statedSp n F q p r
  rw [hp, hr] at h
  rw [(spForm n F).add_left, (spForm n F).add_right, (spForm n F).add_right] at h
  linear_combination h

private lemma commutator_beta_self {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {g h : StatedSp n F}
    (hg : g ∈ sprad (Submodule.span F {a₁, a₂}) hW)
    (hh : h ∈ sprad (Submodule.span F {a₁, a₂}) hW)
    (v : Fin n ⊕ Fin n → F) :
    (spForm n F).β
      (((natRep (StatedSp n F) g - 1) * (natRep (StatedSp n F) h - 1) -
        (natRep (StatedSp n F) h - 1) * (natRep (StatedSp n F) g - 1)) v) v = 0 := by
  set X : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) g - 1 with hX
  set Y : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) h - 1 with hY
  have hX0 : ∀ a ∈ Submodule.span F {a₁, a₂}, X a = 0 :=
    fun a ha => by rw [hX]; exact rad_sub_one_eq_zero_of_mem hg a ha
  have hX2 : ∀ u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}),
      X u ∈ Submodule.span F {a₁, a₂} :=
    fun u hu => by rw [hX]; exact rad_sub_one_mem_of_mem_perp hg u hu
  have hX3 : ∀ u, X u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) :=
    fun u => by rw [hX]; exact rad_sub_one_mem_perp hg u
  have hY0 : ∀ a ∈ Submodule.span F {a₁, a₂}, Y a = 0 :=
    fun a ha => by rw [hY]; exact rad_sub_one_eq_zero_of_mem hh a ha
  have hY2 : ∀ u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}),
      Y u ∈ Submodule.span F {a₁, a₂} :=
    fun u hu => by rw [hY]; exact rad_sub_one_mem_of_mem_perp hh u hu
  have hY3 : ∀ u, Y u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) :=
    fun u => by rw [hY]; exact rad_sub_one_mem_perp hh u
  have hrelX := isometry_relation g (Y v) v
  rw [← hX] at hrelX
  have hrelY := isometry_relation h (X v) v
  rw [← hY] at hrelY
  have hXY0 : (spForm n F).β (X (Y v)) (X v) = 0 :=
    (hX3 v) (X (Y v)) (hX2 (Y v) (hY3 v))
  have hYX0 : (spForm n F).β (Y (X v)) (Y v) = 0 :=
    (hY3 v) (Y (X v)) (hY2 (X v) (hX3 v))
  have hXY : (spForm n F).β (X (Y v)) v = -(spForm n F).β (Y v) (X v) := by
    linear_combination hrelX - hXY0
  have hYX : (spForm n F).β (Y (X v)) v = -(spForm n F).β (X v) (Y v) := by
    linear_combination hrelY - hYX0
  have hswap : (spForm n F).β (X v) (Y v) = -(spForm n F).β (Y v) (X v) :=
    (spForm n F).β_swap_of_alt (spForm_self n F) (Y v) (X v)
  have hmain : (spForm n F).β ((X * Y - Y * X) v) v = 0 := by
    have h1 : (spForm n F).β ((X * Y - Y * X) v) v
        = (spForm n F).β (X (Y v)) v - (spForm n F).β (Y (X v)) v := by
      rw [LinearMap.sub_apply, (spForm n F).β_sub_left, Module.End.mul_apply,
        Module.End.mul_apply]
    rw [h1, hXY, hYX, hswap]
    simp only [CharTwo.neg_eq, sub_self]
  exact hmain

private lemma sub_pairing_mem_perp {n : ℕ} {F : Type} [Field F]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (v : Fin n ⊕ Fin n → F) :
    v - ((spForm n F).β a₁ v) • b₁ - ((spForm n F).β a₂ v) • b₂ ∈
      (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
  have ha1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
  have ha2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
  have ha1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
  have hb1b2 : (spForm n F).β b₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.1
  have ha1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
  have ha2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
  rw [(spForm n F).mem_perp]
  intro a ha
  rw [Submodule.mem_span_pair] at ha
  obtain ⟨α, β, rfl⟩ := ha
  have h1 : (spForm n F).β a₁ (v - (spForm n F).β a₁ v • b₁ - (spForm n F).β a₂ v • b₂) = 0 := by
    rw [(spForm n F).β_sub_right, (spForm n F).β_sub_right, (spForm n F).smul_right,
      (spForm n F).smul_right, ha1b1, ha1b2, mul_one, mul_zero, sub_zero, sub_self]
  have h2 : (spForm n F).β a₂ (v - (spForm n F).β a₁ v • b₁ - (spForm n F).β a₂ v • b₂) = 0 := by
    rw [(spForm n F).β_sub_right, (spForm n F).β_sub_right, (spForm n F).smul_right,
      (spForm n F).smul_right, ha2b1, ha2b2, mul_zero, mul_one, sub_zero, sub_self]
  rw [(spForm n F).add_left, (spForm n F).smul_left, (spForm n F).smul_left, spForm_sigma,
    spForm_sigma, h1, h2, mul_zero, mul_zero, add_zero]

private lemma exists_siegel_form_of_alternating {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (Z : Module.End F (Fin n ⊕ Fin n → F))
    (hZA : ∀ v, Z v ∈ Submodule.span F {a₁, a₂})
    (hZperp : ∀ v ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}), Z v = 0)
    (halt : ∀ v, (spForm n F).β (Z v) v = 0) :
    ∃ c : F, ∀ v,
      Z v = (c * (spForm n F).β a₂ v) • a₁ + (c * (spForm n F).β a₁ v) • a₂ := by
  have ha1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
  have ha2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
  have ha1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
  have ha1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
  have ha2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
  obtain ⟨p₁, p₂, hpZ1⟩ := Submodule.mem_span_pair.mp (hZA b₁)
  obtain ⟨q₁, q₂, hpZ2⟩ := Submodule.mem_span_pair.mp (hZA b₂)
  have hp1 : p₁ = 0 := by
    have h := halt b₁
    rw [← hpZ1] at h
    simp only [(spForm n F).add_left, (spForm n F).smul_left, spForm_sigma, ha1b1, ha2b1,
      mul_one, mul_zero, zero_add, add_zero] at h
    exact h
  have hq2 : q₂ = 0 := by
    have h := halt b₂
    rw [← hpZ2] at h
    simp only [(spForm n F).add_left, (spForm n F).smul_left, spForm_sigma, ha1b2, ha2b2,
      mul_one, mul_zero, zero_add, add_zero] at h
    exact h
  have hpq : p₂ + q₁ = 0 := by
    have h := halt (b₁ + b₂)
    have hZb1 : Z b₁ = p₂ • a₂ := by rw [← hpZ1, hp1, zero_smul, zero_add]
    have hZb2 : Z b₂ = q₁ • a₁ := by rw [← hpZ2, hq2, zero_smul, add_zero]
    rw [map_add, hZb1, hZb2] at h
    simp only [(spForm n F).add_left, (spForm n F).add_right, (spForm n F).smul_left,
      spForm_sigma, ha2b1, ha2b2, ha1b1, ha1b2, mul_one, mul_zero, zero_add, add_zero] at h
    exact h
  have hq1 : q₁ = p₂ := by
    have h2 : q₁ = -p₂ := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hpq
    rwa [CharTwo.neg_eq] at h2
  refine ⟨p₂, fun v => ?_⟩
  have hw : v - ((spForm n F).β a₁ v) • b₁ - ((spForm n F).β a₂ v) • b₂ ∈
      (spForm n F).perp (Submodule.span F {a₁, a₂}) := sub_pairing_mem_perp hp v
  have hdecomp : Z v = ((spForm n F).β a₁ v) • Z b₁ + ((spForm n F).β a₂ v) • Z b₂ := by
    have h1 : v = ((spForm n F).β a₁ v) • b₁ + ((spForm n F).β a₂ v) • b₂ +
        (v - ((spForm n F).β a₁ v) • b₁ - ((spForm n F).β a₂ v) • b₂) := by abel
    have hzw : Z (v - ((spForm n F).β a₁ v) • b₁ - ((spForm n F).β a₂ v) • b₂) = 0 :=
      hZperp _ hw
    conv_lhs => rw [h1]
    simp only [map_add, map_smul, hzw, add_zero]
  rw [hdecomp, ← hpZ1, ← hpZ2, hp1, hq2, hq1]
  simp only [zero_smul, zero_add, add_zero, smul_smul]
  rw [mul_comm ((spForm n F).β a₁ v) p₂, mul_comm ((spForm n F).β a₂ v) p₂, add_comm]

theorem commutator_sprad_le_spAltSiegel {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})} :
    ⁅sprad (Submodule.span F {a₁, a₂}) hW, sprad (Submodule.span F {a₁, a₂}) hW⁆ ≤
      spAltSiegel n F a₁ a₂ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  set X : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) g - 1 with hX
  set Y : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) h - 1 with hY
  have hX0 : ∀ a ∈ Submodule.span F {a₁, a₂}, X a = 0 :=
    fun a ha => by rw [hX]; exact rad_sub_one_eq_zero_of_mem hg a ha
  have hX2 : ∀ u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}),
      X u ∈ Submodule.span F {a₁, a₂} :=
    fun u hu => by rw [hX]; exact rad_sub_one_mem_of_mem_perp hg u hu
  have hX3 : ∀ u, X u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) :=
    fun u => by rw [hX]; exact rad_sub_one_mem_perp hg u
  have hY0 : ∀ a ∈ Submodule.span F {a₁, a₂}, Y a = 0 :=
    fun a ha => by rw [hY]; exact rad_sub_one_eq_zero_of_mem hh a ha
  have hY2 : ∀ u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}),
      Y u ∈ Submodule.span F {a₁, a₂} :=
    fun u hu => by rw [hY]; exact rad_sub_one_mem_of_mem_perp hh u hu
  have hY3 : ∀ u, Y u ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) :=
    fun u => by rw [hY]; exact rad_sub_one_mem_perp hh u
  have hXXX : X * X * X = 0 := mul_three_eq_zero hX0 hX2 hX3
  have hXXY : X * X * Y = 0 := mul_three_eq_zero hX0 hX2 hY3
  have hXYX : X * Y * X = 0 := mul_three_eq_zero hX0 hY2 hX3
  have hXYY : X * Y * Y = 0 := mul_three_eq_zero hX0 hY2 hY3
  have hYXX : Y * X * X = 0 := mul_three_eq_zero hY0 hX2 hX3
  have hYXY : Y * X * Y = 0 := mul_three_eq_zero hY0 hX2 hY3
  have hYYY : Y * Y * Y = 0 := mul_three_eq_zero hY0 hY2 hY3
  have hg_eq : natRep (StatedSp n F) g = 1 + X := by rw [hX]; abel
  have hh_eq : natRep (StatedSp n F) h = 1 + Y := by rw [hY]; abel
  have hZeq : natRep (StatedSp n F) ⁅g, h⁆ = 1 + (X * Y - Y * X) := by
    rw [commutatorElement_def]
    simp only [map_mul]
    rw [hg_eq, hh_eq, natRep_inv_eq g X hg_eq hXXX, natRep_inv_eq h Y hh_eq hYYY]
    exact commutator_expansion X Y hXXX hXXY hXYX hXYY hYXX hYXY hYYY
  set Z : Module.End F (Fin n ⊕ Fin n → F) := X * Y - Y * X with hZ
  have hZeq' : natRep (StatedSp n F) ⁅g, h⁆ = 1 + Z := by rw [hZeq, hZ]
  have hZperp : ∀ v ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}), Z v = 0 := by
    intro v hv
    have h1 : Z v = X (Y v) - Y (X v) := by rw [hZ]; rfl
    rw [h1, hX0 _ (hY2 v hv), hY0 _ (hX2 v hv), sub_self]
  have hZA : ∀ v, Z v ∈ Submodule.span F {a₁, a₂} := by
    intro v
    have h1 : Z v = X (Y v) - Y (X v) := by rw [hZ]; rfl
    rw [h1]
    exact Submodule.sub_mem _ (hX2 _ (hY3 v)) (hY2 _ (hX3 v))
  have halt : ∀ v, (spForm n F).β (Z v) v = 0 := by
    intro v
    have h1 : Z v = (X * Y - Y * X) v := by rw [hZ]
    rw [h1]
    exact commutator_beta_self hg hh v
  obtain ⟨c, hc⟩ := exists_siegel_form_of_alternating hp Z hZA hZperp halt
  refine mem_spAltSiegel_of_mulVec c (fun v => ?_)
  have h1 : natRep (StatedSp n F) ⁅g, h⁆ v = v + Z v := by
    rw [hZeq']
    simp only [LinearMap.add_apply, Module.End.one_apply]
  rw [← natRep_apply, h1, hc v]
  simp only [spForm_β, add_assoc]

private lemma mem_stabilizer_of_forall_apply_mem {n : ℕ} {F : Type} [Field F]
    {A : Submodule F (Fin n ⊕ Fin n → F)} {q : StatedSp n F}
    (h : ∀ a ∈ A, natRep (StatedSp n F) q a ∈ A) :
    q ∈ SymplecticFlag.stabilizer n F A := by
  have hleft : ∀ z, natRep (StatedSp n F) q⁻¹ (natRep (StatedSp n F) q z) = z := by
    intro z
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective (natRep (StatedSp n F) q) := by
    intro x y hxy
    have := congrArg (natRep (StatedSp n F) q⁻¹) hxy
    simpa only [hleft] using this
  have hsurj : Function.Surjective (natRep (StatedSp n F) q) :=
    fun y => ⟨natRep (StatedSp n F) q⁻¹ y, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have hmap : A.map (natRep (StatedSp n F) q) = A := by
    refine Submodule.eq_of_le_of_finrank_eq (fun w hw => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := hw
      exact h a ha
    · exact LinearEquiv.finrank_map_eq
        (LinearEquiv.ofBijective (natRep (StatedSp n F) q) ⟨hinj, hsurj⟩) A
  have hinv : ∀ a ∈ A, natRep (StatedSp n F) q⁻¹ a ∈ A := by
    intro a ha
    have ha' : a ∈ A.map (natRep (StatedSp n F) q) := by rw [hmap]; exact ha
    obtain ⟨b, hb, hba⟩ := ha'
    rw [← hba, hleft]
    exact hb
  refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
  · rw [← natRep_apply]; exact h v hv
  · rw [← natRep_apply]; exact hinv v hv

private theorem eq_span_pair_of_isTotallyIsotropic_invariant {n : ℕ} {F : Type} [Field F]
    [CharP F 2] {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F}
    (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {U : Submodule F (Fin n ⊕ Fin n → F)}
    (hUiso : (spForm n F).IsTotallyIsotropic U) (hU0 : U ≠ ⊥)
    (hUinv : ∀ q ∈ SymplecticFlag.stabilizer n F (Submodule.span F {a₁, a₂}),
        ∀ u ∈ U, natRep (StatedSp n F) q u ∈ U) :
    U = Submodule.span F {a₁, a₂} := by
  set A : Submodule F (Fin n ⊕ Fin n → F) := Submodule.span F {a₁, a₂} with hA
  have ha1A : a₁ ∈ A := by rw [hA]; exact Submodule.subset_span (by simp)
  have ha2A : a₂ ∈ A := by rw [hA]; exact Submodule.subset_span (by simp)
  have hUA : U ≤ (spForm n F).perp A := by
    intro u hu
    rw [(spForm n F).mem_perp]
    intro a ha
    by_contra hau
    obtain ⟨t, ht⟩ := exists_transvection (K := F) (r := n) a
    have htrad : t ∈ sprad A hW :=
      transvection_mem_rad (F := spForm n F) (ρ := natRep (StatedSp n F)) ha ht
    have htStab : t ∈ SymplecticFlag.stabilizer n F A := sprad_le_stabilizer htrad
    have hmem : (spForm n F).β a u • a ∈ U := by
      have h1 := hUinv t htStab u hu
      rw [ht] at h1
      have h2 := Submodule.sub_mem U h1 hu
      rwa [add_sub_cancel_left] at h2
    have haU : a ∈ U := (Submodule.smul_mem_iff (p := U) (x := a) hau).mp hmem
    exact hau ((spForm n F).refl u a (hUiso haU u hu))
  have hUA' : U ≤ A := by
    intro u hu
    by_contra huA
    have huPerp : u ∈ (spForm n F).perp A := hUA hu
    have hx_exists : ∃ x ∈ (spForm n F).perp A, (spForm n F).β x u ≠ 0 := by
      by_contra h
      apply huA
      rw [← (spForm n F).perp_perp A]
      rw [(spForm n F).mem_perp]
      intro x hx
      by_contra hxu
      exact h ⟨x, hx, hxu⟩
    obtain ⟨x, hxPerp, hxu⟩ := hx_exists
    obtain ⟨t, ht⟩ := exists_transvection (K := F) (r := n) x
    have hfixA : ∀ a ∈ A, natRep (StatedSp n F) t a = a := by
      intro a ha
      rw [ht]
      have hxa : (spForm n F).β x a = 0 := (spForm n F).refl a x (hxPerp a ha)
      rw [hxa, zero_smul, add_zero]
    have htStab : t ∈ SymplecticFlag.stabilizer n F A :=
      mem_stabilizer_of_forall_apply_mem (fun a ha => by rw [hfixA a ha]; exact ha)
    have hmem : (spForm n F).β x u • x ∈ U := by
      have h1 := hUinv t htStab u hu
      rw [ht] at h1
      have h2 := Submodule.sub_mem U h1 hu
      rwa [add_sub_cancel_left] at h2
    have hxU : x ∈ U := (Submodule.smul_mem_iff (p := U) (x := x) hxu).mp hmem
    exact hxu ((spForm n F).refl u x (hUiso hxU u hu))
  have hAU : A ≤ U := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have huA : u ∈ A := hUA' huU
    rw [hA, Submodule.mem_span_pair] at huA
    obtain ⟨α, β, hαβ⟩ := huA
    have ha1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
    have ha2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
    have ha1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
    have ha1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
    have ha2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
    have hb2a1 : (spForm n F).β b₂ a₁ = 0 := (spForm n F).refl a₁ b₂ ha1b2
    have hb1a2 : (spForm n F).β b₁ a₂ = 0 := (spForm n F).refl a₂ b₁ ha2b1
    have ha2a1 : (spForm n F).β a₂ a₁ = 0 := (spForm n F).refl a₁ a₂ ha1a2
    have hb2a2 : (spForm n F).β b₂ a₂ = 1 := by
      have h := (spForm n F).β_swap_of_alt (spForm_self n F) a₂ b₂
      rw [ha2b2, CharTwo.neg_eq] at h
      exact h
    have hb1a1 : (spForm n F).β b₁ a₁ = 1 := by
      have h := (spForm n F).β_swap_of_alt (spForm_self n F) a₁ b₁
      rw [ha1b1, CharTwo.neg_eq] at h
      exact h
    obtain ⟨σ₂, hσ₂⟩ := exists_siegel (K := F) (r := n) b₂ a₁ hb2a1
    obtain ⟨σ₁, hσ₁⟩ := exists_siegel (K := F) (r := n) b₁ a₂ hb1a2
    have hσ₂Stab : σ₂ ∈ SymplecticFlag.stabilizer n F A := by
      refine mem_stabilizer_of_forall_apply_mem (fun a ha => ?_)
      rw [hσ₂]
      have hAa : (spForm n F).β a₁ a = 0 := (spForm n F).refl a a₁ (hW ha1A a ha)
      rw [hAa, zero_smul, add_zero]
      exact Submodule.add_mem A ha (Submodule.smul_mem _ _ ha1A)
    have hσ₁Stab : σ₁ ∈ SymplecticFlag.stabilizer n F A := by
      refine mem_stabilizer_of_forall_apply_mem (fun a ha => ?_)
      rw [hσ₁]
      have hAa : (spForm n F).β a₂ a = 0 := (spForm n F).refl a a₂ (hW ha2A a ha)
      rw [hAa, zero_smul, add_zero]
      exact Submodule.add_mem A ha (Submodule.smul_mem _ _ ha2A)
    have ha1U : a₁ ∈ U := by
      by_cases hβ : β = 0
      · have hu_eq : u = α • a₁ := by rw [← hαβ, hβ, zero_smul, add_zero]
        have hα : α ≠ 0 := by
          intro hα0
          apply hu0
          rw [hu_eq, hα0, zero_smul]
        have : α • a₁ ∈ U := by rw [← hu_eq]; exact huU
        exact (Submodule.smul_mem_iff (p := U) (x := a₁) hα).mp this
      · have h1 : (spForm n F).β b₂ u = β := by
          rw [← hαβ]
          simp only [(spForm n F).add_right, (spForm n F).smul_right, hb2a1, hb2a2, mul_zero,
            mul_one, zero_add, add_zero]
        have h2 : (spForm n F).β a₁ u = 0 := by
          rw [← hαβ]
          simp only [(spForm n F).add_right, (spForm n F).smul_right, spForm_self, ha1a2,
            mul_zero, add_zero]
        have hmem : β • a₁ ∈ U := by
          have h3 := hUinv σ₂ hσ₂Stab u huU
          rw [hσ₂, h1, h2, zero_smul, add_zero] at h3
          have h4 := Submodule.sub_mem U h3 huU
          rwa [add_sub_cancel_left] at h4
        exact (Submodule.smul_mem_iff (p := U) (x := a₁) hβ).mp hmem
    have ha2U : a₂ ∈ U := by
      have h3 := hUinv σ₁ hσ₁Stab a₁ ha1U
      rw [hσ₁, hb1a1, ha2a1, zero_smul, add_zero] at h3
      have h4 := Submodule.sub_mem U h3 ha1U
      rw [add_sub_cancel_left] at h4
      simpa using h4
    intro a ha
    rw [hA, Submodule.mem_span_pair] at ha
    obtain ⟨p, q, rfl⟩ := ha
    exact Submodule.add_mem U (Submodule.smul_mem _ _ ha1U) (Submodule.smul_mem _ _ ha2U)
  exact le_antisymm hUA' hAU

theorem pCoreOf_stabilizer_le_sprad {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})} :
    pCoreOf 2 (SymplecticFlag.stabilizer n F (Submodule.span F {a₁, a₂})) ≤
      sprad (Submodule.span F {a₁, a₂}) hW := by
  intro g hg
  set A : Submodule F (Fin n ⊕ Fin n → F) := Submodule.span F {a₁, a₂} with hA
  set Stab : Subgroup (StatedSp n F) := SymplecticFlag.stabilizer n F A with hStab
  set R : Subgroup (StatedSp n F) := pCoreOf 2 Stab with hR
  by_cases hR0 : R = ⊥
  · rw [hR0] at hg
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    rw [hg1, mem_rad]
    exact ⟨fun w _ => by simp, fun v _ => by simp⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR2 : IsPGroup 2 R := GGRootNorm.isPGroup_pCoreOf Stab
    have hnorm : Stab ≤ Subgroup.normalizer (R : Set (StatedSp n F)) :=
      GGRootNorm.le_normalizer_pCoreOf Stab
    have hU1 : isoSeq (spForm n F) (natRep (StatedSp n F)) R 1 ≠ ⊥ :=
      isoSeq_one_ne_bot (spForm n F) (natRep (StatedSp n F)) 2
        (isIsometric_natRep_statedSp n F) (natRep_injective (StatedSp n F)) R hR2 hR0
    have hU1inv : ∀ q ∈ Stab,
        ∀ u ∈ isoSeq (spForm n F) (natRep (StatedSp n F)) R 1,
        natRep (StatedSp n F) q u ∈ isoSeq (spForm n F) (natRep (StatedSp n F)) R 1 :=
      fun q hq u hu => apply_mem_isoSeq (spForm n F) (natRep (StatedSp n F))
        (isIsometric_natRep_statedSp n F) R 1 (hnorm hq) hu
    have hU1eq : isoSeq (spForm n F) (natRep (StatedSp n F)) R 1 = A :=
      eq_span_pair_of_isTotallyIsotropic_invariant hp (hW := hW)
        (U := isoSeq (spForm n F) (natRep (StatedSp n F)) R 1)
        (hUiso := isoSeq_isTotallyIsotropic (spForm n F) (natRep (StatedSp n F)) R 1)
        hU1 hU1inv
    have ha1ne : a₁ ≠ 0 := by
      intro h0
      have h1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
      rw [h0, (spForm n F).β_zero_left] at h1
      exact zero_ne_one h1
    haveI : Nontrivial (Fin n ⊕ Fin n → F) := ⟨⟨a₁, 0, ha1ne⟩⟩
    have hd1 : 1 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := Module.finrank_pos
    set W : Submodule F (Fin n ⊕ Fin n → F) :=
      isoSeq (spForm n F) (natRep (StatedSp n F)) R (Module.finrank F (Fin n ⊕ Fin n → F))
      with hWdef
    have hU1leW : isoSeq (spForm n F) (natRep (StatedSp n F)) R 1 ≤ W := by
      rw [hWdef]
      exact isoSeq_mono (spForm n F) (natRep (StatedSp n F)) R hd1
    have hW0 : W ≠ ⊥ := by
      intro hbot
      apply hU1
      rw [hbot] at hU1leW
      exact le_bot_iff.mp hU1leW
    have hWinv : ∀ q ∈ Stab, ∀ u ∈ W, natRep (StatedSp n F) q u ∈ W := by
      intro q hq u hu
      rw [hWdef] at hu ⊢
      exact apply_mem_isoSeq (spForm n F) (natRep (StatedSp n F))
        (isIsometric_natRep_statedSp n F) R _ (hnorm hq) hu
    have hWiso : (spForm n F).IsTotallyIsotropic W := by
      rw [hWdef]
      exact isoSeq_isTotallyIsotropic (spForm n F) (natRep (StatedSp n F)) R _
    have hWeq : W = A :=
      eq_span_pair_of_isTotallyIsotropic_invariant hp (hW := hW) (U := W) hWiso hW0 hWinv
    rw [mem_rad]
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have hw1 : w ∈ isoSeq (spForm n F) (natRep (StatedSp n F)) R 1 := by
        rw [← hA, ← hU1eq] at hw
        exact hw
      have h1 := isoSeq_triv (spForm n F) (natRep (StatedSp n F)) R 0 hg hw1
      rw [isoSeq_zero, Submodule.mem_bot] at h1
      exact sub_eq_zero.mp h1
    · have hv' : v ∈ (spForm n F).perp W := by
        rw [hWeq, hA]
        exact hv
      have h1 := isoSeq_middle_triv (spForm n F) (natRep (StatedSp n F)) 2
        (isIsometric_natRep_statedSp n F) R hR2 hg hv'
      rw [← hWdef, hWeq] at h1
      exact h1

end CFSG.StandardType.LieKnownR2.Short
