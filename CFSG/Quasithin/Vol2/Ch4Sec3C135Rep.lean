module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cent
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off2

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

structure QC (X K : Subgroup G) (F : Type) [Field F] where
  κ : ↥X → Fin 3 → F
  mul : ∀ x y, κ (x * y) = κ x + κ y
  surj : Function.Surjective κ
  ker : ∀ x, κ x = 0 ↔ (x : G) ∈ K

namespace QC

variable {X K : Subgroup G} (Qc : QC X K F)

theorem κ_one : Qc.κ 1 = 0 := by
  have h := Qc.mul 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem κ_inv (x : ↥X) : Qc.κ x⁻¹ = -Qc.κ x := by
  have h := Qc.mul x x⁻¹
  rw [mul_inv_cancel, Qc.κ_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem κ_eq_iff (x y : ↥X) : Qc.κ x = Qc.κ y ↔ ((x⁻¹ * y : ↥X) : G) ∈ K := by
  rw [← Qc.ker, Qc.mul, Qc.κ_inv, neg_add_eq_zero]

@[expose] noncomputable def sec (v : Fin 3 → F) : ↥X := Classical.choose (Qc.surj v)

theorem κ_sec (v : Fin 3 → F) : Qc.κ (Qc.sec v) = v := Classical.choose_spec (Qc.surj v)

variable {A : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
  (hAK : A ≤ Subgroup.normalizer (K : Set G))

include hAK in
theorem κ_cnj_eq {a : G} (ha : a ∈ A) {x y : ↥X} (h : Qc.κ x = Qc.κ y) :
    Qc.κ (cnj (hAX ha) x) = Qc.κ (cnj (hAX ha) y) := by
  rw [κ_eq_iff] at h ⊢
  have e : ((cnj (hAX ha) x)⁻¹ * cnj (hAX ha) y : ↥X) = cnj (hAX ha) (x⁻¹ * y) :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]; group)
  rw [e, coe_cnj]
  exact (Subgroup.mem_normalizer_iff.mp (hAK ha) _).mp h

@[expose] noncomputable def act {a : G} (ha : a ∈ A) (v : Fin 3 → F) : Fin 3 → F :=
  Qc.κ (cnj (hAX ha) (Qc.sec v))

include hAK in
theorem act_κ {a : G} (ha : a ∈ A) (x : ↥X) :
    Qc.act hAX ha (Qc.κ x) = Qc.κ (cnj (hAX ha) x) :=
  Qc.κ_cnj_eq hAX hAK ha (Qc.κ_sec _)

theorem act_congr {a b : G} (ha : a ∈ A) (hb : b ∈ A) (h : a = b) (v : Fin 3 → F) :
    Qc.act hAX ha v = Qc.act hAX hb v := by
  subst h
  rfl

include hAK in
theorem act_mul {a b : G} (ha : a ∈ A) (hb : b ∈ A) (v : Fin 3 → F) :
    Qc.act hAX (A.mul_mem ha hb) v = Qc.act hAX ha (Qc.act hAX hb v) := by
  show Qc.κ (cnj _ (Qc.sec v)) = Qc.act hAX ha (Qc.κ (cnj (hAX hb) (Qc.sec v)))
  rw [Qc.act_κ hAX hAK ha, ← cnj_mul_left]

theorem act_one (v : Fin 3 → F) : Qc.act hAX A.one_mem v = v := by
  rw [act]
  have e : cnj (hAX A.one_mem) (Qc.sec v) = Qc.sec v := Subtype.ext (by simp [coe_cnj])
  rw [e, Qc.κ_sec]

include hAK in
theorem act_add {a : G} (ha : a ∈ A) (v w : Fin 3 → F) :
    Qc.act hAX ha (v + w) = Qc.act hAX ha v + Qc.act hAX ha w := by
  rw [← Qc.κ_sec v, ← Qc.κ_sec w, ← Qc.mul, Qc.act_κ hAX hAK, Qc.act_κ hAX hAK,
    Qc.act_κ hAX hAK, cnj_mul, Qc.mul]

include hAK in
theorem act_inv_act {a : G} (ha : a ∈ A) (v : Fin 3 → F) :
    Qc.act hAX (A.inv_mem ha) (Qc.act hAX ha v) = v := by
  rw [← Qc.act_mul hAX hAK, Qc.act_congr hAX _ A.one_mem (inv_mul_cancel a), Qc.act_one]

include hAK in
theorem act_act_inv {a : G} (ha : a ∈ A) (v : Fin 3 → F) :
    Qc.act hAX ha (Qc.act hAX (A.inv_mem ha) v) = v := by
  rw [← Qc.act_mul hAX hAK, Qc.act_congr hAX _ A.one_mem (mul_inv_cancel a), Qc.act_one]

@[expose] noncomputable def perm {a : G} (ha : a ∈ A) : Equiv.Perm (Fin 3 → F) where
  toFun := Qc.act hAX ha
  invFun := Qc.act hAX (A.inv_mem ha)
  left_inv := Qc.act_inv_act hAX hAK ha
  right_inv := Qc.act_act_inv hAX hAK ha

@[expose] noncomputable def rep : ↥A →* Equiv.Perm (Fin 3 → F) where
  toFun a := Qc.perm hAX hAK a.2
  map_one' := Equiv.ext fun v => Qc.act_one hAX v
  map_mul' a b := Equiv.ext fun v => Qc.act_mul hAX hAK a.2 b.2 v

theorem rep_κ (a : ↥A) (x : ↥X) : Qc.rep hAX hAK a (Qc.κ x) = Qc.κ (cnj (hAX a.2) x) :=
  Qc.act_κ hAX hAK a.2 x

theorem rep_add (a : ↥A) (v w : Fin 3 → F) :
    Qc.rep hAX hAK a (v + w) = Qc.rep hAX hAK a v + Qc.rep hAX hAK a w :=
  Qc.act_add hAX hAK a.2 v w

variable {L : Subgroup G} (ρL : ↥L →* SpecialLinearGroup (Fin 3) F)
  (hLX : L ≤ Subgroup.normalizer (X : Set G))
  (hnat : ∀ (g : ↥L) (x : ↥X), Qc.κ (cnj (hLX g.2) x) =
    ((ρL g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Qc.κ x)
  (hAL : A ≤ Subgroup.normalizer (L : Set G))

@[expose] def conjL (a : ↥A) (g : ↥L) : ↥L :=
  ⟨a * g * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL a.2) g).mp g.2⟩

include hAK hnat in
theorem rep_intertwine (a : ↥A) (g : ↥L) (v : Fin 3 → F) :
    Qc.rep hAX hAK a (((ρL g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((ρL (conjL hAL a g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Qc.rep hAX hAK a v := by
  obtain ⟨x, rfl⟩ := Qc.surj v
  rw [← hnat, Qc.rep_κ, Qc.rep_κ, ← hnat]
  congr 1
  apply Subtype.ext
  simp only [coe_cnj, conjL]
  group

@[expose] noncomputable def lift1 (a : ↥A) : (Fin 1 → Fin 3 → F) ≃+ (Fin 1 → Fin 3 → F) where
  toFun v i := Qc.rep hAX hAK a (v i)
  invFun v i := Qc.rep hAX hAK a⁻¹ (v i)
  left_inv v := funext fun i => by
    show Qc.rep hAX hAK a⁻¹ (Qc.rep hAX hAK a (v i)) = v i
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := funext fun i => by
    show Qc.rep hAX hAK a (Qc.rep hAX hAK a⁻¹ (v i)) = v i
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' v w := funext fun i => Qc.rep_add hAX hAK a (v i) (w i)

include hnat hAL in
theorem normalizesDact_lift1 (hρL : Function.Surjective ρL) (a : ↥A) :
    NormalizesDact ⇑(Qc.lift1 hAX hAK a) := by
  intro Xm
  obtain ⟨g, rfl⟩ := hρL Xm
  refine ⟨ρL (conjL hAL a g), fun v => funext fun i => ?_⟩
  show Qc.rep hAX hAK a (((ρL g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
    v i) = _
  rw [Qc.rep_intertwine hAX hAK ρL hLX hnat hAL]
  rfl

include hnat hAL in
theorem exists_semi [Finite F] (hρL : Function.Surjective ρL) (a : ↥A) :
    ∃ σ : F ≃+* F, ∀ (c : F) v, Qc.rep hAX hAK a (c • v) = σ c • Qc.rep hAX hAK a v := by
  obtain ⟨σ, hσ⟩ := exists_semilinear (k := 1) one_ne_zero
    (Qc.normalizesDact_lift1 hAX hAK ρL hLX hnat hAL hρL a)
    (by
      have h := Qc.normalizesDact_lift1 hAX hAK ρL hLX hnat hAL hρL a⁻¹
      intro Xm
      obtain ⟨Y, hY⟩ := h Xm
      exact ⟨Y, fun v => hY v⟩)
  refine ⟨σ, fun c v => ?_⟩
  have h := congrFun (hσ c (fun _ => v)) 0
  exact h

end QC

section Pair

variable {X K X' K' : Subgroup G} (QA : QC X K F) (QB : QC X' K' F) {A L : Subgroup G}
  (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
  (hAX' : A ≤ Subgroup.normalizer (X' : Set G)) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
  (ρA : ↥L →* SpecialLinearGroup (Fin 3) F) (hρA : Function.Surjective ρA)
  (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLX' : L ≤ Subgroup.normalizer (X' : Set G))
  (hnatA : ∀ (g : ↥L) (x : ↥X), QA.κ (cnj (hLX g.2) x) =
    ((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ QA.κ x)
  (hnatB : ∀ (g : ↥L) (x : ↥X'), QB.κ (cnj (hLX' g.2) x) =
    ((dualHom (ρA g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ QB.κ x)
  (hAL : A ≤ Subgroup.normalizer (L : Set G))

theorem exists_matrix_of_linear (f : (Fin 3 → F) → (Fin 3 → F))
    (hadd : ∀ v w, f (v + w) = f v + f w) (hlin : ∀ (c : F) v, f (c • v) = c • f v) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, ∀ v, f v = P *ᵥ v := by
  let φ : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := f
      map_add' := hadd
      map_smul' := hlin }
  exact ⟨LinearMap.toMatrix' φ, fun v => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩

theorem sq_of_matrix {f : Equiv.Perm (Fin 3 → F)} (hf : f * f = 1)
    {P : Matrix (Fin 3) (Fin 3) F} (hP : ∀ v, f v = P *ᵥ v) : P * P = 1 := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  rw [← mulVec_mulVec, ← hP, ← hP, ← Equiv.Perm.mul_apply, hf, one_mulVec]
  rfl

include hρA in
theorem exists_smul_of_commute_rho {φ : (Fin 3 → F) → (Fin 3 → F)}
    (hadd : ∀ v w, φ (v + w) = φ v + φ w)
    (h : ∀ (g : ↥L) v, φ (((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      v) = ((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v) :
    ∃ c : F, ∀ v, φ v = c • v := by
  have hz : φ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let ψ : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := φ
      map_zero' := hz
      map_add' := hadd }
  refine exists_smul_of_commute ψ fun i j hij b v => ?_
  obtain ⟨g, hg⟩ := hρA (SpecialLinearGroup.transvection hij b)
  have := h g v
  rw [hg] at this
  exact this

theorem coe_dualHom_of_sq {P : SpecialLinearGroup (Fin 3) F} (hPP : P * P = 1) :
    ((dualHom P : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  rw [coe_dualHom, inv_eq_of_mul_eq_one_right hPP]

theorem tr_sq {P : SpecialLinearGroup (Fin 3) F} (hPP : P * P = 1) :
    (P : Matrix (Fin 3) (Fin 3) F)ᵀ * (P : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
  rw [← transpose_mul, show (P : Matrix (Fin 3) (Fin 3) F) * P = 1 from congrArg Subtype.val hPP,
    transpose_one]

include hnatA hnatB hρA hAL in
theorem lin_dual [CharP F 2] (a : ↥A) (ha2 : a * a = 1)
    (hlin : ∀ (c : F) v, QA.rep hAX hAK a (c • v) = c • QA.rep hAX hAK a v) :
    ∃ P : SpecialLinearGroup (Fin 3) F, (∀ v, QA.rep hAX hAK a v =
      (P : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ∧ ∀ v, QB.rep hAX' hAK' a v =
        (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v := by
  obtain ⟨P₀, hP₀⟩ := exists_matrix_of_linear (QA.rep hAX hAK a) (QA.rep_add hAX hAK a) hlin
  have hsqA : QA.rep hAX hAK a * QA.rep hAX hAK a = 1 := by rw [← map_mul, ha2, map_one]
  have hP₀2 : P₀ * P₀ = 1 := sq_of_matrix hsqA hP₀
  set P : SpecialLinearGroup (Fin 3) F := ⟨P₀, det_eq_one_of_mul_self hP₀2⟩ with hPdef
  have hPP : P * P = 1 := Subtype.ext hP₀2
  have hPm : (P : Matrix (Fin 3) (Fin 3) F) = P₀ := rfl
  refine ⟨P, fun v => by rw [hP₀, hPm], ?_⟩
  have hconj : ∀ g, ρA (QC.conjL hAL a g) = P * ρA g * P := by
    intro g
    apply Subtype.ext
    refine matrix_eq_of_mulVec_eq fun v => ?_
    have hPv : ∀ w, P₀ *ᵥ (P₀ *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hP₀2, one_mulVec]
    have h1 := QA.rep_intertwine hAX hAK ρA hLX hnatA hAL a g (P₀ *ᵥ v)
    rw [hP₀, hP₀, hPv] at h1
    rw [← h1]
    show _ = (P₀ * ((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * P₀) *ᵥ v
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  set ρB := dualHom.comp ρA with hρBdef
  have hρB : Function.Surjective ρB := fun γ => by
    obtain ⟨g, hg⟩ := hρA (dualHom γ)
    exact ⟨g, by rw [hρBdef, MonoidHom.comp_apply, hg, dualHom_dualHom]⟩
  have hnatB' : ∀ (g : ↥L) (x : ↥X'), QB.κ (cnj (hLX' g.2) x) =
      ((ρB g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ QB.κ x := hnatB
  have hdP : ((dualHom P : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F)ᵀ := coe_dualHom_of_sq hPP
  obtain ⟨c, hc⟩ := exists_smul_of_commute_rho ρB hρB
    (φ := fun v => (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QB.rep hAX' hAK' a v)
    (fun v w => by rw [QB.rep_add, mulVec_add]) (fun g v => by
      show (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QB.rep hAX' hAK' a
          (((ρB g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        ((ρB g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QB.rep hAX' hAK' a v)
      rw [QB.rep_intertwine hAX' hAK' ρB hLX' hnatB' hAL, hρBdef, MonoidHom.comp_apply, hconj,
        map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdP,
        mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, tr_sq hPP,
        Matrix.one_mul]
      rfl)
  have hB : ∀ v, QB.rep hAX' hAK' a v = c • ((P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) := by
    intro v
    have h1 := congrArg (fun w => (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w) (hc v)
    simp only [mulVec_mulVec, tr_sq hPP, one_mulVec, mulVec_smul] at h1
    exact h1
  have hc1 : c = 1 := by
    have hsqB : QB.rep hAX' hAK' a * QB.rep hAX' hAK' a = 1 := by rw [← map_mul, ha2, map_one]
    have h1 := congrArg (fun f : Equiv.Perm (Fin 3 → F) => f (Pi.single 0 1)) hsqB
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
    rw [hB, hB, mulVec_smul, mulVec_mulVec, tr_sq hPP, one_mulVec, smul_smul] at h1
    have e0 : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by simpa using congrFun h 0
    have h2 : c * c = 1 := by
      have := smul_left_injective F e0 (h1.trans (one_smul F _).symm)
      exact this
    exact eq_one_of_mul_self_eq_one h2
  intro v
  rw [hB, hc1, one_smul]

include hnatA hnatB hρA hAL in
theorem lin_of_dual [CharP F 2] (a : ↥A) (ha2 : a * a = 1)
    (hlin : ∀ (c : F) v, QB.rep hAX' hAK' a (c • v) = c • QB.rep hAX' hAK' a v) :
    ∀ (c : F) v, QA.rep hAX hAK a (c • v) = c • QA.rep hAX hAK a v := by
  set ρB := dualHom.comp ρA with hρBdef
  have hρB : Function.Surjective ρB := fun γ => by
    obtain ⟨g, hg⟩ := hρA (dualHom γ)
    exact ⟨g, by rw [hρBdef, MonoidHom.comp_apply, hg, dualHom_dualHom]⟩
  have hnatB' : ∀ (g : ↥L) (x : ↥X'), QB.κ (cnj (hLX' g.2) x) =
      ((ρB g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ QB.κ x := hnatB
  obtain ⟨R₀, hR₀⟩ := exists_matrix_of_linear (QB.rep hAX' hAK' a) (QB.rep_add hAX' hAK' a) hlin
  have hsqB : QB.rep hAX' hAK' a * QB.rep hAX' hAK' a = 1 := by rw [← map_mul, ha2, map_one]
  have hR₀2 : R₀ * R₀ = 1 := sq_of_matrix hsqB hR₀
  set R : SpecialLinearGroup (Fin 3) F := ⟨R₀, det_eq_one_of_mul_self hR₀2⟩ with hRdef
  have hRR : R * R = 1 := Subtype.ext hR₀2
  have hRm : (R : Matrix (Fin 3) (Fin 3) F) = R₀ := rfl
  have hconj : ∀ g, ρB (QC.conjL hAL a g) = R * ρB g * R := by
    intro g
    apply Subtype.ext
    refine matrix_eq_of_mulVec_eq fun v => ?_
    have hRv : ∀ w, R₀ *ᵥ (R₀ *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hR₀2, one_mulVec]
    have h1 := QB.rep_intertwine hAX' hAK' ρB hLX' hnatB' hAL a g (R₀ *ᵥ v)
    rw [hR₀, hR₀, hRv] at h1
    rw [← h1]
    show _ = (R₀ * ((ρB g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * R₀) *ᵥ v
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  have hdR : ((dualHom R : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (R : Matrix (Fin 3) (Fin 3) F)ᵀ := coe_dualHom_of_sq hRR
  have hconjA : ∀ g, ρA (QC.conjL hAL a g) = dualHom R * ρA g * dualHom R := by
    intro g
    have h1 := congrArg dualHom (hconj g)
    rwa [hρBdef, MonoidHom.comp_apply, MonoidHom.comp_apply, dualHom_dualHom, map_mul, map_mul,
      dualHom_dualHom] at h1
  obtain ⟨c, hc⟩ := exists_smul_of_commute_rho ρA hρA
    (φ := fun v => (R : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QA.rep hAX hAK a v)
    (fun v w => by rw [QA.rep_add, mulVec_add]) (fun g v => by
      show (R : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QA.rep hAX hAK a
          (((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        ((ρA g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((R : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ QA.rep hAX hAK a v)
      rw [QA.rep_intertwine hAX hAK ρA hLX hnatA hAL, hconjA, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hdR, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, tr_sq hRR, Matrix.one_mul])
  intro c' v
  have hA : ∀ w, QA.rep hAX hAK a w = c • ((R : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w) := by
    intro w
    have h1 := congrArg (fun u => (R : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ u) (hc w)
    simp only [mulVec_mulVec, tr_sq hRR, one_mulVec, mulVec_smul] at h1
    exact h1
  rw [hA, hA, mulVec_smul, smul_comm]

end Pair

end CFSG.Quasithin.H13.Ch4.C135

end
