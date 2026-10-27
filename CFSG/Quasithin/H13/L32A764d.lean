module

public import CFSG.Quasithin.H13.L32A764c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open CFSG.Quasithin.CosetGeom
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem mem_sup_zpowers_of_sq {U H : Subgroup G} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hHU : H ≤ U) {u : G} (huU : u ∈ U) (hu2 : u * u = 1) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers u) : x ∈ H ∨ u * x ∈ H := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let W : Subgroup G :=
    { carrier := {x | x ∈ U ∧ (x ∈ H ∨ u * x ∈ H)}
      mul_mem' := by
        rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
        refine ⟨mul_mem haU hbU, ?_⟩
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · right
          rw [← mul_assoc, hUc u huU a haU, mul_assoc]
          exact mul_mem ha hb
        · right
          rw [← mul_assoc]
          exact mul_mem ha hb
        · left
          have : (u * a) * (u * b) = a * b := by
            rw [show (u * a) * (u * b) = u * (a * u) * b by group, ← hUc u huU a haU,
              ← mul_assoc, hu2, one_mul]
          rw [← this]
          exact mul_mem ha hb
      one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
      inv_mem' := by
        rintro a ⟨haU, ha⟩
        refine ⟨inv_mem haU, ?_⟩
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · right
          have : u * a⁻¹ = (u * a)⁻¹ := by
            rw [mul_inv_rev, hui, hUc a⁻¹ (inv_mem haU) u huU]
          rw [this]
          exact inv_mem ha }
  have hle : H ⊔ Subgroup.zpowers u ≤ W := by
    refine sup_le (fun h hh => ⟨hHU hh, Or.inl hh⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨huU, Or.inr (by rw [hu2]; exact one_mem _)⟩
  exact (hle hx).2

theorem mem_sup_of_comm {U A B : Subgroup G} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hAU : A ≤ U) (hBU : B ≤ U) {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hUc a (hAU ha) b (hBU hb), mul_inv_cancel_right]
      exact hb
    · intro hb
      have hbU : b ∈ U := by
        have := mul_mem (mul_mem (inv_mem (hAU ha)) (hBU hb)) (hAU ha)
        simpa [mul_assoc] using this
      rwa [hUc a (hAU ha) b hbU, mul_inv_cancel_right] at hb
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAB] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem sl24_fix_conj (h₀ X : SL(2, F4)) (p : Fin 2 → F4)
    (hX : ((h₀ * X * h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec p = p) :
    (X : Matrix (Fin 2) (Fin 2) F4).mulVec (((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
      p) = ((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec p := by
  set v := ((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec p with hv
  have hinv : ∀ (A : SL(2, F4)) (x : Fin 2 → F4),
      ((A⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        ((A : Matrix (Fin 2) (Fin 2) F4).mulVec x) = x := by
    intro A x
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hhv : (h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec v = p := by
    rw [hv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have h1 := sl24_conj_mulVec h₀ X v
  rw [hhv, hX] at h1
  have h2 := congrArg (((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec ·) h1
  rw [hinv] at h2
  rw [← hhv, hinv] at h2
  exact h2.symm

theorem coe_swap_upper (a : F4) :
    ((swap24 * upper24 a * swap24⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) =
      !![1, 0; a, 1] := by
  rw [swap24_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_swap24, coe_upper24, f4_swap_upper]

variable [Finite G] {T L V : Subgroup G}

theorem mem_normalizer_of_forall_conj_mem {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [← conjSub_eq_self_iff]
  refine conjSub_eq_of_le fun x hx => ?_
  rw [mem_conjSub] at hx
  have := h _ hx
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem comm_sup_eq :
    ⁅fsuU T V, pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)⁆ ⊔ fsuV1 T V = V ⊔ u0 T V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKU, π, β, hπs, hπk, hβs, hβk, hβe⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  set D := ⁅(fsuU T V), (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))⁆ ⊔ (fsuV1 T V) with hD
  have hVU : V ≤ (fsuU T V) := le_conjClosure V _
  have hU0U : (u0 T V) ≤ (fsuU T V) := centralizerMod_le_left _ _ _
  have hV1V : (fsuV1 T V) ≤ V := inf_le_left
  have hV1U0 : (fsuV1 T V) ≤ (u0 T V) := fsuV1_le_u0 C.hyp C.hMod
  have hVU0U : V ⊔ (u0 T V) ≤ (fsuU T V) := sup_le hVU hU0U
  have hcomm := commutator_le_sup_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
  have hDle : D ≤ V ⊔ (u0 T V) := sup_le hcomm (hV1V.trans le_sup_left)
  have hDU : D ≤ (fsuU T V) := hDle.trans hVU0U
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKU0 : kz T V ≤ Subgroup.normalizer ((u0 T V) : Set G) :=
    hKH.trans (hz_le_normalizer_u0 C.hyp C.hMod)
  have hKV1 : kz T V ≤ Subgroup.normalizer ((fsuV1 T V) : Set G) := hKH.trans C.hF.H_normalizes_V₁
  have hu0K : ∀ u ∈ (u0 T V), ∀ k ∈ kz T V, k * u * k⁻¹ * u⁻¹ ∈ (fsuV1 T V) := fun u hu k hk =>
    ((mem_u0_iff C.hyp C.hMod).mp hu).2 k hk
  obtain ⟨s₁, hs₁R, hs₁Q, -⟩ := C.exists_two
  have hdS : dS T V s₁ ≤ D := by
    refine sup_le ((Subgroup.closure_le _).mpr ?_) le_sup_right
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hs₁R)
  have hdS8 := C.card_dS hs₁R hs₁Q
  have hV12 := C.hF.card_V₁
  have hdSU0 : ¬ dS T V s₁ ≤ (u0 T V) := by
    intro hle
    have := C.dS_inf_u0 hs₁R hs₁Q
    rw [inf_eq_left.mpr hle] at this
    rw [this, hV12] at hdS8
    omega
  obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ V, v ∉ (fsuV1 T V) := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (show V ≤ (fsuV1 T V) from hno)
    rw [hV8, hV12] at this
    omega
  set p := Multiplicative.toAdd (β ⟨v₀, hVU hv₀V⟩) with hp
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv₀1
    have h1 : β ⟨v₀, hVU hv₀V⟩ = 1 := by
      rw [← ofAdd_toAdd (β ⟨v₀, hVU hv₀V⟩), ← hp, h0]
      rfl
    have hu0 : v₀ ∈ (u0 T V) := (l24_ker_iff hβk _).mp h1
    rw [← inf_u0_eq C.hyp C.hMod C.h63 C.hF]
    exact ⟨hv₀V, hu0⟩
  obtain ⟨h₀, hh₀⟩ := sl24_transitive' _ _ f4_e1_ne hp0
  obtain ⟨w, hw⟩ := hπs (h₀ * swap24 * h₀⁻¹)
  have hwH : (w : G) ∈ hz T V := hKH w.2
  have hfix : ∀ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec
      ((h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0]) =
      (h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0] →
      ∃ r : ↥(kz T V), (r : G) ∈ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ∧ π r = A := by
    intro A hA
    rw [hh₀] at hA
    exact C.exists_fix π hπk β hβk hβe (hVU hv₀V) hv₀V hv₀1 A hA
  set Dw := conjSub (w : G) D with hDw
  set C' := D ⊔ Dw with hC'
  have hDwU : Dw ≤ (fsuU T V) := by
    intro x hx
    rw [hDw, mem_conjSub] at hx
    have := (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U hwH) _).mp (hDU hx)
    simpa [mul_assoc] using this
  have hC'U : C' ≤ (fsuU T V) := sup_le hDU hDwU
  have hnorm : ∀ g : G, (∀ c ∈ C', g * c * g⁻¹ * c⁻¹ ∈ C') →
      g ∈ Subgroup.normalizer (C' : Set G) := by
    intro g hg
    refine mem_normalizer_of_forall_conj_mem fun c hc => ?_
    rw [show g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c by group]
    exact mul_mem (hg c hc) hc
  have hcommR : ∀ r ∈ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)), ∀ c ∈ (fsuU T V), r * c * r⁻¹ * c⁻¹ ∈ D := by
    intro r hr c hc
    have := Subgroup.commutator_mem_commutator hr hc
    rw [Subgroup.commutator_comm] at this
    exact Subgroup.mem_sup_left this
  have hRN : ∀ r ∈ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)), r ∈ Subgroup.normalizer (C' : Set G) := fun r hr =>
    hnorm r fun c hc => Subgroup.mem_sup_left (hcommR r hr c (hC'U hc))
  have hRwN : ∀ r ∈ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)), (w : G) * r * (w : G)⁻¹ ∈ Subgroup.normalizer (C' : Set G) := by
    intro r hr
    refine hnorm _ fun c hc => Subgroup.mem_sup_right ?_
    have hc' : (w : G)⁻¹ * c * (w : G) ∈ (fsuU T V) := by
      have := (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (inv_mem hwH)) c).mp
        (hC'U hc)
      simpa using this
    have h1 := hcommR r hr _ hc'
    have h2 := mul_mem_conjSub (g := (w : G)) h1
    rw [show (w : G) * (r * ((w : G)⁻¹ * c * (w : G)) * r⁻¹ * ((w : G)⁻¹ * c * (w : G))⁻¹) *
      (w : G)⁻¹ = (w : G) * r * (w : G)⁻¹ * c * ((w : G) * r * (w : G)⁻¹)⁻¹ * c⁻¹ by group] at h2
    exact h2
  have hON : ∀ o ∈ pCoreOf 2 (kz T V), o ∈ Subgroup.normalizer (C' : Set G) := by
    intro o ho
    refine hnorm o fun c hc => ?_
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (C.comm_Q (pCoreOf_kz_le (T := T) (V := V) ho) (hC'U hc)))
  have hKN : kz T V ≤ Subgroup.normalizer (C' : Set G) := by
    intro k hk
    obtain ⟨r₁, r₂, r₃, r₄, hr₁, hr₂, hr₃, hr₄, o, ho, hko⟩ :=
      Ctx764.exists_decomp π hπk h₀ hfix w hw ⟨k, hk⟩
    have hko' : k = (r₁ : G) * ((w : G) * r₂ * (w : G)⁻¹) * r₃ * ((w : G) * r₄ * (w : G)⁻¹) * o :=
      hko
    rw [hko']
    exact mul_mem (mul_mem (mul_mem (mul_mem (hRN _ hr₁) (hRwN _ hr₂)) (hRN _ hr₃))
      (hRwN _ hr₄)) (hON o ho)
  have hsupU : C' ⊔ (u0 T V) = (fsuU T V) := by
    refine eq_fsuU_of_lt C.hyp C.hMod C.h63 le_sup_right (sup_le hC'U hU0U) ?_ fun e => ?_
    · intro k hk
      rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hKN hk),
        conjSub_eq_self_iff.mpr (hKU0 hk)]
    · apply hdSU0
      rw [← e]
      exact (hdS.trans le_sup_left).trans le_sup_left
  have hU0C : (u0 T V) ≤ C' := by
    by_contra hnle
    obtain ⟨y, hyU0, hyC⟩ := Set.not_subset.mp hnle
    have hyU := hU0U hyU0
    obtain ⟨H₀, ⟨hH₀a, hH₀b, hH₀y⟩, hmax⟩ := Set.exists_max_image
      {X : Subgroup G | C' ⊓ (u0 T V) ≤ X ∧ X ≤ (u0 T V) ∧ y ∉ X} (fun X => Nat.card ↥X) (Set.toFinite _)
      ⟨C' ⊓ (u0 T V), le_rfl, inf_le_right, fun h => hyC h.1⟩
    have hsq : ∀ u ∈ (fsuU T V), u * u = 1 := fun u hu => by rw [← sq]; exact C.hUe u hu
    have hcov : ∀ u ∈ (u0 T V), u ∈ H₀ ∨ u * y ∈ H₀ := by
      intro u hu
      by_contra hc
      push Not at hc
      obtain ⟨hu1, hu2⟩ := hc
      have hX : H₀ ⊔ Subgroup.zpowers u ∈
          {X : Subgroup G | C' ⊓ (u0 T V) ≤ X ∧ X ≤ (u0 T V) ∧ y ∉ X} := by
        refine ⟨hH₀a.trans le_sup_left, sup_le hH₀b (Subgroup.zpowers_le.mpr hu), fun hy => ?_⟩
        rcases mem_sup_zpowers_of_sq C.hUc (hH₀b.trans hU0U) (hU0U hu) (hsq u (hU0U hu)) hy
          with h1 | h1
        · exact hH₀y h1
        · exact hu2 h1
      have hle : Nat.card ↥(H₀ ⊔ Subgroup.zpowers u) ≤ Nat.card ↥H₀ := hmax _ hX
      have hlt : H₀ < H₀ ⊔ Subgroup.zpowers u :=
        lt_of_le_of_ne le_sup_left fun e => hu1 (e ▸ Subgroup.mem_sup_right
          (Subgroup.mem_zpowers u))
      have := Subgroup.card_lt_of_lt hlt
      omega
    have hV1C : (fsuV1 T V) ≤ C' := le_sup_right.trans le_sup_left
    have hV1H₀ : (fsuV1 T V) ≤ H₀ := (le_inf hV1C hV1U0).trans hH₀a
    have hAU : (C' ⊔ H₀) ≤ (fsuU T V) := sup_le hC'U (hH₀b.trans hU0U)
    have hBU : ((fsuV1 T V) ⊔ Subgroup.zpowers y) ≤ (fsuU T V) := sup_le (hV1U0.trans hU0U) (Subgroup.zpowers_le.mpr hyU)
    have hKH₀ : kz T V ≤ Subgroup.normalizer (H₀ : Set G) := by
      intro k hk
      refine mem_normalizer_of_forall_conj_mem fun h hh => ?_
      rw [show k * h * k⁻¹ = (k * h * k⁻¹ * h⁻¹) * h by group]
      exact mul_mem (hV1H₀ (hu0K h (hH₀b hh) k hk)) hh
    have hKB : kz T V ≤ Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := by
      intro k hk
      refine mem_normalizer_of_forall_conj_mem fun b hb => ?_
      have hbU := hBU hb
      rcases mem_sup_zpowers_of_sq C.hUc (hV1U0.trans hU0U) hyU (hsq y hyU) hb with h1 | h1
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hKV1 hk) b).mp h1)
      · have hb' : b = y * (y * b) := by rw [← mul_assoc, hsq y hyU, one_mul]
        have hky : k * y * k⁻¹ = (k * y * k⁻¹ * y⁻¹) * y := by group
        rw [hb', show k * (y * (y * b)) * k⁻¹ = (k * y * k⁻¹) * (k * (y * b) * k⁻¹) by group,
          hky]
        exact mul_mem (mul_mem (Subgroup.mem_sup_left (hu0K y hyU0 k hk))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
          (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hKV1 hk) _).mp h1))
    have hKA : kz T V ≤ Subgroup.normalizer ((C' ⊔ H₀ : Subgroup G) : Set G) := by
      intro k hk
      rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hKN hk),
        conjSub_eq_self_iff.mpr (hKH₀ hk)]
    have hyA : y ∉ (C' ⊔ H₀) := by
      intro hy
      obtain ⟨c, hc, h, hh, rfl⟩ := mem_sup_of_comm C.hUc hC'U (hH₀b.trans hU0U) hy
      apply hH₀y
      have hc0 : c ∈ (u0 T V) := by
        have := mul_mem hyU0 (inv_mem (hH₀b hh))
        simpa using this
      exact mul_mem (hH₀a (Subgroup.mem_inf.mpr ⟨hc, hc0⟩)) hh
    have hinf : (C' ⊔ H₀) ⊓ ((fsuV1 T V) ⊔ Subgroup.zpowers y) = (fsuV1 T V) := by
      refine le_antisymm ?_ (le_inf (hV1C.trans le_sup_left) le_sup_left)
      intro x hx
      obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
      rcases mem_sup_zpowers_of_sq C.hUc (hV1U0.trans hU0U) hyU (hsq y hyU) hxB with h1 | h1
      · exact h1
      · exfalso
        apply hyA
        have hxU := hBU hxB
        have : y = (y * x) * x⁻¹ := by group
        rw [this]
        exact mul_mem (hV1C.trans le_sup_left h1) (inv_mem hxA)
    have hsup : (C' ⊔ H₀) ⊔ ((fsuV1 T V) ⊔ Subgroup.zpowers y) = (fsuU T V) := by
      refine le_antisymm (sup_le hAU hBU) ?_
      rw [← hsupU]
      refine sup_le (le_sup_left.trans le_sup_left) ?_
      intro u hu
      rcases hcov u hu with h1 | h1
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h1)
      · rw [show u = (u * y) * y⁻¹ by group]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right h1))
          (Subgroup.mem_sup_right (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers y))))
    have hind := (C.h63 G T L V C.hyp).2.2.2.2.2.1
    rcases hind (C' ⊔ H₀) ((fsuV1 T V) ⊔ Subgroup.zpowers y) (hV1C.trans le_sup_left) le_sup_left hAU hBU hKA hKB hinf hsup with e | e
    · have := Subgroup.card_le_of_le ((hdS.trans le_sup_left).trans
        (le_sup_left : C' ≤ (C' ⊔ H₀)))
      rw [e, hdS8, hV12] at this
      omega
    · apply hyC
      have : y ∈ ((fsuV1 T V) ⊔ Subgroup.zpowers y) := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      rw [e] at this
      exact hV1C this
  have hCU0 : C' ⊓ (u0 T V) ≤ D := by
    intro c hc
    obtain ⟨hcC, hcU0⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨d, hd, e, he, rfl⟩ := mem_sup_of_comm C.hUc hDU hDwU hcC
    rw [hDw, mem_conjSub] at he
    obtain ⟨e', he', rfl⟩ : ∃ e' ∈ D, e = (w : G) * e' * (w : G)⁻¹ :=
      ⟨(w : G)⁻¹ * e * (w : G), he, by group⟩
    have hdU := hDU hd
    have he'U := hDU he'
    have heU : (w : G) * e' * (w : G)⁻¹ ∈ (fsuU T V) :=
      (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U hwH) e').mp he'U
    have hdVU := hDle hd
    have he'VU := hDle he'
    have hβc : β ⟨d * ((w : G) * e' * (w : G)⁻¹), hC'U hcC⟩ = 1 := (l24_ker_iff hβk _).mpr hcU0
    have hβde : Multiplicative.toAdd (β ⟨d, hdU⟩) +
        Multiplicative.toAdd (β ⟨(w : G) * e' * (w : G)⁻¹, heU⟩) = 0 := by
      have : (⟨d * ((w : G) * e' * (w : G)⁻¹), hC'U hcC⟩ : ↥(fsuU T V)) =
          ⟨d, hdU⟩ * ⟨(w : G) * e' * (w : G)⁻¹, heU⟩ := rfl
      rw [this, map_mul] at hβc
      have := congrArg Multiplicative.toAdd hβc
      simpa using this
    have hde := f4_eq_of_add _ _ hβde
    have hβe' := hβe w ⟨e', he'U⟩ ⟨(w : G) * e' * (w : G)⁻¹, heU⟩ rfl
    have hU1 : ∀ a : F4, ((upper24 a : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        (((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
          (Multiplicative.toAdd (β ⟨d, hdU⟩))) =
        ((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
          (Multiplicative.toAdd (β ⟨d, hdU⟩)) := by
      intro a
      refine sl24_fix_conj h₀ _ _ ?_
      obtain ⟨r, hr, hra⟩ := hfix (h₀ * upper24 a * h₀⁻¹)
        (by rw [sl24_conj_mulVec, coe_upper24, f4_upper_fix])
      rw [← hra]
      exact C.fix_of_mem_sup π β hβk hβe r hr hdU hdVU
    have hL1 : ∀ a : F4, ((swap24 * upper24 a * swap24⁻¹ : SL(2, F4)) :
        Matrix (Fin 2) (Fin 2) F4).mulVec (((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
          (Multiplicative.toAdd (β ⟨(w : G) * e' * (w : G)⁻¹, heU⟩))) =
        ((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
          (Multiplicative.toAdd (β ⟨(w : G) * e' * (w : G)⁻¹, heU⟩)) := by
      intro a
      refine sl24_fix_conj h₀ _ _ ?_
      obtain ⟨r, hr, hra⟩ := hfix (h₀ * upper24 a * h₀⁻¹)
        (by rw [sl24_conj_mulVec, coe_upper24, f4_upper_fix])
      have hrw : h₀ * (swap24 * upper24 a * swap24⁻¹) * h₀⁻¹ = π w * π r * (π w)⁻¹ := by
        rw [hw, hra]
        group
      rw [hrw, hβe', toAdd_ofAdd]
      have hfr := C.fix_of_mem_sup π β hβk hβe r hr he'U he'VU
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec (M := (((π w)⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4)),
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mulVec, hfr]
    have hzero := sl24_fix_both _ (fun a => by rw [← coe_upper24]; exact hU1 a)
      (fun a => by rw [← coe_swap_upper, hde]; exact hL1 a)
    have hd0 : Multiplicative.toAdd (β ⟨d, hdU⟩) = 0 := by
      have h1 : (h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec
          (((h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
            (Multiplicative.toAdd (β ⟨d, hdU⟩))) = Multiplicative.toAdd (β ⟨d, hdU⟩) := by
        rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      rw [← h1, hzero, Matrix.mulVec_zero]
    have hdU0 : d ∈ (u0 T V) := (l24_ker_iff hβk _).mp (by
      rw [← ofAdd_toAdd (β ⟨d, hdU⟩), hd0]
      rfl)
    have heU0 : (w : G) * e' * (w : G)⁻¹ ∈ (u0 T V) := by
      have := mul_mem (inv_mem hdU0) hcU0
      simpa using this
    have he'U0 : e' ∈ (u0 T V) := by
      have := (Subgroup.mem_normalizer_iff.mp (hKU0 (inv_mem w.2)) _).mp heU0
      simpa [mul_assoc] using this
    have hwe : (w : G) * e' * (w : G)⁻¹ * e'⁻¹ ∈ (fsuV1 T V) := hu0K e' he'U0 w w.2
    rw [show d * ((w : G) * e' * (w : G)⁻¹) = d * (((w : G) * e' * (w : G)⁻¹ * e'⁻¹) * e') by
      group]
    exact mul_mem hd (mul_mem (Subgroup.mem_sup_right hwe) he')
  refine le_antisymm hDle ?_
  have hU0D : (u0 T V) ≤ D := fun u hu => hCU0 (Subgroup.mem_inf.mpr ⟨hU0C hu, hu⟩)
  refine sup_le ?_ hU0D
  intro v hv
  have hvVU : v ∈ V ⊔ (u0 T V) := Subgroup.mem_sup_left hv
  rw [← C.dS_sup_u0 hs₁R hs₁Q] at hvVU
  exact (sup_le hdS hU0D) hvVU

end Ctx764

end CFSG.Quasithin.H13.L32A
