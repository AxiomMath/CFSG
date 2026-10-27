module

public import CFSG.Quasithin.Background.F918E1

public section

namespace CFSG.Quasithin

section Count

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [Finite M]

private theorem natCard_dual_vanishing_mul {c : M} (hc : c ≠ 0) :
    Nat.card {F : Module.Dual K M // F c = 0} * Nat.card K = Nat.card M := by
  let S : Submodule K M := Submodule.span K {c}
  have e : {F : Module.Dual K M // F c = 0} ≃ ↥(S.dualAnnihilator) :=
    Equiv.subtypeEquivRight (fun F => by
      rw [Submodule.mem_dualAnnihilator]
      constructor
      · intro h w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
        rw [map_smul, h, smul_zero]
      · intro h
        exact h _ (Submodule.mem_span_singleton_self _))
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K) (V := ↥S.dualAnnihilator),
    Module.natCard_eq_pow_finrank (K := K) (V := M), ← pow_succ]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have h2 : Module.finrank K S = 1 := finrank_span_singleton hc
  congr 1
  omega

end Count

section Aux

variable {W : Type*} [CommGroup W]

private theorem two_nsmul_eq_zero_of_sq_eq_one (hW : ∀ w : W, w ^ 2 = 1) (x : Additive W) :
    (2 : ℕ) • x = 0 := by
  apply Multiplicative.ofAdd.injective
  exact hW (Additive.toMul x)

variable [Module (ZMod 2) (Additive W)]

private theorem mul_self_eq_one_of_module (v : W) : v * v = 1 := by
  have h : (2 : ZMod 2) • Additive.ofMul v = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  rw [two_smul] at h
  have h' : Additive.ofMul (v * v) = 0 := h
  exact ofMul_eq_zero.1 h'

private theorem isTransvectionWith_tvAut (F : Module.Dual (ZMod 2) (Additive W)) {y : W}
    (hy : y ≠ 1) (h : F (Additive.ofMul y) = 0) : IsTransvectionWith (tvAut F y h) y := by
  refine ⟨hy, fun v => ?_⟩
  rcases zmod_two_cases (F (Additive.ofMul v)) with h' | h'
  · exact Or.inl (tvAut_of_eq_zero h h')
  · exact Or.inr (tvAut_of_eq_one h h')

private theorem tvAut_eq_self_iff {F : Module.Dual (ZMod 2) (Additive W)} {y : W} (hy : y ≠ 1)
    (h : F (Additive.ofMul y) = 0) (v : W) :
    tvAut F y h v = v ↔ F (Additive.ofMul v) = 0 := by
  rcases zmod_two_cases (F (Additive.ofMul v)) with h' | h'
  · simp [tvAut_of_eq_zero h h', h']
  · rw [tvAut_of_eq_one h h', h']
    simp [hy]

private theorem tvAut_injective {y : W} (hy : y ≠ 1) :
    Function.Injective fun F : {F : Module.Dual (ZMod 2) (Additive W) //
        F (Additive.ofMul y) = 0} =>
      (⟨tvAut F.1 y F.2, isTransvectionWith_tvAut F.1 hy F.2⟩ :
        {t : MulAut W // IsTransvectionWith t y}) := by
  rintro ⟨F, hF⟩ ⟨F', hF'⟩ h
  have h' : tvAut F y hF = tvAut F' y hF' := congrArg Subtype.val h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have e1 := tvAut_eq_self_iff hy hF (Additive.toMul x)
  have e2 := tvAut_eq_self_iff hy hF' (Additive.toMul x)
  rw [h'] at e1
  have key : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact key _ _ (e1.symm.trans e2)

open scoped Classical in
private theorem transv_ite_add {t : MulAut W} {c : W} (ht : IsTransvectionWith t c) (v w : W) :
    (if t (v * w) = v * w then (0 : ZMod 2) else 1) =
      (if t v = v then 0 else 1) + (if t w = w then 0 else 1) := by
  have hcc : c * c = 1 := mul_self_eq_one_of_module c
  have hne : ∀ a : W, a * c ≠ a := fun a h => ht.1 (mul_left_cancel (h.trans (mul_one a).symm))
  rcases ht.2 v with hv | hv <;> rcases ht.2 w with hw | hw
  · have h1 : t (v * w) = v * w := by rw [map_mul, hv, hw]
    rw [ite_eq_left h1, ite_eq_left hv, ite_eq_left hw]
    simp
  · have h1 : t (v * w) = v * w * c := by rw [map_mul, hv, hw, mul_assoc]
    have h2 : ¬ t (v * w) = v * w := by rw [h1]; exact hne _
    have h3 : ¬ t w = w := by rw [hw]; exact hne _
    rw [ite_eq_right h2, ite_eq_left hv, ite_eq_right h3]
    simp
  · have h1 : t (v * w) = v * w * c := by rw [map_mul, hv, hw, mul_right_comm]
    have h2 : ¬ t (v * w) = v * w := by rw [h1]; exact hne _
    have h3 : ¬ t v = v := by rw [hv]; exact hne _
    rw [ite_eq_right h2, ite_eq_right h3, ite_eq_left hw]
    simp
  · have h1 : t (v * w) = v * w := by rw [map_mul, hv, hw, mul_mul_mul_comm, hcc, mul_one]
    have h3 : ¬ t v = v := by rw [hv]; exact hne _
    have h4 : ¬ t w = w := by rw [hw]; exact hne _
    rw [ite_eq_left h1, ite_eq_right h3, ite_eq_right h4]
    decide

open scoped Classical in
private theorem exists_dual_of_isTransvectionWith {c : W} {t : MulAut W}
    (ht : IsTransvectionWith t c) :
    ∃ (F : Module.Dual (ZMod 2) (Additive W)) (h : F (Additive.ofMul c) = 0), tvAut F c h = t := by
  let F : Module.Dual (ZMod 2) (Additive W) :=
    { toFun := fun x => if t (Additive.toMul x) = Additive.toMul x then 0 else 1
      map_add' := fun x y => transv_ite_add ht (Additive.toMul x) (Additive.toMul y)
      map_smul' := by
        intro a x
        rcases zmod_two_cases a with rfl | rfl
        · simp
        · simp }
  have hF : ∀ v : W, F (Additive.ofMul v) = if t v = v then 0 else 1 := fun v => rfl
  have htc : t c = c := by
    rcases ht.2 c with h | h
    · exact h
    · exfalso
      have hcc : c * c = 1 := mul_self_eq_one_of_module c
      have h1 : t c = t 1 := by rw [h, hcc, map_one]
      exact ht.1 (t.injective h1)
  have hFc : F (Additive.ofMul c) = 0 := by rw [hF, ite_eq_left htc]
  refine ⟨F, hFc, MulEquiv.ext fun v => ?_⟩
  rcases zmod_two_cases (F (Additive.ofMul v)) with h | h
  · rw [tvAut_of_eq_zero hFc h]
    by_contra hne
    rw [hF, ite_eq_right (fun h' => hne h'.symm)] at h
    exact one_ne_zero h
  · rw [tvAut_of_eq_one hFc h]
    have hne : ¬ t v = v := fun h' => by
      rw [hF, ite_eq_left h'] at h
      exact zero_ne_one h
    exact ((ht.2 v).resolve_left hne).symm

private theorem natCard_transvections_aux [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {c : W}
    (hc : c ≠ 1) :
    Nat.card {t : MulAut W // IsTransvectionWith t c} = 2 ^ (rk W - 1) := by
  have hbij : Function.Bijective fun F : {F : Module.Dual (ZMod 2) (Additive W) //
        F (Additive.ofMul c) = 0} =>
      (⟨tvAut F.1 c F.2, isTransvectionWith_tvAut F.1 hc F.2⟩ :
        {t : MulAut W // IsTransvectionWith t c}) := by
    refine ⟨tvAut_injective hc, fun ⟨t, ht⟩ => ?_⟩
    obtain ⟨F, hF, rfl⟩ := exists_dual_of_isTransvectionWith ht
    exact ⟨⟨F, hF⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  have hc' : Additive.ofMul c ≠ 0 := fun h => hc (ofMul_eq_zero.1 h)
  have h1 := natCard_dual_vanishing_mul (K := ZMod 2) hc'
  rw [Nat.card_zmod] at h1
  have h2 : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have h3 : Nat.card W = 2 ^ rk W := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  rw [h2, h3] at h1
  have hrk : 1 ≤ rk W := by
    rcases Nat.eq_zero_or_pos (rk W) with h | h
    · rw [h] at h1
      omega
    · exact h
  have h4 : 2 ^ rk W = 2 ^ (rk W - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

end Aux

variable {V : Type} [CommGroup V] [Finite V]

theorem card_transvections (hV : ∀ v : V, v ^ 2 = 1) (I : Subgroup V) (c : ↥I) (hc : c ≠ 1) :
    Nat.card {t : MulAut ↥I // IsTransvectionWith t c} = 2 ^ (rk I - 1) := by
  have hI : ∀ w : ↥I, w ^ 2 = 1 := fun w => Subtype.ext (hV w)
  let _ : Module (ZMod 2) (Additive ↥I) :=
    AddCommGroup.zmodModule (two_nsmul_eq_zero_of_sq_eq_one hI)
  exact natCard_transvections_aux hI hc

theorem mem_of_card_transvections (hV : ∀ v : V, v ^ 2 = 1) (I : Subgroup V) (c : ↥I) (hc : c ≠ 1)
    (H : Subgroup (MulAut ↥I)) (hH : ∀ t ∈ H, IsTransvectionWith t c)
    (hcard : Nat.card H = 2 ^ (rk I - 1)) :
    ∀ t : MulAut ↥I, IsTransvectionWith t c → t ∈ H := by
  intro t ht
  have hS := card_transvections hV I c hc
  let f : H → {t : MulAut ↥I // IsTransvectionWith t c} := fun h => ⟨h.1, hH h.1 h.2⟩
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun s : {t : MulAut ↥I // IsTransvectionWith t c} => (s : MulAut ↥I)) h)
  have hfin : Finite {t : MulAut ↥I // IsTransvectionWith t c} :=
    (Nat.card_pos_iff.1 (by rw [hS]; positivity)).2
  have hbij := hinj.bijective_of_nat_card_le (by rw [hS, hcard])
  obtain ⟨⟨h, hh⟩, hht⟩ := hbij.2 ⟨t, ht⟩
  have : h = t := congrArg Subtype.val hht
  rw [← this]
  exact hh

omit [Finite V] in
theorem exists_transvection_trivial_on (hV : ∀ v : V, v ^ 2 = 1) (I : Subgroup V) (c : ↥I)
    (hc : c ≠ 1) (J : Subgroup ↥I) (hcJ : c ∈ J) (hJ : J ≠ ⊤) :
    ∃ t : MulAut ↥I, IsTransvectionWith t c ∧ t ≠ 1 ∧ ∀ x ∈ J, t x = x := by
  have hI : ∀ w : ↥I, w ^ 2 = 1 := fun w => Subtype.ext (hV w)
  let _ : Module (ZMod 2) (Additive ↥I) :=
    AddCommGroup.zmodModule (two_nsmul_eq_zero_of_sq_eq_one hI)
  obtain ⟨x, hx⟩ : ∃ x : ↥I, x ∉ J := by
    by_contra h
    push Not at h
    exact hJ (eq_top_iff.2 fun y _ => h y)
  let M : Submodule (ZMod 2) (Additive ↥I) :=
    { carrier := {v | Additive.toMul v ∈ J}
      add_mem' := fun {a b} ha hb => J.mul_mem ha hb
      zero_mem' := J.one_mem
      smul_mem' := by
        intro a v hv
        rcases zmod_two_cases a with rfl | rfl
        · rw [zero_smul]
          exact J.one_mem
        · rw [one_smul]
          exact hv }
  have hxM : Additive.ofMul x ∉ M := hx
  obtain ⟨F, hFx, hFM⟩ := Submodule.exists_le_ker_of_notMem hxM
  have hFc : F (Additive.ofMul c) = 0 :=
    LinearMap.mem_ker.1 (hFM (show Additive.ofMul c ∈ M from hcJ))
  refine ⟨tvAut F c hFc, isTransvectionWith_tvAut F hc hFc, ?_, fun y hy => ?_⟩
  · intro h1
    have h2 : tvAut F c hFc x = x := by rw [h1]; rfl
    exact hFx ((tvAut_eq_self_iff hc hFc x).1 h2)
  · exact tvAut_of_eq_zero hFc (LinearMap.mem_ker.1 (hFM (show Additive.ofMul y ∈ M from hy)))

theorem autSub_eq_top_of_transvections (hV : ∀ v : V, v ^ 2 = 1) {I : Subgroup V}
    {N : Subgroup (MulAut V)} (hN : N ≤ stabSub I) {c : V} (hcI : c ∈ I) (hc1 : c ≠ 1)
    (hfull : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) → t ∈ autSub N I)
    (hgen : Subgroup.closure {x | ∃ n ∈ N, n c = x} = I) : autSub N I = ⊤ := by
  have hexp : ∀ v : ↥I, v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have hu1 : (⟨c, hcI⟩ : ↥I) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hUtop : Subgroup.closure {y : ↥I | ∃ g ∈ autSub N I, g ⟨c, hcI⟩ = y} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : V) ∈ Subgroup.closure {x | ∃ n ∈ N, n c = x} := by
      rw [hgen]
      exact y.2
    have key : ∀ x : V, x ∈ Subgroup.closure {x | ∃ n ∈ N, n c = x} →
        ∃ hx : x ∈ I, (⟨x, hx⟩ : ↥I) ∈
          Subgroup.closure {y : ↥I | ∃ g ∈ autSub N I, g ⟨c, hcI⟩ = y} := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨n, hn, rfl⟩ := hx
        exact ⟨(mem_stabSub.1 (hN hn) c).2 hcI, Subgroup.subset_closure
          ⟨resHom I ⟨n, hN hn⟩, mem_autSub.2 ⟨⟨n, hN hn⟩, hn, rfl⟩, Subtype.ext rfl⟩⟩
      | one => exact ⟨I.one_mem, Subgroup.one_mem _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨haI, ha'⟩ := ha
        obtain ⟨hbI, hb'⟩ := hb
        exact ⟨I.mul_mem haI hbI, Subgroup.mul_mem _ ha' hb'⟩
      | inv a _ ha =>
        obtain ⟨haI, ha'⟩ := ha
        exact ⟨I.inv_mem haI, Subgroup.inv_mem _ ha'⟩
    obtain ⟨hyI, hy'⟩ := key _ hy
    exact hy'
  set G : Subgroup (MulAut ↥I) := autSub N I with hG
  set U : Subgroup ↥I := Subgroup.closure {y : ↥I | ∃ g ∈ G, g ⟨c, hcI⟩ = y} with hU
  set L : Subgroup (MulAut ↥I) := Subgroup.closure
    {x | ∃ g ∈ G, ∃ t : MulAut ↥I, IsTransvectionWith t ⟨c, hcI⟩ ∧ x = g * t * g⁻¹} with hL
  have hb := b410 hexp G ⟨c, hcI⟩ hu1 hfull U hU L hL
  have hLG : L ≤ G := by
    rw [hL, Subgroup.closure_le]
    rintro _ ⟨g, hg, t, ht, rfl⟩
    exact G.mul_mem (G.mul_mem hg (hfull t ht)) (G.inv_mem hg)
  have hmemU : ∀ y : ↥I, y ∈ U := fun y => by
    rw [hUtop]
    exact Subgroup.mem_top y
  rw [eq_top_iff]
  intro φ _
  let ψ : MulAut ↥U :=
    { toFun := fun x => ⟨φ x.1, hmemU _⟩
      invFun := fun x => ⟨φ.symm x.1, hmemU _⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (φ.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul φ x.1 y.1) }
  have hψ : ψ ∈ autSub L U := by
    rw [hb]
    exact Subgroup.mem_top _
  obtain ⟨g, hgL, hgψ⟩ := mem_autSub.1 hψ
  have hgφ : (g : MulAut ↥I) = φ := by
    refine MulEquiv.ext fun y => ?_
    have := congrArg (fun m : MulAut ↥U => ((m ⟨y, hmemU y⟩ : ↥U) : ↥I)) hgψ
    exact this
  rw [← hgφ]
  exact hLG hgL

end CFSG.Quasithin
