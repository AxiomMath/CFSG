module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Fischer.Classification.Symplectic.OrthoGen

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

open CFSG.Open CFSG.Fischer.Classification Matrix Equiv

section Perm

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_ne {a b d : α} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    swap a b * swap a d ≠ swap a d * swap a b := by
  intro h
  have := congrArg (fun σ : Perm α => σ a) h
  simp only [Perm.mul_apply, swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd),
    swap_apply_of_ne_of_ne (Ne.symm hab) hbd] at this
  exact hbd this.symm

theorem disjoint_of_swap_commute {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : swap a b ≠ swap c d) (hc : swap a b * swap c d = swap c d * swap a b) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have key : ∀ {x y z : α}, x ≠ y → x ≠ z → swap x y ≠ swap x z →
      swap x y * swap x z ≠ swap x z * swap x y := fun hxy hxz hne' =>
    swap_mul_swap_ne hxy hxz fun h => hne' (by rw [h])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact key hab hcd hne hc
  · rintro rfl
    rw [swap_comm c] at hne hc
    exact key hab (Ne.symm hcd) hne hc
  · rintro rfl
    rw [swap_comm a] at hne hc
    exact key (Ne.symm hab) hcd hne hc
  · rintro rfl
    rw [swap_comm a, swap_comm c] at hne hc
    exact key (Ne.symm hab) (Ne.symm hcd) hne hc

theorem swap_commute_of_ne {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b :=
  (Perm.Disjoint.commute (Perm.disjoint_swap_swap (by simp_all))).eq

end Perm

variable {H : Type} [Group H] {D : Set H}

theorem eq_six_of_perm (hQ : QHyp H D) {m : ℕ} (φ : H ≃* Perm (Fin m))
    (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) : m = 6 := by
  obtain ⟨e, he, f, hf, hef, hc⟩ := hQ.rank
  obtain ⟨g, hg, hge, hgf, hall⟩ := hQ.thick e he f hf hef hc
  obtain ⟨a, b, hab, hea⟩ := (hφ e).1 he
  obtain ⟨c, d, hcd, hfc⟩ := (hφ f).1 hf
  obtain ⟨p, q, hpq, hgp⟩ := (hφ g).1 hg
  have hcomm : ∀ {x y : H}, x * y = y * x → φ x * φ y = φ y * φ x := fun h => by
    rw [← map_mul, ← map_mul, h]
  have hne : ∀ {x y : H}, x ≠ y → φ x ≠ φ y := fun h h' => h (φ.injective h')
  have hge' : e * g = g * e := hall e he rfl hc
  have hgf' : f * g = g * f := hall f hf hc.symm rfl
  obtain ⟨hac, had, hbc, hbd⟩ := disjoint_of_swap_commute hab hcd
    (by rw [← hea, ← hfc]; exact hne hef) (by rw [← hea, ← hfc]; exact hcomm hc)
  obtain ⟨hpa, hpb, hqa, hqb⟩ := disjoint_of_swap_commute hpq hab
    (by rw [← hgp, ← hea]; exact hne hge) (by rw [← hgp, ← hea]; exact hcomm hge'.symm)
  obtain ⟨hpc, hpd, hqc, hqd⟩ := disjoint_of_swap_commute hpq hcd
    (by rw [← hgp, ← hfc]; exact hne hgf) (by rw [← hgp, ← hfc]; exact hcomm hgf'.symm)
  have hinj : Function.Injective ![a, b, c, d, p, q] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have h6 : 6 ≤ m := by simpa using Fintype.card_le_of_injective _ hinj
  by_contra hm
  obtain ⟨r, hr⟩ : ∃ r, r ∉ Set.range ![a, b, c, d, p, q] := by
    by_contra! hall'
    have hsurj : Function.Surjective ![a, b, c, d, p, q] := fun r => hall' r
    have := Fintype.card_le_of_surjective _ hsurj
    simp only [Fintype.card_fin] at this
    omega
  simp only [Set.mem_range, not_exists, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at hr
  have hr' : r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d ∧ r ≠ p ∧ r ≠ q := by
    refine ⟨fun h => hr.1 h.symm, fun h => hr.2.1 h.symm, fun h => hr.2.2.1 h.symm,
      fun h => hr.2.2.2.1 h.symm, fun h => hr.2.2.2.2.1 h.symm, fun h => ?_⟩
    have := hr.2.2.2.2.2
    simp_all
  obtain ⟨hra, hrb, hrc, hrd, hrp, hrq⟩ := hr'
  set x := φ.symm (swap p r) with hx
  have hφx : φ x = swap p r := φ.apply_symm_apply _
  have hxD : x ∈ D := (hφ x).2 ⟨p, r, fun h => hrp h.symm, hφx⟩
  have hxe : x * e = e * x := φ.injective (by
    rw [map_mul, map_mul, hφx, hea]
    exact swap_commute_of_ne (fun h => hrp h.symm) hab hpa hpb hra hrb)
  have hxf : x * f = f * x := φ.injective (by
    rw [map_mul, map_mul, hφx, hfc]
    exact swap_commute_of_ne (fun h => hrp h.symm) hcd hpc hpd hrc hrd)
  have hxg := hcomm (hall x hxD hxe hxf)
  rw [hφx, hgp] at hxg
  exact swap_mul_swap_ne (fun h => hrp h.symm) hpq hrq hxg

theorem exists_pairings_of_nondeg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {k : ℕ} {w : Fin k → V}
    (hw : LinearIndependent K w) (c : Fin k → K) : ∃ x, ∀ i, B x (w i) = c i := by
  let pm : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => B.flip (w i)
  have hpm : ∀ x i, pm x i = B x (w i) := fun _ _ => rfl
  suffices h : LinearMap.range pm = ⊤ by
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 h c
    exact ⟨x, fun i => by rw [← hpm, hx]⟩
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set a : Fin k → K := fun i => φ fun j => if i = j then 1 else 0
  have hφa : ∀ y, φ y = ∑ i, a i * y i := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  have hsum : ∑ i, a i • w i = 0 := by
    apply hnd
    intro y
    rw [hsymm, map_sum]
    have h0 : φ (pm y) = 0 := hφ ⟨y, rfl⟩
    rw [hφa] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, hpm]
  have ha : ∀ i, a i = 0 := Fintype.linearIndependent_iff.1 hw a hsum
  apply hφ0
  refine LinearMap.ext fun y => ?_
  rw [hφa, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [ha i, zero_mul]

section Orthogonal

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

omit [Fintype ι] [DecidableEq ι] in
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

omit [Fintype ι] [DecidableEq ι] in
theorem polar_self_zmod_two (x : ι → ZMod 2) : QuadraticMap.polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem map_add_polar (u v : ι → ZMod 2) :
    Q (u + v) = Q u + Q v + QuadraticMap.polar Q u v := by
  rw [QuadraticMap.polar]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem add_self_zmod_two (u : ι → ZMod 2) : u + u = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem eq_of_add_eq_zero_zmod_two {u v : ι → ZMod 2} (h : u + v = 0) : u = v := by
  have := congrArg (· + v) h
  simp only [add_assoc, add_self_zmod_two, add_zero, zero_add] at this
  exact this

theorem tv_mulVec {v : ι → ZMod 2} (hv : Q v = 1) (x : ι → ZMod 2) :
    (orthTransvectionGL Q v : Matrix ι ι (ZMod 2)) *ᵥ x = x + QuadraticMap.polar Q x v • v :=
  orthTransvectionGL_mulVec hv x

theorem tv_mem {v : ι → ZMod 2} (hv : Q v = 1) :
    orthTransvectionGL Q v ∈ fischerTransvections (QuadraticMap.polar Q) (fun v => Q v = 1) :=
  orthTransvectionGL_mem_fischerTransvections hv

theorem eq_tv_of_mem {g : GL ι (ZMod 2)}
    (hg : g ∈ fischerTransvections (QuadraticMap.polar Q) (fun v => Q v = 1)) :
    ∃ v, Q v = 1 ∧ g = orthTransvectionGL Q v :=
  eq_orthTransvectionGL_of_mem_fischerTransvections hg

theorem tv_mem_group {v : ι → ZMod 2} (hv : Q v = 1) :
    orthTransvectionGL Q v ∈ (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) :=
  fischerTransvections_polar_subset (tv_mem hv)

theorem tv_mul_mulVec {a b : ι → ZMod 2} (ha : Q a = 1) (hb : Q b = 1) (x : ι → ZMod 2) :
    ((orthTransvectionGL Q a * orthTransvectionGL Q b : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
      x = x + QuadraticMap.polar Q x b • b + QuadraticMap.polar Q x a • a +
        (QuadraticMap.polar Q x b * QuadraticMap.polar Q b a) • a := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, tv_mulVec hb, tv_mulVec ha,
    QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, add_smul, mul_smul]
  abel

theorem exists_polar_eq_one (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    {a : ι → ZMod 2} (ha0 : a ≠ 0) : ∃ x, QuadraticMap.polar Q x a = 1 := by
  by_contra! hx
  apply ha0
  refine hnd a fun y => ?_
  rw [QuadraticMap.polar_comm]
  exact (zmod_two_eq_zero_or_one _).resolve_right (hx y)

omit [Fintype ι] [DecidableEq ι] in
theorem ne_zero_of_eq_one {a : ι → ZMod 2} (ha : Q a = 1) : a ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at ha
  exact zero_ne_one ha

theorem tv_commute_iff (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    {a b : ι → ZMod 2} (ha : Q a = 1) (hb : Q b = 1) :
    orthTransvectionGL Q a * orthTransvectionGL Q b =
        orthTransvectionGL Q b * orthTransvectionGL Q a ↔ QuadraticMap.polar Q a b = 0 := by
  constructor
  · intro h
    rcases zmod_two_eq_zero_or_one (QuadraticMap.polar Q a b) with h0 | h1
    · exact h0
    exfalso
    obtain ⟨x, hx⟩ := exists_polar_eq_one hnd (ne_zero_of_eq_one hb)
    have hab : QuadraticMap.polar Q b a = 1 := by rw [QuadraticMap.polar_comm]; exact h1
    have hx' := congrArg (fun g : GL ι (ZMod 2) => (g : Matrix ι ι (ZMod 2)) *ᵥ x) h
    simp only [tv_mul_mulVec ha hb, tv_mul_mulVec hb ha] at hx'
    rw [hx, hab, h1, one_mul, one_smul, one_smul, mul_one] at hx'
    have key : a = QuadraticMap.polar Q x a • b := by
      have h2 := congrArg (· + (x + b + QuadraticMap.polar Q x a • a)) hx'
      have e1 : x + b + QuadraticMap.polar Q x a • a + a + (x + b + QuadraticMap.polar Q x a • a) =
          a := by
        rw [add_comm _ a, add_assoc a, add_self_zmod_two, add_zero]
      have e2 : x + QuadraticMap.polar Q x a • a + b + QuadraticMap.polar Q x a • b +
          (x + b + QuadraticMap.polar Q x a • a) = QuadraticMap.polar Q x a • b := by
        have : x + QuadraticMap.polar Q x a • a + b + QuadraticMap.polar Q x a • b =
            QuadraticMap.polar Q x a • b + (x + b + QuadraticMap.polar Q x a • a) := by abel
        rw [this, add_assoc, add_self_zmod_two, add_zero]
      rw [e1, e2] at h2
      exact h2
    rcases zmod_two_eq_zero_or_one (QuadraticMap.polar Q x a) with h0 | h0
    · rw [h0, zero_smul] at key
      exact ne_zero_of_eq_one ha key
    · rw [h0, one_smul] at key
      rw [key, polar_self_zmod_two] at h1
      exact zero_ne_one h1
  · intro h
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [tv_mul_mulVec ha hb, tv_mul_mulVec hb ha, h, QuadraticMap.polar_comm Q b a, h, mul_zero,
      mul_zero, zero_smul, zero_smul, add_zero, add_zero, add_right_comm]

theorem eq_of_tv_eq (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    {a b : ι → ZMod 2} (ha : Q a = 1) (hb : Q b = 1)
    (h : orthTransvectionGL Q a = orthTransvectionGL Q b) : a = b := by
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd (ne_zero_of_eq_one ha)
  have hx' := congrArg (fun g : GL ι (ZMod 2) => (g : Matrix ι ι (ZMod 2)) *ᵥ x) h
  simp only [tv_mulVec ha, tv_mulVec hb, hx, one_smul, add_right_inj] at hx'
  rcases zmod_two_eq_zero_or_one (QuadraticMap.polar Q x b) with h0 | h1
  · rw [h0, zero_smul] at hx'
    exact absurd hx' (ne_zero_of_eq_one ha)
  · rwa [h1, one_smul] at hx'

variable {H : Type} [Group H] {D : Set H}

theorem false_of_orthogonal (hQ : QHyp H D)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨e, he, f, hf, hef, hc⟩ := hQ.rank
  obtain ⟨g, hg, hge, hgf, hall⟩ := hQ.thick e he f hf hef hc
  obtain ⟨u, hu, heu⟩ := eq_tv_of_mem ((hφ e).1 he)
  obtain ⟨v, hv, hfv⟩ := eq_tv_of_mem ((hφ f).1 hf)
  obtain ⟨w, hw, hgw⟩ := eq_tv_of_mem ((hφ g).1 hg)
  have hcomm : ∀ {x y : H}, x * y = y * x →
      (φ x : GL ι (ZMod 2)) * φ y = (φ y : GL ι (ZMod 2)) * φ x := fun h => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  have hne : ∀ {x y : H}, x ≠ y → (φ x : GL ι (ZMod 2)) ≠ φ y := fun h h' =>
    h (φ.injective (Subtype.ext h'))
  have huv : QuadraticMap.polar Q u v = 0 := by
    rw [← tv_commute_iff hnd hu hv, ← heu, ← hfv]
    exact hcomm hc
  have hwu : QuadraticMap.polar Q w u = 0 := by
    rw [← tv_commute_iff hnd hw hu, ← heu, ← hgw]
    exact hcomm (hall e he rfl hc).symm
  have hwv : QuadraticMap.polar Q w v = 0 := by
    rw [← tv_commute_iff hnd hw hv, ← hfv, ← hgw]
    exact hcomm (hall f hf hc.symm rfl).symm
  have hu_ne_v : u ≠ v := fun h => hne hef (by rw [heu, hfv, h])
  have hw_ne_u : w ≠ u := fun h => hne hge (by rw [heu, hgw, h])
  have hw_ne_v : w ≠ v := fun h => hne hgf (by rw [hfv, hgw, h])
  have hw_ne_uv : w ≠ u + v := by
    rintro rfl
    rw [map_add_polar, hu, hv, huv] at hw
    exact absurd hw (by decide)
  have hli : LinearIndependent (ZMod 2) ![u, v, w] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc' i
    rw [Fin.sum_univ_three] at hc'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hc'
    rcases zmod_two_eq_zero_or_one (c 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases zmod_two_eq_zero_or_one (c 2) with h2 | h2 <;>
      simp only [h0, h1, h2, zero_smul, one_smul, zero_add, add_zero] at hc'
    · fin_cases i <;> assumption
    · exact absurd hc' (ne_zero_of_eq_one hw)
    · exact absurd hc' (ne_zero_of_eq_one hv)
    · exact absurd (eq_of_add_eq_zero_zmod_two hc') hw_ne_v.symm
    · exact absurd hc' (ne_zero_of_eq_one hu)
    · exact absurd (eq_of_add_eq_zero_zmod_two hc') hw_ne_u.symm
    · exact absurd (eq_of_add_eq_zero_zmod_two hc') hu_ne_v
    · exfalso
      apply hw_ne_uv
      have := congrArg (· + w) hc'
      simp only [zero_add, add_assoc, add_self_zmod_two, add_zero] at this
      exact this.symm
  have hsymm : ∀ x y, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x :=
    fun x y => QuadraticMap.polar_comm _ _ _
  obtain ⟨y, hy⟩ := exists_pairings_of_nondeg (QuadraticMap.polarBilin Q) hsymm
    (fun x hx => hnd x fun y => hx y) hli ![0, 0, 1]
  have hyu : QuadraticMap.polar Q y u = 0 := hy 0
  have hyv : QuadraticMap.polar Q y v = 0 := hy 1
  have hyw : QuadraticMap.polar Q y w = 1 := hy 2
  have huw : QuadraticMap.polar Q u w = 0 := by rw [QuadraticMap.polar_comm]; exact hwu
  obtain ⟨x, hx, hxu, hxv, hxw⟩ : ∃ x, Q x = 1 ∧ QuadraticMap.polar Q x u = 0 ∧
      QuadraticMap.polar Q x v = 0 ∧ QuadraticMap.polar Q x w = 1 := by
    rcases zmod_two_eq_zero_or_one (Q y) with h0 | h1
    · refine ⟨y + u, ?_, ?_, ?_, ?_⟩
      · rw [map_add_polar, h0, hu, hyu]; rfl
      · rw [QuadraticMap.polar_add_left, hyu, polar_self_zmod_two, add_zero]
      · rw [QuadraticMap.polar_add_left, hyv, huv, add_zero]
      · rw [QuadraticMap.polar_add_left, hyw, huw, add_zero]
    · exact ⟨y, h1, hyu, hyv, hyw⟩
  set d := φ.symm ⟨orthTransvectionGL Q x, tv_mem_group hx⟩ with hd
  have hφd : (φ d : GL ι (ZMod 2)) = orthTransvectionGL Q x := by
    rw [hd, MulEquiv.apply_symm_apply]
  have hdD : d ∈ D := (hφ d).2 (hφd ▸ tv_mem hx)
  have hcomm' : ∀ {z : H}, (φ d : GL ι (ZMod 2)) * φ z = (φ z : GL ι (ZMod 2)) * φ d →
      d * z = z * d := fun h => φ.injective (Subtype.ext (by
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, h]))
  have hde : d * e = e * d := hcomm' (by
    rw [hφd, heu, tv_commute_iff hnd hx hu]
    exact hxu)
  have hdf : d * f = f * d := hcomm' (by
    rw [hφd, hfv, tv_commute_iff hnd hx hv]
    exact hxv)
  have hdg := hcomm (hall d hdD hde hdf)
  rw [hφd, hgw, tv_commute_iff hnd hx hw, hxw] at hdg
  exact one_ne_zero hdg

end Orthogonal

end CFSG.Timmesfeld.Transvection.QTwo
