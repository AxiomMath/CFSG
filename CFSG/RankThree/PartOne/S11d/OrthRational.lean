module

public import CFSG.RankThree.PartOne.S11d.OrthFixedLayer
public import CFSG.RankThree.PartOne.S11d.OddIsoBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Eichler

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_comm_semilinear {σ : K ≃+* K} (S : V ≃+ V)
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hQS : ∀ v, Q (S v) = σ (Q v)) {u w : V}
    (hu : Q u = 0) (huw : polar Q u w = 0) (hSu : S u = u) (hSw : S w = w) (v : V) :
    S (eichler Q u w v) = eichler Q u w (S v) := by
  have hp : ∀ a b, polar Q (S a) (S b) = σ (polar Q a b) := fun a b => by
    have := polar_map_semilin S σ 1 (fun v => by rw [one_mul]; exact hQS v) a b
    rwa [one_mul] at this
  have h1 : polar Q (S v) u = σ (polar Q v u) := by simpa [hSu] using hp v u
  have h2 : polar Q (S v) w = σ (polar Q v w) := by simpa [hSw] using hp v w
  have h3 : σ (Q w) = Q w := by
    have := hQS w
    rw [hSw] at this
    exact this.symm
  rw [eichler_apply hu huw, eichler_apply hu huw]
  simp only [map_sub, map_add, hS, hSu, hSw, h1, h2, h3, map_mul]

variable [CharP K 2]

theorem eichler_sq_eq_one {u w : V} (huw : polar Q u w = 0) : eichler Q u w ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [pow_two, eichler_mul huw huw]
  have : w + w = 0 := by rw [← two_smul K w, h2, zero_smul]
  rw [this, eichler_zero_right]

theorem eichler_pair_noncomm (P : HypPair Q) {w : V} (hw : w ∈ P.perp) (hQw : Q w ≠ 0) :
    eichler Q P.e w * eichler Q P.f w ≠ eichler Q P.f w * eichler Q P.e w := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp hw
  have hwe : polar Q w P.e = 0 := by rw [polar_comm, hew]
  have hwf : polar Q w P.f = 0 := by rw [polar_comm, hfw]
  have hww : polar Q w w = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hfe : polar Q P.f P.e = 1 := P.polar_fe
  have hef : polar Q P.e P.f = 1 := P.polar_ef
  have hEf_e : eichler Q P.f w P.e = P.e + w - Q w • P.f := by
    rw [eichler_apply P.Q_f hfw, hef, hew]
    simp [sub_eq_add_neg]
  have hEf_w : eichler Q P.f w w = w := by
    rw [eichler_apply P.Q_f hfw, hwf, hww]
    simp
  have hEe_f : eichler Q P.e w P.f = P.f + w - Q w • P.e := by
    rw [eichler_apply P.Q_e hew, hfe, hfw]
    simp [sub_eq_add_neg]
  have hEe_w : eichler Q P.e w w = w := by
    rw [eichler_apply P.Q_e hew, hwe, hww]
    simp
  have hEf_f : eichler Q P.f w P.f = P.f := eichler_apply_self _ _
  intro hcomm
  have h1 := congrArg (fun g : V ≃ₗ[K] V => g P.f) hcomm
  simp only [LinearEquiv.mul_apply, hEf_f, hEe_f, map_sub, map_add, map_smul, hEf_w,
    hEf_e] at h1
  have h5 : Q w • (w - Q w • P.f) = 0 := by
    have h1' := sub_eq_zero.mpr h1
    rw [← h1']
    module
  have h6 : w - Q w • P.f = 0 := (smul_eq_zero.mp h5).resolve_left hQw
  have h7 : polar Q P.e (w - Q w • P.f) = 0 := by rw [h6, polar_zero_right]
  rw [polar_sub_right, polar_smul_right_eq, hew, hef] at h7
  apply hQw
  linear_combination -h7

end Eichler

section Rational

variable {K : Type} [Field K] [Finite K] [CharP K 2] (k : Subfield K) {σ : K ≃+* K} {d : ℕ}

omit [Finite K] [CharP K 2] in
theorem vecIncl_smul (c : k) (v : Fin d → k) : vecIncl k (c • v) = (c : K) • vecIncl k v := by
  funext i
  simp [vecIncl]

omit [Finite K] [CharP K 2] in
theorem vecIncl_zero : vecIncl k (0 : Fin d → k) = 0 := by
  funext i
  simp [vecIncl]

omit [Finite K] [CharP K 2] in
theorem vecIncl_injective : Function.Injective (vecIncl (K := K) (d := d) k) := fun _ _ h =>
  funext fun i => Subtype.ext (congrFun h i)

omit [Finite K] [CharP K 2] in
theorem vecIncl_sum {ι : Type*} (s : Finset ι) (f : ι → Fin d → k) :
    vecIncl k (∑ i ∈ s, f i) = ∑ i ∈ s, vecIncl k (f i) := by
  funext i
  simp [vecIncl]

omit [Finite K] [CharP K 2] in
theorem coordinateFieldMap_vecIncl (hσk : ∀ c, c ∈ k ↔ σ c = c) (v : Fin d → k) :
    coordinateFieldMap d σ (vecIncl k v) = vecIncl k v :=
  funext fun i => (hσk _).mp (v i).2

omit [Finite K] [CharP K 2] in
theorem exists_vecIncl_of_fixed (hσk : ∀ c, c ∈ k ↔ σ c = c) {v : Fin d → K}
    (h : coordinateFieldMap d σ v = v) : ∃ v₀ : Fin d → k, vecIncl k v₀ = v :=
  ⟨fun i => ⟨v i, (hσk _).mpr (congrFun h i)⟩, rfl⟩

def ratSpace (W : Submodule K (Fin d → K)) : Submodule k (Fin d → k) where
  carrier := {v | vecIncl k v ∈ W}
  add_mem' := fun ha hb => by
    simp only [Set.mem_ofPred_eq, vecIncl_add]
    exact W.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [vecIncl_zero]
    exact W.zero_mem
  smul_mem' := fun c v hv => by
    simp only [Set.mem_ofPred_eq, vecIncl_smul]
    exact W.smul_mem _ hv

omit [Finite K] [CharP K 2] in
theorem mem_ratSpace {W : Submodule K (Fin d → K)} {v : Fin d → k} :
    v ∈ ratSpace k W ↔ vecIncl k v ∈ W := Iff.rfl

variable {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} {p : ℕ}

omit [Finite K] [CharP K 2] in
theorem coordinateFieldMap_pow
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (j : ℕ) (v : Fin d → K) :
    coordinateFieldMap d σ ((x.toLinearMap ^ j) v) =
      (x.toLinearMap ^ j) (coordinateFieldMap d σ v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    exact congrArg ((x.toLinearMap ^ j)) (hSx v)

omit [Finite K] in
theorem fixed_le_span_vecIncl (hσk : ∀ c, c ∈ k ↔ σ c = c) (hodd : Odd p) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v)) :
    fixedSpace x ≤
      Submodule.span K (vecIncl k '' (ratSpace k (fixedSpace x) : Set (Fin d → k))) := by
  have hA : x.toLinearMap ^ p = 1 := by
    rw [← toLinearMap_pow, hxp]
    rfl
  have hrange : LinearMap.range (OddIso.avg x.toLinearMap p) = fixedSpace x :=
    OddIso.range_avg hodd hA
  have hbasis : ∀ i : Fin d, ∃ v₀ : Fin d → k,
      vecIncl k v₀ = OddIso.avg x.toLinearMap p (Pi.single i 1) := by
    intro i
    refine exists_vecIncl_of_fixed k hσk ?_
    unfold OddIso.avg
    rw [LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordinateFieldMap_pow hSx]
    congr 1
    funext l
    by_cases hl : l = i
    · subst hl; simp [coordinateFieldMap_apply]
    · simp [coordinateFieldMap_apply, hl]
  intro w hw
  rw [← hrange] at hw
  obtain ⟨u, rfl⟩ := hw
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin d → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hu, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨v₀, hv₀⟩ := hbasis i
  refine ⟨v₀, ?_, hv₀⟩
  rw [SetLike.mem_coe, mem_ratSpace, hv₀, ← hrange]
  exact LinearMap.mem_range_self _ _

omit [Finite K] in
theorem finrank_le_finrank_ratSpace (hσk : ∀ c, c ∈ k ↔ σ c = c) (hodd : Odd p) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v)) :
    finrank K (fixedSpace x) ≤ finrank k (ratSpace k (fixedSpace x)) := by
  classical
  set W₀ := ratSpace k (fixedSpace x) with hW₀
  let b := Module.finBasis k W₀
  let f : Fin (finrank k W₀) → (Fin d → K) := fun j => vecIncl k (b j : Fin d → k)
  have hle : fixedSpace x ≤ Submodule.span K (Set.range f) := by
    refine (fixed_le_span_vecIncl k hσk hodd hxp hSx).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ W₀ := hw
    have hexp : w = ∑ j, (b.repr ⟨w, hw'⟩ j) • (b j : Fin d → k) := by
      have h1 := b.sum_repr ⟨w, hw'⟩
      have h2 := congrArg (fun z : W₀ => (z : Fin d → k)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    rw [hexp, vecIncl_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [vecIncl_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  calc finrank K (fixedSpace x)
      ≤ finrank K (Submodule.span K (Set.range f)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (finrank k W₀)) := finrank_range_le_card f
    _ = finrank k W₀ := Fintype.card_fin _

omit [Finite K] in
theorem polarNondegOn_ratSpace (hσk : ∀ c, c ∈ k ↔ σ c = c) {Q : QuadraticForm K (Fin d → K)}
    {Q₀ : QuadraticForm k (Fin d → k)} (hext : IsExtension k Q₀ Q) (hx : OddOrderIsometry Q p x)
    (hodd : Odd p) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v)) :
    PolarNondegOn Q₀ (ratSpace k (fixedSpace x)) := by
  intro w₀ hw₀ hperp
  have hspan := fixed_le_span_vecIncl k hσk hodd hxp hSx
  have hW : vecIncl k w₀ ∈ fixedSpace x := hw₀
  have hzero : ∀ w ∈ fixedSpace x, polar Q (vecIncl k w₀) w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => polar Q (vecIncl k w₀) w = 0) ?_ ?_ ?_ ?_
      (hspan hw)
    · rintro _ ⟨y₀, hy₀, rfl⟩
      rw [polar_vecIncl k hext, hperp y₀ hy₀]
      rfl
    · rw [polar_zero_right]
    · intro a b _ _ ha hb
      rw [polar_add_right, ha, hb, add_zero]
    · intro c a _ ha
      rw [polar_smul_right_eq, ha, mul_zero]
  have hnd := hx.polarBilin_fixed_nondegenerate
  have h0 : (⟨vecIncl k w₀, hW⟩ : fixedSpace x) = 0 := by
    refine hnd.1 _ fun b => ?_
    rw [polarBilin_apply_apply, polar_comp_subtype]
    exact hzero b b.2
  exact vecIncl_injective k (by simpa [vecIncl_zero] using congrArg Subtype.val h0)

omit [CharP K 2] in
theorem nondegenerate_comp_of_polarNondegOn {F V' : Type*} [Field F] [AddCommGroup V']
    [Module F V'] {R : QuadraticForm F V'} {U : Submodule F V'} (h : PolarNondegOn R U) :
    (polarBilin (R.comp U.subtype)).Nondegenerate := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := h a a.2 fun y hy => by
      have h1 := ha ⟨y, hy⟩
      rwa [polarBilin_apply_apply, polar_comp_subtype] at h1
    exact Subtype.ext this
  · have := h b b.2 fun y hy => by
      have h1 := hb ⟨y, hy⟩
      rwa [polarBilin_apply_apply, polar_comp_subtype, polar_comm] at h1
    exact Subtype.ext this

theorem exists_rational_hyp_data (hσk : ∀ c, c ∈ k ↔ σ c = c) {Q : QuadraticForm K (Fin d → K)}
    {Q₀ : QuadraticForm k (Fin d → k)} (hext : IsExtension k Q₀ Q) (hodd : Odd p)
    (hx : OddOrderIsometry Q p x) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (h4 : 4 ≤ finrank K (fixedSpace x)) :
    ∃ (P : HypPair Q) (w : Fin d → K), P.e ∈ fixedSpace x ∧ P.f ∈ fixedSpace x ∧
      w ∈ fixedSpace x ∧ w ∈ P.perp ∧ Q w ≠ 0 ∧ coordinateFieldMap d σ P.e = P.e ∧
      coordinateFieldMap d σ P.f = P.f ∧ coordinateFieldMap d σ w = w := by
  have : Finite k := Finite.of_injective k.subtype k.subtype_injective
  set W := fixedSpace x with hW
  set W₀ := ratSpace k W with hW₀
  have h4' : 4 ≤ finrank k W₀ := h4.trans (finrank_le_finrank_ratSpace k hσk hodd hxp hSx)
  have hnd₀ : PolarNondegOn Q₀ W₀ := polarNondegOn_ratSpace k hσk hext hx hodd hxp hSx
  have hcomp := nondegenerate_comp_of_polarNondegOn hnd₀
  have : CharP k 2 := (RingHom.charP_iff_charP k.subtype 2).mpr inferInstance
  have h2k : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have heven : Even (finrank k W₀) := by
    refine LinearMap.BilinForm.IsAlt.even_finrank (B := polarBilin (Q₀.comp W₀.subtype))
      (fun a => ?_) hcomp
    rw [polarBilin_apply_apply, polar_self_eq_two_mul, h2k, zero_mul]
  obtain ⟨m, hm⟩ := heven
  obtain ⟨e, he0, hQe⟩ := exists_singular_of_even_regular (Q₀.comp W₀.subtype) hcomp (n := m)
    (by omega) (by omega)
  obtain ⟨P₀, hPe, hPf⟩ := exists_hypPair_of_mem hcomp (e := (e : Fin d → k)) e.2 hQe
    (fun h => he0 (Subtype.ext h))
  have hePW : P₀.e ∈ W₀ := hPe ▸ e.2
  have hU := CFSG.LocalAnalysis.ComponentInitial.finrank_inf_perp_add_two P₀ hePW hPf
  have hUnd : PolarNondegOn Q₀ (W₀ ⊓ P₀.perp) := hnd₀.inf_perp P₀ hePW hPf
  obtain ⟨w₀, hw₀U, hQw₀⟩ : ∃ w₀ ∈ W₀ ⊓ P₀.perp, Q₀ w₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hbot : W₀ ⊓ P₀.perp = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      refine hUnd u hu fun v hv => ?_
      have h1 := QuadraticMap.map_add Q₀ u v
      rw [hall (u + v) (Submodule.add_mem _ hu hv), hall u hu, hall v hv] at h1
      have : polar Q₀ u v = Q₀ (u + v) - Q₀ u - Q₀ v := rfl
      rw [this, hall (u + v) (Submodule.add_mem _ hu hv), hall u hu, hall v hv]
      ring
    rw [hbot, finrank_bot] at hU
    omega
  set P : HypPair Q := ⟨vecIncl k P₀.e, vecIncl k P₀.f, by rw [hext, P₀.Q_e]; rfl,
    by rw [hext, P₀.Q_f]; rfl, by rw [polar_vecIncl k hext, P₀.polar_ef]; rfl⟩ with hP
  have heW : P.e ∈ W := hePW
  have hfW : P.f ∈ W := hPf
  have hwW : vecIncl k w₀ ∈ W := hw₀U.1
  obtain ⟨hew₀, hfw₀⟩ := HypPair.mem_perp.mp hw₀U.2
  have hew : polar Q P.e (vecIncl k w₀) = 0 := by
    change polar Q (vecIncl k P₀.e) (vecIncl k w₀) = 0
    rw [polar_vecIncl k hext, hew₀]
    rfl
  have hfw : polar Q P.f (vecIncl k w₀) = 0 := by
    change polar Q (vecIncl k P₀.f) (vecIncl k w₀) = 0
    rw [polar_vecIncl k hext, hfw₀]
    rfl
  have hwperp : vecIncl k w₀ ∈ P.perp := HypPair.mem_perp.mpr ⟨hew, hfw⟩
  have hQw : Q (vecIncl k w₀) ≠ 0 := by
    rw [hext]
    intro h
    exact hQw₀ (Subtype.ext (by simpa using h))
  exact ⟨P, vecIncl k w₀, heW, hfW, hwW, hwperp, hQw, coordinateFieldMap_vecIncl k hσk _,
    coordinateFieldMap_vecIncl k hσk _, coordinateFieldMap_vecIncl k hσk _⟩

theorem exists_rational_eichler_pair_fix (hσk : ∀ c, c ∈ k ↔ σ c = c)
    {Q : QuadraticForm K (Fin d → K)} {Q₀ : QuadraticForm k (Fin d → k)}
    (hext : IsExtension k Q₀ Q) (hQS : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hK : 4 ≤ Nat.card K) (hodd : Odd p) (hx : OddOrderIsometry Q p x) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (h4 : 4 ≤ finrank K (fixedSpace x)) :
    ∃ w ∈ fixedSpace x, Q w ≠ 0 ∧
      ∃ t₁ ∈ supportedFixedDerived Q x,
        (∀ v, coordinateFieldMap d σ (t₁ v) = t₁ (coordinateFieldMap d σ v)) ∧ t₁ ^ 2 = 1 ∧
        t₁ w = w ∧ ∃ t₂ ∈ supportedFixedDerived Q x,
          (∀ v, coordinateFieldMap d σ (t₂ v) = t₂ (coordinateFieldMap d σ v)) ∧ t₂ ^ 2 = 1 ∧
          t₂ w = w ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨P, w, heW, hfW, hwW, hwperp, hQw, hSe, hSf, hSw⟩ :=
    exists_rational_hyp_data k hσk hext hodd hx hxp hSx h4
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp hwperp
  have hwe : polar Q w P.e = 0 := by rw [polar_comm, hew]
  have hwf : polar Q w P.f = 0 := by rw [polar_comm, hfw]
  have hww : polar Q w w = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  obtain ⟨-, hM⟩ := hx.fixed_scalar_data hK h4
  have hS : ∀ (c : K) v, coordinateFieldMap d σ (c • v) = σ c • coordinateFieldMap d σ v :=
    coordinateFieldMap_smul σ
  let P' : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  refine ⟨w, hwW, hQw, eichler Q P.e w, supportedDerived_le_supportedFixedDerived hx
      (hM P heW hfW _ ⟨hwW, hwperp⟩),
    eichler_comm_semilinear (coordinateFieldMap d σ) hS hQS P.Q_e hew hSe hSw,
    eichler_sq_eq_one hew, ?_, eichler Q P.f w,
    supportedDerived_le_supportedFixedDerived hx
      (hM P' hfW heW _ ⟨hwW, HypPair.mem_perp.mpr ⟨hfw, hew⟩⟩),
    eichler_comm_semilinear (coordinateFieldMap d σ) hS hQS P.Q_f hfw hSf hSw,
    eichler_sq_eq_one hfw, ?_, eichler_pair_noncomm P hwperp hQw⟩
  · rw [eichler_apply P.Q_e hew, hwe, hww]
    simp
  · rw [eichler_apply P.Q_f hfw, hwf, hww]
    simp

theorem exists_rational_eichler_pair (hσk : ∀ c, c ∈ k ↔ σ c = c) {Q : QuadraticForm K (Fin d → K)}
    {Q₀ : QuadraticForm k (Fin d → k)} (hext : IsExtension k Q₀ Q)
    (hQS : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hK : 4 ≤ Nat.card K) (hodd : Odd p)
    (hx : OddOrderIsometry Q p x) (hxp : x ^ p = 1)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (h4 : 4 ≤ finrank K (fixedSpace x)) :
    ∃ t₁ ∈ supportedFixedDerived Q x,
      (∀ v, coordinateFieldMap d σ (t₁ v) = t₁ (coordinateFieldMap d σ v)) ∧ t₁ ^ 2 = 1 ∧
      ∃ t₂ ∈ supportedFixedDerived Q x,
        (∀ v, coordinateFieldMap d σ (t₂ v) = t₂ (coordinateFieldMap d σ v)) ∧ t₂ ^ 2 = 1 ∧
        t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨-, -, -, t₁, h₁, hS₁, hsq₁, -, t₂, h₂, hS₂, hsq₂, -, hne⟩ :=
    exists_rational_eichler_pair_fix k hσk hext hQS hK hodd hx hxp hSx h4
  exact ⟨t₁, h₁, hS₁, hsq₁, t₂, h₂, hS₂, hsq₂, hne⟩

end Rational

end CFSG.RankThree.PartOne
