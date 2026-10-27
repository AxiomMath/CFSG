module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockForm
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular

public section

namespace CFSG.StandardType

namespace OrdPNsOm

open QuadraticMap Module

section Frame

variable {K : Type} [Field K] {V : Type}

abbrev FrIdx (m : ℕ) : Type := Fin m ⊕ Fin m ⊕ Fin 2

@[expose] def frSw {m : ℕ} : FrIdx m → FrIdx m :=
  Sum.elim (fun i => .inr (.inl i)) (Sum.elim (fun i => .inl i) fun j => .inr (.inr j.rev))

@[simp] theorem frSw_inl {m : ℕ} (i : Fin m) : frSw (.inl i : FrIdx m) = .inr (.inl i) := rfl

@[simp] theorem frSw_inr_inl {m : ℕ} (i : Fin m) : frSw (.inr (.inl i) : FrIdx m) = .inl i := rfl

@[simp] theorem frSw_inr_inr {m : ℕ} (j : Fin 2) :
    frSw (.inr (.inr j) : FrIdx m) = .inr (.inr j.rev) := rfl

theorem frSw_frSw {m : ℕ} (x : FrIdx m) : frSw (frSw x) = x := by
  rcases x with i | i | j <;> simp

theorem frSw_injective {m : ℕ} : Function.Injective (frSw (m := m)) :=
  Function.LeftInverse.injective frSw_frSw

@[expose] def fvec {m : ℕ} (e f : Fin m → V) (a b : V) : FrIdx m → V :=
  Sum.elim e (Sum.elim f ![a, b])

@[simp] theorem fvec_inl {m : ℕ} (e f : Fin m → V) (a b : V) (i : Fin m) :
    fvec e f a b (.inl i) = e i := rfl

@[simp] theorem fvec_inr_inl {m : ℕ} (e f : Fin m → V) (a b : V) (i : Fin m) :
    fvec e f a b (.inr (.inl i)) = f i := rfl

@[simp] theorem fvec_zero {m : ℕ} (e f : Fin m → V) (a b : V) :
    fvec e f a b (.inr (.inr 0)) = a := rfl

@[simp] theorem fvec_one {m : ℕ} (e f : Fin m → V) (a b : V) :
    fvec e f a b (.inr (.inr 1)) = b := rfl

variable [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def stdQ (c₀ : K) (τ : Bool) {m : ℕ} : FrIdx m → K :=
  Sum.elim 0 (Sum.elim 0 ![if τ then 1 else 0, if τ then c₀ else 0])

structure IsFrame (Q : QuadraticForm K V) (c₀ : K) (τ : Bool) {m : ℕ} (e f : Fin m → V)
    (a b : V) : Prop where
  hyp : TableBOrth.IsHypFamily Q e f
  pea : ∀ i, polar Q (e i) a = 0
  peb : ∀ i, polar Q (e i) b = 0
  pfa : ∀ i, polar Q (f i) a = 0
  pfb : ∀ i, polar Q (f i) b = 0
  pab : polar Q a b = 1
  qa : Q a = if τ then 1 else 0
  qb : Q b = if τ then c₀ else 0

variable [CharP K 2]

omit [CharP K 2] in
theorem polar_self_charTwo [CharP K 2] (v : V) : polar Q v v = 0 := by
  rw [QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]

variable {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin m → V} {a b : V}

omit [CharP K 2] in
theorem IsFrame.quad_fvec (hF : IsFrame Q c₀ τ e f a b) (x : FrIdx m) :
    Q (fvec e f a b x) = stdQ c₀ τ x := by
  rcases x with i | i | j
  · exact hF.hyp.map_e i
  · exact hF.hyp.map_f i
  · fin_cases j
    · exact hF.qa
    · exact hF.qb

theorem IsFrame.polar_fvec (hF : IsFrame Q c₀ τ e f a b) (x y : FrIdx m) :
    polar Q (fvec e f a b x) (fvec e f a b y) = if y = frSw x then 1 else 0 := by
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hF.pab
  rcases x with i | i | j <;> rcases y with i' | i' | j'
  · simp [hF.hyp.polar_ee i i']
  · simp only [fvec_inl, fvec_inr_inl, frSw_inl, Sum.inr.injEq, Sum.inl.injEq, hF.hyp.polar_ef]
    simp [eq_comm]
  · fin_cases j' <;> simp [hF.pea, hF.peb]
  · simp only [fvec_inl, fvec_inr_inl, frSw_inr_inl, Sum.inl.injEq]
    rw [polar_comm, hF.hyp.polar_ef]
  · simp [hF.hyp.polar_ff i i']
  · fin_cases j' <;> simp [hF.pfa, hF.pfb]
  · fin_cases j <;> simp [polar_comm _ a, polar_comm _ b, hF.pea, hF.peb]
  · fin_cases j <;> simp [polar_comm _ a, polar_comm _ b, hF.pfa, hF.pfb]
  · fin_cases j <;> fin_cases j' <;> simp [hF.pab, hba, CharTwo.two_eq_zero]

theorem IsFrame.linearIndependent (hF : IsFrame Q c₀ τ e f a b) :
    LinearIndependent K (fvec e f a b) := by
  classical
  refine TableBOrth.linearIndependent_of_polar_dual (QF := Q)
    (d := fun x => fvec e f a b (frSw x)) fun x y => ?_
  rw [hF.polar_fvec]
  by_cases h : x = y
  · subst h
    simp
  · simp [h, show ¬ frSw y = frSw x from fun h' => h (frSw_injective h').symm]

theorem IsFrame.polar_eq {e' f' : Fin m → V} {a' b' : V} (hF : IsFrame Q c₀ τ e f a b)
    (hF' : IsFrame Q c₀ τ e' f' a' b') (x y : FrIdx m) :
    polar Q (fvec e' f' a' b' x) (fvec e' f' a' b' y) = polar Q (fvec e f a b x) (fvec e f a b y) :=
  by rw [hF.polar_fvec, hF'.polar_fvec]

theorem IsFrame.span_eq (hF : IsFrame Q c₀ τ e f a b) {U : Submodule K V}
    [FiniteDimensional K U] (hU : ∀ x, fvec e f a b x ∈ U) (hdim : finrank K U = 2 * m + 2) :
    Submodule.span K (Set.range (fvec e f a b)) = U := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact hU x
  · rw [finrank_span_eq_card hF.linearIndependent, hdim]
    simp only [FrIdx, Fintype.card_sum, Fintype.card_fin]
    ring

end Frame

section Plane

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

open SUTB

theorem linearIndependent_pair_of_polar {a b : V} (hab : polar Q a b = 1) :
    LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => polar Q v b) hst
  have h2 := congrArg (fun v => polar Q a v) hst
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
    polar_self_charTwo, hab, polar_zero_left, polar_zero_right] at h1 h2
  constructor
  · simpa using h1
  · simpa using h2

theorem finrank_span_pair {a b : V} (hab : polar Q a b = 1) :
    finrank K (Submodule.span K {a, b}) = 2 := by
  have h := finrank_span_eq_card (linearIndependent_pair_of_polar hab)
  rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
  exact h

omit [CharP K 2] in
theorem exists_polar_eq_one {U : Submodule K V} (hU : NondegOn (polarBilin Q) U) {v : V}
    (hv : v ∈ U) (hv0 : v ≠ 0) : ∃ w ∈ U, polar Q v w = 1 := by
  obtain ⟨n, hn, hnv⟩ : ∃ n ∈ U, polar Q n v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (hU v hv fun n hn => by rw [polarBilin_apply_apply]; exact h n hn)
  refine ⟨(polar Q n v)⁻¹ • n, U.smul_mem _ hn, ?_⟩
  rw [polar_smul_right, smul_eq_mul, polar_comm Q v n, inv_mul_cancel₀ hnv]

theorem exists_hyp_partner {U : Submodule K V} (hU : NondegOn (polarBilin Q) U) {v : V}
    (hv : v ∈ U) (hv0 : v ≠ 0) (hQv : Q v = 0) : ∃ w ∈ U, Q w = 0 ∧ polar Q v w = 1 := by
  obtain ⟨w, hw, hvw⟩ := exists_polar_eq_one hU hv hv0
  refine ⟨w + Q w • v, U.add_mem hw (U.smul_mem _ hv), ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQv, polar_smul_right, polar_comm, hvw]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
    exact CharTwo.add_self_eq_zero _
  · rw [polar_add_right, polar_smul_right, polar_self_charTwo, hvw, smul_zero, add_zero]

@[expose] def perp2 (Q : QuadraticForm K V) (v w : V) : Submodule K V :=
  LinearMap.ker (polarBilin Q v) ⊓ LinearMap.ker (polarBilin Q w)

omit [CharP K 2] in
theorem mem_perp2 {v w x : V} : x ∈ perp2 Q v w ↔ polar Q v x = 0 ∧ polar Q w x = 0 := by
  simp [perp2, LinearMap.mem_ker, polarBilin_apply_apply]

theorem split_plane [FiniteDimensional K V] {U : Submodule K V} (hU : NondegOn (polarBilin Q) U)
    {v w : V} (hv : v ∈ U) (hw : w ∈ U) (hvw : polar Q v w = 1) :
    U ⊓ perp2 Q v w ⊔ Submodule.span K {v, w} = U ∧
      U ⊓ perp2 Q v w ⊓ Submodule.span K {v, w} = ⊥ ∧
      (∀ x ∈ U ⊓ perp2 Q v w, ∀ y ∈ Submodule.span K {v, w}, polar Q x y = 0) ∧
      NondegOn (polarBilin Q) (U ⊓ perp2 Q v w) ∧
      finrank K ↥(U ⊓ perp2 Q v w) + 2 = finrank K U := by
  have hwv : polar Q w v = 1 := by rw [polar_comm]; exact hvw
  have horth : ∀ x ∈ U ⊓ perp2 Q v w, ∀ y ∈ Submodule.span K {v, w}, polar Q x y = 0 := by
    intro x hx y hy
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
    obtain ⟨h1, h2⟩ := mem_perp2.mp hx.2
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm, h1, polar_comm, h2]
    simp
  have hsplit : ∀ x ∈ U, x - (polar Q x w • v + polar Q x v • w) ∈ U ⊓ perp2 Q v w := by
    intro x hx
    refine ⟨U.sub_mem hx (U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hw)), mem_perp2.mpr ⟨?_, ?_⟩⟩
    · rw [polar_sub_right, polar_add_right, polar_smul_right, polar_smul_right,
        polar_self_charTwo, hvw, polar_comm Q v x]
      simp
    · rw [polar_sub_right, polar_add_right, polar_smul_right, polar_smul_right,
        polar_self_charTwo, hwv, polar_comm Q w x]
      simp
  have hsup : U ⊓ perp2 Q v w ⊔ Submodule.span K {v, w} = U := by
    refine le_antisymm (sup_le inf_le_left (Submodule.span_le.mpr ?_)) fun x hx => ?_
    · rintro _ (rfl | rfl)
      · exact hv
      · exact hw
    · have h1 : x = (x - (polar Q x w • v + polar Q x v • w)) +
          (polar Q x w • v + polar Q x v • w) := by abel
      rw [h1]
      exact Submodule.add_mem_sup (hsplit x hx)
        (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩)
  have hinf : U ⊓ perp2 Q v w ⊓ Submodule.span K {v, w} = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx.2
    obtain ⟨h1, h2⟩ := mem_perp2.mp hx.1.2
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_charTwo, hvw] at h1
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_charTwo, hwv] at h2
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  refine ⟨hsup, hinf, horth, ?_, ?_⟩
  · intro x hx hxo
    refine hU x hx.1 fun n hn => ?_
    have h1 : n = (n - (polar Q n w • v + polar Q n v • w)) +
        (polar Q n w • v + polar Q n v • w) := by abel
    rw [h1, map_add, LinearMap.add_apply, hxo _ (hsplit n hn), zero_add, polarBilin_apply_apply,
      polar_comm]
    exact horth x hx _ (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩)
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ perp2 Q v w)
      (Submodule.span K {v, w})
    rw [hsup, hinf, finrank_bot, add_zero, finrank_span_pair hvw] at h1
    exact h1.symm

theorem IsFrame.cons {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin m → V} {a b : V}
    (hF : IsFrame Q c₀ τ e f a b) {v w : V} (hQv : Q v = 0) (hQw : Q w = 0)
    (hvw : polar Q v w = 1) (hvo : ∀ x, polar Q v (fvec e f a b x) = 0)
    (hwo : ∀ x, polar Q w (fvec e f a b x) = 0) :
    IsFrame Q c₀ τ (Fin.cons v e) (Fin.cons w f) a b := by
  have hve : ∀ i, polar Q v (e i) = 0 := fun i => hvo (.inl i)
  have hvf : ∀ i, polar Q v (f i) = 0 := fun i => hvo (.inr (.inl i))
  have hwe : ∀ i, polar Q w (e i) = 0 := fun i => hwo (.inl i)
  have hwf : ∀ i, polar Q w (f i) = 0 := fun i => hwo (.inr (.inl i))
  have hev : ∀ i, polar Q (e i) v = 0 := fun i => by rw [polar_comm]; exact hve i
  have hfv : ∀ i, polar Q (f i) v = 0 := fun i => by rw [polar_comm]; exact hvf i
  have hew : ∀ i, polar Q (e i) w = 0 := fun i => by rw [polar_comm]; exact hwe i
  have hfw : ∀ i, polar Q (f i) w = 0 := fun i => by rw [polar_comm]; exact hwf i
  have hva : polar Q v a = 0 := hvo (.inr (.inr 0))
  have hvb : polar Q v b = 0 := hvo (.inr (.inr 1))
  have hwa : polar Q w a = 0 := hwo (.inr (.inr 0))
  have hwb : polar Q w b = 0 := hwo (.inr (.inr 1))
  have hwv : polar Q w v = 1 := by rw [polar_comm]; exact hvw
  refine ⟨⟨fun k => ?_, fun k => ?_, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩, fun k => ?_,
    fun k => ?_, fun k => ?_, fun k => ?_, hF.pab, hF.qa, hF.qb⟩
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hQv
    · simpa using hF.hyp.map_e i
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hQw
    · simpa using hF.hyp.map_f i
  · refine Fin.cases ?_ (fun i => ?_) k <;> refine Fin.cases ?_ (fun j => ?_) l
    · simp [CharTwo.two_eq_zero]
    · simp [hve]
    · simp [hev]
    · simpa using hF.hyp.polar_ee i j
  · refine Fin.cases ?_ (fun i => ?_) k <;> refine Fin.cases ?_ (fun j => ?_) l
    · simp [CharTwo.two_eq_zero]
    · simp [hwf]
    · simp [hfw]
    · simpa using hF.hyp.polar_ff i j
  · refine Fin.cases ?_ (fun i => ?_) k <;> refine Fin.cases ?_ (fun j => ?_) l
    · simp [hvw]
    · simp [hvf, (Fin.succ_ne_zero j).symm]
    · simp [hew, Fin.succ_ne_zero i]
    · simpa [Fin.succ_inj] using hF.hyp.polar_ef i j
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hva
    · simpa using hF.pea i
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hvb
    · simpa using hF.peb i
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hwa
    · simpa using hF.pfa i
  · refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hwb
    · simpa using hF.pfb i

end Plane

section Exists

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open SUTB

variable (K) in
@[expose] noncomputable def tailSum (τ : Bool) : ℤ :=
  if τ then -(Nat.card K : ℤ) else Nat.card K

theorem exists_frame_plane [Finite V] {c₀ : K} (hc₀ : c₀ ∉ (wp K).range) {U : Submodule K V}
    (hU : NondegOn (polarBilin Q) U) (hdim : finrank K U = 2) :
    ∃ (τ : Bool) (a b : V), a ∈ U ∧ b ∈ U ∧
      IsFrame Q c₀ τ (Fin.elim0 : Fin 0 → V) Fin.elim0 a b ∧ charSum Q U = tailSum K τ := by
  have hU0 : U ≠ ⊥ := fun h => by rw [h, finrank_bot] at hdim; omega
  have hspan : ∀ {a b : V}, a ∈ U → b ∈ U → polar Q a b = 1 → Submodule.span K {a, b} = U :=
    fun ha hb hab => Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      exacts [ha, hb])) (by rw [finrank_span_pair hab, hdim])
  have hfr0 : ∀ {a b : V} (τ : Bool), polar Q a b = 1 → (Q a = if τ then 1 else 0) →
      (Q b = if τ then c₀ else 0) → IsFrame Q c₀ τ (Fin.elim0 : Fin 0 → V) Fin.elim0 a b :=
    fun _ hab ha hb => ⟨⟨finZeroElim, finZeroElim, finZeroElim, finZeroElim, finZeroElim⟩,
      finZeroElim, finZeroElim, finZeroElim, finZeroElim, hab, ha, hb⟩
  by_cases hiso : ∃ v ∈ U, v ≠ 0 ∧ Q v = 0
  · obtain ⟨v, hv, hv0, hQv⟩ := hiso
    obtain ⟨w, hw, hQw, hvw⟩ := exists_hyp_partner hU hv hv0 hQv
    refine ⟨false, v, w, hv, hw, hfr0 false hvw (by simp [hQv]) (by simp [hQw]), ?_⟩
    rw [← hspan hv hw hvw, charSum_hyp (linearIndependent_pair_of_polar hvw) hQv hQw hvw]
    simp [tailSum]
  · push Not at hiso
    obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hQa₀ : Q a₀ ≠ 0 := hiso a₀ ha₀ ha₀0
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q a₀)⁻¹
    set a := s • a₀ with ha_def
    have ha : a ∈ U := U.smul_mem _ ha₀
    have hQa : Q a = 1 := by
      rw [ha_def, QuadraticMap.map_smul, smul_eq_mul, ← hs, inv_mul_cancel₀ hQa₀]
    have ha0 : a ≠ 0 := fun h => by
      rw [h, QuadraticMap.map_zero] at hQa
      exact zero_ne_one hQa
    obtain ⟨b₁, hb₁, hab₁⟩ := exists_polar_eq_one hU ha ha0
    have hc : Q b₁ ∉ (wp K).range := by
      rintro ⟨t, ht⟩
      rw [wp_apply] at ht
      have h1 : Q (t • a + b₁) = 0 := by
        rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQa, polar_smul_left, hab₁]
        simp only [smul_eq_mul, mul_one]
        linear_combination ht + Q b₁ * (CharTwo.two_eq_zero : (2 : K) = 0)
      have h2 : t • a + b₁ ≠ 0 := by
        intro h0
        have h3 := (LinearIndependent.pair_iff.mp (linearIndependent_pair_of_polar hab₁)) t 1
          (by rw [one_smul]; exact h0)
        exact one_ne_zero h3.2
      exact hiso _ (U.add_mem (U.smul_mem _ ha) hb₁) h2 h1
    have hcc : Q b₁ + c₀ ∈ (wp K).range :=
      (AddSubgroup.add_mem_iff_of_index_two index_range_wp).mpr (iff_of_false hc hc₀)
    obtain ⟨t, ht⟩ := hcc
    rw [wp_apply] at ht
    set b := b₁ + t • a with hb_def
    have hb : b ∈ U := U.add_mem hb₁ (U.smul_mem _ ha)
    have hab : polar Q a b = 1 := by
      rw [hb_def, polar_add_right, polar_smul_right, polar_self_charTwo, hab₁, smul_zero, add_zero]
    have hQb : Q b = c₀ := by
      rw [hb_def, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQa, polar_smul_right, polar_comm,
        hab₁]
      simp only [smul_eq_mul, mul_one]
      linear_combination ht + Q b₁ * (CharTwo.two_eq_zero : (2 : K) = 0)
    refine ⟨true, a, b, ha, hb, hfr0 true hab (by simp [hQa]) (by simp [hQb]), ?_⟩
    rw [← hspan ha hb hab, charSum_aniso (linearIndependent_pair_of_polar hab) hQa hQb hc₀ hab]
    simp [tailSum]

theorem exists_frame [Finite V] {c₀ : K} (hc₀ : c₀ ∉ (wp K).range) :
    ∀ (m : ℕ) (U : Submodule K V), NondegOn (polarBilin Q) U → finrank K U = 2 * m + 2 →
      ∃ (τ : Bool) (e f : Fin m → V) (a b : V), (∀ x, fvec e f a b x ∈ U) ∧
        IsFrame Q c₀ τ e f a b ∧ charSum Q U = (Nat.card K : ℤ) ^ m * tailSum K τ := by
  intro m
  induction m with
  | zero =>
    intro U hU hdim
    obtain ⟨τ, a, b, ha, hb, hF, hS⟩ := exists_frame_plane hc₀ hU (by simpa using hdim)
    refine ⟨τ, Fin.elim0, Fin.elim0, a, b, ?_, hF, by rw [hS, pow_zero, one_mul]⟩
    rintro (i | i | j)
    · exact i.elim0
    · exact i.elim0
    · fin_cases j
      exacts [ha, hb]
  | succ m ih =>
    intro U hU hdim
    obtain ⟨v, hv, hv0, hQv⟩ :=
      CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_charTwo (Q := Q)
        (CharTwo.two_eq_zero : (2 : K) = 0) (S := U) (by omega)
    obtain ⟨w, hw, hQw, hvw⟩ := exists_hyp_partner hU hv hv0 hQv
    obtain ⟨hsup, hinf, horth, hnd', hdim'⟩ := split_plane hU hv hw hvw
    obtain ⟨τ, e, f, a, b, hmem, hF, hS⟩ := ih _ hnd' (by omega)
    have hvo : ∀ x, polar Q v (fvec e f a b x) = 0 := fun x => (mem_perp2.mp (hmem x).2).1
    have hwo : ∀ x, polar Q w (fvec e f a b x) = 0 := fun x => (mem_perp2.mp (hmem x).2).2
    refine ⟨τ, Fin.cons v e, Fin.cons w f, a, b, ?_, hF.cons hQv hQw hvw hvo hwo, ?_⟩
    · rintro (i | i | j)
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hv
        · simpa using (hmem (.inl i)).1
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hw
        · simpa using (hmem (.inr (.inl i))).1
      · exact (hmem (.inr (.inr j))).1
    · rw [← hsup, charSum_sup hinf horth, hS,
        charSum_hyp (linearIndependent_pair_of_polar hvw) hQv hQw hvw]
      ring

omit [FiniteDimensional K V] in
theorem tau_eq_of_modEq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {τ τ' : Bool}
    (h : (Nat.card K : ℤ) ^ m * tailSum K τ ≡ 1 [ZMOD p])
    (h' : (Nat.card K : ℤ) ^ m * tailSum K τ' ≡ 1 [ZMOD p]) : τ = τ' := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hkey : ¬ (p : ℤ) ∣ 2 * (Nat.card K : ℤ) ^ (m + 1) := by
    intro hd
    have h1 : 2 * (Nat.card K : ℤ) ^ (m + 1) = ((2 ^ (1 + (n : ℕ) * (m + 1)) : ℕ) : ℤ) := by
      rw [hq]
      push_cast
      ring
    rw [h1, Int.natCast_dvd_natCast] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hd : (p : ℤ) ∣ (Nat.card K : ℤ) ^ m * tailSum K τ -
      (Nat.card K : ℤ) ^ m * tailSum K τ' := by
    have h1 := dvd_sub h'.dvd h.dvd
    have e : (1 - (Nat.card K : ℤ) ^ m * tailSum K τ') - (1 - (Nat.card K : ℤ) ^ m * tailSum K τ) =
        (Nat.card K : ℤ) ^ m * tailSum K τ - (Nat.card K : ℤ) ^ m * tailSum K τ' := by ring
    rwa [e] at h1
  cases τ <;> cases τ'
  · rfl
  · exfalso
    apply hkey
    have e : (Nat.card K : ℤ) ^ m * tailSum K false - (Nat.card K : ℤ) ^ m * tailSum K true =
        2 * (Nat.card K : ℤ) ^ (m + 1) := by
      simp only [tailSum, Bool.false_eq_true, ite_false, ite_true]
      ring
    rwa [e] at hd
  · exfalso
    apply hkey
    have e : (Nat.card K : ℤ) ^ m * tailSum K true - (Nat.card K : ℤ) ^ m * tailSum K false =
        -(2 * (Nat.card K : ℤ) ^ (m + 1)) := by
      simp only [tailSum, Bool.false_eq_true, ite_false, ite_true]
      ring
    rwa [e, dvd_neg] at hd
  · rfl

theorem exists_frame_of_modEq [Finite V] {c₀ : K} (hc₀ : c₀ ∉ (wp K).range) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {τ₀ : Bool}
    (hτ₀ : (Nat.card K : ℤ) ^ m * tailSum K τ₀ ≡ 1 [ZMOD p]) {U : Submodule K V}
    (hU : NondegOn (polarBilin Q) U) (hdim : finrank K U = 2 * m + 2)
    (hS : charSum Q U ≡ 1 [ZMOD p]) :
    ∃ (e f : Fin m → V) (a b : V), (∀ x, fvec e f a b x ∈ U) ∧ IsFrame Q c₀ τ₀ e f a b := by
  obtain ⟨τ, e, f, a, b, hmem, hF, hSU⟩ := exists_frame hc₀ m U hU hdim
  rw [hSU] at hS
  obtain rfl := tau_eq_of_modEq hp hp2 hS hτ₀
  exact ⟨e, f, a, b, hmem, hF⟩

omit [Finite K] in
theorem exists_orth_frames (hnd : (polarBilin Q).Nondegenerate) {k m : ℕ} {c₀ : K} {τ : Bool}
    {e f e' f' : Fin k → Fin m → V} {a b a' b' : Fin k → V}
    (hF : ∀ j, IsFrame Q c₀ τ (e j) (f j) (a j) (b j))
    (hF' : ∀ j, IsFrame Q c₀ τ (e' j) (f' j) (a' j) (b' j))
    (ho : ∀ j j', j ≠ j' → ∀ x y,
      polar Q (fvec (e j) (f j) (a j) (b j) x) (fvec (e j') (f j') (a j') (b j') y) = 0)
    (ho' : ∀ j j', j ≠ j' → ∀ x y,
      polar Q (fvec (e' j) (f' j) (a' j) (b' j) x) (fvec (e' j') (f' j') (a' j') (b' j') y) = 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ j x,
      g (fvec (e j) (f j) (a j) (b j) x) = fvec (e' j) (f' j) (a' j) (b' j) x := by
  classical
  set u : Fin k × FrIdx m → V := fun z => fvec (e z.1) (f z.1) (a z.1) (b z.1) z.2 with hu
  set u' : Fin k × FrIdx m → V := fun z => fvec (e' z.1) (f' z.1) (a' z.1) (b' z.1) z.2 with hu'
  have hpol : ∀ z z', polar Q (u z) (u z') =
      if z.1 = z'.1 then (if z'.2 = frSw z.2 then 1 else 0) else 0 := by
    rintro ⟨j, x⟩ ⟨j', y⟩
    by_cases hj : j = j'
    · subst hj
      simp only [hu, ite_true]
      exact (hF j).polar_fvec x y
    · simp only [hu, hj, ite_false]
      exact ho j j' hj x y
  have hpol' : ∀ z z', polar Q (u' z) (u' z') =
      if z.1 = z'.1 then (if z'.2 = frSw z.2 then 1 else 0) else 0 := by
    rintro ⟨j, x⟩ ⟨j', y⟩
    by_cases hj : j = j'
    · subst hj
      simp only [hu', ite_true]
      exact (hF' j).polar_fvec x y
    · simp only [hu', hj, ite_false]
      exact ho' j j' hj x y
  have hli : ∀ w : Fin k × FrIdx m → V, (∀ z z', polar Q (w z) (w z') =
      if z.1 = z'.1 then (if z'.2 = frSw z.2 then 1 else 0) else 0) → LinearIndependent K w := by
    intro w hw
    refine TableBOrth.linearIndependent_of_polar_dual (QF := Q)
      (d := fun z => w (z.1, frSw z.2)) fun z z' => ?_
    rw [hw]
    rcases z with ⟨j, x⟩
    rcases z' with ⟨j', y⟩
    by_cases hj : j = j'
    · subst hj
      by_cases hxy : x = y
      · subst hxy
        simp
      · simp [hxy, show ¬ frSw y = frSw x from fun h' => hxy (frSw_injective h').symm]
    · simp [hj]
  obtain ⟨g, hg, hgu⟩ := TableBOrth.exists_orth_apply_eq hnd u u' (hli u hpol) (hli u' hpol')
    (fun z => by rw [hu, hu', (hF' z.1).quad_fvec, (hF z.1).quad_fvec])
    (fun z z' => by rw [hpol, hpol'])
  exact ⟨g, hg, fun j x => hgu (j, x)⟩

end Exists

end OrdPNsOm

end CFSG.StandardType
