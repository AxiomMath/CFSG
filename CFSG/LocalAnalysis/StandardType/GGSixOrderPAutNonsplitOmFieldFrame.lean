module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmRank

public section

namespace CFSG.StandardType

namespace OrdPFieldNsOm

open QuadraticMap Module OrdPNsOm SUTB NoOffOm

section Map

variable {K K₀ : Type} [Field K] [Field K₀] {V V₀ : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup V₀] [Module K₀ V₀] {Q : QuadraticForm K V} {Q₀ : QuadraticForm K₀ V₀}

theorem polar_map (ι : K₀ →+* K) (κ : V₀ →+ V) (hκ : ∀ v, Q (κ v) = ι (Q₀ v)) (u v : V₀) :
    polar Q (κ u) (κ v) = ι (polar Q₀ u v) := by
  change Q (κ u + κ v) - Q (κ u) - Q (κ v) = ι (Q₀ (u + v) - Q₀ u - Q₀ v)
  rw [← map_add κ, hκ, hκ, hκ, map_sub, map_sub]

theorem fvec_map (κ : V₀ →+ V) {m : ℕ} (e f : Fin m → V₀) (a b : V₀) (x : FrIdx m) :
    fvec (κ ∘ e) (κ ∘ f) (κ a) (κ b) x = κ (fvec e f a b x) := by
  rcases x with i | i | j
  · rfl
  · rfl
  · fin_cases j <;> rfl

theorem isFrame_map (ι : K₀ →+* K) (κ : V₀ →+ V) (hκ : ∀ v, Q (κ v) = ι (Q₀ v)) {c₀ : K₀}
    {τ : Bool} {m : ℕ} {e f : Fin m → V₀} {a b : V₀} (hF : IsFrame Q₀ c₀ τ e f a b) :
    IsFrame Q (ι c₀) τ (κ ∘ e) (κ ∘ f) (κ a) (κ b) where
  hyp :=
    { map_e := fun k => by simp [hκ, hF.hyp.map_e k]
      map_f := fun k => by simp [hκ, hF.hyp.map_f k]
      polar_ee := fun i j => by simp [polar_map ι κ hκ, hF.hyp.polar_ee i j]
      polar_ff := fun i j => by simp [polar_map ι κ hκ, hF.hyp.polar_ff i j]
      polar_ef := fun i j => by
        simp only [Function.comp_apply, polar_map ι κ hκ, hF.hyp.polar_ef i j]
        split_ifs <;> simp }
  pea i := by simp [polar_map ι κ hκ, hF.pea i]
  peb i := by simp [polar_map ι κ hκ, hF.peb i]
  pfa i := by simp [polar_map ι κ hκ, hF.pfa i]
  pfb i := by simp [polar_map ι κ hκ, hF.pfb i]
  pab := by simp [polar_map ι κ hκ, hF.pab]
  qa := by rw [hκ, hF.qa]; split_ifs <;> simp
  qb := by rw [hκ, hF.qb]; split_ifs <;> simp

end Map

section Reindex

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isHypFamily_comp {k m : ℕ} {e f : Fin m → V} (h : TableBOrth.IsHypFamily Q e f)
    (φ : Fin k → Fin m) (hφ : Function.Injective φ) :
    TableBOrth.IsHypFamily Q (e ∘ φ) (f ∘ φ) where
  map_e i := h.map_e (φ i)
  map_f i := h.map_f (φ i)
  polar_ee i j := h.polar_ee (φ i) (φ j)
  polar_ff i j := h.polar_ff (φ i) (φ j)
  polar_ef i j := by
    simp only [Function.comp_apply, h.polar_ef (φ i) (φ j), hφ.eq_iff]

theorem isFrame_comp {c₀ : K} {τ : Bool} {k m : ℕ} {e f : Fin m → V} {a b : V}
    (hF : IsFrame Q c₀ τ e f a b) (φ : Fin k → Fin m) (hφ : Function.Injective φ) :
    IsFrame Q c₀ τ (e ∘ φ) (f ∘ φ) a b where
  hyp := isHypFamily_comp hF.hyp φ hφ
  pea i := hF.pea (φ i)
  peb i := hF.peb (φ i)
  pfa i := hF.pfa (φ i)
  pfb i := hF.pfb (φ i)
  pab := hF.pab
  qa := hF.qa
  qb := hF.qb

theorem isFrame_castLE {c₀ : K} {τ : Bool} {k m : ℕ} {e f : Fin m → V} {a b : V}
    (hF : IsFrame Q c₀ τ e f a b) (h : k ≤ m) :
    IsFrame Q c₀ τ (e ∘ Fin.castLE h) (f ∘ Fin.castLE h) a b :=
  isFrame_comp hF _ (Fin.castLE_injective h)

theorem fvec_comp_mem {k m : ℕ} {e f : Fin m → V} {a b : V} (φ : Fin k → Fin m)
    {U : Submodule K V} (hU : ∀ x, fvec e f a b x ∈ U) (x : FrIdx k) :
    fvec (e ∘ φ) (f ∘ φ) a b x ∈ U := by
  rcases x with i | i | j
  · exact hU (.inl (φ i))
  · exact hU (.inr (.inl (φ i)))
  · exact hU (.inr (.inr j))

end Reindex

section CharSumFrame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_mem_span {S T : Set V} (h : ∀ a ∈ S, ∀ b ∈ T, polar Q a b = 0) {a b : V}
    (ha : a ∈ Submodule.span K S) (hb : b ∈ Submodule.span K T) : polar Q a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => exact polar_zero_right _ _
    | add b b' _ _ h1 h2 => rw [polar_add_right, h1, h2, add_zero]
    | smul c b _ h1 => rw [polar_smul_right, h1, smul_zero]
  | zero => exact polar_zero_left _ _
  | add a a' _ _ h1 h2 => rw [polar_add_left, h1, h2, add_zero]
  | smul c a _ h1 => rw [polar_smul_left, h1, smul_zero]

theorem isFrame_tail {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin (m + 1) → V} {a b : V}
    (hF : IsFrame Q c₀ τ e f a b) : IsFrame Q c₀ τ (Fin.tail e) (Fin.tail f) a b :=
  isFrame_comp hF Fin.succ (Fin.succ_injective m)

theorem span_range_fvec_succ {m : ℕ} (e f : Fin (m + 1) → V) (a b : V) :
    Submodule.span K (Set.range (fvec e f a b)) = Submodule.span K {e 0, f 0} ⊔
      Submodule.span K (Set.range (fvec (Fin.tail e) (Fin.tail f) a b)) := by
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rcases x with i | i | j
    · cases i using Fin.cases with
      | zero => exact Or.inl (Or.inl rfl)
      | succ i => exact Or.inr ⟨.inl i, rfl⟩
    · cases i using Fin.cases with
      | zero => exact Or.inl (Or.inr rfl)
      | succ i => exact Or.inr ⟨.inr (.inl i), rfl⟩
    · exact Or.inr ⟨.inr (.inr j), by fin_cases j <;> rfl⟩
  · rintro ((rfl | rfl) | ⟨x, rfl⟩)
    · exact ⟨.inl 0, rfl⟩
    · exact ⟨.inr (.inl 0), rfl⟩
    · rcases x with i | i | j
      · exact ⟨.inl i.succ, rfl⟩
      · exact ⟨.inr (.inl i.succ), rfl⟩
      · exact ⟨.inr (.inr j), by fin_cases j <;> rfl⟩

variable [CharP K 2] [Finite K] [Finite V]

theorem charSum_span_frame {c₀ : K} (hc₀ : c₀ ∉ (wp K).range) {τ : Bool} :
    ∀ {m : ℕ} {e f : Fin m → V} {a b : V}, IsFrame Q c₀ τ e f a b →
      charSum Q (Submodule.span K (Set.range (fvec e f a b))) =
        (Nat.card K : ℤ) ^ m * tailSum K τ := by
  intro m
  induction m with
  | zero =>
    intro e f a b hF
    have hr : Set.range (fvec e f a b) = {a, b} := by
      ext v
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        rcases x with i | i | j
        · exact i.elim0
        · exact i.elim0
        · fin_cases j
          · exact Or.inl rfl
          · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨.inr (.inr 0), rfl⟩
        · exact ⟨.inr (.inr 1), rfl⟩
    rw [hr, pow_zero, one_mul]
    cases τ
    · rw [charSum_hyp (linearIndependent_pair_of_polar hF.pab) (by simpa using hF.qa)
        (by simpa using hF.qb) hF.pab]
      simp [tailSum]
    · rw [charSum_aniso (linearIndependent_pair_of_polar hF.pab) (by simpa using hF.qa)
        (by simpa using hF.qb) hc₀ hF.pab]
      simp [tailSum]
  | succ m ih =>
    intro e f a b hF
    have hef : polar Q (e 0) (f 0) = 1 := by simpa using hF.hyp.polar_ef 0 0
    have hfe : polar Q (f 0) (e 0) = 1 := by rw [polar_comm]; exact hef
    have h0 : ∀ x, polar Q (e 0) (fvec (Fin.tail e) (Fin.tail f) a b x) = 0 := by
      rintro (i | i | j)
      · exact hF.hyp.polar_ee 0 i.succ
      · change polar Q (e 0) (f i.succ) = 0
        rw [hF.hyp.polar_ef]
        simp [(Fin.succ_ne_zero i).symm]
      · fin_cases j
        · exact hF.pea 0
        · exact hF.peb 0
    have h1 : ∀ x, polar Q (f 0) (fvec (Fin.tail e) (Fin.tail f) a b x) = 0 := by
      rintro (i | i | j)
      · change polar Q (f 0) (e i.succ) = 0
        rw [polar_comm, hF.hyp.polar_ef]
        simp [Fin.succ_ne_zero i]
      · exact hF.hyp.polar_ff 0 i.succ
      · fin_cases j
        · exact hF.pfa 0
        · exact hF.pfb 0
    have horth : ∀ u ∈ Submodule.span K {e 0, f 0},
        ∀ v ∈ Submodule.span K (Set.range (fvec (Fin.tail e) (Fin.tail f) a b)),
          polar Q u v = 0 := fun u hu v hv =>
      polar_eq_zero_of_mem_span (by
        rintro _ (rfl | rfl) _ ⟨x, rfl⟩
        exacts [h0 x, h1 x]) hu hv
    have hinf : Submodule.span K {e 0, f 0} ⊓
        Submodule.span K (Set.range (fvec (Fin.tail e) (Fin.tail f) a b)) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hx.1
      have he0 : e 0 ∈ Submodule.span K {e 0, f 0} := Submodule.subset_span (by simp)
      have hf0 : f 0 ∈ Submodule.span K {e 0, f 0} := Submodule.subset_span (by simp)
      have k1 : polar Q x (f 0) = 0 := by rw [polar_comm]; exact horth _ hf0 _ hx.2
      have k2 : polar Q x (e 0) = 0 := by rw [polar_comm]; exact horth _ he0 _ hx.2
      rw [← hst] at k1 k2
      simp only [polar_add_left, polar_smul_left, smul_eq_mul, hef, polar_self_charTwo,
        mul_zero, mul_one, add_zero] at k1
      simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_self_charTwo, hfe, mul_zero,
        mul_one, zero_add] at k2
      rw [← hst, k1, k2, zero_smul, zero_smul, add_zero]
    rw [span_range_fvec_succ, charSum_sup hinf horth,
      charSum_hyp (linearIndependent_pair_of_polar hef) (hF.hyp.map_e 0) (hF.hyp.map_f 0) hef,
      ih (isFrame_tail hF)]
    ring

end CharSumFrame

section Adjust

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem exists_frame_castSucc {c₀ : K} {τ' : Bool} {m : ℕ} {e f : Fin (m + 1) → V} {a b : V}
    (hF : IsFrame Q c₀ τ' e f a b) (τ : Bool) {U : Submodule K V}
    (hU : ∀ x, fvec e f a b x ∈ U) :
    ∃ a' b' : V, a' ∈ U ∧ b' ∈ U ∧
      IsFrame Q c₀ τ (e ∘ Fin.castSucc) (f ∘ Fin.castSucc) a' b' := by
  have hhyp := isHypFamily_comp hF.hyp _ (Fin.castSucc_injective m)
  set l := Fin.last m with hl
  have hel : e l ∈ U := hU (.inl l)
  have hfl : f l ∈ U := hU (.inr (.inl l))
  have ha : a ∈ U := hU (.inr (.inr 0))
  have hb : b ∈ U := hU (.inr (.inr 1))
  have hne : ∀ i : Fin m, Fin.castSucc i ≠ l := fun i => (Fin.castSucc_lt_last i).ne
  have hee : ∀ i, polar Q (e (Fin.castSucc i)) (e l) = 0 := fun i => hF.hyp.polar_ee _ _
  have hef : ∀ i, polar Q (e (Fin.castSucc i)) (f l) = 0 := fun i => by
    rw [hF.hyp.polar_ef]
    simp [hne i]
  have hfe : ∀ i, polar Q (f (Fin.castSucc i)) (e l) = 0 := fun i => by
    rw [polar_comm, hF.hyp.polar_ef]
    simp [(hne i).symm]
  have hff : ∀ i, polar Q (f (Fin.castSucc i)) (f l) = 0 := fun i => hF.hyp.polar_ff _ _
  have hll : polar Q (e l) (f l) = 1 := by
    rw [hF.hyp.polar_ef]
    simp
  cases τ with
  | false =>
    refine ⟨e l, f l, hel, hfl, ⟨hhyp, hee, hef, hfe, hff, hll, ?_, ?_⟩⟩
    · simpa using hF.hyp.map_e l
    · simpa using hF.hyp.map_f l
  | true =>
    cases τ' with
    | true =>
      exact ⟨a, b, ha, hb, ⟨hhyp, fun i => hF.pea _, fun i => hF.peb _, fun i => hF.pfa _,
        fun i => hF.pfb _, hF.pab, hF.qa, hF.qb⟩⟩
    | false =>
      have hQa : Q a = 0 := by simpa using hF.qa
      have hQb : Q b = 0 := by simpa using hF.qb
      have hQe : Q (e l) = 0 := hF.hyp.map_e l
      have hQf : Q (f l) = 0 := hF.hyp.map_f l
      have hfl' : polar Q (f l) (e l) = 1 := by rw [polar_comm]; exact hll
      refine ⟨e l + f l, e l + a + c₀ • b, U.add_mem hel hfl,
        U.add_mem (U.add_mem hel ha) (U.smul_mem _ hb), ⟨hhyp, fun i => ?_, fun i => ?_,
          fun i => ?_, fun i => ?_, ?_, ?_, ?_⟩⟩
      · change polar Q (e (Fin.castSucc i)) (e l + f l) = 0
        rw [polar_add_right, hee, hef, add_zero]
      · change polar Q (e (Fin.castSucc i)) (e l + a + c₀ • b) = 0
        rw [polar_add_right, polar_add_right, polar_smul_right, hee, hF.pea, hF.peb]
        simp
      · change polar Q (f (Fin.castSucc i)) (e l + f l) = 0
        rw [polar_add_right, hfe, hff, add_zero]
      · change polar Q (f (Fin.castSucc i)) (e l + a + c₀ • b) = 0
        rw [polar_add_right, polar_add_right, polar_smul_right, hfe, hF.pfa, hF.pfb]
        simp
      · simp only [polar_add_left, polar_add_right, polar_smul_right, polar_self_charTwo, hfl',
          hF.pea l, hF.peb l, hF.pfa l, hF.pfb l, smul_eq_mul, mul_zero, add_zero, zero_add]
      · rw [QuadraticMap.map_add Q, hQe, hQf, hll]
        simp
      · rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQe, hQa, hQb,
          polar_add_left, polar_smul_right, polar_smul_right, hF.pea l, hF.peb l, hF.pab]
        simp

theorem exists_totallySingular_of_frame [FiniteDimensional K V] {c₀ : K} {τ : Bool} {m : ℕ}
    (hm : 3 ≤ m) {e f : Fin m → V} {a b : V} (hF : IsFrame Q c₀ τ e f a b) :
    ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  refine ⟨Submodule.span K (Set.range (e ∘ Fin.castLE hm)), ?_, ?_⟩
  · have hli : LinearIndependent K (e ∘ Fin.castLE hm) :=
      hF.linearIndependent.comp (fun i => (.inl (Fin.castLE hm i) : FrIdx m))
        (fun i j h => Fin.castLE_injective hm (Sum.inl_injective h))
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  · exact TableBOrth.eq_zero_on_span (by rintro _ ⟨i, rfl⟩; exact hF.hyp.map_e _)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hF.hyp.polar_ee _ _)

end Adjust

section Pieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem finrank_genPieceSpan (hA : GenMax B Γ p A) {S : Finset (GL (Fin d) K)}
    (hS : GenPieceSet B A S) {r : ℕ} (hr : ∀ y ∈ S, finrank K (grng y) = r) :
    finrank K (genPieceSpan S) = S.card * r := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert y S hyS ih =>
    have hS' := hS.mono (Finset.subset_insert y S)
    have h1 := ih hS' fun y' hy' => hr y' (Finset.mem_insert_of_mem hy')
    have hsp : genPieceSpan (insert y S) = genPieceSpan S ⊔ grng y := by
      rw [genPieceSpan, Finset.iSup_insert, sup_comm]
    have hX : NondegOn B (genPieceSpan S) := (hS'.nondegOn_card hA).1
    have horth := orth_genPieceSpan hA.symm hS hyS
    have hinf : genPieceSpan S ⊓ grng y = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hX v hv.1 fun m hm => ?_
      exact (horth v hv.2 m hm).2
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (genPieceSpan S) (grng y)
    rw [hinf, finrank_bot, add_zero] at hfr
    rw [hsp, hfr, h1, hr y (Finset.mem_insert_self y S), Finset.card_insert_of_notMem hyS]
    ring

omit [Finite K] [CharP K 2] in
theorem finrank_add_finrank_orth {X : Submodule K (Fin d → K)} (hX : NondegOn B X) :
    finrank K X + finrank K (X.orthogonalBilin B) = d := by
  rw [Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hX), Module.finrank_fin_fun]

omit [Finite K] [CharP K 2] in
theorem nondegenerate_of_genMax {Q : QuadraticForm K (Fin d → K)} (hA : GenMax (polB Q) Γ p A) :
    (QuadraticMap.polarBilin Q).Nondegenerate :=
  ⟨fun v hv => hA.sep v hv, fun w hw => hA.sep w fun v => by
    have h1 := hw v
    rw [polarBilin_apply_apply] at h1
    rw [polB_apply, polar_comm]
    exact h1⟩

end Pieces

end OrdPFieldNsOm

end CFSG.StandardType
