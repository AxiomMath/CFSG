module

public import CFSG.RankThree.PartOne.CTP.SeitzUPlane
public import CFSG.RankThree.PartOne.CTP.Spectrum4

public section

namespace CFSG.RankThree.PartOne.CTP

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne

section Hyperbolic

variable {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V]

theorem bar_eq_self_of_pow_eq_one (hpq : p ∣ ℓ ^ f - 1) {μ : K} (hμ : μ ^ p = 1) :
    h.bar μ = μ := by
  obtain ⟨k, hk⟩ := hpq
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq : ℓ ^ f = 1 + p * k := by omega
  rw [UnitaryFieldData.bar_apply, hq, pow_add, pow_one, pow_mul, hμ, one_pow, mul_one]

theorem eq_one_of_sq_eq_one_of_pow_eq_one (hp2 : p ≠ 2) (hp : p.Prime) {μ : K} (hμ : μ ^ p = 1)
    (hsq : μ ^ 2 = 1) : μ = 1 := by
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have h3 : μ ^ p = μ := by rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [← h3]
  exact hμ

variable [FiniteDimensional K V]

theorem exists_hyperbolic_pair_of_finrank_two [Finite K] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1)
    {ι : Type*} [Finite ι] (S : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (S i) (S j)) (hpow : ∀ i, S i ^ p = 1)
    (hiso : ∀ i v w, B (S i v) (S i w) = B v w)
    (W : Submodule K V) (hstab : ∀ i, ∀ w ∈ W, S i w ∈ W)
    (hW : (B.domRestrict₁₂ W W).SeparatingLeft) (hdim : Module.finrank K W = 2)
    (hfix : ∀ w ∈ W, (∀ i, S i w = w) → w = 0) :
    ∃ e ∈ W, ∃ f' ∈ W, B e e = 0 ∧ B f' f' = 0 ∧ B e f' = 1 ∧
      ∀ i, ∃ c : K, c ≠ 0 ∧ S i e = c • e ∧ S i f' = c⁻¹ • f' := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hdvd : p ∣ Nat.card K - 1 := by
    have h1 : Nat.card K - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvd
  have : NeZero p := ⟨hp.ne_zero⟩
  let Sw : ι → Module.End K W := fun i => (S i).restrict (hstab i)
  have hSw : ∀ i (w : W), ((Sw i w : W) : V) = S i (w : V) := fun i w => rfl
  have hSwpow : ∀ i (n : ℕ) (w : W), (((Sw i ^ n) w : W) : V) = (S i ^ n) (w : V) := by
    intro i n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hSw]
  have hcommw : ∀ i j, Commute (Sw i) (Sw j) := fun i j => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have := congrArg (fun T : Module.End K V => T (w : V)) (hcomm i j).eq
    simpa [hSw] using this
  have hpoww : ∀ i, Sw i ^ p = 1 := fun i => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hSwpow, hpow i]
    rfl
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ Sw hcommw hpoww
  let e' : Fin (finrank K W) ≃ Fin 2 := finCongr hdim
  let b' : Module.Basis (Fin 2) K W := b.reindex e'
  let u : Fin 2 → V := fun j => (b' j : V)
  let μ' : ι → Fin 2 → K := fun i j => μ i (e'.symm j)
  have hu : ∀ i j, S i (u j) = μ' i j • u j := by
    intro i j
    have := congrArg (fun w : W => (w : V)) (hb i (e'.symm j))
    simpa [u, μ', b', Module.Basis.reindex_apply, hSw] using this
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => b'.ne_zero j (Subtype.ext h0)
  have huW : ∀ j, u j ∈ W := fun j => (b' j).2
  have hμp : ∀ i j, μ' i j ^ p = 1 := by
    intro i j
    have h1 : (S i ^ p) (u j) = μ' i j ^ p • u j := by
      have := Module.End.HasEigenvector.pow_apply (f := S i) (μ := μ' i j) (v := u j)
        ⟨Module.End.mem_eigenspace_iff.mpr (hu i j), hu0 j⟩ p
      exact this
    rw [hpow i, Module.End.one_apply] at h1
    have h2 : (μ' i j ^ p - 1) • u j = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hu0 j))
  have hbar : ∀ i j, h.bar (μ' i j) = μ' i j := fun i j =>
    bar_eq_self_of_pow_eq_one h hpq (hμp i j)
  have hcross : ∀ i a c, (μ' i a * μ' i c - 1) * B (u a) (u c) = 0 := by
    intro i a c
    have h1 := hiso i (u a) (u c)
    rw [hu, hu] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hbar] at h1
    linear_combination h1
  have hspan : ∀ w ∈ W, ∃ a c : K, w = a • u 0 + c • u 1 := by
    intro w hw
    refine ⟨b'.repr ⟨w, hw⟩ 0, b'.repr ⟨w, hw⟩ 1, ?_⟩
    have h1 := b'.sum_repr ⟨w, hw⟩
    rw [Fin.sum_univ_two] at h1
    simpa [u] using (congrArg (fun x : W => (x : V)) h1).symm
  have hnd : ∀ a : Fin 2, (∀ w ∈ W, B (u a) w = 0) → False := by
    intro a ha
    have := hW ⟨u a, huW a⟩ (fun y => by
      rw [LinearMap.domRestrict₁₂_apply]
      exact ha y y.2)
    exact hu0 a (congrArg Subtype.val this)
  have hdiag : ∀ a : Fin 2, B (u a) (u a) = 0 := by
    intro a
    by_contra hne
    have h1 : ∀ i, μ' i a = 1 := by
      intro i
      refine eq_one_of_sq_eq_one_of_pow_eq_one hp2 hp (hμp i a) ?_
      have := hcross i a a
      rcases mul_eq_zero.mp this with h0 | h0
      · linear_combination h0
      · exact absurd h0 hne
    exact hu0 a (hfix _ (huW a) fun i => by rw [hu, h1 i, one_smul])
  have hoff : B (u 0) (u 1) ≠ 0 := by
    intro h0
    refine hnd 0 fun w hw => ?_
    obtain ⟨a, c, rfl⟩ := hspan w hw
    simp [map_add, map_smul, hdiag 0, h0]
  have hprod : ∀ i, μ' i 0 * μ' i 1 = 1 := by
    intro i
    have := hcross i 0 1
    rcases mul_eq_zero.mp this with h0 | h0
    · linear_combination h0
    · exact absurd h0 hoff
  have hne0 : ∀ i, μ' i 0 ≠ 0 := fun i h0 => by
    have := hprod i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨u 0, huW 0, (B (u 0) (u 1))⁻¹ • u 1, W.smul_mem _ (huW 1), hdiag 0, ?_, ?_, fun i => ?_⟩
  · simp [map_smulₛₗ, hdiag 1]
  · simp only [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hoff
  · refine ⟨μ' i 0, hne0 i, hu i 0, ?_⟩
    rw [map_smul, hu i 1, smul_comm, eq_inv_of_mul_eq_one_right (hprod i)]

end Hyperbolic

section Frame

open CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem ordNegQ_eq_two_of_dvd_sub_one (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f - 1) : ordNegQ ℓ f p = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h1 : (ℓ : ZMod p) ^ f = 1 := by
    have h0 : ((ℓ ^ f - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  unfold ordNegQ
  rw [h1, orderOf_neg_one, ZMod.ringChar_zmod_n]
  simp [hp2]

noncomputable abbrev stdB (h : UnitaryFieldData ℓ f K) (n : ℕ) :=
  gramForm h (1 : Matrix (Fin n) (Fin n) K)

abbrev mulSU (x : unitarySU ℓ f K n) (v : Fin n → K) : Fin n → K :=
  (((x : unitarySU ℓ f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v

theorem antidiag_mul_antidiag_self (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) K) * antidiag n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [antidiag, Matrix.one_apply, Fin.rev_rev, eq_comm]
  · intro k _ hk
    simp [antidiag, hk]
  · simp

theorem exists_frame_of_family [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (E : Subgroup (unitarySU ℓ f K n)) (v : Fin n → (Fin n → K))
    (hgram : ∀ i j, stdB h n (v i) (v j) = if j = Fin.rev i then 1 else 0)
    (heig : ∀ x ∈ E, ∃ d : Fin n → K, ∀ c, mulSU x (v c) = d c • v c) :
    ∃ P : GL (Fin n) K, conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K) = antidiag n ∧
      ∀ x ∈ E, (((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K).IsDiag := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  let Pm : Matrix (Fin n) (Fin n) K := Matrix.of fun r c => v c r
  have hσbar : ∀ c : K, σ c = h.bar c := fun c => by
    rw [hσdef, unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  have hPJ : conjTr σ Pm * Pm = antidiag n := by
    ext i j
    have h1 := hgram i j
    rw [gramForm_apply] at h1
    simp only [Matrix.one_mulVec, dotProduct] at h1
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      antidiag, hσbar]
    exact h1
  let Pinv : Matrix (Fin n) (Fin n) K := antidiag n * conjTr σ Pm
  have h1 : Pinv * Pm = 1 := by
    show antidiag n * conjTr σ Pm * Pm = 1
    rw [Matrix.mul_assoc, hPJ, antidiag_mul_antidiag_self]
  have h2 : Pm * Pinv = 1 := mul_eq_one_comm.mp h1
  let P : GL (Fin n) K := ⟨Pm, Pinv, h2, h1⟩
  refine ⟨P, hPJ, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := heig x hx
  have hxP : ((x : unitarySU ℓ f K n) : GL (Fin n) K).1 * Pm = Pm * Matrix.diagonal d := by
    ext r c
    rw [Matrix.mul_diagonal]
    have := congrFun (hd c) r
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pm] using this
  have hP' : ((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := by
    simp only [Units.val_mul]
    show Pinv * ((x : unitarySU ℓ f K n) : GL (Fin n) K).1 * Pm = _
    rw [Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hP']
  exact Matrix.isDiag_diagonal d

structure FrameData (h : UnitaryFieldData ℓ f K) (E : Subgroup (unitarySU ℓ f K n))
    (e₁ f₁ e₂ f₂ w : Fin n → K) : Prop where
  ee₁ : stdB h n e₁ e₁ = 0
  ff₁ : stdB h n f₁ f₁ = 0
  ef₁ : stdB h n e₁ f₁ = 1
  fe₁ : stdB h n f₁ e₁ = 1
  ee₂ : stdB h n e₂ e₂ = 0
  ff₂ : stdB h n f₂ f₂ = 0
  ef₂ : stdB h n e₂ f₂ = 1
  fe₂ : stdB h n f₂ e₂ = 1
  e₁e₂ : stdB h n e₁ e₂ = 0
  e₁f₂ : stdB h n e₁ f₂ = 0
  f₁e₂ : stdB h n f₁ e₂ = 0
  f₁f₂ : stdB h n f₁ f₂ = 0
  e₂e₁ : stdB h n e₂ e₁ = 0
  e₂f₁ : stdB h n e₂ f₁ = 0
  f₂e₁ : stdB h n f₂ e₁ = 0
  f₂f₁ : stdB h n f₂ f₁ = 0
  ww : n = 5 → stdB h n w w = 1
  we₁ : n = 5 → stdB h n w e₁ = 0 ∧ stdB h n e₁ w = 0
  wf₁ : n = 5 → stdB h n w f₁ = 0 ∧ stdB h n f₁ w = 0
  we₂ : n = 5 → stdB h n w e₂ = 0 ∧ stdB h n e₂ w = 0
  wf₂ : n = 5 → stdB h n w f₂ = 0 ∧ stdB h n f₂ w = 0
  eig : ∀ x ∈ E, ∃ c₁ c₂ : K, mulSU x e₁ = c₁ • e₁ ∧ mulSU x f₁ = c₁⁻¹ • f₁ ∧
    mulSU x e₂ = c₂ • e₂ ∧ mulSU x f₂ = c₂⁻¹ • f₂ ∧ (n = 5 → mulSU x w = w)

theorem exists_frameData [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f - 1) (hn : n = 4 ∨ n = 5)
    (E : Subgroup (unitarySU ℓ f K n)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    ∃ e₁ f₁ e₂ f₂ w : Fin n → K, FrameData h E e₁ f₁ e₂ f₂ w := by
  classical
  have hℓ := h.prime
  have : Fintype E := Fintype.ofFinite E
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0)).symm
  set ρ := unitaryRep (ℓ := ℓ) (f := f) (n := n) (K := K) E with hρdef
  set B := stdB h n with hBdef
  have hB : B.IsSymm := gramForm_isSymm h (by simp)
  have hBl : B.SeparatingLeft := gramForm_separatingLeft h (by simp)
  have hP : IsPlane p E := ⟨hp, hcard, fun x => Subtype.ext (hexp x x.2)⟩
  have hρ : ∀ x : E, ρ x ∈ sesqUnitaryGroup B := unitaryRep_mem h E
  obtain ⟨L, hL, M, hM, hLM, hLne, hMne⟩ :=
    exists_two_active ρ hP hpK hρ hB hBl (unitaryRep_injective E)
  have he2 : ordNegQ ℓ f p = 2 := ordNegQ_eq_two_of_dvd_sub_one hℓ hp (by omega) hpq
  have hcop := coprime_ordNegQ (f := f) hp hpℓ hℓ
  have hdim : ∀ x : E, x ≠ 1 → ordNegQ ℓ f p ∣ Module.finrank K (Fin n → K) -
      Module.finrank K (LinearMap.ker (act ρ x - 1)) := by
    intro x _
    have hxp : ((ρ x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p = 1 := by
      have h1 : (ρ x) ^ p = 1 := by
        rw [← map_pow]
        have : x ^ p = 1 := Subtype.ext (hexp x x.2)
        rw [this, map_one]
      have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) h1
      simpa [Units.val_pow_eq_pow_val] using h2
    exact ordNegQ_dvd_finrank_sub h hp hpℓ hB hBl (hρ x) hxp
  have hdvdN : ∀ N ∈ lines p E, 2 ∣ Module.finrank K (lineSpace ρ B N) := fun N hN =>
    he2 ▸ dvd_finrank_lineSpace ρ hP hpK hρ hB hBl hcop hdim hN
  have hsum := finrank_eq_sum ρ hP hpK hρ hB hBl
  rw [Module.finrank_fin_fun] at hsum
  have hSeven : 2 ∣ ∑ N ∈ lines p E, Module.finrank K (lineSpace ρ B N) := Finset.dvd_sum hdvdN
  have hsub : ({L, M} : Finset (Subgroup E)) ⊆ lines p E := by
    intro N hN
    rcases Finset.mem_insert.mp hN with rfl | hN
    · exact hL
    · exact (Finset.mem_singleton.mp hN) ▸ hM
  have hge : Module.finrank K (lineSpace ρ B L) + Module.finrank K (lineSpace ρ B M) ≤
      ∑ N ∈ lines p E, Module.finrank K (lineSpace ρ B N) := by
    calc Module.finrank K (lineSpace ρ B L) + Module.finrank K (lineSpace ρ B M)
        = ∑ N ∈ ({L, M} : Finset (Subgroup E)), Module.finrank K (lineSpace ρ B N) :=
          (Finset.sum_pair (f := fun N : Subgroup E => Module.finrank K (lineSpace ρ B N))
            hLM).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have hposL : 0 < Module.finrank K (lineSpace ρ B L) := Submodule.one_le_finrank_iff.mpr hLne
  have hposM : 0 < Module.finrank K (lineSpace ρ B M) := Submodule.one_le_finrank_iff.mpr hMne
  have hdL := hdvdN L hL
  have hdM := hdvdN M hM
  have hLd : Module.finrank K (lineSpace ρ B L) = 2 := by omega
  have hMd : Module.finrank K (lineSpace ρ B M) = 2 := by omega
  have h0d : Module.finrank K (fixedSpace ρ ⊤) = n - 4 := by omega
  have hpairN : ∀ N ∈ lines p E, Module.finrank K (lineSpace ρ B N) = 2 →
      ∃ e ∈ lineSpace ρ B N, ∃ f' ∈ lineSpace ρ B N, B e e = 0 ∧ B f' f' = 0 ∧ B e f' = 1 ∧
        ∀ y : E, ∃ c : K, c ≠ 0 ∧ act ρ y e = c • e ∧ act ρ y f' = c⁻¹ • f' := by
    intro N hN hd2
    have hNc : Nat.card N = p := mem_lines.mp hN
    refine exists_hyperbolic_pair_of_finrank_two h (B := B) hp (by omega) hpq
      (fun y : E => act ρ y) ?_ ?_ ?_ (lineSpace ρ B N) ?_
      (separatingLeft_lineSpace ρ hP hpK hρ hB hBl hNc) hd2 ?_
    · intro y z
      show act ρ y * act ρ z = act ρ z * act ρ y
      have hyz : y * z = z * y := Subtype.ext (hcomm y y.2 z z.2)
      rw [← act_mul, ← act_mul, hyz]
    · intro y
      rw [← act_pow, hP.pow y, act_one]
    · intro y v w
      exact mem_sesqUnitaryGroup.mp (hρ y) v w
    · intro y w hw
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · have hlw : act ρ l w = w := hw.1 l hl
        have hly : l * y = y * l := Subtype.ext (hcomm l l.2 y y.2)
        calc act ρ l (act ρ y w) = act ρ (l * y) w := by rw [act_mul]; rfl
          _ = act ρ (y * l) w := by rw [hly]
          _ = act ρ y (act ρ l w) := by rw [act_mul]; rfl
          _ = act ρ y w := by rw [hlw]
      · have huy : act ρ y u = u := hu y (Subgroup.mem_top y)
        have h1 := mem_sesqUnitaryGroup.mp (hρ y) u w
        have h2 : B u (act ρ y w) = B u w := by
          have h3 : B (act ρ y u) (act ρ y w) = B u w := h1
          rwa [huy] at h3
        rw [h2]
        exact hw.2 u hu
    · intro w hw hfixw
      have hw0 : w ∈ fixedSpace ρ ⊤ := fun y _ => hfixw y
      have h2 := fixedTop_inf_lineSpace ρ hP hpK hρ hB hBl N
      have h3 : w ∈ fixedSpace ρ ⊤ ⊓ lineSpace ρ B N := ⟨hw0, hw⟩
      rw [h2] at h3
      exact (Submodule.mem_bot K).mp h3
  obtain ⟨e₁, he₁, f₁, hf₁, hee₁, hff₁, hef₁, hpair₁⟩ := hpairN L hL hLd
  obtain ⟨e₂, he₂, f₂, hf₂, hee₂, hff₂, hef₂, hpair₂⟩ := hpairN M hM hMd
  have hLc : Nat.card L = p := mem_lines.mp hL
  have hMc : Nat.card M = p := mem_lines.mp hM
  have hsymm : ∀ u v : Fin n → K, B v u = h.bar (B u v) := fun u v =>
    ((LinearMap.isSymm_def.mp hB) u v).symm
  have hcross : ∀ u ∈ lineSpace ρ B L, ∀ v ∈ lineSpace ρ B M, B u v = 0 ∧ B v u = 0 := by
    intro u hu v hv
    have h1 : B u v = 0 := orth_line_line ρ hP hpK hρ hB hBl hLc hMc hLM hu hv
    exact ⟨h1, by rw [hsymm, h1, map_zero]⟩
  have hfe : ∀ u v : Fin n → K, B u v = 1 → B v u = 1 := fun u v huv => by
    rw [hsymm, huv, map_one]
  obtain ⟨w, hwV0, hww⟩ : ∃ w ∈ fixedSpace ρ ⊤, n = 5 → B w w = 1 := by
    by_cases h5 : n = 5
    · obtain ⟨b, hb⟩ := h.exists_orthonormal_basis
        (B := B.domRestrict₁₂ (fixedSpace ρ ⊤) (fixedSpace ρ ⊤)) (hB.domRestrict _)
        (separatingLeft_fixedTop ρ hP hpK hρ hB hBl)
      have hd0 : 0 < Module.finrank K (fixedSpace ρ ⊤) := by omega
      refine ⟨(b ⟨0, hd0⟩ : Fin n → K), (b ⟨0, hd0⟩).2, fun _ => ?_⟩
      have h1 := hb ⟨0, hd0⟩ ⟨0, hd0⟩
      rw [LinearMap.domRestrict₁₂_apply] at h1
      simpa using h1
    · exact ⟨0, Submodule.zero_mem _, fun h5' => absurd h5' h5⟩
  refine ⟨e₁, f₁, e₂, f₂, w, ⟨hee₁, hff₁, hef₁, hfe e₁ f₁ hef₁, hee₂, hff₂, hef₂,
    hfe e₂ f₂ hef₂, (hcross e₁ he₁ e₂ he₂).1, (hcross e₁ he₁ f₂ hf₂).1,
    (hcross f₁ hf₁ e₂ he₂).1, (hcross f₁ hf₁ f₂ hf₂).1, (hcross e₁ he₁ e₂ he₂).2,
    (hcross f₁ hf₁ e₂ he₂).2, (hcross e₁ he₁ f₂ hf₂).2, (hcross f₁ hf₁ f₂ hf₂).2, hww,
    fun _ => orth_top_line ρ hB hwV0 he₁, fun _ => orth_top_line ρ hB hwV0 hf₁,
    fun _ => orth_top_line ρ hB hwV0 he₂, fun _ => orth_top_line ρ hB hwV0 hf₂, ?_⟩⟩
  intro x hx
  obtain ⟨c₁, -, h1e, h1f⟩ := hpair₁ ⟨x, hx⟩
  obtain ⟨c₂, -, h2e, h2f⟩ := hpair₂ ⟨x, hx⟩
  exact ⟨c₁, c₂, h1e, h1f, h2e, h2f, fun _ => hwV0 ⟨x, hx⟩ (Subgroup.mem_top _)⟩

theorem exists_frame_of_dvd_sub_one [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f - 1)
    (hn : n = 4 ∨ n = 5) (E : Subgroup (unitarySU ℓ f K n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    ∃ P : GL (Fin n) K, conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K) = antidiag n ∧
      ∀ x ∈ E, (((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K).IsDiag := by
  obtain ⟨e₁, f₁, e₂, f₂, w, hd⟩ := exists_frameData h hp hp5 hpℓ hpq hn E hcomm hexp hcard
  rcases hn with rfl | rfl
  · refine exists_frame_of_family h E ![e₁, e₂, f₂, f₁] ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Fin.rev, hd.ee₁, hd.ff₁, hd.ef₁, hd.fe₁, hd.ee₂, hd.ff₂,
        hd.ef₂, hd.fe₂, hd.e₁e₂, hd.e₁f₂, hd.f₁e₂, hd.f₁f₂, hd.e₂e₁, hd.e₂f₁, hd.f₂e₁, hd.f₂f₁]
    · intro x hx
      obtain ⟨c₁, c₂, h1e, h1f, h2e, h2f, -⟩ := hd.eig x hx
      refine ⟨![c₁, c₂, c₂⁻¹, c₁⁻¹], fun c => ?_⟩
      fin_cases c
      · simpa using h1e
      · simpa using h2e
      · simpa using h2f
      · simpa using h1f
  · have hww := hd.ww rfl
    have hwe₁ := hd.we₁ rfl
    have hwf₁ := hd.wf₁ rfl
    have hwe₂ := hd.we₂ rfl
    have hwf₂ := hd.wf₂ rfl
    refine exists_frame_of_family h E ![e₁, e₂, w, f₂, f₁] ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Fin.rev, hd.ee₁, hd.ff₁, hd.ef₁, hd.fe₁, hd.ee₂, hd.ff₂,
        hd.ef₂, hd.fe₂, hd.e₁e₂, hd.e₁f₂, hd.f₁e₂, hd.f₁f₂, hd.e₂e₁, hd.e₂f₁, hd.f₂e₁, hd.f₂f₁,
        hww, hwe₁.1, hwe₁.2, hwf₁.1, hwf₁.2, hwe₂.1, hwe₂.2, hwf₂.1, hwf₂.2]
    · intro x hx
      obtain ⟨c₁, c₂, h1e, h1f, h2e, h2f, hw⟩ := hd.eig x hx
      refine ⟨![c₁, c₂, 1, c₂⁻¹, c₁⁻¹], fun c => ?_⟩
      fin_cases c
      · simpa using h1e
      · simpa using h2e
      · simpa using hw rfl
      · simpa using h2f
      · simpa using h1f

end Frame

end CFSG.RankThree.PartOne.CTP
