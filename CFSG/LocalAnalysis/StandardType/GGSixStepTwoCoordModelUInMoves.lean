module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInSwap

public section

namespace CFSG.StandardType

namespace CoordSUIn

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CoordSU Multiplicative
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Dual

theorem ker_le_ker_dualPoly_pow (h : UnitaryFieldData 2 f K) {p : ℕ} {g : K[X]}
    (hg : Irreducible g) (hgX : g ∣ X ^ p - C 1) (hg0 : g.coeff 0 ≠ 0) {m : ℕ}
    (hm : (m : ZMod p) = -((2 ^ f : ℕ) : ZMod p)) {V : Type} [AddCommGroup V] [Module K V]
    (Y : Module.End K V) :
    LinearMap.ker (aeval Y g) ≤ LinearMap.ker (aeval (Y ^ m) (dualPoly h.bar g)) := by
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : CharP (AdjoinRoot g) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
  have hρ : aeval (AdjoinRoot.root g) g = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hρp : AdjoinRoot.root g ^ p = 1 := by
    obtain ⟨c, hc⟩ := hgX
    have h1 : aeval (AdjoinRoot.root g) (X ^ p - C 1 : K[X]) = 0 := by
      rw [hc, map_mul, hρ, zero_mul]
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, sub_eq_zero] at h1
    exact h1
  have hdual := aeval_dualPoly_inv_pow (h := h) hg0 hρ
  have hdvdp : p ∣ m + 2 ^ f :=
    (ZMod.natCast_eq_zero_iff _ p).mp (by rw [Nat.cast_add, hm, neg_add_cancel])
  obtain ⟨c, hc⟩ := hdvdp
  have hm' : AdjoinRoot.root g ^ m = (AdjoinRoot.root g ^ 2 ^ f)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add, hc, pow_mul, hρp, one_pow])
  have hdvd : g ∣ (dualPoly h.bar g).comp (X ^ m) := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_comp, map_pow, aeval_X, hm']
    exact hdual
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  obtain ⟨d, hd⟩ := hdvd
  have e1 : aeval (Y ^ m) (dualPoly h.bar g) = aeval Y ((dualPoly h.bar g).comp (X ^ m)) := by
    rw [aeval_comp, map_pow, aeval_X]
  rw [e1, hd, mul_comm, map_mul, Module.End.mul_apply, hv, map_zero]

end Dual

section Generators

variable {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem realizable_of_single (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {π : Equiv.Perm (Fin F.r)} {η : Fin F.r → (ZMod p)ˣ} {w : ↥(unitarySU 2 f K n)}
    (hw : ∀ k, w⁻¹ * F.b (π k) * w = F.b k ^ (η k : ZMod p).val) : Realizable F π η := by
  classical
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  set T : (Fin F.r → ZMod p) → (Fin F.r → ZMod p) := fun s k => (η k : ZMod p) * s (π k)
    with hT
  set P : (Fin F.r → ZMod p) → Prop := fun s => w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (T s))
    with hP
  have hadd : ∀ s t, P s → P t → P (s + t) := by
    intro s t hs ht
    have hTst : T (s + t) = T s + T t := by
      funext k
      simp only [hT, Pi.add_apply, mul_add]
    change w⁻¹ * F.ι (ofAdd (s + t)) * w = F.ι (ofAdd (T (s + t)))
    rw [hTst, ofAdd_add, ofAdd_add, map_mul, map_mul, ← hs, ← ht]
    group
  have hzero : P 0 := by
    have hT0 : T 0 = 0 := by
      funext k
      simp only [hT, Pi.zero_apply, mul_zero]
    change w⁻¹ * F.ι (ofAdd 0) * w = F.ι (ofAdd (T 0))
    rw [hT0, ofAdd_zero, map_one]
    group
  have hgen : ∀ l, P (Pi.single l 1) := by
    intro l
    have hTl : T (Pi.single l 1) =
        Pi.single (π.symm l) ((((η (π.symm l) : ZMod p).val : ℕ) : ZMod p)) := by
      funext k
      rw [ZMod.natCast_zmod_val]
      simp only [hT]
      by_cases hk : k = π.symm l
      · subst hk
        simp
      · have hk' : π k ≠ l := fun e => hk (by rw [← e, Equiv.symm_apply_apply])
        simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk']
    change w⁻¹ * F.ι (ofAdd (Pi.single l 1)) * w = F.ι (ofAdd (T (Pi.single l 1)))
    rw [hTl, F.ι_single_pow, F.ι_single, ← hw (π.symm l), Equiv.apply_symm_apply]
  have hsmul : ∀ l (c : ℕ), P (c • Pi.single l 1) := by
    intro l c
    induction c with
    | zero => rw [zero_smul]; exact hzero
    | succ c ih => rw [succ_nsmul]; exact hadd _ _ ih (hgen l)
  refine ⟨w, fun s => ?_⟩
  have hs : s = ∑ l, (s l).val • Pi.single l (1 : ZMod p) := by
    conv_lhs => rw [← Finset.univ_sum_single s]
    refine Finset.sum_congr rfl fun l _ => ?_
    funext k
    by_cases hk : k = l
    · subst hk
      simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne hk]
  have hPs : P s := by
    rw [hs]
    exact Finset.sum_induction _ P hadd hzero fun l _ => hsmul l _
  exact hPs

theorem conj_pow_of_sq {G : Type} [Group G] {σ : G} (hσσ : σ * σ = 1) (a : G) (k : ℕ) :
    σ * a ^ k * σ = (σ * a * σ) ^ k := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hc : ∀ b, σ * b * σ = MulAut.conj σ b := fun b => by rw [MulAut.conj_apply, hσinv]
  rw [hc, hc, map_pow]

end Generators

section Twist

variable {p : ℕ}

theorem pairTwist_apply_left {r : ℕ} (c : (ZMod p)ˣ) (i j : Fin r) : pairTwist c i j i = c := by
  simp [pairTwist]

theorem pairTwist_apply_right {r : ℕ} (c : (ZMod p)ˣ) {i j : Fin r} (hij : i ≠ j) :
    pairTwist c i j j = c⁻¹ := by
  simp [pairTwist, Ne.symm hij]

theorem pairTwist_apply_of_ne {r : ℕ} (c : (ZMod p)ˣ) {i j k : Fin r} (hki : k ≠ i)
    (hkj : k ≠ j) : pairTwist c i j k = 1 := by
  simp [pairTwist, hki, hkj]

end Twist

section Moves

variable {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem lin_mul_pow_apply_left (F : PieceFrame f n K h p A) {i j : Fin F.r} (hij : i ≠ j)
    (m : ℕ) {u : Fin n → K} (hu : u ∈ rng (F.y i)) :
    lin (F.b i * F.b j ^ m) u = lin (F.y i) u := by
  rw [lin_mul, Module.End.mul_apply,
    lin_pow_apply_of_fix (lin_b_apply_of_ne F (Ne.symm hij) hu) m, F.b_on i u hu]

theorem lin_mul_pow_apply_right (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {i j : Fin F.r}
    (hij : i ≠ j) (m : ℕ) {w : Fin n → K} (hw : w ∈ rng (F.y j)) :
    lin (F.b i * F.b j ^ m) w = lin (F.y j ^ m) w := by
  rw [lin_mul, Module.End.mul_apply, lin_b_apply_of_ne F hij
    (rng_inv hA (F.y_mem j) (A.pow_mem (F.b_mem j) m) w hw), lin_b_pow_on hA F j m hw]

theorem aeval_mul_pow_eq_zero (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {i j l : Fin F.r}
    {m : ℕ} {Y : Module.End K (Fin n → K)}
    (hY : ∀ u ∈ rng (F.y l), lin (F.b i * F.b j ^ m) u = Y u) {P : K[X]} {w : Fin n → K}
    (hw : w ∈ rng (F.y l)) (hPw : aeval Y P w = 0) :
    aeval (lin (F.b i * F.b j ^ m)) P w = 0 := by
  rw [SUTB.aeval_eq_of_eqOn (rng_inv hA (F.y_mem l) (A.mul_mem (F.b_mem i)
    (A.pow_mem (F.b_mem j) m))) hY P hw]
  exact hPw

theorem realizable_swap (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {g : K[X]}
    (hg : Irreducible g) (hgm : g.Monic) (hgd : g ∣ cyclotomic p K)
    (hal : ∀ i, LinearMap.ker (aeval (lin (F.y i)) g) ≠ ⊥) {i j : Fin F.r} (hij : i ≠ j) :
    Realizable F (Equiv.swap i j) 1 := by
  have hp := hA.prime
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpK := hA.natCast_ne_zero h
  obtain ⟨wi, hwi, hwi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hal i)
  obtain ⟨wj, hwj, hwj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hal j)
  have hwiU : wi ∈ rng (F.y i) := ker_aeval_le_range hpK hp hgd hwi
  have hwjU : wj ∈ rng (F.y j) := ker_aeval_le_range hpK hp hgd hwj
  have hxi : aeval (lin (F.b i * F.b j ^ 1)) g wi = 0 :=
    aeval_mul_pow_eq_zero hA F (fun u hu => lin_mul_pow_apply_left F hij 1 hu) hwiU
      (LinearMap.mem_ker.mp hwi)
  have hxj : aeval (lin (F.b i * F.b j ^ 1)) g wj = 0 :=
    aeval_mul_pow_eq_zero hA F (fun u hu => by rw [lin_mul_pow_apply_right hA F hij 1 hu, pow_one])
      hwjU (LinearMap.mem_ker.mp hwj)
  obtain ⟨σ, hσσ, hσx, hσi, hσk⟩ := exists_classSwap hA F hij (m := 1) (by simpa using hp.ne_one)
    (mem_primaryFactors_of_ker hg hgm hwi0 hxi) ⟨wi, hwiU, hwi0, hxi⟩ ⟨wj, hwjU, hwj0, hxj⟩
  have hσj := classSwap_b_right hA F (m' := 1) (by rw [one_mul, Nat.one_mod_eq_one.mpr hp.ne_one])
    hσσ hσx hσi
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  refine realizable_of_single hA F (w := σ) fun k => ?_
  rw [hσinv, Pi.one_apply, Units.val_one, ZMod.val_one, pow_one]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, hσj, pow_one]
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, hσi, pow_one]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hσk k hki hkj]

theorem realizable_twist (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {g : K[X]}
    (hg : Irreducible g) (hgm : g.Monic) (hgd : g ∣ cyclotomic p K)
    (hal : ∀ i, LinearMap.ker (aeval (lin (F.y i)) g) ≠ ⊥) {u : (ZMod p)ˣ}
    (hu : (u : ZMod p) = -((2 ^ f : ℕ) : ZMod p)) {i j : Fin F.r} (hij : i ≠ j) :
    Realizable F 1 (pairTwist u i j) := by
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpK := hA.natCast_ne_zero h
  obtain ⟨wi, hwi, hwi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hal i)
  obtain ⟨wj, hwj, hwj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hal j)
  have hwiU : wi ∈ rng (F.y i) := ker_aeval_le_range hpK hp hgd hwi
  have hwjU : wj ∈ rng (F.y j) := ker_aeval_le_range hpK hp hgd hwj
  have hxi : aeval (lin (F.b i * F.b j ^ 1)) g wi = 0 :=
    aeval_mul_pow_eq_zero hA F (fun u hu => lin_mul_pow_apply_left F hij 1 hu) hwiU
      (LinearMap.mem_ker.mp hwi)
  have hxj : aeval (lin (F.b i * F.b j ^ 1)) g wj = 0 :=
    aeval_mul_pow_eq_zero hA F (fun u hu => by rw [lin_mul_pow_apply_right hA F hij 1 hu, pow_one])
      hwjU (LinearMap.mem_ker.mp hwj)
  obtain ⟨σ₁, hσσ₁, hσx₁, hσi₁, hσk₁⟩ := exists_classSwap hA F hij (m := 1)
    (by simpa using hp.ne_one) (mem_primaryFactors_of_ker hg hgm hwi0 hxi) ⟨wi, hwiU, hwi0, hxi⟩
    ⟨wj, hwjU, hwj0, hxj⟩
  have hσj₁ := classSwap_b_right hA F (m' := 1)
    (by rw [one_mul, Nat.one_mod_eq_one.mpr hp.ne_one]) hσσ₁ hσx₁ hσi₁
  rw [pow_one] at hσi₁ hσj₁
  have Hi := unitaryPrimaryData_toUnit h hA (F.y_mem i)
  have hgi : g ∈ primaryFactors (lin (F.y i)) :=
    mem_primaryFactors_of_ker hg hgm hwi0 (LinearMap.mem_ker.mp hwi)
  have hg'i : dualPoly h.bar g ∈ primaryFactors (lin (F.y i)) := dualPoly_mem_primaryFactors Hi hgi
  have hg'irr := irreducible_of_mem_primaryFactors hg'i
  have hg'm := monic_of_mem_primaryFactors hg'i
  have hminp : minpoly K (lin (F.y i)) ∣ X ^ p - C 1 := by
    refine minpoly.dvd K _ ?_
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hA.lin_pow (F.y_mem i), sub_self]
  have hg'X : dualPoly h.bar g ∣ X ^ p - C 1 := (mem_primaryFactors.mp hg'i).2.2.trans hminp
  have hg'1 : dualPoly h.bar g ≠ X - C 1 := by
    intro e
    have h1 := dualPoly_dualPoly_of_mem Hi hgi
    rw [e, dualPoly_X_sub_C_one] at h1
    exact aeval_one_ne_zero_of_dvd hp hpK (E := K) hgd (by rw [← h1, map_sub, aeval_X, aeval_C,
      map_one, sub_self])
  have hg'd : dualPoly h.bar g ∣ cyclotomic p K := dvd_cyclotomic_of_dvd hp hg'irr hg'm hg'X hg'1
  obtain ⟨wi', hwi', hwi'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot Hi.squarefree hg'i)
  have hwi'U : wi' ∈ rng (F.y i) := ker_aeval_le_range hpK hp hg'd hwi'
  set m := (u : ZMod p).val with hmdef
  have hm : ¬ p ∣ m := not_dvd_val_unit hp u
  have hmq : (m : ZMod p) = -((2 ^ f : ℕ) : ZMod p) := by
    rw [hmdef, ZMod.natCast_zmod_val]
    exact hu
  have hgX : g ∣ X ^ p - C 1 := by
    rw [C_1]
    exact hgd.trans (cyclotomic.dvd_X_pow_sub_one p K)
  have hg0 : g.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_mem_primaryFactors Hi.squarefree hgi
  have hxi' : aeval (lin (F.b i * F.b j ^ m)) (dualPoly h.bar g) wi' = 0 :=
    aeval_mul_pow_eq_zero hA F (fun u hu => lin_mul_pow_apply_left F hij m hu) hwi'U
      (mem_primaryComponent.mp hwi')
  have hxj' : aeval (lin (F.b i * F.b j ^ m)) (dualPoly h.bar g) wj = 0 := by
    refine aeval_mul_pow_eq_zero hA F (Y := lin (F.y j) ^ m)
      (fun u hu => by rw [lin_mul_pow_apply_right hA F hij m hu, SUTB.lin_pow]) hwjU ?_
    exact LinearMap.mem_ker.mp (ker_le_ker_dualPoly_pow h hg hgX hg0 hmq (lin (F.y j)) hwj)
  obtain ⟨σu, hσσu, hσxu, hσiu, hσku⟩ := exists_classSwap hA F hij hm
    (mem_primaryFactors_of_ker hg'irr hg'm hwi'0 hxi') ⟨wi', hwi'U, hwi'0, hxi'⟩
    ⟨wj, hwjU, hwj0, hxj'⟩
  set m' := ((u⁻¹ : (ZMod p)ˣ) : ZMod p).val with hm'def
  have hmm' : m * m' % p = 1 := by
    rw [hmdef, hm'def, ← ZMod.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      ZMod.val_one]
  have hσju := classSwap_b_right hA F hmm' hσσu hσxu hσiu
  have hσinv₁ : σ₁⁻¹ = σ₁ := inv_eq_of_mul_eq_one_right hσσ₁
  have hσinvu : σu⁻¹ = σu := inv_eq_of_mul_eq_one_right hσσu
  have hw : ∀ k, (σu * σ₁)⁻¹ * F.b k * (σu * σ₁) = σ₁ * (σu * F.b k * σu) * σ₁ := fun k => by
    rw [_root_.mul_inv_rev, hσinv₁, hσinvu]
    group
  refine realizable_of_single hA F (w := σu * σ₁) fun k => ?_
  rw [Equiv.Perm.one_apply, hw]
  by_cases hki : k = i
  · rw [hki, hσiu, conj_pow_of_sq hσσ₁, hσj₁, pairTwist_apply_left]
  · by_cases hkj : k = j
    · rw [hkj, hσju, conj_pow_of_sq hσσ₁, hσi₁, pairTwist_apply_right u hij]
    · rw [hσku k hki hkj, hσk₁ k hki hkj, pairTwist_apply_of_ne u hki hkj, Units.val_one,
        ZMod.val_one, pow_one]

end Moves

end CoordSUIn

open CoordSUIn NsFrameComp

theorem ggSUPieceSwapInput_holds : GGSUPieceSwapInput := by
  intro f n K _ h p A hA
  have : Finite K := h.finite
  have hp := hA.prime
  obtain ⟨g₀, hg₀, hg₀d⟩ := Polynomial.exists_irreducible_of_degree_pos
    (Polynomial.degree_cyclotomic_pos p K hp.pos)
  obtain ⟨g, hg, hgm, hgg₀, -⟩ := SUTB.exists_monic_of_irreducible (V := Fin n → K) hg₀
  have hgd : g ∣ Polynomial.cyclotomic p K := hgg₀.trans hg₀d
  obtain ⟨F₀⟩ := exists_pieceFrame' h hA
  obtain ⟨F, hal⟩ := exists_aligned_frame hA F₀ hg hgd
  exact ⟨F, fun u hu => ⟨fun i j hij => realizable_swap hA F hg hgm hgd hal hij,
    fun i j hij => realizable_twist hA F hg hgm hgd hal hu hij⟩⟩

end CFSG.StandardType
