module

public import CFSG.Quasithin.Background.SmithB45HM22Pack
public import CFSG.Quasithin.Background.SmithB45HM22Flag
public import CFSG.Quasithin.Background.SmithB45MatSpin

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat Matrix

@[expose] def nsF (ns : List ℕ) (i : ℕ) : ℕ := ns.getD i 0

@[expose] def blockOK (T : PM) (ns : List ℕ) (stds : List PM) : Bool :=
  (List.range (ns.length - 1)).all fun i =>
    (List.range (nsF ns (i + 1) - nsF ns i)).all fun c =>
      PV.lowZero (nsF ns (i + 1)) (PM.col T (nsF ns i + c)) &&
        PV.eqv (nsF ns (i + 1) - nsF ns i) ((PM.col T (nsF ns i + c)).shr (nsF ns i))
          (PM.col (stds.getD i []) c)

@[expose] def flagOK (N : ℕ) (K₁ K₂ P Pi : PM) (ns : List ℕ) (stds₁ stds₂ : List PM) : Bool :=
  P.length == N && Pi.length == N && PM.eqm N (PM.mul P Pi) (PM.idm N) &&
    blockOK (PM.mul Pi (PM.mul K₁ P)) ns stds₁ && blockOK (PM.mul Pi (PM.mul K₂ P)) ns stds₂

theorem flagOK_parts {N : ℕ} {K₁ K₂ P Pi : PM} {ns : List ℕ} {stds₁ stds₂ : List PM}
    (h : flagOK N K₁ K₂ P Pi ns stds₁ stds₂ = true) :
    P.length = N ∧ Pi.length = N ∧ PM.toMat N N P * PM.toMat N N Pi = 1 ∧
      blockOK (PM.mul Pi (PM.mul K₁ P)) ns stds₁ = true ∧
      blockOK (PM.mul Pi (PM.mul K₂ P)) ns stds₂ = true := by
  simp only [flagOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hP, hPi⟩, hid⟩, h1⟩, h2⟩ := h
  refine ⟨hP, hPi, ?_, h1, h2⟩
  rw [← PM.toMat_mul P Pi hP hPi, PM.toMat_eq_of_eqm hid, PM.toMat_idm]

theorem toVec_mem_flagSub {N n : ℕ} {v : PV} (h : PV.lowZero n v = true) :
    PV.toVec N v ∈ flagSub FieldFour N n := fun _ hk => PV.get_eq_zero_of_lowZero h hk

theorem resW_toVec {N n0 d : ℕ} (h : n0 + d ≤ N) (v : PV) :
    resW FieldFour N n0 d (PV.toVec N v) = PV.toVec d (v.shr n0) := by
  funext k
  have h1 : n0 + k.val < N := by omega
  rw [resW_apply, dite_eq_left h1]
  simp only [PV.toVec, PV.get_shr]

theorem toMat_mulVec_single {m n : ℕ} (M : PM) (j : Fin n) :
    PM.toMat m n M *ᵥ Pi.single j 1 = PV.toVec m (PM.col M j) := by
  funext i
  rw [Matrix.mulVec_single_one]
  rfl

theorem exists_window {ns : ℕ → ℕ} (hns0 : ns 0 = 0) {j k : ℕ} (hk : k < ns j) :
    ∃ i < j, ns i ≤ k ∧ k < ns (i + 1) := by
  induction j with
  | zero => rw [hns0] at hk; omega
  | succ j ih =>
    by_cases hkj : k < ns j
    · obtain ⟨i, hi, h⟩ := ih hkj
      exact ⟨i, by omega, h⟩
    · exact ⟨j, by omega, by omega, hk⟩

theorem flagSub_inv_of_blockOK {N : ℕ} {T : PM} {ns : List ℕ}
    {stds : List PM} (h : blockOK T ns stds = true) (hns0 : nsF ns 0 = 0)
    (hmono : ∀ i < ns.length - 1, nsF ns i < nsF ns (i + 1)) {j : ℕ} (hj : j ≤ ns.length - 1)
    {v : Fin N → FieldFour} (hv : v ∈ flagSub FieldFour N (nsF ns j)) :
    PM.toMat N N T *ᵥ v ∈ flagSub FieldFour N (nsF ns j) := by
  intro l hl
  simp only [blockOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < nsF ns j
  · obtain ⟨i, hij, hik, hki⟩ := exists_window hns0 hk
    have hc : (k : ℕ) - nsF ns i < nsF ns (i + 1) - nsF ns i := by omega
    have h1 := (h i (by omega) _ hc).1
    rw [show nsF ns i + ((k : ℕ) - nsF ns i) = k by omega] at h1
    have h2 : PM.toMat N N T l k = (PM.col T k).get l := rfl
    rw [h2, PV.get_eq_zero_of_lowZero h1, zero_mul]
    have : nsF ns (i + 1) ≤ nsF ns j := by
      rcases Nat.lt_or_ge (i + 1) j with h3 | h3
      · exact (ns_mono' hmono (i + 1) j (by omega) hj)
      · rw [show i + 1 = j by omega]
    exact this.trans hl
  · rw [hv k (by omega), mul_zero]

theorem blockW_eq_of_blockOK {N : ℕ} {T : PM} {ns : List ℕ} {stds : List PM}
    (h : blockOK T ns stds = true) {i : ℕ} (hi : i < ns.length - 1)
    (hle : nsF ns (i + 1) ≤ N) (hlt : nsF ns i ≤ nsF ns (i + 1)) :
    blockW FieldFour N (nsF ns i) (nsF ns (i + 1) - nsF ns i) (Matrix.toLin' (PM.toMat N N T)) =
      Matrix.toLin' (PM.toMat _ _ (stds.getD i [])) := by
  simp only [blockOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  apply LinearMap.pi_ext'
  intro c
  apply LinearMap.ext_ring
  have hc := c.isLt
  obtain ⟨-, h2⟩ := h i hi c hc
  have hwin : nsF ns i + (nsF ns (i + 1) - nsF ns i) ≤ N := by omega
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
  have he : embW FieldFour N (nsF ns i) (nsF ns (i + 1) - nsF ns i) (Pi.single c 1) =
      Pi.single (⟨nsF ns i + c, by omega⟩ : Fin N) 1 := by
    funext j
    rw [embW_apply]
    by_cases hj : (j : ℕ) = nsF ns i + c
    · have hj' : nsF ns i ≤ j ∧ (j : ℕ) - nsF ns i < nsF ns (i + 1) - nsF ns i :=
        ⟨by omega, by omega⟩
      rw [dite_eq_left hj', Pi.single_apply, Pi.single_apply]
      have e1 : (⟨(j : ℕ) - nsF ns i, hj'.2⟩ : Fin _) = c := Fin.ext (by simp; omega)
      have e2 : j = ⟨nsF ns i + c, by omega⟩ := Fin.ext hj
      rw [ite_eq_left e1, ite_eq_left e2]
    · rw [Pi.single_apply]
      have hne : j ≠ ⟨nsF ns i + c, by omega⟩ := fun e => hj (congrArg Fin.val e)
      rw [ite_eq_right hne]
      split_ifs with hj'
      · rw [Pi.single_apply, ite_eq_right]
        intro e
        apply hj
        have := congrArg Fin.val e
        simp at this
        omega
      · rfl
  rw [blockW, LinearMap.comp_apply, LinearMap.comp_apply, he, Matrix.toLin'_apply,
    toMat_mulVec_single, resW_toVec hwin, Matrix.toLin'_apply, toMat_mulVec_single]
  exact PV.toVec_eq_of_eqv h2

structure PSpin where
  terms : List (List Bool × FieldFour)
  Q : PM
  Qi : PM
  R : PM
  spin : List (ℕ × Bool)
  Si : PM
  w : PV
  dual : List (ℕ × Bool)
  Ti : PM

@[expose] def PSpin.toSpin (n : ℕ) (d : PSpin) : SpinData FieldFour n where
  terms := d.terms
  Q := PM.unpack n n d.Q
  Qi := PM.unpack n n d.Qi
  R := PM.unpack n n d.R
  spin := d.spin
  Si := PM.unpack n n d.Si
  w := Vector.ofFn fun i => d.w.get i
  dual := d.dual
  Ti := PM.unpack n n d.Ti

@[expose] def nortonOK (n : ℕ) [NeZero n] (A B : PM) (d : PSpin) : Bool :=
  A.length == n && B.length == n && PM.eqm n (PM.mul A A) (PM.idm n) &&
    PM.eqm n (PM.mul B (PM.mul B (PM.mul B B))) (PM.idm n) &&
    (d.toSpin n).check (PM.unpack n n A) (PM.unpack n n B)

theorem irredFam_of_nortonOK {n : ℕ} [NeZero n] {A B : PM} {d : PSpin}
    (h : nortonOK n A B d = true) :
    IrredFam (fun b : Bool =>
      Matrix.toLin' (if b then PM.toMat n n B else PM.toMat n n A)) := by
  simp only [nortonOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hA2⟩, hB4⟩, hchk⟩ := h
  set MA := PM.toMat n n A with hMA
  set MB := PM.toMat n n B with hMB
  have hA2' : MA * MA = 1 := by
    rw [hMA, ← PM.toMat_mul A A hA hA, PM.toMat_eq_of_eqm hA2, PM.toMat_idm]
  have hB4' : MB * (MB * (MB * MB)) = 1 := by
    rw [hMB, ← PM.toMat_mul B B hB hB, ← PM.toMat_mul B _ hB (by rw [PM.length_mul]; exact hB),
      ← PM.toMat_mul B _ hB (by rw [PM.length_mul, PM.length_mul]; exact hB),
      PM.toMat_eq_of_eqm hB4, PM.toMat_idm]
  let uA : (Matrix (Fin n) (Fin n) FieldFour)ˣ := ⟨MA, MA, hA2', hA2'⟩
  let uB : (Matrix (Fin n) (Fin n) FieldFour)ˣ :=
    ⟨MB, MB * (MB * MB), hB4', by simp only [Matrix.mul_assoc]; exact hB4'⟩
  let M : FreeGroup Bool →* Matrix (Fin n) (Fin n) FieldFour :=
    (Units.coeHom _).comp (FreeGroup.lift fun b => if b then uB else uA)
  have ha : untab (PM.unpack n n A) = M (FreeGroup.of false) := by
    rw [PM.untab_unpack]
    simp [M, uA, hMA]
  have hb : untab (PM.unpack n n B) = M (FreeGroup.of true) := by
    rw [PM.untab_unpack]
    simp [M, uB, hMB]
  have hirr := SpinData.isIrreducible_of_check (RingHom.id FieldFour) M ha hb (d.toSpin n) hchk
  intro U hU
  have hinvA : ∀ u ∈ U, MA *ᵥ u ∈ U := fun u hu => by
    have := hU false u hu
    simpa using this
  have hinvB : ∀ u ∈ U, MB *ᵥ u ∈ U := fun u hu => by
    have := hU true u hu
    simpa using this
  have hall : ∀ g : FreeGroup Bool, ∀ u ∈ U, M g *ᵥ u ∈ U := by
    intro g
    induction g using FreeGroup.induction_on with
    | one => intro u hu; simpa using hu
    | of b =>
      intro u hu
      cases b
      · simpa [M, uA] using hinvA u hu
      · simpa [M, uB] using hinvB u hu
    | inv_of b _ =>
      intro u hu
      cases b
      · simpa [M, uA] using hinvA u hu
      · have h1 := hinvB _ (hinvB _ (hinvB u hu))
        simpa [M, uB, Matrix.mulVec_mulVec] using h1
    | mul x y hx hy =>
      intro u hu
      have := hx _ (hy u hu)
      simpa [Matrix.mulVec_mulVec] using this
  let W : Subrepresentation (matrixBaseChange (RingHom.id FieldFour) M) :=
    ⟨U, fun g u hu => by
      rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id]
      exact hall g u hu⟩
  rcases hirr.eq_bot_or_eq_top W with h0 | h0
  · left
    have := congrArg Subrepresentation.toSubmodule h0
    exact this
  · right
    have := congrArg Subrepresentation.toSubmodule h0
    exact this

end CFSG.Quasithin.HM22
