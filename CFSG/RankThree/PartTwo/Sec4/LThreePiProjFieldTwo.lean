module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section PullP

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def pullP (e : L ≃* projImage (slPi π 3 (p ^ f) K))
    (X : Subgroup (GL (Fin 3) K)) : Subgroup G :=
  (((X ⊓ slPi π 3 (p ^ f) K).map ProjGenLinGroup.mk).comap
    ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom)).map L.subtype

omit hLn in
theorem mem_pullP {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {X : Subgroup (GL (Fin 3) K)}
    {g : G} : g ∈ pullP e X ↔ ∃ hg : g ∈ L, ∃ x ∈ X ⊓ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk x = ((e ⟨g, hg⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hl)
    exact ⟨l.2, x, hx, hxe⟩
  · rintro ⟨hg, x, hx, hxe⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨x, hx, hxe⟩), rfl⟩

omit hLn in
theorem pullP_ne_bot {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {X : Subgroup (GL (Fin 3) K)}
    {M : GL (Fin 3) K} (hMX : M ∈ X) (hMS : M ∈ slPi π 3 (p ^ f) K)
    (hM : M ∉ StatedScalars (Fin 3) K) : pullP e X ≠ ⊥ := by
  intro h
  have hmem : ((e.symm (projOf _ ⟨M, hMS⟩) : L) : G) ∈ pullP e X := by
    refine mem_pullP.mpr ⟨(e.symm _).2, M, Subgroup.mem_inf.mpr ⟨hMX, hMS⟩, ?_⟩
    have : (⟨((e.symm (projOf _ ⟨M, hMS⟩) : L) : G), (e.symm _).2⟩ : L) =
      e.symm (projOf _ ⟨M, hMS⟩) := rfl
    rw [this, MulEquiv.apply_symm_apply, coe_projOf]
  rw [h, Subgroup.mem_bot] at hmem
  apply hM
  have h2 : e.symm (projOf _ ⟨M, hMS⟩) = 1 := Subtype.ext hmem
  have h3 := congrArg (fun x : L => ((e x : projImage (slPi π 3 (p ^ f) K)) :
    ProjGenLinGroup (Fin 3) K)) h2
  simp only [MulEquiv.apply_symm_apply, coe_projOf, map_one, Subgroup.coe_one] at h3
  exact mk_eq_one_iff_mem_statedScalars.mp h3

omit hLn in
theorem pullP_sq {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {X : Subgroup (GL (Fin 3) K)}
    (hX2 : ∀ M ∈ X, M ^ 2 = 1) {g : G} (hg : g ∈ pullP e X) : g ^ 2 = 1 := by
  obtain ⟨hgL, x, hx, hxe⟩ := mem_pullP.mp hg
  have h1 : e ⟨g, hgL⟩ ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hxe, ← map_pow, hX2 x (Subgroup.mem_inf.mp hx).1, map_one]
    rfl)
  rw [← map_pow, map_eq_one_iff _ e.injective] at h1
  exact congrArg Subtype.val h1

theorem mem_normalizer_pullP [Finite G] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {X : Subgroup (GL (Fin 3) K)} {a : G}
    (ha : ∀ (m : projImage (slPi π 3 (p ^ f) K)), ∀ x ∈ X ⊓ slPi π 3 (p ^ f) K,
      (m : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk x →
        ∃ x' ∈ X ⊓ slPi π 3 (p ^ f) K,
          ((slAct e ⟨a, mem_normalizer_of_normal a⟩ m : projImage (slPi π 3 (p ^ f) K)) :
            ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk x') :
    a ∈ Subgroup.normalizer (pullP e X : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro g hg
  obtain ⟨hgL, x, hx, hxe⟩ := mem_pullP.mp hg
  obtain ⟨x', hx', hx'e⟩ := ha (e ⟨g, hgL⟩) x hx hxe.symm
  refine mem_pullP.mpr ⟨hLn.conj_mem g hgL a, x', hx', ?_⟩
  have hcoe := coe_slAct_eqP e a (e ⟨g, hgL⟩)
  simp only [MulEquiv.symm_apply_apply] at hcoe
  rw [← hx'e, hcoe]

theorem commute_of_slAct_eqP {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : G} {x : L}
    (h : slAct e ⟨a, mem_normalizer_of_normal a⟩ (e x) = e x) : a * x = x * a := by
  rw [slAct_apply, MulEquiv.symm_apply_apply] at h
  have h1 := congrArg Subtype.val (e.injective h)
  change a * (x : G) * a⁻¹ = x at h1
  calc a * (x : G) = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [h1]

end PullP

section RankFourP

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def diagOrFrobP (e : L ≃* projImage (slPi π 3 (p ^ f) K)) (σ : G) : Set G :=
  {x | ∃ D : GL (Fin 3) K, IsPGLAtP e x D ∧
    ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0} ∪ {σ}

theorem two_and_unitary_of_rank_fourP (hG : SectionFourHyp G) (hK : PiField π p f K)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {ψ : K ≃+* K} {σ : G}
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s))
    {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : Nat.card E = 81)
    (hEgen : E ≤ Subgroup.closure (diagOrFrobP e σ)) : p = 2 ∧ π = false := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hp2 : p = 2 := by
    by_contra hp2
    have htS := tStd_mem_slPi hK
    set t : L := e.symm (projOf _ ⟨tStd K, htS⟩) with ht
    have het : ((e t : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (tStd K) := by
      rw [ht, MulEquiv.apply_symm_apply, coe_projOf]
    have ht1 : (t : G) ≠ 1 := by
      intro h
      apply tStd_ne_one hK hp2
      have h1 : ProjGenLinGroup.mk (tStd K) = 1 := by
        rw [← het, show t = 1 from Subtype.ext h, map_one]
        rfl
      have hs := mk_eq_one_iff_mem_statedScalars.mp h1
      obtain ⟨c, hc⟩ := hs
      have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) hc
      have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) hc
      simp only [coe_tStd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h00 h22
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at h00 h22
      apply Units.ext
      rw [Units.val_one]
      ext i j
      have hm1 : (-1 : K) = 1 := by rw [← h00, h22]
      fin_cases i <;> fin_cases j <;> simp [coe_tStd, hm1]
    have ht2 : (t : G) ^ 2 = 1 := by
      have : e t ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, het, ← map_pow, pow_two, tStd_sq, map_one]
        rfl)
      rw [← map_pow, map_eq_one_iff _ e.injective] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ x ∈ diagOrFrobP e σ, x * (t : G) = t * x := by
      rintro x (⟨D, hD, hDd⟩ | hx)
      · apply commute_of_slAct_eqP (e := e)
        apply Subtype.ext
        rw [hD.2, het, ← map_inv, ← map_mul, ← map_mul, tStd_commute_of_diag hDd,
          mul_inv_cancel_right]
      · rw [Set.mem_singleton_iff.mp hx]
        apply commute_of_slAct_eqP (e := e)
        rw [ht, MulEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [hσψ, coe_projOf, frobGL_tStd]
    have hle : E ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
      refine hEgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨k, rfl⟩
      have : x * (t : G) ^ k * x⁻¹ = (t : G) ^ k := by
        rw [(Commute.zpow_right (hcomm x hx) k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ k
    refine false_of_le_normalizer hG ?_ ?_ hE hE81 hle
    · intro h
      apply ht1
      have : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
      rw [h, Subgroup.mem_bot] at this
      exact this
    · intro g
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, zpow_natCast, ht2, _root_.one_zpow]
      rfl
  refine ⟨hp2, ?_⟩
  subst hp2
  cases π
  · rfl
  · exfalso
    have := hK.charP
    have hle : E ≤ Subgroup.normalizer (pullP e (rootGL K) : Set G) := by
      refine hEgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
      apply mem_normalizer_pullP
      intro m M hM hmM
      rcases hx with ⟨D, hD, hDd⟩ | hx
      · refine ⟨D * M * D⁻¹, Subgroup.mem_inf.mpr
          ⟨conj_mem_rootGL_of_diag hDd (Subgroup.mem_inf.mp hM).1, ?_⟩, ?_⟩
        · exact rootGL_le_slPi _ (conj_mem_rootGL_of_diag hDd (Subgroup.mem_inf.mp hM).1)
        · rw [hD.2, hmM, map_mul, map_mul, map_inv]
      · rw [Set.mem_singleton_iff.mp hx]
        have hMS := (Subgroup.mem_inf.mp hM).2
        have hm : m = projOf _ ⟨M, hMS⟩ := Subtype.ext (by rw [hmM, coe_projOf])
        refine ⟨frobGL ψ M, Subgroup.mem_inf.mpr
          ⟨frobGL_mem_rootGL ψ (Subgroup.mem_inf.mp hM).1, frobGL_mem_slPi hK ψ hMS⟩, ?_⟩
        rw [hm, hσψ]
    have hM : (⟨transvection 0 1 1, transvection 0 1 (-1), by
        rw [transvection_mul_transvection_same _ _ (by decide), add_neg_cancel,
          transvection_zero],
        by rw [transvection_mul_transvection_same _ _ (by decide), neg_add_cancel,
          transvection_zero]⟩ : GL (Fin 3) K) ∈ rootGL K := ⟨1, rfl⟩
    have hMs : (⟨transvection 0 1 1, transvection 0 1 (-1), by
        rw [transvection_mul_transvection_same _ _ (by decide), add_neg_cancel,
          transvection_zero],
        by rw [transvection_mul_transvection_same _ _ (by decide), neg_add_cancel,
          transvection_zero]⟩ : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
      rintro ⟨c, hc⟩
      have h01 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) hc
      simp [transvection, GeneralLinearGroup.coe_scalar] at h01
    refine false_of_le_normalizer hG (pullP_ne_bot hM (rootGL_le_slPi _ hM) hMs) ?_ hE hE81 hle
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow]
    exact pullP_sq (fun M hM => rootGL_sq hM) g.2

end RankFourP

section Rank81

theorem nine_dvd_qSubPi_cube {π : Bool} {q₀ : ℕ} (hq₀ : ModThree π q₀) :
    9 ∣ qSubPi π (q₀ ^ 3) := by
  have hr : q₀ ^ 3 % 9 = (q₀ % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  have h9 : q₀ % 9 < 9 := Nat.mod_lt _ (by norm_num)
  cases π
  · change q₀ % 3 = 2 at hq₀
    change 9 ∣ q₀ ^ 3 + 1
    have : q₀ % 9 = 2 ∨ q₀ % 9 = 5 ∨ q₀ % 9 = 8 := by omega
    rcases this with h | h | h <;> rw [h] at hr <;> norm_num at hr <;> omega
  · change q₀ % 3 = 1 at hq₀
    change 9 ∣ q₀ ^ 3 - 1
    have : q₀ % 9 = 1 ∨ q₀ % 9 = 4 ∨ q₀ % 9 = 7 := by omega
    rcases this with h | h | h <;> rw [h] at hr <;> norm_num at hr <;> omega

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_cube_root_tau (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) :
    ∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K, ((μ : Kˣ) : K) ^ 3 = τ := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτu : Units.mk0 τ hτ0 ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    refine cube_root_mem_qSubPi hq ?_
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity (qSubPi π (p ^ f)) K)
  have hord : orderOf g = qSubPi π (p ^ f) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_rootsOfUnity_qSubPi hK hq]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨Units.mk0 τ hτ0, hτu⟩)
  have hτ3u : (⟨Units.mk0 τ hτ0, hτu⟩ : rootsOfUnity (qSubPi π (p ^ f)) K) ^ 3 = 1 :=
    Subtype.ext (Units.ext (by simp [hτ]))
  have h3 : g ^ (3 * k) = 1 := by
    rw [mul_comm, _root_.zpow_mul, hk, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
      hτ3u]
  have hdvd : (qSubPi π (p ^ f) : ℤ) ∣ 3 * k := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  have h9z : (9 : ℤ) ∣ (qSubPi π (p ^ f) : ℤ) := by exact_mod_cast h9
  obtain ⟨j, rfl⟩ : (3 : ℤ) ∣ k := by
    have h9' : (9 : ℤ) ∣ 3 * k := h9z.trans hdvd
    omega
  refine ⟨((g ^ j : rootsOfUnity (qSubPi π (p ^ f)) K) : Kˣ), (g ^ j).2, ?_⟩
  have h2 : ((g : Kˣ) ^ (3 * j)) = Units.mk0 τ hτ0 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  have h3' : ((g : Kˣ) ^ j) ^ (3 : ℕ) = Units.mk0 τ hτ0 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, show j * ((3 : ℕ) : ℤ) = 3 * j by push_cast; ring, h2]
  rw [Subgroup.coe_zpow, ← Units.val_pow_eq_pow_val, h3', Units.val_mk0]

end Rank81

section FieldRank

variable {K : Type} [Field K]

theorem diagUnits_one : diagUnits (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  rw [Units.val_one, coe_diagUnits, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagUnits_inv (a b c : Kˣ) : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, diagUnits_one]

theorem eq_of_diagUnits_mem_statedScalars {a b c : Kˣ}
    (h : diagUnits a b c ∈ StatedScalars (Fin 3) K) : a = c ∧ b = c := by
  obtain ⟨t, ht⟩ := h
  have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have h11 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 1 1) ht
  have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h00 h11 h22
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h00 h11 h22
  exact ⟨Units.ext (h00.symm.trans h22), Units.ext (h11.symm.trans h22)⟩

theorem mk_diagE_ne_pow {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (n : ℕ) :
    ProjGenLinGroup.mk (diagE (Units.mk0 τ (by rintro rfl; simp at hτ))) ≠
      ProjGenLinGroup.mk (diagTau hτ) ^ n := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ,
    Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, ← hτu, h, Units.val_one])
  have hτu2 : τu ^ 2 ≠ 1 := by
    intro h
    apply hτu1
    calc τu = τu ^ 3 * (τu ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτu3, h, inv_one, one_mul]
  intro h
  rw [← map_pow, diagTau_eq_diagUnits hτ hτ0] at h
  have hpow : ∀ m : ℕ, diagUnits τu (τu ^ 2) 1 ^ m = diagUnits (τu ^ m) (τu ^ (2 * m)) 1 := by
    intro m
    induction m with
    | zero => simp [diagUnits_one]
    | succ m ih =>
      rw [pow_succ, ih, diagUnits_mul]
      congr 1 <;> group
  rw [hpow] at h
  have hs : (diagUnits (τu ^ n) (τu ^ (2 * n)) 1)⁻¹ * diagE τu ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h, inv_mul_cancel]
  rw [diagUnits_inv, diagE, diagUnits_mul, inv_one, one_mul] at hs
  obtain ⟨h0, h1⟩ := eq_of_diagUnits_mem_statedScalars hs
  rw [mul_one] at h1
  rw [inv_mul_eq_one] at h0
  have h1' : τu ^ (2 * n) = 1 := inv_eq_one.mp h1
  have : τu ^ 2 = 1 := by
    calc τu ^ 2 = (τu ^ n) ^ 2 := by rw [h0]
      _ = τu ^ (2 * n) := by rw [← pow_mul, mul_comm]
      _ = 1 := h1'
  exact hτu2 this

end FieldRank

section FieldRankG

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem two_and_unitary_of_field (hG : SectionFourHyp G) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {σ : G}
    (hσ3 : σ ^ 3 = 1) (hσLC : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s))
    {c : G} (hc3 : orderOf c = 3) (hcC : c ∈ Subgroup.centralizer (L : Set G))
    (hcσ : c * σ = σ * c) : p = 2 ∧ π = false := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτuT : τu ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    refine cube_root_mem_qSubPi hq ?_
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hq₀ : ModThree π (p ^ f₀) :=
    modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hψτ : ψ τ = τ := by
    have hφτ : φ τ = τ := frob_eq_of_cube hq₀ hφ hτ
    rcases hψ with rfl | rfl
    · exact hφτ
    · rw [ringAut_sq_apply, hφτ, hφτ]
  have h9 : 9 ∣ qSubPi π (p ^ f) := by
    have := nine_dvd_qSubPi_cube hq₀
    rwa [← pow_mul, mul_comm, ← hf] at this
  obtain ⟨μ, hμT, hμ3⟩ := exists_cube_root_tau hK hq h9 hτ
  have hdS : diagTau hτ ∈ slPi π 3 (p ^ f) K := diagTau_mem_slPi hπ hq' hτ
  set D₂ : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * diagE τu with hD₂
  have hD₂S : D₂ ∈ slPi π 3 (p ^ f) K := by
    rw [mem_slPi_iff hπ]
    refine ⟨mul_mem ((scalar_mem_glPi_iff hK _).mpr (inv_mem hμT))
      (diagUnits_mem_glPi hK hτuT (one_mem _) (one_mem _)), ?_⟩
    rw [hD₂, Units.val_mul, Matrix.det_mul, det_scalar_three, coe_diagE, det_diagonal,
      Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one, Units.val_inv_eq_inv_val, inv_pow, hμ3, hτu, Units.val_mk0]
    exact inv_mul_cancel₀ hτ0
  set x₁ : L := e.symm (projOf _ ⟨diagTau hτ, hdS⟩) with hx₁
  set x₂ : L := e.symm (projOf _ ⟨D₂, hD₂S⟩) with hx₂
  have he₁ : ((e x₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (diagTau hτ) := by rw [hx₁, MulEquiv.apply_symm_apply, coe_projOf]
  have he₂ : ((e x₂ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk D₂ := by rw [hx₂, MulEquiv.apply_symm_apply, coe_projOf]
  have hmkD₂ : ProjGenLinGroup.mk D₂ = ProjGenLinGroup.mk (diagE τu) := by
    rw [hD₂, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]
  have hx₁P : IsPGLAtP e (x₁ : G) (diagTau hτ) := isPGLAtP_of_mem e hπ x₁.2 hdS he₁
  have hx₂P : IsPGLAtP e (x₂ : G) D₂ := isPGLAtP_of_mem e hπ x₂.2 hD₂S he₂
  have hφinj : Function.Injective fun x : L =>
      ((e x : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) :=
    Subtype.val_injective.comp e.injective
  have hcoe_mul : ∀ x y : L, ((e (x * y) : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (e x : ProjGenLinGroup (Fin 3) K) * (e y) := fun x y => by
    rw [map_mul, Subgroup.coe_mul]
  have hx₁3 : (x₁ : G) ^ 3 = 1 := by
    have : x₁ ^ 3 = 1 := hφinj (by
      change ((e (x₁ ^ 3) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((e 1 : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)
      rw [map_pow, Subgroup.coe_pow, he₁, ← map_pow, diagTau_pow_three hτ, map_one, map_one]
      rfl)
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hx₂3 : (x₂ : G) ^ 3 = 1 := by
    have : x₂ ^ 3 = 1 := hφinj (by
      change ((e (x₂ ^ 3) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((e 1 : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)
      rw [map_pow, Subgroup.coe_pow, he₂, hmkD₂, ← map_pow, map_one]
      have : diagE τu ^ 3 = 1 := by
        have hτu3 : τu * (τu * τu) = 1 := by
          rw [← pow_two, ← pow_succ']
          exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ,
            Units.val_one])
        rw [diagE, pow_three, diagUnits_mul, diagUnits_mul, hτu3, mul_one, mul_one,
          diagUnits_one]
      rw [this, map_one]
      rfl)
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hcx : ∀ x : L, (x : G) * c = c * x := fun x =>
    Subgroup.mem_centralizer_iff.mp hcC x x.2
  have hx₁x₂ : (x₁ : G) * x₂ = x₂ * x₁ := by
    have : x₁ * x₂ = x₂ * x₁ := hφinj (by
      simp only
      rw [hcoe_mul, hcoe_mul, he₁, he₂, hmkD₂, ← map_mul, ← map_mul, diagTau_eq_diagUnits hτ hτ0,
        diagE, diagUnits_mul, diagUnits_mul, mul_comm (Units.mk0 τ hτ0), mul_comm (_ ^ 2)])
    exact congrArg Subtype.val this
  have hσx₁ : σ * (x₁ : G) = x₁ * σ := by
    apply commute_of_slAct_eqP (e := e)
    rw [hx₁, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hσψ, coe_projOf, frobGL_diagTau hτ hψτ]
  have hσx₂ : σ * (x₂ : G) = x₂ * σ := by
    apply commute_of_slAct_eqP (e := e)
    rw [hx₂, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hσψ, coe_projOf]
    change ProjGenLinGroup.mk (frobGL ψ D₂) = ProjGenLinGroup.mk D₂
    rw [hmkD₂, hD₂, map_mul, frobGL_scalar, map_mul,
      mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]
    congr 1
    apply Units.ext
    rw [coe_frobGL, coe_diagE, diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp [hτu, hψτ]
  have hx₁1 : (x₁ : G) ≠ 1 := by
    intro h
    apply diagTau_not_mem_statedScalars hτ hτ1
    rw [← mk_eq_one_iff_mem_statedScalars, ← he₁, show x₁ = 1 from Subtype.ext h, map_one]
    rfl
  have hx₂n : ∀ n : ℕ, (x₂ : G) ≠ (x₁ : G) ^ n := by
    intro n h
    apply mk_diagE_ne_pow hτ hτ1 n
    have h1 : x₂ = x₁ ^ n := Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
    rw [← hmkD₂, ← he₂, ← he₁, h1, map_pow, Subgroup.coe_pow]
  set E₁ := Subgroup.zpowers c with hE₁
  set E₂ := E₁ ⊔ Subgroup.zpowers (x₁ : G) with hE₂
  set E₃ := E₂ ⊔ Subgroup.zpowers (x₂ : G) with hE₃
  set E₄ := E₃ ⊔ Subgroup.zpowers σ with hE₄
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcomm₁ : ∀ x : G, x * c = c * x → ∀ a ∈ E₁, a * x = x * a := by
    rintro x hx _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute c x from hx.symm) k)).eq
  have hcommz : ∀ x y : G, x * y = y * x → ∀ a ∈ Subgroup.zpowers y, a * x = x * a := by
    rintro x y hxy _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute y x from hxy.symm) k)).eq
  have hE₁e : CFSG.Assembly.IsElemAbelian 3 E₁ := by
    have := isElemAbelian_sup_zpowers (isElemAbelian_bot (G := G)) hc3' (fun a ha => by
      rw [Subgroup.mem_bot.mp ha, one_mul, mul_one])
    rwa [bot_sup_eq] at this
  have hE₂e : CFSG.Assembly.IsElemAbelian 3 E₂ :=
    isElemAbelian_sup_zpowers hE₁e hx₁3 (hcomm₁ _ (hcx x₁))
  have hx₂E₂ : ∀ a ∈ E₂, a * (x₂ : G) = x₂ * a :=
    commute_sup_of_commute (hcomm₁ _ (hcx x₂)) (hcommz _ _ hx₁x₂.symm)
  have hE₃e : CFSG.Assembly.IsElemAbelian 3 E₃ := isElemAbelian_sup_zpowers hE₂e hx₂3 hx₂E₂
  have hσE₃ : ∀ a ∈ E₃, a * σ = σ * a :=
    commute_sup_of_commute (commute_sup_of_commute (hcomm₁ σ hcσ.symm)
      (hcommz _ _ hσx₁)) (hcommz _ _ hσx₂)
  have hE₄e : CFSG.Assembly.IsElemAbelian 3 E₄ := isElemAbelian_sup_zpowers hE₃e hσ3 hσE₃
  have hE₁C : E₁ ≤ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hcC
  have hcard₁ : Nat.card E₁ = 3 := by rw [Nat.card_zpowers, hc3]
  have hx₁E₁ : (x₁ : G) ∉ E₁ := fun h =>
    hx₁1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨x₁.2, hE₁C h⟩))
  have hcard₂ : Nat.card E₂ = 9 := by
    rw [card_sup_zpowers_of_not_mem hx₁3 (hcomm₁ _ (hcx x₁)) hx₁E₁, hcard₁]
  have hx₂E₂' : (x₂ : G) ∉ E₂ := by
    intro h
    have hcx₁ : c * x₁ = x₁ * c := (hcx x₁).symm
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup hcx₁ h
    have hci : c ^ i = x₂ * ((x₁ : G) ^ j)⁻¹ := by rw [hij]; group
    have hciL : c ^ i ∈ L := by rw [hci]; exact mul_mem x₂.2 (inv_mem (zpow_mem x₁.2 j))
    have hci1 : c ^ i = 1 := Subgroup.mem_bot.mp
      (hLC ▸ Subgroup.mem_inf.mpr ⟨hciL, zpow_mem hcC i⟩)
    rw [hci1, one_mul, zpow_emod_three hx₁3 j] at hij
    have hj : (j % 3).toNat < 3 := by omega
    apply hx₂n (j % 3).toNat
    rw [hij, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))]
  have hcard₃ : Nat.card E₃ = 27 := by
    rw [card_sup_zpowers_of_not_mem hx₂3 hx₂E₂ hx₂E₂', hcard₂]
  have hE₃LC : E₃ ≤ L ⊔ Subgroup.centralizer (L : Set G) :=
    sup_le (sup_le (hE₁C.trans le_sup_right) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left
      x₁.2))) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left x₂.2))
  have hcard₄ : Nat.card E₄ = 81 := by
    rw [card_sup_zpowers_of_not_mem hσ3 hσE₃ (fun h => hσLC (hE₃LC h)), hcard₃]
  have hgen : E₄ ≤ Subgroup.closure (diagOrFrobP e σ) := by
    have hdiag : ∀ x : G, ∀ D : GL (Fin 3) K, IsPGLAtP e x D →
        (∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0) →
          Subgroup.zpowers x ≤ Subgroup.closure (diagOrFrobP e σ) := fun x D hD hDd =>
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl ⟨D, hD, hDd⟩))
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hdiag c 1 (isPGLAtP_of_mem_centralizer e hcC) (fun i j hij => by
        rw [Units.val_one, Matrix.one_apply_ne hij])
    · exact hdiag _ _ hx₁P (diagTau_offdiag hτ)
    · refine hdiag _ _ hx₂P fun i j hij => ?_
      rw [hD₂, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagE, Matrix.scalar_apply,
        diagonal_mul_diagonal, diagonal_apply_ne _ hij]
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl))
  exact two_and_unitary_of_rank_fourP hG hK e hσψ hE₄e hcard₄ hgen

end FieldRankG

end CFSG.RankThree.PartTwo.Sec4
