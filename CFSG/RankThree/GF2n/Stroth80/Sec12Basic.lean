module

public import CFSG.RankThree.GF2n.Tim79Width1
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic
public import CFSG.RankThree.GF2n.Stroth80.InvolutionDim
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.exists_width (H : StrothHyp M Q Z) : ∃ n : ℕ, Width Q Z n := by
  obtain ⟨K, _, _, γ, M₀, hK, -, -, -, ⟨S₁, S₂, hS, hS₁, hS₂⟩, -⟩ := stroth_globalModel H
  haveI : Module.Finite K M₀.E := M₀.fin
  have h1 := Tim79.QuadModel.two_mul_finrank_le_of_totallySingular M₀ S₁ hS₁
  have h2 := Tim79.QuadModel.two_mul_finrank_le_of_totallySingular M₀ S₂ hS₂
  have hsum := Submodule.finrank_add_eq_of_isCompl hS
  refine ⟨Module.finrank K S₁, ?_⟩
  have hc : Nat.card Q = Nat.card Z * Nat.card (M₀.img Q) := M₀.card_eq le_rfl H.Z_normal.1
  have himg : Nat.card (M₀.img Q) = Nat.card M₀.E := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun v => ?_)
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj v
    exact M₀.pi_mem_img hx hx
  have hE : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E := Module.natCard_eq_pow_finrank
  have hd : Module.finrank K M₀.E = 2 * Module.finrank K S₁ := by omega
  unfold Width
  rw [hc, himg, hE, hK, hd, pow_succ, mul_comm]

theorem StrothHyp.isL3Type_of_width_one (H : StrothHyp M Q Z) (hw : Width Q Z 1) :
    ∃ n : ℕ, Nat.card Z = 2 ^ n ∧ Tim79.IsL3Type n Q := by
  obtain ⟨n, hn, hcp⟩ := H.toHyp79.isCentralProductOfL3_of_card (by simpa [Width] using hw)
  obtain ⟨-, D, hDQ, hDL, -, -, hDsup⟩ := hcp
  refine ⟨n, hn, ?_⟩
  have hD0 : D 0 = Q := by
    rw [← hDsup]
    exact (iSup_unique (f := D)).symm
  rw [← hD0]
  exact hDL 0

theorem Ctx.exists_Rt_ne_of_not_TI (hc : Ctx M Q Z B) (hnt : ¬ IsTIMod M Q (LB M Q B)) :
    ∃ t ∈ LB M Q B, t ∉ Q ∧ Rt M (LB M Q B) t ≠ LB M Q B := by
  unfold IsTIMod at hnt
  push Not at hnt
  obtain ⟨m, hm, h1, h2⟩ := hnt
  have hQL : Q ≤ LB M Q B ⊓ conjSubgroup m (LB M Q B) := by
    refine le_inf sec39_Q_le_LB ?_
    have h := Subgroup.map_mono (f := (MulAut.conj m).toMonoidHom)
      (sec39_Q_le_LB (M := M) (Q := Q) (B := B))
    rwa [show Subgroup.map (MulAut.conj m).toMonoidHom Q = conjSubgroup m Q from rfl,
      hc.conj_Q_eq hm] at h
  obtain ⟨t, htL, htQ⟩ : ∃ t ∈ LB M Q B ⊓ conjSubgroup m (LB M Q B), t ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact h1 (le_antisymm (fun x hx => hcon x hx) hQL)
  refine ⟨t, htL.1, htQ, fun heq => h2 ?_⟩
  have hle : conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t :=
    le_iSup₂_of_le m hm (le_iSup_of_le htL.2 le_rfl)
  rw [heq] at hle
  have hcard : conjSubgroup m (LB M Q B) = LB M Q B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  rw [hcard, inf_idem]

theorem IsSLModel.congr {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLModel n q X) : IsSLModel n q Y := by
  obtain ⟨K, f, fin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, ⟨e.symm.trans e'⟩⟩

theorem IsPSLModel.congr {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPSLModel n q X) : IsPSLModel n q Y := by
  obtain ⟨K, f, fin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, ⟨e.symm.trans e'⟩⟩

theorem IsPSUModel.congr {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPSUModel n q X) : IsPSUModel n q Y := by
  obtain ⟨K, f, fin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, ⟨e.symm.trans e'⟩⟩

theorem IsOmegaPlus.congr {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsOmegaPlus n q X) : IsOmegaPlus n q Y := by
  obtain ⟨K, f, fin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, ⟨e.symm.trans e'⟩⟩

theorem IsOmegaMinus.congr {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsOmegaMinus n q X) : IsOmegaMinus n q Y := by
  obtain ⟨K, f, fin, hK, b, c, hbc, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, b, c, hbc, ⟨e.symm.trans e'⟩⟩

theorem quotMulEquivBar [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) :
    ∃ _ : (Q.subgroupOf S).Normal, Nonempty (↥S ⧸ Q.subgroupOf S ≃* ↥(bar M Q S)) := by
  let f : ↥S →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)
  have hker : f.ker = Q.subgroupOf S := by
    ext s
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hrange : f.range = bar M Q S := by
    simp only [f, bar, MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI hn : (Q.subgroupOf S).Normal := by
    rw [← hker]
    exact f.normal_ker
  refine ⟨hn, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)

theorem quotSat_of_bar {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) [(Q.subgroupOf M).Normal]
    {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) (h : P ↥(bar M Q S)) : QuotSat S Q P := by
  obtain ⟨hn, ⟨e⟩⟩ := quotMulEquivBar (M := M) hQS hSM
  exact ⟨hn, hP _ _ e.symm h⟩

theorem OmegaPlusNat.quotSat {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : OmegaPlusNat hc t m) :
    QuotSat (Rt M (LB M Q B) t) (hc.CN t) (IsOmegaPlus m (Nat.card Z)) := by
  obtain ⟨K, fK, finK, hK, φ, hrange, hker, -⟩ := h
  haveI hn : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    rw [← hker]
    exact φ.normal_ker
  refine ⟨hn, K, fK, finK, hK, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)

theorem OmegaMinusNat.quotSat {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : OmegaMinusNat hc t m) :
    QuotSat (Rt M (LB M Q B) t) (hc.CN t) (IsOmegaMinus m (Nat.card Z)) := by
  obtain ⟨K, fK, finK, hK, b, c, hbc, φ, hrange, hker, -⟩ := h
  haveI hn : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    rw [← hker]
    exact φ.normal_ker
  refine ⟨hn, K, fK, finK, hK, b, c, hbc, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)

omit [Finite G] in
theorem quotProd (Q A B S : Subgroup G) [(Q.subgroupOf S).Normal] [(Q.subgroupOf A).Normal]
    [(Q.subgroupOf B).Normal] (hQA : Q ≤ A) (hQB : Q ≤ B) (hAB : A ⊓ B = Q) (hS : A ⊔ B = S)
    (hc : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Q) :
    Nonempty (↥S ⧸ Q.subgroupOf S ≃* (↥A ⧸ Q.subgroupOf A) × (↥B ⧸ Q.subgroupOf B)) := by
  have hAS : A ≤ S := hS ▸ le_sup_left
  have hBS : B ≤ S := hS ▸ le_sup_right
  let fA : ↥A →* ↥S ⧸ Q.subgroupOf S :=
    (QuotientGroup.mk' (Q.subgroupOf S)).comp (Subgroup.inclusion hAS)
  let fB : ↥B →* ↥S ⧸ Q.subgroupOf S :=
    (QuotientGroup.mk' (Q.subgroupOf S)).comp (Subgroup.inclusion hBS)
  have hkA : Q.subgroupOf A ≤ fA.ker := by
    intro x hx
    simp only [fA, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact hx
  have hkB : Q.subgroupOf B ≤ fB.ker := by
    intro x hx
    simp only [fB, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact hx
  let gA : ↥A ⧸ Q.subgroupOf A →* ↥S ⧸ Q.subgroupOf S := QuotientGroup.lift _ fA hkA
  let gB : ↥B ⧸ Q.subgroupOf B →* ↥S ⧸ Q.subgroupOf S := QuotientGroup.lift _ fB hkB
  have hcomm : ∀ (x : ↥A ⧸ Q.subgroupOf A) (y : ↥B ⧸ Q.subgroupOf B), Commute (gA x) (gB y) := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        show QuotientGroup.mk' (Q.subgroupOf S) (Subgroup.inclusion hAS a) *
            QuotientGroup.mk' (Q.subgroupOf S) (Subgroup.inclusion hBS b) =
          QuotientGroup.mk' (Q.subgroupOf S) (Subgroup.inclusion hBS b) *
            QuotientGroup.mk' (Q.subgroupOf S) (Subgroup.inclusion hAS a)
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h := hc (a : G)⁻¹ (A.inv_mem a.2) (b : G)⁻¹ (B.inv_mem b.2)
        have h' := Q.inv_mem h
        convert h' using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
          commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  let Θ := MonoidHom.noncommCoprod gA gB hcomm
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        have h1 : QuotientGroup.mk' (Q.subgroupOf S) (Subgroup.inclusion hAS a *
            Subgroup.inclusion hBS b) = 1 := by
          rw [map_mul]
          exact h
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h1
        have haB : (a : G) ∈ B := by
          have := B.mul_mem (hQB h1) (B.inv_mem b.2)
          simpa using this
        have haQ : (a : G) ∈ Q := by
          rw [← hAB]
          exact ⟨a.2, haB⟩
        have hbQ : (b : G) ∈ Q := by
          have := Q.mul_mem (Q.inv_mem haQ) h1
          simpa using this
        have e1 : (QuotientGroup.mk a : ↥A ⧸ Q.subgroupOf A) = 1 :=
          (QuotientGroup.eq_one_iff a).mpr haQ
        have e2 : (QuotientGroup.mk b : ↥B ⧸ Q.subgroupOf B) = 1 :=
          (QuotientGroup.eq_one_iff b).mpr hbQ
        rw [e1, e2]
        rfl
  have hsurj : Function.Surjective Θ := by
    have hR : (Θ.range.comap (QuotientGroup.mk' (Q.subgroupOf S))) = ⊤ := by
      have hA' : A.subgroupOf S ≤ Θ.range.comap (QuotientGroup.mk' (Q.subgroupOf S)) := by
        intro s hs
        refine ⟨(QuotientGroup.mk (⟨s, hs⟩ : ↥A), 1), ?_⟩
        show gA (QuotientGroup.mk ⟨s, hs⟩) * gB 1 = _
        rw [map_one, mul_one]
        rfl
      have hB' : B.subgroupOf S ≤ Θ.range.comap (QuotientGroup.mk' (Q.subgroupOf S)) := by
        intro s hs
        refine ⟨(1, QuotientGroup.mk (⟨s, hs⟩ : ↥B)), ?_⟩
        show gA 1 * gB (QuotientGroup.mk ⟨s, hs⟩) = _
        rw [map_one, one_mul]
        rfl
      have hsup : A.subgroupOf S ⊔ B.subgroupOf S = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hAS hBS, hS]
        exact Subgroup.subgroupOf_self S
      exact top_le_iff.mp (hsup ▸ sup_le hA' hB')
    intro z
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf S) z
    have : s ∈ Θ.range.comap (QuotientGroup.mk' (Q.subgroupOf S)) := by
      rw [hR]
      exact Subgroup.mem_top s
    exact this
  exact ⟨(MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩).symm⟩

theorem Ctx.LB_le_H0' (hc : Ctx M Q Z B) : LB M Q B ≤ H0 M Z := fun l hl =>
  ⟨hc.LB_le_M hl, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (mul_inv_eq_iff_eq_mul.mp (hc.LB_centralizes_Z hl z hz)).symm⟩

theorem Ctx.isPGroup_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    IsPGroup 2 ↥(LB M Q B) := by
  obtain ⟨k, k', hZk, -⟩ := hc.hyp.cp
  have hcard := (stroth_3_5 h34 hc hw hn hno hgen).2.2.1
  refine IsPGroup.of_card (n := k * ((2 * n + 1) + (n - 1))) ?_
  unfold Width at hw
  rw [hcard, hw, hZk, ← pow_add, ← pow_mul]

theorem stroth_odd (h34 : Stroth34Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
      (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
      Odd (Nat.card ↥(Subgroup.centralizer (bar M Q (Lgen M (LB M Q B)) : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z))) := by
  intro G _ _ M Q Z B _ hc n hw hn hno hgen
  classical
  by_contra hodd
  set T := Lgen M (LB M Q B) with hT
  have hTM : T ≤ M := Lgen_le hc.LB_le_M
  have heven : Even (Nat.card ↥(Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓
      bar M Q (H0 M Z))) := Nat.not_odd_iff_even.mp hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  obtain ⟨y, hyH, hya⟩ := a.2.2
  have hc'H : (y : G) ∈ H0 M Z := hyH
  have ha2 : (a : Mbar M Q) ^ 2 = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha] at this
    exact congrArg Subtype.val this
  have hsq : (y : G) ^ 2 ∈ Q := by
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (y ^ 2) = 1 := by
      rw [map_pow, hya]
      exact ha2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcomm : ∀ s ∈ T, ⁅(y : G), s⁆ ∈ Q := by
    intro s hs
    have hsM : s ∈ M := hTM hs
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q T :=
      ⟨⟨s, hsM⟩, hs, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp a.2.1 _ hmem
    rw [← hya] at h1
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) ⁅y, (⟨s, hsM⟩ : ↥M)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨n0, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp h
  set c0 : ↥(H0 M Z) := ⟨y, hc'H⟩ with hc0
  have hT0sq : φ c0 * φ c0 = 1 := by
    rw [← map_mul]
    exact (hφker _).mpr (by simpa [pow_two] using hsq)
  have hrk := Tim79.QuadModel.range_le_ker_of_sq_eq_one M₀
    (T := (φ c0 : M₀.E →ₗ[GaloisField 2 n0] M₀.E))
    (by
      ext e
      have := congrArg (fun g : M₀.E ≃ₗ[GaloisField 2 n0] M₀.E => g e) hT0sq
      simpa using this)
  have hfixAll : ∀ e : M₀.E, φ c0 e = e := by
    let F : Submodule (GaloisField 2 n0) M₀.E :=
      LinearMap.ker ((φ c0 : M₀.E →ₗ[GaloisField 2 n0] M₀.E) - LinearMap.id)
    have hmemF : ∀ v, v ∈ F ↔ φ c0 v = v := by
      intro v
      simp [F, sub_eq_zero]
    obtain ⟨b₀, hb₀, -⟩ := hc.dictB h
    have hF0 : F ≠ ⊥ := by
      intro hF
      have hr : LinearMap.range ((φ c0 : M₀.E →ₗ[GaloisField 2 n0] M₀.E) - LinearMap.id) = ⊥ := by
        rw [eq_bot_iff]
        exact hrk.trans hF.le
      have hz : ((φ c0 : M₀.E →ₗ[GaloisField 2 n0] M₀.E) - LinearMap.id) = 0 :=
        LinearMap.range_eq_bot.mp hr
      apply hb₀
      have hbF : b₀ ∈ F := by
        simp [F, hz]
      rw [hF] at hbF
      exact (Submodule.mem_bot _).mp hbF
    have hA : ∀ m ∈ M, ∀ u ∈ conjSubgroup m B, M₀.π u ∈ F := by
      intro m hm u hu
      have hcm : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
      have hno' := hc.noA2_conj hno hm
      have hgen' := hgen.conj_of_mem hm
      have h35 := (stroth_3_5 h34 hcm hw hn hno' hgen').2.1
      have hLm : LB M Q (conjSubgroup m B) ≤ H0 M Z := hcm.LB_le_H0'
      have hLT : LB M Q (conjSubgroup m B) ≤ T := by
        rw [hc.LB_conj hm]
        exact le_iSup₂_of_le m hm le_rfl
      let Λ : Subgroup (M₀.E ≃ₗ[GaloisField 2 n0] M₀.E) :=
        (φ.comp (Subgroup.inclusion hLm)).range
      have hΛp : IsPGroup 2 Λ :=
        (hcm.isPGroup_LB h34 hw hn hno' hgen').of_surjective
          (φ.comp (Subgroup.inclusion hLm)).rangeRestrict
          (MonoidHom.rangeRestrict_surjective _)
      have hΛF : ∀ g ∈ Λ, ∀ v ∈ F, g v ∈ F := by
        rintro _ ⟨l, rfl⟩ v hv
        have hlT : (l : G) ∈ T := hLT l.2
        have h1 : ⁅φ c0, φ (Subgroup.inclusion hLm l)⁆ = 1 := by
          rw [← map_commutatorElement]
          refine (hφker _).mpr ?_
          exact hcomm l hlT
        have h2 : φ c0 * φ (Subgroup.inclusion hLm l) = φ (Subgroup.inclusion hLm l) * φ c0 :=
          commutatorElement_eq_one_iff_mul_comm.mp h1
        rw [hmemF] at hv ⊢
        have h3 := congrArg (fun g : M₀.E ≃ₗ[GaloisField 2 n0] M₀.E => g v) h2
        simp only [LinearEquiv.mul_apply] at h3
        have key : φ c0 (φ (Subgroup.inclusion hLm l) v) = φ (Subgroup.inclusion hLm l) v := by
          rw [h3, hv]
        exact key
      haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 n0)
      obtain ⟨f, hfF, hf0, hfix⟩ := exists_fixed_vector_of_isPGroup Λ hΛp F hΛF hF0
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj f
      have hxC : x ∈ CQt Q Z (LB M Q (conjSubgroup m B)) := by
        refine ⟨hxQ, fun l hl => ?_⟩
        have hmem : φ (Subgroup.inclusion hLm ⟨l, hl⟩) ∈ Λ := ⟨⟨l, hl⟩, rfl⟩
        have h1 := hfix _ hmem
        rw [← hφπ _ x hxQ] at h1
        exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hcm.LB_le_M hl)) x).mp hxQ)).mpr h1
      rw [h35] at hxC
      obtain ⟨b, hb0, -, hB, -, -⟩ := hcm.dictB h
      have hle' : conjSubgroup m B ⊔ Z ≤ M₀.lift (M₀.img (conjSubgroup m B)) := sup_le
        (fun u hu => ⟨hcm.le hu, M₀.pi_mem_img hu (hcm.le hu)⟩)
        (fun z hz => ⟨hc.Z_le_Q hz, by
          rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]
          exact AddSubgroup.zero_mem _⟩)
      obtain ⟨s, hs⟩ := (hB _).mp (hle' hxC).2
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hf0 (by rw [hs, zero_smul])
      have hbF : b ∈ F := by
        have := F.smul_mem s⁻¹ hfF
        rwa [hs, smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
      obtain ⟨s', hs'⟩ := (hB _).mp (M₀.pi_mem_img hu (hcm.le hu))
      rw [hs']
      exact F.smul_mem s' hbF
    have hQle : Q ≤ M₀.lift F.toAddSubgroup := by
      calc Q = ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := hgen
        _ ≤ M₀.lift F.toAddSubgroup := by
          refine iSup₂_le fun m hm u hu => ?_
          exact ⟨(hc.conj_of_mem hm).le hu, hA m hm u hu⟩
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    exact (hmemF _).mp (hQle hxQ).2
  have hc0Q : (c0 : G) ∈ Q := by
    refine (hφker c0).mp ?_
    ext e
    simpa using hfixAll e
  have h1a : (a : Mbar M Q) = 1 := by
    rw [← hya]
    exact (QuotientGroup.eq_one_iff y).mpr hc0Q
  have h1 : a = 1 := Subtype.ext h1a
  rw [h1, orderOf_one] at ha
  omega

end CFSG.RankThree.GF2n.Stroth80
