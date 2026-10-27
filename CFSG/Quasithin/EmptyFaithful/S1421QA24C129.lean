module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Gen3
public import CFSG.Quasithin.EmptyFaithful.S1421QA24Emb
public import CFSG.Quasithin.EmptyFaithful.S1421QA15H
public import CFSG.Quasithin.Background.C129Used
public import CFSG.Quasithin.Background.C2PushBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA24

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_le_of_no_normal_three {X : Type*} [Group X] {K N : Subgroup X} (hNK : N ≤ K)
    (hNn : N.Normal) (hN3 : IsPGroup 3 N)
    (h : ∀ N' : Subgroup ↥K, N'.Normal → IsPGroup 3 N' → N' = ⊥) : N = ⊥ := by
  have hn' : (N.subgroupOf K).Normal := hNn.subgroupOf K
  have hp' : IsPGroup 3 (N.subgroupOf K) :=
    hN3.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have h1 := h _ hn' hp'
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNK hn⟩ : ↥K) ∈ N.subgroupOf K := hn
  rw [h1, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

section Consumer

variable {M R H L : Subgroup G}

theorem isSylowTwoOf_sup_of_normalizes (hR2 : IsPGroup 2 R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (R ⊓ L) L) :
    IsSylowTwoOf R (L ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR2, fun P hPY hP2 hRP => ?_⟩
  intro p hp
  have hpY : p ∈ (↑(L ⊔ R) : Set G) := hPY hp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L R hRL] at hpY
  obtain ⟨l, hl, r, hr, rfl⟩ := hpY
  have hlP : l ∈ P := by
    have : l = (l * r) * r⁻¹ := by group
    rw [this]
    exact P.mul_mem hp (P.inv_mem (hRP hr))
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp hsyl).2.2 (P ⊓ L) inf_le_right
    hP2.to_inf_left (inf_le_inf_right _ hRP)
  exact R.mul_mem (hmax ⟨hlP, hl⟩).1 hr

theorem le_of_isBlock2_card_three_of_normalizes (hL : L ∈ cComp M) (hRM : R ≤ M)
    (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hO3 : ∀ N : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), N.Normal → IsPGroup 3 N → N = ⊥)
    (hsyl : IsSylowTwoOf R (L ⊔ R)) (hRH : R ≤ H) {r : ℕ} (Lb : Fin r → Subgroup G)
    (hLb : ∀ i, IsBlock2 (L ⊔ R) (Lb i) ∧ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3)
    (hprod : ∀ h ∈ L ⊔ R, ∃ m ∈ (L ⊔ R) ⊓ H, ∃ x : Fin r → G,
      (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod) : L ≤ H := by
  set Y : Subgroup G := L ⊔ R with hY
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := sup_le hLM hRM
  have hLY : L ≤ Y := le_sup_left
  have hLY' : L ∈ cComp Y := cComp_mem_of_le hL hLY hYM
  have hLsub : IsSubnormal L Y := subnormal_of_mem_cComp hLY'
  have hLn : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr (sup_le Subgroup.le_normalizer hRL)
  have hOR : pCoreOf 2 Y ≤ R := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hOY : pCoreOf 2 Y ≤ Y ⊓ H := le_inf (hOR.trans le_sup_right) (hOR.trans hRH)
  have hB3 : ∀ i, IsPGroup 3 (imageOTwoQuot Y (Lb i)) := by
    intro i
    obtain ⟨e⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot
      (IsBlock2.isSubnormal (hLb i).1)
    have hcard : Nat.card ↥(imageOTwoQuot Y (Lb i)) = 3 ^ 1 :=
      ((Nat.card_congr e.toEquiv).symm.trans (hLb i).2).trans (pow_one 3).symm
    exact IsPGroup.of_card hcard
  have hBsub : ∀ i, (imageOTwoQuot Y (Lb i)).IsSubnormal := fun i =>
    (hLb i).1.2.2.map (QuotientGroup.mk'_surjective _)
  have hx : ∀ x ∈ imageOTwoQuot Y L, ∃ m ∈ imageOTwoQuot Y (Y ⊓ H),
      ∃ b : Fin r → OTwoQuot Y, (∀ i, b i ∈ imageOTwoQuot Y (Lb i)) ∧
        x = m * (List.ofFn b).prod := by
    intro x hx
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨m, hm, xs, hxs, hlm⟩ := hprod l (hLY hlL)
    have hxsY : ∀ i, xs i ∈ Y := fun i => (hLb i).1.2.1 (hxs i)
    refine ⟨QuotientGroup.mk ⟨m, hm.1⟩, mem_imageOTwoQuot_iff.mpr ⟨m, hm.1, hm, rfl⟩,
      fun i => QuotientGroup.mk ⟨xs i, hxsY i⟩,
      fun i => mem_imageOTwoQuot_iff.mpr ⟨xs i, hxsY i, hxs i, rfl⟩, ?_⟩
    have h1 : (⟨l, hl⟩ : ↥Y) =
        ⟨m, hm.1⟩ * (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y)).prod := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      exact hlm
    rw [h1, QuotientGroup.mk_mul]
    congr 1
    have := map_list_prod (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))
      (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y))
    rw [List.map_ofFn] at this
    exact this
  obtain ⟨e⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hLsub
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL)
  have hQperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hKperf : Group.IsPerfect ↥(imageOTwoQuot Y L) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hKn : (imageOTwoQuot Y L).Normal :=
    hLn.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) (QuotientGroup.mk'_surjective _)
  have hK3 : ∀ N : Subgroup (OTwoQuot Y), N ≤ imageOTwoQuot Y L → N.Normal → IsPGroup 3 N →
      N = ⊥ := fun N hNK hNn hN3 =>
    eq_bot_of_le_of_no_normal_three hNK hNn hN3 (no_normal_three_of_mulEquiv e hO3)
  have hle := le_of_forall_eq_mul_prod_of_isPGroup_three_of_perfect hKperf hKn hK3
    (fun i => imageOTwoQuot Y (Lb i)) hB3 hBsub hx
  intro l hl
  have hlY : l ∈ Y := hLY hl
  exact (mem_of_mk_mem_imageOTwoQuot hOY
    (hle (mem_imageOTwoQuot_iff.mpr ⟨l, hlY, hl, rfl⟩) : (QuotientGroup.mk ⟨l, hlY⟩ : OTwoQuot Y) ∈
      imageOTwoQuot Y (Y ⊓ H))).2

end Consumer

section Final

variable {T M H K1 L M₁ : Subgroup G}

theorem core3HeOdd_false_of_isSylowTwoOf_rOf
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (c : S1421.Core3Ctx T M H K1 L M₁)
    (hc : CharTwo (S1421.g0Of T M H K1))
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (S1421.rOf T M K1 ⊓ L) L) : False := by
  have hR := S1421.isTwoRadicalIn_g0_rOf c
  have hcgs := S1421.cgsIn_g0_rOf_le c
  have hMs := S1421.isSQTKIn_g0 c
  have hLG : L ≤ S1421.g0Of T M H K1 := le_of_mem_cComp c.mem
  have hRG : S1421.rOf T M K1 ≤ S1421.g0Of T M H K1 := hR.1
  have hRL : S1421.rOf T M K1 ≤ Subgroup.normalizer (L : Set G) :=
    hRG.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp c.normal)
  have hRM : S1421.rOf T M K1 ≤ M := fun x hx =>
    hcgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRG hx, Subgroup.le_normalizer hx⟩)
  have hYsyl : IsSylowTwoOf (S1421.rOf T M K1) (L ⊔ S1421.rOf T M K1) :=
    isSylowTwoOf_sup_of_normalizes hR.isPGroup hRL hsyl
  have hYG : L ⊔ S1421.rOf T M K1 ≤ S1421.g0Of T M H K1 := sup_le hLG hRG
  have hYc : CharTwo (L ⊔ S1421.rOf T M K1) :=
    C2Push.charTwo_of_pCoreOf_le hc ((c2_1_pCore_le hR).trans le_sup_right) hYG
  have hYs : IsSQTKIn (L ⊔ S1421.rOf T M K1) := hMs.mono hYG
  have hcgsY : cgsIn (L ⊔ S1421.rOf T M K1) (S1421.rOf T M K1) ≤ (L ⊔ S1421.rOf T M K1) ⊓ M :=
    le_inf (cgsIn_le _ _) ((C2Nine.cgsIn_mono_left hYG _).trans hcgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 G (L ⊔ S1421.rOf T M K1) (S1421.rOf T M K1)
    ((L ⊔ S1421.rOf T M K1) ⊓ M) hYs hYc hYsyl hcgsY inf_le_left
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · obtain ⟨i, hi⟩ := hq
    have hB : IsBlock2 (L ⊔ S1421.rOf T M K1) (Lb i) := (hLb i).1.1
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      hB.1.2.2.2.1.resolve_right hi
    have hBperf : ⁅Lb i, Lb i⁆ = Lb i :=
      C1GN.isShort2_perfect_of_perfect_quotient hB.1 (Group.isPerfect_def.mp hBq.1)
    have hBL : Lb i ≤ L := C2Push.le_of_perfect_le_sup hR.isPGroup hRL hBperf hB.2.1
    have hBsubY : IsSubnormal (Lb i) (L ⊔ S1421.rOf T M K1) := IsBlock2.isSubnormal hB
    have hBsubL : IsSubnormal (Lb i) L := A3.subnormal_of_le_of_le hBsubY hBL le_sup_left
    have hBsubG : IsSubnormal (Lb i) (S1421.g0Of T M H K1) :=
      A3.subnormal_trans hBsubL (subnormal_of_mem_cComp c.mem)
    have hBne : Lb i ≠ ⊥ := by
      intro h
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hBq
      rw [h] at hnt
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt
    have hBeq : Lb i = L := by
      by_contra hne
      exact not_subnormal_of_mem_cComp c.mem (lt_of_le_of_ne hBL hne) hBne hBperf hBsubG
    rw [hBeq] at hBq
    exact hnq hBq
  · push Not at hq
    have hLM : L ≤ M :=
      le_of_isBlock2_card_three_of_normalizes c.mem hRG hRL (no_normal_three_L h36 h37 c hnq)
        hYsyl hRM Lb (fun i => ⟨(hLb i).1.1, hq i⟩) hprod
    exact c.st.notation_.not_le (c.lt_L.le.trans hLM)

end Final

end QA24

end CFSG.Quasithin
