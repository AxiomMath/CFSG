module

public import CFSG.Quasithin.Vol2.Ch8Sec1
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch8Sec2L825B
public import CFSG.Quasithin.Vol2.E2StatementsAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L825H

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_inf_eq_82 {H M I : Subgroup G} (hIH : I ≤ H) : H ⊓ M ⊓ I = M ⊓ I := by
  rw [inf_comm H M, inf_assoc, inf_eq_right.mpr hIH]

omit [Finite G] in
theorem pair_82 {T M V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I V h) (ch82I V h))
    (hMI : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G)) (hhI : h ∈ ch82I V h)
    (hcl : QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ ch82I V h) (ch82I V h)))
      (kerIn (M ⊓ ch82I V h) (ch82I V h))) :
    E2.Pair (ch82I V h) (T ⊓ ch82I V h) (M ⊓ ch82I V h) V h where
  sylow := hSyl
  le_T := le_inf hVT le_sup_left
  normal_T := inf_le_left.trans hTV
  elem := hV
  normalizer_le := hMI.ge
  le_X := inf_le_right
  le_pCoreOf := by
    have hVMI : V ≤ M ⊓ ch82I V h := by
      rw [hMI]
      exact le_inf le_sup_left Subgroup.le_normalizer
    have hMIN : M ⊓ ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
      rw [hMI]
      exact inf_le_right
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVMI hMIN
      (B2F.isPGroup_of_isElemAbelian hV)
  closed := hcl
  mem := hhI
  gen := rfl

omit [Finite G] in
theorem star_ne_bot_82 {M V : Subgroup G} {h : G} (hhI : h ∈ ch82I V h)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    E2.star (M ⊓ ch82I V h) (ch82I V h) V ≠ ⊥ := by
  intro hbot
  set I' := ch82I V h with hI'
  set π := QuotientGroup.mk' ((kerIn (M ⊓ I') I').subgroupOf I') with hπ
  have hV : V ≤ pCoreOf 2 I' := by
    intro v hv
    have hvI : v ∈ I' := (le_sup_left : V ≤ I') hv
    have h1 : π ⟨v, hvI⟩ ∈ E2.star (M ⊓ I') I' V := ⟨⟨v, hvI⟩, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, hker] at h1
    exact h1
  have hVh : B6.conjSub h V ≤ pCoreOf 2 I' := by
    intro w hw
    have h1 : h⁻¹ * w * h ∈ pCoreOf 2 I' := hV (B6.mem_conjSub.mp hw)
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I' hhI) _).mp h1
    have h3 : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    rwa [h3] at h2
  have hI : I' ≤ pCoreOf 2 I' := sup_le hV hVh
  obtain ⟨a, b, hab⟩ := hnt
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have ha : (QuotientGroup.mk a' : E2.StarQuot (M ⊓ I') I') = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker]
    exact hI a'.2
  have hb : (QuotientGroup.mk b' : E2.StarQuot (M ⊓ I') I') = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker]
    exact hI b'.2
  rw [ha, hb]

theorem one_lt_qOf_82 {V : Subgroup G} (hV : IsElemAbelian 2 V) (K : Subgroup G)
    (hFF : ¬ IsFFModule (autI hV ⊤)) : ((1 : ℚ) : WithTop ℚ) < qOf (autI hV K) := by
  have hK : ¬ IsFFModule (autI hV K) := fun ⟨A, hA, h1, h2, h3⟩ =>
    hFF ⟨A, hA.trans (autI_mono hV le_top), h1, h2, h3⟩
  have h := (B1_4_5 (fun v => IntMod.sq_eq_one v) (autI hV K)).out 1 3
  rw [WithTop.coe_one]
  exact lt_of_not_ge fun hle => hK (h.mpr hle)

theorem card_autI_ch82A_le_82 {V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hA7 : ch82A V h = B6.conjSub h V ⊓ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autI hV (ch82A V h)) ≤ 2 ^ CFSG.Open.pRank 2 (autI hV ⊤) := by
  have hA : ch82A V h = conjSubgroup V h⁻¹ ⊓ Subgroup.normalizer (V : Set G) := by
    rw [hA7, conjSub_eq_conjSubgroup_82]
  have hle := rk_autI_le_pRank hV (g := h⁻¹)
  rw [← hA] at hle
  have hVg : IsElemAbelian 2 (conjSubgroup V h⁻¹) := isElemAbelian_conjSubgroup hV _
  have hAel : IsElemAbelian 2 (ch82A V h) := by
    rw [hA]
    exact B2F.isElemAbelian_mono inf_le_left hVg
  have hAN : ch82A V h ≤ Subgroup.normalizer (V : Set G) := by
    rw [hA]
    exact inf_le_right
  rw [card_eq_two_pow_rk (isElemAbelian2_autI hV hAel hAN)]
  exact Nat.pow_le_pow_right (by norm_num) hle

omit [Finite G] in
theorem orderOf_convI_82 {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hf : ∀ y ∈ X, y ∈ Subgroup.centralizer (V : Set G) → y = 1) {x : G} (hx : x ∈ X) :
    orderOf (convI hV ⟨x, hXN hx⟩) = orderOf x := by
  let f : ↥X →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hXN)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ((Subgroup.inclusion hXN y : Subgroup.normalizer (V : Set G)) : G) ∈
        Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).mp hy
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hf y y.2 h1)
  have h := orderOf_injective f hinj ⟨x, hx⟩
  change orderOf (convI hV ⟨x, hXN hx⟩) = orderOf (⟨x, hx⟩ : ↥X) at h
  rw [h, Subgroup.orderOf_mk]

omit [Finite G] in
theorem exists_zpowers_eq_82 {X : Subgroup G} (hX : IsCyclic ↥X) :
    ∃ x ∈ X, X = Subgroup.zpowers x ∧ orderOf x = Nat.card ↥X := by
  obtain ⟨g, hg⟩ := hX.exists_generator
  refine ⟨g, g.2, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr g.2), ?_⟩
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have h1 : (g : G) ^ n = y := by
      have := congrArg Subtype.val hn
      rwa [Subgroup.coe_zpow] at this
    rw [← h1]
    exact Subgroup.zpow_mem_zpowers _ n
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg

theorem e214_82 (hE214 : AS_E_2_14) {H T M V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M)) (hDLSz : IsDihL2Sz (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    (∀ j : ℕ, 1 < j → IsPSL 2 2 j (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) →
      ∀ X : Subgroup G, X ≤ M ⊓ ch82I V h → Nat.card ↥X = 2 ^ j - 1 →
        ∀ x ∈ e214P V (ch82I V h) h, (∀ y ∈ X, y * x * y⁻¹ * x⁻¹ ∈ V ⊓ B6.conjSub h V) →
          x ∈ V ⊓ B6.conjSub h V) ∧
    autI hV (ch82I V h) ≤
      Subgroup.normalizer (autI hV (ch82A V h) : Set (MulAut (IntMod V hV))) ∧
    (∀ j : ℕ, (IsPSL 2 2 j (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) ∨
        IsSz j (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) →
      Nat.card ↥(autI hV (ch82A V h)) ≤ 2 ^ (2 * j) →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI hV (ch82I V h)) →
      Nat.card ↥(autI hV (ch82A V h)) = 2 ^ (2 * j) ∧
        (ch82ZI V h).relIndex V = 2 ^ (3 * j)) ∧
    (IsPSL 2 2 2 (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) →
      Nat.card ↥(autI hV (ch82A V h)) ≤ 2 ^ 6 →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI hV (ch82I V h)) →
      ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card ↥(autI hV (ch82A V h)) = 2 ^ (2 * s) ∧
        (ch82ZI V h).relIndex V = 2 ^ (2 * (s + 1))) ∧
    (∀ j : ℕ, 1 < j → IsPSL 2 2 j (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) →
      ∀ X : Subgroup G, X ≤ M ⊓ ch82I V h → Nat.card ↥X = 2 ^ j - 1 →
        V ⊓ Subgroup.centralizer (X : Set G) = ch82ZI V h) := by
  have hMI := inf_inf_eq_82 (M := M) hIC.1
  obtain ⟨-, -, h3, h6, h7, h8, h9⟩ :=
    hE214 G H T (H ⊓ M) V (ch82I V h) h h28 hchar hTI hIC hhI rfl hZ1
      (isDihL2Sz_of_eq hMI.symm hDLSz)
  refine ⟨?_, h6, ?_, ?_, ?_⟩
  · rw [← hMI]
    exact h3
  · rw [← hMI]
    exact h7
  · rw [← hMI]
    exact h8
  · rw [← hMI]
    exact h9

end L825H

end CFSG.Quasithin.H13
