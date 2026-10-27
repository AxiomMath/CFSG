module

public import CFSG.Quasithin.Background.C58Local
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup

variable {G : Type} [Group G]

structure GammaSetup (H T R K₁ : Subgroup G) (t x : G) : Prop where
  cfg : BlockConfig H T R K₁
  sylow : quasithinIsSylowTwo T
  even : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G
  RT : R ≤ T
  TH : T ≤ H
  tT : t ∈ T
  tK : t ∉ normalizer (K₁ : Set G)
  xN : x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G)
  xU : ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G)

namespace GammaSetup

variable {H T R K₁ : Subgroup G} {t x : G} (hs : GammaSetup H T R K₁ t x)
include hs

theorem relIndex_T₁ [Finite G] : (T ⊓ normalizer (K₁ : Set G)).relIndex T = 2 := by
  have h1 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 1 := fun h =>
    hs.tK (((Subgroup.relIndex_eq_one.mp h).trans inf_le_right) hs.tT)
  have h0 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := (T ⊓ normalizer (K₁ : Set G)).subgroupOf T)
  have := hs.cfg.index
  omega

theorem le_normalizer_T₁ [Finite G] :
    T ≤ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) := by
  have hn : ((T ⊓ normalizer (K₁ : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two hs.relIndex_T₁
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

theorem sq_mem_T₁ [Finite G] {g : G} (hg : g ∈ T) : g * g ∈ T ⊓ normalizer (K₁ : Set G) := by
  have h := Subgroup.mul_self_mem_of_index_two (H := (T ⊓ normalizer (K₁ : Set G)).subgroupOf T)
    hs.relIndex_T₁ ⟨g, hg⟩
  exact h

theorem isA4 [Finite G] : IsA4Block K₁ (blockU K₁) := hs.cfg.isA4

theorem U_le_T₁ [Finite G] : blockU K₁ ≤ T ⊓ normalizer (K₁ : Set G) :=
  le_inf (hs.cfg.U_le_R.trans hs.RT) (hs.isA4.le.trans Subgroup.le_normalizer)

theorem T₁_le_normalizer_U [Finite G] :
    T ⊓ normalizer (K₁ : Set G) ≤ normalizer (blockU K₁ : Set G) :=
  inf_le_right.trans (IsA4Block.normalizer_le hs.isA4)

theorem comm_K₂ : ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ t, a * b = b * a := by
  rcases hs.cfg.perm t hs.tT with h | h
  · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h) hs.tK
  · exact h

theorem inf_K₂ : K₁ ⊓ conjSubgroup K₁ t = ⊥ :=
  hs.cfg.disj t hs.tT fun h => hs.tK (conjSubgroup_eq_iff_mem_normalizer.mp h)

theorem no_common_normal [Finite G] {R₀ : Subgroup G}
    (hR₀ : R₀ ≤ T ⊓ normalizer (K₁ : Set G)) (hne : R₀ ≠ ⊥)
    (hY : normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ≤
      normalizer (R₀ : Set G))
    (hK : K₁ ≤ normalizer (R₀ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hs.isA4
  set U₁ := blockU K₁ with hU₁
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set H₀ := normalizer (R₀ : Set G) with hH₀
  have hT2 : IsPGroup 2 T := hs.sylow.1
  set Tsyl : Sylow 2 G := hT2.toSylow hs.sylow.2 with hTsyl
  have hTH₀ : (Tsyl : Subgroup G) ≤ H₀ := hs.le_normalizer_T₁.trans hY
  have hloc : IsTwoLocal H₀ := ⟨R₀, hne, hT2.to_le (hR₀.trans inf_le_left), rfl⟩
  have hF : H₀ ⊓ centralizer (pCoreOf 2 H₀ : Set G) ≤ pCoreOf 2 H₀ :=
    hs.even H₀ hloc ⟨Tsyl, hTH₀⟩
  obtain ⟨hC, hCab⟩ := conjClosure_le_centerOf_pCoreOf H₀ Tsyl hTH₀ hF
    (le_rfl : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T)
  set C := conjClosure (quasithinOmegaOneCenter T) H₀ with hCdef
  have hCN : H₀ ≤ normalizer (C : Set G) := le_normalizer_conjClosure _ _
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    have := hA.card_U
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  obtain ⟨e, heU, he1, heT₁⟩ :=
    exists_central_of_normal hU₁ne hs.U_le_T₁ hs.T₁_le_normalizer_U hT₁2
  set e₂ := t⁻¹ * e * t with he₂
  have he₂K : e₂ ∈ conjSubgroup K₁ t := by
    rw [mem_conjSubgroup_iff]
    have : t * e₂ * t⁻¹ = e := by rw [he₂]; group
    rw [this]; exact hA.le heU
  have hee₂ : e * e₂ = e₂ * e := hs.comm_K₂ e (hA.le heU) e₂ he₂K
  have he2 : e ^ 2 = 1 := hA.sq_U e heU
  have hTN := hs.le_normalizer_T₁
  have hzT : e * e₂ ∈ T := mul_mem (hs.U_le_T₁ heU).1
    (by rw [he₂]; exact mul_mem (mul_mem (inv_mem hs.tT) (hs.U_le_T₁ heU).1) hs.tT)
  have he₂T₁ : ∀ y ∈ T₁, y * e₂ = e₂ * y := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ T₁ := (mem_normalizer_iff.mp (hTN hs.tT) y).mp hy
    have h1 := heT₁ _ hty
    calc y * e₂ = t⁻¹ * ((t * y * t⁻¹) * e) * t := by rw [he₂]; group
      _ = t⁻¹ * (e * (t * y * t⁻¹)) * t := by rw [h1]
      _ = e₂ * y := by rw [he₂]; group
  have htt : t * t ∈ T₁ := hs.sq_mem_T₁ hs.tT
  have hte : t * e * t⁻¹ = e₂ := by
    have h1 := heT₁ _ htt
    calc t * e * t⁻¹ = t⁻¹ * ((t * t) * e) * t⁻¹ * t⁻¹ * t := by group
      _ = t⁻¹ * (e * (t * t)) * t⁻¹ * t⁻¹ * t := by rw [h1]
      _ = e₂ := by rw [he₂]; group
  have hTeq : T ≤ T₁ ⊔ zpowers t := by
    set X := T₁ ⊔ zpowers t with hX
    have hT₁X : T₁ ≤ X := le_sup_left
    have hXT : X ≤ T := sup_le inf_le_left (zpowers_le.mpr hs.tT)
    have hmul := Subgroup.relIndex_mul_relIndex T₁ X T hT₁X hXT
    rw [hs.relIndex_T₁] at hmul
    have h1 : T₁.relIndex X ≠ 1 := fun h =>
      hs.tK ((Subgroup.relIndex_eq_one.mp h (mem_sup_right (mem_zpowers t))).2)
    have h2 : X.relIndex T = 1 := by
      have hd : T₁.relIndex X ∣ 2 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h h1
      · rw [h] at hmul; omega
    exact Subgroup.relIndex_eq_one.mp h2
  have hzc : T ≤ centralizer ({e * e₂} : Set G) := by
    refine hTeq.trans (sup_le ?_ (zpowers_le.mpr ?_))
    · intro y hy
      rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      calc e * e₂ * y = e * (e₂ * y) := by group
        _ = e * (y * e₂) := by rw [he₂T₁ y hy]
        _ = (e * y) * e₂ := by group
        _ = (y * e) * e₂ := by rw [heT₁ y hy]
        _ = y * (e * e₂) := by group
    · rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 : t * (e * e₂) * t⁻¹ = e * e₂ := by
        have h2 : t * e₂ * t⁻¹ = e := by rw [he₂]; group
        calc t * (e * e₂) * t⁻¹ = (t * e * t⁻¹) * (t * e₂ * t⁻¹) := by group
          _ = e₂ * e := by rw [hte, h2]
          _ = e * e₂ := hee₂.symm
      calc e * e₂ * t = t * (e * e₂) * t⁻¹ * t := by rw [h1]
        _ = t * (e * e₂) := by group
  have he₂2 : e₂ ^ 2 = 1 := by
    rw [he₂]
    have : (t⁻¹ * e * t) ^ 2 = t⁻¹ * e ^ 2 * t := by simp [pow_two]; group
    rw [this, he2]; group
  have hz2 : (e * e₂) ^ 2 = 1 := by
    have : (e * e₂) ^ 2 = e ^ 2 * e₂ ^ 2 := by
      simp only [pow_two]
      calc e * e₂ * (e * e₂) = e * (e₂ * e) * e₂ := by group
        _ = e * (e * e₂) * e₂ := by rw [hee₂]
        _ = e * e * (e₂ * e₂) := by group
    rw [this, he2, he₂2, one_mul]
  have hzZ : e * e₂ ∈ quasithinOmegaOneCenter T := by
    refine mem_quasithinOmegaOneCenter_iff.mpr ⟨hzT, ?_, hz2⟩
    rw [mem_centralizer_iff]
    intro g hg
    have := (mem_centralizer_iff.mp (hzc hg)) (e * e₂) rfl
    exact this.symm
  have hzC : e * e₂ ∈ C := le_conjClosure _ _ hzZ
  obtain ⟨c, hcK, hc3, hcN, hcfp, -⟩ := hA.exists_c
  have hcH₀ : c ∈ H₀ := hK hcK
  have hczC : c * (e * e₂) * c⁻¹ ∈ C := (mem_normalizer_iff.mp (hCN hcH₀) _).mp hzC
  have hce₂ : c * e₂ = e₂ * c := hs.comm_K₂ c hcK e₂ he₂K
  have hceU : c * e * c⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hcN e).mp heU
  set w := e * (c * e * c⁻¹)⁻¹ with hw
  have hwC : w ∈ C := by
    have e1 : (e * e₂) * (c * (e * e₂) * c⁻¹)⁻¹ = w := by
      rw [hw]
      have hce₂' : c * e₂ * c⁻¹ = e₂ := by rw [hce₂]; group
      have : c * (e * e₂) * c⁻¹ = (c * e * c⁻¹) * e₂ := by
        calc c * (e * e₂) * c⁻¹ = (c * e * c⁻¹) * (c * e₂ * c⁻¹) := by group
          _ = (c * e * c⁻¹) * e₂ := by rw [hce₂']
      rw [this]; group
    rw [← e1]; exact mul_mem hzC (inv_mem hczC)
  have hwU : w ∈ U₁ := mul_mem heU (inv_mem hceU)
  have hw1 : w ≠ 1 := by
    intro h1
    apply hcfp e heU he1
    rw [hw] at h1
    have := eq_of_mul_inv_eq_one h1
    exact this.symm
  have hUC : U₁ ≤ C := hA.le_of_mem (hK.trans hCN) hwC hwU hw1
  have hxH₀ : x ∈ H₀ := hY hs.xN
  have hUxC : conjSubgroup U₁ x ≤ C := by
    intro v hv
    rw [mem_conjSubgroup_iff] at hv
    have := (mem_normalizer_iff.mp (hCN (inv_mem hxH₀)) _).mp (hUC hv)
    simpa [mul_assoc] using this
  apply hs.xU
  intro v hv
  rw [mem_centralizer_iff]
  intro u hu
  exact (hCab.1.is_comm.comm ⟨u, hUC hu⟩ ⟨v, hUxC hv⟩) |> congrArg Subtype.val

theorem thompsonJ_not_le [Finite G] :
    ¬ thompsonJ (T ⊓ normalizer (K₁ : Set G)) ≤ centralizer (blockU K₁ : Set G) := by
  intro hJ
  have hA := hs.isA4
  set U₁ := blockU K₁ with hU₁
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set P₁ := T₁ ⊓ centralizer (U₁ : Set G) with hP₁
  have hJP : thompsonJ T₁ ≤ P₁ := le_inf (B6.thompsonJ_le T₁) hJ
  have hJeq : thompsonJ P₁ = thompsonJ T₁ := B6.thompsonJ_eq_of_le hJP inf_le_left
  have hKP : K₁ ≤ normalizer (P₁ : Set G) :=
    IsA4Block.le_normalizer_inf hA hs.U_le_T₁ inf_le_right
  have hKJ : K₁ ≤ normalizer (thompsonJ T₁ : Set G) := by
    rw [← hJeq]; exact hKP.trans (normalizer_le_normalizer_thompsonJ P₁)
  have hYJ : normalizer (T₁ : Set G) ≤ normalizer (thompsonJ T₁ : Set G) :=
    normalizer_le_normalizer_thompsonJ T₁
  obtain ⟨A, hAm⟩ := exists_isMaxElemAbelian T₁
  have hA4 : 4 ≤ Nat.card A := by
    have := hAm.2.2 U₁ hs.U_le_T₁ ⟨⟨⟨fun a b => Subtype.ext (hA.comm_U a a.2 b b.2)⟩⟩,
      fun a ha => hA.sq_U a ha⟩
    rwa [hA.card_U] at this
  have hJne : thompsonJ T₁ ≠ ⊥ := by
    intro h
    have hAle : A ≤ thompsonJ T₁ := B6.le_thompsonJ hAm
    rw [h, le_bot_iff] at hAle
    rw [hAle, Subgroup.card_bot] at hA4
    norm_num at hA4
  exact hs.no_common_normal (B6.thompsonJ_le T₁) hJne hYJ hKJ

theorem baum_facts [Finite G] :
    blockU K₁ ≤ baum (T ⊓ normalizer (K₁ : Set G)) ∧
      baum (T ⊓ normalizer (K₁ : Set G)) ≤ normalizer (K₁ : Set G) ∧
      ¬ baum (T ⊓ normalizer (K₁ : Set G)) ≤ centralizer (blockU K₁ : Set G) := by
  have hA := hs.isA4
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  have hT₁2 : IsPGroup 2 T₁ := hs.sylow.1.to_le inf_le_left
  have hJ2 : IsPGroup 2 (thompsonJ T₁) := hT₁2.to_le (B6.thompsonJ_le T₁)
  have hth : ⁅K₁, thompsonJ T₁⁆ = K₁ :=
    IsA4Block.commutator_eq hA hJ2 ((B6.thompsonJ_le T₁).trans inf_le_right)
      ((B6.thompsonJ_le T₁).trans hs.T₁_le_normalizer_U) hs.thompsonJ_not_le
  refine ⟨(C56.a3_blockU_le_baum hT₁2 hs.cfg.short hs.cfg.alt hs.U_le_T₁ hth).1,
    (inf_le_left : baum T₁ ≤ T₁).trans inf_le_right, fun hle => ?_⟩
  exact hs.thompsonJ_not_le ((thompsonJ_le_baum' T₁).trans hle)

theorem conj_le_of_odd [Finite G] {y : G}
    (hy : y ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G))
    (hodd : Odd (orderOf y)) :
    conjSubgroup (blockU K₁) y ≤ centralizer (blockU K₁ : Set G) := by
  obtain ⟨hUB, hBK, hnt⟩ := hs.baum_facts
  have hB2 : IsPGroup 2 (baum (T ⊓ normalizer (K₁ : Set G))) :=
    hs.sylow.1.to_le (inf_le_left.trans inf_le_left)
  have hyB := normalizer_le_normalizer_baum _ hy
  by_contra h
  obtain ⟨W, hP⟩ := pairData_of_block hs.isA4 hs.cfg.short hB2 hUB hBK hnt hyB h
  exact h ((hP.conj_le_of_odd hyB hP.mem_normalizer_sqSub hodd).trans inf_le_right)

theorem pairData [Finite G] :
    ∃ W : Subgroup G, PairData (baum (T ⊓ normalizer (K₁ : Set G)))
      (baum (T ⊓ normalizer (K₁ : Set G)) ⊓ centralizer (blockU K₁ : Set G)) (blockU K₁) W
      ((baum (T ⊓ normalizer (K₁ : Set G)) ⊓ centralizer (blockU K₁ : Set G)) ⊓
        centralizer (K₁ : Set G)) x := by
  obtain ⟨hUB, hBK, hnt⟩ := hs.baum_facts
  have hB2 : IsPGroup 2 (baum (T ⊓ normalizer (K₁ : Set G))) :=
    hs.sylow.1.to_le (inf_le_left.trans inf_le_left)
  exact pairData_of_block hs.isA4 hs.cfg.short hB2 hUB hBK hnt
    (normalizer_le_normalizer_baum _ hs.xN) hs.xU

theorem le_sup_zpowers [Finite G] : T ≤ (T ⊓ normalizer (K₁ : Set G)) ⊔ zpowers t := by
  set X := (T ⊓ normalizer (K₁ : Set G)) ⊔ zpowers t with hX
  have hT₁X : T ⊓ normalizer (K₁ : Set G) ≤ X := le_sup_left
  have hXT : X ≤ T := sup_le inf_le_left (zpowers_le.mpr hs.tT)
  have hmul := Subgroup.relIndex_mul_relIndex _ X T hT₁X hXT
  rw [hs.relIndex_T₁] at hmul
  have h1 : (T ⊓ normalizer (K₁ : Set G)).relIndex X ≠ 1 := fun h =>
    hs.tK ((Subgroup.relIndex_eq_one.mp h (mem_sup_right (mem_zpowers t))).2)
  have h2 : X.relIndex T = 1 := by
    have hd : (T ⊓ normalizer (K₁ : Set G)).relIndex X ∣ 2 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h h1
    · rw [h] at hmul; omega
  exact Subgroup.relIndex_eq_one.mp h2

theorem exists_central [Finite G] :
    ∃ e ∈ blockU K₁, e ≠ 1 ∧ ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₁ne : blockU K₁ ≠ ⊥ := by
    intro h
    have := hs.isA4.card_U
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  exact exists_central_of_normal hU₁ne hs.U_le_T₁ hs.T₁_le_normalizer_U
    (hs.sylow.1.to_le inf_le_left)

theorem z_mem [Finite G] {e : G} (heU : e ∈ blockU K₁) (he1 : e ≠ 1)
    (heT₁ : ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y) :
    e * (t⁻¹ * e * t) ∈ quasithinOmegaOneCenter T ∧ e * (t⁻¹ * e * t) ≠ 1 := by
  have hA := hs.isA4
  set e₂ := t⁻¹ * e * t with he₂
  have he₂K : e₂ ∈ conjSubgroup K₁ t := by
    rw [mem_conjSubgroup_iff]
    have : t * e₂ * t⁻¹ = e := by rw [he₂]; group
    rw [this]; exact hA.le heU
  have hee₂ : e * e₂ = e₂ * e := hs.comm_K₂ e (hA.le heU) e₂ he₂K
  have he2 : e ^ 2 = 1 := hA.sq_U e heU
  have hTN := hs.le_normalizer_T₁
  have hzT : e * e₂ ∈ T := mul_mem (hs.U_le_T₁ heU).1
    (by rw [he₂]; exact mul_mem (mul_mem (inv_mem hs.tT) (hs.U_le_T₁ heU).1) hs.tT)
  have he₂T₁ : ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e₂ = e₂ * y := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ T ⊓ normalizer (K₁ : Set G) :=
      (mem_normalizer_iff.mp (hTN hs.tT) y).mp hy
    have h1 := heT₁ _ hty
    calc y * e₂ = t⁻¹ * ((t * y * t⁻¹) * e) * t := by rw [he₂]; group
      _ = t⁻¹ * (e * (t * y * t⁻¹)) * t := by rw [h1]
      _ = e₂ * y := by rw [he₂]; group
  have htt : t * t ∈ T ⊓ normalizer (K₁ : Set G) := hs.sq_mem_T₁ hs.tT
  have hte : t * e * t⁻¹ = e₂ := by
    have h1 := heT₁ _ htt
    calc t * e * t⁻¹ = t⁻¹ * ((t * t) * e) * t⁻¹ * t⁻¹ * t := by group
      _ = t⁻¹ * (e * (t * t)) * t⁻¹ * t⁻¹ * t := by rw [h1]
      _ = e₂ := by rw [he₂]; group
  have hzc : T ≤ centralizer ({e * e₂} : Set G) := by
    refine hs.le_sup_zpowers.trans (sup_le ?_ (zpowers_le.mpr ?_))
    · intro y hy
      rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      calc e * e₂ * y = e * (e₂ * y) := by group
        _ = e * (y * e₂) := by rw [he₂T₁ y hy]
        _ = (e * y) * e₂ := by group
        _ = (y * e) * e₂ := by rw [heT₁ y hy]
        _ = y * (e * e₂) := by group
    · rw [mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 : t * (e * e₂) * t⁻¹ = e * e₂ := by
        have h2 : t * e₂ * t⁻¹ = e := by rw [he₂]; group
        calc t * (e * e₂) * t⁻¹ = (t * e * t⁻¹) * (t * e₂ * t⁻¹) := by group
          _ = e₂ * e := by rw [hte, h2]
          _ = e * e₂ := hee₂.symm
      calc e * e₂ * t = t * (e * e₂) * t⁻¹ * t := by rw [h1]
        _ = t * (e * e₂) := by group
  have he₂2 : e₂ ^ 2 = 1 := by
    rw [he₂]
    have : (t⁻¹ * e * t) ^ 2 = t⁻¹ * e ^ 2 * t := by simp [pow_two]; group
    rw [this, he2]; group
  have hz2 : (e * e₂) ^ 2 = 1 := by
    have : (e * e₂) ^ 2 = e ^ 2 * e₂ ^ 2 := by
      simp only [pow_two]
      calc e * e₂ * (e * e₂) = e * (e₂ * e) * e₂ := by group
        _ = e * (e * e₂) * e₂ := by rw [hee₂]
        _ = e * e * (e₂ * e₂) := by group
    rw [this, he2, he₂2, one_mul]
  refine ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨hzT, ?_, hz2⟩, ?_⟩
  · rw [mem_centralizer_iff]
    intro g hg
    exact ((mem_centralizer_iff.mp (hzc hg)) (e * e₂) rfl).symm
  · intro h1
    have h2 : e = e₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : e ∈ K₁ ⊓ conjSubgroup K₁ t :=
      Subgroup.mem_inf.mpr ⟨hA.le heU, by rw [h2]; exact (conjSubgroup K₁ t).inv_mem he₂K⟩
    rw [hs.inf_K₂] at h3
    exact he1 h3

end GammaSetup

end CFSG.Quasithin.C58
