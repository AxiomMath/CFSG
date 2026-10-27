module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeConfig
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType
open scoped Pointwise

@[expose] def autFix {K : Type} [Group K] (ζ : MulAut K) : Subgroup K where
  carrier := {k | ζ k = k}
  one_mem' := map_one ζ
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_autFix {K : Type} [Group K] {ζ : MulAut K} {k : K} : k ∈ autFix ζ ↔ ζ k = k := Iff.rfl

structure PumpUpAut {K : Type} [Group K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)) : Prop where
  quasi : CFSG.Open.IsQuasisimple K
  lie : CFSG.StandardType.LargeEvenMarking K (fun _ _ _ _ _ _ => True)
  ζ_ne : ζ ≠ 1
  ζ_cube : ζ ^ 3 = 1
  W_comp : CFSG.Open.IsComponentOf W (autFix ζ)
  W_ne : W ≠ ⊤
  W_model : LieModel W .PSU 5 2 1
  Wk_le : Wk ≤ W
  Wk_model : LieModel Wk .PSU 4 2 1
  Q_two : IsPGroup 2 Q
  Q_card : Nat.card Q = 4
  Q_fix : ∀ q ∈ Q, ∀ w ∈ Wk, q w = w
  ζ_norm_Q : ζ ∈ normalizer (Q : Set (MulAut K))
  ζ_fpf : ∀ q ∈ Q, ζ * q * ζ⁻¹ = q → q = 1
  A_elem : IsElemAbelian 3 A
  ζ_mem : ζ ∈ A
  ξ_mem : ξ ∈ A
  A_norm_Q : A ≤ normalizer (Q : Set (MulAut K))
  A_gen : ∀ α ∈ A, ∃ w ∈ W, ∃ β ∈ zpowers ζ, α = MulAut.conj w * β
  A_fixW : ∀ α ∈ A, (∀ w ∈ W, α w = w) → α ∈ zpowers ζ
  selfcent : ∀ g : K, orderOf g = 3 → (∀ α ∈ A, α g = g) → MulAut.conj g ∈ A
  rank : ∀ F P : Subgroup K, IsElemAbelian 3 F → IsPGroup 2 P → P ≠ ⊥ →
    F ≤ normalizer (P : Set K) → Nat.card F ≤ 3 ^ 5 * Nat.card (F ⊓ center K : Subgroup K)
  ξ_Q : ξ ∈ centralizer (Q : Set (MulAut K))
  ξ_fixWk : ∀ w ∈ Wk, ξ w = w
  ξ_norm : ∀ g : K, ξ g = g → MulAut.conj g ∈ normalizer (Q : Set (MulAut K))

@[expose] def PumpUpTypeInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      (∃ n, 6 ≤ n ∧ LieModel (K ⧸ center K) .PSU n 2 1) ∨
      (∃ r, 5 ≤ r ∧ (LieModel (K ⧸ center K) .PSp r 2 1 ∨
        LieModel (K ⧸ center K) .POmegaPlus r 2 1 ∨ LieModel (K ⧸ center K) .POmegaMinus r 2 1)) ∨
      LieModel (K ⧸ center K) .E6 0 2 1 ∨ LieModel (K ⧸ center K) .twistedE6 0 2 1 ∨
      LieModel (K ⧸ center K) .E7 0 2 1 ∨ LieModel (K ⧸ center K) .E8 0 2 1

@[expose] def PumpUpUnitaryRankInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      ∀ n, 8 ≤ n → LieModel (K ⧸ center K) .PSU n 2 1 → False

@[expose] def PumpUpSymplecticRankInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      ∀ r, 7 ≤ r → LieModel (K ⧸ center K) .PSp r 2 1 → False

@[expose] def PumpUpOrthogonalRankInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      ∀ r, 7 ≤ r → (LieModel (K ⧸ center K) .POmegaPlus r 2 1 ∨
        LieModel (K ⧸ center K) .POmegaMinus r 2 1) → False

@[expose] def PumpUpUnitarySmallInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      (LieModel (K ⧸ center K) .PSU 6 2 1 ∨ LieModel (K ⧸ center K) .PSU 7 2 1) → False

@[expose] def PumpUpTenInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      (LieModel (K ⧸ center K) .PSp 5 2 1 ∨ LieModel (K ⧸ center K) .POmegaMinus 5 2 1) → False

@[expose] def PumpUpOmegaPlusTenInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      LieModel (K ⧸ center K) .POmegaPlus 5 2 1 → False

@[expose] def PumpUpTwelveInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      (LieModel (K ⧸ center K) .PSp 6 2 1 ∨ LieModel (K ⧸ center K) .POmegaPlus 6 2 1) → False

@[expose] def PumpUpOmegaMinusTwelveInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      LieModel (K ⧸ center K) .POmegaMinus 6 2 1 → False

@[expose] def PumpUpE7Input : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      LieModel (K ⧸ center K) .E7 0 2 1 → False

@[expose] def PumpUpE8Input : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      LieModel (K ⧸ center K) .E8 0 2 1 → False

@[expose] def PumpUpE6Input : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      (LieModel (K ⧸ center K) .E6 0 2 1 ∨ LieModel (K ⧸ center K) .twistedE6 0 2 1) → False

structure PumpUpLieInputs : Prop where
  type : PumpUpTypeInput
  unitaryRank : PumpUpUnitaryRankInput
  symplecticRank : PumpUpSymplecticRankInput
  orthogonalRank : PumpUpOrthogonalRankInput
  unitarySmall : PumpUpUnitarySmallInput
  ten : PumpUpTenInput
  omegaPlusTen : PumpUpOmegaPlusTenInput
  twelve : PumpUpTwelveInput
  omegaMinusTwelve : PumpUpOmegaMinusTwelveInput
  e7 : PumpUpE7Input
  e8 : PumpUpE8Input
  e6 : PumpUpE6Input

theorem pumpUpAut_false (hI : PumpUpLieInputs) {K : Type} [Group K] [Finite K]
    {W Wk : Subgroup K} {ζ ξ : MulAut K} {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) : False := by
  rcases hI.type K W Wk ζ ξ Q A h with ⟨n, hn, hU⟩ | ⟨r, hr, hS | hP | hM⟩ | h6 | h6 | h7 | h8
  · rcases (by omega : n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | h8
    · exact hI.unitarySmall K W Wk ζ ξ Q A h (Or.inl hU)
    · exact hI.unitarySmall K W Wk ζ ξ Q A h (Or.inr hU)
    · exact hI.unitaryRank K W Wk ζ ξ Q A h n h8 hU
  · rcases (by omega : r = 5 ∨ r = 6 ∨ 7 ≤ r) with rfl | rfl | h7
    · exact hI.ten K W Wk ζ ξ Q A h (Or.inl hS)
    · exact hI.twelve K W Wk ζ ξ Q A h (Or.inl hS)
    · exact hI.symplecticRank K W Wk ζ ξ Q A h r h7 hS
  · rcases (by omega : r = 5 ∨ r = 6 ∨ 7 ≤ r) with rfl | rfl | h7
    · exact hI.omegaPlusTen K W Wk ζ ξ Q A h hP
    · exact hI.twelve K W Wk ζ ξ Q A h (Or.inr hP)
    · exact hI.orthogonalRank K W Wk ζ ξ Q A h r h7 (Or.inl hP)
  · rcases (by omega : r = 5 ∨ r = 6 ∨ 7 ≤ r) with rfl | rfl | h7
    · exact hI.ten K W Wk ζ ξ Q A h (Or.inr hM)
    · exact hI.omegaMinusTwelve K W Wk ζ ξ Q A h hM
    · exact hI.orthogonalRank K W Wk ζ ξ Q A h r h7 (Or.inr hM)
  · exact hI.e6 K W Wk ζ ξ Q A h (Or.inl h6)
  · exact hI.e6 K W Wk ζ ξ Q A h (Or.inr h6)
  · exact hI.e7 K W Wk ζ ξ Q A h h7
  · exact hI.e8 K W Wk ζ ξ Q A h h8

@[expose] def normConj {Y : Type} [Group Y]
    (K : Subgroup Y) : normalizer (K : Set Y) →* MulAut K where
  toFun g :=
    { toFun := fun k => ⟨(g : Y) * k * (g : Y)⁻¹, (mem_normalizer_iff.1 g.2 k).1 k.2⟩
      invFun := fun k => ⟨(g : Y)⁻¹ * k * g, by
        simpa using (mem_normalizer_iff.1 (inv_mem g.2) k).1 k.2⟩
      left_inv := fun k => by ext; simp [mul_assoc]
      right_inv := fun k => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem normConj_apply {Y : Type} [Group Y] {K : Subgroup Y} (g : normalizer (K : Set Y)) (k : K) :
    ((normConj K g k : K) : Y) = g * k * (g : Y)⁻¹ := rfl

theorem normConj_eq_conj {Y : Type} [Group Y] {K : Subgroup Y} (k : K) :
    normConj K ⟨k, le_normalizer k.2⟩ = MulAut.conj k :=
  MulEquiv.ext fun _ => Subtype.ext (by simp [normConj_apply, MulAut.conj_apply])

theorem normConj_fix_iff {Y : Type} [Group Y]
    {K : Subgroup Y} {g : normalizer (K : Set Y)} {k : K} :
    normConj K g k = k ↔ k * (g : Y) = g * k := by
  rw [Subtype.ext_iff, normConj_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem normConj_eq_one_iff {Y : Type} [Group Y] {K : Subgroup Y} {g : normalizer (K : Set Y)} :
    normConj K g = 1 ↔ (g : Y) ∈ centralizer (K : Set Y) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h k hk
    have := DFunLike.congr_fun h ⟨k, hk⟩
    exact normConj_fix_iff.1 this
  · intro h
    ext k
    exact congrArg Subtype.val (normConj_fix_iff.2 (h k k.2))

theorem autFix_normConj {Y : Type} [Group Y]
    {K C : Subgroup Y} {g : Y} (hg : g ∈ normalizer (K : Set Y))
    (hC : C = centralizer ({g} : Set Y)) :
    autFix (normConj K ⟨g, hg⟩) = (K ⊓ C).subgroupOf K := by
  ext k
  rw [mem_autFix, normConj_fix_iff, mem_subgroupOf, mem_inf, hC, mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq, k.2, true_and]
  exact eq_comm

theorem mem_mapConj {Y : Type} [Group Y]
    {K S : Subgroup Y} {s : Y} (hs : s ∈ S) (hN : s ∈ normalizer (K : Set Y)) :
    normConj K ⟨s, hN⟩ ∈ (S.subgroupOf (normalizer (K : Set Y))).map (normConj K) :=
  ⟨⟨s, hN⟩, mem_subgroupOf.2 hs, rfl⟩

theorem exists_of_mem_mapConj {Y : Type} [Group Y] {K S : Subgroup Y} {α : MulAut K}
    (hα : α ∈ (S.subgroupOf (normalizer (K : Set Y))).map (normConj K)) :
    ∃ s ∈ S, ∃ hs : s ∈ normalizer (K : Set Y), α = normConj K ⟨s, hs⟩ := by
  obtain ⟨s, hs, rfl⟩ := hα
  exact ⟨s, mem_subgroupOf.1 hs, s.2, rfl⟩

theorem normConj_mem_normalizer {Y : Type} [Group Y]
    {K S : Subgroup Y} {g : Y} (hgK : g ∈ normalizer (K : Set Y))
    (hgS : g ∈ normalizer (S : Set Y)) :
    normConj K ⟨g, hgK⟩ ∈ normalizer
      (((S.subgroupOf (normalizer (K : Set Y))).map (normConj K) : Subgroup _) :
        Set (MulAut K)) := by
  have h' : (⟨g, hgK⟩ : normalizer (K : Set Y)) ∈
      normalizer ((S.subgroupOf (normalizer (K : Set Y)) : Subgroup _) : Set _) := by
    rw [mem_normalizer_iff]
    intro b
    simpa only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] using
      mem_normalizer_iff.1 hgS (b : Y)
  exact le_normalizer_map _ (mem_map_of_mem _ h')

theorem normConj_closure_mem {Y : Type} [Group Y]
    {K : Subgroup Y} {s : Set Y} {M : Subgroup (MulAut K)}
    (hsN : s ⊆ normalizer (K : Set Y)) (hs : ∀ y (hy : y ∈ s), normConj K ⟨y, hsN hy⟩ ∈ M)
    {c : Y} (hc : c ∈ closure s) : ∃ h : c ∈ normalizer (K : Set Y), normConj K ⟨c, h⟩ ∈ M := by
  induction hc using Subgroup.closure_induction with
  | mem y hy => exact ⟨hsN hy, hs y hy⟩
  | one =>
    refine ⟨one_mem _, ?_⟩
    rw [show (⟨1, one_mem _⟩ : normalizer (K : Set Y)) = 1 from rfl, map_one]
    exact M.one_mem
  | mul a b _ _ ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨mul_mem ha1 hb1, ?_⟩
    rw [show (⟨a * b, mul_mem ha1 hb1⟩ : normalizer (K : Set Y)) = ⟨a, ha1⟩ * ⟨b, hb1⟩ from rfl,
      map_mul]
    exact mul_mem ha2 hb2
  | inv a _ ha =>
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨inv_mem ha1, ?_⟩
    rw [show (⟨a⁻¹, inv_mem ha1⟩ : normalizer (K : Set Y)) = (⟨a, ha1⟩)⁻¹ from rfl, map_inv]
    exact inv_mem ha2

theorem pumpUpConfig_aut {Y : Type} [Group Y] [Finite Y] {K X Xk T B : Subgroup Y} {z zk d : Y}
    (hc : PumpUpConfig K X Xk T B z zk d) :
    ∃ (W Wk : Subgroup K) (ζ ξ : MulAut K) (Q A : Subgroup (MulAut K)),
      PumpUpAut W Wk ζ ξ Q A := by
  set N := normalizer (K : Set Y) with hNdef
  have hBN : B ≤ N := hc.B_norm_K
  have hXK : X ≤ K := hc.X_lt.le
  have hXkK : Xk ≤ K := hc.Xk_le.trans hXK
  have hzN := hBN hc.z_mem
  have hzkN := hBN hc.zk_mem
  have hdN := hBN hc.d_mem
  have hd3 : d ^ 3 = 1 := hc.B_elem.2 d hc.d_mem
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hc.d_ne
  have hρd : normConj K ⟨d, hdN⟩ = 1 :=
    normConj_eq_one_iff.2 (center_le_centralizer _ hc.d_center)
  have hTinj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ (h₁ : t₁ ∈ N) (h₂ : t₂ ∈ N),
      normConj K ⟨t₁, h₁⟩ = normConj K ⟨t₂, h₂⟩ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ h₁ h₂ he
    have h1 : normConj K (⟨t₁, h₁⟩⁻¹ * ⟨t₂, h₂⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have hmem : t₁⁻¹ * t₂ ∈ T ⊓ centralizer (K : Set Y) :=
      mem_inf.2 ⟨mul_mem (inv_mem ht₁) ht₂, normConj_eq_one_iff.1 h1⟩
    rw [hc.T_faithful, mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  have hcl : closure {z, d} ≤ B := by
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hc.z_mem
    · exact hc.d_mem
  have hclN : ({z, d} : Set Y) ⊆ N := fun y hy => hBN (hcl (subset_closure hy))
  set ζ := normConj K ⟨z, hzN⟩ with hζ
  have hclζ : ∀ c ∈ closure {z, d}, ∃ h : c ∈ N, normConj K ⟨c, h⟩ ∈ zpowers ζ := by
    intro c hc'
    refine normConj_closure_mem hclN (fun y hy => ?_) hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact mem_zpowers _
    · rw [hρd]; exact one_mem _
  have hdec : ∀ b ∈ B, ∃ e ∈ B ⊓ X, ∃ c ∈ closure {z, d}, e * c = b := by
    intro b hb
    rw [hc.B_eq] at hb
    exact exists_mul_of_mem_sup
      (le_normalizer_of_commute fun e he c hc' =>
        elemAbelian_comm hc.B_elem (mem_inf.1 he).1 (hcl hc')) hb
  refine ⟨X.subgroupOf K, Xk.subgroupOf K, ζ, normConj K ⟨zk, hzkN⟩,
    (T.subgroupOf N).map (normConj K), (B.subgroupOf N).map (normConj K),
    { quasi := hc.K_comp.2.2
      lie := hc.K_lie
      ζ_ne := ?_
      ζ_cube := ?_
      W_comp := ?_
      W_ne := ?_
      W_model := hc.X_model.of_mulEquiv (subgroupOfEquivOfLe hXK).symm
      Wk_le := fun w hw => mem_subgroupOf.2 (hc.Xk_le (mem_subgroupOf.1 hw))
      Wk_model := hc.Xk_model.of_mulEquiv (subgroupOfEquivOfLe hXkK).symm
      Q_two := (hc.T_two.comap_subtype).map _
      Q_card := ?_
      Q_fix := ?_
      ζ_norm_Q := normConj_mem_normalizer hzN (hc.B_norm_T hc.z_mem)
      ζ_fpf := ?_
      A_elem := (hc.B_elem.subgroupOf _).map _
      ζ_mem := mem_mapConj hc.z_mem hzN
      ξ_mem := mem_mapConj hc.zk_mem hzkN
      A_norm_Q := ?_
      A_gen := ?_
      A_fixW := ?_
      selfcent := ?_
      rank := ?_
      ξ_Q := ?_
      ξ_fixWk := ?_
      ξ_norm := ?_ }⟩
  · intro h1
    have hKz : K ≤ centralizer ({z} : Set Y) := by
      intro k hk
      rw [mem_centralizer_iff]
      rintro _ rfl
      exact (normConj_fix_iff.1 (DFunLike.congr_fun h1 ⟨k, hk⟩)).symm
    have hXc := hc.X_comp
    rw [inf_eq_left.2 hKz] at hXc
    have := CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_eq_of_subnormal hc.K_comp.2.2 hXc.1 hXc.2.1
      hXc.2.2
    exact hc.X_lt.ne this
  · rw [hζ, ← map_pow]
    rw [show (⟨z, hzN⟩ : N) ^ 3 = 1 from Subtype.ext (by simpa using hc.B_elem.2 z hc.z_mem),
      map_one]
  · rw [autFix_normConj hzN rfl]
    exact ⟨fun w hw => mem_subgroupOf.2 (hc.X_comp.1 (mem_subgroupOf.1 hw)),
      CFSG.Open.IsSubnormal.comap K.subtype hc.X_comp.2.1,
      CFSG.LocalAnalysis.GLTheoremA.I142N.isQuasisimple_of_mulEquiv' (subgroupOfEquivOfLe hXK)
        hc.X_comp.2.2⟩
  · intro h
    rw [subgroupOf_eq_top] at h
    exact lt_irrefl _ (hc.X_lt.trans_le h)
  · set T' := T.subgroupOf N
    have hinj : Function.Injective ((normConj K).comp T'.subtype) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact hTinj _ (mem_subgroupOf.1 a.2) _ (mem_subgroupOf.1 b.2) (a : N).2 (b : N).2 hab
    have hr : ((normConj K).comp T'.subtype).range = T'.map (normConj K) := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hc.T_norm).toEquiv, hc.T_card]
  · intro q hq w hw
    obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_mapConj hq
    exact normConj_fix_iff.2 (mem_centralizer_iff.1 (hc.T_cent ht) w (mem_subgroupOf.1 hw))
  · intro q hq hfix
    obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_mapConj hq
    have hzt : z * t * z⁻¹ ∈ T := (mem_normalizer_iff.1 (hc.B_norm_T hc.z_mem) t).1 ht
    have he : normConj K ⟨z * t * z⁻¹, mul_mem (mul_mem hzN htN) (inv_mem hzN)⟩ =
        normConj K ⟨t, htN⟩ := by
      rw [show (⟨z * t * z⁻¹, mul_mem (mul_mem hzN htN) (inv_mem hzN)⟩ : N) =
        ⟨z, hzN⟩ * ⟨t, htN⟩ * (⟨z, hzN⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
      exact hfix
    have ht1 := hc.z_fpf t ht (hTinj _ hzt _ ht _ _ he)
    subst ht1
    rw [show (⟨1, htN⟩ : N) = 1 from rfl, map_one]
  · intro α hα
    obtain ⟨b, hb, hbN, rfl⟩ := exists_of_mem_mapConj hα
    exact normConj_mem_normalizer hbN (hc.B_norm_T hb)
  · intro α hα
    obtain ⟨b, hb, hbN, rfl⟩ := exists_of_mem_mapConj hα
    obtain ⟨e, he, c, hc', rfl⟩ := hdec b hb
    have heK : e ∈ K := hXK (mem_inf.1 he).2
    obtain ⟨hcN, hcζ⟩ := hclζ c hc'
    refine ⟨⟨e, heK⟩, mem_subgroupOf.2 (mem_inf.1 he).2, _, hcζ, ?_⟩
    refine MulEquiv.ext fun k => Subtype.ext ?_
    simp [normConj_apply, MulAut.conj_apply, mul_assoc]
  · intro α hα hfix
    obtain ⟨b, hb, hbN, rfl⟩ := exists_of_mem_mapConj hα
    have hbX : b ∈ B ⊓ centralizer (X : Set Y) := by
      refine mem_inf.2 ⟨hb, mem_centralizer_iff.2 fun w hw => ?_⟩
      exact normConj_fix_iff.1 (hfix ⟨w, hXK hw⟩ (mem_subgroupOf.2 hw))
    rw [hc.B_cent_X] at hbX
    obtain ⟨_, h⟩ := hclζ b hbX
    exact h
  · intro g hg3 hfix
    have hgB : (g : Y) ∈ centralizer (B : Set Y) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact (normConj_fix_iff.1 (hfix _ (mem_mapConj hb (hBN hb)))).symm
    have hgo : orderOf (g : Y) = 3 := by
      rw [← hg3]; exact orderOf_injective K.subtype K.subtype_injective g
    have := mem_mapConj (hc.B_selfcent _ hgo hgB) (le_normalizer g.2)
    rwa [normConj_eq_conj] at this
  · intro F P hF hP hP1 hFP
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set F' := F.map K.subtype with hF'
    have hcardF : Nat.card F' = Nat.card F := card_map_of_injective K.subtype_injective
    have hle := hc.rank F' (P.map K.subtype) (hF.map _) (hP.map _)
      (fun h => hP1 ((map_eq_bot_iff_of_injective (H := P) (f := K.subtype)
        K.subtype_injective).1 h))
      ((map_mono hFP).trans (le_normalizer_map _))
    have hpos : 0 < Nat.card (F ⊓ center K : Subgroup K) := Nat.card_pos
    by_cases hdF : d ∈ F'
    · obtain ⟨f, hf, hfd⟩ := hdF
      have hfZ : f ∈ F ⊓ center K := by
        refine mem_inf.2 ⟨hf, mem_center_iff.2 fun g => Subtype.ext ?_⟩
        have := mem_center_iff.1 hc.d_center (g : Y)
        simp only [Subgroup.coe_mul]
        rw [← hfd] at this
        exact this
      have hfo : orderOf f = 3 := by
        rw [← orderOf_injective K.subtype K.subtype_injective f]; simpa [hfd] using hdo
      have h3 : 3 ∣ Nat.card (F ⊓ center K : Subgroup K) := by
        rw [← hfo]; exact Subgroup.orderOf_dvd_natCard _ hfZ
      have h3' : 3 ≤ Nat.card (F ⊓ center K : Subgroup K) := Nat.le_of_dvd hpos h3
      have : Nat.card F' ≤ 3 ^ 6 := (card_le_of_le le_sup_left).trans hle
      rw [hcardF] at this
      calc Nat.card F ≤ 3 ^ 5 * 3 := by norm_num at this ⊢; omega
        _ ≤ _ := Nat.mul_le_mul_left _ h3'
    · have hlt : F' < F' ⊔ zpowers d :=
        lt_of_le_of_ne le_sup_left fun h => hdF (h ▸ mem_sup_right (mem_zpowers d))
      have hpd : IsPGroup 3 (zpowers d) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hdo, pow_one])
      haveI : (zpowers d).Normal := ⟨fun n hn g => by
        have hnZ : n ∈ center Y := (zpowers_le.2 hc.d_center) hn
        rw [mem_center_iff.1 hnZ g, mul_inv_cancel_right]
        exact hn⟩
      have hpS : IsPGroup 3 (F' ⊔ zpowers d : Subgroup Y) :=
        IsPGroup.to_sup_of_normal_right (hF.map K.subtype).isPGroup hpd
      obtain ⟨a, ha⟩ := (hF.map K.subtype).isPGroup.exists_card_eq
      obtain ⟨b, hb⟩ := hpS.exists_card_eq
      have hlt' := card_lt_of_lt hlt
      rw [ha, hb] at hlt'
      have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
      have h3 : 3 * Nat.card F' ≤ 3 ^ 6 := by
        rw [ha, ← pow_succ']
        exact (Nat.pow_le_pow_right (by norm_num) hab).trans (by rw [← hb]; exact hle)
      rw [hcardF] at h3
      calc Nat.card F ≤ 3 ^ 5 := by norm_num at h3 ⊢; omega
        _ ≤ 3 ^ 5 * Nat.card (F ⊓ center K : Subgroup K) := Nat.le_mul_of_pos_right _ hpos
  · rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_mapConj hq
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 hc.zk_T t ht)
  · intro w hw
    exact normConj_fix_iff.2 (mem_centralizer_iff.1 hc.zk_Xk w (mem_subgroupOf.1 hw))
  · intro g hg
    have hgz : (g : Y) ∈ centralizer ({zk} : Set Y) := by
      rw [mem_centralizer_iff]
      rintro _ rfl
      exact (normConj_fix_iff.1 hg).symm
    have := normConj_mem_normalizer (S := T) (le_normalizer g.2) (hc.zk_norm hgz)
    rwa [normConj_eq_conj] at this

end CFSG.GGQ2Prime
