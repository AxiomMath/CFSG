module

public import CFSG.Quasithin.Background.F9Pairing
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

theorem relIndex_sup_normal {Γ : Type*} [Group Γ] [Finite Γ] {K C X : Subgroup Γ} [K.Normal]
    (hCX : C ≤ X) (hker : X ⊓ K ≤ C) : (C ⊔ K).relIndex (X ⊔ K) = C.relIndex X := by
  have h1 : K.relIndex (X ⊔ K) = K.relIndex X := Subgroup.relIndex_sup_right X K
  have h2 : K.relIndex (C ⊔ K) = K.relIndex C := Subgroup.relIndex_sup_right C K
  have h3 : K.relIndex (C ⊔ K) * (C ⊔ K).relIndex (X ⊔ K) = K.relIndex (X ⊔ K) :=
    Subgroup.relIndex_mul_relIndex K (C ⊔ K) (X ⊔ K) le_sup_right (sup_le_sup_right hCX K)
  have hKC : K ⊓ C = K ⊓ X := by
    apply le_antisymm (inf_le_inf_left K hCX)
    exact le_inf inf_le_left (by rw [inf_comm]; exact hker)
  have h4 : (K ⊓ X).relIndex C * C.relIndex X = (K ⊓ X).relIndex X :=
    Subgroup.relIndex_mul_relIndex (K ⊓ X) C X (by rw [inf_comm]; exact hker) hCX
  have h5 : K.relIndex X = (K ⊓ X).relIndex X := (Subgroup.inf_relIndex_right K X).symm
  have h6 : K.relIndex C = (K ⊓ X).relIndex C := by
    rw [← hKC]; exact (Subgroup.inf_relIndex_right K C).symm
  rw [h1, h2, h6] at h3
  rw [h5] at h3
  have hpos : (K ⊓ X).relIndex C ≠ 0 := by
    unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite
  have : (K ⊓ X).relIndex C * (C ⊔ K).relIndex (X ⊔ K) = (K ⊓ X).relIndex C * C.relIndex X :=
    h3.trans h4.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this

theorem relIndex_secImg_of_inf_le [Finite G] {A K C X : Subgroup G} [(K.subgroupOf A).Normal]
    (hCX : C ≤ X) (hXA : X ≤ A) (hker : X ⊓ K ≤ C) :
    (secImg A K C).relIndex (secImg A K X) = C.relIndex X := by
  unfold secImg
  rw [Subgroup.relIndex_map_map]
  have hker' : (secMk A K).ker = K.subgroupOf A := QuotientGroup.ker_mk' _
  rw [hker']
  have h := relIndex_sup_normal (Γ := ↥A) (K := K.subgroupOf A) (C := C.subgroupOf A)
    (X := X.subgroupOf A) (fun x hx => hCX hx) (fun x hx => hker ⟨hx.1, hx.2⟩)
  rw [h, Subgroup.relIndex_subgroupOf hXA]

theorem isElemAbelian_of_card_eq_two {C : Subgroup G} (h : Nat.card C = 2) :
    IsElemAbelian 2 C := by
  have hcyc : IsCyclic C := isCyclic_of_prime_card (p := 2) (hp := ⟨Nat.prime_two⟩) h
  let _ : CommGroup C := IsCyclic.commGroup
  rw [isElemAbelian_iff]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have := mul_comm (⟨x, hx⟩ : C) ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  · have := pow_card_eq_one' (G := C) (x := ⟨x, hx⟩)
    rw [h] at this
    simpa using congrArg Subtype.val this

theorem relIndex_eq_of_commutator_le [Finite G] {X Y C : Subgroup G}
    (hY : IsElemAbelian 2 Y) (hC : Nat.card C = 2)
    (hcomm : ⁅X, Y⁆ ≤ C) (hCX : C ≤ Subgroup.centralizer (X : Set G))
    (hCY : C ≤ Subgroup.centralizer (Y : Set G)) :
    (X ⊓ Subgroup.centralizer (Y : Set G)).relIndex X =
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y := by
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_card_eq_two hC
  let _ : CommGroup ↥Y := commGroupOfElemAbelian hY
  let _ : CommGroup ↥C := commGroupOfElemAbelian hCe
  have hB : ∀ y : ↥Y, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hY.2 y y.2)
  let β : ↥X → ↥Y → ↥C := fun x y =>
    ⟨x * y * x⁻¹ * y⁻¹, hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩
  have hcc : ∀ c ∈ C, ∀ z ∈ C, c * z = z * c := fun c hc z hz => isElemAbelian_comm hCe hc hz
  have h1 : ∀ x₁ x₂ y, β (x₁ * x₂) y = β x₁ y * β x₂ y := by
    intro x₁ x₂ y
    apply Subtype.ext
    have hc₂ : (x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹ ∈ C :=
      hcomm (Subgroup.commutator_mem_commutator x₂.2 y.2)
    have hc₁ : (x₁ : G) * y * (x₁ : G)⁻¹ * (y : G)⁻¹ ∈ C :=
      hcomm (Subgroup.commutator_mem_commutator x₁.2 y.2)
    have hx := Subgroup.mem_centralizer_iff.mp (hCX hc₂) (x₁ : G) x₁.2
    change (x₁ * x₂ : G) * y * (x₁ * x₂ : G)⁻¹ * (y : G)⁻¹ =
      ((x₁ : G) * y * (x₁ : G)⁻¹ * (y : G)⁻¹) * ((x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹)
    calc (x₁ * x₂ : G) * y * (x₁ * x₂ : G)⁻¹ * (y : G)⁻¹
        = ((x₁ : G) * ((x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹) * (x₁ : G)⁻¹) *
            ((x₁ : G) * y * (x₁ : G)⁻¹ * (y : G)⁻¹) := by group
      _ = ((x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹) * ((x₁ : G) * y * (x₁ : G)⁻¹ * (y : G)⁻¹) := by
        have : (x₁ : G) * ((x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹) * (x₁ : G)⁻¹ =
            (x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹ := by
          rw [hx]; group
        rw [this]
      _ = ((x₁ : G) * y * (x₁ : G)⁻¹ * (y : G)⁻¹) * ((x₂ : G) * y * (x₂ : G)⁻¹ * (y : G)⁻¹) :=
        (hcc _ hc₁ _ hc₂).symm
  have h2 : ∀ x y₁ y₂, β x (y₁ * y₂) = β x y₁ * β x y₂ := by
    intro x y₁ y₂
    apply Subtype.ext
    have hc₂ : (x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹ ∈ C :=
      hcomm (Subgroup.commutator_mem_commutator x.2 y₂.2)
    have hy := Subgroup.mem_centralizer_iff.mp (hCY hc₂) (y₁ : G) y₁.2
    change (x : G) * (y₁ * y₂ : G) * (x : G)⁻¹ * (y₁ * y₂ : G)⁻¹ =
      ((x : G) * y₁ * (x : G)⁻¹ * (y₁ : G)⁻¹) * ((x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹)
    calc (x : G) * (y₁ * y₂ : G) * (x : G)⁻¹ * (y₁ * y₂ : G)⁻¹
        = ((x : G) * y₁ * (x : G)⁻¹ * (y₁ : G)⁻¹) *
            ((y₁ : G) * ((x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹) * (y₁ : G)⁻¹) := by group
      _ = ((x : G) * y₁ * (x : G)⁻¹ * (y₁ : G)⁻¹) * ((x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹) := by
        have : (y₁ : G) * ((x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹) * (y₁ : G)⁻¹ =
            (x : G) * y₂ * (x : G)⁻¹ * (y₂ : G)⁻¹ := by
          rw [hy]; group
        rw [this]
  have key := card_mul_card_radical_eq hB hC β h1 h2
  have hcm : ∀ (x y : G), x * y * x⁻¹ * y⁻¹ = 1 ↔ x * y = y * x := fun x y => by
    constructor
    · intro e
      calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
        _ = y * x := by rw [e]; group
    · intro e
      calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [e]
        _ = 1 := by group
  have c1 : Nat.card {b : ↥Y // ∀ a, β a b = 1} =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G)) := by
    refine Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := congrArg Subtype.val (b.2 ⟨x, hx⟩)
          exact (hcm x b.1).mp this⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * b.1⁻¹ = 1
          exact (hcm a b.1).mpr (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have c2 : Nat.card {a : ↥X // ∀ b, β a b = 1} =
      Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, Subgroup.mem_centralizer_iff.mpr fun u hu => by
          have := congrArg Subtype.val (a.2 ⟨u, hu⟩)
          exact ((hcm a.1 u).mp this).symm⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => Subtype.ext (by
          show (a.1 : G) * b * (a.1 : G)⁻¹ * (b : G)⁻¹ = 1
          exact (hcm a.1 b).mpr (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2).symm)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [c1, c2] at key
  have e1 := Subgroup.relIndex_mul_card (X ⊓ Subgroup.centralizer (Y : Set G)) X
  have e2 := Subgroup.relIndex_mul_card (Y ⊓ Subgroup.centralizer (X : Set G)) Y
  rw [inf_eq_left.mpr (inf_le_left : X ⊓ Subgroup.centralizer (Y : Set G) ≤ X)] at e1
  rw [inf_eq_left.mpr (inf_le_left : Y ⊓ Subgroup.centralizer (X : Set G) ≤ Y)] at e2
  have p1 : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) := Nat.card_pos
  have p2 : 0 < Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G)) := Nat.card_pos
  rw [← e1, ← e2] at key
  have : (X ⊓ Subgroup.centralizer (Y : Set G)).relIndex X *
        (Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) *
          Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G))) =
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y *
        (Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) *
          Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G))) := by
    calc _ = _ := by ring
      _ = _ := key
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos p1 p2) this

theorem rAV_le_two_iff {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X A : Subgroup (MulAut W)} (hA : IsA2 X A) :
    rAV A ≤ 2 ↔ Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A) := by
  have hmul := hA.rAV_mul
  have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA.rk_pos
  have h1 : rAV A ≤ 2 ↔ rkIdx (fixV A) ≤ 2 * rk A := by
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_right h hpos.le
      rw [hmul] at this
      exact_mod_cast this
    · intro h
      have h' : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk A : ℚ) := by exact_mod_cast h
      rw [← hmul] at h'
      exact le_of_mul_le_mul_right h' hpos
  have hadd := rk_add_rkIdx (fixV A)
  have cW : Nat.card W = 2 ^ rk W := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have cF : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hW (fixV A)
  have cA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isElemAbelian2.isPGroup
  rw [h1, cW, cF, cA, ← pow_mul, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem qOf_le_two_of_mem_Qset {W : Type*} [CommGroup W] [Finite W] {X A : Subgroup (MulAut W)}
    (hA : A ∈ Qset X) : qOf X ≤ 2 := by
  obtain ⟨⟨hA2, hr⟩, hcs⟩ := hA
  have := qOf_le_iff.mpr ⟨A, hA2, (isQuadratic_iff_commSeries_two A).mpr hcs, hr⟩
  exact_mod_cast this

theorem conjAct_apply_coe' {Γ : Type*} [Group Γ] (W : Subgroup Γ)
    (g : Subgroup.normalizer (W : Set Γ)) (w : W) :
    ((conjAct W g w : W) : Γ) = g * w * (g : Γ)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply W g w

theorem mem_autOn_iff {Γ : Type*} [Group Γ] {S W : Subgroup Γ} {a : MulAut ↥W} :
    a ∈ autOn S W ↔ ∃ s : Subgroup.normalizer (W : Set Γ), (s : Γ) ∈ S ∧ conjAct W s = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff

theorem isQuadratic_autOn_of_forall {Γ : Type*} [Group Γ] {S W : Subgroup Γ}
    (hW : IsElemAbelian 2 W)
    (h : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ w ∈ W,
      s₂ * (s₁ * w * s₁⁻¹ * w⁻¹) * s₂⁻¹ * (s₁ * w * s₁⁻¹ * w⁻¹)⁻¹ = 1) :
    @IsQuadratic W (commGroupOfElemAbelian hW) (autOn S W) := by
  let _ : CommGroup W := commGroupOfElemAbelian hW
  unfold IsQuadratic
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨a, ha, v, rfl⟩
  rw [SetLike.mem_coe, mem_fixV]
  intro a' ha'
  obtain ⟨s₁, hs₁, rfl⟩ := mem_autOn_iff.mp ha
  obtain ⟨s₂, hs₂, rfl⟩ := mem_autOn_iff.mp ha'
  apply Subtype.ext
  have h1 := h s₁ hs₁ s₂ hs₂ v v.2
  have h2 := mul_inv_eq_one.mp h1
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe']
  calc _ = (s₂ : Γ) * ((s₁ : Γ) * v * (s₁ : Γ)⁻¹ * (v : Γ)⁻¹) * (s₂ : Γ)⁻¹ := by group
    _ = _ := h2

theorem secMk_comm_of_commutator_mem {A K : Subgroup G} [(K.subgroupOf A).Normal] {x y : A}
    (h : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ K) :
    secMk A K x * secMk A K y = secMk A K y * secMk A K x := by
  have h1 : secMk A K (x * y * x⁻¹ * y⁻¹) = 1 := secMk_eq_one_iff.mpr (by simpa using h)
  simp only [map_mul, map_inv] at h1
  calc secMk A K x * secMk A K y
      = (secMk A K x * secMk A K y * (secMk A K x)⁻¹ * (secMk A K y)⁻¹) * secMk A K y *
          secMk A K x := by group
    _ = secMk A K y * secMk A K x := by rw [h1]; group

theorem isElemAbelian_secImg {A K X : Subgroup G} [(K.subgroupOf A).Normal]
    (hX : IsElemAbelian 2 X) : IsElemAbelian 2 (secImg A K X) := by
  rw [isElemAbelian_iff]
  constructor
  · intro y₁ hy₁ y₂ hy₂
    obtain ⟨x₁, hx₁, rfl⟩ := mem_secImg.mp hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := mem_secImg.mp hy₂
    have := congrArg (secMk A K) (Subtype.ext (isElemAbelian_comm hX hx₁ hx₂) :
      x₁ * x₂ = x₂ * x₁)
    simpa using this
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
    have : x ^ 2 = 1 := Subtype.ext (by simpa using isElemAbelian_pow_eq_one hX hx)
    rw [← map_pow, this, map_one]

section Fin

variable [Finite G]

@[expose] noncomputable def mIdx (X Y : Subgroup G) : ℕ := padicValNat 2 (Y.relIndex X)

@[expose] def QCrit (V₁ Vp H B : Subgroup G) : Prop :=
  B ≤ H ∧ IsElemAbelian 2 B ∧ ¬ B ≤ pCoreOf 2 H ∧
    (∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure Vp H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁) ∧
    (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem isElemAbelian_tilde (h : HypF91 T V L V₁ Vp H) :
    IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUN : ∀ u ∈ conjClosure Vp H, u ∈ Subgroup.normalizer (V₁ : Set G) :=
    fun u hu => h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hu))
  rw [isElemAbelian_iff]
  constructor
  · intro y₁ hy₁ y₂ hy₂
    obtain ⟨u₁, hu₁, rfl⟩ := mem_secImg.mp hy₁
    obtain ⟨u₂, hu₂, rfl⟩ := mem_secImg.mp hy₂
    exact secMk_comm_of_commutator_mem (h.commutator_conjClosure_le _ hu₁ _ (hUQ hu₂))
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hy
    rw [← map_pow]
    exact secMk_eq_one_iff.mpr (h.sq_mem_conjClosure _ hu)

omit [Finite G] in
theorem tilde_le_normalizer {B : Subgroup G} (hBH : B ≤ H) :
    tildeOf V₁ B ≤ Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := mem_secImg.mp hy
  exact secMk_mem_normalizer_secImg (le_normalizer_conjClosure Vp H (hBH hb))

theorem tilde_inf_centralizer_pCoreOf (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    tildeOf V₁ B ⊓ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) =
        tildeOf V₁ (B ⊓ pCoreOf 2 H) := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUN : ∀ u ∈ conjClosure Vp H, u ∈ Subgroup.normalizer (V₁ : Set G) :=
    fun u hu => h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hu))
  ext y
  constructor
  · rintro ⟨hyB, hyC⟩
    obtain ⟨b, hb, rfl⟩ := mem_secImg.mp hyB
    refine mem_secImg.mpr ⟨b, ⟨hb, ?_⟩, rfl⟩
    rw [h.pCoreOf_eq_centralizerMod]
    refine ⟨hBH hb, h.H_normalizes_V₁ (hBH hb), fun u hu => ?_⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC
      (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hUN u hu⟩)
      (secMk_mem_secImg (x := ⟨u, hUN u hu⟩) hu)
    exact commutator_mem_of_secMk_commute (x := b) (y := ⟨u, hUN u hu⟩) hcomm.symm
  · intro hy
    obtain ⟨b, ⟨hbB, hbQ⟩, rfl⟩ := mem_secImg.mp hy
    refine ⟨secMk_mem_secImg hbB, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hy'
    have hbQ' := (h.pCoreOf_eq_centralizerMod ▸ hbQ : (b : G) ∈ centralizerMod V₁ H
      (conjClosure Vp H))
    exact (secMk_comm_of_commutator_mem (x := b) (y := u) (by
      have := hbQ'.2.2 u hu
      exact this)).symm

theorem tilde_inf_centralizer_mod (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) =
        tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) B) := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUN : ∀ u ∈ conjClosure Vp H, u ∈ Subgroup.normalizer (V₁ : Set G) :=
    fun u hu => h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hu))
  ext y
  constructor
  · rintro ⟨hyU, hyC⟩
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hyU
    refine mem_secImg.mpr ⟨u, ⟨hu, u.2, fun b hb => ?_⟩, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC
      (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨b, h.H_normalizes_V₁ (hBH hb)⟩)
      (secMk_mem_secImg (x := ⟨b, h.H_normalizes_V₁ (hBH hb)⟩) hb)
    exact commutator_mem_of_secMk_commute (x := u) (y := ⟨b, h.H_normalizes_V₁ (hBH hb)⟩)
      hcomm.symm
  · intro hy
    obtain ⟨u, ⟨huU, huN, hu⟩, rfl⟩ := mem_secImg.mp hy
    refine ⟨secMk_mem_secImg huU, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
    obtain ⟨b, hb, rfl⟩ := mem_secImg.mp hy'
    exact (secMk_comm_of_commutator_mem (x := u) (y := b) (hu b hb)).symm

theorem card_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    Nat.card (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) =
      (B ⊓ pCoreOf 2 H).relIndex B := by
  rw [card_autOn_eq_relIndex (tilde_le_normalizer hBH), h.tilde_inf_centralizer_pCoreOf hBH]
  exact relIndex_secImg_of_inf_le inf_le_left (hBH.trans h.H_normalizes_V₁)
    (inf_le_inf_left B h.V₁_le_pCoreOf)

theorem relIndex_tilde_fixV (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    (tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))).relIndex
        (tildeOf V₁ (conjClosure Vp H)) =
      (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  rw [h.tilde_inf_centralizer_mod hBH]
  refine relIndex_secImg ?_ (centralizerMod_le_left _ _ _)
    (fun u hu => h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hu)))
  intro c hc
  refine ⟨le_conjClosure Vp H (h.V₁_le_Vp hc), (Subgroup.le_normalizer hc), fun b hb => ?_⟩
  have hb' : b * c⁻¹ * b⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (hBH hb)) c⁻¹).mp (V₁.inv_mem hc)
  have : c * b * c⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by group
  rw [this]
  exact V₁.mul_mem hc hb'

theorem mem_Qset_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H)
    (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 H)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure Vp H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁)
    (hr : (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2) :
    autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  have hŨ := h.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure Vp H)) := commGroupOfElemAbelian hŨ
  have hBt : IsElemAbelian 2 (tildeOf V₁ B) := isElemAbelian_secImg hBel
  have hn := tilde_le_normalizer (V₁ := V₁) (Vp := Vp) hBH
  have hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (V₁ : Set G) := fun b hb =>
    h.H_normalizes_V₁ (hBH hb)
  have hA2 : IsA2 (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) := by
    refine ⟨autOn_le_autOn _ (secImg_mono hBH), ?_, isElemAbelian2_autOn hŨ hBt hn⟩
    refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle
    apply hnt
    intro b hb
    have hy : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (⟨b, hN b hb⟩ : Subgroup.normalizer
        (V₁ : Set G)) ∈ tildeOf V₁ B ⊓ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
      ⟨secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb, hle (secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb)⟩
    rw [h.tilde_inf_centralizer_pCoreOf hBH] at hy
    obtain ⟨b', ⟨hb'B, hb'Q⟩, hbb'⟩ := mem_secImg.mp hy
    have h1 := secMk_eq_secMk_iff.mp hbb'
    have hc : ((b' : G))⁻¹ * b ∈ pCoreOf 2 H := h.V₁_le_pCoreOf h1
    have e : b = (b' : G) * ((b' : G)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ hb'Q hc
  refine ⟨⟨hA2, ?_⟩, ?_⟩
  · rw [rAV_le_two_iff (fun w => Subtype.ext (by simpa using hŨ.2 w w.2)) hA2]
    have c1 := card_autOn_tilde h hBH
    have c2 := card_fixV_autOn_eq hŨ hn
    have c3 := h.relIndex_tilde_fixV hBH
    have hmul := Subgroup.relIndex_mul_card (tildeOf V₁ (conjClosure Vp H) ⊓
      Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))
      (tildeOf V₁ (conjClosure Vp H))
    rw [inf_eq_left.mpr (inf_le_left : tildeOf V₁ (conjClosure Vp H) ⊓
      Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) ≤
        tildeOf V₁ (conjClosure Vp H))] at hmul
    rw [c1, c2]
    calc Nat.card ↥(tildeOf V₁ (conjClosure Vp H))
        = (tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))).relIndex
            (tildeOf V₁ (conjClosure Vp H)) *
          Nat.card ↥(tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
            Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) := hmul.symm
      _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 *
          Nat.card ↥(tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
            Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) := by
        rw [c3]; exact Nat.mul_le_mul_right _ hr
  · rw [← isQuadratic_iff_commSeries_two]
    refine isQuadratic_autOn_of_forall hŨ ?_
    intro s₁ hs₁ s₂ hs₂ w hw
    obtain ⟨b₁, hb₁, rfl⟩ := mem_secImg.mp hs₁
    obtain ⟨b₂, hb₂, rfl⟩ := mem_secImg.mp hs₂
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
    have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        (b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹) = 1 :=
      secMk_eq_one_iff.mpr (by simpa using hquad b₁ hb₁ b₂ hb₂ u hu)
    simpa [map_mul, map_inv] using h1

theorem qInt_tilde_le_two_of_mem (h : HypF91 T V L V₁ Vp H) {A : Subgroup (MulAut
      ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hA : A ∈ @Qset ↥(tildeOf V₁ (conjClosure Vp H))
      (commGroupOfElemAbelian h.isElemAbelian_tilde)
      (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))) :
    qInt (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) h.isElemAbelian_tilde ≤ 2 :=
  @qOf_le_two_of_mem_Qset _ (commGroupOfElemAbelian h.isElemAbelian_tilde) inferInstance _ _ hA

theorem mem_Qset_autOn_tilde_conj (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H)
    (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 H)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure Vp H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁)
    (hr : (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2) {k : G} (hk : k ∈ H) :
    autOn (tildeOf V₁ (conjSub k B)) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  have hkU : conjSub k (conjClosure Vp H) = conjClosure Vp H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hk)
  have hkU' : conjSub k⁻¹ (conjClosure Vp H) = conjClosure Vp H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H (H.inv_mem hk))
  have hkQ : conjSub k (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hk)
  have hkQ' : conjSub k⁻¹ (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H (H.inv_mem hk))
  have hkV : conjSub k V₁ = V₁ :=
    F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hk)
  refine h.mem_Qset_autOn_tilde (B := conjSub k B) ?_ (isElemAbelian_conjSub hBel) ?_ ?_ ?_
  · intro x hx
    have := hBH (mem_conjSub.mp hx)
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hk this) (H.inv_mem hk)
  · intro hle
    apply hnt
    have := (conjSub_le_iff k).mp hle
    rwa [hkQ'] at this
  · intro b₁ hb₁ b₂ hb₂ u hu
    have hb₁' := mem_conjSub.mp hb₁
    have hb₂' := mem_conjSub.mp hb₂
    have hu' : k⁻¹ * u * k ∈ conjClosure Vp H := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure Vp H (H.inv_mem hk)) u).mp hu
    have e1 := hquad _ hb₁' _ hb₂' _ hu'
    have hkm := (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ hk) _).mp e1
    have eq : b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ =
        k * ((k⁻¹ * b₂ * k) * ((k⁻¹ * b₁ * k) * (k⁻¹ * u * k) * (k⁻¹ * b₁ * k)⁻¹ *
          (k⁻¹ * u * k)⁻¹) * (k⁻¹ * b₂ * k)⁻¹ * ((k⁻¹ * b₁ * k) * (k⁻¹ * u * k) *
          (k⁻¹ * b₁ * k)⁻¹ * (k⁻¹ * u * k)⁻¹)⁻¹) * k⁻¹ := by group
    rw [eq]
    exact hkm
  · have hrel : ∀ (X Y : Subgroup G), (conjSub k X).relIndex (conjSub k Y) = X.relIndex Y :=
      fun X Y => Subgroup.relIndex_map_map_of_injective X Y (MulAut.conj k).injective
    have e2 : centralizerMod V₁ (conjClosure Vp H) (conjSub k B) =
        conjSub k (centralizerMod V₁ (conjClosure Vp H) B) := by
      rw [conjSub_centralizerMod, hkV, hkU]
    have e3 : conjSub k B ⊓ pCoreOf 2 H = conjSub k (B ⊓ pCoreOf 2 H) := by
      rw [conjSub_inf, hkQ]
    calc (centralizerMod V₁ (conjClosure Vp H) (conjSub k B)).relIndex (conjClosure Vp H)
        = (conjSub k (centralizerMod V₁ (conjClosure Vp H) B)).relIndex
            (conjSub k (conjClosure Vp H)) := by rw [e2, hkU]
      _ = (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) := hrel _ _
      _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hr
      _ = ((conjSub k B ⊓ pCoreOf 2 H).relIndex (conjSub k B)) ^ 2 := by rw [e3, hrel]

omit [Finite G] in
theorem qcrit_conj (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hB : QCrit V₁ Vp H B) {k : G}
    (hk : k ∈ H) : QCrit V₁ Vp H (conjSub k B) := by
  obtain ⟨hBH, hBel, hnt, hquad, hr⟩ := hB
  have hkU : conjSub k (conjClosure Vp H) = conjClosure Vp H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hk)
  have hkU' : conjSub k⁻¹ (conjClosure Vp H) = conjClosure Vp H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H (H.inv_mem hk))
  have hkQ : conjSub k (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hk)
  have hkQ' : conjSub k⁻¹ (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H (H.inv_mem hk))
  have hkV : conjSub k V₁ = V₁ :=
    F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hk)
  refine ⟨?_, isElemAbelian_conjSub hBel, ?_, ?_, ?_⟩
  · intro x hx
    have := hBH (mem_conjSub.mp hx)
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hk this) (H.inv_mem hk)
  · intro hle
    apply hnt
    have := (conjSub_le_iff k).mp hle
    rwa [hkQ'] at this
  · intro b₁ hb₁ b₂ hb₂ u hu
    have hb₁' := mem_conjSub.mp hb₁
    have hb₂' := mem_conjSub.mp hb₂
    have hu' : k⁻¹ * u * k ∈ conjClosure Vp H := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure Vp H (H.inv_mem hk)) u).mp hu
    have e1 := hquad _ hb₁' _ hb₂' _ hu'
    have hkm := (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ hk) _).mp e1
    have eq : b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ =
        k * ((k⁻¹ * b₂ * k) * ((k⁻¹ * b₁ * k) * (k⁻¹ * u * k) * (k⁻¹ * b₁ * k)⁻¹ *
          (k⁻¹ * u * k)⁻¹) * (k⁻¹ * b₂ * k)⁻¹ * ((k⁻¹ * b₁ * k) * (k⁻¹ * u * k) *
          (k⁻¹ * b₁ * k)⁻¹ * (k⁻¹ * u * k)⁻¹)⁻¹) * k⁻¹ := by group
    rw [eq]
    exact hkm
  · have hrel : ∀ (X Y : Subgroup G), (conjSub k X).relIndex (conjSub k Y) = X.relIndex Y :=
      fun X Y => Subgroup.relIndex_map_map_of_injective X Y (MulAut.conj k).injective
    have e2 : centralizerMod V₁ (conjClosure Vp H) (conjSub k B) =
        conjSub k (centralizerMod V₁ (conjClosure Vp H) B) := by
      rw [conjSub_centralizerMod, hkV, hkU]
    have e3 : conjSub k B ⊓ pCoreOf 2 H = conjSub k (B ⊓ pCoreOf 2 H) := by
      rw [conjSub_inf, hkQ]
    calc (centralizerMod V₁ (conjClosure Vp H) (conjSub k B)).relIndex (conjClosure Vp H)
        = (conjSub k (centralizerMod V₁ (conjClosure Vp H) B)).relIndex
            (conjSub k (conjClosure Vp H)) := by rw [e2, hkU]
      _ = (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) := hrel _ _
      _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hr
      _ = ((conjSub k B ⊓ pCoreOf 2 H).relIndex (conjSub k B)) ^ 2 := by rw [e3, hrel]

theorem mem_Qset_of_qcrit (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hB : QCrit V₁ Vp H B) :
    autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) :=
  h.mem_Qset_autOn_tilde hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2

theorem mem_Qset_of_qcrit_conj (h : HypF91 T V L V₁ Vp H) {B : Subgroup G}
    (hB : QCrit V₁ Vp H B) {k : G} (hk : k ∈ H) :
    autOn (tildeOf V₁ (conjSub k B)) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) :=
  h.mem_Qset_autOn_tilde_conj hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2 hk

end HypF91

end Fin

end CFSG.Quasithin
