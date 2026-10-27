module

public import CFSG.Quasithin.H13.QRCPairedSylow

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
  CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS
open scoped MatrixGroups

variable {A : Type*} [Group A] {k : Type} [Field k]

section Lemmas

theorem mem_normalizer_sup {X Y : Subgroup A} {g : A} (hX : g ∈ normalizer (X : Set A))
    (hY : g ∈ normalizer (Y : Set A)) : g ∈ normalizer ((X ⊔ Y : Subgroup A) : Set A) := by
  have h1 : (X ⊔ Y).map (MulAut.conj g).toMonoidHom = X ⊔ Y := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer' hX, map_conj_eq_of_mem_normalizer' hY]
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← h1]
    exact ⟨y, hy, rfl⟩
  · rw [← h1] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h2 : g * z * g⁻¹ = g * y * g⁻¹ := hzy
      simpa using h2
    rwa [← this]

theorem sup_inf_eq_of_normalizes {W R K : Subgroup A} (hRW : R ≤ normalizer (W : Set A))
    (hWK : W ≤ K) (hKR : K ⊓ R = ⊥) : (W ⊔ R) ⊓ K = W := by
  refine le_antisymm (fun p hp => ?_) (le_inf le_sup_left hWK)
  obtain ⟨hp1, hp2⟩ := mem_inf.1 hp
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left W R hRW] at hp1
  obtain ⟨u, hu, r, hr, rfl⟩ := hp1
  have hrK : r ∈ K := by
    have := K.mul_mem (K.inv_mem (hWK hu)) hp2
    rwa [inv_mul_cancel_left] at this
  have hr1 : r = 1 := by
    have : r ∈ K ⊓ R := ⟨hrK, hr⟩
    rwa [hKR, mem_bot] at this
  subst hr1
  simpa using hu

theorem stdSub_normalizer_le {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup SL(2, k)) :
    stdSub θ (normalizer (Z : Set SL(2, k))) ≤ normalizer ((stdSub θ Z : Subgroup A) : Set A) := by
  intro x hx
  obtain ⟨hxX, hxN⟩ := mem_stdSub.1 hx
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨hyX, hyZ⟩ := mem_stdSub.1 hy
    have hm : x * y * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX)
    refine mem_stdSub.2 ⟨hm, ?_⟩
    have : (⟨x * y * x⁻¹, hm⟩ : X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ * ⟨x, hxX⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hxN _).1 hyZ
  · obtain ⟨hyX', hyZ⟩ := mem_stdSub.1 hy
    have hyX : y ∈ X := by
      have := X.mul_mem (X.mul_mem (X.inv_mem hxX) hyX') hxX
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
    refine mem_stdSub.2 ⟨hyX, ?_⟩
    have : (⟨x * y * x⁻¹, hyX'⟩ : X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ * ⟨x, hxX⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv] at hyZ
    exact (mem_normalizer_iff.1 hxN _).2 hyZ

theorem stdSub_injective {X : Subgroup A} (θ : X ≃* SL(2, k)) {Z Z' : Subgroup SL(2, k)}
    (h : stdSub θ Z = stdSub θ Z') : Z = Z' :=
  map_injective (f := θ.symm.toMonoidHom) θ.symm.injective
    (map_injective X.subtype_injective h)

variable [CharP k 2]

theorem upperUnipotent_le_borel : sl2UpperUnipotentSubgroup k ≤ sl2Borel k :=
  sl2_upperUnipotent_sup_torus (k := k) ▸ le_sup_left

theorem fieldAut_eq_one_of_torus (σ : RingAut k)
    (h : ∀ a : kˣ, Matrix.SpecialLinearGroup.map σ.toRingHom (splitTorusSLHom k a) *
      (splitTorusSLHom k a)⁻¹ ∈ sl2UpperUnipotentSubgroup k) : σ = 1 := by
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero, RingAut.one_apply]
  · have h1 := h (Units.mk0 x hx)
    rw [sl2_map_splitTorus, ← map_inv, ← map_mul] at h1
    have h2 : splitTorusSLHom k (Units.map σ.toRingHom.toMonoidHom (Units.mk0 x hx) *
        (Units.mk0 x hx)⁻¹) ∈ sl2UpperUnipotentSubgroup k ⊓ (splitTorusSLHom k).range :=
      ⟨h1, ⟨_, rfl⟩⟩
    rw [sl2_upperUnipotent_inf_torus, mem_bot, ← map_one (splitTorusSLHom k)] at h2
    have h3 := splitTorusSLHom_injective h2
    rw [mul_inv_eq_one] at h3
    have h4 := congrArg Units.val h3
    simpa using h4

variable [Finite k] {n : ℕ}

theorem borel_ne_top (hk : Nat.card k = 2 ^ n) : sl2Borel k ≠ ⊤ := by
  have h := (benderData_sl2 hk).isCoatom.1
  rwa [sl2_normalizer_upperUnipotent] at h

theorem mem_borel_of_conj_le (hk : Nat.card k = 2 ^ n) (hn : 1 ≤ n) {g : SL(2, k)}
    (hg : ∀ b ∈ sl2Borel k, g * b * g⁻¹ ∈ sl2Borel k) : g ∈ sl2Borel k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := benderData_sl2 hk
  set Ū := sl2UpperUnipotentSubgroup k
  have hidx : ¬ 2 ∣ Ū.relIndex (sl2Borel k) := by
    rw [← sl2_normalizer_upperUnipotent, hD.relIndex]
    intro h
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hle : Ū.map (MulAut.conj g).toMonoidHom ≤ Ū := by
    refine le_of_isPGroup_of_not_dvd_relIndex hD.isPGroup upperUnipotent_le_borel hidx
      (hD.isPGroup.map _) ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact hg u (upperUnipotent_le_borel hu)
    · rintro _ ⟨u, hu, rfl⟩
      rw [sl2_normalizer_upperUnipotent]
      exact hg u (upperUnipotent_le_borel hu)
  have heq : Ū.map (MulAut.conj g).toMonoidHom = Ū :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective])
  have hN : g ∈ normalizer (Ū : Set SL(2, k)) := by
    refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [← heq]
      exact ⟨y, hy, rfl⟩
    · rw [← heq] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have h2 : g * z * g⁻¹ = g * y * g⁻¹ := hzy
        simpa using h2
      rwa [← this]
  rwa [sl2_normalizer_upperUnipotent] at hN

theorem mem_stdSub_borel_of_conj (hk : Nat.card k = 2 ^ n) (hn : 1 ≤ n) {X W : Subgroup A}
    (θ : X ≃* SL(2, k)) (hBW : stdSub θ (sl2Borel k) ≤ W) (hXW : ¬ X ≤ W) {x : A} (hx : x ∈ X)
    (hxB : ∀ b ∈ stdSub θ (sl2Borel k), x * b * x⁻¹ ∈ W) : x ∈ stdSub θ (sl2Borel k) := by
  set W' : Subgroup SL(2, k) := (W.subgroupOf X).map θ.toMonoidHom with hW'
  have hmemW' : ∀ y : X, θ y ∈ W' ↔ (y : A) ∈ W := fun y =>
    ⟨fun ⟨z, hz, hzy⟩ => (θ.injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
  have hBW' : sl2Borel k ≤ W' := by
    intro b hb
    rw [← θ.apply_symm_apply b, hmemW']
    exact hBW (coe_symm_mem_stdSub θ hb)
  have hW'top : W' ≠ ⊤ := by
    intro h
    apply hXW
    intro y hy
    have := (hmemW' ⟨y, hy⟩).1 (h ▸ mem_top _)
    exact this
  have hW'B : W' = sl2Borel k := by
    rcases hBW'.lt_or_eq with h | h
    · have hco := (benderData_sl2 hk).isCoatom
      rw [sl2_normalizer_upperUnipotent] at hco
      exact absurd (hco.2 _ h) hW'top
    · exact h.symm
  refine mem_stdSub.2 ⟨hx, mem_borel_of_conj_le hk hn fun b hb => ?_⟩
  have h1 := hxB _ (coe_symm_mem_stdSub θ hb)
  have hm : x * ((θ.symm b : X) : A) * x⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem hx (θ.symm b).2) (X.inv_mem hx)
  have h2 := (hmemW' ⟨_, hm⟩).2 h1
  rw [hW'B] at h2
  have : (⟨x * ((θ.symm b : X) : A) * x⁻¹, hm⟩ : X) = ⟨x, hx⟩ * θ.symm b * ⟨x, hx⟩⁻¹ := rfl
  rwa [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2

end Lemmas

section Borel

variable [CharP k 2] [Finite k] {n : ℕ} {K₁ K₂ : Subgroup A}

theorem paired_borel (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : A, (∀ x ∈ K₁ ⊔ K₂, a * x = x * a) → a = 1)
    {θ₁ : K₁ ≃* SL(2, k)} {θ₂ : K₂ ≃* SL(2, k)} {R : Subgroup A} (S : Sylow 2 A)
    (hKR : (K₁ ⊔ K₂) ⊓ R = ⊥) (hKRt : (K₁ ⊔ K₂) ⊔ R = ⊤) (hR : ∀ r ∈ R, IsFieldPerm θ₁ θ₂ r)
    (hsw : ∃ r ∈ R, K₁.map (MulAut.conj r).toMonoidHom = K₂)
    (hS : (S : Subgroup A) = stdSub θ₁ (sl2UpperUnipotentSubgroup k) ⊔
      stdSub θ₂ (sl2UpperUnipotentSubgroup k) ⊔ R)
    {B : Subgroup A} (hSB : (S : Subgroup A) ≤ B) (hBtop : B < ⊤)
    (hBmax : ∀ Y : Subgroup A, (S : Subgroup A) ≤ Y → Y < ⊤ → Y ≤ B) :
    B = stdSub θ₁ (sl2Borel k) ⊔ stdSub θ₂ (sl2Borel k) ⊔ R ∧
    B ⊓ (K₁ ⊔ K₂) = stdSub θ₁ (sl2Borel k) ⊔ stdSub θ₂ (sl2Borel k) ∧
    (S : Subgroup A) ⊓ (K₁ ⊔ K₂) = stdSub θ₁ (sl2UpperUnipotentSubgroup k) ⊔
      stdSub θ₂ (sl2UpperUnipotentSubgroup k) ∧
    inSubgroup (pCore 2) B = stdSub θ₁ (sl2UpperUnipotentSubgroup k) ⊔
      stdSub θ₂ (sl2UpperUnipotentSubgroup k) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  set K := K₁ ⊔ K₂ with hKdef
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  set Bb := sl2Borel k with hBb
  set U := stdSub θ₁ Ū ⊔ stdSub θ₂ Ū with hUdef
  set B₁₂ := stdSub θ₁ Bb ⊔ stdSub θ₂ Bb with hB₁₂
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hn1 : 1 ≤ n := by omega
  obtain ⟨s, hsR, hs⟩ := hsw
  have hs' : K₂.map (MulAut.conj s⁻¹).toMonoidHom = K₁ := by
    rw [← hs, ← map_conj_mul, inv_mul_cancel]
    have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
      ext y
      simp
    rw [this, map_id]
  have hRB : R ≤ normalizer (B₁₂ : Set A) := fieldPerm_le_normalizer hR borel_fieldStable
  have hRU : R ≤ normalizer (U : Set A) := fieldPerm_le_normalizer hR upperUnipotent_fieldStable
  have hB₁₂K : B₁₂ ≤ K := sup_le_sup (stdSub_le _ _) (stdSub_le _ _)
  have hUK : U ≤ K := sup_le_sup (stdSub_le _ _) (stdSub_le _ _)
  have hUB : U ≤ B₁₂ := sup_le_sup (stdSub_mono _ upperUnipotent_le_borel)
    (stdSub_mono _ upperUnipotent_le_borel)
  set N := B₁₂ ⊔ R with hNdef
  have hNK : N ⊓ K = B₁₂ := sup_inf_eq_of_normalizes hRB hB₁₂K hKR
  have hSN : (S : Subgroup A) ≤ N := by
    rw [hS]
    exact sup_le_sup_right hUB R
  have hNtop : N < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have h1 : K₁ ≤ B₁₂ := by
      rw [← hNK, h, top_inf_eq]
      exact le_sup_left
    have h2 : K₁ ≤ stdSub θ₁ Bb := by
      have h3 := sup_inf_eq_of_le hc hd (stdSub_le θ₁ Bb)
      rw [← h3]
      exact le_inf (h1.trans (sup_le_sup_left (stdSub_le θ₂ Bb) _)) le_rfl
    apply borel_ne_top hk
    apply stdSub_injective θ₁
    rw [stdSub_top]
    exact le_antisymm (stdSub_le _ _) h2
  have hNB : N ≤ B := hBmax N hSN hNtop
  have hsB : s ∈ B := hSB (hS ▸ (le_sup_right : R ≤ U ⊔ R) hsR)
  have hK₁B : ¬ K₁ ≤ B := by
    intro h
    have hK₂B : K₂ ≤ B := by
      rw [← hs]
      rintro _ ⟨y, hy, rfl⟩
      exact B.mul_mem (B.mul_mem hsB (h hy)) (B.inv_mem hsB)
    apply hBtop.ne
    rw [eq_top_iff, ← hKRt]
    exact sup_le (sup_le h hK₂B) ((le_sup_right : R ≤ N).trans hNB)
  have hK₂B : ¬ K₂ ≤ B := by
    intro h
    apply hK₁B
    rw [← hs']
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (B.mul_mem (B.inv_mem hsB) (h hy)) (B.inv_mem (B.inv_mem hsB))
  have hB₁B : stdSub θ₁ Bb ≤ B := (le_sup_left.trans (le_sup_left : B₁₂ ≤ N)).trans hNB
  have hB₂B : stdSub θ₂ Bb ≤ B := (le_sup_right.trans (le_sup_left : B₁₂ ≤ N)).trans hNB
  have hBK : B ⊓ K = B₁₂ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left.trans hNB) hB₁₂K)
    obtain ⟨hxB, hxK⟩ := mem_inf.1 hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hxK
    have hm₁ : x₁ ∈ stdSub θ₁ Bb := by
      refine mem_stdSub_borel_of_conj hk hn1 θ₁ hB₁B hK₁B hx₁ fun b hb => ?_
      have hbK : b ∈ K₁ := stdSub_le _ _ hb
      have h1 := B.mul_mem (B.mul_mem hxB (hB₁B hb)) (B.inv_mem hxB)
      rwa [show x₁ * x₂ * b * (x₁ * x₂)⁻¹ = x₁ * (x₂ * b * x₂⁻¹) * x₁⁻¹ by group,
        ← hc b hbK x₂ hx₂, mul_inv_cancel_right] at h1
    have hm₂ : x₂ ∈ stdSub θ₂ Bb := by
      refine mem_stdSub_borel_of_conj hk hn1 θ₂ hB₂B hK₂B hx₂ fun b hb => ?_
      have hbK : b ∈ K₂ := stdSub_le _ _ hb
      have h1 := B.mul_mem (B.mul_mem hxB (hB₂B hb)) (B.inv_mem hxB)
      rwa [show x₁ * x₂ * b * (x₁ * x₂)⁻¹ = x₁ * (x₂ * b * x₂⁻¹) * x₁⁻¹ by group,
        hc x₁ hx₁ _ (K₂.mul_mem (K₂.mul_mem hx₂ hbK) (K₂.inv_mem hx₂)),
        mul_inv_cancel_right] at h1
    exact mul_mem_sup hm₁ hm₂
  have hBN : B = N := by
    refine le_antisymm (fun b hb => ?_) hNB
    have hbKR : b ∈ K ⊔ R := hKRt ▸ mem_top b
    rw [← SetLike.mem_coe, normal_mul K R] at hbKR
    obtain ⟨x, hx, r, hr, rfl⟩ := hbKR
    have hrB : r ∈ B := hNB ((le_sup_right : R ≤ N) hr)
    have hxB : x ∈ B := by
      have := B.mul_mem hb (B.inv_mem hrB)
      rwa [mul_inv_cancel_right] at this
    have hxB₁₂ : x ∈ B₁₂ := hBK ▸ ⟨hxB, hx⟩
    exact mul_mem_sup hxB₁₂ hr
  have hSK : (S : Subgroup A) ⊓ K = U := by
    rw [hS]
    exact sup_inf_eq_of_normalizes hRU hUK hKR
  refine ⟨hBN, hBK, hSK, ?_⟩
  have hU2 : IsPGroup 2 U :=
    (isPGroup_stdSub_upperUnipotent hk θ₁).to_sup_of_normal_left'
      (isPGroup_stdSub_upperUnipotent hk θ₂) (le_normalizer_of_commute fun a ha b hb =>
        hc a (stdSub_le _ _ ha) b (stdSub_le _ _ hb))
  have hB₁U : stdSub θ₁ Bb ≤ normalizer (U : Set A) := by
    intro b hb
    refine mem_normalizer_sup ?_ ?_
    · have h1 := stdSub_normalizer_le θ₁ Ū
      rw [sl2_normalizer_upperUnipotent] at h1
      exact h1 hb
    · exact mem_normalizer_of_commute fun y hy =>
        hc b (stdSub_le _ _ hb) y (stdSub_le _ _ hy)
  have hB₂U : stdSub θ₂ Bb ≤ normalizer (U : Set A) := by
    intro b hb
    refine mem_normalizer_sup ?_ ?_
    · exact mem_normalizer_of_commute fun y hy =>
        hc' b (stdSub_le _ _ hb) y (stdSub_le _ _ hy)
    · have h1 := stdSub_normalizer_le θ₂ Ū
      rw [sl2_normalizer_upperUnipotent] at h1
      exact h1 hb
  have hBU : B ≤ normalizer (U : Set A) := by
    rw [hBN]
    exact sup_le (sup_le hB₁U hB₂U) hRU
  have hUO : U ≤ inSubgroup (pCore 2) B :=
    le_inSubgroup_pCore ((hUB.trans le_sup_left).trans hNB) hBU hU2
  refine le_antisymm (fun y hy => ?_) hUO
  set Y := inSubgroup (pCore 2) B with hYdef
  have hY2 : IsPGroup 2 Y := (pCore_isPGroup (p := 2) (G := B)).map _
  have hYn : B ≤ normalizer (Y : Set A) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic B (pCore 2 B))
  have hYB : Y ≤ B := map_subtype_le _
  have hYS : Y ≤ S := by
    have h1 := S.is_maximal' (hY2.to_sup_of_normal_left' S.isPGroup' (hSB.trans hYn))
      le_sup_right
    rw [← h1]
    exact le_sup_left
  have hyS : y ∈ (S : Subgroup A) := hYS hy
  rw [hS, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left U R hRU] at hyS
  obtain ⟨u, hu, r, hr, rfl⟩ := hyS
  have hrY : r ∈ Y := by
    have := Y.mul_mem (Y.inv_mem (hUO hu)) hy
    rwa [inv_mul_cancel_left] at this
  have hcomm : ∀ c ∈ B, c ∈ K → r * c * r⁻¹ * c⁻¹ ∈ U := by
    intro c hcB hcK
    have h1 : r * c * r⁻¹ * c⁻¹ ∈ Y := by
      have h2 := (mem_normalizer_iff.1 (hYn hcB) r⁻¹).1 (Y.inv_mem hrY)
      rw [show r * c * r⁻¹ * c⁻¹ = r * (c * r⁻¹ * c⁻¹) by group]
      exact Y.mul_mem hrY h2
    have h3 : r * c * r⁻¹ * c⁻¹ ∈ K := K.mul_mem (hKn.conj_mem c hcK r) (K.inv_mem hcK)
    rw [← hSK]
    exact ⟨hYS h1, h3⟩
  have htB : (splitTorusSLHom k).range ≤ Bb := by
    rw [hBb, ← sl2_upperUnipotent_sup_torus]
    exact le_sup_right
  have htor₁ : ∀ a : kˣ, ((θ₁.symm (splitTorusSLHom k a) : K₁) : A) ∈ B ∧
      ((θ₁.symm (splitTorusSLHom k a) : K₁) : A) ∈ K := fun a =>
    ⟨hB₁B (coe_symm_mem_stdSub θ₁ (htB ⟨a, rfl⟩)), mem_sup_left (θ₁.symm _).2⟩
  have htor₂ : ∀ a : kˣ, ((θ₂.symm (splitTorusSLHom k a) : K₂) : A) ∈ B ∧
      ((θ₂.symm (splitTorusSLHom k a) : K₂) : A) ∈ K := fun a =>
    ⟨hB₂B (coe_symm_mem_stdSub θ₂ (htB ⟨a, rfl⟩)), mem_sup_right (θ₂.symm _).2⟩
  have hU₁ : U ⊓ K₁ ≤ stdSub θ₁ Ū := by
    rw [← sup_inf_eq_of_le hc hd (stdSub_le θ₁ Ū)]
    exact inf_le_inf_right _ (sup_le_sup_left (stdSub_le θ₂ Ū) _)
  have hU₂ : U ⊓ K₂ ≤ stdSub θ₂ Ū := by
    rw [← sup_inf_eq_of_le hc' (by rw [inf_comm]; exact hd) (stdSub_le θ₂ Ū)]
    rw [sup_comm] at hUdef
    exact inf_le_inf_right _ (hUdef ▸ sup_le_sup_left (stdSub_le θ₁ Ū) _)
  have hfix : ∀ {X : Subgroup A} {θ : X ≃* SL(2, k)} {σ : RingAut k},
      ActsAsField θ θ r σ → (∀ a : kˣ, ((θ.symm (splitTorusSLHom k a) : X) : A) ∈ B ∧
        ((θ.symm (splitTorusSLHom k a) : X) : A) ∈ K) → U ⊓ X ≤ stdSub θ Ū → σ = 1 := by
    intro X θ σ hθ htor hUX
    refine fieldAut_eq_one_of_torus σ fun a => ?_
    set c : X := θ.symm (splitTorusSLHom k a)
    have hcX : r * c * r⁻¹ * (c : A)⁻¹ ∈ X := X.mul_mem (hθ.mem c.2) (X.inv_mem c.2)
    have h1 := hUX ⟨hcomm c (htor a).1 (htor a).2, hcX⟩
    obtain ⟨hx', h2⟩ := mem_stdSub.1 h1
    have : (⟨r * c * r⁻¹ * (c : A)⁻¹, hcX⟩ : X) = ⟨r * c * r⁻¹, hθ.mem c.2⟩ * c⁻¹ := rfl
    rwa [this, map_mul, map_inv, hθ.apply, MulEquiv.apply_symm_apply] at h2
  have hr1 : r = 1 := by
    obtain ⟨σ₁, σ₂, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := hR r hr
    · have e₁ := hfix h₁ htor₁ hU₁
      have e₂ := hfix h₂ htor₂ hU₂
      subst e₁ e₂
      refine hCK r fun x hx => ?_
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hx
      have f₁ : r * x₁ * r⁻¹ = x₁ := by
        have := h₁.apply ⟨x₁, hx₁⟩
        rw [sl_map_one] at this
        exact congrArg Subtype.val (θ₁.injective this)
      have f₂ : r * x₂ * r⁻¹ = x₂ := by
        have := h₂.apply ⟨x₂, hx₂⟩
        rw [sl_map_one] at this
        exact congrArg Subtype.val (θ₂.injective this)
      calc r * (x₁ * x₂) = (r * x₁ * r⁻¹) * (r * x₂ * r⁻¹) * r := by group
        _ = x₁ * x₂ * r := by rw [f₁, f₂]
    · exfalso
      have hku : 1 < Nat.card kˣ := by
        rw [Nat.card_units, hk]
        have : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := rfl
            _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
        omega
      obtain ⟨a, ha⟩ := @exists_ne kˣ (Finite.one_lt_card_iff_nontrivial.1 hku) 1
      set c : K₁ := θ₁.symm (splitTorusSLHom k a)
      have hc₂ : r * c * r⁻¹ ∈ K₂ := h₁.mem c.2
      have h1 := hcomm c (htor₁ a).1 (htor₁ a).2
      obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := exists_mul_of_mem_sup_of_commute
        (fun a ha b hb => hc a (stdSub_le _ _ ha) b (stdSub_le _ _ hb)) h1
      have h2 : (c : A)⁻¹ * (r * c * r⁻¹) = u₁ * u₂ := by
        rw [hu, hc _ (K₁.inv_mem c.2) _ hc₂]
      obtain ⟨e₁, -⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hd (K₁.inv_mem c.2)
        (stdSub_le _ _ hu₁) hc₂ (stdSub_le _ _ hu₂) h2
      have h3 : (c : A) ∈ stdSub θ₁ Ū := by
        have := (stdSub θ₁ Ū).inv_mem (e₁ ▸ hu₁ : (c : A)⁻¹ ∈ stdSub θ₁ Ū)
        rwa [inv_inv] at this
      obtain ⟨hc', h4⟩ := mem_stdSub.1 h3
      have h5 : splitTorusSLHom k a ∈ Ū ⊓ (splitTorusSLHom k).range := by
        refine ⟨?_, ⟨a, rfl⟩⟩
        have : (⟨(c : A), c.2⟩ : K₁) = c := rfl
        rwa [this, MulEquiv.apply_symm_apply] at h4
      rw [sl2_upperUnipotent_inf_torus, mem_bot, ← map_one (splitTorusSLHom k)] at h5
      exact ha (splitTorusSLHom_injective h5)
  subst hr1
  simpa using hu

end Borel

end CFSG.Quasithin.H13.QRC
