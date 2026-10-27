module

public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.H13.GoldschmidtI51Trans
public import CFSG.Quasithin.H13.U3L14B56

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Matrix CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.A6

namespace SL3Aut

open SL3

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def act (A : S) (v : V3) : V3 := (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v

@[expose] def e0 : V3 := ![1, 0, 0]

theorem exists_act_e0 : ∀ v : V3, v ≠ 0 → ∃ A : S, act A e0 = v := by
  decide +kernel

theorem inX1_iff : ∀ A : S, InX1 A ↔ act A e0 = e0 := by
  decide +kernel

@[expose] def ThirdPt (p q r : V3) : Prop :=
  p = 0 ∨ q = 0 ∨ p = q ∨ r = 0 ∨ r = p ∨ r = q ∨ r = p + q ∨
    ∃ A : S, act A p = p ∧ act A q = q ∧ act A r ≠ r

instance (p q r : V3) : Decidable (ThirdPt p q r) := by
  unfold ThirdPt act
  infer_instance

theorem thirdPt_all : ∀ p q r : V3, ThirdPt p q r := by
  decide +kernel

theorem det_eq_one : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), (∀ v : V3, B *ᵥ v = 0 → v = 0) →
    B.det = 1 := by
  decide +kernel

theorem eq_one_of_commute : ∀ x : S, x * ex = ex * x → x * ey = ey * x → x * s1 = s1 * x →
    x * s2 = s2 * x → x = 1 := by
  decide +kernel

theorem vec_facts : (∀ v : V3, v + v = 0) ∧ (∀ p q : V3, p + q = 0 → p = q) ∧
    (∀ p q : V3, p + q = p → q = 0) ∧ (∀ p q : V3, p + q = q → p = 0) ∧ e0 ≠ 0 := by
  decide +kernel

theorem act_mul (A B : S) (v : V3) : act (A * B) v = act A (act B v) := by
  unfold act
  rw [mulVec_mulVec]
  rfl

theorem act_one (v : V3) : act 1 v = v := one_mulVec v

theorem act_add (A : S) (v w : V3) : act A (v + w) = act A v + act A w := by
  unfold act
  rw [mulVec_add]

theorem act_zero (A : S) : act A 0 = 0 := by
  unfold act
  rw [mulVec_zero]

theorem act_inv_act (A : S) (v : V3) : act A⁻¹ (act A v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (A : S) (v : V3) : act A (act A⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_ne_zero (A : S) {v : V3} (hv : v ≠ 0) : act A v ≠ 0 := by
  intro h
  apply hv
  rw [← act_inv_act A v, h, act_zero]

@[expose] def linOf (f : V3 →+ V3) : V3 →ₗ[ZMod 2] V3 where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h c with rfl | rfl <;> simp

theorem exists_eq_conj_of_X1 (β : S →* S) (hinj : Function.Injective β)
    (hX : ∀ x ∈ X1, β x ∈ X1) : ∃ A : S, ∀ x, β x = A * x * A⁻¹ := by
  obtain ⟨hvv, hpq, hpq1, hpq2, he0⟩ := vec_facts
  have hsurj : Function.Surjective β := Finite.injective_iff_surjective.1 hinj
  have hX' : ∀ x, β x ∈ X1 → x ∈ X1 := by
    intro x hx
    let r : ↥X1 → ↥X1 := fun y => ⟨β y, hX y y.2⟩
    have hr : Function.Injective r := fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hr) ⟨β x, hx⟩
    have : (y : S) = x := hinj (congrArg Subtype.val hy)
    exact this ▸ y.2
  have hmemX : ∀ x : S, x ∈ X1 ↔ act x e0 = e0 := fun x => inX1_iff x
  have hex : ∀ v : V3, ∃ A : S, v ≠ 0 → act A e0 = v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨1, fun h => absurd hv h⟩
    · obtain ⟨A, hA⟩ := exists_act_e0 v hv
      exact ⟨A, fun _ => hA⟩
  choose g hg using hex
  classical
  set f : V3 → V3 := fun v => if v = 0 then 0 else act (β (g v)) e0 with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hfv : ∀ v, v ≠ 0 → f v = act (β (g v)) e0 := fun v hv => by simp [hf, hv]
  have key : ∀ (A : S) (v : V3), v ≠ 0 → f (act A v) = act (β A) (f v) := by
    intro A v hv
    set w := act A v with hwdef
    have hw : w ≠ 0 := act_ne_zero A hv
    have h1 : act ((g w)⁻¹ * A * g v) e0 = e0 := by
      calc act ((g w)⁻¹ * A * g v) e0 = act (g w)⁻¹ (act A (act (g v) e0)) := by
            rw [act_mul, act_mul]
        _ = act (g w)⁻¹ (act (g w) e0) := by rw [hg v hv, hg w hw]
        _ = e0 := act_inv_act _ _
    have h2 := (hmemX _).1 (hX _ ((hmemX _).2 h1))
    rw [map_mul, map_mul, map_inv, act_mul, act_mul] at h2
    rw [hfv _ hw, hfv v hv]
    have := congrArg (act (β (g w))) h2
    rw [act_act_inv] at this
    exact this.symm
  have hfne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v hv => by
    rw [hfv v hv]
    exact act_ne_zero _ he0
  have hfinj : ∀ v w, v ≠ 0 → w ≠ 0 → f v = f w → v = w := by
    intro v w hv hw h
    rw [hfv v hv, hfv w hw] at h
    have h1 : act (β ((g w)⁻¹ * g v)) e0 = e0 := by
      rw [map_mul, map_inv, act_mul, h, act_inv_act]
    have h2 := (hmemX _).1 (hX' _ ((hmemX _).2 h1))
    rw [act_mul] at h2
    have := congrArg (act (g w)) h2
    rw [act_act_inv, hg v hv, hg w hw] at this
    exact this
  have hadd2 : ∀ p q, p ≠ 0 → q ≠ 0 → p ≠ q → f (p + q) = f p + f q := by
    intro p q hp hq hpq'
    have hr : p + q ≠ 0 := fun h => hpq' (hpq p q h)
    have hrp : p + q ≠ p := fun h => hq (hpq1 p q h)
    have hrq : p + q ≠ q := fun h => hp (hpq2 p q h)
    rcases thirdPt_all (f p) (f q) (f (p + q)) with h | h | h | h | h | h | h | ⟨B, hBp, hBq, hBr⟩
    · exact absurd h (hfne p hp)
    · exact absurd h (hfne q hq)
    · exact absurd (hfinj p q hp hq h) hpq'
    · exact absurd h (hfne _ hr)
    · exact absurd (hfinj _ p hr hp h) hrp
    · exact absurd (hfinj _ q hr hq h) hrq
    · exact h
    · exfalso
      obtain ⟨A, rfl⟩ := hsurj B
      have hAp : act A p = p := hfinj _ _ (act_ne_zero A hp) hp (by rw [key A p hp, hBp])
      have hAq : act A q = q := hfinj _ _ (act_ne_zero A hq) hq (by rw [key A q hq, hBq])
      apply hBr
      rw [← key A _ hr, act_add, hAp, hAq]
  have hadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    by_cases hv : v = 0
    · rw [hv, zero_add, hf0, zero_add]
    by_cases hw : w = 0
    · rw [hw, add_zero, hf0, add_zero]
    by_cases hvw : v = w
    · rw [hvw, hvv, hf0, hvv]
    exact hadd2 v w hv hw hvw
  set F : V3 →+ V3 := { toFun := f, map_zero' := hf0, map_add' := hadd } with hF
  set B : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' (linOf F) with hB
  have hBv : ∀ v, B *ᵥ v = f v := fun v => LinearMap.toMatrix'_mulVec (linOf F) v
  have hdet : B.det = 1 := det_eq_one B fun v hv => by
    by_contra h
    exact hfne v h (by rw [← hBv]; exact hv)
  set A : S := ⟨B, hdet⟩ with hA
  refine ⟨A, fun x => ?_⟩
  have hcomm : β x * A = A * x := by
    apply Subtype.ext
    show (β x : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B = B * (x : Matrix (Fin 3) (Fin 3) (ZMod 2))
    refine ext_of_mulVec_single fun i => ?_
    set v : V3 := Pi.single i 1
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    show act (β x) (B *ᵥ v) = B *ᵥ act x v
    rw [hBv, hBv]
    by_cases hv : v = 0
    · rw [hv, hf0, act_zero, act_zero, hf0]
    · exact (key x v hv).symm
  rw [← hcomm, mul_inv_cancel_right]

theorem exists_eq_conj (β : S →* S) (hinj : Function.Injective β) (hP : ∀ x ∈ P0, β x ∈ P0)
    (hX : (∀ x ∈ X1, β x ∈ X1) ∨ (∀ x ∈ X2, β x ∈ X2)) : ∃ A : S, ∀ x, β x = A * x * A⁻¹ := by
  rcases hX with hX | hX
  · exact exists_eq_conj_of_X1 β hinj hX
  refine exists_eq_conj_of_X1 β hinj ?_
  have hmapP : P0.map β = P0 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 fun x hx => hP x hx) ?_
    rw [Subgroup.card_map_of_injective hinj]
  have hmap2 : X2.map β = X2 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 fun x hx => hX x hx) ?_
    rw [Subgroup.card_map_of_injective hinj]
  have hle : P0 ≤ X1.map β := by
    rw [← hmapP]
    exact Subgroup.map_mono inf_le_left
  have hcard : Nat.card ↥(X1.map β) = 24 := by
    rw [Subgroup.card_map_of_injective hinj, card_X1]
  rcases overgroups_SL3 _ hle with h | h | h | h
  · rw [h, card_P0] at hcard
    exact absurd hcard (by norm_num)
  · intro x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · exfalso
    have : X1 = X2 := Subgroup.map_injective hinj (h.trans hmap2.symm)
    exact X_incomparable.1 (this ▸ le_refl _)
  · rw [h, Subgroup.card_top, card_S] at hcard
    exact absurd hcard (by norm_num)

end SL3Aut

variable {G : Type} [Group G]

theorem map_eq_one_iff_of_ker {K : Subgroup G} {Q : Type*} [Group Q] {φ : ↥K →* Q}
    (hker : φ.ker = CFSG.Open.pCore 2 ↥K) (k : ↥K) : φ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [← MonoidHom.mem_ker, hker, ← coe_mem_pCoreOf_iff]

theorem map_eq_map_iff_of_ker {K : Subgroup G} {Q : Type*} [Group Q] {φ : ↥K →* Q}
    (hker : φ.ker = CFSG.Open.pCore 2 ↥K) (a b : ↥K) :
    φ a = φ b ↔ (a : G)⁻¹ * b ∈ pCoreOf 2 K := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, map_eq_one_iff_of_ker hker]
  rfl

theorem conj_mem_pCoreOf {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) {x : G}
    (hx : x ∈ pCoreOf 2 K) : t * x * t⁻¹ ∈ pCoreOf 2 K :=
  (mem_normalizer_iff.mp (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K ht) x).mp hx

theorem inf_pCoreOf_le_pCoreOf_of_le [Finite G] {K X : Subgroup G} (hKX : K ≤ X) :
    K ⊓ pCoreOf 2 X ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_left
    ?_ ((LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)
  refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
  exact mem_normalizer_inf (le_normalizer hk)
    (LieType.BorelTits.le_normalizer_pCoreOf 2 X (hKX hk))

theorem pCoreOf_le_pCoreOf [Finite G] {K X : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
    ((LieType.BorelTits.pCoreOf_le 2 K).trans hKX) ?_ (LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact (normal_subgroupOf_iff_le_normalizer ((LieType.BorelTits.pCoreOf_le 2 K).trans hKX)).2
    (hXN.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))

theorem quasithinO2QuotientIso_of_sup [Finite G] {X K : Subgroup G} {Q : Type*} [Group Q]
    (hKX : K ≤ X) (hXN : X ≤ normalizer (K : Set G)) (hX : X = K ⊔ pCoreOf 2 X)
    (hK : quasithinO2QuotientIso K Q) : quasithinO2QuotientIso X Q := by
  obtain ⟨φ, hφ, hker⟩ := hK
  set N := pCoreOf 2 X with hN
  have hKN : K ≤ normalizer (N : Set G) := hKX.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hdec : ∀ x : ↥X, ∃ k : ↥K, ∃ n ∈ N, (x : G) = k * n := by
    intro x
    have hx : (x : G) ∈ ((K ⊔ N : Subgroup G) : Set G) := by
      rw [← hX]
      exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at hx
    obtain ⟨k, hk, n, hn, hkn⟩ := hx
    exact ⟨⟨k, hk⟩, n, hn, hkn.symm⟩
  choose kOf n hn hkn using hdec
  have hwd : ∀ (x : ↥X) (k : ↥K) (m : G), m ∈ N → (x : G) = k * m → φ (kOf x) = φ k := by
    intro x k m hm hx
    rw [map_eq_map_iff_of_ker hker]
    refine inf_pCoreOf_le_pCoreOf_of_le hKX (mem_inf.2 ⟨mul_mem (inv_mem (kOf x).2) k.2, ?_⟩)
    have : ((kOf x : G))⁻¹ * k = n x * m⁻¹ := by
      have h1 := hkn x
      rw [hx] at h1
      calc ((kOf x : G))⁻¹ * k = ((kOf x : G))⁻¹ * (k * m) * m⁻¹ := by group
        _ = ((kOf x : G))⁻¹ * (kOf x * n x) * m⁻¹ := by rw [h1]
        _ = n x * m⁻¹ := by group
    rw [this]
    exact mul_mem (hn x) (inv_mem hm)
  refine ⟨MonoidHom.mk' (fun x => φ (kOf x)) fun x y => ?_, fun q => ?_, ?_⟩
  ·
    rw [← map_mul]
    refine hwd (x * y) (kOf x * kOf y) ((kOf y : G)⁻¹ * n x * kOf y * n y) ?_ ?_
    · refine mul_mem ?_ (hn y)
      have := (mem_normalizer_iff.mp (hKN (inv_mem (kOf y).2)) (n x)).mp (hn x)
      simpa using this
    · rw [Subgroup.coe_mul, hkn x, hkn y, Subgroup.coe_mul]
      group
  · obtain ⟨k, rfl⟩ := hφ q
    exact ⟨⟨k, hKX k.2⟩, hwd _ k 1 (one_mem _) (by simp)⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.mk'_apply, ← coe_mem_pCoreOf_iff,
      map_eq_one_iff_of_ker hker]
    constructor
    · intro h
      rw [hkn x]
      exact mul_mem (pCoreOf_le_pCoreOf hKX hXN h) (hn x)
    · intro h
      have := hwd x 1 x h (by simp)
      rw [map_one] at this
      rw [← map_eq_one_iff_of_ker hker, this]

theorem quot_SL3_of_sup [Finite G] {H₀ K₀ T Y : Subgroup G} (hTsyl : IsSylowTwoOf T H₀)
    (hHN : H₀ ≤ normalizer (K₀ : Set G)) (hH : H₀ = K₀ ⊔ T)
    (hK : quasithinO2QuotientIso K₀ SL3.S) (hTY : T ≤ Y) (hYH : Y ≤ H₀) (hYT : Y ≠ T)
    (hKY : ¬ K₀ ≤ Y) : quasithinO2QuotientIso H₀ SL3.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K₀ ≤ H₀ := hH ▸ le_sup_left
  have hTH : T ≤ H₀ := hTsyl.1
  have hTN : T ≤ normalizer (K₀ : Set G) := hTH.trans hHN
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hconjK : ∀ t ∈ normalizer (K₀ : Set G), ∀ k ∈ K₀, t * k * t⁻¹ ∈ K₀ :=
    fun t ht k hk => (mem_normalizer_iff.mp ht k).mp hk
  have hsylK : IsSylowTwoOf (K₀ ⊓ T) K₀ := by
    have := A4.isSylowTwoOf_inf_normal hTsyl hKH hHN
    rwa [inf_comm] at this
  obtain ⟨φ, hφ, hker, hTφ⟩ := I51.exists_model_hom hK hsylK SL3.P0_sylow.1 SL3.P0_sylow.2
  set P := Y ⊓ K₀ with hP
  have hTP : K₀ ⊓ T ≤ P := le_inf (inf_le_right.trans hTY) inf_le_left
  have hPK : P ≤ K₀ := inf_le_right
  have hPmap : (P.subgroupOf K₀).map φ = SL3.X1 ∨ (P.subgroupOf K₀).map φ = SL3.X2 := by
    have hle : SL3.P0 ≤ (P.subgroupOf K₀).map φ := by
      rw [← hTφ]
      exact map_mono (subgroupOf_mono _ hTP)
    have hcomap := I51.subgroupOf_eq_comap_map hsylK φ hker hTP
    rcases SL3.overgroups_SL3 _ hle with h | h | h | h
    · exfalso
      have hcomap' := I51.subgroupOf_eq_comap_map hsylK φ hker le_rfl
      rw [hTφ] at hcomap'
      rw [h, ← hcomap'] at hcomap
      have hPT : P = K₀ ⊓ T := by
        have := (Subgroup.subgroupOf_inj).1 hcomap
        rwa [inf_eq_left.2 hPK, inf_eq_left.2 inf_le_left] at this
      apply hYT
      refine le_antisymm (fun y hy => ?_) hTY
      have hy' : y ∈ ((K₀ ⊔ T : Subgroup G) : Set G) := by
        rw [← hH]
        exact hYH hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at hy'
      obtain ⟨k, hk, t, ht, rfl⟩ := hy'
      have hkY : k ∈ Y := by
        have := mul_mem hy (inv_mem (hTY ht))
        simpa using this
      have hkT : k ∈ K₀ ⊓ T := hPT ▸ mem_inf.2 ⟨hkY, hk⟩
      exact mul_mem (mem_inf.1 hkT).2 ht
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h, comap_top] at hcomap
      exact hKY fun k hk => (mem_inf.1 ((subgroupOf_eq_top.1 hcomap) hk)).1
  have hTPn : T ≤ normalizer (P : Set G) := fun t ht =>
    mem_normalizer_inf (le_normalizer (hTY ht)) (hTN ht)
  have hTKT : T ≤ normalizer ((K₀ ⊓ T : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (hTN ht) (le_normalizer ht)
  have hCmul : ∀ a b, a ∈ H₀ → b ∈ H₀ → (∀ k ∈ K₀, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀) →
      (∀ k ∈ K₀, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀) →
      ∀ k ∈ K₀, a * b * k * (a * b)⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀ := by
    intro a b ha _ hac hbc k hk
    have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
        a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_pCoreOf (hHN ha) (hbc k hk)) (hac k hk)
  have hCinv : ∀ a, a ∈ H₀ → (∀ k ∈ K₀, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀) →
      ∀ k ∈ K₀, a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀ := by
    intro a ha hac k hk
    have hk' : a⁻¹ * k * a ∈ K₀ := by
      have := hconjK a⁻¹ (inv_mem (hHN ha)) k hk
      simpa using this
    have h1 := inv_mem (hac _ hk')
    have e : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = (a * (a⁻¹ * k * a) * a⁻¹ * (a⁻¹ * k * a)⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  let C : Subgroup G :=
    { carrier := {h | h ∈ H₀ ∧ ∀ k ∈ K₀, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀}
      one_mem' := ⟨one_mem _, fun k _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, hCmul a b ha.1 hb.1 ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, hCinv a ha.1 ha.2⟩ }
  have hmemC : ∀ h, h ∈ C ↔ h ∈ H₀ ∧ ∀ k ∈ K₀, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 K₀ :=
    fun h => Iff.rfl
  have hstep : ∀ t ∈ T, ∃ k₁ ∈ K₀, k₁⁻¹ * t ∈ C := by
    intro t ht
    have htN := hTN ht
    let ct : ↥K₀ → ↥K₀ := fun k => ⟨t * k * t⁻¹, hconjK t htN k k.2⟩
    have hct : ∀ k, (ct k : G) = t * k * t⁻¹ := fun k => rfl
    have hct_mul : ∀ a b, ct (a * b) = ct a * ct b := fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, hct, hct, hct, Subgroup.coe_mul]
      group)
    have hct_eq : ∀ a b : ↥K₀, φ (ct a) = φ (ct b) ↔ φ a = φ b := by
      intro a b
      rw [map_eq_map_iff_of_ker hker, map_eq_map_iff_of_ker hker, hct, hct]
      have e : (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹) = t * ((a : G)⁻¹ * b) * t⁻¹ := by group
      rw [e]
      constructor
      · intro h
        have := conj_mem_pCoreOf (inv_mem htN) h
        simpa [mul_assoc] using this
      · exact conj_mem_pCoreOf htN
    set βf : SL3.S → SL3.S := fun x => φ (ct (Function.surjInv hφ x)) with hβf
    have hβ : ∀ k, βf (φ k) = φ (ct k) := fun k =>
      (hct_eq _ _).2 (Function.surjInv_eq hφ (φ k))
    let β : SL3.S →* SL3.S := MonoidHom.mk' βf fun x y => by
      obtain ⟨a, rfl⟩ := hφ x
      obtain ⟨b, rfl⟩ := hφ y
      rw [← map_mul, hβ, hβ, hβ, hct_mul, map_mul]
    have hβapp : ∀ k, β (φ k) = φ (ct k) := hβ
    have hβinj : Function.Injective β := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := hφ x
      obtain ⟨b, rfl⟩ := hφ y
      rw [hβapp, hβapp] at hxy
      exact (hct_eq a b).1 hxy
    have hβsub : ∀ Q : Subgroup G, T ≤ normalizer (Q : Set G) →
        ∀ x ∈ (Q.subgroupOf K₀).map φ, β x ∈ (Q.subgroupOf K₀).map φ := by
      intro Q hQ x hx
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨ct k, ?_, (hβapp k).symm⟩
      simp only [SetLike.mem_coe, mem_subgroupOf] at hk ⊢
      rw [hct]
      exact (mem_normalizer_iff.mp (hQ ht) k).mp hk
    have hP0 : ∀ x ∈ SL3.P0, β x ∈ SL3.P0 := by
      rw [← hTφ]
      exact hβsub (K₀ ⊓ T) hTKT
    have hX : (∀ x ∈ SL3.X1, β x ∈ SL3.X1) ∨ (∀ x ∈ SL3.X2, β x ∈ SL3.X2) := by
      rcases hPmap with h | h
      · left
        rw [← h]
        exact hβsub P hTPn
      · right
        rw [← h]
        exact hβsub P hTPn
    obtain ⟨A, hA⟩ := SL3Aut.exists_eq_conj β hβinj hP0 hX
    obtain ⟨k₁, hk₁⟩ := hφ A
    refine ⟨k₁, k₁.2, (hmemC _).2 ⟨mul_mem (inv_mem (hKH k₁.2)) (hTH ht), fun k hk => ?_⟩⟩
    have h1 : φ (ct ⟨k, hk⟩) = φ (k₁ * ⟨k, hk⟩ * k₁⁻¹) := by
      rw [← hβapp, hA, map_mul, map_mul, map_inv, hk₁]
    rw [map_eq_map_iff_of_ker hker, hct] at h1
    change (t * k * t⁻¹)⁻¹ * ((k₁ : G) * k * (k₁ : G)⁻¹) ∈ pCoreOf 2 K₀ at h1
    have e : (k₁ : G)⁻¹ * t * k * ((k₁ : G)⁻¹ * t)⁻¹ * k⁻¹ =
        (k * (k₁ : G)⁻¹) * ((t * k * t⁻¹)⁻¹ * ((k₁ : G) * k * (k₁ : G)⁻¹))⁻¹ *
          (k * (k₁ : G)⁻¹)⁻¹ := by group
    rw [e]
    exact conj_mem_pCoreOf (le_normalizer (mul_mem hk (inv_mem k₁.2))) (inv_mem h1)
  have hCH : C ≤ H₀ := fun h hh => hh.1
  have hCconj : ∀ g ∈ H₀, ∀ h ∈ C, g * h * g⁻¹ ∈ C := by
    intro g hg h hh
    refine (hmemC _).2 ⟨mul_mem (mul_mem hg ((hmemC h).1 hh).1) (inv_mem hg), fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K₀ := by
      have := hconjK g⁻¹ (inv_mem (hHN hg)) k hk
      simpa using this
    have := conj_mem_pCoreOf (hHN hg) (((hmemC h).1 hh).2 _ hk')
    have e : g * h * g⁻¹ * k * (g * h * g⁻¹)⁻¹ * k⁻¹ =
        g * (h * (g⁻¹ * k * g) * h⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact this
  have hCnorm : H₀ ≤ normalizer (C : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hCconj g hg h, fun hh => ?_⟩
    have := hCconj g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using this
  have hC2 : IsPGroup 2 ↥C := by
    rintro ⟨h, hh⟩
    obtain ⟨a, ha⟩ := pow_two_mem_of_sup hTN hT2 (show h ∈ K₀ ⊔ T from hH ▸ ((hmemC h).1 hh).1)
    have hhC := ((hmemC _).1 (pow_mem hh (2 ^ a))).2
    have hcent : ∀ x : SL3.S, φ ⟨_, ha⟩ * x = x * φ ⟨_, ha⟩ := by
      intro x
      obtain ⟨k, rfl⟩ := hφ x
      rw [← map_mul, ← map_mul, map_eq_map_iff_of_ker hker]
      set h' : G := h ^ 2 ^ a with hh'
      have hw := hhC k k.2
      change ((h' : G) * k)⁻¹ * ((k : G) * h') ∈ pCoreOf 2 K₀
      have e : ((h' : G) * k)⁻¹ * ((k : G) * h') =
          (((k : G)⁻¹ * h'⁻¹) * (h' * k * h'⁻¹ * (k : G)⁻¹) * ((k : G)⁻¹ * h'⁻¹)⁻¹)⁻¹ := by
        group
      rw [e]
      exact inv_mem (conj_mem_pCoreOf (le_normalizer (mul_mem (inv_mem k.2) (inv_mem ha))) hw)
    have h1 := SL3Aut.eq_one_of_commute _ (hcent _) (hcent _) (hcent _) (hcent _)
    obtain ⟨b, hb⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 K₀)
      ⟨_, (map_eq_one_iff_of_ker hker _).1 h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (h ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hCO : C ≤ pCoreOf 2 H₀ :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hCH
      ((normal_subgroupOf_iff_le_normalizer hCH).2 hCnorm) hC2
  have hTle : T ≤ K₀ ⊔ pCoreOf 2 H₀ := by
    intro t ht
    obtain ⟨k₁, hk₁, hc⟩ := hstep t ht
    have : t = k₁ * (k₁⁻¹ * t) := by group
    rw [this]
    exact mul_mem (mem_sup_left hk₁) (mem_sup_right (hCO hc))
  have hH₀ : H₀ = K₀ ⊔ pCoreOf 2 H₀ :=
    le_antisymm (hH.le.trans (sup_le le_sup_left hTle))
      (sup_le hKH (LieType.BorelTits.pCoreOf_le 2 H₀))
  exact quasithinO2QuotientIso_of_sup hKH hHN hH₀ hK

end CFSG.Quasithin.H13.U3
