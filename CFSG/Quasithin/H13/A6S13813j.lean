module

public import CFSG.Quasithin.H13.A6S13813i
public import CFSG.Quasithin.H13.A6S13813f

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

attribute [local instance] commGroupOfFact

namespace A6Four

variable {M : Type*} [Group M]

@[expose] noncomputable def conjAct {X P : Subgroup M} (hXP : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ ∈ P) :
    ↥X →* MulAut ↥P where
  toFun x :=
    { toFun := fun y => ⟨x * y * x⁻¹, hXP x x.2 y y.2⟩
      invFun := fun y => ⟨x⁻¹ * y * x, by simpa using hXP x⁻¹ (X.inv_mem x.2) y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext y; simp
  map_mul' x x' := by ext y; simp [mul_assoc]

theorem conjAct_apply {X P : Subgroup M} (hXP : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ ∈ P) (x : ↥X)
    (y : ↥P) : ((conjAct hXP x y : ↥P) : M) = x * y * x⁻¹ := rfl

@[expose] def reflList : List (Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  [!![0, 1; 1, 0], !![0, 2; 2, 0], !![1, 0; 0, 2], !![1, 0; 1, 2], !![1, 0; 2, 2],
    !![1, 1; 0, 2], !![1, 2; 0, 2], !![2, 0; 0, 1], !![2, 0; 1, 1], !![2, 0; 2, 1],
    !![2, 1; 0, 1], !![2, 2; 0, 1]]

@[expose] def unipList : List (Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  [!![1, 1; 0, 1], !![1, 2; 0, 1], !![1, 0; 1, 1], !![1, 0; 2, 1], !![2, 1; 2, 0],
    !![2, 2; 1, 0], !![0, 1; 2, 2], !![0, 2; 1, 2]]

theorem mem_reflList_of : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A * A = 1 → A ≠ 1 →
    A ≠ -1 → A ∈ reflList := by
  decide +kernel

theorem mem_unipList_of : ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod 3), Y ^ 3 = 1 → Y ≠ 1 →
    Y ∈ unipList := by
  decide +kernel

theorem refl_unip_not_two : ∀ A ∈ reflList, ∀ Y ∈ unipList,
    (A * (Y * A * Y ^ 2)) ^ 16 ≠ 1 := by
  decide +kernel

end A6Four

namespace A6Four

theorem pow_sixteen_eq_one {M : GL (Fin 2) (ZMod 3)} {k : ℕ} (hk : M ^ 2 ^ k = 1) :
    M ^ 16 = 1 := by
  have h48 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
    decide
  have h1 : orderOf M ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf M ∣ 48 := h48 ▸ orderOf_dvd_natCard M
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj4 : j ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 48 := (pow_dvd_pow 2 (by omega : 5 ≤ j)).trans (hjo ▸ h2)
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjo]
  exact (pow_dvd_pow 2 hj4).trans (by norm_num)

end A6Four

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_closure_order_three :
    S.L1 ≤ Subgroup.closure {x : G | x ∈ S.L1 ∧ x ^ 3 = 1} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcube : ∀ x ∈ S.L1, x ^ 3 ∈ pCoreOf 2 S.L1 := fun x hx => by
    by_cases hhat : IsHatA6 L
    · exact S.cube_mem_pCoreOf_L1_hat hhat hx
    · exact S.cube_mem_pCoreOf_L1 hhat hx
  show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
  refine Subgroup.subset_closure ⟨hxL1, ?_⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, hcube x hxL1⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
    (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')

theorem mem_L1_of_odd {g l q : G} (hl : l ∈ S.L1) (hq : q ∈ Subgroup.normalizer (S.L1 : Set G))
    (hgq : g = l * q) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) {k : ℕ} (hqk : q ^ 2 ^ k = 1) :
    g ∈ S.L1 := by
  have hpow : ∀ n : ℕ, g ^ n * (q ^ n)⁻¹ ∈ S.L1 := by
    intro n
    induction n with
    | zero => simp [S.L1.one_mem]
    | succ n ih =>
      have e : g ^ (n + 1) * (q ^ (n + 1))⁻¹ =
          (g ^ n * (q ^ n)⁻¹) * (q ^ n * l * (q ^ n)⁻¹) := by
        rw [pow_succ, pow_succ, hgq]
        group
      rw [e]
      refine S.L1.mul_mem ih ?_
      have hqn : q ^ n ∈ Subgroup.normalizer (S.L1 : Set G) := Subgroup.pow_mem _ hq n
      exact (Subgroup.mem_normalizer_iff.mp hqn l).mp hl
  have h1 := hpow m
  rw [hgm, one_mul] at h1
  have hqm : q ^ m ∈ S.L1 := by simpa using S.L1.inv_mem h1
  have hcop : Nat.Coprime m (orderOf q) := by
    have hdvd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hqk
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k
      (Nat.coprime_two_right.2 hm))
  have hqz : q ∈ Subgroup.zpowers (q ^ m) := by
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
    refine ⟨u, ?_⟩
    show (q ^ m) ^ (u : ℤ) = q
    rw [zpow_natCast, hu]
  have hq1 : q ∈ S.L1 := (Subgroup.zpowers_le.2 hqm) hqz
  rw [hgq]
  exact S.L1.mul_mem hl hq1

section PSec

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  {hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G)}
  {hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G)} {p : ℕ}
  {P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
  (hP : A6P.PData S.L1 T L H (actH hV₁ hIH)
    (((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) p P)
include hS hH hP

theorem P_shape :
    Nat.card P = p ∨ ((∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ Nat.card P = p ^ 2) ∨
      IsPOnePlusTwo p ↥P := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hF := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, actH hV₁ hIH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hrank := A6P.pRank_range_le_two_of_odd hF S.h13.qtke (actH hV₁ hIH) hker hP.prime hP.ne_two
  have hPX : P ≤ (actH hV₁ hIH).range := hP.le_pCore.trans (pCoreOf_le p _)
  have hrP : CFSG.Open.pRank p P ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hP.prime.one_lt hPX).trans hrank
  have hPp : IsPGroup p ↥P := fun x => ⟨1, Subtype.ext (by simpa using hP.exp x x.2)⟩
  have hPne : P ≠ ⊥ := by
    intro h
    apply hP.not_cent
    intro x hx a _
    rw [h, Subgroup.mem_bot] at hx
    rw [hx, mul_one, one_mul]
  have hrtop : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := by
    rw [pRank_top_subtype]; exact hrP
  have hntop : (⊤ : Subgroup ↥P) ≠ ⊥ := by
    intro h
    apply hPne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ (⊥ : Subgroup ↥P) := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val ((Subgroup.mem_bot).1 this))
  have hexpt : ∀ x ∈ (⊤ : Subgroup ↥P), x ^ p = 1 := fun x _ =>
    Subtype.ext (by simpa using hP.exp x x.2)
  by_cases hr1 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 1
  · left
    obtain ⟨z, -, hz, hzo⟩ := exists_eq_zpowers_of_pRank_le_one hPp hntop hexpt hr1
    rw [← Nat.card_congr (Subgroup.topEquiv (G := ↥P)).toEquiv, hz, Nat.card_zpowers, hzo]
  right
  have hr2 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) = 2 := by omega
  have hΩ : Subgroup.closure {x : ↥P | x ^ p = 1} = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.subset_closure (hexpt x (Subgroup.mem_top x))
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo hP.ne_two hPp hΩ hr2
    (classLeTwo_top_of hP.cls) with he | h
  · left
    obtain ⟨e⟩ := he
    refine ⟨fun x hx y hy => ?_, ?_⟩
    · have h1 : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val (e.injective h1)
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · right
    exact h

theorem four_shape {a b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (ha : a ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hb : b ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) :
    (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ Nat.card P = p ^ 2 ∧
      ∃ z ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH),
        ∀ x ∈ P, z * x * z⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hodd : Odd p := hP.prime.odd_of_ne_two hP.ne_two
  set R := ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH) with hR
  have hRX : R ≤ (actH hV₁ hIH).range := Subgroup.map_le_range _ _
  have haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P := hP.normal a (hRX ha)
  have hbP : ∀ x ∈ P, b * x * b⁻¹ ∈ P := hP.normal b (hRX hb)
  have hfaith : ∀ r ∈ R, r ≠ 1 → ¬ ∀ x ∈ P, r * x * r⁻¹ = x := by
    intro r hr hr1 hc
    apply hr1
    refine S.eq_one_of_cent_P hS hH hP hr fun x hx => ?_
    calc r * x = r * x * r⁻¹ * r := by group
      _ = x * r := by rw [hc x hx]
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have : b = a⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [this, ← (eq_inv_of_mul_eq_one_left ha2)]
  have hna := hfaith a ha ha1
  have hnb := hfaith b hb hb1
  have hnab := hfaith (a * b) (R.mul_mem ha hb) hab1
  rcases S.P_shape hS hH hP with hcard | ⟨hcomm, hcard⟩ | hext
  · exfalso
    exact hne (S.eq_of_card_eq hS hH hP hcard ha hb ha2 hb2 ha1 hb1)
  · refine ⟨hcomm, hcard, ?_⟩
    obtain ⟨z, hz, hzinv⟩ := A6Four.exists_inv_of_rank_two hcomm hP.ne_two hP.exp hcard ha2 hb2
      hab haP hbP hna hnb (by simpa [mul_assoc] using hnab)
    refine ⟨z, ?_, hzinv⟩
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact R.mul_mem ha hb
  · exfalso
    obtain ⟨hZP, hZcard, hZcent, hcomm, hexp, hcent⟩ := A6Four.extraspecial_data hext
    set Z := (Subgroup.center ↥P).map P.subtype with hZ
    have hZinv : ∀ y ∈ ((S.L1 ⊔ T).subgroupOf H).map (actH hV₁ hIH), ∀ z ∈ Z,
        y * z * y⁻¹ ∈ Z := by
      intro y hy z hz
      have hyX : y ∈ (actH hV₁ hIH).range := Subgroup.map_le_range _ _ hy
      have hyz : y * z * y⁻¹ ∈ P := hP.normal y hyX z (hZP hz)
      refine ⟨⟨_, hyz⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext ?_, rfl⟩
      have hw' : y⁻¹ * (w : MulAut _) * y ∈ P := by
        have := hP.normal y⁻¹ ((actH hV₁ hIH).range.inv_mem hyX) (w : MulAut _) w.2
        simpa using this
      have h1 := hZcent z hz _ hw'
      show (w : MulAut _) * (y * z * y⁻¹) = y * z * y⁻¹ * (w : MulAut _)
      calc (w : MulAut _) * (y * z * y⁻¹) = y * ((y⁻¹ * (w : MulAut _) * y) * z) * y⁻¹ := by
            group
        _ = y * (z * (y⁻¹ * (w : MulAut _) * y)) * y⁻¹ := by rw [h1]
        _ = y * z * y⁻¹ * (w : MulAut _) := by group
    have hZne : Z ≠ P := by
      intro h
      have h3 := hext.2.1
      rw [← h, hZcard] at h3
      have : p ^ 1 = p ^ 3 := by rw [pow_one]; exact h3
      have := Nat.pow_right_injective hP.prime.two_le this
      omega
    have hcentZ : A6P.Cent Z R := by
      by_contra hc
      exact hZne (hP.minimal Z hZP hZinv hc)
    have haZ : ∀ z ∈ Z, a * z * a⁻¹ = z := fun z hz => by
      rw [hcentZ z hz a ha, mul_inv_cancel_right]
    have hbZ : ∀ z ∈ Z, b * z * b⁻¹ = z := fun z hz => by
      rw [hcentZ z hz b hb, mul_inv_cancel_right]
    exact A6Four.false_of_extraspecial hodd hZP hZcent hcomm hexp hcent ha2 hb2 hab haP hbP
      haZ hbZ hna hnb (by simpa [mul_assoc] using hnab)


omit hS hH [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))] in
theorem eq_P_of_inv {z : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hz : z ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hzinv : ∀ x ∈ P, z * x * z⁻¹ = x⁻¹)
    {P₀ : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))} (hP₀ : P₀ ≤ P)
    (hinv : ∀ y ∈ ((S.L1 ⊔ T).subgroupOf H).map (actH hV₁ hIH), ∀ x ∈ P₀, y * x * y⁻¹ ∈ P₀)
    (hne : P₀ ≠ ⊥) : P₀ = P := by
  by_contra hP₀P
  have hc : A6P.Cent P₀ (((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) := by
    by_contra hc
    exact hP₀P (hP.minimal P₀ hP₀ hinv hc)
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have h1 := hzinv x (hP₀ hx)
  rw [hc x hx z hz, mul_inv_cancel_right] at h1
  have hodd : Odd p := hP.prime.odd_of_ne_two hP.ne_two
  refine (Subgroup.mem_bot).2 (A6Four.eq_one_of_sq_of_pow_odd hodd (hP.exp x (hP₀ hx)) ?_)
  nth_rewrite 2 [h1]
  exact mul_inv_cancel x

theorem false_of_p3 (hp3 : p = 3)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hcard : Nat.card P = p ^ 2)
    {z a : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hz : z ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hzinv : ∀ x ∈ P, z * x * z⁻¹ = x⁻¹)
    (ha : a ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) (ha2 : a * a = 1)
    (hna : ¬ ∀ x ∈ P, a * x * a⁻¹ = x) (hnai : ¬ ∀ x ∈ P, a * x * a⁻¹ = x⁻¹) : False := by
  subst hp3
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := (hS.hF H hH).toHypF91
  set φ := actH hV₁ hIH with hφ
  set X := φ.range with hX
  set R := ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ with hR
  have hRX : R ≤ X := Subgroup.map_le_range _ _
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥P)
    (fun x y => Subtype.ext (hcomm x x.2 y y.2))
    (fun x => Subtype.ext (by simpa using hP.exp x x.2)) hcard
  set κ : ↥X →* GL (Fin 2) (ZMod 3) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (A6Four.conjAct hP.normal)
    with hκ
  have hκ1 : ∀ m : ↥X, κ m = 1 ↔
      ∀ x ∈ P, (m : MulAut _) * x * (m : MulAut _)⁻¹ = x := by
    intro m
    rw [hκ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective]
    constructor
    · intro h x hx
      have := congrArg (fun α : MulAut ↥P => (α ⟨x, hx⟩ : ↥P).val) h
      simpa [A6Four.conjAct_apply] using this
    · intro h
      ext y
      simp [A6Four.conjAct_apply, h y y.2]
  have hκn : ∀ m : ↥X, κ m = -1 ↔
      ∀ x ∈ P, (m : MulAut _) * x * (m : MulAut _)⁻¹ = x⁻¹ := by
    intro m
    rw [hκ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff]
    constructor
    · intro h x hx
      have := congrArg Subtype.val (h ⟨x, hx⟩)
      simpa [A6Four.conjAct_apply] using this
    · intro h y
      exact Subtype.ext (by simp [A6Four.conjAct_apply, h y y.2])
  set A := κ ⟨a, hRX ha⟩ with hA
  have hAA' : A * A = 1 := by
    have : (⟨a, hRX ha⟩ : ↥X) * ⟨a, hRX ha⟩ = 1 := Subtype.ext ha2
    rw [hA, ← map_mul, this, map_one]
  have hAA : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A = 1 := by
    rw [← Units.val_mul, hAA', Units.val_one]
  have hA1 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h =>
    hna ((hκ1 _).1 (Units.ext (by rw [h, Units.val_one])))
  have hAn : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ -1 := fun h =>
    hnai ((hκn _).1 (Units.ext (by rw [h]; rfl)))
  have hAref := A6Four.mem_reflList_of _ hAA hA1 hAn
  have hL1H : S.L1 ≤ H := le_sup_left.trans hF.L₁T_le_H
  by_cases hcase : ∃ x ∈ S.L1, x ^ 3 = 1 ∧ ∃ hx : x ∈ H,
      ¬ ∀ y ∈ P, φ ⟨x, hx⟩ * y * (φ ⟨x, hx⟩)⁻¹ = y
  · obtain ⟨x, hxL, hx3, hxH, hxn⟩ := hcase
    set y := φ ⟨x, hxH⟩ with hy
    have hyX : y ∈ X := ⟨_, rfl⟩
    set Y := κ ⟨y, hyX⟩ with hYdef
    have hy3 : (⟨y, hyX⟩ : ↥X) ^ 3 = 1 := by
      refine Subtype.ext ?_
      have hx3' : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [hy, ← map_pow, hx3', map_one]
    have hY3 : (Y : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hYdef, ← map_pow, hy3, map_one, Units.val_one]
    have hY1 : (Y : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h =>
      hxn ((hκ1 _).1 (Units.ext (by rw [h, Units.val_one])))
    have hYu := A6Four.mem_unipList_of _ hY3 hY1
    have hxLT : x ∈ S.L1 ⊔ T := Subgroup.mem_sup_left hxL
    have hyR : y * a * y⁻¹ ∈ R := by
      obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.1 ha
      refine ⟨⟨x, hxH⟩ * r * ⟨x, hxH⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hxLT) r).mp (Subgroup.mem_subgroupOf.1 hr)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hra]
    have hc : a * (y * a * y⁻¹) ∈ R := R.mul_mem ha hyR
    obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one_of_mem_R1 hc
    have hcX : a * (y * a * y⁻¹) ∈ X := hRX hc
    have hκc : κ ⟨_, hcX⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨_, hcX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h16 := A6Four.pow_sixteen_eq_one hκc
    have hcc : κ ⟨_, hcX⟩ = A * (Y * A * Y⁻¹) := by
      have : (⟨_, hcX⟩ : ↥X) = ⟨a, hRX ha⟩ * (⟨y, hyX⟩ * ⟨a, hRX ha⟩ * (⟨y, hyX⟩ : ↥X)⁻¹) :=
        Subtype.ext rfl
      rw [this, map_mul, map_mul, map_mul, map_inv]
    have hYinv : Y⁻¹ = Y ^ 2 := by
      have hY3' : Y ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hY3, Units.val_one])
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hY3']
    apply A6Four.refl_unip_not_two _ hAref _ hYu
    have := congrArg Units.val h16
    rw [hcc, hYinv] at this
    simpa using this
  · push Not at hcase
    have hrank := A6P.pRank_range_le_two_of_odd hF S.h13.qtke φ (fun x => by
      have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
        (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
      rw [hφ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
      exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩) Nat.prime_three (by norm_num)
    have hinP : ∀ x (hxL : x ∈ S.L1), x ^ 3 = 1 → φ ⟨x, hL1H hxL⟩ ∈ P := by
      intro x hxL hx3
      by_contra hxP
      set y := φ ⟨x, hL1H hxL⟩ with hy
      have hyc : ∀ w ∈ P, y * w = w * y := fun w hw => by
        have := hcase x hxL hx3 (hL1H hxL) w hw
        calc y * w = y * w * y⁻¹ * y := by group
          _ = w * y := by rw [this]
      have hy3 : y ^ 3 = 1 := by
        have hx3' : (⟨x, hL1H hxL⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        rw [hy, ← map_pow, hx3', map_one]
      set K := Subgroup.zpowers y ⊔ P with hK
      have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set (MulAut _)) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          rw [hyc w hw, mul_inv_cancel_right]
          exact hw
        · intro hw
          have h1 : w = y⁻¹ * (y * w * y⁻¹) * y := by group
          rw [h1]
          have h2 := hyc _ hw
          rw [show y⁻¹ * (y * w * y⁻¹) * y = y⁻¹ * ((y * w * y⁻¹) * y) by group, ← h2]
          simpa [mul_assoc] using hw
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyN
      have hmemK : ∀ k ∈ K, ∃ n : ℤ, ∃ w ∈ P, k = y ^ n * w := by
        intro k hk
        have : k ∈ ((Subgroup.zpowers y :
            Set (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))) *
            (P : Set (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))))) := by
          rw [← hset]; exact hk
        obtain ⟨u, hu, w, hw, rfl⟩ := this
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        exact ⟨n, w, hw, rfl⟩
      have hycomm : ∀ n : ℤ, ∀ w ∈ P, y ^ n * w = w * y ^ n := fun n w hw =>
        ((Commute.zpow_left (hyc w hw) n)).eq
      have hKcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ = k₂ * k₁ := by
        intro k₁ hk₁ k₂ hk₂
        obtain ⟨n₁, w₁, hw₁, rfl⟩ := hmemK k₁ hk₁
        obtain ⟨n₂, w₂, hw₂, rfl⟩ := hmemK k₂ hk₂
        have h11 : Commute (y ^ n₁) (y ^ n₂) := Commute.zpow_zpow_self y n₁ n₂
        have h12 : Commute (y ^ n₁) w₂ := hycomm n₁ w₂ hw₂
        have h21 : Commute w₁ (y ^ n₂) := (hycomm n₂ w₁ hw₁).symm
        have h22 : Commute w₁ w₂ := hcomm w₁ hw₁ w₂ hw₂
        exact (Commute.mul_left (Commute.mul_right h11 h12) (Commute.mul_right h21 h22)).eq
      have hKexp : ∀ k ∈ K, k ^ 3 = 1 := by
        intro k hk
        obtain ⟨n, w, hw, rfl⟩ := hmemK k hk
        rw [(Commute.mul_pow (hycomm n w hw) 3), ← zpow_natCast, ← zpow_mul, mul_comm,
          zpow_mul, zpow_natCast, hy3, one_zpow, one_mul, hP.exp w hw]
      have hKel : IsElemAbelian 3 K :=
        ⟨⟨⟨fun a b => Subtype.ext (hKcomm a a.2 b b.2)⟩⟩, hKexp⟩
      have hKp : IsPGroup 3 ↥K := fun k => ⟨1, Subtype.ext (by simpa using hKexp k k.2)⟩
      obtain ⟨j, hj⟩ := hKp.exists_card_eq
      have hPK : P < K := lt_of_le_of_ne le_sup_right fun h =>
        hxP (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      have hlt := Subgroup.card_lt_of_lt hPK
      rw [hcard, hj] at hlt
      have hj3 : 3 ≤ j := by
        by_contra h
        have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hKX : K ≤ X := sup_le ((Subgroup.zpowers_le).2 ⟨_, rfl⟩)
        (hP.le_pCore.trans (pCoreOf_le 3 _))
      have := CFSG.SectionRank.le_pRank (by norm_num) hKX hKel hj
      rw [← hX] at hrank
      omega
    set L1s := (S.L1.subgroupOf H).map φ with hL1s
    have hL1sP : L1s ≤ P := by
      rintro _ ⟨l, hl, rfl⟩
      have hlL : (l : G) ∈ S.L1 := Subgroup.mem_subgroupOf.1 hl
      have key : ∀ g (hg : g ∈ Subgroup.closure {x : G | x ∈ S.L1 ∧ x ^ 3 = 1}),
          φ ⟨g, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1) hg)⟩ ∈ P := by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx => exact hinP x hx.1 hx.2
        | one =>
          show φ 1 ∈ P
          rw [map_one]
          exact P.one_mem
        | mul x y hx hy ihx ihy =>
          have e : (⟨x * y, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1)
              (Subgroup.mul_mem _ hx hy))⟩ : ↥H) =
              ⟨x, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1) hx)⟩ *
                ⟨y, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1) hy)⟩ := rfl
          rw [e, map_mul]
          exact P.mul_mem ihx ihy
        | inv x hx ihx =>
          have e : (⟨x⁻¹, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1)
              (Subgroup.inv_mem _ hx))⟩ : ↥H) =
              (⟨x, hL1H ((Subgroup.closure_le _).2 (fun x hx => hx.1) hx)⟩)⁻¹ := rfl
          rw [e, map_inv]
          exact P.inv_mem ihx
      exact key l (S.L1_le_closure_order_three hlL)
    have hL1ne : L1s ≠ ⊥ := by
      intro hbot
      obtain ⟨c, hcL, hcρ, -⟩ := S.exists_c0
      have hc1 : φ ⟨c, hL1H hcL⟩ = 1 := by
        have : φ ⟨c, hL1H hcL⟩ ∈ L1s := ⟨⟨c, hL1H hcL⟩, Subgroup.mem_subgroupOf.2 hcL, rfl⟩
        rw [hbot] at this
        exact (Subgroup.mem_bot).1 this
      have hV3 : subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        refine (Subgroup.mem_bot).2 (S.fix_tilde_V3_c012 hS hH hV₁ hIH hcρ (hL1H hcL) hw ?_)
        rw [← hφ, hc1]
        rfl
      have h4 := S.card_tilde_V3 hS hH
      rw [hV3, Subgroup.card_bot] at h4
      norm_num at h4
    have hL1N : S.L1 ⊔ T ≤ Subgroup.normalizer (S.L1 : Set G) :=
      sup_le Subgroup.le_normalizer S.T_le_normalizer_L1
    have hinv : ∀ y ∈ ((S.L1 ⊔ T).subgroupOf H).map φ, ∀ x ∈ L1s, y * x * y⁻¹ ∈ L1s := by
      rintro _ ⟨t, ht, rfl⟩ _ ⟨l, hl, rfl⟩
      refine ⟨t * l * t⁻¹, Subgroup.mem_subgroupOf.2 ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := (Subgroup.mem_normalizer_iff.mp (hL1N (Subgroup.mem_subgroupOf.1 ht)) l).mp
        (Subgroup.mem_subgroupOf.1 hl)
      simpa using this
    have hL1eq := S.eq_P_of_inv hP hz hzinv hL1sP hinv hL1ne
    have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
      have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
        (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
      rw [hφ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
      exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
    have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow (le_sup_right.trans hH.1.1)
    have hPhat : oTwoRes ((P.comap φ).map H.subtype) ≤ S.L1 := by
      rw [oTwoRes, Subgroup.closure_le]
      rintro g ⟨⟨h, hh, rfl⟩, m, hm, hgm⟩
      have hhP : φ h ∈ L1s := hL1eq ▸ (Subgroup.mem_comap.1 hh)
      obtain ⟨l, hl, hlh⟩ := hhP
      have hq : ((l⁻¹ * h : ↥H) : G) ∈ pCoreOf 2 H :=
        (hker _).1 (by rw [map_mul, map_inv, hlh, inv_mul_cancel])
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hq⟩
      have hqk : ((l⁻¹ * h : ↥H) : G) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      refine S.mem_L1_of_odd (Subgroup.mem_subgroupOf.1 hl)
        (S.T_le_normalizer_L1 (hQT hq)) (by simp) hm hgm hqk
    have hL1L : S.L1 ≤ Subgroup.normalizer (L : Set G) :=
      (oTwoRes_le _).trans (inf_le_left.trans Subgroup.le_normalizer)
    exact hP.not_le (hPhat.trans hL1L)

end PSec

end Setting4

end CFSG.Quasithin.H13.A6
