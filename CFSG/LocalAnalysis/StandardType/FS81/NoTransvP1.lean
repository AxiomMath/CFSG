module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvN1

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G]

@[expose] def tb (b₀ x : G) : G := b₀⁻¹ * (x * b₀ * x⁻¹)

theorem conj_b0_eq_tb (b₀ x : G) : x * b₀ * x⁻¹ = b₀ * tb b₀ x := by
  rw [tb, mul_inv_cancel_left]

theorem tb_one (b₀ : G) : tb b₀ 1 = 1 := by simp [tb]

theorem tb_mem {b₀ : G} {K E : Subgroup G} {x : G} (hx : x ∈ transvN1 b₀ K E) :
    tb b₀ x ∈ E ⊓ K :=
  hx.2.2

theorem tb_mul {b₀ : G} {K E : Subgroup G} {x y : G} (hx : x ∈ transvN1 b₀ K E)
    (hy : y ∈ transvN1 b₀ K E) : tb b₀ (x * y) = tb b₀ x * tb b₀ y := by
  have h1 := hx.2.1 _ (tb_mem hy)
  calc tb b₀ (x * y) = b₀⁻¹ * (x * (y * b₀ * y⁻¹) * x⁻¹) := by simp only [tb]; group
    _ = b₀⁻¹ * (x * b₀ * x⁻¹) * (x * tb b₀ y * x⁻¹) := by rw [conj_b0_eq_tb b₀ y]; group
    _ = tb b₀ x * tb b₀ y := by rw [h1]; rfl

theorem tb_inv {b₀ : G} {K E : Subgroup G} {x : G} (hx : x ∈ transvN1 b₀ K E) :
    tb b₀ x⁻¹ = (tb b₀ x)⁻¹ := by
  have := tb_mul hx (Subgroup.inv_mem _ hx)
  rw [mul_inv_cancel, tb_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem tb_pow {b₀ : G} {K E : Subgroup G} {x : G} (hx : x ∈ transvN1 b₀ K E) (k : ℕ) :
    tb b₀ (x ^ k) = tb b₀ x ^ k := by
  induction k with
  | zero => simp [tb_one]
  | succ k ih => rw [pow_succ, tb_mul (Subgroup.pow_mem _ hx k) hx, ih, pow_succ]

theorem tb_conj {b₀ d : G} (hd : d * b₀ * d⁻¹ = b₀) (x : G) :
    tb b₀ (d * x * d⁻¹) = d * tb b₀ x * d⁻¹ := by
  have hc : d * b₀ = b₀ * d := by
    calc d * b₀ = d * b₀ * d⁻¹ * d := by group
      _ = b₀ * d := by rw [hd]
  have h1 : d⁻¹ * b₀ * d = b₀ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have h2 : b₀⁻¹ * d = d * b₀⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hc, mul_inv_cancel_right]
  calc tb b₀ (d * x * d⁻¹) = b₀⁻¹ * d * (x * (d⁻¹ * b₀ * d) * x⁻¹) * d⁻¹ := by
        simp only [tb]; group
    _ = d * b₀⁻¹ * (x * b₀ * x⁻¹) * d⁻¹ := by rw [h1, h2]
    _ = d * tb b₀ x * d⁻¹ := by simp only [tb]; group

theorem quot_eq_one_iff {N A : Subgroup G} [(A.subgroupOf N).Normal] (u : ↥N) :
    (QuotientGroup.mk u : ↥N ⧸ A.subgroupOf N) = 1 ↔ (u : G) ∈ A := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem quot_commute_of_mem {N A : Subgroup G} [(A.subgroupOf N).Normal] {u v : ↥N}
    (huv : (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ ∈ A) :
    Commute (QuotientGroup.mk u : ↥N ⧸ A.subgroupOf N) (QuotientGroup.mk v) := by
  have h1 : (QuotientGroup.mk (u * v * u⁻¹ * v⁻¹) : ↥N ⧸ A.subgroupOf N) = 1 :=
    (quot_eq_one_iff _).mpr (by simpa using huv)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem comm_inv_mul_comm_eq_one {Q : Type*} [Group Q] {x y e₁ e₂ : Q} (h1y : Commute e₁ y)
    (h2x : Commute e₂ x) (h12 : Commute e₁ e₂) (hcx : Commute (x * y * x⁻¹ * y⁻¹) x) :
    x⁻¹ * e₁ * (y * e₂) * (x⁻¹ * e₁)⁻¹ * (y * e₂)⁻¹ * (x * y * x⁻¹ * y⁻¹) = 1 := by
  have step1 : x⁻¹ * e₁ * (y * e₂) * (x⁻¹ * e₁)⁻¹ * (y * e₂)⁻¹ = x⁻¹ * y * x * y⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rw [h1y.left_comm, h12.left_comm, mul_inv_cancel_left, h2x.left_comm, mul_inv_cancel_left]
  have step2 : x⁻¹ * y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    have h3 := hcx.inv_left.eq
    calc x⁻¹ * y * x * y⁻¹ = x⁻¹ * ((x * y * x⁻¹ * y⁻¹)⁻¹ * x) := by group
      _ = x⁻¹ * (x * (x * y * x⁻¹ * y⁻¹)⁻¹) := by rw [h3]
      _ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  rw [step1, step2, inv_mul_cancel]

@[expose] def SignChanges {n : ℕ} (b : Fin (n + 1) → G) (b₀ : G) (E : Subgroup G) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ i → ∃ d ∈ Subgroup.normalizer (E : Set G),
    d * b₀ * d⁻¹ = b₀ ∧ d * b i * d⁻¹ = (b i)⁻¹ ∧ d * b j * d⁻¹ = b j

structure SylowN1 [Finite G] (b₀ : G) (K E P₁ : Subgroup G) : Prop where
  le : P₁ ≤ transvN1 b₀ K E
  pgroup : IsPGroup 3 P₁
  card : Nat.card P₁ = 3 ^ (Nat.card ↥(transvN1 b₀ K E)).factorization 3
  E_le : E ≤ P₁

structure TransvP1 [Finite G] (b₀ : G) (K E P₁ : Subgroup G) : Prop where
  le : P₁ ≤ transvN1 b₀ K E
  pgroup : IsPGroup 3 P₁
  card : Nat.card P₁ = 3 ^ (Nat.card ↥(transvN1 b₀ K E)).factorization 3
  E_le : E ≤ P₁
  surj : ∀ a ∈ E ⊓ K, ∃ x ∈ P₁, tb b₀ x = a

theorem TransvP1.toSylowN1 [Finite G] {b₀ : G} {K E P₁ : Subgroup G}
    (h : TransvP1 b₀ K E P₁) : SylowN1 b₀ K E P₁ :=
  ⟨h.le, h.pgroup, h.card, h.E_le⟩

namespace TransvSetup

variable [Finite G] {b₀ : G} {K E : Subgroup G}

theorem exists_transvP1' (h : TransvSetup b₀ K E) : ∃ P₁ : Subgroup G, TransvP1 b₀ K E P₁ := by
  obtain ⟨P₁, hle, hp, hc, hE, hs⟩ := h.exists_transvP1
  refine ⟨P₁, hle, hp, hc, hE, fun a ha => ?_⟩
  obtain ⟨x, hx, hx', hxa⟩ := hs a ha
  exact ⟨x, hx, hxa⟩

theorem normal_A (h : TransvSetup b₀ K E) :
    ((E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))).Normal :=
  ⟨fun a ha g => Subgroup.mem_subgroupOf.mpr (by
    simpa using h.inv g g.2 a (Subgroup.mem_subgroupOf.mp ha))⟩

theorem comm_E_mem_A (h : TransvSetup b₀ K E) {x : G} (hx : x ∈ transvN1 b₀ K E) {e : G}
    (he : e ∈ E) : x * e * x⁻¹ * e⁻¹ ∈ E ⊓ K := by
  rw [← h.sup] at he
  obtain ⟨y, hy, a, ha, rfl⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers b₀) (B := E ⊓ K)
    (fun y hy z hz => h.comm (h.sup ▸ Subgroup.mem_sup_left hy) hz.1) he
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hβA : tb b₀ x ∈ E ⊓ K := tb_mem hx
  have hβb : Commute b₀ (tb b₀ x) := h.comm h.b0_mem hβA.1
  have hxi : x * b₀ ^ i * x⁻¹ = b₀ ^ i * tb b₀ x ^ i := by
    rw [← conj_zpow, conj_b0_eq_tb, hβb.mul_zpow]
  have hxa : x * a * x⁻¹ = a := hx.2.1 a ha
  have e1 : x * (b₀ ^ i * a) * x⁻¹ * (b₀ ^ i * a)⁻¹ =
      (x * b₀ ^ i * x⁻¹) * (x * a * x⁻¹) * a⁻¹ * (b₀ ^ i)⁻¹ := by group
  rw [e1, hxi, hxa, mul_inv_cancel_right, ((hβb.zpow_zpow i i)).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem _ hβA i

theorem conj_mul_inv_mem_A (h : TransvSetup b₀ K E) {d : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) (hdb : d * b₀ * d⁻¹ = b₀) {c : G} (hc : c ∈ E) :
    d * c * d⁻¹ * c⁻¹ ∈ E ⊓ K := by
  rw [← h.sup] at hc
  obtain ⟨y, hy, a, ha, rfl⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers b₀) (B := E ⊓ K)
    (fun y hy z hz => h.comm (h.sup ▸ Subgroup.mem_sup_left hy) hz.1) hc
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hdi : d * b₀ ^ i * d⁻¹ = b₀ ^ i := by rw [← conj_zpow, hdb]
  have hda : d * a * d⁻¹ ∈ E ⊓ K := h.inv d hdN a ha
  have hw : d * a * d⁻¹ * a⁻¹ ∈ E ⊓ K := Subgroup.mul_mem _ hda (Subgroup.inv_mem _ ha)
  have hcomm : b₀ ^ i * (d * a * d⁻¹ * a⁻¹) = (d * a * d⁻¹ * a⁻¹) * b₀ ^ i :=
    h.comm (Subgroup.zpow_mem _ h.b0_mem i) hw.1
  have e : d * (b₀ ^ i * a) * d⁻¹ * (b₀ ^ i * a)⁻¹ = d * a * d⁻¹ * a⁻¹ := by
    calc d * (b₀ ^ i * a) * d⁻¹ * (b₀ ^ i * a)⁻¹
        = (d * b₀ ^ i * d⁻¹) * (d * a * d⁻¹ * a⁻¹) * (b₀ ^ i)⁻¹ := by group
      _ = d * a * d⁻¹ * a⁻¹ := by rw [hdi, hcomm, mul_inv_cancel_right]
  rw [e]
  exact hw

theorem mem_A_of_conj_mul (h : TransvSetup b₀ K E) {d : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) (hdb : d * b₀ * d⁻¹ = b₀) {c : G} (hc : c ∈ E)
    (hmul : d * c * d⁻¹ * c ∈ E ⊓ K) : c ∈ E ⊓ K := by
  have h1 := h.conj_mul_inv_mem_A hdN hdb hc
  have h2 : c * c ∈ E ⊓ K := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) hmul
    rwa [show (d * c * d⁻¹ * c⁻¹)⁻¹ * (d * c * d⁻¹ * c) = c * c by group] at this
  have hc3 : c ^ 3 = 1 := h.elem.2 c hc
  have : c = (c * c)⁻¹ * c ^ 3 := by group
  rw [this, hc3, mul_one]
  exact Subgroup.inv_mem _ h2

end TransvSetup

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem mem_normalizer (hP : SylowN1 b₀ K E P₁) {x : G} (hx : x ∈ P₁) :
    x ∈ Subgroup.normalizer (E : Set G) :=
  (hP.le hx).1

theorem mem_E (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {x : G} (hx : x ∈ P₁)
    (hx1 : tb b₀ x = 1) : x ∈ E :=
  h.mem_E_of_beta_eq_one hP.pgroup hx (hP.le hx) (Subtype.ext hx1)

theorem surj' (hP : TransvP1 b₀ K E P₁) :
    ∀ β ∈ E ⊓ K, ∃ x ∈ P₁, ∃ hx : x ∈ transvN1 b₀ K E,
      ((transvBeta b₀ K E ⟨x, hx⟩ : ↥(E ⊓ K)) : G) = β := fun β hβ => by
  obtain ⟨x, hx, hxβ⟩ := hP.surj β hβ
  exact ⟨x, hx, hP.le hx, hxβ⟩

theorem exists_sign_normalizer (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    {b : Fin (n + 1) → G} (hbE : ∀ i, b i ∈ E) (hsc : SignChanges b b₀ E) {i j : Fin (n + 1)}
    (hi : i ≠ 0) (hji : j ≠ i) :
    ∃ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) ∧
      d * b₀ * d⁻¹ = b₀ ∧ d * b i * d⁻¹ = (b i)⁻¹ ∧ d * b j * d⁻¹ = b j := by
  obtain ⟨d, hdN, h0, hdi, hdj⟩ := hsc i j hi hji
  obtain ⟨c, hc, hcd⟩ := h.exists_centralizer_mul_mem_normalizer hP.le hP.pgroup hP.card hP.surj'
    hdN
  have hcfix : ∀ y ∈ E, c * y * c⁻¹ = y := fun y hy => by
    rw [← Subgroup.mem_centralizer_iff.mp hc y hy, mul_inv_cancel_right]
  have hconj : ∀ y ∈ E, c * d * y * (c * d)⁻¹ = d * y * d⁻¹ := fun y hy => by
    have hdy : d * y * d⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hdN y).mp hy
    rw [show c * d * y * (c * d)⁻¹ = c * (d * y * d⁻¹) * c⁻¹ by group, hcfix _ hdy]
  refine ⟨c * d, Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hdN, hcd, ?_, ?_, ?_⟩
  · rw [hconj _ h.b0_mem, h0]
  · rw [hconj _ (hbE i), hdi]
  · rw [hconj _ (hbE j), hdj]

theorem forall_of_gen (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {p : G → Prop}
    (hmul : ∀ x y, x ∈ P₁ → y ∈ P₁ → p x → p y → p (x * y)) (hinv : ∀ x, x ∈ P₁ → p x → p x⁻¹)
    (hE : ∀ e ∈ E, p e) (hgen : ∀ k : Fin (n + 1), k ≠ 0 → ∃ x ∈ P₁, tb b₀ x = B.b k ∧ p x) :
    ∀ y ∈ P₁, p y := by
  let T : Subgroup G :=
    { carrier := {a | ∃ x ∈ P₁, p x ∧ tb b₀ x = a}
      mul_mem' := fun {a a'} ⟨x, hx, hpx, hxa⟩ ⟨x', hx', hpx', hxa'⟩ =>
        ⟨x * x', P₁.mul_mem hx hx', hmul x x' hx hx' hpx hpx', by
          rw [tb_mul (hP.le hx) (hP.le hx'), hxa, hxa']⟩
      one_mem' := ⟨1, P₁.one_mem, hE 1 E.one_mem, tb_one b₀⟩
      inv_mem' := fun {a} ⟨x, hx, hpx, hxa⟩ =>
        ⟨x⁻¹, P₁.inv_mem hx, hinv x hx hpx, by rw [tb_inv (hP.le hx), hxa]⟩ }
  have hbT : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ T := fun i hi => by
    obtain ⟨x, hx, hxb, hpx⟩ := hgen i hi
    exact ⟨x, hx, hpx, hxb⟩
  intro y hy
  have hyA : tb b₀ y ∈ E ⊓ K := tb_mem (hP.le hy)
  have hyS : tb b₀ y ∈ B.span := hB.1 ▸ hyA.1
  have hdisj : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := hB.1 ▸ h.disj
  have h0 := B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 hdisj ⟨tb b₀ y, hyS⟩ hyA.2
  have hT : tb b₀ y ∈ T := by
    have := B.vec_mem_of_zero (K := T) hbT h0
    rwa [B.vec_coords] at this
  obtain ⟨x, hx, hpx, hxy⟩ := hT
  have hxyE : x⁻¹ * y ∈ E := hP.mem_E h (P₁.mul_mem (P₁.inv_mem hx) hy) (by
    rw [tb_mul (hP.le (P₁.inv_mem hx)) (hP.le hy), tb_inv (hP.le hx), hxy, inv_mul_cancel])
  have := hmul x (x⁻¹ * y) hx (P₁.mul_mem (P₁.inv_mem hx) hy) hpx (hE _ hxyE)
  rwa [mul_inv_cancel_left] at this

theorem comm_mem_A_of_sign (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {x y d : G}
    (hx : x ∈ P₁) (hy : y ∈ P₁) (hdN : d ∈ Subgroup.normalizer (E : Set G))
    (hdP : d ∈ Subgroup.normalizer (P₁ : Set G)) (hdb : d * b₀ * d⁻¹ = b₀)
    (hdx : tb b₀ (d * x * d⁻¹) = (tb b₀ x)⁻¹) (hdy : tb b₀ (d * y * d⁻¹) = tb b₀ y) :
    x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K := by
  have hxN1 := hP.le hx
  have hyN1 := hP.le hy
  have hdxP : d * x * d⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hdP x).mp hx
  have hdyP : d * y * d⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hdP y).mp hy
  have hcP : x * y * x⁻¹ * y⁻¹ ∈ P₁ :=
    P₁.mul_mem (P₁.mul_mem (P₁.mul_mem hx hy) (P₁.inv_mem hx)) (P₁.inv_mem hy)
  have hcE : x * y * x⁻¹ * y⁻¹ ∈ E := by
    refine hP.mem_E h hcP ?_
    have hA : tb b₀ x * tb b₀ y = tb b₀ y * tb b₀ x := h.comm (tb_mem hxN1).1 (tb_mem hyN1).1
    rw [tb_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN1 hyN1) (Subgroup.inv_mem _ hxN1))
        (Subgroup.inv_mem _ hyN1), tb_mul (Subgroup.mul_mem _ hxN1 hyN1)
        (Subgroup.inv_mem _ hxN1), tb_mul hxN1 hyN1, tb_inv hxN1, tb_inv hyN1, hA]
    group
  set e₁ := x * (d * x * d⁻¹) with he₁
  set e₂ := y⁻¹ * (d * y * d⁻¹) with he₂
  have he₁E : e₁ ∈ E := hP.mem_E h (P₁.mul_mem hx hdxP) (by
    rw [tb_mul hxN1 (hP.le hdxP), hdx, mul_inv_cancel])
  have he₂E : e₂ ∈ E := hP.mem_E h (P₁.mul_mem (P₁.inv_mem hy) hdyP) (by
    rw [tb_mul (Subgroup.inv_mem _ hyN1) (hP.le hdyP), hdy, tb_inv hyN1, inv_mul_cancel])
  have hconj : d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ =
      x⁻¹ * e₁ * (y * e₂) * (x⁻¹ * e₁)⁻¹ * (y * e₂)⁻¹ := by
    rw [he₁, he₂]; group
  have := h.normal_A
  have hEN : ∀ {u : G}, u ∈ E → u ∈ Subgroup.normalizer (E : Set G) := fun hu =>
    mem_normalizer hP.toSylowN1 (hP.E_le hu)
  let X : ↥(Subgroup.normalizer (E : Set G)) := ⟨x, mem_normalizer hP.toSylowN1 hx⟩
  let Y : ↥(Subgroup.normalizer (E : Set G)) := ⟨y, mem_normalizer hP.toSylowN1 hy⟩
  let E₁ : ↥(Subgroup.normalizer (E : Set G)) := ⟨e₁, hEN he₁E⟩
  let E₂ : ↥(Subgroup.normalizer (E : Set G)) := ⟨e₂, hEN he₂E⟩
  have hcomm_E : ∀ {u e : G} (hu : u ∈ transvN1 b₀ K E) (he : e ∈ E),
      Commute (QuotientGroup.mk (⟨e, hEN he⟩ : ↥(Subgroup.normalizer (E : Set G))) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G)))
        (QuotientGroup.mk (⟨u, hu.1⟩ : ↥(Subgroup.normalizer (E : Set G)))) :=
    fun hu he => (quot_commute_of_mem (u := ⟨_, hu.1⟩) (v := ⟨_, hEN he⟩)
      (h.comm_E_mem_A hu he)).symm
  have hkey := comm_inv_mul_comm_eq_one (x := (QuotientGroup.mk X :
      _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))))
    (y := QuotientGroup.mk Y) (e₁ := QuotientGroup.mk E₁) (e₂ := QuotientGroup.mk E₂)
    (hcomm_E hyN1 he₁E) (hcomm_E hxN1 he₂E)
    (quot_commute_of_mem (by
      show e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ E ⊓ K
      rw [h.comm he₁E he₂E, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _))
    (by
      have h1 := hcomm_E hxN1 hcE
      have h2 : (⟨x * y * x⁻¹ * y⁻¹, hEN hcE⟩ : ↥(Subgroup.normalizer (E : Set G))) =
          X * Y * X⁻¹ * Y⁻¹ := rfl
      rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
      exact h1)
  have hmul : d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ * (x * y * x⁻¹ * y⁻¹) ∈ E ⊓ K := by
    rw [hconj]
    have := (quot_eq_one_iff (A := E ⊓ K) (X⁻¹ * E₁ * (Y * E₂) * (X⁻¹ * E₁)⁻¹ * (Y * E₂)⁻¹ *
      (X * Y * X⁻¹ * Y⁻¹))).mp (by
        simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hkey)
    simpa [X, Y, E₁, E₂] using this
  exact h.mem_A_of_conj_mul hdN hdb hcE hmul

theorem comm_mem_A (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E) {x y : G}
    (hx : x ∈ P₁) (hy : y ∈ P₁) : x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K := by
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hbA : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ E ⊓ K := fun i hi => ⟨hbE i, hB.2.2 i hi⟩
  have hpre : ∀ k : Fin (n + 1), k ≠ 0 → ∃ x ∈ P₁, tb b₀ x = B.b k := fun k hk =>
    hP.surj _ (hbA k hk)
  choose! xk hxkP hxkb using hpre
  have hcomm_mul : ∀ {u v v' : G}, u ∈ P₁ → v ∈ P₁ → u * v * u⁻¹ * v⁻¹ ∈ E ⊓ K →
      u * v' * u⁻¹ * v'⁻¹ ∈ E ⊓ K → u * (v * v') * u⁻¹ * (v * v')⁻¹ ∈ E ⊓ K := by
    intro u v v' hu hv h1 h2
    have h3 : v * (u * v' * u⁻¹ * v'⁻¹) * v⁻¹ ∈ E ⊓ K :=
      h.inv v (mem_normalizer hP.toSylowN1 hv) _ h2
    have := Subgroup.mul_mem _ h1 h3
    rwa [show u * v * u⁻¹ * v⁻¹ * (v * (u * v' * u⁻¹ * v'⁻¹) * v⁻¹) =
      u * (v * v') * u⁻¹ * (v * v')⁻¹ by group] at this
  have hcomm_inv : ∀ {u v : G}, v ∈ P₁ → u * v * u⁻¹ * v⁻¹ ∈ E ⊓ K →
      u * v⁻¹ * u⁻¹ * v⁻¹⁻¹ ∈ E ⊓ K := by
    intro u v hv h1
    have := h.inv v⁻¹ (mem_normalizer hP.toSylowN1 (P₁.inv_mem hv)) _ (Subgroup.inv_mem _ h1)
    rwa [show v⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * v⁻¹⁻¹ = u * v⁻¹ * u⁻¹ * v⁻¹⁻¹ by group] at this
  have hcomm_E : ∀ {u e : G}, u ∈ P₁ → e ∈ E → u * e * u⁻¹ * e⁻¹ ∈ E ⊓ K := fun hu he =>
    h.comm_E_mem_A (hP.le hu) he
  have hgen : ∀ k : Fin (n + 1), k ≠ 0 → ∀ l : Fin (n + 1), l ≠ 0 →
      xk k * xk l * (xk k)⁻¹ * (xk l)⁻¹ ∈ E ⊓ K := by
    intro k hk l hl
    by_cases hkl : l = k
    · subst hkl
      rw [mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    obtain ⟨d, hdN, hdP, hd0, hdk, hdl⟩ := hP.exists_sign_normalizer h hbE hsc hk hkl
    refine hP.comm_mem_A_of_sign h (hxkP k hk) (hxkP l hl) hdN hdP hd0 ?_ ?_
    · rw [tb_conj hd0, hxkb k hk, hdk]
    · rw [tb_conj hd0, hxkb l hl, hdl]
  have hk_all : ∀ k : Fin (n + 1), k ≠ 0 → ∀ v ∈ P₁, xk k * v * (xk k)⁻¹ * v⁻¹ ∈ E ⊓ K :=
    fun k hk => hP.forall_of_gen h B hB (p := fun v => xk k * v * (xk k)⁻¹ * v⁻¹ ∈ E ⊓ K)
      (fun v v' hv _ h1 h2 => hcomm_mul (hxkP k hk) hv h1 h2)
      (fun v hv h1 => hcomm_inv hv h1) (fun e he => hcomm_E (hxkP k hk) he)
      (fun l hl => ⟨xk l, hxkP l hl, hxkb l hl, hgen k hk l hl⟩)
  refine hP.forall_of_gen h B hB (p := fun u => ∀ v ∈ P₁, u * v * u⁻¹ * v⁻¹ ∈ E ⊓ K)
    (fun u u' hu hu' h1 h2 v hv => ?_) (fun u hu h1 v hv => ?_) (fun e he v hv => ?_)
    (fun k hk => ⟨xk k, hxkP k hk, hxkb k hk, hk_all k hk⟩) x hx y hy
  · have h3 : u * (u' * v * u'⁻¹ * v⁻¹) * u⁻¹ ∈ E ⊓ K :=
      h.inv u (mem_normalizer hP.toSylowN1 hu) _ (h2 v hv)
    have := Subgroup.mul_mem _ h3 (h1 v hv)
    rwa [show u * (u' * v * u'⁻¹ * v⁻¹) * u⁻¹ * (u * v * u⁻¹ * v⁻¹) =
      u * u' * v * (u * u')⁻¹ * v⁻¹ by group] at this
  · have := h.inv u⁻¹ (mem_normalizer hP.toSylowN1 (P₁.inv_mem hu)) _ (Subgroup.inv_mem _ (h1 v hv))
    rwa [show u⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * u⁻¹⁻¹ = u⁻¹ * v * u⁻¹⁻¹ * v⁻¹ by group] at this
  · have := Subgroup.inv_mem _ (hcomm_E hv he)
    rwa [show (v * e * v⁻¹ * e⁻¹)⁻¹ = e * v * e⁻¹ * v⁻¹ by group] at this

theorem cube_mem_A (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E) {x : G}
    (hx : x ∈ P₁) : x ^ 3 ∈ E ⊓ K := by
  have := h.normal_A
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hbA : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ E ⊓ K := fun i hi => ⟨hbE i, hB.2.2 i hi⟩
  have hcubeE : ∀ {u : G}, u ∈ P₁ → u ^ 3 ∈ E := fun {u} hu =>
    hP.mem_E h (P₁.pow_mem hu 3) (by rw [tb_pow (hP.le hu), h.elem.2 _ (tb_mem (hP.le hu)).1])
  have hmul : ∀ u v, u ∈ P₁ → v ∈ P₁ → u ^ 3 ∈ E ⊓ K → v ^ 3 ∈ E ⊓ K → (u * v) ^ 3 ∈ E ⊓ K := by
    intro u v hu hv h1 h2
    let U : ↥(Subgroup.normalizer (E : Set G)) := ⟨u, mem_normalizer hP.toSylowN1 hu⟩
    let V : ↥(Subgroup.normalizer (E : Set G)) := ⟨v, mem_normalizer hP.toSylowN1 hv⟩
    have hUV : Commute (QuotientGroup.mk U :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) (QuotientGroup.mk V) :=
      quot_commute_of_mem (u := U) (v := V) (hP.comm_mem_A h B hB hsc hu hv)
    have hU : (QuotientGroup.mk (U ^ 3) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) = 1 :=
      (quot_eq_one_iff _).mpr (by simpa [U] using h1)
    have hV : (QuotientGroup.mk (V ^ 3) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) = 1 :=
      (quot_eq_one_iff _).mpr (by simpa [V] using h2)
    have : (QuotientGroup.mk ((U * V) ^ 3) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) = 1 := by
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, hUV.mul_pow, ← QuotientGroup.mk_pow,
        ← QuotientGroup.mk_pow, hU, hV, one_mul]
    simpa [U, V] using (quot_eq_one_iff _).mp this
  refine hP.forall_of_gen h B hB (p := fun u => u ^ 3 ∈ E ⊓ K) hmul
    (fun u _ h1 => by rw [inv_pow]; exact Subgroup.inv_mem _ h1)
    (fun e he => by rw [h.elem.2 e he]; exact Subgroup.one_mem _) (fun k hk => ?_) x hx
  obtain ⟨xk, hxkP, hxkb⟩ := hP.surj _ (hbA k hk)
  refine ⟨xk, hxkP, hxkb, ?_⟩
  obtain ⟨d, hdN, hdP, hd0, hdk, -⟩ := hP.exists_sign_normalizer h hbE hsc hk
    (show (0 : Fin (n + 1)) ≠ k from fun h0 => hk h0.symm)
  have hdxP : d * xk * d⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hdP xk).mp hxkP
  set e₁ := xk * (d * xk * d⁻¹) with he₁
  have he₁E : e₁ ∈ E := hP.mem_E h (P₁.mul_mem hxkP hdxP) (by
    rw [tb_mul (hP.le hxkP) (hP.le hdxP), tb_conj hd0, hxkb, hdk, mul_inv_cancel])
  refine h.mem_A_of_conj_mul hdN hd0 (hcubeE hxkP) ?_
  let X : ↥(Subgroup.normalizer (E : Set G)) := ⟨xk, mem_normalizer hP.toSylowN1 hxkP⟩
  let E₁ : ↥(Subgroup.normalizer (E : Set G)) := ⟨e₁, mem_normalizer hP.toSylowN1 (hP.E_le he₁E)⟩
  have hXE : Commute (QuotientGroup.mk X :
      _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G)))⁻¹ (QuotientGroup.mk E₁) := by
    have := quot_commute_of_mem (A := E ⊓ K) (u := X⁻¹) (v := E₁)
      (by simpa [X, E₁] using h.comm_E_mem_A (hP.le (P₁.inv_mem hxkP)) he₁E)
    rwa [QuotientGroup.mk_inv] at this
  have hE₁3 : (QuotientGroup.mk E₁ :
      _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (quot_eq_one_iff _).mpr (by simp [E₁, h.elem.2 e₁ he₁E])
  have hq : (QuotientGroup.mk ((X⁻¹ * E₁) ^ 3 * X ^ 3) :
      _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_inv]
    rw [hXE.mul_pow, hE₁3, mul_one, inv_pow, inv_mul_cancel]
  have hconj : d * xk ^ 3 * d⁻¹ = (xk⁻¹ * e₁) ^ 3 := by
    rw [he₁, ← conj_pow]; congr 1; group
  rw [hconj]
  simpa [X, E₁] using (quot_eq_one_iff _).mp hq

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
