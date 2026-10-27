module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aRankFour
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aB2Construct
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aAtildeElem

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Lift

open CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem (exists_of_mem_A)

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le {p : ℕ} [Fact p.Prime] {H : Subgroup G} (S : Sylow p ↥H)
    {Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup p Q) :
    ∃ k ∈ H, ∀ q ∈ Q, k⁻¹ * q * k ∈ (S : Subgroup ↥H).map H.subtype := by
  have hQ' : IsPGroup p ↥(Q.subgroupOf H) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H S R
  refine ⟨k, k.2, fun q hq => ?_⟩
  have h1 : (⟨q, hQH hq⟩ : ↥H) ∈ (R : Subgroup ↥H) :=
    hR (by simpa [Subgroup.mem_subgroupOf] using hq)
  rw [← hk] at h1
  simp only [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  refine ⟨_, h1, ?_⟩
  simp [MulAut.conj_symm_apply, MulAut.smul_def]

theorem exists_translate {p : ℕ} [Fact p.Prime] {H : Subgroup G} (S : Sylow p ↥H)
    {g : G} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∃ k ∈ H, ∀ x ∈ (S : Subgroup ↥H).map H.subtype,
      (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈ (S : Subgroup ↥H).map H.subtype := by
  set A₀ := (S : Subgroup ↥H).map H.subtype with hA₀def
  have hA₀H : A₀ ≤ H := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hA₀p : IsPGroup p A₀ := S.isPGroup'.map H.subtype
  set Q := A₀.map (MulAut.conj g).toMonoidHom with hQdef
  have hQH : Q ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x (hA₀H hx)
  have hQp : IsPGroup p Q := hA₀p.map _
  obtain ⟨k, hk, hkQ⟩ := exists_conj_le S hQH hQp
  refine ⟨k, hk, fun x hx => ?_⟩
  have := hkQ (g * x * g⁻¹) ⟨x, hx, rfl⟩
  have e : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
  rw [e]
  exact this

section Ahat

variable (B₁ : Subgroup G) (b : G)

@[expose] def Ahat : Subgroup G where
  carrier := {n | (∀ y ∈ B₁, n * y * n⁻¹ = y) ∧ n * b * n⁻¹ * b⁻¹ ∈ B₁}
  one_mem' := ⟨fun y _ => by simp, by simp⟩
  mul_mem' := fun {n m} hn hm => by
    refine ⟨fun y hy => ?_, ?_⟩
    · rw [show n * m * y * (n * m)⁻¹ = n * (m * y * m⁻¹) * n⁻¹ by group, hm.1 y hy, hn.1 y hy]
    · have e : n * m * b * (n * m)⁻¹ * b⁻¹ =
          (n * (m * b * m⁻¹ * b⁻¹) * n⁻¹) * (n * b * n⁻¹ * b⁻¹) := by group
      rw [e, hn.1 _ hm.2]
      exact mul_mem hm.2 hn.2
  inv_mem' := fun {n} hn => by
    have hinv : ∀ y ∈ B₁, n⁻¹ * y * n⁻¹⁻¹ = y := by
      intro y hy
      have := hn.1 y hy
      calc n⁻¹ * y * n⁻¹⁻¹ = n⁻¹ * (n * y * n⁻¹) * n := by rw [this, inv_inv]
        _ = y := by group
    refine ⟨hinv, ?_⟩
    have e : n⁻¹ * b * n⁻¹⁻¹ * b⁻¹ = n⁻¹ * (n * b * n⁻¹ * b⁻¹)⁻¹ * n⁻¹⁻¹ := by group
    rw [e, hinv _ (inv_mem hn.2)]
    exact inv_mem hn.2

variable {B₁ b}

theorem mem_Ahat {n : G} : n ∈ Ahat B₁ b ↔ (∀ y ∈ B₁, n * y * n⁻¹ = y) ∧ n * b * n⁻¹ * b⁻¹ ∈ B₁ :=
  Iff.rfl

@[expose] def beta (b n : G) : G := n * b * n⁻¹ * b⁻¹

theorem beta_def (n : G) : beta b n = n * b * n⁻¹ * b⁻¹ := rfl

theorem beta_mem {n : G} (hn : n ∈ Ahat B₁ b) : beta b n ∈ B₁ := hn.2

theorem conj_b {n : G} : n * b * n⁻¹ = beta b n * b := by
  rw [beta_def, inv_mul_cancel_right]

theorem beta_mul (hB₁ab : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) {n m : G} (hn : n ∈ Ahat B₁ b)
    (hm : m ∈ Ahat B₁ b) : beta b (n * m) = beta b n * beta b m := by
  have e : beta b (n * m) = (n * beta b m * n⁻¹) * beta b n := by
    simp only [beta_def]
    group
  rw [e, hn.1 _ (beta_mem hm)]
  exact hB₁ab _ (beta_mem hm) _ (beta_mem hn)

theorem beta_conj {g : G} (hgb : g * b * g⁻¹ = b) (x : G) :
    beta b (g * x * g⁻¹) = g * beta b x * g⁻¹ := by
  simp only [beta_def]
  calc g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ * b⁻¹
      = g * x * g⁻¹ * (g * b * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by rw [hgb]
    _ = g * (x * b * x⁻¹ * b⁻¹) * g⁻¹ := by group

theorem beta_one_of_mem (hbB₁ : ∀ y ∈ B₁, b * y = y * b) {y : G} (hy : y ∈ B₁) :
    beta b y = 1 := by
  rw [beta_def, ← hbB₁ y hy]
  group

end Ahat

abbrev BB (b b₁ b₂ b₃ : G) : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)

abbrev BO (b₁ b₂ b₃ : G) : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)

structure Data0 (b b₁ b₂ b₃ : G) : Prop where
  Bab : ∀ x ∈ BB b b₁ b₂ b₃, ∀ y ∈ BB b b₁ b₂ b₃, x * y = y * x
  B3 : ∀ x ∈ BB b b₁ b₂ b₃, x ^ 3 = 1
  Bcard : Nat.card (BB b b₁ b₂ b₃) = 81
  B₁card : Nat.card (BO b₁ b₂ b₃) = 27
  B₁N : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
    ∀ y ∈ BO b₁ b₂ b₃, n * y * n⁻¹ ∈ BO b₁ b₂ b₃
  CB : ∀ x ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
    IsPGroup 3 (Subgroup.zpowers x) → x ∈ BB b b₁ b₂ b₃

structure Data (b b₁ b₂ b₃ : G) : Prop extends Data0 b b₁ b₂ b₃ where
  surj : ∀ y ∈ BO b₁ b₂ b₃, ∃ a : G, (∀ z ∈ BO b₁ b₂ b₃, a * z * a⁻¹ = z) ∧ a * b * a⁻¹ = y * b

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem B₁_le_B : BO b₁ b₂ b₃ ≤ BB b b₁ b₂ b₃ := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.B₁_le_B

theorem b_mem_B : b ∈ BB b b₁ b₂ b₃ := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.b_mem_B

theorem B_eq_sup : BB b b₁ b₂ b₃ = Subgroup.zpowers b ⊔ BO b₁ b₂ b₃ := by
  rw [BB, BO, Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

theorem B₁ab : ∀ x ∈ BO b₁ b₂ b₃, ∀ y ∈ BO b₁ b₂ b₃, x * y = y * x := fun x hx y hy =>
  D.Bab x (D.B₁_le_B hx) y (D.B₁_le_B hy)

theorem B₁3 : ∀ y ∈ BO b₁ b₂ b₃, y ^ 3 = 1 := fun y hy => D.B3 y (D.B₁_le_B hy)

theorem bB₁ : ∀ y ∈ BO b₁ b₂ b₃, b * y = y * b := fun y hy =>
  D.Bab b D.b_mem_B y (D.B₁_le_B hy)

theorem b3 : b ^ 3 = 1 := D.B3 b D.b_mem_B

theorem exists_of_mem_B {z : G} (hz : z ∈ BB b b₁ b₂ b₃) :
    ∃ n : ℕ, n < 3 ∧ ∃ y ∈ BO b₁ b₂ b₃, z = b ^ n * y := by
  rw [D.B_eq_sup] at hz
  refine exists_of_mem_A D.b3 (fun x hx => ?_) hz
  rw [D.bB₁ x hx, mul_inv_cancel_right]
  exact hx

theorem comm_mem {x z : G} (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) (hz : z ∈ BB b b₁ b₂ b₃) :
    x * z * x⁻¹ * z⁻¹ ∈ BO b₁ b₂ b₃ := by
  obtain ⟨n, -, y, hy, rfl⟩ := D.exists_of_mem_B hz
  have hβb : Commute (beta b x) b := (D.bB₁ _ (beta_mem hx)).symm
  have e : x * (b ^ n * y) * x⁻¹ * (b ^ n * y)⁻¹ = beta b x ^ n := by
    have h1 : x * (b ^ n * y) * x⁻¹ = (x * b * x⁻¹) ^ n * (x * y * x⁻¹) := by
      rw [conj_pow]
      group
    rw [h1, hx.1 y hy, conj_b, hβb.mul_pow]
    group
  rw [e]
  exact pow_mem (beta_mem hx) n

theorem B_le_Ahat : BB b b₁ b₂ b₃ ≤ Ahat (BO b₁ b₂ b₃) b := by
  intro z hz
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [D.Bab z hz y (D.B₁_le_B hy), mul_inv_cancel_right]
  · rw [D.Bab z hz b D.b_mem_B, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem cen_le_Ahat :
    Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ≤ Ahat (BO b₁ b₂ b₃) b := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [← hx y (D.B₁_le_B hy), mul_inv_cancel_right]
  · rw [← hx b D.b_mem_B, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem mem_cen_of_beta {x : G} (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) (h1 : beta b x = 1) :
    x ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
  have hxb : x * b * x⁻¹ = b := by rw [conj_b, h1, one_mul]
  have hle : BB b b₁ b₂ b₃ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [BB, Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hzx : x * z * x⁻¹ = z := by
      rcases hz with rfl | hz
      · exact hxb
      · exact hx.1 z (Subgroup.subset_closure hz)
    rw [mul_inv_eq_iff_eq_mul] at hzx
    exact hzx.symm
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)

theorem mem_B_of_beta {x : G} (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) (h1 : beta b x = 1)
    (hp : IsPGroup 3 (Subgroup.zpowers x)) : x ∈ BB b b₁ b₂ b₃ :=
  D.CB x (D.mem_cen_of_beta hx h1) hp

theorem conj_mem_Ahat {g : G}
    (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) {x : G}
    (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) : g * x * g⁻¹ ∈ Ahat (BO b₁ b₂ b₃) b := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := inv_mem hg
  refine ⟨fun y hy => ?_, ?_⟩
  · have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ BO b₁ b₂ b₃ := D.B₁N _ hg' y hy
    calc g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹
        = g * (x * (g⁻¹ * y * g⁻¹⁻¹) * x⁻¹) * g⁻¹ := by group
      _ = y := by rw [hx.1 _ hy']; group
  · have hbg : g⁻¹ * b * g⁻¹⁻¹ ∈ BB b b₁ b₂ b₃ :=
      (Subgroup.mem_normalizer_iff.mp hg' b).mp D.b_mem_B
    have h1 := D.B₁N g hg _ (D.comm_mem hx hbg)
    have e : g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ * b⁻¹ =
        g * (x * (g⁻¹ * b * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * b * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1

theorem Ahat_le_N :
    Ahat (BO b₁ b₂ b₃) b ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
  intro x hx
  refine CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem fun z hz => ?_
  have h1 := D.comm_mem hx hz
  have : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
  rw [this]
  exact mul_mem (D.B₁_le_B h1) hz

theorem beta_one : beta b (1 : G) = 1 := by simp [beta_def]

theorem beta_pow {x : G} (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) (n : ℕ) :
    beta b (x ^ n) = beta b x ^ n := by
  induction n with
  | zero => simp [beta_def]
  | succ n ih => rw [pow_succ, beta_mul D.B₁ab (pow_mem hx n) hx, ih, pow_succ]

theorem beta_inv {x : G} (hx : x ∈ Ahat (BO b₁ b₂ b₃) b) : beta b x⁻¹ = (beta b x)⁻¹ := by
  have h := beta_mul D.B₁ab (inv_mem hx) hx
  rw [inv_mul_cancel, D.beta_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem exists_pow_beta {a : G} (ha : a ∈ Ahat (BO b₁ b₂ b₃) b) :
    ∃ m : ℕ, IsPGroup 3 (Subgroup.zpowers (a ^ m)) ∧ beta b (a ^ m) = beta b a := by
  obtain ⟨e, k, hk3, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' 3 (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (k * j) % 3 = 1 := by
    rcases (by omega : k % 3 = 1 ∨ k % 3 = 2) with h | h
    · exact ⟨1, by rw [mul_one]; exact h⟩
    · exact ⟨2, by rw [Nat.mul_mod, h]⟩
  refine ⟨k * j, fun g => ⟨e, ?_⟩, ?_⟩
  · obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    have hcm : (a ^ (k * j)) ^ (3 ^ e) = 1 := by
      rw [← pow_mul, show k * j * 3 ^ e = (3 ^ e * k) * j by ring, pow_mul, ← hk,
        pow_orderOf_eq_one, one_pow]
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm z,
      zpow_mul, zpow_natCast, hcm, one_zpow]
  · have h3 : beta b a ^ 3 = 1 := D.B₁3 _ (beta_mem ha)
    rw [D.beta_pow ha, pow_eq_pow_mod _ h3, hj, pow_one]

section Sylow

variable {S : Sylow 3 ↥(Ahat (BO b₁ b₂ b₃) b)}
  (hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
include hS

theorem A0_le : (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype ≤
    Ahat (BO b₁ b₂ b₃) b := by
  rintro _ ⟨s, -, rfl⟩
  exact s.2

theorem isPGroup_A0 :
    IsPGroup 3 ↥((S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype) :=
  S.isPGroup'.map _

theorem mem_B_of_mem_A0 {x : G}
    (hx : x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    (h1 : beta b x = 1) : x ∈ BB b b₁ b₂ b₃ :=
  D.mem_B_of_beta (D.A0_le hS hx) h1 ((D.isPGroup_A0 hS).to_le (Subgroup.zpowers_le.2 hx))

theorem cen_conj_pow {δ : G} (hδ : δ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hδA : ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      δ * x * δ⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    {y : G} (hy : y ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype) :
    δ * y * δ⁻¹ * y⁻¹ ∈ BB b b₁ b₂ b₃ ∧
      ∀ n : ℕ, δ ^ n * y * (δ ^ n)⁻¹ = (δ * y * δ⁻¹ * y⁻¹) ^ n * y := by
  rw [Subgroup.mem_centralizer_iff] at hδ
  have hδb : δ * b * δ⁻¹ = b := by rw [← hδ b D.b_mem_B, mul_inv_cancel_right]
  have hyÂ := D.A0_le hS hy
  have hw : δ * y * δ⁻¹ * y⁻¹ ∈ BB b b₁ b₂ b₃ := by
    refine D.mem_B_of_mem_A0 hS (mul_mem (hδA y hy) (inv_mem hy)) ?_
    have hc : beta b (δ * y * δ⁻¹) = beta b y := by
      rw [beta_conj hδb, ← hδ _ (D.B₁_le_B (beta_mem hyÂ)), mul_inv_cancel_right]
    rw [beta_mul D.B₁ab (D.A0_le hS (hδA y hy)) (inv_mem hyÂ), hc, D.beta_inv hyÂ, mul_inv_cancel]
  refine ⟨hw, fun n => ?_⟩
  set w := δ * y * δ⁻¹ * y⁻¹ with hwdef
  have hδw : δ * w * δ⁻¹ = w := by rw [← hδ w hw, mul_inv_cancel_right]
  have hδwn : ∀ n : ℕ, δ * w ^ n * δ⁻¹ = w ^ n := fun n => by rw [← conj_pow, hδw]
  induction n with
  | zero => simp
  | succ n ih =>
    calc δ ^ (n + 1) * y * (δ ^ (n + 1))⁻¹ = δ * (δ ^ n * y * (δ ^ n)⁻¹) * δ⁻¹ := by group
      _ = δ * (w ^ n * y) * δ⁻¹ := by rw [ih]
      _ = (δ * w ^ n * δ⁻¹) * (δ * y * δ⁻¹) := by group
      _ = w ^ n * (w * y) := by rw [hδwn n, hwdef, inv_mul_cancel_right]
      _ = w ^ (n + 1) * y := by rw [← mul_assoc, ← pow_succ]

theorem cen_two {δ : G} (hδ : δ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hδA : ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      δ * x * δ⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    (hδ2 : IsPGroup 2 (Subgroup.zpowers δ)) {y : G}
    (hy : y ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype) :
    δ * y * δ⁻¹ = y := by
  obtain ⟨hw, hpow⟩ := D.cen_conj_pow hS hδ hδA hy
  obtain ⟨f, hf⟩ := hδ2 ⟨δ, Subgroup.mem_zpowers δ⟩
  have hδf : δ ^ (2 ^ f) = 1 := by simpa using congrArg Subtype.val hf
  have h1 := hpow (2 ^ f)
  rw [hδf, one_mul, inv_one, mul_one] at h1
  have hwf : (δ * y * δ⁻¹ * y⁻¹) ^ (2 ^ f) = 1 := by
    have := congrArg (· * y⁻¹) h1
    simpa using this.symm
  have hw3 : (δ * y * δ⁻¹ * y⁻¹) ^ 3 = 1 := D.B3 _ hw
  have hcop : Nat.Coprime (2 ^ f) 3 := Nat.Coprime.pow_left f (by norm_num)
  have hw1 : δ * y * δ⁻¹ * y⁻¹ = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hwf, hw3⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  rw [mul_inv_eq_one] at hw1
  exact hw1

theorem comm_mem_of_cen
    (hAab : ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      ∀ y ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        x * y * x⁻¹ * y⁻¹ ∈ BO b₁ b₂ b₃)
    {δ : G} (hδ : δ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hδA : ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      δ * x * δ⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    {y : G} (hy : y ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype) :
    δ * y * δ⁻¹ * y⁻¹ ∈ BO b₁ b₂ b₃ := by
  obtain ⟨hw, hpow⟩ := D.cen_conj_pow hS hδ hδA hy
  set w := δ * y * δ⁻¹ * y⁻¹ with hwdef
  obtain ⟨e, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos δ).ne' 3 (by norm_num)
  have hδm : δ ^ m ∈ BB b b₁ b₂ b₃ := by
    refine D.CB _ (pow_mem hδ m) fun g => ⟨e, ?_⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    have h1 : (δ ^ m) ^ (3 ^ e) = 1 := by
      rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm z,
      zpow_mul, zpow_natCast, h1, one_zpow]
  have hwm : w ^ m ∈ BO b₁ b₂ b₃ := by
    have h1 := hAab _ (hS hδm) y hy
    have h2 := hpow m
    rw [show δ ^ m * y * (δ ^ m)⁻¹ * y⁻¹ = w ^ m by rw [h2, mul_inv_cancel_right]] at h1
    exact h1
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (m * j) % 3 = 1 := by
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h
    · exact ⟨1, by rw [mul_one]; exact h⟩
    · exact ⟨2, by rw [Nat.mul_mod, h]⟩
  have hw3 : w ^ 3 = 1 := D.B3 _ hw
  have : w = (w ^ m) ^ j := by rw [← pow_mul, pow_eq_pow_mod _ hw3, hj, pow_one]
  rw [this]
  exact pow_mem hwm j

end Sylow

end Data0

namespace Data

variable {b b₁ b₂ b₃ : G} (D : Data b b₁ b₂ b₃)
include D

section Sylow

variable {S : Sylow 3 ↥(Ahat (BO b₁ b₂ b₃) b)}
  (hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
include hS

theorem exists_beta_eq {y : G} (hy : y ∈ BO b₁ b₂ b₃) :
    ∃ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      beta b x = y := by
  obtain ⟨a, ha1, ha2⟩ := D.surj y hy
  have haA : a ∈ Ahat (BO b₁ b₂ b₃) b := ⟨ha1, by rw [ha2, mul_inv_cancel_right]; exact hy⟩
  have hβa : beta b a = y := by rw [beta_def, ha2, mul_inv_cancel_right]
  obtain ⟨m, hmp, hmβ⟩ := D.exists_pow_beta haA
  obtain ⟨k, hk, hkQ⟩ := exists_conj_le S (Subgroup.zpowers_le.2 (pow_mem haA m)) hmp
  refine ⟨k⁻¹ * a ^ m * k, hkQ _ (Subgroup.mem_zpowers _), ?_⟩
  have e : k⁻¹ * a ^ m * k = k⁻¹ * a ^ m * k⁻¹⁻¹ := by rw [inv_inv]
  rw [beta_mul D.B₁ab (mul_mem (inv_mem hk) (pow_mem haA m)) hk,
    beta_mul D.B₁ab (inv_mem hk) (pow_mem haA m), D.beta_inv hk, hmβ, hβa,
    D.B₁ab _ (inv_mem (beta_mem hk)) _ hy, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_translate_cen {g : G}
    (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∃ k ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈
          (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype := by
  obtain ⟨k₀, hk₀, hk₀A⟩ := exists_translate S (fun x hx => D.conj_mem_Ahat hg hx)
  obtain ⟨a, haA, hβa⟩ := D.exists_beta_eq hS (inv_mem (beta_mem hk₀))
  have haÂ := D.A0_le hS haA
  refine ⟨k₀ * a, D.mem_cen_of_beta (mul_mem hk₀ haÂ) ?_, fun x hx => ?_⟩
  · rw [beta_mul D.B₁ab hk₀ haÂ, hβa, mul_inv_cancel]
  · have e : ((k₀ * a)⁻¹ * g) * x * ((k₀ * a)⁻¹ * g)⁻¹ =
        a⁻¹ * ((k₀⁻¹ * g) * x * (k₀⁻¹ * g)⁻¹) * a := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem haA) (hk₀A x hx)) haA

end Sylow

end Data

theorem pow_conj_fix {g x : G} (h : g * x * g⁻¹ = x) (n : ℕ) : g ^ n * x * (g ^ n)⁻¹ = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by group
      _ = x := by rw [ih, h]

theorem pow_conj_inv {g x : G} (h : g * x * g⁻¹ = x⁻¹) {n : ℕ} (hn : Odd n) :
    g ^ n * x * (g ^ n)⁻¹ = x⁻¹ := by
  have h2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
    have e1 : g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
      rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
    have e2 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e1, h, e2, h, inv_inv]
  obtain ⟨k, rfl⟩ := hn
  calc g ^ (2 * k + 1) * x * (g ^ (2 * k + 1))⁻¹
      = g * ((g ^ 2) ^ k * x * ((g ^ 2) ^ k)⁻¹) * g⁻¹ := by
        rw [← pow_mul, pow_succ']; group
    _ = x⁻¹ := by rw [pow_conj_fix h2 k, h]

theorem exists_odd_pow_two (g : G) : ∃ m : ℕ, Odd m ∧ IsPGroup 2 (Subgroup.zpowers (g ^ m)) := by
  obtain ⟨e, u, hu, hge⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨u, hu, fun x => ⟨e, ?_⟩⟩
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp x.2
  apply Subtype.ext
  have h1 : (g ^ u) ^ (2 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hge, pow_orderOf_eq_one]
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm z, zpow_mul,
    zpow_natCast, h1, one_zpow]

theorem conj_inv_of_closure {S : Set G}
    (hab : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) {g : G}
    (hg : ∀ s ∈ S, g * s * g⁻¹ = s⁻¹) : ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ = y⁻¹ := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hg x hx
  | one => simp
  | mul x z hx hz ihx ihz =>
    rw [show g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) by group, ihx, ihz,
      ← mul_inv_rev, hab z hz x hx]
  | inv x hx ihx => rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group, ihx]

theorem conj_eq_of_closure {S : Set G} {g : G} (hg : ∀ s ∈ S, g * s * g⁻¹ = s) :
    ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ = y := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hg x hx
  | one => simp
  | mul x z hx hz ihx ihz =>
    rw [show g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) by group, ihx, ihz]
  | inv x hx ihx => rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group, ihx]

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem mem₁ : b₁ ∈ BO b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
theorem mem₂ : b₂ ∈ BO b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
theorem mem₃ : b₃ ∈ BO b₁ b₂ b₃ := Subgroup.subset_closure (by simp)

theorem cen_le_N : Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := fun _ hk =>
  D.Ahat_le_N (D.cen_le_Ahat hk)

theorem translate_conj {k g z : G} (hk : k ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hz : g * z * g⁻¹ ∈ BB b b₁ b₂ b₃) : (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = g * z * g⁻¹ := by
  rw [Subgroup.mem_centralizer_iff] at hk
  have h := hk _ hz
  calc (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = k⁻¹ * ((g * z * g⁻¹) * k) := by group
    _ = k⁻¹ * (k * (g * z * g⁻¹)) := by rw [h]
    _ = g * z * g⁻¹ := by group

theorem conj_mem_B {g z : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hz : z ∈ BB b b₁ b₂ b₃) : g * z * g⁻¹ ∈ BB b b₁ b₂ b₃ :=
  (Subgroup.mem_normalizer_iff.mp hg z).mp hz

theorem isPGroup_B : IsPGroup 3 (BB b b₁ b₂ b₃) :=
  IsPGroup.of_card (n := 4) (by rw [D.Bcard]; norm_num)

theorem b_not_mem : b ∉ BO b₁ b₂ b₃ := by
  intro hb
  have : BB b b₁ b₂ b₃ = BO b₁ b₂ b₃ := by
    rw [D.B_eq_sup]
    exact sup_eq_right.mpr ((Subgroup.zpowers_le).2 hb)
  have h := D.Bcard
  rw [this, D.B₁card] at h
  omega

theorem b₁_ne_b₂ : b₁ ≠ b₂ := by
  intro e
  have hinj := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord_injective
    (D.B₁ab _ D.mem₁ _ D.mem₂) (D.B₁ab _ D.mem₁ _ D.mem₃) (D.B₁ab _ D.mem₂ _ D.mem₃)
    (D.B₁3 _ D.mem₁) (D.B₁3 _ D.mem₂) (D.B₁3 _ D.mem₃) D.B₁card
  have e' : CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (1, 0, 0) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 1, 0) := by
    simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e]
  exact absurd (hinj e') (by decide)

end Data0

namespace Data

variable {b b₁ b₂ b₃ : G} (D : Data b b₁ b₂ b₃)
include D

section Sylow3

variable {S : Sylow 3 ↥(Ahat (BO b₁ b₂ b₃) b)}
  (hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
include hS

theorem card_A0 :
    Nat.card ↥((S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype) =
      3 ^ 7 := by
  set A0 := (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype
  let φ : ↥A0 →* ↥(BO b₁ b₂ b₃) :=
    { toFun := fun x => ⟨beta b x, beta_mem (D.A0_le hS x.2)⟩
      map_one' := Subtype.ext D.beta_one
      map_mul' := fun x y => Subtype.ext (beta_mul D.B₁ab (D.A0_le hS x.2) (D.A0_le hS y.2)) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := D.exists_beta_eq hS hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : φ.ker = (BB b b₁ b₂ b₃).subgroupOf A0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact D.mem_B_of_mem_A0 hS x.2 (congrArg Subtype.val h1)
    · intro hx
      apply Subtype.ext
      show beta b x = 1
      rw [beta_def, D.Bab _ hx b D.b_mem_B, mul_inv_cancel_right, mul_inv_cancel]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, D.B₁card, D.Bcard] at h1
  rw [h1]
  norm_num

theorem beta_conj_mul {g x y : G} (hgb : g * b * g⁻¹ = b)
    (hg : ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      g * x * g⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    (hx : x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    (hy : y ∈ Ahat (BO b₁ b₂ b₃) b) :
    beta b (g * x * g⁻¹ * y) = g * beta b x * g⁻¹ * beta b y := by
  rw [beta_mul D.B₁ab (D.A0_le hS (hg x hx)) hy, beta_conj hgb]

theorem comm_cube_A0 {t₁ t₂ t₃ : G}
    (ht : ∀ t ∈ ({t₁, t₂, t₃} : Set G), t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ∧
      t * b * t⁻¹ = b ∧
      ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        t * x * t⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
    (ht₁ : t₁ * b₁ * t₁⁻¹ = b₁⁻¹ ∧ t₁ * b₂ * t₁⁻¹ = b₂ ∧ t₁ * b₃ * t₁⁻¹ = b₃)
    (ht₂ : t₂ * b₁ * t₂⁻¹ = b₁ ∧ t₂ * b₂ * t₂⁻¹ = b₂⁻¹ ∧ t₂ * b₃ * t₂⁻¹ = b₃)
    (ht₃ : t₃ * b₁ * t₃⁻¹ = b₁ ∧ t₃ * b₂ * t₃⁻¹ = b₂ ∧ t₃ * b₃ * t₃⁻¹ = b₃⁻¹) :
    (∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
      ∀ y ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        x * y * x⁻¹ * y⁻¹ ∈ BO b₁ b₂ b₃) ∧
      ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        x ^ 3 ∈ BO b₁ b₂ b₃ := by
  set A0 := (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype with hA0
  obtain ⟨a₁, ha₁, hβ₁⟩ := D.exists_beta_eq hS D.mem₁
  obtain ⟨a₂, ha₂, hβ₂⟩ := D.exists_beta_eq hS D.mem₂
  obtain ⟨a₃, ha₃, hβ₃⟩ := D.exists_beta_eq hS D.mem₃
  have hÂ : ∀ {x}, x ∈ A0 → x ∈ Ahat (BO b₁ b₂ b₃) b := fun hx => D.A0_le hS hx
  have key : ∀ x ∈ A0, beta b x = 1 → ∃ z ∈ BB b b₁ b₂ b₃, z⁻¹ * x ∈ BO b₁ b₂ b₃ :=
    fun x hx h1 => ⟨x, D.mem_B_of_mem_A0 hS hx h1, by rw [inv_mul_cancel]; exact one_mem _⟩
  obtain ⟨hN₁, hb₁, hA₁⟩ := ht t₁ (by simp)
  obtain ⟨hN₂, hb₂, hA₂⟩ := ht t₂ (by simp)
  obtain ⟨hN₃, hb₃, hA₃⟩ := ht t₃ (by simp)
  refine CFSG.RankThree.PartTwo.Sec21.FF81.AtildeElem.mem_of_quotient (B := BB b b₁ b₂ b₃)
    (a := ![a₁, a₂, a₃]) (t := ![t₁, t₂, t₃]) hS ?_ (fun x hx y hy => ?_) (D.B₁_le_B.trans hS)
    (fun z hz x hx => ?_) (fun z hz => ?_) (fun x hx y hy => ?_) ?_ (fun x hx => ?_) ?_ ?_ ?_ ?_ ?_
  · intro i; fin_cases i
    exacts [ha₁, ha₂, ha₃]
  · rw [(hÂ hx).1 y hy]; exact hy
  · have h := D.comm_mem (hÂ hx) hz
    have e : z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem h
  · rw [D.B3 z hz]; exact one_mem _
  · refine key _ (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
    rw [beta_mul D.B₁ab (mul_mem (mul_mem (hÂ hx) (hÂ hy)) (inv_mem (hÂ hx))) (inv_mem (hÂ hy)),
      beta_mul D.B₁ab (mul_mem (hÂ hx) (hÂ hy)) (inv_mem (hÂ hx)),
      beta_mul D.B₁ab (hÂ hx) (hÂ hy), D.beta_inv (hÂ hx), D.beta_inv (hÂ hy),
      D.B₁ab _ (beta_mem (hÂ hx)) _ (beta_mem (hÂ hy))]
    group
  · intro i
    fin_cases i
    · refine key _ (pow_mem ha₁ 3) ?_
      show beta b (a₁ ^ 3) = 1
      rw [D.beta_pow (hÂ ha₁), hβ₁, D.B₁3 _ D.mem₁]
    · refine key _ (pow_mem ha₂ 3) ?_
      show beta b (a₂ ^ 3) = 1
      rw [D.beta_pow (hÂ ha₂), hβ₂, D.B₁3 _ D.mem₂]
    · refine key _ (pow_mem ha₃ 3) ?_
      show beta b (a₃ ^ 3) = 1
      rw [D.beta_pow (hÂ ha₃), hβ₃, D.B₁3 _ D.mem₃]
  ·
    obtain ⟨v, hv⟩ := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_coord
      (D.B₁ab _ D.mem₁ _ D.mem₂) (D.B₁ab _ D.mem₁ _ D.mem₃) (D.B₁ab _ D.mem₂ _ D.mem₃)
      (D.B₁3 _ D.mem₁) (D.B₁3 _ D.mem₂) (D.B₁3 _ D.mem₃) (beta_mem (hÂ hx))
    set P := a₁ ^ (v.1 : ℕ) * a₂ ^ (v.2.1 : ℕ) * a₃ ^ (v.2.2 : ℕ) with hP
    have hPA : P ∈ A0 := mul_mem (mul_mem (pow_mem ha₁ _) (pow_mem ha₂ _)) (pow_mem ha₃ _)
    have hβP : beta b P = beta b x := by
      rw [hP, beta_mul D.B₁ab (mul_mem (pow_mem (hÂ ha₁) _) (pow_mem (hÂ ha₂) _))
        (pow_mem (hÂ ha₃) _), beta_mul D.B₁ab (pow_mem (hÂ ha₁) _) (pow_mem (hÂ ha₂) _),
        D.beta_pow (hÂ ha₁), D.beta_pow (hÂ ha₂), D.beta_pow (hÂ ha₃), hβ₁, hβ₂, hβ₃, ← hv]
      rfl
    have hz : P⁻¹ * x ∈ BB b b₁ b₂ b₃ := by
      refine D.mem_B_of_mem_A0 hS (mul_mem (inv_mem hPA) hx) ?_
      rw [beta_mul D.B₁ab (inv_mem (hÂ hPA)) (hÂ hx), D.beta_inv (hÂ hPA), hβP, inv_mul_cancel]
    refine ⟨v.1, v.2.1, v.2.2, P⁻¹ * x, hz, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← hP]
    rw [show (P * (P⁻¹ * x))⁻¹ * x = 1 by group]
    exact one_mem _
  · intro i x hx; fin_cases i
    · exact hA₁ x hx
    · exact hA₂ x hx
    · exact hA₃ x hx
  · intro i y hy; fin_cases i
    · exact D.B₁N _ hN₁ y hy
    · exact D.B₁N _ hN₂ y hy
    · exact D.B₁N _ hN₃ y hy
  ·
    have hfix : ∀ t : G, t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
        t * b * t⁻¹ = b → ∀ z ∈ BB b b₁ b₂ b₃, (t * z * t⁻¹)⁻¹ * z ∈ BO b₁ b₂ b₃ := by
      intro t htN htb z hz
      obtain ⟨n, -, y, hy, rfl⟩ := D.exists_of_mem_B hz
      have hty : t * y * t⁻¹ ∈ BO b₁ b₂ b₃ := D.B₁N t htN y hy
      have e : (t * (b ^ n * y) * t⁻¹)⁻¹ * (b ^ n * y) = (t * y * t⁻¹)⁻¹ * y := by
        rw [show t * (b ^ n * y) * t⁻¹ = (t * b * t⁻¹) ^ n * (t * y * t⁻¹) by
          rw [conj_pow]; group, htb]
        group
      rw [e]
      exact mul_mem (inv_mem hty) hy
    intro i; fin_cases i
    · exact hfix t₁ hN₁ hb₁
    · exact hfix t₂ hN₂ hb₂
    · exact hfix t₃ hN₃ hb₃
  · intro i; fin_cases i
    · refine key _ (mul_mem (hA₁ _ ha₁) ha₁) ?_
      show beta b (t₁ * a₁ * t₁⁻¹ * a₁) = 1
      rw [D.beta_conj_mul hS hb₁ hA₁ ha₁ (hÂ ha₁), hβ₁, ht₁.1, inv_mul_cancel]
    · refine key _ (mul_mem (hA₂ _ ha₂) ha₂) ?_
      show beta b (t₂ * a₂ * t₂⁻¹ * a₂) = 1
      rw [D.beta_conj_mul hS hb₂ hA₂ ha₂ (hÂ ha₂), hβ₂, ht₂.2.1, inv_mul_cancel]
    · refine key _ (mul_mem (hA₃ _ ha₃) ha₃) ?_
      show beta b (t₃ * a₃ * t₃⁻¹ * a₃) = 1
      rw [D.beta_conj_mul hS hb₃ hA₃ ha₃ (hÂ ha₃), hβ₃, ht₃.2.2, inv_mul_cancel]
  · intro i j hij
    have hcase : ∀ (t a y : G), t * b * t⁻¹ = b → (∀ x ∈ A0, t * x * t⁻¹ ∈ A0) → a ∈ A0 →
        beta b a = y → t * y * t⁻¹ = y →
        ∃ z ∈ BB b b₁ b₂ b₃, z⁻¹ * (t * a * t⁻¹ * a⁻¹) ∈ BO b₁ b₂ b₃ := by
      intro t a y htb htA ha hay hty
      refine key _ (mul_mem (htA _ ha) (inv_mem ha)) ?_
      rw [D.beta_conj_mul hS htb htA ha (inv_mem (hÂ ha)), D.beta_inv (hÂ ha), hay, hty,
        mul_inv_cancel]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hcase t₁ a₂ b₂ hb₁ hA₁ ha₂ hβ₂ ht₁.2.1
    · exact hcase t₁ a₃ b₃ hb₁ hA₁ ha₃ hβ₃ ht₁.2.2
    · exact hcase t₂ a₁ b₁ hb₂ hA₂ ha₁ hβ₁ ht₂.1
    · exact hcase t₂ a₃ b₃ hb₂ hA₂ ha₃ hβ₃ ht₂.2.2
    · exact hcase t₃ a₁ b₁ hb₃ hA₃ ha₁ hβ₁ ht₃.1
    · exact hcase t₃ a₂ b₂ hb₃ hA₃ ha₂ hβ₂ ht₃.2.1

end Sylow3

end Data

structure Mono (b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G) : Prop where
  mem : ∀ g ∈ ({τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G),
    g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ∧ g * b * g⁻¹ = b
  inv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹
  s₁ : ι₁ * b₁ * ι₁⁻¹ = b₁⁻¹ ∧ ι₁ * b₂ * ι₁⁻¹ = b₂ ∧ ι₁ * b₃ * ι₁⁻¹ = b₃
  s₂ : ι₂ * b₁ * ι₂⁻¹ = b₁ ∧ ι₂ * b₂ * ι₂⁻¹ = b₂⁻¹ ∧ ι₂ * b₃ * ι₂⁻¹ = b₃
  s₃ : ι₃ * b₁ * ι₃⁻¹ = b₁ ∧ ι₃ * b₂ * ι₃⁻¹ = b₂ ∧ ι₃ * b₃ * ι₃⁻¹ = b₃⁻¹
  p₁₂ : σ₁₂ * b₁ * σ₁₂⁻¹ = b₂ ∧ σ₁₂ * b₂ * σ₁₂⁻¹ = b₁ ∧ σ₁₂ * b₃ * σ₁₂⁻¹ = b₃
  p₂₃ : σ₂₃ * b₁ * σ₂₃⁻¹ = b₁ ∧ σ₂₃ * b₂ * σ₂₃⁻¹ = b₃ ∧ σ₂₃ * b₃ * σ₂₃⁻¹ = b₂
  cyc : γ * b₁ * γ⁻¹ = b₂ ∧ γ * b₂ * γ⁻¹ = b₃ ∧ γ * b₃ * γ⁻¹ = b₁

theorem inv_conj_of_conj {g x y : G} (h : g * x * g⁻¹ = y) : g⁻¹ * y * g = x := by
  rw [← h]; group

theorem Mono.of_gens {b b₁ b₂ b₃ τ t₁ s c : G}
    (hN : ∀ g ∈ ({τ, t₁, s, c} : Set G),
      g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ∧ g * b * g⁻¹ = b)
    (hτ : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (ht₁ : t₁ * b₁ * t₁⁻¹ = b₁⁻¹ ∧ t₁ * b₂ * t₁⁻¹ = b₂ ∧ t₁ * b₃ * t₁⁻¹ = b₃)
    (hs : s * b₁ * s⁻¹ = b₂ ∧ s * b₂ * s⁻¹ = b₁ ∧ s * b₃ * s⁻¹ = b₃)
    (hc : c * b₁ * c⁻¹ = b₂ ∧ c * b₂ * c⁻¹ = b₃ ∧ c * b₃ * c⁻¹ = b₁) :
    Mono b b₁ b₂ b₃ τ t₁ (s * t₁ * s⁻¹) (c * (s * t₁ * s⁻¹) * c⁻¹) s (c * s * c⁻¹) c := by
  obtain ⟨hτN, hτb⟩ := hN τ (by simp)
  obtain ⟨ht₁N, ht₁b⟩ := hN t₁ (by simp)
  obtain ⟨hsN, hsb⟩ := hN s (by simp)
  obtain ⟨hcN, hcb⟩ := hN c (by simp)
  have e : ∀ g h x : G, (g * h * g⁻¹) * x * (g * h * g⁻¹)⁻¹ = g * (h * (g⁻¹ * x * g) * h⁻¹) * g⁻¹ :=
    fun g h x => by group
  have inv' : ∀ g x : G, g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := fun g x => by group
  have si1 := inv_conj_of_conj hs.2.1
  have si2 := inv_conj_of_conj hs.1
  have si3 := inv_conj_of_conj hs.2.2
  have sib := inv_conj_of_conj hsb
  have ci1 := inv_conj_of_conj hc.2.2
  have ci2 := inv_conj_of_conj hc.1
  have ci3 := inv_conj_of_conj hc.2.1
  have cib := inv_conj_of_conj hcb
  have h2b : (s * t₁ * s⁻¹) * b * (s * t₁ * s⁻¹)⁻¹ = b := by rw [e, sib, ht₁b, hsb]
  have h21 : (s * t₁ * s⁻¹) * b₁ * (s * t₁ * s⁻¹)⁻¹ = b₁ := by rw [e, si1, ht₁.2.1, hs.2.1]
  have h22 : (s * t₁ * s⁻¹) * b₂ * (s * t₁ * s⁻¹)⁻¹ = b₂⁻¹ := by
    rw [e, si2, ht₁.1, inv', hs.1]
  have h23 : (s * t₁ * s⁻¹) * b₃ * (s * t₁ * s⁻¹)⁻¹ = b₃ := by rw [e, si3, ht₁.2.2, hs.2.2]
  refine
    { mem := ?_
      inv := hτ
      s₁ := ht₁
      s₂ := ⟨h21, h22, h23⟩
      s₃ := ⟨by rw [e, ci1, h23, hc.2.2], by rw [e, ci2, h21, hc.1],
        by rw [e, ci3, h22, inv', hc.2.1]⟩
      p₁₂ := hs
      p₂₃ := ⟨by rw [e, ci1, hs.2.2, hc.2.2], by rw [e, ci2, hs.1, hc.2.1],
        by rw [e, ci3, hs.2.1, hc.1]⟩
      cyc := hc }
  rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨hτN, hτb⟩
  · exact ⟨ht₁N, ht₁b⟩
  · exact ⟨mul_mem (mul_mem hsN ht₁N) (inv_mem hsN), h2b⟩
  · exact ⟨mul_mem (mul_mem hcN (mul_mem (mul_mem hsN ht₁N) (inv_mem hsN))) (inv_mem hcN),
      by rw [e, cib, h2b, hcb]⟩
  · exact ⟨hsN, hsb⟩
  · exact ⟨mul_mem (mul_mem hcN hsN) (inv_mem hcN), by rw [e, cib, hsb, hcb]⟩
  · exact ⟨hcN, hcb⟩

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem b₁_ne_one : b₁ ≠ 1 := by
  intro e
  have hinj := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord_injective
    (D.B₁ab _ D.mem₁ _ D.mem₂) (D.B₁ab _ D.mem₁ _ D.mem₃) (D.B₁ab _ D.mem₂ _ D.mem₃)
    (D.B₁3 _ D.mem₁) (D.B₁3 _ D.mem₂) (D.B₁3 _ D.mem₃) D.B₁card
  have e' : CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (1, 0, 0) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 0, 0) := by
    simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e]
  exact absurd (hinj e') (by decide)

theorem eq_one_of_eq_inv {y : G} (hy3 : y ^ 3 = 1) (e : y⁻¹ = y) : y = 1 := by
  have hyy : y * y = 1 := by
    calc y * y = y⁻¹ * y := by rw [e]
      _ = 1 := inv_mul_cancel y
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [hy3, hyy, inv_one, one_mul]

theorem mem_cen_of_gens {δ : G} (h : ∀ z ∈ ({b, b₁, b₂, b₃} : Set G), δ * z * δ⁻¹ = z) :
    δ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
  have h' := conj_eq_of_closure h
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have := h' z hz
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

end Data0

namespace Data

variable {b b₁ b₂ b₃ : G} (D : Data b b₁ b₂ b₃)
include D

section Sylow4

variable {S : Sylow 3 ↥(Ahat (BO b₁ b₂ b₃) b)}
  (hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype)
include hS

theorem exists_translate' {g : G}
    (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∃ g' ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (∀ z ∈ BB b b₁ b₂ b₃, g' * z * g'⁻¹ = g * z * g⁻¹) ∧
      ∀ x ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype,
        g' * x * g'⁻¹ ∈ (S : Subgroup ↥(Ahat (BO b₁ b₂ b₃) b)).map (Ahat (BO b₁ b₂ b₃) b).subtype := by
  obtain ⟨k, hk, hkA⟩ := D.exists_translate_cen hS hg
  exact ⟨k⁻¹ * g, mul_mem (inv_mem (D.cen_le_N hk)) hg,
    fun z hz => D.translate_conj hk (D.conj_mem_B hg hz), hkA⟩

end Sylow4

end Data

theorem isPGroup_zpowers_of_pow {p k : ℕ} {x : G} (h : x ^ (p ^ k) = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  intro g
  refine ⟨k, Subtype.ext ?_⟩
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm z, zpow_mul,
    zpow_natCast, h, one_zpow]

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem exists_K : ∃ K : Subgroup G,
    (∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K) ∧
    K ≤ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ∧
    Nat.Coprime (Nat.card K) 3 ∧
    Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ≤ BB b b₁ b₂ b₃ ⊔ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) with hHdef
  have hBH : BB b b₁ b₂ b₃ ≤ H := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => D.Bab w hw z hz
  have hBp : IsPGroup 3 ↥((BB b b₁ b₂ b₃).subgroupOf H) := D.isPGroup_B.comap_subtype
  obtain ⟨P, -⟩ := hBp.exists_le_sylow
  have hPB : ∀ x : ↥H, x ∈ (P : Subgroup ↥H) → (x : G) ∈ BB b b₁ b₂ b₃ := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hk' : (x : G) ^ (3 ^ k) = 1 := by
      have := congrArg (fun y : ↥(P : Subgroup ↥H) => ((y : ↥H) : G)) hk
      simpa using this
    exact D.CB x x.2 (isPGroup_zpowers_of_pow hk')
  have hPc : Subgroup.normalizer ((P : Subgroup ↥H) : Set ↥H) ≤
      Subgroup.centralizer ((P : Subgroup ↥H) : Set ↥H) := by
    intro h _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h.2 _ (hPB x hx))
  set K' := (MonoidHom.transferSylow P hPc).ker with hK'def
  have hcomp : Subgroup.IsComplement' K' (P : Subgroup ↥H) :=
    MonoidHom.ker_transferSylow_isComplement' P hPc
  have hnd : ¬ 3 ∣ Nat.card K' := MonoidHom.not_dvd_card_ker_transferSylow P hPc
  have hcardK : Nat.card (K'.map H.subtype) = Nat.card K' :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hK3 : Nat.Coprime (Nat.card (K'.map H.subtype)) 3 := by
    rw [hcardK]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd).symm
  have hdec : ∀ c : ↥H, ∃ k ∈ K', ∃ q ∈ (P : Subgroup ↥H), k * q = c := by
    intro c
    obtain ⟨⟨k, q⟩, hkq, -⟩ := hcomp.existsUnique c
    exact ⟨k, k.2, q, q.2, hkq⟩
  have h3' : ∀ c : ↥H, Nat.Coprime (orderOf c) 3 → c ∈ K' := by
    intro c hc
    obtain ⟨k, hk, q, hq, rfl⟩ := hdec c
    have hcomm : Commute k q :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp k.2 _ (hPB q hq)).symm
    set m := orderOf (k * q) with hm
    have hm1 : (k * q) ^ m = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at hm1
    have hqm : q ^ m ∈ K' := by
      have : q ^ m = (k ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hm1
      rw [this]
      exact inv_mem (pow_mem hk m)
    have hqm1 : q ^ m = 1 := by
      have hd := hcomp.disjoint
      rw [Subgroup.disjoint_def] at hd
      exact hd hqm (pow_mem hq m)
    obtain ⟨e, he⟩ := P.isPGroup' ⟨q, hq⟩
    have hqe : q ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hq1 : q = 1 := by
      have h1 : orderOf q ∣ Nat.gcd m (3 ^ e) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hqm1) (orderOf_dvd_of_pow_eq_one hqe)
      rw [(Nat.Coprime.pow_right e hc).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact h1
    rw [hq1, mul_one]
    exact hk
  refine ⟨K'.map H.subtype, ?_, ?_, hK3, ?_⟩
  ·
    rintro n hn _ ⟨k, hk, rfl⟩
    have hnH : n * (k : G) * n⁻¹ ∈ H := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : n⁻¹ * z * n⁻¹⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B (inv_mem hn) hz
      have hc := Subgroup.mem_centralizer_iff.mp k.2 _ hz'
      calc z * (n * k * n⁻¹) = n * ((n⁻¹ * z * n⁻¹⁻¹) * k) * n⁻¹ := by group
        _ = n * (k * (n⁻¹ * z * n⁻¹⁻¹)) * n⁻¹ := by rw [hc]
        _ = n * k * n⁻¹ * z := by group
    have hord : orderOf (⟨n * k * n⁻¹, hnH⟩ : ↥H) = orderOf k := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe k]
      exact (SemiconjBy.orderOf_eq n (by
        show n * (k : G) = n * k * n⁻¹ * n
        group)).symm
    have hcop : Nat.Coprime (orderOf k) 3 := by
      have hdvd : orderOf k ∣ Nat.card K' := by
        have := Subgroup.orderOf_dvd_natCard K' hk
        exact this
      exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd
        Nat.prime_three).mpr hnd).symm
    exact ⟨_, h3' _ (hord ▸ hcop), rfl⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · intro c hc
    obtain ⟨k, hk, q, hq, hkq⟩ := hdec ⟨c, hc⟩
    have e : c = (q : G) * (k : G) := by
      have h1 : (k : G) * q = c := congrArg Subtype.val hkq
      have hcomm : (k : G) * q = q * k := (Subgroup.mem_centralizer_iff.mp k.2 _ (hPB q hq)).symm
      rw [← h1, hcomm]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (hPB q hq)) (Subgroup.mem_sup_right ⟨k, hk, rfl⟩)

end Data0

structure Compl (b b₁ b₂ b₃ : G) (K NL : Subgroup G) : Prop where
  KN : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K
  KC : K ≤ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)
  K3 : Nat.Coprime (Nat.card K) 3
  CK : Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ≤ BB b b₁ b₂ b₃ ⊔ K
  NLN : NL ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)
  NLb : ∀ l ∈ NL, l * b * l⁻¹ = b
  NLC : NL ⊓ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ≤ BO b₁ b₂ b₃
  gen : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
    ∃ l ∈ NL, n * l⁻¹ ∈ Ahat (BO b₁ b₂ b₃) b

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem gens_ne : b₂ ≠ b₁ ∧ b₂ ≠ b₁⁻¹ ∧ b₃ ≠ b₁ ∧ b₃ ≠ b₁⁻¹ ∧ b₃ ≠ b₂ ∧ b₃ ≠ b₂⁻¹ := by
  have hinj := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord_injective
    (D.B₁ab _ D.mem₁ _ D.mem₂) (D.B₁ab _ D.mem₁ _ D.mem₃) (D.B₁ab _ D.mem₂ _ D.mem₃)
    (D.B₁3 _ D.mem₁) (D.B₁3 _ D.mem₂) (D.B₁3 _ D.mem₃) D.B₁card
  have hsq : ∀ x : G, x ^ 3 = 1 → x⁻¹ = x ^ 2 := fun x hx => by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]
  have h1 := hsq b₁ (D.B₁3 _ D.mem₁)
  have h2 := hsq b₂ (D.B₁3 _ D.mem₂)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 1, 0) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (1, 0, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e])) (by decide)
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 1, 0) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (2, 0, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e, h1])) (by decide)
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 0, 1) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (1, 0, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e])) (by decide)
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 0, 1) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (2, 0, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e, h1])) (by decide)
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 0, 1) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 1, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e])) (by decide)
  · exact absurd (hinj (show CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 0, 1) =
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord b₁ b₂ b₃ (0, 2, 0) by
        simp [CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.coord, e, h2])) (by decide)

end Data0

namespace Data

variable {b b₁ b₂ b₃ : G} (D : Data b b₁ b₂ b₃)
include D

theorem exists_t {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      n * b * n⁻¹ = b⁻¹ → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hgb : g * b * g⁻¹ * b ∈ BO b₁ b₂ b₃) :
    ∃ t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      t * b * t⁻¹ = b⁻¹ ∧ ∀ y ∈ BO b₁ b₂ b₃, t * y * t⁻¹ = y := by
  set N := Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) with hNdef
  obtain ⟨-, hι₁N, hι₂N, hι₃N, hσ₁₂N, hσ₂₃N, hγN⟩ :
      τ ∈ N ∧ ι₁ ∈ N ∧ ι₂ ∈ N ∧ ι₃ ∈ N ∧ σ₁₂ ∈ N ∧ σ₂₃ ∈ N ∧ γ ∈ N :=
    ⟨(M.mem τ (by simp)).1, (M.mem ι₁ (by simp)).1, (M.mem ι₂ (by simp)).1,
      (M.mem ι₃ (by simp)).1, (M.mem σ₁₂ (by simp)).1, (M.mem σ₂₃ (by simp)).1,
      (M.mem γ (by simp)).1⟩
  obtain ⟨-, hι₁b, hι₂b, hι₃b, hσ₁₂b, hσ₂₃b, hγb⟩ :
      τ * b * τ⁻¹ = b ∧ ι₁ * b * ι₁⁻¹ = b ∧ ι₂ * b * ι₂⁻¹ = b ∧ ι₃ * b * ι₃⁻¹ = b ∧
        σ₁₂ * b * σ₁₂⁻¹ = b ∧ σ₂₃ * b * σ₂₃⁻¹ = b ∧ γ * b * γ⁻¹ = b :=
    ⟨(M.mem τ (by simp)).2, (M.mem ι₁ (by simp)).2, (M.mem ι₂ (by simp)).2,
      (M.mem ι₃ (by simp)).2, (M.mem σ₁₂ (by simp)).2, (M.mem σ₂₃ (by simp)).2,
      (M.mem γ (by simp)).2⟩
  have hcm : ∀ h k x : G, (h * k) * x * (h * k)⁻¹ = h * (k * x * k⁻¹) * h⁻¹ := fun _ _ _ => by
    group
  have hiv : ∀ h x : G, h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := fun _ _ => by group
  obtain ⟨n21, n21', n31, n31', n32, n32'⟩ := D.gens_ne
  obtain ⟨a, ha1, ha2⟩ := D.surj _ hgb
  have haA : a ∈ Ahat (BO b₁ b₂ b₃) b :=
    ⟨ha1, by rw [ha2, mul_inv_cancel_right]; exact hgb⟩
  have hg₁N : a * g ∈ N := mul_mem (D.Ahat_le_N haA) hg
  have hg₁b : (a * g) * b * (a * g)⁻¹ = b⁻¹ := by
    set y₀ := g * b * g⁻¹ * b with hy₀
    have hgb' : g * b * g⁻¹ = y₀ * b⁻¹ := by rw [hy₀, mul_inv_cancel_right]
    have hy₀b : y₀ * b = b * y₀ := (D.bB₁ y₀ hgb).symm
    rw [hcm, hgb', show a * (y₀ * b⁻¹) * a⁻¹ = (a * y₀ * a⁻¹) * (a * b * a⁻¹)⁻¹ by group,
      ha1 y₀ hgb, ha2, hy₀b, mul_inv_rev]
    group
  have step1 : ∀ y ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G),
      ∃ h ∈ N, h * b * h⁻¹ = b ∧ h * y * h⁻¹ = b₁ := by
    rintro y (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, by simp, by simp⟩
    · exact ⟨ι₁, hι₁N, hι₁b, by rw [hiv, M.s₁.1, inv_inv]⟩
    · exact ⟨σ₁₂, hσ₁₂N, hσ₁₂b, M.p₁₂.2.1⟩
    · exact ⟨σ₁₂ * ι₂, mul_mem hσ₁₂N hι₂N, by rw [hcm, hι₂b, hσ₁₂b],
        by rw [hcm, hiv, M.s₂.2.1, inv_inv, M.p₁₂.2.1]⟩
    · exact ⟨γ, hγN, hγb, M.cyc.2.2⟩
    · exact ⟨γ * ι₃, mul_mem hγN hι₃N, by rw [hcm, hι₃b, hγb],
        by rw [hcm, hiv, M.s₃.2.2, inv_inv, M.cyc.2.2]⟩
  obtain ⟨h₁, hh₁N, hh₁b, hh₁⟩ := step1 _ (hmono _ hg₁N hg₁b b₁ (by simp))
  have hg₂N : h₁ * (a * g) ∈ N := mul_mem hh₁N hg₁N
  have hg₂b : (h₁ * (a * g)) * b * (h₁ * (a * g))⁻¹ = b⁻¹ := by rw [hcm, hg₁b, hiv, hh₁b]
  have hg₂1 : (h₁ * (a * g)) * b₁ * (h₁ * (a * g))⁻¹ = b₁ := by rw [hcm, hh₁]
  set g₂ := h₁ * (a * g) with hg₂def
  have hne : ∀ {u v : G}, u ≠ v → g₂ * u * g₂⁻¹ ≠ g₂ * v * g₂⁻¹ := fun huv e =>
    huv (mul_left_cancel (mul_right_cancel e))
  have hy2 := hmono _ hg₂N hg₂b b₂ (by simp)
  obtain ⟨h₂, hh₂N, hh₂b, hh₂1, hh₂⟩ : ∃ h ∈ N, h * b * h⁻¹ = b ∧ h * b₁ * h⁻¹ = b₁ ∧
      h * (g₂ * b₂ * g₂⁻¹) * h⁻¹ = b₂ := by
    rcases hy2 with e | e | e | e | e | e
    · exact absurd (e.trans hg₂1.symm) (hne n21)
    · exact absurd (e.trans (by rw [hiv, hg₂1])) (hne n21')
    · exact ⟨1, one_mem _, by simp, by simp, by rw [e]; simp⟩
    · exact ⟨ι₂, hι₂N, hι₂b, M.s₂.1, by rw [e, hiv, M.s₂.2.1, inv_inv]⟩
    · exact ⟨σ₂₃, hσ₂₃N, hσ₂₃b, M.p₂₃.1, by rw [e, M.p₂₃.2.2]⟩
    · exact ⟨σ₂₃ * ι₃, mul_mem hσ₂₃N hι₃N, by rw [hcm, hι₃b, hσ₂₃b],
        by rw [hcm, M.s₃.1, M.p₂₃.1], by rw [e, hcm, hiv, M.s₃.2.2, inv_inv, M.p₂₃.2.2]⟩
  have hg₃N : h₂ * g₂ ∈ N := mul_mem hh₂N hg₂N
  have hg₃b : (h₂ * g₂) * b * (h₂ * g₂)⁻¹ = b⁻¹ := by rw [hcm, hg₂b, hiv, hh₂b]
  have hg₃1 : (h₂ * g₂) * b₁ * (h₂ * g₂)⁻¹ = b₁ := by rw [hcm, hg₂1, hh₂1]
  have hg₃2 : (h₂ * g₂) * b₂ * (h₂ * g₂)⁻¹ = b₂ := by rw [hcm, hh₂]
  set g₃ := h₂ * g₂ with hg₃def
  have hne3 : ∀ {u v : G}, u ≠ v → g₃ * u * g₃⁻¹ ≠ g₃ * v * g₃⁻¹ := fun huv e =>
    huv (mul_left_cancel (mul_right_cancel e))
  have hy3 := hmono _ hg₃N hg₃b b₃ (by simp)
  obtain ⟨h₃, hh₃N, hh₃b, hh₃1, hh₃2, hh₃⟩ : ∃ h ∈ N, h * b * h⁻¹ = b ∧ h * b₁ * h⁻¹ = b₁ ∧
      h * b₂ * h⁻¹ = b₂ ∧ h * (g₃ * b₃ * g₃⁻¹) * h⁻¹ = b₃ := by
    rcases hy3 with e | e | e | e | e | e
    · exact absurd (e.trans hg₃1.symm) (hne3 n31)
    · exact absurd (e.trans (by rw [hiv, hg₃1])) (hne3 n31')
    · exact absurd (e.trans hg₃2.symm) (hne3 n32)
    · exact absurd (e.trans (by rw [hiv, hg₃2])) (hne3 n32')
    · exact ⟨1, one_mem _, by simp, by simp, by simp, by rw [e]; simp⟩
    · exact ⟨ι₃, hι₃N, hι₃b, M.s₃.1, M.s₃.2.1, by rw [e, hiv, M.s₃.2.2, inv_inv]⟩
  refine ⟨h₃ * g₃, mul_mem hh₃N hg₃N, by rw [hcm, hg₃b, hiv, hh₃b], ?_⟩
  refine conj_eq_of_closure ?_
  rintro y (rfl | rfl | rfl)
  · rw [hcm, hg₃1, hh₃1]
  · rw [hcm, hg₃2, hh₃2]
  · rw [hcm, hh₃]

theorem hbt_of {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      n * b * n⁻¹ = b⁻¹ → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hcompl : (∀ g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      g * b * g⁻¹ * b ∉ BO b₁ b₂ b₃) → ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL) :
    ∀ hb : b ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) →
      (∃ t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
        t * b * t⁻¹ = b⁻¹ ∧ ∀ y ∈ BO b₁ b₂ b₃, t * y * t⁻¹ = y) ∨
      ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL := by
  intro _ _
  by_cases h : ∃ g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      g * b * g⁻¹ * b ∈ BO b₁ b₂ b₃
  · obtain ⟨g, hg, hgb⟩ := h
    exact Or.inl (D.exists_t M hmono hg hgb)
  · exact Or.inr (hcompl fun g hg hgb => h ⟨g, hg, hgb⟩)

end Data

theorem pow_conj_mem {A : Subgroup G} {g : G} (hg : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (n : ℕ) :
    ∀ x ∈ A, g ^ n * x * (g ^ n)⁻¹ ∈ A := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [show g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ by group]
    exact hg _ (ih x hx)

theorem four_le_localRank_of_lift {b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (D : Data b b₁ b₂ b₃) (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirr : ∀ H : Subgroup G, H ≤ BO b₁ b₂ b₃ → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = BO b₁ b₂ b₃)
    (hN3 : ∀ R : Subgroup G, R ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
      IsPGroup 3 R → Nat.card R ≤ 3 ^ 8)
    (hbt : ∀ hb : b ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) →
      (∃ t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
        t * b * t⁻¹ = b⁻¹ ∧ ∀ y ∈ BO b₁ b₂ b₃, t * y * t⁻¹ = y) ∨
      ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL)
    (hbG : b ∈ commutator G) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) with hNdef
  set B₁ := BO b₁ b₂ b₃ with hB₁def
  set Â := Ahat (BO b₁ b₂ b₃) b with hÂdef
  have hBp : IsPGroup 3 ↥((BB b b₁ b₂ b₃).subgroupOf Â) := D.isPGroup_B.comap_subtype
  obtain ⟨S, hSle⟩ := hBp.exists_le_sylow
  have hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥Â).map Â.subtype := fun z hz =>
    ⟨⟨z, D.B_le_Ahat hz⟩, hSle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  set A0 := (S : Subgroup ↥Â).map Â.subtype with hA0def
  have hÂ : ∀ {x}, x ∈ A0 → x ∈ Â := fun hx => D.A0_le hS hx
  obtain ⟨hτN, hτb⟩ := M.mem τ (by simp)
  obtain ⟨hι₁N, hι₁b⟩ := M.mem ι₁ (by simp)
  obtain ⟨hι₂N, hι₂b⟩ := M.mem ι₂ (by simp)
  obtain ⟨hι₃N, hι₃b⟩ := M.mem ι₃ (by simp)
  obtain ⟨hσ₁₂N, hσ₁₂b⟩ := M.mem σ₁₂ (by simp)
  obtain ⟨hσ₂₃N, hσ₂₃b⟩ := M.mem σ₂₃ (by simp)
  obtain ⟨hγN, hγb⟩ := M.mem γ (by simp)
  obtain ⟨τ', hτ'N, hτ'B, hτ'A⟩ := D.exists_translate' hS hτN
  obtain ⟨ι₁', hι₁'N, hι₁'B, hι₁'A⟩ := D.exists_translate' hS hι₁N
  obtain ⟨ι₂', hι₂'N, hι₂'B, hι₂'A⟩ := D.exists_translate' hS hι₂N
  obtain ⟨ι₃', hι₃'N, hι₃'B, hι₃'A⟩ := D.exists_translate' hS hι₃N
  obtain ⟨σ₁₂', hσ₁₂'N, hσ₁₂'B, hσ₁₂'A⟩ := D.exists_translate' hS hσ₁₂N
  obtain ⟨σ₂₃', hσ₂₃'N, hσ₂₃'B, hσ₂₃'A⟩ := D.exists_translate' hS hσ₂₃N
  obtain ⟨γ', hγ'N, hγ'B, hγ'A⟩ := D.exists_translate' hS hγN
  have hb := D.b_mem_B
  have h₁ : b₁ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₁
  have h₂ : b₂ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₂
  have h₃ : b₃ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₃
  obtain ⟨hAab, hA3⟩ := D.comm_cube_A0 hS (t₁ := ι₁') (t₂ := ι₂') (t₃ := ι₃')
    (by
      rintro t (rfl | rfl | rfl)
      · exact ⟨hι₁'N, by rw [hι₁'B b hb, hι₁b], hι₁'A⟩
      · exact ⟨hι₂'N, by rw [hι₂'B b hb, hι₂b], hι₂'A⟩
      · exact ⟨hι₃'N, by rw [hι₃'B b hb, hι₃b], hι₃'A⟩)
    ⟨by rw [hι₁'B _ h₁, M.s₁.1], by rw [hι₁'B _ h₂, M.s₁.2.1], by rw [hι₁'B _ h₃, M.s₁.2.2]⟩
    ⟨by rw [hι₂'B _ h₁, M.s₂.1], by rw [hι₂'B _ h₂, M.s₂.2.1], by rw [hι₂'B _ h₃, M.s₂.2.2]⟩
    ⟨by rw [hι₃'B _ h₁, M.s₃.1], by rw [hι₃'B _ h₂, M.s₃.2.1], by rw [hι₃'B _ h₃, M.s₃.2.2]⟩
  have hτinv : ∀ y ∈ B₁, τ * y * τ⁻¹ = y⁻¹ := conj_inv_of_closure D.B₁ab (by
    rintro s (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2])
  obtain ⟨m, hm, hτ₂p⟩ := exists_odd_pow_two τ'
  set τ₂ := τ' ^ m with hτ₂def
  have hτ₂N : τ₂ ∈ N := pow_mem hτ'N m
  have hτ₂A : ∀ x ∈ A0, τ₂ * x * τ₂⁻¹ ∈ A0 := pow_conj_mem hτ'A m
  have hτ₂b : τ₂ * b * τ₂⁻¹ = b := pow_conj_fix (by rw [hτ'B b hb, hτb]) m
  have hτ₂inv : ∀ y ∈ B₁, τ₂ * y * τ₂⁻¹ = y⁻¹ := fun y hy =>
    pow_conj_inv (by rw [hτ'B y (D.B₁_le_B hy), hτinv y hy]) hm
  have hτ₂sq : ∀ x ∈ A0, τ₂ * (τ₂ * x * τ₂⁻¹) * τ₂⁻¹ = x := by
    intro x hx
    have hδ : τ₂ ^ 2 ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_gens fun z hz => ?_
      have e : τ₂ ^ 2 * z * (τ₂ ^ 2)⁻¹ = τ₂ * (τ₂ * z * τ₂⁻¹) * τ₂⁻¹ := by
        rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
      rw [e]
      rcases hz with rfl | rfl | rfl | rfl
      · rw [hτ₂b, hτ₂b]
      · rw [hτ₂inv _ D.mem₁, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₁, inv_inv]
      · rw [hτ₂inv _ D.mem₂, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₂, inv_inv]
      · rw [hτ₂inv _ D.mem₃, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₃, inv_inv]
    have h2p : IsPGroup 2 (Subgroup.zpowers (τ₂ ^ 2)) :=
      hτ₂p.to_le (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers _) 2))
    have := D.cen_two hS hδ (pow_conj_mem hτ₂A 2) h2p hx
    calc τ₂ * (τ₂ * x * τ₂⁻¹) * τ₂⁻¹ = τ₂ ^ 2 * x * (τ₂ ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
      _ = x := this
  have H : CFSG.RankThree.PartTwo.Sec21.FF81.B2Construct.Hyp A0 B₁ b τ₂ :=
    { B₁A := D.B₁_le_B.trans hS
      bA := hS hb
      B₁n := fun x hx y hy => by rw [(hÂ hx).1 y hy]; exact hy
      Aab := hAab
      A3 := hA3
      B₁3 := D.B₁3
      b3 := D.b3
      bB₁ := D.b_not_mem
      τ2 := hτ₂sq
      τA := hτ₂A
      τB₁ := hτ₂inv
      τb := hτ₂b
      fix := by
        intro x hx hfx
        have h1 : beta b (τ₂ * x * τ₂⁻¹) = (beta b x)⁻¹ := by
          rw [beta_conj hτ₂b, hτ₂inv _ (beta_mem (hÂ hx))]
        have h2 : beta b (τ₂ * x * τ₂⁻¹) = beta b x := by
          have e : τ₂ * x * τ₂⁻¹ = (τ₂ * x * τ₂⁻¹ * x⁻¹) * x := by group
          rw [e, beta_mul D.B₁ab (D.B_le_Ahat (D.B₁_le_B hfx)) (hÂ hx),
            beta_one_of_mem D.bB₁ hfx, one_mul]
        have h3 : beta b x = 1 :=
          D.eq_one_of_eq_inv (D.B₁3 _ (beta_mem (hÂ hx))) (h1.symm.trans h2)
        rw [← D.B_eq_sup]
        exact D.mem_B_of_mem_A0 hS hx h3 }
  set B₂ := H.B₂ with hB₂def
  have hB₂A : B₂ ≤ A0 := H.le_A
  have hnorm : ∀ g ∈ N, (∀ x ∈ A0, g * x * g⁻¹ ∈ A0) →
      (g⁻¹ * τ₂ * g) * τ₂⁻¹ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := by
    intro g hg hgA hδ x hx
    have hgA' : ∀ x ∈ A0, g⁻¹ * x * g⁻¹⁻¹ ∈ A0 := by
      have hgn := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hgA
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgn) y).mp hy
    have hτ₂A' : ∀ x ∈ A0, τ₂⁻¹ * x * τ₂⁻¹⁻¹ ∈ A0 := by
      have hgn := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hτ₂A
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgn) y).mp hy
    refine H.conj_mem (fun y hy => hgA y hy) (fun y hy => D.B₁N g hg y hy) (fun y hy => ?_) hx
    have hδA : ∀ x ∈ A0, ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * x * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ ∈ A0 := by
      intro z hz
      have e : ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * z * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ =
          g⁻¹ * (τ₂ * (g * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * g⁻¹) * τ₂⁻¹) * g⁻¹⁻¹ := by group
      rw [e]
      exact hgA' _ (hτ₂A _ (hgA _ (hτ₂A' _ hz)))
    have e : (g⁻¹ * τ₂ * g) * y * (g⁻¹ * τ₂ * g)⁻¹ * (τ₂ * y * τ₂⁻¹)⁻¹ =
        ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * (τ₂ * y * τ₂⁻¹) * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ *
          (τ₂ * y * τ₂⁻¹)⁻¹ := by group
    rw [e]
    exact D.comm_mem_of_cen hS hAab hδ hδA (hτ₂A y hy)
  have hδfix : ∀ g ∈ N, g * b * g⁻¹ = b →
      (g⁻¹ * τ₂ * g) * τ₂⁻¹ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
    intro g hg hgb
    have hg' : g⁻¹ ∈ N := inv_mem hg
    have hgib : g⁻¹ * b * g⁻¹⁻¹ = b := by
      calc g⁻¹ * b * g⁻¹⁻¹ = g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ := by rw [hgb]
        _ = b := by group
    have hτ₂inv' : ∀ y ∈ B₁, τ₂⁻¹ * y * τ₂⁻¹⁻¹ = y⁻¹ := by
      intro y hy
      have h := hτ₂inv y⁻¹ (inv_mem hy)
      rw [inv_inv] at h
      calc τ₂⁻¹ * y * τ₂⁻¹⁻¹ = τ₂⁻¹ * (τ₂ * y⁻¹ * τ₂⁻¹) * τ₂⁻¹⁻¹ := by rw [h]
        _ = y⁻¹ := by group
    refine D.mem_cen_of_gens fun z hz => ?_
    have e : (g⁻¹ * τ₂ * g) * τ₂⁻¹ * z * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ =
        g⁻¹ * (τ₂ * (g * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * g⁻¹) * τ₂⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    rcases hz with rfl | hz
    · have : τ₂⁻¹ * z * τ₂⁻¹⁻¹ = z := by
        calc τ₂⁻¹ * z * τ₂⁻¹⁻¹ = τ₂⁻¹ * (τ₂ * z * τ₂⁻¹) * τ₂ := by rw [hτ₂b, inv_inv]
          _ = z := by group
      rw [this, hgb, hτ₂b, hgib]
    · have hzB : z ∈ B₁ := Subgroup.subset_closure hz
      rw [hτ₂inv' z hzB, show g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ by group,
        show τ₂ * (g * z * g⁻¹)⁻¹ * τ₂⁻¹ = (τ₂ * (g * z * g⁻¹) * τ₂⁻¹)⁻¹ by group,
        hτ₂inv _ (D.B₁N g hg z hzB), inv_inv]
      group
  have hfixnorm : ∀ g ∈ N, (∀ x ∈ A0, g * x * g⁻¹ ∈ A0) → g * b * g⁻¹ = b →
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := fun g hg hgA hgb =>
    hnorm g hg hgA (hδfix g hg hgb)
  have hγ'b : γ' * b * γ'⁻¹ = b := by rw [hγ'B b hb, hγb]
  obtain ⟨n₀, hcp, hcb, hc₁, hc₂, hc₃⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_pow_isPGroup hγ'b
      (by rw [hγ'B _ h₁, M.cyc.1]) (by rw [hγ'B _ h₂, M.cyc.2.1]) (by rw [hγ'B _ h₃, M.cyc.2.2])
  set c := γ' ^ n₀ with hcdef
  have hcN : c ∈ N := pow_mem hγ'N n₀
  have hcA : ∀ x ∈ A0, c * x * c⁻¹ ∈ A0 := pow_conj_mem hγ'A n₀
  have hcB₂ : ∀ x ∈ B₂, c * x * c⁻¹ ∈ B₂ := hfixnorm c hcN hcA hcb
  have hc3 : c ^ 3 ∈ Subgroup.zpowers b ⊔ B₂ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.cube_mem_A H.B₁_le hcb hc₁ hc₂ hc₃ hcp D.CB
  have hsup : Subgroup.zpowers b ⊔ B₂ = A0 := H.sup_eq
  have hcardA := D.card_A0 hS
  have hB₂card : Nat.card B₂ = 3 ^ 6 := by
    have h : Nat.card A0 = 3 * Nat.card B₂ := H.card_A
    rw [hcardA] at h
    norm_num at h ⊢
    omega
  have hPp : IsPGroup 3 ↥(A0 ⊔ Subgroup.zpowers c : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (D.isPGroup_A0 hS) hcp
      ((Subgroup.zpowers_le).2
        (CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hcA))
  have hPcard : 3 ^ 8 ≤ Nat.card ↥(A0 ⊔ Subgroup.zpowers c : Subgroup G) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hdvd : 3 ^ 7 ∣ 3 ^ k := by
      rw [← hk, ← hcardA]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h7 : 7 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hne : k ≠ 7 := by
      intro hk7
      have heq : A0 = A0 ⊔ Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hk7, hcardA])
      have hcA0 : c ∈ A0 := by
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      have := (hÂ hcA0).1 b₁ D.mem₁
      rw [hc₁] at this
      exact D.b₁_ne_b₂ this.symm
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPmax : ∀ R : Subgroup G, R ≤ N → IsPGroup 3 R →
      Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c ≤ R →
      R = Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c := by
    intro R hRN hRp hPR
    rw [hsup] at hPR ⊢
    exact (Subgroup.eq_of_le_of_card_ge hPR ((hN3 R hRN hRp).trans hPcard)).symm
  have hSetup := H.toSetup (b₁ := b₁) (b₂ := b₂) (b₃ := b₃) (c := c) rfl D.Bab D.B3 D.Bcard
    D.B₁card ((D.A0_le hS).trans D.Ahat_le_N) hcN hcb hc₁ hc₂ hc₃ hcB₂ hc3 hPmax
  have hB₂p : IsPGroup 3 B₂ := (D.isPGroup_A0 hS).to_le hB₂A
  have hker : ∀ x ∈ B₂, x * b = b * x → x ∈ B₁ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.RankFour.ker_of_cenS H.B₁_le H.inv_comm.2 hB₂p
      (fun x hx hx2 => H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hx) hx2) D.CB
  set T : Set G := {ι₁', ι₂', ι₃', σ₁₂', σ₂₃', γ'} with hTdef
  have hT : ∀ g ∈ T, ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hfixnorm _ hι₁'N hι₁'A (by rw [hι₁'B b hb, hι₁b])
    · exact hfixnorm _ hι₂'N hι₂'A (by rw [hι₂'B b hb, hι₂b])
    · exact hfixnorm _ hι₃'N hι₃'A (by rw [hι₃'B b hb, hι₃b])
    · exact hfixnorm _ hσ₁₂'N hσ₁₂'A (by rw [hσ₁₂'B b hb, hσ₁₂b])
    · exact hfixnorm _ hσ₂₃'N hσ₂₃'A (by rw [hσ₂₃'B b hb, hσ₂₃b])
    · exact hfixnorm _ hγ'N hγ'A hγ'b
  have hTb : ∀ g ∈ T, g * b * g⁻¹ = b := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [hι₁'B b hb, hι₁b]
    · rw [hι₂'B b hb, hι₂b]
    · rw [hι₃'B b hb, hι₃b]
    · rw [hσ₁₂'B b hb, hσ₁₂b]
    · rw [hσ₂₃'B b hb, hσ₂₃b]
    · exact hγ'b
  have hB₁irr : ∀ K : Subgroup G, K ≤ B₁ → K ≠ ⊥ → (∀ g ∈ T, ∀ x ∈ K, g * x * g⁻¹ ∈ K) →
      K = B₁ := by
    intro K hKB₁ hK hKT
    refine hirr K hKB₁ hK ?_
    have tr : ∀ {g g' : G}, (∀ z ∈ BB b b₁ b₂ b₃, g' * z * g'⁻¹ = g * z * g⁻¹) → g' ∈ T →
        ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun hg'B hg'T x hx => by
      rw [← hg'B x (D.B₁_le_B (hKB₁ hx))]
      exact hKT _ hg'T x hx
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact tr hι₁'B (by simp [hTdef])
    · exact tr hι₂'B (by simp [hTdef])
    · exact tr hι₃'B (by simp [hTdef])
    · exact tr hσ₁₂'B (by simp [hTdef])
    · exact tr hσ₂₃'B (by simp [hTdef])
    · exact tr hγ'B (by simp [hTdef])
  have hirr' := CFSG.RankThree.PartTwo.Sec21.FF81.RankFour.irreducible_of_kappa H.B₁_le
    H.inv_comm.2 (fun x hx => H.bB₂ hx) (fun y hy => (D.bB₁ y hy).symm) hker hTb hB₁irr
  have hA0N : A0 ≤ N := (D.A0_le hS).trans D.Ahat_le_N
  have hno : ∀ (K NL : Subgroup G), Compl b b₁ b₂ b₃ K NL →
      ∀ hb : b ∈ N, (⟨b, hb⟩ : ↥N) ∉ commutator ↥N := by
    intro K NL C hbN hmem
    have hKA : ∀ k ∈ K, k ∈ A0 → k = 1 := by
      intro k hk hkA
      obtain ⟨e, he⟩ := (D.isPGroup_A0 hS) ⟨k, hkA⟩
      have hke : k ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val he
      have h1 : orderOf k ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hke
      have h2 : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hk
      have hcop : Nat.Coprime (orderOf k) 3 := Nat.Coprime.coprime_dvd_left h2 C.K3
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
      have hi0 : i = 0 := by
        by_contra hi0
        rw [hi] at hcop
        exact absurd (Nat.Coprime.coprime_dvd_left (dvd_pow_self 3 hi0) hcop) (by decide)
      rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
      exact hi
    have hKn : ∀ g ∈ N, g ∈ Subgroup.normalizer (K : Set G) := fun g hg =>
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem (C.KN g hg)
    have hB₂N : B₂ ≤ N := hB₂A.trans hA0N
    have hBK : ∀ z ∈ BB b b₁ b₂ b₃ ⊔ K, ∃ y ∈ BB b b₁ b₂ b₃, ∃ k ∈ K, y * k = z := by
      intro z hz
      have h := Subgroup.coe_mul_of_left_le_normalizer_right (BB b b₁ b₂ b₃) K
        (fun y hy => hKn y (D.Ahat_le_N (D.B_le_Ahat hy)))
      have hz' : z ∈ ((BB b b₁ b₂ b₃ ⊔ K : Subgroup G) : Set G) := hz
      rw [h] at hz'
      obtain ⟨y, hy, k, hk, hyk⟩ := hz'
      exact ⟨y, hy, k, hk, hyk⟩
    have hÂdec : ∀ a ∈ Â, ∃ x ∈ A0, ∃ k ∈ K, a = x * k := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := D.exists_beta_eq hS (beta_mem ha)
      have hc : x⁻¹ * a ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
        refine D.mem_cen_of_beta (mul_mem (inv_mem (hÂ hx)) ha) ?_
        rw [beta_mul D.B₁ab (inv_mem (hÂ hx)) ha, D.beta_inv (hÂ hx), hxa, inv_mul_cancel]
      obtain ⟨z, hz, k, hk, hzk⟩ := hBK _ (C.CK hc)
      exact ⟨x * z, mul_mem hx (hS hz), k, hk, by rw [mul_assoc, hzk, mul_inv_cancel_left]⟩
    have hNdec : ∀ g ∈ N, ∃ x ∈ A0, ∃ k ∈ K, ∃ l ∈ NL, g = x * k * l := by
      intro g hg
      obtain ⟨l, hl, hgl⟩ := C.gen g hg
      obtain ⟨x, hx, k, hk, hxk⟩ := hÂdec _ hgl
      exact ⟨x, hx, k, hk, l, hl, by rw [← hxk, inv_mul_cancel_right]⟩
    set M₀ := B₂ ⊔ K with hM₀
    have hA0M₀ : ∀ x ∈ A0, ∀ m ∈ M₀, x * m * x⁻¹ ∈ M₀ := by
      intro x hx
      have hle : M₀.map (MulAut.conj x).toMonoidHom ≤ M₀ := by
        rw [hM₀, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          refine Subgroup.mem_sup_left ?_
          show x * y * x⁻¹ ∈ B₂
          have hw : x * y * x⁻¹ * y⁻¹ ∈ B₁ := hAab x hx y (hB₂A hy)
          have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
          rw [e]
          exact mul_mem (H.B₁_le hw) hy
        · rintro _ ⟨k, hk, rfl⟩
          exact Subgroup.mem_sup_right (C.KN x (hA0N hx) k hk)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    have hKM₀ : ∀ k ∈ K, ∀ m ∈ M₀, k * m * k⁻¹ ∈ M₀ := fun k hk m hm =>
      mul_mem (mul_mem (Subgroup.mem_sup_right hk) hm) (inv_mem (Subgroup.mem_sup_right hk))
    have hconjB₂ : ∀ g ∈ N, ∀ y ∈ B₂, g * y * g⁻¹ ∈ M₀ := by
      intro g hg y hy
      obtain ⟨x, hx, k, hk, l, hl, rfl⟩ := hNdec g hg
      obtain ⟨k₁, hk₁, hk₁A⟩ := D.exists_translate_cen hS (C.NLN hl)
      have hl'N : k₁⁻¹ * l ∈ N := mul_mem (inv_mem (D.cen_le_N hk₁)) (C.NLN hl)
      have hl'b : (k₁⁻¹ * l) * b * (k₁⁻¹ * l)⁻¹ = b := by
        rw [D.translate_conj hk₁ (by rw [C.NLb l hl]; exact hb), C.NLb l hl]
      have hy₁ : (k₁⁻¹ * l) * y * (k₁⁻¹ * l)⁻¹ ∈ B₂ := hfixnorm _ hl'N hk₁A hl'b y hy
      obtain ⟨z, hz, k₂, hk₂, hzk⟩ := hBK _ (C.CK hk₁)
      have e : x * k * l * y * (x * k * l)⁻¹ =
          x * (k * (z * (k₂ * ((k₁⁻¹ * l) * y * (k₁⁻¹ * l)⁻¹) * k₂⁻¹) * z⁻¹) * k⁻¹) * x⁻¹ := by
        rw [← hzk]
        group
      rw [e]
      exact hA0M₀ x hx _ (hKM₀ k hk _ (hA0M₀ z (hS hz) _
        (hKM₀ k₂ hk₂ _ (Subgroup.mem_sup_left hy₁))))
    have hNM₀ : ∀ g ∈ N, ∀ m ∈ M₀, g * m * g⁻¹ ∈ M₀ := by
      intro g hg
      have hle : M₀.map (MulAut.conj g).toMonoidHom ≤ M₀ := by
        rw [hM₀, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          exact hconjB₂ g hg y hy
        · rintro _ ⟨k, hk, rfl⟩
          exact Subgroup.mem_sup_right (C.KN g hg k hk)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    set M := M₀ ⊔ NL with hMdef
    have hA0M : ∀ x ∈ A0, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
      intro x hx
      have hle : M.map (MulAut.conj x).toMonoidHom ≤ M := by
        rw [hMdef, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨m, hm, rfl⟩
          exact Subgroup.mem_sup_left (hA0M₀ x hx m hm)
        · rintro _ ⟨l, hl, rfl⟩
          show x * l * x⁻¹ ∈ M
          have hxA : x ∈ Subgroup.zpowers b ⊔ B₂ := by rw [hsup]; exact hx
          obtain ⟨j, -, y, hy, rfl⟩ := exists_of_mem_A D.b3 (fun z hz => H.b_conj_mem hz) hxA
          have hlN := C.NLN hl
          have hlb := C.NLb l hl
          have h1 : l * y⁻¹ * l⁻¹ ∈ M₀ := hconjB₂ l hlN _ (inv_mem hy)
          have h2 : y * (l * y⁻¹ * l⁻¹) ∈ M₀ := mul_mem (Subgroup.mem_sup_left hy) h1
          have h3 := hA0M₀ (b ^ j) (pow_mem (hS hb) j) _ h2
          have hlbj : l * b ^ j * l⁻¹ = b ^ j := by rw [← conj_pow, hlb]
          have e : b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹ =
              b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (b ^ j)⁻¹ := by
            calc b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹
                = b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (l * b ^ j * l⁻¹)⁻¹ := by group
              _ = b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (b ^ j)⁻¹ := by rw [hlbj]
          have hcm : b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹ ∈ M₀ := by rw [e]; exact h3
          have e2 : b ^ j * y * l * (b ^ j * y)⁻¹ =
              (b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹) * l := by group
          rw [e2]
          exact mul_mem (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hl)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    have hNM : ∀ g ∈ N, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
      intro g hg m hm
      obtain ⟨x, hx, k, hk, l, hl, rfl⟩ := hNdec g hg
      have hkM : k ∈ M := Subgroup.mem_sup_left (Subgroup.mem_sup_right hk)
      have hlM : l ∈ M := Subgroup.mem_sup_right hl
      have e : x * k * l * m * (x * k * l)⁻¹ = x * (k * l * m * (k * l)⁻¹) * x⁻¹ := by group
      rw [e]
      exact hA0M x hx _ (mul_mem (mul_mem (mul_mem hkM hlM) hm) (inv_mem (mul_mem hkM hlM)))
    haveI hMn : (M.subgroupOf N).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNM g g.2 n hn⟩
    have hle : commutator ↥N ≤ M.subgroupOf N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      obtain ⟨x, hx, k, hk, l, hl, hg⟩ := hNdec g g.2
      obtain ⟨x', hx', k', hk', l', hl', hh⟩ := hNdec h h.2
      have hπ : ∀ (u : ↥N) (y : G) (hy : y ∈ A0) (k₀ : G) (_ : k₀ ∈ K) (l₀ : G) (_ : l₀ ∈ NL),
          (u : G) = y * k₀ * l₀ →
          (QuotientGroup.mk' (M.subgroupOf N) u) =
            QuotientGroup.mk' (M.subgroupOf N) ⟨y, hA0N hy⟩ := by
        intro u y hy k₀ hk₀ l₀ hl₀ hu
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        show (u : G)⁻¹ * y ∈ M
        rw [hu, show (y * k₀ * l₀)⁻¹ * y = (k₀ * l₀)⁻¹ * (y⁻¹ * y) by group, inv_mul_cancel,
          mul_one]
        exact inv_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hk₀))
          (Subgroup.mem_sup_right hl₀))
      have key : QuotientGroup.mk' (M.subgroupOf N) (g * h * g⁻¹ * h⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπ g x hx k hk l hl hg,
          hπ h x' hx' k' hk' l' hl' hh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        show x * x' * x⁻¹ * x'⁻¹ ∈ M
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (H.B₁_le (hAab x hx x' hx')))
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at key
      exact key
    have hbM : b ∈ M := Subgroup.mem_subgroupOf.mp (hle hmem)
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left M₀ NL
      (fun l hl => CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem
        (hNM₀ l (C.NLN hl)))
    have hbM' : b ∈ ((M₀ ⊔ NL : Subgroup G) : Set G) := hbM
    rw [hcoe] at hbM'
    obtain ⟨m, hm, l, hl, hml⟩ := hbM'
    have hM₀Â : M₀ ≤ Â := sup_le (hB₂A.trans (D.A0_le hS)) (C.KC.trans D.cen_le_Ahat)
    have hlÂ : l ∈ Â := by
      have e : l = m⁻¹ * b := by rw [← hml, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hM₀Â hm)) (D.B_le_Ahat hb)
    have hlC : l ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_beta hlÂ ?_
      rw [beta_def, C.NLb l hl, mul_inv_cancel]
    have hlB₁ : l ∈ B₁ := C.NLC ⟨hl, hlC⟩
    have hbM₀ : b ∈ M₀ := by
      rw [← hml]
      exact mul_mem hm (Subgroup.mem_sup_left (H.B₁_le hlB₁))
    have hcoe₂ := Subgroup.coe_mul_of_left_le_normalizer_right B₂ K
      (fun y hy => hKn y (hB₂N hy))
    have hbM₀' : b ∈ ((B₂ ⊔ K : Subgroup G) : Set G) := hbM₀
    rw [hcoe₂] at hbM₀'
    obtain ⟨y, hy, k, hk, hyk⟩ := hbM₀'
    have hkA : k ∈ A0 := by
      have e : k = y⁻¹ * b := by rw [← hyk, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hB₂A hy)) (hS hb)
    have hk1 := hKA k hk hkA
    simp only [hk1, mul_one] at hyk
    rw [hyk] at hy
    exact D.b_not_mem (H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hb) hy)
  have hbN' : ∀ hb : b ∈ N, (⟨b, hb⟩ : ↥N) ∈ commutator ↥N →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧ ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ B₁ := by
    intro hbN hmem
    obtain ⟨t, htN, htb, htB₁⟩ | ⟨K, NL, C⟩ := hbt hbN hmem
    swap
    · exact absurd hmem (hno K NL C hbN)
    have hs₀N : t * τ ∈ N := mul_mem htN hτN
    have hs₀inv : ∀ z ∈ BB b b₁ b₂ b₃, (t * τ) * z * (t * τ)⁻¹ = z⁻¹ := by
      refine conj_inv_of_closure D.Bab ?_
      intro z hz
      have e : (t * τ) * z * (t * τ)⁻¹ = t * (τ * z * τ⁻¹) * t⁻¹ := by group
      rw [e]
      rcases hz with rfl | hz
      · rw [hτb, htb]
      · have hzB : z ∈ B₁ := Subgroup.subset_closure hz
        rw [hτinv z hzB, show t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ by group, htB₁ z hzB]
    obtain ⟨s, hsN, hsB, hsA⟩ := D.exists_translate' hS hs₀N
    have hsinv : ∀ z ∈ BB b b₁ b₂ b₃, s * z * s⁻¹ = z⁻¹ := fun z hz => by
      rw [hsB z hz, hs₀inv z hz]
    have hsinv' : ∀ z ∈ BB b b₁ b₂ b₃, s⁻¹ * z * s⁻¹⁻¹ = z⁻¹ := by
      intro z hz
      have h := hsinv z⁻¹ (inv_mem hz)
      rw [inv_inv] at h
      calc s⁻¹ * z * s⁻¹⁻¹ = s⁻¹ * (s * z⁻¹ * s⁻¹) * s⁻¹⁻¹ := by rw [h]
        _ = z⁻¹ := by group
    have hδ : (s⁻¹ * τ₂ * s) * τ₂⁻¹ ∈
        Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_gens fun z hz => ?_
      have hzB : z ∈ BB b b₁ b₂ b₃ := Subgroup.subset_closure hz
      have hz' : τ₂⁻¹ * z * τ₂⁻¹⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B (inv_mem hτ₂N) hzB
      have e : (s⁻¹ * τ₂ * s) * τ₂⁻¹ * z * ((s⁻¹ * τ₂ * s) * τ₂⁻¹)⁻¹ =
          s⁻¹ * (τ₂ * (s * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * s⁻¹) * τ₂⁻¹) * s⁻¹⁻¹ := by group
      rw [e, hsinv _ hz', show τ₂ * (τ₂⁻¹ * z * τ₂⁻¹⁻¹)⁻¹ * τ₂⁻¹ = z⁻¹ by group,
        hsinv' z⁻¹ (inv_mem hzB), inv_inv]
    have hsB₂ := hnorm s hsN hsA hδ
    refine ⟨s, by rw [hsinv _ h₁], fun x hx => ?_⟩
    have hxA := hB₂A hx
    have hsx : beta b (s * x * s⁻¹) = beta b x := by
      have hsb : s⁻¹ * b * s⁻¹⁻¹ = b⁻¹ := hsinv' b hb
      have e1 : beta b (s * x * s⁻¹) = s * (x * (s⁻¹ * b * s⁻¹⁻¹) * x⁻¹ * (s⁻¹ * b * s⁻¹⁻¹)⁻¹) * s⁻¹ := by
        rw [beta_def]; group
      rw [e1, hsb, inv_inv]
      have e2 : x * b⁻¹ * x⁻¹ * b = (beta b x)⁻¹ := by
        rw [beta_def]
        have hβc : Commute (x * b * x⁻¹ * b⁻¹) b :=
          (D.bB₁ _ (beta_mem (hÂ hxA))).symm
        calc x * b⁻¹ * x⁻¹ * b = b⁻¹ * ((x * b * x⁻¹ * b⁻¹)⁻¹ * b) := by group
          _ = b⁻¹ * (b * (x * b * x⁻¹ * b⁻¹)⁻¹) := by rw [hβc.inv_left.eq]
          _ = (x * b * x⁻¹ * b⁻¹)⁻¹ := by group
      rw [e2, hsinv _ (D.B₁_le_B (inv_mem (beta_mem (hÂ hxA)))), inv_inv]
    have hw : s * x * s⁻¹ * x⁻¹ ∈ BB b b₁ b₂ b₃ := by
      refine D.mem_B_of_mem_A0 hS (mul_mem (hsA x hxA) (inv_mem hxA)) ?_
      rw [beta_mul D.B₁ab (hÂ (hsA x hxA)) (inv_mem (hÂ hxA)), hsx, D.beta_inv (hÂ hxA),
        mul_inv_cancel]
    exact H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hw)
      (mul_mem (hsB₂ x hx) (inv_mem hx))
  have hB₂3 := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exp_three_of_irreducible' hSetup hT
    hirr' hB₂card hbN' hbG
  obtain ⟨m₁, hm₁, ht₂p⟩ := exists_odd_pow_two ι₁'
  set t := ι₁' ^ m₁ with htdef
  have htN : t ∈ N := pow_mem hι₁'N m₁
  have htA : ∀ x ∈ A0, t * x * t⁻¹ ∈ A0 := pow_conj_mem hι₁'A m₁
  have htb : t * b * t⁻¹ = b := pow_conj_fix (by rw [hι₁'B b hb, hι₁b]) m₁
  have ht₁ : t * b₁ * t⁻¹ = b₁⁻¹ := pow_conj_inv (by rw [hι₁'B _ h₁, M.s₁.1]) hm₁
  have ht₂ : t * b₂ * t⁻¹ = b₂ := pow_conj_fix (by rw [hι₁'B _ h₂, M.s₁.2.1]) m₁
  have ht₃ : t * b₃ * t⁻¹ = b₃ := pow_conj_fix (by rw [hι₁'B _ h₃, M.s₁.2.2]) m₁
  have htB₂ : ∀ x ∈ B₂, t * x * t⁻¹ ∈ B₂ := hfixnorm t htN htA htb
  have ht1 : t ≠ 1 := by
    intro e
    rw [e, one_mul, inv_one, mul_one] at ht₁
    exact D.b₁_ne_one (D.eq_one_of_eq_inv (D.B₁3 _ D.mem₁) ht₁.symm)
  have ht2cen : ∀ x ∈ A0, t ^ 2 * x * (t ^ 2)⁻¹ = x := by
    intro x hx
    have hδ : t ^ 2 ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_gens fun z hz => ?_
      have e : t ^ 2 * z * (t ^ 2)⁻¹ = t * (t * z * t⁻¹) * t⁻¹ := by
        rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
      rw [e]
      rcases hz with rfl | rfl | rfl | rfl
      · rw [htb, htb]
      · rw [ht₁, show t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ by group, ht₁, inv_inv]
      · rw [ht₂, ht₂]
      · rw [ht₃, ht₃]
    exact D.cen_two hS hδ (pow_conj_mem htA 2)
      (ht₂p.to_le (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers _) 2))) hx
  by_cases hsq : t ^ 2 = 1
  · exact CFSG.RankThree.PartTwo.Sec21.FF81.RankFour.four_le_localRank_of_setup hSetup hT
      hirr' hB₂card hbN' hbG hker ht1 hsq htB₂ htb ht₁ ht₂ ht₃
  ·
    obtain ⟨f, hf⟩ := ht₂p ⟨t, Subgroup.mem_zpowers t⟩
    have htf : t ^ (2 ^ f) = 1 := by simpa using congrArg Subtype.val hf
    obtain ⟨f', -, hf'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one htf)
    have hf'2 : 2 ≤ f' := by
      by_contra hlt
      rcases (by omega : f' = 0 ∨ f' = 1) with h0 | h0
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hf'
        exact ht1 hf'
      · apply hsq
        rw [h0, pow_one] at hf'
        rw [← hf']
        exact pow_orderOf_eq_one t
    have ht₀1 : t ^ (2 ^ (f' - 1)) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hf']
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have ht₀2 : (t ^ (2 ^ (f' - 1))) ^ 2 = 1 := by
      rw [← pow_mul t (2 ^ (f' - 1)) 2, ← pow_succ, show f' - 1 + 1 = f' by omega, ← hf',
        pow_orderOf_eq_one]
    have ht₀eq : t ^ (2 ^ (f' - 1)) = (t ^ 2) ^ (2 ^ (f' - 2)) := by
      rw [← pow_mul t 2 (2 ^ (f' - 2))]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    have hC : B₂ ≤ Subgroup.centralizer ({t ^ (2 ^ (f' - 1))} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := pow_conj_fix (ht2cen x (hB₂A hx)) (2 ^ (f' - 2))
      rw [← ht₀eq] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have h6 := CFSG.RankThree.PartTwo.Sec3.le_localRank_of_commute_involution (by norm_num)
      ht₀1 ht₀2 ⟨⟨fun x y => Subtype.ext (H.inv_comm.2 _ x.2 _ y.2)⟩⟩ hB₂3 hC hB₂card
    omega

end CFSG.RankThree.PartTwo.Sec21.FF81.Lift
