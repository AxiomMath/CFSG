module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31Theta
public import CFSG.RankThree.PartTwo.Sec21.FF84S31Tools
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG
open scoped commutatorElement

@[expose] def A7TauStmt : Prop :=
  ∀ x : P8, x * τ₀ = τ₀ * x → (∃ k : ℕ, orderOf x = 2 ^ k) → x ∉ Subgroup.zpowers τ₀ →
    ∃ r : P8, r ∈ A6tau ∧ ¬ ∃ k : ℕ, orderOf (x * (r * x * r⁻¹)) = 2 ^ k

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_toABG {p : ℕ} [Fact p.Prime] {P H : Subgroup G} (h : IsSylowOf p P H) :
    CFSG.ABGLocalTools.IsSylowOf p P H :=
  CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨h.1, h.2.1, (Nat.Prime.coprime_iff_not_dvd Fact.out).1 h.2.2⟩

theorem not_isPGroup_two_of_orderOf_three {A : Subgroup G} {x : G} (hx : x ∈ A)
    (hx3 : orderOf x = 3) : ¬ IsPGroup 2 A := by
  intro hA
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hA) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  have : 3 ∣ 2 ^ k := ⟨1, by omega⟩
  have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

end Sylow

section Basic

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem Opp_le (p : ℕ) (H : Subgroup G) : Opp p H ≤ H := Subgroup.map_subtype_le _

theorem orderOf_b₁ (h : FF84Sec3 b L B b₁ b₂) : orderOf b₁ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h13, -, -, hne1, -, -, -⟩ := mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  exact orderOf_eq_prime h13 hne1

theorem X_le_CenS_B (h : FF84Sec3 b L B b₁ b₂) : Opp 3 (Cen b) ≤ CenS B := by
  intro x hx
  have hxL : x ∈ CenS L := (P_C_structure h).1 hx
  have hxb : x ∈ Cen b := Opp_le 3 _ hx
  have hB : B ≤ Cen x := by
    rw [h.mono.2.1]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxL _ (Subgroup.mem_inf.1 h.hb₁).2)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxL _ (Subgroup.mem_inf.1 h.hb₂).2)
  refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hB hy)

theorem mem_C_decomp (h : FF84Sec3 b L B b₁ b₂) {a : G} (ha : a ∈ CenS L ⊓ Cen b) :
    ∃ i : ℤ, ∃ z ∈ Opp 3 (Cen b), a = b ^ i * z := by
  have hsup := (P_C_structure h).2.1
  rw [← hsup, Subgroup.sup_eq_closure] at ha
  have hXc : ∀ z ∈ Opp 3 (Cen b), ∀ i : ℤ, Commute (b ^ i) z := fun z hz i =>
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (Opp_le 3 _ hz)) i).symm
  have hXb : ∀ z ∈ Opp 3 (Cen b), ∀ i : ℤ, z * b ^ i = b ^ i * z := fun z hz i =>
    (hXc z hz i).symm.eq
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨i, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨0, x, hx, by simp⟩
  | one => exact ⟨0, 1, Subgroup.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, z, hz, rfl⟩ := hx
    obtain ⟨j, w, hw, rfl⟩ := hy
    refine ⟨i + j, z * w, Subgroup.mul_mem _ hz hw, ?_⟩
    rw [zpow_add]
    calc b ^ i * z * (b ^ j * w) = b ^ i * (z * b ^ j) * w := by group
      _ = b ^ i * (b ^ j * z) * w := by rw [hXb z hz j]
      _ = b ^ i * b ^ j * (z * w) := by group
  | inv x _ hx =>
    obtain ⟨i, z, hz, rfl⟩ := hx
    refine ⟨-i, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    rw [mul_inv_rev, zpow_neg]
    exact (Commute.inv_inv (hXc z hz i)).eq.symm

theorem two_elt_C (h : FF84Sec3 b L B b₁ b₂) {a : G} (ha : a ∈ CenS L ⊓ Cen b) {n : ℕ}
    (hn : a ^ (2 ^ n) = 1) : a ∈ Opp 3 (Cen b) := by
  obtain ⟨i, z, hz, rfl⟩ := mem_C_decomp h ha
  have hcomm : Commute (b ^ i) z :=
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (Opp_le 3 _ hz)) i).symm
  rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_mul] at hn
  have h1 : b ^ (i * (2 ^ n : ℕ)) ∈ Subgroup.zpowers b ⊓ Opp 3 (Cen b) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩, ?_⟩
    have : b ^ (i * (2 ^ n : ℕ)) = (z ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz _)
  rw [(P_C_structure h).2.2, Subgroup.mem_bot] at h1
  have h3 : (3 : ℤ) ∣ i * (2 ^ n : ℕ) := three_dvd_of_zpow_eq_one h.hyp.ord h1
  have h4 : (3 : ℤ) ∣ i := by
    have hc : IsCoprime (3 : ℤ) ((2 ^ n : ℕ) : ℤ) := by
      rw [Nat.cast_pow]
      exact IsCoprime.pow_right (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    exact hc.dvd_of_dvd_mul_right h3
  have hbi : b ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [h.hyp.ord]; exact_mod_cast h4)
  rw [hbi, one_mul]
  exact hz

theorem no_normal_two (h : FF84Sec3 b L B b₁ b₂) {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ Nor L) (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A) : A ≤ CenS L := by
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hI : ∀ x ∈ L, ∀ y ∈ A ⊓ L, x * y * x⁻¹ ∈ A ⊓ L := by
    intro x hx y hy
    obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨hLA x hx y hyA, L.mul_mem (L.mul_mem hx hyL) (L.inv_mem hx)⟩
  have hne : ¬ L ≤ A ⊓ L := by
    intro hLle
    exact not_isPGroup_two_of_orderOf_three (Subgroup.mem_inf.1 (hLle hb₁L)).1 (orderOf_b₁ h) hA
  have hcen := quasi_commute_of_normal_proper h.hyp.quasi inf_le_right hI hne
  have hL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.hyp.quasi.1
  intro a ha
  have hxL : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 (hAN ha) l).1 hl
  have hz : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CenS L := by
    intro l hl
    have h1 : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L := by
      refine Subgroup.mem_inf.2 ⟨?_, L.mul_mem (hxL l hl) (L.inv_mem hl)⟩
      have e : a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) := by group
      rw [e]
      exact A.mul_mem ha (hLA l hl a⁻¹ (A.inv_mem ha))
    exact Subgroup.mem_centralizer_iff.2 (fun m hm => (hcen _ h1 m hm))
  have := perfect_centralizes_of_comm_central L hL a hxL hz
  exact Subgroup.mem_centralizer_iff.2 (fun l hl => (this l hl).symm)

theorem pgroup_elt {p : ℕ} {A : Subgroup G} (hA : IsPGroup p A) {a : G} (ha : a ∈ A) :
    ∃ k : ℕ, a ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem pgroup_orderOf {A : Subgroup G} (hA : IsPGroup 2 A) {a : G} (ha : a ∈ A) :
    ∃ k : ℕ, orderOf a = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hA) ⟨a, ha⟩
  exact ⟨k, by simpa [Subgroup.orderOf_mk] using hk⟩

theorem mem_Nor_of_comm {V : Subgroup G} {l : G} (hc : ∀ w ∈ V, l * w = w * l) : l ∈ Nor V := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have key : ∀ w ∈ V, l * w * l⁻¹ = w := fun w hw => by rw [hc w hw]; simp
  constructor
  · intro hw
    rw [key w hw]
    exact hw
  · intro hw
    have h2 : l * (l * w * l⁻¹) = l * w := by
      rw [hc _ hw]; group
    have e : l * w * l⁻¹ = w := mul_left_cancel h2
    rw [← e]
    exact hw

theorem conj_mem_CenS {B : Subgroup G} {g x : G} (hg : g ∈ Nor B) (hx : x ∈ CenS B) :
    g * x * g⁻¹ ∈ CenS B := by
  have hg' : g⁻¹ ∈ Nor B := Subgroup.inv_mem _ hg
  refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
  have hy' : g⁻¹ * y * g ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 hg' y).1 hy
    simpa using this
  have e := Subgroup.mem_centralizer_iff.1 hx _ hy'
  calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
    _ = g * x * g⁻¹ * y := by group

theorem L_le_Nor_of_le_X (h : FF84Sec3 b L B b₁ b₂) {V : Subgroup G} (hV : V ≤ Opp 3 (Cen b)) :
    L ≤ Nor V := by
  intro l hl
  have key : ∀ l ∈ L, ∀ x ∈ V, l * x * l⁻¹ = x := fun l hl x hx => by
    have := Subgroup.mem_centralizer_iff.1 ((P_C_structure h).1 (hV hx)) l hl
    rw [this]; simp
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [key l hl y hy]
    exact hy
  · intro hy
    have := key l⁻¹ (L.inv_mem hl) _ hy
    simp only [inv_inv] at this
    have e : y = l * y * l⁻¹ := by
      calc y = l⁻¹ * (l * y * l⁻¹) * l := by group
        _ = l * y * l⁻¹ := this
    rw [e]
    exact hy

theorem Z_Vstar_basic (h : FF84Sec3 b L B b₁ b₂) (V : Subgroup G)
    (hV : IsSylowOf 2 V (Opp 3 (Cen b))) :
    Op 2 (Nor V) ⊓ Cen b = V ∧ Op 2 (Nor V) ⊓ CenS B = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVX : V ≤ Opp 3 (Cen b) := hV.1
  have hV2 : IsPGroup 2 V := hV.2.1
  have hLV := L_le_Nor_of_le_X h hVX
  have hVb : V ≤ Cen b := hVX.trans (Opp_le 3 _)
  have hVstar : V ≤ Op 2 (Nor V) :=
    le_Op_of_normal 2 (Nor V) V Subgroup.le_normalizer hV2
      (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 hn m).1 hm)
  have hA2 : IsPGroup 2 (Op 2 (Nor V) ⊓ Cen b : Subgroup G) :=
    (Op_isPGroup 2 (Nor V)).to_le inf_le_left
  have hAL : ∀ l ∈ L, ∀ a ∈ Op 2 (Nor V) ⊓ Cen b, l * a * l⁻¹ ∈ Op 2 (Nor V) ⊓ Cen b := by
    intro l hl a ha
    obtain ⟨haO, haC⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨Op_conj_mem 2 (Subgroup.le_normalizer (hLV hl)) haO, ?_⟩
    have hlb : l ∈ Cen b := h.hyp.hLC hl
    exact (Cen b).mul_mem ((Cen b).mul_mem hlb haC) ((Cen b).inv_mem hlb)
  have hAN : (Op 2 (Nor V) ⊓ Cen b) ≤ Nor L := fun a ha => h.hyp.hLN (Subgroup.mem_inf.1 ha).2
  have hAcen := no_normal_two h hA2 hAN hAL
  have hAX : (Op 2 (Nor V) ⊓ Cen b) ≤ Opp 3 (Cen b) := by
    intro a ha
    obtain ⟨k, hk⟩ := pgroup_elt hA2 ha
    exact two_elt_C h (Subgroup.mem_inf.2 ⟨hAcen ha, (Subgroup.mem_inf.1 ha).2⟩) hk
  have hEq : Op 2 (Nor V) ⊓ Cen b = V :=
    (isSylowOf_toABG hV).eq_of_le (le_inf hVstar hVb) hAX hA2
  refine ⟨hEq, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hxb : x ∈ Cen b :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h2 b (mem_B_b h)).symm
    rw [← hEq]
    exact Subgroup.mem_inf.2 ⟨h1, hxb⟩
  · intro x hx
    exact Subgroup.mem_inf.2 ⟨hVstar hx, X_le_CenS_B h (hVX hx)⟩

theorem HasTheta.ker_cen {θ : G → P8} (H : HasTheta L b₁ b₂ θ) {g : G} (hg : g ∈ Nor L)
    (h1 : θ g = 1) : g ∈ CenS L := (H.ker g hg).1 h1

theorem key_le_CenS_B (h : FF84Sec3 b L B b₁ b₂) {θ : G → P8} (H : HasTheta L b₁ b₂ θ)
    (hA7 : A7TauStmt) {V' : Subgroup G} (hV'2 : IsPGroup 2 V') (hV'B : V' ≤ CenS B) :
    Op 2 (Nor V') ⊓ Cen b ≤ CenS B := by
  have P : PreTheta L θ := H.toPreTheta
  have hV'b : ∀ w ∈ V', w ∈ Cen b := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (hV'B hw) b (mem_B_b h)).symm
  have hV'N : ∀ w ∈ V', w ∈ Nor L := fun w hw => h.hyp.hLN (hV'b w hw)
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2
  have hwθ : ∀ w ∈ V', θ w = 1 ∨ θ w = τ₀ := by
    intro w hw
    obtain ⟨k, hk⟩ := pgroup_elt hV'2 hw
    exact H.two_elt hb₁N hb₂N (hV'N w hw)
      (Subgroup.mem_centralizer_iff.1 (hV'B hw) b₁ (mem_B_b₁ h)).symm
      (Subgroup.mem_centralizer_iff.1 (hV'B hw) b₂ (mem_B_b₂ h)).symm hk
  have hV'star : V' ≤ Op 2 (Nor V') :=
    le_Op_of_normal 2 (Nor V') V' Subgroup.le_normalizer hV'2
      (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 hn m).1 hm)
  have hY2 : IsPGroup 2 (Op 2 (Nor V') ⊓ Cen b : Subgroup G) :=
    (Op_isPGroup 2 (Nor V')).to_le inf_le_left
  have hYN : (Op 2 (Nor V') ⊓ Cen b) ≤ Nor L := fun a ha => h.hyp.hLN (Subgroup.mem_inf.1 ha).2
  have hX : ∀ z ∈ CenS L ⊓ Cen b, (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ CenS B :=
    fun z hz ⟨k, hk⟩ => X_le_CenS_B h (two_elt_C h hz hk)
  by_cases hall : ∀ v ∈ V', θ v = 1
  ·
    have hV'L : V' ≤ CenS L := fun v hv => HasTheta.ker_cen H (hV'N v hv) (hall v hv)
    have hLV : L ≤ Nor V' := by
      intro l hl
      refine mem_Nor_of_comm (fun w hw => ?_)
      exact Subgroup.mem_centralizer_iff.1 (hV'L hw) l hl
    have hAL : ∀ l ∈ L, ∀ a ∈ Op 2 (Nor V') ⊓ Cen b, l * a * l⁻¹ ∈ Op 2 (Nor V') ⊓ Cen b := by
      intro l hl a ha
      obtain ⟨haO, haC⟩ := Subgroup.mem_inf.1 ha
      refine Subgroup.mem_inf.2 ⟨Op_conj_mem 2 (Subgroup.le_normalizer (hLV hl)) haO, ?_⟩
      have hlb : l ∈ Cen b := h.hyp.hLC hl
      exact (Cen b).mul_mem ((Cen b).mul_mem hlb haC) ((Cen b).inv_mem hlb)
    have hAcen := no_normal_two h hY2 hYN hAL
    intro a ha
    obtain ⟨k, hk⟩ := pgroup_elt hY2 ha
    exact hX a (Subgroup.mem_inf.2 ⟨hAcen ha, (Subgroup.mem_inf.1 ha).2⟩) ⟨k, hk⟩
  · push Not at hall
    obtain ⟨v₀, hv₀, hθv₀⟩ := hall
    have hτ : θ v₀ = τ₀ := (hwθ v₀ hv₀).resolve_left hθv₀
    have hv₀N := hV'N v₀ hv₀
    have hlift : ∀ r ∈ A6tau, ∃ l ∈ L, (∀ w ∈ V', l * w = w * l) ∧ θ l = r := by
      intro r hr
      obtain ⟨l, hl, hlv, hθl⟩ := PreTheta.A6tau_lift P hv₀N hτ r hr
      refine ⟨l, hl, fun w hw => ?_, hθl⟩
      rcases hwθ w hw with h1 | h1
      · exact Subgroup.mem_centralizer_iff.1 (HasTheta.ker_cen H (hV'N w hw) h1) l hl
      · have hz : w * v₀⁻¹ ∈ Nor L := mul_mem (hV'N w hw) (inv_mem hv₀N)
        have hzθ : θ (w * v₀⁻¹) = 1 := by
          rw [P.mul _ (hV'N w hw) _ (inv_mem hv₀N), P.inv hv₀N, h1, hτ]; simp
        have hzl := Subgroup.mem_centralizer_iff.1 (HasTheta.ker_cen H hz hzθ) l hl
        calc l * w = l * ((w * v₀⁻¹) * v₀) := by group
          _ = (l * (w * v₀⁻¹)) * v₀ := by group
          _ = ((w * v₀⁻¹) * l) * v₀ := by rw [hzl]
          _ = (w * v₀⁻¹) * (l * v₀) := by group
          _ = (w * v₀⁻¹) * (v₀ * l) := by rw [hlv]
          _ = w * l := by group
    intro y hy
    obtain ⟨hyO, hyb⟩ := Subgroup.mem_inf.1 hy
    have hyN : y ∈ Nor L := h.hyp.hLN hyb
    have hyV : y ∈ Nor V' := Op_le 2 _ hyO
    have hyk : ∃ k : ℕ, orderOf y = 2 ^ k := pgroup_orderOf hY2 hy
    have hθy : θ y = 1 ∨ θ y = τ₀ := by
      have hτc : θ y * τ₀ = τ₀ * θ y := by
        have h1 : y * v₀ * y⁻¹ ∈ V' := (Subgroup.mem_normalizer_iff.1 hyV v₀).1 hv₀
        have h2 := P.conj hyN hv₀N
        rcases hwθ _ h1 with h3 | h3
        · rw [h3, hτ] at h2
          have : θ y * τ₀ * (θ y)⁻¹ = 1 := h2.symm
          have h4 : τ₀ = 1 := by
            have := congrArg (fun z => (θ y)⁻¹ * z * θ y) this
            simpa [mul_assoc] using this
          exact absurd h4 (by decide +kernel)
        · rw [h3, hτ] at h2
          calc θ y * τ₀ = (θ y * τ₀ * (θ y)⁻¹) * θ y := by group
            _ = τ₀ * θ y := by rw [← h2]
      obtain ⟨k, hk⟩ := hyk
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (hk ▸ P.orderOf_dvd hyN : orderOf (θ y) ∣ 2 ^ k)
      by_contra hne
      push Not at hne
      have hnot : θ y ∉ Subgroup.zpowers τ₀ := by
        intro hmem
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
        have hτ2 : τ₀ ^ 2 = 1 := by decide +kernel
        have hord : orderOf τ₀ = 2 := orderOf_eq_prime hτ2 (by decide +kernel)
        have hi' : τ₀ ^ (i % 2) = θ y := by
          have := zpow_mod_orderOf τ₀ i
          rw [hord] at this
          simpa using this.trans hi
        have hi2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
        rcases hi2 with e | e
        · rw [e] at hi'; simp at hi'; exact hne.1 hi'.symm
        · rw [e] at hi'; simp at hi'; exact hne.2 hi'.symm
      obtain ⟨r, hr, hnord⟩ := hA7 (θ y) hτc ⟨j, hj'⟩ hnot
      obtain ⟨l, hl, hlc, hθl⟩ := hlift r hr
      have hlV : l ∈ Nor V' := mem_Nor_of_comm hlc
      have hlb : l ∈ Cen b := h.hyp.hLC hl
      have hy' : l * y * l⁻¹ ∈ Op 2 (Nor V') ⊓ Cen b :=
        Subgroup.mem_inf.2 ⟨Op_conj_mem 2 (Subgroup.le_normalizer hlV) hyO,
          (Cen b).mul_mem ((Cen b).mul_mem hlb hyb) ((Cen b).inv_mem hlb)⟩
      have hyy := mul_mem hy hy'
      have hlN : l ∈ Nor L := Subgroup.le_normalizer hl
      have hy'N : l * y * l⁻¹ ∈ Nor L := mul_mem (mul_mem hlN hyN) (inv_mem hlN)
      obtain ⟨k2, hk2⟩ := pgroup_orderOf hY2 hyy
      have hθ : θ (y * (l * y * l⁻¹)) = θ y * (r * θ y * r⁻¹) := by
        rw [P.mul _ hyN _ hy'N, P.conj hlN hyN, hθl]
      have hdvd := P.orderOf_dvd (mul_mem hyN hy'N)
      rw [hθ, hk2] at hdvd
      obtain ⟨j2, -, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact hnord ⟨j2, hj2⟩
    rcases hθy with h1 | h1
    · exact hX y (Subgroup.mem_inf.2 ⟨HasTheta.ker_cen H hyN h1, hyb⟩)
        (by obtain ⟨k, hk⟩ := pgroup_elt hY2 hy; exact ⟨k, hk⟩)
    · have hz : y * v₀⁻¹ ∈ Nor L := mul_mem hyN (inv_mem hv₀N)
      have hzθ : θ (y * v₀⁻¹) = 1 := by
        rw [P.mul _ hyN _ (inv_mem hv₀N), P.inv hv₀N, h1, hτ]; simp
      have hzb : y * v₀⁻¹ ∈ Cen b :=
        (Cen b).mul_mem hyb ((Cen b).inv_mem (hV'b v₀ hv₀))
      have hzY : y * v₀⁻¹ ∈ Op 2 (Nor V') ⊓ Cen b :=
        Subgroup.mem_inf.2 ⟨mul_mem hyO (inv_mem (hV'star hv₀)), hzb⟩
      have hzX : y * v₀⁻¹ ∈ CenS B :=
        hX _ (Subgroup.mem_inf.2 ⟨HasTheta.ker_cen H hz hzθ, hzb⟩)
          (by obtain ⟨k, hk⟩ := pgroup_elt hY2 hzY; exact ⟨k, hk⟩)
      have : y = (y * v₀⁻¹) * v₀ := by group
      rw [this]
      exact mul_mem hzX (hV'B hv₀)

theorem exists_swap (h : FF84Sec3 b L B b₁ b₂) :
    ∃ g ∈ Nor B, g * b * g⁻¹ = b₁ ∧ g * b₁ * g⁻¹ = b := by
  obtain ⟨g, hg, hgi⟩ := P_monomial h (Equiv.swap 0 1) (fun _ => 1)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa using hgi 0
  · simpa using hgi 1

theorem Z_Vstar_b₁ (hA7 : A7TauStmt) (hZ : Nat.card (Subgroup.center L) ∣ 2)
    (h : FF84Sec3 b L B b₁ b₂) (V : Subgroup G) (hV : IsSylowOf 2 V (Opp 3 (Cen b))) :
    Op 2 (Nor V) ⊓ Cen b₁ = V := by
  obtain ⟨θ, H⟩ := exists_theta h hZ
  obtain ⟨g, hg, hgb, hgb₁⟩ := exists_swap h
  have hVX : V ≤ Opp 3 (Cen b) := hV.1
  have hV2 : IsPGroup 2 V := hV.2.1
  have hVstar : V ≤ Op 2 (Nor V) :=
    le_Op_of_normal 2 (Nor V) V Subgroup.le_normalizer hV2
      (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 hn m).1 hm)
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hVb₁ : V ≤ Cen b₁ := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 ((P_C_structure h).1 (hVX hv)) b₁ hb₁L).symm
  refine le_antisymm ?_ (le_inf hVstar hVb₁)
  intro a ha
  obtain ⟨haO, hab⟩ := Subgroup.mem_inf.1 ha
  have hV'2 : IsPGroup 2 (conjBy g V) := hV2.map _
  have hV'B : conjBy g V ≤ CenS B := by
    rintro _ ⟨v, hv, rfl⟩
    exact conj_mem_CenS hg (X_le_CenS_B h (hVX hv))
  have hmem : g * a * g⁻¹ ∈ Op 2 (Nor (conjBy g V)) ⊓ Cen b := by
    rw [Nor_conjBy, Op_conjBy]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact ⟨a, haO, by simp [MulAut.conj_apply]⟩
    · rw [← hgb₁, Cen_conjBy]
      exact ⟨a, hab, by simp [MulAut.conj_apply]⟩
  have hCB := conj_mem_CenS (Subgroup.inv_mem _ hg)
    (key_le_CenS_B h H hA7 hV'2 hV'B hmem)
  simp only [inv_inv] at hCB
  have hCB' : a ∈ CenS B := by
    have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [this] at hCB
  exact ((Z_Vstar_basic h V hV).2).le (Subgroup.mem_inf.2 ⟨haO, hCB'⟩)

end Basic

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
