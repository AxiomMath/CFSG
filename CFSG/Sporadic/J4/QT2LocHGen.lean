module

public import CFSG.Sporadic.J4.QT2LocRadGen
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.J4.QT2

open scoped Pointwise

theorem exists_conj_le_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P K : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hK : IsPGroup p K) : ∃ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ P := by
  obtain ⟨Q, hKQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  have hP' : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] using this.symm
  refine ⟨g, fun k hk => ?_⟩
  rw [hP']
  exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
    ⟨k, hKQ hk, by simp [MulAut.smul_def]⟩

theorem card_modEq_one_of_fpf {G : Type*} [Group G] [Finite G] (x : G) (hx : orderOf x = 5)
    (W : Subgroup G) (hW : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hfpf : ∀ w ∈ W, x * w = w * x → w = 1) : Nat.card W ≡ 1 [MOD 5] := by
  classical
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype W := Fintype.ofFinite W
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  let f : W → W := fun w => ⟨x * w * x⁻¹, hW w w.2⟩
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [f] using this
  let σ : Equiv.Perm W := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
  have hσapp : ∀ w : W, ((σ w : W) : G) = x * w * x⁻¹ := fun w => rfl
  have hσn : ∀ n : ℕ, ∀ w : W, (((σ ^ n) w : W) : G) = x ^ n * w * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', Equiv.Perm.mul_apply, hσapp, ih, pow_succ']
      group
  have hσ5 : σ ^ 5 ^ 1 = 1 := by
    ext w
    rw [pow_one, hσn, hx5]
    simp
  have h1 := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) hσ5
  have h2 : σ.supportᶜ = {1} := by
    ext w
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hw
      apply Subtype.ext
      have h3 : x * (w : G) * x⁻¹ = w := by rw [← hσapp, hw]
      have h4 : x * (w : G) = w * x := by
        calc x * (w : G) = (x * (w : G) * x⁻¹) * x := by group
          _ = w * x := by rw [h3]
      exact hfpf _ w.2 h4
    · rintro rfl
      apply Subtype.ext
      simp [hσapp]
  rw [h2, Finset.card_singleton] at h1
  have hc : Fintype.card W = Nat.card W := (Nat.card_eq_fintype_card).symm
  rw [hc] at h1
  exact h1.symm

theorem eq_bot_or_eq_of_fpf {G : Type*} [Group G] [Finite G] (x : G) (hx : orderOf x = 5)
    (V W : Subgroup G) (hV : Nat.card V = 16) (hWV : W ≤ V)
    (hW : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hfpf : ∀ w ∈ W, x * w = w * x → w = 1) :
    W = ⊥ ∨ W = V := by
  have hmod := card_modEq_one_of_fpf x hx W hW hfpf
  have hdvd : Nat.card W ∣ 16 := hV ▸ Subgroup.card_dvd_of_le hWV
  have hle : Nat.card W ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card W := Nat.card_pos
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at hdvd
  obtain ⟨i, hi, hiW⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · interval_cases i
    · left
      rw [Subgroup.eq_bot_iff_card]
      simpa using hiW
    · exfalso
      rw [hiW] at hmod
      exact absurd hmod (by decide)
    · exfalso
      rw [hiW] at hmod
      exact absurd hmod (by decide)
    · exfalso
      rw [hiW] at hmod
      exact absurd hmod (by decide)
    · right
      exact Subgroup.eq_of_le_of_card_ge hWV (by rw [hiW, hV]; norm_num)
  · omega

theorem exists_conj_into_of_involution {G : Type*} [Group G] [Finite G] (H P : Subgroup G)
    (hPH : P ≤ H) (hP : Nat.card P = 2 ^ (Nat.card H).factorization 2) {h : G} (hh : h ∈ H)
    (h2 : h * h = 1) : ∃ g ∈ H, g * h * g⁻¹ ∈ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : Nat.card (P.subgroupOf H) = 2 ^ (Nat.card ↥H).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv]
    exact hP
  have hsq : (⟨h, hh⟩ : ↥H) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [sq] using h2
  have hK : IsPGroup 2 (Subgroup.zpowers (⟨h, hh⟩ : ↥H)) := by
    have hord : orderOf (⟨h, hh⟩ : ↥H) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hc : Nat.card (Subgroup.zpowers (⟨h, hh⟩ : ↥H)) = orderOf (⟨h, hh⟩ : ↥H) :=
      Nat.card_zpowers _
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h1]; rfl)
  obtain ⟨g, hg⟩ := exists_conj_le_of_card (P.subgroupOf H) (Subgroup.zpowers (⟨h, hh⟩ : ↥H)) hP'
    hK
  refine ⟨g.1, g.2, ?_⟩
  exact Subgroup.mem_subgroupOf.1 (hg _ (Subgroup.mem_zpowers _))

theorem eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | 0, l, h => by
    have : l = [] := List.length_eq_zero_iff.1 (by omega)
    simp [this]
  | n + 1, [], _ => by simp
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨?_, eraseDups_nodup n _ ?_⟩
    · intro hmem
      rw [List.mem_eraseDups, List.mem_filter] at hmem
      simp at hmem
    · exact (List.length_filter_le _ _).trans (by simpa using h)

theorem norm_conj {G : Type*} [Group G] (ξ a b c d e : G) :
    ξ * (a * b * c * d * e) * ξ⁻¹ =
      (ξ * a * ξ⁻¹) * (ξ * b * ξ⁻¹) * (ξ * c * ξ⁻¹) * (ξ * d * ξ⁻¹) * (ξ * e * ξ⁻¹) := by
  group

theorem comm_of_conj_eq {G : Type*} [Group G] {ξ N : G} (h : ξ * N * ξ⁻¹ = N) :
    ξ * N = N * ξ := by
  calc ξ * N = (ξ * N * ξ⁻¹) * ξ := by group
    _ = N * ξ := by rw [h]

theorem eq_one_of_conj_eq_one {G : Type*} [Group G] {h v : G} (e : h⁻¹ * v * h = 1) :
    v = 1 := by
  calc v = h * (h⁻¹ * v * h) * h⁻¹ := by group
    _ = 1 := by rw [e]; group

theorem card_conjSub {G : Type*} [Group G] (c : G) (N : Subgroup G) :
    Nat.card (conjSub c N) = Nat.card N :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem mem_conjSub_of_mem {G : Type*} [Group G] (c : G) {N : Subgroup G} {v : G} (hv : v ∈ N) :
    c * v * c⁻¹ ∈ conjSub c N := by
  rw [mem_conjSub]
  have e : c⁻¹ * (c * v * c⁻¹) * c = v := by group
  rw [e]
  exact hv

theorem comm_rot5 {G : Type*} [Group G] {a b c d e : G} (h1 : a * b = b * a)
    (h2 : a * c = c * a) (h3 : a * d = d * a) (h4 : a * e = e * a) :
    b * c * d * e * a = a * b * c * d * e := by
  calc b * c * d * e * a = b * c * d * (e * a) := by group
    _ = b * c * d * (a * e) := by rw [h4]
    _ = b * c * (d * a) * e := by group
    _ = b * c * (a * d) * e := by rw [h3]
    _ = b * (c * a) * d * e := by group
    _ = b * (a * c) * d * e := by rw [h2]
    _ = (b * a) * c * d * e := by group
    _ = (a * b) * c * d * e := by rw [h1]

theorem conj_step {G : Type*} [Group G] (a v : G) (n : ℕ) :
    a * (a ^ n * v * (a ^ n)⁻¹) * a⁻¹ = a ^ (n + 1) * v * (a ^ (n + 1))⁻¹ := by
  rw [pow_succ']
  group

theorem pow_conj_mem_gen {G : Type*} [Group G] {V : Subgroup G} {x : G}
    (h : ∀ v ∈ V, x * v * x⁻¹ ∈ V) : ∀ n : ℕ, ∀ v ∈ V, x ^ n * v * (x ^ n)⁻¹ ∈ V
  | 0, v, hv => by simpa using hv
  | n + 1, v, hv => by
    have := pow_conj_mem_gen h n _ (h v hv)
    have e : x ^ n * (x * v * x⁻¹) * (x ^ n)⁻¹ = x ^ (n + 1) * v * (x ^ (n + 1))⁻¹ := by
      rw [pow_succ']
      group
    rwa [e] at this

theorem norm_five_eq_one {G : Type*} [Group G] {V : Subgroup G} {ξ v0 : G} (w : ℕ → G)
    (hw : ∀ i, w i = ξ ^ i * v0 * (ξ ^ i)⁻¹) (hξ5 : ξ ^ 5 = 1) (hv0 : v0 ∈ V)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hξV : ∀ v ∈ V, ξ * v * ξ⁻¹ ∈ V)
    (hfpf : ∀ v ∈ V, ξ * v = v * ξ → v = 1) : w 0 * w 1 * w 2 * w 3 * w 4 = 1 := by
  have hwV : ∀ i, w i ∈ V := fun i => by
    rw [hw]
    exact pow_conj_mem_gen hξV i v0 hv0
  have hwsucc : ∀ i, ξ * w i * ξ⁻¹ = w (i + 1) := fun i => by
    rw [hw, hw, conj_step]
  have hw5 : w 5 = w 0 := by
    rw [hw, hw, hξ5]
    simp
  have hcomm : ∀ i j, w i * w j = w j * w i := fun i j => hVab _ (hwV i) _ (hwV j)
  have hNV : w 0 * w 1 * w 2 * w 3 * w 4 ∈ V :=
    V.mul_mem (V.mul_mem (V.mul_mem (V.mul_mem (hwV 0) (hwV 1)) (hwV 2)) (hwV 3)) (hwV 4)
  apply hfpf _ hNV
  have e1 := norm_conj ξ (w 0) (w 1) (w 2) (w 3) (w 4)
  rw [hwsucc, hwsucc, hwsucc, hwsucc, hwsucc, hw5] at e1
  have e2 : w 1 * w 2 * w 3 * w 4 * w 0 = w 0 * w 1 * w 2 * w 3 * w 4 :=
    comm_rot5 (hcomm 0 1) (hcomm 0 2) (hcomm 0 3) (hcomm 0 4)
  exact comm_of_conj_eq (e1.trans e2)

end CFSG.Sporadic.J4.QT2
