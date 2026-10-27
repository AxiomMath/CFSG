module

public import CFSG.Walter.W67.Section5.Free
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

public section

namespace CFSG.Walter.W67

open Finset

namespace Sec52

variable {G : Type*} [Group G]

@[expose] def conjP (P₁ : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (P₁ : Set G)) :
    P₁ →* P₁ where
  toFun u := ⟨x * u * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx u).mp u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

theorem card_pow_eq_one_mul_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {P₁ : Subgroup G}
    (hab : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a) (hexp : ∀ a ∈ P₁, a ^ p = 1) {x : G}
    (hxN : x ∈ Subgroup.normalizer (P₁ : Set G)) (hxp : x ^ p = 1)
    (hC : Nat.card (P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ p)
    (hcard : p ^ p ≤ Nat.card P₁) :
    Nat.card {u : P₁ // (x * u) ^ p = 1} * p ≤ Nat.card P₁ := by
  have hcomm : IsMulCommutative P₁ := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  let : CommGroup P₁ := { (inferInstance : Group P₁) with mul_comm := hcomm.is_comm.comm }
  let M := Additive P₁
  let T : Module.End ℤ M := (MonoidHom.toAdditive (conjP P₁ hxN)).toIntLinearMap
  let ι : M → G := fun m => ((Additive.toMul m : P₁) : G)
  have hι0 : ι 0 = 1 := rfl
  have hιadd : ∀ a b : M, ι (a + b) = ι a * ι b := fun a b => rfl
  have hιnsmul : ∀ (n : ℕ) (a : M), ι (n • a) = ι a ^ n := fun n a => by
    induction n with
    | zero => simp [hι0]
    | succ n ih => rw [succ_nsmul, hιadd, ih, pow_succ]
  have hιinj : Function.Injective ι := fun a b h => Additive.toMul.injective (Subtype.ext h)
  have hιT : ∀ m : M, ι (T m) = x * ι m * x⁻¹ := fun m => rfl
  have hιTpow : ∀ (k : ℕ) (m : M), ι ((T ^ k) m) = x ^ k * ι m * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ', Module.End.mul_apply, hιT, ih]
      group
  have hstep : ∀ (n : ℕ) (m : M),
      (x * ι m) ^ n = ι ((∑ i ∈ range n, T ^ (i + 1)) m) * x ^ n := by
    intro n m
    induction n with
    | zero => simp [hι0]
    | succ n ih =>
      rw [pow_succ, ih, sum_range_succ, LinearMap.add_apply, hιadd, hιTpow]
      group
  have hTp : T ^ p = 1 := by
    refine LinearMap.ext fun m => hιinj ?_
    rw [hιTpow, hxp, Module.End.one_apply]
    group
  set N := ∑ i ∈ range p, T ^ i with hNdef
  have hshift : ∑ i ∈ range p, T ^ (i + 1) = N := by
    have h1 := sum_range_succ' (fun i => T ^ i) p
    have h2 := sum_range_succ (fun i => T ^ i) p
    simp only [pow_zero, hTp] at h1 h2
    exact add_right_cancel (h1.symm.trans h2)
  have hnorm : ∀ m : M, (x * ι m) ^ p = ι (N m) := by
    intro m
    rw [hstep, hxp, mul_one, hshift]
  have hM : ∀ m : M, p • m = 0 := by
    intro m
    apply hιinj
    rw [hιnsmul, hι0]
    exact hexp _ (Additive.toMul m).2
  have hMcard : Nat.card M = Nat.card P₁ := rfl
  have hp1 : 1 < Nat.card P₁ :=
    lt_of_lt_of_le (Nat.one_lt_pow hp.out.ne_zero hp.out.one_lt) hcard
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp hp1
  have := Free.charP_end hM
  have hNT : N = (T - 1) ^ (p - 1) := by
    have h := Free.geom_sum_eq_sub_one_pow (p := p) T 1
    simpa only [pow_one] using h
  have hmemC : ∀ m : Free.kerE (T - 1),
      ι m ∈ (P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    intro ⟨m, hm⟩
    refine Subgroup.mem_inf.mpr ⟨(Additive.toMul m).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (T - 1) m = 0 := hm
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    have h3 := congrArg ι h1
    rw [hιT] at h3
    calc ι m * x = (x * ι m * x⁻¹) * x := by rw [h3]
      _ = x * ι m := by group
  have hker1 : Nat.card (Free.kerE (T - 1)) ≤ p :=
    le_trans (Nat.card_le_card_of_injective
      (fun m => (⟨ι m, hmemC m⟩ : (P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)))
      (fun a b hab => by
        have h : ι a = ι b := congrArg
          (fun z : (P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) => (z : G)) hab
        exact Subtype.ext (hιinj h))) hC
  have hNtop : Free.kerE N ≠ ⊤ := by
    intro htop
    have h1 := Free.card_kerE_pow_le (T - 1) (p - 1)
    rw [← hNT, htop, AddSubgroup.card_top] at h1
    have h2 : Nat.card (Free.kerE (T - 1)) ^ (p - 1) ≤ p ^ (p - 1) := Nat.pow_le_pow_left hker1 _
    have h3 : p ^ (p - 1) < p ^ p :=
      Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt hp.out.pos one_pos)
    rw [hMcard] at h1
    omega
  have hE : Nat.card {u : P₁ // (x * u) ^ p = 1} = Nat.card (Free.kerE N) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => ?_)
    change (x * u) ^ p = 1 ↔ N (Additive.ofMul u) = 0
    have h := hnorm (Additive.ofMul u)
    change (x * ↑u) ^ p = ι (N (Additive.ofMul u)) at h
    rw [h]
    constructor
    · intro h'
      exact hιinj (h'.trans hι0.symm)
    · intro h'
      rw [h', hι0]
  have hPp : IsPGroup p P₁ := fun g => ⟨1, Subtype.ext (by simpa using hexp _ g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
  have hidx := AddSubgroup.card_mul_index (Free.kerE N)
  have hidx1 : (Free.kerE N).index ≠ 1 := fun h => hNtop (AddSubgroup.index_eq_one.mp h)
  have hidxdvd : (Free.kerE N).index ∣ Nat.card M := AddSubgroup.index_dvd_card _
  rw [hMcard, hn] at hidxdvd
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp.out).mp hidxdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hjeq
    exact hidx1 hjeq
  have hple : p ≤ (Free.kerE N).index := by
    rw [hjeq]
    exact Nat.le_self_pow hj0 p
  rw [hE]
  calc Nat.card (Free.kerE N) * p ≤ Nat.card (Free.kerE N) * (Free.kerE N).index :=
        Nat.mul_le_mul_left _ hple
    _ = Nat.card M := hidx
    _ = Nat.card P₁ := hMcard

theorem card_sup_mul_card_inf [Finite G] {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) = Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h2, h3, ← h5, ← h4, mul_comm (Nat.card _) (Nat.card A), mul_assoc, ← h1]

omit [Group G] in
theorem card_le_mul_card_inf [Group G] [Finite G] {Q P₁ A : Subgroup G} (hAQ : A ≤ Q) :
    Nat.card A ≤ P₁.relIndex Q * Nat.card (P₁ ⊓ A : Subgroup G) := by
  have h1 := Subgroup.card_mul_index (P₁.subgroupOf A)
  have h2 : Nat.card (P₁.subgroupOf A) = Nat.card (P₁ ⊓ A : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h3 : P₁.relIndex A ≤ P₁.relIndex Q := by
    apply Subgroup.relIndex_le_of_le_right hAQ
    intro h0
    have h4 := Subgroup.card_mul_index (P₁.subgroupOf Q)
    rw [Subgroup.relIndex] at h0
    rw [h0, mul_zero] at h4
    exact Nat.card_pos.ne' h4.symm
  rw [h2] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ h3

theorem eq_of_comm [Finite G] {p : ℕ} [hp : Fact p.Prime] {Q P₁ A : Subgroup G} {x : G}
    (hP₁Q : P₁ ≤ Q) (hAQ : A ≤ Q) (hxQ : x ∈ Q) (hrel : P₁.relIndex Q = p)
    (hAcard : Nat.card A = Nat.card P₁)
    (hP₁ab : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ p ^ 2)
    (hbig : p ^ 3 < Nat.card P₁) : A = P₁ := by
  by_contra hne
  have hsup : Q ≤ A ⊔ P₁ := by
    have hmul := Subgroup.relIndex_mul_relIndex P₁ (A ⊔ P₁) Q le_sup_right (sup_le hAQ hP₁Q)
    rw [hrel] at hmul
    have hpr : (P₁.relIndex (A ⊔ P₁) * (A ⊔ P₁).relIndex Q).Prime := by rw [hmul]; exact hp.out
    rcases Nat.prime_mul_iff.mp hpr with ⟨-, h⟩ | ⟨-, h⟩
    · exact Subgroup.relIndex_eq_one.mp h
    · exfalso
      have hAP : A ≤ P₁ := le_sup_left.trans (Subgroup.relIndex_eq_one.mp h)
      exact hne (Subgroup.eq_of_le_of_card_ge hAP (le_of_eq hAcard.symm))
  have hinf : P₁ ⊓ A ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    obtain ⟨hzP, hzA⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hP₁Q hzP, ?_⟩
    have hle : A ⊔ P₁ ≤ Subgroup.centralizer ({z} : Set G) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hAab a ha z hzA
      · intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hP₁ab a ha z hzP
    have hx := Subgroup.mem_centralizer_singleton_iff.mp (hle (hsup hxQ))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx.symm
  have h1 := card_le_mul_card_inf (P₁ := P₁) hAQ
  have h2 := Subgroup.card_le_of_le hinf
  rw [hrel, hAcard] at h1
  have h3 : p * Nat.card (P₁ ⊓ A : Subgroup G) ≤ p * p ^ 2 :=
    Nat.mul_le_mul_left _ (h2.trans hCx)
  have h4 : p * p ^ 2 = p ^ 3 := by ring
  omega

theorem card_le_of_conj_mem [Finite G] {p : ℕ} {P₁ R : Subgroup G} {x : G} (hxp : x ^ p = 1)
    (hR : ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ P₁) :
    Nat.card R ≤ Nat.card {u : P₁ // (x * u) ^ p = 1} *
      Nat.card (R ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  set C := (Subgroup.centralizer ({x} : Set G)).subgroupOf R
  have hC : Nat.card C = Nat.card (R ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rw [show C = (Subgroup.centralizer ({x} : Set G) ⊓ R).subgroupOf R from
      (Subgroup.inf_subgroupOf_right _ _).symm, inf_comm R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hconj : ∀ a b : R, ((a⁻¹ * b : R) : G) ∈ Subgroup.centralizer ({x} : Set G) ↔
      (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ := by
    intro a b
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (a : G) * x * (a : G)⁻¹ =
            (a : G) * (((a : G)⁻¹ * b) * x * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by
            rw [h]; group
        _ = b * x * (b : G)⁻¹ := by group
    · intro h
      calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * (b * x * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * (a * x * (a : G)⁻¹) * b := by rw [h]
        _ = x * ((a : G)⁻¹ * b) := by group
  let ψ₀ : R → {u : P₁ // (x * u) ^ p = 1} := fun r =>
    ⟨⟨x⁻¹ * ((r : G) * x * (r : G)⁻¹), hR r r.2⟩, by
    change (x * (x⁻¹ * ((r : G) * x * (r : G)⁻¹))) ^ p = 1
    rw [mul_inv_cancel_left, conj_pow, hxp]
    group⟩
  let ψ : R ⧸ C → {u : P₁ // (x * u) ^ p = 1} := Quotient.lift ψ₀ (fun a b hab => by
    have hab' : a⁻¹ * b ∈ C := QuotientGroup.leftRel_apply.mp hab
    have h := (hconj a b).mp hab'
    apply Subtype.ext
    apply Subtype.ext
    change x⁻¹ * ((a : G) * x * (a : G)⁻¹) = x⁻¹ * ((b : G) * x * (b : G)⁻¹)
    rw [h])
  have hψ : Function.Injective ψ := by
    intro q₁ q₂ h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
    have h' : x⁻¹ * ((a : G) * x * (a : G)⁻¹) = x⁻¹ * ((b : G) * x * (b : G)⁻¹) :=
      congrArg (fun u : {u : P₁ // (x * u) ^ p = 1} => ((u.1 : P₁) : G)) h
    rw [QuotientGroup.eq]
    exact (hconj a b).mpr (mul_left_cancel h')
  have h1 := Nat.card_le_card_of_injective ψ hψ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hC]
  exact Nat.mul_le_mul_right _ h1

structure Hyp52 (p : ℕ) (P₁ : Subgroup G) (x : G) : Prop where
  comm : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a
  exp : ∀ a ∈ P₁, a ^ p = 1
  normalizes : x ∈ Subgroup.normalizer (P₁ : Set G)
  orderOf_x : orderOf x = p
  card_fix : Nat.card (P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ p
  card_le : p ^ p ≤ Nat.card P₁
  card_big : p ^ 3 < Nat.card P₁
  centralizer : ∀ R : Subgroup G, IsPGroup p R → x ∈ R →
    Nat.card (R ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ p ^ 2

namespace Hyp52

variable [Finite G] {p : ℕ} [hp : Fact p.Prime] {P₁ : Subgroup G} {x : G} (h : Hyp52 p P₁ x)
include h

omit [Finite G] hp in
theorem isPGroup : IsPGroup p P₁ := fun g => ⟨1, Subtype.ext (by simpa using h.exp _ g.2)⟩

omit [Finite G] hp in
theorem pow_x : x ^ p = 1 := h.orderOf_x ▸ pow_orderOf_eq_one x

omit hp in
theorem not_mem : x ∉ P₁ := by
  intro hx
  have hle : P₁ ≤ P₁ ⊓ Subgroup.centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (h.comm a ha x hx)⟩
  have h1 := Subgroup.card_le_of_le hle
  have h2 := h.card_fix
  have h3 := h.card_big
  have h4 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
  omega

theorem inf_zpowers : P₁ ⊓ Subgroup.zpowers x = ⊥ := by
  have hdvd : Nat.card (P₁ ⊓ Subgroup.zpowers x : Subgroup G) ∣ p := by
    rw [← h.orderOf_x, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply h.not_mem
    have heq : P₁ ⊓ Subgroup.zpowers x = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right
      rw [h1, Nat.card_zpowers, h.orderOf_x]
    have hx : x ∈ P₁ ⊓ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hx).1

theorem card_Q : Nat.card (P₁ ⊔ Subgroup.zpowers x : Subgroup G) = p * Nat.card P₁ := by
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (P₁ : Set G) :=
    Subgroup.zpowers_le.mpr h.normalizes
  have h1 := card_sup_mul_card_inf hN
  rw [h.inf_zpowers, Subgroup.card_bot, mul_one, Nat.card_zpowers, h.orderOf_x,
    sup_comm] at h1
  rw [h1, mul_comm]

theorem relIndex : P₁.relIndex (P₁ ⊔ Subgroup.zpowers x) = p := by
  have h1 := Subgroup.card_mul_index (P₁.subgroupOf (P₁ ⊔ Subgroup.zpowers x))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, h.card_Q] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans (mul_comm _ _))

theorem isPGroup_Q : IsPGroup p (P₁ ⊔ Subgroup.zpowers x : Subgroup G) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.isPGroup
  apply IsPGroup.of_card (n := n + 1)
  rw [h.card_Q, hn, pow_succ, mul_comm]

theorem eq_of_le {A : Subgroup G} (hAQ : A ≤ P₁ ⊔ Subgroup.zpowers x)
    (hAcard : Nat.card A = Nat.card P₁) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = P₁ :=
  eq_of_comm le_sup_left hAQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) h.relIndex
    hAcard h.comm hAab
    (h.centralizer _ h.isPGroup_Q (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))) h.card_big

theorem conj_eq {g : G} (hg : P₁.map (MulAut.conj g).toMonoidHom ≤ P₁ ⊔ Subgroup.zpowers x) :
    P₁.map (MulAut.conj g).toMonoidHom = P₁ := by
  apply h.eq_of_le hg (Subgroup.card_map_of_injective (MulAut.conj g).injective)
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
    _ = g * (b' * a') * g⁻¹ := by rw [h.comm a' ha' b' hb']
    _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group

theorem card_Q_eq :
    Nat.card (P₁ ⊔ Subgroup.zpowers x : Subgroup G) = p ^ (Nat.card G).factorization p := by
  set Q := P₁ ⊔ Subgroup.zpowers x with hQdef
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.isPGroup
  have hQ : Nat.card Q = p ^ (n + 1) := by rw [h.card_Q, hn, pow_succ, mul_comm]
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ^ (n + 1) ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card _
  have hndvd : ¬ p ^ (n + 1 + 1) ∣ Nat.card G := by
    intro hdvd2
    obtain ⟨K, hK, hQK⟩ := Sylow.exists_subgroup_card_pow_succ hdvd2 hQ
    have hxK : x ∈ K := hQK (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hP₁K : P₁ ≤ K := le_sup_left.trans hQK
    have hQidx : (Q.subgroupOf K).index = p := by
      have h1 := Subgroup.card_mul_index (Q.subgroupOf K)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hQ, hK,
        pow_succ p (n + 1)] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h1
    have hQn : (Q.subgroupOf K).Normal := by
      apply Subgroup.normal_of_index_eq_minFac_card
      rw [hQidx, hK, Nat.Prime.pow_minFac hp.out (by omega)]
    have hKQ : ∀ k ∈ K, ∀ y ∈ Q, k * y * k⁻¹ ∈ Q := by
      intro k hk y hy
      exact Subgroup.mem_subgroupOf.mp (hQn.conj_mem ⟨y, hQK hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
        ⟨k, hk⟩)
    have hKP : ∀ k ∈ K, ∀ u ∈ P₁, k * u * k⁻¹ ∈ P₁ := by
      intro k hk u hu
      have hle : P₁.map (MulAut.conj k).toMonoidHom ≤ Q := by
        intro y hy
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
        exact hKQ k hk v (Subgroup.mem_sup_left hv)
      have hmem : k * u * k⁻¹ ∈ P₁.map (MulAut.conj k).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [h.conj_eq hle] at hmem
    have hPn : (P₁.subgroupOf K).Normal :=
      ⟨fun a ha k => Subgroup.mem_subgroupOf.mpr (hKP k k.2 a (Subgroup.mem_subgroupOf.mp ha))⟩
    have hcardq : Nat.card (K ⧸ P₁.subgroupOf K) = p ^ 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P₁.subgroupOf K)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁K).toEquiv, hK, hn,
        show n + 1 + 1 = 2 + n by ring, pow_add] at h1
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos _) h1.symm
    have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardq
    have hR : ∀ r ∈ K, x⁻¹ * (r * x * r⁻¹) ∈ P₁ := by
      intro r hr
      have hc := hab.is_comm.comm (QuotientGroup.mk (⟨r, hr⟩ : K)⁻¹ : K ⧸ P₁.subgroupOf K)
        (QuotientGroup.mk ⟨x, hxK⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
      have h1 := Subgroup.mem_subgroupOf.mp hc
      have h2 : (((⟨r, hr⟩ : K)⁻¹ * ⟨x, hxK⟩)⁻¹ * (⟨x, hxK⟩ * (⟨r, hr⟩ : K)⁻¹) : K) =
          (x⁻¹ * (r * x * r⁻¹) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [h2] at h1
    have h1 := card_le_of_conj_mem (P₁ := P₁) (R := K) h.pow_x hR
    have h2 := card_pow_eq_one_mul_le h.comm h.exp h.normalizes h.pow_x h.card_fix h.card_le
    have h3 := h.centralizer K (IsPGroup.of_card hK) hxK
    have h4 : Nat.card K * p ≤ Nat.card P₁ * p ^ 2 :=
      calc Nat.card K * p ≤ (Nat.card {u : P₁ // (x * u) ^ p = 1} *
            Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) * p :=
            Nat.mul_le_mul_right _ h1
        _ = (Nat.card {u : P₁ // (x * u) ^ p = 1} * p) *
            Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by ring
        _ ≤ Nat.card P₁ * p ^ 2 := Nat.mul_le_mul h2 h3
    rw [hK, hn] at h4
    have h5 : p ^ n * p ^ 2 < p ^ (n + 1 + 1) * p :=
      calc p ^ n * p ^ 2 = p ^ (n + 1 + 1) := by ring
        _ < p ^ (n + 1 + 1) * p := lt_mul_of_one_lt_right (pow_pos hp.out.pos _) hp.out.one_lt
    omega
  rw [hQ]
  congr 1
  have h1 := (hp.out.pow_dvd_iff_le_factorization hG0).mp hdvd
  have h2 : ¬ n + 1 + 1 ≤ (Nat.card G).factorization p := fun hle =>
    hndvd ((hp.out.pow_dvd_iff_le_factorization hG0).mpr hle)
  omega

theorem inf_centralizer :
    (P₁ ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer (P₁ : Set G) = P₁ := by
  set Q := P₁ ⊔ Subgroup.zpowers x
  have hle : P₁ ≤ Q ⊓ Subgroup.centralizer (P₁ : Set G) :=
    le_inf le_sup_left (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm b hb a ha)
  have hmul := Subgroup.relIndex_mul_relIndex P₁ (Q ⊓ Subgroup.centralizer (P₁ : Set G)) Q hle
    inf_le_left
  rw [h.relIndex] at hmul
  have hpr : (P₁.relIndex (Q ⊓ Subgroup.centralizer (P₁ : Set G)) *
      (Q ⊓ Subgroup.centralizer (P₁ : Set G)).relIndex Q).Prime := by
    rw [hmul]; exact hp.out
  rcases Nat.prime_mul_iff.mp hpr with ⟨-, h1⟩ | ⟨-, h1⟩
  · exfalso
    have hx : x ∈ Subgroup.centralizer (P₁ : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.relIndex_eq_one.mp h1
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))).2
    have hle2 : P₁ ≤ P₁ ⊓ Subgroup.centralizer ({x} : Set G) := fun a ha =>
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx a ha)⟩
    have h2 := Subgroup.card_le_of_le hle2
    have h3 := h.card_fix
    have h4 := h.card_big
    have h5 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
    omega
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle

theorem weaklyClosedIn :
    BenderSuzuki.External.WeaklyClosedIn (P₁ ⊔ Subgroup.zpowers x) P₁ :=
  ⟨le_sup_left, fun g hg => h.conj_eq (g := g⁻¹) hg⟩

theorem card_le_of_le_centralizer {S : Subgroup G} (hS : IsPGroup p S)
    (hSC : S ≤ Subgroup.centralizer (P₁ : Set G)) : Nat.card S ≤ Nat.card P₁ := by
  set Q := P₁ ⊔ Subgroup.zpowers x
  let P : Sylow p G := Sylow.ofCard Q h.card_Q_eq
  have hSP : IsPGroup p (S ⊔ P₁ : Subgroup G) :=
    hS.to_sup_of_normal_right' h.isPGroup (hSC.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨P', hP'⟩ := hSP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  have hle : ∀ y ∈ S ⊔ P₁, g * y * g⁻¹ ∈ Q := by
    intro y hy
    have hmem : g * y * g⁻¹ ∈ ((g • P' : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨y, hP' hy, rfl⟩
    rw [hg] at hmem
    exact hmem
  have hP₁ : P₁.map (MulAut.conj g).toMonoidHom = P₁ := h.conj_eq (by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    exact hle v (Subgroup.mem_sup_right hv))
  have hSle : S.map (MulAut.conj g).toMonoidHom ≤ P₁ := by
    rw [← h.inf_centralizer]
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_inf.mpr ⟨hle v (Subgroup.mem_sup_left hv), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hP₁] at hb
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hcv := Subgroup.mem_centralizer_iff.mp (hSC hv) c hc
    calc g * c * g⁻¹ * (g * v * g⁻¹) = g * (c * v) * g⁻¹ := by group
      _ = g * (v * c) * g⁻¹ := by rw [hcv]
      _ = g * v * g⁻¹ * (g * c * g⁻¹) := by group
  have h1 := Subgroup.card_le_of_le hSle
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1

end Hyp52

theorem iterated_eq_one {u z : G} (huz : u * z = z * u) : ∀ k : ℕ,
    BenderSuzuki.External.iteratedInverseFirstCommutator (k + 1) u z = 1
  | 0 => by
    change u⁻¹ * z⁻¹ * u * z = 1
    calc u⁻¹ * z⁻¹ * u * z = u⁻¹ * z⁻¹ * (u * z) := by group
      _ = u⁻¹ * z⁻¹ * (z * u) := by rw [huz]
      _ = 1 := by group
  | k + 1 => by
    change BenderSuzuki.External.inverseFirstCommutator
      (BenderSuzuki.External.iteratedInverseFirstCommutator (k + 1) u z) z = 1
    rw [iterated_eq_one huz k]
    change (1 : G)⁻¹ * z⁻¹ * 1 * z = 1
    group

theorem hallPResidual_eq_top [Finite G] {p : ℕ} [Fact p.Prime] (hperf : commutator G = ⊤) :
    BenderSuzuki.External.hallPResidual p G = ⊤ := by
  let := BenderSuzuki.External.hallPResidual_normal p G
  set N := BenderSuzuki.External.hallPResidual p G
  have hP : IsPGroup p (G ⧸ N) := BenderSuzuki.External.hallPResidual_quotient_isPGroup p
  have hnil := hP.isNilpotent
  have hcomm : commutator (G ⧸ N) = ⊤ := by
    have hsurj := QuotientGroup.mk'_surjective N
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator,
      ← commutator_def, hperf]
  have hlcs : ∀ n, (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Subgroup.lowerCentralSeries_succ, ih, ← commutator_def, hcomm]
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  rw [hlcs] at hn
  rw [eq_top_iff]
  intro g _
  have hg : (QuotientGroup.mk g : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hg
  exact hg

end Sec52

end CFSG.Walter.W67
