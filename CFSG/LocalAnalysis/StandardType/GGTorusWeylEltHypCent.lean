module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.GroupTheory.SubnormalOddInversion
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {L' : Type} [Group L']

private theorem conj_apply_mulAut (a : MulAut L') (x : L') :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  ext g
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem mem_center_of_conj_eq_one {z : L'} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center L' := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : z * g * z⁻¹ = g := by
    have := congrArg (fun f : MulAut L' => f g) h
    simpa only [MulAut.conj_apply, MulAut.one_apply] using this
  calc g * z = z * g * z⁻¹ * z := by rw [hg]
    _ = z * g := by group

private theorem exists_center_of_conj_eq {x y : L'} (h : MulAut.conj x = MulAut.conj y) :
    ∃ z ∈ Subgroup.center L', x = y * z :=
  ⟨y⁻¹ * x, mem_center_of_conj_eq_one (by rw [map_mul, map_inv, h, inv_mul_cancel]),
    by group⟩

theorem ggTorusWeylElt_of_mem_ggHypCent [Finite L'] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection p (ggConjAut A hn)) (hnH : n ∈ ggHypCent A n) :
    GGTorusWeylElt p A n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut L') := Finite.of_injective (fun e : MulAut L' => (e : L' → L'))
    (fun e e' h => MulEquiv.ext (congrFun h))
  obtain ⟨c, hcdef⟩ : ∃ c, MulAut.conj n = c := ⟨_, rfl⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hcA : ∀ x ∈ A, c * x * c⁻¹ ∈ A := fun x hx => by
    have h := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
    rwa [hcdef] at h
  have hdA : ∀ x ∈ A, c * x * c⁻¹ * x⁻¹ ∈ A := fun x hx => A.mul_mem (hcA x hx) (A.inv_mem hx)
  have hφ2 : ∀ x ∈ A, c * (c * x * c⁻¹) * c⁻¹ = x := by
    intro x hx
    have h := congrArg (fun f : MulAut ↥A => ((f ⟨x, hx⟩ : ↥A) : MulAut L')) hφ.1
    simpa only [pow_two, MulAut.mul_apply, ggConjAut_apply, MulAut.one_apply, hcdef] using h
  have hfixn : ∀ x ∈ A, c * x = x * c → x n = n := by
    intro x hx hxc
    have h := hnH
    simp only [ggHypCent, Subgroup.mem_iInf, mem_ggFix, hcdef] at h
    exact h x ⟨hx, hxc⟩
  have hconjy : ∀ x : MulAut L', MulAut.conj (n * (x n)⁻¹) = c * x * c⁻¹ * x⁻¹ := by
    intro x
    rw [map_mul, map_inv, conj_apply_mulAut, hcdef]
    group
  have hinvd : ∀ x ∈ A, c * (c * x * c⁻¹ * x⁻¹) * c⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by
    intro x hx
    calc c * (c * x * c⁻¹ * x⁻¹) * c⁻¹ = c * (c * x * c⁻¹) * c⁻¹ * (c * x⁻¹ * c⁻¹) := by group
      _ = x * (c * x⁻¹ * c⁻¹) := by rw [hφ2 x hx]
      _ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
  obtain ⟨j, h2j⟩ : ∃ j : ℕ, 2 * j = p + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    exact ⟨k + 1, by omega⟩
  have hf : ∀ x ∈ A, x n = ((n * (x n)⁻¹) ^ j)⁻¹ * n * (n * (x n)⁻¹) ^ j := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y, y = n * (x n)⁻¹ := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = c * x * c⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hy]
    have hdA' : d ∈ A := by rw [hd]; exact hdA x hx
    have hconj : MulAut.conj y = d := by rw [hy, hd]; exact hconjy x
    have hdp : d ^ p = 1 := hA.2 d hdA'
    have hcx : c * x * c⁻¹ = d * x := by rw [hd]; group
    have hcd : c * d * c⁻¹ = d⁻¹ := by rw [hd]; exact hinvd x hx
    have hdj : d * (d⁻¹) ^ j = d ^ j := by
      have hjj : d ^ j * d ^ j = d := by
        rw [← pow_add, ← two_mul, h2j, pow_succ, hdp, one_mul]
      calc d * (d⁻¹) ^ j = d ^ j * d ^ j * (d ^ j)⁻¹ := by rw [hjj, inv_pow]
        _ = d ^ j := by group
    have hxd : x * d = d * x := hcomm x hx d hdA'
    have h1 : c * (x * d ^ j) * c⁻¹ = x * d ^ j := by
      calc c * (x * d ^ j) * c⁻¹ = (c * x * c⁻¹) * (c * d * c⁻¹) ^ j := by
            rw [conj_pow]; group
        _ = d * x * (d⁻¹) ^ j := by rw [hcx, hcd]
        _ = x * (d * (d⁻¹) ^ j) := by rw [← hxd]; group
        _ = x * d ^ j := by rw [hdj]
    have hfix' : c * (x * d ^ j) = x * d ^ j * c := by
      calc c * (x * d ^ j) = c * (x * d ^ j) * c⁻¹ * c := by group
        _ = x * d ^ j * c := by rw [h1]
    have hxn : (x * d ^ j) n = n := hfixn _ (A.mul_mem hx (A.pow_mem hdA' j)) hfix'
    have hdjn : (d ^ j) n = y ^ j * n * (y ^ j)⁻¹ := by
      rw [← hconj, ← map_pow, MulAut.conj_apply]
    obtain ⟨z, hz, hxy⟩ := exists_center_of_conj_eq (x := x y) (y := y) (by
      rw [conj_apply_mulAut, hconj, hxd, mul_inv_cancel_right])
    have hzc : ∀ g : L', g * z ^ j = z ^ j * g :=
      Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz j)
    have hyz : Commute y z := Subgroup.mem_center_iff.mp hz y
    have key : y ^ j * x n * (y ^ j)⁻¹ = n := by
      have h := hxn
      rw [MulAut.mul_apply, hdjn, map_mul, map_mul, map_inv, map_pow, hxy, hyz.mul_pow] at h
      calc y ^ j * x n * (y ^ j)⁻¹ = y ^ j * (x n * z ^ j) * (z ^ j)⁻¹ * (y ^ j)⁻¹ := by group
        _ = y ^ j * (z ^ j * x n) * (z ^ j)⁻¹ * (y ^ j)⁻¹ := by rw [hzc]
        _ = y ^ j * z ^ j * x n * (y ^ j * z ^ j)⁻¹ := by group
        _ = n := h
    calc x n = (y ^ j)⁻¹ * (y ^ j * x n * (y ^ j)⁻¹) * y ^ j := by group
      _ = (y ^ j)⁻¹ * n * y ^ j := by rw [key]
  unfold GGTorusWeylElt
  intro a ha
  obtain ⟨y, hy⟩ : ∃ y, y = n * (a n)⁻¹ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = c * a * c⁻¹ * a⁻¹ := ⟨_, rfl⟩
  rw [← hy]
  have hdA' : d ∈ A := by rw [hd]; exact hdA a ha
  have hconj : MulAut.conj y = d := by rw [hy, hd]; exact hconjy a
  have hcd : c * d * c⁻¹ = d⁻¹ := by rw [hd]; exact hinvd a ha
  have han : a n = (y ^ j)⁻¹ * n * y ^ j := by rw [hy]; exact hf a ha
  obtain ⟨z, hz, hnyn⟩ := exists_center_of_conj_eq (x := n * y * n⁻¹) (y := y⁻¹) (by
    rw [map_mul, map_mul, map_inv, map_inv, hconj, hcdef]
    exact hcd)
  have hyz : Commute y z := Subgroup.mem_center_iff.mp hz y
  have hyiz : Commute y⁻¹ z := hyz.inv_left
  have e1 : y ^ p = z ^ j := by
    have h1 : n * (y ^ j)⁻¹ * n⁻¹ = (z ^ j)⁻¹ * y ^ j := by
      have h0 : n * y ^ j * n⁻¹ = (y⁻¹) ^ j * z ^ j := by
        rw [← conj_pow, hnyn, hyiz.mul_pow]
      calc n * (y ^ j)⁻¹ * n⁻¹ = (n * y ^ j * n⁻¹)⁻¹ := by group
        _ = ((y⁻¹) ^ j * z ^ j)⁻¹ := by rw [h0]
        _ = (z ^ j)⁻¹ * y ^ j := by rw [mul_inv_rev, inv_pow, inv_inv]
    have h2 : y = (z ^ j)⁻¹ * y ^ p * y := by
      calc y = n * (a n)⁻¹ := hy
        _ = n * ((y ^ j)⁻¹ * n * y ^ j)⁻¹ := by rw [han]
        _ = n * (y ^ j)⁻¹ * n⁻¹ * y ^ j := by group
        _ = (z ^ j)⁻¹ * y ^ j * y ^ j := by rw [h1]
        _ = (z ^ j)⁻¹ * y ^ (2 * j) := by rw [mul_assoc, ← pow_add, two_mul]
        _ = (z ^ j)⁻¹ * y ^ p * y := by rw [h2j, pow_succ, mul_assoc]
    calc y ^ p = z ^ j * ((z ^ j)⁻¹ * y ^ p * y) * y⁻¹ := by group
      _ = z ^ j * y * y⁻¹ := by rw [← h2]
      _ = z ^ j := by group
  have hypc : y ^ p ∈ Subgroup.center L' :=
    mem_center_of_conj_eq_one (by rw [map_pow, hconj, hA.2 d hdA'])
  have e2 : y ^ p * y ^ p = z ^ p := by
    have h4 : n * y ^ p * n⁻¹ = y ^ p := by
      rw [Subgroup.mem_center_iff.mp hypc n]
      group
    have h5 : n * y ^ p * n⁻¹ = (y⁻¹) ^ p * z ^ p := by
      rw [← conj_pow, hnyn, hyiz.mul_pow]
    calc y ^ p * y ^ p = y ^ p * ((y⁻¹) ^ p * z ^ p) := by rw [← h5, h4]
      _ = z ^ p := by rw [inv_pow]; group
  have hz1 : z = 1 := by
    have h6 : z ^ j * z ^ j = z ^ p := by rw [← e1, e2]
    have h7 : z ^ p * z = z ^ p := by
      rw [← pow_succ, ← h2j, two_mul, pow_add, h6]
    exact mul_left_cancel (a := z ^ p) (by rw [h7, mul_one])
  refine ⟨by rw [e1, hz1, one_pow], fun b hb => ?_⟩
  by_cases hd1 : d = 1
  ·
    have hca : c * a = a * c := by
      have h0 : c * a * c⁻¹ * a⁻¹ = 1 := by rw [← hd]; exact hd1
      calc c * a = c * a * c⁻¹ * a⁻¹ * (a * c) := by group
        _ = a * c := by rw [h0, one_mul]
    have hy1 : y = 1 := by rw [hy, hfixn a ha hca, mul_inv_cancel]
    rw [hy1, map_one]
  have hδmem : ∀ x : ↥A, c * (x : MulAut L') * c⁻¹ * (x : MulAut L')⁻¹ ∈ A :=
    fun x => hdA x x.2
  let δ : ↥A →* ↥A :=
    { toFun := fun x => ⟨c * x * c⁻¹ * (x : MulAut L')⁻¹, hδmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x x' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        have hc' : (x : MulAut L')⁻¹ * (c * x' * c⁻¹ * (x' : MulAut L')⁻¹) =
            (c * x' * c⁻¹ * (x' : MulAut L')⁻¹) * (x : MulAut L')⁻¹ :=
          hcomm _ (A.inv_mem x.2) _ (hδmem x')
        calc c * (↑x * ↑x') * c⁻¹ * (↑x * ↑x')⁻¹
            = c * ↑x * c⁻¹ * ((c * ↑x' * c⁻¹ * (↑x')⁻¹) * (↑x)⁻¹) := by group
          _ = c * ↑x * c⁻¹ * ((↑x)⁻¹ * (c * ↑x' * c⁻¹ * (↑x')⁻¹)) := by rw [hc']
          _ = c * ↑x * c⁻¹ * (↑x)⁻¹ * (c * ↑x' * c⁻¹ * (↑x')⁻¹) := by group) }
  have hker : Nat.card δ.ker * p = Nat.card ↥A := by
    rw [← hφ.2]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MonoidHom.mem_ker, Subtype.ext_iff, Subtype.ext_iff, ggConjAut_apply, hcdef]
    show c * (x : MulAut L') * c⁻¹ * (x : MulAut L')⁻¹ = ((1 : ↥A) : MulAut L') ↔
      c * (x : MulAut L') * c⁻¹ = x
    rw [OneMemClass.coe_one]
    exact mul_inv_eq_one
  have hrange : Nat.card δ.range = p := by
    have h1 := Subgroup.card_mul_index δ.ker
    rw [Subgroup.index_ker] at h1
    have hpos : 0 < Nat.card δ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hker.symm)
  have hdne : (⟨δ ⟨a, ha⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ↥δ.range) ≠ 1 := by
    intro h
    apply hd1
    have h' := congrArg (fun g : ↥δ.range => ((g : ↥A) : MulAut L')) h
    rw [hd]
    exact h'
  have hgen := zpowers_eq_top_of_prime_card hrange hdne
  have hmem : (⟨δ ⟨b, hb⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ↥δ.range) ∈
      Subgroup.zpowers (⟨δ ⟨a, ha⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ↥δ.range) := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hdk : d ^ k = c * b * c⁻¹ * b⁻¹ := by
    have h' := congrArg (fun g : ↥δ.range => ((g : ↥A) : MulAut L')) hk
    simp only [SubgroupClass.coe_zpow] at h'
    rw [hd]
    exact h'
  obtain ⟨yb, hyb⟩ : ∃ yb, yb = n * (b n)⁻¹ := ⟨_, rfl⟩
  have hbn : b n = (yb ^ j)⁻¹ * n * yb ^ j := by rw [hyb]; exact hf b hb
  have hconjb : MulAut.conj yb = c * b * c⁻¹ * b⁻¹ := by rw [hyb]; exact hconjy b
  obtain ⟨u, hu⟩ : ∃ u, u = yb ^ j := ⟨_, rfl⟩
  rw [← hu] at hbn
  have hconju : MulAut.conj u = d ^ (k * j) := by
    rw [hu, map_pow, hconjb, ← hdk, ← zpow_natCast, ← zpow_mul]
  have hcu : u * y = y * u := by
    obtain ⟨w, hw, huw⟩ := exists_center_of_conj_eq (x := u) (y := y ^ (k * j)) (by
      rw [hconju, map_zpow, hconj])
    rw [huw]
    have hwy : y * w = w * y := Subgroup.mem_center_iff.mp hw y
    calc y ^ (k * j) * w * y = y ^ (k * j) * (w * y) := by group
      _ = y ^ (k * j) * (y * w) := by rw [hwy]
      _ = y * (y ^ (k * j) * w) := by group
  have hau : MulAut.conj (a u) = MulAut.conj u := by
    rw [conj_apply_mulAut, hconju, hcomm a ha (d ^ (k * j)) (A.zpow_mem hdA' _),
      mul_inv_cancel_right]
  obtain ⟨z₁, hz₁, hau'⟩ := exists_center_of_conj_eq hau
  have habn : a (b n) = u⁻¹ * a n * u := by
    rw [hbn, map_mul, map_mul, map_inv, hau']
    have hz₁i := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz₁) (u⁻¹ * a n * u)
    calc (u * z₁)⁻¹ * a n * (u * z₁) = z₁⁻¹ * (u⁻¹ * a n * u) * z₁ := by group
      _ = (u⁻¹ * a n * u) * z₁⁻¹ * z₁ := by rw [← hz₁i]
      _ = u⁻¹ * a n * u := by group
  have hba : b (a n) = a (b n) := by
    rw [← MulAut.mul_apply, ← hcomm a ha b hb, MulAut.mul_apply]
  calc b y = b n * (b (a n))⁻¹ := by rw [hy, map_mul, map_inv]
    _ = (u⁻¹ * n * u) * (u⁻¹ * a n * u)⁻¹ := by rw [hba, habn, hbn]
    _ = u⁻¹ * (n * (a n)⁻¹) * u := by group
    _ = u⁻¹ * y * u := by rw [hy]
    _ = y := by rw [mul_assoc, ← hcu]; group

theorem mem_ggHypCent_of_pow_two_pow (A : Subgroup (MulAut L'))
    (hZ : ∀ z ∈ Subgroup.center L', Odd (orderOf z)) {n : L'} {k : ℕ} (hn : n ^ 2 ^ k = 1) :
    n ∈ ggHypCent A n := by
  simp only [ggHypCent, Subgroup.mem_iInf, mem_ggFix]
  rintro a ⟨-, hac⟩
  obtain ⟨z, hz, hz'⟩ := exists_center_of_conj_eq (x := a n) (y := n) (by
    rw [conj_apply_mulAut, ← hac, mul_inv_cancel_right])
  have hzk : z ^ 2 ^ k = 1 := by
    have h1 : (a n) ^ 2 ^ k = 1 := by rw [← map_pow, hn, map_one]
    rwa [hz', (show Commute n z from Subgroup.mem_center_iff.mp hz n).mul_pow, hn,
      one_mul] at h1
  have hz1 : z = 1 := by
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
    exact orderOf_eq_one_iff.mp
      (((Nat.coprime_two_right.mpr (hZ z hz)).pow_right k).eq_one_of_dvd h2)
  rw [hz', hz1, mul_one]

private theorem coe_ggConjAut_pow {A : Subgroup (MulAut L')} {g : MulAut L'}
    (hg : g ∈ Subgroup.normalizer (A : Set (MulAut L'))) (b : ℕ) (x : ↥A) :
    (((ggConjAut A hg ^ b) x : ↥A) : MulAut L') = g ^ b * x * (g ^ b)⁻¹ := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, MulAut.mul_apply, ih, ggConjAut_apply, pow_succ]
    group

theorem exists_two_pow_ggConjAut [Finite L'] {A : Subgroup (MulAut L')} {m : L'}
    (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (h2 : ggConjAut A hm ^ 2 = 1) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) (k : ℕ),
      n ^ 2 ^ k = 1 ∧ ggConjAut A hn = ggConjAut A hm := by
  obtain ⟨k, b, hb, hmb⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have hnm : MulAut.conj (m ^ b) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [map_pow]
    exact Subgroup.pow_mem _ hm b
  refine ⟨m ^ b, hnm, k, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hmb, pow_orderOf_eq_one]
  · obtain ⟨i, rfl⟩ := hb
    have hpow : ggConjAut A hm ^ (2 * i + 1) = ggConjAut A hm := by
      rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [← hpow]
    ext x
    rw [coe_ggConjAut_pow, ggConjAut_apply, map_pow]

theorem ggTorusWeylElt_of_two_pow [Finite L'] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hZ : ∀ z ∈ Subgroup.center L', Odd (orderOf z)) {m : L'}
    (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection p (ggConjAut A hm)) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) (k : ℕ),
      n ^ 2 ^ k = 1 ∧ ggConjAut A hn = ggConjAut A hm ∧ n ∈ ggHypCent A n ∧
        GGTorusWeylElt p A n := by
  obtain ⟨n, hn, k, hnk, hnφ⟩ := exists_two_pow_ggConjAut hm hφ.1
  have hH := mem_ggHypCent_of_pow_two_pow A hZ hnk
  exact ⟨n, hn, k, hnk, hnφ, hH,
    ggTorusWeylElt_of_mem_ggHypCent hp hp2 hA hn (hnφ ▸ hφ) hH⟩

theorem prime_dvd_card_of_isSubnormal_ggHypCent_of_mem [Finite L'] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection p (ggConjAut A hn)) {J : Subgroup L'}
    (hJ : IsSubnormal J (ggHypCent A n)) (hnJ : n ∈ J) : p ∣ Nat.card J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut L') := Finite.of_injective (fun a : MulAut L' => (a : L' → L'))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  have : Finite A := inferInstance
  let H := ggHypCent A n
  let c := (MulAut.conj : L' →* MulAut L')
  let W := H.map c ⊔ A
  have hHstable : ∀ a ∈ A, ∀ x ∈ H, a x ∈ H := by
    intro a ha x hx
    simp only [H, ggHypCent, Subgroup.mem_iInf, mem_ggFix] at hx ⊢
    intro b hb
    have hab : a * b = b * a :=
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a,ha⟩ : A) ⟨b,hb.1⟩)
    have h := congrArg (fun f : MulAut L' => f x) hab
    simpa only [MulAut.mul_apply, hx b hb] using h.symm
  have hAH : A ≤ Subgroup.normalizer (H.map c : Set (MulAut L')) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨a x, hHstable a ha x hx, ?_⟩
      ext z
      simp only [c, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
        MulAut.apply_inv_self]
    · intro hb
      have hforward : ∀ y ∈ H.map c, a⁻¹ * y * (a⁻¹)⁻¹ ∈ H.map c := by
        rintro _ ⟨x,hx,rfl⟩
        refine ⟨a⁻¹ x, hHstable a⁻¹ (A.inv_mem ha) x hx, ?_⟩
        ext z
        simp only [c, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
          MulAut.apply_inv_self]
      simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
        inv_mul_cancel, mul_one] using
        hforward (a * b * a⁻¹) hb
  have hnorm : ((H.map c).subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (show H.map c ≤ W from le_sup_left)]
    intro x g hx hg
    have hW : W ≤ Subgroup.normalizer (H.map c : Set (MulAut L')) :=
      sup_le Subgroup.le_normalizer hAH
    exact (Subgroup.mem_normalizer_iff.mp (hW hg) x).mp hx
  have hchain : IsSubnormal (J.map c) W :=
    (hJ.map c).trans (.step le_sup_left hnorm (.refl W))
  obtain ⟨e,he,heinv⟩ := hφ.exists_inverted_ne_one hp
  have hep : (e : MulAut L') ^ p = 1 := hA.2 e e.2
  have he1 : (e : MulAut L') ≠ 1 := fun h => he (Subtype.ext h)
  have heorder : orderOf (e : MulAut L') = p := orderOf_eq_prime hep he1
  have hinv : c n * (e : MulAut L') * (c n)⁻¹ = (e : MulAut L')⁻¹ := by
    exact congrArg Subtype.val heinv
  have heJ : (e : MulAut L') ∈ J.map c :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.mem_of_isSubnormal_of_inv
      (isSubnormal_iff_open.mp hchain) ⟨n,hnJ,rfl⟩ (Subgroup.mem_sup_right e.2)
      (heorder ▸ hp.odd_of_ne_two hp2) hinv
  have hdvd := Subgroup.orderOf_dvd_natCard (J.map c) heJ
  rw [heorder] at hdvd
  exact hdvd.trans (Subgroup.card_map_dvd J c)

end CFSG.StandardType

end
