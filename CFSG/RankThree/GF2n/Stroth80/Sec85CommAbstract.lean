module

public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement
open CFSG.ClassicalGroups.F2Fixed (comm comm_apply)

variable {H : Type} [Group H]

theorem comm_fixed_coset [Finite H] {N : Subgroup H} {x y : H} (hN2 : IsPGroup 2 ↥N)
    (hy3 : y ^ 3 = 1) (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hx : x⁻¹ * (y * x * y⁻¹) ∈ N) :
    ∃ n ∈ N, ⁅y, x * n⁆ = 1 := by
  obtain ⟨j, hj⟩ := hN2.exists_card_eq
  have hcop3 : Nat.Coprime 3 (Nat.card N) := by
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hord : Nat.Coprime (orderOf y) (Nat.card N) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy3) hcop3
  obtain ⟨n, hnN, hfix⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime N hyN hx hord
  refine ⟨n, hnN, ?_⟩
  rw [commutatorElement_def, hfix]
  exact mul_inv_cancel (x * n)

theorem comm_N_trivial {N Zc R : Subgroup H} {x y : H} (hZN : Zc ≤ N) (hNR : N ≤ R)
    (hZc : ∀ z ∈ Zc, ∀ r ∈ R, r * z = z * r) (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Zc)
    (hxZ : ∀ z ∈ Zc, ⁅x, z⁆ = 1) (hxN : ∀ n ∈ N, ⁅x, n⁆ ∈ Zc) (hxy : ⁅y, x⁆ = 1) (hyR : y ∈ R)
    (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hsurj : ∀ n ∈ N, ∃ m ∈ N, ⁅y, m⁆ * n⁻¹ ∈ Zc) : ∀ n ∈ N, ⁅x, n⁆ = 1 := by
  have key : ∀ a b : H, ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
    intro a b
    simp only [commutatorElement_def]
    group
  have hmul : ∀ a ∈ N, ∀ b ∈ N, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
    intro a ha b hb
    have hcomm : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
      rw [hZc _ (hxN b hb) a (hNR ha), mul_inv_cancel_right]
    rw [key a b, hcomm]
  have hxy' : y * x * y⁻¹ = x := by
    have h := hxy
    rw [commutatorElement_def] at h
    exact mul_inv_eq_one.mp h
  have hconj : ∀ n : H, ⁅x, y * n * y⁻¹⁆ = y * ⁅x, n⁆ * y⁻¹ := by
    intro n
    simp only [commutatorElement_def]
    conv_lhs => rw [← hxy']
    group
  have hconjN : ∀ n ∈ N, ⁅x, y * n * y⁻¹⁆ = ⁅x, n⁆ := by
    intro n hn
    have hcy : y * ⁅x, n⁆ = ⁅x, n⁆ * y := hZc _ (hxN n hn) y hyR
    rw [hconj n, hcy, mul_inv_cancel_right]
  have hyc : ∀ m ∈ N, ⁅y, m⁆ ∈ N := by
    intro m hm
    rw [commutatorElement_def]
    exact N.mul_mem (hyN m hm) (N.inv_mem hm)
  have hmy : ∀ m ∈ N, ⁅x, ⁅y, m⁆⁆ = 1 := by
    intro m hm
    have hm' : m⁻¹ ∈ N := N.inv_mem hm
    have hsq : ⁅x, m⁆ * ⁅x, m⁻¹⁆ = 1 := by
      have h := hmul m hm m⁻¹ hm'
      rw [mul_inv_cancel, commutatorElement_one_right] at h
      exact h.symm
    rw [commutatorElement_def y m, hmul _ (hyN m hm) _ hm', hconjN m hm]
    exact hsq
  intro n hn
  obtain ⟨m, hm, hz⟩ := hsurj n hn
  have hzinv : (⁅y, m⁆ * n⁻¹)⁻¹ ∈ Zc := Zc.inv_mem hz
  have hdecomp : (⁅y, m⁆ * n⁻¹)⁻¹ * ⁅y, m⁆ = n := by group
  have h1 := hmul _ (hZN hzinv) _ (hyc m hm)
  rw [hdecomp, hxZ _ hzinv, hmy m hm, mul_one] at h1
  exact h1

theorem comm_R_trivial {N Zc R : Subgroup H} {x : H} (hNR : N ≤ R)
    (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hZN : Zc ≤ N)
    (hZc : ∀ z ∈ Zc, ∀ r ∈ R, r * z = z * r)
    (hZ : ∀ a ∈ N, (∀ b ∈ N, a * b = b * a) → a ∈ Zc) (hxR : ∀ r ∈ R, ⁅r, x⁆ ∈ N)
    (hx1 : ∀ n ∈ N, ⁅x, n⁆ = 1) (hperf : ∀ r ∈ R, ∃ a ∈ ⁅R, R⁆, ∃ k ∈ N, r = a * k) :
    ∀ r ∈ R, ⁅r, x⁆ = 1 := by
  have comm_of_conj : ∀ c b : H, c * b * c⁻¹ = b → c * b = b * c := by
    intro c b h
    calc c * b = c * b * c⁻¹ * c := by group
      _ = b * c := by rw [h]
  have hxn : ∀ n ∈ N, x * n * x⁻¹ = n := by
    intro n hn
    have h := hx1 n hn
    rw [commutatorElement_def] at h
    exact mul_inv_eq_one.mp h
  have hxn' : ∀ n ∈ N, x⁻¹ * n * x = n := by
    intro n hn
    calc x⁻¹ * n * x = x⁻¹ * (x * n * x⁻¹) * x := by rw [hxn n hn]
      _ = n := by group
  have hNc : ∀ n ∈ N, ⁅n, x⁆ = 1 := by
    intro n hn
    rw [← commutatorElement_inv, hx1 n hn, inv_one]
  have hbr1 : ⁅(1 : H), x⁆ = 1 := by
    rw [commutatorElement_def]
    group
  have hc_mem : ∀ r ∈ R, ⁅r, x⁆ ∈ Zc := by
    intro r hr
    refine hZ _ (hxR r hr) ?_
    intro b hb
    have hm : r⁻¹ * b * r ∈ N := by
      have h := hNn r⁻¹ (R.inv_mem hr) b hb
      rwa [inv_inv] at h
    have hxm := hxn _ hm
    have key : r * x * r⁻¹ * x⁻¹ * b * (r * x * r⁻¹ * x⁻¹)⁻¹ = b := by
      calc r * x * r⁻¹ * x⁻¹ * b * (r * x * r⁻¹ * x⁻¹)⁻¹
          = r * x * r⁻¹ * (x⁻¹ * b * x) * r * x⁻¹ * r⁻¹ := by group
        _ = r * x * r⁻¹ * b * r * x⁻¹ * r⁻¹ := by rw [hxn' b hb]
        _ = r * (x * (r⁻¹ * b * r) * x⁻¹) * r⁻¹ := by group
        _ = r * (r⁻¹ * b * r) * r⁻¹ := by rw [hxm]
        _ = b := by group
    simp only [commutatorElement_def]
    exact comm_of_conj _ _ key
  have hZcomm : ∀ a ∈ Zc, ∀ b ∈ Zc, a * b = b * a :=
    fun a ha b hb => (hZc a ha b (hNR (hZN hb))).symm
  have hcomp : ∀ r ∈ R, ∀ s ∈ R, ⁅r * s, x⁆ = ⁅s, x⁆ * ⁅r, x⁆ := by
    intro r hr s hs
    have hz := hZc _ (hc_mem s hs) r hr
    simp only [commutatorElement_def] at hz ⊢
    calc r * s * x * (r * s)⁻¹ * x⁻¹
        = r * (s * x * s⁻¹ * x⁻¹) * x * r⁻¹ * x⁻¹ := by group
      _ = (s * x * s⁻¹ * x⁻¹ * r) * x * r⁻¹ * x⁻¹ := by rw [hz]
      _ = s * x * s⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹) := by group
  have hmul : ∀ r ∈ R, ∀ s ∈ R, ⁅r * s, x⁆ = ⁅r, x⁆ * ⁅s, x⁆ :=
    fun r hr s hs => (hcomp r hr s hs).trans (hZcomm _ (hc_mem s hs) _ (hc_mem r hr))
  have hinv : ∀ r ∈ R, ⁅r⁻¹, x⁆ = ⁅r, x⁆⁻¹ := by
    intro r hr
    have h := hmul r hr r⁻¹ (R.inv_mem hr)
    have h1 : r * r⁻¹ = 1 := by group
    rw [h1, hbr1] at h
    exact (inv_eq_of_mul_eq_one_right h.symm).symm
  have hcomm_val : ∀ r ∈ R, ∀ s ∈ R,
      ⁅r, x⁆ * ⁅s, x⁆ = ⁅s, x⁆ * ⁅r, x⁆ :=
    fun r hr s hs => hZcomm _ (hc_mem r hr) _ (hc_mem s hs)
  have comm_aux : ∀ u v : H, u * v = v * u → u * v * u⁻¹ * v⁻¹ = 1 := by
    intro u v h
    rw [h]
    group
  have hcomm_R : ∀ r ∈ R, ∀ s ∈ R, ⁅⁅r, s⁆, x⁆ = 1 := by
    intro r hr s hs
    have h1 : r * s ∈ R := R.mul_mem hr hs
    have h2 : r * s * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hr)
    have h3 : r⁻¹ ∈ R := R.inv_mem hr
    have h4 : s⁻¹ ∈ R := R.inv_mem hs
    rw [commutatorElement_def r s, hmul _ h2 _ h4, hmul _ h1 _ h3,
      hmul r hr s hs, hinv r hr, hinv s hs]
    exact comm_aux _ _ (hcomm_val r hr s hs)
  have hSmul : ∀ a ∈ R, ∀ b ∈ R, ⁅a, x⁆ = 1 → ⁅b, x⁆ = 1 →
      ⁅a * b, x⁆ = 1 := by
    intro a ha b hb h1 h2
    rw [hmul a ha b hb, h1, h2, one_mul]
  have hSinv : ∀ a ∈ R, ⁅a, x⁆ = 1 → ⁅a⁻¹, x⁆ = 1 := by
    intro a ha h
    rw [hinv a ha, h, inv_one]
  let S : Subgroup H :=
    { carrier := {g | g ∈ R ∧ ⁅g, x⁆ = 1}
      mul_mem' := fun ha hb => ⟨R.mul_mem ha.1 hb.1, hSmul _ ha.1 _ hb.1 ha.2 hb.2⟩
      one_mem' := ⟨R.one_mem, hbr1⟩
      inv_mem' := fun ha => ⟨R.inv_mem ha.1, hSinv _ ha.1 ha.2⟩ }
  have hS : ∀ g : H, g ∈ S ↔ g ∈ R ∧ ⁅g, x⁆ = 1 := fun g => Iff.rfl
  have hNS : ∀ n ∈ N, n ∈ S := fun n hn => (hS n).mpr ⟨hNR hn, hNc n hn⟩
  have hRR : ⁅R, R⁆ ≤ S := by
    refine Subgroup.commutator_le.mpr ?_
    intro r hr s hs
    refine (hS _).mpr ⟨?_, hcomm_R r hr s hs⟩
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)) (R.inv_mem hs)
  intro r hr
  obtain ⟨a, ha, k, hk, rfl⟩ := hperf r hr
  exact ((hS _).mp (S.mul_mem (hRR ha) (hNS k hk))).2

theorem comm_surj_of_fpf [Finite H] {N Zc : Subgroup H} {y : H} (hZN : Zc ≤ N)
    (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Zc) (hNsq : ∀ n ∈ N, n ^ 2 ∈ Zc)
    (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hyZ : ∀ z ∈ Zc, y * z * y⁻¹ ∈ Zc)
    (hfpf : ∀ n ∈ N, ⁅y, n⁆ ∈ Zc → n ∈ Zc) : ∀ n ∈ N, ∃ m ∈ N, ⁅y, m⁆ * n⁻¹ ∈ Zc := by
  classical
  have hcP : ∀ w ∈ N, ⁅y, w⁆ ∈ N := fun w hw => by
    rw [commutatorElement_def]
    exact N.mul_mem (hyN w hw) (N.inv_mem hw)
  have hyNn : y ∈ Subgroup.normalizer (N : Set H) := Subgroup.mem_normalizer_fintype hyN
  have hyZn : y ∈ Subgroup.normalizer (Zc : Set H) := Subgroup.mem_normalizer_fintype hyZ
  have hzN : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set H) :=
    Subgroup.zpowers_le.mpr hyNn
  have hzI : Subgroup.zpowers y ≤ Subgroup.normalizer (Zc : Set H) :=
    Subgroup.zpowers_le.mpr hyZn
  have hsec : SecHyp (Subgroup.zpowers y) N Zc :=
    ⟨hZN, hNN, hNsq, fun r hr w hw => (Subgroup.mem_normalizer_iff.mp (hzN hr) w).mp hw,
      fun r hr w hw => (Subgroup.mem_normalizer_iff.mp (hzI hr) w).mp hw⟩
  obtain ⟨Mo, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite Mo := hκ.finite
  set g : ↥(Subgroup.zpowers y) := ⟨y, Subgroup.mem_zpowers y⟩ with hg
  have hker : (comm Mo g).ker = ⊥ := by
    rw [CFSG.ClassicalGroups.F2Fixed.ker_comm, eq_bot_iff]
    intro a ha
    obtain ⟨n, hn⟩ := hκ.surj (Multiplicative.ofAdd a)
    have h1 : g • a = a := ha g rfl
    have h2 := hκ.act g n ⟨y * n * y⁻¹, hyN n n.2⟩ rfl
    rw [hn, toAdd_ofAdd, h1] at h2
    have h3 : κ ⟨y * n * y⁻¹, hyN n n.2⟩ = κ n := by rw [hn]; exact h2
    have h4 := (hκ.eq_iff _ _).mp h3
    have h5 : ⁅y, (n : H)⁆ ∈ Zc := by
      have e : (y * n * y⁻¹) * (n : H)⁻¹ = ⁅y, (n : H)⁆ := by
        simp only [commutatorElement_def]
      rwa [← e]
    have h6 : (n : H) ∈ Zc := hfpf n n.2 h5
    have h7 : κ n = 1 := (hκ.ker n).mpr h6
    rw [h7] at hn
    have : a = 0 := by
      have := congrArg Multiplicative.toAdd hn
      simpa using this.symm
    rw [this]
    exact AddSubgroup.zero_mem _
  have hinj : Function.Injective (comm Mo g) :=
    (AddMonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (comm Mo g) := Finite.injective_iff_surjective.mp hinj
  intro n hn
  obtain ⟨b, hb⟩ := hsurj (Multiplicative.toAdd (κ ⟨n, hn⟩))
  obtain ⟨m, hm⟩ := hκ.surj (Multiplicative.ofAdd b)
  refine ⟨m, m.2, ?_⟩
  have h2 := hκ.act g m ⟨y * m * y⁻¹, hyN m m.2⟩ rfl
  have hbm : b = Multiplicative.toAdd (κ m) := by rw [hm]; rfl
  have h3 : κ ⟨⁅y, (m : H)⁆, hcP m m.2⟩ = κ ⟨n, hn⟩ := by
    have e : (⟨⁅y, (m : H)⁆, hcP m m.2⟩ : ↥N) = ⟨y * m * y⁻¹, hyN m m.2⟩ * (m : ↥N)⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_mul, map_inv, h2]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, ← hbm, ← sub_eq_add_neg, ← comm_apply, hb]
  have h4 := (hκ.eq_iff _ _).mp h3
  simpa using h4

theorem sec85_comm_core [Finite H] {R N Zc : Subgroup H} {x y : H} (hNR : N ≤ R)
    (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hN2 : IsPGroup 2 ↥N) (hZN : Zc ≤ N)
    (hZc : ∀ z ∈ Zc, ∀ r ∈ R, r * z = z * r) (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Zc)
    (hNsq : ∀ n ∈ N, n ^ 2 ∈ Zc) (hZ : ∀ a ∈ N, (∀ b ∈ N, a * b = b * a) → a ∈ Zc)
    (hperf : ∀ r ∈ R, ∃ a ∈ ⁅R, R⁆, ∃ k ∈ N, r = a * k) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hxR : ∀ r ∈ R, ⁅r, x⁆ ∈ N) (hxZ : ∀ z ∈ Zc, ⁅x, z⁆ = 1) (hxNZ : ∀ n ∈ N, ⁅x, n⁆ ∈ Zc)
    (hyR : y ∈ R) (hy3 : y ^ 3 = 1) (hfpf : ∀ n ∈ N, ⁅y, n⁆ ∈ Zc → n ∈ Zc) :
    ∃ n₀ ∈ N, ∀ r ∈ R, ⁅r, x * n₀⁆ = 1 := by
  have hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N := hNn y hyR
  have hxNi : ∀ n ∈ N, x⁻¹ * n * x ∈ N := by
    have hx' : x ∈ Subgroup.normalizer (N : Set H) := Subgroup.mem_normalizer_fintype hxN
    intro n hn
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx') n).mp hn
    simpa using this
  have hyZ : ∀ z ∈ Zc, y * z * y⁻¹ ∈ Zc := fun z hz => by
    rw [hZc z hz y hyR, mul_inv_cancel_right]
    exact hz
  have hx : x⁻¹ * (y * x * y⁻¹) ∈ N := by
    have e : x⁻¹ * (y * x * y⁻¹) = x⁻¹ * ⁅y, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hxNi _ (hxR y hyR)
  obtain ⟨n₀, hn₀, hfix⟩ := comm_fixed_coset hN2 hy3 hyN hx
  have hsurj := comm_surj_of_fpf hZN hNN hNsq hyN hyZ hfpf
  refine ⟨n₀, hn₀, ?_⟩
  have hxc : ∀ z ∈ Zc, x * z * x⁻¹ = z := fun z hz => by
    have h1 : x * z = z * x := commutatorElement_eq_one_iff_mul_comm.mp (hxZ z hz)
    rw [h1, mul_inv_cancel_right]
  have hxZ' : ∀ z ∈ Zc, ⁅x * n₀, z⁆ = 1 := by
    intro z hz
    have hc : n₀ * z = z * n₀ := hZc z hz n₀ (hNR hn₀)
    have e : ⁅x * n₀, z⁆ = x * (n₀ * z * n₀⁻¹) * x⁻¹ * z⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, show n₀ * z * n₀⁻¹ = z by rw [hc, mul_inv_cancel_right], hxc z hz, mul_inv_cancel]
  have hxNZ' : ∀ n ∈ N, ⁅x * n₀, n⁆ ∈ Zc := by
    intro n hn
    have e : ⁅x * n₀, n⁆ = (x * ⁅n₀, n⁆ * x⁻¹) * ⁅x, n⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Zc.mul_mem ?_ (hxNZ n hn)
    have h1 : ⁅n₀, n⁆ ∈ Zc := hNN n₀ hn₀ n hn
    rw [hxc _ h1]
    exact h1
  have hN1 := comm_N_trivial hZN hNR hZc hNN hxZ' hxNZ' (by
    exact hfix) hyR hyN hsurj
  have hxR' : ∀ r ∈ R, ⁅r, x * n₀⁆ ∈ N := by
    intro r hr
    have e : ⁅r, x * n₀⁆ = ⁅r, x⁆ * (x * ⁅r, n₀⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine N.mul_mem (hxR r hr) (hxN _ ?_)
    have : ⁅r, n₀⁆ = (r * n₀ * r⁻¹) * n₀⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact N.mul_mem (hNn r hr n₀ hn₀) (N.inv_mem hn₀)
  exact comm_R_trivial hNR hNn hZN hZc hZ hxR' hN1 hperf

end CFSG.RankThree.GF2n.Stroth80
