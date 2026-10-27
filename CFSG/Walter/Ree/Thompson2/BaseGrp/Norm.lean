module

public import CFSG.Walter.Ree.Thompson2.BaseFin.Iso
public import CFSG.Walter.Ree.Thompson2.BaseGrp.S

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

theorem conj_inv_pow {G : Type*} [Group G] (g x : G) (m : ℕ) :
    (g⁻¹ * x * g) ^ m = g⁻¹ * x ^ m * g := by
  have := conj_pow (a := g⁻¹) (b := x) (i := m)
  rwa [inv_inv] at this

theorem conj_pow_of_conj {G : Type*} [Group G] {t c : G} {a : ℕ} (h : t⁻¹ * c * t = c ^ a)
    (m : ℕ) : t⁻¹ * c ^ m * t = c ^ (a * m) := by
  rw [← conj_inv_pow, h, ← pow_mul]

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ)

section S

variable (S : Sylow 2 G)

include C in
theorem S_comm {x y : G} (hx : x ∈ (S : Subgroup G)) (hy : y ∈ (S : Subgroup G)) :
    x * y = y * x := by
  have := (C.h.elementary_sylow S).toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

include C in
theorem S_sq {x : G} (hx : x ∈ (S : Subgroup G)) : x * x = 1 := by
  have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (C.h.elementary_sylow S).exponent_dvd_p
    ⟨x, hx⟩
  have := congrArg Subtype.val this
  simpa [sq] using this

include C in
theorem fix_eq_one
    {d : G} (hdN : d ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hd7 : orderOf d = 7) {s : G} (hs : s ∈ (S : Subgroup G)) (hfix : d⁻¹ * s * d = s) :
    s = 1 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  by_contra hs1
  have hconj : ∀ x ∈ (S : Subgroup G), d⁻¹ * x * d ∈ (S : Subgroup G) := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) x).mp hx
    rwa [inv_inv] at this
  let f : Function.End (S : Subgroup G) := fun x => ⟨d⁻¹ * x * d, hconj x x.2⟩
  have hf7 : f ^ 7 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    have hfn : ∀ n : ℕ, ((f ^ n) x : G) = (d ^ n)⁻¹ * x * d ^ n := by
      intro n
      induction n with
      | zero => show ((x : (S : Subgroup G)) : G) = _; simp
      | succ n ih =>
        rw [pow_succ']
        show d⁻¹ * ((f ^ n) x : G) * d = _
        rw [ih, pow_succ]
        group
    rw [pow_one, hfn, ← hd7, pow_orderOf_eq_one]
    show _ = ((x : (S : Subgroup G)) : G)
    simp
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 7) (n := 1) hf7
  have hS8 : Fintype.card (S : Subgroup G) = 8 := by
    rw [← Nat.card_eq_fintype_card, C.h.card_sylow S]
  rw [hS8] at hmod
  have hle : Fintype.card (Function.fixedPoints f) ≤ 8 := by
    rw [← hS8]; exact Fintype.card_subtype_le _
  have h2 : 2 ≤ Fintype.card (Function.fixedPoints f) := by
    have h1f : Function.IsFixedPt f 1 := by
      show f 1 = 1
      apply Subtype.ext
      show d⁻¹ * 1 * d = 1
      group
    set A : Finset (Function.fixedPoints f) := {⟨1, h1f⟩, ⟨⟨s, hs⟩, Subtype.ext hfix⟩} with hA
    have hsub : A.card = 2 := by
      rw [hA, Finset.card_pair]
      intro h
      apply hs1
      have := congrArg (fun x : Function.fixedPoints f => ((x : (S : Subgroup G)) : G)) h
      exact this.symm
    have := Finset.card_le_univ A
    omega
  have h8 : Fintype.card (Function.fixedPoints f) = 8 := by
    unfold Nat.ModEq at hmod
    omega
  have hall : ∀ x : (S : Subgroup G), f x = x := by
    have huniv : (Finset.univ : Finset (Function.fixedPoints f)).card =
        (Finset.univ : Finset (S : Subgroup G)).card := by
      rw [Finset.card_univ, Finset.card_univ, h8, hS8]
    intro x
    by_contra hx
    have hlt : Fintype.card (Function.fixedPoints f) < Fintype.card (S : Subgroup G) :=
      Fintype.card_subtype_lt (p := fun y => f y = y) hx
    omega
  have hdC : d ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg Subtype.val (hall ⟨x, hx⟩)
    change d⁻¹ * x * d = x at this
    calc x * d = d * (d⁻¹ * x * d) := by group
      _ = d * x := by rw [this]
  rw [C.centralizer_sylow S] at hdC
  have := Subgroup.orderOf_dvd_natCard _ hdC
  rw [hd7, C.h.card_sylow S] at this
  norm_num at this

variable {c : G}

@[expose] def sJ (c : G) (n : ℕ) : G := (c ^ n)⁻¹ * C.J * c ^ n

theorem sJ_mem (hJS : C.J ∈ (S : Subgroup G))
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (n : ℕ) :
    C.sJ c n ∈ (S : Subgroup G) := by
  have hn : (c ^ n)⁻¹ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hcN n)
  have := (Subgroup.mem_normalizer_iff.mp hn C.J).mp hJS
  rwa [inv_inv] at this

theorem sJ_zero : C.sJ c 0 = C.J := by simp [sJ]

theorem sJ_add_seven (hc7 : orderOf c = 7) (n : ℕ) : C.sJ c (n + 7) = C.sJ c n := by
  have h7 : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one c
  simp only [sJ, pow_add, h7, mul_one]

theorem sJ_shift (a m : ℕ) : (c ^ m)⁻¹ * C.sJ c a * c ^ m = C.sJ c (a + m) := by
  simp only [sJ, pow_add]
  group

theorem sJ_ne_one (n : ℕ) : C.sJ c n ≠ 1 := by
  intro h
  apply C.J_ne_one
  have : C.J = c ^ n * C.sJ c n * (c ^ n)⁻¹ := by simp only [sJ]; group
  rw [this, h]
  group

theorem sJ_inj
    (hJS : C.J ∈ (S : Subgroup G))
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hc7 : orderOf c = 7)
    {m n : ℕ} (hm : m < 7) (hn : n < 7) (h : C.sJ c m = C.sJ c n) : m = n := by
  wlog hmn : m < n generalizing m n
  · rcases Nat.lt_or_ge n m with h' | h'
    · exact (this hn hm h.symm h').symm
    · omega
  exfalso
  obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
  have hd7 : orderOf (c ^ j) = 7 := by
    rw [Nat.Coprime.orderOf_pow (by
      rw [hc7]; exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega)), hc7]
  have hfix : (c ^ j)⁻¹ * C.sJ c m * c ^ j = C.sJ c m := by rw [C.sJ_shift, ← h]
  exact C.sJ_ne_one m (C.fix_eq_one S (Subgroup.pow_mem _ hcN j) hd7 (C.sJ_mem S hJS hcN m)
    hfix)

theorem exists_sJ_eq
    (hJS : C.J ∈ (S : Subgroup G))
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hc7 : orderOf c = 7)
    {x : G} (hx : x ∈ (S : Subgroup G)) (hx1 : x ≠ 1) : ∃ n < 7, x = C.sJ c n := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let F : Fin 7 → (S : Subgroup G) := fun n => ⟨C.sJ c n, C.sJ_mem S hJS hcN n⟩
  have hF : Function.Injective F := by
    intro a b hab
    exact Fin.ext (C.sJ_inj S hJS hcN hc7 a.2 b.2 (congrArg Subtype.val hab))
  have hS8 : Fintype.card (S : Subgroup G) = 8 := by
    rw [← Nat.card_eq_fintype_card, C.h.card_sylow S]
  have hsub : Finset.univ.image F ⊆ Finset.univ.erase 1 := by
    intro y hy
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_erase.mpr ⟨fun h => C.sJ_ne_one n (congrArg Subtype.val h),
      Finset.mem_univ _⟩
  have hcard : (Finset.univ.erase (1 : (S : Subgroup G))).card ≤ (Finset.univ.image F).card := by
    rw [Finset.card_image_of_injective _ hF, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Finset.card_univ, hS8, Fintype.card_fin]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hxmem : (⟨x, hx⟩ : (S : Subgroup G)) ∈ Finset.univ.erase 1 :=
    Finset.mem_erase.mpr ⟨fun h => hx1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  rw [← heq] at hxmem
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hxmem
  exact ⟨n, n.2, (congrArg Subtype.val hn).symm⟩

theorem exists_line
    (hJS : C.J ∈ (S : Subgroup G))
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hc7 : orderOf c = 7) :
    ∃ i : ℕ, (i = 1 ∨ i = 3) ∧ C.sJ c 0 * C.sJ c i * C.sJ c (5 * i) = 1 := by
  have hmem := C.sJ_mem S hJS hcN (c := c)
  have hcomm : ∀ a b : ℕ, C.sJ c a * C.sJ c b = C.sJ c b * C.sJ c a :=
    fun a b => C.S_comm S (hmem a) (hmem b)
  have hsq : ∀ a : ℕ, C.sJ c a * C.sJ c a = 1 := fun a => C.S_sq S (hmem a)
  have hinj : ∀ m n : ℕ, m < 7 → n < 7 → C.sJ c m = C.sJ c n → m = n :=
    fun m n hm hn => C.sJ_inj S hJS hcN hc7 hm hn
  have h7 := C.sJ_add_seven hc7
  have e7 : C.sJ c 7 = C.sJ c 0 := by simpa using h7 0
  have e8 : C.sJ c 8 = C.sJ c 1 := h7 1
  have hshift : ∀ a b d m : ℕ, C.sJ c a * C.sJ c b = C.sJ c d →
      C.sJ c (a + m) * C.sJ c (b + m) = C.sJ c (d + m) := by
    intro a b d m h
    rw [← C.sJ_shift, ← C.sJ_shift, ← C.sJ_shift, ← h]
    group
  have h01 : C.sJ c 0 * C.sJ c 1 ∈ (S : Subgroup G) := Subgroup.mul_mem _ (hmem 0) (hmem 1)
  have h011 : C.sJ c 0 * C.sJ c 1 ≠ 1 := by
    intro h
    have : C.sJ c 0 = C.sJ c 1 := by
      calc C.sJ c 0 = C.sJ c 0 * C.sJ c 1 * C.sJ c 1 := by rw [mul_assoc, hsq, mul_one]
        _ = C.sJ c 1 := by rw [h, one_mul]
    exact absurd (hinj 0 1 (by norm_num) (by norm_num) this) (by norm_num)
  obtain ⟨d, hd7, hd⟩ := C.exists_sJ_eq S hJS hcN hc7 h01 h011
  have hcancel : ∀ {a b : ℕ}, C.sJ c a * C.sJ c b = C.sJ c b → C.sJ c a = 1 := by
    intro a b h
    calc C.sJ c a = C.sJ c a * C.sJ c b * C.sJ c b := by rw [mul_assoc, hsq, mul_one]
      _ = 1 := by rw [h, hsq]
  interval_cases d
  · exact absurd (hcancel (a := 1) (b := 0) (by rw [hcomm]; exact hd))
      (C.sJ_ne_one 1)
  · exact absurd (hcancel (a := 0) (b := 1) hd) (C.sJ_ne_one 0)
  ·
    exfalso
    have h1 := hshift 0 1 2 1 hd
    simp only [Nat.reduceAdd] at h1
    have : C.sJ c 3 = C.sJ c 0 := by
      rw [← h1, ← hd, ← mul_assoc, hcomm 1 0, mul_assoc, hsq, mul_one]
    exact absurd (hinj 3 0 (by norm_num) (by norm_num) this) (by norm_num)
  ·
    refine ⟨3, Or.inr rfl, ?_⟩
    rw [show 5 * 3 = 1 + 7 + 7 by norm_num, h7, h7, mul_assoc, hcomm 3 1, ← mul_assoc, hd,
      hsq]
  ·
    exfalso
    have h1 := hshift 0 1 4 4 hd
    simp only [Nat.reduceAdd] at h1
    rw [e8, ← hd] at h1
    have : C.sJ c 5 = C.sJ c 0 := by
      calc C.sJ c 5 = (C.sJ c 0 * C.sJ c 0) * C.sJ c 5 * (C.sJ c 1 * C.sJ c 1) := by
            rw [hsq, hsq, one_mul, mul_one]
        _ = C.sJ c 0 * (C.sJ c 0 * (C.sJ c 5 * C.sJ c 1)) * C.sJ c 1 := by group
        _ = C.sJ c 0 * (C.sJ c 0 * C.sJ c 1 * C.sJ c 5) * C.sJ c 1 := by
            rw [hcomm 5 1]; simp only [mul_assoc]
        _ = C.sJ c 0 * C.sJ c 1 * C.sJ c 1 := by rw [h1]
        _ = C.sJ c 0 := by rw [mul_assoc, hsq, mul_one]
    exact absurd (hinj 5 0 (by norm_num) (by norm_num) this) (by norm_num)
  ·
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [mul_one, hd, hsq]
  ·
    exfalso
    have h1 := hshift 0 1 6 1 hd
    simp only [Nat.reduceAdd] at h1
    rw [e7] at h1
    have : C.sJ c 2 = C.sJ c 6 := by
      calc C.sJ c 2 = C.sJ c 1 * (C.sJ c 1 * C.sJ c 2) := by rw [← mul_assoc, hsq, one_mul]
        _ = C.sJ c 6 := by rw [h1, hcomm, hd]
    exact absurd (hinj 2 6 (by norm_num) (by norm_num) this) (by norm_num)

end S

theorem exists_t
    {c : G} (hc7 : orderOf c = 7) (hTc : C.T⁻¹ * c * C.T ∈ Subgroup.zpowers c) :
    ∃ T' : G, (T' = C.T ∨ T' = C.T⁻¹) ∧ T'⁻¹ * c * T' = c ^ 2 := by
  have hfin : IsOfFinOrder c := isOfFinOrder_of_finite c
  obtain ⟨a, ha⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hTc
  have h7 : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one c
  have hmod : ∀ n : ℕ, c ^ n = c ^ (n % 7) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, h7, one_pow, one_mul]
  set a' := a % 7 with ha'
  have ha' : c ^ a = C.T⁻¹ * c * C.T := ha
  have hTa : C.T⁻¹ * c * C.T = c ^ a' := by rw [← ha', hmod a]
  have ha'7 : a' < 7 := Nat.mod_lt _ (by norm_num)
  have hcube : c ^ (a' * (a' * a')) = c := by
    have h1 := conj_pow_of_conj hTa
    have e : (C.T ^ 3)⁻¹ * c * C.T ^ 3 = c ^ (a' * (a' * a')) := by
      rw [pow_three, show (C.T * (C.T * C.T))⁻¹ * c * (C.T * (C.T * C.T)) =
        C.T⁻¹ * (C.T⁻¹ * (C.T⁻¹ * c * C.T) * C.T) * C.T by group, hTa, h1, h1]
    rw [← e, C.T_pow_three]
    group
  have hTnc : C.T⁻¹ * c * C.T ≠ c := by
    intro h
    apply not_commute_three_seven C.h C.orderOf_T hc7
    calc c * C.T = C.T * (C.T⁻¹ * c * C.T) := by group
      _ = C.T * c := by rw [h]
  have hval : ∀ n < 7, c ^ n = c → n = 1 := by
    intro n hn h
    have := (pow_eq_pow_iff_modEq.mp (h.trans (pow_one c).symm))
    rw [hc7] at this
    unfold Nat.ModEq at this
    omega
  interval_cases a'
  · exfalso
    have : c = 1 := by
      calc c = C.T * (C.T⁻¹ * c * C.T) * C.T⁻¹ := by group
        _ = 1 := by rw [hTa, pow_zero]; group
    rw [this, orderOf_one] at hc7
    norm_num at hc7
  · exact absurd (by rw [hTa, pow_one]) hTnc
  · exact ⟨C.T, Or.inl rfl, hTa⟩
  · rw [hmod] at hcube
    simp only [Nat.reduceMul, Nat.reduceMod] at hcube
    exact absurd (hval 6 (by norm_num) hcube) (by norm_num)
  · refine ⟨C.T⁻¹, Or.inr rfl, ?_⟩
    have hT2 : C.T * C.T = C.T⁻¹ := (inv_eq_mul_self C.T_pow_three).symm
    calc C.T⁻¹⁻¹ * c * C.T⁻¹ = (C.T * C.T)⁻¹ * c * (C.T * C.T) := by rw [hT2]
      _ = C.T⁻¹ * (C.T⁻¹ * c * C.T) * C.T := by group
      _ = C.T⁻¹ * c ^ 4 * C.T := by rw [hTa]
      _ = c ^ (4 * 4) := conj_pow_of_conj hTa 4
      _ = c ^ 2 := by rw [hmod]
  · rw [hmod] at hcube
    simp only [Nat.reduceMul, Nat.reduceMod] at hcube
    exact absurd (hval 6 (by norm_num) hcube) (by norm_num)
  · rw [hmod] at hcube
    simp only [Nat.reduceMul, Nat.reduceMod] at hcube
    exact absurd (hval 6 (by norm_num) hcube) (by norm_num)

theorem J_conj_w (γ : k) : C.J * C.ι (pp σ 0 0 γ) * C.J⁻¹ = (C.ι (pp σ 0 0 γ))⁻¹ := by
  have h := congrArg C.ι (J_conj_pp (σ := σ) 0 0 γ)
  rw [map_mul, map_mul, map_inv, neg_zero] at h
  change C.J⁻¹ * C.ι (pp σ 0 0 γ) * C.J = C.ι (pp σ 0 0 (-γ)) at h
  rw [C.J_inv] at h ⊢
  rw [h, ← map_inv, pp_inv]
  congr 1
  rw [pp_eq_iff]
  refine ⟨by ring, by ring, by ring⟩

theorem w_pow_three (γ : k) : C.ι (pp σ 0 0 γ) ^ 3 = 1 := by
  rw [← map_pow, pp_center_pow]
  have h3 : ((3 : ℕ) : k) = 0 := by exact_mod_cast ThompsonN.three_eq_zero (K := k)
  rw [h3, zero_mul, pp_zero, map_one]

theorem w_comm_T (γ : k) : C.ι (pp σ 0 0 γ) * C.T = C.T * C.ι (pp σ 0 0 γ) := by
  rw [T, tT, ← map_mul, ← map_mul, pp_center_comm]

theorem exists_hatRels
    (S : Sylow 2 G) (hJS : C.J ∈ (S : Subgroup G)) {c : G}
    (hc7 : orderOf c = 7) (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hTc : C.T⁻¹ * c * C.T ∈ Subgroup.zpowers c) {γ : k}
    (huc : C.J * C.ι (pp σ 0 0 γ) * c * (C.J * C.ι (pp σ 0 0 γ))⁻¹ = c⁻¹) :
    ∃ (i : ℕ) (T' : G), (i = 1 ∨ i = 3) ∧ (T' = C.T ∨ T' = C.T⁻¹) ∧
      BaseFin.HatRels C.J (c ^ i) T' (C.J * C.ι (pp σ 0 0 γ)) := by
  obtain ⟨i, hi, hline⟩ := C.exists_line S hJS hcN hc7
  obtain ⟨T', hT', hTc2⟩ := C.exists_t hc7 hTc
  set w := C.ι (pp σ 0 0 γ) with hw
  have hJw := C.J_conj_w γ
  rw [← hw] at hJw
  have hu2 : C.J * w * (C.J * w) = 1 := by
    calc C.J * w * (C.J * w) = (C.J * w * C.J⁻¹) * (C.J * C.J) * w := by group
      _ = 1 := by rw [hJw, C.J_mul_J, mul_one, inv_mul_cancel]
  have hui : (C.J * w)⁻¹ = C.J * w := inv_eq_of_mul_eq_one_right hu2
  have hT'3 : T' ^ 3 = 1 := by
    rcases hT' with rfl | rfl
    · exact C.T_pow_three
    · rw [inv_pow, C.T_pow_three, inv_one]
  have hJT' : C.J * T' = T' * C.J := by
    rcases hT' with rfl | rfl
    · exact C.J_mul_T
    · have := C.J_mul_T
      calc C.J * C.T⁻¹ = C.T⁻¹ * (C.T * C.J) * C.T⁻¹ := by group
        _ = C.T⁻¹ * (C.J * C.T) * C.T⁻¹ := by rw [this]
        _ = C.T⁻¹ * C.J := by group
  have hwT' : w * T' = T' * w := by
    rcases hT' with rfl | rfl
    · exact C.w_comm_T γ
    · have := C.w_comm_T γ
      rw [← hw] at this
      calc w * C.T⁻¹ = C.T⁻¹ * (C.T * w) * C.T⁻¹ := by group
        _ = C.T⁻¹ * (w * C.T) * C.T⁻¹ := by rw [this]
        _ = C.T⁻¹ * w := by group
  have hmem := C.sJ_mem S hJS hcN (c := c)
  have h7 : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one c
  refine ⟨i, T', hi, hT', ?_⟩
  refine ⟨?_, ?_, hT'3, hJT', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq, C.J_mul_J]
  · rw [← pow_mul, mul_comm, pow_mul, h7, one_pow]
  · rw [← conj_inv_pow, hTc2, ← pow_mul, ← pow_mul, mul_comm]
  · exact C.S_comm S hJS (hmem i)
  · rw [← pow_mul]; exact C.S_comm S hJS (hmem (i * 3))
  · rw [← pow_mul]
    have := hline
    rw [C.sJ_zero, mul_comm 5 i] at this
    exact this
  · rw [sq]; exact hu2
  · calc C.J * w * T' = C.J * (w * T') := by group
      _ = C.J * T' * w := by rw [hwT']; group
      _ = T' * (C.J * w) := by rw [hJT']; group
  · have hc' : (C.J * w) * c ^ i * (C.J * w)⁻¹ = (c ^ i)⁻¹ := by
      rw [show (C.J * w) * c ^ i * (C.J * w)⁻¹ = ((C.J * w) * c * (C.J * w)⁻¹) ^ i by
        rw [conj_pow], huc, inv_pow]
    rw [hui] at hc'
    exact hc'
  · calc (C.J * w * C.J) ^ 3 = (C.J * w * C.J⁻¹) ^ 3 := by rw [C.J_inv]
      _ = 1 := by rw [hJw, inv_pow, C.w_pow_three, inv_one]

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
