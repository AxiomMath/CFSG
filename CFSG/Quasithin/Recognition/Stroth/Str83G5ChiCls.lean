module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Defs

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

private theorem two_pow_eq_one (n : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have h : ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) = ((1 : ℕ) : ZMod (2 ^ n - 1)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2
      ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 dvd_rfl).symm
  simpa using h

private theorem two_pow_inj {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : (2 : ZMod (2 ^ n - 1)) ^ s = 2 ^ t) : s = t := by
  by_contra hne
  wlog hlt : s < t generalizing s t
  · exact this ht hs h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (2 : ℕ) ^ s < 2 ^ t := Nat.pow_lt_pow_right (by norm_num) hlt
  have h2 : (2 : ℕ) ^ t ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h4 : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_two_pow
  have h5 : ((2 ^ s : ℕ) : ZMod (2 ^ (m + 1) - 1)) = ((2 ^ t : ℕ) : ZMod (2 ^ (m + 1) - 1)) := by
    simpa using h
  have h6 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h5
  have h7 : 2 ^ (m + 1) - 1 ∣ 2 ^ t - 2 ^ s := (Nat.modEq_iff_dvd' h1.le).1 h6
  have h8 : 2 ^ t - 2 ^ s = 0 := Nat.eq_zero_of_dvd_of_lt h7 (by omega)
  omega

theorem card_cls_of_isUnit (hn : n ≠ 0) {φ : Coord n} (h : IsUnit φ.1) : (cls φ).card = n := by
  unfold cls
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro s hs t ht hst
  have h1 : ((2 : ZMod (2 ^ n - 1)) ^ s) * φ.1 = (2 : ZMod (2 ^ n - 1)) ^ t * φ.1 :=
    congrArg Prod.fst hst
  exact two_pow_inj (Finset.mem_range.1 hs) (Finset.mem_range.1 ht) (h.mul_left_inj.1 h1)

private def frobStep (n : ℕ) (φ : Coord n) : Coord n := (2 : ZMod (2 ^ n - 1)) • φ

private theorem frobStep_iterate (s : ℕ) (φ : Coord n) :
    (frobStep n)^[s] φ = ((2 : ZMod (2 ^ n - 1)) ^ s) • φ := by
  induction s with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply', ih, frobStep, smul_smul, ← pow_succ']

private theorem isPeriodicPt_frobStep_iff (e : ℕ) (φ : Coord n) :
    Function.IsPeriodicPt (frobStep n) e φ ↔
      (2 : ZMod (2 ^ n - 1)) ^ e * φ.1 = φ.1 ∧ (2 : ZMod (2 ^ n - 1)) ^ e * φ.2 = φ.2 := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, frobStep_iterate, Prod.ext_iff]
  rfl

private theorem isPeriodicPt_frobStep_self (φ : Coord n) :
    Function.IsPeriodicPt (frobStep n) n φ := by
  rw [isPeriodicPt_frobStep_iff, two_pow_eq_one, one_mul, one_mul]
  exact ⟨rfl, rfl⟩

private theorem card_cls_eq_minimalPeriod (hn : n ≠ 0) (φ : Coord n) :
    (cls φ).card = Function.minimalPeriod (frobStep n) φ := by
  have hper := isPeriodicPt_frobStep_self φ
  have hpos : 0 < Function.minimalPeriod (frobStep n) φ :=
    hper.minimalPeriod_pos (Nat.pos_of_ne_zero hn)
  have hle : Function.minimalPeriod (frobStep n) φ ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hper.minimalPeriod_dvd
  have hcls : cls φ = (Finset.range n).image fun s => (frobStep n)^[s] φ := by
    unfold cls
    simp only [frobStep_iterate]
  have himg : (Finset.range n).image (fun s => (frobStep n)^[s] φ) =
      (Finset.range (Function.minimalPeriod (frobStep n) φ)).image
        fun s => (frobStep n)^[s] φ := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s % Function.minimalPeriod (frobStep n) φ, Nat.mod_lt _ hpos,
        Function.iterate_mod_minimalPeriod_eq⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, lt_of_lt_of_le hs hle, rfl⟩
  rw [hcls, himg, Finset.card_image_of_injOn, Finset.card_range]
  intro s hs t ht hst
  exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 hs) (Finset.mem_range.1 ht) hst

section Zeta

variable {ζ : GaloisField 2 n}

private theorem two_pow_sub_one_ne_zero (hn : n ≠ 0) : 2 ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_two_pow hn
  omega

private theorem ζ_ne_zero (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1) : ζ ≠ 0 := by
  rintro rfl
  rw [orderOf_zero] at hζ
  exact two_pow_sub_one_ne_zero hn hζ.symm

private theorem pow_eq_pow_iff (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1) {p q : ℕ} :
    ζ ^ p = ζ ^ q ↔ (p : ZMod (2 ^ n - 1)) = q := by
  have hfin : IsOfFinOrder ζ :=
    orderOf_pos_iff.1 (by rw [hζ]; exact Nat.pos_of_ne_zero (two_pow_sub_one_ne_zero hn))
  rw [hfin.pow_eq_pow_iff_modEq, hζ, ZMod.natCast_eq_natCast_iff]

private theorem pow_val_eq_pow_val_iff (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    {x y : ZMod (2 ^ n - 1)} : ζ ^ x.val = ζ ^ y.val ↔ x = y := by
  haveI : NeZero (2 ^ n - 1) := ⟨two_pow_sub_one_ne_zero hn⟩
  rw [pow_eq_pow_iff hn hζ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

private theorem pow_val_pow_two_pow (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (x : ZMod (2 ^ n - 1)) (e : ℕ) :
    (ζ ^ x.val) ^ 2 ^ e = ζ ^ ((2 : ZMod (2 ^ n - 1)) ^ e * x).val := by
  haveI : NeZero (2 ^ n - 1) := ⟨two_pow_sub_one_ne_zero hn⟩
  rw [← pow_mul, pow_eq_pow_iff hn hζ]
  simp [ZMod.natCast_zmod_val, mul_comm]

private theorem pow_two_pow_eq_iff (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (x : ZMod (2 ^ n - 1)) (e : ℕ) :
    (ζ ^ x.val) ^ 2 ^ e = ζ ^ x.val ↔ (2 : ZMod (2 ^ n - 1)) ^ e * x = x := by
  rw [pow_val_pow_two_pow hn hζ, pow_val_eq_pow_val_iff hn hζ]

end Zeta

private theorem two_pow_mod (n j : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ (j % n) = 2 ^ j := by
  calc (2 : ZMod (2 ^ n - 1)) ^ (j % n)
      = (2 ^ n) ^ (j / n) * 2 ^ (j % n) := by rw [two_pow_eq_one, one_pow, one_mul]
    _ = 2 ^ (n * (j / n) + j % n) := by rw [pow_add, pow_mul]
    _ = 2 ^ j := by rw [Nat.div_add_mod]

section Embedding

variable {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G} {φ : Coord n}
  {β : G → GaloisField 2 n}

private theorem IsChiEmb.beta_one (h : IsChiEmb ζ d₁ d₂ C S φ β) : β 1 = 0 := by
  simpa using h.map_mul 1 S.one_mem 1 S.one_mem

private theorem IsChiEmb.beta_inv (h : IsChiEmb ζ d₁ d₂ C S φ β) {s : G} (hs : s ∈ S) :
    β s⁻¹ = -β s := by
  have := h.map_mul s hs s⁻¹ (S.inv_mem hs)
  rw [mul_inv_cancel, h.beta_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

private theorem exists_beta_aeval {φ' : Coord n} {β' : G → GaloisField 2 n}
    (h : IsChiEmb ζ d₁ d₂ C S φ β) (h' : IsChiEmb ζ d₁ d₂ C S φ' β')
    (hS₁ : d₁ ∈ normalizer (S : Set G)) (hS₂ : d₂ ∈ normalizer (S : Set G)) {s₀ : G}
    (hs₀ : s₀ ∈ S) (P : MvPolynomial (Fin 2) (ZMod 2)) :
    ∃ g ∈ S, β g = MvPolynomial.aeval ![ζ ^ φ.1.val, ζ ^ φ.2.val] P * β s₀ ∧
      β' g = MvPolynomial.aeval ![ζ ^ φ'.1.val, ζ ^ φ'.2.val] P * β' s₀ := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    obtain rfl | rfl : r = 0 ∨ r = 1 := by decide +revert
    · exact ⟨1, S.one_mem, by simp [h.beta_one], by simp [h'.beta_one]⟩
    · exact ⟨s₀, hs₀, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨g₁, hg₁, e₁, e₁'⟩ := hp
    obtain ⟨g₂, hg₂, e₂, e₂'⟩ := hq
    refine ⟨g₁ * g₂, S.mul_mem hg₁ hg₂, ?_, ?_⟩
    · rw [h.map_mul _ hg₁ _ hg₂, e₁, e₂, map_add, add_mul]
    · rw [h'.map_mul _ hg₁ _ hg₂, e₁', e₂', map_add, add_mul]
  | mul_X p i hp =>
    obtain ⟨g, hg, e, e'⟩ := hp
    fin_cases i
    · refine ⟨d₁ * g * d₁⁻¹, (mem_normalizer_iff.1 hS₁ g).1 hg, ?_, ?_⟩
      · rw [h.conj₁ g hg, e]
        simp
        ring
      · rw [h'.conj₁ g hg, e']
        simp
        ring
    · refine ⟨d₂ * g * d₂⁻¹, (mem_normalizer_iff.1 hS₂ g).1 hg, ?_, ?_⟩
      · rw [h.conj₂ g hg, e]
        simp
        ring
      · rw [h'.conj₂ g hg, e']
        simp
        ring

private theorem IsChiEmb.relIndex_eq_ncard {v : GaloisField 2 n}
    (h : IsChiEmb ζ d₁ d₂ C S φ β) (hv : v ≠ 0) :
    C.relIndex S = {x | ∃ g ∈ S, β g = x * v}.ncard := by
  let ψ : S →* Multiplicative (GaloisField 2 n) :=
    { toFun := fun s => Multiplicative.ofAdd (β s)
      map_one' := by
        change Multiplicative.ofAdd (β ((1 : S) : G)) = 1
        rw [Subgroup.coe_one, h.beta_one]
        rfl
      map_mul' := fun s t => by
        change Multiplicative.ofAdd (β ((s * t : S) : G)) =
          Multiplicative.ofAdd (β s) * Multiplicative.ofAdd (β t)
        rw [← ofAdd_add]
        exact congrArg _ (h.map_mul s s.2 t t.2) }
  have hker : ψ.ker = C.subgroupOf S := by
    ext s
    simp [ψ, h.eq_zero_iff s s.2, Subgroup.mem_subgroupOf]
  have hrange : (ψ.range : Set (Multiplicative (GaloisField 2 n))) =
      (fun x => Multiplicative.ofAdd (x * v)) '' {x | ∃ g ∈ S, β g = x * v} := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨β s * v⁻¹, ⟨s, s.2, by rw [inv_mul_cancel_right₀ hv]⟩,
        by simp [ψ, inv_mul_cancel_right₀ hv]⟩
    · rintro ⟨y, ⟨g, hg, e⟩, rfl⟩
      exact ⟨⟨g, hg⟩, by simp [ψ, e]⟩
  have hinj : Function.Injective (fun x : GaloisField 2 n => Multiplicative.ofAdd (x * v)) :=
    fun x y hxy => mul_right_cancel₀ hv (Multiplicative.ofAdd.injective hxy)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker,
    show Nat.card ψ.range = (ψ.range : Set (Multiplicative (GaloisField 2 n))).ncard from
      Nat.card_coe_set_eq _, hrange, Set.ncard_image_of_injective _ hinj]

private theorem IsChiEmb.setOf_eq_range_aeval [Finite G] {s₀ : G}
    (h : IsChiEmb ζ d₁ d₂ C S φ β) (hY : IsYSimple (zpowers d₁ ⊔ zpowers d₂) C S)
    (hs₀S : s₀ ∈ S) (hs₀C : s₀ ∉ C) :
    {x | ∃ g ∈ S, β g = x * β s₀} =
      Set.range (MvPolynomial.aeval ![ζ ^ φ.1.val, ζ ^ φ.2.val] :
        MvPolynomial (Fin 2) (ZMod 2) →ₐ[ZMod 2] GaloisField 2 n) := by
  obtain ⟨hCS, -, -, hYS, hsimple⟩ := hY
  have hS₁ : d₁ ∈ normalizer (S : Set G) := hYS (mem_sup_left (mem_zpowers d₁))
  have hS₂ : d₂ ∈ normalizer (S : Set G) := hYS (mem_sup_right (mem_zpowers d₂))
  have hv : β s₀ ≠ 0 := fun h0 => hs₀C ((h.eq_zero_iff s₀ hs₀S).1 h0)
  obtain ⟨a, ha⟩ : ∃ a : GaloisField 2 n, a = ζ ^ φ.1.val := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : GaloisField 2 n, b = ζ ^ φ.2.val := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin 2) (ZMod 2) →ₐ[ZMod 2] GaloisField 2 n,
      f = MvPolynomial.aeval ![a, b] := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hf]
  have hc₁ : ∀ s ∈ S, β (d₁ * s * d₁⁻¹) = a * β s := fun s hs => by rw [ha]; exact h.conj₁ s hs
  have hc₂ : ∀ s ∈ S, β (d₂ * s * d₂⁻¹) = b * β s := fun s hs => by rw [hb]; exact h.conj₂ s hs
  have hf₁ : f (MvPolynomial.X 0) = a := by rw [hf]; simp
  have hf₂ : f (MvPolynomial.X 1) = b := by rw [hf]; simp
  have hmem : ∀ P, ∃ g ∈ S, β g = f P * β s₀ := by
    intro P
    obtain ⟨g, hg, e, -⟩ := exists_beta_aeval h h hS₁ hS₂ hs₀S P
    exact ⟨g, hg, by rw [hf, ha, hb]; exact e⟩
  let J : Subgroup G :=
    { carrier := {s | s ∈ S ∧ ∃ P, β s = f P * β s₀}
      mul_mem' := fun {s t} hs ht => by
        obtain ⟨hsS, P, hP⟩ := hs
        obtain ⟨htS, Q, hQ⟩ := ht
        exact ⟨S.mul_mem hsS htS, P + Q, by rw [h.map_mul s hsS t htS, hP, hQ, map_add, add_mul]⟩
      one_mem' := ⟨S.one_mem, 0, by rw [h.beta_one, map_zero, zero_mul]⟩
      inv_mem' := fun {s} hs => by
        obtain ⟨hsS, P, hP⟩ := hs
        exact ⟨S.inv_mem hsS, -P, by rw [h.beta_inv hsS, hP, map_neg, neg_mul]⟩ }
  have hJ : ∀ s, s ∈ J ↔ s ∈ S ∧ ∃ P, β s = f P * β s₀ := fun s => Iff.rfl
  have hCJ : C ≤ J := fun s hs => (hJ s).2 ⟨hCS.le hs, 0, by
    rw [(h.eq_zero_iff s (hCS.le hs)).2 hs, map_zero, zero_mul]⟩
  have hJS : J ≤ S := fun s hs => ((hJ s).1 hs).1
  have hSJ : S ≤ normalizer (J : Set G) := fun s hs => mem_normalizer_of_conj_mem_of fun j hj => by
    obtain ⟨hjS, P, hP⟩ := (hJ j).1 hj
    refine (hJ _).2 ⟨S.mul_mem (S.mul_mem hs hjS) (S.inv_mem hs), P, ?_⟩
    rw [h.map_mul (s * j) (S.mul_mem hs hjS) s⁻¹ (S.inv_mem hs), h.map_mul s hs j hjS,
      h.beta_inv hs, hP]
    ring
  have hd₁ : d₁ ∈ normalizer (J : Set G) := mem_normalizer_of_conj_mem_of fun j hj => by
    obtain ⟨hjS, P, hP⟩ := (hJ j).1 hj
    refine (hJ _).2 ⟨(mem_normalizer_iff.1 hS₁ j).1 hjS, P * MvPolynomial.X 0, ?_⟩
    rw [hc₁ j hjS, hP, _root_.map_mul, hf₁]
    ring
  have hd₂ : d₂ ∈ normalizer (J : Set G) := mem_normalizer_of_conj_mem_of fun j hj => by
    obtain ⟨hjS, P, hP⟩ := (hJ j).1 hj
    refine (hJ _).2 ⟨(mem_normalizer_iff.1 hS₂ j).1 hjS, P * MvPolynomial.X 1, ?_⟩
    rw [hc₂ j hjS, hP, _root_.map_mul, hf₂]
    ring
  have hirr : ∀ s ∈ S, ∃ P, β s = f P * β s₀ := by
    rcases hsimple J hCJ hJS hSJ (sup_le (zpowers_le.2 hd₁) (zpowers_le.2 hd₂)) with hJC | hJS'
    · have hs₀J : s₀ ∈ J := (hJ s₀).2 ⟨hs₀S, 1, by rw [_root_.map_one, one_mul]⟩
      rw [hJC] at hs₀J
      exact absurd hs₀J hs₀C
    · intro s hs
      exact ((hJ s).1 (hJS' ▸ hs)).2
  ext x
  constructor
  · rintro ⟨g, hg, e⟩
    obtain ⟨P, hP⟩ := hirr g hg
    exact ⟨P, mul_right_cancel₀ hv (hP.symm.trans e)⟩
  · rintro ⟨P, rfl⟩
    exact hmem P

end Embedding

private theorem exists_pow_eq_zpow {M : Type*} [Group M] [Finite M] (x : M) (m : ℤ) :
    ∃ k : ℕ, x ^ m = x ^ k := by
  refine ⟨(m % (orderOf x : ℤ)).toNat, ?_⟩
  have h0 : (orderOf x : ℤ) ≠ 0 := by exact_mod_cast (orderOf_pos x).ne'
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ h0), zpow_mod_orderOf]

private theorem exists_frob_pow_of_aeval {a b a' b' : GaloisField 2 n} (ha : a ≠ 0) (hb : b ≠ 0)
    (T : ∀ P : MvPolynomial (Fin 2) (ZMod 2), MvPolynomial.aeval ![a, b] P = 0 →
      MvPolynomial.aeval ![a', b'] P = 0) :
    ∃ j : ℕ, a' = a ^ 2 ^ j ∧ b' = b ^ 2 ^ j := by
  set A : (GaloisField 2 n)ˣ := Units.mk0 a ha with hA
  set B : (GaloisField 2 n)ˣ := Units.mk0 b hb with hB
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := closure ({A, B} : Set (GaloisField 2 n)ˣ))
  have hAmem : A ∈ closure ({A, B} : Set (GaloisField 2 n)ˣ) := subset_closure (by simp)
  have hBmem : B ∈ closure ({A, B} : Set (GaloisField 2 n)ˣ) := subset_closure (by simp)
  have hpow : ∀ x : closure ({A, B} : Set (GaloisField 2 n)ˣ), ∃ k : ℕ,
      (γ : (GaloisField 2 n)ˣ) ^ k = x := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ x)
    obtain ⟨k, hk⟩ := exists_pow_eq_zpow (γ : (GaloisField 2 n)ˣ) m
    exact ⟨k, by rw [← hk, ← hm]; rfl⟩
  obtain ⟨k, hk⟩ := hpow ⟨A, hAmem⟩
  obtain ⟨l, hl⟩ := hpow ⟨B, hBmem⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, A ^ u * B ^ v = (γ : (GaloisField 2 n)ˣ) := by
    obtain ⟨m₁, m₂, h⟩ := Subgroup.mem_closure_pair.1 γ.2
    obtain ⟨u, hu⟩ := exists_pow_eq_zpow A m₁
    obtain ⟨v, hv⟩ := exists_pow_eq_zpow B m₂
    exact ⟨u, v, by rw [← hu, ← hv]; exact h⟩
  set c : GaloisField 2 n := ((γ : (GaloisField 2 n)ˣ) : GaloisField 2 n) with hc
  have hcab : c = a ^ u * b ^ v := by
    rw [hc, ← huv]
    simp [hA, hB]
  have hca : c ^ k = a := by
    have := congrArg (fun x : (GaloisField 2 n)ˣ => (x : GaloisField 2 n)) hk
    simpa [hc, hA] using this
  have hcb : c ^ l = b := by
    have := congrArg (fun x : (GaloisField 2 n)ˣ => (x : GaloisField 2 n)) hl
    simpa [hc, hB] using this
  set c' : GaloisField 2 n := a' ^ u * b' ^ v with hc'
  have key : ∀ (x y : GaloisField 2 n) (P : Polynomial (ZMod 2)),
      MvPolynomial.aeval ![x, y]
        (Polynomial.aeval ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 2)) ^ u *
          MvPolynomial.X 1 ^ v) P) = Polynomial.aeval (x ^ u * y ^ v) P := by
    intro x y P
    rw [← Polynomial.aeval_algHom_apply]
    simp
  have T1 : ∀ P : Polynomial (ZMod 2), Polynomial.aeval c P = 0 → Polynomial.aeval c' P = 0 := by
    intro P hP
    rw [hcab, ← key] at hP
    have := T _ hP
    rwa [key] at this
  have T2 : a' = c' ^ k := by
    have h0 : MvPolynomial.aeval ![a, b]
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 2)) -
          (MvPolynomial.X 0 ^ u * MvPolynomial.X 1 ^ v) ^ k) = 0 := by
      simp only [map_sub, map_pow, map_mul, MvPolynomial.aeval_X]
      simp [← hcab, hca]
    have := T _ h0
    simp only [map_sub, map_pow, map_mul, MvPolynomial.aeval_X] at this
    simpa [hc', sub_eq_zero] using this
  have T3 : b' = c' ^ l := by
    have h0 : MvPolynomial.aeval ![a, b]
        ((MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 2)) -
          (MvPolynomial.X 0 ^ u * MvPolynomial.X 1 ^ v) ^ l) = 0 := by
      simp only [map_sub, map_pow, map_mul, MvPolynomial.aeval_X]
      simp [← hcab, hcb]
    have := T _ h0
    simp only [map_sub, map_pow, map_mul, MvPolynomial.aeval_X] at this
    simpa [hc', sub_eq_zero] using this
  have hint : IsIntegral (ZMod 2) c := Algebra.IsIntegral.isIntegral c
  have hmin : minpoly (ZMod 2) c' = minpoly (ZMod 2) c :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) (T1 _ (minpoly.aeval _ c))
      (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1
    ((Normal.minpoly_eq_iff_mem_orbit (F := ZMod 2) (GaloisField 2 n)).1 hmin)
  rw [AlgEquiv.smul_def] at hτ
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 (GaloisField 2 n) τ
  rw [Nat.card_zmod] at hj
  refine ⟨j, ?_, ?_⟩
  · rw [T2, ← hτ, ← hca, ← map_pow, hj]
  · rw [T3, ← hτ, ← hcb, ← map_pow, hj]

theorem IsChiEmb.chiLab_subset_cls {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G}
    {φ : Coord n} {β : G → GaloisField 2 n} (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) (hS₁ : d₁ ∈ normalizer (S : Set G))
    (hS₂ : d₂ ∈ normalizer (S : Set G)) (hCS : ¬ S ≤ C) :
    chiLab ζ d₁ d₂ C S ⊆ (cls φ : Set (Coord n)) := by
  rintro φ' ⟨β', h'⟩
  obtain ⟨s₀, hs₀S, hs₀C⟩ := SetLike.not_le_iff_exists.1 hCS
  have hv' : β' s₀ ≠ 0 := fun h0 => hs₀C ((h'.eq_zero_iff s₀ hs₀S).1 h0)
  have hζ0 : ζ ≠ 0 := ζ_ne_zero hn hζ
  have T : ∀ P : MvPolynomial (Fin 2) (ZMod 2),
      MvPolynomial.aeval ![ζ ^ φ.1.val, ζ ^ φ.2.val] P = 0 →
        MvPolynomial.aeval ![ζ ^ φ'.1.val, ζ ^ φ'.2.val] P = 0 := by
    intro P hP
    obtain ⟨g, hg, e, e'⟩ := exists_beta_aeval h h' hS₁ hS₂ hs₀S P
    rw [hP, zero_mul] at e
    have h0 := (h'.eq_zero_iff g hg).2 ((h.eq_zero_iff g hg).1 e)
    rw [e'] at h0
    exact (mul_eq_zero.1 h0).resolve_right hv'
  obtain ⟨j, hj₁, hj₂⟩ := exists_frob_pow_of_aeval (pow_ne_zero _ hζ0) (pow_ne_zero _ hζ0) T
  rw [pow_val_pow_two_pow hn hζ, pow_val_eq_pow_val_iff hn hζ] at hj₁ hj₂
  refine Finset.mem_coe.2 (Finset.mem_image.2
    ⟨j % n, Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hn)), ?_⟩)
  ext
  · simp [two_pow_mod, hj₁]
  · simp [two_pow_mod, hj₂]

private theorem pow_two_pow_eq_of_mem_range {a b : GaloisField 2 n} {e : ℕ}
    (ha : a ^ 2 ^ e = a) (hb : b ^ 2 ^ e = b) {y : GaloisField 2 n}
    (hy : y ∈ Set.range (MvPolynomial.aeval ![a, b] :
      MvPolynomial (Fin 2) (ZMod 2) →ₐ[ZMod 2] GaloisField 2 n)) : y ^ 2 ^ e = y := by
  obtain ⟨P, rfl⟩ := hy
  induction P using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.aeval_C, ← map_pow, ZMod.pow_card_pow]
  | add p q hp hq => rw [map_add, add_pow_char_pow, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, mul_pow, hp, MvPolynomial.aeval_X]
    fin_cases i <;> simp [ha, hb]

private theorem ncard_le_two_pow {e : ℕ} (he : e ≠ 0) {T : Set (GaloisField 2 n)}
    (hT : ∀ y ∈ T, y ^ 2 ^ e = y) : T.ncard ≤ 2 ^ e := by
  classical
  set p : Polynomial (GaloisField 2 n) := Polynomial.X ^ 2 ^ e - Polynomial.X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ he one_lt_two
  have hsub : T ⊆ (p.roots.toFinset : Set (GaloisField 2 n)) := by
    intro y hy
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.2 (hT y hy)
  calc T.ncard ≤ (p.roots.toFinset : Set (GaloisField 2 n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = 2 ^ e := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ he one_lt_two

private theorem ncard_range_aeval_eq {a b : GaloisField 2 n} {d : ℕ} (hd : d ≠ 0)
    (hab : a ^ 2 ^ d = a ∧ b ^ 2 ^ d = b)
    (hmin : ∀ e, e ≠ 0 → a ^ 2 ^ e = a → b ^ 2 ^ e = b → d ≤ e) :
    (Set.range (MvPolynomial.aeval ![a, b] :
      MvPolynomial (Fin 2) (ZMod 2) →ₐ[ZMod 2] GaloisField 2 n)).ncard = 2 ^ d := by
  classical
  set f : MvPolynomial (Fin 2) (ZMod 2) →ₐ[ZMod 2] GaloisField 2 n := MvPolynomial.aeval ![a, b]
    with hf
  have hinv : ∀ x ∈ f.range, x⁻¹ ∈ f.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic f.range (x := ⟨x, hx⟩) (Algebra.IsAlgebraic.isAlgebraic _)
  let K : IntermediateField (ZMod 2) (GaloisField 2 n) := f.range.toIntermediateField hinv
  have hmemK : ∀ y, y ∈ K ↔ y ∈ Set.range f := fun y => Iff.rfl
  have hcard : (Set.range f).ncard = Nat.card K :=
    (Nat.card_coe_set_eq _).symm.trans (Nat.card_congr (Equiv.subtypeEquivRight hmemK).symm)
  have hpow : 2 ^ Module.finrank (ZMod 2) K = Nat.card K := FiniteField.pow_finrank_eq_natCard 2 K
  set k := Module.finrank (ZMod 2) K with hk
  have hfix : ∀ y ∈ K, y ^ 2 ^ k = y := by
    intro y hy
    letI : Fintype K := Fintype.ofFinite K
    have h1 := FiniteField.pow_card (⟨y, hy⟩ : K)
    rw [← Nat.card_eq_fintype_card, ← hpow] at h1
    simpa using congrArg Subtype.val h1
  have haK : a ∈ K := (hmemK a).2 ⟨MvPolynomial.X 0, by simp [hf]⟩
  have hbK : b ∈ K := (hmemK b).2 ⟨MvPolynomial.X 1, by simp [hf]⟩
  have hk0 : k ≠ 0 := by
    intro h0
    have h1 := Finite.one_lt_card (α := K)
    rw [← hpow, h0] at h1
    simp at h1
  have hdk : d ≤ k := hmin k hk0 (hfix a haK) (hfix b hbK)
  have hkd : k ≤ d := by
    have h1 : Nat.card K ≤ 2 ^ d := by
      rw [← hcard]
      exact ncard_le_two_pow hd fun y hy => pow_two_pow_eq_of_mem_range hab.1 hab.2 hy
    rw [← hpow] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  rw [hcard, ← hpow, le_antisymm hkd hdk]

theorem IsChiEmb.relIndex_eq [Finite G] {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G}
    {φ : Coord n} {β : G → GaloisField 2 n} (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) (hY : IsYSimple (zpowers d₁ ⊔ zpowers d₂) C S) :
    C.relIndex S = 2 ^ (cls φ).card := by
  obtain ⟨s₀, hs₀S, hs₀C⟩ := SetLike.exists_of_lt hY.1
  have hv : β s₀ ≠ 0 := fun h0 => hs₀C ((h.eq_zero_iff s₀ hs₀S).1 h0)
  rw [h.relIndex_eq_ncard hv, h.setOf_eq_range_aeval hY hs₀S hs₀C, card_cls_eq_minimalPeriod hn φ]
  have hper := Function.isPeriodicPt_minimalPeriod (frobStep n) φ
  have hpos : 0 < Function.minimalPeriod (frobStep n) φ :=
    (isPeriodicPt_frobStep_self φ).minimalPeriod_pos (Nat.pos_of_ne_zero hn)
  rw [isPeriodicPt_frobStep_iff] at hper
  refine ncard_range_aeval_eq hpos.ne' ⟨?_, ?_⟩ fun e he ha hb => ?_
  · rw [pow_two_pow_eq_iff hn hζ]
    exact hper.1
  · rw [pow_two_pow_eq_iff hn hζ]
    exact hper.2
  · rw [pow_two_pow_eq_iff hn hζ] at ha hb
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero he)
      ((isPeriodicPt_frobStep_iff e φ).2 ⟨ha, hb⟩).minimalPeriod_dvd

end CFSG.Quasithin.Stroth.G5

end
