module

public import CFSG.Quasithin.Background.E2PairMore
public import CFSG.CGT.Timmesfeld75.Dihedral
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

section Dihedral

variable {Y : Type*} [Group Y] {a b : Y}

theorem conj_mul_eq_inv (ha : a * a = 1) (hb : b * b = 1) : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]

theorem conj_mul_eq_inv' (ha : a * a = 1) (hb : b * b = 1) : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [mul_inv_rev, hai, hbi, mul_assoc, mul_assoc, hb, mul_one]

theorem conj_zpow_eq (ha : a * a = 1) (hb : b * b = 1) {x : Y} (hx : x = a ∨ x = b) (k : ℤ) :
    x * (a * b) ^ k * x⁻¹ = (a * b) ^ (-k) := by
  have h : x * (a * b) * x⁻¹ = (a * b)⁻¹ := by
    rcases hx with rfl | rfl
    · exact conj_mul_eq_inv ha hb
    · exact conj_mul_eq_inv' ha hb
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, zpow_neg, inv_zpow]

theorem odd_orderOf_of_conj (ha : a * a = 1) (hb : b * b = 1)
    (hgen : Subgroup.closure ({a, b} : Set Y) = ⊤) {y : Y} (hy : y * a * y⁻¹ = b) :
    Odd (orderOf (a * b)) := by
  set c := a * b with hc
  set E := Subgroup.zpowers (c ^ 2) with hE
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hnorm : ∀ x : Y, (x = a ∨ x = b) → x ∈ Subgroup.normalizer (E : Set Y) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 fun e => ⟨fun he => ?_, fun he => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, conj_zpow_eq ha hb hx]
      congr 1; ring
    · have h2 : x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e := by group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
      have : e = x⁻¹ * (c ^ 2) ^ k * x := by rw [hk]; group
      refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
      have hx' : x⁻¹ = x := by rcases hx with rfl | rfl <;> assumption
      rw [this, hx', ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      have := conj_zpow_eq ha hb hx ((2 : ℕ) * k)
      rw [hx'] at this
      rw [this]
      congr 1; push_cast; ring
  have hEn : E.Normal := by
    have hle : Subgroup.closure ({a, b} : Set Y) ≤ Subgroup.normalizer (E : Set Y) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hnorm _ (Or.inl rfl)
      · exact hnorm _ (Or.inr rfl)
    rw [hgen, top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.1 hle
  have key : ∀ x : Y, a⁻¹ * (x * a * x⁻¹) ∈ E := by
    intro x
    have hx : x ∈ Subgroup.closure ({a, b} : Set Y) := hgen ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · simp
      · rw [hai, hbi]
        exact Subgroup.mem_zpowers_iff.2 ⟨1, by rw [zpow_one, hc, pow_two]; group⟩
    | one => simp
    | mul x₁ x₂ _ _ h₁ h₂ =>
      have e : a⁻¹ * (x₁ * x₂ * a * (x₁ * x₂)⁻¹) =
          (a⁻¹ * (x₁ * a * x₁⁻¹)) * (x₁ * (a⁻¹ * (x₂ * a * x₂⁻¹)) * x₁⁻¹) := by group
      rw [e]
      exact E.mul_mem h₁ (hEn.conj_mem _ h₂ x₁)
    | inv x _ h₁ =>
      have e : a⁻¹ * (x⁻¹ * a * x⁻¹⁻¹) = (x⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * x⁻¹⁻¹)⁻¹ := by group
      rw [e]
      exact E.inv_mem (hEn.conj_mem _ h₁ x⁻¹)
  have hcE : c ∈ E := by
    have := key y
    rwa [hy, hai] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcE
  have h1 : c ^ (2 * k - 1) = 1 := by
    rw [zpow_sub, zpow_one, zpow_mul, zpow_ofNat, hk, mul_inv_cancel]
  have hdvd : (orderOf c : ℤ) ∣ 2 * k - 1 := orderOf_dvd_iff_zpow_eq_one.2 h1
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨m, hm⟩ := hev
  have h2 : (2 : ℤ) ∣ (orderOf c : ℤ) := by
    rw [hm]
    exact ⟨m, by push_cast; ring⟩
  have : (2 : ℤ) ∣ 2 * k - 1 := h2.trans hdvd
  omega

theorem exists_normal_form (ha : a * a = 1) (hb : b * b = 1)
    (hgen : Subgroup.closure ({a, b} : Set Y) = ⊤) (x : Y) :
    ∃ i : ℤ, x = (a * b) ^ i ∨ x = a * (a * b) ^ i := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hca : ∀ i : ℤ, (a * b) ^ i * a = a * (a * b) ^ (-i) := by
    intro i
    have h := conj_zpow_eq ha hb (Or.inl rfl) i
    calc (a * b) ^ i * a = a * (a * (a * b) ^ i * a⁻¹) := by
          rw [hai, ← mul_assoc, ← mul_assoc, ha, one_mul]
      _ = a * (a * b) ^ (-i) := by rw [h]
  have hx : x ∈ Subgroup.closure ({a, b} : Set Y) := hgen ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨1, Or.inr ?_⟩
      rw [zpow_one, ← mul_assoc, ha, one_mul]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy <;> subst hi hj
    · exact ⟨i + j, Or.inl (by rw [zpow_add])⟩
    · refine ⟨-i + j, Or.inr ?_⟩
      rw [← mul_assoc, hca, mul_assoc, ← zpow_add]
    · exact ⟨i + j, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
    · refine ⟨-i + j, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc ((a * b) ^ i), hca, ← mul_assoc, ← mul_assoc, ha, one_mul,
        ← zpow_add]
  | inv x _ hx =>
    obtain ⟨i, hi | hi⟩ := hx <;> subst hi
    · exact ⟨-i, Or.inl (by rw [zpow_neg])⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [mul_inv_rev, ← zpow_neg, hai, hca, neg_neg]

theorem eq_one_of_mem_center (ha : a * a = 1) (hb : b * b = 1)
    (hgen : Subgroup.closure ({a, b} : Set Y) = ⊤) (hodd : Odd (orderOf (a * b))) {z : Y}
    (hz : z ∈ Subgroup.center Y) : z = 1 ∨ a * b = 1 := by
  obtain ⟨i, rfl | rfl⟩ := exists_normal_form ha hb hgen z
  · left
    have h1 : a * (a * b) ^ i * a⁻¹ = (a * b) ^ i := by
      rw [Subgroup.mem_center_iff.1 hz a, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_zpow_eq ha hb (Or.inl rfl)] at h1
    have h2 : (a * b) ^ (2 * i) = 1 := by
      have : (a * b) ^ (2 * i) = ((a * b) ^ (-i))⁻¹ * (a * b) ^ i := by
        rw [← zpow_neg, neg_neg, ← zpow_add]; congr 1; ring
      rw [this, h1, inv_mul_cancel]
    have hdvd : (orderOf (a * b) : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.2 h2
    have hcop : IsCoprime (orderOf (a * b) : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime (orderOf (a * b)) 2 := (Nat.coprime_two_right.2 hodd)
      exact_mod_cast this
    exact orderOf_dvd_iff_zpow_eq_one.1 (hcop.dvd_of_dvd_mul_left hdvd)
  · right
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hca1 : (a * b) * a = a * (a * b) ^ (-1 : ℤ) := by
      have h := conj_zpow_eq ha hb (Or.inl rfl) 1
      rw [zpow_one] at h
      calc (a * b) * a = a * (a * (a * b) * a⁻¹) := by
            rw [hai, ← mul_assoc, ← mul_assoc, ha, one_mul]
        _ = a * (a * b) ^ (-1 : ℤ) := by rw [h]
    have hzc : a * b * (a * (a * b) ^ i) = a * (a * b) ^ i * (a * b) :=
      Subgroup.mem_center_iff.1 hz (a * b)
    have e1 : a * b * (a * (a * b) ^ i) = a * (a * b) ^ (-1 + i) := by
      rw [← mul_assoc, hca1, mul_assoc, ← zpow_add]
    have e2 : a * (a * b) ^ i * (a * b) = a * (a * b) ^ (i + 1) := by
      rw [mul_assoc, zpow_add_one]
    rw [e1, e2] at hzc
    have h3 : (a * b) ^ (-1 + i) = (a * b) ^ (i + 1) := mul_left_cancel hzc
    have h2 : (a * b) ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = (i + 1) - (-1 + i) by ring, zpow_sub, ← h3, mul_inv_cancel]
    have h2' : (a * b) ^ 2 = 1 := by rwa [zpow_ofNat] at h2
    have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
    have h1' : orderOf (a * b) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 h1'

end Dihedral

namespace Pair

variable {G : Type} [Group G] {X T M V : Subgroup G} {g : G}

theorem closure_mk_eq_top (h : Pair X T M V g) {K : Subgroup G} [(K.subgroupOf X).Normal]
    (hBK : kerIn M X ⊓ V ≤ K) (hAK : conjSub g (kerIn M X ⊓ V) ≤ K) {v : G} (hv : v ∈ V)
    (hvB : v ∉ kerIn M X ⊓ V) (hidx : (kerIn M X ⊓ V).relIndex V = 2) :
    Subgroup.closure ({((⟨v, h.V_le hv⟩ : X) : X ⧸ K.subgroupOf X),
      ((⟨g * v * g⁻¹, h.conj_le (mem_conjSub.2 (by group; exact hv))⟩ : X) :
        X ⧸ K.subgroupOf X)} : Set (X ⧸ K.subgroupOf X)) = ⊤ := by
  set S := Subgroup.closure ({((⟨v, h.V_le hv⟩ : X) : X ⧸ K.subgroupOf X),
      ((⟨g * v * g⁻¹, h.conj_le (mem_conjSub.2 (by group; exact hv))⟩ : X) :
        X ⧸ K.subgroupOf X)} : Set (X ⧸ K.subgroupOf X)) with hS
  have hidx' : ((kerIn M X ⊓ V).subgroupOf V).index = 2 := hidx
  have hdich : ∀ u ∈ V, u ∈ kerIn M X ⊓ V ∨ v⁻¹ * u ∈ kerIn M X ⊓ V := by
    intro u hu
    by_cases huB : u ∈ kerIn M X ⊓ V
    · exact Or.inl huB
    · right
      have key := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨v⁻¹, V.inv_mem hv⟩)
        (b := ⟨u, hu⟩)
      simp only [Subgroup.mem_subgroupOf] at key
      have hv' : v⁻¹ ∉ kerIn M X ⊓ V := fun h' => hvB (by simpa using (kerIn M X ⊓ V).inv_mem h')
      exact key.2 (iff_of_false hv' huB)
  have hmk1 : ∀ (u : G) (hu : u ∈ X), u ∈ K → ((⟨u, hu⟩ : X) : X ⧸ K.subgroupOf X) = 1 :=
    fun u hu huK => (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 huK)
  have hmain : ∀ y ∈ (V ⊔ conjSub g V : Subgroup G), ∀ hy : y ∈ X,
      ((⟨y, hy⟩ : X) : X ⧸ K.subgroupOf X) ∈ S := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem u hu =>
      intro huX
      rcases hu with hu | hu
      · rcases hdich u hu with huB | huB
        · rw [hmk1 u huX (hBK huB)]; exact S.one_mem
        · have e : ((⟨u, huX⟩ : X) : X ⧸ K.subgroupOf X) =
              ((⟨v, h.V_le hv⟩ : X) : X ⧸ K.subgroupOf X) *
                ((⟨v⁻¹ * u, X.mul_mem (X.inv_mem (h.V_le hv)) huX⟩ : X) : X ⧸ K.subgroupOf X) := by
            rw [← QuotientGroup.mk_mul]; congr 1; ext; simp
          rw [e, hmk1 _ _ (hBK huB), mul_one]
          exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have hu' : g⁻¹ * u * g ∈ V := mem_conjSub.1 hu
        rcases hdich _ hu' with huB | huB
        · have : u ∈ conjSub g (kerIn M X ⊓ V) := mem_conjSub.2 huB
          rw [hmk1 u huX (hAK this)]; exact S.one_mem
        · have hw : (g * v * g⁻¹)⁻¹ * u ∈ conjSub g (kerIn M X ⊓ V) := by
            rw [mem_conjSub]
            have e : g⁻¹ * ((g * v * g⁻¹)⁻¹ * u) * g = v⁻¹ * (g⁻¹ * u * g) := by group
            rw [e]; exact huB
          have hwX : g * v * g⁻¹ ∈ X := h.conj_le (mem_conjSub.2 (by group; exact hv))
          have e : ((⟨u, huX⟩ : X) : X ⧸ K.subgroupOf X) =
              ((⟨g * v * g⁻¹, hwX⟩ : X) : X ⧸ K.subgroupOf X) *
                ((⟨(g * v * g⁻¹)⁻¹ * u, X.mul_mem (X.inv_mem hwX) huX⟩ : X) :
                  X ⧸ K.subgroupOf X) := by
            rw [← QuotientGroup.mk_mul]; congr 1; ext
            simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv]; group
          rw [e, hmk1 _ _ (hAK hw), mul_one]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one =>
      intro hy1
      rw [hmk1 1 hy1 K.one_mem]
      exact S.one_mem
    | mul x y hx hy ihx ihy =>
      intro hxyX
      have hxX : x ∈ X := by rw [← Subgroup.sup_eq_closure, ← h.gen] at hx; exact hx
      have hyX : y ∈ X := by rw [← Subgroup.sup_eq_closure, ← h.gen] at hy; exact hy
      have e : ((⟨x * y, hxyX⟩ : X) : X ⧸ K.subgroupOf X) =
          ((⟨x, hxX⟩ : X) : X ⧸ K.subgroupOf X) * ((⟨y, hyX⟩ : X) : X ⧸ K.subgroupOf X) := by
        rw [← QuotientGroup.mk_mul]; rfl
      rw [e]; exact S.mul_mem (ihx hxX) (ihy hyX)
    | inv x hx ihx =>
      intro hxX'
      have hxX : x ∈ X := by rw [← Subgroup.sup_eq_closure, ← h.gen] at hx; exact hx
      have e : ((⟨x⁻¹, hxX'⟩ : X) : X ⧸ K.subgroupOf X) =
          (((⟨x, hxX⟩ : X) : X ⧸ K.subgroupOf X))⁻¹ := by
        rw [← QuotientGroup.mk_inv]; rfl
      rw [e]; exact S.inv_mem (ihx hxX)
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  exact hmain y (h.gen ▸ hy) hy

theorem e2_10_six [Finite G] (h : Pair X T M V g) (hidx : (kerIn M X ⊓ V).relIndex V = 2) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) = pCoreOf 2 X ∧ pCoreOf 2 X = kerIn M X ∧
      ∃ m : ℕ, Odd m ∧ Nonempty (StarQuot M X ≃* DihedralGroup m) := by
  set J := kerIn M X with hJ
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  obtain ⟨v, hvV, hvB⟩ : ∃ v ∈ V, v ∉ kerIn M X ⊓ V := by
    by_contra hne
    push Not at hne
    have h1 : (kerIn M X ⊓ V).relIndex V = 1 := Subgroup.relIndex_eq_one.2 hne
    exact absurd (h1.symm.trans hidx) (by norm_num)
  have hvX : v ∈ X := h.V_le hvV
  have hwX : g * v * g⁻¹ ∈ X := h.conj_le (mem_conjSub.2 (by group; exact hvV))
  have hgX : g ∈ X := h.mem
  have hv2 : v * v = 1 := by rw [← pow_two]; exact h.elem.2 v hvV
  have hw2 : g * v * g⁻¹ * (g * v * g⁻¹) = 1 := by
    have : g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
    rw [this, hv2]; group
  have hJX : J ≤ X := kerIn_le.trans h.le_X
  have hPX : P ≤ X := h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hPJ : P ≤ J := h.P_le_pCoreOf.trans h.pCoreOf_le_kerIn
  have hPn : (P.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).2 h.le_normalizer_P
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (le_normalizer_kerIn M X)
  set a : X ⧸ P.subgroupOf X := ((⟨v, hvX⟩ : X) : X ⧸ P.subgroupOf X) with ha
  set b : X ⧸ P.subgroupOf X := ((⟨g * v * g⁻¹, hwX⟩ : X) : X ⧸ P.subgroupOf X) with hb
  have ha2 : a * a = 1 := by
    rw [ha, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simp [hv2]))
  have hb2 : b * b = 1 := by
    rw [hb, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simp [hw2]))
  have hgen : Subgroup.closure ({a, b} : Set (X ⧸ P.subgroupOf X)) = ⊤ :=
    h.closure_mk_eq_top le_sup_left le_sup_right hvV hvB hidx
  have hconj : ((⟨g, hgX⟩ : X) : X ⧸ P.subgroupOf X) * a *
      (((⟨g, hgX⟩ : X) : X ⧸ P.subgroupOf X))⁻¹ = b := by
    rw [ha, hb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hodd : Odd (orderOf (a * b)) := odd_orderOf_of_conj ha2 hb2 hgen hconj
  have hJP : J ≤ P := by
    intro j hj
    have hjX : j ∈ X := hJX hj
    have hcen : ((⟨j, hjX⟩ : X) : X ⧸ P.subgroupOf X) ∈ Subgroup.center (X ⧸ P.subgroupOf X) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hc := h.commutator_kerIn_mem_P hx hj
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have key : (x * j)⁻¹ * (j * x) = (x * j)⁻¹ * (x * j * x⁻¹ * j⁻¹)⁻¹ * ((x * j)⁻¹)⁻¹ := by
        group
      rw [key]
      exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_P (X.inv_mem (X.mul_mem hx hjX)))
        _).mp (P.inv_mem hc)
    rcases eq_one_of_mem_center ha2 hb2 hgen hodd hcen with h1 | h1
    · exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
    · exfalso
      have hdd : ∀ d (hd : d ∈ X), d * d ∈ P := by
        intro d hd
        have hq : ((⟨d, hd⟩ : X) : X ⧸ P.subgroupOf X) *
            ((⟨d, hd⟩ : X) : X ⧸ P.subgroupOf X) = 1 := by
          obtain ⟨i, hi | hi⟩ := exists_normal_form ha2 hb2 hgen
            ((⟨d, hd⟩ : X) : X ⧸ P.subgroupOf X)
          · rw [hi, h1, one_zpow, one_mul]
          · rw [hi, h1, one_zpow, mul_one, ha2]
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
        simpa using hq
      have hXJ : X ≤ J :=
        h.le_kerIn_of_isTwoQuotient le_rfl Subgroup.le_normalizer hJX fun d hd =>
          ⟨1, by rw [pow_one, pow_two]; exact hPJ (hdd d hd)⟩
      exact hvB ⟨hXJ hvX, hvV⟩
  have hPO : P = pCoreOf 2 X := le_antisymm h.P_le_pCoreOf (h.pCoreOf_le_kerIn.trans hJP)
  refine ⟨hPO, le_antisymm h.pCoreOf_le_kerIn (hJP.trans h.P_le_pCoreOf), ?_⟩
  set a' : X ⧸ J.subgroupOf X := ((⟨v, hvX⟩ : X) : X ⧸ J.subgroupOf X) with ha'
  set b' : X ⧸ J.subgroupOf X := ((⟨g * v * g⁻¹, hwX⟩ : X) : X ⧸ J.subgroupOf X) with hb'
  have ha2' : a' * a' = 1 := by
    rw [ha', ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simp [hv2]))
  have hb2' : b' * b' = 1 := by
    rw [hb', ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simp [hw2]))
  have ha1' : a' ≠ 1 := by
    intro h1
    have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
    exact hvB ⟨this, hvV⟩
  have hgen' : Subgroup.closure ({a', b'} : Set (X ⧸ J.subgroupOf X)) = ⊤ :=
    h.closure_mk_eq_top inf_le_left (h.A_le_pCoreOf.trans h.pCoreOf_le_kerIn) hvV hvB hidx
  have hpow : (a' * b') ^ orderOf (a * b) = 1 := by
    have h1 : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
    rw [ha, hb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    rw [ha', hb', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hPJ h1
  have hodd' : Odd (orderOf (a' * b')) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hpow)
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.dihedral_mulEquiv_of_involutions hodd' ha2' ha1' hb2' rfl
    hgen'
  exact ⟨orderOf (a' * b'), hodd', ⟨e.symm⟩⟩

end Pair

end E2

end CFSG.Quasithin
