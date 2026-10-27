module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.LieType.BorelTits Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (g : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {X : Subgroup G} : x ∈ cj g X ↔ g⁻¹ * x * g ∈ X := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_cj_iff {g x : G} {X : Subgroup G} : x ∈ cj g X ↔ ∃ y ∈ X, g * y * g⁻¹ = x := by
  unfold cj
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem conj_mem_cj {g y : G} {X : Subgroup G} (hy : y ∈ X) : g * y * g⁻¹ ∈ cj g X :=
  mem_cj_iff.2 ⟨y, hy, rfl⟩

theorem cj_one (X : Subgroup G) : cj 1 X = X := by
  ext x; rw [mem_cj]; simp

theorem cj_mul (g h : G) (X : Subgroup G) : cj (g * h) X = cj g (cj h X) := by
  ext x
  simp only [mem_cj]
  simp [mul_assoc]

theorem conjAct_apply_coe' (W : Subgroup G) (g : normalizer (W : Set G)) (w : W) :
    ((conjAct W g w : W) : G) = g * w * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl g) w

theorem conjAct_eq_one_iff (W : Subgroup G) (x : normalizer (W : Set G)) :
    conjAct W x = 1 ↔ (x : G) ∈ centralizer (W : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff x


namespace A4Data

variable {X W : Subgroup G} {c : G} (h : A4Data X W c)
include h

theorem map (e : G ≃* G) :
    A4Data (X.map e.toMonoidHom) (W.map e.toMonoidHom) (e c) where
  le := Subgroup.map_mono h.le
  card_W := by rw [Subgroup.card_map_of_injective e.injective]; exact h.card_W
  sq_eq_one := by
    rintro _ ⟨w, hw, rfl⟩
    show e w ^ 2 = 1
    rw [← map_pow, h.sq_eq_one w hw, map_one]
  comm := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    show e u * e v = e v * e u
    rw [← map_mul, ← map_mul, h.comm u hu v hv]
  mem_X := ⟨c, h.mem_X, rfl⟩
  order_c := by rw [MulEquiv.orderOf_eq]; exact h.order_c
  mem_normalizer := by
    rw [← Subgroup.map_equiv_normalizer_eq W e]
    exact ⟨c, h.mem_normalizer, rfl⟩
  fpf := by
    rintro _ ⟨w, hw, rfl⟩ hw1 hfix
    apply h.fpf w hw (fun h' => hw1 (by rw [h', map_one]))
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    exact hfix
  eq_sup := by
    rw [h.eq_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  card_X := by rw [Subgroup.card_map_of_injective e.injective]; exact h.card_X
  center := by
    rintro _ ⟨x, hx, rfl⟩ hcen
    have : x = 1 := by
      apply h.center x hx
      intro l hl
      apply e.injective
      rw [map_mul, map_mul]
      exact hcen (e l) ⟨l, hl, rfl⟩
    rw [this, map_one]

theorem card_mulAut : Nat.card (MulAut W) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite W := h.finite_W
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := W)
    (fun a b => Subtype.ext (h.comm a a.2 b b.2))
    (fun a => Subtype.ext (h.sq_eq_one a a.2)) (n := 2) (by rw [h.card_W]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod,
    Fin.prod_univ_two]
  norm_num

theorem exists_zpow_inv_mul_mem_centralizer_of_odd {g : G}
    (hgW : g ∈ normalizer (W : Set G)) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m ∈ centralizer (W : Set G)) :
    ∃ i : ℤ, (c ^ i)⁻¹ * g ∈ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcW := h.mem_normalizer
  set a : MulAut W := conjAct W ⟨c, hcW⟩ with ha
  set γ : MulAut W := conjAct W ⟨g, hgW⟩ with hγ
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow]
    rw [conjAct_eq_one_iff]
    show c ^ 3 ∈ centralizer (W : Set G)
    rw [h.c_pow_three]; exact one_mem _
  have ha1 : a ≠ 1 := by
    intro h1
    rw [ha, conjAct_eq_one_iff] at h1
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_mem_W
    apply h.fpf u hu hu1
    have := mem_centralizer_iff.1 h1 u hu
    calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [this]
      _ = u := by group
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  set P : Subgroup (MulAut W) := Subgroup.zpowers a with hP
  have hPcard : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hord]
  have hidx : P.index = 2 := by
    have := Subgroup.card_mul_index P
    rw [hPcard, h.card_mulAut] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hγm : γ ^ m = 1 := by
    rw [hγ, ← map_pow, conjAct_eq_one_iff]
    exact hgm
  have hγ2 : γ ^ 2 ∈ P := by
    have := Subgroup.pow_index_mem P γ
    rwa [hidx] at this
  have hγP : γ ∈ P := by
    obtain ⟨j, rfl⟩ := hm
    have : γ = (γ ^ 2) ^ (j + 1) := by
      calc γ = γ ^ (2 * j + 1) * γ := by rw [hγm, one_mul]
        _ = (γ ^ 2) ^ (j + 1) := by rw [← pow_succ, ← pow_mul]; congr 1
    rw [this]
    exact Subgroup.pow_mem P hγ2 _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hγP
  refine ⟨i, ?_⟩
  have hmem : (c ^ i)⁻¹ * g ∈ normalizer (W : Set G) :=
    Subgroup.mul_mem _ (inv_mem (zpow_mem hcW i)) hgW
  have key : conjAct W ⟨(c ^ i)⁻¹ * g, hmem⟩ = 1 := by
    have : (⟨(c ^ i)⁻¹ * g, hmem⟩ : normalizer (W : Set G)) =
        (⟨c, hcW⟩ ^ i)⁻¹ * ⟨g, hgW⟩ := by
      apply Subtype.ext
      simp
    rw [this, map_mul, map_inv, map_zpow, ← ha, ← hγ, ← hi, inv_mul_cancel]
  exact (conjAct_eq_one_iff W _).1 key

theorem normalizer_le_normalizer_W : normalizer (X : Set G) ≤ normalizer (W : Set G) := by
  have key : ∀ g ∈ normalizer (X : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    have hwX : w ∈ X := h.le hw
    have h1 : g * w * g⁻¹ ∈ X := (mem_normalizer_iff.1 hg w).1 hwX
    apply h.mem_W_of_sq_eq_one h1
    have : (g * w * g⁻¹) ^ 2 = g * (w * w) * g⁻¹ := by rw [pow_two]; group
    rw [this, ← pow_two, h.sq_eq_one w hw]; group
  intro g hg
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key g hg w, fun hw => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hw
  rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this

theorem index_zpowers_conjAct :
    (Subgroup.zpowers (conjAct W ⟨c, h.mem_normalizer⟩)).index = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcW := h.mem_normalizer
  set a : MulAut W := conjAct W ⟨c, hcW⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow, conjAct_eq_one_iff]
    show c ^ 3 ∈ centralizer (W : Set G)
    rw [h.c_pow_three]; exact one_mem _
  have ha1 : a ≠ 1 := by
    intro h1
    rw [ha, conjAct_eq_one_iff] at h1
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_mem_W
    apply h.fpf u hu hu1
    have := mem_centralizer_iff.1 h1 u hu
    calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [this]
      _ = u := by group
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hPcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have := Subgroup.card_mul_index (Subgroup.zpowers a)
  rw [hPcard, h.card_mulAut] at this
  omega

theorem exists_zpow_or_zpow_mul {g a₀ : G} (hgW : g ∈ normalizer (W : Set G))
    (ha₀ : a₀ ∈ normalizer (W : Set G))
    (hna₀ : ∀ i : ℤ, (c ^ i)⁻¹ * a₀ ∉ centralizer (W : Set G)) :
    ∃ i : ℤ, (c ^ i)⁻¹ * g ∈ centralizer (W : Set G) ∨
      (c ^ i * a₀)⁻¹ * g ∈ centralizer (W : Set G) := by
  have hcW := h.mem_normalizer
  set a : MulAut W := conjAct W ⟨c, hcW⟩ with ha
  set γ : MulAut W := conjAct W ⟨g, hgW⟩ with hγ
  set δ : MulAut W := conjAct W ⟨a₀, ha₀⟩ with hδ
  set P : Subgroup (MulAut W) := Subgroup.zpowers a with hP
  have hidx : P.index = 2 := h.index_zpowers_conjAct
  have hcpow : ∀ i : ℤ, c ^ i ∈ normalizer (W : Set G) := fun i => zpow_mem hcW i
  have hact : ∀ i : ℤ, conjAct W ⟨c ^ i, hcpow i⟩ = a ^ i := fun i => by
    have : (⟨c ^ i, hcpow i⟩ : normalizer (W : Set G)) = ⟨c, hcW⟩ ^ i := Subtype.ext (by simp)
    rw [this, map_zpow]
  have hδP : δ ∉ P := by
    intro hδ'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hδ'
    apply hna₀ i
    have hmem : (c ^ i)⁻¹ * a₀ ∈ normalizer (W : Set G) :=
      Subgroup.mul_mem _ (inv_mem (hcpow i)) ha₀
    rw [← conjAct_eq_one_iff W ⟨_, hmem⟩]
    have : (⟨(c ^ i)⁻¹ * a₀, hmem⟩ : normalizer (W : Set G)) =
        (⟨c ^ i, hcpow i⟩ : normalizer (W : Set G))⁻¹ * ⟨a₀, ha₀⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, hact, hi, ← hδ, inv_mul_cancel]
  by_cases hγP : γ ∈ P
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hγP
    refine ⟨i, Or.inl ?_⟩
    have hmem : (c ^ i)⁻¹ * g ∈ normalizer (W : Set G) :=
      Subgroup.mul_mem _ (inv_mem (hcpow i)) hgW
    rw [← conjAct_eq_one_iff W ⟨_, hmem⟩]
    have : (⟨(c ^ i)⁻¹ * g, hmem⟩ : normalizer (W : Set G)) =
        (⟨c ^ i, hcpow i⟩ : normalizer (W : Set G))⁻¹ * ⟨g, hgW⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, hact, hi, ← hγ, inv_mul_cancel]
  · obtain ⟨b, hb⟩ := Subgroup.index_eq_two_iff.1 hidx
    have h1 : γ * b ∈ P := by
      rcases hb γ with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact h2
      · exact absurd h2 hγP
    have h2 : δ * b ∈ P := by
      rcases hb δ with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact h2
      · exact absurd h2 hδP
    have h3 : γ * δ⁻¹ ∈ P := by
      have := P.mul_mem h1 (P.inv_mem h2)
      rwa [show γ * b * (δ * b)⁻¹ = γ * δ⁻¹ by group] at this
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h3
    refine ⟨i, Or.inr ?_⟩
    have hmem : (c ^ i * a₀)⁻¹ * g ∈ normalizer (W : Set G) :=
      Subgroup.mul_mem _ (inv_mem (Subgroup.mul_mem _ (hcpow i) ha₀)) hgW
    rw [← conjAct_eq_one_iff W ⟨_, hmem⟩]
    have : (⟨(c ^ i * a₀)⁻¹ * g, hmem⟩ : normalizer (W : Set G)) =
        ((⟨c ^ i, hcpow i⟩ : normalizer (W : Set G)) * ⟨a₀, ha₀⟩)⁻¹ * ⟨g, hgW⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_inv, map_mul, hact, hi, ← hδ, ← hγ]
    have : γ = a ^ i * δ := by rw [hi]; group
    rw [this]; group


theorem exists_mem_mul_centralizer_of_odd {g : G} (hg : g ∈ normalizer (X : Set G)) {m : ℕ}
    (hm : Odd m) (hgm : g ^ m ∈ centralizer (W : Set G)) :
    ∃ x ∈ X, x⁻¹ * g ∈ centralizer (X : Set G) := by
  have hgW := h.normalizer_le_normalizer_W hg
  obtain ⟨i, hi⟩ := h.exists_zpow_inv_mul_mem_centralizer_of_odd hgW hm hgm
  have hnX : (c ^ i)⁻¹ * g ∈ normalizer (X : Set G) :=
    Subgroup.mul_mem _ (inv_mem (Subgroup.le_normalizer (zpow_mem h.mem_X i))) hg
  obtain ⟨w, hw, hwc⟩ := h.exists_mul_mem_centralizer hnX hi
  refine ⟨c ^ i * w, X.mul_mem (zpow_mem h.mem_X i) (h.le hw), ?_⟩
  have : (c ^ i * w)⁻¹ * g = w⁻¹ * ((c ^ i)⁻¹ * g) := by group
  rw [this]; exact hwc

theorem mem_W_of_sq_mem {x : G} (hx : x ∈ X) (h2 : x ^ 2 ∈ W) : x ∈ W := by
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp hx
  have hk : c ^ k ∈ normalizer (W : Set G) := zpow_mem h.mem_normalizer k
  have hconj : c ^ k * w * (c ^ k)⁻¹ ∈ W := (mem_normalizer_iff.1 hk w).1 hw
  have h1 : c ^ (2 * k) = (w * (c ^ k * w * (c ^ k)⁻¹))⁻¹ * (w * c ^ k) ^ 2 := by
    rw [pow_two]; group
  have h3 : c ^ (2 * k) = 1 := by
    apply h.zpow_c_eq_one_of_mem
    rw [h1]
    exact W.mul_mem (W.inv_mem (W.mul_mem hw hconj)) h2
  have h4 : c ^ k = 1 := by
    have h5 : c ^ (3 * k) = 1 := by
      rw [zpow_mul]
      have : c ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact h.c_pow_three
      rw [this, one_zpow]
    calc c ^ k = c ^ (3 * k) * (c ^ (2 * k))⁻¹ := by rw [← zpow_neg, ← zpow_add]; congr 1; ring
      _ = 1 := by rw [h5, h3]; simp
  rw [h4, mul_one]; exact hw

theorem mem_W_of_two_pow {x : G} (hx : x ∈ X) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x ∈ W := by
  induction n generalizing x with
  | zero => simp at hxn; rw [hxn]; exact W.one_mem
  | succ n ih =>
    apply h.mem_W_of_sq_mem hx
    apply ih (X.pow_mem hx 2)
    rw [← pow_mul, ← pow_succ']; exact hxn

theorem W_eq {W' : Subgroup G} {c' : G} (h' : A4Data X W' c') : W = W' := by
  apply le_antisymm
  · intro w hw
    exact h'.mem_W_of_sq_eq_one (h.le hw) (h.sq_eq_one w hw)
  · intro w hw
    exact h.mem_W_of_sq_eq_one (h'.le hw) (h'.sq_eq_one w hw)

end A4Data

section Subnormal

theorem le_pCoreOf_of_isSubnormal {M X U : Subgroup G} [Finite G] (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) (hU : IsPGroup 2 U) (hUX : U ≤ X)
    (hn : X ≤ normalizer (U : Set G)) : U ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ A : Subgroup M, A.IsSubnormal → ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ A.map M.subtype → A.map M.subtype ≤ normalizer (U : Set G) → U ≤ pCoreOf 2 M := by
    intro A hA
    induction hA with
    | top =>
      intro U hU hUA hn
      rw [Subgroup.map_top, Subgroup.range_subtype] at hUA hn
      exact le_pCoreOf_of_le_normalizer 2 hUA hn hU
    | step A K hAK hK hN ih =>
      intro U hU hUA hn
      have h1 : U ≤ pCoreOf 2 (A.map M.subtype) := le_pCoreOf_of_le_normalizer 2 hUA hn hU
      refine h1.trans (ih _ (pCoreOf_isPGroup 2 _)
        ((pCoreOf_le 2 _).trans (Subgroup.map_mono hAK)) ?_)
      have hKA : K ≤ normalizer (A : Set M) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).1 hN
      have h2 : K.map M.subtype ≤ normalizer ((A.map M.subtype : Subgroup G) : Set G) :=
        (Subgroup.map_mono hKA).trans (Subgroup.le_normalizer_map _)
      exact h2.trans (normalizer_le_normalizer_pCoreOf 2 _)
  rw [← Subgroup.map_subgroupOf_eq_of_le hXM] at hUX hn
  exact key _ hXs U hU hUX hn

theorem isSubnormal_cj {M X : Subgroup G} (hXs : (X.subgroupOf M).IsSubnormal)
    {m : G} (hm : m ∈ M) : ((cj m X).subgroupOf M).IsSubnormal := by
  have h1 := hXs.map (f := (MulAut.conj (⟨m, hm⟩ : M)).toMonoidHom)
    (MulAut.conj (⟨m, hm⟩ : M)).surjective
  convert h1 using 1
  ext y
  rw [Subgroup.mem_subgroupOf, mem_cj, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  simp [MulAut.conj_symm_apply]

end Subnormal

theorem exists_mul_of_odd_mem [Finite G] {M N T : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hTM : T ≤ M)
    (hTidx : ¬ 2 ∣ (T.subgroupOf M).index)
    (hodd : ∀ g ∈ M, Odd (orderOf g) → g ∈ N) :
    ∀ m ∈ M, ∃ n ∈ N, ∃ t ∈ T, m = n * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hMN
  have hQ : IsPGroup 2 (↥M ⧸ N.subgroupOf M) := by
    intro q
    induction q using QuotientGroup.induction_on with | _ g => ?_
    have hord : orderOf g ≠ 0 := (orderOf_pos g).ne'
    obtain ⟨k, m', hm', hkm⟩ := Nat.exists_eq_two_pow_mul_odd hord
    refine ⟨k, ?_⟩
    have hgk : orderOf (g ^ 2 ^ k) = m' := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m', hkm⟩, hkm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hmem : ((g ^ 2 ^ k : M) : G) ∈ N := by
      apply hodd _ (g ^ 2 ^ k).2
      rw [Subgroup.orderOf_coe, hgk]; exact hm'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  obtain ⟨e, he⟩ := hQ.exists_card_eq
  have hNidx : N.relIndex M = 2 ^ e := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, he]
  set P : Subgroup G := N ⊔ T with hP
  have hd1 : P.relIndex M ∣ 2 ^ e :=
    hNidx ▸ Subgroup.relIndex_dvd_of_le_left M (le_sup_left : N ≤ P)
  have hd2 : P.relIndex M ∣ (T.subgroupOf M).index := by
    have := Subgroup.relIndex_dvd_of_le_left M (le_sup_right : T ≤ P)
    simpa [Subgroup.relIndex] using this
  have hd1' : P.relIndex M = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hTidx
      refine dvd_trans ?_ hd2
      rw [hj]; exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  have hMP : M ≤ P := Subgroup.relIndex_eq_one.1 hd1'
  intro m hm
  have hm' : m ∈ ((N ⊔ T : Subgroup G) : Set G) := hMP hm
  rw [coe_mul_of_right_le_normalizer_left N T (hTM.trans hMN)] at hm'
  obtain ⟨n, hn, t, ht, rfl⟩ := hm'
  exact ⟨n, hn, t, ht, rfl⟩

theorem center_sup_eq_one {X Y : Subgroup G} (hXc : ∀ g ∈ X, (∀ l ∈ X, g * l = l * g) → g = 1)
    (hYc : ∀ g ∈ Y, (∀ l ∈ Y, g * l = l * g) → g = 1)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ z ∈ X ⊔ Y, (∀ l ∈ X ⊔ Y, z * l = l * z) → z = 1 := by
  have hle : X ≤ normalizer (Y : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hXY x hx y hy]; group
      rwa [this]
    · intro hu
      have h2 : x * (x * y * x⁻¹) = x * y := by
        calc x * (x * y * x⁻¹) = (x * y * x⁻¹) * x := hXY x hx _ hu
          _ = x * y := by group
      have h3 : x * y * x⁻¹ = y := mul_left_cancel h2
      rwa [h3] at hu
  intro z hz hcen
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X Y hle] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have hx1 : x = 1 := by
    apply hXc x hx
    intro x' hx'
    have h1 := hcen x' (Subgroup.mem_sup_left hx')
    have h3 : (x * x') * y = (x' * x) * y := by
      calc (x * x') * y = x * (x' * y) := by group
        _ = x * (y * x') := by rw [hXY x' hx' y hy]
        _ = (x * y) * x' := by group
        _ = x' * (x * y) := h1
        _ = (x' * x) * y := by group
    exact mul_right_cancel h3
  have hy1 : y = 1 := by
    apply hYc y hy
    intro y' hy'
    have h1 := hcen y' (Subgroup.mem_sup_right hy')
    have h3 : x * (y * y') = x * (y' * y) := by
      calc x * (y * y') = (x * y) * y' := by group
        _ = y' * (x * y) := h1
        _ = (y' * x) * y := by group
        _ = (x * y') * y := by rw [hXY x hx y' hy']
        _ = x * (y' * y) := by group
    exact mul_left_cancel h3
  subst hx1 hy1
  exact one_mul 1

theorem false_of_three_commuting [Finite G] {M X₁ X₂ X₃ W₁ W₂ W₃ : Subgroup G} {c₁ c₂ c₃ : G}
    (hrank : CFSG.Open.pRank 3 M ≤ 2) (h₁ : A4Data X₁ W₁ c₁) (h₂ : A4Data X₂ W₂ c₂)
    (h₃ : A4Data X₃ W₃ c₃) (h₁M : X₁ ≤ M) (h₂M : X₂ ≤ M) (h₃M : X₃ ≤ M)
    (h₁₂ : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) (h₁₃ : ∀ x ∈ X₁, ∀ y ∈ X₃, x * y = y * x)
    (h₂₃ : ∀ x ∈ X₂, ∀ y ∈ X₃, x * y = y * x) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hE₁ : IsElemAbelian 3 (zpowers c₁) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := a.2
      obtain ⟨j, hj⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact ((Commute.refl c₁).zpow_zpow i j).eq
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have : c₁ ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact h₁.c_pow_three
      rw [this, one_zpow]
  have hc₁ : Nat.card (zpowers c₁) = 3 := by rw [Nat.card_zpowers, h₁.order_c]
  have hc₁₂ : Commute c₁ c₂ := h₁₂ c₁ h₁.mem_X c₂ h₂.mem_X
  have hn₂ : c₂ ∉ zpowers c₁ := by
    intro hmem
    have hX₁ : c₂ ∈ X₁ := (zpowers_le.2 h₁.mem_X) hmem
    have h1 : c₂ = 1 := h₁.center c₂ hX₁ (fun l hl => (h₁₂ l hl c₂ h₂.mem_X).symm)
    have := h₂.order_c
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨hE₂, hc₂card⟩ := exists_elemAbelian_sup_zpowers (p := 3) hE₁ h₂.order_c
    (fun e he => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 he
      exact hc₁₂.zpow_left i) hn₂
  have hE₂le : zpowers c₁ ⊔ zpowers c₂ ≤ X₁ ⊔ X₂ :=
    sup_le_sup (zpowers_le.2 h₁.mem_X) (zpowers_le.2 h₂.mem_X)
  have hle : X₁ ⊔ X₂ ≤ centralizer ({c₃} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2 (h₁₃ x hx c₃ h₃.mem_X))
      (fun x hx => mem_centralizer_singleton_iff.2 (h₂₃ x hx c₃ h₃.mem_X))
  have hn₃ : c₃ ∉ zpowers c₁ ⊔ zpowers c₂ := by
    intro hmem
    have hmem' : c₃ ∈ X₁ ⊔ X₂ := hE₂le hmem
    have h1 : c₃ = 1 := center_sup_eq_one h₁.center h₂.center h₁₂ c₃ hmem'
      (fun l hl => (mem_centralizer_singleton_iff.1 (hle hl)).symm)
    have := h₃.order_c
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨hE₃, hc₃card⟩ := exists_elemAbelian_sup_zpowers (p := 3) hE₂ h₃.order_c
    (fun e he => (mem_centralizer_singleton_iff.1 (hle (hE₂le he)))) hn₃
  have hE₃M : zpowers c₁ ⊔ zpowers c₂ ⊔ zpowers c₃ ≤ M :=
    sup_le (sup_le (zpowers_le.2 (h₁M h₁.mem_X)) (zpowers_le.2 (h₂M h₂.mem_X)))
      (zpowers_le.2 (h₃M h₃.mem_X))
  have hcard27 : Nat.card ↥(zpowers c₁ ⊔ zpowers c₂ ⊔ zpowers c₃) = 3 ^ 3 := by
    rw [hc₃card, hc₂card, hc₁]; norm_num
  have := le_pRank (by norm_num : Nat.Prime 3) hE₃M hE₃ hcard27
  omega


end CFSG.Quasithin.S14110
