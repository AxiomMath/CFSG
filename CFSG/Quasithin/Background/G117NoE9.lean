module

public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Quasithin

namespace G11

namespace G117

theorem eq_one_or_eq_of_mem_zpowers {Q : Type*} [Group Q] {t : Q} (ht2 : t * t = 1) {z : Q}
    (hz : z ∈ Subgroup.zpowers t) : z = 1 ∨ z = t := by
  have ht1 : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one]
    exact ht2
  rw [Subgroup.zpowers_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    right
    exact hx
  | one => left; rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · left; simp
    · right; simp
    · right; simp
    · left; exact ht2
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · left; simp
    · right; exact ht1

section Config

variable {Q : Type*} [Group Q] (t c : Q) (E : Subgroup Q)

@[expose] def e27 : Subgroup Q := Subgroup.closure ((E : Set Q) ∪ {c})

variable {t c E}

theorem e27_comm (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEc : ∀ e ∈ E, e * c = c * e) :
    ∀ x ∈ e27 c E, ∀ y ∈ e27 c E, x * y = y * x := by
  have hgenN : ((E : Set Q) ∪ {c}) ⊆ Subgroup.centralizer ((E : Set Q) ∪ {c}) := by
    intro x hx y hy
    rw [Set.mem_union, SetLike.mem_coe, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · exact (hEcomm y hy x hx)
    · exact (hEc x hx).symm
    · exact (hEc y hy)
    · rfl
  have hNle : e27 c E ≤ Subgroup.centralizer ((E : Set Q) ∪ {c}) :=
    (Subgroup.closure_le _).2 hgenN
  intro x hx y hy
  have h1 : y ∈ Subgroup.centralizer ((E : Set Q) ∪ {c}) := hNle hy
  have h2 : x ∈ Subgroup.centralizer (Subgroup.centralizer ((E : Set Q) ∪ {c}) : Set Q) :=
    Subgroup.closure_le_centralizer_centralizer _ hx
  exact (Subgroup.mem_centralizer_iff.1 h2 y h1).symm

theorem e27_pow_three (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hEc : ∀ e ∈ E, e * c = c * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hc3 : c ^ 3 = 1) :
    ∀ x ∈ e27 c E, x ^ 3 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hE3 x hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hc3
  | one => simp
  | mul x y hxN hyN hx hy =>
    have hcom : Commute x y := e27_comm hEcomm hEc x hxN y hyN
    rw [hcom.mul_pow, hx, hy, one_mul]
  | inv x _ hx => rw [inv_pow, hx, inv_one]

theorem mem_e27_of_mem_E {e : Q} (he : e ∈ E) : e ∈ e27 c E :=
  Subgroup.subset_closure (Or.inl he)

theorem c_mem_e27 : c ∈ e27 c E := Subgroup.subset_closure (Or.inr rfl)

theorem e27_conj_E (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEc : ∀ e ∈ E, e * c = c * e)
    {x : Q} (hx : x ∈ E) : ∀ m ∈ e27 c E, x * m * x⁻¹ = m := by
  have hgen : ∀ y ∈ ((E : Set Q) ∪ {c}), x * y = y * x := by
    intro y hy
    rw [Set.mem_union, SetLike.mem_coe, Set.mem_singleton_iff] at hy
    rcases hy with hy | rfl
    · exact hEcomm x hx y hy
    · exact hEc x hx
  intro m hm
  have hle : e27 c E ≤ Subgroup.centralizer ({x} : Set Q) := by
    rw [e27, Subgroup.closure_le]
    intro y hy z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hgen y hy
  have := Subgroup.mem_centralizer_iff.1 (hle hm) x rfl
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem e27_conj_t (htc : t * c * t⁻¹ = c⁻¹) (hEt : ∀ e ∈ E, e * t = t * e) :
    ∀ n ∈ e27 c E, t * n * t⁻¹ ∈ e27 c E := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · have : t * x * t⁻¹ = x := by
        rw [mul_inv_eq_iff_eq_mul, hEt x hx]
      rw [this]
      exact mem_e27_of_mem_E hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, htc]
      exact (e27 c E).inv_mem c_mem_e27
  | one => simp
  | mul x y _ _ hx hy =>
    have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [this]
    exact (e27 c E).mul_mem hx hy
  | inv x _ hx =>
    have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [this]
    exact (e27 c E).inv_mem hx

theorem e27_normal (hgen : Subgroup.closure ((E : Set Q) ∪ {t, c}) = ⊤) (ht2 : t * t = 1)
    (htc : t * c * t⁻¹ = c⁻¹) (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hEt : ∀ e ∈ E, e * t = t * e) (hEc : ∀ e ∈ E, e * c = c * e) : (e27 c E).Normal := by
  have hNconj : ∀ g : Q, ∀ n : Q, g * n * g⁻¹ ∈ e27 c E ↔ n ∈ e27 c E := by
    intro g
    have hg : g ∈ Subgroup.closure ((E : Set Q) ∪ {t, c}) := by
      rw [hgen]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · intro n
        constructor
        · intro h
          have hxinv : x⁻¹ ∈ E := E.inv_mem hx
          have h1 := e27_conj_E hEcomm hEc hxinv _ h
          have h2 : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
          rw [h2] at h1
          rw [h1]
          exact h
        · intro hn
          rw [e27_conj_E hEcomm hEc hx n hn]
          exact hn
      · intro n
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · constructor
          · intro h
            have h1 := e27_conj_t htc hEt _ h
            have e : x * (x * n * x⁻¹) * x⁻¹ = n := by
              have : x * (x * n * x⁻¹) * x⁻¹ = (x * x) * n * (x * x)⁻¹ := by group
              rw [this, ht2]
              simp
            rw [e] at h1
            exact h1
          · exact e27_conj_t htc hEt n
        · constructor
          · intro h
            have h1 := (e27 x E).mul_mem ((e27 x E).mul_mem ((e27 x E).inv_mem c_mem_e27) h)
              c_mem_e27
            have e : x⁻¹ * (x * n * x⁻¹) * x = n := by group
            rw [e] at h1
            exact h1
          · intro hn
            exact (e27 x E).mul_mem ((e27 x E).mul_mem c_mem_e27 hn) ((e27 x E).inv_mem c_mem_e27)
    | one => intro n; simp
    | mul x y _ _ hx hy =>
      intro n
      have : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [this, hx, hy]
    | inv x _ hx =>
      intro n
      rw [← hx (x⁻¹ * n * x⁻¹⁻¹)]
      have : x * (x⁻¹ * n * x⁻¹⁻¹) * x⁻¹ = n := by group
      rw [this]
  exact ⟨fun n hn g => (hNconj g n).2 hn⟩

theorem e27_sup_zpowers (hgen : Subgroup.closure ((E : Set Q) ∪ {t, c}) = ⊤) :
    e27 c E ⊔ Subgroup.zpowers t = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact Subgroup.mem_sup_left (mem_e27_of_mem_E hx)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · exact Subgroup.mem_sup_left c_mem_e27

theorem centralizer_e27_le (hgen : Subgroup.closure ((E : Set Q) ∪ {t, c}) = ⊤) (ht2 : t * t = 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (htc : t * c * t⁻¹ = c⁻¹)
    (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEt : ∀ e ∈ E, e * t = t * e)
    (hEc : ∀ e ∈ E, e * c = c * e) {x : Q} (hx : ∀ y ∈ e27 c E, y * x = x * y) : x ∈ e27 c E := by
  have hNnormal := e27_normal hgen ht2 htc hEcomm hEt hEc
  have hxQ : x ∈ e27 c E ⊔ Subgroup.zpowers t := by
    rw [e27_sup_zpowers hgen]
    exact Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hxQ
  rcases eq_one_or_eq_of_mem_zpowers ht2 hz with rfl | rfl
  · rw [mul_one]
    exact hy
  · exfalso
    have h1 : c * (y * z) = (y * z) * c := hx c c_mem_e27
    have e1 : (y * z) * c * (y * z)⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    have e2 : (y * z) * c * (y * z)⁻¹ = y * (z * c * z⁻¹) * y⁻¹ := by group
    rw [e2, htc] at e1
    have e3 : y * c⁻¹ * y⁻¹ = c⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact e27_comm hEcomm hEc y hy c⁻¹ ((e27 c E).inv_mem c_mem_e27)
    rw [e3] at e1
    have hcc : c * c = 1 := by
      have : c⁻¹ * c = c * c := by rw [e1]
      rw [← this]
      simp
    apply hc1
    calc c = c * (c * c) := by rw [hcc, mul_one]
      _ = c ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := hc3

end Config

theorem no_E9_S3_core {Q : Type*} [Group Q] [Finite Q] (hq : IsQuotientOfSQTKTauCeti Q) (t c : Q)
    (E : Subgroup Q) (hgen : Subgroup.closure ((E : Set Q) ∪ {t, c}) = ⊤) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (htc : t * c * t⁻¹ = c⁻¹)
    (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEnc : ¬ IsCyclic ↥E) (hEt : ∀ e ∈ E, e * t = t * e) (hEc : ∀ e ∈ E, e * c = c * e) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, _, _, hst, -, φ, hφ⟩ := hq
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 := by
    have h := hst 3 Nat.prime_three (by norm_num)
    rw [G11.assemblyPRank_top_eq] at h
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  have hNnormal := e27_normal hgen ht2 htc hEcomm hEt hEc
  have hNp : IsPGroup 3 ↥(e27 c E) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (e27_pow_three hEcomm hEc hE3 hc3 g g.2)⟩
  have hNpc : e27 c E ≤ CFSG.Open.pCore 3 Q := CFSG.LieType.BorelTits.le_pCore 3 hNnormal hNp
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 Q : Set Q) ≤ CFSG.Open.pCore 3 Q := by
    intro x hx
    apply hNpc
    exact centralizer_e27_le hgen ht2 hc3 hc1 htc hEcomm hEt hEc fun y hy =>
      Subgroup.mem_centralizer_iff.1 hx y (hNpc hy)
  have hA := A1c.A131Concl_of_surjective (p := 3) (by norm_num) hF _ S φ hφ rfl hrk
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers t) := fun g => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    show (g : Q) ^ 2 = 1
    rcases eq_one_or_eq_of_mem_zpowers ht2 g.2 with h | h
    · rw [h]
      simp
    · rw [h, pow_two]
      exact ht2⟩
  have hcyc := hA.1 (Subgroup.zpowers t) hT2 (mt Subgroup.zpowers_eq_bot.1 ht1)
  have hEle : E ≤ CFSG.Open.pCore 3 Q ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set Q) := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hNpc (mem_e27_of_mem_E he), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro z hz
    rcases eq_one_or_eq_of_mem_zpowers ht2 hz with rfl | rfl
    · simp
    · exact (hEt e he).symm
  apply hEnc
  have := hcyc
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hEle).surjective

theorem no_S3_noncyclic {A : Type*} [Group A] [Finite A] {Γ : Subgroup A}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) {t c : A} (htΓ : t ∈ Γ) (hcΓ : c ∈ Γ) {E : Subgroup A}
    (hEΓ : E ≤ Γ) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (htc : t * c * t⁻¹ = c⁻¹) (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEnc : ¬ IsCyclic ↥E) (hEt : ∀ e ∈ E, e * t = t * e)
    (hEc : ∀ e ∈ E, e * c = c * e) : False := by
  set M : Subgroup A := Subgroup.closure ((E : Set A) ∪ {t, c}) with hM
  have hMΓ : M ≤ Γ := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with hx | hx
    · exact hEΓ hx
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact htΓ
      · exact hcΓ)
  have hqM : IsQuotientOfSQTKTauCeti ↥M := hq.of_le hMΓ
  have htM : t ∈ M := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hcM : c ∈ M := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hEM : E ≤ M := fun e he => Subgroup.subset_closure (Or.inl he)
  have hgen : Subgroup.closure (((E.subgroupOf M : Subgroup M) : Set M) ∪
      {(⟨t, htM⟩ : M), (⟨c, hcM⟩ : M)}) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := (E : Set A) ∪ {t, c})
    rw [← hM] at h
    convert h using 2
    ext x
    simp only [Set.mem_union, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
  refine no_E9_S3_core hqM ⟨t, htM⟩ ⟨c, hcM⟩ (E.subgroupOf M) hgen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext ht2
  · intro h
    exact ht1 (congrArg Subtype.val h)
  · exact Subtype.ext hc3
  · intro h
    exact hc1 (congrArg Subtype.val h)
  · exact Subtype.ext htc
  · intro e he e' he'
    exact Subtype.ext (hEcomm e he e' he')
  · intro e he
    exact Subtype.ext (hE3 e he)
  · intro hcyc
    exact hEnc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEM).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEM).surjective)
  · intro e he
    exact Subtype.ext (hEt e he)
  · intro e he
    exact Subtype.ext (hEc e he)

theorem not_isCyclic_of_card_nine {E : Type*} [Group E] (h9 : Nat.card E = 9)
    (h3 : ∀ e : E, e ^ 3 = 1) : ¬ IsCyclic E := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 g)
  rw [hg, h9] at h1
  omega

theorem no_E9_S3 {A : Type*} [Group A] [Finite A] {Γ : Subgroup A}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) {t c : A} (htΓ : t ∈ Γ) (hcΓ : c ∈ Γ) {E : Subgroup A}
    (hEΓ : E ≤ Γ) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (htc : t * c * t⁻¹ = c⁻¹) (hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9) (hEt : ∀ e ∈ E, e * t = t * e)
    (hEc : ∀ e ∈ E, e * c = c * e) : False :=
  no_S3_noncyclic hq htΓ hcΓ hEΓ ht2 ht1 hc3 hc1 htc hEcomm hE3
    (not_isCyclic_of_card_nine hE9 fun e => Subtype.ext (hE3 e e.2)) hEt hEc


theorem eq_one_of_commute_of_two_S3 {A : Type*} [Group A] [Finite A] {Γ H : Subgroup A}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hHΓ : H ≤ Γ) {t₁ c₁ t₂ c₂ : A}
    (ht₁ : t₁ ∈ H) (hc₁ : c₁ ∈ H) (ht₂ : t₂ ∈ H) (hc₂ : c₂ ∈ H)
    (ht₁2 : t₁ * t₁ = 1) (ht₁1 : t₁ ≠ 1) (hc₁3 : c₁ ^ 3 = 1) (hc₁1 : c₁ ≠ 1)
    (h₁ : t₁ * c₁ * t₁⁻¹ = c₁⁻¹) (hc₂3 : c₂ ^ 3 = 1) (hc₂1 : c₂ ≠ 1)
    (h₂ : t₂ * c₂ * t₂⁻¹ = c₂⁻¹) (hc₁c₂ : c₁ * c₂ = c₂ * c₁) (ht₁c₂ : t₁ * c₂ = c₂ * t₁)
    {c₀ : A} (hc₀Γ : c₀ ∈ Γ) (hc₀ : ∀ h ∈ H, h * c₀ = c₀ * h) (hc₀3 : c₀ ^ 3 = 1) :
    c₀ = 1 := by
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E₀ : Subgroup A := Subgroup.zpowers c₂ with hE₀
  have hc₂E₀ : c₂ ∈ E₀ := Subgroup.mem_zpowers c₂
  have hE₀H : E₀ ≤ H := (Subgroup.zpowers_le).2 hc₂
  have hE₀comm : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact (Commute.zpow_zpow_self c₂ a b).eq
  have hE₀c : ∀ e ∈ E₀, e * c₀ = c₀ * e := fun e he => hc₀ e (hE₀H he)
  have hE₀3 : ∀ e ∈ E₀, e ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₂3, one_zpow]
  have hEcomm := e27_comm hE₀comm hE₀c
  have hE3 := e27_pow_three hE₀comm hE₀c hE₀3 hc₀3
  have hEΓ : e27 c₀ E₀ ≤ Γ := by
    rw [e27, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hHΓ (hE₀H hx)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hc₀Γ
  have hcent : ∀ z : A, (∀ e ∈ E₀, e * z = z * e) → z * c₀ = c₀ * z → ∀ x ∈ e27 c₀ E₀,
      x * z = z * x := by
    intro z hz hz0 x hx
    have hle : e27 c₀ E₀ ≤ Subgroup.centralizer ({z} : Set A) := by
      rw [e27, Subgroup.closure_le]
      rintro y (hy | hy) w hw
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hz y hy).symm
      · rw [Set.mem_singleton_iff] at hy hw
        rw [hy, hw]
        exact hz0
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) z rfl).symm
  have hEt : ∀ e ∈ e27 c₀ E₀, e * t₁ = t₁ * e := by
    refine hcent t₁ (fun e he => ?_) (hc₀ t₁ ht₁)
    obtain ⟨a, rfl⟩ := he
    exact ((Commute.zpow_left (show Commute c₂ t₁ from ht₁c₂.symm) a)).eq
  have hEc : ∀ e ∈ e27 c₀ E₀, e * c₁ = c₁ * e := by
    refine hcent c₁ (fun e he => ?_) (hc₀ c₁ hc₁)
    obtain ⟨a, rfl⟩ := he
    exact ((Commute.zpow_left (show Commute c₂ c₁ from hc₁c₂.symm) a)).eq
  have hEnc : ¬ IsCyclic ↥(e27 c₀ E₀) := by
    intro hcyc
    have hord0 : orderOf c₀ = 3 := orderOf_eq_prime hc₀3 hne
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(e27 c₀ E₀))
    have hg3 : g ^ 3 = 1 := Subtype.ext (hE3 g g.2)
    have h1 : Nat.card ↥(e27 c₀ E₀) ∣ 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one hg3
    have hle : Subgroup.zpowers c₀ ≤ e27 c₀ E₀ := (Subgroup.zpowers_le).2 c_mem_e27
    have h2 : Nat.card ↥(Subgroup.zpowers c₀) ≤ Nat.card ↥(e27 c₀ E₀) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord0] at h2
    have h3 : Nat.card ↥(e27 c₀ E₀) ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    have heq : Subgroup.zpowers c₀ = e27 c₀ E₀ := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, hord0]
      exact h3
    have hc₂mem : c₂ ∈ Subgroup.zpowers c₀ := by
      rw [heq]
      exact mem_e27_of_mem_E hc₂E₀
    obtain ⟨k, hk⟩ := hc₂mem
    have hcomm₂ : t₂ * c₂ = c₂ * t₂ := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute t₂ c₀ from hc₀ t₂ ht₂) k)).eq
    have : c₂ = c₂⁻¹ := by
      rw [← h₂, eq_mul_inv_iff_mul_eq]
      exact hcomm₂.symm
    have hcc : c₂ * c₂ = 1 := by
      calc c₂ * c₂ = c₂⁻¹ * c₂ := by rw [← this]
        _ = 1 := inv_mul_cancel c₂
    apply hc₂1
    calc c₂ = c₂ * (c₂ * c₂) := by rw [hcc, mul_one]
      _ = c₂ ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := hc₂3
  exact no_S3_noncyclic hq (hHΓ ht₁) (hHΓ hc₁) hEΓ ht₁2 ht₁1 hc₁3 hc₁1 h₁ hEcomm hE3 hEnc hEt hEc

end G117

end G11

end CFSG.Quasithin
