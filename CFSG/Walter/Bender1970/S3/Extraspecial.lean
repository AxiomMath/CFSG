module

public import CFSG.Walter.Bender1970.S3.Involution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Walter.Bender1970.S2.Basic

public section

namespace CFSG.Walter

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

section Extraspecial

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X)
  (hexp : ∀ x ∈ X, x ^ p = 1)
  (hZp : Nat.card (X ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = p)
  (hX3 : Nat.card X ≤ p ^ 3) (hcomm : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G))

omit [Finite G] in
theorem commute_of_mem_center {z x : G} (hz : z ∈ X ⊓ Subgroup.centralizer (X : Set G))
    (hx : x ∈ X) : Commute z x :=
  ((Subgroup.mem_centralizer_iff.mp hz.2) x hx).symm

omit [Finite G] in
include hp hp2 hexp in
theorem mem_of_sq_mem {Z : Subgroup G} {x : G} (hx : x ∈ X) (hx2 : x ^ 2 ∈ Z) : x ∈ Z := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have : (x ^ 2) ^ (k + 1) = x := by
    rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hexp x hx, one_mul]
  rw [← this]
  exact Z.pow_mem hx2 _

omit [Finite G] in
include hp hp2 hexp in
theorem eq_one_of_sq_eq_one {x : G} (hx : x ∈ X) (hx2 : x * x = 1) : x = 1 := by
  have h := mem_of_sq_mem hp hp2 hexp (Z := ⊥) hx (by rw [pow_two, hx2]; exact one_mem _)
  exact Subgroup.mem_bot.mp h

omit [Finite G] in
include hp hp2 hexp in
theorem centralizes_of_forall_mem_center {e : G} (he : e * e = 1)
    (heZ : ∀ z ∈ X ⊓ Subgroup.centralizer (X : Set G), e * z * e⁻¹ = z)
    (h : ∀ x ∈ X, x⁻¹ * (e * x * e⁻¹) ∈ X ⊓ Subgroup.centralizer (X : Set G)) :
    X ≤ Subgroup.centralizer ({e} : Set G) := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  intro x hx
  set z := x⁻¹ * (e * x * e⁻¹) with hzdef
  have hz := h x hx
  have hexz : e * x * e⁻¹ = x * z := by rw [hzdef]; group
  have hzz : z * z = 1 := by
    have h1 : x = e * (e * x * e⁻¹) * e⁻¹ := by
      rw [heinv]
      calc x = (e * e) * x * (e * e) := by rw [he]; group
        _ = e * (e * x * e) * e := by group
    have h2 : x = x * z * z := by
      calc x = e * (x * z) * e⁻¹ := by rw [← hexz]; exact h1
        _ = (e * x * e⁻¹) * (e * z * e⁻¹) := by group
        _ = x * z * z := by rw [hexz, heZ z hz]
    calc z * z = x⁻¹ * (x * z * z) := by group
      _ = 1 := by rw [← h2, inv_mul_cancel]
  have hz1 : z = 1 := eq_one_of_sq_eq_one hp hp2 hexp hz.1 hzz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : e * x * e⁻¹ = x := by rw [hexz, hz1, mul_one]
  calc x * e = e * x * e⁻¹ * e := by rw [this]
    _ = e * x := by group

end Extraspecial

omit [Finite G] in
theorem commutatorElement_inv_right_of_commute {x y : G} (h : Commute ⁅x, y⁆ y) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h' : y⁻¹ * ⁅x, y⁆⁻¹ * y = ⁅x, y⁆⁻¹ := by
    rw [mul_assoc, h.inv_left.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← h']
  simp only [commutatorElement_def]
  group

theorem card_ge_of_lt' {A B : Subgroup G} {p : ℕ} (hp : p.Prime) (hBp : IsPGroup p B)
    (hAB : A < B) : p * Nat.card A ≤ Nat.card B := by
  have : Fact p.Prime := ⟨hp⟩
  have hle := hAB.le
  set i := (A.subgroupOf B).index
  have hcard : Nat.card A * i = Nat.card B := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact (A.subgroupOf B).card_mul_index
  have hi1 : i ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h
    exact hAB.ne (le_antisymm hle h)
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hidvd : i ∣ p ^ n := hn ▸ hcard ▸ dvd_mul_left i _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hidvd
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; exact hi1 hk
  have hpi : p ≤ i := by
    rw [hk]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hk0)
  rw [← hcard, mul_comm]
  exact Nat.mul_le_mul_left _ hpi

section Sign

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X)
  (hexp : ∀ x ∈ X, x ^ p = 1)
  (hZp : Nat.card (X ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = p)
  (hX3 : Nat.card X ≤ p ^ 3) (hcomm : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G))

include hp hp2 hXp hexp hZp hX3 hcomm in
theorem sign_of_centralizes_center {e : G} (he : e * e = 1)
    (heX : e ∈ Subgroup.normalizer (X : Set G))
    (heZ : ∀ z ∈ X ⊓ Subgroup.centralizer (X : Set G), e * z * e⁻¹ = z) :
    (∀ x ∈ X, x⁻¹ * (e * x * e⁻¹) ∈ X ⊓ Subgroup.centralizer (X : Set G)) ∨
      (∀ x ∈ X, x * (e * x * e⁻¹) ∈ X ⊓ Subgroup.centralizer (X : Set G)) := by
  set Z := X ⊓ Subgroup.centralizer (X : Set G) with hZdef
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hconj : ∀ x ∈ X, e * x * e⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp heX x).mp hx
  have hcommZ : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hcomm ▸ Subgroup.commutator_mem_commutator ha hb
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha, hau⟩, ⟨b, hb, hbw⟩⟩ := hcon
  set a' := b * (e * b * e⁻¹) with ha'def
  set b' := a⁻¹ * (e * a * e⁻¹) with hb'def
  have ha'X : a' ∈ X := X.mul_mem hb (hconj b hb)
  have hb'X : b' ∈ X := X.mul_mem (X.inv_mem ha) (hconj a ha)
  have hee : e⁻¹ * e⁻¹ = 1 := by rw [heinv, he]
  have hb'inv : e * b' * e⁻¹ = b'⁻¹ := by
    rw [hb'def]
    have h1 : e * (a⁻¹ * (e * a * e⁻¹)) * e⁻¹ = e * a⁻¹ * (e * a) * (e⁻¹ * e⁻¹) := by group
    have h2 : (a⁻¹ * (e * a * e⁻¹))⁻¹ = e * a⁻¹ * e⁻¹ * a := by group
    rw [h1, h2, hee, mul_one, heinv]
    group
  set z₁ := a'⁻¹ * (e * a' * e⁻¹) with hz₁def
  have hz₁ : z₁ ∈ Z := by
    have hea' : e * a' * e⁻¹ = (e * b * e⁻¹) * b := by
      rw [ha'def]
      have h1 : e * (b * (e * b * e⁻¹)) * e⁻¹ =
          (e * b * e⁻¹) * ((e * e) * b * (e⁻¹ * e⁻¹)) := by group
      rw [h1, he, hee]
      group
    rw [hz₁def, hea', ha'def]
    have : (b * (e * b * e⁻¹))⁻¹ * (e * b * e⁻¹ * b) =
        ⁅(e * b * e⁻¹)⁻¹, b⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact hcommZ _ (X.inv_mem (hconj b hb)) _ (X.inv_mem hb)
  have hea' : e * a' * e⁻¹ = a' * z₁ := by rw [hz₁def]; group
  have hZX : Z ≤ X := inf_le_left
  have hcZx : ∀ z ∈ Z, ∀ x ∈ X, Commute z x := fun z hz x hx => commute_of_mem_center hz hx
  have hc1 : ⁅a', b'⁆ ≠ 1 := by
    intro hc
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    set C := X ⊓ Subgroup.centralizer ({a'} : Set G) with hCdef
    have hCX : C < X := by
      refine lt_of_le_of_ne inf_le_left fun h => hbw ⟨ha'X, ?_⟩
      show a' ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxC : x ∈ C := h ▸ hx
      exact Subgroup.mem_centralizer_singleton_iff.mp hxC.2
    have hC2 : Nat.card C ≤ p ^ 2 := by
      have h1 := card_ge_of_lt' hp hXp hCX
      have h2 : p * Nat.card C ≤ p * p ^ 2 := by
        calc p * Nat.card C ≤ Nat.card X := h1
          _ ≤ p ^ 3 := hX3
          _ = p * p ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_left h2 hp.pos
    set D := Z ⊔ Subgroup.zpowers a' with hDdef
    have hDX : D ≤ X := sup_le hZX (Subgroup.zpowers_le.mpr ha'X)
    have hZD : Z < D := by
      refine lt_of_le_of_ne le_sup_left fun h => hbw ?_
      rw [h]
      exact (le_sup_right : Subgroup.zpowers a' ≤ D) (Subgroup.mem_zpowers a')
    have hD2 : p ^ 2 ≤ Nat.card D := by
      have := card_ge_of_lt' hp (hXp.to_le hDX) hZD
      rw [hZp] at this
      rw [pow_two]
      exact this
    have hDC : D ≤ C := by
      refine sup_le (fun z hz => ⟨hz.1, ?_⟩) (Subgroup.zpowers_le.mpr ⟨ha'X, ?_⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcZx z hz a' ha'X)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hDeq : D = C := Subgroup.eq_of_le_of_card_ge hDC (hC2.trans hD2)
    have hb'D : b' ∈ D := hDeq ▸ ⟨hb'X, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩
    obtain ⟨z, hz, y, hy, hb'zy⟩ := GorensteinWalter.mem_sup_decompose_of_centralizes hb'D (by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hcZx z hz _ (X.zpow_mem ha'X k)).eq)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hz₁a : Commute a' z₁ := (hcZx z₁ hz₁ a' ha'X).symm
    have heb' : e * b' * e⁻¹ = b' * z₁ ^ k := by
      rw [hb'zy]
      calc e * (z * a' ^ k) * e⁻¹ = (e * z * e⁻¹) * (e * a' * e⁻¹) ^ k := by
            rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul,
              map_zpow]
        _ = z * (a' * z₁) ^ k := by rw [heZ z hz, hea']
        _ = z * a' ^ k * z₁ ^ k := by rw [hz₁a.mul_zpow, mul_assoc]
    rw [hb'inv] at heb'
    have hsq : b'⁻¹ ^ 2 ∈ Z := by
      have : b'⁻¹ ^ 2 = z₁ ^ k := by
        rw [pow_two]
        calc b'⁻¹ * b'⁻¹ = b'⁻¹ * (b' * z₁ ^ k) := by rw [← heb']
          _ = z₁ ^ k := by group
      rw [this]
      exact Z.zpow_mem hz₁ k
    have := mem_of_sq_mem hp hp2 hexp (X.inv_mem hb'X) hsq
    exact hau (by simpa using Z.inv_mem this)
  have hcZ : ⁅a', b'⁆ ∈ Z := hcommZ a' ha'X b' hb'X
  have hec : e * ⁅a', b'⁆ * e⁻¹ = ⁅a', b'⁆⁻¹ := by
    calc e * ⁅a', b'⁆ * e⁻¹ = ⁅e * a' * e⁻¹, e * b' * e⁻¹⁆ := by
          rw [← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply]
      _ = ⁅a' * z₁, b'⁻¹⁆ := by rw [hea', hb'inv]
      _ = ⁅a', b'⁻¹⁆ :=
          commutatorElement_mul_left_of_commute' (hcZx z₁ hz₁ _ (X.inv_mem hb'X))
      _ = ⁅a', b'⁆⁻¹ :=
          commutatorElement_inv_right_of_commute (hcZx _ hcZ b' hb'X)
  rw [heZ _ hcZ] at hec
  apply hc1
  refine eq_one_of_sq_eq_one hp hp2 hexp (hZX hcZ) ?_
  calc ⁅a', b'⁆ * ⁅a', b'⁆ = ⁅a', b'⁆⁻¹ * ⁅a', b'⁆ := by rw [← hec]
    _ = 1 := inv_mul_cancel _

include hp hp2 hXp hexp hZp hX3 hcomm in
theorem card_le_four_of_faithful {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (X : Set G)) (hEc : IsMulCommutative E)
    (hE2 : ∀ e ∈ E, e * e = 1)
    (hfaith : ∀ e ∈ E, X ≤ Subgroup.centralizer ({e} : Set G) → e = 1) :
    Nat.card E ≤ 4 := by
  classical
  set Z := X ⊓ Subgroup.centralizer (X : Set G) with hZdef
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  have hinvE : ∀ e ∈ E, e⁻¹ = e := fun e he => inv_eq_of_mul_eq_one_right (hE2 e he)
  have hfwd : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
    show g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have := (Subgroup.mem_centralizer_iff.mp hz.2) _ hx'
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * x := by group
  have hNZ : ∀ e ∈ E, e ∈ Subgroup.normalizer (Z : Set G) := by
    intro e he
    have heX := hEN he
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd e heX z, fun hz => ?_⟩
    have h1 := hfwd e⁻¹ (Subgroup.inv_mem _ heX) _ hz
    simpa [mul_assoc] using h1
  let cz : G → Prop := fun e => ∀ z ∈ Z, e * z * e⁻¹ = z
  let pl : G → Prop := fun e => ∀ x ∈ X, x⁻¹ * (e * x * e⁻¹) ∈ Z
  let mi : G → Prop := fun e => ∀ x ∈ X, x * (e * x * e⁻¹) ∈ Z
  have F0 : ∀ e ∈ E, cz e ∨ ∀ z ∈ Z, e * z * e⁻¹ = z⁻¹ := fun e he =>
    conj_eq_or_conj_eq_inv_of_card_eq_prime hp hZp (hE2 e he) (hNZ e he)
  have F1 : ∀ e ∈ E, cz e → pl e → e = 1 := fun e he hcz hpl =>
    hfaith e he (centralizes_of_forall_mem_center hp hp2 hexp (hE2 e he) hcz hpl)
  have F2 : ∀ e ∈ E, cz e → pl e ∨ mi e := fun e he hcz =>
    sign_of_centralizes_center hp hp2 hXp hexp hZp hX3 hcomm (hE2 e he) (hEN he) hcz
  have F3 : ∀ e ∈ E, ∀ f ∈ E, ¬ cz e → ¬ cz f → cz (e * f) := by
    intro e he f hf hce hcf z hz
    have he' := (F0 e he).resolve_left hce
    have hf' := (F0 f hf).resolve_left hcf
    calc e * f * z * (e * f)⁻¹ = e * (f * z * f⁻¹) * e⁻¹ := by group
      _ = e * z⁻¹ * e⁻¹ := by rw [hf' z hz]
      _ = (e * z * e⁻¹)⁻¹ := by group
      _ = z := by rw [he' z hz, inv_inv]
  have F4 : ∀ e ∈ E, ∀ f ∈ E, cz e → cz f → mi e → mi f → cz (e * f) ∧ pl (e * f) := by
    intro e he f hf hce hcf hme hmf
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · calc e * f * z * (e * f)⁻¹ = e * (f * z * f⁻¹) * e⁻¹ := by group
        _ = z := by rw [hcf z hz, hce z hz]
    · set z₁ := x * (f * x * f⁻¹)
      set z₂ := x * (e * x * e⁻¹)
      have hz₁ : z₁ ∈ Z := hmf x hx
      have hz₂ : z₂ ∈ Z := hme x hx
      have hfx : f * x * f⁻¹ = x⁻¹ * z₁ := by simp only [z₁]; group
      have hex : e * x * e⁻¹ = x⁻¹ * z₂ := by simp only [z₂]; group
      have h : x⁻¹ * (e * f * x * (e * f)⁻¹) = z₂⁻¹ * z₁ := by
        calc x⁻¹ * (e * f * x * (e * f)⁻¹) = x⁻¹ * (e * (f * x * f⁻¹) * e⁻¹) := by group
          _ = x⁻¹ * (e * (x⁻¹ * z₁) * e⁻¹) := by rw [hfx]
          _ = x⁻¹ * ((e * x * e⁻¹)⁻¹ * (e * z₁ * e⁻¹)) := by group
          _ = x⁻¹ * ((x⁻¹ * z₂)⁻¹ * z₁) := by rw [hex, hce z₁ hz₁]
          _ = x⁻¹ * z₂⁻¹ * x * z₁ := by group
          _ = z₂⁻¹ * z₁ := by
              rw [mul_assoc x⁻¹, (commute_of_mem_center (Z.inv_mem hz₂) hx).eq]
              group
      rw [show (e * f) * x * (e * f)⁻¹ = e * f * x * (e * f)⁻¹ by rfl, h]
      exact Z.mul_mem (Z.inv_mem hz₂) hz₁
  obtain ⟨a, haE, hacz, hami⟩ : ∃ a ∈ E, cz a ∧ (a ≠ 1 → mi a) ∧
      (∀ e ∈ E, cz e → mi e → e ≠ 1 → a ≠ 1) := by
    by_cases h : ∃ a ∈ E, cz a ∧ mi a ∧ a ≠ 1
    · obtain ⟨a, haE, hacz, hami, ha1⟩ := h
      exact ⟨a, haE, hacz, fun _ => hami, fun _ _ _ _ _ => ha1⟩
    · push Not at h
      refine ⟨1, E.one_mem, fun z _ => by group, fun h1 => absurd rfl h1, ?_⟩
      intro e he hce hme he1
      exact absurd (h e he hce hme) he1
  obtain ⟨b, hbE, hb⟩ : ∃ b ∈ E, ∀ e ∈ E, ¬ cz e → ¬ cz b := by
    by_cases h : ∃ b ∈ E, ¬ cz b
    · obtain ⟨b, hbE, hb⟩ := h
      exact ⟨b, hbE, fun _ _ _ => hb⟩
    · push Not at h
      exact ⟨1, E.one_mem, fun e he hce => absurd (h e he) hce⟩
  obtain ⟨hami, hamin⟩ := hami
  have hI : ∀ f ∈ E, cz f → f = 1 ∨ f = a := by
    intro f hf hcf
    rcases F2 f hf hcf with hpl | hmi
    · exact Or.inl (F1 f hf hcf hpl)
    · by_cases hf1 : f = 1
      · exact Or.inl hf1
      · right
        have ha1 : a ≠ 1 := hamin f hf hcf hmi hf1
        obtain ⟨h1, h2⟩ := F4 f hf a haE hcf hacz hmi (hami ha1)
        have hfa := F1 _ (E.mul_mem hf haE) h1 h2
        calc f = f * a * a⁻¹ := by group
          _ = a := by rw [hfa, one_mul, hinvE a haE]
  have key : ∀ e ∈ E, e = 1 ∨ e = a ∨ e = b ∨ e = a * b := by
    intro e he
    by_cases hce : cz e
    · rcases hI e he hce with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hcb := hb e he hce
      have hceb := F3 e he b hbE hce hcb
      rcases hI _ (E.mul_mem he hbE) hceb with h | h
      · right; right; left
        calc e = e * b * b⁻¹ := by group
          _ = b := by rw [h, one_mul, hinvE b hbE]
      · right; right; right
        calc e = e * b * b⁻¹ := by group
          _ = a * b := by rw [h, hinvE b hbE]
  have hsub : (E : Set G) ⊆ ↑({1, a, b, a * b} : Finset G) := by
    intro e he
    rcases key e he with h | h | h | h <;> simp [h]
  calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑({1, a, b, a * b} : Finset G) : Set G).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, a, b, a * b} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp

end Sign

end CFSG.Walter
