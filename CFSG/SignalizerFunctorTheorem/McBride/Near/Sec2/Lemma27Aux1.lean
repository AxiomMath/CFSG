module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

@[expose] def wSub (A B X : Subgroup Γ) : Subgroup Γ :=
  ⨆ (E : Subgroup Γ) (_ : E ≤ A ∧ E ⊓ B = ⊥ ∧ E ⊔ B = A), cenIn X E

theorem mem_cenIn_iff {X : Subgroup Γ} {S : Set Γ} {x : Γ} :
    x ∈ cenIn X S ↔ x ∈ X ∧ ∀ s ∈ S, s * x = x * s := by
  unfold cenIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]

theorem cenIn_le_left (X : Subgroup Γ) (S : Set Γ) : cenIn X S ≤ X := inf_le_left

theorem cenIn_mono_left {X Y : Subgroup Γ} (h : Y ≤ X) (S : Set Γ) : cenIn Y S ≤ cenIn X S :=
  inf_le_inf_right _ h

theorem le_cenIn_of_le_centralizer {X : Subgroup Γ} {E : Subgroup Γ}
    (h : E ≤ Subgroup.centralizer (X : Set Γ)) : X ≤ cenIn X (E : Set Γ) := by
  intro x hx
  rw [mem_cenIn_iff]
  refine ⟨hx, fun e he => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (h he) x hx).symm

theorem wSub_le (A B X : Subgroup Γ) : wSub A B X ≤ X :=
  iSup₂_le fun _ _ => cenIn_le_left _ _

theorem wSub_mono {X Y : Subgroup Γ} (A B : Subgroup Γ) (h : Y ≤ X) :
    wSub A B Y ≤ wSub A B X :=
  iSup₂_mono fun _ _ => cenIn_mono_left h _

theorem cenIn_le_wSub {A B E X : Subgroup Γ} (hE : E ≤ A ∧ E ⊓ B = ⊥ ∧ E ⊔ B = A) :
    cenIn X (E : Set Γ) ≤ wSub A B X :=
  le_iSup₂_of_le E hE le_rfl

theorem admits_cenIn {A X S : Subgroup Γ} (hA : IsMulCommutative A) (hAX : Admits A X)
    (hSA : S ≤ A) : Admits A (cenIn X (S : Set Γ)) := by
  have key : ∀ a ∈ A, ∀ y : Γ, y ∈ cenIn X (S : Set Γ) → a * y * a⁻¹ ∈ cenIn X (S : Set Γ) := by
    intro a ha y hy
    have hcomm : ∀ s ∈ S, s * a = a * s := fun s hs =>
      congrArg Subtype.val (mul_comm' (⟨s, hSA hs⟩ : A) ⟨a, ha⟩)
    rw [mem_cenIn_iff] at hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAX ha) y).mp hy.1, fun s hs => ?_⟩
    have h1 := hy.2 s hs
    have h2 := hcomm s hs
    have h3 : a⁻¹ * s = s * a⁻¹ := by
      have := congrArg (fun z => a⁻¹ * z * a⁻¹) h2
      simpa [mul_assoc] using this
    calc s * (a * y * a⁻¹) = (s * a) * y * a⁻¹ := by group
      _ = (a * s) * y * a⁻¹ := by rw [h2]
      _ = a * (s * y) * a⁻¹ := by group
      _ = a * (y * s) * a⁻¹ := by rw [h1]
      _ = a * y * (s * a⁻¹) := by group
      _ = a * y * (a⁻¹ * s) := by rw [h3]
      _ = a * y * a⁻¹ * s := by group
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ hx

theorem admits_wSub {A B X : Subgroup Γ} (hA : IsMulCommutative A) (hAX : Admits A X) :
    Admits A (wSub A B X) := by
  have key : ∀ a ∈ A, ∀ y : Γ, y ∈ wSub A B X → a * y * a⁻¹ ∈ wSub A B X := by
    intro a ha y hy
    have hle : wSub A B X ≤ (wSub A B X).comap (MulAut.conj a).toMonoidHom := by
      refine iSup₂_le fun E hE => ?_
      intro z hz
      exact cenIn_le_wSub hE
        ((Subgroup.mem_normalizer_iff.mp (admits_cenIn hA hAX hE.1 ha) z).mp hz)
    exact hle hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ hx

theorem isMulCommutative_of_le {A F : Subgroup Γ} (hA : IsMulCommutative A) (hFA : F ≤ A) :
    IsMulCommutative F :=
  ⟨⟨fun x y => Subtype.ext (by
    have := mul_comm' (⟨x, hFA x.2⟩ : A) ⟨y, hFA y.2⟩
    simpa using congrArg Subtype.val this)⟩⟩

theorem exists_isCompl_of_le {p : ℕ} (hp : p.Prime) {A : Subgroup Γ} (hA : IsElemAbelian p A)
    {D F : Subgroup Γ} (hDF : D ≤ F) (hFA : F ≤ A) :
    ∃ E : Subgroup Γ, E ≤ F ∧ D ⊓ E = ⊥ ∧ D ⊔ E = F := by
  have : IsMulCommutative F := isMulCommutative_of_le hA.1 hFA
  let _ : CommGroup F := { (inferInstance : Group F) with mul_comm := mul_comm' }
  obtain ⟨E', hE'⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists p hp F
    (fun x => Subtype.ext (by simpa using hA.2 x (hFA x.2))) (D.subgroupOf F)
  have hD : (D.subgroupOf F).map F.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDF
  refine ⟨E'.map F.subtype, Subgroup.map_subtype_le E', ?_, ?_⟩
  · rw [← hD, ← Subgroup.map_inf_eq _ _ F.subtype F.subtype_injective, hE'.disjoint.eq_bot,
      Subgroup.map_bot]
  · rw [← hD, ← Subgroup.map_sup, hE'.sup_eq_top, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_zpow_mul_eq {p : ℕ} (hp : p.Prime) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i) :
    ∃ j k : ℤ, i * j = 1 + p * k := by
  have hcop : IsCoprime (p : ℤ) i :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hi
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨v, -u, by linarith⟩

theorem mem_zpowers_zpow {p : ℕ} (hp : p.Prime) {g : Γ} (hg : g ^ p = 1) {i : ℤ}
    (hi : ¬ (p : ℤ) ∣ i) : g ∈ Subgroup.zpowers (g ^ i) := by
  obtain ⟨j, k, hjk⟩ := exists_zpow_mul_eq hp hi
  refine ⟨j, ?_⟩
  show (g ^ i) ^ j = g
  rw [← zpow_mul, hjk, zpow_add, zpow_one, zpow_mul, zpow_natCast, hg, one_zpow, mul_one]

theorem zpow_eq_one_of_dvd {p : ℕ} {g : Γ} (hg : g ^ p = 1) {i : ℤ} (hi : (p : ℤ) ∣ i) :
    g ^ i = 1 := by
  obtain ⟨k, rfl⟩ := hi
  rw [zpow_mul, zpow_natCast, hg, one_zpow]

theorem pow_eq_one_of_isElemAbelian {p : ℕ} {A : Subgroup Γ} (hA : IsElemAbelian p A) {a : Γ}
    (ha : a ∈ A) : a ^ p = 1 := hA.2 a ha

theorem commute_of_mem {A : Subgroup Γ} (hA : IsMulCommutative A) {a b : Γ} (ha : a ∈ A)
    (hb : b ∈ A) : Commute a b :=
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem mem_sup_zpowers_iff {A C : Subgroup Γ} (hA : IsMulCommutative A) (hCA : C ≤ A) {a : Γ}
    (ha : a ∈ A) {z : Γ} :
    z ∈ C ⊔ Subgroup.zpowers a ↔ ∃ c ∈ C, ∃ i : ℤ, c * a ^ i = z := by
  have hcomm : ∀ x ∈ C, ∀ y ∈ Subgroup.zpowers a, Commute x y := by
    intro x hx y hy
    exact commute_of_mem hA (hCA hx) ((Subgroup.zpowers_le.mpr ha) hy)
  rw [mem_sup_iff_of_commute hcomm]
  constructor
  · rintro ⟨c, hc, l, hl, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact ⟨c, hc, i, rfl⟩
  · rintro ⟨c, hc, i, rfl⟩
    exact ⟨c, hc, a ^ i, Subgroup.zpow_mem_zpowers a i, rfl⟩

theorem mem_sup_zpowers_of_not_mem {p : ℕ} (hp : p.Prime) {A C : Subgroup Γ}
    (hA : IsElemAbelian p A) (hCA : C ≤ A) {a b : Γ} (ha : a ∈ A)
    (hb : b ∈ C ⊔ Subgroup.zpowers a) (hbC : b ∉ C) : a ∈ C ⊔ Subgroup.zpowers b := by
  obtain ⟨c, hc, i, rfl⟩ := (mem_sup_zpowers_iff hA.1 hCA ha).mp hb
  have hi : ¬ (p : ℤ) ∣ i := by
    intro hdvd
    rw [zpow_eq_one_of_dvd (pow_eq_one_of_isElemAbelian hA ha) hdvd, mul_one] at hbC
    exact hbC hc
  have h1 : a ∈ Subgroup.zpowers (a ^ i) :=
    mem_zpowers_zpow hp (pow_eq_one_of_isElemAbelian hA ha) hi
  have h2 : a ^ i ∈ C ⊔ Subgroup.zpowers (c * a ^ i) := by
    have h := Subgroup.mul_mem_sup (inv_mem hc : c⁻¹ ∈ C)
      (Subgroup.mem_zpowers (c * a ^ i))
    simpa using h
  have h3 : Subgroup.zpowers (a ^ i) ≤ C ⊔ Subgroup.zpowers (c * a ^ i) :=
    Subgroup.zpowers_le.mpr h2
  exact h3 h1

theorem le_wSub_or_le_cenIn_of_cyclic {p : ℕ} (hp : p.Prime) {A B X C : Subgroup Γ}
    (hA : IsElemAbelian p A) (hCA : C ≤ A) (hCX : C ≤ Subgroup.centralizer (X : Set Γ))
    (hB : B ≤ A) {a : Γ} (ha : a ∈ A) (hAa : A ≤ C ⊔ Subgroup.zpowers a) :
    X ≤ wSub A B X ∨ X ≤ cenIn X (B : Set Γ) := by
  by_cases hBC : B ≤ C
  · exact Or.inr (le_cenIn_of_le_centralizer (hBC.trans hCX))
  · left
    obtain ⟨b, hbB, hbC⟩ := Set.not_subset.mp hBC
    have hbA : b ∈ A := hB hbB
    have haCb : a ∈ C ⊔ Subgroup.zpowers b :=
      mem_sup_zpowers_of_not_mem hp hA hCA ha (hAa hbA) hbC
    have hCB : A ≤ C ⊔ B := by
      refine hAa.trans (sup_le le_sup_left ?_)
      refine Subgroup.zpowers_le.mpr ?_
      have : C ⊔ Subgroup.zpowers b ≤ C ⊔ B :=
        sup_le_sup_left (Subgroup.zpowers_le.mpr hbB) C
      exact this haCb
    obtain ⟨E, hEC, hE1, hE2⟩ := exists_isCompl_of_le hp hA (inf_le_right : B ⊓ C ≤ C) hCA
    have hEA : E ≤ A := hEC.trans hCA
    have hEB : E ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxE := (Subgroup.mem_inf.mp hx).1
      have hxB := (Subgroup.mem_inf.mp hx).2
      have : x ∈ (B ⊓ C) ⊓ E := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxB, hEC hxE⟩, hxE⟩
      rw [hE1] at this
      exact this
    have hEsup : E ⊔ B = A := by
      refine le_antisymm (sup_le hEA hB) ?_
      refine hCB.trans (sup_le ?_ le_sup_right)
      rw [← hE2]
      exact sup_le (inf_le_left.trans le_sup_right) le_sup_left
    exact (le_cenIn_of_le_centralizer (hEC.trans hCX)).trans (cenIn_le_wSub ⟨hEA, hEB, hEsup⟩)

theorem zpow_identity {A : Subgroup Γ} (hA : IsMulCommutative A) {x y c : Γ} (hx : x ∈ A)
    (hy : y ∈ A) (hc : c ∈ A) (s₁ t₁ s₂ t₂ i : ℤ)
    (h : c * (x ^ s₁ * y ^ t₁) ^ i = x ^ s₂ * y ^ t₂) :
    x ^ (s₂ - s₁ * i) * y ^ (t₂ - t₁ * i) = c := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  have key : ∀ (x y c : A), c * (x ^ s₁ * y ^ t₁) ^ i = x ^ s₂ * y ^ t₂ →
      x ^ (s₂ - s₁ * i) * y ^ (t₂ - t₁ * i) = c := by
    intro x y c h
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_zpow] at h'
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    linear_combination (norm := module) (-1 : ℤ) • h'
  have := key ⟨x, hx⟩ ⟨y, hy⟩ ⟨c, hc⟩ (Subtype.ext (by simpa using h))
  simpa using congrArg Subtype.val this

theorem dvd_of_zpow_mul_zpow_mem {p : ℕ} (hp : p.Prime) {A C : Subgroup Γ}
    (hA : IsElemAbelian p A) {x y : Γ} (hx : x ∈ A) (hy : y ∈ A) (hxC : x ∉ C)
    (hyx : y ∉ C ⊔ Subgroup.zpowers x) {s t : ℤ} (h : x ^ s * y ^ t ∈ C) :
    (p : ℤ) ∣ s ∧ (p : ℤ) ∣ t := by
  have hxp := pow_eq_one_of_isElemAbelian hA hx
  have hyp := pow_eq_one_of_isElemAbelian hA hy
  have ht : (p : ℤ) ∣ t := by
    by_contra ht
    refine hyx ?_
    have h1 : y ^ t ∈ C ⊔ Subgroup.zpowers x := by
      have : y ^ t = (x ^ s)⁻¹ * (x ^ s * y ^ t) := by group
      rw [this]
      exact mul_mem (inv_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x s)))
        (Subgroup.mem_sup_left h)
    exact (Subgroup.zpowers_le.mpr h1) (mem_zpowers_zpow hp hyp ht)
  refine ⟨?_, ht⟩
  by_contra hs
  rw [zpow_eq_one_of_dvd hyp ht, mul_one] at h
  exact hxC ((Subgroup.zpowers_le.mpr h) (mem_zpowers_zpow hp hxp hs))

theorem zpow_mul_zpow_not_mem_sup {p : ℕ} (hp : p.Prime) {A C : Subgroup Γ}
    (hA : IsElemAbelian p A) (hCA : C ≤ A) {x y : Γ} (hx : x ∈ A) (hy : y ∈ A) (hxC : x ∉ C)
    (hyx : y ∉ C ⊔ Subgroup.zpowers x) {s₁ t₁ s₂ t₂ : ℤ}
    (hdet : ¬ (p : ℤ) ∣ s₁ * t₂ - s₂ * t₁) :
    x ^ s₂ * y ^ t₂ ∉ C ⊔ Subgroup.zpowers (x ^ s₁ * y ^ t₁) := by
  intro hmem
  have ha : x ^ s₁ * y ^ t₁ ∈ A := mul_mem (zpow_mem hx _) (zpow_mem hy _)
  obtain ⟨c, hc, i, hci⟩ := (mem_sup_zpowers_iff hA.1 hCA ha).mp hmem
  have h1 := zpow_identity hA.1 hx hy (hCA hc) s₁ t₁ s₂ t₂ i hci
  obtain ⟨hd1, hd2⟩ := dvd_of_zpow_mul_zpow_mem hp hA hx hy hxC hyx (h1 ▸ hc)
  apply hdet
  have : s₁ * t₂ - s₂ * t₁ = -(s₂ - s₁ * i) * t₁ + (t₂ - t₁ * i) * s₁ := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr hd1) _) (dvd_mul_of_dvd_left hd2 _)

theorem exists_three_semiregular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A C N : Subgroup Γ}
    (hA : IsElemAbelian p A) (hCA : C ≤ A) (hCN : C ≤ N) {x y : Γ} (hx : x ∈ A) (hxN : x ∉ N)
    (hy : y ∈ A) (hyx : y ∉ C ⊔ Subgroup.zpowers x) :
    ∃ a : Fin 3 → Γ, (∀ i, a i ∈ A ∧ a i ∉ N) ∧
      ∀ i j, i ≠ j → a j ∉ C ⊔ Subgroup.zpowers (a i) := by
  have hxC : x ∉ C := fun h => hxN (hCN h)
  have hnd : ∀ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) → ¬ (p : ℤ) ∣ d := by
    intro d hd hdvd
    have h := Int.natCast_dvd.mp hdvd
    rcases hd with rfl | rfl | rfl | rfl <;> simp at h
    · exact hp.one_lt.ne' h
    · exact hp.one_lt.ne' h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hind : ∀ s₁ t₁ s₂ t₂ : ℤ,
      (s₁ * t₂ - s₂ * t₁ = 1 ∨ s₁ * t₂ - s₂ * t₁ = -1 ∨ s₁ * t₂ - s₂ * t₁ = 2 ∨
        s₁ * t₂ - s₂ * t₁ = -2) →
      x ^ s₂ * y ^ t₂ ∉ C ⊔ Subgroup.zpowers (x ^ s₁ * y ^ t₁) := fun s₁ t₁ s₂ t₂ hd =>
    zpow_mul_zpow_not_mem_sup hp hA hCA hx hy hxC hyx (hnd _ hd)
  have e10 : x ^ (1 : ℤ) * y ^ (0 : ℤ) = x := by simp
  have e11 : x ^ (1 : ℤ) * y ^ (1 : ℤ) = x * y := by simp
  have e12 : x ^ (1 : ℤ) * y ^ (2 : ℤ) = x * y ^ 2 := by simp [pow_two]
  have e01 : x ^ (0 : ℤ) * y ^ (1 : ℤ) = y := by simp
  have i01 : x * y ∉ C ⊔ Subgroup.zpowers x := by
    have := hind 1 0 1 1 (by norm_num); rwa [e10, e11] at this
  have i02 : x * y ^ 2 ∉ C ⊔ Subgroup.zpowers x := by
    have := hind 1 0 1 2 (by norm_num); rwa [e10, e12] at this
  have i03 : y ∉ C ⊔ Subgroup.zpowers x := hyx
  have i10 : x ∉ C ⊔ Subgroup.zpowers (x * y) := by
    have := hind 1 1 1 0 (by norm_num); rwa [e10, e11] at this
  have i12 : x * y ^ 2 ∉ C ⊔ Subgroup.zpowers (x * y) := by
    have := hind 1 1 1 2 (by norm_num); rwa [e11, e12] at this
  have i13 : y ∉ C ⊔ Subgroup.zpowers (x * y) := by
    have := hind 1 1 0 1 (by norm_num); rwa [e11, e01] at this
  have i20 : x ∉ C ⊔ Subgroup.zpowers (x * y ^ 2) := by
    have := hind 1 2 1 0 (by norm_num); rwa [e10, e12] at this
  have i21 : x * y ∉ C ⊔ Subgroup.zpowers (x * y ^ 2) := by
    have := hind 1 2 1 1 (by norm_num); rwa [e11, e12] at this
  have i23 : y ∉ C ⊔ Subgroup.zpowers (x * y ^ 2) := by
    have := hind 1 2 0 1 (by norm_num); rwa [e12, e01] at this
  have i30 : x ∉ C ⊔ Subgroup.zpowers y := by
    have := hind 0 1 1 0 (by norm_num); rwa [e10, e01] at this
  have i31 : x * y ∉ C ⊔ Subgroup.zpowers y := by
    have := hind 0 1 1 1 (by norm_num); rwa [e11, e01] at this
  have i32 : x * y ^ 2 ∉ C ⊔ Subgroup.zpowers y := by
    have := hind 0 1 1 2 (by norm_num); rwa [e12, e01] at this
  have hxyA : x * y ∈ A := mul_mem hx hy
  have hxy2A : x * y ^ 2 ∈ A := mul_mem hx (pow_mem hy 2)
  by_cases hyN : y ∈ N
  · have h1 : x * y ∉ N := fun h => hxN (by simpa using mul_mem h (inv_mem hyN))
    have h2 : x * y ^ 2 ∉ N := fun h => hxN (by
      have := mul_mem h (inv_mem (pow_mem hyN 2)); simpa using this)
    refine ⟨![x, x * y, x * y ^ 2], fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> simp [hx, hxN, hxyA, h1, hxy2A, h2]
    · fin_cases i <;> fin_cases j <;> simp_all
  · by_cases hxyN : x * y ∈ N
    · have h2 : x * y ^ 2 ∉ N := fun h => hyN (by
        have := mul_mem h (inv_mem hxyN)
        have hxy : x * y = y * x := (commute_of_mem hA.1 hx hy).eq
        have e : x * y ^ 2 * (x * y)⁻¹ = y := by
          calc x * y ^ 2 * (x * y)⁻¹ = x * y * x⁻¹ := by group
            _ = y * x * x⁻¹ := by rw [hxy]
            _ = y := by group
        rwa [e] at this)
      refine ⟨![x, y, x * y ^ 2], fun i => ?_, fun i j hij => ?_⟩
      · fin_cases i <;> simp [hx, hxN, hy, hyN, hxy2A, h2]
      · fin_cases i <;> fin_cases j <;> simp_all
    · refine ⟨![x, y, x * y], fun i => ?_, fun i j hij => ?_⟩
      · fin_cases i <;> simp [hx, hxN, hy, hyN, hxyA, hxyN]
      · fin_cases i <;> fin_cases j <;> simp_all

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
