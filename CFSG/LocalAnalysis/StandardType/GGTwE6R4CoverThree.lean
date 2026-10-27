module

public import CFSG.LocalAnalysis.StandardType.GGTwE6R4Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree

public section

namespace CFSG.StandardType.TwE6R4

open CFSG.Open
open CFSG.LieType.Steinberg.Exceptional


private theorem c2_conj_injective {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Function.Injective
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hrZ : r ∈ Subgroup.center (TwE6Delta.RecipeR K n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun f : MulAut (TwE6Delta.RecipeR K n) => f g) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * r = r * g * r⁻¹ * r := by rw [h]
      _ = r * g := by group
  rw [TwE6Delta.center_recipeR_eq_bot hn hK] at hrZ
  exact hrZ

private theorem c2_conj_mem {n : ℕ} {K : Type} [Field K]
    (r : TwE6Delta.RecipeR K n) : MulAut.conj r ∈ TwE6Delta.RecipeI K n :=
  Subgroup.subset_closure (Set.mem_union_left _ ⟨r, rfl⟩)

private theorem c2_congr_conj {G H : Type*} [Group G] [Group H] (Φ : MulAut G ≃* MulAut H)
    (a b : MulAut G) : Φ (MulAut.conj a b) = MulAut.conj (Φ a) (Φ b) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem c2_exists_conj {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {Y Y₁ : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hY : IsElemAbelian 3 Y)
    (hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hY6 : Nat.card Y = 3 ^ 6)
    (hY₁ : IsElemAbelian 3 Y₁)
    (hY₁I : (Y₁ : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hY₁6 : Nat.card Y₁ = 3 ^ 6) :
    ∃ β : MulAut (TwE6Delta.RecipeR K n),
      ∀ y ∈ Y, ∃ y₁ ∈ Y₁, MulAut.conj β y₁ = y := by
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set Φ := MulAut.congr ε with hΦ
  have hY₀ : IsElemAbelian 3 (Y.map Φ.symm.toMonoidHom) := hY.map _
  have hY₀card : Nat.card (Y.map Φ.symm.toMonoidHom) = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (K := Y) (fun a b h => Φ.symm.injective h)).trans hY6
  have hY₀I : Y.map Φ.symm.toMonoidHom ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hε (Φ.symm y)).1 (by rw [MulEquiv.apply_symm_apply]; exact hYI hy)
  have hY₁₀ : IsElemAbelian 3 (Y₁.map Φ.symm.toMonoidHom) := hY₁.map _
  have hY₁₀card : Nat.card (Y₁.map Φ.symm.toMonoidHom) = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (K := Y₁) (fun a b h => Φ.symm.injective h)).trans hY₁6
  have hY₁₀I : Y₁.map Φ.symm.toMonoidHom ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hε (Φ.symm y)).1 (by rw [MulEquiv.apply_symm_apply]; exact hY₁I hy)
  obtain ⟨β₀, -, hβ₀⟩ :=
    TwE6DD2.exists_conj_of_card hn hK σ hσ h3 hY₁₀ hY₁₀I hY₁₀card hY₀ hY₀I hY₀card
  refine ⟨Φ β₀, fun y hy => ?_⟩
  have hy₀ : Φ.symm y ∈ Y.map Φ.symm.toMonoidHom := ⟨y, hy, rfl⟩
  rw [← hβ₀] at hy₀
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hy₀
  obtain ⟨y₁, hy₁, hy₁eq⟩ := Subgroup.mem_map.1 hx
  refine ⟨y₁, hy₁, ?_⟩
  have hxy : Φ x = y₁ := by
    rw [← hy₁eq]
    exact MulEquiv.apply_symm_apply Φ y₁
  calc MulAut.conj (Φ β₀) y₁ = MulAut.conj (Φ β₀) (Φ x) := by rw [hxy]
    _ = Φ (MulAut.conj β₀ x) := (c2_congr_conj Φ β₀ x).symm
    _ = Φ (Φ.symm y) := congrArg Φ hxeq
    _ = y := MulEquiv.apply_symm_apply Φ y

private theorem c2_torus (h5 : GGTwE6ThreeNoRankSixInput) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (h9 : ¬ 9 ∣ 2 ^ n + 1)
    {q : twistedE6Group 2 n →* TwE6Delta.RecipeR K n}
    (hq : Function.Surjective q)
    (hqk : q.ker ≤ Subgroup.center (twistedE6Group 2 n)) :
    ∃ E : Subgroup (twistedE6Group 2 n), IsElemAbelian 3 E ∧
      ∃ Y₁ : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 Y₁ ∧
        (↑Y₁ : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n ∧
        Nat.card Y₁ = 3 ^ 6 ∧ ∀ u, MulAut.conj (q u) ∈ Y₁ → u ∈ E := by
  obtain ⟨E, hE, hEcard⟩ := TwE6Lang.exists_isElemAbelian_twistedE6 hn Nat.prime_three h3
  haveI := TwE6DD2.finite_twistedE6Group n
  haveI := TwE6Delta.finite_mulAut_recipeR hK
  have hqk3 : Nat.card q.ker ∣ 3 :=
    (Subgroup.card_dvd_of_le hqk).trans (TwE6DD2.card_center_dvd_three hn)
  have hrange : (q.domRestrict E).range = E.map q := by
    rw [MonoidHom.range_eq_map]
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨e, -, he⟩
      exact ⟨(e : twistedE6Group 2 n), e.2, by simpa using he⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, trivial, rfl⟩
  have hne : E ⊓ q.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (q.domRestrict E) := by
      intro a b hab
      have hab' : q (a : twistedE6Group 2 n) = q (b : twistedE6Group 2 n) := by
        simpa using hab
      have hmem : (a : twistedE6Group 2 n) * (b : twistedE6Group 2 n)⁻¹ ∈ E ⊓ q.ker :=
        ⟨E.mul_mem a.2 (E.inv_mem b.2), by
          show q ((a : twistedE6Group 2 n) * (b : twistedE6Group 2 n)⁻¹) = 1
          rw [map_mul, map_inv, hab', mul_inv_cancel]⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext (mul_inv_eq_one.mp hmem)
    have hcard : Nat.card (E.map q) = 3 ^ 6 := by
      have h1 : Nat.card (q.domRestrict E).range = Nat.card E := by
        have h2 := Subgroup.card_map_of_injective (f := q.domRestrict E) (K := ⊤) hinj
        rwa [Subgroup.map_top, Subgroup.card_top] at h2
      rw [← hrange, h1, hEcard]
    exact h5 K n hn hK h3 h9 (E.map q) (hE.map q) hcard
  have hne' : ¬ ∀ x ∈ E ⊓ q.ker, x = 1 := fun h => hne ((Subgroup.eq_bot_iff_forall _).2 h)
  push Not at hne'
  obtain ⟨c, hc, hc1⟩ := hne'
  have hc3 : orderOf c = 3 := by
    have h1 : orderOf c ∣ 3 := (Subgroup.orderOf_dvd_natCard q.ker hc.2).trans hqk3
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hc1
    · exact h
  have hqk_card : Nat.card q.ker = 3 := by
    have h3dvd : 3 ∣ Nat.card q.ker := by
      rw [← hc3]
      exact Subgroup.orderOf_dvd_natCard q.ker hc.2
    exact Nat.dvd_antisymm hqk3 h3dvd
  have hkerE : q.ker ≤ E := by
    have h3dvd : 3 ∣ Nat.card ↥(E ⊓ q.ker) := by
      rw [← hc3]
      exact Subgroup.orderOf_dvd_natCard (E ⊓ q.ker) hc
    have hle3 : Nat.card ↥(E ⊓ q.ker) ∣ 3 := by
      rw [← hqk_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcard : Nat.card ↥(E ⊓ q.ker) = Nat.card ↥q.ker := by
      rw [hqk_card]
      exact (Nat.dvd_antisymm h3dvd hle3).symm
    have heq : E ⊓ q.ker = q.ker :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq hcard.symm)
    intro x hx
    exact (heq.ge hx).1
  have hĒcard : Nat.card (E.map q) = 3 ^ 5 := by
    have hker : (q.domRestrict E).ker = q.ker.subgroupOf E := MonoidHom.ker_domRestrict E q
    have hkercard : Nat.card (q.ker.subgroupOf E) = 3 := by
      have hmap : (q.ker.subgroupOf E).map E.subtype = q.ker := by
        apply le_antisymm
        · rintro x ⟨e, he, rfl⟩
          exact Subgroup.mem_subgroupOf.mp he
        · intro x hx
          exact ⟨⟨x, hkerE hx⟩, hx, rfl⟩
      rw [← Subgroup.card_map_of_injective (f := E.subtype) (K := q.ker.subgroupOf E)
        (Subgroup.subtype_injective E), hmap, hqk_card]
    have hprod := Subgroup.card_ker_mul_card_range (q.domRestrict E)
    rw [hker, hrange, hkercard, hEcard] at hprod
    have h2 : 3 * Nat.card (E.map q) = 3 * 3 ^ 5 := by rw [hprod]; norm_num
    exact Nat.mul_left_cancel (by norm_num) h2
  have hconjinj := c2_conj_injective hn hK
  set X : Subgroup (MulAut (TwE6Delta.RecipeR K n)) :=
    (E.map q).map (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))
    with hXdef
  have hX : IsElemAbelian 3 X := (hE.map q).map _
  have hXcard : Nat.card X = 3 ^ 5 := by
    rw [hXdef, Subgroup.card_map_of_injective hconjinj, hĒcard]
  have hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro x ⟨r, -, rfl⟩
    exact c2_conj_mem r
  obtain ⟨Y₁, hXY₁, hY₁, hY₁I, hY₁6, -⟩ :=
    TwE6DD2.exists_cubeTorus_recipe hn hK h3 hX hXI (by rw [hXcard])
  refine ⟨E, hE, Y₁, hY₁, hY₁I, hY₁6, ?_⟩
  let cR : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n) := MulAut.conj
  have hconjinj' : Function.Injective cR := hconjinj
  have hnotinn : ¬ Y₁ ≤ cR.range := by
    intro hinn
    have hR₁ : IsElemAbelian 3 (Y₁.comap cR) := hY₁.comap hconjinj'
    have hcardR₁ : Nat.card ↥(Y₁.comap cR) = 3 ^ 6 := by
      have hmap : (Y₁.comap cR).map cR = Y₁ := by
        rw [Subgroup.map_comap_eq, inf_eq_right.mpr hinn]
      rw [← Subgroup.card_map_of_injective (f := cR) (K := Y₁.comap cR) hconjinj',
        hmap, hY₁6]
    exact h5 K n hn hK h3 h9 _ hR₁ hcardR₁
  change ∀ u, cR (q u) ∈ Y₁ → u ∈ E
  intro u hu
  have hEq : Y₁ ⊓ cR.range = X := by
    have h1 : X ≤ Y₁ ⊓ cR.range := by
      refine le_inf hXY₁ ?_
      rintro x ⟨r, -, rfl⟩
      exact ⟨r, rfl⟩
    have h2 : Nat.card ↥(Y₁ ⊓ cR.range) ≤ Nat.card X := by
      have hdvd : Nat.card ↥(Y₁ ⊓ cR.range) ∣ 3 ^ 6 := by
        rw [← hY₁6]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, hk, hk6⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hne6 : Nat.card ↥(Y₁ ⊓ cR.range) ≠ 3 ^ 6 := by
        intro hc
        have heq : Y₁ ⊓ cR.range = Y₁ :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hY₁6, hc])
        exact hnotinn (heq ▸ inf_le_right)
      have hkne : k ≠ 6 := by
        rintro rfl
        exact hne6 hk6
      have hk5 : k ≤ 5 := by omega
      rw [hXcard]
      calc Nat.card ↥(Y₁ ⊓ cR.range) = 3 ^ k := hk6
        _ ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk5
    exact (Subgroup.eq_of_le_of_card_ge h1 h2).symm
  have hu' : cR (q u) ∈ Y₁ ⊓ cR.range := ⟨hu, ⟨q u, rfl⟩⟩
  rw [hEq] at hu'
  obtain ⟨r, hr, hrq⟩ := Subgroup.mem_map.1 hu'
  have hru : r = q u := hconjinj hrq
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.1 hr
  have hqu : q e = q u := heq.trans hru
  have hmem : e⁻¹ * u ∈ q.ker := by
    show q (e⁻¹ * u) = 1
    rw [map_mul, map_inv, hqu, inv_mul_cancel]
  have hEu : e⁻¹ * u ∈ E := hkerE hmem
  have : u = e * (e⁻¹ * u) := by group
  rw [this]
  exact E.mul_mem he hEu

private theorem c2_preimage (h5 : GGTwE6ThreeNoRankSixInput) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (h9 : ¬ 9 ∣ 2 ^ n + 1)
    {q : twistedE6Group 2 n →* TwE6Delta.RecipeR K n}
    (hq : Function.Surjective q)
    (hqk : q.ker ≤ Subgroup.center (twistedE6Group 2 n))
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hY : IsElemAbelian 3 Y) (hY6 : Nat.card Y = 3 ^ 6) :
    (∀ u₁ u₂ : twistedE6Group 2 n,
        MulAut.conj (q u₁) ∈ Y → MulAut.conj (q u₂) ∈ Y → u₁ * u₂ = u₂ * u₁) ∧
      ∀ u : twistedE6Group 2 n, MulAut.conj (q u) ∈ Y → u ^ 3 = 1 := by
  obtain ⟨E, hE, Y₁, hY₁, hY₁I, hY₁6, hY₁pre⟩ := c2_torus h5 hn hK h3 h9 hq hqk
  obtain ⟨β, hβ⟩ := c2_exists_conj hn hK h3 hY hYI hY6 hY₁ hY₁I hY₁6
  obtain ⟨φ, hφ⟩ := TwE6DD2.exists_lift_sc hn hq hqk β
  have hc : ∀ (b : MulAut (TwE6Delta.RecipeR K n)) (r : TwE6Delta.RecipeR K n),
      MulAut.conj (b r) = b * MulAut.conj r * b⁻¹ := by
    intro b r
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hpre : ∀ u : twistedE6Group 2 n, MulAut.conj (q u) ∈ Y → ∃ e ∈ E, φ e = u := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁eq⟩ := hβ (MulAut.conj (q u)) hu
    set u' : twistedE6Group 2 n := φ.symm u with hu'def
    have hqu : q u = β (q u') := by
      rw [← hφ u', hu'def, MulEquiv.apply_symm_apply]
    have h2 : MulAut.conj (q u) = MulAut.conj β (MulAut.conj (q u')) := by
      rw [hqu, hc β (q u'), MulAut.conj_apply]
    have h1 : MulAut.conj β (MulAut.conj (q u')) = MulAut.conj β y₁ := by
      rw [← h2, hy₁eq]
    have hqu' : MulAut.conj (q u') = y₁ := (MulAut.conj β).injective h1
    refine ⟨u', hY₁pre u' (by rw [hqu']; exact hy₁), ?_⟩
    rw [hu'def, MulEquiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · intro u₁ u₂ h₁ h₂
    obtain ⟨e₁, he₁, rfl⟩ := hpre u₁ h₁
    obtain ⟨e₂, he₂, rfl⟩ := hpre u₂ h₂
    calc φ e₁ * φ e₂ = φ (e₁ * e₂) := (map_mul φ e₁ e₂).symm
      _ = φ (e₂ * e₁) := congrArg φ (hE.comm he₁ he₂)
      _ = φ e₂ * φ e₁ := map_mul φ e₂ e₁
  · intro u hu
    obtain ⟨e, he, rfl⟩ := hpre u hu
    calc (φ e) ^ 3 = φ (e ^ 3) := (map_pow φ e 3).symm
      _ = φ 1 := congrArg φ (hE.2 e he)
      _ = 1 := map_one φ

theorem cover_commute_of_not_nine (h5 : GGTwE6ThreeNoRankSixInput) {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (h9 : ¬ 9 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n)
    (hY : IsElemAbelian 3 Y) (hY6 : Nat.card Y = 3 ^ 6) :
    (∀ l₁ l₂ : L', MulAut.conj (ψ l₁) ∈ Y → MulAut.conj (ψ l₂) ∈ Y → l₁ * l₂ = l₂ * l₁) ∧
      ∀ l : L', MulAut.conj (ψ l) ∈ Y → l ^ 3 = 1 := by
  obtain ⟨q, α, hq, hqk, hαs, hα⟩ := TwE6DD2.exists_sc_quot hn hK hψ hker hperf
  set N : Subgroup L' := TableBU.twoPartOf ψ.ker hker (Nat.card L') with hNdef
  have hNbot : ∀ x : L', (x : L' ⧸ N) = 1 → x = 1 := by
    intro x hx
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 hx
    rw [hNdef, TableBU.mem_twoPartOf] at hxN
    obtain ⟨hxker, hx2⟩ := hxN
    have h1 : orderOf x ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hx2
    have h2 : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hxker
    have hcop : Nat.Coprime (orderOf x) 2 :=
      Nat.Coprime.coprime_dvd_left h2 (Nat.coprime_two_right.2 hodd)
    exact orderOf_eq_one_iff.1 ((hcop.pow_right (Nat.card L')).eq_one_of_dvd h1)
  have hqu : ∀ (u : twistedE6Group 2 n) (l : L'), α u = (l : L' ⧸ N) → q u = ψ l := by
    intro u l h
    rw [← hα, h, QuotientGroup.lift_mk]
  obtain ⟨hcommU, hcubeU⟩ := c2_preimage h5 hn hK h3 h9 hq hqk hYI hY hY6
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ h₁ h₂
    obtain ⟨u₁, hu₁⟩ := hαs (l₁ : L' ⧸ N)
    obtain ⟨u₂, hu₂⟩ := hαs (l₂ : L' ⧸ N)
    have hq₁ : MulAut.conj (q u₁) ∈ Y := by rwa [hqu u₁ l₁ hu₁]
    have hq₂ : MulAut.conj (q u₂) ∈ Y := by rwa [hqu u₂ l₂ hu₂]
    have hu : u₁ * u₂ = u₂ * u₁ := hcommU u₁ u₂ hq₁ hq₂
    have hmk : ((l₁ * l₂ : L') : L' ⧸ N) = ((l₂ * l₁ : L') : L' ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hu₁, ← hu₂,
        ← map_mul α u₁ u₂, ← map_mul α u₂ u₁, hu]
    have hx : (((l₂ * l₁)⁻¹ * (l₁ * l₂) : L') : L' ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, inv_mul_cancel]
    have h1 : l₂ * l₁ = l₁ * l₂ :=
      inv_mul_eq_one.mp (hNbot ((l₂ * l₁)⁻¹ * (l₁ * l₂)) hx)
    exact h1.symm
  · intro l hl
    obtain ⟨u, hu⟩ := hαs (l : L' ⧸ N)
    have hq : MulAut.conj (q u) ∈ Y := by rwa [hqu u l hu]
    have hu3 : u ^ 3 = 1 := hcubeU u hq
    have hmk : ((l ^ 3 : L') : L' ⧸ N) = 1 := by
      rw [QuotientGroup.mk_pow, ← hu, ← map_pow, hu3, map_one]
    exact hNbot (l ^ 3) hmk

end CFSG.StandardType.TwE6R4
