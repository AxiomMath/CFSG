module

public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34

private theorem transfer_eq_pow_index {G : Type*} [Group G] [Finite G] {A : Type*} [CommGroup A]
    {H : Subgroup G} (φ : H →* A) {y : G} (hy : y ∈ H)
    (h : ∀ (g : G) (n : ℕ) (hn : g⁻¹ * y ^ n * g ∈ H),
      φ ⟨g⁻¹ * y ^ n * g, hn⟩ = φ ⟨y, hy⟩ ^ n) :
    φ.transfer y = φ ⟨y, hy⟩ ^ H.index := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers y) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod H y, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => h _ _ _

theorem le_oddOrderClosure_of_fixedPointFree {G : Type*} [Group G] [Finite G]
    {D L : Subgroup G} (hLD : L ≤ D) (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) {f : G}
    (hfD : f ∈ D) (hf : Odd (orderOf f)) (hfL : ∀ l ∈ L, f * l * f⁻¹ ∈ L)
    (hfix : ∀ l ∈ L, f * l = l * f → l = 1) : L ≤ CFSG.GroupTheory.oddOrderClosure D := by
  classical
  let c : L → L := fun x => ⟨x⁻¹ * (f * x * f⁻¹), L.mul_mem (L.inv_mem x.2) (hfL x x.2)⟩
  have hinj : Function.Injective c := by
    intro x y hxy
    have hxy' : (x : G)⁻¹ * (f * x * f⁻¹) = (y : G)⁻¹ * (f * y * f⁻¹) :=
      congrArg Subtype.val hxy
    set l : G := (x : G) * (y : G)⁻¹ with hl
    have hxy'' : (x : G)⁻¹ * (f * x * f⁻¹) = (y : G)⁻¹ * (f * y * f⁻¹) := hxy'
    have hAB : (f * x * f⁻¹) * (f * y * f⁻¹)⁻¹ = l := by
      calc
        (f * x * f⁻¹) * (f * y * f⁻¹)⁻¹
            = (x : G) * ((x : G)⁻¹ * (f * x * f⁻¹) * (f * y * f⁻¹)⁻¹) := by group
        _ = (x : G) * ((y : G)⁻¹ * (f * y * f⁻¹) * (f * y * f⁻¹)⁻¹) := by rw [hxy'']
        _ = l := by rw [hl]; group
    have hconj : f * l * f⁻¹ = l := by
      calc f * l * f⁻¹ = (f * x * f⁻¹) * (f * y * f⁻¹)⁻¹ := by rw [hl]; group
        _ = l := hAB
    have hcomm : f * l = l * f := by
      calc f * l = (f * l * f⁻¹) * f := by group
        _ = l * f := by rw [hconj]
    have hmem : l ∈ L := by
      rw [hl]
      exact L.mul_mem x.2 (L.inv_mem y.2)
    have h1 : l = 1 := hfix _ hmem hcomm
    have hxyl : (x : G) * (y : G)⁻¹ = 1 := by rw [← hl]; exact h1
    apply Subtype.ext
    rw [← mul_inv_eq_one]
    exact h1
  have hsurj : Function.Surjective c := Finite.surjective_of_injective hinj
  intro l hl
  obtain ⟨x, hx⟩ := hsurj ⟨l, hl⟩
  have hx' : ((c x : L) : G) = l := congrArg Subtype.val hx
  rw [← hx']
  have hxD : (x : G) ∈ D := hLD x.2
  have h1 : (x : G)⁻¹ * f * x ∈ D :=
    D.mul_mem (D.mul_mem (D.inv_mem hxD) hfD) hxD
  have h2 : f⁻¹ ∈ D := D.inv_mem hfD
  have hodd1 : Odd (orderOf ((x : G)⁻¹ * f * x)) := by
    have hc : (x : G)⁻¹ * f * x = MulAut.conj (x : G)⁻¹ f := by
      rw [MulAut.conj_apply, inv_inv]
    rw [hc, MulEquiv.orderOf_eq]
    exact hf
  have hodd2 : Odd (orderOf (f⁻¹)) := by rwa [orderOf_inv]
  have hmem1 := CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd h1 hodd1
  have hmem2 := CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd h2 hodd2
  have hcx : ((c x : L) : G) = ((x : G)⁻¹ * f * x) * f⁻¹ := by
    change (x : G)⁻¹ * (f * x * f⁻¹) = ((x : G)⁻¹ * f * x) * f⁻¹
    group
  rw [hcx]
  exact (CFSG.GroupTheory.oddOrderClosure D).mul_mem hmem1 hmem2

private theorem pow_eq_one_of_even_of_sq_eq_one {A : Type*} [Monoid A] {x : A}
    (hx : x * x = 1) {n : ℕ} (hn : Even n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
  rw [pow_mul, pow_two, hx, one_pow]

private theorem pow_eq_self_of_odd_of_sq_eq_one {A : Type*} [Monoid A] {x : A}
    (hx : x * x = 1) {n : ℕ} (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

private theorem map_eq_one_of_odd_order_of_card_two {H : Type*} [Group H] {A : Type*} [Group A]
    [Finite A] {f : H →* A} (hcard : Nat.card A = 2) {x : H} (hx : Odd (orderOf x)) :
    f x = 1 := by
  have hdvd1 : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
  have hdvd2 : orderOf (f x) ∣ 2 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hodd : Odd (orderOf (f x)) := hx.of_dvd_nat hdvd1
  have hle : orderOf (f x) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  obtain ⟨k, hk⟩ := hodd
  have h1 : orderOf (f x) = 1 := by omega
  exact orderOf_eq_one_iff.mp h1

private theorem conj_mul_self_eq_one {H : Type*} [Group H] {g x : H} (hx : x * x = 1) :
    (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
  have h := conj_pow (a := g⁻¹) (b := x) (i := 2)
  simp only [pow_two, hx, mul_one, inv_inv] at h
  rw [inv_mul_cancel] at h
  simpa [pow_two] using h

private theorem conj_ne_one {H : Type*} [Group H] {g x : H} (hx : x ≠ 1) :
    g⁻¹ * x * g ≠ 1 := by
  intro h
  apply hx
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * 1 * g⁻¹ := by rw [h]
    _ = 1 := by group

private def supZpowersUnion {H : Type*} [Group H] (T₁ : Subgroup H) (x : H)
    (hxN : ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁) (hx2T : x * x ∈ T₁) : Subgroup H where
  carrier := {z | z ∈ T₁ ∨ ∃ y ∈ T₁, z = y * x}
  one_mem' := Or.inl T₁.one_mem
  mul_mem' := by
    rintro a b (ha | ⟨ya, hya, rfl⟩) (hb | ⟨yb, hyb, rfl⟩)
    · exact Or.inl (T₁.mul_mem ha hb)
    · exact Or.inr ⟨a * yb, T₁.mul_mem ha hyb, by group⟩
    · exact Or.inr ⟨ya * (x * b * x⁻¹), T₁.mul_mem hya (hxN b hb), by group⟩
    · refine Or.inl ?_
      have h1 : ya * (x * yb * x⁻¹) ∈ T₁ := T₁.mul_mem hya (hxN yb hyb)
      have h2 : (ya * x) * (yb * x) = (ya * (x * yb * x⁻¹)) * (x * x) := by group
      rw [h2]
      exact T₁.mul_mem h1 hx2T
  inv_mem' := by
    rintro a (ha | ⟨ya, hya, rfl⟩)
    · exact Or.inl (T₁.inv_mem ha)
    · refine Or.inr ⟨(x * x)⁻¹ * (x * ya⁻¹ * x⁻¹), ?_, by group⟩
      exact T₁.mul_mem (T₁.inv_mem hx2T) (hxN ya⁻¹ (T₁.inv_mem hya))

private theorem le_supZpowersUnion {H : Type*} [Group H] {T₁ : Subgroup H} {x : H}
    (hxN : ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁) (hx2T : x * x ∈ T₁) :
    T₁ ⊔ Subgroup.zpowers x ≤ supZpowersUnion T₁ x hxN hx2T := by
  refine sup_le (fun z hz => Or.inl hz) (Subgroup.zpowers_le.mpr ?_)
  exact Or.inr ⟨1, T₁.one_mem, (one_mul x).symm⟩

open Subgroup

private theorem core_le {H : Type*} [Group H] [Finite H] {T T₀ T₁ : Subgroup H}
    {t lam a : H} (P : H → Prop) (hP : ∀ g y : H, P (g * y * g⁻¹) ↔ P y)
    (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (htT : t ∈ T) (ht2 : t * t = 1) (hcent : ∀ g : H, g * t = t * g)
    (htT₀ : t ∉ T₀) (hPt : ¬ P t) (hT₀T : T₀ ≤ T)
    (hT₁ : ∀ x, x ∈ T₁ ↔ x ∈ T₀ ∨ ∃ s ∈ T₀, x = t * s)
    (hT₁T : T₁ ≤ T) (hT₁n : ∀ g ∈ T, ∀ x ∈ T₁, g * x * g⁻¹ ∈ T₁)
    (hidx : T₁.relIndex T = 4)
    (hlamT : lam ∈ T) (hlam : lam * lam = t)
    (hroot : ∀ x ∈ T, x * x = t → x * lam⁻¹ ∈ T₁)
    (haT : a ∈ T) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t)
    (hPa : ¬ P a) (hPat : ¬ P (a * t))
    (hinv : ∀ y ∈ T, y * y = 1 → y ≠ 1 → y ≠ t → ¬ P y → ¬ P (y * t) →
      y ∉ T₁ ∧ y * lam⁻¹ ∉ T₁)
    (hPT₀ : ∀ y ∈ T, y * y = 1 → y ≠ 1 → P y → y ∈ T₀)
    (hT₀gen : T₀ ≤ Subgroup.closure {y | y ∈ T₀ ∧ y * y = 1 ∧ P y}) :
    CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup H) ⊓ T ≤ T₀ := by
  classical
  have htT₁ : t ∈ T₁ := (hT₁ t).mpr (Or.inr ⟨1, T₀.one_mem, by rw [mul_one]⟩)
  have hT₀T₁ : T₀ ≤ T₁ := fun x hx => (hT₁ x).mpr (Or.inl hx)
  have hsqT₁ : ∀ x ∈ T₁, x * x ∈ T₀ := by
    intro x hx
    rcases (hT₁ x).mp hx with hxT₀ | ⟨s, hs, rfl⟩
    · exact T₀.mul_mem hxT₀ hxT₀
    · have hcomm : t * s = s * t := (hcent s).symm
      have hcalc : (t * s) * (t * s) = s * s := by
        calc (t * s) * (t * s) = t * (s * t) * s := by group
          _ = t * (t * s) * s := by rw [← hcomm]
          _ = s * s := by rw [← mul_assoc t t, ht2, one_mul]
      rw [hcalc]
      exact T₀.mul_mem hs hs
  have hlamT₁ : lam ∉ T₁ := by
    intro h
    exact htT₀ (hlam ▸ hsqT₁ lam h)
  have hainv := hinv a haT ha2 ha1 hat hPa hPat
  have haT₁ : a ∉ T₁ := hainv.1
  have ha_lam : a * lam⁻¹ ∉ T₁ := hainv.2
  have hlam_a : lam * a⁻¹ ∉ T₁ := by
    intro h
    exact ha_lam (by simpa [mul_inv_rev] using T₁.inv_mem h)
  let Ua : Subgroup H := T₁ ⊔ Subgroup.zpowers lam
  let Ul : Subgroup H := T₁ ⊔ Subgroup.zpowers a
  have hUaT : Ua ≤ T := sup_le hT₁T (Subgroup.zpowers_le.mpr hlamT)
  have hUlT : Ul ≤ T := sup_le hT₁T (Subgroup.zpowers_le.mpr haT)
  have hUa_union : ∀ {z : H}, z ∈ Ua → z ∈ T₁ ∨ ∃ y ∈ T₁, z = y * lam := by
    intro z hz
    exact le_supZpowersUnion (fun y hy => hT₁n lam hlamT y hy)
      (by rw [hlam]; exact htT₁) hz
  have hUl_union : ∀ {z : H}, z ∈ Ul → z ∈ T₁ ∨ ∃ y ∈ T₁, z = y * a := by
    intro z hz
    exact le_supZpowersUnion (fun y hy => hT₁n a haT y hy)
      (by rw [ha2]; exact T₁.one_mem) hz
  have haUa : a ∉ Ua := by
    intro h
    rcases hUa_union h with h' | ⟨y, hy, hya⟩
    · exact haT₁ h'
    · have h1 : a * lam⁻¹ = y := by rw [hya]; group
      exact ha_lam (h1 ▸ hy)
  have hlamUl : lam ∉ Ul := by
    intro h
    rcases hUl_union h with h' | ⟨y, hy, hya⟩
    · exact hlamT₁ h'
    · have h1 : lam * a⁻¹ = y := by rw [hya]; group
      exact hlam_a (h1 ▸ hy)
  have hT₁Ua : T₁ ≤ Ua := le_sup_left
  have hT₁Ul : T₁ ≤ Ul := le_sup_left
  have hUa_dvd : Ua.relIndex T ∣ 4 := by
    have h := Subgroup.relIndex_dvd_of_le_left hT₁Ua (L := T)
    simpa [hidx] using h
  have hUl_dvd : Ul.relIndex T ∣ 4 := by
    have h := Subgroup.relIndex_dvd_of_le_left hT₁Ul (L := T)
    simpa [hidx] using h
  have hUa_index : Ua.relIndex T = 2 := by
    have h4 : Ua.relIndex T ∣ 2 ^ 2 := by simpa using hUa_dvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    interval_cases k
    · have : T ≤ Ua := Subgroup.relIndex_eq_one.mp hk
      exact absurd (this haT) haUa
    · simpa using hk
    · exfalso
      have hmul := Subgroup.relIndex_mul_relIndex (H := T₁) (K := Ua) (L := T) hT₁Ua hUaT
      rw [hidx, hk] at hmul
      have h1 : T₁.relIndex Ua = 1 := by omega
      exact hlamT₁ (Subgroup.relIndex_eq_one.mp h1
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)))
  have hUl_index : Ul.relIndex T = 2 := by
    have h4 : Ul.relIndex T ∣ 2 ^ 2 := by simpa using hUl_dvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    interval_cases k
    · have : T ≤ Ul := Subgroup.relIndex_eq_one.mp hk
      exact absurd (this hlamT) hlamUl
    · simpa using hk
    · exfalso
      have hmul := Subgroup.relIndex_mul_relIndex (H := T₁) (K := Ul) (L := T) hT₁Ul hUlT
      rw [hidx, hk] at hmul
      have h1 : T₁.relIndex Ul = 1 := by omega
      exact haT₁ (Subgroup.relIndex_eq_one.mp h1
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let UaT : Subgroup T := Ua.subgroupOf T
  let UlT : Subgroup T := Ul.subgroupOf T
  haveI hUaTn : UaT.Normal := Subgroup.normal_of_index_eq_two hUa_index
  haveI hUlTn : UlT.Normal := Subgroup.normal_of_index_eq_two hUl_index
  have hQaCard : Nat.card (T ⧸ UaT) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hUa_index
  have hQlCard : Nat.card (T ⧸ UlT) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hUl_index
  haveI : IsCyclic (T ⧸ UaT) := isCyclic_of_prime_card hQaCard
  haveI : IsCyclic (T ⧸ UlT) := isCyclic_of_prime_card hQlCard
  letI : CommGroup (T ⧸ UaT) := IsCyclic.commGroup
  letI : CommGroup (T ⧸ UlT) := IsCyclic.commGroup
  let φa : T →* (T ⧸ UaT) := QuotientGroup.mk' UaT
  let φl : T →* (T ⧸ UlT) := QuotientGroup.mk' UlT
  let Va : H →* (T ⧸ UaT) := φa.transfer
  let Vl : H →* (T ⧸ UlT) := φl.transfer
  have hφa_sq : φa ⟨a, haT⟩ * φa ⟨a, haT⟩ = 1 := by
    have h := pow_card_eq_one' (G := T ⧸ UaT) (x := φa ⟨a, haT⟩)
    rwa [hQaCard, pow_two] at h
  have hφl_sq : φl ⟨lam, hlamT⟩ * φl ⟨lam, hlamT⟩ = 1 := by
    have h := pow_card_eq_one' (G := T ⧸ UlT) (x := φl ⟨lam, hlamT⟩)
    rwa [hQlCard, pow_two] at h
  have hφa_a_ne : φa ⟨a, haT⟩ ≠ 1 := by
    intro h
    apply haUa
    have h1 : (⟨a, haT⟩ : T) ∈ (QuotientGroup.mk' UaT).ker := MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk'] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hφl_lam_ne : φl ⟨lam, hlamT⟩ ≠ 1 := by
    intro h
    apply hlamUl
    have h1 : (⟨lam, hlamT⟩ : T) ∈ (QuotientGroup.mk' UlT).ker := MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk'] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hφa_lam : φa ⟨lam, hlamT⟩ = 1 := by
    have h1 : (⟨lam, hlamT⟩ : T) ∈ UaT :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers lam))
    have h2 : (⟨lam, hlamT⟩ : T) ∈ (QuotientGroup.mk' UaT).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  have hφa_t : φa ⟨t, htT⟩ = 1 := by
    have h1 : (⟨t, htT⟩ : T) ∈ UaT :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left htT₁)
    have h2 : (⟨t, htT⟩ : T) ∈ (QuotientGroup.mk' UaT).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  have hφl_t : φl ⟨t, htT⟩ = 1 := by
    have h1 : (⟨t, htT⟩ : T) ∈ UlT :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left htT₁)
    have h2 : (⟨t, htT⟩ : T) ∈ (QuotientGroup.mk' UlT).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  have hTodd : Odd T.index := Nat.not_even_iff_odd.mp (fun h => hTidx (even_iff_two_dvd.mp h))
  have hVa_a_val : Va a = φa ⟨a, haT⟩ ^ T.index := by
    refine transfer_eq_pow_index φa haT ?_
    intro g n hn
    by_cases hn_even : Even n
    · have han : a ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one ha2 hn_even
      have hz1 : g⁻¹ * a ^ n * g = 1 := by rw [han]; group
      have hsub : (⟨g⁻¹ * a ^ n * g, hn⟩ : T) = 1 := Subtype.ext hz1
      rw [hsub, map_one]
      exact (pow_eq_one_of_even_of_sq_eq_one (A := T ⧸ UaT) hφa_sq hn_even).symm
    · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      have han : a ^ n = a := pow_eq_self_of_odd_of_sq_eq_one ha2 hn_odd
      let z : H := g⁻¹ * a * g
      have hzT : z ∈ T := by
        rw [show z = g⁻¹ * a ^ n * g by rw [han]]
        exact hn
      have hz2 : z * z = 1 := by
        have h := conj_pow (a := g⁻¹) (b := a) (i := 2)
        simp only [pow_two, ha2, mul_one, inv_inv] at h
        rw [inv_mul_cancel] at h
        simpa [z, pow_two] using h
      have hz1 : z ≠ 1 := by
        intro hz
        apply ha1
        calc a = g * z * g⁻¹ := by rw [show z = g⁻¹ * a * g from rfl]; group
          _ = g * 1 * g⁻¹ := by rw [hz]
          _ = 1 := by group
      have hgt : g * t * g⁻¹ = t := by rw [hcent g]; group
      have hzt : z ≠ t := by
        intro hz
        apply hat
        calc a = g * z * g⁻¹ := by rw [show z = g⁻¹ * a * g from rfl]; group
          _ = g * t * g⁻¹ := by rw [hz]
          _ = t := hgt
      have hPz : ¬ P z := by
        intro hzP
        exact hPa ((hP g⁻¹ a).mp (by simpa [z] using hzP))
      have hzt_eq : z * t = g⁻¹ * (a * t) * g := by
        calc z * t = g⁻¹ * a * g * t := rfl
          _ = g⁻¹ * a * (g * t) := by group
          _ = g⁻¹ * a * (t * g) := by rw [hcent g]
          _ = g⁻¹ * (a * t) * g := by group
      have hPzt : ¬ P (z * t) := by
        intro hzP
        apply hPat
        have h' : P (g⁻¹ * (a * t) * (g⁻¹)⁻¹) := by
          rw [inv_inv, ← hzt_eq]
          exact hzP
        exact (hP g⁻¹ (a * t)).mp h'
      have hinvz := hinv z hzT hz2 hz1 hzt hPz hPzt
      have hzT₁ : z ∉ T₁ := hinvz.1
      have hzUa : z ∉ Ua := by
        intro hzUa
        rcases hUa_union hzUa with h' | ⟨y, hy, hzy⟩
        · exact hzT₁ h'
        · have h1 : z * lam⁻¹ = y := by rw [hzy]; group
          exact hinvz.2 (h1 ▸ hy)
      have hmemUa : a⁻¹ * z ∈ Ua :=
        CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUa_index haT hzT haUa hzUa
      have hker : φa ⟨a⁻¹ * z, T.mul_mem (T.inv_mem haT) hzT⟩ = 1 := by
        have h1 : (⟨a⁻¹ * z, T.mul_mem (T.inv_mem haT) hzT⟩ : T) ∈ UaT :=
          Subgroup.mem_subgroupOf.mpr hmemUa
        have h2 : (⟨a⁻¹ * z, T.mul_mem (T.inv_mem haT) hzT⟩ : T) ∈
            (QuotientGroup.mk' UaT).ker := by
          rw [QuotientGroup.ker_mk']
          exact h1
        exact MonoidHom.mem_ker.mp h2
      have hza : φa ⟨z, hzT⟩ = φa ⟨a, haT⟩ := by
        have heq : (⟨a⁻¹ * z, T.mul_mem (T.inv_mem haT) hzT⟩ : T) =
            (⟨a, haT⟩ : T)⁻¹ * ⟨z, hzT⟩ := Subtype.ext rfl
        rw [heq, map_mul, map_inv] at hker
        exact (inv_mul_eq_one.mp hker).symm
      have hsub : (⟨g⁻¹ * a ^ n * g, hn⟩ : T) = ⟨z, hzT⟩ := by
        apply Subtype.ext
        simp [z, han]
      rw [hsub, hza, pow_eq_self_of_odd_of_sq_eq_one hφa_sq hn_odd]
  have hVa_a_ne : Va a ≠ 1 := by
    rw [hVa_a_val, pow_eq_self_of_odd_of_sq_eq_one hφa_sq hTodd]
    exact hφa_a_ne
  have hker_UaT : ∀ (z : H) (hzT : z ∈ T), z ∈ T₁ → φa ⟨z, hzT⟩ = 1 := by
    intro z hzT hzT₁
    have h1 : (⟨z, hzT⟩ : T) ∈ UaT :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hzT₁)
    have h2 : (⟨z, hzT⟩ : T) ∈ (QuotientGroup.mk' UaT).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  have hker_UlT : ∀ (z : H) (hzT : z ∈ T), z ∈ T₁ → φl ⟨z, hzT⟩ = 1 := by
    intro z hzT hzT₁
    have h1 : (⟨z, hzT⟩ : T) ∈ UlT :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hzT₁)
    have h2 : (⟨z, hzT⟩ : T) ∈ (QuotientGroup.mk' UlT).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  have hcentral_t : ∀ (g : H) (n : ℕ), g⁻¹ * t ^ n * g = t ^ n := by
    intro g n
    have h : Commute (g⁻¹) (t ^ n) := (show Commute g t from hcent g).inv_left.pow_right n
    rw [h.eq]
    group
  have hVa_t_val : Va t = φa ⟨t, htT⟩ ^ T.index := by
    refine transfer_eq_pow_index φa htT ?_
    intro g n hn
    have hconj := hcentral_t g n
    have hsub : (⟨g⁻¹ * t ^ n * g, hn⟩ : T) = ⟨t ^ n, T.pow_mem htT n⟩ :=
      Subtype.ext hconj
    rw [hsub]
    by_cases hn_even : Even n
    · have htn : t ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one ht2 hn_even
      have h1 : (⟨t ^ n, T.pow_mem htT n⟩ : T) = 1 := Subtype.ext htn
      rw [h1, map_one, hφa_t, one_pow]
    · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      have htn : t ^ n = t := pow_eq_self_of_odd_of_sq_eq_one ht2 hn_odd
      have h1 : (⟨t ^ n, T.pow_mem htT n⟩ : T) = ⟨t, htT⟩ := Subtype.ext htn
      rw [h1, hφa_t, one_pow]
  have hVa_t : Va t = 1 := by rw [hVa_t_val, hφa_t, one_pow]
  have hVa_x : ∀ x ∈ T₀, x * x = 1 → P x → Va x = 1 := by
    intro x hxT₀ hx2 hxP
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hxT : x ∈ T := hT₀T hxT₀
      have hxT₁ : x ∈ T₁ := hT₀T₁ hxT₀
      have hφx : φa ⟨x, hxT⟩ = 1 := hker_UaT x hxT hxT₁
      have hval : Va x = φa ⟨x, hxT⟩ ^ T.index := by
        refine transfer_eq_pow_index φa hxT ?_
        intro g n hn
        have hφz : φa ⟨g⁻¹ * x ^ n * g, hn⟩ = 1 := by
          by_cases hn_even : Even n
          · have hxn : x ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one hx2 hn_even
            have hsub : (⟨g⁻¹ * x ^ n * g, hn⟩ : T) = 1 := by
              apply Subtype.ext
              show g⁻¹ * x ^ n * g = 1
              rw [hxn]
              simp
            rw [hsub, map_one]
          · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
            have hxn : x ^ n = x := pow_eq_self_of_odd_of_sq_eq_one hx2 hn_odd
            let z : H := g⁻¹ * x * g
            have hzT : z ∈ T := by
              rw [show z = g⁻¹ * x ^ n * g by rw [hxn]]
              exact hn
            have hz2 : z * z = 1 := conj_mul_self_eq_one hx2
            have hz1 : z ≠ 1 := conj_ne_one hx1
            have hPz : P z := by
              have h' := (hP g⁻¹ x).mpr hxP
              simpa [z] using h'
            have hzT₁ : z ∈ T₁ := hT₀T₁ (hPT₀ z hzT hz2 hz1 hPz)
            have hφz' : φa ⟨z, hzT⟩ = 1 := hker_UaT z hzT hzT₁
            have hsub : (⟨g⁻¹ * x ^ n * g, hn⟩ : T) = ⟨z, hzT⟩ :=
              Subtype.ext (by simp [z, hxn])
            rw [hsub, hφz']
        rw [hφz, hφx, one_pow]
      rw [hval, hφx, one_pow]
  have hVa_T₀ : T₀ ≤ Va.ker := by
    have hgen_le : Subgroup.closure {y : H | y ∈ T₀ ∧ y * y = 1 ∧ P y} ≤ Va.ker := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyT₀, hy2, hyP⟩
      exact MonoidHom.mem_ker.mpr (hVa_x y hyT₀ hy2 hyP)
    exact hT₀gen.trans hgen_le
  have hVa_T₁ : T₁ ≤ Va.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    rcases (hT₁ x).mp hx with hxT₀ | ⟨s, hs, rfl⟩
    · exact MonoidHom.mem_ker.mp (hVa_T₀ hxT₀)
    · rw [map_mul, hVa_t, MonoidHom.mem_ker.mp (hVa_T₀ hs), mul_one]
  have hVa_lam_val : Va lam = φa ⟨lam, hlamT⟩ ^ T.index := by
    refine transfer_eq_pow_index φa hlamT ?_
    intro g n hn
    by_cases hn_even : Even n
    · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn_even
      have han : lam ^ (2 * k) = t ^ k := by
        rw [pow_mul, show lam ^ 2 = t by rw [pow_two, hlam]]
      have hconj : g⁻¹ * lam ^ (2 * k) * g = t ^ k := by
        rw [han]
        exact hcentral_t g k
      have hsub : (⟨g⁻¹ * lam ^ (2 * k) * g, hn⟩ : T) = ⟨t ^ k, T.pow_mem htT k⟩ :=
        Subtype.ext hconj
      rw [hsub, hker_UaT _ _ (T₁.pow_mem htT₁ k), hφa_lam, one_pow]
    · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      obtain ⟨k, rfl⟩ := hn_odd
      have han : lam ^ (2 * k + 1) = t ^ k * lam := by
        rw [pow_succ, pow_mul, show lam ^ 2 = t by rw [pow_two, hlam]]
      let z : H := g⁻¹ * lam ^ (2 * k + 1) * g
      have hzT : z ∈ T := hn
      have hz2 : z * z = t := by
        have hsq : lam ^ (2 * k + 1) * lam ^ (2 * k + 1) = t := by
          rw [← pow_add]
          have hexp : 2 * k + 1 + (2 * k + 1) = 2 * (2 * k + 1) := by ring
          rw [hexp, pow_mul]
          rw [show lam ^ 2 = t by rw [pow_two, hlam]]
          exact pow_eq_self_of_odd_of_sq_eq_one ht2 (odd_two_mul_add_one k)
        have h := conj_pow (a := g⁻¹) (b := lam ^ (2 * k + 1)) (i := 2)
        simp only [pow_two, inv_inv] at h
        rw [hsq] at h
        have hgt : g⁻¹ * t * g = t := by
          have hc : Commute (g⁻¹) t := (show Commute g t from hcent g).inv_left
          rw [hc.eq]
          group
        rw [hgt] at h
        exact h
      have hz_lam : z * lam⁻¹ ∈ T₁ := hroot z hzT hz2
      have hmemT : z * lam⁻¹ ∈ T := hT₁T hz_lam
      have hker : φa ⟨z * lam⁻¹, hmemT⟩ = 1 := hker_UaT _ hmemT hz_lam
      have hφz : φa ⟨z, hzT⟩ = 1 := by
        have heq : (⟨z, hzT⟩ : T) = ⟨z * lam⁻¹, hmemT⟩ * ⟨lam, hlamT⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_mul]; group)
        rw [heq, map_mul, hker, one_mul]
        exact hφa_lam
      have hsub : (⟨g⁻¹ * lam ^ (2 * k + 1) * g, hn⟩ : T) = ⟨z, hzT⟩ :=
        Subtype.ext rfl
      rw [hsub, hφz, hφa_lam, one_pow]
  have hVa_lam : Va lam = 1 := by rw [hVa_lam_val, hφa_lam, one_pow]
  have hVl_t_val : Vl t = φl ⟨t, htT⟩ ^ T.index := by
    refine transfer_eq_pow_index φl htT ?_
    intro g n hn
    have hconj := hcentral_t g n
    have hsub : (⟨g⁻¹ * t ^ n * g, hn⟩ : T) = ⟨t ^ n, T.pow_mem htT n⟩ :=
      Subtype.ext hconj
    rw [hsub]
    by_cases hn_even : Even n
    · have htn : t ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one ht2 hn_even
      have h1 : (⟨t ^ n, T.pow_mem htT n⟩ : T) = 1 := Subtype.ext htn
      rw [h1, map_one, hφl_t, one_pow]
    · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      have htn : t ^ n = t := pow_eq_self_of_odd_of_sq_eq_one ht2 hn_odd
      have h1 : (⟨t ^ n, T.pow_mem htT n⟩ : T) = ⟨t, htT⟩ := Subtype.ext htn
      rw [h1, hφl_t, one_pow]
  have hVl_t : Vl t = 1 := by rw [hVl_t_val, hφl_t, one_pow]
  have hVl_x : ∀ x ∈ T₀, x * x = 1 → P x → Vl x = 1 := by
    intro x hxT₀ hx2 hxP
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hxT : x ∈ T := hT₀T hxT₀
      have hxT₁ : x ∈ T₁ := hT₀T₁ hxT₀
      have hφx : φl ⟨x, hxT⟩ = 1 := hker_UlT x hxT hxT₁
      have hval : Vl x = φl ⟨x, hxT⟩ ^ T.index := by
        refine transfer_eq_pow_index φl hxT ?_
        intro g n hn
        have hφz : φl ⟨g⁻¹ * x ^ n * g, hn⟩ = 1 := by
          by_cases hn_even : Even n
          · have hxn : x ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one hx2 hn_even
            have hsub : (⟨g⁻¹ * x ^ n * g, hn⟩ : T) = 1 := by
              apply Subtype.ext
              show g⁻¹ * x ^ n * g = 1
              rw [hxn]
              simp
            rw [hsub, map_one]
          · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
            have hxn : x ^ n = x := pow_eq_self_of_odd_of_sq_eq_one hx2 hn_odd
            let z : H := g⁻¹ * x * g
            have hzT : z ∈ T := by
              rw [show z = g⁻¹ * x ^ n * g by rw [hxn]]
              exact hn
            have hz2 : z * z = 1 := conj_mul_self_eq_one hx2
            have hz1 : z ≠ 1 := conj_ne_one hx1
            have hPz : P z := by
              have h' := (hP g⁻¹ x).mpr hxP
              simpa [z] using h'
            have hzT₁ : z ∈ T₁ := hT₀T₁ (hPT₀ z hzT hz2 hz1 hPz)
            have hφz' : φl ⟨z, hzT⟩ = 1 := hker_UlT z hzT hzT₁
            have hsub : (⟨g⁻¹ * x ^ n * g, hn⟩ : T) = ⟨z, hzT⟩ := by
              apply Subtype.ext
              show g⁻¹ * x ^ n * g = z
              rw [hxn]
            rw [hsub, hφz']
        rw [hφz, hφx, one_pow]
      rw [hval, hφx, one_pow]
  have hVl_T₀ : T₀ ≤ Vl.ker := by
    have hgen_le : Subgroup.closure {y : H | y ∈ T₀ ∧ y * y = 1 ∧ P y} ≤ Vl.ker := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyT₀, hy2, hyP⟩
      exact MonoidHom.mem_ker.mpr (hVl_x y hyT₀ hy2 hyP)
    exact hT₀gen.trans hgen_le
  have hVl_T₁ : T₁ ≤ Vl.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    rcases (hT₁ x).mp hx with hxT₀ | ⟨s, hs, rfl⟩
    · exact MonoidHom.mem_ker.mp (hVl_T₀ hxT₀)
    · rw [map_mul, hVl_t, MonoidHom.mem_ker.mp (hVl_T₀ hs), mul_one]
  have hVl_lam_val : Vl lam = φl ⟨lam, hlamT⟩ ^ T.index := by
    refine transfer_eq_pow_index φl hlamT ?_
    intro g n hn
    by_cases hn_even : Even n
    · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn_even
      have han : lam ^ (2 * k) = t ^ k := by
        rw [pow_mul, show lam ^ 2 = t by rw [pow_two, hlam]]
      have hconj : g⁻¹ * lam ^ (2 * k) * g = t ^ k := by
        rw [han]
        exact hcentral_t g k
      have hsub : (⟨g⁻¹ * lam ^ (2 * k) * g, hn⟩ : T) = ⟨t ^ k, T.pow_mem htT k⟩ :=
        Subtype.ext hconj
      rw [hsub]
      have hφz : φl ⟨t ^ k, T.pow_mem htT k⟩ = 1 := hker_UlT _ _ (T₁.pow_mem htT₁ k)
      rw [hφz, pow_mul, pow_two, hφl_sq, one_pow]
    · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      obtain ⟨k, rfl⟩ := hn_odd
      have han : lam ^ (2 * k + 1) = t ^ k * lam := by
        rw [pow_succ, pow_mul, show lam ^ 2 = t by rw [pow_two, hlam]]
      let z : H := g⁻¹ * lam ^ (2 * k + 1) * g
      have hzT : z ∈ T := hn
      have hz2 : z * z = t := by
        have hsq : lam ^ (2 * k + 1) * lam ^ (2 * k + 1) = t := by
          rw [← pow_add]
          have hexp : 2 * k + 1 + (2 * k + 1) = 2 * (2 * k + 1) := by ring
          rw [hexp, pow_mul]
          rw [show lam ^ 2 = t by rw [pow_two, hlam]]
          exact pow_eq_self_of_odd_of_sq_eq_one ht2 (odd_two_mul_add_one k)
        have h := conj_pow (a := g⁻¹) (b := lam ^ (2 * k + 1)) (i := 2)
        simp only [pow_two, inv_inv] at h
        rw [hsq] at h
        have hgt : g⁻¹ * t * g = t := by
          have hc : Commute (g⁻¹) t := (show Commute g t from hcent g).inv_left
          rw [hc.eq]
          group
        rw [hgt] at h
        exact h
      have hz_lam : z * lam⁻¹ ∈ T₁ := hroot z hzT hz2
      have hmemT : z * lam⁻¹ ∈ T := hT₁T hz_lam
      have hker : φl ⟨z * lam⁻¹, hmemT⟩ = 1 := hker_UlT _ hmemT hz_lam
      have hφz : φl ⟨z, hzT⟩ = φl ⟨lam, hlamT⟩ := by
        have heq : (⟨z, hzT⟩ : T) = ⟨z * lam⁻¹, hmemT⟩ * ⟨lam, hlamT⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_mul]; group)
        rw [heq, map_mul, hker, one_mul]
      have hsub : (⟨g⁻¹ * lam ^ (2 * k + 1) * g, hn⟩ : T) = ⟨z, hzT⟩ :=
        Subtype.ext rfl
      rw [hsub, hφz, pow_eq_self_of_odd_of_sq_eq_one hφl_sq (odd_two_mul_add_one k)]
  have hVl_lam_ne : Vl lam ≠ 1 := by
    rw [hVl_lam_val, pow_eq_self_of_odd_of_sq_eq_one hφl_sq hTodd]
    exact hφl_lam_ne
  let B : Subgroup H := Va.ker ⊓ Vl.ker
  let Φ : H →* (T ⧸ UaT) × (T ⧸ UlT) := Va.prod Vl
  have hT₁B : T₁ ≤ B := fun x hx => ⟨hVa_T₁ hx, hVl_T₁ hx⟩
  have hUa_le_kernel : Ua ≤ Va.ker := by
    intro z hz
    rcases hUa_union hz with hzT₁ | ⟨yy, hyy, hzy⟩
    · exact hVa_T₁ hzT₁
    · rw [hzy, MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp (hVa_T₁ hyy), hVa_lam,
        mul_one]
  have hVa_kernel : ∀ x ∈ T, Va x = 1 → x ∈ Ua := by
    intro x hxT hx
    by_contra hxUa
    have hmem : a⁻¹ * x ∈ Ua :=
      CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUa_index haT hxT haUa hxUa
    have hker : Va (a⁻¹ * x) = 1 := MonoidHom.mem_ker.mp (hUa_le_kernel hmem)
    have hxa : Va x = Va a := by
      calc Va x = Va (a * (a⁻¹ * x)) := by rw [mul_inv_cancel_left]
        _ = Va a * Va (a⁻¹ * x) := map_mul Va a (a⁻¹ * x)
        _ = Va a := by rw [hker, mul_one]
    exact hVa_a_ne (by rw [← hxa]; exact hx)
  have hB_T : B ⊓ T = T₁ := by
    refine le_antisymm ?_ fun x hx => ⟨hT₁B hx, hT₁T hx⟩
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxT : x ∈ T := hx.2
    have hxVa : Va x = 1 := MonoidHom.mem_ker.mp hx.1.1
    have hxUa : x ∈ Ua := hVa_kernel x hxT hxVa
    by_contra hxT₁
    rcases hUa_union hxUa with h | ⟨yy, hyy, hxy⟩
    · exact hxT₁ h
    · have hlamB : lam ∈ B := by
        have hyB : yy⁻¹ ∈ B := B.inv_mem (hT₁B hyy)
        have h1 : lam = yy⁻¹ * x := by rw [hxy]; group
        rw [h1]
        exact B.mul_mem hyB hx.1
      have hlamVl : lam ∈ Vl.ker := hlamB.2
      exact hVl_lam_ne (MonoidHom.mem_ker.mp hlamVl)
  have hBker : B = Φ.ker := by
    ext x
    simp [B, Φ, MonoidHom.mem_ker, Subgroup.mem_inf, Prod.ext_iff]
  have hkerT : (Φ.comp T.subtype).ker = B.subgroupOf T := by
    ext x
    change Φ (T.subtype x) = 1 ↔ x ∈ B.subgroupOf T
    rw [Subgroup.mem_subgroupOf, hBker, MonoidHom.mem_ker]
    rfl
  have hcardRangeT : Nat.card ((Φ.comp T.subtype).range) = 4 := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange (Φ.comp T.subtype)).toEquiv
    rw [hkerT] at h
    rw [← h, ← Subgroup.index_eq_card]
    change B.relIndex T = 4
    rw [← Subgroup.inf_relIndex_right (H := B) (K := T), hB_T, hidx]
  have hRange_le : (Φ.comp T.subtype).range ≤ Φ.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨(x : H), rfl⟩
  have hcardTarget : Nat.card ((T ⧸ UaT) × (T ⧸ UlT)) = 4 := by
    rw [Nat.card_prod, hQaCard, hQlCard]
  have hRange_card : Nat.card Φ.range = 4 := by
    have h1 : Nat.card ((Φ.comp T.subtype).range) ≤ Nat.card Φ.range :=
      Subgroup.card_le_of_le hRange_le
    have h2 : Nat.card Φ.range ≤ Nat.card ((T ⧸ UaT) × (T ⧸ UlT)) :=
      Subgroup.card_le_card_group Φ.range
    omega
  have hRange_top : Φ.range = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hcardTarget]
    omega
  have hBidx : B.index = 4 := by
    rw [hBker]
    calc Φ.ker.index = Nat.card (H ⧸ Φ.ker) := Subgroup.index_eq_card _
      _ = Nat.card Φ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
      _ = 4 := by rw [hRange_top, Subgroup.card_top, hcardTarget]
  have hT₁B_index : (T₁.subgroupOf B).index = T.index := by
    have h1 : T₁.relIndex B * B.index = T₁.index := Subgroup.relIndex_mul_index hT₁B
    have h2 : T₁.relIndex T * T.index = T₁.index := Subgroup.relIndex_mul_index hT₁T
    rw [hBidx] at h1
    rw [hidx] at h2
    change T₁.relIndex B = T.index
    omega
  have hT₀T₁_rel : T₀.relIndex T₁ = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨t, htT₁, htT₀, ?_⟩
    intro b hb
    rcases (hT₁ b).mp hb with hbT₀ | ⟨s, hs, rfl⟩
    · exact Or.inr hbT₀
    · left
      have hst : t * s = s * t := (hcent s).symm
      have hcalc : (t * s) * t = s := by
        calc (t * s) * t = t * (s * t) := by group
          _ = t * (t * s) := by rw [← hst]
          _ = s := by rw [← mul_assoc, ht2, one_mul]
      rw [hcalc]
      exact hs
  let Bg := ↥B
  let T₁B : Subgroup Bg := T₁.subgroupOf B
  let T₀B : Subgroup T₁B := (T₀.subgroupOf B).subgroupOf T₁B
  have hT₀B_index : T₀B.index = 2 := by
    change ((T₀.subgroupOf B).subgroupOf T₁B).index = 2
    rw [show ((T₀.subgroupOf B).subgroupOf T₁B).index =
        (T₀.subgroupOf B).relIndex T₁B from rfl]
    rw [Subgroup.relIndex_subgroupOf (H := T₀) (K := T₁) (L := B) hT₁B]
    exact hT₀T₁_rel
  haveI hT₀Bn : T₀B.Normal := Subgroup.normal_of_index_eq_two hT₀B_index
  have hQbCard : Nat.card (T₁B ⧸ T₀B) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hT₀B_index
  haveI : IsCyclic (T₁B ⧸ T₀B) := isCyclic_of_prime_card hQbCard
  letI : CommGroup (T₁B ⧸ T₀B) := IsCyclic.commGroup
  let φb : T₁B →* (T₁B ⧸ T₀B) := QuotientGroup.mk' T₀B
  let W : Bg →* (T₁B ⧸ T₀B) := φb.transfer
  have hT₁B_odd : Odd T₁B.index := by
    rw [show T₁B.index = T.index from hT₁B_index]
    exact hTodd
  have hφb_of_T₀ : ∀ (z : Bg) (hz : z ∈ T₁B), z ∈ T₀.subgroupOf B → φb ⟨z, hz⟩ = 1 := by
    intro z hz hzT₀
    have h1 : (⟨z, hz⟩ : T₁B) ∈ T₀B := Subgroup.mem_subgroupOf.mpr hzT₀
    have h2 : (⟨z, hz⟩ : T₁B) ∈ (QuotientGroup.mk' T₀B).ker := by
      rw [QuotientGroup.ker_mk']
      exact h1
    exact MonoidHom.mem_ker.mp h2
  let y : Bg := ⟨t, hT₁B htT₁⟩
  have hy : y ∈ T₁B := by
    rw [Subgroup.mem_subgroupOf]
    exact htT₁
  have hWt_val : W y = φb ⟨y, hy⟩ ^ T₁B.index := by
    refine transfer_eq_pow_index φb (y := y) hy ?_
    intro g n hn
    let ytn : Bg := ⟨t ^ n, hT₁B (T₁.pow_mem htT₁ n)⟩
    have hytn : ytn ∈ T₁B := Subgroup.mem_subgroupOf.mpr (T₁.pow_mem htT₁ n)
    have hpow : (⟨y, hy⟩ : T₁B) ^ n = ⟨ytn, hytn⟩ :=
      Subtype.ext (Subtype.ext (by rfl))
    have hconj : (⟨g⁻¹ * y ^ n * g, hn⟩ : T₁B) = ⟨ytn, hytn⟩ :=
      Subtype.ext (Subtype.ext (by
        change ((g : Bg) : H)⁻¹ * ((y : Bg) : H) ^ n * ((g : Bg) : H) = t ^ n
        rw [show ((y : Bg) : H) = t from rfl]
        exact hcentral_t (g : Bg) n))
    rw [hconj, ← hpow, map_pow]
  have hφb_t_ne : φb ⟨y, hy⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨y, hy⟩ : T₁B) ∈ (QuotientGroup.mk' T₀B).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk'] at h2
    have h3 : (y : Bg) ∈ T₀.subgroupOf B := Subgroup.mem_subgroupOf.mp h2
    have h4 : (y : H) ∈ T₀ := Subgroup.mem_subgroupOf.mp h3
    exact htT₀ (by simpa [y] using h4)
  have hφb_sq : φb ⟨y, hy⟩ * φb ⟨y, hy⟩ = 1 := by
    have h := pow_card_eq_one' (G := T₁B ⧸ T₀B) (x := φb ⟨y, hy⟩)
    rwa [hQbCard, pow_two] at h
  have hWt_ne : W y ≠ 1 := by
    rw [hWt_val, pow_eq_self_of_odd_of_sq_eq_one hφb_sq hT₁B_odd]
    exact hφb_t_ne
  have hWx : ∀ x (hxT₀ : x ∈ T₀), x * x = 1 → P x →
      W ⟨x, hT₁B (hT₀T₁ hxT₀)⟩ = 1 := by
    intro x hxT₀ hx2 hxP
    let y : Bg := ⟨x, hT₁B (hT₀T₁ hxT₀)⟩
    have hy : y ∈ T₁B := by
      rw [Subgroup.mem_subgroupOf]
      exact hT₀T₁ hxT₀
    have hφb_y : φb ⟨y, hy⟩ = 1 :=
      hφb_of_T₀ y hy (Subgroup.mem_subgroupOf.mpr (by simpa [y] using hxT₀))
    have hval : W y = φb ⟨y, hy⟩ ^ T₁B.index := by
      refine transfer_eq_pow_index φb (y := y) hy ?_
      intro g n hn
      have hφz : φb ⟨g⁻¹ * y ^ n * g, hn⟩ = 1 := by
        let z : Bg := g⁻¹ * y ^ n * g
        have hzT₁B : z ∈ T₁B := hn
        have hzT : (z : H) ∈ T := hT₁T (Subgroup.mem_subgroupOf.mp hzT₁B)
        by_cases hn_even : Even n
        · have hxn : x ^ n = 1 := pow_eq_one_of_even_of_sq_eq_one hx2 hn_even
          have hz1 : (z : H) = 1 := by
            change ((g : Bg) : H)⁻¹ * ((y : Bg) : H) ^ n * ((g : Bg) : H) = 1
            rw [show ((y : Bg) : H) = x from rfl, hxn]
            group
          change φb ⟨z, hzT₁B⟩ = 1
          exact hφb_of_T₀ z hzT₁B
            (Subgroup.mem_subgroupOf.mpr (by rw [hz1]; exact T₀.one_mem))
        · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
          by_cases hx1 : x = 1
          · have hxn : x ^ n = 1 := by rw [hx1, one_pow]
            have hz1 : (z : H) = 1 := by
              change ((g : Bg) : H)⁻¹ * ((y : Bg) : H) ^ n * ((g : Bg) : H) = 1
              rw [show ((y : Bg) : H) = x from rfl, hxn]
              group
            change φb ⟨z, hzT₁B⟩ = 1
            exact hφb_of_T₀ z hzT₁B
              (Subgroup.mem_subgroupOf.mpr (by rw [hz1]; exact T₀.one_mem))
          · have hxn : x ^ n = x := pow_eq_self_of_odd_of_sq_eq_one hx2 hn_odd
            have hz1 : (z : H) = ((g : Bg) : H)⁻¹ * x * ((g : Bg) : H) := by
              change ((g : Bg) : H)⁻¹ * ((y : Bg) : H) ^ n * ((g : Bg) : H) =
                ((g : Bg) : H)⁻¹ * x * ((g : Bg) : H)
              rw [show ((y : Bg) : H) = x from rfl, hxn]
            have hz2 : (z : H) * (z : H) = 1 := by
              rw [hz1]
              exact conj_mul_self_eq_one hx2
            have hz_ne1 : (z : H) ≠ 1 := by
              rw [hz1]
              exact conj_ne_one hx1
            have hPz : P (z : H) := by
              rw [hz1]
              have h' := (hP ((g : Bg) : H)⁻¹ x).mpr hxP
              simpa using h'
            have hzT₀ : (z : H) ∈ T₀ := hPT₀ (z : H) hzT hz2 hz_ne1 hPz
            change φb ⟨z, hzT₁B⟩ = 1
            exact hφb_of_T₀ z hzT₁B (Subgroup.mem_subgroupOf.mpr hzT₀)
      rw [hφz, hφb_y, one_pow]
    rw [hval, hφb_y, one_pow]
  let A' : Subgroup Bg := W.ker
  let A'H : Subgroup H := A'.map B.subtype
  have hT₀_A : T₀ ≤ A'H := by
    have hgenA : Subgroup.closure {y : H | y ∈ T₀ ∧ y * y = 1 ∧ P y} ≤ A'H := by
      rw [Subgroup.closure_le]
      rintro z ⟨hzT₀, hz2, hzP⟩
      refine Subgroup.mem_map.mpr ⟨⟨z, hT₁B (hT₀T₁ hzT₀)⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr (hWx z hzT₀ hz2 hzP)
    exact hT₀gen.trans hgenA
  have htA' : t ∉ A'H := by
    intro htA
    obtain ⟨z, hzA, hzt⟩ := Subgroup.mem_map.mp htA
    have hzy : z = y := Subtype.ext hzt
    rw [hzy] at hzA
    exact hWt_ne (MonoidHom.mem_ker.mp hzA)
  have hA_T : A'H ⊓ T₁ = T₀ := by
    set K : Subgroup H := A'H ⊓ T₁ with hKdef
    have hT₀K : T₀ ≤ K := fun z hz => ⟨hT₀_A hz, hT₀T₁ hz⟩
    have hKle : K ≤ T₁ := inf_le_right
    have hKne : K ≠ T₁ := by
      intro h
      have htK : t ∈ K := by rw [h]; exact htT₁
      exact htA' htK.1
    have hmul : T₀.relIndex K * K.relIndex T₁ = 2 := by
      rw [Subgroup.relIndex_mul_relIndex (H := T₀) (K := K) (L := T₁) hT₀K hKle,
        hT₀T₁_rel]
    have hKrelne : K.relIndex T₁ ≠ 1 := by
      intro h1
      have hle : T₁ ≤ K := Subgroup.relIndex_eq_one.mp h1
      exact hKne (le_antisymm hKle hle)
    have hKrel : K.relIndex T₁ = 2 := by
      have hdvd : K.relIndex T₁ ∣ 2 := by
        rw [← hmul]
        exact dvd_mul_left _ _
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd h1 hKrelne
      · exact h2
    have hT₀Krel : T₀.relIndex K = 1 := by
      have hmul' : T₀.relIndex K * 2 = 2 := by simpa [hKrel] using hmul
      have hdvd : T₀.relIndex K ∣ 2 := by
        rw [← hmul']
        exact dvd_mul_right _ _
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hmul'
        norm_num at hmul'
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hT₀Krel) hT₀K
  have hO2_le : CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup H) ≤ A'H := by
    rw [CFSG.GroupTheory.oddOrderClosure_le_iff]
    intro g hg
    have hgodd : Odd (orderOf g) := hg.2
    have hVag : Va g = 1 := map_eq_one_of_odd_order_of_card_two hQaCard hgodd
    have hVlg : Vl g = 1 := map_eq_one_of_odd_order_of_card_two hQlCard hgodd
    have hgB : g ∈ B := ⟨MonoidHom.mem_ker.mpr hVag, MonoidHom.mem_ker.mpr hVlg⟩
    let g' : Bg := ⟨g, hgB⟩
    have hg'odd : Odd (orderOf g') := by
      rw [← Subgroup.orderOf_coe g']
      change Odd (orderOf g)
      exact hgodd
    have hWg : W g' = 1 := map_eq_one_of_odd_order_of_card_two hQbCard hg'odd
    exact Subgroup.mem_map.mpr ⟨g', MonoidHom.mem_ker.mpr hWg, rfl⟩
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hxA : x ∈ A'H := hO2_le hx.1
  have hxT : x ∈ T := hx.2
  have hxB : x ∈ B := Subgroup.map_subtype_le A' hxA
  have hxT₁ : x ∈ T₁ := by
    rw [← hB_T]
    exact ⟨hxB, hxT⟩
  rw [← hA_T]
  exact ⟨hxA, hxT₁⟩

theorem oddOrderClosure_inf_le {G : Type*} [Group G] [Finite G] {D T T₀ T₁ : Subgroup G}
    {t lam a : G} (P : G → Prop) (hP : ∀ g y : G, P (g * y * g⁻¹) ↔ P y)
    (hTD : T ≤ D) (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.relIndex D)
    (htD : ∀ g ∈ D, g * t = t * g) (htT : t ∈ T) (ht2 : t * t = 1) (htT₀ : t ∉ T₀)
    (hPt : ¬ P t) (hT₀T : T₀ ≤ T)
    (hT₁ : ∀ x, x ∈ T₁ ↔ x ∈ T₀ ∨ ∃ s ∈ T₀, x = t * s)
    (hT₁T : T₁ ≤ T) (hT₁n : ∀ g ∈ T, ∀ x ∈ T₁, g * x * g⁻¹ ∈ T₁) (hidx : T₁.relIndex T = 4)
    (hlamT : lam ∈ T) (hlam : lam * lam = t)
    (hroot : ∀ x ∈ T, x * x = t → x * lam⁻¹ ∈ T₁)
    (haT : a ∈ T) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) (hPa : ¬ P a)
    (hPat : ¬ P (a * t))
    (hinv : ∀ y ∈ T, y * y = 1 → y ≠ 1 → y ≠ t → ¬ P y → ¬ P (y * t) →
      y ∉ T₁ ∧ y * lam⁻¹ ∉ T₁)
    (hPT₀ : ∀ y ∈ T, y * y = 1 → y ≠ 1 → P y → y ∈ T₀)
    (hT₀gen : T₀ ≤ Subgroup.closure {y | y ∈ T₀ ∧ y * y = 1 ∧ P y}) :
    CFSG.GroupTheory.oddOrderClosure D ⊓ T ≤ T₀ := by
  classical
  let Dg := ↥D
  let T' : Subgroup Dg := T.subgroupOf D
  let T₀' : Subgroup Dg := T₀.subgroupOf D
  let T₁' : Subgroup Dg := T₁.subgroupOf D
  let t' : Dg := ⟨t, hTD htT⟩
  let lam' : Dg := ⟨lam, hTD hlamT⟩
  let a' : Dg := ⟨a, hTD haT⟩
  let P' : Dg → Prop := fun x => P (x : G)
  have hP' : ∀ g y : Dg, P' (g * y * g⁻¹) ↔ P' y := by
    intro g y
    exact hP (g : G) (y : G)
  have hT' : IsPGroup 2 T' := by
    change IsPGroup 2 (T.subgroupOf D)
    exact hT.comap_subtype (K := D)
  have hTidx' : ¬ 2 ∣ T'.index := by
    simpa [T', Subgroup.relIndex] using hTidx
  have htT' : t' ∈ T' := Subgroup.mem_subgroupOf.mpr htT
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  have hcent' : ∀ g : Dg, g * t' = t' * g := by
    intro g
    apply Subtype.ext
    exact htD (g : G) g.2
  have htT₀' : t' ∉ T₀' := fun h => htT₀ (Subgroup.mem_subgroupOf.mp h)
  have hPt' : ¬ P' t' := hPt
  have hT₀T' : T₀' ≤ T' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hT₀T (Subgroup.mem_subgroupOf.mp hx))
  have hT₁' : ∀ x : Dg, x ∈ T₁' ↔ x ∈ T₀' ∨ ∃ s ∈ T₀', x = t' * s := by
    intro x
    constructor
    · intro hx
      rcases (hT₁ (x : G)).mp (Subgroup.mem_subgroupOf.mp hx) with hxT₀ | ⟨s, hs, hxs⟩
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr hxT₀)
      · refine Or.inr ⟨⟨s, hTD (hT₀T hs)⟩, Subgroup.mem_subgroupOf.mpr hs, ?_⟩
        apply Subtype.ext
        exact hxs
    · rintro (hxT₀ | ⟨s, hs, hxs⟩)
      · exact Subgroup.mem_subgroupOf.mpr
          ((hT₁ (x : G)).mpr (Or.inl (Subgroup.mem_subgroupOf.mp hxT₀)))
      · refine Subgroup.mem_subgroupOf.mpr
          ((hT₁ (x : G)).mpr (Or.inr ⟨(s : G), Subgroup.mem_subgroupOf.mp hs, ?_⟩))
        exact congrArg Subtype.val hxs
  have hT₁T' : T₁' ≤ T' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hT₁T (Subgroup.mem_subgroupOf.mp hx))
  have hT₁n' : ∀ g ∈ T', ∀ x ∈ T₁', g * x * g⁻¹ ∈ T₁' := by
    intro g hg x hx
    have hgG : (g : G) ∈ T := Subgroup.mem_subgroupOf.mp hg
    have hxG : (x : G) ∈ T₁ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (by
      show (g : G) * (x : G) * (g : G)⁻¹ ∈ T₁
      exact hT₁n (g : G) hgG (x : G) hxG)
  have hidx' : T₁'.relIndex T' = 4 := by
    have h := Subgroup.relIndex_subgroupOf (H := T₁) (K := T) (L := D) hTD
    simpa [T', T₁', hidx] using h
  have hlamT' : lam' ∈ T' := Subgroup.mem_subgroupOf.mpr hlamT
  have hlam' : lam' * lam' = t' := Subtype.ext hlam
  have hroot' : ∀ x ∈ T', x * x = t' → x * lam'⁻¹ ∈ T₁' := by
    intro x hx hx2
    have hxG : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hx2G : (x : G) * (x : G) = t := congrArg Subtype.val hx2
    exact Subgroup.mem_subgroupOf.mpr (by
      show (x : G) * lam⁻¹ ∈ T₁
      exact hroot (x : G) hxG hx2G)
  have haT' : a' ∈ T' := Subgroup.mem_subgroupOf.mpr haT
  have ha2' : a' * a' = 1 := Subtype.ext ha2
  have ha1' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hat' : a' ≠ t' := fun h => hat (congrArg Subtype.val h)
  have hPa' : ¬ P' a' := hPa
  have hPat' : ¬ P' (a' * t') := by
    change ¬ P (a * t)
    exact hPat
  have hinv' : ∀ y ∈ T', y * y = 1 → y ≠ 1 → y ≠ t' → ¬ P' y → ¬ P' (y * t') →
      y ∉ T₁' ∧ y * lam'⁻¹ ∉ T₁' := by
    intro y hy hy2 hy1 hyt hyP hyPt
    have hyG : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
    have hy2G : (y : G) * (y : G) = 1 := congrArg Subtype.val hy2
    have hy1G : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hytG : (y : G) ≠ t := fun h => hyt (Subtype.ext h)
    have hyPG : ¬ P (y : G) := hyP
    have hyPtG : ¬ P ((y : G) * t) := by
      change ¬ P ((y : G) * t)
      exact hyPt
    have h := hinv (y : G) hyG hy2G hy1G hytG hyPG hyPtG
    refine ⟨fun hmem => h.1 (Subgroup.mem_subgroupOf.mp hmem), ?_⟩
    intro hmem
    exact h.2 (by
      show (y : G) * lam⁻¹ ∈ T₁
      exact Subgroup.mem_subgroupOf.mp hmem)
  have hPT₀' : ∀ y ∈ T', y * y = 1 → y ≠ 1 → P' y → y ∈ T₀' := by
    intro y hy hy2 hy1 hyP
    exact Subgroup.mem_subgroupOf.mpr
      (hPT₀ (y : G) (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hy2)
        (fun h => hy1 (Subtype.ext h)) hyP)
  have hT₀gen' : T₀' ≤ Subgroup.closure {y : Dg | y ∈ T₀' ∧ y * y = 1 ∧ P' y} := by
    have hmapS : (Subgroup.closure {y : Dg | y ∈ T₀' ∧ y * y = 1 ∧ P' y}).map D.subtype =
        Subgroup.closure {y : G | y ∈ T₀ ∧ y * y = 1 ∧ P y} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨Subgroup.mem_subgroupOf.mp hy.1, ?_, hy.2.2⟩
        show (y : G) * (y : G) = 1
        exact congrArg Subtype.val hy.2.1
      · rintro ⟨hzT₀, hz2, hzP⟩
        exact ⟨⟨z, hTD (hT₀T hzT₀)⟩,
          ⟨Subgroup.mem_subgroupOf.mpr hzT₀, Subtype.ext hz2, hzP⟩, rfl⟩
    intro x hx
    have hxG : (x : G) ∈ Subgroup.closure {y : G | y ∈ T₀ ∧ y * y = 1 ∧ P y} :=
      hT₀gen (Subgroup.mem_subgroupOf.mp hx)
    rw [← hmapS] at hxG
    rcases Subgroup.mem_map.mp hxG with ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hcore := core_le (H := Dg) (T := T') (T₀ := T₀') (T₁ := T₁')
    P' hP' hT' hTidx' htT' ht2' hcent' htT₀' hPt' hT₀T' hT₁' hT₁T' hT₁n' hidx'
    hlamT' hlam' hroot' haT' ha2' ha1' hat' hPa' hPat' hinv' hPT₀' hT₀gen'
  have hmapO2 : (CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup Dg)).map D.subtype =
      CFSG.GroupTheory.oddOrderClosure D := by
    refine le_antisymm ?_ ?_
    · have h := CFSG.GroupTheory.map_oddOrderClosure_le D.subtype (⊤ : Subgroup Dg)
      simpa [Subgroup.map_top, D.range_subtype] using h
    · rw [CFSG.GroupTheory.oddOrderClosure_le_iff]
      rintro g ⟨hgD, hgodd⟩
      refine Subgroup.mem_map.mpr ⟨⟨g, hgD⟩, ?_, rfl⟩
      exact CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd (Subgroup.mem_top _)
        (by
          rw [← Subgroup.orderOf_coe]
          change Odd (orderOf g)
          exact hgodd)
  have hmapT : T'.map D.subtype = T := by
    change (T.subgroupOf D).map D.subtype = T
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTD]
  have hmapT₀ : T₀'.map D.subtype = T₀ := by
    change (T₀.subgroupOf D).map D.subtype = T₀
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (fun x hx => hTD (hT₀T hx))]
  have hmapT₁ : T₁'.map D.subtype = T₁ := by
    change (T₁.subgroupOf D).map D.subtype = T₁
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (fun x hx => hTD (hT₁T hx))]
  have hcore_map : (CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup Dg) ⊓ T').map D.subtype ≤
      T₀ := by
    refine (Subgroup.map_mono hcore).trans ?_
    rw [hmapT₀]
  have hmap_inf : (CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup Dg) ⊓ T').map D.subtype =
      CFSG.GroupTheory.oddOrderClosure D ⊓ T := by
    rw [Subgroup.map_inf _ _ _ D.subtype_injective, hmapO2, hmapT]
  rw [← hmap_inf]
  exact hcore_map

theorem oddOrderClosure_inf_eq {G : Type*} [Group G] [Finite G] {D T T₀ T₁ : Subgroup G}
    {t lam a : G} (P : G → Prop) (hP : ∀ g y : G, P (g * y * g⁻¹) ↔ P y)
    (hTD : T ≤ D) (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.relIndex D)
    (htD : ∀ g ∈ D, g * t = t * g) (htT : t ∈ T) (ht2 : t * t = 1) (htT₀ : t ∉ T₀)
    (hPt : ¬ P t) (hT₀T : T₀ ≤ T)
    (hT₁ : ∀ x, x ∈ T₁ ↔ x ∈ T₀ ∨ ∃ s ∈ T₀, x = t * s)
    (hT₁T : T₁ ≤ T) (hT₁n : ∀ g ∈ T, ∀ x ∈ T₁, g * x * g⁻¹ ∈ T₁) (hidx : T₁.relIndex T = 4)
    (hlamT : lam ∈ T) (hlam : lam * lam = t)
    (hroot : ∀ x ∈ T, x * x = t → x * lam⁻¹ ∈ T₁)
    (haT : a ∈ T) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) (hPa : ¬ P a)
    (hPat : ¬ P (a * t))
    (hinv : ∀ y ∈ T, y * y = 1 → y ≠ 1 → y ≠ t → ¬ P y → ¬ P (y * t) →
      y ∉ T₁ ∧ y * lam⁻¹ ∉ T₁)
    (hPT₀ : ∀ y ∈ T, y * y = 1 → y ≠ 1 → P y → y ∈ T₀)
    (hT₀gen : T₀ ≤ Subgroup.closure {y | y ∈ T₀ ∧ y * y = 1 ∧ P y})
    {L : Subgroup G} {f τ : G} (hLD : L ≤ D) (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hfD : f ∈ D) (hf : Odd (orderOf f)) (hfL : ∀ l ∈ L, f * l * f⁻¹ ∈ L)
    (hfix : ∀ l ∈ L, f * l = l * f → l = 1) (hτD : τ ∈ D)
    (hT₀L : T₀ ≤ L ⊔ L.map (MulAut.conj τ).toMonoidHom) :
    CFSG.GroupTheory.oddOrderClosure D ⊓ T = T₀ := by
  refine le_antisymm (oddOrderClosure_inf_le P hP hTD hT hTidx htD htT ht2 htT₀ hPt hT₀T
    hT₁ hT₁T hT₁n hidx hlamT hlam hroot haT ha2 ha1 hat hPa hPat hinv hPT₀ hT₀gen) ?_
  have hL' : L ≤ CFSG.GroupTheory.oddOrderClosure D :=
    le_oddOrderClosure_of_fixedPointFree hLD hL hfD hf hfL hfix
  have hLconj : L.map (MulAut.conj τ).toMonoidHom ≤ CFSG.GroupTheory.oddOrderClosure D := by
    rintro y ⟨x, hx, rfl⟩
    exact CFSG.GroupTheory.conj_mem_oddOrderClosure (Subgroup.le_normalizer hτD) (hL' hx)
  have hT₀O2 : T₀ ≤ CFSG.GroupTheory.oddOrderClosure D :=
    hT₀L.trans (sup_le hL' hLconj)
  intro x hx
  exact ⟨hT₀O2 hx, hT₀T hx⟩

end CFSG.Sporadic.SuzRecog.SuzL34
