module

public import CFSG.Quasithin.Recognition.St84.SemidirectRec
public import CFSG.Quasithin.Recognition.St84.HeisF4Rigid
public import CFSG.GroupTheory.CardMapInfKer
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.F112R.St84.Heis

variable {G : Type*} [Group G]

theorem ker_parAct {P Q : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (χ : ↥Q ≃* Q1M) :
    (parAct hPQ χ).ker = (P ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf P := by
  ext p
  show parAct hPQ χ p = 1 ↔ p ∈ (P ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf P
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, parAct_eq_one_iff]
  simp

theorem inf_eq_bot_of_le_normalizer_of_parAct_eq_ρM {P Q R A : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (χ : ↥Q ≃* Q1M)
    {r₀ : G} (hr₀ : r₀ ∈ R) (hRP : R ≤ P)
    (hρ : parAct hPQ χ ⟨r₀, hRP hr₀⟩ = ρM) (hRQ : R ⊓ Q = ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    A ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxQ⟩ := Subgroup.mem_inf.mp hx
  have hxcomm : ∀ r ∈ R, x * r = r * x := by
    intro r hr
    have h1 : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hAR hxA) r).mp hr
    have h2 : r * x⁻¹ * r⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPQ (hRP hr)) x⁻¹).mp (Q.inv_mem hxQ)
    have h3 : x * r * x⁻¹ * r⁻¹ ∈ Q := by
      have e : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
      rw [e]
      exact Q.mul_mem hxQ h2
    have h4 : x * r * x⁻¹ * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hr)
    have h5 : x * r * x⁻¹ * r⁻¹ = 1 := by
      have hmem : x * r * x⁻¹ * r⁻¹ ∈ R ⊓ Q := ⟨h4, h3⟩
      rwa [hRQ] at hmem
    have h6 : x * r * x⁻¹ = r := mul_inv_eq_one.mp h5
    calc x * r = (x * r * x⁻¹) * x := by group
      _ = r * x := by rw [h6]
  have hconj : r₀ * x * r₀⁻¹ = x := by
    rw [← hxcomm r₀ hr₀]
    group
  have hfix : ρM (χ ⟨x, hxQ⟩) = χ ⟨x, hxQ⟩ := by
    rw [← hρ, parAct_apply]
    simp only [MulEquiv.symm_apply_apply]
    exact congrArg χ (Subtype.ext hconj)
  have hone : χ ⟨x, hxQ⟩ = 1 := eq_one_of_ρM_eq (χ ⟨x, hxQ⟩) hfix
  have hx1 : x = 1 := by
    have hsub : (⟨x, hxQ⟩ : ↥Q) = 1 := χ.injective (by rw [hone, map_one])
    simpa using congrArg Subtype.val hsub
  simpa [hx1]

theorem map_eq_AJ3_of_card_eq_nine [Finite G] {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hker : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G))) (χ : ↥Q ≃* Q1M)
    {R : Subgroup ↥P} (hR : Nat.card R = 9) {β : ↥P} (hβR : β ∈ R)
    (hχβ : parAct hPQ χ β = βM) :
    R.map (parAct hPQ χ) = AJ3 := by
  classical
  let ψ : ↥P →* MulAut Q1M := parAct hPQ χ
  have hK2 : IsPGroup 2 ψ.ker := by
    rw [ker_parAct hPQ χ]
    exact hker.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (p := 3) (n := 2) (by rw [hR]; norm_num)
  have hRdisj : R ⊓ ψ.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_coprime hR3 hK2 (by norm_num : Nat.Coprime 3 2))
  have hcommR : ∀ x y : ↥R, x * y = y * x :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (by rw [hR]; norm_num)).is_comm.comm
  have hle : R.map ψ ≤ AJ3 := by
    rintro _ ⟨r, hr, rfl⟩
    have hψβ : ψ β = βM := hχβ
    have hcomm : ψ r * βM = βM * ψ r := by
      have hrr : (⟨r, hr⟩ : ↥R) * ⟨β, hβR⟩ = ⟨β, hβR⟩ * ⟨r, hr⟩ := hcommR _ _
      have h := congrArg (fun x : ↥R => ψ (x : ↥P)) hrr
      simpa only [Subgroup.coe_mul, map_mul, hψβ] using h
    have hmemAJ : ψ r ∈ AJ := mem_AJ_of_commute hcomm
    have hpow : (ψ r) ^ 9 = 1 := by
      have h9 : (⟨r, hr⟩ : ↥R) ^ 9 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        simpa [hR] using orderOf_dvd_natCard (⟨r, hr⟩ : ↥R)
      have h9' : r ^ 9 = 1 := by simpa using congrArg Subtype.val h9
      calc (ψ r) ^ 9 = ψ (r ^ 9) := (map_pow ψ r 9).symm
        _ = 1 := by rw [h9', map_one]
    exact mem_AJ3_of_pow hmemAJ hpow
  have hcard : Nat.card ↥(R.map ψ) = Nat.card AJ3 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot ψ hRdisj, hR, card_AJ3]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

theorem exists_sylow_map_eq_AJ3 [Finite G] {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hker : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G))) (χ : ↥Q ≃* Q1M)
    {β : G} (hβP : β ∈ P) (hβ3 : β ^ 3 = 1) (hχβ : parAct hPQ χ ⟨β, hβP⟩ = βM)
    (h3 : Nat.factorization (Nat.card P) 3 = 2) :
    ∃ R0 : Sylow 3 ↥P, β ∈ (R0 : Subgroup ↥P).map P.subtype ∧
      Nat.card (R0 : Subgroup ↥P) = 9 ∧ (R0 : Subgroup ↥P).map (parAct hPQ χ) = AJ3 := by
  classical
  let βP : ↥P := ⟨β, hβP⟩
  have hβP3 : βP ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hβ3
  have hzβ : IsPGroup 3 (Subgroup.zpowers βP) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa using orderOf_dvd_of_pow_eq_one hβP3
  obtain ⟨R0, hR0le⟩ := hzβ.exists_le_sylow
  have hβR0 : βP ∈ (R0 : Subgroup ↥P) := hR0le (Subgroup.mem_zpowers βP)
  have hR0card : Nat.card ((R0 : Subgroup ↥P)) = 9 := by
    rw [Sylow.card_eq_multiplicity, h3]
    norm_num
  exact ⟨R0, Subgroup.mem_map.mpr ⟨βP, hβR0, rfl⟩, hR0card,
    map_eq_AJ3_of_card_eq_nine hPQ hker χ hR0card hβR0 hχβ⟩

theorem AJ_le_of_AJ3_le_of_τM_mem {H : Subgroup (MulAut Q1M)}
    (h3 : AJ3 ≤ H) (hτ : τM ∈ H) : AJ ≤ H := by
  have hρ : ρM ∈ H := h3 ρM_mem_AJ3
  have hβ : βM ∈ H := h3 (mem_AJ3_iff.mpr (aj3List_exponents_mem 0 1))
  intro x hx
  rw [mem_AJ_iff] at hx
  rw [mem_ajList] at hx
  obtain ⟨i, j, k, rfl⟩ := hx
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ hρ _) (Subgroup.pow_mem _ hβ _))
    (Subgroup.pow_mem _ hτ _)

private theorem exists_frattini_normalizer {X : Type*} [Group X] [Finite X]
    {H N0 : Subgroup X} {ψ : X →* MulAut Q1M} {R0 : Sylow 3 X}
    (hHmap : H.map ψ = AJ) (hN0map : N0.map ψ = AJ3) (hN0H : N0 ≤ H)
    (hR0N0 : (R0 : Subgroup X) ≤ N0) (hR0H : (R0 : Subgroup X) ≤ H)
    (hN0normal : (N0.subgroupOf H).Normal)
    (hR0map : (R0 : Subgroup X).map ψ = AJ3) :
    ∃ AH : Subgroup ↥H, (R0.subtype hR0H : Subgroup ↥H) ≤ AH ∧
      AH ≤ Subgroup.normalizer ((R0.subtype hR0H : Sylow 3 ↥H) : Set ↥H) ∧
      AH.map (ψ.comp H.subtype) = AJ := by
  classical
  let RH : Sylow 3 ↥H := R0.subtype hR0H
  let AH : Subgroup ↥H := Subgroup.normalizer (RH : Set ↥H)
  let ψH : ↥H →* MulAut Q1M := ψ.comp H.subtype
  have hRHN0 : (RH : Subgroup ↥H) ≤ N0.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hR0N0 hx
  have hψHrange : ψH.range = AJ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hHmap]
  have hN0Hmap : (N0.subgroupOf H).map ψH = AJ3 := by
    rw [show ψH = ψ.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hN0H, hN0map]
  have hRHmap : (RH : Subgroup ↥H).map ψH = AJ3 := by
    have hcoe : (RH : Subgroup ↥H) = (R0 : Subgroup X).subgroupOf H := rfl
    rw [hcoe, show ψH = ψ.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR0H, hR0map]
  have hfrattini : AH ⊔ N0.subgroupOf H = ⊤ :=
    Sylow.normalizer_sup_eq_top' RH hRHN0
  have hAHmap : AH.map ψH = AJ := by
    have h1 : AH.map ψH ⊔ (N0.subgroupOf H).map ψH = (⊤ : Subgroup ↥H).map ψH := by
      rw [← Subgroup.map_sup, hfrattini]
    rw [hN0Hmap, ← MonoidHom.range_eq_map, hψHrange] at h1
    have hle : AJ3 ≤ AH.map ψH := by
      rw [← hRHmap]
      exact Subgroup.map_mono Subgroup.le_normalizer
    rw [sup_eq_left.mpr hle] at h1
    exact h1
  exact ⟨AH, Subgroup.le_normalizer, le_refl AH, hAHmap⟩

private theorem exists_normalizer_sylow_map_eq_AJ {X : Type*} [Group X] [Finite X]
    (ψ : X →* MulAut Q1M) (R0 : Sylow 3 X)
    (hR0map : (R0 : Subgroup X).map ψ = AJ3) (hAJ : AJ ≤ ψ.range) :
    ∃ A : Subgroup X, (R0 : Subgroup X) ≤ A ∧
      A ≤ Subgroup.normalizer (R0 : Set X) ∧ A.map ψ = AJ := by
  classical
  let H : Subgroup X := AJ.comap ψ
  let N0 : Subgroup X := AJ3.comap ψ
  have hAJ3le : AJ3 ≤ ψ.range := by
    rw [MonoidHom.range_eq_map, ← hR0map]
    exact Subgroup.map_mono le_top
  have hHmap : H.map ψ = AJ := Subgroup.map_comap_eq_self hAJ
  have hN0map : N0.map ψ = AJ3 := Subgroup.map_comap_eq_self hAJ3le
  have hN0H : N0 ≤ H := by
    intro x hx
    change ψ x ∈ AJ3 at hx
    change ψ x ∈ AJ
    exact AJ3_le_AJ hx
  have hR0N0 : (R0 : Subgroup X) ≤ N0 := by
    intro r hr
    have hmem : ψ r ∈ (R0 : Subgroup X).map ψ := ⟨r, hr, rfl⟩
    rwa [hR0map] at hmem
  have hR0H : (R0 : Subgroup X) ≤ H := hR0N0.trans hN0H
  have hAJ3normal : (AJ3.subgroupOf AJ).Normal := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (AJ3_le_AJ.trans AJ_le_AJ')).mp AJ3_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer AJ3_le_AJ).mpr (AJ_le_AJ'.trans h)
  have hN0normal : (N0.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN0H]
    intro n h hnh hh
    change ψ (h * n * h⁻¹) ∈ AJ3
    change ψ n ∈ AJ3 at hnh
    change ψ h ∈ AJ at hh
    have hconj : ψ h * ψ n * (ψ h)⁻¹ ∈ AJ3 :=
      (Subgroup.normal_subgroupOf_iff AJ3_le_AJ).mp hAJ3normal (ψ n) (ψ h) hnh hh
    rw [map_mul, map_mul, map_inv]
    exact hconj
  obtain ⟨AH, hRHAH, hAHnorm, hAHmap⟩ :=
    exists_frattini_normalizer hHmap hN0map hN0H hR0N0 hR0H hN0normal hR0map
  let A : Subgroup X := AH.map H.subtype
  have hR0coe : (R0.subtype hR0H : Subgroup ↥H).map H.subtype = (R0 : Subgroup X) := by
    rw [show (R0.subtype hR0H : Subgroup ↥H) = (R0 : Subgroup X).subgroupOf H from rfl,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR0H]
  have hR0A : (R0 : Subgroup X) ≤ A := by
    rw [← hR0coe]
    exact Subgroup.map_mono hRHAH
  have hAnorm : A ≤ Subgroup.normalizer (R0 : Set X) := by
    have h2 := Subgroup.le_normalizer_map (H := (R0.subtype hR0H : Subgroup ↥H)) (f := H.subtype)
    rw [hR0coe] at h2
    exact (Subgroup.map_mono hAHnorm).trans h2
  have hAmap : A.map ψ = AJ := by
    rw [show A = AH.map H.subtype from rfl, Subgroup.map_map, hAHmap]
  exact ⟨A, hR0A, hAnorm, hAmap⟩

theorem exists_complement_of_sylow_map_eq_AJ3 [Finite G] {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (χ : ↥Q ≃* Q1M)
    {R0 : Sylow 3 ↥P} (hR0card : Nat.card (R0 : Subgroup ↥P) = 9)
    (hR0map : (R0 : Subgroup ↥P).map (parAct hPQ χ) = AJ3)
    (hAJ : AJ ≤ (parAct hPQ χ).range) :
    ∃ A : Subgroup G, ∃ hAP : A ≤ P,
      (R0 : Subgroup ↥P).map P.subtype ≤ A ∧
      Nat.card ((R0 : Subgroup ↥P).map P.subtype) = 9 ∧
      A ≤ Subgroup.normalizer ((R0 : Subgroup ↥P).map P.subtype : Set G) ∧ A ⊓ Q = ⊥ ∧
      ((parAct hPQ χ).comp (Subgroup.inclusion hAP)).range = AJ := by
  classical
  let ψ : ↥P →* MulAut Q1M := parAct hPQ χ
  obtain ⟨A', hR0A', hA'norm, hA'map⟩ :=
    exists_normalizer_sylow_map_eq_AJ ψ R0 hR0map hAJ
  let A : Subgroup G := A'.map P.subtype
  have hAP : A ≤ P := Subgroup.map_subtype_le A'
  let R : Subgroup G := (R0 : Subgroup ↥P).map P.subtype
  have hRcard : Nat.card R = 9 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hR0card]
  have hRA : R ≤ A := Subgroup.map_mono hR0A'
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    have h := Subgroup.le_normalizer_map (H := (R0 : Subgroup ↥P)) (f := P.subtype)
    exact (Subgroup.map_mono hA'norm).trans h
  have hρMmem : ρM ∈ (R0 : Subgroup ↥P).map ψ := by
    rw [hR0map]
    exact ρM_mem_AJ3
  obtain ⟨r0, hr0R0, hr0ψ⟩ := Subgroup.mem_map.mp hρMmem
  have hr0R : (r0 : G) ∈ R := Subgroup.mem_map.mpr ⟨r0, hr0R0, rfl⟩
  have hρ : parAct hPQ χ ⟨(r0 : G), hAP (hRA hr0R)⟩ = ρM := by
    have hsub : (⟨(r0 : G), hAP (hRA hr0R)⟩ : ↥P) = r0 := Subtype.ext rfl
    calc parAct hPQ χ ⟨(r0 : G), hAP (hRA hr0R)⟩ = ψ ⟨(r0 : G), hAP (hRA hr0R)⟩ := rfl
      _ = ψ r0 := by rw [hsub]
      _ = ρM := hr0ψ
  have hRQ : R ⊓ Q = ⊥ := by
    have hQcard : Nat.card Q = 64 := by
      rw [Nat.card_congr χ.toEquiv, card_Q1M]
    have hR3 : IsPGroup 3 R := IsPGroup.of_card (p := 3) (n := 2) (by rw [hRcard]; norm_num)
    have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (p := 2) (n := 6) (by rw [hQcard]; norm_num)
    exact disjoint_iff.mp
      (IsPGroup.disjoint_of_coprime hR3 hQ2 (by norm_num : Nat.Coprime 3 2))
  have hAQ : A ⊓ Q = ⊥ :=
    inf_eq_bot_of_le_normalizer_of_parAct_eq_ρM hPQ χ hr0R (hRA.trans hAP) hρ hRQ hAR
  have hrange : ((parAct hPQ χ).comp (Subgroup.inclusion hAP)).range = AJ := by
    rw [show parAct hPQ χ = ψ from rfl, ← hA'map]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp a.2
      exact Subgroup.mem_map.mpr ⟨p, hp, congrArg ψ (Subtype.ext hpa)⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, Subgroup.mem_map.mpr ⟨p, hp, rfl⟩⟩,
        congrArg ψ (Subtype.ext rfl)⟩
  exact ⟨A, hAP, hRA, hRcard, hAR, hAQ, hrange⟩

theorem exists_heisComplement [Finite G] {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (h3 : Nat.factorization (Nat.card P) 3 = 2)
    (hker : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G))) (χ : ↥Q ≃* Q1M)
    {β t : G} (hβP : β ∈ P) (hβ3 : β ^ 3 = 1) (hχβ : parAct hPQ χ ⟨β, hβP⟩ = βM)
    (htP : t ∈ P) (hχt : parAct hPQ χ ⟨t, htP⟩ = τM) :
    ∃ R A : Subgroup G, ∃ hAP : A ≤ P, β ∈ R ∧ R ≤ A ∧ Nat.card R = 9 ∧
      A ≤ Subgroup.normalizer (R : Set G) ∧ A ⊓ Q = ⊥ ∧
      ((parAct hPQ χ).comp (Subgroup.inclusion hAP)).range = AJ := by
  obtain ⟨R0, hβR0, hR0card, hR0map⟩ :=
    exists_sylow_map_eq_AJ3 hPQ hker χ hβP hβ3 hχβ h3
  have hAJ3le : AJ3 ≤ (parAct hPQ χ).range := by
    rw [MonoidHom.range_eq_map, ← hR0map]
    exact Subgroup.map_mono le_top
  have hAJ : AJ ≤ (parAct hPQ χ).range :=
    AJ_le_of_AJ3_le_of_τM_mem hAJ3le ⟨⟨t, htP⟩, hχt⟩
  obtain ⟨A, hAP, hRA, hRcard, hAR, hAQ, hrange⟩ :=
    exists_complement_of_sylow_map_eq_AJ3 hPQ χ hR0card hR0map hAJ
  exact ⟨(R0 : Subgroup ↥P).map P.subtype, A, hAP, hβR0, hRA, hRcard, hAR, hAQ, hrange⟩

theorem nonempty_mulEquiv_heisModel [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hP : Nat.card P = 1152)
    (hC : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) (χ : ↥Q ≃* Q1M)
    {β t : G} (hβP : β ∈ P) (hβ3 : β ^ 3 = 1) (hχβ : parAct hPQ χ ⟨β, hβP⟩ = βM)
    (htP : t ∈ P) (hχt : parAct hPQ χ ⟨t, htP⟩ = τM) :
    Nonempty (↥P ≃* Q1M ⋊[AJ.subtype] ↥AJ) := by
  classical
  have hQcard : Nat.card Q = 64 := by
    rw [Nat.card_congr χ.toEquiv, card_Q1M]
  have hQ2 : IsPGroup 2 Q :=
    IsPGroup.of_card (p := 2) (n := 6) (by rw [hQcard]; norm_num)
  have hker : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G)) := hQ2.to_le hC
  have h3 : Nat.factorization (Nat.card P) 3 = 2 := by
    rw [hP]
    decide +kernel
  obtain ⟨_, A, hAP, _, _, _, _, hAQ, hrange⟩ :=
    exists_heisComplement hPQ h3 hker χ hβP hβ3 hχβ htP hχt
  let ψ : ↥P →* MulAut Q1M := parAct hPQ χ
  let ψA : ↥A →* MulAut Q1M := ψ.comp (Subgroup.inclusion hAP)
  have hrangeA : ψA.range = AJ := hrange
  have hinjA : Function.Injective ψA := by
    intro a b hab
    have h1 : ψA (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1' : parAct hPQ χ ⟨((a * b⁻¹ : ↥A) : G), hAP (a * b⁻¹).2⟩ = 1 := h1
    have hcen : ((a * b⁻¹ : ↥A) : G) ∈ Subgroup.centralizer (Q : Set G) :=
      (parAct_eq_one_iff (P := P) (Q := Q) (hPQ := hPQ) (χ := χ)
        ⟨((a * b⁻¹ : ↥A) : G), hAP (a * b⁻¹).2⟩).mp h1'
    have hP' : ((a * b⁻¹ : ↥A) : G) ∈ P := hAP (a * b⁻¹).2
    have hQ' : ((a * b⁻¹ : ↥A) : G) ∈ Q := hC ⟨hP', hcen⟩
    have hbot : ((a * b⁻¹ : ↥A) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hAQ]
      exact ⟨(a * b⁻¹).2, hQ'⟩
    have hzero : a * b⁻¹ = 1 := by
      apply Subtype.ext
      simpa using hbot
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [hzero]; simp
  have hAcard : Nat.card A = 18 := by
    have h1 : Nat.card ↥A = Nat.card ψA.range :=
      Nat.card_congr (MonoidHom.ofInjective hinjA).toEquiv
    rw [h1, hrangeA, card_AJ]
  have hcard : Nat.card Q * Nat.card A = Nat.card P := by
    rw [hQcard, hAcard, hP]
  let e : ↥A ≃* ↥AJ := (MonoidHom.ofInjective hinjA).trans (MulEquiv.subgroupCongr hrangeA)
  have he : ∀ a : ↥A, (e a : MulAut Q1M) = parAct hPQ χ (Subgroup.inclusion hAP a) := by
    intro a
    rfl
  exact nonempty_mulEquiv_semidirect hQP hPQ hAP hAQ hcard χ e he

end CFSG.Quasithin.F112R.St84
