module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutLocal
public import CFSG.Holt.SmallGroups

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree.Asc83Table CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

theorem card_normalizer_le_of_A6 {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) {E : Subgroup X} (hE : Nat.card E = 9) :
    Nat.card (normalizer (E : Set X)) ≤ 36 := by
  have hX : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hA6 e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X).factorization 3 = 2 := by
    rw [hX, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  let P : Sylow 3 X := Sylow.ofCard E (by rw [hE, hfac]; norm_num)
  have hPE : (P : Subgroup X) = E := rfl
  have hn1 : Nat.card (Sylow 3 X) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 X
  have hn2 : Nat.card (Sylow 3 X) = (normalizer ((P : Subgroup X) : Set X)).index :=
    Sylow.card_eq_index_normalizer P
  have hn3 : Nat.card (Sylow 3 X) ∣ (P : Subgroup X).index := Sylow.card_dvd_index P
  have hidxE : (P : Subgroup X).index = 40 := by
    have := Subgroup.index_mul_card (P : Subgroup X)
    have h9 : Nat.card (P : Subgroup X) = 9 := hE
    rw [h9, hX] at this
    omega
  have hne_top : normalizer ((P : Subgroup X) : Set X) ≠ ⊤ := by
    intro htop
    have hnorm : (P : Subgroup X).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup X) with h0 | h0
    · rw [hPE] at h0
      rw [h0, Subgroup.card_bot] at hE; omega
    · rw [hPE] at h0
      rw [h0, Subgroup.card_top, hX] at hE; omega
  have hfact := CFSG.Holt.SmallGroups.card_le_factorial_index hne_top
  rw [hX] at hfact
  set n := (normalizer ((P : Subgroup X) : Set X)).index with hn
  have hndvd : n ∣ 40 := by rw [← hidxE, ← hn2]; exact hn3
  have hnmod : n % 3 = 1 := by
    have := hn1
    rw [hn2] at this
    exact this
  have hn10 : 10 ≤ n := by
    have hle : n ≤ 40 := Nat.le_of_dvd (by norm_num) hndvd
    interval_cases n <;> first | omega | (exfalso; revert hfact; decide) | skip
  have hcard := Subgroup.index_mul_card (normalizer ((P : Subgroup X) : Set X))
  rw [hX] at hcard
  have : Nat.card (normalizer ((P : Subgroup X) : Set X)) ≤ 36 := by nlinarith
  exact this

theorem mem_normalizer_inf_out {Y : Type*} [Group Y] {F I : Subgroup Y} {g : Y}
    (hF : g ∈ normalizer (F : Set Y)) (hI : g ∈ normalizer (I : Set Y)) :
    g ∈ normalizer ((F ⊓ I : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at *
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hF x, hI x]

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem exists_u_J3Plain {Y : Type} [Group Y] [Finite Y] (e : Y ≃* NativeSporadic.J3)
    {F : Subgroup Y} (hF : CFSG.IsElementaryAbelian 3 F) (hF27 : Nat.card F = 27)
    {l : Y} (hlF : l ∈ F) (hl1 : l ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({e l} : Set NativeSporadic.J3)))
    (hN : 1944 ≤ Nat.card (normalizer (F : Set Y)))
    {u₀ : Y} (hu₀N : u₀ ∈ normalizer (F : Set Y)) (hu₀ : orderOf u₀ = 8) :
    ∃ u : Y, u ∈ normalizer (F : Set Y) ∧ orderOf u = 8 ∧
      u ∈ normalizer ((zpowers l : Subgroup Y) : Set Y) ∧ u ∉ centralizer ({l} : Set Y) := by
  obtain ⟨hFcomm, hF3⟩ := isElementaryAbelian_iff.1 hF
  have hl3 : l ^ 3 = 1 := hF3 l hlF
  obtain ⟨I, hIC, hIperf, ⟨eI⟩, hImax, hC1080, hD3, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Plain e hl3 hl1 h5
  obtain ⟨B₁, hB₁F, hB₁c, hB₁3B, hB₁3A⟩ := j3_e27_class_split e hF hF27
  set N : Subgroup Y := normalizer (F : Set Y) with hNdef
  have hlB₁ : l ∉ B₁ := fun hB => by
    have := hB₁3B l hB hl1
    omega
  have hlN : l ∈ N := Subgroup.le_normalizer hlF
  have hFC : F ≤ centralizer ({l} : Set Y) := fun f hf => Subgroup.mem_centralizer_singleton_iff.2 (hFcomm f hf l hlF)
  have hDIcomm : ∀ x ∈ zpowers l, ∀ y ∈ I, x * y = y * x := fun x hx y hy => hDcomm x hx y (hIC hy)
  obtain ⟨hFeq, hFcard⟩ := card_eq_mul_card_inf_of_le (D := zpowers l) (I := I) (F := F) hDIcomm
    hDI (Subgroup.zpowers_le.2 hlF) (by rw [hCeq]; exact hFC)
  have hE₀ : Nat.card ↥(F ⊓ I) = 9 := by
    rw [hD3, hF27] at hFcard; omega
  have hM₀ : Nat.card ↥(I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) ≤ 36 := by
    have hE₀I : F ⊓ I ≤ I := inf_le_right
    have hE'card : Nat.card ((F ⊓ I).subgroupOf I) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀I).toEquiv]; exact hE₀
    have h36 := card_normalizer_le_of_A6 eI hE'card
    have hle : (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)).subgroupOf I ≤
        normalizer (((F ⊓ I).subgroupOf I : Subgroup ↥I) : Set ↥I) := by
      intro x hx
      have hx' := Subgroup.mem_subgroupOf.1 hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.1 hx'.2 (h : Y)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this
    calc Nat.card ↥(I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y))
        = Nat.card ↥((I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)).subgroupOf I) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ ≤ Nat.card ↥(normalizer (((F ⊓ I).subgroupOf I : Subgroup ↥I) : Set ↥I)) :=
          Subgroup.card_le_of_le hle
      _ ≤ 36 := h36
  have hCN : Nat.card ↥(N ⊓ centralizer ({l} : Set Y)) ≤ 108 := by
    have hle : N ⊓ centralizer ({l} : Set Y) ≤
        zpowers l ⊔ (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) := by
      intro y hy
      have hyC : y ∈ zpowers l ⊔ I := by rw [hCeq]; exact hy.2
      obtain ⟨d, hd, i, hi, rfl⟩ := (mem_sup_of_commute hDIcomm).1 hyC
      have hdN : d ∈ N := Subgroup.le_normalizer ((Subgroup.zpowers_le.2 hlF) hd)
      have hiN : i ∈ N := by
        have := N.mul_mem (N.inv_mem hdN) hy.1
        simpa using this
      have hi' : i ∈ normalizer ((F ⊓ I : Subgroup Y) : Set Y) :=
        mem_normalizer_inf_out hiN (Subgroup.le_normalizer hi)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right ⟨hi, hi'⟩)
    have hM₀N : (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) ≤
        normalizer ((zpowers l : Subgroup Y) : Set Y) := by
      refine le_trans ?_ (centralizer_le_normalizer' (zpowers l))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hDIcomm d hd x hx.1
    have hdisj : Disjoint (zpowers l) (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) :=
      hDI.mono_right inf_le_left
    have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (zpowers l)
      (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) hM₀N hdisj
    calc Nat.card ↥(N ⊓ centralizer ({l} : Set Y))
        ≤ Nat.card ↥(zpowers l ⊔ (I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y))) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥(zpowers l) * Nat.card ↥(I ⊓ normalizer ((F ⊓ I : Subgroup Y) : Set Y)) := hsup
      _ ≤ 3 * 36 := by rw [hD3]; exact Nat.mul_le_mul_left 3 hM₀
  have hHcard : Nat.card ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N) =
      Nat.card ↥(N ⊓ centralizer ({l} : Set Y)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hB₁F' : (B₁ : Set Y) ⊆ (F : Set Y) := hB₁F
  have hTcard : ((F : Set Y) \ (B₁ : Set Y)).ncard = 18 := by
    have h1 : (F : Set Y).ncard = 27 := by
      rw [← Nat.card_coe_set_eq]; exact hF27
    have h2 : (B₁ : Set Y).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]; exact hB₁c
    rw [Set.ncard_diff hB₁F' (Set.toFinite _), h1, h2]
  have hmemT : ∀ n : ↥N, (n : Y) * l * (n : Y)⁻¹ ∈ (F : Set Y) \ (B₁ : Set Y) := by
    intro n
    refine ⟨(Subgroup.mem_normalizer_iff.1 n.2 l).1 hlF, ?_⟩
    intro hB
    have hne : (n : Y) * l * (n : Y)⁻¹ ≠ 1 := fun h1 => hl1 (conj_eq_one_iff.1 h1)
    have h1 := hB₁3B _ hB hne
    rw [card_cent_conj] at h1
    omega
  let φ : ↥N ⧸ ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N) → Y :=
    Quotient.lift (fun n : ↥N => (n : Y) * l * (n : Y)⁻¹) (by
      intro n n' hnn'
      have hmem := QuotientGroup.leftRel_apply.1 hnn'
      have hc : ((n⁻¹ * n' : ↥N) : Y) ∈ centralizer ({l} : Set Y) :=
        (Subgroup.mem_subgroupOf.1 hmem).2
      have hk := Subgroup.mem_centralizer_singleton_iff.1 hc
      have hk' : ((n : Y)⁻¹ * (n' : Y)) * l = l * ((n : Y)⁻¹ * (n' : Y)) := by
        simpa using hk
      show (n : Y) * l * (n : Y)⁻¹ = (n' : Y) * l * (n' : Y)⁻¹
      calc (n : Y) * l * (n : Y)⁻¹
          = (n : Y) * (l * ((n : Y)⁻¹ * (n' : Y))) * ((n : Y)⁻¹ * (n' : Y))⁻¹ * (n : Y)⁻¹ := by
            group
        _ = (n : Y) * (((n : Y)⁻¹ * (n' : Y)) * l) * ((n : Y)⁻¹ * (n' : Y))⁻¹ * (n : Y)⁻¹ := by
            rw [hk']
        _ = (n' : Y) * l * (n' : Y)⁻¹ := by group)
  have hφmk : ∀ n : ↥N, φ (QuotientGroup.mk n) = (n : Y) * l * (n : Y)⁻¹ := fun n => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφmk, hφmk] at hxy
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.2 ⟨N.mul_mem (N.inv_mem n.2) n'.2, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show ((n : Y)⁻¹ * (n' : Y)) * l = l * ((n : Y)⁻¹ * (n' : Y))
    calc ((n : Y)⁻¹ * (n' : Y)) * l
        = (n : Y)⁻¹ * ((n' : Y) * l * (n' : Y)⁻¹) * (n' : Y) := by group
      _ = (n : Y)⁻¹ * ((n : Y) * l * (n : Y)⁻¹) * (n' : Y) := by rw [hxy]
      _ = l * ((n : Y)⁻¹ * (n' : Y)) := by group
  have hrange : Set.range φ ⊆ (F : Set Y) \ (B₁ : Set Y) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    exact hmemT n
  have hidx : Nat.card (↥N ⧸ ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N)) ≤ 18 := by
    calc Nat.card (↥N ⧸ ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N))
        = Nat.card (Set.range φ) := (Nat.card_range_of_injective hφinj).symm
      _ = (Set.range φ).ncard := Nat.card_coe_set_eq _
      _ ≤ ((F : Set Y) \ (B₁ : Set Y)).ncard := Set.ncard_le_ncard hrange (Set.toFinite _)
      _ = 18 := hTcard
  have hNcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N)
  have h18 : Nat.card (↥N ⧸ ((N ⊓ centralizer ({l} : Set Y)).subgroupOf N)) = 18 ∧
      Nat.card ↥(N ⊓ centralizer ({l} : Set Y)) = 108 := by
    rw [hHcard] at hNcard
    have hN' : 1944 ≤ Nat.card ↥N := hN
    constructor
    · apply le_antisymm hidx
      by_contra hlt
      push Not at hlt
      nlinarith
    · apply le_antisymm hCN
      by_contra hlt
      push Not at hlt
      nlinarith
  obtain ⟨h18a, h18b⟩ := h18
  have hTeq : Set.range φ = (F : Set Y) \ (B₁ : Set Y) := by
    refine Set.eq_of_subset_of_ncard_le hrange ?_ (Set.toFinite _)
    rw [hTcard, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hφinj, h18a]
  have hlinvT : l⁻¹ ∈ (F : Set Y) \ (B₁ : Set Y) := by
    refine ⟨F.inv_mem hlF, fun hB => hlB₁ ?_⟩
    simpa using B₁.inv_mem hB
  obtain ⟨x₀, hx₀⟩ : l⁻¹ ∈ Set.range φ := hTeq ▸ hlinvT
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective x₀
  rw [hφmk] at hx₀
  set q : ↥N := ⟨l, hlN⟩ with hq
  have hq3 : orderOf q = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hl3 hl1
  have hcentq : centralizer ({q} : Set ↥N) = (N ⊓ centralizer ({l} : Set Y)).subgroupOf N := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have := congrArg Subtype.val hx
      simpa using this
    · intro hx
      have hx' := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      exact Subtype.ext (by simpa using hx')
  have hS := card_normalizer_zpowers_le (X := ↥N) (q := q) hq3
  rw [hcentq, hHcard, h18b] at hS
  have hn₀S : n₀ ∈ normalizer ((zpowers q : Subgroup ↥N) : Set ↥N) := by
    apply normalizer_zpowers_of_conj_mem
    have : n₀ * q * n₀⁻¹ = q⁻¹ := Subtype.ext (by simpa using hx₀)
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers q)
  have hHS : (N ⊓ centralizer ({l} : Set Y)).subgroupOf N ≤
      normalizer ((zpowers q : Subgroup ↥N) : Set ↥N) := by
    rw [← hcentq]
    intro x hx
    apply normalizer_zpowers_of_conj_mem
    have : x * q * x⁻¹ = q := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hx
      rw [this]; group
    rw [this]
    exact Subgroup.mem_zpowers q
  have hn₀H : n₀ ∉ (N ⊓ centralizer ({l} : Set Y)).subgroupOf N := by
    intro hH
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hH).2
    have h1 : (n₀ : Y) * l * (n₀ : Y)⁻¹ = l := by rw [hc]; group
    rw [hx₀] at h1
    apply hl1
    have h2 : l * l = 1 := by
      calc l * l = l⁻¹⁻¹ * l := by rw [inv_inv]
        _ = 1 := by rw [h1]; group
    have h3 : l * l * l = 1 := by simpa [pow_succ] using hl3
    rw [h2, one_mul] at h3
    exact h3
  have hSge : 216 ≤ Nat.card (normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHS
    rw [hHcard, h18b] at hk
    have hk1 : k ≠ 1 := by
      rintro rfl
      have heq := Subgroup.eq_of_le_of_card_ge hHS (by rw [hHcard, h18b, hk])
      exact hn₀H (heq ▸ hn₀S)
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := ↥(normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)))
      omega
    omega
  have hS216 : Nat.card (normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)) = 216 := by omega
  have hindexS : (normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)).index = 9 := by
    have := Subgroup.index_mul_card (normalizer ((zpowers q : Subgroup ↥N) : Set ↥N))
    rw [hS216] at this
    have hN1944 : Nat.card ↥N = 1944 := by
      have := hNcard
      rw [h18a, hHcard, h18b] at this
      omega
    omega
  set u₀' : ↥N := ⟨u₀, hu₀N⟩ with hu₀'
  have hu₀'ord : orderOf u₀' = 8 := by rw [← Subgroup.orderOf_coe]; exact hu₀
  have hT₀card : Nat.card (zpowers u₀') = 2 ^ 3 := by
    rw [Nat.card_zpowers, hu₀'ord]; norm_num
  have hpg : IsPGroup 2 (zpowers u₀') := IsPGroup.of_card hT₀card
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : Nat.card (↥N ⧸ normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)) = 9 := hindexS
  obtain ⟨x, hx⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card
    (α := ↥N ⧸ normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)) (by rw [hcardQ]; norm_num)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix := MulAction.mem_fixedPoints.1 hx ⟨u₀', Subgroup.mem_zpowers u₀'⟩
  have hfix' : (QuotientGroup.mk (u₀' * g) : ↥N ⧸ normalizer ((zpowers q : Subgroup ↥N) : Set ↥N)) =
      QuotientGroup.mk g := hfix
  have hmem := QuotientGroup.eq.1 hfix'
  have hu'S : g⁻¹ * u₀' * g ∈ normalizer ((zpowers q : Subgroup ↥N) : Set ↥N) := by
    have := Subgroup.inv_mem _ hmem
    simpa [mul_assoc] using this
  have hu'ord : orderOf (g⁻¹ * u₀' * g) = 8 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective u₀'
    rw [hu₀'ord] at this
    simpa using this
  refine ⟨((g⁻¹ * u₀' * g : ↥N) : Y), (g⁻¹ * u₀' * g : ↥N).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hu'ord
  · apply normalizer_zpowers_of_conj_mem
    have h1 := (Subgroup.mem_normalizer_iff.1 hu'S q).1 (Subgroup.mem_zpowers q)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  · intro hc
    have hH : (g⁻¹ * u₀' * g : ↥N) ∈ (N ⊓ centralizer ({l} : Set Y)).subgroupOf N :=
      Subgroup.mem_subgroupOf.2 ⟨(g⁻¹ * u₀' * g : ↥N).2, hc⟩
    have hdvd := Subgroup.orderOf_dvd_natCard _ hH
    rw [hu'ord, hHcard, h18b] at hdvd
    omega

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
