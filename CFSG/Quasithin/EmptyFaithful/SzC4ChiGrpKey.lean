module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpEx

public section

namespace CFSG.Quasithin.SzC4

theorem chi_exact_aux (D : DeltaAPI) : ∀ (n : ℕ) {A M B : Type} [Group A] [Group M] [Group B]
    [Finite A] [Finite M] [Finite B], Nat.card M = n → IsPGroup 2 M → ∀ (ι : A →* M)
    (π : M →* B), Function.Injective ι → Function.Surjective π → ι.range = π.ker →
    ∀ (φA : MulAut A) (φM : MulAut M) (φB : MulAut B), φM ^ 7 = 1 →
    (∀ a : A, φM (ι a) = ι (φA a)) → (∀ m : M, π (φM m) = φB (π m)) →
    chi D M φM = chi D A φA + chi D B φB := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A M B _ _ _ _ _ _ hn hM ι π hι hπ hex φA φM φB h7 h1 h2
    have hA2 : IsPGroup 2 A := hM.of_injective ι hι
    have hB2 : IsPGroup 2 B := hM.of_surjective π hπ
    have hA7 : φA ^ 7 = 1 := pow_eq_one_of_injective ι hι φA φM h1 7 h7
    have hB7 : φB ^ 7 = 1 := pow_eq_one_of_surjective π hπ φM φB (fun m => (h2 m).symm) 7 h7
    by_cases hnt : Nontrivial M
    swap
    · rw [not_nontrivial_iff_subsingleton] at hnt
      have : Subsingleton A := hι.subsingleton
      have : Subsingleton B := hπ.subsingleton
      rw [chi_of_subsingleton, chi_of_subsingleton, chi_of_subsingleton]
      rfl
    have hqA7 : sqQuotAut φA ^ 7 = 1 :=
      pow_eq_one_of_surjective (QuotientGroup.mk' (sq A)) (QuotientGroup.mk'_surjective _) φA
        (sqQuotAut φA) (fun x => rfl) 7 hA7
    have hqM7 : sqQuotAut φM ^ 7 = 1 :=
      pow_eq_one_of_surjective (QuotientGroup.mk' (sq M)) (QuotientGroup.mk'_surjective _) φM
        (sqQuotAut φM) (fun x => rfl) 7 h7
    have hq1 : ∀ q, sqQuotAut φM (sqMapQ ι q) = sqMapQ ι (sqQuotAut φA q) := fun q =>
      (sqMapQ_comm ι φA φM h1 q).symm
    have h4 := delta_four D quotient_sq_exp quotient_sq_exp (sqMapQ ι) (sqMapQ π)
      (sqMapQ_surjective π hπ) (sqMapQ_range_eq_ker ι π hπ hex) (sqQuotAut φA) (sqQuotAut φM)
      (sqQuotAut φB) hqA7 hqM7 hq1 (sqMapQ_comm π φM φB fun m => (h2 m).symm)
    have hLinv : ∀ a, φA a ∈ (sq M).comap ι ↔ a ∈ (sq M).comap ι := fun a => by
      rw [Subgroup.mem_comap, Subgroup.mem_comap, ← h1, sq_invariant]
    have hsqL : ∀ a ∈ sq A, a ∈ (sq M).comap ι := fun a ha =>
      sq_map_le ι (Subgroup.mem_map_of_mem ι ha)
    have hLb : ∀ a ∈ (sq M).comap ι, QuotientGroup.mk' (sq A) a ∈ (sqMapQ ι).ker := fun a ha =>
      (QuotientGroup.eq_one_iff (ι a)).2 ha
    let ι₁ : (sq M).comap ι →* sq M := subHom ι _ (sq M) fun a ha => ha
    let ι₂ : sq A →* (sq M).comap ι := subHom (MonoidHom.id A) (sq A) _ hsqL
    let π₁ : sq M →* sq B := subHom π (sq M) (sq B) fun m hm =>
      sq_map_le π (Subgroup.mem_map_of_mem π hm)
    let π₂ : (sq M).comap ι →* (sqMapQ ι).ker :=
      subHom (QuotientGroup.mk' (sq A)) _ (sqMapQ ι).ker hLb
    have inj1 : Function.Injective ι₁ := fun a b h =>
      Subtype.ext (hι (congrArg Subtype.val h))
    have surj1 : Function.Surjective π₁ := fun y => by
      have hy : (y : B) ∈ (sq M).map π := by rw [sq_map_eq π hπ]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have ex1 : ι₁.range = π₁.ker := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have : ι a ∈ π.ker := hex ▸ ⟨a, rfl⟩
        exact Subtype.ext this
      · intro hx
        have hx' : (x : M) ∈ π.ker := congrArg Subtype.val hx
        rw [← hex] at hx'
        obtain ⟨a, ha⟩ := hx'
        refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
        show ι a ∈ sq M
        rw [ha]
        exact x.2
    have hsM2 : IsPGroup 2 (sq M) := hM.to_subgroup (sq M)
    have hsM7 : sqRestrictAut φM ^ 7 = 1 :=
      pow_eq_one_of_injective (sq M).subtype Subtype.val_injective _ φM (fun x => rfl) 7 h7
    have h3 : chi D (sq M) (sqRestrictAut φM) =
        chi D ((sq M).comap ι) (restrictAut φA _ hLinv) + chi D (sq B) (sqRestrictAut φB) :=
      ih (Nat.card (sq M)) (lt_of_lt_of_eq (sq_lt_of_isPGroup hM) hn) rfl hsM2 ι₁ π₁ inj1 surj1
        ex1 (restrictAut φA _ hLinv) (sqRestrictAut φM) (sqRestrictAut φB) hsM7
        (fun a => Subtype.ext (h1 a)) (fun x => Subtype.ext (h2 x))
    have hL2 : IsPGroup 2 ((sq M).comap ι) :=
      hM.of_injective (ι.comp ((sq M).comap ι).subtype) (hι.comp Subtype.val_injective)
    have hL7 : restrictAut φA _ hLinv ^ 7 = 1 :=
      pow_eq_one_of_injective ((sq M).comap ι).subtype Subtype.val_injective _ φA
        (fun x => rfl) 7 hA7
    have hlt : Nat.card ((sq M).comap ι) < n := by
      have h1' : Nat.card ((sq M).comap ι) ≤ Nat.card (sq M) :=
        Nat.card_le_card_of_injective ι₁ inj1
      have h2' : Nat.card (sq M) < Nat.card M := sq_lt_of_isPGroup hM
      omega
    have inj2 : Function.Injective ι₂ := fun a b h =>
      Subtype.ext (congrArg (fun x : (sq M).comap ι => (x : A)) h)
    have surj2 : Function.Surjective π₂ := by
      rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H a =>
        have ha : a ∈ (sq M).comap ι := (QuotientGroup.eq_one_iff (ι a)).1 hq
        exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
    have ex2 : ι₂.range = π₂.ker := by
      ext a
      constructor
      · rintro ⟨x, rfl⟩
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 x.2)
      · intro ha
        have : (QuotientGroup.mk a.1 : A ⧸ sq A) = 1 := congrArg Subtype.val ha
        exact ⟨⟨a.1, (QuotientGroup.eq_one_iff _).1 this⟩, Subtype.ext rfl⟩
    have h4' : chi D ((sq M).comap ι) (restrictAut φA _ hLinv) =
        chi D (sq A) (sqRestrictAut φA) + chi D (sqMapQ ι).ker
          (restrictAut (sqQuotAut φA) (sqMapQ ι).ker
            (ker_invariant (sqMapQ ι) (sqQuotAut φA) (sqQuotAut φM) hq1)) :=
      ih _ hlt rfl hL2 ι₂ π₂ inj2 surj2 ex2 (sqRestrictAut φA) (restrictAut φA _ hLinv) _ hL7
        (fun x => Subtype.ext rfl) (fun a => Subtype.ext rfl)
    have hLb7 : restrictAut (sqQuotAut φA) (sqMapQ ι).ker
        (ker_invariant (sqMapQ ι) (sqQuotAut φA) (sqQuotAut φM) hq1) ^ 7 = 1 :=
      pow_eq_one_of_injective (sqMapQ ι).ker.subtype Subtype.val_injective _ (sqQuotAut φA)
        (fun x => rfl) 7 hqA7
    have hchiLb := chi_of_isExpTwo D (sqMapQ ι).ker (isExpTwo_subgroup quotient_sq_exp _) _ hLb7
    rw [chi_unfold D φM hM h7, chi_unfold D φA hA2 hA7, chi_unfold D φB hB2 hB7, h3, h4',
      hchiLb]
    linarith

theorem chi_exact (D : DeltaAPI) {A M B : Type} [Group A] [Group M] [Group B] [Finite A]
    [Finite M] [Finite B] (hM : IsPGroup 2 M) (ι : A →* M) (π : M →* B)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : ι.range = π.ker)
    (φA : MulAut A) (φM : MulAut M) (φB : MulAut B) (h7 : φM ^ 7 = 1)
    (h1 : ∀ a : A, φM (ι a) = ι (φA a)) (h2 : ∀ m : M, π (φM m) = φB (π m)) :
    chi D M φM = chi D A φA + chi D B φB :=
  chi_exact_aux D _ rfl hM ι π hι hπ hex φA φM φB h7 h1 h2

end CFSG.Quasithin.SzC4
