module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A6Aut
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.E6.Alt.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Unc25A6 CFSG.Quasithin.E6.Bar

theorem encard_invSet_le : (InvSet Dsub).encard ≤ 3 := by
  let f : MulAut X0 → List ℕ := fun β =>
    code ((Function.surjInv conjAut_surjective β : ↥A6Models.autA6) : P10)
  have hinj : Set.InjOn f (InvSet Dsub) := by
    intro β _ β' _ h
    have h1 : Function.surjInv conjAut_surjective β = Function.surjInv conjAut_surjective β' :=
      Subtype.ext (code_injective h)
    calc β = conjAut (Function.surjInv conjAut_surjective β) :=
          (Function.surjInv_eq conjAut_surjective β).symm
      _ = conjAut (Function.surjInv conjAut_surjective β') := by rw [h1]
      _ = β' := Function.surjInv_eq conjAut_surjective β'
  have hmaps : Set.MapsTo f (InvSet Dsub) (↑invCentD.toFinset : Set (List ℕ)) := by
    intro β hβ
    obtain ⟨a, ha, hmem⟩ := (mem_invSet_iff β).1 hβ
    have h1 : Function.surjInv conjAut_surjective β = a :=
      conjAut_injective ((Function.surjInv_eq conjAut_surjective β).trans ha.symm)
    have h2 : f β = code (a : P10) := by simp only [f, h1]
    rw [Finset.mem_coe, List.mem_toFinset, h2]
    exact hmem
  calc (InvSet Dsub).encard ≤ (↑invCentD.toFinset : Set (List ℕ)).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = (invCentD.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (invCentD.length : ℕ∞) := by exact_mod_cast List.toFinset_card_le _
    _ = 3 := by rw [invCentD_length]; rfl

theorem mem_fixedSub_iff (a : ↥A6Models.autA6) (x : X0) :
    x ∈ fixedSub (conjAut a) ↔ (a : P10) * (x : P10) = (x : P10) * (a : P10) := by
  rw [mem_fixedSub]
  constructor
  · intro h
    have := congrArg (fun y : X0 => (y : P10)) h
    change (a : P10) * (x : P10) * (a : P10)⁻¹ = (x : P10) at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro h
    apply Subtype.ext
    change (a : P10) * (x : P10) * (a : P10)⁻¹ = (x : P10)
    rw [h, mul_inv_cancel_right]

theorem mem_fixedSub_iff_code (a : ↥A6Models.autA6) (x : X0) :
    x ∈ fixedSub (conjAut a) ↔ (code (x : P10)) ∈ Core.cpslList (code (a : P10)) := by
  rw [mem_fixedSub_iff, Core.cpslList, List.mem_filter]
  constructor
  · intro h
    refine ⟨code_X0_mem x, ?_⟩
    rw [beq_iff_eq, ← code_mul, ← code_mul, h]
  · rintro ⟨-, h⟩
    rw [beq_iff_eq, ← code_mul, ← code_mul] at h
    exact (code_injective h).symm

theorem card_fixedSub (a : ↥A6Models.autA6) :
    Nat.card ↥(fixedSub (conjAut a)) = (Core.cpslList (code (a : P10))).length := by
  have h1 : Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(a : P10)} : Set P10)) =
      (Core.cpslList (code (a : P10))).length := card_psl29_centralizer
  rw [← h1]
  let f : ↥(fixedSub (conjAut a)) →
      ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(a : P10)} : Set P10)) := fun x =>
    ⟨((x : X0) : P10), (x : X0).2, by
      show ((x : X0) : P10) ∈ Subgroup.centralizer ({(a : P10)} : Set P10)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((mem_fixedSub_iff a x).1 x.2).symm⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun x y hxy => ?_, fun y => ?_⟩)
  · exact Subtype.ext (Subtype.ext (congrArg
      (fun z : ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(a : P10)} : Set P10)) => (z : P10)) hxy))
  · refine ⟨⟨⟨y.1, y.2.1⟩, (mem_fixedSub_iff a _).2 ?_⟩, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 y.2.2).symm

theorem exists_pow_two_pow_three_of_dvd_24 {d : ℕ} (h : d ∣ 24) :
    ∃ a b : ℕ, d = 2 ^ a * 3 ^ b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 (show d ∣ 2 ^ 3 * 3 ^ 1 from h)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  exact ⟨a, b, rfl⟩

theorem isSolvable_of_card_dvd_24 {X : Type} [Group X] [Finite X] (h : Nat.card X ∣ 24) :
    Group.IsSolvable X := by
  obtain ⟨a, b, hab⟩ := exists_pow_two_pow_three_of_dvd_24 h
  have := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hab])

theorem isSolvable_fixedSub {β : MulAut X0} (hβ : β ∈ InvSet Dsub) :
    Group.IsSolvable ↥(fixedSub β) := by
  obtain ⟨a, rfl, hmem⟩ := (mem_invSet_iff β).1 hβ
  refine isSolvable_of_card_dvd_24 ?_
  rw [card_fixedSub]
  exact invCentD_dvd _ hmem

end CFSG.Quasithin.E6.Alt.A6
