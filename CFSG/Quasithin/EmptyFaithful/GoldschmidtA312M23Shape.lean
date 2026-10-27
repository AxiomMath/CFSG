module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuCases
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.Quasithin.A312ExtShapes CFSG.Quasithin.A312Ru CFSG.Quasithin.A312Words

theorem not_prime_half_factorial {m : ℕ} (hm : 5 ≤ m) : ¬ (m.factorial / 2).Prime := by
  intro hp
  have h3 : 3 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h5 : 120 ≤ m.factorial :=
    calc 120 = (5 : ℕ).factorial := by decide
      _ ≤ m.factorial := Nat.factorial_le hm
  obtain ⟨c, hc⟩ := h2
  have hc' : m.factorial / 2 = c := by omega
  rw [hc'] at hp
  have h3c : 3 ∣ c := by omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3c
  omega

variable {G : Type} [Group G] [Finite G]

theorem isExt_e2_alt_of_data {T B Z A : Subgroup G} (hB : B ∈ lFamily T) (hZ : B ⊔ T = Z)
    (hAZ : A ≤ Z) (hcomm : ⁅Z, Z⁆ ≤ A) (hperf : ⁅A, A⁆ = A) {m k : ℕ} (hm : 5 ≤ m)
    (V : Subgroup ↥A) [V.Normal] (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVsq : ∀ x ∈ V, x * x = 1) (hVcard : Nat.card V = 2 ^ k) (π : ↥A →* Equiv.Perm (Fin m))
    (hker : π.ker = V) (hsign : ∀ a, Equiv.Perm.sign (π a) = 1)
    (hr : Nat.card π.range = m.factorial / 2) :
    IsExt ↥B (fun V _ => IsE2 k V) (fun Y _ => IsAlt m Y) := by
  classical
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have hcardA : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  have hnab : ∃ a b : alternatingGroup (Fin m), a * b ≠ b * a :=
    nonabelian_of_simple (by rw [hcardA]; exact not_prime_half_factorial hm)
  have hmem : ∀ a, π a ∈ alternatingGroup (Fin m) := fun a =>
    Equiv.Perm.mem_alternatingGroup.mpr (hsign a)
  have hle : π.range ≤ alternatingGroup (Fin m) := by
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hrange : π.range = alternatingGroup (Fin m) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hr, hcardA])
  let f : ↥A →* alternatingGroup (Fin m) := π.codRestrict _ hmem
  have hf : Function.Surjective f := by
    intro g
    have : (g : Equiv.Perm (Fin m)) ∈ π.range := by rw [hrange]; exact g.2
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  have hfker : f.ker = V := by
    rw [← hker]
    ext a
    simp [f, MonoidHom.mem_ker]
  have hsolv : Group.IsSolvable f.ker := by
    rw [hfker]
    exact Group.isSolvable_of_comm fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2)
  have hE2 : IsE2 k ↥V :=
    PermLat.isElemAbelianOfRank_of_card (fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2))
      (fun a => Subtype.ext (hVsq a.1 a.2)) hVcard
  let e : (↥A ⧸ V) ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact isExt_of_eq_subgroup
    (eq_of_perfect_simple_quotient hB hZ hAZ hcomm hperf hnab f hf hsolv).symm
    (fun V W _ _ e h => IsE2.of_mulEquiv e h) (fun V W _ _ e h => IsAlt.of_mulEquiv e h)
    ⟨V, inferInstance, hE2, ⟨e⟩⟩

theorem isExt_e2_psl32_of_data {T B Z A : Subgroup G} (hB : B ∈ lFamily T) (hZ : B ⊔ T = Z)
    (hAZ : A ≤ Z) (hcomm : ⁅Z, Z⁆ ≤ A) (hperf : ⁅A, A⁆ = A) {k : ℕ} (V : Subgroup ↥A) [V.Normal]
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hVcard : Nat.card V = 2 ^ k) (π : ↥A →* Equiv.Perm (Fin 7)) (hker : π.ker = V)
    (hr : Nat.card π.range = 168) (htr : ∀ i j, ∃ a, π a i = j) :
    IsExt ↥B (fun V _ => IsE2 k V) (fun Y _ => IsPSL 3 2 1 Y) := by
  classical
  have hAperf : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  have hRperf : Group.IsPerfect ↥π.range := Group.IsPerfect.range π
  have hnt : Nontrivial ↥π.range :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  have hns : ¬ Group.IsSolvable ↥π.range := Group.IsPerfect.not_isSolvable _
  have hsimple : IsSimpleGroup ↥π.range := isSimpleGroup_of_card_168 hr hns
  have hnab : ∃ a b : ↥π.range, a * b ≠ b * a :=
    nonabelian_of_simple (by rw [hr]; norm_num)
  let f : ↥A →* ↥π.range := π.rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective π
  have hsolv : Group.IsSolvable f.ker := by
    rw [MonoidHom.ker_rangeRestrict, hker]
    exact Group.isSolvable_of_comm fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2)
  have hPSL : IsPSL 3 2 1 ↥π.range :=
    isPSL_three_two_of_perm_seven hr π.range.subtype (Subgroup.subtype_injective _) fun i j => by
      obtain ⟨a, ha⟩ := htr i j
      exact ⟨⟨π a, a, rfl⟩, ha⟩
  have hE2 : IsE2 k ↥V :=
    PermLat.isElemAbelianOfRank_of_card (fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2))
      (fun a => Subtype.ext (hVsq a.1 a.2)) hVcard
  let e : (↥A ⧸ V) ≃* ↥π.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange π)
  exact isExt_of_eq_subgroup
    (eq_of_perfect_simple_quotient hB hZ hAZ hcomm hperf hnab f hf hsolv).symm
    (fun V W _ _ e h => IsE2.of_mulEquiv e h) (fun V W _ _ e h => IsPSL.of_mulEquiv e h)
    ⟨V, inferInstance, hE2, IsPSL.of_mulEquiv e.symm hPSL⟩

variable {α : Type} [MulAction G α]

theorem e2_alt_of_core {S B Y : Subgroup G} {ol : List G} {t : G} (hB : B ∈ lFamily S)
    (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t)
    (hA : perfectCore Y = Subgroup.closure {x | x ∈ ol})
    (hcomm : ⁅Y, Y⁆ ≤ Subgroup.closure {x | x ∈ ol}) {m : ℕ} (pt : Fin m → α)
    (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) (vl : List G)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol})
    (hVnorm : ∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {x | x ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {x | x ∈ vl})
    (hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) (hvsq : ∀ a ∈ vl, a * a = 1)
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) {r k : ℕ}
    (hE : Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) = r)
    (hN : Nat.card (Subgroup.closure {x | x ∈ ol}) =
      Nat.card (Subgroup.closure {x | x ∈ vl}) * r)
    (hk : Nat.card (Subgroup.closure {x | x ∈ vl}) = 2 ^ k) (hm : 5 ≤ m)
    (hr : r = m.factorial / 2) :
    IsExt ↥B (fun V _ => IsE2 k V) (fun Y _ => IsAlt m Y) := by
  have hperf : ⁅Subgroup.closure {x | x ∈ ol}, Subgroup.closure {x | x ∈ ol}⁆ =
      Subgroup.closure {x | x ∈ ol} := by
    rw [← hA]
    exact perfectCore_perfect Y
  obtain ⟨V', hVn, π, hVc, hVsq, hVcard, hker, -, -, hrcard, hsign⟩ :=
    ext_core hid hperf pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN
  have := hVn
  exact isExt_e2_alt_of_data hB hY ((Subgroup.closure_le Y).mpr fun g hg => hid.mem g hg) hcomm
    hperf hm V' hVc hVsq (hVcard.trans hk) π hker hsign (hrcard.trans hr)

theorem e2_psl32_of_core {S B Y : Subgroup G} {ol : List G} {t : G} (hB : B ∈ lFamily S)
    (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t)
    (hA : perfectCore Y = Subgroup.closure {x | x ∈ ol})
    (hcomm : ⁅Y, Y⁆ ≤ Subgroup.closure {x | x ∈ ol}) {m : ℕ} (hm : m = 7) (pt : Fin m → α)
    (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) (vl : List G)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol})
    (hVnorm : ∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {x | x ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {x | x ∈ vl})
    (hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) (hvsq : ∀ a ∈ vl, a * a = 1)
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) {r k : ℕ}
    (hE : Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) = r)
    (hN : Nat.card (Subgroup.closure {x | x ∈ ol}) =
      Nat.card (Subgroup.closure {x | x ∈ vl}) * r)
    (hk : Nat.card (Subgroup.closure {x | x ∈ vl}) = 2 ^ k) (hr : r = 168)
    (htr : ∀ i j : Fin m, ∃ e ∈ Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}, e i = j) :
    IsExt ↥B (fun V _ => IsE2 k V) (fun Y _ => IsPSL 3 2 1 Y) := by
  subst hm
  have hperf : ⁅Subgroup.closure {x | x ∈ ol}, Subgroup.closure {x | x ∈ ol}⁆ =
      Subgroup.closure {x | x ∈ ol} := by
    rw [← hA]
    exact perfectCore_perfect Y
  obtain ⟨V', hVn, π, hVc, hVsq, hVcard, hker, -, hrange, hrcard, -⟩ :=
    ext_core hid hperf pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN
  have := hVn
  refine isExt_e2_psl32_of_data hB hY ((Subgroup.closure_le Y).mpr fun g hg => hid.mem g hg) hcomm
    hperf V' hVc hVsq (hVcard.trans hk) π hker (hrcard.trans hr) fun i j => ?_
  have := htr i j
  rw [← hrange] at this
  obtain ⟨e, ⟨a, rfl⟩, hej⟩ := this
  exact ⟨a, hej⟩

end CFSG.Quasithin.A312M23
