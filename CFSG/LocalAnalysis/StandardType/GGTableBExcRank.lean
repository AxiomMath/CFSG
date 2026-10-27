module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc

variable (τ : Tag) (K : Type) [Field K]

@[expose] def torusPow (p : ℕ) : Subgroup (adjointGroup τ K) where
  carrier := {g | (g : ModGL τ K) ∈ torusGroup τ K ∧ g ^ p = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := Subtype.ext
      (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha.1)
        (torusGroup_le_diagonalGroup hb.1))
    rw [hc.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

variable {τ K}

theorem mem_torusPow {p : ℕ} {g : adjointGroup τ K} :
    g ∈ torusPow τ K p ↔ (g : ModGL τ K) ∈ torusGroup τ K ∧ g ^ p = 1 :=
  Iff.rfl

@[expose] noncomputable def torusPowElt (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K)
    (p : ℕ) (ζ : Kˣ) (x : Fin τ.rank → ZMod p) : adjointGroup τ K :=
  ⟨rootDiagUnit τ fun i => ζ ^ (x i).val,
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (hfull _)⟩

theorem coe_torusPowElt (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K)
    (p : ℕ) (ζ : Kˣ) (x : Fin τ.rank → ZMod p) :
    (torusPowElt hfull p ζ x : ModGL τ K) = rootDiagUnit τ fun i => ζ ^ (x i).val :=
  rfl

theorem bijective_torusPowElt (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K)
    {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) :
    (∀ x, torusPowElt hfull p ζ x ∈ torusPow τ K p) ∧ Function.Injective (torusPowElt hfull p ζ) ∧
      ∀ g ∈ torusPow τ K p, ∃ x, torusPowElt hfull p ζ x = g := by
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine ⟨fun x => ⟨hfull _, Subtype.ext ?_⟩, fun x y hxy => ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_pow, coe_torusPowElt, rootDiagUnit_pow, OneMemClass.coe_one,
      ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  · funext i
    have h := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) hxy
    simp only [coe_torusPowElt] at h
    exact CFSG.RankThree.Chevalley.eq_of_pow_val_eq_pow_val hζ
      (congrFun (rootDiagUnit_injective h) i)
  · obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg.1
    have hap' : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [← rootDiagUnit_pow, ← ha, rootDiagUnit_one, ← Subgroup.coe_pow, hg.2,
        OneMemClass.coe_one]
    have hap : a ^ p = 1 := rootDiagUnit_injective hap'
    have hai : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun hap i
    choose m hm using fun i =>
      CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζ (hai i)
    refine ⟨m, Subtype.ext ?_⟩
    rw [coe_torusPowElt, ha]
    congr 1
    exact funext hm

theorem card_torusPow_of_full [Finite K]
    (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow τ K p) = p ^ τ.rank := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  obtain ⟨hmem, hinj, hsurj⟩ := bijective_torusPowElt hfull hζo
  let e : (Fin τ.rank → ZMod p) ≃ torusPow τ K p :=
    Equiv.ofBijective (fun x => ⟨torusPowElt hfull p ζ x, hmem x⟩)
      ⟨fun x y h => hinj (congrArg Subtype.val h), fun g => by
        obtain ⟨x, hx⟩ := hsurj g g.2
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem full_of_E7_E8 [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ torusGroup τ K :=
  (even_power_two_Cartan_root_diagonals_inner τ (Or.inr (Or.inr (Or.inr hτ))) K
    (ringChar.eq K 2)).1 a

theorem card_torusPow_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow .E8 K p) = p ^ 8 :=
  card_torusPow_of_full (full_of_E7_E8 (Or.inr rfl)) hp hpq

theorem card_torusPow_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow .E7 K p) = p ^ 7 :=
  card_torusPow_of_full (full_of_E7_E8 (Or.inl rfl)) hp hpq

theorem exists_conj_le_torusPow [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E) :
    ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom ≤ torusPow τ K p := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  refine ⟨g, fun x hx => ⟨Subgroup.mem_subgroupOf.mp (hg hx), ?_⟩⟩
  obtain ⟨e, he, rfl⟩ := hx
  rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 e he, map_one]

end TableBExc

open TableBExc in
@[expose] def GGExcToralRankInput (τ : Tag) (K : Type) [Field K]
    (p : ℕ) : Prop :=
  ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ τ.rank ≤ Nat.card E →
    ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom = torusPow τ K p

open TableBExc in
theorem GGExcToralRankInput.card_le {τ : Tag} {K : Type} [Field K]
    {p : ℕ} (h : GGExcToralRankInput τ K p)
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) {E : Subgroup (adjointGroup τ K)}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ τ.rank := by
  by_contra hlt
  obtain ⟨g, hg⟩ := h E hE (not_le.mp hlt).le
  have h1 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hg, hV] at h1
  omega

namespace TableBExc

variable {τ : Tag} {K : Type} [Field K]

theorem ggExcToralRankInput_of_not_dvd_index [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) : GGExcToralRankInput τ K p := by
  intro E hE hcard
  obtain ⟨g, hg⟩ := exists_conj_le_torusPow hp hidx hE
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [hV, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hcard

theorem geomSum_cast {p q : ℕ} (hq1 : (q : ZMod p) = 1) (n s : ℕ) :
    (CFSG.Timmesfeld.ExceptionalOrders.geomSum n s q : ZMod p) = n := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.geomSum]
  push_cast
  simp [hq1]

theorem cast_eq_one_of_dvd_sub_one {p q : ℕ} (hq : 1 ≤ q) (hpq : p ∣ q - 1) :
    (q : ZMod p) = 1 := by
  have h := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hpq
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
  exact h

theorem not_dvd_smooth {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (a b c d : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp
        (hp.dvd_of_dvd_pow h)
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow h)
    omega


theorem index_torusGroup_eq [Finite K] {M : ℕ}
    (hC : Nat.card (adjointGroup τ K) = Nat.card (torusGroup τ K) * M) :
    ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index = M := by
  have hcard := Subgroup.card_mul_index ((torusGroup τ K).subgroupOf (adjointGroup τ K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup).toEquiv, hC] at hcard
  have hpos : 0 < Nat.card (torusGroup τ K) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hcard

theorem not_dvd_index_torusGroup_E8 [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .E8 K).subgroupOf (adjointGroup .E8 K)).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [index_torusGroup_eq (by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
      CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8,
      ← CFSG.Timmesfeld.ExceptionalOrders.ordE8_eq _ hq, mul_assoc])]
  have hq1 := cast_eq_one_of_dvd_sub_one hq hpq
  have hW := not_dvd_smooth hp hp11 14 5 2 1
  rw [← ZMod.natCast_eq_zero_iff] at hW ⊢
  intro h
  apply hW
  rw [← h]
  push_cast
  simp only [geomSum_cast hq1, hq1, one_pow]
  norm_num

theorem not_dvd_index_torusGroup_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .E7 K).subgroupOf (adjointGroup .E7 K)).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hodd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).1 h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h3
  have hH : Nat.card (torusGroup .E7 K) = (Nat.card K - 1) ^ 7 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
    rwa [Nat.gcd_comm, hodd, mul_one] at h
  rw [index_torusGroup_eq (M := Nat.card K ^ 63 * _) (by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hH, CFSG.Open.ordE7, hodd,
      Nat.div_one, ← CFSG.Timmesfeld.ExceptionalOrders.ordE7_mul _ hq, mul_assoc])]
  have hq1 := cast_eq_one_of_dvd_sub_one hq hpq
  have hW := not_dvd_smooth hp hp11 10 4 1 1
  rw [← ZMod.natCast_eq_zero_iff] at hW ⊢
  intro h
  apply hW
  rw [← h]
  push_cast
  simp only [geomSum_cast hq1, hq1, one_pow]
  norm_num

theorem ggExcToralRankInput_E8_of_eleven_le [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput .E8 K p :=
  ggExcToralRankInput_of_not_dvd_index hp (not_dvd_index_torusGroup_E8 hp hp11 hpq)
    (card_torusPow_E8 hp hpq)

theorem ggExcToralRankInput_E7_of_eleven_le [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput .E7 K p :=
  ggExcToralRankInput_of_not_dvd_index hp (not_dvd_index_torusGroup_E7 hp hp11 hpq)
    (card_torusPow_E7 hp hpq)

end TableBExc

end CFSG.StandardType
