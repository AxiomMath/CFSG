module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LD
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.Quasithin.Vol2.Ch10SecQ34LC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

section PSL

variable {A : Type*} [Group A] {p : ℕ} [hp : Fact p.Prime]

theorem center_eq_bot_of_mulEquiv (e : A ≃* PSL(2, ZMod p)) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h := mem_center_of_mulEquiv e (Subgroup.mem_center_iff.mp ha)
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot (ZMod p), Subgroup.mem_bot] at h
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h, map_one])

theorem isOddPrimePower_card (hp2 : p ≠ 2) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, hp.out, hp.out.odd_of_ne_two hp2, le_rfl, by rw [Nat.card_zmod, pow_one]⟩

theorem centralizer_eq_of_kleinFour (hp2 : p ≠ 2) (e : A ≃* PSL(2, ZMod p)) {V : Subgroup A}
    (hV : IsKleinFour ↥V) : Subgroup.centralizer (V : Set A) = V := by
  have hV' := CFSG.GorensteinWalter.isKleinFour_map_of_injective V hV e.toMonoidHom e.injective
  have h := CFSG.GorensteinWalter.psl2_kleinFour_centralizer_eq_self (ZMod p)
    (isOddPrimePower_card hp2) _ hV'
  refine le_antisymm (fun a ha => ?_) fun v hv => ?_
  · have hea : e a ∈ Subgroup.centralizer ((V.map e.toMonoidHom : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp ha w hw
      change e w * e a = e a * e w
      rw [← map_mul, ← map_mul, this]
    rw [h] at hea
    obtain ⟨w, hw, hwa⟩ := hea
    have : w = a := e.injective hwa
    exact this ▸ hw
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hc := isMulCommutative_iff.mp hV.isMulCommutative ⟨w, hw⟩ ⟨v, hv⟩
    exact congrArg Subtype.val hc

theorem exists_dihedral_of_sylow [Finite A] (hp2 : p ≠ 2) (e : A ≃* PSL(2, ZMod p))
    {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup (PSL(2, ZMod p)) := S.map (e : A →* PSL(2, ZMod p)) with hS'
  have h2 : IsPGroup 2 ↥S' := hS.2.1.map _
  have hidx : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_map_equiv]
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  obtain ⟨m, hm, ⟨eP⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p)
    (isOddPrimePower_card hp2) (h2.toSylow hidx)
  exact ⟨m, hm, ⟨(Subgroup.equivMapOfInjective S (e : A →* PSL(2, ZMod p)) e.injective).trans eP⟩⟩

theorem sixteen_dvd_sq_sub_one {q : ℕ} (h8 : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q ^ 2 - 1 := by
  have h16 : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
  have hsq : q ^ 2 % 16 = 1 % 16 := by
    rw [Nat.pow_mod]
    rcases h16 with h | h | h | h <;> simp [h]
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hsq)

theorem eight_dvd_card_sylow [Finite A] (h8 : p % 8 = 1 ∨ p % 8 = 7) (e : A ≃* PSL(2, ZMod p))
    {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) : 8 ∣ Nat.card S := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hcard := CFSG.GorensteinWalter.psl2_card_formula (ZMod p) (isOddPrimePower_card hp2)
  rw [Nat.card_zmod] at hcard
  obtain ⟨c, hc⟩ := sixteen_dvd_sq_sub_one h8
  have hA : Nat.card A = 8 * (p * c) := by
    rw [Nat.card_congr e.toEquiv, hcard, hc, show p * (16 * c) = 2 * (8 * (p * c)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hmul := S.card_mul_index
  have hidx : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  have hcop : Nat.Coprime 8 S.index :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [hmul, hA]
  exact dvd_mul_right 8 _

end PSL

section Elements

variable {A : Type*} [Group A]

theorem eq_one_of_odd_of_isPGroup {P : Subgroup A} (hP : IsPGroup 2 P) {a : A} (haP : a ∈ P)
    (hodd : Odd (orderOf a)) : a = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨a, haP⟩
  have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · rw [hj] at hodd
    exact absurd (Nat.even_pow.mpr ⟨even_two, by omega⟩) (Nat.not_even_iff_odd.mpr hodd)

theorem mem_normalizer_of_forall_conj_mem [Finite A] {U : Subgroup A} {g : A}
    (h : ∀ u ∈ U, g * u * g⁻¹ ∈ U) : g ∈ Subgroup.normalizer (U : Set A) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply] using h u hu
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem alt4_sq_of_pow_four : ∀ y : alternatingGroup (Fin 4), y ^ 4 = 1 → y ^ 2 = 1 := by
  decide

theorem card_alt4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_pCoreOf_eq_four [Finite A] {Y : Subgroup A} (hY : Nat.card Y = 12)
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) : Nat.card (pCoreOf 2 Y) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 2 (n := 2)
    (by rw [hY]; norm_num)
  have h2 : ∀ y ∈ Y, ∀ k : ℕ, y ^ 2 ^ k = 1 → y ∈ pCoreOf 2 Y := by
    intro y hy k hk
    have hcop : Nat.Coprime 3 (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
        (Nat.Coprime.pow_right k (by norm_num))
    exact (Subgroup.zpowers_le.mpr (hY3 y hy)) (A4.mem_zpowers_pow_of_coprime hcop)
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card hP
  have hle : P.map Y.subtype ≤ pCoreOf 2 Y := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hP2 ⟨q, hq⟩
    exact h2 q q.2 k (congrArg (fun z : ↥P => ((z : ↥Y) : A)) hk)
  have hcardP : Nat.card ↥(P.map Y.subtype) = 4 := by
    rw [← Nat.card_congr (P.equivMapOfInjective _ Y.subtype_injective).toEquiv, hP]
    norm_num
  have h4 : 4 ∣ Nat.card ↥(pCoreOf 2 Y) := hcardP ▸ Subgroup.card_dvd_of_le hle
  have h12 : Nat.card ↥(pCoreOf 2 Y) ∣ 12 :=
    hY ▸ Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  rw [hk] at h4 h12 ⊢
  have hk3 : k < 3 := by
    by_contra h
    have := (Nat.pow_dvd_pow 2 (show 3 ≤ k by omega)).trans h12
    norm_num at this
  interval_cases k
  · norm_num at h4
  · norm_num at h4
  · norm_num

theorem conjAutHom_eq_one_iff {V : Subgroup A} (a : ↥(Subgroup.normalizer (V : Set A))) :
    conjAutHom V a = 1 ↔ (a : A) ∈ Subgroup.centralizer (V : Set A) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : A)) h
    simp only [conjAutHom_apply, MulAut.one_apply] at h1
    calc v * (a : A) = (a : A) * v * (a : A)⁻¹ * a := by rw [h1]
      _ = a * v := by group
  · intro ha
    ext v
    rw [conjAutHom_apply, MulAut.one_apply]
    rw [← Subgroup.mem_centralizer_iff.mp ha v v.2]
    group

theorem relIndex_centralizer_dvd_two [Finite A] {S Y : Subgroup A} (hY : Nat.card Y = 3)
    (hSY : S ≤ Subgroup.normalizer (Y : Set A)) :
    (S ⊓ Subgroup.centralizer (Y : Set A)).relIndex S ∣ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥S →* MulAut ↥Y := (conjAutHom Y).comp (Subgroup.inclusion hSY) with hφ
  have hker : φ.ker = (S ⊓ Subgroup.centralizer (Y : Set A)).subgroupOf S := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hφ, MonoidHom.comp_apply,
      conjAutHom_eq_one_iff]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hcard : Nat.card (MulAut ↥Y) = 2 := by
    have : IsCyclic ↥Y := isCyclic_of_prime_card hY
    rw [IsCyclic.card_mulAut, hY, Nat.totient_prime Nat.prime_three]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, ← hcard]
  exact Subgroup.card_subgroup_dvd_card φ.range

end Elements

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
