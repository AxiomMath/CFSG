module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement


theorem le_of_two_group_quotient {Z : Type*} [Group Z] [Finite Z]
    (hZ : ∀ V : Subgroup Z, V.Normal → IsPGroup 2 V → V = ⊥)
    {R N : Subgroup Z} [R.Normal] (hNc : N ≤ Subgroup.center Z)
    (hR : ∀ x ∈ R, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : R ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN' : N.subgroupOf R ≤ Subgroup.center ↥R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hNc hx)) y)
  have : (N.subgroupOf R).Normal := Subgroup.normal_of_le_center hN'
  have hp : IsPGroup 2 (↥R ⧸ N.subgroupOf R) := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hR x.1 x.2
    exact ⟨k, by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk⟩
  have : Group.IsNilpotent (↥R ⧸ N.subgroupOf R) := hp.isNilpotent
  have : Group.IsNilpotent ↥R := Subgroup.isNilpotent_of_ker_le_center
    (QuotientGroup.mk' (N.subgroupOf R)) (by rw [QuotientGroup.ker_mk']; exact hN')
  let P : Sylow 2 ↥R := default
  have hP' : ((P : Subgroup ↥R).map R.subtype).Normal := by
    have : (P : Subgroup ↥R).Characteristic := Sylow.characteristic_of_normal P inferInstance
    infer_instance
  have hbot := hZ _ hP' (P.isPGroup'.map R.subtype)
  have hPbot : (P : Subgroup ↥R) = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp hbot
  have hodd : ¬ 2 ∣ Nat.card ↥R := by
    intro h2
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have h3 := P.card_eq_multiplicity
    rw [hPbot, Subgroup.card_bot] at h3
    rcases Nat.pow_eq_one.mp h3.symm with h | h <;> omega
  intro x hx
  obtain ⟨k, hk⟩ := hR x hx
  have hodd' : Odd (orderOf (⟨x, hx⟩ : ↥R)) := by
    have hdvd := orderOf_dvd_natCard (⟨x, hx⟩ : ↥R)
    rcases Nat.even_or_odd (orderOf (⟨x, hx⟩ : ↥R)) with h | h
    · exact absurd ((even_iff_two_dvd.mp h).trans hdvd) hodd
    · exact h
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime (x := (⟨x, hx⟩ : ↥R))
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd'))
  have h2 : (x ^ 2 ^ k) ^ u = x := congrArg Subtype.val hu
  rw [← h2]
  exact pow_mem hk u

theorem normal_pGroup_quotient_eq_bot {X : Type*} [Group X] [Finite X]
    {V : Subgroup (X ⧸ CFSG.Open.pCore 2 X)} (hV : V.Normal) (h2 : IsPGroup 2 V) : V = ⊥ := by
  have hWn : (V.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))).Normal := hV.comap _
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.Open.pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hW2 := h2.comap_of_ker_isPGroup (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) hker
  have hWle := CFSG.LieType.BorelTits.le_pCore 2 hWn hW2
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  exact (QuotientGroup.eq_one_iff x).mpr (hWle (Subgroup.mem_comap.mpr hv))

section Levi

variable {F : Type} [Field F] [Finite F] {m : ℕ}

omit [Field F] in
theorem exists_four (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) : ∃ s : Finset F, s.card = 4 := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
  rw [hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem normal_pGroup_le_ker (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) {Y : Type*} [Group Y]
    (ψ : Y →* SL(2, F)) (hψ : Function.Surjective ψ) {V : Subgroup Y} [V.Normal]
    (hV : IsPGroup 2 V) : V ≤ ψ.ker := by
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hK4 := exists_four hm hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  have hnab := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
  have hn : (V.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map ψ) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h2 : IsPGroup 2 SL(2, F) := by
      have := hV.map ψ
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnab
    have : Group.IsNilpotent SL(2, F) := h2.isNilpotent
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

theorem two_dvd_card_sl (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) : 2 ∣ Nat.card SL(2, F) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem false_of_normal_sylow (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) {W : Type*} [Group W]
    (g : W →* SL(2, F)) (hg : Function.Surjective g) {V : Subgroup W} [V.Normal]
    (hV : IsPGroup 2 V) (hodd : ¬ 2 ∣ V.index) : False := by
  have hle := normal_pGroup_le_ker hm hF g hg hV
  have h1 : V.map g = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hle
  have h2 := Subgroup.index_map_dvd V hg
  rw [h1, Subgroup.index_bot] at h2
  exact hodd ((two_dvd_card_sl (by omega) hF).trans h2)

end Levi


section Cover

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem isL2Quot_of_levi_cover (hm : 2 ≤ m) {Y : Type} [Group Y] [Finite Y]
    (hF : Nat.card F = 2 ^ m) (hperf : Group.IsPerfect Y) (ψ : Y →* SL(2, F))
    (hψ : Function.Surjective ψ) (N : Subgroup Y) [N.Normal]
    (hRN : ∀ x ∈ ψ.ker, ∃ k : ℕ, x ^ 2 ^ k ∈ N)
    (hN : ∀ n ∈ N, ∀ y : Y, ⁅n, y⁆ ∈ CFSG.Open.pCore 2 Y) :
    IsL2Quot m (Y ⧸ CFSG.Open.pCore 2 Y) ∧ Group.IsSolvable ψ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : (CFSG.Open.pCore 2 Y).Normal := inferInstance
  have hO2 : IsPGroup 2 (CFSG.Open.pCore 2 Y) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hOker : CFSG.Open.pCore 2 Y ≤ ψ.ker := normal_pGroup_le_ker hm hF ψ hψ hO2
  let ψ' : Y ⧸ CFSG.Open.pCore 2 Y →* SL(2, F) := QuotientGroup.lift _ ψ hOker
  have hψ' : Function.Surjective ψ' := fun w => by
    obtain ⟨y, rfl⟩ := hψ w
    exact ⟨QuotientGroup.mk y, rfl⟩
  let Nb : Subgroup (Y ⧸ CFSG.Open.pCore 2 Y) := N.map (QuotientGroup.mk' _)
  have hNc : Nb ≤ Subgroup.center (Y ⧸ CFSG.Open.pCore 2 Y) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 Y)) ⁅n, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hN n hn y)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hR : ∀ x ∈ ψ'.ker, ∃ k : ℕ, x ^ 2 ^ k ∈ Nb := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : ψ y = 1 := hx
    obtain ⟨k, hk⟩ := hRN y hy
    exact ⟨k, ⟨y ^ 2 ^ k, hk, by simp [QuotientGroup.mk_pow]⟩⟩
  have hle : ψ'.ker ≤ Nb := le_of_two_group_quotient
    (fun V hV h2 => normal_pGroup_quotient_eq_bot hV h2) hNc hR
  have hcen : ψ'.ker ≤ Subgroup.center (Y ⧸ CFSG.Open.pCore 2 Y) := hle.trans hNc
  have : Group.IsPerfect Y := hperf
  refine ⟨isL2Quot_of_oddCover hm hF inferInstance ψ' hψ' hcen
    (fun x hx => Case2a.odd_orderOf_of_central (hcen hx)), ?_⟩
  let θ : ↥ψ.ker →* ↥(Subgroup.center (Y ⧸ CFSG.Open.pCore 2 Y)) :=
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 Y)).comp (ψ.ker).subtype).codRestrict _ (by
      intro x
      refine hcen ?_
      show ψ' (QuotientGroup.mk (x : Y)) = 1
      exact x.2)
  have hOR : (CFSG.Open.pCore 2 Y).subgroupOf ψ.ker ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hx
  have hker : θ.ker ≤ ((CFSG.Open.pCore 2 Y).subgroupOf ψ.ker).subtype.range := by
    intro x hx
    have h' : (QuotientGroup.mk (x : Y) : Y ⧸ CFSG.Open.pCore 2 Y) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff (x : Y)).mp h')⟩, rfl⟩
  have hP : IsPGroup 2 ↥((CFSG.Open.pCore 2 Y).subgroupOf ψ.ker) :=
    hO2.of_equiv (Subgroup.subgroupOfEquivOfLe hOker).symm
  have : Group.IsNilpotent ↥((CFSG.Open.pCore 2 Y).subgroupOf ψ.ker) := hP.isNilpotent
  exact Group.isSolvable_of_ker_le_range _ θ hker

end Cover

end CFSG.Quasithin.F146Field.Case2b
