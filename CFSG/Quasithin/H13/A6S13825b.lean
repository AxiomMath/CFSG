module

public import CFSG.Quasithin.H13.A6S13825p
public import CFSG.Quasithin.H13.A6S1372L76F
public import CFSG.Quasithin.H13.A5W1623a
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.SBd8.Flag

namespace L13825

section Transport

variable {Y : Type} [Group Y] {n : ℕ} {K : Subgroup Y}
  (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2))

@[expose] def toSL (X : Subgroup Y) : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  (X.subgroupOf K).map e.toMonoidHom

@[expose] def ofSL (P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) : Subgroup Y :=
  (P.map e.symm.toMonoidHom).map K.subtype

theorem mem_toSL {X : Subgroup Y} {y : SpecialLinearGroup (Fin n) (ZMod 2)} :
    y ∈ toSL e X ↔ ((e.symm y : ↥K) : Y) ∈ X := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using Subgroup.mem_subgroupOf.mp hk
  · intro h
    exact ⟨e.symm y, Subgroup.mem_subgroupOf.mpr h, by simp⟩

theorem ofSL_le (P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) : ofSL e P ≤ K :=
  Subgroup.map_subtype_le _

theorem ofSL_mono {P P' : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (h : P ≤ P') :
    ofSL e P ≤ ofSL e P' :=
  Subgroup.map_mono (Subgroup.map_mono h)

theorem toSL_mono {X Z : Subgroup Y} (h : X ≤ Z) : toSL e X ≤ toSL e Z := fun _ hy =>
  (mem_toSL e).mpr (h ((mem_toSL e).mp hy))

theorem ofSL_toSL {X : Subgroup Y} (hXK : X ≤ K) : ofSL e (toSL e X) = X := by
  ext x
  constructor
  · rintro ⟨k, ⟨y, hy, rfl⟩, rfl⟩
    exact (mem_toSL e).mp hy
  · intro hx
    refine ⟨⟨x, hXK hx⟩, ⟨e ⟨x, hXK hx⟩, (mem_toSL e).mpr (by simpa using hx), by simp⟩, rfl⟩

theorem card_ofSL (P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
    Nat.card ↥(ofSL e P) = Nat.card ↥P := by
  rw [ofSL, Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective]

theorem card_toSL {X : Subgroup Y} (hXK : X ≤ K) : Nat.card ↥(toSL e X) = Nat.card ↥X := by
  rw [toSL, Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv

theorem toSL_sup {X Z : Subgroup Y} (hXK : X ≤ K) (hZK : Z ≤ K) :
    toSL e (X ⊔ Z) = toSL e X ⊔ toSL e Z := by
  rw [toSL, toSL, toSL, Subgroup.subgroupOf_sup hXK hZK, Subgroup.map_sup]

theorem isSolvable_ofSL_iff (P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
    Group.IsSolvable ↥(ofSL e P) ↔ Group.IsSolvable ↥P := by
  have e1 : ↥P ≃* ↥(P.map e.symm.toMonoidHom) :=
    P.equivMapOfInjective _ e.symm.injective
  have e2 : ↥(P.map e.symm.toMonoidHom) ≃* ↥(ofSL e P) :=
    (P.map e.symm.toMonoidHom).equivMapOfInjective _ K.subtype_injective
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := (e1.trans e2).toMonoidHom)
      (MulEquiv.injective _)
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := (e1.trans e2).symm.toMonoidHom)
      (MulEquiv.injective _)

theorem isSolvable_toSL {X : Subgroup Y} (hXK : X ≤ K) (hX : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥(toSL e X) := by
  have h1 : Group.IsSolvable ↥(X.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom) (MulEquiv.injective _)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap (X.subgroupOf K))
    (MonoidHom.subgroupMap_surjective _ _)

theorem le_normalizer_toSL {P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    {X : Subgroup Y} (h : ofSL e P ≤ Subgroup.normalizer (X : Set Y)) :
    P ≤ Subgroup.normalizer (toSL e X : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  intro p hp
  have hk : ((e.symm p : ↥K) : Y) ∈ Subgroup.normalizer (X : Set Y) :=
    h ⟨e.symm p, ⟨p, hp, rfl⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_toSL, mem_toSL, map_mul, map_mul, map_inv]
  simpa using Subgroup.mem_normalizer_iff.mp hk ((e.symm y : ↥K) : Y)

end Transport

variable {G : Type} [Group G] [Finite G]

theorem not_nine_dvd_of_decomp {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 2 ↥P) {c : G}
    (hcX : c ∈ X) (hdec : ∀ x ∈ X, x ∈ P ∨ c * c * x ∈ P ∨ c * x ∈ P) : ¬ 9 ∣ Nat.card ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥P × Fin 3 → ↥X := fun pi =>
    if pi.2 = 0 then ⟨pi.1, hPX pi.1.2⟩
    else if pi.2 = 1 then ⟨(c * c)⁻¹ * pi.1, X.mul_mem (X.inv_mem (X.mul_mem hcX hcX)) (hPX pi.1.2)⟩
    else ⟨c⁻¹ * pi.1, X.mul_mem (X.inv_mem hcX) (hPX pi.1.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hdec x hx with h | h | h
    · exact ⟨(⟨x, h⟩, 0), by simp [f]⟩
    · refine ⟨(⟨c * c * x, h⟩, 1), ?_⟩
      simp only [f]
      exact Subtype.ext (by simp [mul_assoc])
    · refine ⟨(⟨c * x, h⟩, 2), ?_⟩
      simp only [f]
      exact Subtype.ext (by simp)
  have hle : Nat.card ↥X ≤ Nat.card ↥P * 3 := by
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
  obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le hPX
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hpos : 0 < Nat.card ↥P := Nat.card_pos
  have hi3 : i ≤ 3 := by
    rw [hi] at hle
    exact Nat.le_of_mul_le_mul_left hle hpos
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, mul_zero] at hi
      exact absurd hi (Nat.card_pos (α := ↥X)).ne'
    · exact h
  intro h9
  rw [hi, hk] at h9
  have hc : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have := Nat.le_of_dvd hi0 (hc.dvd_of_dvd_mul_left h9)
  omega

theorem not_nine_dvd_sup {X T : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT : IsPGroup 2 ↥T) (h9 : ¬ 9 ∣ Nat.card ↥X) : ¬ 9 ∣ Nat.card ↥(X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have h1 := h.trans (CFSG.Quasithin.H13.Ln2P.card_sup_dvd_mul X T hTX)
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk] at h1
  exact h9 ((Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h1)

theorem nine_dvd_of_two_le_pRank {X : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 3 X) :
    9 ∣ Nat.card ↥X := by
  set s : Set ℕ := {k | ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ k}
    with hs
  have hp : CFSG.Open.pRank 3 X = sSup s := rfl
  have hne : s.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hp, hne, csSup_empty] at h
    exact absurd h (by simp)
  have hbdd : BddAbove s := ⟨Nat.card G, fun k hk => by
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : 3 ^ k ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega⟩
  obtain ⟨E, hEX, -, hE⟩ := Nat.sSup_mem hne hbdd
  rw [← hp] at hE
  have h9 : 9 ∣ Nat.card ↥E := by
    rw [hE, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 h
  exact h9.trans (Subgroup.card_dvd_of_le hEX)

variable {T L V : Subgroup G}

theorem three_dvd_card_kst (S : Setting4 G T L V) {H : Subgroup G}
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G} (hXH : X ≤ H) {c : G} (hc : c ∈ X)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) : 3 ∣ Nat.card ↥(S.KSt H X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [S.kst_eq hF hXH]
  set y : ↥((X.subgroupOf H).map (S1549C.starHom hF)) :=
    ⟨S1549C.starHom hF ⟨c, hXH hc⟩, ⟨c, hXH hc⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩ with hy
  have hc' : (⟨c, hXH hc⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    show (S1549C.starHom hF ⟨c, hXH hc⟩) ^ 3 = 1
    rw [← map_pow, hc', map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : S1549C.starHom hF ⟨c, hXH hc⟩ = 1 := congrArg Subtype.val h
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
      ⟨_, (S1549C.starHom_eq_one_iff hF _).1 h1⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc' : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hk')
      (orderOf_dvd_of_pow_eq_one hc3)
    exact hc1 (orderOf_eq_one_iff.mp hc')
  rw [← orderOf_eq_prime hy3 hy1]
  exact orderOf_dvd_natCard y

theorem nine_dvd_card_kst (S : Setting4 G T L V) {H : Subgroup G}
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {X : Subgroup G} (hXH : X ≤ H)
    (h9 : 9 ∣ Nat.card ↥X) : 9 ∣ Nat.card ↥(S.KSt H X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hF.card_autOn_tilde hXH]
  have h1 := ((X ⊓ pCoreOf 2 H).subgroupOf X).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  obtain ⟨k, hk⟩ := ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
    (inf_le_right : X ⊓ pCoreOf 2 H ≤ pCoreOf 2 H)).exists_card_eq
  rw [← h1, hk] at h9
  exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_left h9

open Setting4 in
theorem star_setup (h21 : Lem13821) (h16 : Lem13816) {S : Setting4 G T L V} (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn : 1 ≤ n)
    (hKn : IsPSL n 2 1 ↥(S.KSt H K)) :
    S.KSt H K ≤ S.KSt H H ∧ S.KSt H H ≤ Subgroup.normalizer (S.KSt H K : Set _) ∧
      S.KSt H T ≤ S.KSt H H ∧ S.KSt H H ≤ S.KSt H K ⊔ S.KSt H T ∧
      S.KSt H H ⊓ Subgroup.centralizer (S.KSt H K : Set _) = ⊥ ∧
      ∃ e : ↥(S.KSt H K) ≃* SpecialLinearGroup (Fin n) (ZMod 2),
        ((S.KSt H T ⊓ S.KSt H K).subgroupOf (S.KSt H K)).map e.toMonoidHom =
          unitriangular n (ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKT : K ⊔ T = H := (h21 G T L V S hS H hH K hK).2.2.1.1
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKsHs : S.KSt H K ≤ S.KSt H H := S.kst_mono hF hKH le_rfl
  have hHsN : S.KSt H H ≤ Subgroup.normalizer (S.KSt H K : Set _) :=
    S.kst_le_normalizer hF hKH le_rfl hKnH
  have hTsHs : S.KSt H T ≤ S.KSt H H := S.kst_mono hF hTH le_rfl
  have hHsKT : S.KSt H H ≤ S.KSt H K ⊔ S.KSt H T := by
    rw [← congrArg (S.KSt H) hKT, S.kst_sup hF hKH hTH]
  have hTs2 : IsPGroup 2 ↥(S.KSt H T) := S.kst_isPGroup hF hTH hTsyl.2.1
  have hTsyl' : IsSylowTwoOf (S.KSt H T) (S.KSt H H) := S.isSylowTwoOf_kst hF hTH hTsyl
  have hTK : IsSylowTwoOf (S.KSt H T ⊓ S.KSt H K) (S.KSt H K) :=
    CFSG.Quasithin.SzN19.isSylowTwoOf_inf_of_normalizes hTsyl' hKsHs (hTsHs.trans hHsN) hHsKT
  obtain ⟨e₀⟩ := CFSG.Quasithin.FLc.nonempty_equiv_SLt_of_isPSL hKn
  have hZ : ∀ k ∈ S.KSt H K, (∀ k' ∈ S.KSt H K, k * k' = k' * k) → k = 1 := by
    intro k hk hcomm
    have hc : e₀ ⟨k, hk⟩ ∈ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨⟨y', hy'⟩, rfl⟩ := e₀.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm y' hy').symm
    rw [← scalars_eq_center, G11.P4GL.scalars_trivial, Subgroup.mem_bot] at hc
    have := congrArg Subtype.val (e₀.injective (hc.trans (map_one e₀).symm))
    simpa using this
  have hC := inf_centralizer_eq_bot hHsN hHsKT hTsHs hTs2 hZ (S.kst_O2 hF)
  obtain ⟨e, he⟩ := exists_std_equiv hn hTK e₀
  exact ⟨hKsHs, hHsN, hTsHs, hHsKT, hC, e, he⟩

theorem mem_normalizer_sup {Y : Type} [Group Y] {A B : Subgroup Y} {g : Y}
    (hA : g ∈ Subgroup.normalizer (A : Set Y)) (hB : g ∈ Subgroup.normalizer (B : Set Y)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  rw [← CFSG.Quasithin.A38.map_conj_eq_iff] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem exists_order_three_L1 (S : Setting4 G T L V) :
    ∃ c ∈ S.L1, c ^ 3 = 1 ∧ c ≠ 1 := by
  by_cases hhat : IsHatA6 L
  · obtain ⟨c, hc, hc3, hcO, -⟩ := l0_decomp hhat
    exact ⟨c, S.l0_le_L1 hc, hc3, fun h => hcO (by rw [h]; exact Subgroup.one_mem _)⟩
  · exact ⟨S.cL1 hhat, S.cL1_mem hhat, S.cL1_cube hhat,
      fun h => S.cL1_not_mem hhat (by rw [h]; exact Subgroup.one_mem _)⟩

open Setting4 in
theorem false_of_pbShape (h21 : Lem13821) {S : Setting4 G T L V} (hS : S.Hyp138)
    (hno3 : ∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 3 2 1 ↥(S.KSt H' K'))
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} {n : ℕ}
    (e : ↥(S.KSt H K) ≃* SpecialLinearGroup (Fin n) (ZMod 2))
    (he : ((S.KSt H T ⊓ S.KSt H K).subgroupOf (S.KSt H K)).map e.toMonoidHom =
      unitriangular n (ZMod 2))
    (hKsHs : S.KSt H K ≤ S.KSt H H) (hTK : S.KSt H T ≤ S.KSt H K)
    (hLK : S.KSt H S.L1 ≤ S.KSt H K) (hLs : Group.IsSolvable ↥(S.KSt H S.L1)) {C : Set ℕ}
    (hQ : toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) = flagStabilizer n (ZMod 2) C)
    (hpb : PBShape n C) : False := by
  obtain ⟨C', hle, hns, h5, h27, hNN⟩ := hpb
  have hTTK : S.KSt H T ⊓ S.KSt H K = S.KSt H T := inf_eq_left.mpr hTK
  have hU : toSL e (S.KSt H T ⊓ S.KSt H K) = unitriangular n (ZMod 2) := he
  have hR : toSL e (S.KSt H S.L1) ⊔ unitriangular n (ZMod 2) = flagStabilizer n (ZMod 2) C := by
    rw [← hU, ← toSL_sup e hLK inf_le_right, hQ]
  refine false_of_pb h21 hS hno3 hH (P := ofSL e (flagStabilizer n (ZMod 2) C'))
    ((ofSL_le e _).trans hKsHs) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← ofSL_toSL e hLK]
    exact ofSL_mono e ((le_sup_left.trans hR.le).trans hle)
  · rw [← hTTK, ← ofSL_toSL e (inf_le_right : S.KSt H T ⊓ S.KSt H K ≤ _), hU]
    exact ofSL_mono e ((le_sup_right.trans hR.le).trans hle)
  · rwa [isSolvable_ofSL_iff]
  · intro hN
    exact hNN _ (isSolvable_toSL e hLK hLs) hR (le_normalizer_toSL e hN)
  · rwa [card_ofSL]
  · rwa [card_ofSL]

end L13825

open L13825 Setting4 in
theorem lem13825NoL3_of (h21 : Lem13821) (h16 : Lem13816)
    (h1334 : Stmt13_3_4) : Lem13825NoL3 := by
  intro G _ _ T L V S hS H hH K hK _ hK3
  obtain ⟨hKsHs, hHsN, hTsHs, hHsKT, hC, e, he⟩ := star_setup h21 h16 hS hH hK (by norm_num) hK3
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  obtain ⟨hL1K, -, ⟨-, hAut⟩, -⟩ := h21 G T L V S hS H hH K hK
  have hTK : ¬ S.KSt H T ≤ S.KSt H K := by
    intro hTK
    obtain ⟨φ⟩ := hAut hK3
    have h336 : Nat.card ↥(S.KSt H H) = 336 := by
      rw [Nat.card_congr φ.toEquiv,
        Nat.card_congr (MulAut.congr (e.trans (G11.P4GL.slEquiv 3))).toEquiv]
      exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32
    have h168 : Nat.card ↥(S.KSt H K) = 168 := by
      rw [Nat.card_congr e.toEquiv, card_SL_three]
    have := Subgroup.card_le_of_le (hHsKT.trans (sup_le le_rfl hTK))
    omega
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ S.KSt H T, t ∉ S.KSt H K := by
    by_contra hne
    exact hTK fun t ht => by_contra fun h => hne ⟨t, ht, h⟩
  have hLK : S.KSt H S.L1 ≤ S.KSt H K := S.kst_mono hF hL1K hKH
  have hBK : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H K := sup_le hLK inf_le_right
  have hUB : upperTriangular 3 (ZMod 2) ≤ toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) := by
    rw [upperTriangular_eq_unitriangular (Nat.card_zmod 2), ← he]
    exact toSL_mono e le_sup_right
  obtain ⟨hQ, hCc⟩ := eq_flagStabilizer_borelOvergroupCuts hUB
  have hBLT : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H (S.L1 ⊔ T) := by
    rw [S.kst_sup hF hL1H hTH]
    exact sup_le_sup_left inf_le_left _
  have hLTs : Group.IsSolvable ↥(S.KSt H (S.L1 ⊔ T)) :=
    S.kst_isSolvable hF hH.1.1 (S.isSolvable_L1T h1334 hS)
  have hBs : Group.IsSolvable ↥(S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBLT)
      (Subgroup.inclusion_injective _)
  have hQs := isSolvable_toSL e hBK hBs
  rw [hQ] at hQs
  obtain ⟨c, hcL, hc3, hc1⟩ := exists_order_three_L1 S
  have h3 : 3 ∣ Nat.card ↥(flagStabilizer 3 (ZMod 2)
      (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
    rw [← hQ, card_toSL e hBK]
    exact (three_dvd_card_kst S hF hL1H hcL hc3 hc1).trans (Subgroup.card_dvd_of_le le_sup_left)
  have htB : t ∈ Subgroup.normalizer
      ((S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) : Subgroup _) : Set _) :=
    mem_normalizer_sup (S.kst_le_normalizer hF hL1H hTH S.T_le_normalizer_L1 htT)
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer htT, hHsN (hTsHs htT)⟩)
  have hrev := revCuts_eq_of_conj (by norm_num) e hKsHs hHsN hC hTsHs he htT htK htB hCc hQ
  rcases cuts_three hCc hQs h3 with h | h <;> rw [h] at hrev
  · have h2 : (2 : ℕ) ∈ revCuts 3 ({1} : Set ℕ) := ⟨by norm_num, by simp⟩
    rw [hrev] at h2
    simp at h2
  · have h1 : (1 : ℕ) ∈ revCuts 3 ({2} : Set ℕ) := ⟨by norm_num, by simp⟩
    rw [hrev] at h1
    simp at h1

open L13825 Setting4 in
theorem lem13825Par_of (h21 : Lem13821) (h16 : Lem13816)
    (h1334 : Stmt13_3_4) : Lem13825Par := by
  intro G _ _ T L V S hS hno3 H hH K hK _ n hn4 hn5 hKn
  obtain ⟨hKsHs, hHsN, hTsHs, hHsKT, hC, e, he⟩ := star_setup h21 h16 hS hH hK (by omega) hKn
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hL1K : S.L1 ≤ K := (h21 G T L V S hS H hH K hK).1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKleH : S.KSt H T ≤ S.KSt H K ↔ T ≤ K ⊔ pCoreOf 2 H := S.kst_le_iff hF hTH hKH
  have hLK : S.KSt H S.L1 ≤ S.KSt H K := S.kst_mono hF hL1K hKH
  have hBK : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H K := sup_le hLK inf_le_right
  have hUle : ∀ {X : Subgroup _}, X ≤ S.KSt H K →
      upperTriangular n (ZMod 2) ≤ toSL e (X ⊔ (S.KSt H T ⊓ S.KSt H K)) := fun {X} _ => by
    rw [upperTriangular_eq_unitriangular (Nat.card_zmod 2), ← he]
    exact toSL_mono e le_sup_right
  obtain ⟨hQ, hCc⟩ := eq_flagStabilizer_borelOvergroupCuts (hUle hLK)
  have hLT : S.KSt H (S.L1 ⊔ T) = S.KSt H S.L1 ⊔ S.KSt H T := S.kst_sup hF hL1H hTH
  have hBLT : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H (S.L1 ⊔ T) := by
    rw [hLT]
    exact sup_le_sup_left inf_le_left _
  have hLTs : Group.IsSolvable ↥(S.KSt H (S.L1 ⊔ T)) :=
    S.kst_isSolvable hF hH.1.1 (S.isSolvable_L1T h1334 hS)
  have hBs : Group.IsSolvable ↥(S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBLT)
      (Subgroup.inclusion_injective _)
  have hLs : Group.IsSolvable ↥(S.KSt H S.L1) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion
      (le_sup_left : S.KSt H S.L1 ≤ S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)))
      (Subgroup.inclusion_injective _)
  have hQs := isSolvable_toSL e hBK hBs
  rw [hQ] at hQs
  have hTN : ∀ t ∈ S.KSt H T, ∀ {X : Subgroup G}, X ≤ H →
      T ≤ Subgroup.normalizer (X : Set G) →
      t ∈ Subgroup.normalizer ((S.KSt H X ⊔ (S.KSt H T ⊓ S.KSt H K) : Subgroup _) : Set _) :=
    fun t ht X hXH hTX => mem_normalizer_sup (S.kst_le_normalizer hF hXH hTH hTX ht)
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hHsN (hTsHs ht)⟩)
  by_cases hhat : IsHatA6 L
  ·
    have h9 : 9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2)
        (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
      rw [← hQ, card_toSL e hBK]
      exact (nine_dvd_card_kst S hF hL1H
        (nine_dvd_of_two_le_pRank (S.two_le_pRank_L1_of_hat hhat))).trans
        (Subgroup.card_dvd_of_le le_sup_left)
    have hTK : S.KSt H T ≤ S.KSt H K := by
      by_contra hTK
      obtain ⟨t, htT, htK⟩ : ∃ t ∈ S.KSt H T, t ∉ S.KSt H K := by
        by_contra hne
        exact hTK fun t ht => by_contra fun h => hne ⟨t, ht, h⟩
      obtain ⟨c, hc0, hc3, hcO, hdec⟩ := l0_decomp hhat
      have hL0L1 : l0 L ≤ S.L1 := S.l0_le_L1
      have hL0H : l0 L ≤ H := hL0L1.trans hL1H
      have hTL0 : T ≤ Subgroup.normalizer (l0 L : Set G) :=
        A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans normalizer_L_le_o2Z)
      have hL0K : S.KSt H (l0 L) ≤ S.KSt H K := S.kst_mono hF (hL0L1.trans hL1K) hKH
      have hB₀K : S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H K := sup_le hL0K inf_le_right
      have hB₀B : S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K) ≤
          S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) :=
        sup_le_sup_right (S.kst_mono hF hL0L1 hL1H) _
      obtain ⟨hQ₀, hC₀⟩ := eq_flagStabilizer_borelOvergroupCuts (hUle hL0K)
      have hQ₀s := isSolvable_toSL e hB₀K (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hB₀B) (Subgroup.inclusion_injective _))
      rw [hQ₀] at hQ₀s
      have h3 : 3 ∣ Nat.card ↥(flagStabilizer n (ZMod 2)
          (borelOvergroupCuts (toSL e (S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
        rw [← hQ₀, card_toSL e hB₀K]
        exact (three_dvd_card_kst S hF hL0H hc0 hc3
          (fun h => hcO (by rw [h]; exact Subgroup.one_mem _))).trans
          (Subgroup.card_dvd_of_le le_sup_left)
      have h9' : ¬ 9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2)
          (borelOvergroupCuts (toSL e (S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
        rw [← hQ₀, card_toSL e hB₀K]
        intro h
        refine not_nine_dvd_sup hTL0 hTsyl.2.1 (not_nine_dvd_of_decomp
          (CFSG.LieType.BorelTits.pCoreOf_le 2 (l0 L))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l0 L)) hc0 hdec) ?_
        have hle : S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H (l0 L ⊔ T) := by
          rw [S.kst_sup hF hL0H hTH]
          exact sup_le_sup_left inf_le_left _
        exact h.trans ((Subgroup.card_dvd_of_le hle).trans
          (S.card_kst_dvd hF (sup_le hL0H hTH)))
      obtain ⟨j, hj, hjn, hCj⟩ := cuts_minPar hn4 hn5 hC₀ hQ₀s h3 h9'
      have hrev := revCuts_eq_of_conj (by omega) e hKsHs hHsN hC hTsHs he htT htK
        (hTN t htT hL0H hTL0) hC₀ hQ₀
      rw [hCj, revCuts_minPar hjn] at hrev
      have hjj : n - j = j := eq_of_minPar_eq hj hjn hrev
      obtain rfl : n = 4 := by omega
      obtain rfl : j = 2 := by omega
      have hsub : borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))) ⊆
          ({1, 3} : Set ℕ) := by
        have hle : flagStabilizer 4 (ZMod 2)
            (borelOvergroupCuts (toSL e (S.KSt H (l0 L) ⊔ (S.KSt H T ⊓ S.KSt H K)))) ≤
            flagStabilizer 4 (ZMod 2)
              (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)))) := by
          rw [← hQ₀, ← hQ]
          exact toSL_mono e hB₀B
        have h1 := (flagStabilizer_le_iff hC₀ hCc).1 hle
        rw [hCj] at h1
        intro c hc
        have := h1 hc
        simp only [minPar, Set.mem_ofPred_eq] at this
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      exact false_of_le_one_three hCc hsub hQs h9
    refine ⟨?_, fun _ => hKleH.1 hTK, fun _ => hhat⟩
    by_contra hn
    obtain rfl : n = 5 := by omega
    exact false_of_pbShape h21 hS hno3 hH e he hKsHs hTK hLK hLs hQ
      (pbShape_five_nine hCc (cuts_five_nine hCc hQs h9))
  ·
    have h9 : ¬ 9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2)
        (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
      rw [← hQ, card_toSL e hBK]
      intro h
      refine not_nine_dvd_sup S.T_le_normalizer_L1 hTsyl.2.1 (not_nine_dvd_of_decomp
        (CFSG.LieType.BorelTits.pCoreOf_le 2 S.L1) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1)
        (S.cL1_mem hhat) fun x hx => S.L1_decomp hhat hx) ?_
      exact h.trans ((Subgroup.card_dvd_of_le hBLT).trans (S.card_kst_dvd hF hH.1.1))
    have h3 : 3 ∣ Nat.card ↥(flagStabilizer n (ZMod 2)
        (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
      rw [← hQ, card_toSL e hBK]
      exact (three_dvd_card_kst S hF hL1H (S.cL1_mem hhat) (S.cL1_cube hhat)
        (fun h => S.cL1_not_mem hhat (by rw [h]; exact Subgroup.one_mem _))).trans
        (Subgroup.card_dvd_of_le le_sup_left)
    obtain ⟨j, hj, hjn, hCj⟩ := cuts_minPar hn4 hn5 hCc hQs h3 h9
    have hTK : ¬ S.KSt H T ≤ S.KSt H K := fun hTK =>
      false_of_pbShape h21 hS hno3 hH e he hKsHs hTK hLK hLs hQ
        (hCj ▸ pbShape_minPar hn4 hn5 hj hjn)
    obtain ⟨t, htT, htK⟩ : ∃ t ∈ S.KSt H T, t ∉ S.KSt H K := by
      by_contra hne
      exact hTK fun t ht => by_contra fun h => hne ⟨t, ht, h⟩
    have hrev := revCuts_eq_of_conj (by omega) e hKsHs hHsN hC hTsHs he htT htK
      (hTN t htT hL1H S.T_le_normalizer_L1) hCc hQ
    rw [hCj, revCuts_minPar hjn] at hrev
    have hjj : n - j = j := eq_of_minPar_eq hj hjn hrev
    exact ⟨by omega, fun h => absurd h hhat, fun h => absurd (hKleH.2 h) hTK⟩

end CFSG.Quasithin.H13.A6
