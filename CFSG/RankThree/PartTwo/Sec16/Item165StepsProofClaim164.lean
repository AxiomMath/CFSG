module

public import CFSG.RankThree.PartTwo.Sec13.Item131a
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

namespace Steps165

variable {G : Type} [Group G] [Finite G]

theorem eq_zpowers_sup_inf {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine (h.isElemAbelian.2 c h.mem_A)
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
    (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.toSec13Data.card_eq, hcard])).symm

theorem isSylowOf_of_card_nine {L Q : Subgroup G} (h27 : ¬ 27 ∣ Nat.card L) (hQL : Q ≤ L)
    (hQ9 : Nat.card Q = 9) : CFSG.ABGLocalTools.IsSylowOf 3 Q L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨hQL, IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num), fun h3 => h27 ?_⟩
  have h1 := Subgroup.relIndex_mul_card Q L
  rw [inf_eq_left.mpr hQL, hQ9] at h1
  rw [← h1]
  exact Dvd.dvd.trans (by norm_num : (27 : ℕ) ∣ 3 * 9) (Nat.mul_dvd_mul_right h3 9)

omit [Finite G] in
theorem eq_map_conj_of_forall {P P' : Subgroup G} {k : G}
    (hk : ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P) : P' = P.map (MulAut.conj k).toMonoidHom := by
  ext x
  rw [hk x]
  constructor
  · intro hx
    refine ⟨k⁻¹ * x * k, hx, ?_⟩
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  · rintro ⟨y, hy, rfl⟩
    change k⁻¹ * (k * y * k⁻¹) * k ∈ P
    simpa [mul_assoc] using hy

theorem claim164_of_sylow {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (h27 : ¬ 27 ∣ Nat.card L) :
    Claim164 A c L := by
  intro g hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3L : 3 ∣ Nat.card L := by
    have : 9 ∣ Nat.card L := h9 ▸ Subgroup.card_dvd_of_le inf_le_right
    exact (show 3 ∣ 9 by norm_num).trans this
  have hgL : L.map (MulAut.conj g).toMonoidHom = L := Late.map_conj_eq_of_mem_normalizer
    (normalizer_zpowers_le_normalizer_L h h3L hg)
  have hgz : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
    Late.map_conj_eq_of_mem_normalizer hg
  have hP'L : (A ⊓ L).map (MulAut.conj g).toMonoidHom ≤ L := by
    calc (A ⊓ L).map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono inf_le_right
      _ = L := hgL
  have hP'9 : Nat.card ((A ⊓ L).map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h9]
  obtain ⟨k, hkL, hk⟩ := (isSylowOf_of_card_nine h27 inf_le_right h9).exists_mem_conj
    (isSylowOf_of_card_nine h27 hP'L hP'9)
  have hP' := eq_map_conj_of_forall hk
  have hkC : k ∈ Subgroup.centralizer ({c} : Set G) := h.le_centralizer hkL
  have hkz : (Subgroup.zpowers c).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change k * c * k⁻¹ = c
    rw [Subgroup.mem_centralizer_singleton_iff.mp hkC, mul_inv_cancel_right]
  have hA := eq_zpowers_sup_inf h hcL h9
  have heq : A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj k).toMonoidHom := by
    calc A.map (MulAut.conj g).toMonoidHom
        = (Subgroup.zpowers c ⊔ (A ⊓ L)).map (MulAut.conj g).toMonoidHom := by
          rw [← hA]
      _ = Subgroup.zpowers c ⊔ (A ⊓ L).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_sup, hgz]
      _ = Subgroup.zpowers c ⊔ (A ⊓ L).map (MulAut.conj k).toMonoidHom := by
          rw [← hP']
      _ = (Subgroup.zpowers c ⊔ (A ⊓ L)).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_sup, hkz]
      _ = A.map (MulAut.conj k).toMonoidHom := by rw [← hA]
  have hw : k⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_map_conj_eq ?_
    rw [← Late.map_conj_map_conj, heq, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  have hkH : k ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c hkC
  have hmem : k⁻¹ * g ∈
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hkH) hg, hw⟩
  have e : g = k * (k⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hkL hmem

omit [Finite G] in
theorem not_dvd_eightyOne_L {q : ℕ} (h3 : q % 3 = 1) (h9 : q % 9 ≠ 1) :
    ¬ 81 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1' : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h1']
  push_cast
  have key : ∀ x : ZMod 81, x.val % 3 = 1 → x.val % 9 ≠ 1 →
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ≠ 0 := by decide
  refine key (q : ZMod 81) ?_ ?_
  · rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact h3
  · rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact h9

omit [Finite G] in
theorem not_dvd_eightyOne_U {q : ℕ} (h3 : q % 3 = 2) (h9 : q % 9 ≠ 8) :
    ¬ 81 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1]
  push_cast
  have key : ∀ x : ZMod 81, x.val % 3 = 2 → x.val % 9 ≠ 8 →
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) ≠ 0 := by decide
  refine key (q : ZMod 81) ?_ ?_
  · rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact h3
  · rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact h9

omit [Finite G] in
theorem not_dvd_card_projSL {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (h3 : p ^ e % 3 = 1)
    (h9 : p ^ e % 9 ≠ 1) :
    ¬ 27 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p e)) := by
  intro h27
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
  rw [GaloisField.card p e (by omega)] at hc
  have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
  rw [hg] at hc
  apply not_dvd_eightyOne_L h3 h9
  rw [← hc]
  exact Dvd.dvd.trans (by norm_num : (81 : ℕ) ∣ 27 * 3) (Nat.mul_dvd_mul_right h27 3)

omit [Finite G] in
theorem not_dvd_card_projSU {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (h3 : p ^ e % 3 = 2)
    (h9 : p ^ e % 9 ≠ 8) :
    ¬ 27 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 p e) := by
  intro h27
  have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
  have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
  rw [hg] at hc
  apply not_dvd_eightyOne_U h3 h9
  rw [← hc]
  exact Dvd.dvd.trans (by norm_num : (81 : ℕ) ∣ 27 * 3) (Nat.mul_dvd_mul_right h27 3)

omit [Finite G] in
theorem not_dvd_card_alt7 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

omit [Finite G] in
theorem not_dvd_card_M22 : ¬ 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
  rw [KFacts.KS14.card_nativeM22]
  decide

theorem not_dvd_card_of_quot {L : Subgroup G}
    (h : ¬ 27 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : ¬ 27 ∣ Nat.card L := by
  intro h27
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hcop : Nat.Coprime (3 ^ 3) (Nat.card (aschbacherSolvableCore 3 ↥L)) :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)] at h27
  exact h (hcop.dvd_of_dvd_mul_right h27)

theorem not_dvd_card_of_equiv {L : Subgroup G} {S : Type*} [Group S]
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* S) (hS : ¬ 27 ∣ Nat.card S) :
    ¬ 27 ∣ Nat.card L :=
  not_dvd_card_of_quot (by rwa [Nat.card_congr e.toEquiv])

theorem center_thetaQuot_eq_bot (hspor : SporadicModels131) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := hspor
  rcases (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with hJ | hL3 | hA7 | hM22 | hM12
  · obtain ⟨φ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φ hJ2z
  · obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq).2
    · by_cases hq2 : 2 < p ^ e
      · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq hq2).2
      · exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_lA.1
        have : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
          have := isSolvable_projSU_two
          exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
        obtain ⟨hperf, -, a, b, hab⟩ := hQ
        have : Nontrivial ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
            Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := ⟨⟨a * b, b * a, hab⟩⟩
        have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
          (QuotientGroup.mk_surjective (s := Subgroup.center _)).nontrivial
        have := hperf
        exact Group.IsPerfect.not_isSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) inferInstance
  · obtain ⟨φ⟩ := hA7
    exact center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2
  · obtain ⟨φ⟩ := hM22
    exact center_eq_bot_of_mulEquiv φ hM22z
  · obtain ⟨φ⟩ := hM12
    exact center_eq_bot_of_mulEquiv φ hM12z

theorem claim164_of_item131a (h131a : Item131a) (hspor : SporadicModels131) (h138 : Item138N)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hM12 : ¬ (Nonempty (lBarA c L A ≃*
        Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
      Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))))
    (hPGL : ¬ (Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧ ∃ x ∈ A, Sec4.InducesTypeOn L x 3)) :
    Claim164 A c L := by
  have hD := h.toSec13Data
  have hZ := center_thetaQuot_eq_bot hspor h
  obtain ⟨⟨hM22p, hM22z⟩, -, ⟨hJ2p, hJ2z⟩⟩ := hspor
  rcases h131a G A c L hD with ⟨hL3, -⟩ | hP | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | hM | ⟨⟨φ⟩, -⟩ | h7
  ·
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hSZ⟩ := isPerfect_center_projSL p e he hq
      obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod hD hS hSZ φ
      have hmod := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he
        (Or.inl ⟨hq, ⟨ψ⟩⟩) hprod
      exact claim164_of_sylow h hcL h9 (not_dvd_card_of_equiv ψ
        (not_dvd_card_projSL he hq fun h1 => hmod (Or.inl h1)))
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hSZ⟩ := isPerfect_center_projSU p e he hq hq2
        obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod hD hS hSZ φ
        have hmod := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he
          (Or.inr ⟨hq, ⟨ψ⟩⟩) hprod
        exact claim164_of_sylow h hcL h9 (not_dvd_card_of_equiv ψ
          (not_dvd_card_projSU he hq fun h1 => hmod (Or.inr h1)))
      · exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable hD isSolvable_projSU_two φ
  ·
    exact absurd hP hPGL
  ·
    obtain ⟨hS, hSZ⟩ := isPerfect_center_alt7
    obtain ⟨hcL, h9, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hSZ φ
    exact claim164_of_sylow h hcL h9 (not_dvd_card_of_equiv ψ not_dvd_card_alt7)
  ·
    obtain ⟨hcL, h9, -, ⟨ψ⟩⟩ := facts_of_prod hD hM22p hM22z φ
    exact claim164_of_sylow h hcL h9 (not_dvd_card_of_equiv ψ not_dvd_card_M22)
  ·
    exact absurd hM hM12
  ·
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
    exact (hJ.false ψ).elim
  ·
    exfalso
    apply not_mem_of_center_eq_bot hD hZ
    rcases h7 with hSL | ⟨hHeis, -⟩
    · exact mem_of_isSLThreePiTwo slTwoCenter hD hSL
    · exact mem_of_isHeisCentral hD hHeis

theorem claim164_of_not_m12_pgl (h131a : Item131a) (hspor : SporadicModels131)
    (h138 : Item138N) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hM12 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) : Claim164 A c L := by
  refine claim164_of_item131a h131a hspor h138 h hJ ?_ fun hP => hPGL hP.1
  rintro ⟨⟨φ⟩, -⟩
  obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod h.toSec13Data hspor.2.1.1 hspor.2.1.2 φ
  exact hM12.false ψ

theorem claim164_of_prod (h131a : Item131a) (hspor : SporadicModels131) (h138 : Item138N)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hM12 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Claim164 A c L := by
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data (center_thetaQuot_eq_bot hspor h)
  exact claim164_of_not_m12_pgl h131a hspor h138 h hJ hM12 fun hP =>
    Proof1514.false_of_prod_of_isZ3PGLThreePi h.toSec13Data hcL hprod hP

omit [Finite G] in
theorem card_projImage_slPi_ne_alt7 {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) :
    Nat.card (CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) K)) ≠ 2520 := by
  intro h
  have hc := card_projImage_slPi_mul_three hK hq
  rw [h] at hc
  have hf : f ≠ 0 := by have := hK.one_le; omega
  have hq2 : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
  generalize p ^ f = q at hc hq2
  have hpos : 1 ≤ (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
    have h1 : 1 ≤ q ^ 2 - 1 := by
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have h2 : 1 ≤ cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
      have : 8 ≤ q ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
      cases π <;> simp only [Bool.cond_false, Bool.cond_true] <;> omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hq20 : q < 20 := by
    by_contra hge
    have h8 : 8000 ≤ q ^ 3 := by
      calc 8000 = 20 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) :=
      Nat.le_mul_of_pos_right _ hpos
    rw [← mul_assoc] at this
    omega
  interval_cases q <;> cases π <;> simp at hc

theorem claim164_of_alt7 (h131a : Item131a) (hspor : SporadicModels131) (h138 : Item138N)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) : Claim164 A c L := by
  refine claim164_of_item131a h131a hspor h138 h
    ⟨fun φ => KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (φ.symm.trans ψ)⟩ ?_ ?_
  · rintro ⟨⟨φ⟩, -⟩
    obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod h.toSec13Data hspor.2.1.1 hspor.2.1.2 φ
    exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 ψ).false χ
  · rintro ⟨-, -, x, -, hx⟩
    obtain ⟨-, π, p, f, K, _, hK, hq, e, -⟩ := hx
    refine card_projImage_slPi_ne_alt7 hK hq ?_
    rw [Nat.card_congr (e.symm.trans ψ).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

end Steps165

@[expose] noncomputable def Claim164Y0R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (scriptY0Star A (lB A)).Nonempty → Claim164 A c L

theorem item131a_of_item131 (h131 : Item131) : Item131a := by
  intro G _ _ A c L hD
  rcases h131 G A c L hD with h | h | h | h | h | h | ⟨h7, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

theorem claim164Y0R_of (h415 : Sec4.Item4_15) (h131 : Item131) (hspor : SporadicModels131)
    (h138 : Item138N) (h1514 : Sec15.Item1514R) (h163 : Item163R) (hMeets : Step163Meets) :
    Claim164Y0R := by
  intro G _ _ A c L h hY0
  obtain ⟨Y, hY⟩ := hY0
  have h131a := item131a_of_item131 h131
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact claim164_of_j2_of_item131 h415 h131 hspor h hJ
  have hJ' := not_nonempty_iff.mp hJ
  obtain ⟨-, -, -, hLY, -⟩ := h163 G A c L h Y hY
  rcases h1514 G A c L h Y hY (hMeets G A c L h Y hY hLY) with
      ⟨-, -, -, hprod, hM12⟩ | ⟨⟨ψ⟩, -⟩ | ⟨-, -, -, -, hnot, -⟩
  · exact Steps165.claim164_of_prod h131a hspor h138 h hJ' hM12 hprod
  · exact Steps165.claim164_of_alt7 h131a hspor h138 h ψ
  · exact absurd hLY (hnot Y hY)

theorem item164R_of_y0 (h163 : Item163R) (hfr : Claim164Y0R) : Item164R := by
  intro G _ _ A c L h Y hY
  exact rank3II_16_4_of (h163 G A c L h) (hfr G A c L h ⟨Y, hY⟩) Y hY

theorem item164R_of_route (h415 : Sec4.Item4_15) (h131 : Item131) (hspor : SporadicModels131)
    (h138 : Item138N) (h1514 : Sec15.Item1514R) (h163 : Item163R) (hMeets : Step163Meets) :
    Item164R :=
  item164R_of_y0 h163 (claim164Y0R_of h415 h131 hspor h138 h1514 h163 hMeets)

end CFSG.RankThree.PartTwo.Sec16
