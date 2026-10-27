module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofLift
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1519

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open Proof1517

theorem step1519P_of
    (h135 : Item135Simple) (h142 : Concl142R) :
    Step1519P := by
  intro G _ _ A c L h Y hctx m p hiso hp hp3
  have hpp : p.Prime := hp.1
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hθc := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hAbE, hAb9⟩ := isElemAbelian_card_aBar h hctx
  obtain ⟨Pb, hPbE, hPbc, hPbN⟩ := Torus1519.ks1519Torus _ m p hiso hp hp3 _ hAbE hAb9
  set K := Pb.comap π with hK
  set KG := K.map L.subtype with hKG
  have hKGL : KG ≤ L := Subgroup.map_subtype_le K
  have hcKG : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective L.subtype_injective
  have hp3' : p ≠ 3 := by omega
  have hPb3 : ¬ 3 ∣ Nat.card Pb := by
    rw [hPbc]
    intro h3
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hθc.2.2.1
  have hK3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_comap π hPb3 hker3
  have hAKG : A ≤ Subgroup.normalizer (KG : Set G) := le_normalizer_map_comap h hctx hPbN
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨R, hRKG, hRp, hAR, hRcard⟩ :=
    Sec17.HeadProof.exists_invariant_sylow hA3 (by rwa [hcKG]) hAKG hpp
  have hθ2 : IsPGroup 2 θ := by
    rw [hθdef, Proof1517.theta_eq_pCore_two h135 h hctx]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hθ2
  have hKc : Nat.card K = 2 ^ a * p ^ 2 := by
    rw [← ha, ← hPbc]
    exact QuotientGroup.card_preimage_mk θ (Pb : Set (↥L ⧸ θ))
  have hp2 : (2 : ℕ) ≠ p := by omega
  have hfact : (2 ^ a * p ^ 2).factorization p = 2 := by
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow hpp]
    simp [hp2]
  have hRc : Nat.card R = p ^ 2 := by rw [hRcard, hcKG, hKc, hfact]
  have hRθ : ∀ x : ↥L, (x : G) ∈ R → x ∈ θ → x = 1 := by
    intro x hxR hxθ
    obtain ⟨i, hi⟩ := hRp ⟨(x : G), hxR⟩
    obtain ⟨j, hj⟩ := hθ2 ⟨x, hxθ⟩
    have hi' : x ^ p ^ i = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hi
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (p ^ i) (2 ^ j) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp Nat.prime_two).mpr (by omega))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hi') (orderOf_dvd_of_pow_eq_one hj'))
  have hRL : ∀ {x : G}, x ∈ R → x ∈ L := fun hx => hKGL (hRKG hx)
  have hRPb : ∀ {x : G} (hx : x ∈ R), π ⟨x, hRL hx⟩ ∈ Pb := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hRKG hx
    have : y = ⟨x, hRL hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hRE : CFSG.Assembly.IsElemAbelian p R := by
    have hPbc' := hPbE.1
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hu := hRL u.2
      have hv := hRL v.2
      have hcomm : π ⟨(u : G), hu⟩ * π ⟨(v : G), hv⟩ = π ⟨(v : G), hv⟩ * π ⟨(u : G), hu⟩ :=
        congrArg Subtype.val (mul_comm' (⟨_, hRPb u.2⟩ : Pb) ⟨_, hRPb v.2⟩)
      have hθuv : (⟨(u : G), hu⟩ : ↥L) * ⟨(v : G), hv⟩ *
          ((⟨(v : G), hv⟩ : ↥L) * ⟨(u : G), hu⟩)⁻¹ ∈ θ := by
        have h1 : π ((⟨(u : G), hu⟩ : ↥L) * ⟨(v : G), hv⟩ *
            ((⟨(v : G), hv⟩ : ↥L) * ⟨(u : G), hu⟩)⁻¹) = 1 := by
          rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hRuv : ((⟨(u : G), hu⟩ : ↥L) * ⟨(v : G), hv⟩ *
          ((⟨(v : G), hv⟩ : ↥L) * ⟨(u : G), hu⟩)⁻¹ : ↥L) ∈ R.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact R.mul_mem (R.mul_mem u.2 v.2) (R.inv_mem (R.mul_mem v.2 u.2))
      have h1 := hRθ _ (Subgroup.mem_subgroupOf.mp hRuv) hθuv
      have h2 : (u : G) * v * ((v : G) * u)⁻¹ = 1 := congrArg Subtype.val h1
      exact mul_inv_eq_one.mp h2
    · have hxL := hRL hx
      have hxp : π ⟨x, hxL⟩ ^ p = 1 := by
        have := hPbE.2 _ (hRPb hx)
        exact this
      have hθx : (⟨x, hxL⟩ : ↥L) ^ p ∈ θ := by
        have h1 : π ((⟨x, hxL⟩ : ↥L) ^ p) = 1 := by rw [map_pow]; exact hxp
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hRx : ((⟨x, hxL⟩ : ↥L) ^ p : ↥L) ∈ R.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        simpa using R.pow_mem hx p
      have h1 := hRθ _ (Subgroup.mem_subgroupOf.mp hRx) hθx
      simpa using congrArg Subtype.val h1
  have hRL' : R ≤ L := hRKG.trans hKGL
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hRc]
    intro h3
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  exact ⟨R, hRE, hRc, ⟨⟨mem_scriptQ_of_le_L h142 h hRL' hR3 hAR, hRL'⟩,
    (isPiSubgroup_piOf_iff hpp R).mpr hRp⟩⟩

end CFSG.RankThree.PartTwo.Sec15
