module

public import CFSG.LocalAnalysis.UniquenessCase.Frob4PNormalCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Borel
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem frob4P_sylow_conj {p : ℕ} [Fact p.Prime] {P K R : Subgroup G}
    (hP : IsSylowOf p P K) (hRK : R ≤ K) (hR : IsPGroup p R) :
    ∃ k ∈ K, ∀ g ∈ R, k * g * k⁻¹ ∈ P := by
  obtain ⟨S, hRS⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hkK, hconj⟩ := hP.exists_mem_conj
    (show IsSylowOf p ((S : Subgroup K).map K.subtype) K from ⟨S, rfl⟩)
  refine ⟨k⁻¹, K.inv_mem hkK, fun g hg => ?_⟩
  have hgS : (⟨g, hRK hg⟩ : K) ∈ (S : Subgroup K) := hRS (Subgroup.mem_subgroupOf.mpr hg)
  have hgmap : g ∈ (S : Subgroup K).map K.subtype := ⟨⟨g, hRK hg⟩, hgS, rfl⟩
  have h := (hconj g).mp hgmap
  simpa using h

private theorem frob4P_exists_isSylowOf_ge_of_le {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQK : Q ≤ K) (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨T, hT⟩ := hQ'.exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem frob4P_not_commute_conj {p : ℕ} [Fact p.Prime] {M : Subgroup G} {x d q x₁ : G}
    (hxM : x ∈ M) (hxp : orderOf x = p) (hdM : d ∈ M)
    (hq : q ∈ uniqueFourPrimeCore p M)
    (hdx : d ∈ normalizer ((zpowers x : Subgroup G) : Set G))
    (hdc : d ∉ centralizer ({x} : Set G))
    (hx₁ : x₁ ∈ zpowers x) (hx₁1 : x₁ ≠ 1) :
    d * (q⁻¹ * x₁ * q) ≠ q⁻¹ * x₁ * q * d := by
  classical
  intro habs
  obtain ⟨-, hQnorm, hQcop⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hq'Q : d * q * d⁻¹ ∈ uniqueFourPrimeCore p M :=
    (Subgroup.mem_normalizer_iff.mp (hQnorm hdM) q).mp hq
  have hyZ : d * x₁ * d⁻¹ ∈ zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hdx x₁).mp hx₁
  set c : G := (d * q * d⁻¹) * q⁻¹ with hc
  have hy_eq : d * x₁ * d⁻¹ = c * x₁ * c⁻¹ := by
    rw [hc]
    have h1 : d * (q⁻¹ * x₁ * q) * d⁻¹ = q⁻¹ * x₁ * q := by
      rw [habs]; group
    have h2 : d * (q⁻¹ * x₁ * q) * d⁻¹ =
        (d * q * d⁻¹)⁻¹ * (d * x₁ * d⁻¹) * (d * q * d⁻¹) := by group
    have hmid : (d * q * d⁻¹)⁻¹ * (d * x₁ * d⁻¹) * (d * q * d⁻¹) = q⁻¹ * x₁ * q := by
      rw [← h2, h1]
    calc d * x₁ * d⁻¹
        = (d * q * d⁻¹) * ((d * q * d⁻¹)⁻¹ * (d * x₁ * d⁻¹) * (d * q * d⁻¹)) *
            (d * q * d⁻¹)⁻¹ := by group
      _ = (d * q * d⁻¹) * (q⁻¹ * x₁ * q) * (d * q * d⁻¹)⁻¹ := by rw [hmid]
      _ = ((d * q * d⁻¹) * q⁻¹) * x₁ * ((d * q * d⁻¹) * q⁻¹)⁻¹ := by group
  have hx₁M : x₁ ∈ M := (Subgroup.zpowers_le.mpr hxM) hx₁
  have hcQ : c ∈ uniqueFourPrimeCore p M := by
    rw [hc]
    exact (uniqueFourPrimeCore p M).mul_mem hq'Q ((uniqueFourPrimeCore p M).inv_mem hq)
  have hconjQ : x₁ * c⁻¹ * x₁⁻¹ ∈ uniqueFourPrimeCore p M :=
    (Subgroup.mem_normalizer_iff.mp (hQnorm hx₁M) c⁻¹).mp
      ((uniqueFourPrimeCore p M).inv_mem hcQ)
  have hyxQ : (d * x₁ * d⁻¹) * x₁⁻¹ ∈ uniqueFourPrimeCore p M := by
    rw [hy_eq]
    have h : (c * x₁ * c⁻¹) * x₁⁻¹ = c * (x₁ * c⁻¹ * x₁⁻¹) := by group
    rw [h]
    exact (uniqueFourPrimeCore p M).mul_mem hcQ hconjQ
  have hyxZ : (d * x₁ * d⁻¹) * x₁⁻¹ ∈ zpowers x :=
    (zpowers x).mul_mem hyZ ((zpowers x).inv_mem hx₁)
  have hone : (d * x₁ * d⁻¹) * x₁⁻¹ = 1 := by
    have hdvd1 : orderOf ((d * x₁ * d⁻¹) * x₁⁻¹) ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard (zpowers x) hyxZ
      rwa [Nat.card_zpowers, hxp] at h
    have hdvd2 : orderOf ((d * x₁ * d⁻¹) * x₁⁻¹) ∣
        Nat.card (uniqueFourPrimeCore p M) :=
      Subgroup.orderOf_dvd_natCard _ hyxQ
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hQcop hdvd1 hdvd2)
  have hyx₁ : d * x₁ * d⁻¹ = x₁ := by
    calc d * x₁ * d⁻¹ = ((d * x₁ * d⁻¹) * x₁⁻¹) * x₁ := by group
      _ = 1 * x₁ := by rw [hone]
      _ = x₁ := by group
  have hcomm : d * x₁ = x₁ * d := by
    calc d * x₁ = (d * x₁ * d⁻¹) * d := by group
      _ = x₁ * d := by rw [hyx₁]
  have hx₁ord : orderOf x₁ = p := by
    have hdvd : orderOf x₁ ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard (zpowers x) hx₁
      rwa [Nat.card_zpowers, hxp] at h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf x₁) hdvd with h | h
    · exact absurd h (fun h1 => hx₁1 (orderOf_eq_one_iff.mp h1))
    · exact h
  have hzpx : zpowers x₁ = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₁) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hx₁ord, hxp]
  have hcent : d ∈ centralizer ((zpowers x₁ : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  rw [hzpx] at hcent
  rw [centralizer_zpowers_eq] at hcent
  exact hdc hcent

theorem frob4P_exists_mem_conj_le {p : ℕ} [Fact p.Prime] {M P U R : Subgroup G}
    (hM : Group.IsSolvable M) (hP : IsSylowOf p P M) (hab : IsMulCommutative P) (hUP : U ≤ P)
    (hRM : R ≤ M) (hR : IsPGroup p R) (hRU : R ≤ centralizer (U : Set G)) :
    ∃ q ∈ uniqueFourPrimeCore p M ⊓ centralizer (U : Set G), ∀ g ∈ R, q * g * q⁻¹ ∈ P := by
  classical
  obtain ⟨hQle, hQnorm, _⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  let Q : Subgroup G := uniqueFourPrimeCore p M
  let N : Subgroup G := P ⊔ uniqueFourPrimeCore p M
  have hN : M ≤ normalizer (N : Set G) := frob4P_sylow_sup_primeCore_normal hM hP hab
  have hPM : P ≤ M := hP.le
  have hPnormQ : P ≤ normalizer (Q : Set G) := hPM.trans hQnorm
  have hRN : R ≤ N := by
    intro g hg
    obtain ⟨k, hkM, hkg⟩ := frob4P_sylow_conj hP hRM hR
    have hkgP : k * g * k⁻¹ ∈ P := hkg g hg
    have hkgN : k * g * k⁻¹ ∈ N := Subgroup.mem_sup_left hkgP
    have hmem := (Subgroup.mem_normalizer_iff.mp (hN (M.inv_mem hkM)) (k * g * k⁻¹)).mp hkgN
    have heq : k⁻¹ * (k * g * k⁻¹) * (k⁻¹)⁻¹ = g := by group
    rwa [heq] at hmem
  have hPCU : P ≤ centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h := hab.is_comm.comm (⟨a, ha⟩ : P) ⟨b, hUP hb⟩
    exact (congrArg Subtype.val h).symm
  have hPY : P ≤ N ⊓ centralizer (U : Set G) := le_inf le_sup_left hPCU
  have hRY : R ≤ N ⊓ centralizer (U : Set G) := le_inf hRN hRU
  have hYM : N ⊓ centralizer (U : Set G) ≤ M := inf_le_left.trans (sup_le hPM hQle)
  have hPsylY : IsSylowOf p P (N ⊓ centralizer (U : Set G)) := hP.of_le hPY hYM
  obtain ⟨y, hyY, hy⟩ := frob4P_sylow_conj hPsylY hRY hR
  have hyPQ : y ∈ (P : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P Q hPnormQ]
    exact hyY.1
  rw [Set.mem_mul] at hyPQ
  obtain ⟨u, huP, c, hcQ, huc⟩ := hyPQ
  have hc_eq : c = u⁻¹ * y := by rw [← huc]; group
  have huC : u ∈ centralizer (U : Set G) := hPCU huP
  have hyC : y ∈ centralizer (U : Set G) := hyY.2
  have hcC : c ∈ centralizer (U : Set G) := by
    rw [hc_eq]
    exact (centralizer (U : Set G)).mul_mem ((centralizer (U : Set G)).inv_mem huC) hyC
  refine ⟨c, ⟨hcQ, hcC⟩, fun g hg => ?_⟩
  have h := hy g hg
  have h2 : c * g * c⁻¹ = u⁻¹ * (y * g * y⁻¹) * u := by rw [← huc]; group
  rw [h2]
  exact P.mul_mem (P.mul_mem (P.inv_mem huP) h) huP

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem frob4P_isSylowOf_centralizer [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hM : Group.IsSolvable M) {d : G}
    (hdL : d ∈ centralizer ((layerOf x : Subgroup G) : Set G))
    (hdx : d ∈ normalizer ((zpowers x : Subgroup G) : Set G))
    (hdc : d ∉ centralizer ({x} : Set G)) :
    IsSylowOf p (frU P x) (centralizer ({d} : Set G)) := by
  classical
  have hPM : (P : Subgroup G) ≤ M := fr_P_le_M hl
  have hxM : x ∈ M := hl.point.elem.1
  have hxp : orderOf x = p := hl.point.elem.2.1
  have hdM : d ∈ M := fr_centralizer_layer_le hG hl hdL
  have hPsyl : IsSylowOf p (P : Subgroup G) M :=
    ⟨P.subtype hPM, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM]⟩
  have hab : IsMulCommutative (P : Subgroup G) := hl.abel
  have hUP : frU P x ≤ (P : Subgroup G) := inf_le_left
  have hUbot : frU P x ≠ ⊥ := frU_ne_bot hG hl
  have hNUM : normalizer (frU P x : Set G) ≤ M := fr_normalizer_le hG hl le_rfl hUbot
  have hpGroup : ∀ Q : Subgroup G, IsPGroup p Q → IsMulCommutative Q := fr_pGroup_abelian hl
  have hUleCd : frU P x ≤ centralizer ({d} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdL u hu.2
  have hUp : IsPGroup p (frU P x) := P.isPGroup'.to_inf_left
  obtain ⟨P', hP'syl, hUP'⟩ := frob4P_exists_isSylowOf_ge_of_le hUleCd hUp
  have hP'p : IsPGroup p P' := hP'syl.isPGroup
  have hP'C : P' ≤ centralizer ({d} : Set G) := hP'syl.le
  have hP'abel : IsMulCommutative P' := hpGroup P' hP'p
  have hP'CU : P' ≤ centralizer ((frU P x : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := hP'abel.is_comm.comm (⟨g, hg⟩ : P') ⟨u, hUP' hu⟩
    exact (congrArg Subtype.val h).symm
  have hP'M : P' ≤ M := hP'CU.trans ((Subgroup.centralizer_le_normalizer _).trans hNUM)
  obtain ⟨q, hqQU, hqconj⟩ := frob4P_exists_mem_conj_le hM hPsyl hab hUP hP'M hP'p hP'CU
  have hqQ : q ∈ uniqueFourPrimeCore p M := hqQU.1
  have hqC : q ∈ centralizer ((frU P x : Subgroup G) : Set G) := hqQU.2
  have hP'leU : P' ≤ frU P x := by
    intro g hgP'
    have hqgP : q * g * q⁻¹ ∈ (P : Subgroup G) := hqconj g hgP'
    obtain ⟨t, htU, z, hzZ, htgz⟩ := fr_P_decomp hG hl hqgP
    have hqt : q⁻¹ * t * q = t := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hqC t htU
      calc q⁻¹ * t * q = q⁻¹ * (t * q) := by group
        _ = q⁻¹ * (q * t) := by rw [hcomm]
        _ = t := by group
    have hg_expr : g = q⁻¹ * (t * z) * q := by rw [← htgz]; group
    set z' : G := q⁻¹ * z * q with hz'def
    have hz'_eq : z' = t⁻¹ * g := by
      have hz_eq : z = t⁻¹ * (q * g * q⁻¹) := by rw [htgz]; group
      rw [hz'def, hz_eq]
      calc q⁻¹ * (t⁻¹ * (q * g * q⁻¹)) * q = (q⁻¹ * t⁻¹ * q) * g := by group
        _ = t⁻¹ * g := by
          have h1 : q⁻¹ * t⁻¹ * q = t⁻¹ := by
            calc q⁻¹ * t⁻¹ * q = (q⁻¹ * t * q)⁻¹ := by group
              _ = t⁻¹ := by rw [hqt]
          rw [h1]
    have hz'P' : z' ∈ P' := by
      rw [hz'_eq]
      exact P'.mul_mem (P'.inv_mem (hUP' htU)) hgP'
    have hz'd : Commute z' d := Subgroup.mem_centralizer_singleton_iff.mp (hP'C hz'P')
    have hgz' : g = t * z' := by
      rw [hz'def, hg_expr]
      calc q⁻¹ * (t * z) * q = (q⁻¹ * t * q) * (q⁻¹ * z * q) := by group
        _ = t * (q⁻¹ * z * q) := by rw [hqt]
    by_cases hz1 : z = 1
    · rw [hgz']
      have hz'1 : z' = 1 := by rw [hz'def, hz1]; group
      rw [hz'1, mul_one]
      exact htU
    · exfalso
      let Z0 : Subgroup G := (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G)
      have hzZ0 : z ∈ Z0 := hzZ
      have hZ0p : IsPGroup p Z0 := P.isPGroup'.to_inf_left
      obtain ⟨k, hk⟩ := hZ0p.exists_card_eq
      have hdvd : orderOf z ∣ p ^ k := by
        rw [← hk]
        exact Subgroup.orderOf_dvd_natCard _ hzZ0
      obtain ⟨a, -, ha_eq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [pow_zero] at ha_eq
        exact hz1 (orderOf_eq_one_iff.mp ha_eq)
      have hpdvd : p ∣ orderOf z := by
        rw [ha_eq]
        exact dvd_pow_self p ha0
      set w : G := z ^ (orderOf z / p) with hwdef
      have hword : orderOf w = p := by
        rw [hwdef]
        exact orderOf_pow_orderOf_div (orderOf_pos z).ne' hpdvd
      have hwZ : w ∈ Z0 := by
        rw [hwdef]
        exact Z0.pow_mem hzZ0 _
      have hwne : w ≠ 1 := by
        intro h
        have h1 : orderOf w = 1 := orderOf_eq_one_iff.mpr h
        rw [hword] at h1
        exact (Fact.out : p.Prime).ne_one h1
      have hzpx : zpowers w = zpowers x :=
        fr_Z0_unique hl (Subgroup.zpowers_le.mpr hwZ) (by rw [Nat.card_zpowers, hword])
      have hwzp : w ∈ zpowers x := by
        rw [← hzpx]
        exact Subgroup.mem_zpowers w
      have hz'pow : q⁻¹ * w * q = z' ^ (orderOf z / p) := by
        rw [hwdef, hz'def]
        simpa using (conj_pow (a := q⁻¹) (b := z) (i := orderOf z / p)).symm
      have hcontr : d * (q⁻¹ * w * q) = q⁻¹ * w * q * d := by
        rw [hz'pow]
        exact (hz'd.pow_left (orderOf z / p)).symm
      exact frob4P_not_commute_conj hxM hxp hdM hqQ hdx hdc hwzp hwne hcontr
  have hP'eqU : P' = frU P x := le_antisymm hP'leU hUP'
  rw [← hP'eqU]
  exact hP'syl

end CFSG.LocalAnalysis.UniquenessCase.UC22
