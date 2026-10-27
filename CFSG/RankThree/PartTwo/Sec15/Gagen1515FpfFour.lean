module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfX0
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import TauCeti.GroupTheory.ExponentPrime
import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.TripleCover
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem exists_y_notMem_zpowers
    (h : Ctx A c L d) :
    ∃ y : G, y ∈ A ⊓ L ∧ y ∉ Subgroup.zpowers d := by
  obtain ⟨-, h9, -⟩ := j2_point_facts h.sec13Data h.conf.j2
  have hdAL : d ∈ A ⊓ L := ⟨h.mem_d, h.mem_L⟩
  have hd3pow : d ^ 3 = 1 := h.isE27.1.2 d h.mem_d
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3pow h.ne_d
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hdord]
  by_contra hcon
  push Not at hcon
  have hle : A ⊓ L ≤ Subgroup.zpowers d := fun z hz => hcon z hz
  have hcard := Subgroup.card_le_of_le hle
  rw [h9, hd3] at hcard
  omega

theorem conj_mulAut_pow_three_ne_one_of_notMem {y : G} (hyX : y ∈ x₀ L d)
    (hy3 : y ^ 3 = 1) (hyd : y ∉ Subgroup.zpowers d)
    (hcenter : (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype = Subgroup.zpowers d) :
    (MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d))) ^ 3 = 1 ∧
      MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d)) ≠ 1 := by
  have hyQ3 : (⟨y, hyX⟩ : ↥(x₀ L d)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  refine ⟨?_, ?_⟩
  · change (MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d)) : MulAut ↥(x₀ L d)) ^ 3 = 1
    rw [← map_pow, hyQ3, map_one]
  · intro hf
    apply hyd
    have hycenter : (⟨y, hyX⟩ : ↥(x₀ L d)) ∈ Subgroup.center ↥(x₀ L d) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h := congrArg (fun φ : MulAut ↥(x₀ L d) => φ z) hf
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h' : (⟨y, hyX⟩ : ↥(x₀ L d)) * z = z * (⟨y, hyX⟩ : ↥(x₀ L d)) := by
        calc (⟨y, hyX⟩ : ↥(x₀ L d)) * z =
            ((⟨y, hyX⟩ : ↥(x₀ L d)) * z * (⟨y, hyX⟩ : ↥(x₀ L d))⁻¹) *
              (⟨y, hyX⟩ : ↥(x₀ L d)) := by group
          _ = z * (⟨y, hyX⟩ : ↥(x₀ L d)) := by rw [h]
      exact h'.symm
    have hymap : y ∈ (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype :=
      ⟨⟨y, hyX⟩, hycenter, rfl⟩
    rwa [hcenter] at hymap

theorem conj_mem_normalizer_map_subtype {y : G} (hyX : y ∈ x₀ L d)
    {V : Subgroup ↥(x₀ L d)}
    (hVinv : ∀ g ∈ Subgroup.zpowers (MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d))),
      ∀ v ∈ V, g v ∈ V) :
    y ∈ Subgroup.normalizer ((V.map (x₀ L d).subtype : Subgroup G) : Set G) := by
  let f : MulAut ↥(x₀ L d) := MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d))
  have hVinv' : ∀ g ∈ Subgroup.zpowers f, ∀ v ∈ V, g v ∈ V := hVinv
  rw [Subgroup.mem_normalizer_iff']
  intro n
  constructor
  · rintro ⟨v, hv, hv_eq⟩
    have hv_eq' : (v : G) = n * y := hv_eq
    refine ⟨f v, hVinv' f (Subgroup.mem_zpowers f) v hv, ?_⟩
    have hn_eq : n = (v : G) * y⁻¹ := by
      calc n = (n * y) * y⁻¹ := by group
        _ = (v : G) * y⁻¹ := by rw [hv_eq']
    rw [hn_eq]
    change (((MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d))) v : ↥(x₀ L d)) : G) =
      y * ((v : G) * y⁻¹)
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_subtype]
    group
  · rintro ⟨v, hv, hv_eq⟩
    have hv_eq' : (v : G) = y * n := hv_eq
    have hf'inv : MulAut.conj ((⟨y, hyX⟩ : ↥(x₀ L d))⁻¹) = f⁻¹ := by
      rw [show f = MulAut.conj (⟨y, hyX⟩ : ↥(x₀ L d)) from rfl, ← map_inv]
    refine ⟨MulAut.conj ((⟨y, hyX⟩ : ↥(x₀ L d))⁻¹) v, ?_, ?_⟩
    · rw [hf'inv]
      exact hVinv' (f⁻¹) (Subgroup.inv_mem _ (Subgroup.mem_zpowers f)) v hv
    · have hn_eq : n = y⁻¹ * (v : G) := by
        calc n = y⁻¹ * (y * n) := by group
          _ = y⁻¹ * (v : G) := by rw [hv_eq']
      rw [hn_eq]
      simp only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_subtype]

theorem inf_eq_sup_zpowers_of_card_nine
    (h : Ctx A c L d) {y : G} (hyAL : y ∈ A ⊓ L)
    (hyd : y ∉ Subgroup.zpowers d) :
    A ⊓ L = (Subgroup.zpowers d ⊔ Subgroup.zpowers y : Subgroup G) := by
  obtain ⟨-, h9, -⟩ := j2_point_facts h.sec13Data h.conf.j2
  have hdAL : d ∈ A ⊓ L := ⟨h.mem_d, h.mem_L⟩
  have hd3pow : d ^ 3 = 1 := h.isE27.1.2 d h.mem_d
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3pow h.ne_d
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hdord]
  have hyA : y ∈ A := hyAL.1
  have hy3pow : y ^ 3 = 1 := h.isE27.1.2 y hyA
  have hy1 : y ≠ 1 := by
    intro h1
    exact hyd (h1 ▸ Subgroup.one_mem (Subgroup.zpowers d))
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3pow hy1
  have hy3 : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hyord]
  have hcomm_dy : ∀ x ∈ Subgroup.zpowers d, ∀ z ∈ Subgroup.zpowers y, x * z = z * x := by
    intro x hx z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow (h.sec13Data.commute hdAL.1 hyAL.1) m n).eq
  have hinf_bot : (Subgroup.zpowers d ⊓ Subgroup.zpowers y : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hzd : z ∈ Subgroup.zpowers d := hz.1
    have hzy : z ∈ Subgroup.zpowers y := hz.2
    have hz_eq : Subgroup.zpowers z = Subgroup.zpowers d :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers (y := d) (z := z) Nat.prime_three
        hd3pow hz1 hzd
    have hd_mem_y : d ∈ Subgroup.zpowers y := by
      have hle : Subgroup.zpowers d ≤ Subgroup.zpowers y := by
        rw [← hz_eq]
        exact Subgroup.zpowers_le.mpr hzy
      exact hle (Subgroup.mem_zpowers d)
    have hy_eq : Subgroup.zpowers d = Subgroup.zpowers y :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers (y := y) (z := d) Nat.prime_three
        hy3pow h.ne_d hd_mem_y
    exact hyd (hy_eq.symm ▸ Subgroup.mem_zpowers y)
  have hcard_sup : Nat.card
      (Subgroup.zpowers d ⊔ Subgroup.zpowers y : Subgroup G) = 9 := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers d) (Subgroup.zpowers y) hcomm_dy).1
    rw [hinf_bot, Subgroup.card_bot, mul_one, hd3, hy3] at hcard
    omega
  refine (Subgroup.eq_of_le_of_card_ge (K := A ⊓ L) ?_ ?_).symm
  · exact sup_le (Subgroup.zpowers_le.mpr hdAL) (Subgroup.zpowers_le.mpr hyAL)
  · rw [h9, hcard_sup]

theorem exists_four
    (h142 : Concl142 A (lB A)) (h : Ctx A c L d) :
    ∃ T : Subgroup G, T ≤ x₀ L d ∧ T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧
      A ≤ Subgroup.normalizer (T : Set G) ∧ T ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyAL, hyd⟩ := exists_y_notMem_zpowers h
  have hyA : y ∈ A := hyAL.1
  have hy3pow : y ^ 3 = 1 := h.isE27.1.2 y hyA
  have hyX : y ∈ x₀ L d := h.inf_le_x₀ hyAL
  obtain ⟨hf3, hf1⟩ := conj_mulAut_pow_three_ne_one_of_notMem hyX hy3pow hyd h.center_x₀
  obtain ⟨hperf, htc, -, -, -, -, -⟩ := h.residual_facts
  obtain ⟨hZcard, ⟨e⟩⟩ := htc
  let Q := ↥(x₀ L d)
  haveI : Group.IsPerfect Q := hperf
  obtain ⟨V, hVne, hV2, hVinv⟩ :=
    CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.exists_V_of_order_three hZcard e hf3 hf1
  set T : Subgroup G := V.map (x₀ L d).subtype with hT
  have hTX0 : T ≤ x₀ L d := Subgroup.map_subtype_le V
  have hTne : T ≠ ⊥ := by
    intro hbot
    exact hVne ((Subgroup.map_eq_bot_iff_of_injective V (x₀ L d).subtype_injective).mp hbot)
  have hT2 : IsPGroup 2 ↥T := hV2.map (x₀ L d).subtype
  have hyN : y ∈ Subgroup.normalizer (T : Set G) := by
    rw [hT]
    exact conj_mem_normalizer_map_subtype hyX hVinv
  obtain ⟨-, -, hAeq⟩ := j2_point_facts h.sec13Data h.conf.j2
  have hALeq := inf_eq_sup_zpowers_of_card_nine h hyAL hyd
  have hAgen : A = Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers y := by
    calc A = Subgroup.zpowers c ⊔ (A ⊓ L) := hAeq
      _ = Subgroup.zpowers c ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers y : Subgroup G) := by
        rw [hALeq]
      _ = (Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers y : Subgroup G) :=
        (sup_assoc _ _ _).symm
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := hTX0.trans h.x₀_le_centralizer
  have hTd : T ≤ Subgroup.centralizer ({d} : Set G) :=
    hTX0.trans (Item148HJ.residual_le_centralizer_singleton L d)
  have hcN : c ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTc ht))
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTd ht))
  have hAN : A ≤ Subgroup.normalizer (T : Set G) := by
    rw [hAgen]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcN) (Subgroup.zpowers_le.mpr hdN))
      (Subgroup.zpowers_le.mpr hyN)
  have hT3 : IsPiSubgroup (piCompl 3) T := by
    have hcop : Nat.Coprime 3 (Nat.card T) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    exact (isPiSubgroup_piCompl_iff Nat.prime_three T).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  have hQ := Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 h.isE27 h142
    h.sec13Data.zpowers_mem_omegaA hT3 hAN
  have hTc' : T ⊓ Subgroup.centralizer ({c} : Set G) = T := inf_eq_left.mpr hTc
  refine ⟨T, hTX0, hTne, hT2, hAN, ?_⟩
  rwa [hTc'] at hQ

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
