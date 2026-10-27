module

public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Gen
import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9 GenSeven L9_le_of_le)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc9r96_conj_mem_pCoreOf_I9 {H : Subgroup G} {h o : G} (hh : h ∈ H)
    (ho : o ∈ pCoreOf 2 (F09.I9 H)) : h * o * h⁻¹ ∈ pCoreOf 2 (F09.I9 H) := by
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  exact CFSG.HardMathSupport.Cooperstein.Proving.conj_mem_pCoreOf (hHI hh) ho

private theorem uc9r96_eq_one_of_conj_eq_mul {K : Type} [Group K] {u v w : K} {m n : ℕ}
    (h : u * v * u⁻¹ = v * w) (hwu : Commute w u) (hwv : Commute w v) (hm : Commute (u ^ m) v)
    (hn : v ^ n = 1) (hmn : m.Coprime n) : w = 1 := by
  have key : ∀ k : ℕ, u ^ k * v * (u ^ k)⁻¹ = v * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : u * w ^ k * u⁻¹ = w ^ k := by
        rw [← (hwu.pow_left k).eq, mul_inv_cancel_right]
      calc u ^ (k + 1) * v * (u ^ (k + 1))⁻¹ = u * (u ^ k * v * (u ^ k)⁻¹) * u⁻¹ := by group
        _ = u * v * u⁻¹ * (u * w ^ k * u⁻¹) := by rw [ih]; group
        _ = v * w ^ (k + 1) := by rw [h, e1]; group
  have hwm : w ^ m = 1 := by
    have h1 := key m
    rw [hm.eq, mul_inv_cancel_right] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one v).symm)
  have hwn : w ^ n = 1 := by
    have h1 : (v * w) ^ n = 1 := by
      rw [← h, conj_pow, hn, mul_one, mul_inv_cancel]
    rwa [hwv.symm.mul_pow, hn, one_mul] at h1
  have hd : orderOf w ∣ Nat.gcd m n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hwm) (orderOf_dvd_of_pow_eq_one hwn)
  rwa [hmn.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd

private theorem uc9r96_mk_mul_mk_comm {K : Type} [Group K] {N O T : Subgroup K} [O.Normal]
    (hT : ∀ y ∈ T, ∀ i ∈ N, y * i * y⁻¹ * i⁻¹ ∈ O) {x a : K} {m : ℕ} (hx : x ∈ T) (ha : a ∈ T)
    (hxm : x ^ m ∈ N) (ha7 : a ^ 7 = 1) (hm : m.Coprime 7) (hj : a⁻¹ * (x * a * x⁻¹) ∈ N) :
    QuotientGroup.mk' O a * QuotientGroup.mk' O x =
      QuotientGroup.mk' O x * QuotientGroup.mk' O a := by
  have hc : ∀ y ∈ T, ∀ i ∈ N, Commute (QuotientGroup.mk' O i) (QuotientGroup.mk' O y) := by
    intro y hy i hi
    have h1 : y * i * y⁻¹ * i⁻¹ ∈ (QuotientGroup.mk' O).ker := by
      rw [QuotientGroup.ker_mk']
      exact hT y hy i hi
    rw [MonoidHom.mem_ker] at h1
    simp only [map_mul, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  have hw := uc9r96_eq_one_of_conj_eq_mul (u := QuotientGroup.mk' O x) (v := QuotientGroup.mk' O a)
    (w := QuotientGroup.mk' O (a⁻¹ * (x * a * x⁻¹))) (m := m) (n := 7)
    (by simp only [map_mul, map_inv]; group) (hc x hx _ hj) (hc a ha _ hj)
    (by rw [← map_pow]; exact hc a ha _ hxm) (by rw [← map_pow, ha7, map_one]) hm
  simp only [map_mul, map_inv] at hw
  exact eq_mul_inv_iff_mul_eq.1 (inv_mul_eq_one.1 hw)

namespace Core

variable {D : Data G} {Y H : Subgroup G} {q : ℕ}

theorem mul_mul_inv_mul_inv_mem_pCoreOf (S : Core D Y H q) (h17 : F09.I9 H ≤ D.M)
    {y i : G} (hy : y ∈ F09.L9 Y H) (hi : i ∈ F09.I9 H) :
    y * i * y⁻¹ * i⁻¹ ∈ pCoreOf 2 (F09.I9 H) := by
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hI3 : ¬ 3 ∣ Nat.card (F09.I9 H) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H)
  have hIX : ⁅F09.I9 H, Opp 3 Y⁆ ≤ pCoreOf 2 (F09.I9 H) :=
    S.comm_le (F09.I9 H) (Subgroup.map_subtype_le _) h17 hI3 (S.opp_le_H.trans hHI)
  suffices hC : y ∈ H ∧ ∀ i ∈ F09.I9 H, y * i * y⁻¹ * i⁻¹ ∈ pCoreOf 2 (F09.I9 H) from hC.2 i hi
  refine Subgroup.iSup_induction (C := fun y => y ∈ H ∧
    ∀ i ∈ F09.I9 H, y * i * y⁻¹ * i⁻¹ ∈ pCoreOf 2 (F09.I9 H)) _ hy ?_ ?_ ?_
  · rintro h _ ⟨x, hx, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem h.2 (S.opp_le_H hx)) (H.inv_mem h.2), fun i hi => ?_⟩
    have hi' : (h : G)⁻¹ * i * h ∈ F09.I9 H := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hHI (H.inv_mem h.2)) i).mp hi
    have hc : ⁅x, (h : G)⁻¹ * i * h⁆ ∈ pCoreOf 2 (F09.I9 H) :=
      hIX (by rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator hx hi')
    rw [commutatorElement_def] at hc
    have := uc9r96_conj_mem_pCoreOf_I9 h.2 hc
    convert this using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · exact ⟨H.one_mem, fun i _ => by simpa using (pCoreOf 2 (F09.I9 H)).one_mem⟩
  · rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨H.mul_mem ha hb, fun i hi => ?_⟩
    have e : a * b * i * (a * b)⁻¹ * i⁻¹ =
        a * (b * i * b⁻¹ * i⁻¹) * a⁻¹ * (a * i * a⁻¹ * i⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 (F09.I9 H)).mul_mem (uc9r96_conj_mem_pCoreOf_I9 ha (hB i hi)) (hA i hi)

theorem mem_wbar9_of_mem_centralizer (S : Core D Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) (h17 : F09.I9 H ≤ D.M) :
    ∀ Aq : Subgroup (F09.Lbar9 Y H), Aq ≤ xbar9 Y H → Nat.card Aq = 7 →
      ∀ x ∈ centralizer (Aq : Set (F09.Lbar9 Y H)), Nat.Coprime (orderOf x) 7 →
        x ∈ wbar9 D Y H := by
  intro Aq hAq h7 xb hxb hcop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Lb := F09.img9 H (F09.L9 Y H)
  have hAb : Nat.card (Aq.map Lb.subtype) = 7 := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, h7]
  have hAbX : Aq.map Lb.subtype ≤ F09.img9 H (Opp 3 Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hAq hd
  obtain ⟨A, hAX, hAc, hAD⟩ := S.exists_le_opp_card_eq_img9_eq (p := 7) (by norm_num)
    (by norm_num) (IsPGroup.of_card (n := 1) (by rw [hAb, pow_one])) hAbX
  rw [hAb] at hAc
  have hAH : A ≤ H := hAX.trans S.opp_le_H
  have hNA : normalizer (A : Set G) ≤ D.M :=
    hN A hAX (by rw [hAc]; norm_num) (by rw [hAc]; decide)
  have hPc : Nat.card (A.subgroupOf H) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc]
  have hP7 : IsPGroup 7 (A.subgroupOf H) := IsPGroup.of_card (n := 1) (by rw [hPc, pow_one])
  obtain ⟨x, hxL, hxx⟩ := Subgroup.mem_map.1 xb.2
  have hxG : (x : G) ∈ F09.L9 Y H := Subgroup.mem_subgroupOf.1 hxL
  set O : Subgroup ↥H := (pCoreOf 2 (F09.I9 H)).subgroupOf H with hOdef
  have hOn : O.Normal := ⟨fun o ho h => by
    rw [hOdef, Subgroup.mem_subgroupOf] at ho ⊢
    simpa using uc9r96_conj_mem_pCoreOf_I9 h.2 ho⟩
  have hO7 : Nat.Coprime 7 (Nat.card O) := by
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (F09.I9 H)) := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact CFSG.pCore_isPGroup.map _
    have hO2 : IsPGroup 2 O := hP2.comap_of_injective H.subtype H.subtype_injective
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hOI : O ≤ CFSG.pPrimeCore 3 ↥H := fun o ho => by
    have h1 := Subgroup.mem_subgroupOf.1 ho
    rw [CFSG.openPCoreOf_eq_map_pCore] at h1
    have h2 : (o : G) ∈ F09.I9 H := Subgroup.map_subtype_le _ h1
    rw [F09.I9] at h2
    exact (Subgroup.mem_map_iff_mem (x := o) H.subtype_injective).1 h2
  have hT : ∀ y ∈ (F09.L9 Y H).subgroupOf H, ∀ i ∈ CFSG.pPrimeCore 3 ↥H,
      y * i * y⁻¹ * i⁻¹ ∈ O := by
    intro y hy i hi
    rw [hOdef, Subgroup.mem_subgroupOf]
    simpa using S.mul_mul_inv_mul_inv_mem_pCoreOf h17 (Subgroup.mem_subgroupOf.1 hy)
      (Subgroup.mem_map_of_mem H.subtype hi)
  have hxm : x ^ orderOf xb ∈ CFSG.pPrimeCore 3 ↥H := by
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) (x ^ orderOf xb) = 1 := by
      rw [map_pow, hxx, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hxN : QuotientGroup.mk' O x ∈ normalizer
      (((A.subgroupOf H).map (QuotientGroup.mk' O) : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have haG : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) a ∈ F09.img9 H A :=
      Subgroup.mem_map_of_mem _ ha
    rw [hAD] at h1
    obtain ⟨ab, hab, hab'⟩ := Subgroup.mem_map.1 h1
    have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxb ab hab)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxx] at h2
    rw [Subgroup.coe_subtype] at hab'
    rw [hab'] at h2
    refine uc9r96_mk_mul_mk_comm hT hxL (Subgroup.mem_subgroupOf.2 (F09.opp_le_L9 Y H (hAX haG)))
      hxm ?_ hcop ?_
    · have h3 := pow_card_eq_one' (G := ↥(A.subgroupOf H)) (x := ⟨a, ha⟩)
      rw [hPc] at h3
      simpa using congrArg Subtype.val h3
    · have h3 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) (a⁻¹ * (x * a * x⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [← h2]
        group
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨g, hg, hgx⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
    (by norm_num : Nat.Prime 7) O hO7 hP7 hxN
  obtain ⟨c, hc, hgc⟩ := (QuotientGroup.mk'_eq_mk' _).1 hgx
  have hc1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) c = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hOI hc
  have hgM : (g : G) ∈ D.M := by
    apply hNA
    have := Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH] at this
  rw [wbar9, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 ⟨g.2, hgM⟩, ?_⟩
  rw [← hxx, ← hgc, map_mul, hc1, mul_one]

theorem false_of_genSeven (S : Core D Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    (h92L : H = F09.L9 Y H ⊔ (H ⊓ D.M)) (h17 : F09.I9 H ≤ D.M)
    (hgen : GenSeven (F09.Lbar9 Y H) (xbar9 Y H)) : False := by
  have hXH : Opp 3 Y ≤ H := S.opp_le_H
  have hXM : Opp 3 Y ≤ H ⊓ D.M := le_inf hXH S.opp_le_M
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (H ⊓ D.M) :=
    Subgroup.map_mono fun y hy => hXM hy
  have hXW : xbar9 Y H ≤ wbar9 D Y H := fun z hz =>
    Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hz))
  have htop := hgen (wbar9 D Y H) hXW (S.normalizer_le_wbar9 hN)
    (S.mem_wbar9_of_mem_centralizer hN h17)
  have hLM : F09.L9 Y H ≤ D.M := by
    intro l hl
    have hlH : l ∈ H := L9_le_of_le S.Y_le_H hl
    have hl' : (⟨l, hlH⟩ : ↥H) ∈ (F09.L9 Y H).subgroupOf H := Subgroup.mem_subgroupOf.2 hl
    have hmem : (⟨_, Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) hl'⟩ :
        F09.Lbar9 Y H) ∈ wbar9 D Y H := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hmem)
    have hgl' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) g =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ := hgl
    obtain ⟨c, hc, hgc⟩ := (QuotientGroup.mk'_eq_mk' _).1 hgl'
    have hlc : l = (g : G) * (c : G) := by rw [← Subgroup.coe_mul, hgc]
    rw [hlc]
    exact D.M.mul_mem (Subgroup.mem_subgroupOf.1 hg).2 (h17 (Subgroup.mem_map_of_mem H.subtype hc))
  exact S.not_H_le_M (h92L.le.trans (sup_le hLM inf_le_right))

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
