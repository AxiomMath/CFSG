module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddLstar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSimple
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem not_dvd_card_L9_inf_I9_of_center (S : Slice D L D₃ Y H q) (hI : F09.I9 H ≤ D.M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (center ↥(barImage H (F09.L9 Y H)))) :
    ¬ p ∣ Nat.card ↥(F09.L9 Y H ⊓ F09.I9 H) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ↥H, (t₀ : G) = t := ⟨⟨t, L9_le_of_le S.Y_le_H t.2.1⟩, rfl⟩
  have ht₀L : t₀ ∈ (F09.L9 Y H).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf, ht₀]
    exact t.2.1
  have ht₀I : (t₀ : G) ∈ F09.I9 H := by
    rw [ht₀]
    exact t.2.2
  have htp : t₀ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ht₀, Subgroup.coe_one, ← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one,
      Subgroup.coe_one])
  have htb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t₀ ∈ barImage H (F09.L9 Y H) :=
    Subgroup.mem_map_of_mem _ ht₀L
  have hcen : (⟨_, htb⟩ : ↥(barImage H (F09.L9 Y H))) ∈ center ↥(barImage H (F09.L9 Y H)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y₀, hy₀, hw₀⟩ := Subgroup.mem_map.mp w.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    change (w : Bar2 H) * QuotientGroup.mk' (CFSG.pCore 2 ↥H) t₀ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) t₀ * (w : Bar2 H)
    rw [← hw₀, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, show (y₀ * t₀)⁻¹ * (t₀ * y₀) = ⁅t₀⁻¹, y₀⁻¹⁆ by
        rw [commutatorElement_def]; group]
    have hc := S.comm_I9_L9_le hI (Subgroup.commutator_mem_commutator
      ((F09.I9 H).inv_mem ht₀I) ((F09.L9 Y H).inv_mem (Subgroup.mem_subgroupOf.mp hy₀)))
    rw [CFSG.openPCoreOf_eq_map_pCore] at hc
    refine (Subgroup.mem_map_iff_mem H.subtype_injective).mp ?_
    rw [map_commutatorElement, map_inv, map_inv]
    exact hc
  have hord : orderOf (⟨_, htb⟩ : ↥(barImage H (F09.L9 Y H))) = p := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => ?_
    · rw [Subgroup.coe_pow, Subgroup.coe_one]
      change QuotientGroup.mk' (CFSG.pCore 2 ↥H) t₀ ^ p = 1
      rw [← map_pow, htp, map_one]
    · have h1' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t₀ = 1 := congrArg Subtype.val h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1'
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥H) ⟨t₀, h1'⟩
      have hn' : t ^ 2 ^ n = 1 := Subtype.ext (by
        have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hn
        simpa [ht₀] using this)
      have h2 : p ∣ 2 ^ n := ht ▸ orderOf_dvd_of_pow_eq_one hn'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  apply hZ
  have := orderOf_dvd_natCard (⟨_, hcen⟩ : ↥(center ↥(barImage H (F09.L9 Y H))))
  rwa [Subgroup.orderOf_mk, hord] at this

theorem not_dvd_card_center_barImage_L9 (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hJ : IsSpor (F09.Lbar9 Y H) .J1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ Nat.card (center ↥(barImage H (F09.L9 Y H))) := by
  obtain ⟨e⟩ := S.nonempty_lbar9_mulEquiv hyp hI
  obtain ⟨hcomm, hsimp⟩ := S.isQuasisimple_barImage_L9 hyp hI
  haveI : IsSimpleGroup (F09.Lbar9 Y H) := S.isSimpleGroup_Lbar9 hyp
  haveI : Group.IsPerfect (F09.Lbar9 Y H) := Subgroup.isPerfect_iff.mpr (by
    rw [F09.img9, ← Subgroup.map_commutator, S.commutator_subgroupOf_L9 hyp])
  have hnab : ∃ a b : ↥(barImage H (F09.L9 Y H)) ⧸ center ↥(barImage H (F09.L9 Y H)),
      a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative (F09.Lbar9 Y H) := ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul, h])⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (G := F09.Lbar9 Y H) inferInstance
  obtain ⟨j⟩ : Nonempty (F09.Lbar9 Y H ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ
  exact hSp _ ⟨⟨hcomm⟩, hsimp, hnab⟩ (Or.inr (Or.inl ⟨e.symm.trans j⟩)) p hp hp3

theorem normalizer_le_wbar9_of_not_dvd (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) (hI : F09.I9 H ≤ D.M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpLI : ¬ p ∣ Nat.card ↥(F09.L9 Y H ⊓ F09.I9 H)) :
    ∀ Aq : Subgroup (F09.Lbar9 Y H), Aq ≤ xbar9 Y H → Nat.card Aq = p →
      normalizer (Aq : Set (F09.Lbar9 Y H)) ≤ wbar9 D Y H := by
  intro Aq hAq hAp xb hxb
  haveI : Fact p.Prime := ⟨hp⟩
  set Lb := F09.img9 H (F09.L9 Y H)
  have hAb : Nat.card (Aq.map Lb.subtype) = p := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, hAp]
  have hAbX : Aq.map Lb.subtype ≤ F09.img9 H (Opp 3 Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hAq hd
  obtain ⟨A, hAX, hAc, hAD⟩ := S.exists_le_opp_card_eq_img9_eq hp hp2
    (IsPGroup.of_card (n := 1) (by rw [hAb, pow_one])) hAbX
  rw [hAb] at hAc
  have hAH : A ≤ H := hAX.trans ((opp_le 3 Y).trans S.Y_le_H)
  have hAL : A ≤ F09.L9 Y H := hAX.trans (F09.opp_le_L9 Y H)
  have hNA : normalizer (A : Set G) ≤ D.M := hN A (hAX.trans (opp_le 3 Y))
    (by rw [hAc]; exact hp) (by rw [hAc]; exact hp.odd_of_ne_two hp2)
  have hAp' : IsPGroup p (A.subgroupOf H) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc, pow_one])
  have hx : (xb : F09.Hbar9 H) ∈ normalizer ((F09.img9 H A : Subgroup (F09.Hbar9 H)) :
      Set (F09.Hbar9 H)) := by
    rw [hAD]
    exact Subgroup.le_normalizer_map Lb.subtype ⟨xb, hxb, rfl⟩
  obtain ⟨x, hxL, hxx⟩ := Subgroup.mem_map.1 xb.2
  have hxL' : (x : G) ∈ F09.L9 Y H := Subgroup.mem_subgroupOf.1 hxL
  set O : Subgroup ↥H := (F09.L9 Y H ⊓ F09.I9 H).subgroupOf H with hOdef
  haveI hOn : O.Normal := ⟨fun o ho h => by
    rw [hOdef, Subgroup.mem_subgroupOf] at ho ⊢
    have e : ((h * o * h⁻¹ : ↥H) : G) = (h : G) * o * (h : G)⁻¹ := by simp
    rw [e]
    exact ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_L9 Y H h.2) _).mp ho.1,
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H h.2)
        _).mp ho.2⟩⟩
  have hO : p.Coprime (Nat.card O) := by
    rw [hOdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (L9_le_of_le S.Y_le_H))).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpLI
  have hOI : O ≤ CFSG.pPrimeCore 3 ↥H := fun o ho => by
    have h1 : (o : G) ∈ F09.I9 H := (Subgroup.mem_subgroupOf.1 ho).2
    rw [F09.I9] at h1
    exact (Subgroup.mem_map_iff_mem (x := o) H.subtype_injective).1 h1
  have hxN : QuotientGroup.mk' O x ∈ normalizer
      (((A.subgroupOf H).map (QuotientGroup.mk' O) : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hn
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) (x * a * x⁻¹) ∈ F09.img9 H A := by
      rw [map_mul, map_mul, map_inv, hxx]
      exact (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mem_map_of_mem _ ha)
    obtain ⟨a', ha', haa'⟩ := Subgroup.mem_map.1 h1
    obtain ⟨i, hi, hia⟩ := (QuotientGroup.mk'_eq_mk' _).1 haa'
    have hiO : i ∈ O := by
      rw [hOdef, Subgroup.mem_subgroupOf]
      refine ⟨?_, Subgroup.mem_map_of_mem H.subtype hi⟩
      have hi' : i = a'⁻¹ * (x * a * x⁻¹) := by rw [← hia]; group
      have ha'L : (a' : G) ∈ F09.L9 Y H := hAL (Subgroup.mem_subgroupOf.1 ha')
      have haL : (a : G) ∈ F09.L9 Y H := hAL (Subgroup.mem_subgroupOf.1 ha)
      rw [hi']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (F09.L9 Y H).mul_mem ((F09.L9 Y H).inv_mem ha'L)
        ((F09.L9 Y H).mul_mem ((F09.L9 Y H).mul_mem hxL' haL) ((F09.L9 Y H).inv_mem hxL'))
    have hi1 : QuotientGroup.mk' O i = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hiO
    refine Subgroup.mem_map.2 ⟨a', ha', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← hia, map_mul, hi1, mul_one]
  obtain ⟨g, hg, hgx⟩ :=
    CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO hAp' hxN
  obtain ⟨c, hc, hgc⟩ := (QuotientGroup.mk'_eq_mk' _).1 hgx
  have hgM : (g : G) ∈ D.M := by
    apply hNA
    have := Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH] at this
  have hxM : (x : G) ∈ D.M := by
    rw [← hgc, Subgroup.coe_mul]
    exact D.M.mul_mem hgM (hI (Subgroup.mem_map_of_mem H.subtype (hOI hc)))
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 ⟨x.2, hxM⟩, hxx⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
