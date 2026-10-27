module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154R1110SecA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Five

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R1110Second (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ n : ℕ, 1 < n → ∀ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal →
        IsElemAbelian p Xbar → Nat.card Xbar = p ^ n →
        Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ →
        (D.sig = D.sig1 → ∀ v ∈ V, v ≠ 1 →
          1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) →
            UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)))

theorem r1110G_of_core_second (D : Data G) (hC : R1110Core D) (hS : R1110Second D) :
    R1110G D := by
  intro V₀ V hV _ p hp hp2 P hP
  obtain ⟨h1, h2, h3⟩ := hC V₀ V hV p hp hp2 P hP
  exact ⟨h1, h2, fun n hn Xbar hXn hXe hXc hXle =>
    ⟨h3 n hn Xbar hXn hXe hXc hXle, hS V₀ V hV p hp hp2 n hn Xbar hXn hXe hXc hXle⟩⟩

private theorem s16h_exists_conj_le {p : ℕ} (hp : p.Prime) {K H B : Subgroup G}
    (hBK : B ≤ K) (hB : IsPGroup p B) (hindex : ¬ p ∣ H.relIndex K) :
    ∃ k ∈ K, conjSubgroup B k ≤ H := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Hk : Subgroup ↥K := H.subgroupOf K
  have hBk : IsPGroup p (B.subgroupOf K) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBK).symm
  have hindexK : ¬ p ∣ Nat.card (↥K ⧸ Hk) := by
    rw [← Subgroup.index_eq_card (H := Hk)]
    exact hindex
  obtain ⟨q, hq⟩ := hBk.nonempty_fixed_point_of_prime_not_dvd_card (↥K ⧸ Hk) hindexK
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ x : B.subgroupOf K, k⁻¹ * (x : ↥K) * k ∈ Hk := by
    intro x
    have hb : ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      have := (MulAction.mem_fixedPoints.mp hq) x⁻¹
      simpa only [Subgroup.smul_def] using this
    have hb' : (QuotientGroup.mk (((x⁻¹ : B.subgroupOf K) : ↥K) * k) : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      change ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k
      exact hb
    have h := QuotientGroup.eq.mp hb'
    have heq : ((((x⁻¹ : B.subgroupOf K) : ↥K)) * k)⁻¹ * k = k⁻¹ * (x : ↥K) * k := by
      rw [Subgroup.coe_inv (x := x)]
      group
    rwa [heq] at h
  refine ⟨(k : G), k.2, ?_⟩
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hb : (k : G) * x * (k : G)⁻¹ ∈ B := hx
  have hmem0 : (⟨(k : G) * x * (k : G)⁻¹, hBK hb⟩ : ↥K) ∈ B.subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr hb
  let xB : ↥(B.subgroupOf K) := ⟨(⟨(k : G) * x * (k : G)⁻¹, hBK hb⟩ : ↥K), hmem0⟩
  have hmem := Subgroup.mem_subgroupOf.mp (hfix xB)
  have heq : (↑(k⁻¹ * (↑xB : ↥K) * k) : G) = x := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, xB]
    group
  rwa [heq] at hmem

private theorem s16h_gamma_conj_le {p : ℕ} (hp : p.Prime) {B M : Subgroup G} {x : G}
    (hx : x ∈ M) (hΓ : rankThreeGamma 1 p B ≤ M) : rankThreeGamma 1 p (conjSubgroup B x) ≤ M := by
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q hQ hrank => ?_
  have hQB : conjSubgroup Q x⁻¹ ≤ B := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hy' : x⁻¹ * y * x ∈ Q := by simpa only [inv_inv] using hy
    have h1 : x⁻¹ * y * x ∈ conjSubgroup B x := hQ hy'
    rw [mem_conjSubgroup_iff] at h1
    have heq : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [heq] at h1
  have hrank' : 1 ≤ CFSG.Open.pRank p (conjSubgroup Q x⁻¹) := by
    have h := CFSG.SectionRank.pRank_le_map hp.one_lt
      (MulAut.conj (x⁻¹)⁻¹).toMonoidHom (MulAut.conj (x⁻¹)⁻¹).injective Q
    exact hrank.trans h
  have hNQ' : Subgroup.normalizer (conjSubgroup Q x⁻¹ : Set G) ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQB hrank').trans hΓ
  have key : ∀ n : G, n ∈ Subgroup.normalizer (Q : Set G) →
      x * n * x⁻¹ ∈ Subgroup.normalizer (conjSubgroup Q x⁻¹ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    simp only [mem_conjSubgroup_iff, inv_inv]
    constructor
    · intro hy
      have h := (hn (x⁻¹ * y * x)).mp hy
      have heq : x⁻¹ * (x * n * x⁻¹ * y * (x * n * x⁻¹)⁻¹) * x =
          n * (x⁻¹ * y * x) * n⁻¹ := by group
      rwa [heq]
    · intro hy
      have h : n * (x⁻¹ * y * x) * n⁻¹ ∈ Q := by
        have heq : x⁻¹ * (x * n * x⁻¹ * y * (x * n * x⁻¹)⁻¹) * x =
            n * (x⁻¹ * y * x) * n⁻¹ := by group
        rwa [heq] at hy
      exact (hn (x⁻¹ * y * x)).mpr h
  intro n hn
  have h2 : x * n * x⁻¹ ∈ M := hNQ' (key n hn)
  have heq : n = x⁻¹ * (x * n * x⁻¹) * x := by group
  rw [heq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hx) h2) hx

theorem r1110Second_holds (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h1110 : R1110Core D) :
    R1110Second D := by
  intro V₀ V hV _ p hp hp2 n hn Xbar hXn hXe hXc hXd hσ v hvV hv1 hrk
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
    with hYdef
  have hYIn : F11.InP11 D Y := by
    rw [hYdef]
    exact s16e_d3_inP11 D hSg hσ h1110 h77 hV hp hp2 hn Xbar hXn hXe hXc hXd hP
  have hYInKeep : F11.InP11 D Y := hYIn
  obtain ⟨p', hp'pr, -, -, hYp', -, hYnc, -, hYΓ', -⟩ := hYIn
  have hYexpP : ∀ x ∈ Y, x ^ p = 1 := by
    rw [hYdef]
    exact ((h1110 V₀ V hV p hp hp2 P hP).2.2 n hn Xbar hXn hXe hXc hXd).1
  have hYnebot : Y ≠ ⊥ := by
    intro hbot
    exact hYnc (by rw [hbot]; exact isCyclic_of_subsingleton)
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYnebot
  haveI : Fact p'.Prime := ⟨hp'pr⟩
  have hpdvd : orderOf y ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (hYexpP y.1 y.2)
  have hp'dvd : p' ∣ orderOf y := hYp'.dvd_orderOf hy1
  have horder : orderOf y = p := by
    rcases (Nat.dvd_prime hp).1 hpdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hp'eq : p' = p := (Nat.prime_dvd_prime_iff_eq hp'pr hp).1 (horder ▸ hp'dvd)
  have hYΓ : rankThreeGamma 1 p Y ≤ D.M := by rw [← hp'eq]; exact hYΓ'
  have hcard4 : Nat.card V₀ ≤ 4 := by
    have hcard8 : Nat.card V₀ < 8 := by
      by_contra h
      rw [not_lt] at h
      exact (hV.2.2 h).2 Y hYInKeep
    rcases hV.1 with h0 | ⟨hbot, -⟩
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h0.1.2.2.2.isPGroup
      have hk8 : 2 ^ k < 8 := by simpa only [hk] using hcard8
      have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hk8
      calc Nat.card V₀ = 2 ^ k := hk
        _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    · rw [hbot, Subgroup.card_bot]
      norm_num
  have hMn : D.M ≤ normalizer (V₀ : Set G) := by
    rcases hV.1 with h0 | ⟨hbot, -⟩
    · exact h0.1.2.2.1
    · rw [hbot]
      intro m _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
  by_cases hv0 : v ∈ V₀
  · obtain ⟨q, hq⟩ := hx.sig_nonempty
    obtain ⟨hqpr, hq2⟩ := D.sig_prime q hq
    have hq3 : 3 ≤ q := by have := hqpr.two_le; omega
    obtain ⟨E, hEM, hEea, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hqpr (by
        rw [UC6.groupPRank_eq_pRank]
        exact hx.three_le q hq)
    let S : Set G := {x | x ∈ V₀ ∧ x ≠ 1}
    have hSfin : S.Finite := Set.toFinite S
    have hS3 : S.ncard ≤ 3 := by
      have hins : insert (1 : G) S ⊆ (V₀ : Set G) := by
        intro x hx
        rw [Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact V₀.one_mem
        · exact hx.1
      have h1not : (1 : G) ∉ S := by intro h; exact h.2 rfl
      have hcard := Set.ncard_le_ncard hins
      rw [Set.ncard_insert_of_notMem h1not hSfin] at hcard
      have hV₀' : (V₀ : Set G).ncard ≤ 4 := by
        rw [← Nat.card_coe_set_eq]; exact hcard4
      omega
    have hSw : ∀ e ∈ E, e * v * e⁻¹ ∈ S := by
      intro e he
      refine ⟨?_, ?_⟩
      · exact ((Subgroup.mem_normalizer_iff.1 (hMn (hEM he))) v).1 hv0
      · intro h
        exact hv1 (by
          calc v = e⁻¹ * (e * v * e⁻¹) * e := by group
            _ = 1 := by rw [h]; group)
    have hnc := c23_not_isCyclic_inf_centralizer hqpr hq3 hEea hEcard hS3 hSw
    have hE'p : IsPGroup q ↥(E ⊓ centralizer ({v} : Set G)) :=
      (IsElemAbelian.mono hEea inf_le_left).isPGroup
    have huniq : UniqueMax D.M (E ⊓ centralizer ({v} : Set G)) :=
      h61 q hq (E ⊓ centralizer ({v} : Set G)) (inf_le_left.trans hEM) hE'p hnc
    exact uc22p22u_uniqueMax_mono D (le_inf (inf_le_left.trans hEM) inf_le_right) inf_le_left huniq
  · obtain ⟨B, hBY, hBcE, hBnc⟩ :=
      s16h_ten_second_noncyclic D h1110 hV hp hp2 hP hn Xbar hXn hXe hXc hXd hvV hrk
    have hBY' : B ≤ Y := by rw [hYdef]; exact hBY
    have hBp : IsPGroup p B := hp'eq ▸ hYp'.to_le hBY'
    obtain ⟨n', -, hn'⟩ := r113_holds D V₀ V hV hcard4 v hvV hv0
    have hindex : ¬ p ∣ (D.M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt D.M V₀ v) := by
      rw [hn']
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
    obtain ⟨k, hkK, hB'leH⟩ := s16h_exists_conj_le hp hBcE hBp hindex
    have hkM : k ∈ D.M := hkK.1
    have hB'p : IsPGroup p (conjSubgroup B k) :=
      hBp.of_equiv (Subgroup.equivMapOfInjective B (MulAut.conj k⁻¹).toMonoidHom
        (MulAut.conj k⁻¹).injective)
    have hB'nc : ¬ IsCyclic ↥(conjSubgroup B k) := fun hc =>
      hBnc ((Subgroup.equivMapOfInjective B (MulAut.conj k⁻¹).toMonoidHom
        (MulAut.conj k⁻¹).injective).isCyclic.2 hc)
    have hBΓ : rankThreeGamma 1 p B ≤ D.M := (uc22p22u_gamma_mono hBY').trans hYΓ
    have hB'Γ : rankThreeGamma 1 p (conjSubgroup B k) ≤ D.M := s16h_gamma_conj_le hp hkM hBΓ
    have hUniq := uc22p22u_uniqueMax_of_noncyclic D h61 h63 hp hp2
      (hB'leH.trans inf_le_left) hB'p hB'nc (Or.inl hB'Γ)
    exact uc22p22u_uniqueMax_mono D hB'leH inf_le_left hUniq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
