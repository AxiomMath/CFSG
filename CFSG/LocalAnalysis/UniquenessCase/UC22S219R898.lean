module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229G898
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s219r_two_le_pRank_centralizer {M L : Subgroup G} (hLM : L ≤ M) {n : ℕ}
    (hX : IsSU3 (Bar2 L) n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpn : ¬ p ∣ 2 * n) (hpq : ¬ p ∣ 2 ^ n + 1) {B : Subgroup G} (hBM : B ≤ M)
    (hBN : B ≤ normalizer (L : Set G)) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup G} (hEL : E ≤ L) (hE : IsPGroup q E) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥B →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hBN)
  have hpow : ∀ b : ↥B, φ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (by simpa using hBel.2 _ b.2)
    rw [this, map_one]
  have hinn : φ.range ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    rintro _ ⟨b, rfl⟩
    exact uc22ine229_mem_inner hX hp hp3 hpn (hpow b)
  have hRel : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hBel.subgroupOf B).map φ
  have hR : Nat.card φ.range ≤ p := UCK.u3RankOne (Bar2 L) n hX p hp hp2 hpq _ hinn hRel
  have hKc : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : p * p ^ 2 ≤ p * Nat.card φ.ker :=
      calc p * p ^ 2 = Nat.card φ.ker * Nat.card φ.range := by
            rw [Subgroup.card_ker_mul_card_range, hBcard]
            ring
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hR
        _ = p * Nat.card φ.ker := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  let K : Subgroup G := φ.ker.map B.subtype
  have hKB : K ≤ B := Subgroup.map_subtype_le _
  have hKcard : p ^ 2 ≤ Nat.card K := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hKc
  obtain ⟨A, hAK, hAel, hAc⟩ := UC6S846.exists_card_p_sq hp (hBel.mono hKB) hKcard
  have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hp hp2
    (pCoreOf 2 L) A E (UC6S846.isPGroup_pCoreOf L) ((hAK.trans (hKB.trans hBN)).trans hNO)
    ((hEL.trans Subgroup.le_normalizer).trans hNO) hAel.isPGroup hE (fun e he a ha => by
      obtain ⟨b, hb, rfl⟩ := hAK ha
      have h1 : UC6S846.rhoL L (Subgroup.inclusion hBN b) = 1 := hb
      have h2 : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ pCoreOf 2 L :=
        (UC6S846.rhoL_fix_iff L (Subgroup.inclusion hBN b) ⟨e, hEL he⟩).1
          (by rw [h1, MulAut.one_apply])
      have h3 : e * (b : G) * e⁻¹ * (b : G)⁻¹ = ((b : G) * e * (b : G)⁻¹ * e⁻¹)⁻¹ := by group
      change e * (b : G) * e⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 L
      rw [h3]
      exact inv_mem h2)
  have hA'M : A' ≤ M :=
    hA'le.trans (sup_le (hAK.trans (hKB.trans hBM)) ((Subgroup.map_subtype_le _).trans hLM))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  exact UC6S846.le_pRank' hp (le_inf hA'M hA'C) hA'el hA'c

theorem uc22s219r_gamma_three (D : Data G) (hSg : UC6S846.SigmaStd D) (hCen : UCK.U3Center)
    (h76 : F07.R76Sig D) {L : Subgroup G} (hL : L ∈ calC D.M) (hX : IsSU3 (Bar2 L) 3)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = 7) (h7 : ¬ IsStronglyPEmbedded 7 D.M)
    {E : Subgroup G} (hEL : E ≤ L) (hEel : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) :
    rankThreeGamma 1 3 E ≤ D.M := by
  have hLM : L ≤ D.M := hL.1.le
  have hEM : E ≤ D.M := hEL.trans hLM
  by_cases h3 : IsStronglyPEmbedded 3 D.M
  · exact h3.rankThreeGamma_one_le_of_le Nat.prime_three hEel.isPGroup hEM
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hsp
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (hSg.three_le p hpσ)
  have h7r : CFSG.Open.pRank 7 D.M ≤ 3 := by
    by_contra h
    exact h7 (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem 7 (by norm_num) (by norm_num)
      (by omega)))
  have hZ7 : ¬ 7 ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen (Bar2 L) 3 hX))
    omega
  have hBN : B ≤ normalizer (L : Set G) := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    haveI : Fact p.Prime := ⟨hp⟩
    exact uc22ine229_normalizes_of_pRank_le_three hL (hBM hy) hp hp5
      (orderOf_eq_prime (hBel.2 y hy) hy1) (by norm_num) (by norm_num) hXL hXc hZ7 h7r
  have hpn : ¬ p ∣ 2 * 3 := fun h => by
    rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3')
  have hpq : ¬ p ∣ 2 ^ 3 + 1 := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h)))
  have h2 := uc22s219r_two_le_pRank_centralizer hLM hX hp hp2 hp3 hpn hpq hBM hBN hBel hBc
    Nat.prime_three (by norm_num) hEL hEel.isPGroup
  refine h76 p hpσ hp2 hsp 3 Nat.prime_three E hEM hEel hEc (by omega) fun Y hYE _ => ?_
  refine lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_))
  exact inf_le_inf_left _ ((Subgroup.centralizer_le hYE).trans
    (Subgroup.centralizer_le_normalizer _))

theorem uc22s219r_mem_uniqueSet_three (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hCen : UCK.U3Center) (hFF : UCK.U3FixField) (hI3 : UCK.U3Fix3Inner) (hCov : UCK.U3E9Cover)
    (hFix : UCK.U3E9Fix) (h76 : F07.R76Sig D) (h63 : UC6.R6_3 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hX : IsSU3 (Bar2 L) 3) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : Nat.card X = 7) (hXN : normalizer (X : Set G) ≤ D.M) : X ∈ uniqueSet D.M := by
  classical
  by_contra hXU
  have hr : Nat.Prime 7 := by norm_num
  obtain ⟨g, y, hC⟩ := UC6S898.exists_ctx898 D hSg hCen hL hX hr (by norm_num) hXL hXc hXN hXU
  have hαr := hC.rho_pow
  have hLM : L ≤ D.M := hL.1.le
  have hZ : ¬ 7 ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have h4 : 7 ∣ 3 := hdvd.trans (hCen (Bar2 L) 3 hX)
    omega
  have hΓ : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      rankThreeGamma 1 3 E ≤ D.M := fun E hEL hEel hEc =>
    uc22s219r_gamma_three D hSg hCen h76 hL hX hXL hXc hC.hnsp hEL hEel hEc
  have key : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      E ∈ uniqueSet D.M := by
    intro E hEL hEel hEc
    have hU := h63 3 Nat.prime_three (by norm_num) E (hEL.trans hLM) hEel hEc (hΓ E hEL hEel hEc)
    refine mem_uniqueSet_of_forall D.maxLocal (hEL.trans hLM) (fun H hH hEH => ?_)
    have : H ∈ calMOf E := ⟨hH, hEH⟩
    rw [hU] at this
    exact this
  let Y : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
  have hYpg : IsPGroup 7 ↥Y := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hC.hYc)
  have hYgen : ∀ b ∈ Y, ∃ k : ℕ, y ^ k = b := hC.hyall
  have hBN : Y ≤ normalizer (L : Set G) := hC.mem_normalizer
  have hα : UC6S846.rhoL L ⟨y, hC.hyN⟩ ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    by_contra hα
    obtain ⟨m, hnm, -⟩ := hFF (Bar2 L) 3 hX 3 ⟨1, by norm_num⟩ dvd_rfl 7 hr (by norm_num) _ hαr hα
    omega
  obtain ⟨z, hzo, hz⟩ := hI3 (Bar2 L) hX _ hαr hα
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hZ3 : IsPGroup 3 ↥(Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by simpa using hzcard)
  have hzfix : ∀ e ∈ Subgroup.zpowers z, UC6S846.rhoL L ⟨y, hC.hyN⟩ e = e := by
    intro e he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [map_zpow]
    exact congrArg (· ^ j) hz
  obtain ⟨A, hAL, hAc, hAπ, hAcard, hAel⟩ := UC6S898.exists_lift_fixed (B := Y) (ℓ := 7) (q := 3)
    hr (by norm_num) Nat.prime_three (by norm_num) hBN hYpg (Subgroup.zpowers z) hZ3
    (UC6S898.rho_fix_of_generator hC.hyN hBN hYgen hzfix)
  have hAel' : IsElemAbelian 3 A :=
    hAel (UC6S898.isElemAbelian_of_card_prime Nat.prime_three hzcard)
  have hAc3 : Nat.card A = 3 := hAcard.trans hzcard
  obtain ⟨Eb, hEbel, hEbc, hzEb⟩ := hCov (Bar2 L) hX z hzo
  have hAEb : (A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤ Eb :=
    hAπ.trans ((Subgroup.zpowers_le).2 hzEb)
  obtain ⟨S, hSL, hAS, hScard, hSel⟩ := UC6S898.exists_pgroup_containing (L := L)
    Nat.prime_three (by norm_num) Eb hEbel.isPGroup hAL hAel'.isPGroup hAEb
  have hNA : normalizer (A : Set G) ≤ D.M :=
    (UC6S898.normalizer_le_gamma hAS Nat.prime_three hAel' hAc3).trans
      (hΓ S hSL (hSel hEbel) (hScard.trans hEbc))
  let A₂ : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hA₂c : Nat.card A₂ = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAc3]
  have hA₂X : ∀ a ∈ A₂, ∀ x ∈ X, a * x * a⁻¹ = x := by
    intro a ha x hx
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have hy₀ : g⁻¹ * x * g ∈ Y := by
      refine (UC6S898.mem_map_conj_inv g _).2 ?_
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]
      exact hx
    have hcomm : (g⁻¹ * x * g) * a₀ = a₀ * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_iff.1 (hAc ha₀) _ hy₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a₀ * g⁻¹ * x * (g * a₀ * g⁻¹)⁻¹
        = g * (a₀ * (g⁻¹ * x * g) * a₀⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [← hcomm]; group
      _ = x := by group
  have hA₂cent : A₂ ≤ centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hA₂X a ha x hx
    calc x * a = (a * x * a⁻¹) * a := by rw [h1]
      _ = a * x := by group
  have hA₂M : A₂ ≤ D.M := fun a ha =>
    hXN (Subgroup.centralizer_le_normalizer _ (hA₂cent ha))
  have hA₂N : A₂ ≤ normalizer (L : Set G) := fun a ha =>
    UC6S898.mem_normalizer_of_centralizes hL (hA₂M ha) hr (by norm_num) hXL hXc hZ (hA₂X a ha)
  have hA₂pg : IsPGroup 3 ↥A₂ := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA₂c)
  obtain ⟨a₂, ha₂, ha₂o, ha₂gen⟩ := UC6S898.exists_generator Nat.prime_three hA₂c
  have hβ3 : (UC6S846.rhoL L ⟨a₂, hA₂N ha₂⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a₂, hA₂N ha₂⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using (ha₂o ▸ pow_orderOf_eq_one a₂))
    rw [this, map_one]
  obtain ⟨x, hxX, hxo, -⟩ := UC6S898.exists_generator hr hXc
  have hxL : x ∈ L := hXL hxX
  have hXpg : IsPGroup 7 ↥X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXc)
  have hxbo : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) = 7 := by
    have hdvd : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∣ 7 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ 7 = 1 :=
        Subtype.ext (by simpa using (hxo ▸ pow_orderOf_eq_one x))
      rw [this, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h7
    · exfalso
      have hxk : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
      have hxO : x ∈ pCoreOf 2 L := ⟨_, hxk, rfl⟩
      have hx1 : x = 1 := UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr
        (by norm_num : 7 ≠ 2) hXpg (UC6S846.isPGroup_pCoreOf L) hxX hxO
      rw [hx1, orderOf_one] at hxo
      omega
    · exact h7
  have hβx : UC6S846.rhoL L ⟨a₂, hA₂N ha₂⟩ (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) =
      QuotientGroup.mk (⟨x, hxL⟩ : ↥L) := by
    refine (UC6S846.rhoL_fix_iff L ⟨a₂, hA₂N ha₂⟩ ⟨x, hxL⟩).2 ?_
    show a₂ * x * a₂⁻¹ * x⁻¹ ∈ pCoreOf 2 L
    rw [hA₂X a₂ ha₂ x hxX, mul_inv_cancel]
    exact (pCoreOf 2 L).one_mem
  obtain ⟨Eb₂, hEb₂el, hEb₂c, hEb₂fix⟩ := hFix (Bar2 L) hX _ hxbo _ hβ3 hβx
  obtain ⟨E, hEL, hEcent, -, hEcard, hEel⟩ := UC6S898.exists_lift_fixed (B := A₂) (ℓ := 3)
    (q := 3) Nat.prime_three (by norm_num) Nat.prime_three (by norm_num) hA₂N hA₂pg Eb₂
    hEb₂el.isPGroup (UC6S898.rho_fix_of_generator (hA₂N ha₂) hA₂N ha₂gen hEb₂fix)
  have hEU := key E hEL (hEel hEb₂el) (hEcard.trans hEb₂c)
  have hEMg : E ≤ D.M.map (MulAut.conj g).toMonoidHom := fun e he =>
    UC6S898.normalizer_map_conj_le g hNA (Subgroup.centralizer_le_normalizer _ (hEcent he))
  exact hC.hMg (hEU.2 g hEMg)

theorem uc22s219r_mem_uniqueSet_of_ne (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h846 : F08.R846 D) (hCen : UCK.U3Center) (hRange : UCK.U3Range) (hFI : UCK.U3FixInner)
    (hFF : UCK.U3FixField) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsSU3 (Bar2 L) n)
    {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ} (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (hres : ¬ (n = 3 ∨ n = 3 * r)) {X : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = r)
    (hXN : normalizer (X : Set G) ≤ D.M) : X ∈ uniqueSet D.M := by
  classical
  by_contra hXU
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  obtain ⟨g, y, hC⟩ := UC6S898.exists_ctx898 D hSg hCen hL hX hr hr5 hXL hXc hXN hXU
  have hαr := hC.rho_pow
  obtain ⟨q, hq, hq3, hqn, z, hzo, hαz⟩ : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ 2 ^ n + 1 ∧
      ∃ z : Bar2 L, orderOf z = q ∧ UC6S846.rhoL L ⟨y, hC.hyN⟩ z = z := by
    have hn2 : 2 ≤ n := hRange (Bar2 L) n hX
    by_cases hα : UC6S846.rhoL L ⟨y, hC.hyN⟩ ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range
    · have hn3 : n ≠ 3 := fun h => hres (Or.inl h)
      obtain ⟨q, hq, hq3, hqn⟩ := UC6S898.exists_prime_gt_three_dvd hn2 hn3
      obtain ⟨z, hzo, hz⟩ := hFI (Bar2 L) n hX s hs hsn r hr hrs _ hαr hα q hq hq3 hqn
      exact ⟨q, hq, hq3, hqn, z, hzo, hz⟩
    · obtain ⟨m, hnm, hm⟩ := hFF (Bar2 L) n hX s hs hsn r hr hrs _ hαr hα
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hnm
        rw [hnm] at hsn
        rcases (Nat.dvd_prime hr).1 hsn with rfl | rfl
        · have : r ∣ 1 := by simpa using hrs
          exact hr.one_lt.ne' (Nat.dvd_one.1 this)
        · exact UC6S898.not_dvd_two_pow_sub_one_self hr hrs
      have hm3 : m ≠ 3 := fun h => hres (Or.inr (by rw [hnm, h, mul_comm]))
      obtain ⟨q, hq, hq3, hqm⟩ := UC6S898.exists_prime_gt_three_dvd (by omega) hm3
      have hqn : q ∣ 2 ^ n + 1 :=
        hqm.trans (by rw [hnm]; exact UC6S898.two_pow_add_one_dvd (hr.odd_of_ne_two hr2))
      obtain ⟨z, hzo, hz⟩ := hm q hq hq3 hqm
      exact ⟨q, hq, hq3, hqn, z, hzo, hz⟩
  exact UC6S898.false_of_fixed898 D h846 hL hX hr hr5 hC hq hq3 hqn hzo hαz

theorem uc22s219r_mem_uniqueSet (D : Data G) (hSg : UC6S846.SigmaStd D) (h846 : F08.R846 D)
    (hCen : UCK.U3Center) (hRange : UCK.U3Range) (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField)
    (hI3 : UCK.U3Fix3Inner) (hCov : UCK.U3E9Cover) (hFix : UCK.U3E9Fix) (h76 : F07.R76Sig D)
    (h63 : UC6.R6_3 D) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsSU3 (Bar2 L) n)
    {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ} (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (hres : n = 3 ∨ n ≠ 3 * r) {X : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = r)
    (hXN : normalizer (X : Set G) ≤ D.M) : X ∈ uniqueSet D.M := by
  rcases eq_or_ne n 3 with rfl | hn3
  · obtain rfl : r = 7 := UC6S898.eq_seven_of_residual hr hs hsn hrs (Or.inl rfl)
    exact uc22s219r_mem_uniqueSet_three D hSg hCen hFF hI3 hCov hFix h76 h63 hL hX hXL hXc hXN
  · exact uc22s219r_mem_uniqueSet_of_ne D hSg h846 hCen hRange hFI hFF hL hX hs hsn hr hrs
      (fun h => h.elim hn3 (hres.resolve_left hn3)) hXL hXc hXN

end CFSG.LocalAnalysis.UniquenessCase.UC22
