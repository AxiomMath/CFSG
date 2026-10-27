module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPMember
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34OuterInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846Ker
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineLift
public import CFSG.Quasithin.Background.RonanD33

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_inf_pCoreOf_of_rhoL_mem_range {D : Data G} {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) (hZ : Subgroup.center (Bar2 L) = ⊥) {a : G}
    (haT : a ∈ D.T) (haN : a ∈ normalizer (L : Set G))
    (hinn : UC6S846.rhoL L ⟨a, haN⟩ ∈
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range) :
    a ∈ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T) := by
  classical
  have hTH : D.T ≤ L ⊔ D.T := le_sup_right
  have hTsyl : IsSylowIn 2 D.T (L ⊔ D.T) := TwelveShort.isSylowIn_of_le D hTH
  have hQT : pCoreOf 2 (L ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hTH D.sylowM.isPGroup hTsyl.2.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hinn
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
  have hlL : (l : G) ∈ L := l.2
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hρl : UC6S846.rhoL L ⟨(l : G), hlN⟩ = MulAut.conj y := by
    rw [UC6S846.rhoL_inner L (l : G) hlL, ← hl, QuotientGroup.coe_mk']
  have hinner : UC6S846.rhoL L ⟨a * (l : G)⁻¹,
      (normalizer (L : Set G)).mul_mem haN (Subgroup.inv_mem _ hlN)⟩ = 1 := by
    have heq : UC6S846.rhoL L ⟨a, haN⟩ = UC6S846.rhoL L ⟨(l : G), hlN⟩ := by
      rw [hρl, hy]
    have hmul : (⟨a, haN⟩ * ⟨(l : G), hlN⟩⁻¹ : ↥(normalizer (L : Set G))) =
        ⟨a * (l : G)⁻¹, (normalizer (L : Set G)).mul_mem haN
          (Subgroup.inv_mem _ hlN)⟩ := Subtype.ext rfl
    rw [← hmul, map_mul, map_inv, heq, mul_inv_cancel]
  have hmemH : a * (l : G)⁻¹ ∈ L ⊔ D.T :=
    (L ⊔ D.T).mul_mem (hTH haT)
      ((L ⊔ D.T).inv_mem ((le_sup_left : L ≤ L ⊔ D.T) hlL))
  have hkerL : ∀ w ∈ L, ∀ hw : w ∈ normalizer (L : Set G), UC6S846.rhoL L ⟨w, hw⟩ = 1 →
      w ∈ pCoreOf 2 L := fun w hwL hw hρ =>
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.inf_centralizerBar_le_pCore_of_center_bar2
      (P := L) hZ ⟨CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.mem_centralizerBar_iff.mpr
        ⟨hwL, fun z hz => (UC6S846.rhoL_fix_iff L ⟨w, hw⟩ ⟨z, hz⟩).1 (by rw [hρ]; rfl)⟩, hwL⟩
  have hker : a * (l : G)⁻¹ ∈ pCoreOf 2 (L ⊔ D.T) :=
    UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one D.sylowM.isPGroup hTL hkerL hmemH
      ((normalizer (L : Set G)).mul_mem haN (Subgroup.inv_mem _ hlN)) hinner
  have hlT : (l : G) ∈ D.T := by
    have h1 : (a * (l : G)⁻¹)⁻¹ * a = (l : G) := by group
    rw [← h1]
    exact D.T.mul_mem (D.T.inv_mem (hQT hker)) haT
  have haeq : a = (a * (l : G)⁻¹) * (l : G) := by group
  rw [haeq]
  exact ((D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T)).mul_mem
    ((le_sup_right : pCoreOf 2 (L ⊔ D.T) ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T)) hker)
    ((le_sup_left : D.T ⊓ L ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T))
      (Subgroup.mem_inf.mpr ⟨hlT, hlL⟩))

theorem mem_normalizer_zpowers_sup_pCoreOf_of_rhoL_mem_zpowers {D : Data G}
    {L : Subgroup G} (hTL : D.T ≤ normalizer (L : Set G)) {x t : G} (hxL : x ∈ L)
    (htH : t ∈ L ⊔ D.T) (htN : t ∈ normalizer (L : Set G))
    (h : UC6S846.rhoL L ⟨t, htN⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩) ∈
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩)) :
    t ∈ normalizer ((Subgroup.zpowers x ⊔ pCoreOf 2 (L ⊔ D.T) : Subgroup G) : Set G) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  have hHnorm : H ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hTL
  have hQnorm : H ≤ normalizer (Q : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hpQ : pCoreOf 2 L = L ⊓ Q :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal le_sup_left hHnorm
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hconj : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN x).mp hxL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hρx : UC6S846.rhoL L ⟨t, htN⟩ (π ⟨x, hxL⟩) = π ⟨t * x * t⁻¹, hconj⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.rhoL_apply_mk htN ⟨x, hxL⟩
  have hdiv : ((⟨t * x * t⁻¹, hconj⟩ : ↥L) / (⟨x, hxL⟩ ^ k)) ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_iff_div_mem (N := CFSG.pCore 2 ↥L)).mp ?_
    change π ⟨t * x * t⁻¹, hconj⟩ = π (⟨x, hxL⟩ ^ k)
    rw [← hρx, ← hk, map_zpow]
  have hmemL : (t * x * t⁻¹) * (x ^ k)⁻¹ ∈ L :=
    L.mul_mem hconj (L.inv_mem (L.zpow_mem hxL k))
  have hdivG : (t * x * t⁻¹) * (x ^ k)⁻¹ ∈ pCoreOf 2 L := by
    have hcoe : ((⟨t * x * t⁻¹, hconj⟩ : ↥L) / (⟨x, hxL⟩ ^ k) : ↥L) =
        ⟨(t * x * t⁻¹) * (x ^ k)⁻¹, hmemL⟩ := by
      ext
      simp [div_eq_mul_inv]
    rw [hcoe] at hdiv
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L)
      (⟨(t * x * t⁻¹) * (x ^ k)⁻¹, hmemL⟩ : ↥L)).mpr hdiv
  have hmem : t * x * t⁻¹ ∈ Subgroup.zpowers x ⊔ Q := by
    have heq : t * x * t⁻¹ = ((t * x * t⁻¹) * (x ^ k)⁻¹) * (x ^ k) := by group
    rw [heq]
    refine (Subgroup.zpowers x ⊔ Q).mul_mem ?_ ?_
    · exact (le_sup_right : Q ≤ Subgroup.zpowers x ⊔ Q) ((hpQ ▸ hdivG).2)
    · exact (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Q)
        (Subgroup.zpow_mem_zpowers x k)
  have hmap_le : (Subgroup.zpowers x ⊔ Q).map (MulAut.conj t).toMonoidHom ≤
      Subgroup.zpowers x ⊔ Q := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      simpa [MulAut.conj_apply] using hmem
    · have hQmap : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) Q = Q := by
        simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm htH)
      rw [hQmap]
      exact le_sup_right
  have hcard : Nat.card ↥((Subgroup.zpowers x ⊔ Q).map (MulAut.conj t).toMonoidHom) =
      Nat.card ↥(Subgroup.zpowers x ⊔ Q) :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm))

theorem calP19_4_nonempty_of_outer_U34 (hU : Inputs1719.K_U34OuterInv) (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A J : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJU : J = L ∧ IsU3 (Bar2 L) 2)
    (hout : ¬ A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T)) :
    (calP19_4 D L K J A).Nonempty := by
  classical
  obtain ⟨hJL, hU3⟩ := hJU
  rw [hJL] at hJ hout ⊢
  have hA0 : A ∈ E3.gammaSet V₀ 0 D.T := hA
  have hJ0 : JChoice19 D L K L := hJ
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hLN : (L.subgroupOf D.M).Normal := by
    rcases hJ with ⟨-, hN⟩ | ⟨hJsup, hnotN⟩
    · exact hN
    · exfalso
      have hKleL : K ≤ L := hJsup.symm ▸ le_sup_right
      rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, hLn, -⟩
      · have hcard : Nat.card K = Nat.card L := by
          rw [hKx, E3.card_conjSubgroup]
        exact h.hne (Subgroup.eq_of_le_of_card_ge hKleL (le_of_eq hcard.symm))
      · exact hnotN hLn
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hMN
  have hTH : D.T ≤ L ⊔ D.T := le_sup_right
  have hTsyl : IsSylowIn 2 D.T (L ⊔ D.T) := TwelveShort.isSylowIn_of_le D hTH
  have hQT : pCoreOf 2 (L ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hTH D.sylowM.isPGroup hTsyl.2.2
  have hHnorm : L ⊔ D.T ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hTL
  have hpLQ : pCoreOf 2 L = L ⊓ pCoreOf 2 (L ⊔ D.T) :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal le_sup_left hHnorm
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hV0 : InCalV D.M V₀ := by
    rcases h.hyp.hyp125.1 with ⟨-, hbot⟩ | ⟨hV0, -⟩
    · exact absurd hbot (ne_bot_of_one_lt_mSub h.hyp.big)
    · exact hV0.1
  have hAeq : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0.2.2.2.isPGroup g) hAg).1 hmq
  have hAel : IsElemAbelian 2 A := hAeq ▸ E3.isElemAbelian_conjSubgroup hV0.2.2.2 g
  obtain ⟨a, haA, haout⟩ := SetLike.not_le_iff_exists.mp hout
  have haT : a ∈ D.T := hAT haA
  have haN : a ∈ normalizer (L : Set G) := hTL haT
  have hσout : UC6S846.rhoL L ⟨a, haN⟩ ∉
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    intro hinn
    exact haout (mem_sup_inf_pCoreOf_of_rhoL_mem_range hTL (center_bar2_of_isU3_two hU3) haT haN
      hinn)
  have ha2 : a * a = 1 := by
    have h := hAel.2 a haA
    rwa [pow_two] at h
  have hσ2 : UC6S846.rhoL L ⟨a, haN⟩ * UC6S846.rhoL L ⟨a, haN⟩ = 1 := by
    have h1 : (⟨a, haN⟩ : ↥(normalizer (L : Set G))) * ⟨a, haN⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using ha2)
    calc UC6S846.rhoL L ⟨a, haN⟩ * UC6S846.rhoL L ⟨a, haN⟩
        = UC6S846.rhoL L (⟨a, haN⟩ * ⟨a, haN⟩) := (map_mul _ _ _).symm
      _ = 1 := by rw [h1, map_one]
  obtain ⟨xbar, hxord, hxinv, hxfix⟩ :=
    hU (Bar2 L) hU3 (UC6S846.rhoL L ⟨a, haN⟩) hσ2 hσout
  have hxbar5 : xbar ^ 5 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one xbar
  have hxbar_ne : xbar ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) xbar
  set d : ℕ := Nat.card (CFSG.pCore 2 ↥L) with hddef
  have hd2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (G := ↥(CFSG.pCore 2 ↥L)) hd2
  have hdk : d = 2 ^ k := hddef.trans hk
  have hdcop : Nat.Coprime d 5 := hdk ▸ Nat.Coprime.pow_left k (by norm_num)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hdcop (by norm_num : 1 < 5)
  have hx05 : x₀ ^ 5 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥L) (x₀ ^ 5) = 1
    rw [map_pow, hx₀, hxbar5]
  have hx05pow : (x₀ ^ 5) ^ d = 1 := by
    rw [hddef]
    exact (orderOf_dvd_iff_pow_eq_one).mp
      (Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 ↥L) hx05)
  set e : ℕ := d * s with hedef
  set xL : ↥L := x₀ ^ e with hxLdef
  have hx5 : xL ^ 5 = 1 := by
    rw [hxLdef, hedef, ← pow_mul,
      show d * s * 5 = 5 * (d * s) from by ring, pow_mul, pow_mul, hx05pow, one_pow]
  have hmkx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL = xbar := by
    rw [hxLdef, hedef, map_pow, hx₀,
      pow_eq_pow_mod (a := xbar) (n := 5) (d * s) hxbar5, hs, pow_one]
  have hxLne : xL ≠ 1 := by
    intro h1
    rw [h1, map_one] at hmkx
    exact hxbar_ne hmkx.symm
  have hxLord : orderOf xL = 5 := by
    have hdvd : orderOf xL ∣ 5 := (orderOf_dvd_iff_pow_eq_one).mpr hx5
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hxLne
    · exact h5
  have hσx : UC6S846.rhoL L ⟨a, haN⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)⁻¹ := by
    rw [hmkx, hxinv]
  have hconjL : a * (xL : G) * a⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp haN (xL : G)).mp xL.2
  have hcommL : a * (xL : G) * a⁻¹ * (xL : G)⁻¹ ∈ L :=
    L.mul_mem hconjL (L.inv_mem xL.2)
  have hmkx_ord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) = 5 := by
    rw [hmkx]
    exact hxord
  have hmkx_sq_ne : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) ≠ 1 := by
    intro h2
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) ^ 2 = 1 := by
      rw [pow_two]
      exact h2
    have hdvd := (orderOf_dvd_iff_pow_eq_one).mpr h3
    rw [hmkx_ord] at hdvd
    norm_num at hdvd
  have hcomm_not : ⁅a, (xL : G)⁆ ∉ pCoreOf 2 (L ⊔ D.T) := by
    rw [commutatorElement_def]
    intro hmemQ
    have hmemO2 : a * (xL : G) * a⁻¹ * (xL : G)⁻¹ ∈ pCoreOf 2 L := by
      rw [hpLQ]
      exact ⟨hcommL, hmemQ⟩
    have hone : QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨a * (xL : G) * a⁻¹ * (xL : G)⁻¹, hcommL⟩ = 1 := by
      change (QuotientGroup.mk (⟨a * (xL : G) * a⁻¹ * (xL : G)⁻¹, hcommL⟩ :
        ↥L) : Bar2 L) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L)
        (⟨a * (xL : G) * a⁻¹ * (xL : G)⁻¹, hcommL⟩ : ↥L)).mp hmemO2
    have himg : QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨a * (xL : G) * a⁻¹ * (xL : G)⁻¹, hcommL⟩ =
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL))⁻¹ := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a * (xL : G) * a⁻¹, hconjL⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)⁻¹ := by
        rw [← hσx]
        exact (CFSG.LocalAnalysis.UniquenessCase.UC22.rhoL_apply_mk (K := L) (r := a)
          haN xL).symm
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨(xL : G)⁻¹, L.inv_mem xL.2⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)⁻¹ := by
        rw [← map_inv]
        rfl
      calc QuotientGroup.mk' (CFSG.pCore 2 ↥L)
            ⟨a * (xL : G) * a⁻¹ * (xL : G)⁻¹, hcommL⟩
          = QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a * (xL : G) * a⁻¹, hconjL⟩ *
              QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨(xL : G)⁻¹, L.inv_mem xL.2⟩ := by
              rw [← map_mul]
              exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Subtype.ext rfl)
        _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)⁻¹ *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)⁻¹ := by rw [h1, h2]
        _ = ((QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL))⁻¹ := by rw [mul_inv_rev]
    rw [himg] at hone
    exact hmkx_sq_ne (inv_eq_one.mp hone)
  refine ⟨Subgroup.zpowers (xL : G) ⊔ E1.tauOf (L ⊔ D.T) D.T A, ?_⟩
  refine sup_tauOf_mem_calP19_4 (D := D) (L := L) (K := K) (J := L)
    (X := Subgroup.zpowers (xL : G)) (q := 5) h hA0 hJ0 Nat.prime_five (by norm_num) ?_ ?_ ?_
    ?_ (Or.inl rfl)
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxLord]
  · exact Subgroup.zpowers_le.mpr xL.2
  · intro t ht
    have htT : t ∈ D.T := (E1.mem_tauOf.mp ht).1
    have htN : t ∈ normalizer (L : Set G) := hTL htT
    have htacQ : t * a * t⁻¹ * a⁻¹ ∈ pCoreOf 2 (L ⊔ D.T) := by
      have h := (E1.mem_tauOf.mp ht).2.2 a haA
      rwa [commutatorElement_def] at h
    have htacN : t * a * t⁻¹ * a⁻¹ ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).mul_mem
          ((normalizer (L : Set G)).mul_mem (hTL htT) (hTL haT))
          ((normalizer (L : Set G)).inv_mem (hTL htT)))
        ((normalizer (L : Set G)).inv_mem (hTL haT))
    have hρq : UC6S846.rhoL L ⟨t * a * t⁻¹ * a⁻¹, htacN⟩ = 1 :=
      UC6S846.rhoL_eq_one_of_mem_pCoreOf (le_sup_left : L ≤ L ⊔ D.T) htacN htacQ
    have hcommAut : UC6S846.rhoL L ⟨t, htN⟩ * UC6S846.rhoL L ⟨a, haN⟩ =
        UC6S846.rhoL L ⟨a, haN⟩ * UC6S846.rhoL L ⟨t, htN⟩ := by
      have h1 : UC6S846.rhoL L ⟨t, htN⟩ * UC6S846.rhoL L ⟨a, haN⟩ *
          (UC6S846.rhoL L ⟨t, htN⟩)⁻¹ * (UC6S846.rhoL L ⟨a, haN⟩)⁻¹ = 1 := by
        have hsub : (⟨t, htN⟩ * ⟨a, haN⟩ * ⟨t, htN⟩⁻¹ * ⟨a, haN⟩⁻¹ :
            ↥(normalizer (L : Set G))) = ⟨t * a * t⁻¹ * a⁻¹, htacN⟩ := Subtype.ext rfl
        calc UC6S846.rhoL L ⟨t, htN⟩ * UC6S846.rhoL L ⟨a, haN⟩ *
              (UC6S846.rhoL L ⟨t, htN⟩)⁻¹ * (UC6S846.rhoL L ⟨a, haN⟩)⁻¹
            = UC6S846.rhoL L (⟨t, htN⟩ * ⟨a, haN⟩ * ⟨t, htN⟩⁻¹ * ⟨a, haN⟩⁻¹) := by
                simp only [map_mul, map_inv]
          _ = UC6S846.rhoL L ⟨t * a * t⁻¹ * a⁻¹, htacN⟩ := by rw [hsub]
          _ = 1 := hρq
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hfix : UC6S846.rhoL L ⟨t, htN⟩ xbar ∈ Subgroup.zpowers xbar :=
      hxfix _ hcommAut
    exact mem_normalizer_zpowers_sup_pCoreOf_of_rhoL_mem_zpowers hTL xL.2
      (hTH htT) htN
      (by
        show UC6S846.rhoL L ⟨t, htN⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL) ∈
          Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥L) xL)
        rw [hmkx]
        exact hfix)
  · exact ⟨a, haA, (xL : G), Subgroup.mem_zpowers _, hcomm_not⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
