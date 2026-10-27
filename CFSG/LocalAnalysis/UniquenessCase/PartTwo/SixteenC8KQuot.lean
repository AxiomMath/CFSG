module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatDefs
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem c8k_pprime_quot (Γ : Type) [Group Γ] [Finite Γ] :
    (CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ)).comap (QuotientGroup.mk' (CFSG.pCore 2 Γ)) =
      CFSG.pPrimeCore 3 Γ := by
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 Γ)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Γ))
    rw [hn]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
  exact (CFSG.prime_complement_kernel_core_preimage (p := 3)
    (QuotientGroup.mk' (CFSG.pCore 2 Γ)) (QuotientGroup.mk'_surjective _) hker).1

theorem c8k_no2_quot (Γ : Type) [Group Γ] [Finite Γ] :
    CFSG.pCore 2 (Γ ⧸ CFSG.pCore 2 Γ) = ⊥ := by
  let Q := CFSG.pCore 2 Γ
  let K := (CFSG.pCore 2 (Γ ⧸ Q)).comap (QuotientGroup.mk' Q)
  have hKn : K.Normal := CFSG.pCore_normal.comap _
  have hKp : IsPGroup 2 K := IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup _
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hKQ : K ≤ Q := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff y).mpr (hKQ hx)

theorem c8k_dorder_quot {d : Γ} (hd : orderOf d = 3) :
    orderOf (d : Γ ⧸ CFSG.pCore 2 Γ) = 3 := by
  change orderOf (QuotientGroup.mk' (CFSG.pCore 2 Γ) d) = 3
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Γ) d) ∣ 3 := by
    rw [← hd]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 Γ)) d
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exfalso
    have hdQ : d ∈ CFSG.pCore 2 Γ :=
      (QuotientGroup.eq_one_iff d).1 ((orderOf_eq_one_iff).1 h)
    have h3dvd : 3 ∣ Nat.card ↥(CFSG.pCore 2 Γ) := by
      rw [← hd, ← Subgroup.orderOf_mk d hdQ]
      exact orderOf_dvd_natCard (⟨d, hdQ⟩ : CFSG.pCore 2 Γ)
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Γ))
    have hnot : ¬ 3 ∣ 2 ^ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
    exact hnot (hn ▸ h3dvd)
  · exact h

theorem c8k_ne_top_quot {B : Subgroup Γ} (hq : CFSG.pCore 2 Γ ≤ B) (hB : B ≠ ⊤) :
    B.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) ≠ ⊤ := by
  intro h
  refine hB ?_
  have hc := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (CFSG.pCore 2 Γ))
    (H := B) (by rwa [QuotientGroup.ker_mk'])
  rw [h, Subgroup.comap_top] at hc
  exact hc.symm

theorem c8k_prod_quot {B : Subgroup Γ} (h : B ⊔ CFSG.pPrimeCore 3 Γ = ⊤) :
    B.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) ⊔ CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ) = ⊤ := by
  have hmap : (CFSG.pPrimeCore 3 Γ).map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) =
      CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ) := by
    rw [← c8k_pprime_quot Γ]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have htop : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) (⊤ : Subgroup Γ) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))) h
  rw [Subgroup.map_sup, htop, hmap] at this
  exact this

theorem c8k_cent_quot {B : Subgroup Γ} {d : Γ} (hd : orderOf d = 3) (hq : CFSG.pCore 2 Γ ≤ B)
    (hc : centralizer ({d} : Set Γ) ≤ B) :
    centralizer ({(d : Γ ⧸ CFSG.pCore 2 Γ)} : Set (Γ ⧸ CFSG.pCore 2 Γ)) ≤
      B.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) := by
  haveI : Fact (IsPGroup 3 ↥(Subgroup.zpowers d)) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd, pow_one])⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pCore 2 Γ)) := by
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Γ))
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer (p := 3)
    (T := Subgroup.zpowers d) (M := CFSG.pCore 2 Γ) CFSG.pCore_normal hcop
  simp only at h
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    centralizer_closure, centralizer_closure] at h
  rw [show centralizer ({(d : Γ ⧸ CFSG.pCore 2 Γ)} : Set (Γ ⧸ CFSG.pCore 2 Γ)) =
      (centralizer ({d} : Set Γ)).map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) from h]
  exact Subgroup.map_mono hc

theorem c8k_rank_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    pRank p (⊤ : Subgroup (Γ ⧸ CFSG.pCore 2 Γ)) ≤ pRank p (⊤ : Subgroup Γ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 Γ) := by
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Γ))
    rw [hn]
    intro hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdiv))
  have h := CFSG.SectionRank.pRank_quotient_eq (p := p) (G := Γ) (CFSG.pCore 2 Γ) hN
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact h.le

theorem c8k_l3_quot (h : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1) :
    IsL3 ((Γ ⧸ CFSG.pCore 2 Γ) ⧸ CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ)) 1 := by
  have hle : CFSG.pCore 2 Γ ≤ CFSG.pPrimeCore 3 Γ :=
    (QuotientGroup.le_comap_mk' (CFSG.pCore 2 Γ)
      (CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ))).trans (c8k_pprime_quot Γ).le
  have hmap : (CFSG.pPrimeCore 3 Γ).map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) =
      CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ) := by
    rw [← c8k_pprime_quot Γ]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  refine CFSG.Blueprint.LieModel.of_mulEquiv ?_ h
  exact (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 Γ) (CFSG.pPrimeCore 3 Γ)
    hle).symm.trans (QuotientGroup.quotientMulEquivOfEq hmap)

theorem c8h_setup_of_kctx {B : Subgroup Γ} {d : Γ} (h : C8KCtx Γ B d) :
    C8HatSetup (Γ ⧸ CFSG.pCore 2 Γ) (B.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)))
      (d : Γ ⧸ CFSG.pCore 2 Γ) :=
  { kgroup := h.kgroup.quotient _
    l3 := c8k_l3_quot h.l3
    ne_top := c8k_ne_top_quot h.q_le h.ne_top
    prod := c8k_prod_quot h.prod
    q_le := by rw [c8k_no2_quot]; exact bot_le
    d_order := c8k_dorder_quot h.d_order
    d_cent := c8k_cent_quot h.d_order h.q_le h.d_cent
    rank := fun p hp hp3 =>
      (c8k_rank_quot hp (by omega)).trans (h.rank p hp hp3)
    no2 := c8k_no2_quot Γ }

theorem c8k_invol_transfer
    (h : ∀ t : Γ ⧸ CFSG.pCore 2 Γ, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ)) :
    ∀ t : Γ, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 Γ := by
  intro t ht
  rw [← c8k_pprime_quot Γ]
  exact h _ (by rw [← map_pow, ht, map_one])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
