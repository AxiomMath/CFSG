module
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.GrunCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_2.Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_a

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.5.4(a)

The normal-Sylow branch in the minimal non-`q`-nilpotent argument.  This file
contains both source branches used in the proof: the non-`q`-normal branch via
IV.5.3 and the `q`-normal branch via Grun's second theorem.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

/-- Unpack the empty bad-subgroup hypothesis for a single nontrivial `p`-subgroup.
This is local to the IV.5.4(a) Frobenius branch, so the file does not depend
back on IV.6.2. -/
private theorem hkt_iv54_normalizer_hasNormalPComplement_of_no_noncomplement_pSubgroups
    {Q : Type u} [Group Q] {p : ℕ}
    (hbad_empty : ¬ ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup p U ∧ ¬ HasNormalPComplement p (↥(Subgroup.normalizer (U : Set Q))))
    {U : Subgroup Q} (hU_ne_bot : U ≠ ⊥) (hUp : IsPGroup p U) :
    HasNormalPComplement p (↥(Subgroup.normalizer (U : Set Q))) := by
  by_contra hcomp
  exact hbad_empty ⟨U, hU_ne_bot, hUp, hcomp⟩

/-- The empty bad-subgroup condition passes to a subgroup normalizer in the
minimal-counterexample step of IV.5.4(a). -/
private theorem hkt_iv54_intrinsic_normalizer_hasNormalPComplement_of_no_noncomplement_pSubgroups
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hbad_empty : ¬ ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup q U ∧ ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (H : Subgroup Q) {U : Subgroup H}
    (hU_ne_bot : U ≠ ⊥) (hUp : IsPGroup q U) :
    HasNormalPComplement q (Subgroup.normalizer (U : Set H)) := by
  classical
  let UQ : Subgroup Q := U.map H.subtype
  have hUQ_ne_bot : UQ ≠ ⊥ := by
    intro hbot
    exact hU_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (H := U) (f := H.subtype)
        H.subtype_injective).1 (by simpa [UQ] using hbot))
  have hUQp : IsPGroup q UQ := by
    simpa [UQ] using hUp.map H.subtype
  have hcomp_ambient :
      HasNormalPComplement q (Subgroup.normalizer (UQ : Set Q)) :=
    hkt_iv54_normalizer_hasNormalPComplement_of_no_noncomplement_pSubgroups
      (Q := Q) (p := q) hbad_empty hUQ_ne_bot hUQp
  simpa [UQ] using
    hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
      (G := Q) (p := q) (N := H) (K := U) hcomp_ambient

/-- Normal-Sylow endpoint for the empty bad-subgroup branch in IV.5.4(a). -/
private theorem hkt_iv54_hasNormalPComplement_of_no_noncomplement_pSubgroups_of_normal_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hbad_empty : ¬ ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup q U ∧ ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q))))
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hSnormal : (S : Subgroup Q).Normal) :
    HasNormalPComplement q Q := by
  classical
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hcomp_norm :
      HasNormalPComplement q (Subgroup.normalizer ((S : Subgroup Q) : Set Q)) :=
    hkt_iv54_normalizer_hasNormalPComplement_of_no_noncomplement_pSubgroups
      (Q := Q) (p := q) hbad_empty hS_ne_bot (by simpa using S.isPGroup')
  have hNtop : Subgroup.normalizer ((S : Subgroup Q) : Set Q) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hSnormal
  exact hkt_hasNormalPComplement_of_subgroup_eq_top
    (Subgroup.normalizer ((S : Subgroup Q) : Set Q)) hNtop hcomp_norm
private theorem hkt_iv54_generated_coprime_action_trivial_from_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (_x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hcompH : HasNormalPComplement q (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q))))) :
    ∀ a : Q, a ∈ A → a * x = x * a := by
  classical
  let H : Subgroup Q := (A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)
  have hA_le_generated : A ≤ H := by
    exact le_sup_left
  have hx_mem_generated : x ∈ H := by
    exact (le_sup_right :
      (Subgroup.zpowers x : Subgroup Q) ≤ H)
      (Subgroup.mem_zpowers x)
  have hx_qprime_element : IsPElement (p := r) x :=
    x_p
  rcases hcompH with ⟨K, hKnormal, hKcop, hquotp⟩
  letI : K.Normal := hKnormal
  let AH : Subgroup H := A.subgroupOf H
  have hH_le_normalizer : H ≤ Subgroup.normalizer (A : Set Q) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact Subgroup.zpowers_le.2 x_norm
  have hAHnormal : AH.Normal := by
    simpa [AH, H] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := A) (K := H) hA_le_generated).2 hH_le_normalizer
  have hAHp : IsPGroup q AH := by
    simpa [AH, H] using
      A_p.of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := A) (K := H) hA_le_generated).symm)
  let xH : H := ⟨x, hx_mem_generated⟩
  have hxH_r : IsPElement (p := r) xH := by
    rcases hx_qprime_element with ⟨n, hn⟩
    exact ⟨n, by simpa [xH, Subgroup.orderOf_coe] using hn⟩
  have hxH_mem_K : xH ∈ K := by
    rcases hxH_r with ⟨n, hn⟩
    rcases (IsPGroup.iff_orderOf (p := q) (G := H ⧸ K)).1 hquotp
        (QuotientGroup.mk' K xH) with ⟨m, hm⟩
    have hbar_dvd_x : orderOf (QuotientGroup.mk' K xH) ∣ orderOf xH :=
      orderOf_map_dvd (QuotientGroup.mk' K) xH
    have hbar_dvd_r : orderOf (QuotientGroup.mk' K xH) ∣ r ^ n := by
      simpa [hn] using hbar_dvd_x
    have hbar_dvd_q : orderOf (QuotientGroup.mk' K xH) ∣ q ^ m := by
      rw [hm]
    have hcop_qr : Nat.Coprime (q ^ m) (r ^ n) := by
      exact (((Nat.coprime_primes (Fact.out : q.Prime) hr).2
        (fun hqr => hr_ne_q hqr.symm)).pow_right n).pow_left m
    have hbar_order_one : orderOf (QuotientGroup.mk' K xH) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_qr hbar_dvd_q hbar_dvd_r
    exact (QuotientGroup.eq_one_iff (N := K) (x := xH)).1
      (orderOf_eq_one_iff.mp hbar_order_one)
  have hinf_bot : AH ⊓ K = ⊥ := by
    rcases hAHp.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card AH) (Nat.card K) := by
      rw [hn]
      exact hKcop.pow_left n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcomm_bot : ⁅AH, K⁆ = ⊥ := by
    have hleft : ⁅AH, K⁆ ≤ AH := by
      letI : AH.Normal := hAHnormal
      exact Subgroup.commutator_le_left (H₁ := AH) (H₂ := K)
    have hright : ⁅AH, K⁆ ≤ K := by
      exact Subgroup.commutator_le_right (H₁ := AH) (H₂ := K)
    apply eq_bot_iff.mpr
    intro y hy
    have hyinf : y ∈ AH ⊓ K := ⟨hleft hy, hright hy⟩
    simpa [hinf_bot] using hyinf
  have hK_le_centAH : K ≤ Subgroup.centralizer (AH : Set H) := by
    have hcomm_K_AH : ⁅K, AH⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hcomm_bot
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := AH)).1
      hcomm_K_AH
  intro a ha
  let aH : H := ⟨a, hA_le_generated ha⟩
  have haH : aH ∈ AH :=
    (Subgroup.mem_subgroupOf (h := aH) (H := A) (K := H)).mpr ha
  have hcommH : aH * xH = xH * aH :=
    (Subgroup.mem_centralizer_iff.mp (hK_le_centAH hxH_mem_K)) aH haH
  exact congrArg Subtype.val hcommH

/-- IV.5.4(a), top generated-subgroup branch: the case
`A ⊔ ⟨x⟩ = Q` turns the IV.5.3 witness into the local quotient-control setup
from which the selected Sylow subgroup must be normal. -/
private theorem hkt_iv54_generated_top_burnside_or_normal_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (_hq_dvd : q ∣ Nat.card Q)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (_x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤)
    (_hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hcomp_N : HasNormalPComplement q (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (_hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    (S : Subgroup Q).Normal ∨
      (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
  classical
  by_cases hSnormal : (S : Subgroup Q).Normal
  · exact Or.inl hSnormal
  by_cases hburnside :
      (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))
  · exact Or.inr hburnside
  by_cases hQp : IsPGroup q Q
  · have htop_q : IsPGroup q (⊤ : Subgroup Q) := by
      exact hQp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).symm
    have hS_top : (S : Subgroup Q) = ⊤ :=
      (S.is_maximal' htop_q le_top).symm
    have hS_normal : (S : Subgroup Q).Normal := by
      rw [hS_top]
      infer_instance
    exact False.elim (hSnormal hS_normal)
  · have hH_le_normalizer :
        ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) ≤
          Subgroup.normalizer (A : Set Q) := by
      exact sup_le Subgroup.le_normalizer
        (Subgroup.zpowers_le.mpr x_norm)
    have hnormalizer_top : Subgroup.normalizer (A : Set Q) = ⊤ := by
      exact top_unique (by simpa [hHtop] using hH_le_normalizer)
    have hAnormal : A.Normal :=
      Subgroup.normalizer_eq_top_iff.mp hnormalizer_top
    letI : A.Normal := hAnormal
    let π : Q →* Q ⧸ A := QuotientGroup.mk' A
    have hmap_top : (Subgroup.zpowers x : Subgroup Q).map π = ⊤ := by
      have hmap_sup :
          (((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)).map π) = ⊤ := by
        rw [hHtop]
        exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective A)
      have hAmap_bot : (A.map π) = ⊥ := by
        ext y
        constructor
        · intro hy
          rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
          simp [π, QuotientGroup.eq_one_iff]
          exact ha
        · intro hy
          simp at hy
          subst y
          exact ⟨1, A.one_mem, by simp [π]⟩
      rw [Subgroup.map_sup, hAmap_bot] at hmap_sup
      simpa using hmap_sup
    have hzpowers_quot_top : Subgroup.zpowers (π x) = ⊤ := by
      simpa [π, MonoidHom.map_zpowers] using hmap_top
    have horder : orderOf (π x) = Nat.card (Q ⧸ A) := by
      exact orderOf_eq_card_of_zpowers_eq_top hzpowers_quot_top
    have hcard_quot_dvd_orderx : Nat.card (Q ⧸ A) ∣ orderOf x := by
      rw [← horder]
      exact orderOf_map_dvd π x
    have hq_not_dvd_quot : ¬ q ∣ Nat.card (Q ⧸ A) := by
      rcases x_p with ⟨n, hn⟩
      intro hq_dvd_quot
      have hq_dvd_rpow : q ∣ r ^ n :=
        hq_dvd_quot.trans (by simpa [hn] using hcard_quot_dvd_orderx)
      have hcop_qr : Nat.Coprime q r := by
        exact (Nat.coprime_primes (Fact.out : q.Prime) hr).2
          (fun hqr => hr_ne_q hqr.symm)
      have hcop_q_rpow : Nat.Coprime q (r ^ n) := hcop_qr.pow_right n
      have hq_eq_one : q = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop_q_rpow (dvd_refl q) hq_dvd_rpow
      exact (Fact.out : q.Prime).ne_one hq_eq_one
    have hSylow_le_A (T : Sylow q Q) : (T : Subgroup Q) ≤ A := by
      intro t ht
      let Tmap : Subgroup (Q ⧸ A) := (T : Subgroup Q).map π
      have htmap : π t ∈ Tmap := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have hTmap_p : IsPGroup q Tmap := T.isPGroup'.map π
      have hTmap_card_one : Nat.card Tmap = 1 := by
        rcases hTmap_p.card_eq_or_dvd with hcard | hdiv
        · exact hcard
        · exact False.elim
            (hq_not_dvd_quot (hdiv.trans (Subgroup.card_subgroup_dvd_card Tmap)))
      have hTmap_bot : Tmap = ⊥ :=
        (Subgroup.card_eq_one (H := Tmap)).1 hTmap_card_one
      have hpi_one : π t = 1 := by
        simpa [Tmap, hTmap_bot] using htmap
      simpa [π, QuotientGroup.eq_one_iff] using hpi_one
    obtain ⟨T, hA_le_T⟩ := A_p.exists_le_sylow
    have hT_eq_A : (T : Subgroup Q) = A :=
      le_antisymm (hSylow_le_A T) hA_le_T
    have hTnormal : (T : Subgroup Q).Normal := by
      simpa [hT_eq_A] using hAnormal
    have _ : Unique (Sylow q Q) := Sylow.unique_of_normal T hTnormal
    exact Or.inl (Sylow.normal_of_subsingleton S)

private theorem hkt_iv54_generated_top_sylow_normal_of_not_normal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N : HasNormalPComplement q (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (_hS_not_normal : ¬ (S : Subgroup Q).Normal) :
    (S : Subgroup Q).Normal := by
  classical
  rcases hkt_iv54_generated_top_burnside_or_normal_source
      (Q := Q) (q := q) S hq_dvd A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop hNproper hcomp_N hquot_N hnot_burnside with hnormal | hburnside
  · exact hnormal
  · exact False.elim (hnot_burnside hburnside)

private theorem hkt_iv54_generated_top_local_quotient_core
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N : HasNormalPComplement q (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    (S : Subgroup Q).Normal ∨
      (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
  classical
  by_cases hSnormal : (S : Subgroup Q).Normal
  · exact Or.inl hSnormal
  · exact Or.inl (hkt_iv54_generated_top_sylow_normal_of_not_normal
      (Q := Q) (q := q) S hq_dvd A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop hNproper hcomp_N hquot_N hnot_burnside hSnormal)

private theorem hkt_iv54_generated_top_local_quotient_forces_burnside_or_normal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N : HasNormalPComplement q (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    (S : Subgroup Q).Normal ∨
      (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
  classical
  exact hkt_iv54_generated_top_local_quotient_core
    (Q := Q) (q := q) S hq_dvd A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop hNproper hcomp_N hquot_N hnot_burnside

private theorem hkt_iv54_witness_A_ne_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (_A_p : IsPGroup q A)
    (_hr : r.Prime) (_hr_ne_q : r ≠ q)
    (_x_p : IsPElement (p := r) x)
    (_x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q)) :
    A ≠ ⊥ := by
  classical
  intro hA_bot
  have hx_cent : x ∈ Subgroup.centralizer (A : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha_bot : a ∈ (⊥ : Subgroup Q) := by
      simpa [hA_bot] using ha
    have ha_one : a = 1 := by
      simpa using ha_bot
    simp [ha_one]
  exact x_not_cent hx_cent

private theorem hkt_iv54_generated_subgroup_ne_bot_of_witness
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q)) :
    ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) ≠ ⊥ := by
  classical
  intro hbot
  have hA_le_bot : A ≤ (⊥ : Subgroup Q) := by
    intro a ha
    have haH : a ∈ ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) :=
      (le_sup_left : (A : Subgroup Q) ≤
        ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q))) ha
    simpa [hbot] using haH
  exact hkt_iv54_witness_A_ne_bot (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent (le_bot_iff.mp hA_le_bot)

private theorem hkt_iv54_generated_subgroup_q_dvd_card_of_witness
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q)) :
    q ∣ Nat.card (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)))) := by
  classical
  have hA_ne_bot : A ≠ ⊥ := hkt_iv54_witness_A_ne_bot (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent
  have hq_dvd_A : q ∣ Nat.card A := by
    rcases A_p.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hA_ne_bot ((Subgroup.card_eq_one (H := A)).1 hcard))
    · exact hdiv
  exact hq_dvd_A.trans (Subgroup.card_dvd_of_le
    (show (A : Subgroup Q) ≤
      ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) from le_sup_left))

private theorem hkt_iv54_generated_subgroup_hasNormalPComplement_of_proper
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHproper : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) ≠ ⊤) :
    HasNormalPComplement q (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)))) := by
  classical
  exact hproper (((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)))
    (hkt_iv54_generated_subgroup_ne_bot_of_witness (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent)
    hHproper
    (hkt_iv54_generated_subgroup_q_dvd_card_of_witness (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent)

private theorem hkt_iv54_pprime_element_centralizes_A_of_generated_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hcompH : HasNormalPComplement q (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q))))) :
    x ∈ Subgroup.centralizer (A : Set Q) := by
  classical
  have hcentralizes : ∀ a : Q, a ∈ A → a * x = x * a :=
    hkt_iv54_generated_coprime_action_trivial_from_complement
      (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent hcompH
  rw [Subgroup.mem_centralizer_iff]
  exact hcentralizes

private theorem hkt_iv54_generated_top_forces_sylow_normal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤) :
    (S : Subgroup Q).Normal := by
  classical
  rcases hkt_iv54_generated_top_local_quotient_forces_burnside_or_normal
      (Q := Q) (q := q) S hq_dvd A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop hNproper hcomp_N hquot_N hnot_burnside with hnormal | hburnside
  · exact hnormal
  · exact False.elim (hnot_burnside hburnside)

private theorem hkt_iv54_witness_generated_proper_contradiction
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (_hq_dvd : q ∣ Nat.card Q)
    (_hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (_hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHproper : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) ≠ ⊤) : False := by
  classical
  have hcompH : HasNormalPComplement q (↥(((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)))) :=
    hkt_iv54_generated_subgroup_hasNormalPComplement_of_proper
      (Q := Q) (q := q) hproper A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHproper
  have hcent : x ∈ Subgroup.centralizer (A : Set Q) :=
    hkt_iv54_pprime_element_centralizes_A_of_generated_complement
      (Q := Q) (q := q) A r x A_p hr hr_ne_q x_p x_norm x_not_cent hcompH
  exact x_not_cent hcent

private theorem hkt_iv54_witness_generated_top_contradiction
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q))
    (hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤) : False := by
  classical
  have hnormal : (S : Subgroup Q).Normal :=
    hkt_iv54_generated_top_forces_sylow_normal
      (Q := Q) (q := q) S hq_dvd hNproper hcomp_N hquot_N
      hnot_burnside A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop
  exact hS_not_normal hnormal

private theorem hkt_hasNormalPComplement_of_burnside_iv51_witness_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (A : Subgroup Q) (r : ℕ) (x : Q)
    (A_p : IsPGroup q A)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q)) :
    HasNormalPComplement q Q := by
  classical
  by_cases hHtop : ((A : Subgroup Q) ⊔ (Subgroup.zpowers x : Subgroup Q)) = ⊤
  · exact False.elim
      (hkt_iv54_witness_generated_top_contradiction
        (Q := Q) (q := q) S hq_dvd hNproper hcomp_N hquot_N
        hnot_burnside hS_not_normal A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop)
  · exact False.elim
      (hkt_iv54_witness_generated_proper_contradiction
        (Q := Q) (q := q) hproper S hq_dvd hNproper hcomp_N hquot_N
        hnot_burnside A r x A_p hr hr_ne_q x_p x_norm x_not_cent hHtop)

/-- Huppert IV.5.3, in the minimal-non-`q`-nilpotent branch form used in
IV.5.4(a): if the fixed Sylow center is not weakly closed, the IV.5.3 witness
`A` and the prime-power element normalizing but not centralizing `A`, together
with the minimality hypotheses, force a normal `q`-complement in the ambient
group. -/
public theorem hkt_huppert_iv53_hasNormalPComplement_of_not_pNormal_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (hnot_pnormal : ¬ ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    HasNormalPComplement q Q := by
  classical
  obtain ⟨A, A_p, r, hr, hr_ne_q, x, x_p, x_norm, x_not_cent⟩ :=
    hkt_huppert_iv53_witness_of_not_pNormal (Q := Q) (q := q) S hnot_pnormal
  exact hkt_hasNormalPComplement_of_burnside_iv51_witness_minimal_non_pnilpotent
    (Q := Q) (q := q) hproper S hq_dvd hNproper hcomp_N hquot_N
    hnot_burnside hS_not_normal A r x A_p hr hr_ne_q x_p x_norm x_not_cent

private theorem hkt_iv54_centerIn_normal_of_normalizer_top
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hZNtop :
      Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) = ⊤) :
    (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := by
  classical
  exact Subgroup.normalizer_eq_top_iff.mp hZNtop


private theorem hkt_iv54_center_quotient_proper_subgroups_have_complement_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (_hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H) :
    letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
    ∀ H : Subgroup (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)),
      H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q H := by
  classical
  -- IV.5.4(a), quotient-minimality transfer source: lift a proper nontrivial
  -- subgroup of `Q/Z(S)` to `Q`, apply the ambient minimality hypothesis, and
  -- descend the normal `q`-complement back to the quotient subgroup.
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  letI : Z.Normal := by
    simpa [Z] using hZnormal
  intro Hbar hHbar_ne_bot hHbar_ne_top hqHbar
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let Hpre : Subgroup Q := Hbar.comap π
  have hZ_le_Hpre : Z ≤ Hpre := by
    intro z hz
    change π z ∈ Hbar
    have hzπ : π z = 1 := (QuotientGroup.eq_one_iff (N := Z) (x := z)).2 hz
    rw [hzπ]
    exact Hbar.one_mem
  have hHpre_map : Hpre.map π = Hbar := by
    simpa [Hpre, π] using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := π) (h := QuotientGroup.mk'_surjective Z) Hbar)
  have hHpre_ne_bot : Hpre ≠ ⊥ := by
    intro hbot
    exact hHbar_ne_bot (by
      calc
        Hbar = Hpre.map π := hHpre_map.symm
        _ = (⊥ : Subgroup Q).map π := by rw [hbot]
        _ = ⊥ := by simp)
  have hHpre_ne_top : Hpre ≠ ⊤ := by
    intro htop
    exact hHbar_ne_top (by
      calc
        Hbar = Hpre.map π := hHpre_map.symm
        _ = (⊤ : Subgroup Q).map π := by rw [htop]
        _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Z))
  have hqHpre : q ∣ Nat.card Hpre := by
    have hmap_dvd : Nat.card (Hpre.map π) ∣ Nat.card Hpre :=
      Subgroup.card_map_dvd (H := Hpre) π
    exact hqHbar.trans (by simpa [hHpre_map] using hmap_dvd)
  have hcomp_pre : HasNormalPComplement q Hpre :=
    hproper Hpre hHpre_ne_bot hHpre_ne_top hqHpre
  haveI : (Z.subgroupOf Hpre).Normal := by
    have hnorm_top : Subgroup.normalizer (Z : Set Q) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Z.Normal)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := Z) (K := Hpre) hZ_le_Hpre).2 (by
          simp [hnorm_top])
  have hcomp_map : HasNormalPComplement q (Hpre.map π) :=
    hkt_hasNormalPComplement_map_quotient_of_normal_subgroup
      (H := Q) (p := q) (N := Z) (K := Hpre) hZ_le_Hpre hcomp_pre
  rw [← hHpre_map]
  exact hcomp_map

private theorem hkt_iv54_center_quotient_q_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q)) :
    letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
    q ∣ Nat.card (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)) := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  letI : Z.Normal := by
    simpa [Z] using hZnormal
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let Sbar : Subgroup (Q ⧸ Z) := (S : Subgroup Q).map π
  have hSbar_p : IsPGroup q Sbar := IsPGroup.map S.isPGroup' π
  have hSbar_ne_bot : Sbar ≠ ⊥ := by
    intro hbot
    exact hcenter_ne_sylow (by
      apply le_antisymm
      · intro x hx
        exact hx.1
      · intro s hs
        have hmap : π s ∈ Sbar := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
        have hmap_bot : π s ∈ (⊥ : Subgroup (Q ⧸ Z)) := by
          simpa [Sbar, hbot] using hmap
        have hpi_one : π s = 1 := by
          simpa using hmap_bot
        exact (QuotientGroup.eq_one_iff (N := Z) (x := s)).1 hpi_one)
  have hq_dvd_Sbar : q ∣ Nat.card Sbar := by
    rcases hSbar_p.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hSbar_ne_bot ((Subgroup.card_eq_one (H := Sbar)).1 hcard))
    · exact hdvd
  exact hq_dvd_Sbar.trans (Subgroup.card_subgroup_dvd_card Sbar)

private theorem hkt_iv54_center_quotient_hasNormalPComplement_of_quotient_complement_direct
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (_hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hquot_comp :
      HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    HasNormalPComplement q Q := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  haveI : Z.Normal := by simpa [Z] using hZnormal
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨Kbar, hKbar_normal, hKbar_coprime, hquot_p⟩ := hquot_comp
  let pre : Subgroup Q := Kbar.comap π
  have hZ_le_S : Z ≤ (S : Subgroup Q) := by
    intro x hx
    exact hx.1
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hZ_ne_bot : Z ≠ ⊥ := by
    simpa [Z] using section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
  have hq_dvd_Z : q ∣ Nat.card Z := by
    have hZp : IsPGroup q Z := IsPGroup.to_le S.isPGroup' hZ_le_S
    rcases hZp.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hZ_ne_bot ((Subgroup.card_eq_one (H := Z)).1 hcard))
    · exact hdvd
  have hZ_le_pre : Z ≤ pre := by
    intro z hz
    change π z ∈ Kbar
    have hzπ : π z = 1 := (QuotientGroup.eq_one_iff (N := Z) (x := z)).2 hz
    rw [hzπ]
    exact Kbar.one_mem
  have hq_dvd_pre : q ∣ Nat.card pre := by
    have hZsub_dvd : Nat.card (Z.subgroupOf pre) ∣ Nat.card pre :=
      Subgroup.card_subgroup_dvd_card (Z.subgroupOf pre)
    have hZsub_card : Nat.card (Z.subgroupOf pre) = Nat.card Z :=
      natCard_subgroupOf_eq Z pre hZ_le_pre
    exact hq_dvd_Z.trans (by simpa [hZsub_card] using hZsub_dvd)
  have hpre_ne_bot : pre ≠ ⊥ := by
    intro hbot
    exact hZ_ne_bot (le_bot_iff.mp (by simpa [hbot] using hZ_le_pre))
  have hq_dvd_quot : q ∣ Nat.card (Q ⧸ Z) := by
    let Sbar : Subgroup (Q ⧸ Z) := (S : Subgroup Q).map π
    have hSbar_p : IsPGroup q Sbar :=
      IsPGroup.map (p := q) (H := (S : Subgroup Q)) S.isPGroup' π
    have hSbar_ne_bot : Sbar ≠ ⊥ := by
      intro hSbar_bot
      have hS_le_Z : (S : Subgroup Q) ≤ Z := by
        intro x hxS
        have hxSbar : π x ∈ Sbar := Subgroup.mem_map_of_mem π hxS
        have hxbot : π x ∈ (⊥ : Subgroup (Q ⧸ Z)) := by
          simpa [Sbar, hSbar_bot] using hxSbar
        exact (QuotientGroup.eq_one_iff (N := Z) (x := x)).1
          (Subgroup.mem_bot.mp hxbot)
      exact hcenter_ne_sylow (by simpa [Z] using le_antisymm hZ_le_S hS_le_Z)
    have hq_dvd_Sbar : q ∣ Nat.card Sbar := by
      rcases hSbar_p.card_eq_or_dvd with hcard | hdvd
      · exact False.elim (hSbar_ne_bot ((Subgroup.card_eq_one (H := Sbar)).1 hcard))
      · exact hdvd
    exact hq_dvd_Sbar.trans (Subgroup.card_subgroup_dvd_card Sbar)
  have hpre_normal : pre.Normal := by
    simpa [pre, π] using hKbar_normal.comap π
  have hpre_map : pre.map π = Kbar := by
    simpa [pre] using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := π) (h := QuotientGroup.mk'_surjective Z) Kbar)
  have hquot_pre_p :
      letI : pre.Normal := hpre_normal
      IsPGroup q (Q ⧸ pre) := by
    haveI : pre.Normal := hpre_normal
    have hmid : IsPGroup q ((Q ⧸ Z) ⧸ pre.map π) := by
      let e1 : (Q ⧸ Z) ⧸ Kbar ≃* (Q ⧸ Z) ⧸ pre.map π :=
        QuotientGroup.quotientMulEquivOfEq hpre_map.symm
      exact hquot_p.of_equiv e1
    let e2 : (Q ⧸ Z) ⧸ pre.map π ≃* Q ⧸ pre :=
      QuotientGroup.quotientQuotientEquivQuotient (N := Z) (M := pre) hZ_le_pre
    exact hmid.of_equiv e2
  have hpre_ne_top : pre ≠ ⊤ := by
    intro hpre_top
    have hKbar_top : Kbar = ⊤ := by
      calc
        Kbar = pre.map π := hpre_map.symm
        _ = (⊤ : Subgroup Q).map π := by rw [hpre_top]
        _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Z)
    exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hKbar_coprime)
      (by simpa [hKbar_top] using hq_dvd_quot)
  have hpre_comp : HasNormalPComplement q pre :=
    hproper pre hpre_ne_bot hpre_ne_top hq_dvd_pre
  letI : pre.Normal := hpre_normal
  exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    (G := Q) (p := q) pre hquot_pre_p hpre_comp
private theorem hkt_iv54_center_quotient_sylow_normal_lift_from_image_direct
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (himage :
      ((S : Subgroup Q).map
        (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))).Normal) :
    (S : Subgroup Q).Normal := by
  classical
  have hZleS :
      centerIn (G := Q) (S : Subgroup Q) ≤ (S : Subgroup Q) := by
    intro x hx
    exact hx.1
  have hcomap :
      Subgroup.comap
          (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))
          ((S : Subgroup Q).map
            (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) =
        (S : Subgroup Q) := by
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hZleS
  have hpre :
      (Subgroup.comap
          (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))
          ((S : Subgroup Q).map
            (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)))).Normal :=
    himage.comap
      (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))
  simpa [hcomap] using hpre
private theorem hkt_iv54_proper_sylow_normalizer_quotient_control_false_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot : ¬ HasNormalPComplement q Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hNcomp :
      HasNormalPComplement q
        (↥(Subgroup.normalizer ((S : Subgroup Q) : Set Q))))
    (hNquot :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q))))) :
    False := by
  classical
  induction hcard : Nat.card Q using Nat.strong_induction_on generalizing Q with
  | h n ih =>
    by_cases hSnormal : (S : Subgroup Q).Normal
    · exact hNproper (Subgroup.normalizer_eq_top_iff.mpr hSnormal)
    by_cases hQcomp : HasNormalPComplement q Q
    · exact hnot hQcomp
    by_cases hQp : IsPGroup q Q
    · exact hnot (hkt_hasNormalPComplement_of_isPGroup (Q := Q) (p := q) hQp)
    · -- IV.5.4(a), proper-normalizer core source: split into the `q`-normal
      -- branch handled by Grün's second theorem and the non-`q`-normal branch
      -- handled by Huppert IV.5.3.
      have hnot_burnside :
          ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
        intro hburnside
        exact hnot (hkt_hasNormalPComplement_of_sylow_le_center_normalizer S hburnside)
      by_cases hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)
      · -- Remaining p-normal/Grün IV.3.7 transfer branch.  The proper
        -- `N_Q(Z(S))` case is formal from minimality plus Grün's second theorem;
        -- only the top center-normalizer quotient branch remains a source step.
        let ZN : Subgroup Q :=
          Subgroup.normalizer ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
        by_cases hZNtop : ZN = ⊤
        · have hZnormal :
              (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := by
            exact Subgroup.normalizer_eq_top_iff.mp (by simpa [ZN] using hZNtop)
          by_cases hcenter_eq_sylow :
              centerIn (G := Q) (S : Subgroup Q) = (S : Subgroup Q)
          · have hSnormal' : (S : Subgroup Q).Normal := by
              simpa [hcenter_eq_sylow] using hZnormal
            exact False.elim (hSnormal hSnormal')
          · letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
            by_cases hquot_comp :
                HasNormalPComplement q
                  (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))
            · exact hnot
                (hkt_iv54_center_quotient_hasNormalPComplement_of_quotient_complement_direct
                  (Q := Q) (q := q) S hproper hq_dvd hpnormal hcenter_eq_sylow
                  hquot_comp)
            · let π : Q →* Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) :=
                QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)
              by_cases himage : ((S : Subgroup Q).map π).Normal
              · have hSnormal' : (S : Subgroup Q).Normal :=
                  hkt_iv54_center_quotient_sylow_normal_lift_from_image_direct
                    (Q := Q) (q := q) S (by simpa [π] using himage)
                exact False.elim (hSnormal hSnormal')
              · let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
                let Qbar : Type u := Q ⧸ Z
                letI : Z.Normal := by simpa [Z] using hZnormal
                let πZ : Q →* Qbar := QuotientGroup.mk' Z
                let Sbar : Sylow q Qbar :=
                  S.mapSurjective (f := πZ) (QuotientGroup.mk'_surjective Z)
                have hZ_le_S : Z ≤ (S : Subgroup Q) := by
                  intro x hx
                  exact hx.1
                have hproper_bar :
                    ∀ H : Subgroup Qbar, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
                      HasNormalPComplement q H := by
                  simpa [Qbar, Z] using
                    hkt_iv54_center_quotient_proper_subgroups_have_complement_source
                      (Q := Q) (q := q) S hcenter_eq_sylow hproper
                have hq_bar : q ∣ Nat.card Qbar := by
                  simpa [Qbar, Z] using
                    hkt_iv54_center_quotient_q_dvd_card (Q := Q) (q := q) S hcenter_eq_sylow
                have hquot_not_bar : ¬ HasNormalPComplement q Qbar := by
                  simpa [Qbar, Z] using hquot_comp
                have hSbar_not_normal : ¬ (Sbar : Subgroup Qbar).Normal := by
                  intro hSbar_normal
                  exact himage (by
                    simpa [Qbar, Z, π, πZ, Sbar, Sylow.coe_mapSurjective] using
                      hSbar_normal)
                have hSbar_normalizer_proper :
                    Subgroup.normalizer ((Sbar : Subgroup Qbar) : Set Qbar) ≠ ⊤ := by
                  intro htop
                  exact hSbar_not_normal (Subgroup.normalizer_eq_top_iff.mp htop)
                have hSbar_not_burnside :
                    ¬ (Sbar : Subgroup Qbar) ≤
                      centerIn (G := Qbar) (Subgroup.normalizer (Sbar : Subgroup Qbar)) := by
                  intro hburnside_bar
                  exact hquot_not_bar
                    (hkt_hasNormalPComplement_of_sylow_le_center_normalizer
                      (Q := Qbar) (q := q) Sbar hburnside_bar)
                have hNbar_comp :
                    HasNormalPComplement q
                      (Subgroup.normalizer ((Sbar : Subgroup Qbar) : Set Qbar)) := by
                  have hcomp_norm_image :
                      HasNormalPComplement q
                        (Subgroup.normalizer (((S : Subgroup Q).map πZ : Subgroup Qbar) : Set Qbar)) := by
                    simpa [Qbar, Z, πZ] using
                      hkt_hasNormalPComplement_normalizer_map_quotient_of_normalizer
                        (G := Q) (p := q) (N := Z) (T := (S : Subgroup Q))
                        hZ_le_S hNcomp
                  have hSbar_subgroup_eq : (Sbar : Subgroup Qbar) = (S : Subgroup Q).map πZ := by
                    simp [Sbar, Sylow.coe_mapSurjective]
                  convert hcomp_norm_image
                have hNbar_quot :
                    IsPGroup q
                      ((Subgroup.normalizer ((Sbar : Subgroup Qbar) : Set Qbar)) ⧸
                        ((Subgroup.centralizer ((Sbar : Subgroup Qbar) : Set Qbar)).subgroupOf
                          (Subgroup.normalizer ((Sbar : Subgroup Qbar) : Set Qbar)))) := by
                  exact hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
                    (Q := Qbar) (q := q) (U := (Sbar : Subgroup Qbar)) Sbar.isPGroup'
                    hNbar_comp
                by_cases hQbar_p : IsPGroup q Qbar
                · exact hquot_not_bar
                    (hkt_hasNormalPComplement_of_isPGroup (Q := Qbar) (p := q) hQbar_p)
                · by_cases hpnormal_bar : ∀ T : Sylow q Qbar, centerIn (G := Qbar) (Sbar : Subgroup Qbar) ≤ (T : Subgroup Qbar) → centerIn (G := Qbar) (Sbar : Subgroup Qbar) = centerIn (G := Qbar) (T : Subgroup Qbar)
                  · have hsource_false : False := by
                      let Sbar' : Sylow q (Q ⧸ Z) := by
                        simpa [Qbar] using Sbar
                      let ZNbar : Subgroup (Q ⧸ Z) :=
                        Subgroup.normalizer
                          ((centerIn (G := Q ⧸ Z) (Sbar' : Subgroup (Q ⧸ Z)) :
                            Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z))
                      have hq_bar' : q ∣ Nat.card (Q ⧸ Z) := by
                        simpa [Qbar] using hq_bar
                      have hproper_bar' :
                          ∀ H : Subgroup (Q ⧸ Z), H ≠ ⊥ → H ≠ ⊤ →
                            q ∣ Nat.card H → HasNormalPComplement q H := by
                        simpa [Qbar] using hproper_bar
                      have hquot_not_bar' : ¬ HasNormalPComplement q (Q ⧸ Z) := by
                        simpa [Qbar] using hquot_not_bar
                      have hpnormal_bar' : ∀ T : Sylow q (Q ⧸ Z), centerIn (G := Q ⧸ Z) (Sbar' : Subgroup (Q ⧸ Z)) ≤ (T : Subgroup (Q ⧸ Z)) → centerIn (G := Q ⧸ Z) (Sbar' : Subgroup (Q ⧸ Z)) = centerIn (G := Q ⧸ Z) (T : Subgroup (Q ⧸ Z)) := by
                        simpa [Qbar] using hpnormal_bar
                      by_cases hZNbar_top : ZNbar = ⊤
                      · by_cases hcenterbar_eq_sylow :
                            centerIn (G := Q ⧸ Z) (Sbar' : Subgroup (Q ⧸ Z)) =
                              (Sbar' : Subgroup (Q ⧸ Z))
                        · have hSbar'_normal : (Sbar' : Subgroup (Q ⧸ Z)).Normal := by
                            have hcenterbar_normal :
                                (centerIn (G := Q ⧸ Z) (Sbar' : Subgroup (Q ⧸ Z)) :
                                  Subgroup (Q ⧸ Z)).Normal :=
                              Subgroup.normalizer_eq_top_iff.mp
                                (by simpa [ZNbar] using hZNbar_top)
                            simpa [hcenterbar_eq_sylow] using hcenterbar_normal
                          exact hSbar_not_normal (by simpa [Qbar] using hSbar'_normal)
                        · -- Remaining source: after quotienting by `Z(S)`,
                          -- the induced Sylow is still in the top
                          -- center-normalizer, proper-normalizer,
                          -- non-`q`-nilpotent, non-`q`-group, `q`-normal
                          -- branch.
                          have hZ_ne_bot : Z ≠ ⊥ := by
                            have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
                              Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
                            simpa [Z] using
                              section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
                          have hZ_nontrivial : Nontrivial Z :=
                            (Subgroup.nontrivial_iff_ne_bot (H := Z)).2 hZ_ne_bot
                          have hZ_card : 1 < Nat.card Z :=
                            Finite.one_lt_card_iff_nontrivial.mpr hZ_nontrivial
                          have hcard_mul :
                              Nat.card Q = Nat.card (Q ⧸ Z) * Nat.card Z := by
                            simpa [Z] using
                              (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Z))
                          have hQbar_lt_Q : Nat.card (Q ⧸ Z) < Nat.card Q := by
                            calc
                              Nat.card (Q ⧸ Z) <
                                  Nat.card (Q ⧸ Z) * Nat.card Z :=
                                lt_mul_of_one_lt_right Nat.card_pos hZ_card
                              _ = Nat.card Q := hcard_mul.symm
                          have hQbar_lt_n : Nat.card (Q ⧸ Z) < n := by
                            simpa [hcard] using hQbar_lt_Q
                          have hNproper_bar' :
                              Subgroup.normalizer ((Sbar' : Subgroup (Q ⧸ Z)) :
                                Set (Q ⧸ Z)) ≠ ⊤ := by
                            simpa [Qbar] using hSbar_normalizer_proper
                          have hNcomp_bar' :
                              HasNormalPComplement q
                                (↥(Subgroup.normalizer
                                  ((Sbar' : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z)))) := by
                            simpa [Qbar] using hNbar_comp
                          have hNquot_bar' :
                              IsPGroup q
                                ((Subgroup.normalizer
                                    ((Sbar' : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z))) ⧸
                                  ((Subgroup.centralizer
                                      ((Sbar' : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z))).subgroupOf
                                    (Subgroup.normalizer
                                      ((Sbar' : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z))))) := by
                            simpa [Qbar] using hNbar_quot
                          exact ih (Nat.card (Q ⧸ Z)) hQbar_lt_n
                            (Q := Q ⧸ Z) Sbar' hproper_bar' hq_bar'
                            hquot_not_bar' hNproper_bar' hNcomp_bar' hNquot_bar' rfl
                      · have hSbar_le_ZNbar : (Sbar' : Subgroup (Q ⧸ Z)) ≤ ZNbar := by
                          simpa [ZNbar] using
                            sylow_le_normalizer_centerIn (Q := Q ⧸ Z) (q := q) Sbar'
                        have hZNbar_ne_bot : ZNbar ≠ ⊥ := by
                          intro hbot
                          have hSbar_le_bot : (Sbar' : Subgroup (Q ⧸ Z)) ≤ ⊥ := by
                            simpa [hbot] using hSbar_le_ZNbar
                          exact (Sylow.ne_bot_of_dvd_card (G := Q ⧸ Z) (p := q) Sbar' hq_bar')
                            (le_bot_iff.mp hSbar_le_bot)
                        have hq_dvd_ZNbar : q ∣ Nat.card ZNbar :=
                          (Sbar'.dvd_card_of_dvd_card hq_bar').trans
                            (Subgroup.card_dvd_of_le hSbar_le_ZNbar)
                        have hZNbar_comp : HasNormalPComplement q ZNbar :=
                          hproper_bar' ZNbar hZNbar_ne_bot hZNbar_top hq_dvd_ZNbar
                        have hresbar_comp :
                            HasNormalPComplement q (hktAbelianPResidual q (Q ⧸ Z)) :=
                          hktAbelianPResidual_hasNormalPComplement_of_center_normalizer_minimal
                            (Q := Q ⧸ Z) (q := q) hproper_bar' Sbar' hpnormal_bar'
                            (by simpa [ZNbar] using hZNbar_comp)
                            (by simpa [ZNbar] using hq_dvd_ZNbar)
                        exact hquot_not_bar'
                          (hkt_grun_second_hasNormalPComplement_of_center_normalizer
                            (Q := Q ⧸ Z) (q := q) Sbar' hpnormal_bar'
                            (by simpa [ZNbar] using hZNbar_comp) hresbar_comp)
                    exact hsource_false
                  · exact hquot_not_bar
                      (hkt_huppert_iv53_hasNormalPComplement_of_not_pNormal_minimal_non_pnilpotent
                        (Q := Qbar) (q := q) hproper_bar Sbar hq_bar
                        hSbar_normalizer_proper hNbar_comp hNbar_quot hSbar_not_burnside
                        hSbar_not_normal hpnormal_bar)
        · have hS_le_ZN : (S : Subgroup Q) ≤ ZN := by
            simpa [ZN] using sylow_le_normalizer_centerIn (Q := Q) (q := q) S
          have hZN_ne_bot : ZN ≠ ⊥ := by
            intro hbot
            have hS_le_bot : (S : Subgroup Q) ≤ ⊥ := by
              simpa [hbot] using hS_le_ZN
            exact (Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd)
              (le_bot_iff.mp hS_le_bot)
          have hq_dvd_ZN : q ∣ Nat.card ZN :=
            (S.dvd_card_of_dvd_card hq_dvd).trans (Subgroup.card_dvd_of_le hS_le_ZN)
          have hZN_comp : HasNormalPComplement q ZN :=
            hproper ZN hZN_ne_bot hZNtop hq_dvd_ZN
          have hres_comp : HasNormalPComplement q (hktAbelianPResidual q Q) :=
            hktAbelianPResidual_hasNormalPComplement_of_center_normalizer_minimal
              (Q := Q) (q := q) hproper S hpnormal
              (by simpa [ZN] using hZN_comp) (by simpa [ZN] using hq_dvd_ZN)
          exact hnot
            (hkt_grun_second_hasNormalPComplement_of_center_normalizer
              (Q := Q) (q := q) S hpnormal (by simpa [ZN] using hZN_comp) hres_comp)
      · exact hnot
          (hkt_huppert_iv53_hasNormalPComplement_of_not_pNormal_minimal_non_pnilpotent
            (Q := Q) (q := q) hproper S hq_dvd hNproper hNcomp hNquot
            hnot_burnside hSnormal hpnormal)

private theorem hkt_iv54_center_quotient_proper_sylow_normalizer_false_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hproper_bar :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ∀ H : Subgroup (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q H)
    (hquot_not :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ¬ HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)))
    (Sbar :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      Sylow q (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)))
    (hSbar_normalizer_proper :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      Subgroup.normalizer ((Sbar : Subgroup
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) : Set
          (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) ≠ ⊤) :
    False := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  letI : Z.Normal := by
    simpa [Z] using hZnormal
  let Qbar : Type u := Q ⧸ Z
  let Nbar : Subgroup Qbar := Subgroup.normalizer ((Sbar : Subgroup Qbar) : Set Qbar)
  have hq_bar : q ∣ Nat.card Qbar := by
    simpa [Qbar, Z] using
      hkt_iv54_center_quotient_q_dvd_card (Q := Q) (q := q) S hcenter_ne_sylow
  have hSbar_ne_bot : (Sbar : Subgroup Qbar) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Qbar) (p := q) Sbar hq_bar
  have hNbar_ne_bot : Nbar ≠ ⊥ := by
    intro hNbot
    exact hSbar_ne_bot (eq_bot_iff.mpr (by
      intro x hx
      have hxN : x ∈ Nbar := Subgroup.le_normalizer hx
      simpa [Nbar, hNbot] using hxN))
  have hq_Nbar : q ∣ Nat.card Nbar := by
    have hq_Sbar : q ∣ Nat.card (Sbar : Subgroup Qbar) :=
      Sbar.dvd_card_of_dvd_card hq_bar
    exact hq_Sbar.trans (Subgroup.card_dvd_of_le (Subgroup.le_normalizer
      (H := (Sbar : Subgroup Qbar))))
  have hNbar_comp : HasNormalPComplement q Nbar := by
    simpa [Qbar, Z, Nbar] using
      hproper_bar Nbar hNbar_ne_bot hSbar_normalizer_proper hq_Nbar
  have hNbar_quot :
      IsPGroup q
        (Nbar ⧸
          ((Subgroup.centralizer ((Sbar : Subgroup Qbar) : Set Qbar)).subgroupOf
            Nbar)) := by
    simpa [Nbar] using
      hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
        (Q := Qbar) (q := q) (U := (Sbar : Subgroup Qbar)) Sbar.isPGroup'
        (by simpa [Nbar] using hNbar_comp)
  exact
    hkt_iv54_proper_sylow_normalizer_quotient_control_false_source
      (Q := Qbar) (q := q) Sbar
      (by simpa [Qbar, Z] using hproper_bar)
      (by simpa [Qbar, Z] using hq_bar)
      (by simpa [Qbar, Z] using hquot_not)
      (by simpa [Qbar, Z, Nbar] using hSbar_normalizer_proper)
      (by simpa [Nbar] using hNbar_comp)
      (by simpa [Nbar] using hNbar_quot)
private theorem hkt_iv54_center_quotient_image_sylow_normal_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hproper_bar :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ∀ H : Subgroup (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q H)
    (_hq_dvd : q ∣ Nat.card Q)
    (_hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hquot_not :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ¬ HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
    ((S : Subgroup Q).map
      (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))).Normal := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  letI : Z.Normal := by
    simpa [Z] using hZnormal
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let Sbar : Sylow q (Q ⧸ Z) :=
    S.mapSurjective (f := π) (QuotientGroup.mk'_surjective Z)
  change (Sbar : Subgroup (Q ⧸ Z)).Normal
  by_cases hNtop : Subgroup.normalizer ((Sbar : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z)) = ⊤
  · exact Subgroup.normalizer_eq_top_iff.mp hNtop
  · exact False.elim
      (hkt_iv54_center_quotient_proper_sylow_normalizer_false_source
        (Q := Q) (q := q) S hcenter_ne_sylow hproper_bar hquot_not Sbar hNtop)

private theorem hkt_iv54_center_quotient_image_sylow_normal_from_minimal_counterexample
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hquot_not :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ¬ HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
    ((S : Subgroup Q).map
      (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))).Normal := by
  classical
  have hproper_bar :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ∀ H : Subgroup (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q)),
        H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H → HasNormalPComplement q H :=
    hkt_iv54_center_quotient_proper_subgroups_have_complement_source
      (Q := Q) (q := q) S hcenter_ne_sylow hproper
  exact hkt_iv54_center_quotient_image_sylow_normal_source
    (Q := Q) (q := q) S hcenter_ne_sylow hproper_bar hq_dvd hpnormal hquot_not

private theorem hkt_iv54_center_quotient_nonpnilpotent_minimal_counterexample_step
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hquot_not :
      letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
      ¬ HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
    ((S : Subgroup Q).map
      (QuotientGroup.mk' (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))).Normal := by
  classical
  exact hkt_iv54_center_quotient_image_sylow_normal_from_minimal_counterexample
    (Q := Q) (q := q) S hcenter_ne_sylow hproper hq_dvd hpnormal hquot_not

private theorem hkt_iv54_center_quotient_raw_preimage_of_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hq_dvd : q ∣ Nat.card Q)
    (_hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hquot_comp :
      HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    ∃ preimage : Subgroup Q,
      preimage ≠ ⊥ ∧
        preimage ≠ ⊤ ∧
          q ∣ Nat.card preimage ∧
            ∃ hpreimage_normal : preimage.Normal,
              letI : preimage.Normal := hpreimage_normal
              IsPGroup q (Q ⧸ preimage) := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  haveI : Z.Normal := by simpa [Z] using hZnormal
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨Kbar, hKbar_normal, hKbar_coprime, hquot_p⟩ := hquot_comp
  have hZ_le_S : Z ≤ (S : Subgroup Q) := by
    intro x hx
    exact hx.1
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hZ_ne_bot : Z ≠ ⊥ := by
    simpa [Z] using section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
  have hq_dvd_Z : q ∣ Nat.card Z := by
    have hZp : IsPGroup q Z := IsPGroup.to_le S.isPGroup' hZ_le_S
    rcases hZp.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hZ_ne_bot ((Subgroup.card_eq_one (H := Z)).1 hcard))
    · exact hdvd
  have hZ_le_preimage : Z ≤ Kbar.comap π := by
    intro z hz
    change π z ∈ Kbar
    have hzπ : π z = 1 := (QuotientGroup.eq_one_iff (N := Z) (x := z)).2 hz
    rw [hzπ]
    exact Kbar.one_mem
  have hq_dvd_preimage : q ∣ Nat.card (Kbar.comap π) := by
    have hZsub_dvd : Nat.card (Z.subgroupOf (Kbar.comap π)) ∣ Nat.card (Kbar.comap π) :=
      Subgroup.card_subgroup_dvd_card (Z.subgroupOf (Kbar.comap π))
    have hZsub_card : Nat.card (Z.subgroupOf (Kbar.comap π)) = Nat.card Z :=
      natCard_subgroupOf_eq Z (Kbar.comap π) hZ_le_preimage
    exact hq_dvd_Z.trans (by simpa [hZsub_card] using hZsub_dvd)
  have hpreimage_ne_bot : Kbar.comap π ≠ ⊥ := by
    intro hbot
    exact hZ_ne_bot (le_bot_iff.mp (by simpa [hbot] using hZ_le_preimage))
  have hq_dvd_quot : q ∣ Nat.card (Q ⧸ Z) := by
    let Sbar : Subgroup (Q ⧸ Z) := (S : Subgroup Q).map π
    have hSbar_p : IsPGroup q Sbar :=
      IsPGroup.map (p := q) (H := (S : Subgroup Q)) S.isPGroup' π
    have hSbar_ne_bot : Sbar ≠ ⊥ := by
      intro hSbar_bot
      have hS_le_Z : (S : Subgroup Q) ≤ Z := by
        intro x hxS
        have hxSbar : π x ∈ Sbar := Subgroup.mem_map_of_mem π hxS
        have hxbot : π x ∈ (⊥ : Subgroup (Q ⧸ Z)) := by
          simpa [Sbar, hSbar_bot] using hxSbar
        exact (QuotientGroup.eq_one_iff (N := Z) (x := x)).1
          (Subgroup.mem_bot.mp hxbot)
      exact hcenter_ne_sylow (by simpa [Z] using le_antisymm hZ_le_S hS_le_Z)
    have hq_dvd_Sbar : q ∣ Nat.card Sbar := by
      rcases hSbar_p.card_eq_or_dvd with hcard | hdvd
      · exact False.elim (hSbar_ne_bot ((Subgroup.card_eq_one (H := Sbar)).1 hcard))
      · exact hdvd
    exact hq_dvd_Sbar.trans (Subgroup.card_subgroup_dvd_card Sbar)
  have hpreimage_normal : (Kbar.comap π).Normal := hKbar_normal.comap π
  have hpreimage_map : (Kbar.comap π).map π = Kbar := by
    exact Subgroup.map_comap_eq_self_of_surjective
      (f := π) (h := QuotientGroup.mk'_surjective Z) Kbar
  have hquot_preimage_p :
      letI : (Kbar.comap π).Normal := hpreimage_normal
      IsPGroup q (Q ⧸ Kbar.comap π) := by
    let pre : Subgroup Q := Kbar.comap π
    haveI : pre.Normal := by simpa [pre] using hpreimage_normal
    have hZ_le_pre : Z ≤ pre := by simpa [pre] using hZ_le_preimage
    have hpre_map : pre.map π = Kbar := by simpa [pre] using hpreimage_map
    have hmid : IsPGroup q ((Q ⧸ Z) ⧸ pre.map π) := by
      let e1 : (Q ⧸ Z) ⧸ Kbar ≃* (Q ⧸ Z) ⧸ pre.map π :=
        QuotientGroup.quotientMulEquivOfEq hpre_map.symm
      exact hquot_p.of_equiv e1
    let e2 : (Q ⧸ Z) ⧸ pre.map π ≃* Q ⧸ pre :=
      QuotientGroup.quotientQuotientEquivQuotient (N := Z) (M := pre) hZ_le_pre
    simpa [pre] using hmid.of_equiv e2
  refine ⟨Kbar.comap π, hpreimage_ne_bot, ?_, hq_dvd_preimage,
    hpreimage_normal, hquot_preimage_p⟩
  intro hpre_top
  have hKbar_top : Kbar = ⊤ := by
    calc
      Kbar = (Kbar.comap π).map π := by
        exact (Subgroup.map_comap_eq_self_of_surjective
          (f := π) (h := QuotientGroup.mk'_surjective Z) Kbar).symm
      _ = (⊤ : Subgroup Q).map π := by rw [hpre_top]
      _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Z)
  exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hKbar_coprime)
    (by simpa [hKbar_top] using hq_dvd_quot)

private theorem hkt_iv54_center_quotient_complement_lift_from_extension
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (_S : Sylow q Q) (preimage : Subgroup Q)
    (hpreimage_normal : preimage.Normal)
    (hquot_preimage_p :
      letI : preimage.Normal := hpreimage_normal
      IsPGroup q (Q ⧸ preimage))
    (hpreimage_has_complement : HasNormalPComplement q preimage) :
    HasNormalPComplement q Q := by
  classical
  letI : preimage.Normal := hpreimage_normal
  exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    (G := Q) (p := q) preimage hquot_preimage_p hpreimage_has_complement

private theorem hkt_iv54_center_quotient_complement_lift_core
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (preimage : Subgroup Q)
    (hpreimage_normal : preimage.Normal)
    (hquot_preimage_p :
      letI : preimage.Normal := hpreimage_normal
      IsPGroup q (Q ⧸ preimage))
    (hpreimage_has_complement : HasNormalPComplement q preimage) :
    HasNormalPComplement q Q := by
  classical
  exact hkt_iv54_center_quotient_complement_lift_from_extension
    (Q := Q) (q := q) S preimage hpreimage_normal hquot_preimage_p
    hpreimage_has_complement

private theorem hkt_iv54_center_quotient_complement_lifts_from_preimage
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (preimage : Subgroup Q)
    (hpreimage_normal : preimage.Normal)
    (hquot_preimage_p :
      letI : preimage.Normal := hpreimage_normal
      IsPGroup q (Q ⧸ preimage))
    (hpreimage_has_complement : HasNormalPComplement q preimage) :
    HasNormalPComplement q Q := by
  classical
  exact hkt_iv54_center_quotient_complement_lift_core
    (Q := Q) (q := q) S preimage hpreimage_normal hquot_preimage_p
    hpreimage_has_complement

private theorem hkt_iv54_center_quotient_nonpnilpotent_forces_sylow_normal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hquot_not :
      ¬ HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    (S : Subgroup Q).Normal := by
  classical
  have himage :=
    hkt_iv54_center_quotient_nonpnilpotent_minimal_counterexample_step
      (Q := Q) (q := q) S hcenter_ne_sylow hproper hq_dvd hpnormal
      (by simpa using hquot_not)
  exact hkt_iv54_center_quotient_sylow_normal_lift_from_image_direct
    (Q := Q) (q := q) S himage

private theorem hkt_iv54_center_quotient_pnilpotent_lifts_complement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    [hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hq_dvd : q ∣ Nat.card Q)
    (_hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q))
    (hquot_comp :
      HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))) :
    HasNormalPComplement q Q := by
  classical
  obtain ⟨preimage, hpreimage_ne_bot, hpreimage_ne_top, hpreimage_q_dvd_card,
      hpreimage_normal, hquot_preimage_p⟩ :=
    hkt_iv54_center_quotient_raw_preimage_of_complement
      (Q := Q) (q := q) S hq_dvd hpnormal hcenter_ne_sylow hquot_comp
  have hpreimage_has_complement : HasNormalPComplement q preimage :=
    hproper preimage hpreimage_ne_bot hpreimage_ne_top hpreimage_q_dvd_card
  exact hkt_iv54_center_quotient_complement_lifts_from_preimage
    (Q := Q) (q := q) S preimage hpreimage_normal hquot_preimage_p
    hpreimage_has_complement

private theorem hkt_iv54_center_eq_sylow_top_contradiction
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (hZNtop :
      Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) = ⊤)
    (hcenter_eq_sylow :
      centerIn (G := Q) (S : Subgroup Q) = (S : Subgroup Q)) :
    False := by
  classical
  have hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal :=
    hkt_iv54_centerIn_normal_of_normalizer_top (Q := Q) (q := q) S hZNtop
  have hSnormal : (S : Subgroup Q).Normal := by
    simpa [hcenter_eq_sylow] using hZnormal
  exact hS_not_normal hSnormal

private theorem hkt_iv54_center_quotient_branch_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hZNtop :
      Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) = ⊤)
    (hcenter_ne_sylow :
      centerIn (G := Q) (S : Subgroup Q) ≠ (S : Subgroup Q)) :
    HasNormalPComplement q Q := by
  classical
  have hZnormal : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal :=
    hkt_iv54_centerIn_normal_of_normalizer_top (Q := Q) (q := q) S hZNtop
  letI : (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q).Normal := hZnormal
  by_cases hquot_comp :
      HasNormalPComplement q
        (Q ⧸ (centerIn (G := Q) (S : Subgroup Q) : Subgroup Q))
  · exact hkt_iv54_center_quotient_pnilpotent_lifts_complement
      (Q := Q) (q := q) S hproper hq_dvd hnot_burnside hpnormal
      hcenter_ne_sylow hquot_comp
  · have hSnormal : (S : Subgroup Q).Normal :=
      hkt_iv54_center_quotient_nonpnilpotent_forces_sylow_normal
        (Q := Q) (q := q) S hproper hq_dvd hnot_burnside hpnormal
        hcenter_ne_sylow hquot_comp
    exact False.elim (hS_not_normal hSnormal)

private theorem hkt_grun_second_center_normalizer_top_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hZNtop :
      Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) = ⊤) :
    HasNormalPComplement q Q := by
  classical
  by_cases hcenter_eq_sylow :
      centerIn (G := Q) (S : Subgroup Q) = (S : Subgroup Q)
  · exact False.elim
      (hkt_iv54_center_eq_sylow_top_contradiction
        (Q := Q) (q := q) S hS_not_normal hZNtop hcenter_eq_sylow)
  · exact hkt_iv54_center_quotient_branch_hasNormalPComplement
      (Q := Q) (q := q) hproper S hq_dvd hnot_burnside hS_not_normal
      hpnormal hZNtop hcenter_eq_sylow
/-- Grun's second theorem, in the exact normal-complement consequence needed in
Huppert IV.5.4(a): for a `q`-normal minimal non-`q`-nilpotent group, the
comparison with `N_Q(Z(S))` forces a normal `q`-complement in the ambient
group. This packages the proper `N_Q(Z(S))` case using Grun II and the
`N_Q(Z(S)) = Q` case using the quotient by `Z(S)`. -/
private theorem hkt_grun_second_hasNormalPComplement_of_pNormal_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (_hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (_hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (_hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))))
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)))
    (hS_not_normal : ¬ (S : Subgroup Q).Normal)
    (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    HasNormalPComplement q Q := by
  classical
  let ZN : Subgroup Q :=
    Subgroup.normalizer ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
  by_cases hZNtop : ZN = ⊤
  · exact hkt_grun_second_center_normalizer_top_hasNormalPComplement
      (Q := Q) (q := q) hproper S hq_dvd hnot_burnside hS_not_normal
      hpnormal (by simpa [ZN] using hZNtop)
  · have hS_le_ZN : (S : Subgroup Q) ≤ ZN := by
      simpa [ZN] using sylow_le_normalizer_centerIn (Q := Q) (q := q) S
    have hZN_ne_bot : ZN ≠ ⊥ := by
      intro hbot
      have hS_le_bot : (S : Subgroup Q) ≤ ⊥ := by
        simpa [hbot] using hS_le_ZN
      exact (Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd)
        (le_bot_iff.mp hS_le_bot)
    have hq_dvd_ZN : q ∣ Nat.card ZN :=
      (S.dvd_card_of_dvd_card hq_dvd).trans (Subgroup.card_dvd_of_le hS_le_ZN)
    have hZN_comp : HasNormalPComplement q ZN :=
      hproper ZN hZN_ne_bot hZNtop hq_dvd_ZN
    have hres_comp : HasNormalPComplement q (hktAbelianPResidual q Q) :=
      hktAbelianPResidual_hasNormalPComplement_of_center_normalizer_minimal
        (Q := Q) (q := q) hproper S hpnormal
        (by simpa [ZN] using hZN_comp) (by simpa [ZN] using hq_dvd_ZN)
    exact hkt_grun_second_hasNormalPComplement_of_center_normalizer
      (Q := Q) (q := q) S hpnormal (by simpa [ZN] using hZN_comp) hres_comp
/-- Huppert IV.5.4(a), proper-normalizer core for the Frobenius minimal
counterexample branch. If the Sylow normalizer were proper, the
minimal-counterexample hypothesis makes that normalizer `q`-nilpotent; the
Grun/IV.5.3 argument then forces a global normal `q`-complement, contradicting
`hnot`. The point of this statement is to keep the real source step as a
contradiction for the proper-normalizer branch, rather than pretending that the
local data directly proves the false-in-general focal-trivial statement. -/
private theorem hkt_false_of_proper_sylow_normalizer_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hnot : ¬ HasNormalPComplement q Q)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q)
    (hNproper : Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcomp_N :
      HasNormalPComplement q
        (Subgroup.normalizer ((S : Subgroup Q) : Set Q)))
    (hquot_N :
      IsPGroup q
        ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) ⧸
          ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup Q) : Set Q))))) :
    False := by
  classical
  let N : Subgroup Q := Subgroup.normalizer ((S : Subgroup Q) : Set Q)
  have hS_le_N : (S : Subgroup Q) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := (S : Subgroup Q)))
  let SN : Sylow q N := S.subtype hS_le_N
  have hSN_coe : (SN : Subgroup N) = (S : Subgroup Q).subgroupOf N := by
    simp [SN]
  have hSN_normal : (SN : Subgroup N).Normal := by
    have hsub_normal : ((S : Subgroup Q).subgroupOf N).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := (S : Subgroup Q)) (K := N) hS_le_N).2 (by
          intro n hn
          simpa [N] using hn)
    simpa [hSN_coe]
      using hsub_normal
  have hNproper' : N ≠ ⊤ := by
    simpa [N] using hNproper
  have hcomp_N' : HasNormalPComplement q N := by
    simpa [N] using hcomp_N
  have hquot_N' :
      IsPGroup q
        (N ⧸ ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf N)) := by
    simpa [N] using hquot_N
  have hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
    intro hburnside
    exact hnot (hkt_hasNormalPComplement_of_sylow_le_center_normalizer S hburnside)
  have hS_not_normal : ¬ (S : Subgroup Q).Normal := by
    intro hSnormal
    exact hNproper (Subgroup.normalizer_eq_top_iff.mpr hSnormal)
  -- Source route to formalize here:
  -- * non-`q`-normal branch: Huppert IV.5.3 gives a `q`-subgroup `A` and a
  --   `q'`-power element `x ∈ N_Q(A) \ C_Q(A)`; minimality forces
  --   `A ⊔ zpowers x = ⊤`, so `A` is the invariant Sylow subgroup.
  -- * `q`-normal branch: apply Grun's second theorem to `N_Q(Z(S))`; the
  --   proper case produces a normal `q`-complement in `Q`, and the top case
  --   descends to `Q ⧸ Z(S)` and lifts the complement back.
  -- The already assembled local data above (`hcomp_N`, `hquot_N`) is exactly
  -- the normalizer side of that source argument.
  by_cases hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)
  · exact hnot
      (hkt_grun_second_hasNormalPComplement_of_pNormal_minimal_non_pnilpotent
        (Q := Q) (q := q) hproper S hq_dvd hNproper hcomp_N hquot_N
        hnot_burnside hS_not_normal hpnormal)
  · exact hnot
      (hkt_huppert_iv53_hasNormalPComplement_of_not_pNormal_minimal_non_pnilpotent
        (Q := Q) (q := q) hproper S hq_dvd hNproper hcomp_N hquot_N
        hnot_burnside hS_not_normal hpnormal)

/-- p-length exit used at the end of Huppert IV.6.2: it is enough to show
that the subgroup generated by all `q`-elements is contained in
`O_{q',q}(Q)`. The already formalized BG1 p-length criterion then converts
the normal `q`-complement of `O_{q',q}(Q)` to `HasPLengthOne q Q`. -/
public theorem hkt_hasPLengthOne_of_pElementsSubgroup_le_Op_p'p
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hle : pElementsSubgroup q Q ≤ Op_p'p q Q) :
    HasPLengthOne q Q := by
  have hcompOp : HasNormalPComplement q (↥(Op_p'p q Q)) :=
    hasNormalPComplement_Op_p'p (G := Q) (p := q)
  have hcompElems : HasNormalPComplement q (↥(pElementsSubgroup q Q)) :=
    hasNormalPComplement_of_le (G := Q) (p := q) hle hcompOp
  exact (hasPLengthOne_iff_hasNormalPComplement_pElements (G := Q) (p := q)).2 hcompElems

/-- Huppert IV.5.4, isolated core for the Frobenius empty-bad-subgroup branch:
in a minimal non-`q`-nilpotent counterexample whose proper nontrivial
`q`-divisible subgroups are already `q`-nilpotent, a Sylow `q`-subgroup is
normal.  This is the exact source step still needed before the already proved
normal-Sylow endpoint can finish IV.5.8(b). -/
public theorem hkt_frobenius_normal_sylow_of_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hnot : ¬ HasNormalPComplement q Q)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q) :
    (S : Subgroup Q).Normal := by
  classical
  by_cases hNtop : Subgroup.normalizer ((S : Subgroup Q) : Set Q) = ⊤
  · exact Subgroup.normalizer_eq_top_iff.mp hNtop
  let N : Subgroup Q := Subgroup.normalizer ((S : Subgroup Q) : Set Q)
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hS_le_N : (S : Subgroup Q) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := (S : Subgroup Q)))
  have hN_ne_bot : N ≠ ⊥ := by
    intro hNbot
    exact hS_ne_bot (le_bot_iff.mp (by simpa [N, hNbot] using hS_le_N))
  have hq_dvd_N : q ∣ Nat.card N := by
    exact dvd_trans
      (S.dvd_card_of_dvd_card hq_dvd)
      (Subgroup.card_dvd_of_le hS_le_N)
  have hcomp_N : HasNormalPComplement q N :=
    hproper N hN_ne_bot (by simpa [N] using hNtop) hq_dvd_N
  have hquot_N :
      IsPGroup q
        (N ⧸ ((Subgroup.centralizer ((S : Subgroup Q) : Set Q)).subgroupOf N)) := by
    simpa [N] using
      hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
        (Q := Q) (q := q) (U := (S : Subgroup Q)) S.isPGroup' hcomp_N
  exact False.elim
    (hkt_false_of_proper_sylow_normalizer_minimal_non_pnilpotent
      (Q := Q) (q := q) hproper hnot S hq_dvd (by simpa [N] using hNtop)
      (by simpa [N] using hcomp_N)
      (by simpa [N] using hquot_N))

/-- Frobenius IV.5.8(b), in the exact form needed for the empty bad-subgroup
branch of Thompson IV.6.2.  If no nontrivial `q`-subgroup has a bad normalizer,
then every proper `q`-subgroup normalizer is `q`-nilpotent, so Frobenius'
normal-complement theorem gives a global normal `q`-complement. -/
public theorem huppertIV58_hasNormalPComplement_of_no_noncomplement_pSubgroups
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hbad_empty : ¬ ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup q U ∧ ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q)))) :
    HasNormalPComplement q Q := by
  classical
  induction hcard : Nat.card Q using Nat.strong_induction_on generalizing Q with
  | h n ih =>
      by_cases hq_dvd : q ∣ Nat.card Q
      · by_contra hnot
        let S : Sylow q Q := default
        have hproper :
            ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
              HasNormalPComplement q H := by
          intro H hH_ne_bot hH_ne_top _hqH
          have hbad_H : ¬ ∃ U : Subgroup H, U ≠ ⊥ ∧ IsPGroup q U ∧ ¬ HasNormalPComplement q (↥(Subgroup.normalizer (U : Set H))) := by
            intro hbadH
            rcases hbadH with ⟨U, hUbad⟩
            exact hUbad.2.2
              (hkt_iv54_intrinsic_normalizer_hasNormalPComplement_of_no_noncomplement_pSubgroups
                (Q := Q) (q := q) hbad_empty H hUbad.1 hUbad.2.1)
          have hH_lt_Q : Nat.card H < n := by
            rw [← hcard]
            simpa using natCard_lt_of_subgroup_lt (G := Q)
              (lt_top_iff_ne_top.mpr hH_ne_top)
          exact ih (Nat.card H) hH_lt_Q (Q := H) hbad_H rfl
        have hSnormal : (S : Subgroup Q).Normal :=
          hkt_frobenius_normal_sylow_of_minimal_non_pnilpotent
            (Q := Q) (q := q) hproper hnot S hq_dvd
        exact hnot
          (hkt_iv54_hasNormalPComplement_of_no_noncomplement_pSubgroups_of_normal_sylow
            (Q := Q) (q := q) hbad_empty S hq_dvd hSnormal)
      · exact hkt_hasNormalPComplement_of_not_dvd_card (Q := Q) (p := q) hq_dvd

/-- Huppert IV.5.4(a): in the minimal non-`q`-nilpotent setup, the Sylow
`q`-subgroup is normal. -/
public theorem huppert_IV_5_4_a_invariant_sylow_of_minimal_non_pnilpotent
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hnot : ¬ HasNormalPComplement q Q)
    (S : Sylow q Q) (hq_dvd : q ∣ Nat.card Q) :
    (S : Subgroup Q).Normal :=
  hkt_frobenius_normal_sylow_of_minimal_non_pnilpotent
    (Q := Q) (q := q) hproper hnot S hq_dvd

end External
end CFSG.BenderSuzuki
