module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5QuotBasic
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.RankThree.PartOne.CTP.StrongPQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Fourteen5

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem mem_star_iff {A : Subgroup G} {y : HStar H} :
    y ∈ star H A ↔ ∃ a : ↥H, (a : G) ∈ A ∧ QuotientGroup.mk' (core H) a = y := by
  constructor
  · rintro ⟨a, ha, hay⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, hay⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, hay⟩

theorem star_self : star H H = ⊤ := by
  unfold star
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem star_mono {A B : Subgroup G} (hAB : A ≤ B) : star H A ≤ star H B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)

theorem star_inf_left (A : Subgroup G) : star H (H ⊓ A) = star H A := by
  unfold star
  rw [Subgroup.inf_subgroupOf_left]

theorem star_sup {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    star H (A ⊔ B) = star H A ⊔ star H B := by
  unfold star
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem map_conj_star (A : Subgroup G) {h : G} (hh : h ∈ H) :
    (star H A).map (MulAut.conj (QuotientGroup.mk' (core H) ⟨h, hh⟩)).toMonoidHom =
      star H (A.map (MulAut.conj h).toMonoidHom) := by
  let hH : ↥H := ⟨h, hh⟩
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨a', ha'A, rfl⟩ := (mem_star_iff (A := A) (y := a)).mp ha
    refine (mem_star_iff (A := A.map (MulAut.conj h).toMonoidHom) (y := y)).mpr
      ⟨hH * a' * hH⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨(a' : G), ha'A, by simp [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, hH]⟩
    · rw [map_mul, map_mul, map_inv]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hay
  · intro hy
    obtain ⟨b, hbA, hby⟩ := (mem_star_iff (A := A.map (MulAut.conj h).toMonoidHom) (y := y)).mp hy
    rw [Subgroup.mem_map] at hbA
    obtain ⟨a, haA, hab⟩ := hbA
    rw [Subgroup.mem_map]
    refine ⟨(QuotientGroup.mk' (core H) hH)⁻¹ * y * QuotientGroup.mk' (core H) hH, ?_, ?_⟩
    · refine (mem_star_iff (A := A) (y := (QuotientGroup.mk' (core H) hH)⁻¹ * y *
        QuotientGroup.mk' (core H) hH)).mpr ⟨hH⁻¹ * b * hH, ?_, ?_⟩
      · have hcoe : ((hH⁻¹ * b * hH : ↥H) : G) = a := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hab
          rw [show ((hH⁻¹ * b * hH : ↥H) : G) = h⁻¹ * (b : G) * h by simp [hH],
            ← hab]
          group
        rw [hcoe]
        exact haA
      · rw [map_mul, map_mul, map_inv, hby]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hH]
      group

theorem star_le_centralizer {A B : Subgroup G} (h : A ≤ centralizer (B : Set G)) :
    star H A ≤ centralizer (star H B : Set (HStar H)) := by
  intro y hy
  obtain ⟨a, haA, rfl⟩ := (mem_star_iff (A := A) (y := y)).mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨b, hbB, rfl⟩ := (mem_star_iff (A := B) (y := z)).mp hz
  have hcomm : (b : G) * (a : G) = (a : G) * (b : G) :=
    (Subgroup.mem_centralizer_iff.mp (h haA)) (b : G) hbB
  have hcomm' : b * a = a * b := Subtype.ext hcomm
  show QuotientGroup.mk' (core H) b * QuotientGroup.mk' (core H) a =
    QuotientGroup.mk' (core H) a * QuotientGroup.mk' (core H) b
  rw [← map_mul, ← map_mul, hcomm']

theorem isCyclic_star {A : Subgroup G} (hA : IsCyclic ↥A) : IsCyclic ↥(star H A) := by
  haveI : IsCyclic ↥A := hA
  haveI hcyc : IsCyclic ↥(A.subgroupOf H) :=
    isCyclic_of_injective
      { toFun := fun x => (⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩ : A)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hxy)))
  have hrange : ((QuotientGroup.mk' (core H)).comp (A.subgroupOf H).subtype).range =
      star H A := by
    rw [MonoidHom.range_comp, Subgroup.subtype_range]
    rfl
  rw [← hrange]
  exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

section Coprime

variable {p : ℕ} [Fact p.Prime]

theorem card_star {A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup p A)
    (hp : ¬ p ∣ Nat.card (rankThreePrimeCore 3 H)) : Nat.card (star H A) = Nat.card A := by
  have hcore : Nat.card (core H) = Nat.card (rankThreePrimeCore 3 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rankThreePrimeCore_facts H).1).toEquiv
  have hp' : ¬ p ∣ Nat.card (core H) := fun h => hp (hcore ▸ h)
  have h := CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime
    (H := ↥H) (E := A.subgroupOf H) (N := core H) hA.comap_subtype hp'
  unfold star
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv

theorem normalizer_star_le {A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup p A)
    (hp : ¬ p ∣ Nat.card (rankThreePrimeCore 3 H)) :
    normalizer (star H A : Set (HStar H)) ≤ star H (normalizer (A : Set G)) := by
  have hcore : Nat.card (core H) = Nat.card (rankThreePrimeCore 3 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rankThreePrimeCore_facts H).1).toEquiv
  have hp' : ¬ p ∣ Nat.card (core H) := fun h => hp (hcore ▸ h)
  have h := normalizer_map_mk'_le_of_coprime (B := ↥H) (N := core H)
    (A := A.subgroupOf H) hA.comap_subtype hp'
  unfold star
  rw [Subgroup.subgroupOf_normalizer_eq hAH]
  exact h

theorem isSylowOf_star {A C : Subgroup G} (hCH : C ≤ H) (h : CFSG.ABGLocalTools.IsSylowOf p A C) :
    CFSG.ABGLocalTools.IsSylowOf p (star H A) (star H C) := by
  have hle : A ≤ H := h.le.trans hCH
  have hmap : CFSG.ABGLocalTools.IsSylowOf p ((A.subgroupOf H).map H.subtype)
      ((C.subgroupOf H).map H.subtype) := by
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hCH]
  have h' : CFSG.ABGLocalTools.IsSylowOf p (A.subgroupOf H) (C.subgroupOf H) :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).1 hmap
  unfold star
  exact isSylowOf_map_mk' h'

theorem isStronglyPEmbedded_star {M : Subgroup G} (hM : IsStronglyPEmbedded p M) (hHM : ¬ H ≤ M)
    (hp : p ∣ Nat.card ↥(H ⊓ M)) (hIM : rankThreePrimeCore 3 H ≤ M)
    (hpI : ¬ p ∣ Nat.card (rankThreePrimeCore 3 H)) : IsStronglyPEmbedded p (star H M) := by
  have hsub := hM.subgroupOf hHM hp
  rw [Subgroup.inf_subgroupOf_left] at hsub
  have hcore : Nat.card (core H) = Nat.card (rankThreePrimeCore 3 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rankThreePrimeCore_facts H).1).toEquiv
  have hp' : ¬ p ∣ Nat.card (core H) := fun h => hpI (hcore ▸ h)
  have hle : core H ≤ M.subgroupOf H := Subgroup.subgroupOf_mono H hIM
  have h := hsub.map_quotient (N := core H) hle hp'
  unfold star
  exact h

end Coprime

theorem normal_eq_bot_star {U : Subgroup (HStar H)} (hU : U.Normal) (h3 : ¬ 3 ∣ Nat.card U) :
    U = ⊥ := by
  have hcore : Nat.card (core H) = Nat.card (rankThreePrimeCore 3 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rankThreePrimeCore_facts H).1).toEquiv
  refine eq_bot_of_normal_of_not_dvd (B := ↥H) (N := core H) (p := 3) ?_ ?_ hU h3
  · intro U' hUn h3U
    have hmem : U'.map H.subtype ∈
        {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime 3 (Nat.card N)} := by
      refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
      · rw [← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
        exact hUn
      · rw [Subgroup.card_map_of_injective H.subtype_injective]
        exact (Nat.prime_three.coprime_iff_not_dvd).mpr h3U
    have hle : U'.map H.subtype ≤ rankThreePrimeCore 3 H := le_sSup hmem
    intro u hu
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem H.subtype hu))
  · rw [hcore]
    exact (rankThreePrimeCore_facts H).2.2

theorem isKGroup_star (hG : CFSG.Open.IsKProper G) (hH : H ≠ ⊤) :
    CFSG.Open.IsKGroup (HStar H) :=
  (hG.isKGroup H hH).quotient (core H)

theorem exists_isSylowOf_two_star {M : Subgroup G} (hodd : Odd (M.relIndex H)) :
    ∃ S : Subgroup (HStar H), CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ S ≤ star H M := by
  obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H ⊓ M)
  have hS₀HM : S₀ ≤ H ⊓ M := hS₀.le
  have hS₀H : CFSG.ABGLocalTools.IsSylowOf 2 S₀ H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS₀ ⊢
    obtain ⟨_, hP, hdvd⟩ := hS₀
    refine ⟨hS₀HM.trans inf_le_left, hP, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex (H := S₀) (K := H ⊓ M) (L := H) hS₀HM inf_le_left,
      Subgroup.inf_relIndex_left]
    intro h2
    rcases Nat.prime_two.dvd_mul.mp h2 with h | h
    · exact hdvd h
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  refine ⟨star H S₀, ?_, ?_⟩
  · rw [← star_self (H := H)]
    exact isSylowOf_star le_rfl hS₀H
  · exact (star_mono (H := H) hS₀HM).trans (star_mono (H := H) inf_le_right)

end Fourteen5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
