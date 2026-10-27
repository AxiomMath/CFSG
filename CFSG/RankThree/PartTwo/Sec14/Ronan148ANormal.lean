module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped Pointwise

section Group

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem false_of_le_centralizer_of_rank_two {J A B₀ E : Subgroup Γ} {e : Γ} (hB₀J : B₀ ≤ J)
    (he1 : e ≠ 1) (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set Γ))
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (A : Set Γ) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set Γ) ≤ Subgroup.zpowers e)
    (hEC : E ≤ Subgroup.centralizer (J : Set Γ)) (hEcard : Nat.card E = 9)
    (hE3 : ∀ y ∈ E, y ^ 3 = 1) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup Γ := Subgroup.centralizer (J : Set Γ) with hCdef
  have K1 : ∀ w : Γ, w ∈ C → w ^ 3 = 1 → w * e = e * w → w ∈ Subgroup.zpowers e := by
    intro w hwC hw3 hwe
    have hcen : A ≤ Subgroup.centralizer ({w} : Set Γ) := by
      rw [hA]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hwe
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hwC b (hB₀J hb)).symm
    have hwA : w ∈ Subgroup.centralizer (A : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hcen ha) w (Set.mem_singleton w)).symm
    exact hAJ (Subgroup.mem_inf.mpr ⟨hF3 w hwA hw3, hwC⟩)
  set E' : Subgroup C := E.subgroupOf C with hE'def
  have hE'3 : IsPGroup 3 E' := by
    intro y
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE3 _ (Subgroup.mem_subgroupOf.mp y.2)
  set e' : C := ⟨e, heJ⟩ with he'def
  have he'3 : e' ^ 3 = 1 := Subtype.ext (by simpa [he'def] using he3)
  obtain ⟨P, hP⟩ := (Res2LBal.isPGroup_zpowers he'3).exists_le_sylow
  have he'P : e' ∈ (P : Subgroup C) := hP (Subgroup.mem_zpowers e')
  haveI : Finite (Sylow 3 C) := Finite.of_injective
    (fun Q : Sylow 3 C => ((Q : Subgroup C) : Set C)) (by
      intro Q R h
      exact Sylow.ext (SetLike.coe_injective h))
  have FA : ∀ w : C, w ∈ (P : Subgroup C) → (w : Γ) ^ 3 = 1 →
      (w : Γ) ∈ Subgroup.zpowers e := by
    intro w hwP hw3
    have hP3 : IsPGroup 3 (P : Subgroup C) := P.isPGroup'
    haveI hnt : Nontrivial (P : Subgroup C) := ⟨⟨⟨e', he'P⟩, 1, fun h =>
      he1 (congrArg (fun t : (P : Subgroup C) => ((t : C) : Γ)) h)⟩⟩
    haveI hZ : Nontrivial (Subgroup.center (P : Subgroup C)) := IsPGroup.center_nontrivial hP3
    have hZ3 : IsPGroup 3 (Subgroup.center (P : Subgroup C)) := hP3.to_subgroup _
    have h3Z : 3 ∣ Nat.card (Subgroup.center (P : Subgroup C)) := by
      obtain ⟨n, hn, hcard⟩ := hZ3.nontrivial_iff_card.mp inferInstance
      rw [hcard]
      exact dvd_pow_self 3 hn.ne'
    obtain ⟨z0, hz0⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (P : Subgroup C))) 3 h3Z
    have hz03 : z0 ^ 3 = 1 := by
      have h := pow_orderOf_eq_one z0
      rwa [hz0] at h
    have hz0ne : z0 ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz0
      norm_num at hz0
    obtain ⟨z, hzcen, hz3, hz1⟩ : ∃ z : (P : Subgroup C),
        (∀ g : (P : Subgroup C), g * z = z * g) ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
      refine ⟨z0.1, fun g => Subgroup.mem_center_iff.mp z0.2 g, ?_, ?_⟩
      · have h := congrArg Subtype.val hz03
        simpa using h
      · intro h
        exact hz0ne (Subtype.ext h)
    have hzΓ3 : ((z : C) : Γ) ^ 3 = 1 := by
      have h := congrArg (fun t : (P : Subgroup C) => ((t : C) : Γ)) hz3
      simpa using h
    have hzΓ1 : ((z : C) : Γ) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    have hzC : ((z : C) : Γ) ∈ C := (z : C).2
    have hcomm : ((z : C) : Γ) * e = e * ((z : C) : Γ) := by
      have h := congrArg (fun t : (P : Subgroup C) => ((t : C) : Γ)) (hzcen ⟨e', he'P⟩)
      simp only [Subgroup.coe_mul] at h
      exact h.symm
    have hK1 : ((z : C) : Γ) ∈ Subgroup.zpowers e := K1 _ hzC hzΓ3 hcomm
    have hle : Subgroup.zpowers ((z : C) : Γ) ≤ Subgroup.zpowers e :=
      Subgroup.zpowers_le.mpr hK1
    have hordz : orderOf ((z : C) : Γ) = 3 := orderOf_eq_prime hzΓ3 hzΓ1
    have heq : Subgroup.zpowers ((z : C) : Γ) = Subgroup.zpowers e := by
      refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
      rw [Nat.card_zpowers, Nat.card_zpowers, hordz, orderOf_eq_prime he3 he1]
    have he_mem : e ∈ Subgroup.zpowers ((z : C) : Γ) := by
      rw [heq]
      exact Subgroup.mem_zpowers e
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he_mem
    have hcentral : ∀ w : C, w ∈ (P : Subgroup C) → Commute (w : Γ) e := by
      intro w hwP
      have h := congrArg (fun t : (P : Subgroup C) => ((t : C) : Γ)) (hzcen ⟨w, hwP⟩)
      simp only [Subgroup.coe_mul] at h
      have hc : Commute (w : Γ) ((z : C) : Γ) := h
      have hc' := hc.zpow_right k
      rw [hk] at hc'
      exact hc'
    exact K1 (w : Γ) w.2 hw3 (hcentral w hwP)
  obtain ⟨R, hR⟩ := hE'3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥C) R P
  have hsub : MulAut.conj g • (R : Subgroup C) = (P : Subgroup C) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hconj : ∀ y ∈ E', MulAut.conj g y ∈ (P : Subgroup C) := by
    intro y hy
    rw [← hsub]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (R : Subgroup C) (hR hy)
  obtain ⟨f, hf⟩ : ∃ f : Γ, f = (g : Γ)⁻¹ * e * (g : Γ) := ⟨_, rfl⟩
  have hfk : ∀ k : ℤ, f ^ k = (g : Γ)⁻¹ * e ^ k * (g : Γ) := by
    intro k
    have h := conj_zpow (i := k) (a := (g : Γ)⁻¹) (b := e)
    rw [inv_inv] at h
    rw [hf]
    exact h
  have hf3 : f ^ 3 = 1 := by
    have h := conj_pow (i := 3) (a := (g : Γ)⁻¹) (b := e)
    rw [inv_inv, he3] at h
    rw [hf, h]
    simp
  have hf1 : f ≠ 1 := by
    intro h
    apply he1
    have h' : e = (g : Γ) * f * (g : Γ)⁻¹ := by
      rw [hf]
      group
    rw [h', h, mul_one, mul_inv_cancel]
  have hEf : E ≤ Subgroup.zpowers f := by
    intro y hy
    have hyC : y ∈ C := hEC hy
    have hy' : (⟨y, hyC⟩ : C) ∈ E' := Subgroup.mem_subgroupOf.mpr hy
    have hw := hconj _ hy'
    have hw3 : (((MulAut.conj g) (⟨y, hyC⟩ : C) : C) : Γ) ^ 3 = 1 := by
      show ((g : Γ) * y * (g : Γ)⁻¹) ^ 3 = 1
      rw [conj_pow, hE3 y hy]
      simp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (FA _ hw hw3)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [hfk k, hk]
    show (g : Γ)⁻¹ * ((g : Γ) * y * (g : Γ)⁻¹) * (g : Γ) = y
    group
  have hcard := Subgroup.card_le_of_le hEf
  rw [Nat.card_zpowers, orderOf_eq_prime hf3 hf1, hEcard] at hcard
  norm_num at hcard

theorem map_conj_eq_of_rank_two {J A B₀ : Subgroup Γ} {e : Γ} (hJ : IsComponent J)
    (hB₀J : B₀ ≤ J) (hB₀9 : Nat.card B₀ = 9) (hB₀3 : ∀ b ∈ B₀, b ^ 3 = 1)
    (he1 : e ≠ 1) (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set Γ))
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (A : Set Γ) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set Γ) ≤ Subgroup.zpowers e) (x : Γ) :
    J.map (MulAut.conj x).toMonoidHom = J := by
  by_contra hne
  set J' : Subgroup Γ := J.map (MulAut.conj x).toMonoidHom with hJ'def
  have hJ' : IsComponent J' := Res2LBal.isComponent_conj hJ x
  have hJ'C : J' ≤ Subgroup.centralizer (J : Set Γ) := fun y hy =>
    Res2LBal.mem_centralizer_of_mem_of_ne hJ hJ' (fun h => hne h.symm) hy
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  refine false_of_le_centralizer_of_rank_two hB₀J he1 he3 heJ hA hF3 hAJ
    ((Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hB₀J).trans hJ'C) ?_ ?_
  · rw [Subgroup.card_map_of_injective hinj]
    exact hB₀9
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, hB₀3 b hb, map_one]

end Group

variable {G : Type} [Group G] [Finite G]

theorem map_normal_of_img148_eq {A Y X J : Subgroup G} [(ker148 A Y).Normal] (hXY : X ≤ Y)
    (hXJ : img148 A Y X = img148 A Y J)
    (hN : ∀ (y : G) (hy : y ∈ Y),
      QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) ∈
        Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal := by
  rw [map_mk_normal_iff hXY]
  have hOY : pPrimeCoreOf 3 Y ≤ Y := pPrimeCoreOf_le 3 Y
  have hXN : X ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hXY.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hkey : ∀ u : ↥(Y ⊔ A),
      (QuotientGroup.mk' (ker148 A Y) u ∈ img148 A Y X ↔
        (u : G) ∈ X ⊔ pPrimeCoreOf 3 Y) := by
    intro u
    constructor
    · intro hmem
      obtain ⟨g, hg, hgX, hgu⟩ := mem_img148_iff.mp hmem
      have h1 : (g : G)⁻¹ * (u : G) ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_iff.mp hgu
      have h3 : g * ((g : G)⁻¹ * (u : G)) ∈ X ⊔ pPrimeCoreOf 3 Y :=
        mul_mem (Subgroup.mem_sup_left hgX) (Subgroup.mem_sup_right h1)
      simpa using h3
    · intro hu'
      have hmul : (u : G) ∈ (pPrimeCoreOf 3 Y : Set G) * (X : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hXN, SetLike.mem_coe, sup_comm]
        exact hu'
      obtain ⟨o, ho, x, hx, hox⟩ := Set.mem_mul.mp hmul
      have hoM : o ∈ Y ⊔ A := Subgroup.mem_sup_left (hOY ho)
      have hxM : x ∈ Y ⊔ A := Subgroup.mem_sup_left (hXY hx)
      have hu_eq : u = (⟨o, hoM⟩ : ↥(Y ⊔ A)) * ⟨x, hxM⟩ := Subtype.ext hox.symm
      have hop : QuotientGroup.mk' (ker148 A Y) (⟨o, hoM⟩ : ↥(Y ⊔ A)) = 1 :=
        mk'_ker148_eq_one_iff.mpr ho
      rw [hu_eq, map_mul, hop, one_mul]
      exact mem_img148_iff.mpr ⟨x, hxM, hx, rfl⟩
  have hfwd : ∀ y ∈ Y, ∀ h ∈ X ⊔ pPrimeCoreOf 3 Y, y * h * y⁻¹ ∈ X ⊔ pPrimeCoreOf 3 Y := by
    intro y hy h hh
    have hhY : h ∈ Y := sup_le hXY hOY hh
    have hw : QuotientGroup.mk' (ker148 A Y) (⟨h, Subgroup.mem_sup_left hhY⟩ : ↥(Y ⊔ A)) ∈
        img148 A Y J := by
      rw [← hXJ]
      exact (hkey ⟨h, Subgroup.mem_sup_left hhY⟩).mpr hh
    have hc := (Subgroup.mem_normalizer_iff.mp (hN y hy)
      (QuotientGroup.mk' (ker148 A Y) (⟨h, Subgroup.mem_sup_left hhY⟩ : ↥(Y ⊔ A)))).mp hw
    rw [← hXJ] at hc
    have hmul : QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) *
        QuotientGroup.mk' (ker148 A Y) (⟨h, Subgroup.mem_sup_left hhY⟩ : ↥(Y ⊔ A)) *
        (QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))⁻¹ =
        QuotientGroup.mk' (ker148 A Y)
          ((⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) * ⟨h, Subgroup.mem_sup_left hhY⟩ *
            (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A))⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hmul] at hc
    exact (hkey ((⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) * ⟨h, Subgroup.mem_sup_left hhY⟩ *
      (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A))⁻¹)).mp hc
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hfwd y hy h
  · intro hh
    have := hfwd y⁻¹ (Y.inv_mem hy) (y * h * y⁻¹) hh
    simpa [mul_assoc] using this

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
