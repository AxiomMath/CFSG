module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQCore
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

theorem lemmaQ_of (hKF1 : FF84KF1) (hKS : FF84KSOut) : LemmaQ := by
  unfold LemmaQ
  intro G _ _ H P A B' K hX hP hP9 hAP hBP hA3 hB3 hAB hKC hKn hK60 hKs hAK hiii
  have hPH : P ≤ H := hP.1
  have hAH : A ≤ H := hAP.trans hPH
  have hBH : B' ≤ H := hBP.trans hPH
  have hKH : K ≤ H := hKC.trans inf_le_left
  have hcardS : ∀ S : Subgroup G, S ≤ H → Nat.card (S.subgroupOf H) = Nat.card S :=
    fun S hS => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have hP9' : Nat.card (P.subgroupOf H) = 9 := (hcardS P hPH).trans hP9
  have hP' : IsSylowOf 3 (P.subgroupOf H) ⊤ := by
    unfold IsSylowOf
    refine ⟨le_top, (IsPGroup.iff_card).2 ⟨2, by simp [hP9']⟩, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hP.2.2
  have hAP' : A.subgroupOf H ≤ P.subgroupOf H :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hAP (Subgroup.mem_subgroupOf.1 hx))
  have hBP' : B'.subgroupOf H ≤ P.subgroupOf H :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hBP (Subgroup.mem_subgroupOf.1 hx))
  have hA' : Nat.card (A.subgroupOf H) = 3 := (hcardS A hAH).trans hA3
  have hB'' : Nat.card (B'.subgroupOf H) = 3 := (hcardS B' hBH).trans hB3
  have hAB' : A.subgroupOf H ⊓ B'.subgroupOf H = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (x : G) ∈ A ⊓ B' :=
      ⟨Subgroup.mem_subgroupOf.1 hx.1, Subgroup.mem_subgroupOf.1 hx.2⟩
    rw [hAB, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hAK' : A.subgroupOf H ≤ K.subgroupOf H :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hAK (Subgroup.mem_subgroupOf.1 hx))
  have hK' : Nat.card (K.subgroupOf H) = 60 := (hcardS K hKH).trans hK60
  have hKs' : IsSimpleGroup (K.subgroupOf H) :=
    (Subgroup.subgroupOfEquivOfLe hKH).isSimpleGroup
  have hKC' : K.subgroupOf H ≤ CenS (B'.subgroupOf H) := by
    intro y hy
    have hyC : (y : G) ∈ CenS B' := (hKC (Subgroup.mem_subgroupOf.1 hy)).2
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbB : (b : G) ∈ B' := Subgroup.mem_subgroupOf.1 hb
    have hc : (b : G) * (y : G) = (y : G) * (b : G) := Subgroup.mem_centralizer_iff.1 hyC (b : G) hbB
    exact Subtype.ext hc
  have hKn' : ((K.subgroupOf H).subgroupOf (CenS (B'.subgroupOf H))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKC']
    intro h k hh hk
    have hkC : (k : G) ∈ CenS B' := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have e := congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.1 hk ⟨b, hBH hb⟩ (Subgroup.mem_subgroupOf.2 hb))
      simpa using e
    have hconj := (Subgroup.normal_subgroupOf_iff hKC).1 hKn (h : G) (k : G)
      (Subgroup.mem_subgroupOf.1 hh) ⟨k.2, hkC⟩
    apply Subgroup.mem_subgroupOf.2
    simpa using hconj
  have hiii' : ¬ ∃ g : H, conjBy g (A.subgroupOf H) = B'.subgroupOf H := by
    rintro ⟨g, hg⟩
    apply hiii
    refine ⟨(g : G), g.2, ?_⟩
    have key : ∀ y : H, y ∈ conjBy g (A.subgroupOf H) ↔ (y : G) ∈ conjBy (g : G) A := by
      intro y
      rw [mem_conjBy_iff, mem_conjBy_iff, Subgroup.mem_subgroupOf]
      simp
    ext x
    constructor
    · intro hx
      have hxH : x ∈ H := by
        have h1 : (g : G)⁻¹ * x * (g : G) ∈ A := (mem_conjBy_iff _ _ _).1 hx
        have e : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
        rw [e]
        exact H.mul_mem (H.mul_mem g.2 (hAH h1)) (H.inv_mem g.2)
      have hy : (⟨x, hxH⟩ : H) ∈ conjBy g (A.subgroupOf H) := (key ⟨x, hxH⟩).2 hx
      rw [hg] at hy
      exact Subgroup.mem_subgroupOf.1 hy
    · intro hx
      have hy : (⟨x, hBH hx⟩ : H) ∈ B'.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
      rw [← hg] at hy
      exact (key ⟨x, hBH hx⟩).1 hy
  have hcore := lemmaQ_core hKF1 hKS hX (P.subgroupOf H) (A.subgroupOf H) (B'.subgroupOf H)
    (K.subgroupOf H) hP' hP9' hAP' hBP' hA' hB'' hAB' hKC' hKn' hK' hKs' hAK' hiii'
  have hmap : (K.subgroupOf H ⊔ pPrimeCore 3 H).map H.subtype = K ⊔ Opp 3 H := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH]
    rfl
  have hN : ∀ N : Subgroup H, (N.map H.subtype).subgroupOf H = N := by
    intro N
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hyeq : y = x := Subtype.ext hyx
      rw [← hyeq]
      exact hy
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_subtype_le _
  · rw [← hmap, hN]
    exact hcore

end CFSG.RankThree.PartTwo.Sec21.FF84
