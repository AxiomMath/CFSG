module

public import CFSG.Quasithin.H13.KGFactE623Blk
public import CFSG.Quasithin.H13.KGFact68Base
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut

public section

namespace CFSG.Quasithin.H13.KGE623

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Id2519

@[expose] def Sp44OrderThreeCent : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
    ∀ y : StatedProj (StatedSp 2 F), y ^ 3 = 1 → y ≠ 1 →
    ∀ E : Subgroup (StatedProj (StatedSp 2 F)), CFSG.Open.IsElemAbelian 2 E →
      E ≤ Subgroup.centralizer {y} → Nat.card E ≤ 4

theorem false_of_sp44_block (hSp : Sp44OrderThreeCent) {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} {u : Y} (hu : u ∈ Subgroup.normalizer (X : Set Y)) (hu2 : u ^ 2 = 1)
    (huC : u ∉ Subgroup.centralizer (X : Set Y)) (h : StatedClassicalModel X .PSp 2 2 2)
    {B : Subgroup Y} (hS : IsShort2 B) (hA : IsAltType B 5) (hBX : B ≤ X)
    (hBu : B ≤ Subgroup.centralizer ({u} : Set Y)) : False := by
  classical
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := h
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
  set c : MulAut X := KG68.conjOn X u hu with hc
  set τ : MulAut (StatedProj (StatedSp 2 F)) := (φ.symm.trans c).trans φ with hτdef
  have hτ : ∀ x : X, τ (φ x) = φ (c x) := fun x => by
    show φ (c (φ.symm (φ x))) = φ (c x)
    rw [MulEquiv.symm_apply_apply]
  have hcB : ∀ b (hb : b ∈ B), c ⟨b, hBX hb⟩ = ⟨b, hBX hb⟩ := by
    intro b hb
    apply Subtype.ext
    rw [hc, KG68.conjOn_coe]
    have h1 : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.mp (hBu hb)
    calc u * b * u⁻¹ = b * u * u⁻¹ := by rw [h1]
      _ = b := by group
  have hτB : ∀ b (hb : b ∈ B), τ (φ ⟨b, hBX hb⟩) = φ ⟨b, hBX hb⟩ := fun b hb => by
    rw [hτ, hcB b hb]
  have hττ : τ * τ = 1 := by
    refine MulEquiv.ext fun p => ?_
    obtain ⟨x, rfl⟩ := φ.surjective p
    rw [MulAut.mul_apply, hτ, hτ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hc, KG68.conjOn_coe, KG68.conjOn_coe]
    have hu1 : u * u = 1 := by rw [← sq]; exact hu2
    calc u * (u * (x : Y) * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ := by group
      _ = x := by rw [hu1]; group
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply huC
    rw [← KG68.conjOn_eq_one_iff X hu]
    refine MulEquiv.ext fun x => ?_
    have h2 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) => α (φ x)) h1
    simp only [MulAut.one_apply] at h2
    rw [hτ] at h2
    exact φ.injective h2
  by_cases hin : τ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))
  ·
    obtain ⟨s, hs⟩ := hin
    have hsB : ∀ b (hb : b ∈ B), s * φ ⟨b, hBX hb⟩ = φ ⟨b, hBX hb⟩ * s := by
      intro b hb
      have h1 := hτB b hb
      rw [← hs, MulAut.conj_apply] at h1
      calc s * φ ⟨b, hBX hb⟩ = (s * φ ⟨b, hBX hb⟩ * s⁻¹) * s := by group
        _ = φ ⟨b, hBX hb⟩ * s := by rw [h1]
    have hs2 : s ^ 2 = 1 := by
      refine USp4.eq_one_of_central fun q => ?_
      have h1 : MulAut.conj (s ^ 2) = 1 := by rw [map_pow, hs, sq, hττ]
      have h2 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) => α q) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc s ^ 2 * q = (s ^ 2 * q * (s ^ 2)⁻¹) * s ^ 2 := by group
        _ = q * s ^ 2 := by rw [h2]
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply hτ1
      rw [← hs, map_one]
    obtain ⟨x, hx, hx3, hxC, w₁, hw₁, w₂, hw₂, hxw₁, hxw₂, hw₁C, hw₂C, hw₁₂C⟩ :=
      exists_elements hS hA
    have hw₁B : w₁ ∈ B := C1.blockQ_le B (C1.blockU_le_blockQ hS hw₁)
    have hw₂B : w₂ ∈ B := C1.blockQ_le B (C1.blockU_le_blockQ hS hw₂)
    have hw₁₂B : w₁ * w₂ ∈ B := mul_mem hw₁B hw₂B
    set y := φ ⟨x, hBX hx⟩ with hy
    set p := φ ⟨w₁, hBX hw₁B⟩ with hp
    set q := φ ⟨w₂, hBX hw₂B⟩ with hq
    have hpq : p * q = φ ⟨w₁ * w₂, hBX hw₁₂B⟩ := by rw [hp, hq, ← map_mul]; rfl
    have hnc : ∀ w (hw : w ∈ B), w ∉ Subgroup.centralizer (B : Set Y) →
        ∃ b, ∃ hb : b ∈ B, φ ⟨w, hBX hw⟩ * φ ⟨b, hBX hb⟩ ≠ φ ⟨b, hBX hb⟩ * φ ⟨w, hBX hw⟩ := by
      intro w hw hwC
      by_contra hcon
      apply hwC
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : φ ⟨w, hBX hw⟩ * φ ⟨b, hBX hb⟩ = φ ⟨b, hBX hb⟩ * φ ⟨w, hBX hw⟩ := by
        by_contra hne
        exact hcon ⟨b, hb, hne⟩
      rw [← map_mul, ← map_mul] at h1
      exact (congrArg Subtype.val (φ.injective h1)).symm
    have hne1 : ∀ w (hw : w ∈ B), w ∉ Subgroup.centralizer (B : Set Y) → φ ⟨w, hBX hw⟩ ≠ 1 := by
      intro w hw hwC h1
      obtain ⟨b, hb, hne⟩ := hnc w hw hwC
      apply hne
      rw [h1, one_mul, mul_one]
    have hnes : ∀ w (hw : w ∈ B), w ∉ Subgroup.centralizer (B : Set Y) → s ≠ φ ⟨w, hBX hw⟩ := by
      intro w hw hwC h1
      obtain ⟨b, hb, hne⟩ := hnc w hw hwC
      apply hne
      rw [← h1]
      exact hsB b hb
    have hp1 : p ≠ 1 := hne1 w₁ hw₁B hw₁C
    have hq1 : q ≠ 1 := hne1 w₂ hw₂B hw₂C
    have hpq1 : p * q ≠ 1 := by rw [hpq]; exact hne1 _ hw₁₂B hw₁₂C
    have hsp : s ≠ p := hnes w₁ hw₁B hw₁C
    have hsq : s ≠ q := hnes w₂ hw₂B hw₂C
    have hspq : s ≠ p * q := by rw [hpq]; exact hnes _ hw₁₂B hw₁₂C
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← map_pow]
      have : (⟨x, hBX hx⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hy1 : y ≠ 1 := by
      intro h1
      apply hxC
      have hx1 : x = 1 := by
        have h2 : (⟨x, hBX hx⟩ : X) = 1 := φ.injective (by rw [map_one]; exact h1)
        exact congrArg Subtype.val h2
      rw [hx1]
      exact one_mem _
    have hp2 : p ^ 2 = 1 := by
      rw [hp, ← map_pow]
      have : (⟨w₁, hBX hw₁B⟩ : X) ^ 2 = 1 :=
        Subtype.ext (by simpa using C1.blockU_sq hS w₁ hw₁)
      rw [this, map_one]
    have hq2 : q ^ 2 = 1 := by
      rw [hq, ← map_pow]
      have : (⟨w₂, hBX hw₂B⟩ : X) ^ 2 = 1 :=
        Subtype.ext (by simpa using C1.blockU_sq hS w₂ hw₂)
      rw [this, map_one]
    have hpqc : p * q = q * p := by
      rw [hp, hq, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (C1.blockU_comm hS w₁ hw₁ w₂ (C1.blockU_le_blockQ hS hw₂))
    have hyp : y * p = p * y := by
      rw [hy, hp, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxw₁
    have hyq : y * q = q * y := by
      rw [hy, hq, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxw₂
    have hsp' : s * p = p * s := hsB w₁ hw₁B
    have hsq' : s * q = q * s := hsB w₂ hw₂B
    have hsy : s * y = y * s := hsB x hx
    set E := Subgroup.closure ({s, p, q} : Set (StatedProj (StatedSp 2 F))) with hE
    have hgen : ∀ a ∈ ({s, p, q} : Set (StatedProj (StatedSp 2 F))),
        ∀ b ∈ ({s, p, q} : Set (StatedProj (StatedSp 2 F))), a * b = b * a := by
      intro a ha b hb
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
      all_goals first
        | rfl
        | exact hsp' | exact hsp'.symm | exact hsq' | exact hsq'.symm
        | exact hpqc | exact hpqc.symm
    have hEcomm : IsMulCommutative E :=
      Subgroup.isMulCommutative_closure fun a ha b hb _ => hgen a ha b hb
    have hEsq : ∀ e ∈ E, e ^ 2 = 1 := by
      intro e he
      induction he using Subgroup.closure_induction with
      | mem a ha =>
        rcases ha with ha | ha | ha <;> rw [ha]
        · exact hs2
        · exact hp2
        · exact hq2
      | one => exact one_pow 2
      | mul a b ha hb iha ihb =>
        have hab : a * b = b * a :=
          congrArg Subtype.val (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
              rw [sq, sq, sq, mul_assoc, ← mul_assoc b a b, ← hab, mul_assoc, mul_assoc]
          _ = 1 := by rw [iha, ihb, one_mul]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    have hEab : CFSG.Open.IsElemAbelian 2 E := ⟨hEcomm, hEsq⟩
    have hEC : E ≤ Subgroup.centralizer {y} := by
      rw [hE, Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases ha with ha | ha | ha <;> rw [ha]
      · exact hsy
      · exact hyp.symm
      · exact hyq.symm
    have hsub : (({1, s, p, q, p * q} : Finset (StatedProj (StatedSp 2 F))) :
        Set (StatedProj (StatedSp 2 F))) ⊆ (E : Set (StatedProj (StatedSp 2 F))) := by
      intro z hz
      have hsE : s ∈ E := Subgroup.subset_closure (by simp)
      have hpE : p ∈ E := Subgroup.subset_closure (by simp)
      have hqE : q ∈ E := Subgroup.subset_closure (by simp)
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz | hz <;> rw [hz]
      · exact one_mem E
      · exact hsE
      · exact hpE
      · exact hqE
      · exact mul_mem hpE hqE
    have n1 : (1 : StatedProj (StatedSp 2 F)) ∉
        ({s, p, q, p * q} : Finset (StatedProj (StatedSp 2 F))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hs1.symm, hp1.symm, hq1.symm, hpq1.symm⟩
    have n2 : s ∉ ({p, q, p * q} : Finset (StatedProj (StatedSp 2 F))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hsp, hsq, hspq⟩
    have n3 : p ∉ ({q, p * q} : Finset (StatedProj (StatedSp 2 F))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h1 => hpq1 ?_, fun h1 => hq1 ?_⟩
      · rw [← h1, ← sq, hp2]
      · calc q = p⁻¹ * (p * q) := by group
          _ = 1 := by rw [← h1, inv_mul_cancel]
    have n4 : q ∉ ({p * q} : Finset (StatedProj (StatedSp 2 F))) := by
      rw [Finset.mem_singleton]
      intro h1
      apply hp1
      calc p = (p * q) * q⁻¹ := by group
        _ = 1 := by rw [← h1, mul_inv_cancel]
    have hfin : ({1, s, p, q, p * q} : Finset (StatedProj (StatedSp 2 F))).card = 5 := by
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_singleton]
    have h5 : 5 ≤ Nat.card E := by
      calc 5 = ((({1, s, p, q, p * q} : Finset (StatedProj (StatedSp 2 F))) :
            Set (StatedProj (StatedSp 2 F)))).ncard := by rw [Set.ncard_coe_finset, hfin]
        _ ≤ (E : Set (StatedProj (StatedSp 2 F))).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card E := (Nat.card_coe_set_eq (E : Set (StatedProj (StatedSp 2 F)))).symm
    have h4 := hSp F hF4 y hy3 hy1 E hEab hEC
    omega
  ·
    obtain ⟨hinv, -, -⟩ := USp4.aut_facts hF4
    have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
    obtain ⟨σ, g, hσ1, hσσ, hτg⟩ := USp4.exists_conj_fieldAut hF4 hττ hin (hinv τ hord)
    set cg := spInner 2 F g with hcg
    have hf : fieldAut 2 F σ = cg⁻¹ * τ * cg := by rw [hτg]; group
    have hfix : ∀ b (hb : b ∈ B), fieldAut 2 F σ (cg⁻¹ (φ ⟨b, hBX hb⟩)) = cg⁻¹ (φ ⟨b, hBX hb⟩) := by
      intro b hb
      rw [hf, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hτB b hb]
    have hle : Nat.card B ≤ 720 := by
      rw [← USp4.card_fixedSub_fieldAut hF4 hσ1 hσσ]
      refine Nat.card_le_card_of_injective (fun b : B =>
        (⟨cg⁻¹ (φ ⟨b, hBX b.2⟩), USp4.mem_fixedSub.mpr (hfix b b.2)⟩ :
          USp4.fixedSub (fieldAut 2 F σ))) ?_
      intro b b' hbb'
      have h1 := congrArg Subtype.val hbb'
      have h2 := φ.injective ((cg⁻¹).injective h1)
      have h3 := congrArg (fun z : X => (z : Y)) h2
      exact Subtype.ext h3
    have := card_ge hS hA
    omega

end CFSG.Quasithin.H13.KGE623
