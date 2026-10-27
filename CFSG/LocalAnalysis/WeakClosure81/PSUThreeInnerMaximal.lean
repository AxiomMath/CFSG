module

public import CFSG.ClassicalGroups.Unitary.NonsingularLineMaximal
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {p f : ℕ} {K : Type} [Field K]

theorem isCoatom_centralizer_psu3_of_equiv {L : Type} [Group L]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K))
    {z : L} (hz : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set L)) := by
  have hz' : orderOf (e z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz
  have hbase : IsCoatom (Subgroup.centralizer ({e z} :
      Set (StatedProj (StatedSU 3 (p ^ f) K)))) :=
    CFSG.ClassicalGroups.Unitary.isCoatom_centralizer_statedProj_of_orderOf h hp2 hz'
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isCoatom_centralizer_of_equiv e z hbase

theorem isCoatom_centralizer_of_almostSimple
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hAS : CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple L)
    (hconj : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ L, g * x * g⁻¹ = y)
    (hmax : ∀ x : ↥L, orderOf x = 2 →
      IsCoatom (Subgroup.centralizer ({x} : Set ↥L)))
    {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set Q)) := by
  classical
  let C : Subgroup Q := Subgroup.centralizer ({z} : Set Q)
  have hCproper : C ≠ ⊤ := by
    intro htop
    have hzC : z ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlC : l ∈ C := by rw [htop]; exact Subgroup.mem_top l
      exact Subgroup.mem_centralizer_singleton_iff.mp hlC
    have hzbot : z ∈ (⊥ : Subgroup Q) := by
      rw [hAS.centralizer_eq] at hzC
      exact hzC
    have hz1 : z = 1 := by simpa using hzbot
    have hz2' : orderOf (1 : Q) = 2 := by rwa [hz1] at hz2
    simp at hz2'
  have hzsq : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hdecomp : ∀ q : Q, ∃ l ∈ L, ∃ c ∈ C, q = l * c := by
    intro q
    have hqzL : q * z * q⁻¹ ∈ L := hAS.normal.conj_mem z hzL q
    have hqz2 : orderOf (q * z * q⁻¹) = 2 := by
      have hsq : (q * z * q⁻¹) * (q * z * q⁻¹) = 1 := by
        calc (q * z * q⁻¹) * (q * z * q⁻¹) = q * (z * z) * q⁻¹ := by group
          _ = 1 := by rw [hzsq]; group
      have hne1 : q * z * q⁻¹ ≠ 1 := by
        intro h1
        have hz1 : z = 1 := by
          calc z = q⁻¹ * (q * z * q⁻¹) * q := by group
            _ = 1 := by rw [h1]; group
        rw [hz1, orderOf_one] at hz2
        omega
      exact orderOf_eq_prime (by rwa [sq]) hne1
    obtain ⟨l, hlL, hlconj⟩ := hconj z hzL (q * z * q⁻¹) hqzL hz2 hqz2
    have hcC : l⁻¹ * q ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l⁻¹ * q) * z = l⁻¹ * (q * z * q⁻¹) * q := by group
        _ = l⁻¹ * (l * z * l⁻¹) * q := by rw [← hlconj]
        _ = z * (l⁻¹ * q) := by group
    refine ⟨l, hlL, l⁻¹ * q, hcC, ?_⟩
    group
  refine ⟨hCproper, ?_⟩
  intro M hM
  let CL : Subgroup ↥L := Subgroup.centralizer ({⟨z, hzL⟩} : Set ↥L)
  have hCLmax : IsCoatom CL := hmax ⟨z, hzL⟩ (by
    simpa only [Subgroup.orderOf_mk] using hz2)
  have hCLle : CL ≤ (M ⊓ L).subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, x.2⟩
    have hxC : (x : Q) ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxL : x * (⟨z, hzL⟩ : ↥L) = (⟨z, hzL⟩ : ↥L) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (show x ∈ Subgroup.centralizer ({⟨z, hzL⟩} : Set ↥L) from hx)
      simpa using congrArg (fun t : ↥L => (t : Q)) hxL
    exact hM.le hxC
  rcases (IsCoatom.le_iff hCLmax).mp hCLle with htop | heq
  · rw [eq_top_iff]
    intro q _
    obtain ⟨l, hlL, c, hcC, hmul⟩ := hdecomp q
    have hLleM : L ≤ M := by
      intro l' hl'
      have : (⟨l', hl'⟩ : ↥L) ∈ (M ⊓ L).subgroupOf L := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    rw [hmul]
    exact M.mul_mem (hLleM hlL) (hM.le hcC)
  · have hML : M ≤ C := by
      intro m hm
      obtain ⟨l, hlL, c, hcC, hmul⟩ := hdecomp m
      have hcM : c ∈ M := hM.le hcC
      have hm' : l * c ∈ M := by rwa [hmul] at hm
      have hlM : l ∈ M := by
        have : l = (l * c) * c⁻¹ := by group
        rw [this]
        exact M.mul_mem hm' (M.inv_mem hcM)
      have hlCL : (⟨l, hlL⟩ : ↥L) ∈ CL := by
        have hlK : (⟨l, hlL⟩ : ↥L) ∈ (M ⊓ L).subgroupOf L := by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨hlM, hlL⟩
        rw [heq] at hlK
        exact hlK
      have hlz : l * z = z * l := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hlCL
        simpa using congrArg (fun t : ↥L => (t : Q)) this
      have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
      rw [Subgroup.mem_centralizer_singleton_iff, hmul]
      calc (l * c) * z = l * (c * z) := by group
        _ = l * (z * c) := by rw [hcz]
        _ = (l * z) * c := by group
        _ = (z * l) * c := by rw [hlz]
        _ = z * (l * c) := by group
    exact absurd hML hM.2

theorem isCoatom_centralizer_of_almostSimple_psu3
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hAS : CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple L)
    (hL : CFSG.Blueprint.LieModel ↥L .PSU 3 p f)
    (hp2 : p ≠ 2) (hf : 2 ≤ f)
    {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set Q)) := by
  obtain ⟨hp, _, F, hFld, hFfin, hFcard, ⟨eS⟩⟩ :=
    CFSG.GH74.Generic.lieModel_psu_data hL
  letI : Field F := hFld
  letI : Finite F := hFfin
  have hf1 : 1 ≤ f := by omega
  have hUF : UnitaryFieldData p f F := by
    refine ⟨hp, hf1, ?_⟩
    rw [hFcard, ← pow_mul, Nat.mul_comm]
  have hmax : ∀ x : ↥L, orderOf x = 2 →
      IsCoatom (Subgroup.centralizer ({x} : Set ↥L)) := by
    intro x hx2
    exact isCoatom_centralizer_psu3_of_equiv hUF hp2 eS hx2
  have hconj : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ L, g * x * g⁻¹ = y := by
    intro x hxL y hyL hx2 hy2
    let xL : ↥L := ⟨x, hxL⟩
    let yL : ↥L := ⟨y, hyL⟩
    have hx2' : orderOf xL = 2 := by
      dsimp [xL]
      simpa only [Subgroup.orderOf_mk] using hx2
    have hy2' : orderOf yL = 2 := by
      dsimp [yL]
      simpa only [Subgroup.orderOf_mk] using hy2
    have hxe : orderOf (eS xL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hx2'
    have hye : orderOf (eS yL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hy2'
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psu3
      hUF hp2 (a := eS xL) (b := eS yL) hxe hye
    refine ⟨((eS.symm g : ↥L) : Q), (eS.symm g).2, ?_⟩
    have hconjL : eS.symm g * xL * (eS.symm g)⁻¹ = yL := by
      apply eS.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    exact congrArg (fun t : ↥L => (t : Q)) hconjL
  exact isCoatom_centralizer_of_almostSimple hAS hconj hmax hzL hz2

end CFSG.LocalAnalysis.WeakClosure81

end
