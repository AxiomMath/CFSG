module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C632Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

theorem isStronglyPEmbedded_inf {G : Type} [Group G] [Finite G] {M X : Subgroup G} {p : ℕ}
    (hM : IsStronglyPEmbedded p M) (hX : ¬ X ≤ M) (hpX : p ∣ Nat.card ↥(M ⊓ X)) :
    IsStronglyPEmbedded p ((M ⊓ X).subgroupOf X) := by
  refine ⟨fun h => hX ((subgroupOf_eq_top.1 h).trans inf_le_left), ?_, fun g hg hp => ?_⟩
  · rwa [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : M ⊓ X ≤ X)).toEquiv]
  · have hgM : (g : G) ∉ M := fun h => hg (mem_subgroupOf.2 ⟨h, g.2⟩)
    apply hM.2.2 g hgM
    refine hp.trans ?_
    set Y : Subgroup ↥X := (M ⊓ X).subgroupOf X
    have hle : (Y ⊓ Y.map (MulAut.conj g).toMonoidHom).map X.subtype ≤
        M ⊓ M.map (MulAut.conj (g : G)).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, ⟨y', hy', hyy'⟩⟩, rfl⟩
      refine ⟨(mem_subgroupOf.1 hy1).1, (y' : G), (mem_subgroupOf.1 hy').1, ?_⟩
      rw [← hyy']
      simp [MulAut.conj_apply]
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective X.subtype_injective] at this

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem le_M_of_le_A_inf_L {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) : B ≤ m.M :=
  hB.trans (inf_le_left.trans ((sup_le m.hZ.le m.E_le_R).trans m.R_le_M))

theorem isPGroup_of_le_A_inf_L {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) : IsPGroup m.r B :=
  m.d.sylow.isPGroup.to_le (hB.trans (inf_le_left.trans (sup_le m.hZ.le m.E_le_R)))

theorem K_eq_U_sup_centralizer_of_le (h631 : m.C631) {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) :
    m.K = m.U ⊔ (m.K ⊓ centralizer (B : Set G)) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h631' : ⁅m.A ⊓ m.L, m.K⁆ ≤ m.U := h631
  exact eq_sup_centralizer_of_coprime m.U_le_K m.K_le_normalizer_U (m.isPGroup_of_le_A_inf_L hB)
    (fun b hb => m.mem_normalizer_K (m.le_M_of_le_A_inf_L hB hb))
    ((commutator_mono hB le_rfl).trans h631')
    ((Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_U)

theorem K_inf_centralizer_le_M_inf_normalizer (B : Subgroup G) :
    m.K ⊓ centralizer (B : Set G) ≤ m.M ⊓ normalizer (B : Set G) :=
  inf_le_inf m.K_le_M (centralizer_le_normalizer _)

theorem M_inf_normalizer_le_normalizer_centralizer (B : Subgroup G) :
    m.M ⊓ normalizer (B : Set G) ≤
      normalizer ((m.K ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  rintro x ⟨hxM, hxB⟩
  refine mem_normalizer_of_forward_uc6 fun c hc => Subgroup.mem_inf.2 ⟨m.conj_mem_K hxM hc.1, ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : x⁻¹ * b * x ∈ B := by
    have := (mem_normalizer_iff.1 (inv_mem hxB) b).1 hb
    simpa using this
  have hcb := mem_centralizer_iff.1 hc.2 _ hb'
  calc b * (x * c * x⁻¹) = x * ((x⁻¹ * b * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * b * x)) * x⁻¹ := by rw [hcb]
    _ = x * c * x⁻¹ * b := by group

theorem surjective_mk_comp_inclusion {C : Subgroup G} (hCK : C ≤ m.K) (hKUC : m.K = m.U ⊔ C) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.K)).comp (inclusion hCK)) := by
  set U' : Subgroup ↥m.K := CFSG.pPrimeCore m.r ↥m.K
  set C' : Subgroup ↥m.K := C.subgroupOf m.K with hC'
  have htop : (⊤ : Subgroup ↥m.K).map m.K.subtype = m.K := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  have hUC : U' ⊔ C' = ⊤ := by
    apply Subgroup.map_injective m.K.subtype_injective
    rw [Subgroup.map_sup, hC', Subgroup.map_subgroupOf_eq_of_le hCK, htop]
    exact hKUC.symm
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hk : k ∈ U' ⊔ C' := by
    rw [hUC]
    exact Subgroup.mem_top k
  have hk' : k ∈ (U' : Set ↥m.K) * (C' : Set ↥m.K) := by
    rw [← Subgroup.normal_mul]
    exact hk
  obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.1 hk'
  refine ⟨⟨(c : G), mem_subgroupOf.1 hc⟩, ?_⟩
  have hinc : inclusion hCK ⟨(c : G), mem_subgroupOf.1 hc⟩ = c := Subtype.ext (coe_inclusion _ _)
  rw [MonoidHom.comp_apply, hinc, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff u).2 hu, one_mul]

theorem dvd_card_Kbar {p : ℕ} (hp : p ∈ uniqueFourSigma m.M) (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S)
    (h626 : m.C626) (h628b : m.C628b) : p ∣ Nat.card m.Kbar := by
  have hpr : p.Prime := hp.1.1
  set K' : Subgroup ↥m.M := m.K.subgroupOf m.M
  have hMcard : Nat.card K' * K'.index = Nat.card ↥m.M := Subgroup.card_mul_index K'
  have hK'card : Nat.card K' = Nat.card m.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.K_le_M).toEquiv
  have hpK : p ∣ Nat.card m.K := by
    have h := m.dvd_card_M_of_mem_sigma hp
    rw [← hMcard, hK'card] at h
    exact ((Nat.Prime.dvd_mul hpr).1 h).resolve_right (m.not_dvd_index_K hp hcyc h626)
  have hKcard : Nat.card m.K = Nat.card m.Kbar * Nat.card (CFSG.pPrimeCore m.r ↥m.K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hKcard] at hpK
  exact ((Nat.Prime.dvd_mul hpr).1 hpK).resolve_right (h628b p hp)

end Mz614

theorem Mz614.not_isPSolvable_inf_normalizer {G : Type} [Group G] [Finite G] (m : Mz614 G) {p : ℕ}
    (hp : p ∈ uniqueFourSigma m.M) (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626)
    (h628b : m.C628b) (h629 : m.C629) (h631 : m.C631) {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(m.M ⊓ normalizer (B : Set G)) := by
  intro hsolv
  have hpr : p.Prime := hp.1.1
  set X0 : Subgroup G := m.M ⊓ normalizer (B : Set G)
  set C : Subgroup G := m.K ⊓ centralizer (B : Set G)
  have hCK : C ≤ m.K := inf_le_left
  have hCX0 : C ≤ X0 := m.K_inf_centralizer_le_M_inf_normalizer B
  haveI hHn : (C.subgroupOf X0).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCX0).2 (m.M_inf_normalizer_le_normalizer_centralizer B)
  set ψ : ↥(C.subgroupOf X0) →* m.Kbar :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.K)).comp (inclusion hCK)).comp
      (subgroupOfEquivOfLe hCX0).toMonoidHom
  have hψs : Function.Surjective ψ :=
    (m.surjective_mk_comp_inclusion hCK (m.K_eq_U_sup_centralizer_of_le h631 hB)).comp
      (subgroupOfEquivOfLe hCX0).surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  haveI : IsSimpleGroup m.Kbar := h629.1
  haveI hsimple : IsSimpleGroup (↥(C.subgroupOf X0) ⧸ ψ.ker) := e.isSimpleGroup
  have hidx : ψ.ker.index = Nat.card m.Kbar := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr e.toEquiv
  have hdvd : p ∣ Nat.card m.Kbar := m.dvd_card_Kbar hp hcyc h626 h628b
  rcases hsolv _ hHn.isSubnormal ψ.ker hsimple with h | h
  · haveI : Fact p.Prime := ⟨hpr⟩
    haveI : IsCyclic m.Kbar := isCyclic_of_prime_card (hidx ▸ h)
    obtain ⟨a, b, hab⟩ := h629.2
    exact hab (mul_comm' a b)
  · rw [hidx] at h
    exact hpr.ne_one (Nat.Coprime.eq_one_of_dvd h hdvd)

end CFSG.LocalAnalysis.UniquenessCase.UC6
