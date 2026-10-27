module

public import CFSG.LocalAnalysis.StandardType.FS81.ConstructYE7
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
import CFSG.LocalAnalysis.SeitzReduction.EnKLLevi
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
import CFSG.ClassicalGroups.Alternating.TransvectionGenerationTwo
import CFSG.GroupTheory.NormalLeCentralizerOfInfBot
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot

theorem le_centralizer_of_normal_threePrime {G : Type} [Group G] [Finite G] {b₀ : G}
    {K R : Subgroup G} (hKsimple : IsSimpleGroup ↥K) (hK3 : 3 ∣ Nat.card K)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hRC : R ≤ Subgroup.centralizer ({b₀} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hR3 : ¬ 3 ∣ Nat.card R) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  have := hKsimple
  have hRconj : ∀ a ∈ R, ∀ c ∈ Subgroup.centralizer ({b₀} : Set G), c * a * c⁻¹ ∈ R := by
    intro a ha c hc
    have h := hRn.conj_mem ⟨a, hRC ha⟩ ha ⟨c, hc⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hbot : R ⊓ K = ⊥ := by
    have hNn : ((R ⊓ K).subgroupOf K).Normal := by
      refine Subgroup.Normal.mk fun n hn k => ?_
      have hnR : (n : G) ∈ R := (Subgroup.mem_subgroupOf.mp hn).1
      have hnK : (n : G) ∈ K := (Subgroup.mem_subgroupOf.mp hn).2
      change ((k : G) * (n : G) * (k : G)⁻¹) ∈ R ⊓ K
      exact ⟨hRconj (n : G) hnR (k : G) (hKC k.2),
        K.mul_mem (K.mul_mem k.2 hnK) (K.inv_mem k.2)⟩
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ K).subgroupOf K) with h | h
    · have hd := Subgroup.subgroupOf_eq_bot.mp h
      rw [disjoint_iff] at hd
      rwa [inf_assoc, inf_idem] at hd
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact absurd (hK3.trans ((Subgroup.card_dvd_of_le h).trans
        (Subgroup.card_dvd_of_le inf_le_left))) hR3
  have hbotC : (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))) ⊓
      (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))) = ⊥ := by
    change Subgroup.comap (Subgroup.centralizer ({b₀} : Set G)).subtype R ⊓
      Subgroup.comap (Subgroup.centralizer ({b₀} : Set G)).subtype K = ⊥
    rw [← Subgroup.comap_inf, hbot]
    simp
  have hle := CFSG.normal_le_centralizer_of_inf_eq_bot hRn hKn hbotC
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := Subgroup.mem_centralizer_iff.1
    (hle (x := ⟨r, hRC hr⟩) hr) ⟨k, hKC hk⟩ hk
  exact congrArg Subtype.val h

private theorem centralizes_inf_centralizer_of_normal_threePrime
    {G : Type} [Group G] [Finite G] {x : G} {K Q : Subgroup G}
    (hQx : Q ≤ Subgroup.centralizer ({x} : Set G))
    (hQn : (Q.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hbot : Q ⊓ (K ⊓ Subgroup.centralizer ({x} : Set G)) = ⊥) :
    Q ≤ Subgroup.centralizer ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hQconj : ∀ a ∈ Q, ∀ h ∈ Subgroup.centralizer ({x} : Set G), h * a * h⁻¹ ∈ Q := by
    intro a ha h hh
    have h' := hQn.conj_mem ⟨a, hQx ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨h, hh⟩
    simpa using Subgroup.mem_subgroupOf.mp h'
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcK : c ∈ K := hc.1
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) := hc.2
  have hqcx : q ∈ Subgroup.centralizer ({x} : Set G) := hQx hq
  have hconjQ : c * q⁻¹ * c⁻¹ ∈ Q := hQconj q⁻¹ (Q.inv_mem hq) c hcx
  have hcommQ : q * (c * q⁻¹ * c⁻¹) ∈ Q := Q.mul_mem hq hconjQ
  have hcommK : q * (c * q⁻¹ * c⁻¹) ∈ K := by
    have hqcq : q * c * q⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hQK hq) c).1 hcK
    have h : q * c * q⁻¹ * c⁻¹ ∈ K := K.mul_mem hqcq (K.inv_mem hcK)
    simpa [mul_assoc] using h
  have hcommx : q * (c * q⁻¹ * c⁻¹) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqx : Commute q x := Subgroup.mem_centralizer_singleton_iff.1 hqcx
    have hcx' : Commute c x := Subgroup.mem_centralizer_singleton_iff.1 hcx
    have h1 : Commute (q⁻¹ * c⁻¹) x := hqx.inv_left.mul_left hcx'.inv_left
    have h2 : Commute (c * (q⁻¹ * c⁻¹)) x := hcx'.mul_left h1
    have h3 : Commute (q * (c * (q⁻¹ * c⁻¹))) x := hqx.mul_left h2
    simpa [mul_assoc] using h3.eq
  have hmem : q * (c * q⁻¹ * c⁻¹) ∈ Q ⊓ (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ⟨hcommQ, hcommK, hcommx⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hqc : q * c = c * q := by
    calc q * c = (q * (c * q⁻¹ * c⁻¹)) * (c * q) := by group
      _ = c * q := by rw [hmem, one_mul]
  exact hqc.symm

private theorem le_centralizer_map_conj_of_map_conj_inv
    {G : Type} [Group G] {K R : Subgroup G} {g : G}
    (h : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer (K : Set G)) :
    R ≤ Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom) : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  have hqQ : MulAut.conj g⁻¹ r ∈ R.map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hr
  have hcomm : MulAut.conj g⁻¹ r * k = k * MulAut.conj g⁻¹ r :=
    (Subgroup.mem_centralizer_iff.1 (h hqQ) k hk).symm
  have hr_eq : r = g * (MulAut.conj g⁻¹ r) * g⁻¹ := by
    rw [MulAut.conj_apply]; group
  rw [hr_eq, MulAut.conj_apply]
  calc g * k * g⁻¹ * (g * (MulAut.conj g⁻¹ r) * g⁻¹)
      = g * (k * (MulAut.conj g⁻¹ r)) * g⁻¹ := by group
    _ = g * ((MulAut.conj g⁻¹ r) * k) * g⁻¹ := by rw [hcomm]
    _ = g * (MulAut.conj g⁻¹ r) * g⁻¹ * (g * k * g⁻¹) := by group

private theorem map_conj_inv_le_centralizer {G : Type} [Group G] [Finite G] {b₀ : G}
    {K R : Subgroup G} {g : G} (hRK : R ≤ Subgroup.centralizer (K : Set G))
    (hRC : R ≤ Subgroup.centralizer ({b₀} : Set G)) (hg : g * b₀ * g⁻¹ ∈ K) :
    R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({g⁻¹ * b₀ * g} : Set G) ∧
      R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({b₀} : Set G) := by
  constructor
  · intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    have hab : a * b₀ = b₀ * a := Subgroup.mem_centralizer_singleton_iff.1 (hRC ha)
    change (MulAut.conj g⁻¹) a * (g⁻¹ * b₀ * g) = (g⁻¹ * b₀ * g) * (MulAut.conj g⁻¹) a
    rw [MulAut.conj_apply]
    simp only [inv_inv]
    calc g⁻¹ * a * g * (g⁻¹ * b₀ * g) = g⁻¹ * (a * b₀) * g := by group
      _ = g⁻¹ * (b₀ * a) * g := by rw [hab]
      _ = (g⁻¹ * b₀ * g) * (g⁻¹ * a * g) := by group
  · intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    have hcomm : a * (g * b₀ * g⁻¹) = (g * b₀ * g⁻¹) * a :=
      (Subgroup.mem_centralizer_iff.1 (hRK ha) (g * b₀ * g⁻¹) hg).symm
    change (MulAut.conj g⁻¹) a * b₀ = b₀ * (MulAut.conj g⁻¹) a
    rw [MulAut.conj_apply]
    simp only [inv_inv]
    calc g⁻¹ * a * g * b₀ = g⁻¹ * (a * (g * b₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b₀ * g⁻¹) * a) * g := by rw [hcomm]
      _ = b₀ * (g⁻¹ * a * g) := by group

private theorem map_conj_inv_normal {G : Type} [Group G] {b₀ : G} {R : Subgroup G} {g : G}
    (hRC : R ≤ Subgroup.centralizer ({b₀} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal) :
    ((R.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
      (Subgroup.centralizer ({g⁻¹ * b₀ * g} : Set G))).Normal := by
  refine Subgroup.Normal.mk fun n hn h => ?_
  have hnQ : (n : G) ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_subgroupOf.mp hn
  have hh : (h : G) ∈ Subgroup.centralizer ({g⁻¹ * b₀ * g} : Set G) := h.2
  rw [Subgroup.mem_map] at hnQ
  obtain ⟨r₀, hr₀, hn_eq⟩ := hnQ
  have hgh : g * (h : G) * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hhx : (h : G) * (g⁻¹ * b₀ * g) = (g⁻¹ * b₀ * g) * (h : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 hh
    calc (g * (h : G) * g⁻¹) * b₀ = g * ((h : G) * (g⁻¹ * b₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b₀ * g) * (h : G)) * g⁻¹ := by rw [hhx]
      _ = b₀ * (g * (h : G) * g⁻¹) := by group
  have hconjR : (g * (h : G) * g⁻¹) * r₀ * (g * (h : G) * g⁻¹)⁻¹ ∈ R := by
    have h := hRn.conj_mem ⟨r₀, hRC hr₀⟩ hr₀ ⟨g * (h : G) * g⁻¹, hgh⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hmem : (h : G) * (n : G) * (h : G)⁻¹ ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.mem_map]
    refine ⟨(g * (h : G) * g⁻¹) * r₀ * (g * (h : G) * g⁻¹)⁻¹, hconjR, ?_⟩
    change (MulAut.conj g⁻¹) r₀ = (n : G) at hn_eq
    have hr₀ : r₀ = g * (n : G) * g⁻¹ := by
      rw [MulAut.conj_apply] at hn_eq
      simp only [inv_inv] at hn_eq
      rw [← hn_eq]; group
    change (MulAut.conj g⁻¹) ((g * (h : G) * g⁻¹) * r₀ * (g * (h : G) * g⁻¹)⁻¹) =
      (h : G) * (n : G) * (h : G)⁻¹
    rw [hr₀, MulAut.conj_apply]
    simp only [inv_inv]
    group
  rw [Subgroup.mem_subgroupOf]
  simpa using hmem

private noncomputable def perpLeviImage {G : Type} [Group G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) : Subgroup G :=
  ((perpLevi .E7 (ZMod 2)).map ψ.toMonoidHom).map K.subtype

private theorem exists_mul_zpowers_map_perpLevi_of_mem_inf_centralizer_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3)
    {c : G} (hcK : c ∈ K)
    (hcx : c ∈ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G)) :
    ∃ y ∈ Subgroup.zpowers (((ψ r : ↥K) : G)),
      ∃ d ∈ perpLeviImage ψ, c = y * d := by
  have hXJ : Subgroup.zpowers r ≤
      (highRootSL2 .E7 (ZMod 2)).subgroupOf (adjointGroup .E7 (ZMod 2)) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hr)
  have hXcard : Nat.card (Subgroup.zpowers r) = Nat.card (ZMod 2) + 1 := by
    rw [Nat.card_zpowers, hr3, Nat.card_zmod]
  have hXcyc : IsCyclic (Subgroup.zpowers r) := Subgroup.isCyclic_zpowers r
  have hc' : ψ.symm ⟨c, hcK⟩ ∈ Subgroup.centralizer
      (Subgroup.zpowers r : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    apply MulEquiv.injective ψ
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Subgroup.subtype_injective K
    simpa using Subgroup.mem_centralizer_singleton_iff.1 hcx
  obtain ⟨y₀, hy₀, d₀, hd₀, hcd⟩ :=
    exists_mul_of_mem_centralizer_nonsplit_E7_of_finite (K := ZMod 2)
      (X := Subgroup.zpowers r) hXJ hXcard hXcyc hc'
  refine ⟨((ψ y₀ : ↥K) : G), ?_, ((ψ d₀ : ↥K) : G), ?_, ?_⟩
  · have hmem : ((ψ y₀ : ↥K) : G) ∈
        Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r)) :=
      Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_map_of_mem ψ.toMonoidHom hy₀)
    have hmap : Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r)) =
        Subgroup.zpowers (((ψ r : ↥K) : G)) := by
      rw [MonoidHom.map_zpowers ψ.toMonoidHom, MonoidHom.map_zpowers K.subtype]
      rfl
    rwa [hmap] at hmem
  · exact Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_map_of_mem ψ.toMonoidHom hd₀)
  · have h := congrArg (fun z : ↥K => (z : G)) (congrArg ψ hcd)
    simpa using h

private theorem inf_centralizer_perpLeviImage_E7 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) :
    K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G) =
      Subgroup.zpowers ((ψ r : ↥K) : G) ⊔ perpLeviImage ψ := by
  have hXJ : Subgroup.zpowers r ≤
      (highRootSL2 .E7 (ZMod 2)).subgroupOf (adjointGroup .E7 (ZMod 2)) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hr)
  have hXcard : Nat.card (Subgroup.zpowers r) = Nat.card (ZMod 2) + 1 := by
    rw [Nat.card_zpowers, hr3, Nat.card_zmod]
  have hXcyc : IsCyclic (Subgroup.zpowers r) := Subgroup.isCyclic_zpowers r
  have h := inf_centralizer_nonsplit_E7_of_finite (K := ZMod 2) (G := G) (L := K)
    (X := Subgroup.zpowers r) (e := ψ.symm) hXJ hXcard hXcyc
  have hmap : Subgroup.map K.subtype
      (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r)) = Subgroup.zpowers ((ψ r : ↥K) : G) := by
    rw [MonoidHom.map_zpowers ψ.toMonoidHom, MonoidHom.map_zpowers K.subtype]
    rfl
  have hcen : Subgroup.centralizer
      (((Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r))) :
        Subgroup G) : Set G) = Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G) := by
    rw [hmap, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h' : K ⊓ Subgroup.centralizer
      (((Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r))) :
        Subgroup G) : Set G) =
      Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r)) ⊔
        Subgroup.map K.subtype (Subgroup.map ψ.toMonoidHom (perpLevi .E7 (ZMod 2))) := h
  rw [hcen] at h'
  simpa [perpLeviImage] using h'

private theorem isSimpleGroup_perpLeviImage_E7 {G : Type} [Group G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) :
    IsSimpleGroup ↥(perpLeviImage ψ) := by
  have eD : ↥(perpLevi .E7 (ZMod 2)) ≃* ↥(perpLeviImage ψ) :=
    (Subgroup.equivMapOfInjective (perpLevi .E7 (ZMod 2)) ψ.toMonoidHom
      (MulEquiv.injective ψ)).trans
      (Subgroup.equivMapOfInjective ((perpLevi .E7 (ZMod 2)).map ψ.toMonoidHom) K.subtype
        (Subgroup.subtype_injective K))
  have : IsSimpleGroup ↥(perpLevi .E7 (ZMod 2)) := isSimpleGroup_perpLevi_E7
  exact MulEquiv.isSimpleGroup eD.symm

private theorem center_perpLeviImage_E7 {G : Type} [Group G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) :
    Subgroup.center ↥(perpLeviImage ψ) = ⊥ := by
  have eD : ↥(perpLevi .E7 (ZMod 2)) ≃* ↥(perpLeviImage ψ) :=
    (Subgroup.equivMapOfInjective (perpLevi .E7 (ZMod 2)) ψ.toMonoidHom
      (MulEquiv.injective ψ)).trans
      (Subgroup.equivMapOfInjective ((perpLevi .E7 (ZMod 2)).map ψ.toMonoidHom) K.subtype
        (Subgroup.subtype_injective K))
  rw [← Subgroup.map_center_eq eD, center_perpLevi_E7_eq_bot (K := ZMod 2), Subgroup.map_bot]

private theorem dvd_card_perpLeviImage_E7 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) :
    3 ∣ Nat.card ↥(perpLeviImage ψ) := by
  obtain ⟨u, hu, hu3, -⟩ :=
    exists_mem_perpLevi_orderOf_eq_three (τ := .E7) (K := ZMod 2) (Or.inr (Or.inl rfl))
  have huD : ((ψ u : ↥K) : G) ∈ perpLeviImage ψ :=
    Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_map_of_mem ψ.toMonoidHom hu)
  have hu3' : orderOf (((ψ u : ↥K) : G)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ u, hu3]
  rw [← hu3']
  exact Subgroup.orderOf_dvd_natCard (perpLeviImage ψ) huD

private theorem exists_mem_inner_of_mem_normalizer
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {q : G} (hqK : q ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : ↥K, (∀ c : ↥K, q * c * q⁻¹ = k * c * k⁻¹) ∧
      ((k : G)⁻¹ * q) ∈ Subgroup.centralizer (K : Set G) := by
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨q, hqK⟩ with hα
  have hαcoe : ∀ c : ↥K, ((α c : ↥K) : G) = q * c * q⁻¹ := fun c =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨q, hqK⟩ c
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 :=
    CFSG.ClassicalGroups.Alternating.eq_zero_or_eq_one_of_card_eq_two (Nat.card_zmod 2)
  obtain ⟨g₀, hg₀⟩ := CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_forall_eq_zero_or_eq_one
    (τ := .E7) (K := ZMod 2) (Or.inl rfl) h01 ((ψ.trans α).trans ψ.symm)
  have hconj : ∀ c : ↥K, q * c * q⁻¹ = (ψ g₀) * c * (ψ g₀)⁻¹ := by
    intro c
    have h := congrArg (fun β : MulAut ↥(adjointGroup .E7 (ZMod 2)) => β (ψ.symm c)) hg₀
    simp only [MulEquiv.trans_apply, MulAut.conj_apply] at h
    have h2 : α c = (ψ g₀) * c * (ψ g₀)⁻¹ := by
      apply MulEquiv.injective ψ.symm
      simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] using h
    rw [← hαcoe c, h2]
    rfl
  refine ⟨ψ g₀, hconj, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h' : q * c * q⁻¹ = ((ψ g₀ : ↥K) : G) * c * ((ψ g₀ : ↥K) : G)⁻¹ := by
    simpa using hconj ⟨c, hc⟩
  calc c * (((ψ g₀ : ↥K) : G)⁻¹ * q)
      = ((ψ g₀ : ↥K) : G)⁻¹ * (((ψ g₀ : ↥K) : G) * c * ((ψ g₀ : ↥K) : G)⁻¹) * q := by
        group
    _ = ((ψ g₀ : ↥K) : G)⁻¹ * (q * c * q⁻¹) * q := by rw [← h']
    _ = (((ψ g₀ : ↥K) : G)⁻¹ * q) * c := by group

private theorem perpLeviImage_le_inf_centralizer_E7 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) :
    perpLeviImage ψ ≤ K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G) := by
  rw [inf_centralizer_perpLeviImage_E7 ψ hr hr3]
  exact le_sup_right

private theorem inf_eq_bot_of_normal_threePrime_subgroup_centralizer_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) (N : Subgroup G)
    (hNle : N ≤ K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))
    (hNn : (N.subgroupOf (K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))).Normal)
    (hN3 : ¬ 3 ∣ Nat.card N) :
    N ⊓ perpLeviImage ψ = ⊥ := by
  classical
  set x : G := ((ψ r : ↥K) : G) with hx
  have hinf : K ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.zpowers x ⊔ perpLeviImage ψ := inf_centralizer_perpLeviImage_E7 ψ hr hr3
  have hNle' : N ≤ Subgroup.zpowers x ⊔ perpLeviImage ψ := by rw [← hinf]; exact hNle
  have hNn' : (N.subgroupOf (Subgroup.zpowers x ⊔ perpLeviImage ψ)).Normal := by
    rw [← hinf]; exact hNn
  have hN'normal : ((N ⊓ perpLeviImage ψ).subgroupOf (perpLeviImage ψ)).Normal := by
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := N)
      (A := Subgroup.zpowers x ⊔ perpLeviImage ψ) (B := perpLeviImage ψ) (hN := hNn')
    rwa [inf_eq_right.mpr le_sup_right] at h
  have := hN'normal
  have := isSimpleGroup_perpLeviImage_E7 ψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N ⊓ perpLeviImage ψ).subgroupOf (perpLeviImage ψ)) with h | h
  · have hd := Subgroup.subgroupOf_eq_bot.mp h
    rw [disjoint_iff] at hd
    rwa [inf_assoc, inf_idem] at hd
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd ((dvd_card_perpLeviImage_E7 ψ).trans ((Subgroup.card_dvd_of_le h).trans
      (Subgroup.card_dvd_of_le inf_le_left))) hN3

private theorem zpowers_le_centralizer_perpLeviImage_E7 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) :
    Subgroup.zpowers ((ψ r : ↥K) : G) ≤ Subgroup.centralizer (perpLeviImage ψ : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.1
    (perpLeviImage_le_inf_centralizer_E7 ψ hr hr3 hd).2

private theorem commute_normal_threePrime_subgroup_centralizer_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) (N : Subgroup G)
    (hNle : N ≤ K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))
    (hNn : (N.subgroupOf (K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))).Normal)
    (hNDbot : N ⊓ perpLeviImage ψ = ⊥) :
    ∀ n ∈ N, ∀ d ∈ perpLeviImage ψ, n * d = d * n := by
  classical
  set x : G := ((ψ r : ↥K) : G) with hx
  have hinf : K ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.zpowers x ⊔ perpLeviImage ψ := inf_centralizer_perpLeviImage_E7 ψ hr hr3
  have hNle' : N ≤ Subgroup.zpowers x ⊔ perpLeviImage ψ := by rw [← hinf]; exact hNle
  have hNn' : (N.subgroupOf (Subgroup.zpowers x ⊔ perpLeviImage ψ)).Normal := by
    rw [← hinf]; exact hNn
  have hxcent := zpowers_le_centralizer_perpLeviImage_E7 ψ hr hr3
  intro n hn d hd
  have hmem : n * d * n⁻¹ * d⁻¹ ∈ N ⊓ perpLeviImage ψ := by
    constructor
    · have hconjN : d * n⁻¹ * d⁻¹ ∈ N := by
        have h := hNn'.conj_mem ⟨n⁻¹, Subgroup.inv_mem _ (hNle' hn)⟩
          (Subgroup.inv_mem _ hn) ⟨d, Subgroup.mem_sup_right hd⟩
        simpa using Subgroup.mem_subgroupOf.mp h
      have := N.mul_mem hn hconjN
      simpa [mul_assoc] using this
    · obtain ⟨y, hy, d', hd', rfl⟩ :=
        exists_mul_zpowers_map_perpLevi_of_mem_inf_centralizer_E7 ψ hr hr3
          (hNle (x := n) hn).1 (hNle (x := n) hn).2
      have hyc : y ∈ Subgroup.centralizer (perpLeviImage ψ : Set G) := hxcent hy
      have he : d' * d * d'⁻¹ ∈ perpLeviImage ψ :=
        (perpLeviImage ψ).mul_mem ((perpLeviImage ψ).mul_mem hd' hd) ((perpLeviImage ψ).inv_mem hd')
      have hye : y * (d' * d * d'⁻¹) * y⁻¹ = d' * d * d'⁻¹ := by
        calc y * (d' * d * d'⁻¹) * y⁻¹ = (d' * d * d'⁻¹) * y * y⁻¹ := by
              rw [show y * (d' * d * d'⁻¹) = (d' * d * d'⁻¹) * y from
                (Subgroup.mem_centralizer_iff.1 hyc _ he).symm]
          _ = d' * d * d'⁻¹ := by group
      have hconj : y * d' * d * (y * d')⁻¹ = d' * d * d'⁻¹ := by
        calc y * d' * d * (y * d')⁻¹ = y * (d' * d * d'⁻¹) * y⁻¹ := by group
          _ = d' * d * d'⁻¹ := hye
      rw [hconj]
      exact (perpLeviImage ψ).mul_mem he ((perpLeviImage ψ).inv_mem hd)
  rw [hNDbot, Subgroup.mem_bot] at hmem
  calc n * d = (n * d * n⁻¹ * d⁻¹) * (d * n) := by group
    _ = d * n := by rw [hmem, one_mul]

private theorem exists_mem_zpowers_of_mem_centralizes_inf_centralizer_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) {Q : Subgroup G}
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hQcent : Q ≤ Subgroup.centralizer
      ((K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G) : Subgroup G) : Set G))
    {q : G} (hq : q ∈ Q) :
    ∃ k : ↥K, (k : G) ∈ Subgroup.zpowers (((ψ r : ↥K) : G)) ∧
      ((k : G)⁻¹ * q) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  set x : G := ((ψ r : ↥K) : G) with hx
  obtain ⟨k, -, hdC⟩ := exists_mem_inner_of_mem_normalizer ψ (hQK hq)
  have hkcent : (k : G) ∈ Subgroup.centralizer
      ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    have hqcent : q ∈ Subgroup.centralizer
        ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := hQcent hq
    have hdcent : ((k : G)⁻¹ * q) ∈ Subgroup.centralizer
        ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hdC
    have hk_eq : (k : G) = q * ((k : G)⁻¹ * q)⁻¹ := by group
    rw [hk_eq]
    exact Subgroup.mul_mem _ hqcent (Subgroup.inv_mem _ hdcent)
  have hkx : (k : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxmem : x ∈ (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
      ⟨show x ∈ K from (ψ r).2, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 hkcent x hxmem).symm
  have hxcent := zpowers_le_centralizer_perpLeviImage_E7 ψ hr hr3
  have hkD : (k : G) ∈ Subgroup.centralizer (perpLeviImage ψ : Set G) :=
    Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (perpLeviImage_le_inf_centralizer_E7 ψ hr hr3)) hkcent
  obtain ⟨y, hy, d', hd', hkfac⟩ :=
    exists_mul_zpowers_map_perpLevi_of_mem_inf_centralizer_E7 ψ hr hr3 k.2 hkx
  have hd'1 : d' = 1 := by
    have hd'center : (⟨d', hd'⟩ : ↥(perpLeviImage ψ)) ∈
        Subgroup.center ↥(perpLeviImage ψ) := by
      rw [Subgroup.mem_center_iff]
      intro d₁
      have hkD' : Commute (k : G) (d₁ : G) :=
        (Subgroup.mem_centralizer_iff.1 hkD (d₁ : G) d₁.2).symm
      have hyD' : Commute y (d₁ : G) :=
        (Subgroup.mem_centralizer_iff.1 (hxcent hy) (d₁ : G) d₁.2).symm
      have hd'eq : d' = y⁻¹ * (k : G) := by rw [hkfac]; group
      have hd'comm : Commute d' (d₁ : G) := by
        rw [hd'eq]
        exact hyD'.inv_left.mul_left hkD'
      exact Subtype.ext hd'comm.eq.symm
    rw [center_perpLeviImage_E7 ψ, Subgroup.mem_bot] at hd'center
    exact congrArg Subtype.val hd'center
  refine ⟨k, ?_, hdC⟩
  rw [hkfac, hd'1, mul_one]
  exact hy

private theorem eq_bot_of_normal_threePrime_subgroup_centralizer_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) (N : Subgroup G)
    (hNle : N ≤ K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))
    (hNn : (N.subgroupOf (K ⊓ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))).Normal)
    (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  classical
  set x : G := ((ψ r : ↥K) : G) with hx
  have hxcent := zpowers_le_centralizer_perpLeviImage_E7 ψ hr hr3
  have hNDbot := inf_eq_bot_of_normal_threePrime_subgroup_centralizer_E7 ψ hr hr3 N hNle hNn hN3
  have hNDcomm := commute_normal_threePrime_subgroup_centralizer_E7 ψ hr hr3 N hNle hNn hNDbot
  have hDcenter := center_perpLeviImage_E7 ψ
  have hNle_x : N ≤ Subgroup.zpowers x := by
    intro n hn
    obtain ⟨y, hy, d, hd, hnd⟩ :=
      exists_mul_zpowers_map_perpLevi_of_mem_inf_centralizer_E7 ψ hr hr3
        (hNle (x := n) hn).1 (hNle (x := n) hn).2
    have hmemN : y * d ∈ N := hnd ▸ hn
    have hdcenter : (⟨d, hd⟩ : ↥(perpLeviImage ψ)) ∈ Subgroup.center ↥(perpLeviImage ψ) := by
      rw [Subgroup.mem_center_iff]
      intro d₁
      have hkD' : Commute (y * d) (d₁ : G) := hNDcomm (y * d) hmemN (d₁ : G) d₁.2
      have hyD' : Commute y (d₁ : G) :=
        (Subgroup.mem_centralizer_iff.1 (hxcent hy) (d₁ : G) d₁.2).symm
      have hd'eq : d = y⁻¹ * (y * d) := by group
      have hd'comm : Commute d (d₁ : G) := by
        rw [hd'eq]
        exact hyD'.inv_left.mul_left hkD'
      exact Subtype.ext hd'comm.eq.symm
    rw [hDcenter, Subgroup.mem_bot] at hdcenter
    have hd1 : d = 1 := congrArg Subtype.val hdcenter
    rw [hd1, mul_one] at hnd
    exact hnd ▸ hy
  have hx3 : orderOf x = 3 := by
    rw [hx, Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ r, hr3]
  have hprime : Nat.Prime (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hx3]; norm_num
  have : Fact (Nat.Prime (Nat.card (Subgroup.zpowers x))) := ⟨hprime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (N.subgroupOf (Subgroup.zpowers x)) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hmem : n ∈ N ⊓ Subgroup.zpowers x := ⟨hn, hNle_x hn⟩
    rw [disjoint_iff.mp h, Subgroup.mem_bot] at hmem
    exact hmem
  · rw [Subgroup.subgroupOf_eq_top] at h
    have h3 : 3 ∣ Nat.card N := by
      rw [← hx3]
      exact Subgroup.orderOf_dvd_natCard N (h (Subgroup.mem_zpowers x))
    exact absurd h3 hN3

theorem le_centralizer_of_normal_centralizer_rootElt_E7 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) {Q : Subgroup G} (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hQx : Q ≤ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))
    (hQn : (Q.subgroupOf (Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))).Normal)
    (hQ3 : ¬ 3 ∣ Nat.card Q) :
    Q ≤ Subgroup.centralizer (K : Set G) := by
  classical
  set x : G := ((ψ r : ↥K) : G) with hx
  have hQx' : Q ≤ Subgroup.centralizer ({x} : Set G) := hQx
  have hQn' : (Q.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := hQn
  have hQbot : Q ⊓ (K ⊓ Subgroup.centralizer ({x} : Set G)) = ⊥ := by
    have hNn : ((Q ⊓ (K ⊓ Subgroup.centralizer ({x} : Set G))).subgroupOf
        (K ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
      have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := Q)
        (A := Subgroup.centralizer ({x} : Set G))
        (B := K ⊓ Subgroup.centralizer ({x} : Set G)) (hN := hQn')
      rwa [inf_eq_right.mpr inf_le_right] at h
    refine eq_bot_of_normal_threePrime_subgroup_centralizer_E7 ψ hr hr3 _ inf_le_right hNn ?_
    intro h3
    exact hQ3 (h3.trans (Subgroup.card_dvd_of_le (inf_le_left : Q ⊓ _ ≤ Q)))
  have hQcent : Q ≤ Subgroup.centralizer
      ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    centralizes_inf_centralizer_of_normal_threePrime hQx' hQn' hQK hQbot
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [← Subgroup.map_center_eq ψ,
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := ZMod 2),
      Subgroup.map_bot]
  intro q hq
  obtain ⟨k, hkz, hdC⟩ :=
    exists_mem_zpowers_of_mem_centralizes_inf_centralizer_E7 ψ hr hr3 hQK hQcent hq
  have hx3 : orderOf x = 3 := by
    rw [hx, Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ r, hr3]
  have hm3 : ¬ 3 ∣ orderOf q := by
    intro h
    exact hQ3 (h.trans (Subgroup.orderOf_dvd_natCard Q hq))
  have hkpow : (k : G) ^ orderOf q = 1 := by
    have hkd : Commute (k : G) ((k : G)⁻¹ * q) :=
      Subgroup.mem_centralizer_iff.1 hdC (k : G) k.2
    have hprod : (k : G) ^ orderOf q * (((k : G)⁻¹ * q) ^ orderOf q) = 1 := by
      rw [← hkd.mul_pow (orderOf q)]
      rw [show (k : G) * ((k : G)⁻¹ * q) = q from by group]
      exact pow_orderOf_eq_one q
    have hkeq : (k : G) ^ orderOf q = ((((k : G)⁻¹ * q) ^ orderOf q))⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hprod
    have hcent : (((k : G)⁻¹ * q) ^ orderOf q)⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).inv_mem
        ((Subgroup.centralizer (K : Set G)).pow_mem hdC (orderOf q))
    have hkcentK : (k : G) ^ orderOf q ∈ Subgroup.centralizer (K : Set G) := hkeq.symm ▸ hcent
    have hkK : (k : G) ^ orderOf q ∈ K := K.pow_mem k.2 (orderOf q)
    have hkcenter : (⟨(k : G) ^ orderOf q, hkK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkcentK (y : G) y.2)
    rw [hZ, Subgroup.mem_bot] at hkcenter
    exact congrArg Subtype.val hkcenter
  have hk1 : (k : G) = 1 := by
    have hdvd3 : orderOf (k : G) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) hkz
      rwa [Nat.card_zpowers, hx3] at h
    have hdvdm : orderOf (k : G) ∣ orderOf q := orderOf_dvd_of_pow_eq_one hkpow
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h3 ▸ hdvdm) hm3
  have hqeqd : q = (k : G)⁻¹ * q := by rw [hk1]; group
  rwa [hqeqd]

theorem e7RootCoreAt_holds : E7RootCoreAt := by
  intro G _ _ b₀ K E hstd B hB hrec g hg hroot R hRC hRn hR3
  obtain ⟨ψ, r, hr, hxr⟩ := hroot
  have hA : FS81HypA b₀ K := hstd.2.1.1
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hA.2.1
  have hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal := hA.2.2.1
  have hb₀3 : orderOf b₀ = 3 := hA.1
  have hxK : g⁻¹ * b₀ * g ∈ K := by rw [← hxr]; exact (ψ r).2
  have hx3 : orderOf (g⁻¹ * b₀ * g) = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b₀
    rw [MulAut.conj_apply, inv_inv, hb₀3] at h
    exact h
  have hr3 : orderOf r = 3 := by
    have h1 : orderOf ((ψ r : ↥K) : G) = orderOf r := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ r]
    rw [hxr, hx3] at h1
    exact h1.symm
  have hKsimple : IsSimpleGroup ↥K := by
    have : IsSimpleGroup ↥(adjointGroup .E7 (ZMod 2)) :=
      CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
        (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (ZMod 2))
    exact MulEquiv.isSimpleGroup ψ.symm
  have hK3 : 3 ∣ Nat.card K := by
    rw [← hx3]
    exact Subgroup.orderOf_dvd_natCard K hxK
  have hRK : R ≤ Subgroup.centralizer (K : Set G) :=
    le_centralizer_of_normal_threePrime hKsimple hK3 hKC hKn hRC hRn hR3
  refine ⟨hRK, ?_⟩
  set Q : Subgroup G := R.map (MulAut.conj g⁻¹).toMonoidHom with hQ
  obtain ⟨hQx, hQC⟩ := map_conj_inv_le_centralizer hRK hRC hg
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) :=
    hQC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn)
  have hQn := map_conj_inv_normal (g := g) hRC hRn
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    rw [hQ, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))]
    exact hR3
  have hQx' : Q ≤ Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G) := by rwa [hxr]
  have hQn' : (Q.subgroupOf (Subgroup.centralizer ({((ψ r : ↥K) : G)} : Set G))).Normal := by
    rwa [hxr]
  have hQcent : Q ≤ Subgroup.centralizer (K : Set G) :=
    le_centralizer_of_normal_centralizer_rootElt_E7 ψ hr hr3 hQK hQx' hQn' hQ3
  exact le_centralizer_map_conj_of_map_conj_inv hQcent

end CFSG.StandardType.FrameRoute.FS81
