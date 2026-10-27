module

public import CFSG.Quasithin.Vol2.Ch12Sec8Three
public import CFSG.Quasithin.Vol2.Ch12Sec8Four
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.Background.G2L2Three
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_mulAut_le_six_of_card_four {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 4) :
    Nat.card (MulAut V) ≤ 6 ∧ Finite (MulAut V) := by
  classical
  let f : MulAut V → Equiv.Perm {v : V // v ≠ 1} := fun a =>
    Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
  have hf : Function.Injective f := by
    intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  have : Fintype V := Fintype.ofFinite V
  have hthree : Nat.card {v : V // v ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, ← Nat.card_eq_fintype_card, hV]
  refine ⟨?_, Finite.of_injective f hf⟩
  calc Nat.card (MulAut V) ≤ Nat.card (Equiv.Perm {v : V // v ≠ 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = 6 := by rw [Nat.card_perm, hthree]; rfl

variable [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

theorem normalizer_Z_eq_centralizer (h : Hyp1281Two G T M L) :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) =
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  le_antisymm (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
    (Subgroup.centralizer_le_normalizer _)

theorem isHz_centralizer (h : Hyp1281Two G T M L) :
    IsHz T M L (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  rw [← h.normalizer_Z_eq_centralizer]
  exact h.isHz_normalizer

theorem almostSpecialHyp_g1 (h : Hyp1281Two G T M L) :
    AlmostSpecialHyp (VZ T M) (quasithinOmegaOneCenter T) L T
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
  h.almostSpecialHyp h.isHz_centralizer

theorem uOfL22_le_T (h : Hyp1281Two G T M L) : uOfL22 T M ≤ T :=
  h.almostSpecialHyp_g1.G22_three.1

theorem T_le_normalizer_uOfL22 (h : Hyp1281Two G T M L) :
    T ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
  h.almostSpecialHyp_g1.G22_three.2

theorem g1_le_normalizer_uOfL22 (_h : Hyp1281Two G T M L) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (uOfL22 T M : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem VZ_le_uOfL22 (T M : Subgroup G) : VZ T M ≤ uOfL22 T M := le_conjClosure _ _

omit [Finite G] in
theorem omegaOneCenter_le_VZ (T M : Subgroup G) : quasithinOmegaOneCenter T ≤ VZ T M :=
  le_conjClosure _ _

theorem uOfL22_le_g1 (h : Hyp1281Two G T M L) :
    uOfL22 T M ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hA := h.almostSpecialHyp_g1
  refine conjClosure_le fun x hx v hv => ?_
  have hvH : v ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hA.V_le_H hv
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hvH) (Subgroup.inv_mem _ hx)

theorem commutator_mem_omegaOneCenter (h : Hyp1281Two G T M L) {x y : G}
    (hx : x ∈ uOfL22 T M) (hy : y ∈ uOfL22 T M) :
    x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T :=
  h.almostSpecialHyp_g1.G22_commutator_mem hx hy

theorem sq_mem_omegaOneCenter (h : Hyp1281Two G T M L) {x : G} (hx : x ∈ uOfL22 T M) :
    x ^ 2 ∈ quasithinOmegaOneCenter T :=
  h.almostSpecialHyp_g1.G22_sq_mem hx

theorem omegaOneCenter_le_centerOf_uOfL22 (h : Hyp1281Two G T M L) :
    quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) := by
  refine le_inf ((omegaOneCenter_le_VZ T M).trans (VZ_le_uOfL22 T M)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have := (Subgroup.mem_centralizer_iff.mp (h.uOfL22_le_g1 hu)) z hz
  exact this.symm

theorem exists_zgen (h : Hyp1281Two G T M L) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧
      ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z := by
  have hZ2 := h.card_omegaOneCenter
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : quasithinOmegaOneCenter T)).mp hZ2
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  refine ⟨z, z.2, fun he => hzZ (Subtype.ext he), fun w hw => ?_⟩
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · right
    have h1 := hy ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))
    have h2 := hy z hzZ
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_mem_VZ_not_mem (h : Hyp1281Two G T M L) :
    ∃ a ∈ VZ T M, a ∉ quasithinOmegaOneCenter T := by
  by_contra hall
  push Not at hall
  have hle : VZ T M ≤ quasithinOmegaOneCenter T := fun a ha => hall a ha
  have := Subgroup.card_le_of_le hle
  rw [h.rank_two, h.card_omegaOneCenter] at this
  omega

theorem VZ_cases (h : Hyp1281Two G T M L) {z a : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (ha : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) :
    ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = a ∨ w = z * a := by
  have hA := h.almostSpecialHyp_g1
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have hsq : z * z = 1 := by simpa [sq] using hA.sq_eq_one_of_mem_V hzV
  have ha1 : a ≠ 1 := fun he => haZ (he ▸ Subgroup.one_mem _)
  have haz : a ≠ z := fun he => haZ (he ▸ hzZ)
  have hza1 : z * a ≠ 1 := by
    intro he
    apply haZ
    have : a = z⁻¹ := by
      calc a = z⁻¹ * (z * a) := by group
        _ = z⁻¹ := by rw [he, mul_one]
    rw [this, inv_eq_of_mul_eq_one_right hsq]
    exact hzZ
  have hzaz : z * a ≠ z := fun he => ha1 (by simpa using he)
  have hzaa : z * a ≠ a := fun he => hz1 (by simpa using he)
  intro w hw
  have := eq_or_eq_or_eq_or_eq_of_card_four h.rank_two
    (a := (1 : VZ T M)) (b := ⟨z, hzV⟩) (c := ⟨a, ha⟩) (d := ⟨z * a, Subgroup.mul_mem _ hzV ha⟩)
    (fun he => hz1 (congrArg Subtype.val he).symm)
    (fun he => ha1 (congrArg Subtype.val he).symm)
    (fun he => hza1 (congrArg Subtype.val he).symm)
    (fun he => haz (congrArg Subtype.val he).symm)
    (fun he => hzaz (congrArg Subtype.val he).symm)
    (fun he => hzaa (congrArg Subtype.val he).symm) ⟨w, hw⟩
  rcases this with he | he | he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (Or.inl (congrArg Subtype.val he))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val he)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val he)))

theorem card_OTwoQuot (h : Hyp1281Two G T M L) : Nat.card (OTwoQuot (L ⊔ T)) = 6 := by
  obtain ⟨e⟩ := h.sThree
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem LT_le_normalizer_VZ (h : Hyp1281Two G T M L) :
    L ⊔ T ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (sup_le h.le h.inM.2).trans h.isTwoReducedIn.1.2.1

theorem card_autOn_LT (h : Hyp1281Two G T M L) : Nat.card (autOn (L ⊔ T) (VZ T M)) = 6 := by
  rw [card_autOn_eq_relIndex h.LT_le_normalizer_VZ, h.centralizer]
  have hsub : (pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T) = CFSG.Open.pCore 2 ↥(L ⊔ T) :=
    map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥(L ⊔ T))
  show ((pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T)).index = 6
  rw [hsub]
  exact h.card_OTwoQuot

theorem autOn_LT_eq_top (h : Hyp1281Two G T M L) : autOn (L ⊔ T) (VZ T M) = ⊤ := by
  obtain ⟨hcard, hfin⟩ := card_mulAut_le_six_of_card_four (V := ↥(VZ T M)) h.rank_two
  have h6 := h.card_autOn_LT
  have := hfin
  have hle := Subgroup.card_le_card_group (autOn (L ⊔ T) (VZ T M))
  exact Subgroup.eq_top_of_card_eq _ (by omega)

theorem lemma_12_8_3_one (h : Hyp1281Two G T M L) :
    autOn M (VZ T M) = ⊤ ∧ autOn M (VZ T M) = autOn (L ⊔ T) (VZ T M) := by
  have hle : autOn (L ⊔ T) (VZ T M) ≤ autOn M (VZ T M) :=
    autOn_le_autOn (VZ T M) (sup_le h.le h.inM.2)
  have htop : autOn M (VZ T M) = ⊤ := by
    rw [eq_top_iff]
    exact h.autOn_LT_eq_top ▸ hle
  exact ⟨htop, htop.trans h.autOn_LT_eq_top.symm⟩

theorem conj_eq_of_not_centralizes (h : Hyp1281Two G T M L) {z a x : G}
    (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T)
    (hx : x ∈ Subgroup.normalizer (VZ T M : Set G))
    (hxZ : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hxC : x ∉ Subgroup.centralizer (VZ T M : Set G)) : x * a * x⁻¹ = z * a := by
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have hxz : x * z * x⁻¹ = z := by
    have := (Subgroup.mem_centralizer_iff.mp hxZ) z hzZ
    rw [← this]
    group
  have hxaV : x * a * x⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hx a).mp haV
  have ha1 : a ≠ 1 := fun he => haZ (he ▸ Subgroup.one_mem _)
  rcases hcases _ hxaV with he | he | he | he
  · exfalso
    apply ha1
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [this, he]
    group
  · exfalso
    apply haZ
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [this, he, ← hxz]
    have e : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    rw [e]
    exact hzZ
  · exfalso
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hcases w hw with rfl | rfl | rfl | rfl
    · simp
    · have : x * w * x⁻¹ = w := hxz
      calc w * x = (x * w * x⁻¹) * x := by rw [this]
        _ = x * w := by group
    · calc w * x = (x * w * x⁻¹) * x := by rw [he]
        _ = x * w := by group
    · have h1 : x * (z * a) * x⁻¹ = z * a := by
        have : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
        rw [this, hxz, he]
      calc z * a * x = (x * (z * a) * x⁻¹) * x := by rw [h1]
        _ = x * (z * a) := by group
  · exact he

theorem inv_mul_mem_centralizer_VZ (h : Hyp1281Two G T M L) {u u' : G}
    (hu : u ∈ Subgroup.normalizer (VZ T M : Set G))
    (hu' : u' ∈ Subgroup.normalizer (VZ T M : Set G))
    (huZ : u ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hu'Z : u' ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hnu : u ∉ Subgroup.centralizer (VZ T M : Set G))
    (hnu' : u' ∉ Subgroup.centralizer (VZ T M : Set G)) :
    u⁻¹ * u' ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨z, hzZ, hz1, -⟩ := h.exists_zgen
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have hA := h.almostSpecialHyp_g1
  have hzV := omegaOneCenter_le_VZ T M hzZ
  have hsq : z * z = 1 := by simpa [sq] using hA.sq_eq_one_of_mem_V hzV
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hsq
  have e1 := h.conj_eq_of_not_centralizes hzZ hz1 haV haZ hu huZ hnu
  have e2 := h.conj_eq_of_not_centralizes hzZ hz1 haV haZ hu' hu'Z hnu'
  have huz : u⁻¹ * z * u = z := by
    have := (Subgroup.mem_centralizer_iff.mp huZ) z hzZ
    calc u⁻¹ * z * u = u⁻¹ * (z * u) := by group
      _ = u⁻¹ * (u * z) := by rw [this]
      _ = z := by group
  have hua : u⁻¹ * a * u = z * a := by
    have h1 : a = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by
      calc a = u⁻¹ * (u * a * u⁻¹) * u := by group
        _ = u⁻¹ * (z * a) * u := by rw [e1]
        _ = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by group
    rw [huz] at h1
    calc u⁻¹ * a * u = z⁻¹ * (z * (u⁻¹ * a * u)) := by group
      _ = z⁻¹ * a := by rw [← h1]
      _ = z * a := by rw [hzi]
  have hfixa : (u⁻¹ * u') * a * (u⁻¹ * u')⁻¹ = a := by
    calc (u⁻¹ * u') * a * (u⁻¹ * u')⁻¹ = u⁻¹ * (u' * a * u'⁻¹) * u := by group
      _ = u⁻¹ * (z * a) * u := by rw [e2]
      _ = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by group
      _ = z * (z * a) := by rw [huz, hua]
      _ = (z * z) * a := by group
      _ = a := by rw [hsq, one_mul]
  have hfixz : (u⁻¹ * u') * z * (u⁻¹ * u')⁻¹ = z := by
    have h1 := (Subgroup.mem_centralizer_iff.mp huZ) z hzZ
    have h2 := (Subgroup.mem_centralizer_iff.mp hu'Z) z hzZ
    calc (u⁻¹ * u') * z * (u⁻¹ * u')⁻¹ = u⁻¹ * (u' * z * u'⁻¹) * u := by group
      _ = u⁻¹ * z * u := by rw [← h2]; group
      _ = z := huz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  set c := u⁻¹ * u' with hc
  rcases hcases w hw with rfl | rfl | rfl | rfl
  · simp
  · calc w * c = (c * w * c⁻¹) * c := by rw [hfixz]
      _ = c * w := by group
  · calc w * c = (c * w * c⁻¹) * c := by rw [hfixa]
      _ = c * w := by group
  · have : c * (z * a) * c⁻¹ = z * a := by
      have : c * (z * a) * c⁻¹ = (c * z * c⁻¹) * (c * a * c⁻¹) := by group
      rw [this, hfixz, hfixa]
    calc z * a * c = (c * (z * a) * c⁻¹) * c := by rw [this]
      _ = c * (z * a) := by group

omit [Finite G] in
theorem isMulCommutative_of_le_centerOf {U : Subgroup G} (h : U ≤ centerOf U) :
    IsMulCommutative ↥U :=
  ⟨⟨fun a b => Subtype.ext (by
    have := Subgroup.mem_centralizer_iff.mp (h a.2).2 b b.2
    exact this.symm)⟩⟩

omit [Finite G] in
theorem le_centerOf_of_isMulCommutative {U : Subgroup G} (h : IsMulCommutative ↥U) :
    U ≤ centerOf U := fun x hx =>
  ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := h.is_comm.comm (⟨y, hy⟩ : U) ⟨x, hx⟩
    exact (congrArg Subtype.val this)⟩

theorem uOfL22_le_normalizer_VZ (h : Hyp1281Two G T M L) :
    uOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
  h.uOfL22_le_T.trans (h.inM.2.trans h.isTwoReducedIn.1.2.1)

theorem isMulCommutative_of_le_centralizer_VZ (h : Hyp1281Two G T M L)
    (hc : uOfL22 T M ≤ Subgroup.centralizer (VZ T M : Set G)) :
    IsMulCommutative ↥(uOfL22 T M) := by
  set U := uOfL22 T M with hUdef
  have hVZ : VZ T M ≤ centerOf U := by
    refine le_inf (VZ_le_uOfL22 T M) ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (hc hu)) v hv).symm
  have hN : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (centerOf U : Set G) :=
    (h.g1_le_normalizer_uOfL22).trans (normalizer_le_normalizer_centerOf U)
  apply isMulCommutative_of_le_centerOf
  refine conjClosure_le fun x hx v hv => ?_
  have := (Subgroup.mem_normalizer_iff.mp (hN hx) v).mp (hVZ hv)
  exact this

theorem not_le_centralizer_VZ_of_nonabelian (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    ¬ uOfL22 T M ≤ Subgroup.centralizer (VZ T M : Set G) :=
  fun hc => hU (h.isMulCommutative_of_le_centralizer_VZ hc)

theorem not_le_pCoreOf_LT_of_nonabelian (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    ¬ uOfL22 T M ≤ pCoreOf 2 (L ⊔ T) := by
  intro hle
  apply h.not_le_centralizer_VZ_of_nonabelian hU
  intro u hu
  have : u ∈ (L ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [h.centralizer]
    exact hle hu
  exact this.2

theorem lemma_12_8_8_three (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    VZ T M ⊓ centerOf (uOfL22 T M) = quasithinOmegaOneCenter T := by
  have hZle : quasithinOmegaOneCenter T ≤ VZ T M ⊓ centerOf (uOfL22 T M) :=
    le_inf (omegaOneCenter_le_VZ T M) h.omegaOneCenter_le_centerOf_uOfL22
  by_cases heq : VZ T M ⊓ centerOf (uOfL22 T M) = VZ T M
  · exfalso
    apply hU
    apply h.isMulCommutative_of_le_centralizer_VZ
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ VZ T M ⊓ centerOf (uOfL22 T M) := by rw [heq]; exact hv
    exact (Subgroup.mem_centralizer_iff.mp hv'.2.2 u hu).symm
  · have hcard := card_le_two_of_le_of_ne_of_card_four inf_le_left heq h.rank_two
    exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [h.card_omegaOneCenter]; exact hcard)).symm

theorem commutator_uOfL22_eq (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    ⁅uOfL22 T M, uOfL22 T M⁆ = quasithinOmegaOneCenter T := by
  have hle : ⁅uOfL22 T M, uOfL22 T M⁆ ≤ quasithinOmegaOneCenter T := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact h.commutator_mem_omegaOneCenter ha hb
  by_cases hbot : ⁅uOfL22 T M, uOfL22 T M⁆ = ⊥
  · exfalso
    apply hU
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a
    obtain ⟨y, hy⟩ := b
    refine Subtype.ext ?_
    show x * y = y * x
    have : ⁅x, y⁆ ∈ ⁅uOfL22 T M, uOfL22 T M⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y * x := by rw [this]; group
  · have hcard : Nat.card ↥⁅uOfL22 T M, uOfL22 T M⁆ ∣ 2 := by
      rw [← h.card_omegaOneCenter]
      exact Subgroup.card_dvd_of_le hle
    have h1 : Nat.card ↥⁅uOfL22 T M, uOfL22 T M⁆ ≠ 1 := fun h1 =>
      hbot (Subgroup.card_eq_one.mp h1)
    have h2 : Nat.card ↥⁅uOfL22 T M, uOfL22 T M⁆ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h | h
      · exact absurd h h1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h2, h.card_omegaOneCenter])

theorem frattiniOf_uOfL22 (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    frattiniOf (uOfL22 T M) = quasithinOmegaOneCenter T := by
  apply le_antisymm h.almostSpecialHyp_g1.G22_two
  calc quasithinOmegaOneCenter T = ⁅uOfL22 T M, uOfL22 T M⁆ := (h.commutator_uOfL22_eq hU).symm
    _ ≤ frattiniOf (uOfL22 T M) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Fact (IsPGroup 2 ↥(uOfL22 T M)) := ⟨h.sylow.1.to_le h.uOfL22_le_T⟩
      have hc : commutator ↥(uOfL22 T M) ≤ frattini ↥(uOfL22 T M) :=
        commutator_le_frattini_of_isPGroup (p := 2)
      have : ⁅(⟨a, ha⟩ : ↥(uOfL22 T M)), ⟨b, hb⟩⁆ ∈ frattini ↥(uOfL22 T M) :=
        hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      exact ⟨_, this, by simp [commutatorElement_def]⟩

@[expose] def wOfU (T M : Subgroup G) : Subgroup G :=
  uOfL22 T M ⊓ Subgroup.centralizer (VZ T M : Set G)

omit [Finite G] in
theorem wOfU_le_uOfL22 (T M : Subgroup G) : wOfU T M ≤ uOfL22 T M := inf_le_left

theorem VZ_le_wOfU (h : Hyp1281Two G T M L) : VZ T M ≤ wOfU T M :=
  le_inf (VZ_le_uOfL22 T M) fun _ hx => Subgroup.mem_centralizer_iff.mpr fun _ hy =>
    h.almostSpecialHyp_g1.commV hy hx

omit [Finite G] in
theorem centerOf_uOfL22_le_wOfU (T M : Subgroup G) : centerOf (uOfL22 T M) ≤ wOfU T M :=
  le_inf inf_le_left (fun _ hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2) y (VZ_le_uOfL22 T M hy))

theorem uOfL22_le_normalizer_wOfU (h : Hyp1281Two G T M L) :
    uOfL22 T M ≤ Subgroup.normalizer (wOfU T M : Set G) := by
  intro u hu
  have h1 : u ∈ Subgroup.normalizer (Subgroup.centralizer (VZ T M : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (h.uOfL22_le_normalizer_VZ hu)
  have h2 : u ∈ Subgroup.normalizer (uOfL22 T M : Set G) := Subgroup.le_normalizer hu
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h2, h1⟩

theorem T_le_normalizer_wOfU (h : Hyp1281Two G T M L) :
    T ≤ Subgroup.normalizer (wOfU T M : Set G) := by
  intro t ht
  have h1 : t ∈ Subgroup.normalizer (Subgroup.centralizer (VZ T M : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (h.inM.2.trans h.isTwoReducedIn.1.2.1 ht)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.T_le_normalizer_uOfL22 ht, h1⟩

theorem mem_wOfU_or_inv_mul_mem (h : Hyp1281Two G T M L) {u u' : G} (hu : u ∈ uOfL22 T M)
    (hu' : u' ∈ uOfL22 T M) (huW : u ∉ wOfU T M) :
    u' ∈ wOfU T M ∨ u⁻¹ * u' ∈ wOfU T M := by
  by_cases hu'W : u' ∈ wOfU T M
  · exact Or.inl hu'W
  · right
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hu', ?_⟩
    exact h.inv_mul_mem_centralizer_VZ (h.uOfL22_le_normalizer_VZ hu)
      (h.uOfL22_le_normalizer_VZ hu') (h.uOfL22_le_g1 hu) (h.uOfL22_le_g1 hu')
      (fun hc => huW ⟨hu, hc⟩) (fun hc => hu'W ⟨hu', hc⟩)

end Hyp1281Two

end CFSG.Quasithin
