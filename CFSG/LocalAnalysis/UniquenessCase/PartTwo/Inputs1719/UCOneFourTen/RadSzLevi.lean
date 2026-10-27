module

public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ClassicalGroups.PCoreSection
import CFSG.Fischer.Classification.Recognition.SymOBasic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CommutatorCentralDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup
open scoped commutatorElement

private lemma inf_eq_bot_of_pCoreOf {S : Type} [Group S] [Finite S]
    {U R N H : Subgroup S}
    (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U)
    (hP : normalizer (U : Set S) = R ⊔ N ⊔ H) (hN : IsSimpleGroup ↥N)
    (hN2 : ¬ IsPGroup 2 ↥N) : N ⊓ U = ⊥ := by
  let P : Subgroup S := normalizer (U : Set S)
  have hP' : P = R ⊔ N ⊔ H := hP
  have hNleP : N ≤ P := by
    rw [hP']
    exact le_sup_right.trans le_sup_left
  have hU2 : IsPGroup 2 (U : Subgroup S) := by
    rw [← hrad]
    exact CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 P
  have hinfNormal : ((N ⊓ U).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    constructor
    · exact N.mul_mem (N.mul_mem hk hh.1) (N.inv_mem hk)
    · exact (Subgroup.mem_normalizer_iff.mp (hNleP hk) h).mp hh.2
  have : ((N ⊓ U).subgroupOf N).Normal := hinfNormal
  rcases hN.eq_bot_or_eq_top_of_normal ((N ⊓ U).subgroupOf N) with hbot | htop
  · have hdisj : Disjoint (N ⊓ U) N := Subgroup.subgroupOf_eq_bot.mp hbot
    have hle : N ⊓ U ≤ N := inf_le_left
    simpa [inf_eq_left.mpr hle] using hdisj.eq_bot
  · exfalso
    have hle : N ≤ N ⊓ U := Subgroup.subgroupOf_eq_top.mp htop
    exact hN2 (hU2.to_le (hle.trans inf_le_right))

theorem card_eq_of_isComponentOf_sup {S : Type} [Group S] [Finite S] {U R N H : Subgroup S}
    (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U)
    (hP : normalizer (U : Set S) = R ⊔ N ⊔ H) (hRU : R ≤ U) (hN : IsSimpleGroup ↥N)
    (hN2 : ¬ IsPGroup 2 ↥N) (hNH : N ≤ centralizer (H : Set S))
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    {B : Subgroup (↥(normalizer (U : Set S)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set S)))}
    (hB : CFSG.Open.IsComponentOf B ⊤) : Nat.card B = Nat.card N := by
  classical
  let P : Subgroup S := normalizer (U : Set S)
  let V : Subgroup ↥P := CFSG.pCore 2 ↥P
  let Q := ↥P ⧸ V
  let π : ↥P →* Q := QuotientGroup.mk' V
  let Nbar : Subgroup Q := (N.subgroupOf P).map π
  let Hbar : Subgroup Q := (H.subgroupOf P).map π
  have hP' : P = R ⊔ N ⊔ H := hP
  have hRleP : R ≤ P := by
    rw [hP']
    exact le_sup_left.trans le_sup_left
  have hNleP : N ≤ P := by
    rw [hP']
    exact le_sup_right.trans le_sup_left
  have hHleP : H ≤ P := by
    rw [hP']
    exact le_sup_right
  have hVmap : V.map P.subtype = U := by
    simpa [P, V, CFSG.Open.pCoreOf] using hrad
  have hNU : N ⊓ U = ⊥ := inf_eq_bot_of_pCoreOf hrad hP hN hN2
  have hker : ∀ x : ↥(N.subgroupOf P), π x = 1 → x = 1 := by
    intro x hx
    have hxq : ((x : ↥P) : Q) = 1 := by
      rw [← QuotientGroup.mk'_apply]
      exact hx
    have hxV : (x : ↥P) ∈ V :=
      (QuotientGroup.eq_one_iff (N := V) (x : ↥P)).mp hxq
    have hxU : (x : S) ∈ U := by
      have hmem : ((x : ↥P) : S) ∈ V.map P.subtype :=
        Subgroup.mem_map_of_mem P.subtype hxV
      rwa [hVmap] at hmem
    have hxN : (x : S) ∈ N := Subgroup.mem_subgroupOf.mp x.2
    have hxbot : (x : S) ∈ (⊥ : Subgroup S) := by
      rw [← hNU]
      exact ⟨hxN, hxU⟩
    have hx1 : (x : S) = 1 := by simpa using hxbot
    exact Subtype.ext (Subtype.ext hx1)
  let ψ : ↥(N.subgroupOf P) →* Q := π.comp (N.subgroupOf P).subtype
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hker x hx
  have hrange : ψ.range = Nbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eNbarNsub : ↥(N.subgroupOf P) ≃* ↥Nbar :=
    (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)
  have eNbarN : ↥Nbar ≃* ↥N :=
    eNbarNsub.symm.trans (Subgroup.subgroupOfEquivOfLe hNleP)
  have hNbar_card : Nat.card Nbar = Nat.card N := Nat.card_congr eNbarN.toEquiv
  have hNbarSimple : IsSimpleGroup ↥Nbar :=
    (MulEquiv.isSimpleGroup_congr eNbarN).mpr hN
  have hRV : R.subgroupOf P ≤ V := by
    intro x hx
    have hxR : (x : S) ∈ R := Subgroup.mem_subgroupOf.mp hx
    have hxU : (x : S) ∈ U := hRU hxR
    have hxmap : (x : S) ∈ V.map P.subtype := by rwa [hVmap]
    obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hxmap
    have hveqx : v = x := Subtype.ext hveq
    simpa [hveqx] using hv
  have hRbot : (R.subgroupOf P).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hRV
  have hsub : (R ⊔ N ⊔ H).subgroupOf P =
      R.subgroupOf P ⊔ N.subgroupOf P ⊔ H.subgroupOf P := by
    rw [Subgroup.subgroupOf_sup (sup_le hRleP hNleP) hHleP,
      Subgroup.subgroupOf_sup hRleP hNleP]
  have hsubtop : (R ⊔ N ⊔ H).subgroupOf P = ⊤ := by
    rw [← hP']
    exact Subgroup.subgroupOf_self P
  have htop_map : (R.subgroupOf P ⊔ N.subgroupOf P ⊔ H.subgroupOf P).map π = ⊤ := by
    rw [← hsub, hsubtop, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective V)]
  have htopQ : Nbar ⊔ Hbar = ⊤ := by
    have h := htop_map
    rw [Subgroup.map_sup, Subgroup.map_sup, hRbot] at h
    simpa [Nbar, Hbar] using h
  have hNbar_le_cent_Hbar : Nbar ≤ Subgroup.centralizer (Hbar : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hy with ⟨n, hn, rfl⟩
    rcases hz with ⟨h, hh, rfl⟩
    show π h * π n = π n * π h
    rw [← map_mul, ← map_mul]
    congr 1
    have hnN : (n : S) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hhH : (h : S) ∈ H := Subgroup.mem_subgroupOf.mp hh
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hNH hnN) h hhH)
  have hHbar_le_cent_Hbar : Hbar ≤ Subgroup.centralizer (Hbar : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hy with ⟨a, ha, rfl⟩
    rcases hz with ⟨b, hb, rfl⟩
    show π b * π a = π a * π b
    rw [← map_mul, ← map_mul]
    congr 1
    have haH : (a : S) ∈ H := Subgroup.mem_subgroupOf.mp ha
    have hbH : (b : S) ∈ H := Subgroup.mem_subgroupOf.mp hb
    exact Subtype.ext (hH (a : S) haH (b : S) hbH).symm
  have hHbar_cent_sup :
      Hbar ≤ Subgroup.centralizer ((Nbar ⊔ Hbar : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le hNbar_le_cent_Hbar hHbar_le_cent_Hbar
  have hHbar_center : Hbar ≤ Subgroup.center Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Nbar ⊔ Hbar := by rw [htopQ]; trivial
    exact Subgroup.mem_centralizer_iff.mp (hHbar_cent_sup hz) g hg
  have hHbar_le_cent_Nbar : Hbar ≤ Subgroup.centralizer (Nbar : Set Q) :=
    (Subgroup.le_centralizer_iff).mp hNbar_le_cent_Hbar
  have hHbar_norm_Nbar : Hbar ≤ Subgroup.normalizer (Nbar : Set Q) :=
    hHbar_le_cent_Nbar.trans (Subgroup.centralizer_le_normalizer (Nbar : Set Q))
  have hNbar_normal : Nbar.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (by
      simpa [htopQ] using sup_le Subgroup.le_normalizer hHbar_norm_Nbar))
  have hcomm_le : commutator Q ≤ Nbar := by
    rw [show commutator Q = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ from rfl]
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨n₁, hn₁, h₁, hh₁, hg₁⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Nbar) (t := Hbar) (hs := hNbar_normal)).mp
        (by rw [htopQ]; trivial)
    obtain ⟨n₂, hn₂, h₂, hh₂, hg₂⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Nbar) (t := Hbar) (hs := hNbar_normal)).mp
        (by rw [htopQ]; trivial)
    have hc₁ : h₁ ∈ Subgroup.center Q := hHbar_center hh₁
    have hc₂ : h₂ ∈ Subgroup.center Q := hHbar_center hh₂
    have hx : g₁ = h₁ * n₁ := by
      calc g₁ = n₁ * h₁ := hg₁.symm
        _ = h₁ * n₁ := Subgroup.mem_center_iff.mp hc₁ n₁
    have hy : g₂ = h₂ * n₂ := by
      calc g₂ = n₂ * h₂ := hg₂.symm
        _ = h₂ * n₂ := Subgroup.mem_center_iff.mp hc₂ n₂
    have hcomm_eq : ⁅g₁, g₂⁆ = ⁅n₁, n₂⁆ :=
      CFSG.GorensteinWalter.commutator_eq_of_central_decomposition hx hy
        (Subgroup.mem_center_iff.mp hc₁ n₁).symm
        (Subgroup.mem_center_iff.mp hc₁ n₂).symm
        (Subgroup.mem_center_iff.mp hc₂ n₁).symm
        (Subgroup.mem_center_iff.mp hc₂ n₂).symm
        (Subgroup.mem_center_iff.mp hc₁ g₂).symm
        (Subgroup.mem_center_iff.mp hc₂ g₁).symm
    rw [hcomm_eq, commutatorElement_def]
    exact Nbar.mul_mem (Nbar.mul_mem (Nbar.mul_mem hn₁ hn₂) (Nbar.inv_mem hn₁))
      (Nbar.inv_mem hn₂)
  have hmapB : (⊤ : Subgroup ↥B).map B.subtype = B := by
    simpa using (Subgroup.map_subgroupOf_eq_of_le (H := B) (K := B) le_rfl)
  have hBcommMap : (commutator (↥B)).map B.subtype = ⁅B, B⁆ := by
    rw [show commutator (↥B) = ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ from rfl,
      Subgroup.map_commutator, hmapB]
  have hBmap : (commutator (↥B)).map B.subtype = B := by
    rw [hB.2.2.1, hmapB]
  have hB_eq_comm : B = ⁅B, B⁆ := hBmap.symm.trans hBcommMap
  have hB_le_Nbar : B ≤ Nbar := by
    rw [hB_eq_comm]
    exact (Subgroup.commutator_mono le_top le_top).trans hcomm_le
  have hB_ne_bot : B ≠ ⊥ := by
    intro hbot
    have hqnt : Nontrivial (↥B ⧸ Subgroup.center ↥B) := hB.2.2.2.toNontrivial
    have hBsub : Subsingleton ↥B := by
      rw [hbot]
      infer_instance
    have hqsub : Subsingleton (↥B ⧸ Subgroup.center ↥B) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim x y]
    obtain ⟨a, b, hab⟩ := hqnt.exists_pair_ne
    exact hab (hqsub.elim a b)
  have hBN : B ⊓ Nbar = ⊥ ∨ Nbar ≤ B :=
    CFSG.Fischer.Classification.Recognition.SymO.IsSubnormal.inf_eq_bot_or_le
      (A := B) (C := ⊤) (S := Nbar) hB.2.1 le_top hNbarSimple
  have hB_eq_Nbar : B = Nbar := by
    rcases hBN with hbot | hle
    · exfalso
      apply hB_ne_bot
      have hBinf : B ⊓ Nbar = B := inf_eq_left.mpr hB_le_Nbar
      rw [hBinf] at hbot
      exact hbot
    · exact le_antisymm hB_le_Nbar hle
  calc Nat.card B = Nat.card Nbar := by rw [hB_eq_Nbar]
    _ = Nat.card N := hNbar_card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
