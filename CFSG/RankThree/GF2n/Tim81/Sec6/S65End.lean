module

public import CFSG.RankThree.GF2n.Tim81.Sec6.S65Hat
import CFSG.RankThree.GF2n.Tim81.Sec5.I6Conic
import CFSG.RankThree.GF2n.Tim81.Sec5.I6ConicOdd
import CFSG.Timmesfeld.Bridge.Asc72BenderTorus
import CFSG.GroupTheory.AbelianCommutatorCount
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools
import CFSG.RankThree.GF2n.Tim78S45Aux

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld CFSG.Open
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}
variable {U B : Subgroup G} {α β : G}
variable {H : Subgroup G} {h₀ y₀ z₀ : G}

private theorem conj_sylowImage_eq {S₁ : Sylow 2 ↥U} {g : ↥U}
    (hg : g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U)) :
    conjSubgroup (g : G) (sylowImage U S₁) = sylowImage U S₁ := by
  have hcomp : (MulAut.conj (g : G)).toMonoidHom.comp U.subtype =
      U.subtype.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  show (sylowImage U S₁).map (MulAut.conj (g : G)).toMonoidHom = sylowImage U S₁
  rw [sylowImage, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  congr 1
  exact conjSubgroup_eq_self_iff.mpr hg

private theorem exists_frame_sylow (hS : Sec6Hyp M V)
    (hm : MinBad V U B α β) (ht : Twin M V U α H h₀ y₀ z₀) :
    ∃ S₁ : Sylow 2 ↥U, V ⊔ conjSubgroup y₀ V ≤ sylowImage U S₁ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hroot := hS.sec5.toRootHyp
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hαz0 : Commute α z₀ :=
    Subgroup.mem_centralizer_iff.mp ht.mem_ZU.2 α hm.le.2.2.1
  have hαz1 : α * z₀ ≠ 1 := by
    intro h
    apply ht.not_mem
    have hz : z₀ = α := by
      calc z₀ = α * (α * z₀) := by rw [← mul_assoc, hα2, one_mul]
        _ = α * 1 := by rw [h]
        _ = α := mul_one α
    rw [hz]
    exact hm.memα
  have hA'omega : conjSubgroup y₀ V ∈ omegaSet V :=
    Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top y₀)
  have hcommVA' : ∀ x ∈ V, ∀ y ∈ conjSubgroup y₀ V, Commute x y :=
    hroot.commute_of_commute_mem (mem_omegaSet_self V) hA'omega hm.memα ht.mem hα1 hαz1
      ((Commute.refl α).mul_right hαz0)
  have hVA'ea : IsElemAbelian 2 (V ⊔ conjSubgroup y₀ V) :=
    hroot.elem.sup_of_commute (Tim78.isElemAbelian_conjSubgroup hroot.elem y₀)
      (fun a ha b hb => (hcommVA' a ha b hb).eq)
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := ht.shape.shape
  have hcardV : Nat.card V = 2 ^ l := hw.card_V
  have hcardA' : Nat.card (conjSubgroup y₀ V) = 2 ^ l := by
    rw [card_conjSubgroup]
    exact hcardV
  have hVA'2 : IsPGroup 2 ↥(V ⊔ conjSubgroup y₀ V) := by
    refine IsPGroup.of_card (n := 2 * l) ?_
    have hcomm : ∀ v ∈ V, ∀ c ∈ conjSubgroup y₀ V, v * c = c * v :=
      fun v hv c hc => (hcommVA' v hv c hc).eq
    have hprod :=
      (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V (conjSubgroup y₀ V) hcomm).1
    have hinf : V ⊓ conjSubgroup y₀ V = ⊥ :=
      inf_conjSubgroup_eq_bot_of_isTI hroot.toHyp.ti ht.ne
    rw [hinf, Subgroup.card_bot, mul_one, hcardV, hcardA', ← pow_add] at hprod
    rw [hprod]
    congr 1
    ring
  have hVA'U : V ⊔ conjSubgroup y₀ V ≤ U := sup_le hm.le.1 ht.le
  have hVA'2' : IsPGroup 2 ↥((V ⊔ conjSubgroup y₀ V).subgroupOf U) := hVA'2.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hVA'2'.exists_le_sylow
  refine ⟨S₁, fun x hx => ?_⟩
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hVA'U hx⟩, hS₁ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem exists_frame_data (hB : OddTranspBender) (hS : Sec6Hyp M V)
    (h64 : OmegaM M V) (hm : MinBad V U B α β)
    {S₁ : Sylow 2 ↥U} (hVS₁ : V ⊔ conjSubgroup y₀ V ≤ sylowImage U S₁) :
    ∃ (g : ↥U) (Z : Subgroup (UHat U)),
      g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U) ∧ 4 ≤ Nat.card Z ∧
      (∀ x ∈ S₁, (x : G) * x = 1 → piU U x ∈ Z) ∧
      piU U ⟨α, hm.le.2.2.1⟩ ∈ Z ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ k : ℕ,
        piU U g ^ k * piU U ⟨α, hm.le.2.2.1⟩ * (piU U g ^ k)⁻¹ = z) ∧
      ∀ z ∈ Z, Commute (piU U g) z → z = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hα2 : α * α = 1 :=
    hS.sec5.toRootHyp.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hK : CFSG.BenderSuzuki.IsBenderGroup (UHat U) := hm.isBender hB hS h64
  have hsurj : Function.Surjective (piU U) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical (UBar U)) y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥U) z
    exact ⟨w, rfl⟩
  let Q : Sylow 2 (UHat U) := Sylow.mapSurjective hsurj S₁
  have hQ : (Q : Subgroup (UHat U)) = (S₁ : Subgroup ↥U).map (piU U) :=
    Sylow.coe_mapSurjective hsurj S₁
  let Z : Subgroup (UHat U) :=
    (Subgroup.center ↥(Q : Subgroup (UHat U))).map (Q : Subgroup (UHat U)).subtype
  have h4 : 4 ≤ Nat.card Z := by
    rw [show Nat.card Z = Nat.card (Subgroup.center ↥(Q : Subgroup (UHat U))) from
      Subgroup.card_map_of_injective (Q : Subgroup (UHat U)).subtype_injective]
    exact Asc72.IsBenderGroup.four_le_card_center hK Q
  have hZ : ∀ x ∈ S₁, (x : G) * x = 1 → piU U x ∈ Z := by
    intro x hx hx2
    have hxQ : piU U x ∈ (Q : Subgroup (UHat U)) := by
      rw [hQ]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hx2' : piU U x * piU U x = 1 := by
      rw [← map_mul]
      have hx2U : x * x = 1 := Subtype.ext (by simpa using hx2)
      rw [hx2U, map_one]
    have hcent := Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hxQ hx2'
    exact Subgroup.mem_map.mpr
      ⟨⟨piU U x, hxQ⟩,
        Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcent y y.2).eq.symm, rfl⟩
  have hαU_mem : (⟨α, hm.le.2.2.1⟩ : ↥U) ∈ S₁ := by
    have hα : α ∈ sylowImage U S₁ := hVS₁ (Subgroup.mem_sup_left hm.memα)
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hα
    have hx' : x = ⟨α, hm.le.2.2.1⟩ := Subtype.ext hxeq
    rwa [hx'] at hx
  have hαZ : piU U ⟨α, hm.le.2.2.1⟩ ∈ Z := hZ ⟨α, hm.le.2.2.1⟩ hαU_mem hα2
  have hα1' : piU U ⟨α, hm.le.2.2.1⟩ ≠ 1 :=
    hm.piU_ne_one hS h64 ⟨mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1, V,
      mem_omegaSet_self V, hm.le.1, hm.memα⟩
  obtain ⟨t, htN, htrans, hcent⟩ := Asc72.IsBenderGroup.exists_torus hK Q
  have htN' : t ∈ Subgroup.normalizer
      (((S₁ : Subgroup ↥U).map (piU U) : Subgroup (UHat U)) : Set (UHat U)) := by
    rw [← hQ]
    exact htN
  obtain ⟨w, hw⟩ := hsurj t
  obtain ⟨g, hgN, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Res148.exists_mem_normalizer_map_eq (piU U) S₁ htN' ⟨w, hw⟩
  refine ⟨g, Z, hgN, h4, hZ, hαZ, ?_, ?_⟩
  · intro z hz hz1
    obtain ⟨k, hk⟩ := htrans (piU U ⟨α, hm.le.2.2.1⟩) hαZ z hz hα1' hz1
    exact ⟨k, by simpa [hg] using hk⟩
  · intro z hz hcomm
    exact hcent z hz (by rwa [hg] at hcomm)

theorem MinBad.exists_frame (hB : OddTranspBender) (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) (ht : Twin M V U α H h₀ y₀ z₀) :
    ∃ (S₁ : Sylow 2 ↥U) (g : ↥U) (Z : Subgroup (UHat U)),
      V ⊔ conjSubgroup y₀ V ≤ sylowImage U S₁ ∧
      g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U) ∧ 4 ≤ Nat.card Z ∧
      (∀ x ∈ S₁, (x : G) * x = 1 → piU U x ∈ Z) ∧
      piU U ⟨α, hm.le.2.2.1⟩ ∈ Z ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ k : ℕ,
        piU U g ^ k * piU U ⟨α, hm.le.2.2.1⟩ * (piU U g ^ k)⁻¹ = z) ∧
      ∀ z ∈ Z, Commute (piU U g) z → z = 1 := by
  obtain ⟨S₁, hVS₁⟩ := exists_frame_sylow hS hm ht
  obtain ⟨g, Z, hg, h4, hZ, hαZ, htrans, hcent⟩ := exists_frame_data hB hS h64 hm hVS₁
  exact ⟨S₁, g, Z, hVS₁, hg, h4, hZ, hαZ, htrans, hcent⟩

private theorem span_points_stable
    {S₁ : Sylow 2 ↥U} {g : ↥U}
    (hg : g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U)) :
    conjSubgroup (g : G) (⨆ C ∈ ptsIn V (sylowImage U S₁), C) =
      ⨆ C ∈ ptsIn V (sylowImage U S₁), C := by
  have hgS : conjSubgroup (g : G) (sylowImage U S₁) = sylowImage U S₁ :=
    conj_sylowImage_eq hg
  have hpts_conj : ∀ C ∈ ptsIn V (sylowImage U S₁),
      conjSubgroup (g : G) C ∈ ptsIn V (sylowImage U S₁) := by
    intro C hC
    refine ⟨?_, ?_⟩
    · obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hC.1
      rw [hk, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top ((g : G) * k))
    · rw [← hgS]
      exact Subgroup.map_mono hC.2
  have hpts_conj_inv : ∀ C ∈ ptsIn V (sylowImage U S₁),
      conjSubgroup ((g : G)⁻¹) C ∈ ptsIn V (sylowImage U S₁) := by
    intro C hC
    refine ⟨?_, ?_⟩
    · obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hC.1
      rw [hk, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top ((g : G)⁻¹ * k))
    · have hgS_inv : conjSubgroup ((g : G)⁻¹) (sylowImage U S₁) = sylowImage U S₁ := by
        calc conjSubgroup ((g : G)⁻¹) (sylowImage U S₁)
            = conjSubgroup ((g : G)⁻¹) (conjSubgroup (g : G) (sylowImage U S₁)) := by
                rw [hgS]
          _ = conjSubgroup ((g : G)⁻¹ * (g : G)) (sylowImage U S₁) :=
                CGT.Timmesfeld75.conjSubgroup_conjSubgroup _ _ _
          _ = sylowImage U S₁ := by rw [inv_mul_cancel, conjSubgroup_one]
      rw [← hgS_inv]
      exact Subgroup.map_mono hC.2
  have hmap : conjSubgroup (g : G) (⨆ C ∈ ptsIn V (sylowImage U S₁), C) =
      ⨆ C ∈ ptsIn V (sylowImage U S₁), conjSubgroup (g : G) C := by
    simp only [conjSubgroup, Subgroup.map_iSup]
  rw [hmap]
  refine le_antisymm (iSup₂_le fun C hC => ?_) (iSup₂_le fun C hC => ?_)
  · exact le_iSup₂ (f := fun C (_ : C ∈ ptsIn V (sylowImage U S₁)) => C) _
      (hpts_conj C hC)
  · have h := le_iSup₂ (f := fun C (_ : C ∈ ptsIn V (sylowImage U S₁)) =>
        conjSubgroup (g : G) C) (conjSubgroup ((g : G)⁻¹) C) (hpts_conj_inv C hC)
    rwa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h

private theorem ker_restrict_piU
    {S₁ : Sylow 2 ↥U} (hR : CFSG.solvableRadical (UBar U) = ⊥) :
    Nat.card ↥(((piU U).comp
        ((⨆ C ∈ ptsIn V (sylowImage U S₁), C).subgroupOf U).subtype).ker) =
      Nat.card ↥((⨆ C ∈ ptsIn V (sylowImage U S₁), C) ⊓ ZU U) := by
  classical
  let L₁ : Subgroup G := ⨆ C ∈ ptsIn V (sylowImage U S₁), C
  let LU : Subgroup ↥U := L₁.subgroupOf U
  let f : ↥LU →* UHat U := (piU U).comp LU.subtype
  have hKmap : (f.ker.map LU.subtype).map U.subtype = L₁ ⊓ ZU U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      have hx1 : (QuotientGroup.mk' (CFSG.solvableRadical (UBar U)))
          ((QuotientGroup.mk' (Subgroup.center ↥U)) (z : ↥U)) = 1 := hz
      have hmem : (QuotientGroup.mk' (Subgroup.center ↥U)) (z : ↥U) ∈
          CFSG.solvableRadical (UBar U) := (QuotientGroup.eq_one_iff _).mp hx1
      rw [hR] at hmem
      have hxcenter : (z : ↥U) ∈ Subgroup.center ↥U := by
        rw [← QuotientGroup.eq_one_iff]
        exact Subgroup.mem_bot.mp hmem
      exact ⟨z.2, mem_center_iff_mem_ZU.mp hxcenter⟩
    · rintro ⟨hyL, hyZU⟩
      have hyU : y ∈ U := hyZU.1
      have hcenter : (⟨y, hyU⟩ : ↥U) ∈ Subgroup.center ↥U :=
        mem_center_iff_mem_ZU.mpr hyZU
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥U)) ⟨y, hyU⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hcenter
      have hz : (⟨⟨y, hyU⟩, Subgroup.mem_subgroupOf.mpr hyL⟩ : ↥LU) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        show (QuotientGroup.mk' (CFSG.solvableRadical (UBar U)))
          ((QuotientGroup.mk' (Subgroup.center ↥U)) ⟨y, hyU⟩) = 1
        rw [h1, map_one]
      refine ⟨(⟨⟨y, hyU⟩, Subgroup.mem_subgroupOf.mpr hyL⟩ : ↥LU), ?_, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨⟨y, hyU⟩, Subgroup.mem_subgroupOf.mpr hyL⟩ : ↥LU), hz, rfl⟩
  rw [← hKmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective U),
    Subgroup.card_map_of_injective (Subgroup.subtype_injective LU)]

private theorem card_span_points_le (hS : Sec6Hyp M V)
    (ht : Twin M V U α H h₀ y₀ z₀)
    {S₁ : Sylow 2 ↥U} {Z : Subgroup (UHat U)}
    (hZ : ∀ x ∈ S₁, (x : G) * x = 1 → piU U x ∈ Z)
    (hR : CFSG.solvableRadical (UBar U) = ⊥)
    (hsub : ptsIn V (sylowImage U S₁) ⊆ Tim79a.omegaOf V H) :
    Nat.card ↥(⨆ C ∈ ptsIn V (sylowImage U S₁), C) ≤
      Nat.card ↥((⨆ C ∈ ptsIn V (sylowImage U S₁), C) ⊓ ZU U) * Nat.card Z := by
  classical
  have hroot := hS.sec5.toRootHyp
  let L₁ : Subgroup G := ⨆ C ∈ ptsIn V (sylowImage U S₁), C
  have hL₁W : L₁ ≤ Tim79a.xOf V H := iSup₂_le fun C hC => Tim79a.le_xOf (hsub hC)
  have hL₁U : L₁ ≤ U := iSup₂_le fun C hC =>
    hC.2.trans (Subgroup.map_subtype_le (H := U) (K := (S₁ : Subgroup ↥U)))
  let LU : Subgroup ↥U := L₁.subgroupOf U
  let f : ↥LU →* UHat U := (piU U).comp LU.subtype
  have hCZ : ∀ C ∈ ptsIn V (sylowImage U S₁),
      C ≤ (Subgroup.comap (piU U) Z).map U.subtype := by
    intro C hC c hc
    obtain ⟨u, huS, huc⟩ := Subgroup.mem_map.mp (hC.2 hc)
    have hCL : C ≤ L₁ := le_iSup₂ (f := fun C (_ : C ∈ ptsIn V (sylowImage U S₁)) => C) C hC
    have hu2 : (u : G) * (u : G) = 1 := by
      rw [show (u : G) = c from huc]
      exact (ht.shape.isElemAbelian hroot).mul_self_eq_one (hL₁W (hCL hc))
    exact Subgroup.mem_map.mpr ⟨u, hZ u huS hu2, huc⟩
  have hL₁Z : L₁ ≤ (Subgroup.comap (piU U) Z).map U.subtype := iSup₂_le hCZ
  have hrange : f.range ≤ Z := by
    rintro y ⟨x, rfl⟩
    have hxmap : ((x : ↥U) : G) ∈ (Subgroup.comap (piU U) Z).map U.subtype :=
      hL₁Z x.2
    obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hxmap
    have hxeq : (x : ↥U) = u := Subtype.ext hueq.symm
    show piU U (x : ↥U) ∈ Z
    rw [hxeq]
    exact hu
  have hker : Nat.card f.ker = Nat.card ↥(L₁ ⊓ ZU U) :=
    ker_restrict_piU hR
  have hcardLU : Nat.card ↥LU = Nat.card L₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁U).toEquiv
  change Nat.card L₁ ≤ Nat.card ↥(L₁ ⊓ ZU U) * Nat.card Z
  calc Nat.card L₁ = Nat.card ↥LU := hcardLU.symm
    _ = Nat.card f.ker * Nat.card f.range := (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ↥(L₁ ⊓ ZU U) * Nat.card f.range := by rw [hker]
    _ ≤ Nat.card ↥(L₁ ⊓ ZU U) * Nat.card Z :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange)

theorem Twin.exists_small (hS : Sec6Hyp M V)
    (ht : Twin M V U α H h₀ y₀ z₀) {S₁ : Sylow 2 ↥U} {g : ↥U} {Z : Subgroup (UHat U)}
    (hg : g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U))
    (hZ : ∀ x ∈ S₁, (x : G) * x = 1 → piU U x ∈ Z)
    (hR : CFSG.solvableRadical (UBar U) = ⊥)
    (hsub : ptsIn V (sylowImage U S₁) ⊆ Tim79a.omegaOf V H) (hVS : V ≤ sylowImage U S₁) :
    ∃ X : Subgroup G, V ≤ X ∧ conjSubgroup (g : G) X = X ∧
      Nat.card X ≤ Nat.card V * Nat.card Z := by
  classical
  have hroot := hS.sec5.toRootHyp
  let L₁ : Subgroup G := ⨆ C ∈ ptsIn V (sylowImage U S₁), C
  have hL₁W : L₁ ≤ Tim79a.xOf V H := iSup₂_le fun C hC => Tim79a.le_xOf (hsub hC)
  have hL₁U : L₁ ≤ U := iSup₂_le fun C hC =>
    hC.2.trans (Subgroup.map_subtype_le (H := U) (K := (S₁ : Subgroup ↥U)))
  have hL₁ab : ∀ x ∈ L₁, ∀ y ∈ L₁, Commute x y := by
    intro x hx y hy
    exact congrArg Subtype.val ((ht.shape.isElemAbelian hroot).1.is_comm.comm
      ⟨x, hL₁W hx⟩ ⟨y, hL₁W hy⟩)
  have hL₁_stable : conjSubgroup (g : G) L₁ = L₁ := span_points_stable hg
  let K : Subgroup G := L₁ ⊓ ZU U
  have hKL : K ≤ L₁ := inf_le_left
  have hKcomm : ∀ x ∈ K, Commute (g : G) x :=
    fun x hx => Subgroup.mem_centralizer_iff.mp hx.2.2 (g : G) g.2
  have hVpts : V ∈ ptsIn V (sylowImage U S₁) := ⟨mem_omegaSet_self V, hVS⟩
  have hVL₁ : V ≤ L₁ := le_iSup₂ (f := fun C (_ : C ∈ ptsIn V (sylowImage U S₁)) => C) V hVpts
  have hcardL : Nat.card L₁ ≤ Nat.card K * Nat.card Z :=
    card_span_points_le hS ht hZ hR hsub
  obtain ⟨X, hVX, hgX, hcardX⟩ :=
    CFSG.GroupTheory.exists_conj_stable_card_mul_le hL₁ab hVL₁ hKL hL₁_stable hKcomm
  refine ⟨X, hVX, hgX, ?_⟩
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have h1 : Nat.card X * Nat.card K ≤ Nat.card V * (Nat.card K * Nat.card Z) :=
    hcardX.trans (Nat.mul_le_mul_left _ hcardL)
  have h2 : Nat.card X * Nat.card K ≤ (Nat.card V * Nat.card Z) * Nat.card K := by
    calc Nat.card X * Nat.card K ≤ Nat.card V * (Nat.card K * Nat.card Z) := h1
      _ = Nat.card V * Nat.card K * Nat.card Z := by rw [mul_assoc]
      _ = Nat.card V * Nat.card Z * Nat.card K := by ring
  exact Nat.le_of_mul_le_mul_right h2 hKpos

private theorem conj_pow_mem_ptsIn
    {S₁ : Sylow 2 ↥U} {g : ↥U}
    (hg : g ∈ Subgroup.normalizer ((S₁ : Subgroup ↥U) : Set ↥U))
    (hVS : V ⊔ conjSubgroup y₀ V ≤ sylowImage U S₁) :
    ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ∈ ptsIn V (sylowImage U S₁) := by
  have hV_S : V ≤ sylowImage U S₁ := le_sup_left.trans hVS
  have hgS : conjSubgroup (g : G) (sylowImage U S₁) = sylowImage U S₁ :=
    conj_sylowImage_eq hg
  intro i
  refine ⟨Tim79a.mem_omegaOf.mpr ⟨(g : G) ^ i, Subgroup.mem_top _, rfl⟩, ?_⟩
  induction i with
  | zero =>
    have h0 : conjSubgroup ((g : G) ^ 0) V = V := by
      simp [CGT.Timmesfeld75.conjSubgroup_one]
    rw [h0]
    exact hV_S
  | succ i ih =>
    have hstep : conjSubgroup ((g : G) ^ (i + 1)) V =
        conjSubgroup (g : G) (conjSubgroup ((g : G) ^ i) V) := by
      simp only [pow_succ', CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    rw [hstep]
    calc conjSubgroup (g : G) (conjSubgroup ((g : G) ^ i) V)
        ≤ conjSubgroup (g : G) (sylowImage U S₁) := Subgroup.map_mono ih
      _ = sylowImage U S₁ := hgS

private theorem odd_ncard_ptsIn (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) (ht : Twin M V U α H h₀ y₀ z₀)
    {S₁ : Sylow 2 ↥U} {g : ↥U} {k₀ : ℕ} (hnc : NoCommPair M V)
    (hVS : V ⊔ conjSubgroup y₀ V ≤ sylowImage U S₁)
    (hPmem : ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ∈ ptsIn V (sylowImage U S₁))
    (hk₀3 : 3 ≤ k₀)
    (hdist : ∀ i < k₀, ∀ j < k₀,
      conjSubgroup ((g : G) ^ i) V = conjSubgroup ((g : G) ^ j) V → i = j) :
    Odd (ptsIn V (sylowImage U S₁)).ncard := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hV_S : V ≤ sylowImage U S₁ := le_sup_left.trans hVS
  have hsub : ptsIn V (sylowImage U S₁) ⊆ Tim79a.omegaOf V H :=
    fun C hC => hm.mem_pts hS h64 hnc ht (S₁.isPGroup'.map U.subtype) hVS hC
  have hcl : ∀ C ∈ Tim79a.omegaOf V H, C ≤ (⨆ A ∈ ptsIn V (sylowImage U S₁), A) →
      C ∈ ptsIn V (sylowImage U S₁) := by
    intro C hC hle
    refine ⟨?_, ?_⟩
    · obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hC
      exact Tim79a.mem_omegaOf.mpr ⟨k, Subgroup.mem_top _, hk⟩
    · exact hle.trans (iSup₂_le fun A hA => hA.2)
  have hVmem : V ∈ ptsIn V (sylowImage U S₁) := ⟨mem_omegaSet_self V, hV_S⟩
  have h3 : 3 ≤ (ptsIn V (sylowImage U S₁)).ncard := by
    have hsub_range : ((fun i => conjSubgroup ((g : G) ^ i) V) '' {i : ℕ | i < k₀}) ⊆
        ptsIn V (sylowImage U S₁) := by
      rintro _ ⟨i, hi, rfl⟩
      exact hPmem i
    have himg : ((fun i => conjSubgroup ((g : G) ^ i) V) '' {i : ℕ | i < k₀}).ncard = k₀ := by
      rw [Set.InjOn.ncard_image]
      · have hset : {i : ℕ | i < k₀} = (Finset.range k₀ : Set ℕ) := by
          ext i
          simp
        rw [hset, Set.ncard_coe_finset, Finset.card_range]
      · intro i hi j hj hij
        exact hdist i hi j hj hij
    calc 3 ≤ k₀ := hk₀3
      _ = ((fun i => conjSubgroup ((g : G) ^ i) V) '' {i : ℕ | i < k₀}).ncard := himg.symm
      _ ≤ (ptsIn V (sylowImage U S₁)).ncard := Set.ncard_le_ncard hsub_range
  exact Sec45Shape.odd_ncard_of_closed hroot ht.shape hsub hVmem h3 hcl

private theorem card_contradiction (hroot : RootHyp M V) (hshape : Sec45Shape M V H h₀)
    {S₁ : Sylow 2 ↥U} {g : ↥U} {Z : Subgroup (UHat U)} {X : Subgroup G} {k₀ : ℕ}
    (hPleX : ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ≤ X)
    (hPmem : ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ∈ ptsIn V (sylowImage U S₁))
    (hsub : ptsIn V (sylowImage U S₁) ⊆ Tim79a.omegaOf V H)
    (hdist : ∀ i < k₀, ∀ j < k₀,
      conjSubgroup ((g : G) ^ i) V = conjSubgroup ((g : G) ^ j) V → i = j)
    (hk₀pos : 0 < k₀) (hk₀3 : 3 ≤ k₀)
    (hcardX : Nat.card X ≤ Nat.card V * Nat.card Z)
    (hcardZ : Nat.card Z ≤ k₀ + 1) : False := by
  classical
  let P : ℕ → Subgroup G := fun i => conjSubgroup ((g : G) ^ i) V
  let 𝒞 : Finset (Subgroup G) := (Finset.range k₀).image P
  have h𝒞card : 𝒞.card = k₀ := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hdist i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have hpts : ∀ C ∈ 𝒞, C ∈ Tim79a.omegaOf V H := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    exact hsub (hPmem i)
  have hV𝒞 : V ∈ 𝒞 := by
    refine Finset.mem_image.mpr ⟨0, by simp [hk₀pos], ?_⟩
    simp [P, CGT.Timmesfeld75.conjSubgroup_one]
  have hX𝒞 : ∀ C ∈ 𝒞, C ≤ X := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    exact hPleX i
  have hcount := Sec45Shape.card_add_le hroot hshape 𝒞 hpts hV𝒞 hX𝒞
  rw [h𝒞card] at hcount
  have hq : 4 ≤ Nat.card V := hroot.four_le_card
  have h1 : Nat.card V + (k₀ - 1) * (Nat.card V ^ 2 - Nat.card V) ≤
      Nat.card V * Nat.card Z := hcount.trans hcardX
  have h2 : Nat.card V * Nat.card Z ≤ Nat.card V * (k₀ + 1) :=
    Nat.mul_le_mul_left _ hcardZ
  have h3 : Nat.card V + (k₀ - 1) * (Nat.card V ^ 2 - Nat.card V) ≤
      Nat.card V * (k₀ + 1) := h1.trans h2
  have hqsub : Nat.card V ^ 2 - Nat.card V = Nat.card V * (Nat.card V - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [hqsub] at h3
  have h5 : (k₀ - 1) * (Nat.card V * (Nat.card V - 1)) ≤ Nat.card V * k₀ := by
    have h6 : Nat.card V * (k₀ + 1) = Nat.card V * k₀ + Nat.card V := by ring
    rw [h6] at h3
    omega
  have h5' : Nat.card V * ((k₀ - 1) * (Nat.card V - 1)) ≤ Nat.card V * k₀ := by
    calc Nat.card V * ((k₀ - 1) * (Nat.card V - 1))
        = (k₀ - 1) * (Nat.card V * (Nat.card V - 1)) := by ring
      _ ≤ Nat.card V * k₀ := h5
  have hqpos : 0 < Nat.card V := by omega
  have h4' : (k₀ - 1) * (Nat.card V - 1) ≤ k₀ :=
    Nat.le_of_mul_le_mul_left h5' hqpos
  have h7 : 2 * (k₀ - 1) ≤ (k₀ - 1) * (Nat.card V - 1) := by
    calc 2 * (k₀ - 1) = (k₀ - 1) * 2 := by ring
      _ ≤ (k₀ - 1) * (Nat.card V - 1) := Nat.mul_le_mul_left _ (by omega)
  have h8 : 2 * (k₀ - 1) ≤ k₀ := h7.trans h4'
  have h8' : k₀ < 3 := by omega
  exact absurd hk₀3 (not_le_of_gt h8')

theorem MinBad.false (hB : OddTranspBender) (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hnc : NoCommPair M V) (hm : MinBad V U B α β) : False := by
  classical
  have hroot := hS.sec5.toRootHyp
  obtain ⟨H, h₀, y₀, z₀, ht⟩ := hm.exists_twin hS h64
  obtain ⟨S₁, g, Z, hVS, hg, h4, hZ, -, htrans, -⟩ := hm.exists_frame hB hS h64 ht
  obtain ⟨k₀, hk₀pos, hcardZ, hdist⟩ := hm.orbit_bound hS ht (piU U) g htrans
  have hk₀3 : 3 ≤ k₀ := by omega
  have hV_S : V ≤ sylowImage U S₁ := le_sup_left.trans hVS
  have hPmem : ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ∈ ptsIn V (sylowImage U S₁) :=
    conj_pow_mem_ptsIn hg hVS
  have hsub : ptsIn V (sylowImage U S₁) ⊆ Tim79a.omegaOf V H :=
    fun C hC => hm.mem_pts hS h64 hnc ht (S₁.isPGroup'.map U.subtype) hVS hC
  have hodd : Odd (ptsIn V (sylowImage U S₁)).ncard :=
    odd_ncard_ptsIn hS h64 hm ht hnc hVS hPmem hk₀3 hdist
  have hR : CFSG.solvableRadical (UBar U) = ⊥ := hm.solvableRadical_eq_bot hS h64 hodd
  obtain ⟨X, hVX, hgX, hcardX⟩ := Twin.exists_small hS ht hg hZ hR hsub hV_S
  have hPleX : ∀ i : ℕ, conjSubgroup ((g : G) ^ i) V ≤ X := by
    intro i
    induction i with
    | zero =>
      have h0 : conjSubgroup ((g : G) ^ 0) V = V := by
        simp [CGT.Timmesfeld75.conjSubgroup_one]
      rw [h0]
      exact hVX
    | succ i ih =>
      have hstep : conjSubgroup ((g : G) ^ (i + 1)) V =
          conjSubgroup (g : G) (conjSubgroup ((g : G) ^ i) V) := by
        simp only [pow_succ', CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      rw [hstep]
      calc conjSubgroup (g : G) (conjSubgroup ((g : G) ^ i) V) ≤ conjSubgroup (g : G) X :=
            Subgroup.map_mono ih
        _ = X := hgX
  exact card_contradiction hroot ht.shape hPleX hPmem hsub hdist hk₀pos hk₀3 hcardX hcardZ

theorem Sec6Hyp.stmt65a_of (hB : OddTranspBender) (hS : Sec6Hyp M V) :
    ∀ n : ℕ, Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) → n ≤ 3 → NoCommPair M V →
      (∀ B ∈ omegaSet V, B ≤ M → B = V ∨ B ∈ sigmaSet M V) →
        Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V) := by
  intro n _hn _hn3 hnc h64
  constructor
  · intro d hd
    obtain ⟨A, hA, hdA⟩ := exists_omegaSet_of_mem_classD hd
    have hd2 : d * d = 1 := hS.sec5.toRootHyp.mul_self_of_mem hA hdA
    exact orderOf_eq_prime (by simpa [pow_two] using hd2) (classD_ne_one hd)
  · intro d hd e he
    by_contra h
    push Not at h
    obtain ⟨U, B, α, β, hm⟩ := exists_minBad hd he (fun h' => h'.elim h.1 h.2)
    exact MinBad.false hB hS h64 hnc hm

end CFSG.RankThree.GF2n.Tim81
