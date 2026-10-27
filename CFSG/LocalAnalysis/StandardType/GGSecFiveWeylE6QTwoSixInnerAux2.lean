module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInnerAux3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.USixTwo
open CFSG.RankThree.PartOne
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open Matrix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

omit [Finite G] in
private theorem exists_threeA_preimage (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K) :
    ∃ (a : ↥Bs) (ha : (a : G) ∈ L),
      piOf (K := K) θ ⟨a, ha⟩ = USixTwo.threeA hω ∧ a ≠ 1 := by
  classical
  have hmap' : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K := hmap
  have h3Amem : USixTwo.threeA hω ∈ USixTwo.torU K := USixTwo.threeA_mem_torU hω
  rw [← hmap'] at h3Amem
  obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp h3Amem
  have hlE : (l : G) ∈ Bs ⊓ L := Subgroup.mem_subgroupOf.mp hl
  let a : ↥Bs := ⟨(l : G), hlE.1⟩
  have haL : (a : G) ∈ L := hlE.2
  have hπa : piOf (K := K) θ ⟨a, haL⟩ = USixTwo.threeA hω := by
    have hsub : (⟨a, haL⟩ : ↥L) = l := Subtype.ext rfl
    rw [hsub]; exact hlπ
  refine ⟨a, haL, hπa, ?_⟩
  intro h
  have h1 : piOf (K := K) θ ⟨a, haL⟩ = 1 := by
    have hsub : (⟨a, haL⟩ : ↥L) = 1 := by
      apply Subtype.ext
      exact congrArg (fun q : ↥Bs => (q : G)) h
    rw [hsub, map_one]
  rw [hπa] at h1
  exact threeA_ne_one hK hω h1

private theorem cElem_mem_sup_ZL (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {n : ↥L} (hn : piOf (K := K) θ n = Psigma hK (Equiv.swap 0 1)) (b : ↥Bs) :
    ((cElem hNL n b : ↥L) : G) ∈ Bs ⊔ ZL (L := L) := by
  have hmap' : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K := hmap
  obtain ⟨β, hβ_mem, hβ_ind⟩ := hI (b : G)⁻¹ (Bs.inv_mem b.2)
  have hβ_ind' : ∀ l l' : L, (l' : G) = (b : G) * l * (b : G)⁻¹ →
      β (piOf (K := K) θ l) = piOf (K := K) θ l' := by
    intro l l' hl'
    exact hβ_ind l l' (by simpa using hl')
  have hβfix : ∀ u ∈ USixTwo.torU K, β u = u := by
    intro u hu
    rw [← hmap'] at hu
    obtain ⟨e, he, heπ⟩ := Subgroup.mem_map.mp hu
    have heB : (e : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp he).1
    have hcomm : (b : G) * (e : G) = (e : G) * (b : G) :=
      congrArg (fun z : ↥Bs => (z : G)) (hBs.1.is_comm.comm b ⟨(e : G), heB⟩)
    have hbe : (b : G) * (e : G) * (b : G)⁻¹ = (e : G) := by rw [hcomm]; group
    rw [← heπ]; exact hβ_ind' e e (by rw [hbe])
  obtain ⟨k, hk⟩ := pi_delta hK hω θ hmap' hBs hI hNL hn b
  have hc_eq : piOf (K := K) θ (cElem hNL n b) =
      β (piOf (K := K) θ (deltaElem hNL n b)) := by
    have hconj : ((conjBL hNL b (deltaElem hNL n b) : ↥L) : G) =
        (b : G) * ((deltaElem hNL n b : ↥L) : G) * (b : G)⁻¹ := rfl
    have hβd := hβ_ind' (deltaElem hNL n b) (conjBL hNL b (deltaElem hNL n b)) hconj
    rw [hβd]; congr 1
    apply Subtype.ext; simp only [conjBL, deltaElem_coe, cElem_coe, Subgroup.coe_mk]; group
  have hc_tor : piOf (K := K) θ (cElem hNL n b) ∈ USixTwo.torU K := by
    rw [hc_eq, hk, hβfix _ (Subgroup.pow_mem (USixTwo.torU K) (threeA_mem_torU hω) k)]
    exact Subgroup.pow_mem (USixTwo.torU K) (threeA_mem_torU hω) k
  obtain ⟨e, he, heπ⟩ := Subgroup.mem_map.mp (by rw [hmap']; exact hc_tor)
  have hker : (cElem hNL n b * e⁻¹ : ↥L) ∈ Subgroup.center L := by
    rw [← piOf_ker_aux θ, MonoidHom.mem_ker]; rw [map_mul, map_inv, heπ]; group
  have hmemZ : ((cElem hNL n b * e⁻¹ : ↥L) : G) ∈ ZL (L := L) := by
    refine (mem_ZL (L := L)).mpr ⟨(cElem hNL n b * e⁻¹ : ↥L).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg (fun z : ↥L => (z : G))
      (Subgroup.mem_center_iff.mp hker (⟨l, hl⟩ : ↥L))
  have heB : (e : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp he).1
  have hcEq : ((cElem hNL n b : ↥L) : G) =
      ((cElem hNL n b * e⁻¹ : ↥L) : G) * (e : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hcEq]
  exact (Bs ⊔ ZL (L := L)).mul_mem (Subgroup.mem_sup_right hmemZ)
    (Subgroup.mem_sup_left heB)

omit [Finite K] in
private theorem mem_normalizer_sup_ZL {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {n : ↥L}
    (hcX : ∀ b : ↥Bs, ((cElem hNL n b : ↥L) : G) ∈ Bs ⊔ ZL (L := L)) :
    (n : G) ∈ Subgroup.normalizer ((Bs ⊔ ZL (L := L) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Bs ⊔ ZL (L := L)).map (MulAut.conj (n : G)).toMonoidHom ≤
      Bs ⊔ ZL (L := L) := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro - ⟨b, hb, rfl⟩
      change (n : G) * (b : G) * (n : G)⁻¹ ∈ Bs ⊔ ZL (L := L)
      have h1 : (n : G) * b * (n : G)⁻¹ = ((cElem hNL n ⟨b, hb⟩ : ↥L) : G) * b := by
        rw [cElem_coe]; group
      rw [h1]
      exact (Bs ⊔ ZL (L := L)).mul_mem (hcX ⟨b, hb⟩) (Subgroup.mem_sup_left hb)
    · rintro - ⟨z, hz, rfl⟩
      change (n : G) * z * (n : G)⁻¹ ∈ Bs ⊔ ZL (L := L)
      have hzL : z ∈ L := ((mem_ZL (L := L)).mp hz).1
      have hmem : (n : G) * z * (n : G)⁻¹ ∈ ZL (L := L) := by
        refine (mem_ZL (L := L)).mpr ⟨L.mul_mem (L.mul_mem n.2 hzL) (L.inv_mem n.2), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hnl : (n : G)⁻¹ * l * (n : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem n.2) hl) n.2
        have hcomm : z * ((n : G)⁻¹ * l * (n : G)) =
            ((n : G)⁻¹ * l * (n : G)) * z :=
          (Subgroup.mem_centralizer_iff.mp ((mem_ZL (L := L)).mp hz).2 _ hnl).symm
        calc l * ((n : G) * z * (n : G)⁻¹)
            = (n : G) * (((n : G)⁻¹ * l * (n : G)) * z) * (n : G)⁻¹ := by group
          _ = (n : G) * (z * ((n : G)⁻¹ * l * (n : G))) * (n : G)⁻¹ := by rw [← hcomm]
          _ = ((n : G) * z * (n : G)⁻¹) * l := by group
      exact Subgroup.mem_sup_right hmem
  have hcardmap : Nat.card ↥((Bs ⊔ ZL (L := L)).map
      (MulAut.conj (n : G)).toMonoidHom) = Nat.card ↥(Bs ⊔ ZL (L := L)) :=
    Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardmap.symm)

omit [Finite K] in
private theorem sup_ZL_facts (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hcard : Nat.card Bs = 3 ^ 6)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.Coprime (Nat.card Bs) (Nat.card ↥(ZL (L := L))) ∧
      Bs ⊓ ZL (L := L) = ⊥ ∧
      Nat.card ↥(Bs ⊔ ZL (L := L)) = Nat.card Bs * Nat.card ↥(ZL (L := L)) := by
  have hBsN : Bs ≤ Subgroup.normalizer (ZL (L := L) : Set G) := le_normalizer_ZL hNL
  have hZ2' : IsPGroup 2 ↥(ZL (L := L)) := isPGroup_ZL hZ2
  obtain ⟨m, hm⟩ := isPGroup_iff_card_dvd_pow.mp hZ2'
  have hcop : Nat.Coprime (Nat.card ↥Bs) (Nat.card ↥(ZL (L := L))) := by
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hm
      ((by norm_num : Nat.Coprime 3 2).pow_left 6 |>.pow_right m)
  have hdisj : Bs ⊓ ZL (L := L) = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  refine ⟨hcop, hdisj, ?_⟩
  rw [sup_comm]
  have hdisj' : Disjoint (ZL (L := L)) Bs := Subgroup.disjoint_of_coprime_natCard hcop.symm
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (ZL (L := L)) Bs hBsN hdisj']
  exact Nat.mul_comm _ _

omit [Finite K] in
private theorem isComplement'_ZL_Bs
    (hcardX : Nat.card ↥(Bs ⊔ ZL (L := L)) =
      Nat.card Bs * Nat.card ↥(ZL (L := L)))
    (hdisjBZ : Bs ⊓ ZL (L := L) = ⊥) :
    ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).IsComplement'
      (Bs.subgroupOf (Bs ⊔ ZL (L := L))) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show ZL (L := L) ≤ Bs ⊔ ZL (L := L) from le_sup_right)).toEquiv,
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show Bs ≤ Bs ⊔ ZL (L := L) from le_sup_left)).toEquiv, hcardX]
    exact Nat.mul_comm _ _
  · rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨hyZ, hyB⟩ := Subgroup.mem_inf.mp hy
    have hyZ' : (y : G) ∈ ZL (L := L) := Subgroup.mem_subgroupOf.mp hyZ
    have hyB' : (y : G) ∈ Bs := Subgroup.mem_subgroupOf.mp hyB
    have hbot : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisjBZ]; exact Subgroup.mem_inf.mpr ⟨hyB', hyZ'⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)

omit [Finite G] [Finite K] in
private theorem K2_le_sup_ZL {Bs L : Subgroup G} {n : ↥L}
    (hnX : (n : G) ∈ Subgroup.normalizer
      ((Bs ⊔ ZL (L := L) : Subgroup G) : Set G)) :
    Bs.map (MulAut.conj (n : G)).toMonoidHom ≤ Bs ⊔ ZL (L := L) := by
  have hmapX : (Bs ⊔ ZL (L := L)).map (MulAut.conj (n : G)).toMonoidHom =
      Bs ⊔ ZL (L := L) := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnX
  rintro y hy
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hmem : (MulAut.conj (n : G)).toMonoidHom b ∈
      (Bs ⊔ ZL (L := L)).map (MulAut.conj (n : G)).toMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hb)
  rwa [hmapX] at hmem

omit [Finite K] in
private theorem isComplement'_ZL_K2
    (hcardX : Nat.card ↥(Bs ⊔ ZL (L := L)) =
      Nat.card Bs * Nat.card ↥(ZL (L := L)))
    (hdisjBZ : Bs ⊓ ZL (L := L) = ⊥)
    {n : ↥L} (hK2le : Bs.map (MulAut.conj (n : G)).toMonoidHom ≤ Bs ⊔ ZL (L := L)) :
    ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).IsComplement'
      ((Bs.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf (Bs ⊔ ZL (L := L))) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show ZL (L := L) ≤ Bs ⊔ ZL (L := L) from le_sup_right)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK2le).toEquiv,
      show Nat.card ↥(Bs.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card ↥Bs from
        Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective,
      hcardX]
    exact Nat.mul_comm _ _
  · rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨hyZ, hyK⟩ := Subgroup.mem_inf.mp hy
    have hyZ' : (y : G) ∈ ZL (L := L) := Subgroup.mem_subgroupOf.mp hyZ
    have hyK' : (y : G) ∈ Bs.map (MulAut.conj (n : G)).toMonoidHom :=
      Subgroup.mem_subgroupOf.mp hyK
    obtain ⟨b, hb, hbn⟩ := Subgroup.mem_map.mp hyK'
    have hbZ : b ∈ ZL (L := L) := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (ZL (L := L) : Set G)).inv_mem
          (le_normalizer_ZL_self n.2)) (y : G)).mp hyZ'
      have hb_eq : b = (n : G)⁻¹ * (y : G) * (n : G) := by
        rw [← hbn]
        change b = (n : G)⁻¹ * ((n : G) * (b : G) * (n : G)⁻¹) * (n : G)
        group
      rw [hb_eq]; simpa using h
    have hb1 : b = 1 := by
      have hbot : b ∈ (⊥ : Subgroup G) := by
        rw [← hdisjBZ]; exact Subgroup.mem_inf.mpr ⟨hb, hbZ⟩
      exact Subgroup.mem_bot.mp hbot
    apply Subtype.ext
    rw [← hbn, hb1]
    simp

omit [Finite K] in
private theorem exists_conj_ZL (hcard : Nat.card Bs = 3 ^ 6)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {n : ↥L}
    (hcopBZ : Nat.Coprime (Nat.card Bs) (Nat.card ↥(ZL (L := L))))
    (hcomp1 : ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).IsComplement'
      (Bs.subgroupOf (Bs ⊔ ZL (L := L))))
    (hcomp2 : ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).IsComplement'
      ((Bs.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf (Bs ⊔ ZL (L := L))))
    (hK2le : Bs.map (MulAut.conj (n : G)).toMonoidHom ≤ Bs ⊔ ZL (L := L)) :
    ∃ z : ↥(Bs ⊔ ZL (L := L)), (z : G) ∈ ZL (L := L) ∧
      (Bs.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf (Bs ⊔ ZL (L := L)) =
        (Bs.subgroupOf (Bs ⊔ ZL (L := L))).map (MulAut.conj z).toMonoidHom := by
  have hZleX : ZL (L := L) ≤ Bs ⊔ ZL (L := L) := le_sup_right
  have hBsN : Bs ≤ Subgroup.normalizer (ZL (L := L) : Set G) := le_normalizer_ZL hNL
  have hZnormalX : ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZleX]
    exact sup_le hBsN (fun z hz => Subgroup.le_normalizer hz)
  have hcommZsub : IsMulCommutative ↥((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))) :=
    ⟨⟨fun (a b : ↥((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L)))) => by
      apply Subtype.ext
      apply Subtype.ext
      have ha : ((a : ↥(Bs ⊔ ZL (L := L))) : G) ∈ ZL (L := L) :=
        Subgroup.mem_subgroupOf.mp a.2
      have hb : ((b : ↥(Bs ⊔ ZL (L := L))) : G) ∈ ZL (L := L) :=
        Subgroup.mem_subgroupOf.mp b.2
      exact congrArg (fun z : ↥(ZL (L := L)) => (z : G))
        (isMulCommutative_ZL.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)⟩⟩
  have hidx : ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).index = 3 ^ 6 := by
    rw [hcomp2.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK2le).toEquiv,
      show Nat.card ↥(Bs.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card ↥Bs from
        Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective,
      hcard]
  have hcop : Nat.Coprime (Nat.card ↥((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))))
      ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).index := by
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleX).toEquiv]
    simpa [hcard] using hcopBZ.symm
  let normalZsub : ((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))).Normal := hZnormalX
  let commZsub : IsMulCommutative ↥((ZL (L := L)).subgroupOf (Bs ⊔ ZL (L := L))) :=
    hcommZsub
  obtain ⟨z, hz⟩ := Subgroup.exists_conj_eq_of_isComplement' hcop hcomp1 hcomp2
  exact ⟨z, Subgroup.mem_subgroupOf.mp z.2, hz⟩

private theorem ZL_piOf_eq_one
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    {z0 : G} (hz0Z : z0 ∈ ZL (L := L)) (hz0L : z0 ∈ L) :
    piOf (K := K) θ ⟨z0, hz0L⟩ = 1 := by
  have hz0c : (⟨z0, hz0L⟩ : ↥L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp ((mem_ZL (L := L)).mp hz0Z).2 (l : G) l.2)
  rw [← MonoidHom.mem_ker, piOf_ker_aux θ]
  exact hz0c

omit [Finite G] [Finite K] in
private theorem conj_eq_of_subgroupOf {Bs L : Subgroup G} {n : ↥L}
    {z : ↥(Bs ⊔ ZL (L := L))}
    (hK2le : Bs.map (MulAut.conj (n : G)).toMonoidHom ≤ Bs ⊔ ZL (L := L))
    (hz : (Bs.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf (Bs ⊔ ZL (L := L)) =
      (Bs.subgroupOf (Bs ⊔ ZL (L := L))).map (MulAut.conj z).toMonoidHom) :
    Bs.map (MulAut.conj (n : G)).toMonoidHom =
      Bs.map (MulAut.conj (z : G)).toMonoidHom := by
  ext y
  constructor
  · intro hy
    have hyX : y ∈ Bs ⊔ ZL (L := L) := hK2le hy
    have hy' : (⟨y, hyX⟩ : ↥(Bs ⊔ ZL (L := L))) ∈
        (Bs.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf (Bs ⊔ ZL (L := L)) :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [hz] at hy'
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hy'
    refine Subgroup.mem_map.mpr ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, ?_⟩
    have hthis := congrArg (fun q : ↥(Bs ⊔ ZL (L := L)) => (q : G)) hwe
    show (MulAut.conj (z : G)).toMonoidHom (w : G) = y
    simpa [MulAut.conj_apply] using hthis
  · intro hy
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
    have hbX : b ∈ Bs ⊔ ZL (L := L) := Subgroup.mem_sup_left hb
    have hb' : (⟨b, hbX⟩ : ↥(Bs ⊔ ZL (L := L))) ∈
        Bs.subgroupOf (Bs ⊔ ZL (L := L)) := Subgroup.mem_subgroupOf.mpr hb
    have hmem : (MulAut.conj z).toMonoidHom ⟨b, hbX⟩ ∈
        (Bs.subgroupOf (Bs ⊔ ZL (L := L))).map (MulAut.conj z).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hb'
    rw [← hz] at hmem
    have hK2mem : (((MulAut.conj z).toMonoidHom ⟨b, hbX⟩ :
        ↥(Bs ⊔ ZL (L := L))) : G) ∈ Bs.map (MulAut.conj (n : G)).toMonoidHom :=
      Subgroup.mem_subgroupOf.mp hmem
    have heq : (((MulAut.conj z).toMonoidHom ⟨b, hbX⟩ :
        ↥(Bs ⊔ ZL (L := L))) : G) = y := by
      show ((z : ↥(Bs ⊔ ZL (L := L))) : G) * (b : G) *
          ((z : ↥(Bs ⊔ ZL (L := L))) : G)⁻¹ = y
      simpa using hby
    rwa [← heq]

omit [Finite K] in
private theorem exists_psigma_preimage_normalizing_Bs (hK : Nat.card K = 4)
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    {z0 : G} (hz0L : z0 ∈ L)
    (hpi_z : piOf (K := K) θ ⟨z0, hz0L⟩ = 1)
    {n : ↥L} (hn : piOf (K := K) θ n = Psigma hK (Equiv.swap 0 1))
    (hK2eq : Bs.map (MulAut.conj (n : G)).toMonoidHom =
      Bs.map (MulAut.conj z0).toMonoidHom) :
    ∃ n' : ↥L, piOf (K := K) θ n' = Psigma hK (Equiv.swap 0 1) ∧
      (n' : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  let n' : ↥L := ⟨z0⁻¹ * (n : G), L.mul_mem (L.inv_mem hz0L) n.2⟩
  have hn'π : piOf (K := K) θ n' = Psigma hK (Equiv.swap 0 1) := by
    have hval : n' = (⟨z0, hz0L⟩ : ↥L)⁻¹ * n := Subtype.ext (by simp [n'])
    rw [hval, map_mul, map_inv, hpi_z, inv_one, one_mul, hn]
  refine ⟨n', hn'π, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hval : (n' : G) = z0⁻¹ * (n : G) := rfl
  have hle : Bs.map (MulAut.conj (n' : G)).toMonoidHom ≤ Bs := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hnb : (n : G) * b * (n : G)⁻¹ ∈ Bs.map (MulAut.conj z0).toMonoidHom := by
      rw [← hK2eq]
      exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp hnb
    change z0 * b' * z0⁻¹ = (n : G) * b * (n : G)⁻¹ at hb'e
    have hgoal : (MulAut.conj (n' : G)).toMonoidHom b = b' := by
      show (n' : G) * (b : G) * (n' : G)⁻¹ = b'
      rw [hval]
      calc (z0⁻¹ * (n : G)) * (b : G) * (z0⁻¹ * (n : G))⁻¹
          = z0⁻¹ * ((n : G) * (b : G) * (n : G)⁻¹) * z0 := by group
        _ = z0⁻¹ * (z0 * b' * z0⁻¹) * z0 := by rw [hb'e]
        _ = b' := by group
    change (MulAut.conj (n' : G)).toMonoidHom (b : G) ∈ Bs
    rw [hgoal]
    exact hb'
  have hcardmap : Nat.card ↥(Bs.map (MulAut.conj (n' : G)).toMonoidHom) = Nat.card ↥Bs :=
    Subgroup.card_map_of_injective (MulAut.conj (n' : G)).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardmap.symm)

theorem exists_normalizing_preimage_of_card_six (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    ∃ (a : ↥Bs) (ha : (a : G) ∈ L),
      piOf (K := K) θ ⟨a, ha⟩ = USixTwo.threeA hω ∧ a ≠ 1 ∧
        ∃ n' : ↥L, piOf (K := K) θ n' = Psigma hK (Equiv.swap 0 1) ∧
          (n' : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  obtain ⟨a, haL, hπa, ha1⟩ := exists_threeA_preimage hK hω θ hmap
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  obtain ⟨n, hn⟩ := piOf_surjective θ (Psigma hK σ)
  let Z : Subgroup G := ZL (L := L)
  let X : Subgroup G := Bs ⊔ Z
  have hZle : Z ≤ L := fun z hz => ((mem_ZL (L := L)).mp hz).1
  obtain ⟨hcopBZ, hdisjBZ, hcardX⟩ := sup_ZL_facts hZ2 hcard hNL
  have hcX : ∀ b : ↥Bs, ((cElem hNL n b : ↥L) : G) ∈ X := by
    intro b
    exact cElem_mem_sup_ZL hK hω θ hmap hBs hI hNL hn b
  have hnX : (n : G) ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_sup_ZL hNL hcX
  let K2 : Subgroup G := Bs.map (MulAut.conj (n : G)).toMonoidHom
  have hcomp1 : (Z.subgroupOf X).IsComplement' (Bs.subgroupOf X) :=
    isComplement'_ZL_Bs hcardX hdisjBZ
  have hK2le : K2 ≤ X := K2_le_sup_ZL hnX
  have hcomp2 : (Z.subgroupOf X).IsComplement' (K2.subgroupOf X) :=
    isComplement'_ZL_K2 hcardX hdisjBZ hK2le
  obtain ⟨z, hz0Z, hz⟩ :=
    exists_conj_ZL hcard hNL hcopBZ hcomp1 hcomp2 hK2le
  let z0 : G := ((z : ↥X) : G)
  have hz0L : z0 ∈ L := hZle hz0Z
  have hpi_z : piOf (K := K) θ ⟨z0, hz0L⟩ = 1 := ZL_piOf_eq_one θ hz0Z hz0L
  have hK2eq : K2 = Bs.map (MulAut.conj z0).toMonoidHom :=
    conj_eq_of_subgroupOf hK2le hz
  obtain ⟨n', hn'π, hn'N⟩ :=
    exists_psigma_preimage_normalizing_Bs hK θ hz0L hpi_z hn hK2eq
  exact ⟨a, haL, hπa, ha1, n', hn'π, hn'N⟩

end CFSG.StandardType.E6QTwo

end
