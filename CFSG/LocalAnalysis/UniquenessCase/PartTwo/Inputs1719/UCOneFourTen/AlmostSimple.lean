module

import CFSG.Blueprint.LieModelAPI
import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X]

theorem isSubnormal_mono {L W V : Subgroup X} (h : CFSG.Open.IsSubnormal L V) (hLW : L ≤ W)
    (hWV : W ≤ V) : CFSG.Open.IsSubnormal L W := by
  have h' := h.inf W
  rwa [inf_eq_left.mpr hLW, inf_eq_right.mpr hWV] at h'

theorem ne_bot_of_isSz [Finite X] {L : Subgroup X} {n : ℕ} (hSz : IsSz (Bar2 L) n) : L ≠ ⊥ := by
  intro hbot
  have hLsub : Subsingleton ↥L := by
    rw [hbot]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
  have hs : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 L) 2 n
      (CFSG.Blueprint.LieModel.suzukiModel hSz).2).2
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim x y])

theorem le_normalizer_of_le_component [Finite X] {K L : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hKs : CFSG.Open.IsSubnormal K ⊤) (hLK : L ≤ K)
    (hL : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) :
    normalizer (L : Set X) ≤ normalizer (K : Set X) := by
  have hKc : CFSG.IsComponent K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native K).mp
      ((CFSG.Assembly.isComponentOf_iff_open (L := K) (K := ⊤)).mpr ⟨le_top, hKs, hK⟩)
  intro g hg
  set f : X ≃* X := MulAut.conj g with hf
  have hmapL : L.map f.toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  set K' : Subgroup X := K.map f.toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv f hKc
  have hLK' : L ≤ K' := by rw [← hmapL]; exact Subgroup.map_mono hLK
  rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with hEq | hcomm
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq.symm
  · exfalso
    have hcent : L ≤ Subgroup.centralizer (L : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxK : x ∈ K := hLK hx
      have hyK' : y ∈ K' := hLK' hy
      have hx' : x ∈ Subgroup.centralizer (K' : Set X) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hxK
      exact (Subgroup.mem_centralizer_iff.mp hx' y hyK')
    have hbot : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    exact hL1 (by rw [← hL, hbot])

theorem eq_of_isSubnormal_of_le [Finite X] {K L : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hL : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (hs : CFSG.Open.IsSubnormal L K) : L = K := by
  have hLK : L ≤ K := hs.le
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mpr hK)
  have hKq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := ↥K)).symm hKq
  have hcomp : CFSG.IsComponent (⊤ : Subgroup ↥K) := ⟨hKq', Subgroup.IsSubnormal.top⟩
  have hsub : (L.subgroupOf K).IsSubnormal := hs.subgroupOf
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hsub with htop | hbot
  · exact le_antisymm hLK (Subgroup.subgroupOf_eq_top.mp (le_antisymm le_top htop))
  · exfalso
    have hPP : ⁅L.subgroupOf K, L.subgroupOf K⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono le_top le_rfl).trans hbot.le)
    have hLL : ⁅L, L⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map K.subtype) hPP
      rw [Subgroup.map_commutator, Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hLK] at hmap
      exact hmap
    exact hL1 (by rw [← hL, hLL])

theorem centralizer_le_of_sup_eq_top [Finite X] {K T : Subgroup X} (hO2 : CFSG.pCore 2 X = ⊥)
    (hKn : K.Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = ⊤) :
    centralizer (K : Set X) ≤ K := by
  have hKnormal : K.Normal := hKn
  set D := Subgroup.centralizer (K : Set X) with hDdef
  have hXK2 : IsPGroup 2 (X ⧸ K) := by
    refine IsPGroup.of_surjective hT ((QuotientGroup.mk' K).comp T.subtype) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ K ⊔ T := by rw [hKT]; exact Subgroup.mem_top x
    obtain ⟨k, hk, t, ht, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := K) (t := T) (hs := hKn)).mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    have hk1 : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    show (QuotientGroup.mk' K) t = (QuotientGroup.mk' K) (k * t)
    rw [map_mul, hk1, one_mul]
  have hDn : D.Normal := by rw [hDdef]; infer_instance
  have hDnil : Group.IsNilpotent ↥D := by
    have hXKnil : Group.IsNilpotent (X ⧸ K) := IsPGroup.isNilpotent hXK2
    refine Subgroup.isNilpotent_of_ker_le_center ((QuotientGroup.mk' K).comp D.subtype) ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxK : (x : X) ∈ K := (QuotientGroup.eq_one_iff (x : X)).mp hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp y.2 (x : X) hxK).symm
  have hDodd : Odd (Nat.card D) := by
    have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥D))
    have q := (Group.isNilpotent_of_finite_tfae (G := ↥D)).out 1 4
    have hPn : (P : Subgroup ↥D).Normal := q.mp hDnil 2 inferInstance P
    have hPc : (P : Subgroup ↥D).Characteristic := Sylow.characteristic_of_normal P hPn
    have hmapn : ((P : Subgroup ↥D).map D.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hmap2 : IsPGroup 2 ((P : Subgroup ↥D).map D.subtype) := P.isPGroup'.map _
    have hle : (P : Subgroup ↥D).map D.subtype ≤ CFSG.pCore 2 X :=
      CFSG.LieType.BorelTits.le_pCore 2 hmapn hmap2
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective] at hle
    exact P.ne_bot_of_dvd_card h2 hle
  intro d hd
  have hodd : Odd (orderOf d) := hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hd)
  have hq1 : QuotientGroup.mk' K d = 1 := by
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' K d)) (orderOf d) :=
      hXK2.orderOf_coprime (Nat.coprime_two_left.mpr hodd) _
    have hdvd : orderOf (QuotientGroup.mk' K d) ∣ orderOf d := orderOf_map_dvd _ d
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  exact (QuotientGroup.eq_one_iff d).mp hq1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
