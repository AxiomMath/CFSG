module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Centralizer

variable {Z : Type*} [Group Z]

theorem isPGroup_quotient_of_sup_eq_top {Lb Tb : Subgroup Z} [Lb.Normal] (hTb : IsPGroup 2 Tb)
    (hsup : Lb ⊔ Tb = ⊤) : IsPGroup 2 (Z ⧸ Lb) := by
  let g : Tb →* Z ⧸ Lb := (QuotientGroup.mk' Lb).comp Tb.subtype
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Lb q
    have hz : z ∈ Lb ⊔ Tb := hsup ▸ mem_top z
    obtain ⟨l, hl, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hz
    refine ⟨⟨t, ht⟩, ?_⟩
    have hl1 : (QuotientGroup.mk' Lb) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    change (QuotientGroup.mk' Lb) t = (QuotientGroup.mk' Lb) (l * t)
    rw [map_mul, hl1, one_mul]
  exact hTb.of_surjective g hgs

theorem centralizer_le_of_isPGroup_quotient [Finite Z] {Lb Tb : Subgroup Z} [Lb.Normal]
    (hTb : IsPGroup 2 Tb) (hsup : Lb ⊔ Tb = ⊤)
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) :
    centralizer (Lb : Set Z) ≤ Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := centralizer (Lb : Set Z) with hD
  have hQ2 := isPGroup_quotient_of_sup_eq_top hTb hsup
  let f : D →* Z ⧸ Lb := (QuotientGroup.mk' Lb).comp D.subtype
  have hfk : f.ker ≤ center D := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hdL : (d : Z) ∈ Lb := (QuotientGroup.eq_one_iff (d : Z)).mp hd
    rw [Subgroup.mem_center_iff]
    intro d'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp d'.2 _ hdL).symm
  have : Group.IsNilpotent (Z ⧸ Lb) := hQ2.isNilpotent
  have : Group.IsNilpotent D := Subgroup.isNilpotent_of_ker_le_center f hfk
  obtain ⟨P⟩ : Nonempty (Sylow 2 D) := Sylow.nonempty
  have : (P : Subgroup D).Characteristic := Sylow.characteristic_of_normal P inferInstance
  have hPZ : ((P : Subgroup D).map D.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hP1 := hO2 _ hPZ (P.isPGroup'.map D.subtype)
  have hPbot : (P : Subgroup D) = ⊥ := by
    rwa [Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective] at hP1
  have hodd : ¬ 2 ∣ Nat.card D := fun h2 => Sylow.ne_bot_of_dvd_card P h2 hPbot
  intro d hd
  obtain ⟨k, hk⟩ := hQ2 (f ⟨d, hd⟩)
  have h1 : orderOf (f ⟨d, hd⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (f ⟨d, hd⟩) ∣ Nat.card D :=
    (orderOf_map_dvd f _).trans (orderOf_dvd_natCard _)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hodd ((dvd_pow_self 2 hj0).trans (hj ▸ h2))
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact (QuotientGroup.eq_one_iff d).mp hj

theorem centralizer_eq_map_center {Lb : Subgroup Z} (hle : centralizer (Lb : Set Z) ≤ Lb) :
    centralizer (Lb : Set Z) = (center Lb).map Lb.subtype := by
  ext z
  constructor
  · intro hz
    refine ⟨⟨z, hle hz⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz _ l.2)
  · rintro ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hl ⟨h, hh⟩)

end Centralizer

section Kernel

variable {G : Type} [Group G]

theorem eq_bot_of_normal_of_isPGroup_two {N : Subgroup G} {Z : Type} [Group Z] (ψ : ↥N →* Z)
    (hψs : Function.Surjective ψ) (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (K : Subgroup Z) (hK : K.Normal) (hK2 : IsPGroup 2 K) : K = ⊥ := by
  have hker2 : IsPGroup 2 ψ.ker := by
    have hk : ψ.ker = CFSG.pCore 2 ↥N := by
      ext y
      rw [MonoidHom.mem_ker, hψk, CFSG.mem_openPCoreOf_iff]
    rw [hk]
    exact CFSG.pCore_isPGroup
  have hP2 : IsPGroup 2 (K.comap ψ) := hK2.comap_of_ker_isPGroup ψ hker2
  have hPle : K.comap ψ ≤ CFSG.pCore 2 ↥N := le_sSup ⟨hK.comap ψ, hP2⟩
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨n, rfl⟩ := hψs k
  exact (hψk n).mpr ((CFSG.mem_openPCoreOf_iff n).mpr (hPle hk))

end Kernel

theorem isSylowIn_map_of_surjective {G : Type} [Group G] {V T N : Subgroup G}
    (hsyl : IsSylowIn 2 T (normalizer (V : Set G))) (hTN : T ≤ N)
    (hNM : N ≤ normalizer (V : Set G)) {X : Type} [Group X] (χ : ↥N →* X)
    (hχ : Function.Surjective χ) : IsSylowIn 2 ((T.subgroupOf N).map χ) ⊤ := by
  have hT2' : IsPGroup 2 (T.subgroupOf N) :=
    hsyl.isPGroup.of_equiv (subgroupOfEquivOfLe hTN).symm
  refine ⟨le_top, hT2'.map χ, fun hd => hsyl.not_dvd_relIndex ?_⟩
  rw [Subgroup.relIndex_top_right] at hd
  have h1 : 2 ∣ T.relIndex N := hd.trans (Subgroup.index_map_dvd _ hχ)
  rw [← Subgroup.relIndex_mul_relIndex T N (normalizer (V : Set G)) hTN hNM]
  exact h1.mul_right _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914
