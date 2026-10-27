module

public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma95LN (L K : Subgroup G) : Prop :=
  L ≤ Subgroup.normalizer (K : Set G)

theorem eq_sup_theta_of_le_normalizer {L K : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (K : Set G))
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K)
    (hLsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  set Nθ : Subgroup ↥L := aschbacherSolvableCore 3 ↥L
  set H' : Subgroup ↥L := (L ⊓ K).subgroupOf L
  have hHn : H'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := L ⊓ K) (K := L) inf_le_left).mpr
      (Late.le_normalizer_inf Subgroup.le_normalizer hLN)
  let π : ↥L →* ↥L ⧸ Nθ := QuotientGroup.mk' Nθ
  haveI : (H'.map π).Normal := hHn.map _ (QuotientGroup.mk'_surjective Nθ)
  rcases hLsimple.eq_bot_or_eq_top_of_normal (H'.map π) with hbot | htop
  · exfalso
    have hle' : H' ≤ Nθ := by
      have hker : H' ≤ π.ker := (Subgroup.map_eq_bot_iff (H := H') (f := π)).mp hbot
      rwa [QuotientGroup.ker_mk'] at hker
    have hHle : L ⊓ K ≤ inSubgroup (aschbacherSolvableCore 3) L := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hle' hx, rfl⟩
    haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) :=
      (solvable_prime_complement_core_characterization (H := ↥L) (p := 3)
        Nat.prime_three).1
    haveI : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) L) := by
      let φ : ↥(aschbacherSolvableCore 3 ↥L) →*
          ↥(inSubgroup (aschbacherSolvableCore 3) L) :=
        (Subgroup.equivMapOfInjective (aschbacherSolvableCore 3 ↥L) L.subtype
          L.subtype_injective).toMonoidHom
      have hφsurj : Function.Surjective φ :=
        (Subgroup.equivMapOfInjective (aschbacherSolvableCore 3 ↥L) L.subtype
          L.subtype_injective).surjective
      exact Group.isSolvable_of_surjective hφsurj
    haveI : Group.IsSolvable ↥(L ⊓ K) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHle)
    have hKV : (L ⊓ K).subgroupOf K ⊔ CFSG.pCore 2 ↥K = ⊤ := by
      refine Subgroup.map_injective K.subtype_injective ?_
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right,
        Subgroup.map_top, Subgroup.range_subtype]
      exact hcover.symm
    haveI : Group.IsSolvable ↥((L ⊓ K).subgroupOf K) := by
      let ψ : ↥(L ⊓ K) →* ↥((L ⊓ K).subgroupOf K) :=
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom
      have hψsurj : Function.Surjective ψ :=
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.surjective
      exact Group.isSolvable_of_surjective hψsurj
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp ((L ⊓ K).subgroupOf K).subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
      have hk : k ∈ (L ⊓ K).subgroupOf K ⊔ CFSG.pCore 2 ↥K := hKV ▸ Subgroup.mem_top k
      obtain ⟨y, hy, z, hz, hyz⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := (L ⊓ K).subgroupOf K)
          (t := CFSG.pCore 2 ↥K)).mp hk
      refine ⟨⟨y, hy⟩, ?_⟩
      have hz1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) z = 1 :=
        (QuotientGroup.eq_one_iff z).mpr hz
      rw [← hyz, map_mul, hz1, mul_one]
      rfl
    haveI : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hKq.1
    haveI : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hKq
    exact Group.IsPerfect.not_isSolvable (↥K ⧸ CFSG.pCore 2 ↥K)
      (Group.isSolvable_of_surjective hsurj)
  · have hsup' : H' ⊔ Nθ = ⊤ := by
      have h := Subgroup.comap_map_eq (f := π) H'
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have h := congrArg (Subgroup.map L.subtype) hsup'
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_left : L ⊓ K ≤ L),
      Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm

theorem sup_eq_sup_theta {L K θ : Subgroup G}
    (hsplit : L = (L ⊓ K) ⊔ θ) (hθL : θ ≤ L) :
    L ⊔ K = K ⊔ θ := by
  apply le_antisymm
  · apply sup_le
    · refine hsplit.le.trans ?_
      apply sup_le
      · exact (inf_le_right (a := L) (b := K)).trans (le_sup_left (a := K) (b := θ))
      · exact le_sup_right (a := K) (b := θ)
    · exact le_sup_left (a := K) (b := θ)
  · apply sup_le
    · exact le_sup_right (a := L) (b := K)
    · exact hθL.trans (le_sup_left (a := L) (b := K))

theorem oPrimeResidualOf_le_of_eq_sup {L K θ : Subgroup G}
    (hM : L ⊔ K = K ⊔ θ)
    (hθK : θ ≤ Subgroup.normalizer (K : Set G))
    (hθcop : Nat.Coprime 3 (Nat.card ↥θ)) :
    oPrimeResidualOf 3 (L ⊔ K) ≤ K := by
  rw [Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro x ⟨hxM, k, hx3⟩
  rw [hM] at hxM
  exact Sec14.mem_left_of_pow_prime_pow Nat.prime_three hθK hθcop hxM hx3

theorem le_K_of_eq_sup_pCoreOf_two_of_a7_of_LN {A : Subgroup G} {c : G} {L K : Subgroup G}
    (h : Sec15R G A c L) (hK : K ∈ scriptY0Star A (lB A))
    (hL7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K)
    (hLN : Lemma95LN L K) :
    L ≤ K := by
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have hK3 : K = oPrimeResidualOf 3 K := hK4.2.1
  have hL3 : L = oPrimeResidualOf 3 L := Sec16.eq_oPrimeResidualOf_of_sec15R h
  have hLsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    obtain ⟨e⟩ := hL7
    exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  have hsplit : L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) L :=
    eq_sup_theta_of_le_normalizer hLN hK4.2.2.2 hcover hLsimple
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ L :=
    Subgroup.map_subtype_le _
  have hM : L ⊔ K = K ⊔ inSubgroup (aschbacherSolvableCore 3) L :=
    sup_eq_sup_theta hsplit hθL
  have hθK : inSubgroup (aschbacherSolvableCore 3) L ≤
      Subgroup.normalizer (K : Set G) := hθL.trans hLN
  obtain ⟨-, -, hθnot3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) (p := 3) Nat.prime_three
  have hθcard : Nat.card ↥(inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card ↥(aschbacherSolvableCore 3 ↥L) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ L.subtype_injective).toEquiv).symm
  have hθcop : Nat.Coprime 3 (Nat.card ↥(inSubgroup (aschbacherSolvableCore 3) L)) := by
    rw [hθcard]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr hθnot3
  have hKM : K ≤ oPrimeResidualOf 3 (L ⊔ K) :=
    hK3.le.trans (Sec15.oPrimeResidualOf_mono 3 (show K ≤ L ⊔ K from le_sup_right))
  have hLM : L ≤ oPrimeResidualOf 3 (L ⊔ K) :=
    hL3.le.trans (Sec15.oPrimeResidualOf_mono 3 (show L ≤ L ⊔ K from le_sup_left))
  have hM3 : L ⊔ K = oPrimeResidualOf 3 (L ⊔ K) :=
    le_antisymm (sup_le hLM hKM) (Sec14.oPrimeResidualOf_le_self 3 _)
  exact le_sup_left.trans (hM3.le.trans (oPrimeResidualOf_le_of_eq_sup hM hθK hθcop))

theorem le_K_of_mem_scriptY0Star_of_a7_of_LN {A : Subgroup G} {c : G} {L X K : Subgroup G}
    (h : Sec15R G A c L) (hX4 : X ∈ scriptY4 A (lB A)) (hK : K ∈ scriptY0Star A (lB A))
    (hXK : X ≤ K) (hLX : ¬ L ≤ X) (hLΔ : L ≤ delta A (lB A) L)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hL7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K)
    (hLN : Lemma95LN L K) :
    L ≤ K :=
  le_K_of_eq_sup_pCoreOf_two_of_a7_of_LN h hK hL7 hcover hLN

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
