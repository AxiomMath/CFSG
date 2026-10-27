module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

variable {X : Type*} [Group X] [Finite X]

namespace TIConfig

variable {H V N : Subgroup X}

theorem maximal_local (h : TIConfig H V N) {D : Subgroup X} (hDH : D ≤ H) (hD1 : D ≠ ⊥)
    (hDp : IsPGroup 2 D) (hKD : NormIn H V ≤ NormIn H D) : NormIn H D ≤ NormIn H V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNY : N ≤ NormIn H D := fun n hn => hKD (h.N_le hn)
  have hND : N ≤ normalizer (D : Set X) := fun n hn => (mem_NormIn.1 (hNY hn)).2
  have hDNp : IsPGroup 2 (D ⊔ N : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hDp h.N_pgroup hND
  have hNH : N ≤ H := fun n hn => (mem_NormIn.1 (h.N_le hn)).1
  have hDNH : (D ⊔ N : Subgroup X) ≤ H := sup_le hDH hNH
  have hK_DN : ∀ k ∈ NormIn H V, k ∈ normalizer ((D ⊔ N : Subgroup X) : Set X) :=
    fun k hk => conj_sup_mem (mem_NormIn.1 (hKD hk)).2 (h.N_normal k hk)
  have hP_le : (D ⊔ N : Subgroup X) ⊓ NormIn H V ≤ N := by
    refine h.pcore_le ((D ⊔ N : Subgroup X) ⊓ NormIn H V) inf_le_right (fun k hk => ?_)
      (IsPGroup.to_inf_left hDNp)
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨hzDN, hzK⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2
      ⟨conj_mem_of_mem_normalizer (hK_DN k hk) hzDN,
        (NormIn H V).mul_mem ((NormIn H V).mul_mem hk hzK) ((NormIn H V).inv_mem hk)⟩
  have hDN : D ≤ N := by
    by_contra hnDN
    have hnle : ¬ (D ⊔ N : Subgroup X) ≤ N :=
      fun hle => hnDN (fun d hd => hle (Subgroup.mem_sup_left hd))
    obtain ⟨x, hxDN, hxnorm, hxN⟩ := exists_mem_normalizer_not_mem hDNp le_sup_right hnle
    have hxV : x ∈ normalizer (V : Set X) := by
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      have hzc : z ∈ cenIn N := by
        rw [h.cenIn_N_eq]
        exact hz
      have hxz := conj_mem_cenIn hxnorm hzc
      rwa [h.cenIn_N_eq] at hxz
    have hxK : x ∈ NormIn H V := mem_NormIn.2 ⟨hDNH hxDN, hxV⟩
    exact hxN (hP_le (Subgroup.mem_inf.2 ⟨hxDN, hxK⟩))
  have hDVN : (D ⊔ V : Subgroup X) ≤ N := sup_le hDN h.V_le_N
  have hK_DV : ∀ k ∈ NormIn H V, k ∈ normalizer ((D ⊔ V : Subgroup X) : Set X) :=
    fun k hk => conj_sup_mem (mem_NormIn.1 (hKD hk)).2 (mem_NormIn.1 hk).2
  have hVA : V ≤ cenIn (D ⊔ V : Subgroup X) := fun v hv =>
    mem_cenIn.2 ⟨Subgroup.mem_sup_right hv, fun s hs => h.VN_comm v hv s (hDVN hs)⟩
  have hAK : cenIn (D ⊔ V : Subgroup X) ≤ NormIn H V :=
    fun x hx => h.N_le (hDVN (mem_cenIn.1 hx).1)
  have hAn : ∀ k ∈ NormIn H V,
      k ∈ normalizer (cenIn (D ⊔ V : Subgroup X) : Set X) :=
    fun k hk => mem_normalizer_of_conj_mem fun z hz => conj_mem_cenIn (hK_DV k hk) hz
  have hAab : ∀ x ∈ cenIn (D ⊔ V : Subgroup X), ∀ y ∈ cenIn (D ⊔ V : Subgroup X),
      x * y = y * x :=
    fun x hx y hy => (mem_cenIn.1 hx).2 y (mem_cenIn.1 hy).1
  have hA : cenIn (D ⊔ V : Subgroup X) = V :=
    le_antisymm (h.maxAb _ hVA hAK hAn hAab).le hVA
  have hcenD : cenIn D ≤ V := by
    intro z hz
    obtain ⟨hzD, hzc⟩ := mem_cenIn.1 hz
    have hzN : z ∈ N := hDN hzD
    have hcent : (D ⊔ V : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
      refine sup_le ?_ ?_
      · intro d hd
        refine Subgroup.mem_centralizer_iff.2 ?_
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact hzc d hd
      · intro v hv
        refine Subgroup.mem_centralizer_iff.2 ?_
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact (h.VN_comm v hv z hzN).symm
    have hzA : z ∈ cenIn (D ⊔ V : Subgroup X) :=
      mem_cenIn.2 ⟨Subgroup.mem_sup_left hzD, fun s hs =>
        Subgroup.mem_centralizer_iff.1 (hcent hs) z (Set.mem_singleton z)⟩
    rw [hA] at hzA
    exact hzA
  obtain ⟨z, hzD, hz1⟩ := exists_ne_one_mem_cenIn hDp hD1
  have hzV : z ∈ V := hcenD hzD
  intro y hy
  obtain ⟨hyH, hyN⟩ := mem_NormIn.1 hy
  have hyzV : y * z * y⁻¹ ∈ V := hcenD (conj_mem_cenIn hyN hzD)
  exact mem_NormIn.2 ⟨hyH, h.ti y z hzV hz1 hyzV⟩

end TIConfig

end CFSG.RankThree.GF2n.Stroth80
