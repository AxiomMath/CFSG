module

public import CFSG.RankThree.GF2n.Parrott.CentralizerCentralizerJ
public import CFSG.RankThree.GF2n.Parrott.MemJOfIndexTwo

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem omega_one_center_le (h : Tim79a.ParrottHyp z) {j : J z}
    (hj : j ∉ Subgroup.center (J z))
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    {w : ↥(H z)} (hwK : w ∈ Subgroup.centralizer (K : Set ↥(H z)))
    (hw2 : (w : G) ^ 2 = 1) :
    (w : G) ∈ Subgroup.zpowers (j : G) ⊔
      (Subgroup.center (J z)).map (J z).subtype := by
  let jH : ↥(H z) := ⟨(j : G), J_le_H j.2⟩
  have hCj_eq : centralizerJ jH = Subgroup.centralizer ({j} : Set (J z)) := by
    ext x
    rw [mem_centralizerJ_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
  have hCj_index : (centralizerJ jH).index = 2 := by
    rw [hCj_eq]
    exact index_centralizerJ_eq_two h hj
  have hZw : conjZ z w = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [conjZ_apply_coe, MulAut.one_apply]
    change (w : G) * (x : G) * (w : G)⁻¹ = (x : G)
    have hxJ : (x : G) ∈ J z := x.2.1
    let c : J z := ⟨(x : G), hxJ⟩
    have hcCenter : c ∈ Subgroup.center (J z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 (y : G) y.2)
    have hcCj : c ∈ Subgroup.centralizer ({j} : Set (J z)) :=
      Subgroup.center_le_centralizer _ hcCenter
    have hcK : Subgroup.inclusion (J_le_H (z := z)) c ∈ K :=
      hCK (Subgroup.mem_map_of_mem _ hcCj)
    have hcomm := Subgroup.mem_centralizer_iff.mp hwK _ hcK
    have hxw : (x : G) * (w : G) = (w : G) * (x : G) := congrArg Subtype.val hcomm
    rw [← hxw]
    group
  have hsq : (w : G) ^ 2 ∈ Subgroup.centralizer (J z : Set G) := by
    rw [hw2]
    exact Subgroup.one_mem _
  by_cases hwJ : (w : G) ∈ J z
  · let wJ : J z := ⟨(w : G), hwJ⟩
    have hwJ_double : wJ ∈ Subgroup.centralizer
        (Subgroup.centralizer ({j} : Set (J z))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcK : Subgroup.inclusion (J_le_H (z := z)) c ∈ K :=
        hCK (Subgroup.mem_map_of_mem _ hc)
      have hcomm := Subgroup.mem_centralizer_iff.mp hwK _ hcK
      apply Subtype.ext
      simpa [wJ] using congrArg Subtype.val hcomm
    have hwJ_sup : wJ ∈ Subgroup.zpowers j ⊔ Subgroup.center (J z) :=
      (centralizer_centralizer_eq_sup_center (z := z) h (j := j)) ▸ hwJ_double
    have hmap : (w : G) ∈
        (Subgroup.zpowers j ⊔ Subgroup.center (J z)).map (J z).subtype := by
      simpa [wJ] using Subgroup.mem_map_of_mem (J z).subtype hwJ_sup
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
  · have hCj_le_Cw : centralizerJ jH ≤ centralizerJ w := by
      intro c hc
      rw [mem_centralizerJ_iff] at hc ⊢
      have hcCj : c ∈ Subgroup.centralizer ({j} : Set (J z)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext hc
      have hcK : Subgroup.inclusion (J_le_H (z := z)) c ∈ K :=
        hCK (Subgroup.mem_map_of_mem _ hcCj)
      have hcomm := Subgroup.mem_centralizer_iff.mp hwK _ hcK
      exact congrArg Subtype.val hcomm
    have hCw_dvd : (Subgroup.centralizer ({(w : G)} : Set G)).relIndex (J z) ∣ 2 := by
      have hCw_index : (centralizerJ w).index ∣ 2 := by
        have hdiv := Subgroup.index_dvd_of_le hCj_le_Cw
        rwa [hCj_index] at hdiv
      have hCw_eq : centralizerJ w =
          (Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z) :=
        Subgroup.inf_subgroupOf_right _ _
      rw [hCw_eq] at hCw_index
      simpa [Subgroup.relIndex] using hCw_index
    have hCw_ne_one : (Subgroup.centralizer ({(w : G)} : Set G)).relIndex (J z) ≠ 1 := by
      intro h1
      have hJle : J z ≤ Subgroup.centralizer ({(w : G)} : Set G) :=
        Subgroup.relIndex_eq_one.mp h1
      have hwcent : (w : G) ∈ Subgroup.centralizer (J z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hJle hy)
      have hwcenterIn : (w : G) ∈ centerIn (J z) := by
        rw [← centralizer_J_eq_centerIn h]
        exact ⟨w.2, hwcent⟩
      exact hwJ hwcenterIn.1
    have hidx : (Subgroup.centralizer ({(w : G)} : Set G)).relIndex (J z) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hCw_dvd with h1 | h2
      · exact absurd h1 hCw_ne_one
      · exact h2
    exact absurd (mem_J_of_conjZ_eq_one_of_sq_mem_centralizer (z := z) h hZw hsq hidx) hwJ

end CFSG.RankThree.GF2n.Parrott
