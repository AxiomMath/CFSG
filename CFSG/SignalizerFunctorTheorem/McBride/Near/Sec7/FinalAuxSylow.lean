module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

variable {G : Type*} [Group G]

theorem le_of_isPGroup_of_relIndex_coprime [Finite G] {r : ℕ} (hr : r.Prime) {K P : Subgroup G}
    (hPK : P ≤ K) (hPr : IsPGroup r P) (hidx : ¬ r ∣ P.relIndex K) {Q : Subgroup G}
    (hQK : Q ≤ K) (hQr : IsPGroup r Q) (hPQ : P ≤ Q) : Q ≤ P := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := hPr.exists_card_eq
  obtain ⟨m, hm⟩ := hQr.exists_card_eq
  have hK : P.relIndex K * Nat.card P = Nat.card K := by
    simpa [inf_of_le_left hPK] using Subgroup.relIndex_mul_card (H := P) (K := K)
  have hdvd : Nat.card Q ∣ Nat.card K := Subgroup.card_dvd_of_le hQK
  have hcop : Nat.Coprime (r ^ m) (P.relIndex K) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).mpr hidx)
  rw [← hK, hm, ha] at hdvd
  have hdvd' : r ^ m ∣ r ^ a := hcop.dvd_of_dvd_mul_left hdvd
  have hle : Nat.card Q ≤ Nat.card P := by
    rw [hm, ha]
    exact Nat.le_of_dvd (pow_pos hr.pos a) hdvd'
  exact (Subgroup.eq_of_le_of_card_ge hPQ hle).ge

theorem coord_mem_of_maximal [Finite G] {S : Set (Subgroup G)} {K P : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hK : IsDirectProduct S K) (hPK : P ≤ K) (hPab : IsMulCommutative P)
    (hPr : IsPGroup r P)
    (hmax : ∀ Q : Subgroup G, Q ≤ K → IsPGroup r Q → P ≤ Q → Q ≤ P)
    {J : Subgroup G} (hJ : J ∈ S) {y : G} (hy : y ∈ P) :
    ((hK.coord hJ ⟨y, hPK hy⟩ : J) : G) ∈ P := by
  let _ := hr
  set z : J := hK.coord hJ ⟨y, hPK hy⟩ with hz
  have hcomm : ∀ p' ∈ P, Commute (z : G) p' := by
    intro p' hp'
    have hp'K : p' ∈ K := hPK hp'
    have hmem : p' ∈ J ⊔ sSup (S \ {J}) := (hK.isDirectPair hJ).sup_eq ▸ hp'K
    obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute (hK.commute_sSup_diff hJ)).mp hmem
    have hcoord : ((hK.coord hJ ⟨j * l, hp'K⟩ : J) : G) = j := hK.coord_mul hJ hj hl
    have hxx : Commute (⟨y, hPK hy⟩ : K) ⟨j * l, hp'K⟩ :=
      Subtype.ext (isMulCommutative_iff_of_setLike.mp hPab y hy _ hp')
    have hzj : Commute (z : G) j := by
      rw [← hcoord]
      exact (hxx.map (hK.coord hJ)).map J.subtype
    exact hzj.mul_right (hK.commute_sSup_diff hJ _ z.2 l hl)
  have hzp : IsPGroup r (Subgroup.zpowers (z : G)) := by
    obtain ⟨n, hn⟩ := hPr ⟨y, hy⟩
    have hn' : (⟨y, hPK hy⟩ : K) ^ r ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    have h1 : z ^ r ^ n = 1 := by rw [hz, ← map_pow, hn', map_one]
    refine IsPGroup.of_card_dvd_pow (n := n) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val h1)
  have hzc : (z : G) ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun p' hp' => (hcomm p' hp').symm.eq
  have hnorm : P ≤ Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) :=
    (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hzc)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ : IsPGroup r (P ⊔ Subgroup.zpowers (z : G) : Subgroup G) :=
    hPr.to_sup_of_normal_right' hzp hnorm
  have hQK : P ⊔ Subgroup.zpowers (z : G) ≤ K :=
    sup_le hPK (Subgroup.zpowers_le.mpr (hK.le hJ z.2))
  exact hmax _ hQK hQ le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
