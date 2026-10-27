module


import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Exp32
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS1
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.AS

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D S : Subgroup G}

theorem comm_calc {a w t c : G} (haw : a * w = w * a) (hc : ⁅a, t⁆ = c) (hcw : c * w = w * c)
    (hct : c * t = t * c) : ⁅⁅a, w * t⁆, w * t⁆ = 1 := by
  have e1 : ⁅a, w * t⁆ = c := by
    rw [← hc, commutatorElement_def, commutatorElement_def]
    calc a * (w * t) * a⁻¹ * (w * t)⁻¹ = (a * w) * t * a⁻¹ * t⁻¹ * w⁻¹ := by group
      _ = w * (a * t * a⁻¹ * t⁻¹) * w⁻¹ := by rw [haw]; group
      _ = a * t * a⁻¹ * t⁻¹ := by
          have : (a * t * a⁻¹ * t⁻¹) * w = w * (a * t * a⁻¹ * t⁻¹) := by
            rw [← commutatorElement_def, hc]; exact hcw
          rw [← this]; group
  rw [e1, commutatorElement_def]
  have hct' : t * c⁻¹ = c⁻¹ * t := by
    calc t * c⁻¹ = c⁻¹ * (c * t) * c⁻¹ := by group
      _ = c⁻¹ * (t * c) * c⁻¹ := by rw [hct]
      _ = c⁻¹ * t := by group
  calc c * (w * t) * c⁻¹ * (w * t)⁻¹ = c * w * (t * c⁻¹) * t⁻¹ * w⁻¹ := by group
    _ = c * w * c⁻¹ * w⁻¹ := by rw [hct']; group
    _ = 1 := by rw [hcw]; group

namespace AStarCtx

variable (c : AStarCtx b J B A P D S)
include c

theorem eq_S_of_le {T : Subgroup G} (hT : IsPGroup 3 T) (hST : S ≤ T) (hTN : T ≤ Nor A) :
    T = S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, hz1⟩ := c.exists_z
  set Y : Subgroup G := Nor A ⊓ Cen (z : G) with hY
  have hTC : T ⊓ CenS A = c.As := (eq_of_sylowOf_three_le c.As_sylow hT.to_inf_left
    inf_le_right (le_inf (c.As_le_S.trans hST) c.As_le_cenS)).symm
  set C' : Subgroup ↥(Nor A) := (CenS A).subgroupOf (Nor A) with hC'
  set Y' : Subgroup ↥(Nor A) := Y.subgroupOf (Nor A) with hY'
  haveI hCn : C'.Normal := by
    rw [hC', Subgroup.normal_subgroupOf_iff (cenS_le_nor A)]
    intro x n hx hn
    exact (Subgroup.mem_normalizer_iff.mp (mem_nor_cenS hn) x).mp hx
  have hsup : C' ⊔ Y' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨n, hn⟩ -
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_nor c.pre c.odd hz hz1 hn
    have hxN : x ∈ Nor A := cenS_le_nor A hx
    have hyN : y ∈ Nor A := hy.1
    have : (⟨x * y, hn⟩ : ↥(Nor A)) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
    rw [this]
    exact Subgroup.mul_mem_sup (show (⟨x, hxN⟩ : ↥(Nor A)) ∈ C' from hx)
      (show (⟨y, hyN⟩ : ↥(Nor A)) ∈ Y' from hy)
  have hdvd : (CenS A).relIndex T ∣ Nat.card Y := by
    rw [← Subgroup.relIndex_subgroupOf hTN]
    refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
    rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_left,
      Subgroup.relIndex_subgroupOf (inf_le_left : Y ≤ Nor A)]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨R, hR⟩ := L41.exists_sylowOf_p (p := 3) Y
  have hR3 := card_le_three_of_Y c.pre hz hz1 hR.2.1 hR.1
  rw [L41.isSylowOf_card_p hR] at hR3
  have hvY : (Nat.card Y).factorization 3 ≤ 1 := by
    by_contra hcon
    have : 3 ^ 2 ≤ 3 ^ (Nat.card Y).factorization 3 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hrT : (CenS A).relIndex T ∣ 3 ^ n := hn ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, hj, hjr⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hrT
  have hj1 : j ≤ 1 := by
    have : 3 ^ j ∣ Nat.card Y := hjr ▸ hdvd
    exact ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp
      this).trans hvY
  have hr3 : (CenS A).relIndex T ≤ 3 := by
    rw [hjr]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 3 := by norm_num
  have hcard := Subgroup.relIndex_mul_card (CenS A) T
  rw [inf_comm, hTC] at hcard
  refine (Subgroup.eq_of_le_of_card_ge hST ?_).symm
  rw [c.card_S, ← hcard]
  exact Nat.mul_le_mul_right _ hr3

theorem nor_As_of_nor_S {g : G} (hg : g ∈ Nor S) : g ∈ Nor c.As := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set As' := conjBy g c.As with hAs'
  have hAs'S : As' ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (c.As_le_S hy)
  have hcomm' : ∀ x ∈ As', ∀ y ∈ As', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := c.As_comm' hx hy
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have hle : As' ≤ c.As := by
    by_contra hnle
    rcases eq_or_eq_of_card_three_mul (le_sup_left : c.As ≤ c.As ⊔ As')
      (sup_le c.As_le_S hAs'S) c.card_S with e | e
    · exact hnle (e ▸ le_sup_right)
    · set I := c.As ⊓ As' with hI
      have hcen : c.As ⊔ As' ≤ Subgroup.centralizer (I : Set G) := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · exact Subgroup.mem_centralizer_iff.mpr fun x hx => c.As_comm' hx.1 hy
        · exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm' x hx.2 y hy
      have hbI : b ∈ Subgroup.centralizer (I : Set G) := hcen (by rw [e]; exact c.b_mem_S)
      have hIB : I ≤ B ⊓ J := fun x hx =>
        mem_B0_of_cen c.pre (c.As_le_cenS hx.1) (Subgroup.mem_centralizer_iff.mp hbI x hx)
          (zpowers_isPGroup_of_mem c.As_isPGroup hx.1)
      have hI9 : Nat.card I ≤ 9 := by
        calc Nat.card I ≤ Nat.card ↥(B ⊓ J) := Subgroup.card_le_of_le hIB
          _ = 9 := by rw [c.pre.elemB0.2]; norm_num
      have hr : c.As.relIndex S = 3 := by
        have h1 := Subgroup.relIndex_mul_card c.As S
        rw [inf_of_le_left c.As_le_S, c.card_S] at h1
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
      have hr' : c.As.relIndex As' ≤ 3 :=
        hr ▸ Subgroup.relIndex_le_of_le_right hAs'S (by rw [hr]; norm_num)
      have h2 := Subgroup.relIndex_mul_card c.As As'
      have h3 : Nat.card As' ≤ 27 := by
        rw [← h2]
        calc c.As.relIndex As' * Nat.card I ≤ 3 * 9 := Nat.mul_le_mul hr' hI9
          _ = 27 := by norm_num
      have h4 : Nat.card As' = Nat.card c.As := L41.card_conjBy g c.As
      have h5 : Nat.card A ≤ Nat.card c.As := Subgroup.card_le_of_le c.A_le_As
      rw [c.pre.elemA.2] at h5
      omega
  exact L41.mem_nor_of_forall fun y hy => hle ⟨y, hy, rfl⟩

theorem nor_A_of_nor_S {g : G} (hg : g ∈ Nor S) : g ∈ Nor A := by
  have hgAs := c.nor_As_of_nor_S hg
  refine L41.mem_nor_of_forall fun a ha => ?_
  have hs : g * a * g⁻¹ ∈ c.As := (Subgroup.mem_normalizer_iff.mp hgAs a).mp (c.A_le_As ha)
  refine (c.charA hs).mp ?_
  have hb' : g⁻¹ * b * g⁻¹⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hg) b).mp
      c.b_mem_S
  have hZ : Subgroup.zpowers b ≤ Subgroup.normalizer (c.As : Set G) :=
    (Subgroup.zpowers_le).mpr c.b_nor_As
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left c.As (Subgroup.zpowers b) hZ
  have hb'' : g⁻¹ * b * g⁻¹⁻¹ ∈ ((c.As : Set G) * (Subgroup.zpowers b : Set G)) := by
    rw [← hset, ← c.S_eq]; exact hb'
  obtain ⟨w, hw, t, ht, hwt⟩ := Set.mem_mul.mp hb''
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hc : ⁅a, b ^ k⁆ ∈ B ⊓ J := by
    rw [← commutatorElement_inv]
    exact (B ⊓ J).inv_mem (c.pre.commbA ▸ Subgroup.commutator_mem_commutator
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k) ha)
  have hwC := c.As_le_cenS hw
  have key : ⁅⁅a, w * b ^ k⁆, w * b ^ k⁆ = 1 :=
    comm_calc (Subgroup.mem_centralizer_iff.mp hwC a ha) rfl
      (Subgroup.mem_centralizer_iff.mp hwC _ (B0_le_A c.pre hc))
      (comm_B c.pre hc.1 (B.zpow_mem (b_mem_B c.pre) k))
  rw [hwt] at key
  have := congrArg (MulAut.conj g) key
  rw [map_one, map_commutatorElement, map_commutatorElement] at this
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem mem_S_of_nor {g : G} (hg : g ∈ Nor S) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) :
    g ∈ S := by
  have hT : IsPGroup 3 ↥(S ⊔ Subgroup.zpowers g) :=
    c.S_isPGroup.to_sup_of_normal_left' hg3 ((Subgroup.zpowers_le).mpr hg)
  have hTN : S ⊔ Subgroup.zpowers g ≤ Nor A :=
    sup_le c.S_le_nor ((Subgroup.zpowers_le).mpr (c.nor_A_of_nor_S hg))
  have := c.eq_S_of_le hT le_sup_left hTN
  rw [← this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem S_sylow : IsSylowOf 3 S ⊤ := by
  obtain ⟨R, hR, hSR⟩ := exists_sylowOf_three_ge (Subgroup.le_normalizer : S ≤ Nor S)
    c.S_isPGroup
  have hRS : R ≤ S := fun r hr =>
    c.mem_S_of_nor (hR.1 hr) (zpowers_isPGroup_of_mem hR.2.1 hr)
  rw [le_antisymm hRS hSR] at hR
  exact isSylowOf_top_of_sylowOf_nor hR

theorem aStar : FF79AStar b D A c.As := by
  refine ⟨c.A_le_As, c.As_sylow, ⟨⟨fun x y => Subtype.ext (c.As_comm' x.2 y.2)⟩⟩, c.b_nor_As,
    c.D_nor_As, fun z hz hz1 s hs => c.z_inv_As hz hz1 hs, ?_, fun s hs => c.charA hs⟩
  rw [← c.S_eq]
  exact c.S_sylow

end AStarCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.AS

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.RankThree.PartTwo.Sec21.FF79.AS

theorem ff79AStarExists_holds : FF79AStarExists := by
  intro G _ _ b J B A P D _ _ _ hS h
  have hodd : Odd (Nat.card (CenS A)) :=
    odd_card_cenS_of_localRank h.elemA (le_of_eq hS.rank3)
  obtain ⟨S, hS1, hS2, hS3⟩ := exists_S h hodd
  exact ⟨_, (⟨h, hodd, hS1, hS2, hS3⟩ : AStarCtx b J B A P D S).aStar⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
