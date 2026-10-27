module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34GL32
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAffine
public import CFSG.Quasithin.Background.FFC9G
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.S152SMax
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

namespace S152S

section GL32Facts

open CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.Setup.Family

theorem isInner_of_pow_three {α : MulAut GL32} (h : α ^ 3 = 1) : IsInner α := by
  by_contra hα
  have h2 : IsInner (α * α) := out_mul32 α α hα hα
  have h3 : α * α * α = 1 := by rw [← h, pow_three']
  have heq : α = (α * α)⁻¹ := eq_inv_of_mul_eq_one_right h3
  have hinv : IsInner (α * α)⁻¹ := by
    obtain ⟨k, hk⟩ := isInner_iff_conj.mp h2
    exact isInner_iff_conj.mpr ⟨k⁻¹, by rw [hk, map_inv]⟩
  have : IsInner α := by rw [heq]; exact hinv
  exact hα this

theorem isInner_of_pow_three_equiv {Y : Type} [Group Y] (e : Y ≃* GL32) {α : MulAut Y}
    (h : α ^ 3 = 1) : IsInner α :=
  isInner_of_isInner_congr e (isInner_of_pow_three (by rw [← map_pow, h, map_one]))

end GL32Facts

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_of_pow_three [Finite G] {I S L : Subgroup G} (hA3 : A3Orbits G)
    (hSQ : SQTKGroup ↥I) (hS : IsSylowTwoOf S I) (hLcomp : L ∈ cComp I) {p : G} (hp : p ∈ I)
    (hp3 : p ^ 3 = 1) : p ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hIS, horb⟩ := hA3 I S L hSQ hS hLcomp
  have hmem : ∀ q ∈ I, conjByElt q L ∈ conjSubgroupsBy S L := fun q hq => by
    rw [← hIS]
    exact ⟨q, hq, rfl⟩
  rcases horb with hn | ⟨t, htS, htn, hset, -⟩
  · obtain ⟨s, hs, hsq⟩ := hmem p hp
    have hsL : L.map (MulAut.conj s).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hn s hs)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hsq.trans hsL)
  · by_contra hpn
    have hpL : conjByElt p L ≠ L := fun h => hpn (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
    have h1 := hmem p hp
    rw [hset] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    have hpt : conjByElt p L = conjByElt t L := h1.resolve_left hpL
    have h2 := hmem (p * p) (I.mul_mem hp hp)
    rw [hset] at h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    have hmul : conjByElt (p * p) L = conjByElt p (conjByElt p L) := cjSub_mul_eq p p L
    rcases h2 with h2 | h2
    ·
      have hpp : p * p ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
      have hp4 : p = (p * p) * (p * p) := by
        calc p = p * p ^ 3 := by rw [hp3, mul_one]
          _ = (p * p) * (p * p) := by rw [pow_three']; group
      exact hpn (hp4 ▸ Subgroup.mul_mem _ hpp hpp)
    ·
      have hinj : conjByElt p L = conjByElt p (conjByElt p L) := by
        rw [← hmul, h2, hpt]
      have : conjByElt p L = L := by
        have := Subgroup.map_injective (MulAut.conj p).injective hinj
        exact this.symm
      exact hpL this

end Normalizer

section Commute

variable {G : Type} [Group G]

theorem l32_comm_of_pow_three {L : Subgroup G} (e : ↥L ≃* CFSG.QuasithinUnique.Setup.Family.GL32)
    {p z l : G} (hpN : p ∈ Subgroup.normalizer (L : Set G)) (hp3 : p ^ 3 = 1) (hl : l ∈ L)
    (hact : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) (hpz : p * z = z * p) (hl2 : l * l = 1) (hl1 : l ≠ 1)
    (hZ : ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1) : ∀ y ∈ L, p * y = y * p := by
  set α : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨p, hpN⟩ with hα
  have hαy : ∀ y : ↥L, ((α y : ↥L) : G) = p * (y : G) * p⁻¹ := fun y => rfl
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨p, hpN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hp3)
    rw [this, map_one]
  obtain ⟨x, hx⟩ := isInner_of_pow_three_equiv e hα3
  have hpx : ∀ y ∈ L, p * y * p⁻¹ = (x : G) * y * (x : G)⁻¹ := fun y hy => by
    have := congrArg Subtype.val (hx ⟨y, hy⟩)
    rw [hαy] at this
    simpa using this
  have hxL : (x : G) ∈ L := x.2
  have hxl : (x : G) * l = l * (x : G) := by
    have hzp1 : z⁻¹ * p = p * z⁻¹ := by
      calc z⁻¹ * p = z⁻¹ * (p * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * p) * z⁻¹ := by rw [hpz]
        _ = p * z⁻¹ := by group
    have hzp2 : p⁻¹ * z = z * p⁻¹ := by
      calc p⁻¹ * z = p⁻¹ * (z * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * z) * p⁻¹ := by rw [← hpz]
        _ = z * p⁻¹ := by group
    have key : ∀ w ∈ L,
        (l⁻¹ * (x : G) * l) * w * (l⁻¹ * (x : G) * l)⁻¹ = (x : G) * w * (x : G)⁻¹ := by
      intro w hw
      have hy : l * w * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hw) (L.inv_mem hl)
      have hy' : l⁻¹ * (l * w * l⁻¹) * l = w := by group
      have hactY : z⁻¹ * (l * w * l⁻¹) * z = w := by rw [hact _ hy, hy']
      have hactX := hact (x : G) hxL
      have eB : z⁻¹ * (p * (l * w * l⁻¹) * p⁻¹) * z = p * (z⁻¹ * (l * w * l⁻¹) * z) * p⁻¹ := by
        calc z⁻¹ * (p * (l * w * l⁻¹) * p⁻¹) * z
            = (z⁻¹ * p) * (l * w * l⁻¹) * (p⁻¹ * z) := by group
          _ = (p * z⁻¹) * (l * w * l⁻¹) * (z * p⁻¹) := by rw [hzp1, hzp2]
          _ = p * (z⁻¹ * (l * w * l⁻¹) * z) * p⁻¹ := by group
      have eA := hpx (l * w * l⁻¹) hy
      have eD : z⁻¹ * ((x : G) * (l * w * l⁻¹) * (x : G)⁻¹) * z =
          (l⁻¹ * (x : G) * l) * w * (l⁻¹ * (x : G) * l)⁻¹ := by
        calc z⁻¹ * ((x : G) * (l * w * l⁻¹) * (x : G)⁻¹) * z
            = (z⁻¹ * (x : G) * z) * (z⁻¹ * (l * w * l⁻¹) * z) * (z⁻¹ * (x : G) * z)⁻¹ := by group
          _ = (l⁻¹ * (x : G) * l) * w * (l⁻¹ * (x : G) * l)⁻¹ := by rw [hactX, hactY]
      have eC : p * (z⁻¹ * (l * w * l⁻¹) * z) * p⁻¹ = (x : G) * w * (x : G)⁻¹ := by
        rw [hactY]
        exact hpx w hw
      calc (l⁻¹ * (x : G) * l) * w * (l⁻¹ * (x : G) * l)⁻¹
          = z⁻¹ * ((x : G) * (l * w * l⁻¹) * (x : G)⁻¹) * z := eD.symm
        _ = z⁻¹ * (p * (l * w * l⁻¹) * p⁻¹) * z := by rw [eA]
        _ = p * (z⁻¹ * (l * w * l⁻¹) * z) * p⁻¹ := eB
        _ = (x : G) * w * (x : G)⁻¹ := eC
    have hc : (x : G)⁻¹ * l⁻¹ * (x : G) * l ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hxL) (L.inv_mem hl)) hxL) hl
    have hc1 : (x : G)⁻¹ * l⁻¹ * (x : G) * l = 1 := by
      apply hZ _ hc
      intro w hw
      have h2 : ((x : G)⁻¹ * l⁻¹ * (x : G) * l) * w * ((x : G)⁻¹ * l⁻¹ * (x : G) * l)⁻¹ = w := by
        calc ((x : G)⁻¹ * l⁻¹ * (x : G) * l) * w * ((x : G)⁻¹ * l⁻¹ * (x : G) * l)⁻¹
            = (x : G)⁻¹ * ((l⁻¹ * (x : G) * l) * w * (l⁻¹ * (x : G) * l)⁻¹) * (x : G) := by group
          _ = (x : G)⁻¹ * ((x : G) * w * (x : G)⁻¹) * (x : G) := by rw [key w hw]
          _ = w := by group
      calc w * ((x : G)⁻¹ * l⁻¹ * (x : G) * l)
          = (((x : G)⁻¹ * l⁻¹ * (x : G) * l) * w * ((x : G)⁻¹ * l⁻¹ * (x : G) * l)⁻¹) *
              ((x : G)⁻¹ * l⁻¹ * (x : G) * l) := by rw [h2]
        _ = ((x : G)⁻¹ * l⁻¹ * (x : G) * l) * w := by group
    have h1 : l⁻¹ * (x : G) * l = (x : G) := by
      calc l⁻¹ * (x : G) * l = (x : G) * ((x : G)⁻¹ * l⁻¹ * (x : G) * l) := by group
        _ = (x : G) := by rw [hc1, mul_one]
    calc (x : G) * l = l * (l⁻¹ * (x : G) * l) := by group
      _ = l * (x : G) := by rw [h1]
  have hx3 : (x : G) ^ 3 = 1 := by
    have hxx : ∀ y ∈ L, (x : G) * y * (x : G)⁻¹ ∈ L := fun y hy =>
      L.mul_mem (L.mul_mem hxL hy) (L.inv_mem hxL)
    have hcomm : ∀ y ∈ L, y * (x : G) ^ 3 = (x : G) ^ 3 * y := by
      intro y hy
      have h1 : p * (p * (p * y * p⁻¹) * p⁻¹) * p⁻¹ = p ^ 3 * y * (p ^ 3)⁻¹ := by
        rw [pow_three']; group
      rw [hp3] at h1
      have h2 : p * y * p⁻¹ = (x : G) * y * (x : G)⁻¹ := hpx y hy
      have h3 : p * ((x : G) * y * (x : G)⁻¹) * p⁻¹ =
          (x : G) * ((x : G) * y * (x : G)⁻¹) * (x : G)⁻¹ := hpx _ (hxx y hy)
      have h4 : p * ((x : G) * ((x : G) * y * (x : G)⁻¹) * (x : G)⁻¹) * p⁻¹ =
          (x : G) * ((x : G) * ((x : G) * y * (x : G)⁻¹) * (x : G)⁻¹) * (x : G)⁻¹ :=
        hpx _ (hxx _ (hxx y hy))
      rw [h2, h3, h4] at h1
      have h5 : (x : G) ^ 3 * y * ((x : G) ^ 3)⁻¹ = y := by
        calc (x : G) ^ 3 * y * ((x : G) ^ 3)⁻¹
            = (x : G) * ((x : G) * ((x : G) * y * (x : G)⁻¹) * (x : G)⁻¹) * (x : G)⁻¹ := by
              rw [pow_three']; group
          _ = 1 * y * (1 : G)⁻¹ := h1
          _ = y := by group
      calc y * (x : G) ^ 3 = ((x : G) ^ 3 * y * ((x : G) ^ 3)⁻¹) * (x : G) ^ 3 := by rw [h5]
        _ = (x : G) ^ 3 * y := by group
    exact hZ _ (L.pow_mem hxL 3) hcomm
  have hx1 : x = 1 := by
    have hb2 : e ⟨l, hl⟩ * e ⟨l, hl⟩ = 1 := by
      rw [← map_mul, show (⟨l, hl⟩ : ↥L) * ⟨l, hl⟩ = 1 from Subtype.ext hl2, map_one]
    have hb1 : e ⟨l, hl⟩ ≠ 1 := by
      intro h
      apply hl1
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    have ha3 : e x ^ 3 = 1 := by
      rw [← map_pow, show x ^ 3 = 1 from Subtype.ext hx3, map_one]
    have hab : Commute (e x) (e ⟨l, hl⟩) := by
      show e x * e ⟨l, hl⟩ = e ⟨l, hl⟩ * e x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxl
    by_contra hx1
    have ha1 : e x ≠ 1 := by
      intro h
      exact hx1 (e.injective (h.trans (map_one e).symm))
    have hoa : orderOf (e x) = 3 := orderOf_eq_prime ha3 ha1
    have hob : orderOf (e ⟨l, hl⟩) = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
    have h6 := hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hoa, hob]; norm_num)
    rw [hoa, hob] at h6
    exact CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.orderOf_ne_six_GL_three_zmod_two
      (e x * e ⟨l, hl⟩) (by rw [h6])
  intro y hy
  have := hpx y hy
  rw [hx1] at this
  simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at this
  calc p * y = (p * y * p⁻¹) * p := by group
    _ = y * p := by rw [this]

end Commute

section Final

variable {G : Type} [Group G] [Finite G]

theorem false_of_centralizes {I L P : Subgroup G} (hSQ : SQTKGroup ↥I) (hLI : L ≤ I) (hPI : P ≤ I)
    (hPL : ∀ p ∈ P, ∀ y ∈ L, p * y = y * p) (hP9 : Nat.card P = 9) (hPexp : ∀ x ∈ P, x ^ 3 = 1)
    (hc : ∃ c ∈ L, c ≠ 1 ∧ c ^ 3 = 1) (hZ : ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcL, hc1, hc3⟩ := hc
  have hPcomm : IsMulCommutative ↥P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP9]; norm_num)
  have hPbot : P ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hP9; omega
  obtain ⟨⟨x, hxP⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPbot
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hord : orderOf x = 3 := orderOf_eq_prime (hPexp x hxP) hx1
  obtain ⟨y, hyP, hyx⟩ : ∃ y ∈ P, y ∉ Subgroup.zpowers x := by
    by_contra h
    have hle : P ≤ Subgroup.zpowers x := fun y hy => by
      by_contra hn
      exact h ⟨y, hy, hn⟩
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, hP9] at this
    omega
  have hxy : Commute x y := by
    have := hPcomm.is_comm.comm ⟨x, hxP⟩ ⟨y, hyP⟩
    exact congrArg Subtype.val this
  have hcP : c ∉ P := by
    intro hcP
    exact hc1 (hZ c hcL fun w hw => (hPL c hcP w hw).symm)
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ P :=
    sup_le ((Subgroup.zpowers_le).2 hxP) ((Subgroup.zpowers_le).2 hyP)
  have h3 : 3 ≤ CFSG.Open.pRank 3 I :=
    FFC.three_le_pRank_three_of_gens (hPI hxP) (hPI hyP) (hLI hcL) hx1 (hPexp x hxP) (hPexp y hyP) hc3
      hxy (hPL x hxP c hcL) (hPL y hyP c hcL) hyx (fun h => hcP (hsup h))
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2 := hSQ.1 3 Nat.prime_three (by norm_num)
  rw [pRank_top_subtype] at hr
  omega

theorem false_of_l32 {I S Mi L P : Subgroup G} {z : G} (hA3 : A3Orbits G)
    (hSQ : SQTKGroup ↥I) (hS : IsSylowTwoOf S I) (hz2 : z ^ 2 = 1)
    (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hcomp : IsComponentIn L I) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hinn : InducesInner z L)
    (hL32 : IsPSL 3 2 1 ↥L) (hcen : Subgroup.center ↥L = ⊥)
    (hPM : P ≤ Mi) (hP9 : Nat.card P = 9) (hPexp : ∀ x ∈ P, x ^ 3 = 1) : False := by
  have hZ : ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1 := by
    intro x hx hc
    have hmem : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
    rw [hcen, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32
    (Or.inl ⟨by decide, hL32⟩)
  obtain ⟨l, hl, hact⟩ := hinn
  have hLI : L ≤ I := hcomp.1
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hl2 : l * l = 1 := by
    have hh : ∀ x ∈ L, l⁻¹ * (l⁻¹ * x * l) * l = x := by
      intro x hx
      have hx' : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
      have h1 := hact x hx
      have h2 := hact _ hx'
      have h3 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
        rw [hzi]
        calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzz]; simp
      rw [← h2, ← h1]
      exact h3
    refine hZ _ (L.mul_mem hl hl) fun y hy => ?_
    have h4 := hh y hy
    calc y * (l * l) = (l * l) * (l⁻¹ * (l⁻¹ * y * l) * l) := by group
      _ = (l * l) * y := by rw [h4]
  have hl1 : l ≠ 1 := by
    intro h1
    have hcomm : ⁅L, Subgroup.zpowers z⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h2 := hact x hx
      rw [h1, inv_one, one_mul, mul_one, mul_assoc] at h2
      have h3 : x * z = z * x := inv_mul_eq_iff_eq_mul.mp h2
      exact (Commute.zpow_left (show Commute z x from h3.symm) n).eq
    rw [hLz] at hcomm
    exact Unc25G2.isComponentIn_ne_bot hcomp hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∃ c ∈ L, c ≠ 1 ∧ c ^ 3 = 1 := by
    have h168 : Nat.card ↥L = 168 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two
    have : Fintype ↥L := Fintype.ofFinite _
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card (G := ↥L) 3
      (by rw [← Nat.card_eq_fintype_card, h168]; norm_num)
    refine ⟨c, c.2, fun h => ?_, ?_⟩
    · have hc1 : c = 1 := Subtype.ext h
      rw [hc1, orderOf_one] at hc
      omega
    · have := pow_orderOf_eq_one c
      rw [hc] at this
      exact congrArg Subtype.val this
  have hPI : P ≤ I := hPM.trans (by rw [hMi]; exact inf_le_left)
  have hPL : ∀ p ∈ P, ∀ y ∈ L, p * y = y * p := by
    intro p hp
    have hpMi : p ∈ I ⊓ Subgroup.centralizer ({z} : Set G) := hMi ▸ hPM hp
    have hpz : p * z = z * p :=
      (Subgroup.mem_centralizer_iff.1 hpMi.2 z (Set.mem_singleton z)).symm
    have hpN : p ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_pow_three hA3 hSQ hS (Id2519.mem_cComp_of_isComponentIn hcomp) hpMi.1
        (hPexp p hp)
    exact l32_comm_of_pow_three e hpN (hPexp p hp) hl hact hpz hl2 hl1 hZ
  exact false_of_centralizes hSQ hLI hPI hPL hP9 hPexp hc hZ

end Final

end S152S

end CFSG.Quasithin
