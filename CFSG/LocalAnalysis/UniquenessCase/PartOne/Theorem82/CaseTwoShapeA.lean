module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShape
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFusion
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem y_not_mem_S : t.y ∉ t.d.S := fun hy =>
  t.y_not_mem_L (by simpa [t.hdL] using t.d.hS.le hy)

private theorem inf_S_zpowers_y_eq_bot : t.d.S ⊓ Subgroup.zpowers t.y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  obtain ⟨hwS, hwy⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwy
  have hk3 : t.y ^ k = t.y ^ (k % 3) :=
    zpow_eq_zpow_emod k (by change t.y ^ ((3 : ℕ) : ℤ) = 1; rw [zpow_natCast]; exact t.hy3)
  rw [hk3] at hk
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h] at hk
    rw [zpow_zero] at hk
    exact hk.symm
  · rw [h] at hk
    rw [zpow_one] at hk
    exact absurd (hk.symm ▸ hwS) t.y_not_mem_S
  · exfalso
    rw [h] at hk
    have h2S : t.y ^ (2 : ℕ) ∈ t.d.S := by
      rw [← hk] at hwS
      simpa using hwS
    have hy : (t.y ^ 2) ^ 2 = t.y := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, t.hy3, one_mul, pow_one]
    apply t.y_not_mem_S
    rw [← hy]
    exact t.d.S.pow_mem h2S 2

private theorem exists_mem_S_mul_zpowers_of_mem_inf_centralizer_y {x : G}
    (hx : x ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) :
    ∃ s ∈ t.d.S, ∃ k : ℤ, s * t.y ^ k = x := by
  have hyNorm : t.y ∈ Subgroup.normalizer (t.d.S : Set G) := by
    have h := CFSG.GroupTheory.WreathThree.mem_normalizer_base t.isWreathThree
    rwa [t.base_eq] at h
  have hnorm : Subgroup.zpowers t.y ≤ Subgroup.normalizer (t.d.S : Set G) :=
    Subgroup.zpowers_le.mpr hyNorm
  have hxP : x ∈ t.d.S ⊔ Subgroup.zpowers t.y := by
    rw [t.hPy]
    exact hx.1
  have hxmul : x ∈ (t.d.S : Set G) * (Subgroup.zpowers t.y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left t.d.S (Subgroup.zpowers t.y) hnorm]
    exact hxP
  obtain ⟨s, hs, w, hw, hsw⟩ := Set.mem_mul.mp hxmul
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨s, hs, k, by rw [hk]; exact hsw⟩

private theorem zpow_y_pow_three (k : ℤ) : (t.y ^ k) ^ 3 = 1 := by
  have hy3z : t.y ^ (3 : ℤ) = 1 := by
    change t.y ^ ((3 : ℕ) : ℤ) = 1
    rw [zpow_natCast]
    exact t.hy3
  have hk3 : t.y ^ k = t.y ^ (k % 3) := zpow_eq_zpow_emod k hy3z
  rw [hk3]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h]
    norm_num
  · rw [h]
    change (t.y ^ (1 : ℤ)) ^ 3 = 1
    rw [zpow_one]
    exact t.hy3
  · rw [h]
    change (t.y ^ (2 : ℤ)) ^ 3 = 1
    have h2 : t.y ^ (2 : ℤ) = t.y ^ (2 : ℕ) := zpow_natCast t.y 2
    rw [h2]
    have hpow : (t.y ^ (2 : ℕ)) ^ 3 = (t.y ^ 3) ^ 2 := by group
    rw [hpow, t.hy3, one_pow]

private theorem exists_mem_Z_mul_zpowers_of_mem_inf_centralizer_y {x : G}
    (hx : x ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ z₀ ∈ t.Z, ∃ k : ℤ, z₀ * t.y ^ k = x := by
  obtain ⟨s, hs, k, hsk⟩ := t.exists_mem_S_mul_zpowers_of_mem_inf_centralizer_y hx
  have hxK : Commute x t.y := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hsy : Commute s t.y := by
    have hs_eq : s = x * (t.y ^ k)⁻¹ := by
      rw [← hsk]
      group
    rw [hs_eq]
    exact (hxK.mul_left (((Commute.refl t.y).zpow_left k).inv_left)).eq
  have hsw : Commute s (t.y ^ k) := hsy.zpow_right k
  have hs3 : s ^ 3 = 1 := by
    have h1 : x ^ 3 = s ^ 3 * (t.y ^ k) ^ 3 := by
      rw [← hsk]
      exact hsw.mul_pow 3
    rw [t.zpow_y_pow_three k, mul_one, hx3] at h1
    exact h1.symm
  have hsAA : s ∈ t.d.AA := t.d.mem_AA_of_pow_eq_one hs hs3
  have hsZ : s ∈ t.Z :=
    Subgroup.mem_inf.mpr ⟨hsAA, Subgroup.mem_centralizer_singleton_iff.mpr hsy⟩
  exact ⟨s, hsZ, k, hsk⟩

theorem mem_sup_Z_zpowers_of_mem_inf_centralizer_y {x : G}
    (hx : x ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ t.Z ⊔ Subgroup.zpowers t.y := by
  obtain ⟨z₀, hz₀, k, hk⟩ := t.exists_mem_Z_mul_zpowers_of_mem_inf_centralizer_y hx hx3
  rw [← hk]
  exact Subgroup.mul_mem_sup hz₀ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t.y) k)

private theorem Z_le_P : t.Z ≤ t.P := by
  rw [← t.hPy]
  exact (t.Z_le_AA.trans t.d.AA_le_S).trans le_sup_left

private theorem Z_le_centralizer_zpowers_y :
    t.Z ≤ Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hk]
  exact (Commute.zpow_right
    (Subgroup.mem_centralizer_singleton_iff.mp (t.Z_le_centralizer hz)) k).symm

private theorem zpowers_y_le_centralizer_zpowers_y :
    Subgroup.zpowers t.y ≤ Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hk]
  exact (Commute.refl t.y).zpow_left k

private theorem commute_of_mem_sup_Z_zpowers_y {a b : G}
    (ha : a ∈ t.Z ⊔ Subgroup.zpowers t.y) (hb : b ∈ t.Z ⊔ Subgroup.zpowers t.y) :
    a * b = b * a := by
  have hZE : t.Z ≤ Subgroup.centralizer ((t.Z ⊔ Subgroup.zpowers t.y : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (t.Z_le_P.trans t.le_centralizer_Z)
      (Subgroup.zpowers_le.mpr (t.le_centralizer_Z t.hyP))
  have hyE : Subgroup.zpowers t.y ≤
      Subgroup.centralizer ((t.Z ⊔ Subgroup.zpowers t.y : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le t.Z_le_centralizer_zpowers_y t.zpowers_y_le_centralizer_zpowers_y
  have hE : (t.Z ⊔ Subgroup.zpowers t.y : Subgroup G) ≤
      Subgroup.centralizer ((t.Z ⊔ Subgroup.zpowers t.y : Subgroup G) : Set G) :=
    sup_le hZE hyE
  exact ((Subgroup.mem_centralizer_iff.mp (hE ha) b hb)).symm

private theorem mem_Z_of_mem_inf_centralizer_y_of_mem_S {x : G}
    (hx : x ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) (hx3 : x ^ 3 = 1)
    (hxS : x ∈ t.d.S) : x ∈ t.Z := by
  obtain ⟨z₀, hz₀, k, hk⟩ := t.exists_mem_Z_mul_zpowers_of_mem_inf_centralizer_y hx hx3
  have hwS : t.y ^ k ∈ t.d.S := by
    have hw : t.y ^ k = z₀⁻¹ * x := by
      rw [← hk]
      group
    rw [hw]
    exact t.d.S.mul_mem (t.d.S.inv_mem ((t.Z_le_AA.trans t.d.AA_le_S) hz₀)) hxS
  have hw : t.y ^ k ∈ t.d.S ⊓ Subgroup.zpowers t.y :=
    Subgroup.mem_inf.mpr ⟨hwS, Subgroup.zpow_mem _ (Subgroup.mem_zpowers t.y) k⟩
  rw [t.inf_S_zpowers_y_eq_bot, Subgroup.mem_bot] at hw
  rw [← hk, hw, mul_one]
  exact hz₀

section

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem map_conj_Z_eq_of_le_inf_centralizer_y (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {h : G}
    (hh : h ∈ Subgroup.centralizer ({t.y} : Set G))
    (hZh : t.Z.map (MulAut.conj h).toMonoidHom ≤
      t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) :
    t.Z.map (MulAut.conj h).toMonoidHom = t.Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzZ, hz1⟩ : ∃ z : G, z ∈ t.Z ∧ z ≠ 1 := by
    haveI : Nontrivial ↥t.Z :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [t.card_Z]; norm_num)
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥t.Z)
    exact ⟨z, z.2, fun h' => hz (Subtype.ext h')⟩
  have hzAA : z ∈ t.d.AA := t.Z_le_AA hzZ
  have hz3 : z ^ 3 = 1 := t.d.isElemAbelian_AA.2 z hzAA
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZgen : t.Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [Nat.card_zpowers, hzord, t.card_Z]
  let z' : G := h * z * h⁻¹
  have hz'Zmap : z' ∈ t.Z.map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hzZ
  have hz'T : z' ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G) := hZh hz'Zmap
  have hz'3 : z' ^ 3 = 1 := by
    have hconj : z' ^ 3 = h * z ^ 3 * h⁻¹ := by
      simpa [z'] using conj_pow (a := h) (b := z) (i := 3)
    rw [hconj, hz3]
    group
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    have hz_eq : z = h⁻¹ * z' * h := by
      rw [show z' = h * z * h⁻¹ from rfl]
      group
    rw [hz_eq, h1]
    group
  have hz'E : z' ∈ t.Z ⊔ Subgroup.zpowers t.y :=
    t.mem_sup_Z_zpowers_of_mem_inf_centralizer_y hz'T hz'3
  have hz'Z : z' ∈ t.Z := by
    by_contra hnot
    have hz'S : z' ∉ t.d.S := fun hS =>
      hnot (t.mem_Z_of_mem_inf_centralizer_y_of_mem_S hz'T hz'3 hS)
    have hcontra :=
      t.conj_not_mem_AA hOut hp hN hZ hz'T.1 hz'3 hz'S h⁻¹
    apply hcontra
    have heq : h⁻¹ * z' * (h⁻¹)⁻¹ = z := by
      simp only [z', inv_inv]
      group
    rw [heq]
    exact hzAA
  have hmap_le : t.Z.map (MulAut.conj h).toMonoidHom ≤ t.Z := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [hZgen] at hv
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hveq : (MulAut.conj h) v = z' ^ j := by
      rw [← hj]
      simpa only [MulAut.conj_apply, z'] using
        (conj_zpow (a := h) (b := z) (i := j)).symm
    change (MulAut.conj h) v ∈ t.Z
    rw [hveq]
    exact t.Z.zpow_mem hz'Z j
  have hcard : Nat.card (t.Z.map (MulAut.conj h).toMonoidHom) = Nat.card t.Z :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  exact Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)

theorem isWeaklyClosedIn_Z_inf_centralizer_y (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn
      (t.Z.subgroupOf (Subgroup.centralizer ({t.y} : Set G)))
      ((t.P ⊓ Subgroup.centralizer ({t.y} : Set G)).subgroupOf
        (Subgroup.centralizer ({t.y} : Set G))) := by
  intro g hg
  let K : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
  let T : Subgroup G := t.P ⊓ K
  have hTK : T ≤ K := inf_le_right
  have hconj : (CFSG.conjugate (t.Z.subgroupOf K) g).map K.subtype =
      CFSG.conjugate t.Z (g : G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y ∈ CFSG.conjugate (t.Z.subgroupOf K) g at hy
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6] at hy
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6]
      simpa using (Subgroup.mem_subgroupOf.mp hy)
    · intro hx
      have hx' : (g : G) * x * (g : G)⁻¹ ∈ t.Z := by
        rwa [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6] at hx
      have hxK : x ∈ K := by
        have hxx : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
        rw [hxx]
        exact K.mul_mem (K.mul_mem (K.inv_mem g.2) (t.Z_le_centralizer hx')) g.2
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      change (⟨x, hxK⟩ : ↥K) ∈ CFSG.conjugate (t.Z.subgroupOf K) g
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6]
      rw [Subgroup.mem_subgroupOf]
      simpa using hx'
  have hmapT : (T.subgroupOf K).map K.subtype = T :=
    Subgroup.map_subgroupOf_eq_of_le (G := G) (H := T) (K := K) hTK
  have hmapZ : (t.Z.subgroupOf K).map K.subtype = t.Z :=
    Subgroup.map_subgroupOf_eq_of_le (G := G) (H := t.Z) (K := K) t.Z_le_centralizer
  have hle : CFSG.conjugate t.Z (g : G) ≤ T := by
    have hmap := Subgroup.map_mono (f := K.subtype) hg
    rw [hmapT] at hmap
    rwa [hconj] at hmap
  have hZeq : CFSG.conjugate t.Z (g : G) = t.Z :=
    t.map_conj_Z_eq_of_le_inf_centralizer_y hOut hp hN hZ (K.inv_mem g.2)
      (by simpa only [CFSG.conjugate, T, K] using hle)
  apply Subgroup.map_injective K.subtype_injective
  rw [hconj, hZeq]
  exact hmapZ.symm

theorem pRank_Xz (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hOut : PerfectAutInner) {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 t.Xz = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
  let T : Subgroup G := t.P ⊓ K
  let S' : Subgroup ↥K := T.subgroupOf K
  let Z' : Subgroup ↥K := t.Z.subgroupOf K
  have hKne : K ≠ ⊤ := by
    intro htop
    have hycenter : t.y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ K := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    haveI : IsSimpleGroup G := c.standing.simple
    have hcenter : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := c.standing.nonab
        exact (hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) a b)).elim
    have hy1 : t.y = 1 := by
      rwa [hcenter, Subgroup.mem_bot] at hycenter
    have h3 : orderOf t.y = 3 := t.orderOf_y
    rw [hy1, orderOf_one] at h3
    omega
  have hK : CFSG.Open.IsKGroup ↥K := c.standing.kProper.isKGroup K hKne
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T K :=
    t.isSylowOf_inf_centralizer_y_centralizer hOut hp hN hZ
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S' ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K]
    have hmapT : S'.map K.subtype = T := Subgroup.map_subgroupOf_eq_of_le inf_le_right
    have hmapTop : (⊤ : Subgroup ↥K).map K.subtype = K := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [hmapT, hmapTop]
    exact hTsyl
  have hΩ : ∀ x ∈ S', x ^ 3 = 1 → ∀ y ∈ S', y ^ 3 = 1 → x * y = y * x := by
    intro x hx hx3 y hy hy3
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
    have hx3G : (x : G) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hx3
    have hy3G : (y : G) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hy3
    have hxE : (x : G) ∈ t.Z ⊔ Subgroup.zpowers t.y :=
      t.mem_sup_Z_zpowers_of_mem_inf_centralizer_y hxT hx3G
    have hyE : (y : G) ∈ t.Z ⊔ Subgroup.zpowers t.y :=
      t.mem_sup_Z_zpowers_of_mem_inf_centralizer_y hyT hy3G
    exact Subtype.ext (t.commute_of_mem_sup_Z_zpowers_y hxE hyE)
  have hcardE : Nat.card ↥(t.Z ⊔ Subgroup.zpowers t.y) = 9 := by
    have hcomm : ∀ a ∈ t.Z, ∀ b ∈ Subgroup.zpowers t.y, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (t.Z_le_centralizer_zpowers_y ha) b hb).symm
    have hcard :=
      (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute t.Z
        (Subgroup.zpowers t.y) hcomm).1
    have hZdisj : t.Z ⊓ Subgroup.zpowers t.y = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      obtain ⟨hwZ, hwy⟩ := Subgroup.mem_inf.mp hw
      have hwS : w ∈ t.d.S ⊓ Subgroup.zpowers t.y :=
        Subgroup.mem_inf.mpr ⟨(t.Z_le_AA.trans t.d.AA_le_S) hwZ, hwy⟩
      rw [t.inf_S_zpowers_y_eq_bot, Subgroup.mem_bot] at hwS
      exact hwS
    rw [hZdisj, Subgroup.card_bot, t.card_Z, Nat.card_zpowers, t.orderOf_y] at hcard
    omega
  have hrank : CFSG.Open.pRank 3 S' ≤ 3 := by
    refine CFSG.SectionRank.pRank_le (p := 3) (H := S') (k := 3) (by norm_num) ?_
    intro E hES hE
    have hEmap : E.map K.subtype ≤ t.Z ⊔ Subgroup.zpowers t.y := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      have heT : (e : G) ∈ T := Subgroup.mem_subgroupOf.mp (hES he)
      have he3 : (e : G) ^ 3 = 1 := by
        simpa using congrArg Subtype.val (hE.2 e he)
      exact t.mem_sup_Z_zpowers_of_mem_inf_centralizer_y heT he3
    have hcard : Nat.card E = Nat.card (E.map K.subtype) :=
      (Subgroup.card_map_of_injective K.subtype_injective).symm
    have hle9 : Nat.card (E.map K.subtype) ≤ 9 := by
      rw [← hcardE]
      exact Subgroup.card_le_of_le hEmap
    rw [hcard]
    calc Nat.card (E.map K.subtype) ≤ 9 := hle9
      _ = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ 3 := by norm_num
  have hZcard : Nat.card Z' = 3 := by
    have h1 : Nat.card Z' = Nat.card t.Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe t.Z_le_centralizer).toEquiv
    rw [h1, t.card_Z]
  have hZle : Z' ≤ S' := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact Subgroup.mem_inf.mpr ⟨t.Z_le_P hz, z.2⟩
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z' S' :=
    t.isWeaklyClosedIn_Z_inf_centralizer_y hOut hp hN hZ
  have hconc := hK332 ↥K hK S' hSyl hΩ hrank Z' hZle hZcard hwc
  have hX : (Subgroup.normalClosure (Z' : Set ↥K)).map K.subtype = t.Xz := rfl
  rw [← hX, CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.pRank_map_subtype (p := 3)
    (by norm_num) K (Subgroup.normalClosure (Z' : Set ↥K))]
  exact hconc

end

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
