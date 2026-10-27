module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerY
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem exists_ne_one_Z : ∃ z : G, z ∈ t.Z ∧ z ≠ 1 := by
  have hcard : Nat.card t.Z = 3 := t.card_Z
  haveI : Nontrivial ↥t.Z :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥t.Z)
  exact ⟨z, z.2, fun h => hz (Subtype.ext h)⟩

private theorem eq_zpowers_of_mem_Z {z : G} (hzZ : z ∈ t.Z) (hz1 : z ≠ 1) :
    t.Z = Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
  rw [Nat.card_zpowers,
    orderOf_eq_prime (t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ)) hz1, t.card_Z]

theorem conj_y_not_mem_AA (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) (g : G) :
    g * t.y * g⁻¹ ∉ t.d.AA := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hxAA
  let x : G := g * t.y * g⁻¹
  have hxAA' : x ∈ t.d.AA := hxAA
  have hy1 : t.y ≠ 1 := by
    intro h
    have h1 : orderOf t.y = 1 := by rw [h, orderOf_one]
    rw [t.orderOf_y] at h1
    exact (by norm_num : (3 : ℕ) ≠ 1) h1
  have hx1 : x ≠ 1 := by
    intro h
    apply hy1
    calc t.y = g⁻¹ * x * g := by
          rw [show x = g * t.y * g⁻¹ from rfl]
          group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group
  have hCx : Subgroup.centralizer ({x} : Set G) ≤ c.S.M :=
    t.centralizer_le_of_mem_AA hN hZ hxAA' hx1
  let Y : Subgroup G := t.Ky.map (MulAut.conj g).toMonoidHom
  have hYcent : Y ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show x = g * t.y * g⁻¹ from rfl]
    have hwC : w * t.y = t.y * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (t.Ky_le hw).2
    calc (g * w * g⁻¹) * (g * t.y * g⁻¹) = g * (w * t.y) * g⁻¹ := by group
      _ = g * (t.y * w) * g⁻¹ := by rw [hwC]
      _ = (g * t.y * g⁻¹) * (g * w * g⁻¹) := by group
  have hYM : Y ≤ c.S.M := hYcent.trans hCx
  have hYperfect : ⁅Y, Y⁆ = Y := by
    have h := Subgroup.map_commutator (H₁ := t.Ky) (H₂ := t.Ky)
      (f := (MulAut.conj g).toMonoidHom)
    rw [t.commutator_Ky] at h
    exact h.symm
  obtain ⟨z, hzZ, hz1⟩ := t.exists_ne_one_Z
  have hzA : z ∈ t.d.AA := t.Z_le_AA hzZ
  have hzS : z ∈ t.d.S := t.d.AA_le_S hzA
  have hzC : z ∈ Subgroup.centralizer ({t.y} : Set G) := t.Z_le_centralizer hzZ
  have hzKy : z ∈ t.Ky := t.inf_centralizer_le_Ky (Subgroup.mem_inf.mpr ⟨hzS, hzC⟩)
  have hgzY : g * z * g⁻¹ ∈ Y := by
    refine Subgroup.mem_map.mpr ⟨z, hzKy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hz3 : z ^ 3 = 1 := t.d.isElemAbelian_AA.2 z hzA
  have hgz3 : (g * z * g⁻¹) ^ 3 = 1 := by
    have hconj : (g * z * g⁻¹) ^ 3 = g * z ^ 3 * g⁻¹ := by
      simpa using conj_pow (a := g) (b := z) (i := 3)
    rw [hconj, hz3]
    group
  have hgzP : IsPGroup 3 (Subgroup.zpowers (g * z * g⁻¹)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hgz3)
  have hgzL : g * z * g⁻¹ ∈ c.L :=
    t.mem_L_of_mem_perfect hOut hYM hYperfect hgzY hgzP
  obtain ⟨l, hlL, hlA⟩ := t.exists_conj_mem_AA hgzL hgz3
  let k : G := l * g
  have hkz : k * z * k⁻¹ ∈ t.d.AA := by
    have h := hlA
    rw [show l * (g * z * g⁻¹) * l⁻¹ = (l * g) * z * (l * g)⁻¹ by group] at h
    simpa [k] using h
  have hkaM : ∀ a ∈ t.d.AA, k⁻¹ * a * k ∈ c.S.M := by
    intro a ha
    have hcomm : a * (k * z * k⁻¹) = (k * z * k⁻¹) * a :=
      congrArg Subtype.val
        ((t.d.isElemAbelian_AA.1).is_comm.comm ⟨a, ha⟩ ⟨k * z * k⁻¹, hkz⟩)
    have hcent : k⁻¹ * a * k ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (k⁻¹ * a * k) * z = k⁻¹ * (a * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * a) * k := by rw [hcomm]
        _ = z * (k⁻¹ * a * k) := by group
    have hCeq : Subgroup.centralizer (t.Z : Set G) =
        Subgroup.centralizer ({z} : Set G) := by
      rw [t.eq_zpowers_of_mem_Z hzZ hz1, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
    rw [← hCeq] at hcent
    exact hZ hcent
  let B : Subgroup G := t.d.AA.map (MulAut.conj k⁻¹).toMonoidHom
  have hBM : B ≤ c.S.M := by
    rintro _ ⟨a, ha, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hkaM a ha
  have hBp : IsPGroup 3 B := t.d.isElemAbelian_AA.isPGroup.map _
  obtain ⟨Q, hBQ⟩ := (hBp.comap_subtype (K := c.S.M)).exists_le_sylow
  let Q' : Subgroup G := (Q : Subgroup ↥c.S.M).map c.S.M.subtype
  have hQ'syl : CFSG.ABGLocalTools.IsSylowOf 3 Q' c.S.M := ⟨Q, rfl⟩
  have hBQ' : B ≤ Q' := by
    intro y hy
    exact Subgroup.mem_map_of_mem c.S.M.subtype
      (hBQ (show (⟨y, hBM hy⟩ : c.S.M) ∈ B.subgroupOf c.S.M from
        Subgroup.mem_subgroupOf.mpr hy))
  obtain ⟨m, hmM, hm⟩ := t.hP.exists_mem_conj hQ'syl
  let C : Subgroup G := t.d.AA.map (MulAut.conj (m⁻¹ * k⁻¹)).toMonoidHom
  have hCP : C ≤ t.P := by
    rintro _ ⟨a, ha, rfl⟩
    have hbB : k⁻¹ * a * k ∈ B := by
      refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hthis : m⁻¹ * (k⁻¹ * a * k) * m ∈ t.P := (hm (k⁻¹ * a * k)).mp (hBQ' hbB)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (m⁻¹ * k⁻¹) * a * (m⁻¹ * k⁻¹)⁻¹ = m⁻¹ * (k⁻¹ * a * k) * m by group]
    exact hthis
  have hCcard : Nat.card C = 27 := by
    rw [show C = t.d.AA.map (MulAut.conj (m⁻¹ * k⁻¹)).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj (m⁻¹ * k⁻¹)).injective, t.d.card_AA]
  have hCelem : CFSG.Open.IsElemAbelian 3 C :=
    CFSG.Open.IsElemAbelian.map t.d.isElemAbelian_AA _
  have hCA : C = t.d.AA := t.eq_AA_of_isElemAbelian hCP hCelem hCcard
  have hnorm : m⁻¹ * k⁻¹ ∈ Subgroup.normalizer (t.d.AA : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [C] using hCA)
  have hmkM : m⁻¹ * k⁻¹ ∈ c.S.M := t.normalizer_AA_le hp hN hnorm
  have hkmM : k * m ∈ c.S.M := by
    have h := c.S.M.inv_mem hmkM
    simpa [mul_inv_rev] using h
  have hkM : k ∈ c.S.M := by
    have h : (k * m) * m⁻¹ ∈ c.S.M := c.S.M.mul_mem hkmM (c.S.M.inv_mem hmM)
    simpa using h
  have hlM : l ∈ c.S.M := c.hyp81.1 hlL
  have hgM : g ∈ c.S.M := by
    have h : l⁻¹ * k ∈ c.S.M := c.S.M.mul_mem (c.S.M.inv_mem hlM) hkM
    simpa [k] using h
  have hxL : x ∈ c.L := t.hdL ▸ t.d.AA_le_L hxAA'
  have hyL : t.y ∈ c.L := by
    have hgMinv : g⁻¹ ∈ c.S.M := c.S.M.inv_mem hgM
    have h := (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hgMinv) x).mp hxL
    simpa [x, mul_assoc] using h
  exact t.y_not_mem_L hyL

theorem conj_not_mem_AA (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {x : G} (hxP : x ∈ t.P)
    (hx3 : x ^ 3 = 1) (hxS : x ∉ t.d.S) (g : G) : g * x * g⁻¹ ∉ t.d.AA := by
  rcases t.mem_AA_or_exists_conj_eq hxP hx3 with hxA | ⟨s, hsS, hconj | hconj⟩
  · exact fun _ => hxS (t.d.AA_le_S hxA)
  · intro hmem
    apply t.conj_y_not_mem_AA hOut hp hN hZ (g * s⁻¹)
    have hxeq : x = s⁻¹ * t.y * s := by
      have h := congrArg (fun z => s⁻¹ * z * s) hconj
      simpa [mul_assoc] using h
    have hgeq : g * x * g⁻¹ = (g * s⁻¹) * t.y * (g * s⁻¹)⁻¹ := by
      rw [hxeq]
      group
    rw [hgeq] at hmem
    exact hmem
  · intro hmem
    apply t.conj_y_not_mem_AA hOut hp hN hZ (g * s⁻¹)
    have hxeq : x = s⁻¹ * t.y⁻¹ * s := by
      have h := congrArg (fun z => s⁻¹ * z * s) hconj
      simpa [mul_assoc] using h
    have hgeq : (g * x * g⁻¹)⁻¹ = (g * s⁻¹) * t.y * (g * s⁻¹)⁻¹ := by
      rw [hxeq]
      group
    have hinvA : (g * x * g⁻¹)⁻¹ ∈ t.d.AA := t.d.AA.inv_mem hmem
    rwa [hgeq] at hinvA

theorem normalizer_inf_centralizer_y_le (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.normalizer ((t.P ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) : Set G) ≤
      c.S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg
  obtain ⟨z, hzZ, hz1⟩ := t.exists_ne_one_Z
  have hzA : z ∈ t.d.AA := t.Z_le_AA hzZ
  have hzS : z ∈ t.d.S := t.d.AA_le_S hzA
  have hzC : z ∈ Subgroup.centralizer ({t.y} : Set G) := t.Z_le_centralizer hzZ
  have hSP : t.d.S ≤ t.P := by
    rw [← t.hPy]
    exact le_sup_left
  have hzT : z ∈ (t.P ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) :=
    Subgroup.mem_inf.mpr ⟨hSP hzS, hzC⟩
  let u : G := g * z * g⁻¹
  have huT : u ∈ (t.P ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hg z).mp hzT
  have huP : u ∈ t.P := huT.1
  have hz3 : z ^ 3 = 1 := t.d.isElemAbelian_AA.2 z hzA
  have hu3 : u ^ 3 = 1 := by
    have hconj : u ^ 3 = g * z ^ 3 * g⁻¹ := by
      simpa [u] using conj_pow (a := g) (b := z) (i := 3)
    rw [hconj, hz3]
    group
  have huS : u ∈ t.d.S := by
    by_contra huS
    have h := t.conj_not_mem_AA hOut hp hN hZ huP hu3 huS g⁻¹
    apply h
    have heq : g⁻¹ * u * (g⁻¹)⁻¹ = z := by
      rw [show u = g * z * g⁻¹ from rfl]
      group
    rwa [heq]
  have huAA : u ∈ t.d.AA := t.d.mem_AA_of_pow_eq_one huS hu3
  have huZ : u ∈ t.Z := Subgroup.mem_inf.mpr ⟨huAA, huT.2⟩
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * u * g := by
          rw [show u = g * z * g⁻¹ from rfl]
          group
      _ = 1 := by rw [h]; group
  have hZgen : t.Z = Subgroup.zpowers z := t.eq_zpowers_of_mem_Z hzZ hz1
  have hZmap : t.Z.map (MulAut.conj g).toMonoidHom = t.Z := by
    rw [hZgen, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← t.eq_zpowers_of_mem_Z huZ hu1]
    exact hZgen
  have hNZ : g ∈ Subgroup.normalizer (t.Z : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hZmap
  exact t.normalizer_Z_le hp hN hZ hNZ

theorem isSylowOf_inf_centralizer_y_centralizer (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (t.P ⊓ Subgroup.centralizer ({t.y} : Set G))
      (Subgroup.centralizer ({t.y} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le
    (H := c.S.M) (M := Subgroup.centralizer ({t.y} : Set G))
    t.isSylowOf_inf_centralizer_y ?_
  intro x hx
  exact t.normalizer_inf_centralizer_y_le hOut hp hN hZ hx.1

theorem false_of_inducesAlternating (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) (hIIa : t.InducesAlternating) : False :=
  t.false_of_forall_conj_y (p := p) hp hN
    (fun g => t.conj_y_not_mem_AA hOut hp hN hZ g)
    (fun g => t.conj_ne_inv_of_inducesAlternating hIIa
      (t.isSylowOf_inf_centralizer_y_centralizer hOut hp hN hZ)
      (t.normalizer_inf_centralizer_y_le hOut hp hN hZ) g)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
