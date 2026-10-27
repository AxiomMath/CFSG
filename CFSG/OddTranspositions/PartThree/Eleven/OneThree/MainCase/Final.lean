module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.PCore
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.ShapeLocal
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.ShapeBlocks
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Witness
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Chain
import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.Asc72Local

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}


namespace MainHyp

variable {hC : HypothesisC D}

private structure TriData {U : Type} [Group U]
    (hS : Setup (Halpha D hC.alpha) (DstarH hC))
    (p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U) where
  v : Halpha D hC.alpha
  a : Halpha D hC.alpha
  c : Halpha D hC.alpha
  n : ℕ
  z : Halpha D hC.alpha
  w : Halpha D hC.alpha
  hv : v ∈ DstarH hC
  htri : IsTriangle (DstarH hC) v a c
  hnodd : Odd n
  hn1 : 1 < n
  hord : orderOf (v * c * a) = 2 * n
  hzdef : z = (v * c * a) ^ n
  hzz : z * z = 1
  hz1 : z ≠ 1
  hzv : Commute z v
  hzc : Commute z c
  hwF : w ∈ DstarH hC
  hvw : Commute v w
  hzeq : z = v * c * w
  hpz : (p z).2 = 1

private noncomputable def exists_triData {U : Type} [Group U] [Finite U]
    (hS : Setup (Halpha D hC.alpha) (DstarH hC))
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) :
    TriData hS p := by
  classical
  let v : Halpha D hC.alpha := Classical.choose (DstarH_nonempty hC)
  have hv : v ∈ DstarH hC := Classical.choose_spec (DstarH_nonempty hC)
  let tri := exists_isTriangle hS hU hp hodd hv
  let a : Halpha D hC.alpha := Classical.choose tri
  let c : Halpha D hC.alpha := Classical.choose (Classical.choose_spec tri)
  have htri : IsTriangle (DstarH hC) v a c :=
    Classical.choose_spec (Classical.choose_spec tri)
  let h3 := (isThirdKind_of_isTriangle hS hU hp hodd htri).1
  let n : ℕ := Classical.choose h3
  have hnodd : Odd n := (Classical.choose_spec h3).1
  have hn1 : 1 < n := (Classical.choose_spec h3).2.1
  have hord : orderOf (v * c * a) = 2 * n := (Classical.choose_spec h3).2.2
  have hz := (isThirdKind_of_isTriangle hS hU hp hodd htri).2
  let z : Halpha D hC.alpha := (v * c * a) ^ n
  let w : Halpha D hC.alpha := v * c * z
  obtain ⟨hzz, hz1, hzv, hzc, -, hwF⟩ :=
    IsTriangle.third_kind hS.oddT hS.normal htri hnodd hord
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one hv
  have hc2 : c * c = 1 := hS.oddT.mul_self_eq_one htri.2.1
  have hvc : Commute v c := htri.2.2.2.2.1
  have hvc2 : (v * c) * (v * c) = 1 := by
    calc (v * c) * (v * c) = v * (c * v) * c := by group
      _ = v * (v * c) * c := by rw [hvc.eq]
      _ = (v * v) * (c * c) := by group
      _ = 1 := by rw [hv2, hc2, mul_one]
  have hvw : Commute v w :=
    ((Commute.refl v).mul_right hvc).mul_right hzv.symm
  have hzeq : z = v * c * w := by
    calc z = 1 * z := (one_mul z).symm
      _ = ((v * c) * (v * c)) * z := by rw [hvc2]
      _ = (v * c) * ((v * c) * z) := by rw [mul_assoc]
      _ = v * c * w := rfl
  exact ⟨v, a, c, n, z, w, hv, htri, hnodd, hn1, hord, rfl, hzz, hz1, hzv, hzc, hwF,
    hvw, hzeq, hz n hord⟩

private structure WitData {U : Type} [Group U] [Finite U]
    {hS : Setup (Halpha D hC.alpha) (DstarH hC)}
    {p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U}
    (T : TriData hS p) where
  β : Set G
  u' : G
  hβ : β ∈ Dalpha D hC.alpha
  hvβ : (T.v : G) ∈ β
  hu'β : u' ∈ DalphaStar D β
  hdu' : ¬ Commute hC.d u'
  hu'α : u' ∉ hC.alpha
  hu'v : Commute u' (T.v : G)
  hu'c : Commute u' (T.c : G)
  hu'w : Commute u' (T.w : G)
  hu'z : Commute u' (T.z : G)
  hu'K : ∀ κ ∈ kBlock D hC.alpha, Commute u' (κ * (T.v : G) * κ⁻¹)

private noncomputable def exists_witData {U : Type} [Group U] [Finite U]
    (h : MainHyp hC) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    {hS : Setup (Halpha D hC.alpha) (DstarH hC)}
    {p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U}
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) (T : TriData hS p) :
    WitData T := by
  classical
  have hvStar : (T.v : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp T.hv
  let exβ := mem_DalphaStar_iff.mp hvStar
  let β : Set G := Classical.choose exβ
  have hβ : β ∈ Dalpha D hC.alpha := (Classical.choose_spec exβ).1
  have hvβ : (T.v : G) ∈ β := (Classical.choose_spec exβ).2
  have hcStar : (T.c : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp T.htri.2.1
  have hvc : (T.v : G) ≠ (T.c : G) := fun hvc =>
    T.htri.2.2.2.1 (Subtype.ext hvc)
  have hcomm : Commute (T.v : G) (T.c : G) :=
    T.htri.2.2.2.2.1.map (Halpha D hC.alpha).subtype
  let wit := h.exists_witness hU φ hQ1 hβ hvβ hcStar hvc hcomm
  let u' : G := Classical.choose wit
  obtain ⟨hu'β, hdu', hu'α, hu'v, hq, hκ⟩ := Classical.choose_spec wit
  have hu'c : Commute u' (T.c : G) := hq (T.c : G) hcStar hvc.symm hcomm
  have hwStar : (T.w : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp T.hwF
  have hu'w : Commute u' (T.w : G) := by
    by_cases hwv : T.w = T.v
    · simpa [hwv] using hu'v
    · exact hq (T.w : G) hwStar (fun h => hwv (Subtype.ext h))
        (T.hvw.map (Halpha D hC.alpha).subtype)
  have hzG : (T.z : G) = (T.v : G) * (T.c : G) * (T.w : G) :=
    congrArg Subtype.val T.hzeq
  have hu'z : Commute u' (T.z : G) := by
    rw [hzG]
    exact (hu'v.mul_right hu'c).mul_right hu'w
  exact ⟨β, u', hβ, hvβ, hu'β, hdu', hu'α, hu'v, hu'c, hu'w, hu'z, hκ⟩

private theorem exists_lift_centSet {z : Halpha D hC.alpha} {y : G}
    (hy : y ∈ DalphaStar D hC.alpha) (hyz : Commute y (z : G)) :
    ∃ yH : Halpha D hC.alpha, (yH : G) = y ∧ yH ∈ centSet (DstarH hC) z := by
  refine ⟨⟨y, Subgroup.subset_closure hy⟩, rfl, (mem_DstarH_iff hC).mpr hy, ?_⟩
  exact Subtype.ext hyz.eq

private theorem localGroup_map_subtype_le {z : Halpha D hC.alpha} :
    (localGroup (DstarH hC) z).map (Halpha D hC.alpha).subtype ≤
      localGroup (DalphaStar D hC.alpha) (z : G) := by
  rw [Subgroup.map_le_iff_le_comap, localGroup, Subgroup.closure_le]
  intro x hx
  change (x : G) ∈ localGroup (DalphaStar D hC.alpha) (z : G)
  exact Subgroup.subset_closure
    ⟨(mem_DstarH_iff hC).mp hx.1, hx.2.map (Halpha D hC.alpha).subtype⟩

private theorem mem_localGroup_subtype {z l : Halpha D hC.alpha}
    (hl : l ∈ localGroup (DstarH hC) z) :
    (l : G) ∈ localGroup (DalphaStar D hC.alpha) (z : G) :=
  localGroup_map_subtype_le (hC := hC)
    (Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype hl)

private theorem exists_local_decomp {U : Type} [Group U]
    (p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U)
    (hS : Setup (Halpha D hC.alpha) (DstarH hC)) (hodd : Odd (Nat.card p.ker))
    {z v : Halpha D hC.alpha} (hz : z * z = 1) (hpz : (p z).2 = 1)
    (hv : v ∈ DstarH hC) {d : Halpha D hC.alpha} (hd : d ∈ DstarH hC) :
    ∃ l ∈ localGroup (DstarH hC) z, ∃ k ∈ p.ker,
      d = l * (k * v * k⁻¹) * l⁻¹ := by
  obtain ⟨h, hh, hdv⟩ := hC.Halpha_transitive (v : G) ((mem_DstarH_iff hC).mp hv)
    (d : G) ((mem_DstarH_iff hC).mp hd)
  let hH : Halpha D hC.alpha := ⟨h, hh⟩
  have hdvH : hH * v * hH⁻¹ = d := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] using hdv
  have htop : hH ∈ ((p.ker ⊔ localGroup (DstarH hC) z : Subgroup (Halpha D hC.alpha)) :
      Set (Halpha D hC.alpha)) := by
    rw [ker_sup_localGroup_eq_top hS hodd hz hpz]
    exact Subgroup.mem_top hH
  rw [Subgroup.normal_mul] at htop
  obtain ⟨k, hk, l, hl, hkl⟩ := Set.mem_mul.mp htop
  have hk' : l⁻¹ * k * l ∈ p.ker := by
    apply MonoidHom.mem_ker.mpr
    have hk1 : p k = 1 := MonoidHom.mem_ker.mp hk
    rw [map_mul, map_mul, map_inv, hk1, mul_one]
    exact inv_mul_cancel (p l)
  refine ⟨l, hl, l⁻¹ * k * l, hk', ?_⟩
  rw [← hdvH]
  apply Subtype.ext
  have hklG : (k : G) * (l : G) = h := congrArg Subtype.val hkl
  show (hH : G) * (v : G) * (hH : G)⁻¹ =
    (l : G) * (((l⁻¹ * k * l : Halpha D hC.alpha) : G) * (v : G) *
      ((l⁻¹ * k * l : Halpha D hC.alpha) : G)⁻¹) * (l : G)⁻¹
  rw [show (hH : G) = h from rfl, ← hklG]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

private theorem exists_decomp_dalphaStar {U : Type} [Group U]
    (p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U)
    (hS : Setup (Halpha D hC.alpha) (DstarH hC)) (hodd : Odd (Nat.card p.ker))
    (hpker : p.ker = EightOne.twoOddCore (Halpha D hC.alpha))
    {z v : Halpha D hC.alpha} (hz : z * z = 1) (hpz : (p z).2 = 1)
    (hv : v ∈ DstarH hC) :
    ∀ d ∈ DalphaStar D hC.alpha,
      ∃ l ∈ localGroup (DalphaStar D hC.alpha) (z : G),
        ∃ k ∈ kBlock D hC.alpha, d = l * (k * (v : G) * k⁻¹) * l⁻¹ := by
  intro d hd
  let dH : Halpha D hC.alpha := ⟨d, Subgroup.subset_closure hd⟩
  have hdF : dH ∈ DstarH hC := hd
  obtain ⟨l, hl, k, hk, heq⟩ :=
    exists_local_decomp p hS hodd hz hpz hv hdF
  have hkK : k ∈ EightOne.twoOddCore (Halpha D hC.alpha) := by rwa [← hpker]
  refine ⟨(l : G), mem_localGroup_subtype (hC := hC) hl, (k : G),
    Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype hkK, ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val heq

private theorem mem_DalphaStar_conj_inv {β : Set G} {g : G}
    (hψ : cimg g⁻¹ β = hC.alpha) {x : G} (hx : x ∈ DalphaStar D β) :
    g⁻¹ * x * g ∈ DalphaStar D hC.alpha := by
  have h := DalphaStar.conj hC.setup.normal hx g⁻¹
  rw [show (fun y => g⁻¹ * y * (g⁻¹)⁻¹) '' β = hC.alpha by
    simpa [cimg] using hψ] at h
  simpa only [inv_inv] using h

private theorem commute_conj_inv_of_commute {g z x : G} (hg : Commute g z)
    (hx : Commute x z) : Commute (g⁻¹ * x * g) z := by
  have h1 : Commute (g⁻¹ * x * (g⁻¹)⁻¹) (g⁻¹ * z * (g⁻¹)⁻¹) :=
    (Commute.conj_iff g⁻¹).mpr hx
  have h2 : g⁻¹ * z * (g⁻¹)⁻¹ = z := by
    rw [inv_inv]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [← hg.eq]
      _ = z := by group
  rw [h2] at h1
  simpa only [inv_inv] using h1

private theorem mem_D_of_mem_DalphaStar {β : Set G} {x : G}
    (hx : x ∈ DalphaStar D β) : x ∈ D := by
  obtain ⟨δ, hδ, hxδ⟩ := mem_DalphaStar_iff.mp hx
  exact (mem_Dalpha_iff.mp hδ).2.1 hxδ

private theorem exists_chainData {U : Type} [Group U] [Finite U]
    (hS : Setup (Halpha D hC.alpha) (DstarH hC))
    {p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U}
    (hodd : Odd (Nat.card p.ker))
    {z : Halpha D hC.alpha} (hz : z * z = 1) (hpz : (p z).2 = 1)
    {v x : G} (hv : v ∈ DalphaStar D hC.alpha) (hzv : Commute v (z : G))
    (hgen : ∀ d ∈ DalphaStar D hC.alpha,
      ∃ l ∈ localGroup (DalphaStar D hC.alpha) (z : G),
        ∃ k ∈ kBlock D hC.alpha, d = l * (k * v * k⁻¹) * l⁻¹)
    (hxD : x ∈ D)
    (hxK : ∀ k ∈ kBlock D hC.alpha, Commute x (k * v * k⁻¹))
    (hdx : ¬ Commute hC.d x) (hxα : x ∉ hC.alpha) (hxz : Commute x (z : G)) :
    ∃ (y : G) (_ : y ∈ centSet (DalphaStar D hC.alpha) (z : G)),
      ¬ Commute x y ∧ ∃ g₁ : G, g₁ ∈ localGroup D (z : G) ∧
        g₁ * hC.d * g₁⁻¹ = v := by
  classical
  let exy := exists_not_commute_centSet (hC := hC) (z := (z : G)) (v := v) (x := x)
    hgen hxD hdx hxα hxK
  let y : G := Classical.choose exy
  obtain ⟨hyCent, hxy⟩ := Classical.choose_spec exy
  have hyStar : y ∈ DalphaStar D hC.alpha := hyCent.1
  have hyz : Commute y (z : G) := hyCent.2
  have hyD : y ∈ D := DalphaStar_subset hC.isBlock_alpha hyStar
  have hdz : Commute hC.d (z : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC z.2)).symm
  obtain ⟨yH, hyHval, hyCentF⟩ := exists_lift_centSet (hC := hC) hyStar hyz
  obtain ⟨vH, hvHval, hvCentF⟩ := exists_lift_centSet (hC := hC) hv hzv
  let exl := exists_conj_eq_of_mem_centSet (X := Halpha D hC.alpha) (F := DstarH hC)
    (p := p) hS hodd hz hpz hyCentF hvCentF
  let lH : Halpha D hC.alpha := Classical.choose exl
  have hlH : lH ∈ localGroup (DstarH hC) z := (Classical.choose_spec exl).1
  have hlyv : lH * yH * lH⁻¹ = vH := (Classical.choose_spec exl).2
  have hlStar : (lH : G) ∈ localGroup (DalphaStar D hC.alpha) (z : G) :=
    mem_localGroup_subtype (hC := hC) (z := z) hlH
  have hsub : centSet (DalphaStar D hC.alpha) (z : G) ⊆ centSet D (z : G) := by
    intro t ht
    exact ⟨DalphaStar_subset hC.isBlock_alpha ht.1, ht.2⟩
  have hl : (lH : G) ∈ localGroup D (z : G) := Subgroup.closure_mono hsub hlStar
  have hlyvG : (lH : G) * y * (lH : G)⁻¹ = v := by
    have h := congrArg Subtype.val hlyv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rwa [hyHval, hvHval] at h
  let exg := exists_conj_localGroup_of_chain hC.setup.oddT
    ⟨hC.hd, hdz⟩ ⟨hxD, hxz⟩ ⟨hyD, hyz⟩ hdx hxy hl hlyvG
  exact ⟨y, ⟨hyStar, hyz⟩, hxy, Classical.choose exg,
    (Classical.choose_spec exg).1, (Classical.choose_spec exg).2⟩

private theorem psi_eq_alpha {β : Set G} {v g₁ : G} (hβ : β ∈ Dalpha D hC.alpha)
    (hvβ : v ∈ β) (hg₁u : g₁ * hC.d * g₁⁻¹ = v) :
    cimg g₁⁻¹ β = hC.alpha := by
  have hψclass : cimg g₁⁻¹ β ∈ blockClass hC.alpha :=
    cimg_mem_blockClass_iff.mpr hβ.1
  have huψ : hC.d ∈ cimg g₁⁻¹ β := by
    refine ⟨v, hvβ, ?_⟩
    rw [inv_inv, ← hg₁u]
    group
  exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hψclass
    (mem_blockClass_self hC.alpha) ⟨hC.d, huψ, hC.d_mem_alpha⟩

private theorem mem_DalphaStar_of_triangle (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {v a c : Halpha D hC.alpha}
    (htri : IsTriangle (DstarH hC) v a c) (hvβ : (v : G) ∈ β) :
    (c : G) ∈ DalphaStar D β ∧ hC.d ∈ DalphaStar D β := by
  have hcStar : (c : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp htri.2.1
  obtain ⟨γ, hγ, hcγ⟩ := mem_DalphaStar_iff.mp hcStar
  have hvc : (v : G) ≠ (c : G) := fun hvc => htri.2.2.2.1 (Subtype.ext hvc)
  have hcomm : Commute (v : G) (c : G) := htri.2.2.2.2.1.map (Halpha D hC.alpha).subtype
  refine ⟨?_, ?_⟩
  · exact subset_DalphaStar
      (h.mem_Dalpha_of_mem_of_commute hβ hγ hvβ hcγ hvc hcomm) hcγ
  · exact subset_DalphaStar (mem_Dalpha_symm hβ hC.isBlock_alpha.subset) hC.d_mem_alpha

private theorem pullback_lift {z c : Halpha D hC.alpha} {β : Set G} {u' g₁ : G}
    (hzc : Commute z c) (hcd : Commute (c : G) hC.d)
    (hψ : cimg g₁⁻¹ β = hC.alpha)
    (hcβ : (c : G) ∈ DalphaStar D β) (huβ : hC.d ∈ DalphaStar D β)
    (hu'β : u' ∈ DalphaStar D β) (hu'c : Commute u' (c : G))
    (hu'z : Commute u' (z : G)) (hg₁ : g₁ ∈ localGroup D (z : G)) :
    ∃ y0H y1H y2H : Halpha D hC.alpha,
      y0H ∈ centSet (DstarH hC) z ∧ y1H ∈ centSet (DstarH hC) z ∧
        y2H ∈ centSet (DstarH hC) z ∧ Commute y0H y1H ∧ Commute y0H y2H ∧
        (y1H : G) = g₁⁻¹ * hC.d * g₁ ∧ (y2H : G) = g₁⁻¹ * u' * g₁ := by
  classical
  let y0 : G := g₁⁻¹ * (c : G) * g₁
  let y1 : G := g₁⁻¹ * hC.d * g₁
  let y2 : G := g₁⁻¹ * u' * g₁
  have hy0 : y0 ∈ DalphaStar D hC.alpha := mem_DalphaStar_conj_inv (hC := hC) hψ hcβ
  have hy1 : y1 ∈ DalphaStar D hC.alpha := mem_DalphaStar_conj_inv (hC := hC) hψ huβ
  have hy2 : y2 ∈ DalphaStar D hC.alpha := mem_DalphaStar_conj_inv (hC := hC) hψ hu'β
  have hg₁z : Commute g₁ (z : G) := commute_of_mem_localGroup hg₁
  have hcz : Commute (c : G) (z : G) := hzc.symm.map (Halpha D hC.alpha).subtype
  have hdz : Commute hC.d (z : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC z.2)).symm
  have hy0z : Commute y0 (z : G) := commute_conj_inv_of_commute hg₁z hcz
  have hy1z : Commute y1 (z : G) := commute_conj_inv_of_commute hg₁z hdz
  have hy2z : Commute y2 (z : G) := commute_conj_inv_of_commute hg₁z hu'z
  have h01 : Commute y0 y1 := by
    have h := (Commute.conj_iff g₁⁻¹).mpr hcd
    simpa only [y0, y1, inv_inv] using h
  have h02 : Commute y0 y2 := by
    have h := (Commute.conj_iff g₁⁻¹).mpr hu'c.symm
    simpa only [y0, y2, inv_inv] using h
  obtain ⟨y0H, hy0Hval, hy0H⟩ := exists_lift_centSet (hC := hC) hy0 hy0z
  obtain ⟨y1H, hy1Hval, hy1H⟩ := exists_lift_centSet (hC := hC) hy1 hy1z
  obtain ⟨y2H, hy2Hval, hy2H⟩ := exists_lift_centSet (hC := hC) hy2 hy2z
  have h01H : Commute y0H y1H := by
    show y0H * y1H = y1H * y0H
    apply Subtype.ext
    show (y0H : G) * (y1H : G) = (y1H : G) * (y0H : G)
    rw [hy0Hval, hy1Hval]
    exact h01.eq
  have h02H : Commute y0H y2H := by
    show y0H * y2H = y2H * y0H
    apply Subtype.ext
    show (y0H : G) * (y2H : G) = (y2H : G) * (y0H : G)
    rw [hy0Hval, hy2Hval]
    exact h02.eq
  exact ⟨y0H, y1H, y2H, hy0H, hy1H, hy2H, h01H, h02H, hy1Hval, hy2Hval⟩

private theorem false_of_chainData {U : Type} [Group U] [Finite U]
    (h : MainHyp hC) (hS : Setup (Halpha D hC.alpha) (DstarH hC))
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (p : Halpha D hC.alpha →* Multiplicative (ZMod 2) × U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker))
    {v a c z : Halpha D hC.alpha} {n : ℕ}
    (htri : IsTriangle (DstarH hC) v a c) (hord : orderOf (v * c * a) = 2 * n)
    (hzdef : z = (v * c * a) ^ n) (hzc : Commute z c)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hvβ : (v : G) ∈ β)
    {u' g₁ : G} (hu'β : u' ∈ DalphaStar D β) (hdu' : ¬ Commute hC.d u')
    (hu'c : Commute u' (c : G)) (hu'z : Commute u' (z : G))
    (hg₁ : g₁ ∈ localGroup D (z : G)) (hg₁u : g₁ * hC.d * g₁⁻¹ = (v : G)) :
    False := by
  classical
  have hψ : cimg g₁⁻¹ β = hC.alpha := psi_eq_alpha hβ hvβ hg₁u
  obtain ⟨hcβ, huβ⟩ := mem_DalphaStar_of_triangle h hβ htri hvβ
  have hcStar : (c : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp htri.2.1
  have hcd : Commute (c : G) hC.d := (hC.DalphaStar_subset_commute hcStar).2
  obtain ⟨y0H, y1H, y2H, hy0H, hy1H, hy2H, h01H, h02H, hy1Hval, hy2Hval⟩ :=
    pullback_lift hzc hcd hψ hcβ huβ hu'β hu'c hu'z hg₁
  have hinj : Set.InjOn p (centSet (DstarH hC) z) := by
    have h := injOn_centSet_of_isTriangle hS hU hp hodd htri hord
    rwa [← hzdef] at h
  have hcommH := commute_of_commute_of_injOn hS hU hp hodd hinj hy0H hy1H hy2H h01H h02H
  have h12G : Commute (g₁⁻¹ * hC.d * g₁) (g₁⁻¹ * u' * g₁) := by
    have h := congrArg Subtype.val hcommH.eq
    change (g₁⁻¹ * hC.d * g₁) * (g₁⁻¹ * u' * g₁) =
      (g₁⁻¹ * u' * g₁) * (g₁⁻¹ * hC.d * g₁)
    simpa only [Subgroup.coe_mul, hy1Hval, hy2Hval] using h
  exact hdu' (by
    have h := (Commute.conj_iff g₁⁻¹).mp (by simpa only [inv_inv] using h12G)
    simpa only [inv_inv] using h)

theorem false_of_shape (h : MainHyp hC) {U : Type} [Group U] [Finite U]
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) : False := by
  classical
  let H : Subgroup G := Halpha D hC.alpha
  let F : Set H := DstarH hC
  let hS : Setup H F := Nine.setup_DstarH hC
  let p : H →* Multiplicative (ZMod 2) × U := shapeProj φ
  have hp : Function.Surjective p := shapeProj_surjective φ
  have hpker : p.ker = EightOne.twoOddCore H := ker_shapeProj φ
  have hodd : Odd (Nat.card p.ker) := by
    rw [hpker]
    exact odd_card_twoOddCore hQ1
  let T : TriData hS p := exists_triData hS hU p hp hodd
  let W : WitData T := exists_witData h hU φ hQ1 T
  have hgen : ∀ d ∈ DalphaStar D hC.alpha,
      ∃ l ∈ localGroup (DalphaStar D hC.alpha) (T.z : G),
        ∃ k ∈ kBlock D hC.alpha, d = l * (k * (T.v : G) * k⁻¹) * l⁻¹ :=
    exists_decomp_dalphaStar p hS hodd hpker T.hzz T.hpz T.hv
  have hu'D : W.u' ∈ D := mem_D_of_mem_DalphaStar W.hu'β
  obtain ⟨y, hy, hxy, g₁, hg₁, hg₁u⟩ :=
    exists_chainData hS hodd T.hzz T.hpz ((mem_DstarH_iff hC).mp T.hv)
      (T.hzv.symm.map (Halpha D hC.alpha).subtype) hgen hu'D W.hu'K W.hdu' W.hu'α
      W.hu'z
  exact false_of_chainData h hS hU p hp hodd T.htri T.hord T.hzdef T.hzc W.hβ W.hvβ
    W.hu'β W.hdu' W.hu'c W.hu'z hg₁ hg₁u

theorem false_of_pCore_le_center (h : MainHyp hC)
    (hS : EightOneShape (Halpha D hC.alpha))
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha)) : False := by
  have hQ1 := pCore_eq_bot_of_eightOneShape (Nine.setup_DstarH hC) hS hQ
  rcases hS with hL2 | hU
  · obtain ⟨φ⟩ := hL2
    exact h.false_of_shape (.isPSL2 2 le_rfl (MulEquiv.refl _)) φ hQ1
  · obtain ⟨φ⟩ := hU
    haveI : Finite ↥(CFSG.Theory.Comparator.PSU3Model 2) := by
      have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 4)) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
      exact Subtype.finite
    exact h.false_of_shape (.isPSU3 2 le_rfl (MulEquiv.refl _)) φ hQ1

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
