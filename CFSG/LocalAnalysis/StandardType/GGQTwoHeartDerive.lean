module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartGraph
public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDict
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Heart

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2hV_finiteV {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) : Finite M.V :=
  Finite.of_equiv (Additive ↥Bs) M.model.toEquiv

private theorem ggQ2hV_psi_ne_zero {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) {yB : ↥Bs}
    (hyx : (yB : G) ∉ Subgroup.zpowers x) :
    D.Ψ (M.model (Additive.ofMul yB)) ≠ 0 := by
  intro h0
  have hmem : M.model (Additive.ofMul yB) ∈ LinearMap.ker D.Ψ := LinearMap.mem_ker.mpr h0
  rw [D.ker_eq] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hβ : Additive.ofMul yB = c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) := by
    apply M.model.injective
    calc M.model (Additive.ofMul yB)
        = c • M.model (⟨x, M.hx⟩ : ↥Bs) := hc.symm
      _ = (c.val : ZMod 3) • M.model (⟨x, M.hx⟩ : ↥Bs) := by rw [ZMod.natCast_zmod_val]
      _ = c.val • M.model (⟨x, M.hx⟩ : ↥Bs) := Nat.cast_smul_eq_nsmul (ZMod 3) c.val _
      _ = M.model (c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) :=
            (map_nsmul M.model.toAddMonoidHom c.val _).symm
  rw [← ofMul_pow] at hβ
  have hb_eq : yB = (⟨x, M.hx⟩ : ↥Bs) ^ c.val := Additive.ofMul.injective hβ
  have hbG : (yB : G) = x ^ c.val := by
    have h := congrArg (fun t : ↥Bs => (t : G)) hb_eq
    simpa using h
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), by rw [zpow_natCast]; exact hbG.symm⟩)

private theorem ggQ2hV_ker_card {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (hx0 : M.xV ≠ 0) :
    Nat.card (LinearMap.ker D.Ψ) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite M.V := ggQ2hV_finiteV M
  rw [D.ker_eq, ← FiniteField.pow_finrank_eq_natCard 3
      ↥(Submodule.span (ZMod 3) {M.xV}), finrank_span_singleton hx0]
  norm_num

private theorem ggQ2hV_comap_card {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (SK : Submodule (ZMod 3) E6Heart.H) :
    Nat.card ↥(Submodule.comap D.Ψ SK) =
      Nat.card (LinearMap.ker D.Ψ) * Nat.card ↥SK := by
  haveI : Finite M.V := ggQ2hV_finiteV M
  let g : ↥(Submodule.comap D.Ψ SK) →ₗ[ZMod 3] SK :=
    LinearMap.codRestrict SK (D.Ψ.comp (Submodule.comap D.Ψ SK).subtype) (fun w => w.2)
  have hsurj : Function.Surjective g := by
    intro s
    obtain ⟨v, hv⟩ := D.surj s.1
    refine ⟨⟨v, ?_⟩, ?_⟩
    · rw [Submodule.mem_comap, hv]; exact s.2
    · exact Subtype.ext hv
  have hker : Nat.card ↥(LinearMap.ker g) = Nat.card ↥(LinearMap.ker D.Ψ) := by
    refine Nat.card_congr ?_
    refine ⟨fun k => ⟨(k.1 : ↥(Submodule.comap D.Ψ SK)).1, ?_⟩,
      fun v => ⟨⟨v.1, ?_⟩, ?_⟩, fun k => ?_, fun v => ?_⟩
    · exact congrArg Subtype.val k.2
    · rw [Submodule.mem_comap, v.2]; exact SK.zero_mem
    · exact Subtype.ext v.2
    · exact Subtype.ext (Subtype.ext rfl)
    · exact Subtype.ext rfl
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective (f := g.toAddMonoidHom) hsurj
  have hker' : Nat.card ↥(g.toAddMonoidHom.ker) = Nat.card ↥(D.Ψ.ker) := hker
  rw [hker'] at hcard
  exact hcard.symm

private theorem ggQ2hV_card_F {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V) (hx0 : M.xV ≠ 0)
    (c : (M.phiGraph yV).ConnectedComponent)
    (c' : (E6Heart.graph (D.Ψ yV)).ConnectedComponent)
    (hker : {v : M.V | ∀ a : c.supp, M.rootForm a.1.1 v = 0} =
      D.Ψ ⁻¹' E6Heart.compKernel (D.Ψ yV) c')
    (hker3 : Nat.card (E6Heart.compKernel (D.Ψ yV) c') = 3) :
    Nat.card {v : M.V // ∀ a : c.supp, M.rootForm a.1.1 v = 0} = 9 := by
  haveI : Finite M.V := ggQ2hV_finiteV M
  let SK : Submodule (ZMod 3) E6Heart.H :=
    ⨅ (a : {a : E6Heart.Phi (D.Ψ yV) // a ∈ c'.supp}), LinearMap.ker (E6Heart.alpha a.1.1)
  have hSK : (SK : Set E6Heart.H) = E6Heart.compKernel (D.Ψ yV) c' := by
    ext t
    change t ∈ (⨅ a : {a : E6Heart.Phi (D.Ψ yV) // a ∈ c'.supp},
        LinearMap.ker (E6Heart.alpha a.1.1)) ↔
      (∀ a : E6Heart.Phi (D.Ψ yV), a ∈ c'.supp → E6Heart.alpha a.1 t = 0)
    rw [Submodule.mem_iInf]
    exact ⟨fun h a ha => by simpa using h ⟨a, ha⟩, fun h a => h a.1 a.2⟩
  have hSKcard : Nat.card ↥SK = 3 := by
    have hiff : ∀ x : E6Heart.H, x ∈ SK ↔ x ∈ E6Heart.compKernel (D.Ψ yV) c' := by
      intro x
      have hx : x ∈ (SK : Set E6Heart.H) ↔ x ∈ E6Heart.compKernel (D.Ψ yV) c' := by
        simp only [hSK]
      simpa using hx
    have he : ↥SK ≃ ↥(E6Heart.compKernel (D.Ψ yV) c') :=
      Equiv.subtypeEquiv (Equiv.refl E6Heart.H) (fun x => hiff x)
    rw [Nat.card_congr he]
    exact hker3
  have hset : {v : M.V | ∀ a : c.supp, M.rootForm a.1.1 v = 0} =
      (Submodule.comap D.Ψ SK : Set M.V) := by
    ext v
    rw [hker]
    constructor
    · intro hv
      rw [SetLike.mem_coe, Submodule.mem_comap, ← SetLike.mem_coe]
      exact hSK.symm ▸ hv
    · intro hv
      rw [SetLike.mem_coe, Submodule.mem_comap, ← SetLike.mem_coe] at hv
      rw [hSK] at hv
      exact hv
  have hcardW : Nat.card ↥(Submodule.comap D.Ψ SK) = 9 := by
    rw [ggQ2hV_comap_card D SK, ggQ2hV_ker_card D hx0, hSKcard]
  have he : {v : M.V // ∀ a : c.supp, M.rootForm a.1.1 v = 0} ≃
      ↥(Submodule.comap D.Ψ SK) :=
    Equiv.subtypeEquiv (Equiv.refl M.V) (fun v => Set.ext_iff.mp hset v)
  rw [Nat.card_congr he]
  exact hcardW

theorem ggQ2_heartB_i1 (hJ : GGQ2HeartJCentralizes) {G : Type}
    [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {labL : LargeEvenLabel} (htag : labL.tag = .twE6)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL)) (M : GGQ2LDatum 3 Bs L x)
    (hW : GGQ2LabelWeyl labL M.coxeter) (hB : M.ShapeB) : GGQTwoI1 Bs D J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Dd⟩ := ggQ2_heartDict htag M hW hB
  have hstdPre : LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hBle : B ≤ Bs := hBstar.1
  have hDleB : D ≤ B := hstdPre.1
  have hDleBs : D ≤ Bs := hDleB.trans hBle
  have hcardD9 : Nat.card D = 9 := by
    rw [hstdPre.2.2.1]; norm_num
  have hxD : x ∈ D := hstdPre.2.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hstdPre.2.2.2.2.2.2
  have hDCJ : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDcent]; exact inf_le_right
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x M.hx
  have hcardZp : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
  have hnotle : ¬ D ≤ Subgroup.zpowers x := by
    intro hle
    have hle' : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hcardD9, hcardZp] at hle'
    omega
  obtain ⟨y, hyD, hyS⟩ := Set.not_subset.mp hnotle
  let yB : ↥Bs := ⟨y, hDleBs hyD⟩
  have hyB : (yB : G) ∈ D := hyD
  have hyx : (yB : G) ∉ Subgroup.zpowers x := hyS
  obtain ⟨c, hc6, hcent⟩ := hJ hS rfl htag hmark M hW hB yB hyB hyx
  let yV : M.V := M.model (Additive.ofMul yB)
  have hyV : Dd.Ψ yV ≠ 0 := ggQ2hV_psi_ne_zero Dd hyx
  obtain ⟨c', hsize, hker⟩ := Dd.comp_transport yV c
  have hbig : 6 < E6Heart.compSize (Dd.Ψ yV) c' := by
    rw [← hsize]; exact hc6
  have hker3 : Nat.card (E6Heart.compKernel (Dd.Ψ yV) c') = 3 :=
    E6Heart.e6_heart_big_component_kernel (Dd.Ψ yV) hyV c' hbig
  have hx0 : M.xV ≠ 0 := fun h0 => hB.2.2.1 (h0 ▸ M.coSpan.zero_mem)
  let F : Set M.V := {v | ∀ a : c.supp, M.rootForm a.1.1 v = 0}
  have hFcard : Nat.card ↥F = 9 := ggQ2hV_card_F Dd yV hx0 c c' hker hker3
  let C : Subgroup ↥Bs := (Subgroup.centralizer (J : Set G)).subgroupOf Bs
  let eBsV : ↥Bs ≃ M.V := Additive.ofMul.trans M.model.toEquiv
  have heval : ∀ b : ↥Bs, eBsV b = M.model (Additive.ofMul b) := fun _ => rfl
  have hmemC : ∀ b : ↥Bs, b ∈ C ↔ ∀ j ∈ J, (b : G) * j = j * (b : G) := by
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h j hj; exact (h j hj).symm
    · intro h j hj; exact (h j hj).symm
  have hCle : Nat.card ↥C ≤ 9 := by
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
    have hinj : Function.Injective (fun b : ↥C => (⟨eBsV b.1, by
        rw [heval]
        exact fun a => hcent b.1 ((hmemC b.1).mp b.2) a⟩ : ↥F)) := by
      intro b b' h
      exact Subtype.ext (eBsV.injective (congrArg Subtype.val h))
    calc Nat.card ↥C ≤ Nat.card ↥F := Nat.card_le_card_of_injective _ hinj
      _ = 9 := hFcard
  have hDbcard : Nat.card ↥(D.subgroupOf Bs) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleBs).toEquiv, hcardD9]
  have hle : D.subgroupOf Bs ≤ C := Subgroup.subgroupOf_mono Bs hDCJ
  have heq : D.subgroupOf Bs = C :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hDbcard]; exact hCle)
  intro b hb hcomm
  let bB : ↥Bs := ⟨b, hb⟩
  have hbC : bB ∈ C := (hmemC bB).mpr hcomm
  have hbD' : bB ∈ D.subgroupOf Bs := by rw [heq]; exact hbC
  exact Subgroup.mem_subgroupOf.mp hbD'

end CFSG.StandardType

end
