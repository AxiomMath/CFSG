module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.LieType.ChevTwo.OrthogonalAutLarge
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthAmbient
import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.StandardType.NbrOrth
open Multiplicative

private theorem p9uOA_pow_prime {p : ℕ} (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem p9uOA_mem_range {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (y : ↥(orthDerived Φ.Q)) : Φ.ψ y ∈ L := by
  have h : Φ.ψ y ∈ Φ.ψ.range := ⟨y, rfl⟩
  rwa [Φ.hrange] at h

private theorem p9uOA_mem_range_tauΩ_iff {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (y : ↥(orthDerived Φ.Q)) :
    y ∈ (Φ.Δ.τΩ Φ.hA).range ↔ (y : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.A := by
  constructor
  · rintro ⟨f, rfl⟩
    have h : Φ.Δ.τ f ∈ Φ.Δ.τ.range := ⟨f, rfl⟩
    rw [Φ.Δ.τ_range] at h
    simpa using h
  · intro hy
    rw [← Φ.Δ.τ_range] at hy
    obtain ⟨f, hf⟩ := hy
    exact ⟨f, Subtype.ext (by simpa using hf)⟩

private theorem p9uOA_range_beta {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) : Φ.β.range = (Φ.Δ.τΩ Φ.hA).range := by
  ext y
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨b, rfl⟩
    exact (p9uOA_mem_range_tauΩ_iff Φ (Φ.β b)).mpr (Φ.hβA b)
  · intro hy
    rw [p9uOA_mem_range_tauΩ_iff Φ y] at hy
    obtain ⟨b, hb⟩ := Φ.hβsurj (y : Φ.V ≃ₗ[Φ.F] Φ.V) hy
    exact ⟨b, Subtype.ext hb⟩

private theorem p9uOA_center_eq_bot {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥)
    {z : ↥(orthDerived Φ.Q)} (hz : ∀ y, z * y = y * z) : z = 1 := by
  have hc : (⟨Φ.ψ z, p9uOA_mem_range Φ z⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    have hg' : (l : G) ∈ Φ.ψ.range := by rw [Φ.hrange]; exact l.2
    obtain ⟨y, hy⟩ := hg'
    apply Subtype.ext
    show (l : G) * Φ.ψ z = Φ.ψ z * (l : G)
    rw [← hy, ← map_mul, ← map_mul, hz y]
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : Φ.ψ z = 1 := congrArg Subtype.val hc
  exact Φ.hinj (by rw [h1, map_one])

private theorem p9uOA_beta_conj {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L)
    (hZ : ∀ z : ↥(orthDerived Φ.Q), (∀ y, z * y = y * z) → z = 1)
    {w : ↥(orthDerived Φ.Q)} {b b' : ↥Bs}
    (h : Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ = (b' : G)) : w * Φ.β b * w⁻¹ = Φ.β b' := by
  have hc : ∀ y, ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) * y =
      y * ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) := by
    intro y
    have h1 : Φ.ψ (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹) =
        Φ.ψ (Φ.β b' * y * (Φ.β b')⁻¹) := by
      calc Φ.ψ (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹)
          = Φ.ψ w * Φ.ψ (Φ.β b * (w⁻¹ * y * w) * (Φ.β b)⁻¹) * (Φ.ψ w)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = Φ.ψ w * ((b : G) * Φ.ψ (w⁻¹ * y * w) * (b : G)⁻¹) * (Φ.ψ w)⁻¹ := by
            rw [Φ.hcompat]
        _ = (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹) * Φ.ψ y *
              (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = (b' : G) * Φ.ψ y * (b' : G)⁻¹ := by rw [h]
        _ = Φ.ψ (Φ.β b' * y * (Φ.β b')⁻¹) := (Φ.hcompat b' y).symm
    have h2 := Φ.hinj h1
    calc ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) * y
        = (Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹) *
            (w * Φ.β b * w⁻¹) := by group
      _ = (Φ.β b')⁻¹ * (Φ.β b' * y * (Φ.β b')⁻¹) * (w * Φ.β b * w⁻¹) := by rw [h2]
      _ = y * ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) := by group
  exact (inv_mul_eq_one.mp (hZ _ hc)).symm

private theorem p9uOA_inf_le_hyperplane {G : Type} [Group G] {Bs L : Subgroup G}
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer L Bs) :
    Bs ⊓ Subgroup.centralizer (L : Set G) ≤ ggHyperplane Bs r := by
  intro k hk
  obtain ⟨g, hgL, -, hact⟩ := mem_ggAutomizer_iff.mp hr
  rw [ggHyperplane, Subgroup.mem_map]
  refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
  change r ⟨k, hk.1⟩ = ⟨k, hk.1⟩
  apply Subtype.ext
  rw [hact]
  have hc : g * k = k * g := (Subgroup.mem_centralizer_iff.mp hk.2) g hgL
  rw [hc]
  group

private theorem p9uOA_beta_eq_one_iff {p : ℕ} {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥) (b : ↥Bs) :
    Φ.β b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro hb
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : l ∈ Φ.ψ.range := by rw [Φ.hrange]; exact hl
    obtain ⟨y, rfl⟩ := hl'
    have h := Φ.hcompat b y
    rw [hb] at h
    simp only [one_mul, inv_one, mul_one] at h
    have hψ : (b : G) * Φ.ψ y = Φ.ψ y * (b : G) := by
      calc (b : G) * Φ.ψ y = ((b : G) * Φ.ψ y * (b : G)⁻¹) * (b : G) := by group
        _ = Φ.ψ y * (b : G) := by conv_rhs => rw [h]
    exact hψ.symm
  · intro hb
    have hcent : ∀ y : ↥(orthDerived Φ.Q), Φ.β b * y = y * Φ.β b := by
      intro y
      have hy : Φ.ψ y ∈ L := p9uOA_mem_range Φ y
      have h1 := (Subgroup.mem_centralizer_iff.mp hb) (Φ.ψ y) hy
      have hc : (b : G) * Φ.ψ y * (b : G)⁻¹ = Φ.ψ y := by
        rw [h1.symm]; group
      have h2 : Φ.β b * y * (Φ.β b)⁻¹ = y := by
        apply Φ.hinj
        rw [Φ.hcompat b y]
        exact hc
      calc Φ.β b * y = (Φ.β b * y * (Φ.β b)⁻¹) * Φ.β b := by group
        _ = y * Φ.β b := by rw [h2]
    exact p9uOA_center_eq_bot Φ hZ hcent

private theorem p9uOA_single_mem {p : ℕ} {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥)
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G)) (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin Φ.r) (a : Multiplicative (ZMod p)) :
    ∃ b : ↥Bs, (b : G) ∈ L ∧ Φ.β b = Φ.Δ.τΩ Φ.hA (Pi.mulSingle i a) := by
  haveI : Nontrivial (Fin Φ.r) := Fin.nontrivial_iff_two_le.mpr (by have := Φ.hr; omega)
  obtain ⟨j, hji⟩ : ∃ j : Fin Φ.r, j ≠ i := exists_ne i
  have hij : i ≠ j := hji.symm
  obtain ⟨w, hw, hwN⟩ := Φ.dinvReal i j hij
  set f : Fin Φ.r → Multiplicative (ZMod p) :=
    Pi.mulSingle i (a ^ ((p + 1) / 2)) with hfdef
  have hfi : f i ^ 2 = a := by
    rw [hfdef, Pi.mulSingle_eq_same, ← pow_mul]
    have hmul : ((p + 1) / 2) * 2 = p + 1 := by
      obtain ⟨k, hk⟩ : Odd p := hp.eq_two_or_odd'.resolve_left hp2
      omega
    rw [hmul, pow_succ, p9uOA_pow_prime a, one_mul]
  have hfj : f j = 1 := by
    rw [hfdef, Pi.mulSingle_eq_of_ne hji]
  have hfA : Φ.Δ.τ f ∈ Φ.A := le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩
  obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ f) hfA
  have hbτ : Φ.β b = Φ.Δ.τΩ Φ.hA f := by
    apply Subtype.ext
    simpa using hb
  have hw' : ∀ f' : Fin Φ.r → Multiplicative (ZMod p),
      w * Φ.Δ.τΩ Φ.hA f' * w⁻¹ = Φ.Δ.τΩ Φ.hA (dinv i j f') := by
    intro f'
    apply Subtype.ext
    simpa using hw f'
  set c : ↥Bs := ggConjAut Bs hwN b with hcdef
  have hβc : Φ.β c = w * Φ.β b * w⁻¹ :=
    (p9uOA_beta_conj Φ (fun z hz => p9uOA_center_eq_bot Φ hZ hz)
      (ggConjAut_apply Bs hwN b).symm).symm
  have hwL : Φ.ψ w ∈ L := p9uOA_mem_range Φ w
  have hbwb : (b : G) * Φ.ψ w * (b : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hBN b.2) (Φ.ψ w)).mp hwL
  refine ⟨b * c⁻¹, ?_, ?_⟩
  · change ((b * c⁻¹ : ↥Bs) : G) ∈ L
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcdef, ggConjAut_apply Bs hwN b]
    have heq : (b : G) * (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹)⁻¹
        = ((b : G) * Φ.ψ w * (b : G)⁻¹) * (Φ.ψ w)⁻¹ := by group
    rw [heq]
    exact L.mul_mem hbwb (L.inv_mem hwL)
  · rw [map_mul, map_inv, hβc, hbτ, hw']
    rw [← map_inv, ← map_mul]
    congr 1
    rw [mul_inv_dinv hij f, hfi, hfj, one_pow, Pi.mulSingle_one, mul_one]

theorem qtwoDL1_baseO_odd (ha₀ : GGLNoncyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥L = ⊥)
    {r₀ r₀' : MulAut ↥Bs} (hr₀ : r₀ ∈ ggAutomizer L Bs) (hrefl₀ : GGIsReflection p r₀)
    (hr₀' : r₀' ∈ ggAutomizer L Bs) (hrefl₀' : GGIsReflection p r₀')
    (hne : r₀ * r₀' ≠ r₀' * r₀) :
    Odd (Nat.card ↥(Subgroup.centralizer
      ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (L : Set G))) := by
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  have hBN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  have hKsA : Bs ⊓ Subgroup.centralizer (L : Set G) ≤
      (ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') :=
    le_inf (p9uOA_inf_le_hyperplane hr₀) (p9uOA_inf_le_hyperplane hr₀')
  set F' : Subgroup ↥(orthDerived Φ.Q) := ((Bs ⊓ L).subgroupOf Bs).map Φ.β with hF'def
  set Fc : Subgroup (Fin Φ.r → Multiplicative (ZMod p)) :=
    F'.comap (Φ.Δ.τΩ Φ.hA) with hFcdef
  have hS : (⊤ : Subgroup (Fin Φ.r → Multiplicative (ZMod p))) = Subgroup.closure
      (Set.range (fun ia : Fin Φ.r × Multiplicative (ZMod p) =>
        (Pi.mulSingle ia.1 ia.2 : Fin Φ.r → Multiplicative (ZMod p)))) := by
    refine le_antisymm ?_ le_top
    intro f _
    rw [← Finset.univ_prod_mulSingle f]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨(i, f i), rfl⟩
  have hSle : Set.range (fun ia : Fin Φ.r × Multiplicative (ZMod p) =>
      (Pi.mulSingle ia.1 ia.2 : Fin Φ.r → Multiplicative (ZMod p))) ≤ Fc := by
    rintro y ⟨⟨i, a⟩, rfl⟩
    rw [hFcdef]
    change (Pi.mulSingle i a : Fin Φ.r → Multiplicative (ZMod p)) ∈
      F'.comap (Φ.Δ.τΩ Φ.hA)
    rw [Subgroup.mem_comap]
    obtain ⟨b, hbL, hbβ⟩ := p9uOA_single_mem Φ hZ hBN hpp hp2 i a
    exact Subgroup.mem_map.mpr ⟨b, ⟨b.2, hbL⟩, hbβ⟩
  have hFc : Fc = ⊤ :=
    eq_top_iff.mpr (by rw [hS]; exact (Subgroup.closure_le _).mpr hSle)
  have hT : (Φ.Δ.τΩ Φ.hA).range ≤ F' := by
    calc (Φ.Δ.τΩ Φ.hA).range
        = (⊤ : Subgroup (Fin Φ.r → Multiplicative (ZMod p))).map (Φ.Δ.τΩ Φ.hA) :=
          MonoidHom.range_eq_map _
      _ = Fc.map (Φ.Δ.τΩ Φ.hA) := by rw [hFc]
      _ ≤ F' := by
          rw [hFcdef]
          exact Subgroup.map_comap_le (f := Φ.Δ.τΩ Φ.hA) F'
  refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le ?_)
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  let B : ↥Bs := ⟨b, hb⟩
  have hbβ : Φ.β B ∈ (Φ.Δ.τΩ Φ.hA).range := by
    rw [← p9uOA_range_beta Φ]
    exact ⟨B, rfl⟩
  obtain ⟨k, hk, hβk⟩ := Subgroup.mem_map.mp (hT hbβ)
  have hkL : (k : G) ∈ L := hk.2
  have huβ : Φ.β (B * k⁻¹) = 1 := by
    rw [map_mul, map_inv, hβk, mul_inv_cancel]
  have huC : ((B * k⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (L : Set G) :=
    (p9uOA_beta_eq_one_iff Φ hZ (B * k⁻¹)).mp huβ
  have huA : ((B * k⁻¹ : ↥Bs) : G) ∈
      (ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') :=
    hKsA ⟨(B * k⁻¹).2, huC⟩
  have htA := (Subgroup.mem_centralizer_iff.mp ht.1) ((B * k⁻¹ : ↥Bs) : G) huA
  have htL := (Subgroup.mem_centralizer_iff.mp ht.2) (k : G) hkL
  change (B : G) * t = t * (B : G)
  calc (B : G) * t
      = (((B * k⁻¹ : ↥Bs) : G) * (k : G)) * t := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
    _ = ((B * k⁻¹ : ↥Bs) : G) * ((k : G) * t) := by group
    _ = ((B * k⁻¹ : ↥Bs) : G) * (t * (k : G)) := by rw [htL]
    _ = t * (((B * k⁻¹ : ↥Bs) : G) * (k : G)) := by rw [← mul_assoc, htA]; group
    _ = t * (B : G) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]; group

end CFSG.StandardType.QTwo

end
