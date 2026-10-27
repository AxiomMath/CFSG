module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

namespace B48Om

private theorem eq_one_of_mem_centralizer {G : Type} [Group G] {N : Subgroup G}
    (hZ : Subgroup.center ↥N = ⊥) {z : G} (hzN : z ∈ N)
    (hzC : z ∈ Subgroup.centralizer (N : Set G)) : z = 1 := by
  have hmem : (⟨z, hzN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (k : G) k.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem inv_mul_mem_centralizer {G : Type} [Group G] {N : Subgroup G} {b g : G}
    (h : ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) :
    g⁻¹ * b ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hbk : b * k = g * k * g⁻¹ * b := by
    calc b * k = (b * k * b⁻¹) * b := by group
      _ = g * k * g⁻¹ * b := by rw [h k hk]
  calc k * (g⁻¹ * b) = g⁻¹ * (g * k * g⁻¹ * b) := by group
    _ = g⁻¹ * (b * k) := by rw [hbk]
    _ = g⁻¹ * b * k := by group

private theorem commute_of_conj_eq {G : Type} [Group G] {N : Subgroup G}
    (hZ : Subgroup.center ↥N = ⊥) {b b' g g' : G} (hgN : g ∈ N) (hg'N : g' ∈ N)
    (hc : g⁻¹ * b ∈ Subgroup.centralizer (N : Set G))
    (hc' : g'⁻¹ * b' ∈ Subgroup.centralizer (N : Set G)) (hbb : b * b' = b' * b) :
    g * g' = g' * g := by
  set c := g⁻¹ * b with hcdef
  set c' := g'⁻¹ * b' with hc'def
  have hb : b = g * c := by rw [hcdef]; group
  have hb' : b' = g' * c' := by rw [hc'def]; group
  have hcg' : g' * c = c * g' := Subgroup.mem_centralizer_iff.mp hc g' hg'N
  have hc'g : g * c' = c' * g := Subgroup.mem_centralizer_iff.mp hc' g hgN
  have h1 : g * g' * (c * c') = g' * g * (c' * c) := by
    have e1 : g * c * (g' * c') = g * g' * (c * c') := by
      calc g * c * (g' * c') = g * (c * g') * c' := by group
        _ = g * (g' * c) * c' := by rw [hcg']
        _ = g * g' * (c * c') := by group
    have e2 : g' * c' * (g * c) = g' * g * (c' * c) := by
      calc g' * c' * (g * c) = g' * (c' * g) * c := by group
        _ = g' * (g * c') * c := by rw [hc'g]
        _ = g' * g * (c' * c) := by group
    rw [← e1, ← e2, ← hb, ← hb', hbb]
  have hw : (g' * g)⁻¹ * (g * g') = (c' * c) * (c * c')⁻¹ := by
    calc (g' * g)⁻¹ * (g * g') = (g' * g)⁻¹ * (g * g' * (c * c')) * (c * c')⁻¹ := by group
      _ = (g' * g)⁻¹ * (g' * g * (c' * c)) * (c * c')⁻¹ := by rw [h1]
      _ = (c' * c) * (c * c')⁻¹ := by group
  have hwN : (g' * g)⁻¹ * (g * g') ∈ N :=
    N.mul_mem (N.inv_mem (N.mul_mem hg'N hgN)) (N.mul_mem hgN hg'N)
  have hwC : (g' * g)⁻¹ * (g * g') ∈ Subgroup.centralizer (N : Set G) := by
    rw [hw]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc' hc)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hc'))
  have h1' := eq_one_of_mem_centralizer hZ hwN hwC
  exact (inv_mul_eq_one.mp h1').symm

theorem exists_mem_inf_mul {G : Type} [Group G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) :
    ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ N, g⁻¹ * b ∈ Subgroup.centralizer (N : Set G) := by
  intro b hb
  obtain ⟨g, hgN, hgb⟩ := hinner b hb
  have hc : g⁻¹ * b ∈ Subgroup.centralizer (N : Set G) := inv_mul_mem_centralizer hgb
  have hgC : g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    obtain ⟨g', hg'N, hg'b⟩ := hinner b' hb'
    have hc' : g'⁻¹ * b' ∈ Subgroup.centralizer (N : Set G) := inv_mul_mem_centralizer hg'b
    have hbb : b * b' = b' * b := by
      have h := hBs.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩
      exact congrArg Subtype.val h
    have hgg' : g * g' = g' * g := commute_of_conj_eq hZ hgN hg'N hc hc' hbb
    have hc'g : g * (g'⁻¹ * b') = (g'⁻¹ * b') * g := Subgroup.mem_centralizer_iff.mp hc' g hgN
    calc b' * g = g' * (g'⁻¹ * b') * g := by group
      _ = g' * (g * (g'⁻¹ * b')) := by rw [hc'g]; group
      _ = g' * g * (g'⁻¹ * b') := by group
      _ = g * g' * (g'⁻¹ * b') := by rw [hgg']
      _ = g * b' := by group
  have hgp : g ^ p = 1 := by
    have hcomm : Commute g (g⁻¹ * b) := Subgroup.mem_centralizer_iff.mp hc g hgN
    have hbp : b ^ p = 1 := hBs.2.1.2 b hb
    have hprod : g ^ p * (g⁻¹ * b) ^ p = 1 := by
      rw [← hcomm.mul_pow, show g * (g⁻¹ * b) = b by group, hbp]
    have hgpC : g ^ p ∈ Subgroup.centralizer (N : Set G) := by
      rw [eq_inv_of_mul_eq_one_left hprod]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
    exact eq_one_of_mem_centralizer hZ (N.pow_mem hgN p) hgpC
  exact ⟨g, Subgroup.mem_inf.mpr ⟨hBs.2.2.2 g hgC hgp, hgN⟩, hc⟩

theorem mem_inf_of_commute {G : Type} [Group G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) {t : G} (htN : t ∈ N)
    (htC : t ∈ Subgroup.centralizer ((Bs ⊓ N : Subgroup G) : Set G)) (htp : t ^ p = 1) :
    t ∈ Bs ⊓ N := by
  refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 t ?_ htp, htN⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨g, hgE, hc⟩ := exists_mem_inf_mul hBs hZ hinner b hb
  have htg : g * t = t * g := Subgroup.mem_centralizer_iff.mp htC g hgE
  have htc : t * (g⁻¹ * b) = (g⁻¹ * b) * t := Subgroup.mem_centralizer_iff.mp hc t htN
  calc b * t = g * ((g⁻¹ * b) * t) := by group
    _ = g * (t * (g⁻¹ * b)) := by rw [htc]
    _ = (g * t) * (g⁻¹ * b) := by group
    _ = (t * g) * (g⁻¹ * b) := by rw [htg]
    _ = t * b := by group

private theorem conj_mem_of_split {G : Type} [Group G] {Bs N : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ N, g⁻¹ * b ∈ Subgroup.centralizer (N : Set G)) {s : G}
    (hsN : s ∈ N) (hsE : s ∈ Subgroup.normalizer ((Bs ⊓ N : Subgroup G) : Set G)) {b : G}
    (hb : b ∈ Bs) : s * b * s⁻¹ ∈ Bs := by
  obtain ⟨g, hgE, hc⟩ := hsplit b hb
  have hsc : s * (g⁻¹ * b) = (g⁻¹ * b) * s := Subgroup.mem_centralizer_iff.mp hc s hsN
  have hsg : s * g * s⁻¹ ∈ Bs ⊓ N := (Subgroup.mem_normalizer_iff.mp hsE g).mp hgE
  have heq : s * b * s⁻¹ = (s * g * s⁻¹) * (g⁻¹ * b) := by
    calc s * b * s⁻¹ = s * g * s⁻¹ * (s * (g⁻¹ * b) * s⁻¹) := by group
      _ = s * g * s⁻¹ * ((g⁻¹ * b) * s * s⁻¹) := by rw [hsc]
      _ = (s * g * s⁻¹) * (g⁻¹ * b) := by group
  rw [heq]
  exact Bs.mul_mem (Subgroup.mem_inf.mp hsg).1
    (Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp hgE).1) hb)

theorem mem_normalizer_of_split {G : Type} [Group G] {Bs N : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ N, g⁻¹ * b ∈ Subgroup.centralizer (N : Set G)) {s : G}
    (hsN : s ∈ N) (hsE : s ∈ Subgroup.normalizer ((Bs ⊓ N : Subgroup G) : Set G)) :
    s ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact conj_mem_of_split hsplit hsN hsE
  · intro hb
    have h := conj_mem_of_split hsplit (N.inv_mem hsN) (Subgroup.inv_mem _ hsE) hb
    rwa [show s⁻¹ * (s * b * s⁻¹) * s⁻¹⁻¹ = b by group] at h

theorem mem_normalizer_of_mem_inf {G : Type} [Group G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) {s : G} (hsN : s ∈ N)
    (hsE : s ∈ Subgroup.normalizer ((Bs ⊓ N : Subgroup G) : Set G)) :
    s ∈ Subgroup.normalizer (Bs : Set G) :=
  mem_normalizer_of_split (exists_mem_inf_mul hBs hZ hinner) hsN hsE

theorem bstar_transport_of_split {G : Type} [Group G] {Bs J : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J, g⁻¹ * b ∈ Subgroup.centralizer (J : Set G)) :
    Bs = (Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)) ∧
      J ⊓ Subgroup.normalizer (Bs : Set G) =
        J ⊓ Subgroup.normalizer (((Bs ⊓ J : Subgroup G)) : Set G) ∧
      J ⊓ Subgroup.centralizer (Bs : Set G) =
        J ⊓ Subgroup.centralizer (((Bs ⊓ J : Subgroup G)) : Set G) := by
  let E : Subgroup G := Bs ⊓ J
  let U : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hsplit' : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J,
      ∃ u ∈ Bs ⊓ Subgroup.centralizer (J : Set G), b = g * u := by
    intro b hb
    obtain ⟨g, hgE, hc⟩ := hsplit b hb
    refine ⟨g, hgE, g⁻¹ * b,
      Subgroup.mem_inf.mpr ⟨Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp hgE).1) hb, hc⟩, ?_⟩
    group
  have hsup : Bs = E ⊔ U := by
    apply le_antisymm
    · intro b hb
      obtain ⟨g, hgE, u, huU, rfl⟩ := hsplit' b hb
      exact Subgroup.mul_mem_sup hgE huU
    · exact sup_le inf_le_left inf_le_left
  have hN_le : J ⊓ Subgroup.normalizer (Bs : Set G) ≤
      J ⊓ Subgroup.normalizer (E : Set G) := by
    intro s hs
    obtain ⟨hsJ, hsN⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨hsJ, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxE
      have hxBs : x ∈ Bs := (Subgroup.mem_inf.mp hxE).1
      have hxJ : x ∈ J := (Subgroup.mem_inf.mp hxE).2
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hsN x).mp hxBs,
         (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hsJ) x).mp hxJ⟩
    · intro hxE
      have hxBs : x ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hsN x).mpr (Subgroup.mem_inf.mp hxE).1
      have hxJ : x ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hsJ) x).mpr
          (Subgroup.mem_inf.mp hxE).2
      exact Subgroup.mem_inf.mpr ⟨hxBs, hxJ⟩
  have hN_ge : J ⊓ Subgroup.normalizer (E : Set G) ≤
      J ⊓ Subgroup.normalizer (Bs : Set G) := by
    intro s hs
    obtain ⟨hsJ, hsE⟩ := Subgroup.mem_inf.mp hs
    exact Subgroup.mem_inf.mpr ⟨hsJ,
      mem_normalizer_of_split hsplit hsJ hsE⟩
  have hC_le : J ⊓ Subgroup.centralizer (Bs : Set G) ≤
      J ⊓ Subgroup.centralizer (E : Set G) := by
    intro s hs
    obtain ⟨hsJ, hsC⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨hsJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hxE
    exact Subgroup.mem_centralizer_iff.mp hsC x (Subgroup.mem_inf.mp hxE).1
  have hC_ge : J ⊓ Subgroup.centralizer (E : Set G) ≤
      J ⊓ Subgroup.centralizer (Bs : Set G) := by
    intro s hs
    obtain ⟨hsJ, hsC⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨hsJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨g, hgE, u, huU, rfl⟩ := hsplit' b hb
    have hgs : g * s = s * g := Subgroup.mem_centralizer_iff.mp hsC g hgE
    have hus : s * u = u * s :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huU).2 s hsJ
    calc
      (g * u) * s = g * (u * s) := by group
      _ = g * (s * u) := by rw [← hus]
      _ = (g * s) * u := by group
      _ = (s * g) * u := by rw [hgs]
      _ = s * (g * u) := by group
  simpa only [E, U] using
    ⟨hsup, le_antisymm hN_le hN_ge, le_antisymm hC_le hC_ge⟩

private def conjAut {G : Type} [Group G] {Bs : Subgroup G} (s : G)
    (hs : s ∈ Subgroup.normalizer (Bs : Set G)) : MulAut ↥Bs where
  toFun b := ⟨s * (b : G) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs (b : G)).mp b.2⟩
  invFun b := ⟨s⁻¹ * (b : G) * s,
    (Subgroup.mem_normalizer_iff.mp hs (s⁻¹ * (b : G) * s)).mpr (by
      rw [show s * (s⁻¹ * (b : G) * s) * s⁻¹ = (b : G) by group]
      exact b.2)⟩
  left_inv b := by
    apply Subtype.ext
    show s⁻¹ * (s * (b : G) * s⁻¹) * s = (b : G)
    group
  right_inv b := by
    apply Subtype.ext
    show s * (s⁻¹ * (b : G) * s) * s⁻¹ = (b : G)
    group
  map_mul' b b' := by
    apply Subtype.ext
    show s * ((b * b' : ↥Bs) : G) * s⁻¹ = (s * (b : G) * s⁻¹) * (s * (b' : G) * s⁻¹)
    rw [Subgroup.coe_mul]
    group

private theorem conjAut_apply {G : Type} [Group G] {Bs : Subgroup G} (s : G)
    (hs : s ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ((conjAut s hs b : ↥Bs) : G) = s * (b : G) * s⁻¹ := rfl

theorem card_le_ggAutomizer {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) {ι : Type} (s : ι → G)
    (hsN : ∀ i, s i ∈ N) (hsE : ∀ i, s i ∈ Subgroup.normalizer ((Bs ⊓ N : Subgroup G) : Set G))
    (hdist : ∀ i j, (∀ e ∈ Bs ⊓ N, s i * e * (s i)⁻¹ = s j * e * (s j)⁻¹) → i = j) :
    Nat.card ι ≤ Nat.card (ggAutomizer N Bs) := by
  have hsB : ∀ i, s i ∈ Subgroup.normalizer (Bs : Set G) := fun i =>
    mem_normalizer_of_mem_inf hBs hZ hinner (hsN i) (hsE i)
  let f : ι → ↥(ggAutomizer N Bs) := fun i =>
    ⟨conjAut (s i) (hsB i),
      Subgroup.subset_closure ⟨s i, hsN i, hsB i, fun b => conjAut_apply _ _ b⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval : conjAut (s i) (hsB i) = conjAut (s j) (hsB j) := congrArg Subtype.val hij
    apply hdist i j
    intro e he
    have h := congrArg (fun φ : MulAut ↥Bs => ((φ ⟨e, (Subgroup.mem_inf.mp he).1⟩ : ↥Bs) : G))
      hval
    simpa only [conjAut_apply] using h
  exact Nat.card_le_card_of_injective f hf

noncomputable def ggAutomizer_restrictEquiv_of_split {G : Type} [Group G] {Bs J : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J, g⁻¹ * b ∈ Subgroup.centralizer (J : Set G)) :
    ggAutomizer J Bs ≃* ggAutomizer J (Bs ⊓ J) := by
  classical
  let E : Subgroup G := Bs ⊓ J
  let N : Subgroup G := J ⊓ Subgroup.normalizer (Bs : Set G)
  let C : Subgroup G := J ⊓ Subgroup.centralizer (Bs : Set G)
  have htr := bstar_transport_of_split hsplit
  have hN_E : N = J ⊓ Subgroup.normalizer (E : Set G) := by
    dsimp [N, E]
    exact htr.2.1
  have hC_E : C = J ⊓ Subgroup.centralizer (E : Set G) := by
    dsimp [C, E]
    exact htr.2.2
  have hNE : N ≤ Subgroup.normalizer (E : Set G) := by
    rw [hN_E]
    exact inf_le_right
  let ρBs : ↥N →* MulAut ↥Bs :=
    (Subgroup.normalizerMonoidHom Bs).comp
      (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G)))
  let ρE : ↥N →* MulAut ↥E :=
    (Subgroup.normalizerMonoidHom E).comp (Subgroup.inclusion hNE)
  have hkerBs : ρBs.ker = C.subgroupOf N := by
    rw [show ρBs = (Subgroup.normalizerMonoidHom Bs).comp
          (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G))) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, C]
    simp [show (x : G) ∈ J from (Subgroup.mem_inf.mp x.2).1]
  have hkerE : ρE.ker = (J ⊓ Subgroup.centralizer (E : Set G)).subgroupOf N := by
    rw [show ρE = (Subgroup.normalizerMonoidHom E).comp
          (Subgroup.inclusion hNE) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp [show (x : G) ∈ J from (Subgroup.mem_inf.mp x.2).1]
  have hkerEq : ρBs.ker = ρE.ker := by
    rw [hkerBs, hkerE, hC_E]
  have hRangeBs : ρBs.range = ggAutomizer J Bs := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hφ
      rw [mem_ggAutomizer_iff]
      exact ⟨(n : G), (Subgroup.mem_inf.mp n.2).1, (Subgroup.mem_inf.mp n.2).2,
        fun b => Subgroup.normalizerMonoidHom_apply_apply_coe Bs
          (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G)) n) b⟩
    · intro hφ
      obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hφ
      let n : ↥N := ⟨g, Subgroup.mem_inf.mpr ⟨hgJ, hgN⟩⟩
      refine MonoidHom.mem_range.mpr ⟨n, ?_⟩
      ext b
      dsimp [ρBs]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hgact b).symm
  have hRangeE : ρE.range = ggAutomizer J E := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hφ
      rw [mem_ggAutomizer_iff]
      have hnE : (n : G) ∈ Subgroup.normalizer (E : Set G) := by
        have hn : (n : G) ∈ J ⊓ Subgroup.normalizer (E : Set G) := by
          rw [← hN_E]
          exact n.2
        exact (Subgroup.mem_inf.mp hn).2
      exact ⟨(n : G), (Subgroup.mem_inf.mp n.2).1, hnE,
        fun b => Subgroup.normalizerMonoidHom_apply_apply_coe E
          (Subgroup.inclusion hNE n) b⟩
    · intro hφ
      obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hφ
      have hnN : g ∈ N := by
        rw [hN_E]
        exact Subgroup.mem_inf.mpr ⟨hgJ, hgN⟩
      let n : ↥N := ⟨g, hnN⟩
      refine MonoidHom.mem_range.mpr ⟨n, ?_⟩
      ext b
      dsimp [ρE]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hgact b).symm
  exact (MulEquiv.subgroupCongr hRangeBs).symm.trans
    ((QuotientGroup.quotientKerEquivRange ρBs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        ((QuotientGroup.quotientKerEquivRange ρE).trans (MulEquiv.subgroupCongr hRangeE))))

noncomputable def ggAutomizer_restrictEquiv {G : Type} [Group G] {p : ℕ} {B Bs J : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥J = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ x ∈ J, b * x * b⁻¹ = j * x * j⁻¹) :
    ggAutomizer J Bs ≃* ggAutomizer J (Bs ⊓ J) :=
  ggAutomizer_restrictEquiv_of_split (exists_mem_inf_mul hBs hZ hinner)

theorem ggAutomizer_card_eq_of_split {G : Type} [Group G] {Bs J : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J, g⁻¹ * b ∈ Subgroup.centralizer (J : Set G)) :
    Nat.card (ggAutomizer J Bs) = Nat.card (ggAutomizer J (Bs ⊓ J)) :=
  Nat.card_congr (ggAutomizer_restrictEquiv_of_split hsplit).toEquiv

theorem ggAutomizer_card_eq {G : Type} [Group G] {p : ℕ} {B Bs J : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥J = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ x ∈ J, b * x * b⁻¹ = j * x * j⁻¹) :
    Nat.card (ggAutomizer J Bs) = Nat.card (ggAutomizer J (Bs ⊓ J)) :=
  Nat.card_congr (ggAutomizer_restrictEquiv hBs hZ hinner).toEquiv

theorem ggAutomizer_restrictEquiv_of_split_apply_coe {G : Type} [Group G] {Bs J : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J, g⁻¹ * b ∈ Subgroup.centralizer (J : Set G))
    (a : ggAutomizer J Bs) (x : ↥(Bs ⊓ J)) :
    (((ggAutomizer_restrictEquiv_of_split hsplit a : MulAut ↥(Bs ⊓ J)) x : ↥(Bs ⊓ J)) : G) =
      (((a : MulAut ↥Bs) (Subgroup.inclusion inf_le_left x) : ↥Bs) : G) := by
  classical
  let E : Subgroup G := Bs ⊓ J
  let N : Subgroup G := J ⊓ Subgroup.normalizer (Bs : Set G)
  let C : Subgroup G := J ⊓ Subgroup.centralizer (Bs : Set G)
  have htr := bstar_transport_of_split hsplit
  have hN_E : N = J ⊓ Subgroup.normalizer (E : Set G) := by
    dsimp [N, E]
    exact htr.2.1
  have hC_E : C = J ⊓ Subgroup.centralizer (E : Set G) := by
    dsimp [C, E]
    exact htr.2.2
  have hNE : N ≤ Subgroup.normalizer (E : Set G) := by
    rw [hN_E]
    exact inf_le_right
  let ρBs : ↥N →* MulAut ↥Bs :=
    (Subgroup.normalizerMonoidHom Bs).comp
      (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G)))
  let ρE : ↥N →* MulAut ↥E :=
    (Subgroup.normalizerMonoidHom E).comp (Subgroup.inclusion hNE)
  have hkerBs : ρBs.ker = C.subgroupOf N := by
    rw [show ρBs = (Subgroup.normalizerMonoidHom Bs).comp
          (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G))) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, C]
    simp [show (y : G) ∈ J from (Subgroup.mem_inf.mp y.2).1]
  have hkerE : ρE.ker = (J ⊓ Subgroup.centralizer (E : Set G)).subgroupOf N := by
    rw [show ρE = (Subgroup.normalizerMonoidHom E).comp
          (Subgroup.inclusion hNE) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp [show (y : G) ∈ J from (Subgroup.mem_inf.mp y.2).1]
  have hkerEq : ρBs.ker = ρE.ker := by
    rw [hkerBs, hkerE, hC_E]
  have hRangeBs : ρBs.range = ggAutomizer J Bs := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hφ
      rw [mem_ggAutomizer_iff]
      exact ⟨(n : G), (Subgroup.mem_inf.mp n.2).1, (Subgroup.mem_inf.mp n.2).2,
        fun b => Subgroup.normalizerMonoidHom_apply_apply_coe Bs
          (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (Bs : Set G)) n) b⟩
    · intro hφ
      obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hφ
      let n : ↥N := ⟨g, Subgroup.mem_inf.mpr ⟨hgJ, hgN⟩⟩
      refine MonoidHom.mem_range.mpr ⟨n, ?_⟩
      ext b
      dsimp [ρBs]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hgact b).symm
  have hRangeE : ρE.range = ggAutomizer J E := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hφ
      rw [mem_ggAutomizer_iff]
      have hnE : (n : G) ∈ Subgroup.normalizer (E : Set G) := by
        have hn : (n : G) ∈ J ⊓ Subgroup.normalizer (E : Set G) := by
          rw [← hN_E]
          exact n.2
        exact (Subgroup.mem_inf.mp hn).2
      exact ⟨(n : G), (Subgroup.mem_inf.mp n.2).1, hnE,
        fun b => Subgroup.normalizerMonoidHom_apply_apply_coe E
          (Subgroup.inclusion hNE n) b⟩
    · intro hφ
      obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hφ
      have hnN : g ∈ N := by
        rw [hN_E]
        exact Subgroup.mem_inf.mpr ⟨hgJ, hgN⟩
      let n : ↥N := ⟨g, hnN⟩
      refine MonoidHom.mem_range.mpr ⟨n, ?_⟩
      ext b
      dsimp [ρE]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hgact b).symm
  have hdef :
      ggAutomizer_restrictEquiv_of_split hsplit =
        (MulEquiv.subgroupCongr hRangeBs).symm.trans
          ((QuotientGroup.quotientKerEquivRange ρBs).symm.trans
            ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
              ((QuotientGroup.quotientKerEquivRange ρE).trans (MulEquiv.subgroupCongr hRangeE)))) := by
    dsimp [ggAutomizer_restrictEquiv_of_split, E, N, C, hN_E, hC_E, hNE, ρBs, ρE, hkerBs, hkerE,
      hkerEq, hRangeBs, hRangeE]
  obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp a.2
  let n : ↥N := ⟨g, Subgroup.mem_inf.mpr ⟨hgJ, hgN⟩⟩
  have hρ : (ρBs n : MulAut ↥Bs) = (a : MulAut ↥Bs) := by
    ext b
    dsimp [ρBs]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (hgact b).symm
  have ha_eq : a = (MulEquiv.subgroupCongr hRangeBs)
      (QuotientGroup.quotientKerEquivRange ρBs (QuotientGroup.mk n)) := by
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply,
      TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk]
    exact hρ.symm
  rw [hdef]
  simp only [MulEquiv.trans_apply]
  rw [ha_eq]
  simp only [MulEquiv.symm_apply_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk]
  simp only [MulEquiv.subgroupCongr_apply,
    TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk]
  simp [ρE, ρBs, MonoidHom.comp_apply]

theorem central_factor_fixed {G : Type} [Group G] {Bs J : Subgroup G}
    {n u : G} (hnJ : n ∈ J)
    (hu : u ∈ Bs ⊓ Subgroup.centralizer (J : Set G)) : n * u * n⁻¹ = u := by
  have hcomm : n * u = u * n :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 n hnJ
  calc
    n * u * n⁻¹ = (u * n) * n⁻¹ := by rw [hcomm]
    _ = u := by group

theorem ggAutomizer_central_factor_fixed {G : Type} [Group G] {Bs J : Subgroup G}
    (φ : ggAutomizer J Bs) {u : G}
    (hu : u ∈ Bs ⊓ Subgroup.centralizer (J : Set G)) :
    ((φ : MulAut ↥Bs) ⟨u, (Subgroup.mem_inf.mp hu).1⟩ : ↥Bs) =
      ⟨u, (Subgroup.mem_inf.mp hu).1⟩ := by
  obtain ⟨g, hgJ, _, hgact⟩ := mem_ggAutomizer_iff.mp φ.2
  apply Subtype.ext
  rw [hgact]
  exact central_factor_fixed hgJ hu

end B48Om

end CFSG.StandardType

end
