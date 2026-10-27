module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Sections

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open scoped Pointwise

private theorem cfCover {X Y : Type} [Group X] [Group Y] (f : X →* Y) {L : Type} [Group L]
    (N M : Subgroup Y) (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (hs : IsSimpleGroup (M ⧸ N.subgroupOf M)) (e : (M ⧸ N.subgroupOf M) ≃* L)
    (hcov : ∀ m ∈ M, ∃ x : X, ∃ n ∈ N, f x * n = m) : E1.IsCompositionFactor X L := by
  haveI := hN
  haveI := hs
  let g : ↥(M.comap f) →* ↥M :=
    (f.comp (M.comap f).subtype).codRestrict M (fun x => Subgroup.mem_comap.mp x.2)
  let Φ : ↥(M.comap f) →* ↥M ⧸ N.subgroupOf M := (QuotientGroup.mk' (N.subgroupOf M)).comp g
  have hΦ : ∀ x : ↥(M.comap f), Φ x = ((g x : ↥M) : ↥M ⧸ N.subgroupOf M) := fun x => rfl
  have hker : Φ.ker = (N.comap f).subgroupOf (M.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, hΦ, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
    subst hm
    obtain ⟨x, n, hn, hxn⟩ := hcov m.1 m.2
    have hfx : x ∈ M.comap f := by
      rw [Subgroup.mem_comap]
      have hfx' : f x = m.1 * n⁻¹ := by rw [← hxn]; group
      rw [hfx']
      exact M.mul_mem m.2 (M.inv_mem (hNM hn))
    refine ⟨⟨x, hfx⟩, ?_⟩
    have key : ((g ⟨x, hfx⟩)⁻¹ * m : ↥M).1 = n := by
      show (f x)⁻¹ * m.1 = n
      rw [← hxn]
      group
    rw [hΦ, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf, key]
    exact hn
  haveI hKn : ((N.comap f).subgroupOf (M.comap f)).Normal := by
    rw [← hker]
    infer_instance
  let Ψ : (↥(M.comap f) ⧸ (N.comap f).subgroupOf (M.comap f)) ≃* (↥M ⧸ N.subgroupOf M) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj)
  unfold E1.IsCompositionFactor
  exact ⟨N.comap f, M.comap f, hKn, Subgroup.comap_mono hNM, hNs.comap f, hMs.comap f,
    Ψ.isSimpleGroup, ⟨Ψ.trans e⟩⟩

private theorem normalMapSubgroupOf {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (M N : Subgroup X) (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal) :
    ((N.map f).subgroupOf (M.map f)).Normal := by
  constructor
  intro n hn g
  obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
  have hkm : m * k * m⁻¹ ∈ N := by
    have h1 := hN.conj_mem ⟨k, hNM hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have e : ((g * n * g⁻¹ : ↥(M.map f)) : Y) = f (m * k * m⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hmg, hkn]
  rw [Subgroup.mem_subgroupOf, e]
  exact Subgroup.mem_map_of_mem f hkm

private theorem cfPush {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) {L : Type} [Group L] (N M : Subgroup X) (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (hs : IsSimpleGroup (M ⧸ N.subgroupOf M)) (e : (M ⧸ N.subgroupOf M) ≃* L)
    (hker : ∀ m ∈ M, f m ∈ N.map f → m ∈ N) : E1.IsCompositionFactor Y L := by
  haveI := hN
  haveI := hs
  have hnorm : ((N.map f).subgroupOf (M.map f)).Normal :=
    normalMapSubgroupOf f M N hNM hN
  haveI := hnorm
  let g : ↥M →* ↥(M.map f) :=
    (f.comp M.subtype).codRestrict (M.map f) (fun m => Subgroup.mem_map_of_mem f m.2)
  let Θ : ↥M →* ↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f) :=
    (QuotientGroup.mk' ((N.map f).subgroupOf (M.map f))).comp g
  have hΘsurj : Function.Surjective Θ := by
    intro q
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective ((N.map f).subgroupOf (M.map f)) q
    obtain ⟨m, hm, hfm⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨m, hm⟩, ?_⟩
    have hgm : g ⟨m, hm⟩ = y := Subtype.ext hfm
    rw [← hy]
    show QuotientGroup.mk' _ (g ⟨m, hm⟩) = QuotientGroup.mk' _ y
    rw [hgm]
  have hΘker : Θ.ker = N.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (g x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact hker x.1 x.2 h1
    · intro h1
      exact Subgroup.mem_map_of_mem f h1
  let Ψ : (↥M ⧸ N.subgroupOf M) ≃* (↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f)) :=
    (QuotientGroup.quotientMulEquivOfEq hΘker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj)
  have hsimp : IsSimpleGroup (↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f)) :=
    Ψ.symm.isSimpleGroup
  unfold E1.IsCompositionFactor
  exact ⟨N.map f, M.map f, hnorm, Subgroup.map_mono hNM, hNs.map hf, hMs.map hf, hsimp,
    ⟨Ψ.symm.trans e⟩⟩


theorem isCompositionFactor_of_normal {X : Type} [Group X] (A : Subgroup X) [A.Normal]
    {L : Type} [Group L] (h : E1.IsCompositionFactor X L) :
    E1.IsCompositionFactor ↥A L ∨ E1.IsCompositionFactor (X ⧸ A) L := by
  classical
  obtain ⟨N, M, hN, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  haveI := hN
  haveI := hs
  by_cases hK : (M ⊓ A) ⊔ N = M
  · left
    have hLE : M ⊓ A ≤ Subgroup.normalizer (N : Set X) := fun x hx =>
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hN (Subgroup.mem_inf.mp hx).1
    refine cfCover A.subtype N M hNM hN hNs hMs hs e ?_
    intro m hm
    have hm' : m ∈ ((M ⊓ A : Subgroup X) : Set X) * (N : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (M ⊓ A) N hLE, hK]
      exact hm
    obtain ⟨a, ha, n, hn, han⟩ := Set.mem_mul.mp hm'
    exact ⟨⟨a, (Subgroup.mem_inf.mp ha).2⟩, n, hn, han⟩
  · right
    have hle : M ⊓ A ≤ N := by
      haveI : ((A.subgroupOf M ⊔ N.subgroupOf M).map
          (QuotientGroup.mk' (N.subgroupOf M))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      rcases Subgroup.Normal.eq_bot_or_eq_top
          ((A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) with
        hS | hS
      · intro x hx
        have h1 : ((⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥M) : ↥M ⧸ N.subgroupOf M) ∈
            (A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) :=
          Subgroup.mem_map_of_mem _
            (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hx).2))
        rw [hS, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      · exfalso
        apply hK
        have htop : ∀ y : ↥M, y ∈ A.subgroupOf M ⊔ N.subgroupOf M := by
          intro y
          have h1 : QuotientGroup.mk' (N.subgroupOf M) y ∈
              (A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) := by
            rw [hS]
            exact Subgroup.mem_top _
          obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp h1
          obtain ⟨z, hz, hkz⟩ := (QuotientGroup.mk'_eq_mk' (N.subgroupOf M)).mp hky
          rw [← hkz]
          exact Subgroup.mul_mem _ hk (Subgroup.mem_sup_right hz)
        refine le_antisymm (sup_le inf_le_left hNM) (fun m hm => ?_)
        obtain ⟨a, ha, q, hq, haq⟩ :=
          Subgroup.mem_sup_of_normal_right.mp (htop ⟨m, hm⟩)
        have hm_eq : m = (a : X) * (q : X) := (congrArg Subtype.val haq).symm
        rw [hm_eq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨a.2, Subgroup.mem_subgroupOf.mp ha⟩)
          (Subgroup.mem_subgroupOf.mp hq)
    have hker : ∀ m ∈ M, (QuotientGroup.mk' A) m ∈ N.map (QuotientGroup.mk' A) → m ∈ N := by
      intro m hm hmN
      obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp hmN
      obtain ⟨z, hz, hnz⟩ := (QuotientGroup.mk'_eq_mk' A).mp hnm
      have hzM : z ∈ M := by
        have hz' : z = n⁻¹ * m := by
          rw [← hnz]
          group
        rw [hz']
        exact M.mul_mem (M.inv_mem (hNM hn)) hm
      have hzN : z ∈ N := hle (Subgroup.mem_inf.mpr ⟨hzM, hz⟩)
      rw [← hnz]
      exact N.mul_mem hn hzN
    exact cfPush (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A) N M hNM hN hNs hMs hs e
      hker

theorem isCompositionFactor_natCard_dvd {X : Type} [Group X] [Finite X] {L : Type} [Group L]
    (h : E1.IsCompositionFactor X L) : Nat.card L ∣ Nat.card X := by
  obtain ⟨N, M, hN, -, -, -, -, ⟨e⟩⟩ := h
  haveI := hN
  rw [← Nat.card_congr e.toEquiv]
  have h1 : Nat.card (↥M ⧸ N.subgroupOf M) ∣ Nat.card ↥M := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  exact h1.trans (Subgroup.card_subgroup_dvd_card M)

theorem isCompositionFactor_finite {X : Type} [Group X] [Finite X] {L : Type} [Group L]
    (h : E1.IsCompositionFactor X L) : Finite L := by
  obtain ⟨N, M, hN, -, -, -, -, ⟨e⟩⟩ := h
  haveI := hN
  exact Finite.of_equiv _ e.toEquiv

theorem isCompositionFactor_commute {X : Type} [Group X] (hX : ∀ a b : X, a * b = b * a)
    {L : Type} [Group L] (h : E1.IsCompositionFactor X L) : ∀ a b : L, a * b = b * a := by
  obtain ⟨N, M, hN, -, -, -, -, ⟨e⟩⟩ := h
  haveI := hN
  intro a b
  apply e.symm.injective
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm a)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm b)
  rw [map_mul, map_mul, ← hx, ← hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hX x.1 y.1)

theorem isCompositionFactor_mulEquiv_of_isSimpleGroup {Y : Type} [Group Y] [hY : IsSimpleGroup Y]
    {L : Type} [Group L] (h : E1.IsCompositionFactor Y L) : Nonempty (Y ≃* L) := by
  obtain ⟨N, M, hN, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  haveI := hN
  haveI := hs
  rcases hMs.eq_bot_or_top_of_isSimpleGroup hY with hM | hM
  · exfalso
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥M ⧸ N.subgroupOf M)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : Y) ∈ (⊥ : Subgroup Y) := hM ▸ x.2
    have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
    exact hq (by rw [hx1]; exact QuotientGroup.mk_one _)
  · rcases hNs.eq_bot_or_top_of_isSimpleGroup hY with hN' | hN'
    · have hNb : N.subgroupOf M = ⊥ := by
        rw [hN']
        exact Subgroup.bot_subgroupOf M
      have e1 : Y ≃* ↥M :=
        (Subgroup.topEquiv (G := Y)).symm.trans (MulEquiv.subgroupCongr hM.symm)
      have e2 : ↥M ≃* (↥M ⧸ N.subgroupOf M) :=
        (QuotientGroup.quotientBot (G := ↥M)).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hNb.symm)
      exact ⟨(e1.trans e2).trans e⟩
    · exfalso
      obtain ⟨q, hq⟩ := exists_ne (1 : ↥M ⧸ N.subgroupOf M)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : x ∈ N.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf, hN']
        exact Subgroup.mem_top _
      exact hq ((QuotientGroup.eq_one_iff x).mpr hx)

end CFSG.LocalAnalysis.WeakClosure81

end
