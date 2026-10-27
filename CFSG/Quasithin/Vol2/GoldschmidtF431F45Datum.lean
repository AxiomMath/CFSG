module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Setup

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 CFSG.Open
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

namespace F45

open SpOut2

section Stabilizers

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem smul_xv_iff (c : α.Completion Y) (k : c.G0) :
    k • c.xv = c.xv ↔ (k : Y) ∈ c.φ1.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left]

theorem smul_lv_iff (c : α.Completion Y) (k : c.G0) :
    k • c.lv = c.lv ↔ (k : Y) ∈ c.φ2.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]

end Stabilizers

section Datum

variable {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ) (hpm : 3 ≤ pm)

@[expose] noncomputable def phiG0 {X : Type*} [Group X] (Φ : X →* ↥A.K) :
    X →* (A.setting hfin pm hpm).ι.G0 :=
  Φ.codRestrict _ (fun x => by
    have := (A.setting hfin pm hpm).ι.gen
    rw [this]
    exact Subgroup.mem_top _)

theorem mem_range_φ1_iff (k : ↥A.K) : k ∈ (A.setting hfin pm hpm).ι.φ1.range ↔
    (k : MulAut D) ∈ A.N1 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact n.2
  · intro h
    exact ⟨⟨k.1, h⟩, rfl⟩

theorem mem_range_φ2_iff (k : ↥A.K) : k ∈ (A.setting hfin pm hpm).ι.φ2.range ↔
    (k : MulAut D) ∈ A.N2 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact n.2
  · intro h
    exact ⟨⟨k.1, h⟩, rfl⟩

theorem mem_normalizer_map_iff {X H : Type*} [Group X] [Group H] (Φ : X →* H)
    (hΦ : Function.Injective Φ) (R : Subgroup X) (y : X) :
    Φ y ∈ Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H) ↔
      y ∈ Subgroup.normalizer (R : Set X) := by
  constructor
  · intro h
    have h' : Φ y ∈ Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H) ⊓ Φ.range := ⟨h, y, rfl⟩
    rw [normalizer_map_inf_range Φ hΦ R] at h'
    obtain ⟨z, hz, hzy⟩ := h'
    rwa [← hΦ hzy]
  · exact fun h => map_mem_normalizer_map Φ h

theorem xdatum_of_ctx {F : Type} [Field F] [Finite F] [CharP F 2] (Φ : antiSp F →* ↥A.K)
    (ψ : ↥A.K) (k₀ : ℕ) (R : Fin 2 → Subgroup (antiSp F)) (hP : OutProps Φ ψ k₀)
    (hN : ∀ j : Fin 2, (![A.Mb1, A.Mb2] : Fin 2 → Subgroup ↥A.K) j =
      Subgroup.normalizer (((R j).map Φ : Subgroup ↥A.K) : Set ↥A.K))
    (hψ : ∀ j : Fin 2, ψ ∈ Subgroup.normalizer (((R j).map Φ : Subgroup ↥A.K) : Set ↥A.K))
    (hΦr : ∀ k : ↥A.K, k ∈ Φ.range ↔ (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range)
    {V : Type} [MulAction (antiSp F) V] (ΓM : SimpleGraph V) (v₁ v₂ : V)
    (s1 : ∀ y, y • v₁ = v₁ ↔ y ∈ Subgroup.normalizer (R 0 : Set (antiSp F)))
    (s2 : ∀ y, y • v₂ = v₂ ↔ y ∈ Subgroup.normalizer (R 1 : Set (antiSp F)))
    (disj : ∀ y z : antiSp F, y • v₁ ≠ z • v₂)
    (noadj1 : ∀ y z : antiSp F, ¬ ΓM.Adj (y • v₁) (z • v₁))
    (noadj2 : ∀ y z : antiSp F, ¬ ΓM.Adj (y • v₂) (z • v₂)) (adj12 : ΓM.Adj v₁ v₂) :
    XDatum (A.setting hfin pm hpm) (phiG0 A hfin pm hpm Φ) ΓM v₁ v₂ := by
  have hN0 : A.Mb1 = Subgroup.normalizer (((R 0).map Φ : Subgroup ↥A.K) : Set ↥A.K) := hN 0
  have hN1 : A.Mb2 = Subgroup.normalizer (((R 1).map Φ : Subgroup ↥A.K) : Set ↥A.K) := hN 1
  have hψ1 : ψ ∈ A.Mb1 := by rw [hN0]; exact hψ 0
  have hψ2 : ψ ∈ A.Mb2 := by rw [hN1]; exact hψ 1
  have hs1 : ∀ y, phiG0 A hfin pm hpm Φ y • (A.setting hfin pm hpm).ι.xv =
      (A.setting hfin pm hpm).ι.xv ↔ y ∈ Subgroup.normalizer (R 0 : Set (antiSp F)) := by
    intro y
    refine (smul_xv_iff (A.setting hfin pm hpm).ι (phiG0 A hfin pm hpm Φ y)).trans ?_
    refine (mem_range_φ1_iff A hfin pm hpm (Φ y)).trans ?_
    have h1 : ((Φ y : ↥A.K) : MulAut D) ∈ A.N1 ↔ Φ y ∈ A.Mb1 := Subgroup.mem_subgroupOf.symm
    rw [h1, hN0]
    exact mem_normalizer_map_iff Φ hP.inj (R 0) y
  have hs2 : ∀ y, phiG0 A hfin pm hpm Φ y • (A.setting hfin pm hpm).ι.lv =
      (A.setting hfin pm hpm).ι.lv ↔ y ∈ Subgroup.normalizer (R 1 : Set (antiSp F)) := by
    intro y
    refine (smul_lv_iff (A.setting hfin pm hpm).ι (phiG0 A hfin pm hpm Φ y)).trans ?_
    refine (mem_range_φ2_iff A hfin pm hpm (Φ y)).trans ?_
    have h1 : ((Φ y : ↥A.K) : MulAut D) ∈ A.N2 ↔ Φ y ∈ A.Mb2 := Subgroup.mem_subgroupOf.symm
    rw [h1, hN1]
    exact mem_normalizer_map_iff Φ hP.inj (R 1) y
  refine ⟨?_, ?_, ?_, fun y => (hs1 y).trans (s1 y).symm, fun y => (hs2 y).trans (s2 y).symm,
    disj, noadj1, noadj2, adj12⟩
  · intro a b h
    exact hP.inj (congrArg Subtype.val h)
  · ext g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := (hΦr g.1).mpr hg
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact (hΦr _).mp ⟨x, rfl⟩
  · intro g
    obtain ⟨x, s, hxs⟩ := hP.gen g.1
    have hmem : ψ ^ s ∈ (A.setting hfin pm hpm).ι.φ1.range ⊔
        (A.setting hfin pm hpm).ι.φ2.range := by
      rw [(A.setting hfin pm hpm).ι.gen]
      exact Subgroup.mem_top _
    refine ⟨x, ⟨ψ ^ s, hmem⟩, ?_, ?_, ?_⟩
    · exact (smul_xv_iff (A.setting hfin pm hpm).ι ⟨ψ ^ s, hmem⟩).mpr
        ((mem_range_φ1_iff A hfin pm hpm (ψ ^ s)).mpr
          (Subgroup.mem_subgroupOf.mp (A.Mb1.pow_mem hψ1 s)))
    · exact (smul_lv_iff (A.setting hfin pm hpm).ι ⟨ψ ^ s, hmem⟩).mpr
        ((mem_range_φ2_iff A hfin pm hpm (ψ ^ s)).mpr
          (Subgroup.mem_subgroupOf.mp (A.Mb2.pow_mem hψ2 s)))
    · exact Subtype.ext hxs

end Datum

end F45

end CFSG.Quasithin.H13.F431
