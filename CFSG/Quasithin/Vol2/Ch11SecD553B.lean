module

public import CFSG.Quasithin.Vol2.Ch11SecD553A
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Background.A1bReduced

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_centralizer_of_le_abelian {A B V : Subgroup G} (hV : IsMulCommutative ↥V)
    (hA : A ≤ V) (hB : B ≤ V) : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hV.is_comm.comm (⟨b, hB hb⟩ : ↥V) ⟨a, hA ha⟩)

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem le_cClos_of_abelian (hRank : RankV2Fact) (hComm : PointCommFact) (h : Hyp11 G T L I n)
    (hset : NatSetting11 G T L I n)
    (hkind : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hone : ∀ g : G, g ∉ Subgroup.normalizer (fsuV T I : Set G) →
      ∃ y ∈ L, fsuV T I ⊓ conjSubgroup (fsuV T I) g ≤ conjSubgroup V₁ y)
    {m : ℕ} (hm : n + 1 < m) (hr : ((m : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I))
    (habel : IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    V₂ ≤ E3.cClos (fsuV T I) 1 T := by
  set V := fsuV T I with hVdef
  have hVel := SecA.isElemAbelian_fsuV h
  have hV₂V := SecA.IsVi.le_fsuV hV₂
  have hVT := SecA.fsuV_le_T h
  refine le_inf (hV₂V.trans hVT) ?_
  rw [Subgroup.le_centralizer_iff]
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAT, g, hAg, hmA⟩ := hA
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  by_contra hne
  have hVab : IsMulCommutative ↥V := hVel.1
  have hgV : g ∉ Subgroup.normalizer (V : Set G) := by
    intro hg
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hg] at hAg
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_le_abelian hVab hV₂V hAg))
  have hAel : IsElemAbelian 2 A :=
    A1b.isElemAbelian_of_le hAg (E3.isElemAbelian_conjSubgroup hVel g)
  have hrank := hRank G T L I n V₂ hset hkind hV₂ A hAT hAel
  have hBA : A ⊓ Subgroup.centralizer (V₂ : Set G) ≤ A := inf_le_left
  have hmB : E3.mQuot (conjSubgroup V g) (A ⊓ Subgroup.centralizer (V₂ : Set G)) < m := by
    rw [E3.mQuot_add hBA hAg, hmA]
    omega
  have hV₂N : V₂ ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    have hCB : Subgroup.centralizer ((A ⊓ Subgroup.centralizer (V₂ : Set G) : Subgroup G) :
        Set G) ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
      by_contra hnc
      have h1 := E3.rParam_le_mQuot (hBA.trans hAg) hnc
      rw [E3.rParam_conj] at h1
      have h2 : ((m : ℕ) : ℕ∞) ≤ E3.mQuot (conjSubgroup V g)
          (A ⊓ Subgroup.centralizer (V₂ : Set G)) := hr.trans h1
      exact absurd (by exact_mod_cast h2) (not_le.mpr hmB)
    refine le_trans ?_ hCB
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right
  have hcomm : ⁅V₂, A⁆ ≤ V ⊓ conjSubgroup V g := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 : a * v⁻¹ * a⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (SecA.T_le_normalizer_fsuV T I (hAT ha)) _).mp
          (V.inv_mem (hV₂V hv))
      have := V.mul_mem (hV₂V hv) h1
      simpa [mul_assoc] using this
    · have h1 : v * a * v⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.mp (hV₂N hv) a).mp (hAg ha)
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hAg ha))
  obtain ⟨y, hy, hVy⟩ := hone g hgV
  have hV₁A : V₁ ≤ ⁅V₂, A⁆ := by
    by_contra hnot
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv a ha
    have hza : ⁅V₂, Subgroup.zpowers a⁆ ≤ ⁅V₂, A⁆ :=
      Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr ha)
    rcases hComm G T L I n V₁ V₂ hset hkind hV₁ hV₂ a (hAT ha) y hy
        (hza.trans (hcomm.trans hVy)) with h0 | h1
    · have := Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers a)
      rw [h0] at this
      exact this
    · exact absurd (h1 ▸ hza) hnot
  obtain ⟨y', hy', hVy'⟩ := hone g⁻¹ fun hg' => hgV (by simpa using Subgroup.inv_mem _ hg')
  have hVg : V ⊓ conjSubgroup V g ≤ conjSubgroup V₁ (y' * g) := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈ V ⊓ conjSubgroup V g⁻¹ :=
      ⟨mem_conjSubgroup_iff.mp hx.2, mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hx.1)⟩
    have := mem_conjSubgroup_iff.mp (hVy' hgx)
    rw [mem_conjSubgroup_iff]
    convert this using 1
    group
  have hV₁eq : V₁ = conjSubgroup V₁ (y' * g) :=
    Subgroup.eq_of_le_of_card_ge (hV₁A.trans (hcomm.trans hVg)) (card_conjSubgroup V₁ _).le
  have hyg : y' * g ∈ Subgroup.normalizer (V₁ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hV₁eq.symm
  have hVgle : conjSubgroup V g ≤ conjClosure V (Subgroup.normalizer (V₁ : Set G)) := by
    have heq : conjSubgroup V g = conjSubgroup V (y' * g) := by
      rw [← conjSubgroup_conjSubgroup,
        conjSubgroup_eq_iff_mem_normalizer.mpr (SecA.L_le_normalizer_fsuV h hy')]
    rw [heq]
    intro w hw
    have := mem_conjClosure (Subgroup.inv_mem _ hyg) (mem_conjSubgroup_iff.mp hw)
    simpa [mul_assoc] using this
  exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_le_abelian
    habel (hV₂V.trans (le_conjClosure V _)) (hAg.trans hVgle)))

end CFSG.Quasithin.Vol2.Ch11.SecD
