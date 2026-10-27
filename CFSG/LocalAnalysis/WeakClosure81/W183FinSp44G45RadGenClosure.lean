module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45Rad
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisAutClass
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (minorAut uElt antiSp antiUnipotent uElt_mem_antiUnipotent antiSp_ext glMat_uElt)
open CFSG.QuasithinUnique.Fin257.Sp4
  (wS wT wS_mem_normalizer_radA1 wT_mem_normalizer_radA2 wS_not_mem_normalizer_U
   wS_not_mem_normalizer_radA2 wT_not_mem_normalizer_radA1 normalizer_U_le_normalizer_radA1
   normalizer_U_le_normalizer_radA2 glMat_wS_conj glMat_wT_conj glMat_mul glMat_wS glMat_wT)

theorem w183finSp44rg_radA1_map_minorAut :
    (radA1 GF4).map (minorAut GF4).toMonoidHom = radA2 GF4 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (CFSG.RankThree.PartOne.KCRootAxis.minorAut_mem_radA2_iff (K := GF4) x).mpr hx
  · intro hy
    refine ⟨(minorAut GF4)⁻¹ y, ?_, ?_⟩
    · exact (CFSG.RankThree.PartOne.KCRootAxis.minorAut_mem_radA2_iff
        (K := GF4) ((minorAut GF4)⁻¹ y)).mp (by simpa using hy)
    · simp

theorem w183finSp44rg_autConj_mul (A : Subgroup (MulAut S4)) (h k : MulAut S4) :
    autConj (h * k) A = autConj h (autConj k A) := by
  rw [autConj, autConj, autConj]
  have hcomp : (MulAut.conj (h * k)).toMonoidHom =
      (MulAut.conj h).toMonoidHom.comp (MulAut.conj k).toMonoidHom := by
    rw [map_mul]
    apply MonoidHom.ext
    intro α
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  rw [hcomp, ← Subgroup.map_map]

theorem w183finSp44rg_conj_conj (τ : MulAut S4) :
    (MulAut.conj τ).toMonoidHom.comp (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp τ.toMonoidHom := by
  ext x
  simp [MulAut.conj_apply]

theorem w183finSp44rg_autConj_minorAut_Q1 :
    autConj (minorAut GF4) Q1sub = Q2sub := by
  rw [autConj, Q1sub, Q2sub, Subgroup.map_map]
  have hcomp : (MulAut.conj (minorAut GF4)).toMonoidHom.comp (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp (minorAut GF4).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  rw [hcomp, ← Subgroup.map_map, w183finSp44rg_radA1_map_minorAut]

theorem w183finSp44rg_mem_autStab_of_map {G : Type*} [Group G] {H : Subgroup G} {α : MulAut G}
    (h : H.map α.toMonoidHom = H) :
    α ∈ CFSG.RankThree.PartOne.KCRootAxis.autStab H := by
  rw [CFSG.RankThree.PartOne.KCRootAxis.mem_autStab]
  intro x
  conv_lhs => rw [← h]
  exact Subgroup.mem_map_iff_mem (f := α.toMonoidHom) (K := H) α.injective

theorem w183finSp44rg_autConj_Q1_of_map (τ : MulAut S4)
    (h : (radA1 GF4).map τ.toMonoidHom = radA2 GF4) :
    autConj τ Q1sub = Q2sub := by
  rw [autConj, Q1sub, Q2sub, Subgroup.map_map, w183finSp44rg_conj_conj τ,
    ← Subgroup.map_map, h]

theorem w183finSp44rg_autConj_Q2_of_map (τ : MulAut S4)
    (h : (radA2 GF4).map τ.toMonoidHom = radA1 GF4) :
    autConj τ Q2sub = Q1sub := by
  rw [autConj, Q2sub, Q1sub, Subgroup.map_map, w183finSp44rg_conj_conj τ,
    ← Subgroup.map_map, h]

theorem w183finSp44rg_autConj_minorAut_Q2 :
    autConj (minorAut GF4) Q2sub = Q1sub := by
  rw [autConj, Q2sub, Q1sub, Subgroup.map_map]
  have hcomp : (MulAut.conj (minorAut GF4)).toMonoidHom.comp (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp (minorAut GF4).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  rw [hcomp, ← Subgroup.map_map, ← CFSG.RankThree.PartOne.KCRootAxis.radA1_eq_map]

theorem w183finSp44rg_autConj_normalizer (H : Subgroup (MulAut S4)) (p : MulAut S4)
    (hp : p ∈ Subgroup.normalizer (H : Set (MulAut S4))) : autConj p H = H := by
  rw [autConj, MulEquiv.toMonoidHom_eq_coe]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp hp

theorem w183finSp44rg_map_iSup_autConj (P E : Subgroup (MulAut S4)) {q : MulAut S4}
    (hq : q ∈ P) : (⨆ p ∈ P, autConj (q * p) E) = ⨆ p ∈ P, autConj p E := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun p => iSup_le fun hp => ?_
    exact le_iSup_of_le (q * p) (le_iSup_of_le (mul_mem hq hp) le_rfl)
  · refine iSup_le fun p => iSup_le fun hp => ?_
    have hp' : q⁻¹ * p ∈ P := mul_mem (inv_mem hq) hp
    calc autConj p E = autConj (q * (q⁻¹ * p)) E := by rw [mul_inv_cancel_left]
      _ ≤ ⨆ p ∈ P, autConj (q * p) E :=
          le_iSup_of_le (q⁻¹ * p) (le_iSup_of_le hp' le_rfl)

theorem w183finSp44rg_autConj_iSup_self (P E : Subgroup (MulAut S4)) {q : MulAut S4}
    (hq : q ∈ P) : autConj q (⨆ p ∈ P, autConj p E) = ⨆ p ∈ P, autConj p E := by
  have h1 : autConj q (⨆ p ∈ P, autConj p E) =
      ⨆ p ∈ P, autConj (q * p) E := by
    rw [autConj, Subgroup.map_iSup]
    apply iSup_congr
    intro p
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro hp
    exact (w183finSp44rg_autConj_mul E q p).symm
  rw [h1]
  exact w183finSp44rg_map_iSup_autConj P E hq

private theorem w183finSp44rg_autConj_conj_map (A : Subgroup S4) {u : S4}
    (hu : u ∈ Subgroup.normalizer (A : Set S4)) :
    autConj (MulAut.conj u) (A.map (MulAut.conj : S4 →* MulAut S4)) =
      A.map (MulAut.conj : S4 →* MulAut S4) := by
  change (A.map (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj (MulAut.conj u)) =
    A.map (MulAut.conj : S4 →* MulAut S4)
  rw [Subgroup.map_map]
  have hcomp : (↑(MulAut.conj (MulAut.conj u)) : MulAut S4 →* MulAut S4).comp
        (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp (↑(MulAut.conj u) : S4 →* S4) := by
    ext x
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map, Subgroup.mem_normalizer_iff_map_conj_eq.mp hu]

private theorem w183finSp44rg_conj_le {P E : Subgroup (MulAut S4)} {q : MulAut S4}
    (hq : q ∈ P) :
    autConj q (⨆ p ∈ P, autConj p E) ≤ ⨆ p ∈ P, autConj p E :=
  le_of_eq (w183finSp44rg_autConj_iSup_self P E hq)

private theorem w183finSp44rg_isSimple_S4 : IsSimpleGroup S4 := by
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 GF4)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp GF4 2 (by norm_num)
      (Or.inl (Or.inr (by rw [Nat.card_eq_fintype_card]; decide)))
  exact (antiProjEquiv GF4).isSimpleGroup

private theorem w183finSp44rg_wS_factor :
    (wS : S4) = uElt 1 0 0 0 * (wS * uElt 1 0 0 0 * (wS : S4)⁻¹) * uElt 1 0 0 0 := by
  apply antiSp_ext
  rw [glMat_mul, glMat_mul, glMat_wS_conj, glMat_uElt, glMat_wS]
  decide +kernel

private theorem w183finSp44rg_wT_factor :
    (wT : S4) = uElt 0 0 0 1 * (wT * uElt 0 0 0 1 * (wT : S4)⁻¹) * uElt 0 0 0 1 := by
  apply antiSp_ext
  rw [glMat_mul, glMat_mul, glMat_wT_conj, glMat_uElt, glMat_wT]
  decide +kernel

theorem w183finSp44rg_rad_c12 :
    (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
        autConj p (Psub ⊓ innAutOf S4)) ⊔
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
        autConj p (Psub ⊓ innAutOf S4)) = innAutOf S4 := by
  have hNorm : (innAutOf S4).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S4
  have hSU : Psub ⊓ innAutOf S4 = Usub := Psub_inf_inner
  have hB : CFSG.QuasithinUnique.Borel252.BorelData S4 (antiUnipotent GF4) (radA1 GF4)
      (radA2 GF4) :=
    CFSG.QuasithinUnique.Borel252.Sp4.borelData_Sp (K := GF4) (n := 2) (by norm_num)
      (by rw [Nat.card_eq_fintype_card]; decide)
  set S : Subgroup (MulAut S4) := Psub ⊓ innAutOf S4 with hS
  set P1 : Subgroup (MulAut S4) :=
    innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)) with hP1
  set P2 : Subgroup (MulAut S4) :=
    innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)) with hP2
  set N1 : Subgroup (MulAut S4) := ⨆ p ∈ P1, autConj p S with hN1
  set N2 : Subgroup (MulAut S4) := ⨆ p ∈ P2, autConj p S with hN2
  set K : Subgroup (MulAut S4) := N1 ⊔ N2 with hK
  have hconjInn : ∀ (p : MulAut S4) (A : Subgroup (MulAut S4)), A ≤ innAutOf S4 →
      autConj p A ≤ innAutOf S4 := by
    intro p A hA
    rintro _ ⟨β, hβ, rfl⟩
    exact hNorm.conj_mem β (hA hβ) p
  have hKle : K ≤ innAutOf S4 :=
    sup_le (iSup₂_le fun p _ => hconjInn p S inf_le_right)
      (iSup₂_le fun p _ => hconjInn p S inf_le_right)
  have hg1 : ∀ g ∈ Subgroup.normalizer (radA1 GF4 : Set S4), MulAut.conj g ∈ P1 := fun g hg =>
    Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (w183finSp44rg_autConj_conj_map (radA1 GF4) hg)⟩
  have hg2 : ∀ g ∈ Subgroup.normalizer (radA2 GF4 : Set S4), MulAut.conj g ∈ P2 := fun g hg =>
    Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (w183finSp44rg_autConj_conj_map (radA2 GF4) hg)⟩
  have hK_conj : ∀ q ∈ P1, q ∈ P2 → autConj q K ≤ K := by
    intro q hq1 hq2
    rw [hK, autConj, Subgroup.map_sup]
    exact sup_le_sup (w183finSp44rg_conj_le (P := P1) (E := S) hq1)
      (w183finSp44rg_conj_le (P := P2) (E := S) hq2)
  have hK_norm : ∀ q ∈ P1, q ∈ P2 → q ∈ Subgroup.normalizer (K : Set (MulAut S4)) := by
    intro q hq1 hq2
    have key : ∀ q ∈ P1, q ∈ P2 → ∀ α ∈ K, q * α * q⁻¹ ∈ K := by
      intro q hq1 hq2 α hα
      have h : MulAut.conj q α ∈ autConj q K := Subgroup.mem_map.mpr ⟨α, hα, rfl⟩
      exact hK_conj q hq1 hq2 (by simpa using h)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key q hq1 hq2 h hh, fun hh => ?_⟩
    have h1 := key q⁻¹ (P1.inv_mem hq1) (P2.inv_mem hq2) _ hh
    have e : q⁻¹ * (q * h * q⁻¹) * q⁻¹⁻¹ = h := by group
    rwa [e] at h1
  have hN1_of : ∀ q ∈ P1, ∀ y ∈ S, q * y * q⁻¹ ∈ N1 := by
    intro q hq y hy
    have h : MulAut.conj q y ∈ autConj q S := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (le_iSup₂_of_le q hq le_rfl : autConj q S ≤ N1) (by simpa using h)
  have hN2_of : ∀ q ∈ P2, ∀ y ∈ S, q * y * q⁻¹ ∈ N2 := by
    intro q hq y hy
    have h : MulAut.conj q y ∈ autConj q S := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (le_iSup₂_of_le q hq le_rfl : autConj q S ≤ N2) (by simpa using h)
  have hxS : MulAut.conj (uElt (1 : GF4) 0 0 0) ∈ S := by
    rw [hSU]
    exact Subgroup.mem_map.mpr ⟨_, uElt_mem_antiUnipotent _ _ _ _, rfl⟩
  have hyS : MulAut.conj (uElt (0 : GF4) 0 0 1) ∈ S := by
    rw [hSU]
    exact Subgroup.mem_map.mpr ⟨_, uElt_mem_antiUnipotent _ _ _ _, rfl⟩
  have hwS_N1 : MulAut.conj (wS : S4) ∈ N1 := by
    have hx1 : MulAut.conj (uElt (1 : GF4) 0 0 0) ∈ N1 := by
      simpa using hN1_of 1 P1.one_mem _ hxS
    have hx2 : MulAut.conj (wS * uElt (1 : GF4) 0 0 0 * (wS : S4)⁻¹) ∈ N1 := by
      have h := hN1_of _ (hg1 wS wS_mem_normalizer_radA1) _ hxS
      simpa [map_mul, map_inv] using h
    have h := N1.mul_mem (N1.mul_mem hx1 hx2) hx1
    rw [← map_mul, ← map_mul, ← w183finSp44rg_wS_factor] at h
    exact h
  have hwT_N2 : MulAut.conj (wT : S4) ∈ N2 := by
    have hy1 : MulAut.conj (uElt (0 : GF4) 0 0 1) ∈ N2 := by
      simpa using hN2_of 1 P2.one_mem _ hyS
    have hy2 : MulAut.conj (wT * uElt (0 : GF4) 0 0 1 * (wT : S4)⁻¹) ∈ N2 := by
      have h := hN2_of _ (hg2 wT wT_mem_normalizer_radA2) _ hyS
      simpa [map_mul, map_inv] using h
    have h := N2.mul_mem (N2.mul_mem hy1 hy2) hy1
    rw [← map_mul, ← map_mul, ← w183finSp44rg_wT_factor] at h
    exact h
  set X : Subgroup S4 :=
    (Subgroup.normalizer (K : Set (MulAut S4))).comap (MulAut.conj : S4 →* MulAut S4) with hX
  have hNU_le : Subgroup.normalizer (antiUnipotent GF4 : Set S4) ≤ X := by
    intro g hg
    exact Subgroup.mem_comap.mpr (hK_norm _ (hg1 g (normalizer_U_le_normalizer_radA1 hg))
      (hg2 g (normalizer_U_le_normalizer_radA2 hg)))
  have hwS_X : (wS : S4) ∈ X :=
    Subgroup.mem_comap.mpr (Subgroup.le_normalizer (Subgroup.mem_sup_left hwS_N1))
  have hwT_X : (wT : S4) ∈ X :=
    Subgroup.mem_comap.mpr (Subgroup.le_normalizer (Subgroup.mem_sup_right hwT_N2))
  have hXtop : X = ⊤ := by
    by_contra hne
    have hlt : X < ⊤ := lt_top_iff_ne_top.mpr hne
    have h1 : Subgroup.normalizer (antiUnipotent GF4 : Set S4) < X :=
      lt_of_le_of_ne hNU_le fun h => wS_not_mem_normalizer_U (h ▸ hwS_X)
    rcases hB.only X h1 hlt with h | h
    · exact wT_not_mem_normalizer_radA1 (h ▸ hwT_X)
    · exact wS_not_mem_normalizer_radA2 (h ▸ hwS_X)
  have hKnorm : (K.comap (MulAut.conj : S4 →* MulAut S4)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgX : g ∈ X := by
      rw [hXtop]
      exact Subgroup.mem_top g
    have hg : MulAut.conj g ∈ Subgroup.normalizer (K : Set (MulAut S4)) :=
      Subgroup.mem_comap.mp hgX
    have h := (Subgroup.mem_normalizer_iff.mp hg (MulAut.conj n)).mp (Subgroup.mem_comap.mp hn)
    rw [Subgroup.mem_comap]
    simpa [map_mul, map_inv] using h
  haveI := w183finSp44rg_isSimple_S4
  have hne : K.comap (MulAut.conj : S4 →* MulAut S4) ≠ ⊥ := by
    intro hbot
    have hx : MulAut.conj (uElt (1 : GF4) 0 0 0) ∈ K :=
      Subgroup.mem_sup_left (by simpa using hN1_of 1 P1.one_mem _ hxS)
    have hmem : uElt (1 : GF4) 0 0 0 ∈ K.comap (MulAut.conj : S4 →* MulAut S4) :=
      Subgroup.mem_comap.mpr hx
    rw [hbot, Subgroup.mem_bot] at hmem
    have h := (uElt_inj (hmem.trans uElt_zero_eq_one.symm)).1
    exact one_ne_zero h
  have htop : K.comap (MulAut.conj : S4 →* MulAut S4) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  refine le_antisymm hKle ?_
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ K.comap (MulAut.conj : S4 →* MulAut S4) := htop ▸ Subgroup.mem_top y
  exact Subgroup.mem_comap.mp hy

theorem w183finSp44rg_autConj_inner_Q1 {g : S4}
    (hg : (radA1 GF4).map (MulAut.conj g).toMonoidHom = radA1 GF4) :
    autConj (MulAut.conj g) Q1sub = Q1sub := by
  rw [autConj, Q1sub, Subgroup.map_map, w183finSp44rg_conj_conj (MulAut.conj g),
    ← Subgroup.map_map, hg]

theorem w183finSp44rg_autConj_inner_Q2 {g : S4}
    (hg : (radA2 GF4).map (MulAut.conj g).toMonoidHom = radA2 GF4) :
    autConj (MulAut.conj g) Q2sub = Q2sub := by
  rw [autConj, Q2sub, Subgroup.map_map, w183finSp44rg_conj_conj (MulAut.conj g),
    ← Subgroup.map_map, hg]

theorem w183finSp44rg_invariant_Q1 {H : Subgroup (MulAut S4)} (hH : H ≤ Q1sub)
    (hinv : ∀ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
      autConj p H = H) (h8 : 8 ≤ Nat.card H) : H = Q1sub := by
  have h4 : 4 ≤ Nat.card GF4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hstruct := rootAxisStructure_one (K := GF4) h4
  let c := (MulAut.conj : S4 →* MulAut S4)
  have hcinj : Function.Injective c := conj_injective (K := GF4)
  let H₀ : Subgroup S4 := H.comap c
  have hHrange : H ≤ c.range :=
    hH.trans (Subgroup.map_le_range (f := c) (radA1 GF4))
  have hHmap : H₀.map c = H := Subgroup.map_comap_eq_self hHrange
  have hH₀le : H₀ ≤ radA1 GF4 := by
    have h1 : H.comap c ≤ ((radA1 GF4).map c).comap c := Subgroup.comap_mono hH
    rw [Subgroup.comap_map_eq_self_of_injective hcinj] at h1
    exact h1
  have hcard₀ : 8 ≤ Nat.card H₀ := by
    rw [← Subgroup.card_map_of_injective (f := c) hcinj, hHmap]
    exact h8
  have hrootU : Nat.card (rootU GF4 Axis.one) = 4 := by
    have e : GF4 ≃ rootU GF4 Axis.one := Equiv.ofBijective
      (fun b => ⟨uElt 0 b 0 0, ⟨b, rfl⟩⟩)
      ⟨fun a b h => (uElt_inj (congrArg Subtype.val h)).2.1,
       fun ⟨g, b, hb⟩ => ⟨b, Subtype.ext hb.symm⟩⟩
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    decide
  have hnotU : ¬ H₀ ≤ rootU GF4 Axis.one := by
    intro hle
    have hcardle : Nat.card H₀ ≤ Nat.card (rootU GF4 Axis.one) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [hrootU] at hcardle
    omega
  have hrootC : H₀ ≤ rootC GF4 Axis.one := hH₀le.trans hstruct.A_le_C
  have hnormal : ∀ g ∈ rootC GF4 Axis.one, ∀ v ∈ H₀, g * v * g⁻¹ ∈ H₀ := by
    intro g hg v hv
    have hgN : g ∈ Subgroup.normalizer (rootU₁ GF4 : Set (antiSp GF4)) :=
      (Subgroup.centralizer_le_normalizer (rootU GF4 Axis.one : Set (antiSp GF4))) hg
    have hgA : g ∈ Subgroup.normalizer (radA1 GF4 : Set S4) := by
      rw [← hstruct.N_eq]
      exact hgN
    have hmapA : (radA1 GF4).map (MulAut.conj g).toMonoidHom = radA1 GF4 :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgA
    have hQ : (MulAut.conj g) ∈ Subgroup.normalizer (Q1sub : Set (MulAut S4)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, ← autConj]
      exact w183finSp44rg_autConj_inner_Q1 hmapA
    have hinner : (MulAut.conj g) ∈
        (innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4))) := ⟨⟨g, rfl⟩, hQ⟩
    have hfix := hinv (MulAut.conj g) hinner
    have hmap0 : H₀.map (MulAut.conj g).toMonoidHom = H₀ := by
      have h := hfix
      rw [← hHmap, autConj, Subgroup.map_map, w183finSp44rg_conj_conj (MulAut.conj g),
        ← Subgroup.map_map] at h
      exact Subgroup.map_injective hcinj h
    have hv' : (MulAut.conj g) v ∈ H₀ := by
      have hmem : (MulAut.conj g) v ∈ H₀.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hv
      rwa [hmap0] at hmem
    simpa [MulAut.conj_apply] using hv'
  have hH₀eq : H₀ = radA1 GF4 := hstruct.normal_eq_A H₀ hrootC hnormal hH₀le hnotU
  rw [← hHmap, hH₀eq, Q1sub]

theorem w183finSp44rg_invariant_Q2 {H : Subgroup (MulAut S4)} (hH : H ≤ Q2sub)
    (hinv : ∀ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
      autConj p H = H) (h8 : 8 ≤ Nat.card H) : H = Q2sub := by
  have h4 : 4 ≤ Nat.card GF4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hstruct := rootAxisStructure_two (K := GF4) h4
  let c := (MulAut.conj : S4 →* MulAut S4)
  have hcinj : Function.Injective c := conj_injective (K := GF4)
  let H₀ : Subgroup S4 := H.comap c
  have hHrange : H ≤ c.range :=
    hH.trans (Subgroup.map_le_range (f := c) (radA2 GF4))
  have hHmap : H₀.map c = H := Subgroup.map_comap_eq_self hHrange
  have hH₀le : H₀ ≤ radA2 GF4 := by
    have h1 : H.comap c ≤ ((radA2 GF4).map c).comap c := Subgroup.comap_mono hH
    rw [Subgroup.comap_map_eq_self_of_injective hcinj] at h1
    exact h1
  have hcard₀ : 8 ≤ Nat.card H₀ := by
    rw [← Subgroup.card_map_of_injective (f := c) hcinj, hHmap]
    exact h8
  have hrootU : Nat.card (rootU GF4 Axis.two) = 4 := by
    have e : GF4 ≃ rootU GF4 Axis.two := Equiv.ofBijective
      (fun b => ⟨uElt 0 0 b 0, ⟨b, rfl⟩⟩)
      ⟨fun a b h => (uElt_inj (congrArg Subtype.val h)).2.2.1,
       fun ⟨g, b, hb⟩ => ⟨b, Subtype.ext hb.symm⟩⟩
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    decide
  have hnotU : ¬ H₀ ≤ rootU GF4 Axis.two := by
    intro hle
    have hcardle : Nat.card H₀ ≤ Nat.card (rootU GF4 Axis.two) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [hrootU] at hcardle
    omega
  have hrootC : H₀ ≤ rootC GF4 Axis.two := hH₀le.trans hstruct.A_le_C
  have hnormal : ∀ g ∈ rootC GF4 Axis.two, ∀ v ∈ H₀, g * v * g⁻¹ ∈ H₀ := by
    intro g hg v hv
    have hgN : g ∈ Subgroup.normalizer (rootU₂ GF4 : Set (antiSp GF4)) :=
      (Subgroup.centralizer_le_normalizer (rootU GF4 Axis.two : Set (antiSp GF4))) hg
    have hgA : g ∈ Subgroup.normalizer (radA2 GF4 : Set S4) := by
      rw [← hstruct.N_eq]
      exact hgN
    have hmapA : (radA2 GF4).map (MulAut.conj g).toMonoidHom = radA2 GF4 :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgA
    have hQ : (MulAut.conj g) ∈ Subgroup.normalizer (Q2sub : Set (MulAut S4)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, ← autConj]
      exact w183finSp44rg_autConj_inner_Q2 hmapA
    have hinner : (MulAut.conj g) ∈
        (innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4))) := ⟨⟨g, rfl⟩, hQ⟩
    have hfix := hinv (MulAut.conj g) hinner
    have hmap0 : H₀.map (MulAut.conj g).toMonoidHom = H₀ := by
      have h := hfix
      rw [← hHmap, autConj, Subgroup.map_map, w183finSp44rg_conj_conj (MulAut.conj g),
        ← Subgroup.map_map] at h
      exact Subgroup.map_injective hcinj h
    have hv' : (MulAut.conj g) v ∈ H₀ := by
      have hmem : (MulAut.conj g) v ∈ H₀.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hv
      rwa [hmap0] at hmem
    simpa [MulAut.conj_apply] using hv'
  have hH₀eq : H₀ = radA2 GF4 := hstruct.normal_eq_A H₀ hrootC hnormal hH₀le hnotU
  rw [← hHmap, hH₀eq, Q2sub]

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
