module

public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel
public import CFSG.RankThree.GF2n.Stroth80.Sec8EndMain
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_normalizer_centrePre_of_normalizes (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hgM : g ∈ M)
    (hg : g ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G)) :
    g ∈ Subgroup.normalizer (Z0 : Set G) := by
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hz' : z ∈ Z0 := hz
  refine (hZ0.mem_iff (x := g * z * g⁻¹)).mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp
    (hZ0.le hz'), fun ρ hρ => ?_⟩
  have hgi : g⁻¹ ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := Subgroup.inv_mem _ hg
  have hσ : g⁻¹ * ρ * g⁻¹⁻¹ ∈ Rt M (LB M Q B) t := (Subgroup.mem_normalizer_iff.mp hgi ρ).mp hρ
  have hq : ⁅z, g⁻¹ * ρ * g⁻¹⁻¹⁆ ∈ Q := hZ0.comm_mem hz' hσ
  have e : ⁅g * z * g⁻¹, ρ⁆ = g * ⁅z, g⁻¹ * ρ * g⁻¹⁻¹⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hQn g hgM _ hq

theorem sec8StrongClosure_of (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hzt : Sec8ZtStatement) (h310chi : Stroth310ChiStatement) (h53 : Stroth53Statement)
    (h56 : Stroth56SpStatement) (hD : Sec8V1InterDimStatement)
    (hS : Sec8LemmaHStatement) : Sec8StrongClosureStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hs0 g hgM hxLN
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  by_cases hsQ : s ∈ Q
  · exact hQZ0 (hQn g hgM s hsQ)
  obtain ⟨hxL, hxN⟩ := hxLN
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨m, hm2, hmSp⟩ := hs.sp
  set V := Vt M (LB M Q B) B Z t with hVdef
  set V₁ := Sec8V1 M Q Z B t r with hV₁def
  set W₁ := Sec8W1 M Q Z B t r with hW₁def
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨hRs, hVs⟩ := hzt G M Q Z B hc n t hs Z0 hZ0 s hs0 hsQ
  have hsmem : s ∈ conjSubgroup g⁻¹ (LB M Q B) := by
    rw [mem_conjSubgroup, inv_inv]
    exact hxL
  have hBV : conjSubgroup g⁻¹ B ⊔ Z ≤ V := by
    refine sup_le ?_ sec39_Z_le_Vt
    have := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) hgi hsmem
    rwa [hVs] at this
  obtain ⟨r', hr'R, hr'eq⟩ := h56 G M Q Z B hc n t hs g⁻¹ hgi hBV
  have hr'M : r' ∈ M := hRM hr'R
  have hg₁M : g * r' ∈ M := M.mul_mem hgM hr'M
  have hg₁BZ : conjSubgroup (g * r') (B ⊔ Z : Subgroup G) = B ⊔ Z := by
    have h1 : conjSubgroup r' (B ⊔ Z : Subgroup G) = conjSubgroup g⁻¹ (B ⊔ Z : Subgroup G) := by
      rw [conjSubgroup_sup', conjSubgroup_sup', hc.conj_Z_eq hr'M, hc.conj_Z_eq hgi, hr'eq]
    rw [conjSubgroup_mul, h1, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hg₁L : g * r' ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (hc.mem_normalizer_LB_iff' hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hg₁M).mpr
      (conjSubgroup_eq_self_iff.mp hg₁BZ)
  have hr'V : conjSubgroup r' V = V := conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr'R)
  have hV₁Q : V₁ ≤ Q := fun v hv =>
    (sup_le inf_le_left (hc.Vt_le_Q t) : (Q ⊓ QB B) ⊔ V ≤ Q) hv.1
  have h53b := h53.2.1 G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) V W₁ V₁ rfl rfl rfl rfl rfl
  have h53d := h53.2.2.2.1 G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Rt M (LB M Q B) t) V W₁ V₁ rfl rfl rfl rfl rfl rfl
  have hxV₁ : ∀ v ∈ V₁, ⁅g * s * g⁻¹, v⁆ ∈ Z := fun v hv => h53d.1 _ hxN v hv
  have hxW₁ : ∀ w ∈ W₁, ⁅g * s * g⁻¹, w⁆ ∈ V₁ := fun w hw => h53b.2 _ hxN w hw
  have hxH : g * s * g⁻¹ ∈ H0 M Z := hc.LB_le_H0 hxL
  have hUW : Ut Q Z (g * s * g⁻¹) ≤ Wt Q V₁ := Ut_le_Wt_of_fixes hc hV₁Q hxH hxV₁
  have hUs : Ut Q Z s = V := sec8_ZV_of_parts h51 hA hzt h310chi hc hs hZ0 hs0 hsQ
  have hVgW : ∀ v ∈ V, g * v * g⁻¹ ∈ W₁ := by
    intro v hv
    have h1 : g * v * g⁻¹ ∈ conjSubgroup g (Ut Q Z s) := by
      rw [hUs]
      refine mem_conjSubgroup.mpr ?_
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rw [e]
      exact hv
    rw [← Ut_conj_of_normalizes (hc.conj_Q_eq hgM) (hc.conj_Z_eq hgM) s] at h1
    exact hUW h1
  have hdim := hD G M Q Z B hc n t hs r hr m hmSp Z0 hZ0 s hs0 hsQ g hgM hxW₁
  have hii : ∀ v ∈ V, (g * r') * v * (g * r')⁻¹ ∈ W₁ := by
    intro v hv
    have h1 : r' * v * r'⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hr'V) v).mp hv
    have e : (g * r') * v * (g * r')⁻¹ = g * (r' * v * r'⁻¹) * g⁻¹ := by group
    rw [e]
    exact hVgW _ h1
  have hiii : conjSubgroup (g * r') V = conjSubgroup g V := by
    rw [conjSubgroup_mul, hr'V]
  have hdim' : Nat.card Z ^ (m + 1) ≤ Nat.card ↥(V₁ ⊓ conjSubgroup (g * r') V) := by
    rw [hiii]
    exact hdim
  have hgR : g * r' ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    hS G M Q Z B hc n t hs r hr m hmSp (g * r') hg₁M hg₁L hii hdim'
  have hgZ0 : g * r' ∈ Subgroup.normalizer (Z0 : Set G) :=
    mem_normalizer_centrePre_of_normalizes hc hZ0 hg₁M hgR
  have hx1 : (g * r') * s * (g * r')⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hgZ0 s).mp hs0
  have hcomm : ⁅r', s⁆ ∈ Q := by
    have := hZ0.comm_mem hs0 hr'R
    rw [← commutatorElement_inv]
    exact Q.inv_mem this
  have e : g * s * g⁻¹ = (g * ⁅r', s⁆ * g⁻¹)⁻¹ * ((g * r') * s * (g * r')⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Z0.mul_mem (Z0.inv_mem (hQZ0 (hQn g hgM _ hcomm))) hx1

theorem step84CaseTwo_of_strong (h : Sec8StrongClosureStatement) : Step84CaseTwoStatement :=
  fun G _ _ M Q Z B hc n t hs Z0 hZ0 _ => h G M Q Z B hc n t hs Z0 hZ0

end CFSG.RankThree.GF2n.Stroth80
