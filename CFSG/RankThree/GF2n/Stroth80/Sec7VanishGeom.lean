module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishPair
public import CFSG.RankThree.GF2n.Stroth80.Sec710Point
public import CFSG.RankThree.GF2n.Stroth80.Sec56Singular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem vanishGeom_conj_le_of_le {g : G} {A C : Subgroup G} (h : A ≤ conjSubgroup g C) :
    conjSubgroup g⁻¹ A ≤ C := by
  intro y hy
  have hy' : g * y * g⁻¹ ∈ A := by
    rw [mem_conjSubgroup] at hy
    simpa using hy
  have h1 := h hy'
  rw [mem_conjSubgroup] at h1
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rwa [e] at h1

theorem vanishGeom_comm_mem_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hZV : Sec7ZVStatement) {x g : G} (hg : g ∈ M) (hq : x * (g * t * g⁻¹)⁻¹ ∈ Q)
    {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t) :
    ⁅v, x⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hUt : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hcommZ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    CFSG.RankThree.GF2n.Smith81.comm_mem_Z hc.hyp ha hb
  have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hc.LB_le_M ht)) (M.inv_mem hg)
  have hgvQ : g⁻¹ * v * g ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hg)) v).mp hvQ
  have hyQ : ⁅v, g * t * g⁻¹⁆ ∈ Q := by
    have e : ⁅v, g * t * g⁻¹⁆ = v * ((g * t * g⁻¹) * v⁻¹ * (g * t * g⁻¹)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hvQ ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hx₀M) v⁻¹).mp
      (Q.inv_mem hvQ))
  have hyc : ⁅v, g * t * g⁻¹⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * ⁅v, g * t * g⁻¹⁆ * g = ⁅g⁻¹ * v * g, t⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, ← hUt]
    exact comm_mem_Ut hgvQ
  have hxe : x = (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
  have e1 : ⁅v, x⁆ = ⁅v, x * (g * t * g⁻¹)⁻¹⁆ *
      (⁅v, g * t * g⁻¹⁆ * ⁅⁅v, g * t * g⁻¹⁆⁻¹, x * (g * t * g⁻¹)⁻¹⁆) := by
    generalize x * (g * t * g⁻¹)⁻¹ = q₀ at hxe ⊢
    rw [hxe]
    simp only [commutatorElement_def]
    group
  have hz1 : ⁅v, x * (g * t * g⁻¹)⁻¹⁆ ∈ Z := hcommZ v hvQ _ hq
  have hz2 : ⁅⁅v, g * t * g⁻¹⁆⁻¹, x * (g * t * g⁻¹)⁻¹⁆ ∈ Z :=
    hcommZ _ (Q.inv_mem hyQ) _ hq
  have hZc : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    hc.Z_le_conjSubgroup sec39_Z_le_Vt hg
  rw [e1]
  exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem (hZc hz1)
    ((conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem hyc (hZc hz2))

theorem step71VanishGeom_core (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hno : ¬ Conc71abcd hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hW : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = Q' y → ∃ A ∈ X, (A : Matrix ι ι K) *ᵥ x = y)
    (hOrb : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z)
    {x : G} (hx : ConjMod M Q t x) (hxt : ⁅x, t⁆ ∈ Q)
    (hmov : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) :
    ∃ v ∈ Vt M (LB M Q B) B Z t, ∀ r ∈ Rt M (LB M Q B) t, ⁅x, v⁆ ∉ conjSubgroup r B ⊔ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxM : x ∈ M := hx.1
  obtain ⟨g, hg, hq⟩ := hx.2
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hRM : ∀ y ∈ Rt M (LB M Q B) t, y ∈ M := fun y hy => hc.Rt_le_M t hy
  have hZVle : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hxVn : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)) v).mp hv
  have hsing := hc.omega_singular h34 hRoot hs.toSec5 hnat hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨uB, hQuB, huB0, hBiff, -, -, hHyp⟩ :=
    hc.omega_points_core h34 hRoot hs.toSec5 hnat hK E hQ h3 hX φ hφ hker ψ hψ hsing
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, hv₀Z⟩ := hmov
  obtain ⟨r₀, hr₀, hu₀⟩ := hcon v₀ hv₀
  have hu₀V : ⁅x, v₀⁆ ∈ Vt M (LB M Q B) B Z t := by
    have e : ⁅x, v₀⁆ = (x * v₀ * x⁻¹) * v₀⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hxVn v₀ hv₀) ((Vt M (LB M Q B) B Z t).inv_mem hv₀)
  have hu₀c : ⁅x, v₀⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    have e : ⁅x, v₀⁆ = (⁅v₀, x⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).inv_mem
      (vanishGeom_comm_mem_conj hc hs hZV hg hq hv₀)
  have hu₀Z : secVec ψ ⟨⁅x, v₀⁆, hu₀V⟩ ≠ 0 := fun h => hv₀Z ((secVec_eq_zero_iff ψ _).mp h)
  have hQM : Q ≤ M := fun q hq => hc.LB_le_M (Subgroup.mem_sup_left hq)
  have hbM : ∀ b ∈ conjSubgroup r₀ B, b ∈ M := fun b hb => by
    have hb' : r₀⁻¹ * b * r₀ ∈ B := mem_conjSubgroup.mp hb
    have e : b = r₀ * (r₀⁻¹ * b * r₀) * r₀⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (hRM r₀ hr₀) (hQM (hc.le hb'))) (M.inv_mem (hRM r₀ hr₀))
  have hHR : conjSubgroup r₀ B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hbM b hb)
  obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hHR hu₀
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    have hb' : r₀⁻¹ * a * r₀ ∈ B := mem_conjSubgroup.mp ha
    have e : a = r₀ * (r₀⁻¹ * a * r₀) * r₀⁻¹ := by group
    rw [e]
    exact hVR r₀ hr₀ _ (hBV hb')
  have hzV : z ∈ Vt M (LB M Q B) B Z t := hZVle hz
  have hsv : secVec ψ ⟨⁅x, v₀⁆, hu₀V⟩ = secVec ψ ⟨a, haV⟩ := by
    have e : (⟨⁅x, v₀⁆, hu₀V⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨a, haV⟩ * ⟨z, hzV⟩ :=
      Subtype.ext haz.symm
    rw [e, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero]
  have hQa : Q' (secVec ψ ⟨a, haV⟩) = 0 := by
    have hb' : r₀⁻¹ * a * r₀ ∈ B := mem_conjSubgroup.mp ha
    have hbV : r₀⁻¹ * a * r₀ ∈ Vt M (LB M Q B) B Z t := hBV hb'
    obtain ⟨c, hc'⟩ := (hBiff (secVec ψ ⟨r₀⁻¹ * a * r₀, hbV⟩)).mp ⟨⟨_, hbV⟩, hb', rfl⟩
    have hsa : secVec ψ ⟨a, haV⟩ = (φ ⟨r₀, hr₀⟩ : Matrix ι ι K) *ᵥ
        secVec ψ ⟨r₀⁻¹ * a * r₀, hbV⟩ :=
      hψ ⟨r₀, hr₀⟩ ⟨r₀⁻¹ * a * r₀, hbV⟩ ⟨a, haV⟩ (by group)
    have hmemr : (φ ⟨r₀, hr₀⟩ : GL ι K) ∈ X := by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hsa, hc', vanishGeom_isometry_of_mem E hmemr, QuadraticMap.map_smul, hQuB, smul_zero]
  have hQu₀ : Q' (secVec ψ ⟨⁅x, v₀⁆, hu₀V⟩) = 0 := by
    rw [hsv]
    exact hQa
  obtain ⟨r₁, hr₁R, hr₁le⟩ := exists_point_le_of_singular h34 hRoot hc hs.toSec5 hnat hK E hQ h3
    hX hW φ hφ hker ψ hψ hg hu₀Z hQu₀ ⟨⟨⁅x, v₀⁆, hu₀V⟩, hu₀c, rfl⟩
  have hr₁M : r₁ ∈ M := hRM r₁ hr₁R
  have hr₁le' : conjSubgroup r₁ B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_trans le_sup_left hr₁le
  have hm₁M : g⁻¹ * r₁ ∈ M := M.mul_mem (M.inv_mem hg) hr₁M
  have hle : conjSubgroup (g⁻¹ * r₁) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    apply sup_le
    · rw [conjSubgroup_mul]
      exact vanishGeom_conj_le_of_le hr₁le'
    · exact hZVle
  obtain ⟨r₂, hr₂R, hE₁⟩ := hOrb (g⁻¹ * r₁) hm₁M hle
  have hr₂M : r₂ ∈ M := hRM r₂ hr₂R
  have hZg : conjSubgroup g Z = Z := conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hg)
  have hsup : ∀ (A C : Subgroup G), conjSubgroup g (A ⊔ C) = conjSubgroup g A ⊔ conjSubgroup g C :=
    fun A C => by
      unfold conjSubgroup
      exact Subgroup.map_sup _ _ _
  have hA : conjSubgroup g (conjSubgroup (g⁻¹ * r₁) B) = conjSubgroup r₁ B := by
    rw [← conjSubgroup_mul]
    congr 1
    group
  have hB : conjSubgroup g (conjSubgroup r₂ B) = conjSubgroup (g * r₂) B := by
    rw [conjSubgroup_mul]
  have hE₂ : conjSubgroup (g * r₂) B ⊔ Z = conjSubgroup r₁ B ⊔ Z := by
    have h := congrArg (conjSubgroup g) hE₁
    rw [hsup, hA, hZg, hsup, hB, hZg] at h
    exact h.symm
  have hLB := hc.conj_LB_eq_of_conj_BZ (M.mul_mem hg hr₂M) hr₁M hE₂
  have hconjQ : ∀ m ∈ M, ∀ y ∈ Q, m⁻¹ * y * m ∈ Q := fun m hm y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hm)) y).mp hy
    simpa using this
  have hLB_le : Q ≤ LB M Q B := fun q hq => Subgroup.mem_sup_left hq
  have htR : t ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht ht
  have hx1 : (g * r₂)⁻¹ * x * (g * r₂) ∈ LB M Q B := by
    have e : (g * r₂)⁻¹ * x * (g * r₂) =
        (r₂⁻¹ * (g⁻¹ * (x * (g * t * g⁻¹)⁻¹) * g) * r₂) * (⁅r₂⁻¹, t⁆ * t) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hq₁ : r₂⁻¹ * (g⁻¹ * (x * (g * t * g⁻¹)⁻¹) * g) * r₂ ∈ Q :=
      hconjQ r₂ hr₂M _ (hconjQ g hg _ hq)
    have ht' : ⁅r₂⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr₂R)
    exact (LB M Q B).mul_mem (hLB_le hq₁) ((LB M Q B).mul_mem (hLB_le ht') ht)
  have hx2 : x ∈ conjSubgroup (g * r₂) (LB M Q B) := mem_conjSubgroup.mpr hx1
  rw [hLB] at hx2
  have hx' : r₁⁻¹ * x * r₁ ∈ LB M Q B := mem_conjSubgroup.mp hx2
  have hq₀ : x * (g * t * g⁻¹)⁻¹ ∈ Q := hq
  have hq₂ : r₁⁻¹ * (x * (g * t * g⁻¹)⁻¹) * r₁ ∈ Q := hconjQ r₁ hr₁M _ hq₀
  have hgt : (r₁⁻¹ * g) * t * (r₁⁻¹ * g)⁻¹ ∈ LB M Q B := by
    have e2 : (r₁⁻¹ * g) * t * (r₁⁻¹ * g)⁻¹ =
        (r₁⁻¹ * (x * (g * t * g⁻¹)⁻¹) * r₁)⁻¹ * (r₁⁻¹ * x * r₁) := by
      group
    rw [e2]
    exact (LB M Q B).mul_mem (hLB_le (Q.inv_mem hq₂)) hx'
  have hgCN : (r₁⁻¹ * g) * t * (r₁⁻¹ * g)⁻¹ ∈ hc.CN t := by
    by_contra hn
    apply hno
    left
    refine ⟨t, htR, fun r hr => ?_, r₁⁻¹ * g, M.mul_mem (M.inv_mem hr₁M) hg, hgt, hn⟩
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.Rt_comm_mem_Q hr)
  have hx3 : r₁⁻¹ * x * r₁ ∈ hc.CN t := by
    have e3 : r₁⁻¹ * x * r₁ = (r₁⁻¹ * (x * (g * t * g⁻¹)⁻¹) * r₁) *
        ((r₁⁻¹ * g) * t * (r₁⁻¹ * g)⁻¹) := by
      group
    rw [e3]
    exact (hc.CN t).mul_mem (hc.Q_le_CN ht hq₂) hgCN
  have hxCN : x ∈ hc.CN t := by
    rw [Ctx.mem_CN] at hx3 ⊢
    obtain ⟨hx3R, hx3V⟩ := hx3
    refine ⟨?_, ?_⟩
    · have e4 : x = r₁ * (r₁⁻¹ * x * r₁) * r₁⁻¹ := by group
      rw [e4]
      exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hr₁R hx3R)
        ((Rt M (LB M Q B) t).inv_mem hr₁R)
    · intro v hv
      have hw : r₁⁻¹ * v * r₁ ∈ Vt M (LB M Q B) B Z t := by
        have := hVR r₁⁻¹ ((Rt M (LB M Q B) t).inv_mem hr₁R) v hv
        simpa using this
      have hz := hx3V _ hw
      have e5 : ⁅x, v⁆ = r₁ * ⁅r₁⁻¹ * x * r₁, r₁⁻¹ * v * r₁⁆ * r₁⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e5]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hr₁M) _).mp hz
  exact hv₀Z ((Ctx.mem_CN.mp hxCN).2 v₀ hv₀)

@[expose] def OmegaMinusFourGeomStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) →
      ∃ v ∈ Vt M (LB M Q B) B Z t, ∀ r ∈ Rt M (LB M Q B) t, ⁅x, v⁆ ∉ conjSubgroup r B ⊔ Z

theorem step71VanishGeom_of_omega3 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hZV : Sec7ZVStatement) (hOm4 : OmegaMinusFourGeomStatement) :
    Step71VanishGeomStatement := by
  unfold Step71VanishGeomStatement
  intro G _ _ M Q Z B hc n t hs hno x hx hxt hmov
  obtain ⟨m, hm2, hm⟩ := hs.orth
  rcases hm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  ·
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      subst h2
      exact hs.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    have hnat' := hnat
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hW : ∀ x y : (Fin m ⊕ Fin m) → K, x ≠ 0 → y ≠ 0 → quadPlus m K x = quadPlus m K y →
        ∃ A ∈ StatedOmega (StatedQuadPlus m K),
          ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = y :=
      fun a d ha hd hxy => statedOmegaPlus_exists_mulVec_eq hm3 ha hd hxy
    have hSC := (sec56SingularConj_of h34 hRoot).1 G M Q Z B hc n t hs.toSec5 K hK m hm3
    have hOrb := Ctx.conj_orbit_omegaPlus h34 hRoot hc hs.toSec5 hK hm3 hSC hnat'
    exact step71VanishGeom_core h34 hRoot hZV hc hs hno
      (Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat'⟩⟩) hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm3) φ hφ
      hker ψ hψ hW hOrb hx hxt hmov
  · by_cases hm2' : m = 2
    · subst hm2'
      exact hOm4 G M Q Z B hc n t hs hno ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ x hx hxt hmov
    ·
      have hm3 : 3 ≤ m := by omega
      haveI : CharP K 2 := sec7ctr_charP hc hK
      have hnat' := hnat
      obtain ⟨φ, hφ, hker, hact⟩ := hnat
      obtain ⟨-, hn, ψ, hψ⟩ := hact
      haveI := hn
      haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
      have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega
      have hW : ∀ x y : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) → K, x ≠ 0 → y ≠ 0 →
          quadMinus m K b c x = quadMinus m K b c y →
          ∃ A ∈ StatedOmega (StatedQuadMinus m K b c),
            ((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
              Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ
              x = y :=
        fun a d ha hd hxy => statedOmegaMinus_exists_mulVec_eq hm3 hirr ha hd hxy
      have hSC := (sec56SingularConj_of h34 hRoot).2 G M Q Z B hc n t hs.toSec5 K hK m b c hm3 hirr
      have hOrb := Ctx.conj_orbit_omegaMinus h34 hRoot hc hs.toSec5 hK hm3 hirr hSC hnat'
      exact step71VanishGeom_core h34 hRoot hZV hc hs hno
        (Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm2, hirr, hnat'⟩⟩) hK
        (ElemMatrixIso.minus hm2 hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus hm2 hirr) φ hφ hker ψ hψ hW hOrb hx hxt hmov

theorem step71VanishPair_of_omega4
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement)
    (hOm4 : OmegaMinusFourGeomStatement) (hWm4 : OmegaMinusFourSingularTransStatement) :
    Step71VanishPairStatement :=
  step71VanishPair_of_geom (step71VanishGeom_of_omega3 h34 hRoot hZV hOm4) h34 hRoot h310chi hZc
    hZV hZcard hWm4


end CFSG.RankThree.GF2n.Stroth80
