module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishGeom

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step71VanishGeom_point (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
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
    {v₀ : G} (hv₀ : v₀ ∈ Vt M (LB M Q B) B Z t) (hv₀Z : ⁅x, v₀⁆ ∉ Z) :
    ∀ r ∈ Rt M (LB M Q B) t, ⁅x, v₀⁆ ∉ conjSubgroup r B ⊔ Z := by
  classical
  intro r₀ hr₀ hu₀
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
  have hq₂ : r₁⁻¹ * (x * (g * t * g⁻¹)⁻¹) * r₁ ∈ Q := hconjQ r₁ hr₁M _ hq
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

theorem step71Vanish_defect_nonsingular (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
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
    {x : G} (hx : ConjMod M Q t x) (hxt : ⁅x, t⁆ ∈ Q) (F : (ι → K) →ₗ[K] (ι → K))
    (hF : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      F (secVec ψ k) = secVec ψ k') :
    ∀ w, F w ≠ w → Q' (F w - w) ≠ 0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxM : x ∈ M := hx.1
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)) v).mp hv
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hsing := hc.omega_singular h34 hRoot hs.toSec5 hnat hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨uB, hQuB, huB0, hBiff, -, -, -⟩ :=
    hc.omega_points_core h34 hRoot hs.toSec5 hnat hK E hQ h3 hX φ hφ hker ψ hψ hsing
  intro w hFw hQw
  obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
  have hcommV : ⁅x, (k : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
    have e : ⁅x, (k : G)⁆ = (x * k * x⁻¹) * (k : G)⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hxV k k.2) ((Vt M (LB M Q B) B Z t).inv_mem k.2)
  have hvec : secVec ψ ⟨⁅x, (k : G)⁆, hcommV⟩ = F (secVec ψ k) - secVec ψ k := by
    have e : (⟨⁅x, (k : G)⁆, hcommV⟩ : ↥(Vt M (LB M Q B) B Z t)) =
        ⟨x * k * x⁻¹, hxV k k.2⟩ * k⁻¹ := Subtype.ext (by simp [commutatorElement_def])
    rw [e, secVec_mul, secVec_inv, hF k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl, sub_eq_add_neg]
  have hne : F (secVec ψ k) - secVec ψ k ≠ 0 := sub_ne_zero.mpr hFw
  have hkZ : ⁅x, (k : G)⁆ ∉ Z := by
    intro hz
    apply hne
    rw [← hvec]
    exact (secVec_eq_zero_iff ψ _).mpr hz
  obtain ⟨A, hAX, hAu⟩ := hW uB _ huB0 hne (by rw [hQuB, hQw])
  have hAR : A ∈ φ.range := by rw [hφ]; exact hAX
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hAR
  obtain ⟨b, hbB, hbu⟩ := (hBiff uB).mpr ⟨1, (one_smul K uB).symm⟩
  have hrb : (r : G) * b * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hVR r r.2 b b.2
  have hvb : secVec ψ ⟨(r : G) * b * (r : G)⁻¹, hrb⟩ = (φ r : Matrix ι ι K) *ᵥ uB := by
    rw [← hbu]
    exact hψ r b ⟨(r : G) * b * (r : G)⁻¹, hrb⟩ rfl
  have hmem : ⁅x, (k : G)⁆ ∈ conjSubgroup (r : G) B ⊔ Z := by
    have h1 : secVec ψ ⟨⁅x, (k : G)⁆, hcommV⟩ = secVec ψ ⟨(r : G) * b * (r : G)⁻¹, hrb⟩ := by
      rw [hvec, hvb, hAu]
    refine mem_of_secVec_eq (le_sup_right : Z ≤ conjSubgroup (r : G) B ⊔ Z) ψ
      (w := ⟨(r : G) * b * (r : G)⁻¹, hrb⟩) (y := ⟨⁅x, (k : G)⁆, hcommV⟩) ?_ h1.symm
    refine Subgroup.mem_sup_left (mem_conjSubgroup.mpr ?_)
    have e : (r : G)⁻¹ * ((r : G) * b * (r : G)⁻¹) * r = b := by group
    rw [e]
    exact hbB
  exact step71VanishGeom_point h34 hRoot hZV hc hs hno hnat hK E hQ h3 hX φ hφ hker ψ hψ hW hOrb
    hx hxt k.2 hkZ r r.2 hmem

end CFSG.RankThree.GF2n.Stroth80
