module

public import CFSG.RankThree.GF2n.Stroth80.Sec5PtsCore
public import CFSG.RankThree.GF2n.Stroth80.Sec83Count
public import CFSG.RankThree.GF2n.Stroth80.Sec84Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem sec5NatPointsSp_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Sec5NatPointsSpStatement := by
  intro G _ _ M Q Z B hc n t hs hnat r hr hplane
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hnat
  obtain ⟨u, hu0, hL, hr'⟩ := hc.sp_points h34 hRoot hs hK hm φ hφ hker hact
  have hr1 := hr' ⟨r, hr⟩
  exact ⟨K, fK, finK, hK, m, hm, φ, u, (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u,
    hφ, hker, hact, hr1.1.mp hplane, hL, hr1.2⟩

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_hypPlane_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnat : SpNat hc t) :
    ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t ∧
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) := by
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hnat
  obtain ⟨u, hu0, hL, hr'⟩ := hc.sp_points h34 hRoot hs hK hm φ hφ hker hact
  obtain ⟨u', hu'⟩ : ∃ u' : Fin m ⊕ Fin m → K, spForm m K u u' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (spForm_nondegenerate.1 u hcon)
  have hu'0 : u' ≠ 0 := fun h0 => hu' (by rw [h0, map_zero])
  obtain ⟨r, hr⟩ := exists_mulVec_eq_of_range φ hφ (exists_statedSp_mulVec_eq hu0 hu'0)
  have hr1 := hr' r
  have hne : spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
    rw [hr]; exact hu'
  refine ⟨r, r.2, hr1.1.mpr hne, ?_⟩
  have hL2 := hr1.2
  rw [← hc.LB_conj (hc.Rt_le_M t r.2)] at hL2
  exact le_sup_secSp φ hφ hker hne hL hL2


theorem Ctx.Rt_eq_sup_of_51 (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hgen : Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B))) :
    Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B) := by
  have h1 := (h51 G M Q Z B hc n t hs hnat r hr hplane (conjSubgroup r B) (LB M Q B)
    (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl).1
  have hNle : hc.CN t ≤ LB M Q B ⊔ LB M Q (conjSubgroup r B) := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := h1 x hx
    exact Subgroup.mul_mem_sup ha.1 hb.1
  rw [sup_eq_right.mpr hNle] at hgen
  exact le_antisymm hgen (sup_le (le_Rt (LB M Q B) hs.mem) (hc.LB_conj_le_Rt_of_mem hs.mem hr))

theorem sec8AExists_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Sec8AExistsStatement := by
  intro G _ _ M Q Z B hc n t hs8
  obtain ⟨r, hr, hplane, hgen⟩ := hc.exists_hypPlane_sp h34 hRoot hs8.toSec5 hs8.spNat
  exact ⟨r, ⟨hr, hplane, hc.Rt_eq_sup_of_51 h51 hs8.toSec5 (Or.inl hs8.spNat) hr hplane hgen⟩⟩


theorem mem_sup_Z_iff_secVec {D V : Subgroup G} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [(Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (hZV : Z ≤ V) (hDV : D ≤ V)
    (hcent : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d) {w : ι → K}
    (hD : ∀ x : ι → K, (∃ b : ↥V, (b : G) ∈ D ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • w)
    (y : ↥V) : (y : G) ∈ D ⊔ Z ↔ ∃ c : K, secVec ψ y = c • w := by
  constructor
  · intro hy
    obtain ⟨d, hd, z, hz, hyz⟩ := exists_mul_of_mem_sup hcent hy
    have e : y = ⟨d, hDV hd⟩ * ⟨z, hZV hz⟩ := Subtype.ext hyz
    obtain ⟨c, hc⟩ := (hD (secVec ψ ⟨d, hDV hd⟩)).mp ⟨⟨d, hDV hd⟩, hd, rfl⟩
    refine ⟨c, ?_⟩
    rw [e, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hZV hz⟩).mpr hz, add_zero, hc]
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb, hbv⟩ := (hD (secVec ψ y)).mpr ⟨c, hc⟩
    exact mem_of_secVec_eq (S := D ⊔ Z) le_sup_right ψ (w := b) (Subgroup.mem_sup_left hb) hbv

theorem Ctx.conj_sup_eq_of_mulVec_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {m : G} (hm : m ∈ M) (hmV : conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t)
    {u d₀ : ι → K}
    (hBiff : ∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
      ∃ c : K, x = c • u)
    (hDiff : ∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ conjSubgroup m B ∧
      secVec ψ b = x) ↔ ∃ c : K, x = c • d₀)
    (r : ↥(Rt M (LB M Q B) t)) (hr : (φ r : Matrix ι ι K) *ᵥ u = d₀) :
    conjSubgroup m B ⊔ Z = conjSubgroup (r : G) B ⊔ Z := by
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hmV
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVR := hc.Rt_normalizes_Vt hs.mem
  have hCr : Ctx M Q Z (conjSubgroup (r : G) B) := hc.conj_of_mem (hc.Rt_le_M t r.2)
  have hrV : conjSubgroup (r : G) B ⊔ Z ≤ Vt M (LB M Q B) B Z t :=
    hc.conj_Rt_le_Vt hs.mem r.2
  have hcent : ∀ (D : Subgroup G), D ≤ Q → ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d := by
    intro D hDQ d hd z hz
    have := hc.conj_Z_of_mem_Q (hDQ hd) hz
    calc d * z = (d * z * d⁻¹) * d := by group
      _ = z * d := by rw [this]
  have hBr : ∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t),
      (b : G) ∈ conjSubgroup (r : G) B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • d₀ := by
    intro x
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb1 : (r : G)⁻¹ * (b : G) * (r : G) ∈ B := mem_conjSubgroup.mp hb
      have hb1V : (r : G)⁻¹ * (b : G) * (r : G) ∈ Vt M (LB M Q B) B Z t :=
        hc.B_le_Vt hs.mem hb1
      obtain ⟨c, hcc⟩ := (hBiff (secVec ψ ⟨_, hb1V⟩)).mp ⟨⟨_, hb1V⟩, hb1, rfl⟩
      refine ⟨c, ?_⟩
      have e1 := hψ r ⟨_, hb1V⟩ b (by group)
      show secVec ψ b = c • d₀
      rw [← hr]
      show Multiplicative.toAdd (ψ (QuotientGroup.mk b)) = _
      rw [e1]
      show (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨_, hb1V⟩ = _
      rw [hcc, Matrix.mulVec_smul]
    · rintro ⟨c, rfl⟩
      obtain ⟨b₁, hb₁B, hb₁⟩ := (hBiff (c • u)).mpr ⟨c, rfl⟩
      have hbV : (r : G) * (b₁ : G) * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
        (Subgroup.mem_normalizer_iff.mp (hVR r.2) b₁).mp b₁.2
      refine ⟨⟨_, hbV⟩, ?_, ?_⟩
      · rw [mem_conjSubgroup]
        show (r : G)⁻¹ * ((r : G) * (b₁ : G) * (r : G)⁻¹) * (r : G) ∈ B
        rw [show (r : G)⁻¹ * ((r : G) * (b₁ : G) * (r : G)⁻¹) * (r : G) = (b₁ : G) by group]
        exact hb₁B
      · have e1 := hψ r b₁ ⟨_, hbV⟩ rfl
        show Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨_, hbV⟩)) = _
        rw [e1]
        show (φ r : Matrix ι ι K) *ᵥ secVec ψ b₁ = _
        rw [hb₁, Matrix.mulVec_smul, hr]
  have key1 := mem_sup_Z_iff_secVec ψ hZV hDV (hcent _ hD.le) hDiff
  have key2 := mem_sup_Z_iff_secVec ψ hZV (le_trans le_sup_left hrV) (hcent _ hCr.le) hBr
  ext x
  constructor
  · intro hx
    have hxV : x ∈ Vt M (LB M Q B) B Z t := hmV hx
    exact (key2 ⟨x, hxV⟩).mpr ((key1 ⟨x, hxV⟩).mp hx)
  · intro hx
    have hxV : x ∈ Vt M (LB M Q B) B Z t := hrV hx
    exact (key1 ⟨x, hxV⟩).mpr ((key2 ⟨x, hxV⟩).mp hx)

theorem Ctx.conj_orbit_of_transitive (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X)
    (htrans : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → ∃ A ∈ X, (A : Matrix ι ι K) *ᵥ x = y)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z := by
  intro m hm hmV
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv hs.mem hK hX φ hφ ψ hψ
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ hglob θ hθ
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hmV
  obtain ⟨d₀, hd₀D, hd0, hDiff⟩ := hD.exists_point_of_le hDV ψ hglob θ hθ
  obtain ⟨A, hA, hAu⟩ := htrans (secVec ψ b₀) (secVec ψ d₀) hu0 hd0
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A := by
    rw [← hφ] at hA
    exact MonoidHom.mem_range.mp hA
  exact ⟨r, r.2, hc.conj_sup_eq_of_mulVec_eq hs φ ψ hψ hm hmV hBiff hDiff r
    (by rw [hr]; exact hAu)⟩

theorem stroth56Sp_holds : Stroth56SpStatement := by
  intro G _ _ M Q Z B hc n t hs8 m hm hmV
  obtain ⟨K, fK, finK, hK, mm, hmm, hnat⟩ := hs8.spNat
  haveI : Nonempty (Fin mm ⊕ Fin mm) := ⟨Sum.inl ⟨0, by omega⟩⟩
  exact hc.conj_orbit_of_transitive hs8.toSec5 hK addCommutantScalar_statedSp
    (fun x y hx hy => exists_statedSp_mulVec_eq hx hy) hnat m hm hmV

end CFSG.RankThree.GF2n.Stroth80
