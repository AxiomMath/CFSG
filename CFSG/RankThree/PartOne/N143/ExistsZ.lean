module

import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.N143.Hessian
public import CFSG.RankThree.PartOne.N143.QEqual

public section

namespace CFSG.RankThree.PartOne.N143

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}

theorem JGood.torusImage_le {c : G} {J : Subgroup G} (h : JGood p A c J) :
    torusImage A J ≤ reflectionGroup p A := by
  rw [h.facts12.three.1]
  exact Subgroup.closure_mono Set.inter_subset_left

theorem JGood.reflection_inv {c : G} {J : Subgroup G} (h : JGood p A c J) {s : MulAut A}
    (hs : s ∈ reflectionSet p A) (hsJ : s ∈ torusImage A J) {x : MulAut A}
    (hxJ : x ∈ torusImage A J) (hx3 : x ^ 3 = 1) : s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := h.weyl
  have hs2 : s * s = 1 := Sec138Loc.mul_self_eq_one_of_reflection hs.1
  have hs1 : s ≠ 1 := by
    intro h1
    have := hs.1.1
    rw [h1, orderOf_one] at this
    omega
  have key : ∀ τ σ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → σ ^ 3 = 1 → τ * σ * τ⁻¹ = σ⁻¹ := by
    decide
  have h1 := key (e ⟨s, hsJ⟩) (e ⟨x, hxJ⟩)
    (by rw [← map_mul]; convert map_one e; exact Subtype.ext hs2)
    (fun h1 => hs1 (by
      have := e.injective (h1.trans (map_one e).symm)
      exact congrArg Subtype.val this))
    (by rw [← map_pow]; convert map_one e; exact Subtype.ext hx3)
  have h2 : e (⟨s, hsJ⟩ * ⟨x, hxJ⟩ * ⟨s, hsJ⟩⁻¹) = e ⟨x, hxJ⟩⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h1
  have := congrArg Subtype.val (e.injective h2)
  simpa using this

theorem exists_z (hJ : JFacts) {c : G} {L : Subgroup G} (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs) :
    ∃ (z : G) (hz : z ∈ Subgroup.normalizer (A : Set G)), z ^ 3 = 1 ∧
      A.normalizerMonoidHom ⟨z, hz⟩ = zs := by
  obtain ⟨c1, h1⟩ := hgood L hctx.facts13.inZeroStar
  obtain ⟨k, hk1, hk3, hzk⟩ := hspec.z_scalar
  obtain ⟨x0, hx0, hx03, a0, ha0, hne0⟩ := hJ.1 G p A c1 L h1
  obtain ⟨hx0L, hx0W⟩ := Subgroup.mem_inf.1 hx0
  set xs : MulAut A := A.normalizerMonoidHom ⟨x0, hx0W⟩ with hxs
  have hxsJ : xs ∈ torusImage A L := Sec12Three.mem_torusImage_iff.mpr ⟨x0, hx0L, hx0W, rfl⟩
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxs, ← map_pow]
    have : (⟨x0, hx0W⟩ : Subgroup.normalizer (A : Set G)) ^ 3 = 1 := Subtype.ext hx03
    rw [this, map_one]
  have hxs1 : xs ≠ 1 := by
    intro h
    apply hne0
    have := congrArg (fun φ : MulAut A => ((φ ⟨a0, ha0⟩ : A) : G)) h
    simpa [hxs] using this
  have hxsX : xs ∈ reflectionGroup p A := h1.torusImage_le hxsJ
  have hxsP : xs ∈ Ps := (hspec.mem_P xs hxsX).2 hxs3
  have hxsZ : xs ∉ Subgroup.zpowers zs := by
    intro hmem
    obtain ⟨s, hs, hsJ⟩ := h1.exists_reflection
    have hinv := h1.reflection_inv hs hsJ hxsJ hxs3
    have hcomm : s * xs = xs * s := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
      rw [← hi]
      exact (Commute.zpow_left (hspec.z_central s : Commute zs s) i).eq.symm
    have h2 : xs = xs⁻¹ := by
      rw [← hinv, mul_inv_eq_iff_eq_mul.2 hcomm]
    have h3 : xs * xs = 1 := by
      rw [eq_inv_iff_mul_eq_one] at h2
      exact h2
    apply hxs1
    calc xs = xs ^ 3 * (xs * xs)⁻¹ := by group
      _ = 1 := by rw [hxs3, h3]; simp
  obtain ⟨g', hg'P, hg'⟩ := hspec.heis xs hxsP hxsZ
  obtain ⟨g, hgW, hgg⟩ := WeylIso.exists_lift
    (WeylIso.closure_le_weyl (hspec.P_le hg'P))
  set y : G := g * x0 * g⁻¹ with hy
  have hyW : y ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgW hx0W) (Subgroup.inv_mem _ hgW)
  have hy3 : y ^ 3 = 1 := by
    rw [hy, conj_pow, hx03, mul_one, mul_inv_cancel]
  have hπy : A.normalizerMonoidHom ⟨y, hyW⟩ = xs * zs := by
    have : (⟨y, hyW⟩ : Subgroup.normalizer (A : Set G)) =
        ⟨g, hgW⟩ * ⟨x0, hx0W⟩ * ⟨g, hgW⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    have hgg' : A.normalizerMonoidHom ⟨g, hgW⟩ = g' := hgg
    rw [hgg', ← hxs, hg']
  have hyact : ∀ a ∈ A, y * a * y⁻¹ = x0 * a ^ k * x0⁻¹ := by
    intro a ha
    have h1' := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) hπy
    have e1 : ((A.normalizerMonoidHom ⟨y, hyW⟩ ⟨a, ha⟩ : A) : G) = y * a * y⁻¹ := rfl
    have e2 : (((xs * zs) ⟨a, ha⟩ : A) : G) = x0 * ((zs ⟨a, ha⟩ : A) : G) * x0⁻¹ := rfl
    simp only [e1, e2] at h1'
    rw [h1', hzk ⟨a, ha⟩]
    rfl
  have hu : x0⁻¹ * y ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hx0W) hyW
  have hus : IsScalarOn A (x0⁻¹ * y) := ⟨k, fun a ha => by
    have hπu : A.normalizerMonoidHom ⟨x0⁻¹ * y, hu⟩ = zs := by
      have : (⟨x0⁻¹ * y, hu⟩ : Subgroup.normalizer (A : Set G)) =
          ⟨x0, hx0W⟩⁻¹ * ⟨y, hyW⟩ := rfl
      rw [this, map_mul, map_inv, hπy, ← hxs]
      group
    have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) hπu
    have e1 : ((A.normalizerMonoidHom ⟨x0⁻¹ * y, hu⟩ ⟨a, ha⟩ : A) : G) =
        (x0⁻¹ * y) * a * (x0⁻¹ * y)⁻¹ := rfl
    simp only [e1] at h2
    rw [h2, hzk ⟨a, ha⟩]
    rfl⟩
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := by
    have := h1.mem_normalizer_mul_of_scalar hx0L hu hus
    simpa using this
  have hTA : ∀ a ∈ Tof A L, y * a * y⁻¹ = x0 * a ^ k * x0⁻¹ := fun a ha =>
    hyact a (Tof_le A L ha)
  obtain ⟨l, hlL, hlN, hlact⟩ := hJ.2.2.1 G p A c1 L h1 x0 hx0 hx03 ⟨a0, ha0, hne0⟩ y
    (Subgroup.mem_inf.2 ⟨hyN, hyW⟩) hy3 k hk1 hk3 hTA
  set z0 : G := l⁻¹ * y * l with hz0
  have hlc : Commute l c1 := (Sec12Three.comm_c_L h1.hyp l hlL).symm
  have hxc : Commute x0 c1 := (Sec12Three.comm_c_L h1.hyp x0 hx0L).symm
  have hc1A : c1 ∈ A := h1.hyp.c_mem
  have hz0c : z0 * c1 * z0⁻¹ = c1 ^ k := by
    have hyc : y * c1 * y⁻¹ = c1 ^ k := by
      rw [hyact c1 hc1A]
      exact mul_inv_eq_iff_eq_mul.2 (Commute.pow_right hxc k)
    have hlc1 : l * c1 * l⁻¹ = c1 := mul_inv_eq_iff_eq_mul.2 hlc
    have hlck : l⁻¹ * c1 ^ k * l = c1 ^ k := by
      have h' : c1 ^ k * l = l * c1 ^ k := (Commute.pow_right hlc k).eq.symm
      calc l⁻¹ * c1 ^ k * l = l⁻¹ * (c1 ^ k * l) := mul_assoc _ _ _
        _ = l⁻¹ * (l * c1 ^ k) := by rw [h']
        _ = c1 ^ k := inv_mul_cancel_left _ _
    calc z0 * c1 * z0⁻¹ = l⁻¹ * (y * (l * c1 * l⁻¹) * y⁻¹) * l := by simp only [hz0]; group
      _ = l⁻¹ * (y * c1 * y⁻¹) * l := by rw [hlc1]
      _ = c1 ^ k := by rw [hyc, hlck]
  have hlact' : ∀ a ∈ Tof A L, z0 * a * z0⁻¹ = a ^ k := hlact
  have hz0A : ∀ a ∈ A, z0 * a * z0⁻¹ = a ^ k := by
    intro a ha
    obtain ⟨hA1, -⟩ := h1.A_eq
    rw [hA1] at ha
    have hcommA : ∀ u ∈ Subgroup.zpowers c1, ∀ t ∈ Tof A L, u * t = t * u := fun u hu t ht =>
      Sec12Three.mul_comm_of_mem_A h1.hyp (Subgroup.zpowers_le.2 hc1A hu) (Tof_le A L ht)
    obtain ⟨u, hu, t, ht, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcommA ha
    have hu' : z0 * u * z0⁻¹ = u ^ k := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← conj_zpow, hz0c, ← zpow_natCast c1 k, ← zpow_mul, ← zpow_natCast (c1 ^ i) k,
        ← zpow_mul, mul_comm]
    calc z0 * (u * t) * z0⁻¹ = (z0 * u * z0⁻¹) * (z0 * t * z0⁻¹) := by group
      _ = u ^ k * t ^ k := by rw [hu', hlact' t ht]
      _ = (u * t) ^ k := (Commute.mul_pow (hcommA u hu t ht) k).symm
  have hz0W : z0 ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => by
      have hn' : n ∈ A := hn
      show z0 * n * z0⁻¹ ∈ (A : Set G)
      rw [hz0A n hn']
      exact A.pow_mem hn' k
  have hz03 : z0 ^ 3 = 1 := by
    have : z0 = l⁻¹ * y * l⁻¹⁻¹ := by simp [hz0]
    rw [this, conj_pow, hy3]
    group
  refine ⟨z0, hz0W, hz03, ?_⟩
  ext a
  show z0 * (a : G) * z0⁻¹ = ((zs a : A) : G)
  rw [hz0A a a.2, hzk a]
  rfl

end CFSG.RankThree.PartOne.N143
