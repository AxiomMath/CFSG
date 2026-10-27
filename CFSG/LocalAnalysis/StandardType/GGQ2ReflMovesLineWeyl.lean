module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemmaH4
import CFSG.LocalAnalysis.StandardType.GGE6DepBlockFrame
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2rw_zpowers_subtype_iff {G : Type} [Group G] {Bs : Subgroup G} {u : G}
    (hu : u ∈ Bs) (b : ↥Bs) :
    (b : G) ∈ Subgroup.zpowers u ↔ b ∈ Subgroup.zpowers (⟨u, hu⟩ : ↥Bs) := by
  constructor
  · rintro ⟨k, hk⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, hk⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem ggQ2rw_eq_inv_of_mem_zpowers {H : Type} [Group H] [Finite H] {x y : H}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1)
    (hyx : y ≠ x) : y = x⁻¹ := by
  classical
  have hx2 : x ^ 2 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc] using hx3
  have hxord : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  rw [mem_zpowers_iff_mem_range_orderOf] at hy
  rw [hxord] at hy
  rw [Finset.mem_image] at hy
  obtain ⟨n, hnmem, hn⟩ := hy
  rw [Finset.mem_range] at hnmem
  interval_cases n
  · exact absurd (by simpa using hn.symm) hy1
  · exact absurd (by simpa using hn.symm) hyx
  · rw [← hn, hx2]

private theorem ggQ2rw_reflCentre_of_inv {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) {r : MulAut ↥Bs} (hr : GGIsReflection 3 r) {c : ↥Bs}
    (hc1 : c ≠ 1) (hrc : r c = c⁻¹) : GGReflCentre r c := by
  classical
  have hcomm : IsMulCommutative ↥Bs := hBs.1
  have hc3 : c ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 c c.2)
  have hdc : r c * c⁻¹ = c := by
    have hc2 : c * c = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc] using hc3
    have hc4 : c ^ 4 = c := by
      calc c ^ 4 = c ^ 3 * c := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
        _ = 1 * c := by rw [hc3]
        _ = c := one_mul c
    calc r c * c⁻¹ = c⁻¹ * c⁻¹ := by rw [hrc]
      _ = (c * c) * (c * c) := by rw [← hc2]
      _ = c ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      _ = c := hc4
  let δ : ↥Bs →* ↥Bs :=
    { toFun := fun b => r b * b⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  let D : Subgroup ↥Bs := Subgroup.comap δ (Subgroup.zpowers c)
  have htop : (⊤ : Subgroup ↥Bs) ≤ D := by
    rw [← GGIsReflection.eqLocus_sup_zpowers_of_inverted_three hBs hr hc1 hrc]
    refine sup_le ?_ ?_
    · intro b hb
      change δ b ∈ Subgroup.zpowers c
      have hb' : r b = b := hb
      simp [δ, hb']
    · rw [Subgroup.zpowers_le]
      change δ c ∈ Subgroup.zpowers c
      rw [show δ c = c from hdc]
      exact Subgroup.mem_zpowers c
  intro b
  exact htop (Subgroup.mem_top b)

private theorem ggQ2rw_eq_one_or_of_mem_zpowers_of_sq {H : Type} [Group H] {r : H}
    (hr : r ^ 2 = 1) {x : H} (hx : x ∈ Subgroup.zpowers r) : x = 1 ∨ x = r := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hk]
  have hr' : r ^ (2 : ℤ) = 1 := by simpa using hr
  rw [zpow_eq_zpow_emod k hr']
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem ggQ2_refl_movesLine_of_weylGroup {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) {u : G} (hu : u ∈ Bs)
    {A W : Subgroup (MulAut ↥Bs)} (hWG : W ≤ ggAutomizer ⊤ Bs) (hW : GGWeylReflectionGroup 3 W)
    (hAW : A ≤ W) (hA1 : A ≠ ⊥) (hAu : ∀ φ ∈ A, φ ⟨u, hu⟩ = ⟨u, hu⟩)
    (hWu : ¬ ∀ φ ∈ W, φ ⟨u, hu⟩ = ⟨u, hu⟩) :
    ∃ φ ∈ W, GGIsReflection 3 φ ∧ GGQ2MovesLine Bs u φ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommBs : IsMulCommutative ↥Bs := hBs.1
  have hpow : ∀ b : ↥Bs, b ^ 3 = 1 :=
    fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  set x0 : ↥Bs := ⟨u, hu⟩ with hx0
  have hx0_ne : x0 ≠ 1 := by
    intro h1
    apply hWu
    intro φ hφ
    have hgoal : φ x0 = x0 := by rw [h1, map_one]
    simpa [hx0] using hgoal
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have : Finite ι := ggIsWeylMatrix_finite hM
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  have hgenM : Subgroup.closure (Set.range M.simple) = ⊤ := by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.subgroup_closure_range_simple (cs := M.toCoxeterSystem))
  have hclosureW : Subgroup.closure (Set.range (fun k => f (M.simple k))) =
      (⊤ : Subgroup ↥W) := by
    rw [show Set.range (fun k => f (M.simple k)) =
        f.toMonoidHom '' Set.range M.simple by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨M.simple k, ⟨k, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩]
    rw [← MonoidHom.map_closure, hgenM, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr f.surjective
  have hline_iff : ∀ b : ↥Bs, (b : G) ∈ Subgroup.zpowers u ↔ b ∈ Subgroup.zpowers x0 :=
    fun b => ggQ2rw_zpowers_subtype_iff hu b
  let LinePres : MulAut ↥Bs → Prop :=
    fun φ => ∀ b : ↥Bs, b ∈ Subgroup.zpowers x0 → φ b ∈ Subgroup.zpowers x0
  have hmoves_iff : ∀ φ : MulAut ↥Bs,
      GGQ2MovesLine Bs u φ ↔ ¬ LinePres φ := by
    intro φ
    constructor
    · rintro ⟨b, hb, hb'⟩ hP
      exact hb' ((hline_iff (φ b)).mpr (hP b ((hline_iff b).mp hb)))
    · intro hne
      by_contra hP
      exact hne fun b hb => by
        by_contra hb'
        exact hP ⟨b, (hline_iff b).mpr hb, fun h => hb' ((hline_iff (φ b)).mp h)⟩
  by_contra hconcl
  push Not at hconcl
  have hrefl_line : ∀ φ ∈ W, GGIsReflection 3 φ → LinePres φ := by
    intro φ hφ hr
    by_contra hP
    exact hconcl φ hφ hr ((hmoves_iff φ).mpr hP)
  have hgen_line : ∀ k : ι, LinePres (((f (M.simple k) : ↥W) : MulAut ↥Bs)) :=
    fun k => hrefl_line _ (f (M.simple k)).2 (hf k)
  have hlineM : ∀ g : M.Group, LinePres (((f g : ↥W) : MulAut ↥Bs)) := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range M.simple) := by
      rw [hgenM]; exact Subgroup.mem_top g
    refine Subgroup.closure_induction'' (s := Set.range M.simple)
      (p := fun g _ => LinePres (((f g : ↥W) : MulAut ↥Bs))) ?_ ?_ ?_ ?_ hg
    · rintro s ⟨k, rfl⟩
      exact hgen_line k
    · rintro s ⟨k, rfl⟩
      rw [show (M.simple k)⁻¹ = M.simple k from
        CoxeterSystem.inv_simple (cs := M.toCoxeterSystem) k]
      exact hgen_line k
    · intro b hb
      simpa using hb
    · intro x y _ _ hx hy b hb
      have hmul : (((f (x * y) : ↥W) : MulAut ↥Bs)) =
          (((f x : ↥W) : MulAut ↥Bs) * ((f y : ↥W) : MulAut ↥Bs)) := by
        rw [map_mul]
        rfl
      rw [hmul, MulAut.mul_apply]
      exact hx _ (hy b hb)
  have hW_line : ∀ w ∈ W, LinePres w := by
    intro w hw
    have h := hlineM (f.symm ⟨w, hw⟩)
    have hsymm : f (f.symm (⟨w, hw⟩ : ↥W)) = ⟨w, hw⟩ :=
      MulEquiv.apply_symm_apply f ⟨w, hw⟩
    rw [hsymm] at h
    exact h
  have hfix_all_of : (∀ k : ι, (((f (M.simple k) : ↥W) : MulAut ↥Bs) x0 = x0)) →
      ∀ g : M.Group, (((f g : ↥W) : MulAut ↥Bs) x0 = x0) := by
    intro hall g
    have hg : g ∈ Subgroup.closure (Set.range M.simple) := by
      rw [hgenM]; exact Subgroup.mem_top g
    refine Subgroup.closure_induction'' (s := Set.range M.simple)
      (p := fun g _ => (((f g : ↥W) : MulAut ↥Bs) x0 = x0)) ?_ ?_ ?_ ?_ hg
    · rintro s ⟨k, rfl⟩
      exact hall k
    · rintro s ⟨k, rfl⟩
      rw [show (M.simple k)⁻¹ = M.simple k from
        CoxeterSystem.inv_simple (cs := M.toCoxeterSystem) k]
      exact hall k
    · simp
    · intro x y _ _ hx hy
      simp [map_mul, hy, hx]
  have hex : ∃ k : ι, (((f (M.simple k) : ↥W) : MulAut ↥Bs) x0 ≠ x0) := by
    by_contra h
    push Not at h
    apply hWu
    intro φ hφ
    have hfix := hfix_all_of h (f.symm ⟨φ, hφ⟩)
    simpa [hx0] using hfix
  obtain ⟨k₀, hk₀⟩ := hex
  let rW : ↥W := f (M.simple k₀)
  let r : MulAut ↥Bs := (rW : MulAut ↥Bs)
  let c : M.Group := f.symm rW
  have hfc : f c = rW := MulEquiv.apply_symm_apply f rW
  have hrW : r ∈ W := rW.2
  have hrRefl : GGIsReflection 3 r := hf k₀
  have hrx : r x0 ≠ x0 := hk₀
  have hrS : r x0 ∈ Subgroup.zpowers x0 :=
    hW_line r hrW x0 (Subgroup.mem_zpowers x0)
  have hr1 : r x0 ≠ 1 := by
    intro h
    apply hx0_ne
    have := congrArg (fun y => (r⁻¹ : MulAut ↥Bs) y) h
    simpa using this
  have hrinv : r x0 = x0⁻¹ :=
    ggQ2rw_eq_inv_of_mem_zpowers (hpow x0) hx0_ne hrS hr1 hrx
  have hrCentre : GGReflCentre r x0 :=
    ggQ2rw_reflCentre_of_inv hBs hrRefl hx0_ne hrinv
  have hNT_top : ∀ φ ∈ ggAutomizer ⊤ Bs, ¬ GGIsTransvection 3 φ := by
    intro φ hφ
    rw [ggAutomizer_eq] at hφ
    exact hNT φ hφ
  have hr_top : r ∈ ggAutomizer ⊤ Bs := hWG hrW
  have hcentral : ∀ w ∈ W, w * r * w⁻¹ = r := by
    intro w hw
    have hw_top : w ∈ ggAutomizer ⊤ Bs := hWG hw
    have hwr_refl : GGIsReflection 3 (w * r * w⁻¹) := hrRefl.conj w
    have hwr_mem : w * r * w⁻¹ ∈ ggAutomizer ⊤ Bs :=
      (ggAutomizer ⊤ Bs).mul_mem ((ggAutomizer ⊤ Bs).mul_mem hw_top hr_top)
        ((ggAutomizer ⊤ Bs).inv_mem hw_top)
    have hwx_mem : w x0 ∈ Subgroup.zpowers x0 :=
      hW_line w hw x0 (Subgroup.mem_zpowers x0)
    have hwx_ne : w x0 ≠ 1 := by
      intro h
      apply hx0_ne
      have := congrArg (fun y => (w⁻¹ : MulAut ↥Bs) y) h
      simpa using this
    have hwx_inv : (w * r * w⁻¹) (w x0) = (w x0)⁻¹ := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hrinv, map_inv]
    have hwr_centre_wx : GGReflCentre (w * r * w⁻¹) (w x0) :=
      ggQ2rw_reflCentre_of_inv hBs hwr_refl hwx_ne hwx_inv
    have hzpeq : Subgroup.zpowers (w x0) = Subgroup.zpowers x0 := by
      by_cases hwx : w x0 = x0
      · rw [hwx]
      · rw [ggQ2rw_eq_inv_of_mem_zpowers (hpow x0) hx0_ne hwx_mem hwx_ne hwx,
          Subgroup.zpowers_inv]
    have hwr_centre : GGReflCentre (w * r * w⁻¹) x0 := by
      intro b
      have h1 := hwr_centre_wx b
      rwa [hzpeq] at h1
    exact ggIsReflection_eq_of_centre hBs hNT_top hwr_mem hr_top hwr_refl hrRefl
      hwr_centre hrCentre
  have hcomm_rW : ∀ w : ↥W, rW * w = w * rW := by
    intro w
    apply Subtype.ext
    have h := hcentral w w.2
    have h2 : ((w : ↥W) : MulAut ↥Bs) * r = r * ((w : ↥W) : MulAut ↥Bs) := by
      have h3 := congrArg (fun x => x * ((w : ↥W) : MulAut ↥Bs)) h
      simpa [mul_assoc] using h3
    exact h2.symm
  have hc_central : ∀ g : M.Group, g * c = c * g := by
    intro g
    apply f.injective
    rw [map_mul, map_mul, hfc]
    exact (hcomm_rW (f g)).symm
  have hc_eq : M.simple k₀ = c := by
    apply f.injective
    rw [hfc]
  have hcomm_simple : ∀ j : ι, M.simple k₀ * M.simple j = M.simple j * M.simple k₀ := by
    intro j
    rw [hc_eq]
    exact (hc_central (M.simple j)).symm
  have hc_sq : ∀ j : ι, (M.simple k₀ * M.simple j) ^ 2 = 1 := by
    intro j
    have hcomm := hcomm_simple j
    have hsi : M.simple k₀ * M.simple k₀ = 1 := by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        M.toCoxeterSystem.simple_mul_simple_self k₀
    have hsj : M.simple j * M.simple j = 1 := by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        M.toCoxeterSystem.simple_mul_simple_self j
    rw [pow_two]
    calc (M.simple k₀ * M.simple j) * (M.simple k₀ * M.simple j)
        = M.simple k₀ * (M.simple j * M.simple k₀) * M.simple j := by group
      _ = M.simple k₀ * (M.simple k₀ * M.simple j) * M.simple j := by rw [← hcomm]
      _ = (M.simple k₀ * M.simple k₀) * (M.simple j * M.simple j) := by group
      _ = 1 := by rw [hsi, hsj, one_mul]
  by_cases hsub : Subsingleton ι
  · have hleW : ∀ w : ↥W, w ∈ Subgroup.zpowers rW := by
      have hrangeW : Set.range (fun k => f (M.simple k)) = {rW} := by
        ext y
        constructor
        · rintro ⟨k, rfl⟩
          have hk : k = k₀ := Subsingleton.elim k k₀
          rw [hk, Set.mem_singleton_iff]
        · intro hy
          rw [Set.mem_singleton_iff] at hy
          exact ⟨k₀, hy.symm⟩
      have hle : Subgroup.closure (Set.range (fun k => f (M.simple k))) ≤
          Subgroup.zpowers rW := by
        rw [Subgroup.closure_le, hrangeW, Subgroup.zpowers_eq_closure]
        exact Subgroup.subset_closure
      intro w
      exact hle (by rw [hclosureW]; exact Subgroup.mem_top w)
    have hrW_sq : rW ^ 2 = 1 := by
      apply Subtype.ext
      exact hrRefl.1
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro φ hφ
    have hφW : φ ∈ W := hAW hφ
    have hmem : (⟨φ, hφW⟩ : ↥W) ∈ Subgroup.zpowers rW := hleW ⟨φ, hφW⟩
    rcases ggQ2rw_eq_one_or_of_mem_zpowers_of_sq hrW_sq hmem with h1 | hr
    · exact congrArg Subtype.val h1
    · exfalso
      have hφr : φ = r := congrArg Subtype.val hr
      have hfix : φ x0 = x0 := by simpa [hx0] using hAu φ hφ
      exact hrx (by rw [← hφr]; exact hfix)
  · push Not at hsub
    obtain ⟨j, k, hjk⟩ := hsub
    have hex2 : ∃ j : ι, j ≠ k₀ := by
      by_cases h : j = k₀
      · exact ⟨k, fun hk => hjk (h.trans hk.symm)⟩
      · exact ⟨j, h⟩
    obtain ⟨j, hji⟩ := hex2
    have hpath := ggRC_weyl_connected hM k₀ j
    have hk0j : k₀ ≠ j := fun h => hji h.symm
    rcases Relation.ReflTransGen.cases_head hpath with hEq | ⟨v, hv, _⟩
    · exact hk0j hEq
    · have hord : orderOf (M.simple k₀ * M.simple v) = M.M k₀ v := by
        simpa [CoxeterMatrix.toCoxeterSystem_simple] using
          CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem k₀ v
      have hdvd : M.M k₀ v ∣ 2 := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one (hc_sq v)
      have hoff : M.M k₀ v ≠ 1 := M.off_diagonal k₀ v hv.1
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact hoff h1
      · exact hv.2 h2

end CFSG.StandardType

end
