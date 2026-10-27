module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.Mathlib.LinearAlgebra.DeterminantFixedSubspace

public section
namespace CFSG.StandardType
open CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_plane_kernel_le_prime_mul_card_range {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (y z : V) (hy : y ≠ 0)
    (a d : Module.Dual (ZMod p) V) (a' : H → ZMod p)
    (b' : H → ZMod p) (c : H →* (ZMod p)ˣ) (d' : H → ZMod p)
    (hshape : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v = v +
      (a' g * a v + b' g * d v) • y + (((c g : ZMod p) - 1) * a v) • z + (d' g * d v) • z)
    (ha : a y = 0) (had : d y = 0) (haz : a z = 1) (hdz : d z = 0)
    : Nat.card H ≤ p * Nat.card c.range := by
  classical
  let U := c.ker
  have hnt : ∀ φ ∈ H, ¬ GGIsTransvection p φ := ggNoTransvection_of_le_automizer hNT hH
  have hshapeU : ∀ g : U, ∀ v,
      ggLin (p := p) ι g.1.1 v = v + (a' g.1 * a v + b' g.1 * d v) • y +
        (d' g.1 * d v) • z := by
    intro g v
    have hg : c g.1 = 1 := MonoidHom.mem_ker.mp g.2
    simpa only [hg, Units.val_one, sub_self, zero_mul, zero_smul, add_zero] using hshape g.1 v
  have ha_mul : ∀ g h : U, a' (g.1 * h.1) = a' g.1 + a' h.1 := by
    intro g h
    have hgz0 : ggLin (p := p) ι g.1.1 z = z + a' g.1 • y := by
      rw [hshapeU, haz, hdz]
      module
    have hhz0 : ggLin (p := p) ι h.1.1 z = z + a' h.1 • y := by
      rw [hshapeU, haz, hdz]
      module
    have hghz0 : ggLin (p := p) ι (g.1.1 * h.1.1) z = z + a' (g.1 * h.1) • y := by
      have hgv := hshapeU (g * h) z
      change ggLin (p := p) ι (g.1.1 * h.1.1) z =
        z + (a' (g.1 * h.1) * a z + b' (g.1 * h.1) * d z) • y +
          (d' (g.1 * h.1) * d z) • z at hgv
      rw [haz, hdz] at hgv
      simpa only [mul_one, mul_zero, add_zero, zero_smul] using hgv
    have hgz : ggLin (p := p) ι (g.1.1 * h.1.1) z = z + (a' g.1 + a' h.1) • y := by
      rw [map_mul, LinearEquiv.mul_apply]
      change ggLin (p := p) ι g.1.1 (ggLin (p := p) ι h.1.1 z) = _
      rw [hhz0, map_add, map_smul, hgz0]
      have hgy : ggLin (p := p) ι g.1.1 y = y := by
        rw [hshapeU, ha, had]
        module
      rw [hgy]
      module
    have heq : (a' (g.1 * h.1) - (a' g.1 + a' h.1)) • y = 0 := by
      have hgh' : ggLin (p := p) ι (g.1.1 * h.1.1) z =
          z + a' (g.1 * h.1) • y := hghz0
      rw [hgz] at hgh'
      have he : a' (g.1 * h.1) • y = (a' g.1 + a' h.1) • y :=
        add_left_cancel hgh'.symm
      rw [sub_smul, he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_right hy)
  let f : U →* Multiplicative (ZMod p) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (a' g.1)) (fun g h => ha_mul g h)
  have hker : ∀ g : U, f g = 1 → g = 1 := by
    intro g hg
    have hg0 : a' g.1 = 0 := (ofAdd_eq_one).mp hg
    let w : V := b' g.1 • y + d' g.1 • z
    have hφ : ∀ v, ggLin (p := p) ι g.1.1 v = v + d v • w := by
      intro v
      rw [hshapeU, hg0]
      dsimp only [w]
      module
    have hδw : d w = 0 := by simp [w, had, hdz]
    by_cases hd0 : d = 0
    · apply Subtype.ext
      apply Subtype.ext
      apply ggLin_injective (p := p) ι
      ext v
      simp [hφ, hd0]
    by_cases hw0 : w = 0
    · apply Subtype.ext
      apply Subtype.ext
      apply ggLin_injective (p := p) ι
      ext v
      simp [hφ, hw0]
    exact (hnt g.1.1 g.1.2 (ggIsTransvection_of_apply ι hw0 hd0 hδw hφ)).elim
  have hf : Function.Injective f := (injective_iff_map_eq_one f).mpr hker
  have hu : Nat.card U ≤ p := by
    have ht := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using ht
  calc Nat.card H = Nat.card c.ker * Nat.card c.range := (Subgroup.card_ker_mul_card_range c).symm
    _ ≤ p * Nat.card c.range := Nat.mul_le_mul_right _ hu


theorem card_plane_kernel_le_two_mul_prime {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (y z : V) (hy : y ≠ 0)
    (a d : Module.Dual (ZMod p) V) (a' : H → ZMod p)
    (b' : H → ZMod p) (c : H →* (ZMod p)ˣ) (d' : H → ZMod p)
    (hshape : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v = v +
      (a' g * a v + b' g * d v) • y + (((c g : ZMod p) - 1) * a v) • z + (d' g * d v) • z)
    (ha : a y = 0) (had : d y = 0) (haz : a z = 1) (hdz : d z = 0)
    (hc : ∀ g : H, c g = 1 ∨ c g = -1) : Nat.card H ≤ 2 * p := by
  classical
  have hker := card_plane_kernel_le_prime_mul_card_range hNT ι H hH y z hy a d a' b' c d'
    hshape ha had haz hdz
  have hr : Nat.card c.range ≤ 2 := by
    have hinc : c.range ≤ Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
      rintro x ⟨g, rfl⟩
      rcases hc g with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    calc Nat.card c.range ≤ Nat.card (Subgroup.zpowers (-1 : (ZMod p)ˣ)) :=
      Subgroup.card_le_of_le hinc
      _ = orderOf (-1 : (ZMod p)ˣ) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  calc Nat.card H ≤ p * Nat.card c.range := hker
    _ ≤ p * 2 := Nat.mul_le_mul_left _ hr
    _ = 2 * p := Nat.mul_comm _ _


theorem scalar_eq_of_faithful_prime_characters {p : ℕ} [Fact p.Prime]
    {U : Type} [Group U] [Nontrivial U]
    (a d : U →* Multiplicative (ZMod p))
    (ha : Function.Injective a) (hd : Function.Injective d)
    (τ : U → U) (r s : ZMod p)
    (hτa : ∀ u, Multiplicative.toAdd (a (τ u)) = r * Multiplicative.toAdd (a u))
    (hτd : ∀ u, Multiplicative.toAdd (d (τ u)) = s * Multiplicative.toAdd (d u)) : r = s := by
  classical
  obtain ⟨u, hu⟩ := exists_ne (1 : U)
  have hau : a u ≠ 1 := by intro h; exact hu (ha (h.trans a.map_one.symm))
  have hdu : d u ≠ 1 := by intro h; exact hu (hd (h.trans d.map_one.symm))
  have ha0 : Multiplicative.toAdd (a u) ≠ 0 := by exact hau
  have hd0 : Multiplicative.toAdd (d u) ≠ 0 := by exact hdu
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨n, hn⟩ := mem_powers_of_prime_card hcard hau (g' := a (τ u))
  have ht : τ u = u ^ n := ha (by simpa only [map_pow] using hn.symm)
  have hscalar (f : U →* Multiplicative (ZMod p)) :
      Multiplicative.toAdd (f (τ u)) = (n : ZMod p) * Multiplicative.toAdd (f u) := by
    rw [ht, map_pow]
    change n • Multiplicative.toAdd (f u) = _
    simp [nsmul_eq_mul]
  have hr : r = (n : ZMod p) := mul_right_cancel₀ ha0 ((hτa u).symm.trans (hscalar a))
  have hs : s = (n : ZMod p) := mul_right_cancel₀ hd0 ((hτd u).symm.trans (hscalar d))
  exact hr.trans hs.symm


theorem card_le_six_of_correlated_prime_three_characters {H : Type} [Group H] [Finite H]
    (mu c : H →* (ZMod 3)ˣ)
    (hk : Nat.card ↥(mu.prod c).ker ≤ 3)
    (hscalar : Nontrivial ↥(mu.prod c).ker → ∀ g : H, mu g = 1) :
    Nat.card H ≤ 6 := by
  classical
  by_cases hnt : Nontrivial ↥(mu.prod c).ker
  · have hm : ∀ g : H, mu g = 1 := hscalar hnt
    have hker : (mu.prod c).ker = c.ker := by
      ext g
      simp [MonoidHom.mem_ker, hm, Prod.ext_iff]
    have hcK : Nat.card c.ker ≤ 3 := by
      rw [← hker]
      exact hk
    have hcR : Nat.card c.range ≤ 2 := by
      calc Nat.card c.range ≤ Nat.card (ZMod 3)ˣ := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
        _ = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
    calc Nat.card H = Nat.card c.ker * Nat.card c.range := (Subgroup.card_ker_mul_card_range c).symm
      _ ≤ 3 * 2 := Nat.mul_le_mul hcK hcR
      _ = 6 := by norm_num
  · have hu : Subsingleton ↥(mu.prod c).ker := not_nontrivial_iff_subsingleton.mp hnt
    have hf : Function.Injective (mu.prod c) := (injective_iff_map_eq_one _).mpr fun g hg => by
      have he : (⟨g, MonoidHom.mem_ker.mpr hg⟩ : ↥(mu.prod c).ker) = 1 := @Subsingleton.elim _ hu _ _
      exact congrArg Subtype.val he
    calc Nat.card H ≤ Nat.card ((ZMod 3)ˣ × (ZMod 3)ˣ) := Nat.card_le_card_of_injective _ hf
      _ = 4 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units]
      _ ≤ 6 := by norm_num


theorem plane_scalar_eq_sq_of_nontrivial_kernel {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (y z v0 : V) (hy : y ≠ 0)
    (l a d : Module.Dual (ZMod p) V)
    (mu c : H →* (ZMod p)ˣ) (A B D : H → ZMod p)
    (hshape : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v = (mu g : ZMod p) • v +
      (((1 - (mu g : ZMod p)) * l v + A g * a v + B g * d v) • y) +
        (((c g : ZMod p) - (mu g : ZMod p)) * a v + D g * d v) • z)
    (hly : l y = 1) (hlz : l z = 0)
    (hay : a y = 0) (haz : a z = 1)
    (hdy : d y = 0) (hdz : d z = 0) (hdv : d v0 = 1)
    (hnt : Nontrivial ↥(mu.prod c).ker) : ∀ g : H, mu g = c g ^ 2 := by
  classical
  let U := (mu.prod c).ker
  let T (g : H) := ggLin (p := p) ι g.1
  have hmu (u : U) : mu u.1 = 1 := congrArg Prod.fst (MonoidHom.mem_ker.mp u.2)
  have hc (u : U) : c u.1 = 1 := congrArg Prod.snd (MonoidHom.mem_ker.mp u.2)
  have hGz (g : H) : T g z = (c g : ZMod p) • z + A g • y := by
    dsimp only [T]; rw [hshape, hlz, haz, hdz]; module
  have hGy (g : H) : T g y = y := by
    dsimp only [T]; rw [hshape, hly, hay, hdy]; module
  have haG (g : H) (v : V) : a (T g v) = (c g : ZMod p) * a v + D g * d v := by
    dsimp only [T]; rw [hshape]
    simp only [map_add, map_smul, hay, haz, smul_eq_mul]
    ring
  have hdG (g : H) (v : V) : d (T g v) = (mu g : ZMod p) * d v := by
    dsimp only [T]; rw [hshape]
    simp only [map_add, map_smul, hdy, hdz, smul_eq_mul, mul_zero, add_zero]
  have hAmul (u v : U) : A (u.1 * v.1) = A u.1 + A v.1 := by
    have hm : T (u.1 * v.1) z = T u.1 (T v.1 z) := by
      simp only [T, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply]
    simp only [hGz, hGy, map_add, map_smul] at hm
    simp only [map_mul, hc u, hc v, one_mul, Units.val_one, one_smul] at hm
    have he : (A (u.1 * v.1) - (A u.1 + A v.1)) • y = 0 := by
      have hm' : z + A (u.1 * v.1) • y = z + (A u.1 + A v.1) • y := by
        simpa only [map_mul, hc u, hc v, one_mul, Units.val_one, one_smul, add_assoc, add_smul] using hm
      rw [sub_smul, add_left_cancel hm', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hy)
  have hDmul (u v : U) : D (u.1 * v.1) = D u.1 + D v.1 := by
    have hm : a (T (u.1 * v.1) v0) = a (T u.1 (T v.1 v0)) := by
      simp only [T, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply]
    rw [haG, haG, haG, hdG, hc u, hc v, hmu v, hdv] at hm
    simp only [map_mul, hc u, hc v, one_mul, Units.val_one, mul_one, add_assoc] at hm
    linear_combination hm
  let fa : U →* Multiplicative (ZMod p) := MonoidHom.mk' (fun u => Multiplicative.ofAdd (A u.1)) hAmul
  let fd : U →* Multiplicative (ZMod p) := MonoidHom.mk' (fun u => Multiplicative.ofAdd (D u.1)) hDmul
  have hntv : ∀ φ ∈ H, ¬ GGIsTransvection p φ := ggNoTransvection_of_le_automizer hNT hH
  have hshapeU (u : U) (v : V) : T u.1 v = v + (A u.1 * a v + B u.1 * d v) • y + (D u.1 * d v) • z := by
    dsimp only [T]; rw [hshape, hmu u, hc u]
    simp only [Units.val_one, sub_self, zero_mul, zero_add, one_smul]
  have hfa : Function.Injective fa := (injective_iff_map_eq_one _).mpr fun u hu => by
    have hAu : A u.1 = 0 := (ofAdd_eq_one).mp hu
    let w := B u.1 • y + D u.1 • z
    have hlin : ∀ v, ggLin (p := p) ι u.1.1 v = v + d v • w := by
      intro v; rw [hshapeU, hAu]; dsimp only [w]; module
    have hdw : d w = 0 := by simp [w, hdy, hdz]
    have hdne : d ≠ 0 := by intro h; simp [h] at hdv
    by_cases hw : w = 0
    · apply Subtype.ext; apply Subtype.ext; apply ggLin_injective (p := p) ι
      ext v; simp [hlin, hw]
    · exact (hntv _ u.1.2 (ggIsTransvection_of_apply ι hw hdne hdw hlin)).elim
  have hfd : Function.Injective fd := (injective_iff_map_eq_one _).mpr fun u hu => by
    have hDu : D u.1 = 0 := (ofAdd_eq_one).mp hu
    let e : Module.Dual (ZMod p) V := A u.1 • a + B u.1 • d
    have hlin : ∀ v, ggLin (p := p) ι u.1.1 v = v + e v • y := by
      intro v; rw [hshapeU, hDu]; dsimp only [e]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; module
    have hey : e y = 0 := by simp [e, hay, hdy]
    by_cases he : e = 0
    · apply Subtype.ext; apply Subtype.ext; apply ggLin_injective (p := p) ι
      ext v; simp [hlin, he]
    · exact (hntv _ u.1.2 (ggIsTransvection_of_apply ι hy he hey hlin)).elim
  intro g
  let tau : U → U := fun u => ⟨g * u.1 * g⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp u.2]
    simp⟩
  have hcomm (u : U) (v : V) : T (tau u).1 (T g v) = T g (T u.1 v) := by
    have he : (tau u).1 * g = g * u.1 := by dsimp [tau]; group
    have h := congrArg (fun k : H => T k v) he
    simpa only [T, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply] using h
  have hta (u : U) : A (tau u).1 = (c g : ZMod p)⁻¹ * A u.1 := by
    have hm := hcomm u z
    simp only [hGz, hGy, hc u, hc (tau u), Units.val_one, one_smul, map_add, map_smul] at hm
    have he : ((c g : ZMod p) * A (tau u).1 - A u.1) • y = 0 := by
      have hm' : (c g : ZMod p) • z + ((c g : ZMod p) * A (tau u).1 + A g) • y =
          (c g : ZMod p) • z + (A g + A u.1) • y := by
        simpa only [smul_add, smul_smul, add_assoc, add_smul] using hm
      have h := add_left_cancel hm'
      have hsc : ((c g : ZMod p) * A (tau u).1 + A g - (A g + A u.1)) • y = 0 := by
        rw [sub_smul, h, sub_self]
      convert hsc using 1; module
    have heq := sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hy)
    have hcn : (c g : ZMod p) ≠ 0 := (c g).ne_zero
    calc
      A (tau u).1 = (c g : ZMod p)⁻¹ * ((c g : ZMod p) * A (tau u).1) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcn, one_mul]
      _ = (c g : ZMod p)⁻¹ * A u.1 := by rw [heq]
  have htd (u : U) : D (tau u).1 = ((c g : ZMod p) / (mu g : ZMod p)) * D u.1 := by
    have hm := congrArg a (hcomm u v0)
    rw [haG, haG, haG, hdG, haG, hdG, hc u, hc (tau u), hmu u, hdv] at hm
    simp only [Units.val_one, mul_one, one_mul] at hm
    have heq : (mu g : ZMod p) * D (tau u).1 = (c g : ZMod p) * D u.1 := by
      linear_combination hm
    have hmun : (mu g : ZMod p) ≠ 0 := (mu g).ne_zero
    calc
      D (tau u).1 = (mu g : ZMod p)⁻¹ * ((mu g : ZMod p) * D (tau u).1) := by
        rw [← mul_assoc, inv_mul_cancel₀ hmun, one_mul]
      _ = (mu g : ZMod p)⁻¹ * ((c g : ZMod p) * D u.1) := by rw [heq]
      _ = ((c g : ZMod p) / (mu g : ZMod p)) * D u.1 := by field_simp
  let : Nontrivial U := hnt
  have hsc : (c g : ZMod p)⁻¹ = (c g : ZMod p) / (mu g : ZMod p) :=
    scalar_eq_of_faithful_prime_characters fa fd hfa hfd tau _ _ hta htd
  apply Units.ext
  change (mu g : ZMod p) = (c g : ZMod p) ^ 2
  field_simp at hsc
  linear_combination hsc


theorem card_plane_correlated_le_six {G : Type} [Group G] [Finite G]  {Bs : Subgroup G} (hNT : GGNoTransvection 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (y z : V) (hy : y ≠ 0)
    (l a d : Module.Dual (ZMod 3) V)
    (mu c : H →* (ZMod 3)ˣ) (A B D : H → ZMod 3)
    (hshape : ∀ g : H, ∀ v, ggLin (p := 3) ι g.1 v = (mu g : ZMod 3) • v +
      (((1 - (mu g : ZMod 3)) * l v + A g * a v + B g * d v) • y) +
        (((c g : ZMod 3) - (mu g : ZMod 3)) * a v + D g * d v) • z)
    (hly : l y = 1) (hlz : l z = 0)
    (hay : a y = 0) (haz : a z = 1)
    (hdy : d y = 0) (hdz : d z = 0)
    : Nat.card H ≤ 6 := by
  classical
  let U := (mu.prod c).ker
  have hmu (u : U) : mu u.1 = 1 := congrArg Prod.fst (MonoidHom.mem_ker.mp u.2)
  have hc (u : U) : c u.1 = 1 := congrArg Prod.snd (MonoidHom.mem_ker.mp u.2)
  let H0 : Subgroup (MulAut ↥Bs) := U.map H.subtype
  let e : U ≃* H0 := U.equivMapOfInjective H.subtype Subtype.val_injective
  have hc0 : Nat.card U ≤ 3 := by
    let c0 : H0 →* (ZMod 3)ˣ := 1
    have hH0 : H0 ≤ ggAutomizer ⊤ Bs := by
      rintro _ ⟨g,hg,rfl⟩; exact hH g.2
    have hshape0 : ∀ g : H0, ∀ v, ggLin (p := 3) ι g.1 v = v +
        ((A (e.symm g).1) * a v + (B (e.symm g).1) * d v) • y +
          (((c0 g : ZMod 3) - 1) * a v) • z + ((D (e.symm g).1) * d v) • z := by
      intro g v
      have he : (e.symm g).1.1 = g.1 := congrArg Subtype.val (e.apply_symm_apply g)
      rw [← he, hshape, hmu, hc]
      simp [c0]
    have h := card_plane_kernel_le_prime_mul_card_range hNT ι H0 hH0 y z hy a d
      (fun g => A (e.symm g).1) (fun g => B (e.symm g).1) c0 (fun g => D (e.symm g).1)
      hshape0 hay hdy haz hdz
    have hcR : Nat.card c0.range = 1 := by
      rw [show c0.range = ⊥ from MonoidHom.range_one]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [hcR, mul_one] at h
    rw [Nat.card_congr e.toEquiv]
    exact h
  by_cases hd0 : d = 0
  · have hinj : Function.Injective (mu.prod c) := (injective_iff_map_eq_one _).mpr fun g hg => by
      have hmg : mu g = 1 := congrArg Prod.fst hg
      have hcg : c g = 1 := congrArg Prod.snd hg
      have hlin : ∀ v, ggLin (p := 3) ι g.1 v = v + (A g * a v) • y := by
        intro v
        rw [hshape, hmg, hcg, hd0]
        simp only [Units.val_one, sub_self, zero_mul, LinearMap.zero_apply, mul_zero,
          add_zero, zero_add, one_smul, zero_smul]
      have hntv := ggNoTransvection_of_le_automizer hNT hH g.1 g.2
      by_cases hA : A g = 0
      · apply Subtype.ext
        apply ggLin_injective (p := 3) ι
        ext v
        rw [hlin, hA, zero_mul, zero_smul, add_zero]
        change v = ggLin (p := 3) ι (1 : MulAut Bs) v
        rw [map_one]
        rfl
      · have hane : a ≠ 0 := by intro h; simp [h] at haz
        have hAane : (A g • a : Module.Dual (ZMod 3) V) ≠ 0 := by
          exact smul_ne_zero hA hane
        have hay' : (A g • a) y = 0 := by simp [hay]
        exact (hntv (ggIsTransvection_of_apply ι hy hAane hay'
          (by intro v; simpa [LinearMap.smul_apply, smul_eq_mul] using hlin v))).elim
    calc Nat.card H ≤ Nat.card ((ZMod 3)ˣ × (ZMod 3)ˣ) := Nat.card_le_card_of_injective _ hinj
      _ = 4 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units]
      _ ≤ 6 := by norm_num
  · obtain ⟨v, hv⟩ : ∃ v, d v ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (LinearMap.ext h)
    let v0 : V := (d v)⁻¹ • v
    have hdv : d v0 = 1 := by simp [v0, hv]
    have hscalar : Nontrivial U → ∀ g : H, mu g = 1 := by
      intro hn g
      rw [plane_scalar_eq_sq_of_nontrivial_kernel hNT ι H hH y z v0 hy l a d mu c A B D
        hshape hly hlz hay haz hdy hdz hdv hn g]
      have hsq : ∀ u : (ZMod 3)ˣ, u ^ 2 = 1 := by decide
      exact hsq _
    exact card_le_six_of_correlated_prime_three_characters mu c hc0 hscalar


theorem eq_one_of_fix_submodule_of_codim_le_one {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {g : MulAut ↥Bs} (hg : g ∈ ggAutomizer ⊤ Bs)
    (S : Submodule (ZMod p) V)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) S + 1)
    (hfix : ∀ v ∈ S, ggLin (p := p) ι g v = v)
    (hsq : ∀ v, ggLin (p := p) ι g (ggLin (p := p) ι g v - v) =
      ggLin (p := p) ι g v - v) : g = 1 := by
  classical
  let T := ggLin (p := p) ι g
  let N : V →ₗ[ZMod p] V := T.toLinearMap - LinearMap.id
  have hker : S ≤ N.ker := by
    intro v hv
    simp only [LinearMap.mem_ker, N, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      sub_eq_zero]
    exact hfix v hv
  have hdim := Submodule.finrank_mono hker
  have hsum := LinearMap.finrank_range_add_finrank_ker N
  have hr : Module.finrank (ZMod p) N.range ≤ 1 := by omega
  by_cases h0 : N = 0
  · apply ggLin_injective (p := p) ι
    have hT : T.toLinearMap = LinearMap.id := sub_eq_zero.mp h0
    ext v
    rw [map_one]
    change T v = v
    exact congrArg (fun f : V →ₗ[ZMod p] V => f v) hT
  have hRne : N.range ≠ ⊥ := by
    intro hr0
    apply h0
    apply LinearMap.ext
    intro v
    have hv := LinearMap.mem_range_self N v
    rw [hr0] at hv
    exact hv
  have hone : Module.finrank (ZMod p) N.range = 1 := by
    have hpos : 1 ≤ Module.finrank (ZMod p) N.range := Submodule.one_le_finrank_iff.mpr hRne
    omega
  have : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have htr : GGIsTransvection p g := (ggIsTransvection_iff_ggLin ι g).mpr ⟨hone, by
    intro w hw
    obtain ⟨v,rfl⟩ := hw
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hsq v⟩
  exact (ggNoTransvection_of_le_automizer hNT le_rfl g hg htr).elim


theorem eq_one_of_fix_submodule_of_det_one {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {g : MulAut Bs} (hg : g ∈ ggAutomizer ⊤ Bs)
    (S : Submodule (ZMod p) V)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) S + 1)
    (hfix : ∀ v ∈ S, ggLin (p := p) ι g v = v)
    (hdet : (ggLin (p := p) ι g).det = 1) : g = 1 := by
  have hmove := LinearEquiv.displacement_mem_of_fix_submodule_of_det_one (ggLin (p := p) ι g) S hcodim hfix hdet
  exact eq_one_of_fix_submodule_of_codim_le_one hNT ι hg S hcodim hfix
    (fun v => hfix _ (hmove v))


theorem finrank_add_cartan_rank_le_sup_coroot_rootker_add_card {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p)) :
    Module.finrank (ZMod p) V + Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤
      Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range h) ⊔ (LinearMap.pi a).ker) + Fintype.card Λ := by
  classical
  let R : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi a
  let U := Submodule.span (ZMod p) (Set.range h)
  let S := U ⊔ R.ker
  let f : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  have hcomp : R.comp f = (C.map (Int.castRingHom (ZMod p))).mulVecLin := by
    ext i j
    simp [R, f, hpair, Matrix.mulVec_single]
  have hfle : f.range ≤ U := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  have hmap : (R.comp f).range ≤ (R.comp S.subtype).range := by
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨f v, (show U ≤ S from le_sup_left) (hfle (LinearMap.mem_range_self f v))⟩,rfl⟩
  have hr : Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤
      Module.finrank (ZMod p) (R.comp S.subtype).range := by
    change Module.finrank (ZMod p) (C.map (Int.castRingHom (ZMod p))).mulVecLin.range ≤ _
    rw [← hcomp]
    exact Submodule.finrank_mono hmap
  have hkerfin : Module.finrank (ZMod p) (R.comp S.subtype).ker =
      Module.finrank (ZMod p) R.ker := by
    let e : (R.comp S.subtype).ker ≃ₗ[ZMod p] R.ker :=
      { toFun := fun x => ⟨x.1.1,x.2⟩
        invFun := fun x => ⟨⟨x.1,(show R.ker ≤ S from le_sup_right) x.2⟩,x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  have hS := LinearMap.finrank_range_add_finrank_ker (R.comp S.subtype)
  have hV := LinearMap.finrank_range_add_finrank_ker R
  have hrankR : Module.finrank (ZMod p) R.range ≤ Fintype.card Λ := by
    exact (Submodule.finrank_le R.range).trans_eq (Module.finrank_pi (ZMod p))
  change Module.finrank (ZMod p) V + Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤
    Module.finrank (ZMod p) S + Fintype.card Λ
  omega


theorem finrank_le_sup_coroot_rootker_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p)) :
    Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range h) ⊔ (LinearMap.pi a).ker) + 1 := by
  have hr := finrank_add_cartan_rank_le_sup_coroot_rootker_add_card h a hpair
  have hc := ggIntCartan_card_le_rank_add_one hM hC p hp2
  omega

theorem sup_coroot_rootker_eq_top_of_full_rank {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Submodule.span (ZMod p) (Set.range h) ⊔ (LinearMap.pi a).ker = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hr := finrank_add_cartan_rank_le_sup_coroot_rootker_add_card h a hpair
  rw [hfull] at hr
  have hle := Submodule.finrank_le (Submodule.span (ZMod p) (Set.range h) ⊔ (LinearMap.pi a).ker)
  omega


end CFSG.StandardType
