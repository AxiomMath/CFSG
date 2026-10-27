module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylOuter
import CFSG.LocalAnalysis.StandardType.GGTriD4LineComponent
import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma triD4Line_conj_mul_conj {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    MulAut.conj (φ y) = φ * MulAut.conj y * φ⁻¹ := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private lemma triD4Line_conj_alpha_cube {G : Type*} [Group G] (α : MulAut G) (hα3 : α ^ 3 = 1)
    (x : G) : (MulAut.conj x * α) ^ 3 = MulAut.conj (x * α x * α (α x)) := by
  ext y
  simp only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply, map_mul,
    map_inv, mul_assoc]
  have h3y : α (α (α y)) = y := by
    have := congrArg (fun φ : MulAut G => φ y) hα3
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [h3y]

private lemma triD4Line_conj_alpha_inv_sq {G : Type*} [Group G] (α : MulAut G) (hα3 : α ^ 3 = 1)
    (x : G) : (MulAut.conj x * α⁻¹) ^ 2 = MulAut.conj (x * α⁻¹ x) * α := by
  have hα3' : α ^ 2 * α = 1 := by
    rw [← pow_succ]
    norm_num
    exact hα3
  have hαinv : α⁻¹ = α ^ 2 := inv_eq_of_mul_eq_one_right hα3'
  have h2 : α⁻¹ * α⁻¹ = α := by
    rw [hαinv, ← pow_add]
    rw [show (2:ℕ)+2 = 1+3 by norm_num, pow_add, hα3, mul_one, pow_one]
  ext y
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have h2y : α⁻¹ (α⁻¹ y) = α y := by
    simpa [MulAut.mul_apply] using congrArg (fun φ : MulAut G => φ y) h2
  rw [h2y]

private lemma triD4Line_conj_injective_of_center_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g h hgh
  have hmem : h⁻¹ * g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut G => φ z) hgh
    simp only [MulAut.conj_apply] at hz
    calc z * (h⁻¹ * g) = h⁻¹ * (h * z * h⁻¹) * g := by group
      _ = h⁻¹ * (g * z * g⁻¹) * g := by rw [← hz]
      _ = (h⁻¹ * g) * z := by group
  have h1 : h⁻¹ * g = 1 := Subgroup.mem_bot.mp (hZ ▸ hmem)
  calc g = h * (h⁻¹ * g) := by group
    _ = h * 1 := by rw [h1]
    _ = h := by rw [mul_one]

private lemma triD4Line_alpha_mem_centralizer {n : ℕ} {K : Type} [Field K] {k : Type} [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer {D.z₀}) :
    D.α y ∈ Subgroup.centralizer {D.z₀} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc D.α y * D.z₀ = D.α (y * D.z₀) := by rw [map_mul, D.α_z₀]
    _ = D.α (D.z₀ * y) := by rw [hy]
    _ = D.z₀ * D.α y := by rw [map_mul, D.α_z₀]

private lemma triD4Line_alpha_inv_mem_centralizer {n : ℕ} {K : Type} [Field K] {k : Type}
    [Field k] [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer {D.z₀}) :
    D.α⁻¹ y ∈ Subgroup.centralizer {D.z₀} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  apply D.α.injective
  rw [map_mul, map_mul, D.α_z₀]
  have hαinv : D.α (D.α⁻¹ y) = y := by simp [MulAut.inv_apply]
  rw [hαinv]
  exact hy

private lemma triD4Line_fix_or_torus_R_alpha {n : ℕ} (K : Type) [Field K] [Finite K]
    (k : Type) [Field k] [Algebra k K] (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hZ : Subgroup.center (GGTriD4R n K) = ⊥)
    (hA : IsElemAbelian 3 A) (hz : MulAut.conj D.z₀ ∈ A)
    (hE9 : Nat.card (triD4LineE n K A) = 9) (f : MulAut (GGTriD4R n K)) (hfA : f ∈ A)
    (hfo : f ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)))
    (x : GGTriD4R n K) (hxX₀ : x ∈ Subgroup.centralizer {D.z₀})
    (hf : f = MulAut.conj x * D.α) (hf3 : f ^ 3 = 1)
    (hdeg : Module.finrank k K = 3) (h3 : 3 ∣ Nat.card k - 1) (hk : Nat.card k = 2 ^ n) :
    (∃ f' ∈ A, f' ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) ∧
      ∀ J₁ : Subgroup (GGTriD4R n K), IsComponentOf J₁ (ggFix (MulAut.conj D.z₀)) →
        ∀ l ∈ J₁, f' l = l) ∨
    ∃ e₁ : GGTriD4R n K, MulAut.conj e₁ ∈ A ∧ e₁ ∉ Subgroup.zpowers D.z₀ ∧
      ∃ T : Subgroup (GGTriD4R n K), T ≤ Subgroup.centralizer {e₁} ∧
        Nonempty (T ≃* Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)) ×
          Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1))) := by
  set X₀ : Subgroup (GGTriD4R n K) := Subgroup.centralizer {D.z₀} with hX₀
  set EA : Subgroup (GGTriD4R n K) := triD4LineE n K A with hEA
  haveI : IsMulCommutative ↥A := hA.1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => Subgroup.mul_comm_of_mem_isMulCommutative A ha hb
  have hEAea : IsElemAbelian 3 EA := by
    rw [hEA]
    exact triD4Line_E_isElemAbelian K hZ A hA
  have hEAle : EA ≤ X₀ := by
    intro e he
    rw [hX₀, Subgroup.mem_centralizer_singleton_iff]
    have hcomm : MulAut.conj D.z₀ * MulAut.conj e = MulAut.conj e * MulAut.conj D.z₀ :=
      hAc _ hz _ he
    have h1 : MulAut.conj (D.z₀ * e) = MulAut.conj (e * D.z₀) := by
      rw [map_mul, map_mul]
      exact hcomm
    exact (triD4Line_conj_injective_of_center_bot hZ h1).symm
  have hzX₀ : D.z₀ ∈ X₀ := by
    rw [hX₀, Subgroup.mem_centralizer_singleton_iff]
  let zX : TriD4LineX k K := D.Θ ⟨D.z₀, hzX₀⟩
  let E : Subgroup (TriD4LineX k K) := (EA.subgroupOf X₀).map D.Θ.toMonoidHom
  have hEAab_sub : IsMulCommutative ↥(EA.subgroupOf X₀) := by
    haveI : IsMulCommutative ↥EA := hEAea.1
    refine IsMulCommutative.mk ⟨fun a b => Subtype.ext ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      Subgroup.mul_comm_of_mem_isMulCommutative EA (Subgroup.mem_subgroupOf.mp a.2)
        (Subgroup.mem_subgroupOf.mp b.2)
  have hEcard : Nat.card E = 9 := by
    rw [show E = (EA.subgroupOf X₀).map D.Θ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective D.Θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEAle).toEquiv, hE9]
  have hEea : IsElemAbelian 3 E := by
    constructor
    · refine IsMulCommutative.mk ⟨fun u v => ?_⟩
      apply Subtype.ext
      change (u : TriD4LineX k K) * (v : TriD4LineX k K) =
        (v : TriD4LineX k K) * (u : TriD4LineX k K)
      obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      exact congrArg D.Θ
        (Subgroup.mul_comm_of_mem_isMulCommutative (EA.subgroupOf X₀) hu' hv')
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hy3 : y ^ 3 = 1 :=
        Subtype.ext (hEAea.2 y.val (Subgroup.mem_subgroupOf.mp hy))
      have := congrArg D.Θ hy3
      simpa [map_pow] using this
  have hzX3 : orderOf zX = 3 := by
    rw [show zX = D.Θ ⟨D.z₀, hzX₀⟩ from rfl, MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe (⟨D.z₀, hzX₀⟩ : X₀)).symm.trans D.orderOf_z₀
  have hzXc : zX ∈ Subgroup.center (TriD4LineX k K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := D.Θ.surjective y
    have hcenter : (⟨D.z₀, hzX₀⟩ : X₀) ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp u.2
    have := Subgroup.mem_center_iff.mp hcenter w
    simpa [zX] using congrArg D.Θ this
  have hzXE : zX ∈ E := by
    refine Subgroup.mem_map.mpr ⟨⟨D.z₀, hzX₀⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hz
  let eX : TriD4LineX k K := D.Θ ⟨x, hxX₀⟩
  have hfX₀ : ∀ y : X₀, f y.val ∈ X₀ := by
    intro y
    rw [hf, MulAut.mul_apply]
    exact X₀.mul_mem (X₀.mul_mem hxX₀ (triD4Line_alpha_mem_centralizer D y.val y.2))
      (X₀.inv_mem hxX₀)
  have hact : ∀ y : X₀, D.Θ ⟨f y.val, hfX₀ y⟩ =
      eX * triD4LineSigma k K D.σ (D.Θ y) * eX⁻¹ := by
    intro y
    have hαy : D.α y.val ∈ X₀ := triD4Line_alpha_mem_centralizer D y.val y.2
    have hsub : (⟨f y.val, hfX₀ y⟩ : X₀) =
        ⟨x, hxX₀⟩ * ⟨D.α y.val, hαy⟩ * ⟨x, hxX₀⟩⁻¹ := by
      apply Subtype.ext
      simp [hf, MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    rw [hsub, map_mul, map_mul, map_inv, D.Θ_α y hαy]
  have hx : ∀ e ∈ E, eX * triD4LineSigma k K D.σ e * eX⁻¹ = e := by
    intro e he
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp he
    have hyEA : y.val ∈ EA := Subgroup.mem_subgroupOf.mp hy
    have hcomm : f * MulAut.conj y.val = MulAut.conj y.val * f := hAc f hfA _ hyEA
    have hfix : f y.val = y.val := by
      apply triD4Line_conj_injective_of_center_bot hZ
      rw [triD4Line_conj_mul_conj f y.val, hcomm]
      group
    have hfx : f y.val = x * D.α y.val * x⁻¹ := by
      rw [hf, MulAut.mul_apply, MulAut.conj_apply]
    have hxy : x * D.α y.val * x⁻¹ = y.val := by rw [← hfx]; exact hfix
    have hαy : D.α y.val ∈ X₀ := triD4Line_alpha_mem_centralizer D y.val y.2
    have hsub : (⟨x, hxX₀⟩ * ⟨D.α y.val, hαy⟩ * ⟨x, hxX₀⟩⁻¹ : X₀) = ⟨y.val, y.2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      exact hxy
    have hαyΘ : D.Θ ⟨D.α y.val, hαy⟩ = triD4LineSigma k K D.σ (D.Θ y) :=
      D.Θ_α y hαy
    rw [← hyeq]
    change eX * triD4LineSigma k K D.σ (D.Θ y) * eX⁻¹ = D.Θ y
    rw [← hαyΘ]
    calc eX * D.Θ ⟨D.α y.val, hαy⟩ * eX⁻¹
        = D.Θ ⟨x, hxX₀⟩ * D.Θ ⟨D.α y.val, hαy⟩ * D.Θ ⟨x, hxX₀⟩⁻¹ := by
            simp only [map_inv, eX]
      _ = D.Θ (⟨x, hxX₀⟩ * ⟨D.α y.val, hαy⟩ * ⟨x, hxX₀⟩⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = D.Θ y := by rw [hsub]
  have hα3 : D.α ^ 3 = 1 := by simpa [D.orderOf_α] using pow_orderOf_eq_one D.α
  have hx3 : eX * triD4LineSigma k K D.σ eX * triD4LineSigma k K (D.σ ^ 2) eX = 1 := by
    have hcube : MulAut.conj (x * D.α x * D.α (D.α x)) = 1 := by
      rw [← triD4Line_conj_alpha_cube D.α hα3 x, ← hf]
      exact hf3
    have hxR : x * D.α x * D.α (D.α x) = 1 :=
      triD4Line_conj_injective_of_center_bot hZ (by simpa using hcube)
    have hαx : D.α x ∈ X₀ := triD4Line_alpha_mem_centralizer D x hxX₀
    have hα2x : D.α (D.α x) ∈ X₀ := triD4Line_alpha_mem_centralizer D (D.α x) hαx
    have hmem : x * D.α x * D.α (D.α x) ∈ X₀ :=
      X₀.mul_mem (X₀.mul_mem hxX₀ hαx) hα2x
    have h1 : D.Θ ⟨x * D.α x * D.α (D.α x), hmem⟩ = 1 := by
      rw [show (⟨x * D.α x * D.α (D.α x), hmem⟩ : X₀) = ⟨1, X₀.one_mem⟩ from
        Subtype.ext hxR]
      exact map_one D.Θ
    have h2 : D.Θ ⟨x * D.α x * D.α (D.α x), hmem⟩ =
        eX * triD4LineSigma k K D.σ eX * triD4LineSigma k K D.σ
          (triD4LineSigma k K D.σ eX) := by
      have hsub2 : (⟨x * D.α x * D.α (D.α x), hmem⟩ : X₀) =
          ⟨x, hxX₀⟩ * ⟨D.α x, hαx⟩ * ⟨D.α (D.α x), hα2x⟩ := Subtype.ext rfl
      rw [hsub2, map_mul, map_mul]
      simp only [D.Θ_α ⟨x, hxX₀⟩ hαx, D.Θ_α ⟨D.α x, hαx⟩ hα2x, eX]
    have hsq : D.σ ^ 2 = D.σ * D.σ := by rw [pow_two]
    rw [hsq, triD4LineSigma_mul_apply, ← h2]
    exact h1
  obtain hdich := triD4LineX_fix_or_torus k K hdeg h3 D.σ D.orderOf_σ zX hzX3 hzXc E hEea
    hEcard hzXE eX hx hx3
  rcases hdich with ⟨e', he'E, hfix⟩ | ⟨e₁, he₁E, he₁z, T, hT, hTiso⟩
  · left
    obtain ⟨e'R', he'R'map, he'R'eq⟩ := Subgroup.mem_map.mp he'E
    let e'R : GGTriD4R n K := e'R'.val
    have he'R_A : MulAut.conj e'R ∈ A := Subgroup.mem_subgroupOf.mp he'R'map
    have he'R_X₀ : e'R ∈ X₀ := e'R'.2
    let f'' : MulAut (GGTriD4R n K) := MulAut.conj e'R * f
    have hf''A : f'' ∈ A := A.mul_mem he'R_A hfA
    have hf''o : f'' ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) := by
      intro hmem
      obtain ⟨g, hg⟩ := hmem
      apply hfo
      refine ⟨e'R⁻¹ * g, ?_⟩
      calc MulAut.conj (e'R⁻¹ * g) = (MulAut.conj e'R)⁻¹ * MulAut.conj g := by
            rw [map_mul, map_inv]
        _ = (MulAut.conj e'R)⁻¹ * f'' := by rw [hg]
        _ = f := by dsimp [f'']; group
    refine ⟨f'', hf''A, hf''o, ?_⟩
    have hgg : ggFix (MulAut.conj D.z₀) = X₀ := by
      ext z
      rw [mem_ggFix, MulAut.conj_apply, hX₀, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hz'
        calc z * D.z₀ = (D.z₀ * z * D.z₀⁻¹) * D.z₀ := by rw [hz']
          _ = D.z₀ * z := by group
      · intro hz'
        calc D.z₀ * z * D.z₀⁻¹ = z * D.z₀ * D.z₀⁻¹ := by rw [← hz']
          _ = z := by group
    intro J₁ hJ' l hl
    rw [hgg] at hJ'
    have hJle : J₁ ≤ X₀ := hJ'.1
    have hcomp : IsComponentOf (J₁.subgroupOf X₀) ⊤ := by
      refine ⟨le_top, ?_, ?_⟩
      · exact IsSubnormal.of_mathlib (IsSubnormal.subgroupOf hJ'.2.1)
      · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ'.1)
          hJ'.2.2
    have hcompmap : IsComponentOf ((J₁.subgroupOf X₀).map D.Θ.toMonoidHom) ⊤ := by
      simpa [Subgroup.map_top, MulEquiv.range_eq_top] using
        isComponentOf_map_of_injective D.Θ.toMonoidHom D.Θ.injective hcomp
    have hN0 : (J₁.subgroupOf X₀).map D.Θ.toMonoidHom = triD4LineN0 k K :=
      (triD4LineN0_unique_component k K _).mp hcompmap
    have hlX₀ : l ∈ X₀ := hJle hl
    have hlN0 : D.Θ ⟨l, hlX₀⟩ ∈ triD4LineN0 k K := by
      rw [← hN0]
      exact Subgroup.mem_map.mpr ⟨⟨l, hlX₀⟩, by rw [Subgroup.mem_subgroupOf]; exact hl, rfl⟩
    have hfixl := hfix (D.Θ ⟨l, hlX₀⟩) hlN0
    have hflX₀ : f l ∈ X₀ := hfX₀ ⟨l, hlX₀⟩
    have hf''lX₀ : f'' l ∈ X₀ :=
      X₀.mul_mem (X₀.mul_mem he'R_X₀ hflX₀) (X₀.inv_mem he'R_X₀)
    have hfl : f l = x * D.α l * x⁻¹ := by rw [hf, MulAut.mul_apply, MulAut.conj_apply]
    have htheta : D.Θ ⟨f'' l, hf''lX₀⟩ = D.Θ ⟨l, hlX₀⟩ := by
      have hsub : (⟨f'' l, hf''lX₀⟩ : X₀) =
          ⟨e'R, he'R_X₀⟩ * ⟨f l, hflX₀⟩ * ⟨e'R, he'R_X₀⟩⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul, map_mul, map_inv]
      have hΘe' : D.Θ ⟨e'R, he'R_X₀⟩ = e' := by
        change D.Θ ⟨e'R'.val, he'R_X₀⟩ = e'
        rw [show (⟨e'R'.val, he'R_X₀⟩ : X₀) = e'R' from Subtype.ext rfl]
        exact he'R'eq
      have hΘfl : D.Θ ⟨f l, hflX₀⟩ =
          eX * triD4LineSigma k K D.σ (D.Θ ⟨l, hlX₀⟩) * eX⁻¹ := hact ⟨l, hlX₀⟩
      rw [hΘe', hΘfl]
      calc e' * (eX * triD4LineSigma k K D.σ (D.Θ ⟨l, hlX₀⟩) * eX⁻¹) * e'⁻¹
          = e' * eX * triD4LineSigma k K D.σ (D.Θ ⟨l, hlX₀⟩) * eX⁻¹ * e'⁻¹ := by group
        _ = D.Θ ⟨l, hlX₀⟩ := hfixl
    exact congrArg Subtype.val (D.Θ.injective htheta)
  · right
    obtain ⟨e₁R', he₁R'map, he₁R'eq⟩ := Subgroup.mem_map.mp he₁E
    let e₁R : GGTriD4R n K := e₁R'.val
    have he₁R_A : MulAut.conj e₁R ∈ A := Subgroup.mem_subgroupOf.mp he₁R'map
    have he₁R_z : e₁R ∉ Subgroup.zpowers D.z₀ := by
      intro hzpow
      apply he₁z
      have hsub : e₁R' ∈ Subgroup.zpowers (⟨D.z₀, hzX₀⟩ : X₀) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzpow
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        have hval : (⟨D.z₀, hzX₀⟩ : X₀) ^ k = e₁R' := by
          apply Subtype.ext
          simpa [e₁R] using hk
        rw [hval]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsub
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      rw [← he₁R'eq]
      change (D.Θ ⟨D.z₀, hzX₀⟩) ^ k = D.Θ e₁R'
      rw [← map_zpow, hk]
    let T_R : Subgroup (GGTriD4R n K) := T.map (X₀.subtype.comp D.Θ.symm.toMonoidHom)
    have hTR_le : T_R ≤ Subgroup.centralizer {e₁R} := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ht' : t * e₁ = e₁ * t := Subgroup.mem_centralizer_singleton_iff.mp (hT ht)
      have h := congrArg (fun z => (D.Θ.symm z).val) ht'
      rw [map_mul, map_mul] at h
      have he₁symm : D.Θ.symm e₁ = e₁R' := by
        rw [← he₁R'eq]
        exact MulEquiv.symm_apply_apply D.Θ e₁R'
      rw [he₁symm] at h
      simpa [e₁R] using h
    refine ⟨e₁R, he₁R_A, he₁R_z, T_R, hTR_le, ?_⟩
    have hinj : Function.Injective (X₀.subtype.comp D.Θ.symm.toMonoidHom) := by
      intro a b hab
      exact D.Θ.symm.injective (Subtype.ext hab)
    obtain ⟨iso⟩ := hTiso
    have hm : Nat.card k ^ 2 + Nat.card k + 1 = (2 ^ n) ^ 2 + 2 ^ n + 1 := by rw [hk]
    refine ⟨(T.equivMapOfInjective (X₀.subtype.comp D.Θ.symm.toMonoidHom) hinj).symm.trans
      (iso.trans (MulEquiv.cast (M := fun m => Multiplicative (ZMod m) ×
        Multiplicative (ZMod m)) hm))⟩


theorem triD4Line_fix_or_torus_R
    {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n) (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A)
    (hz : MulAut.conj D.z₀ ∈ A) :
    (∃ f ∈ A, f ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) ∧
      ∀ J₁ : Subgroup (GGTriD4R n K), IsComponentOf J₁ (ggFix (MulAut.conj D.z₀)) →
        ∀ l ∈ J₁, f l = l) ∨
    ∃ e₁ : GGTriD4R n K, MulAut.conj e₁ ∈ A ∧ e₁ ∉ Subgroup.zpowers D.z₀ ∧
      ∃ T : Subgroup (GGTriD4R n K), T ≤ Subgroup.centralizer {e₁} ∧
        Nonempty (T ≃* Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)) ×
          Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1))) := by
  have hn1 : 1 ≤ n := by omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype K := Fintype.ofFinite K
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn1 K hK
  obtain ⟨hE9, f, hfA, hfo, hf3, _hdec⟩ := triD4Line_A_structure hn1 hev K hK A hA h27
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    haveI := hA.1
    intro a ha b hb
    exact Subgroup.mul_comm_of_mem_isMulCommutative A ha hb
  have hdeg : Module.finrank k K = 3 := by
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    exact (Nat.pow_right_injective h2n hcard).symm
  have h3 : 3 ∣ Nat.card k - 1 := by
    rw [hk]
    obtain ⟨m, rfl⟩ := hev
    have h4 : 3 ∣ 4 ^ m - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    have e : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    rw [e]; exact h4
  obtain ⟨x, hxX₀, hfx | hfx⟩ :=
    triD4Line_outer_form hn1 K hK k D A hcomm hz f hfA hfo hf3
  · exact triD4Line_fix_or_torus_R_alpha K k D A hZ hA hz hE9 f hfA hfo x hxX₀ hfx hf3
      hdeg h3 hk
  · have hα3 : D.α ^ 3 = 1 := by simpa [D.orderOf_α] using pow_orderOf_eq_one D.α
    refine triD4Line_fix_or_torus_R_alpha K k D A hZ hA hz hE9 (f ^ 2) ?_ ?_
      (x * D.α⁻¹ x) ?_ ?_ ?_ hdeg h3 hk
    · exact A.pow_mem hfA 2
    · intro hmem
      obtain ⟨g, hg⟩ := hmem
      apply hfo
      have hf4 : f = (f ^ 2) ^ 2 := by
        rw [← pow_mul]
        rw [show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_add, hf3, one_mul, pow_one]
      refine ⟨g ^ 2, ?_⟩
      calc MulAut.conj (g ^ 2) = (MulAut.conj g) ^ 2 := by rw [map_pow]
        _ = (f ^ 2) ^ 2 := by rw [hg]
        _ = f := hf4.symm
    · exact Subgroup.mul_mem _ hxX₀ (triD4Line_alpha_inv_mem_centralizer D x hxX₀)
    · rw [hfx]
      exact triD4Line_conj_alpha_inv_sq D.α hα3 x
    · have hpow : (f ^ 2) ^ 3 = (f ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
      rw [hpow, hf3, one_pow]

end CFSG.StandardType
