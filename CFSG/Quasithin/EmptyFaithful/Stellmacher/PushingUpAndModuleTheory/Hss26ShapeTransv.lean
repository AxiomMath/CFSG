module

public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreNat

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push
  CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem exists_transvectionWith {V : Type*} [CommGroup V] [Finite V] (t : MulAut V) (ht : t ≠ 1)
    (D : Subgroup V) (hD : D.index ≤ 2) (hfix : ∀ v ∈ D, t v = v) :
    ∃ w, IsTransvectionWith t w := by
  obtain ⟨v₀, hv₀⟩ := B1.exists_moved_of_ne_one ht
  have hv₀D : v₀ ∉ D := fun h => hv₀ (hfix v₀ h)
  have hi2 : D.index = 2 := by
    have h1 : D.index ≠ 1 := fun h => hv₀D (by rw [Subgroup.index_eq_one.mp h]; trivial)
    have h0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨e, he⟩ := Subgroup.index_eq_two_iff.mp hi2
  refine ⟨t v₀ * v₀⁻¹, ?_, fun v => ?_⟩
  · intro h
    exact hv₀ (mul_inv_eq_one.mp h)
  · by_cases hv : v ∈ D
    · exact Or.inl (hfix v hv)
    · right
      have h1 : v * e ∈ D := by
        rcases he v with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hv
      have h2 : v₀ * e ∈ D := by
        rcases he v₀ with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hv₀D
      have h3 : v * v₀⁻¹ ∈ D := by
        have := D.mul_mem h1 (D.inv_mem h2)
        simpa [mul_inv_rev, mul_assoc] using this
      have h4 := hfix _ h3
      rw [map_mul, map_inv] at h4
      calc t v = (t v * (t v₀)⁻¹) * t v₀ := by group
        _ = (v * v₀⁻¹) * t v₀ := by rw [h4]
        _ = v * (t v₀ * v₀⁻¹) := by rw [mul_assoc, mul_comm v₀⁻¹ (t v₀)]

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conjAct_coe_apply (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : V) :
    ((CFSG.Quasithin.conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) x

omit [Finite G] in
theorem conjAct_eq_one_iff' {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    CFSG.Quasithin.conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have := congrArg (fun f : MulAut V => ((f ⟨z, hz⟩ : V) : G)) h
    simp only [conjAct_coe_apply, MulAut.one_apply] at this
    calc z * g = (g * z * (g : G)⁻¹) * g := by rw [this]
      _ = g * z := by group
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [conjAct_coe_apply]
    have := h v v.2
    calc (g : G) * v * (g : G)⁻¹ = (v * g) * (g : G)⁻¹ := by rw [this]
      _ = v := by group

theorem false_of_inverted {n : ℕ} {X P Z : Subgroup G} (hPH : PushHyp X P Z)
    (φ : ↥X →* Perm (Fin n)) (hφ1 : ∀ u : ↥X, φ u = 1 ↔ (u : G) ∈ pCoreOf 2 X)
    (hJ : ¬ thompsonJ P ≤ pCoreOf 2 X) {x : ↥X} {y : Perm (Fin n)} (hxy : φ x = y)
    (hy5 : orderOf y = 5)
    (hinv : ∀ t ∈ φ.range, t * t = 1 → t ≠ 1 → t * y * t⁻¹ = y⁻¹) :
    False := by
  classical
  have hXN : X ≤ Subgroup.normalizer (Z : Set G) := hPH.normal
  let ρ : ↥X →* MulAut ↥Z := (CFSG.Quasithin.conjAct Z).comp (Subgroup.inclusion hXN)
  have hρ1 : ∀ u : ↥X, ρ u = 1 ↔ φ u = 1 := by
    intro u
    rw [hφ1]
    change CFSG.Quasithin.conjAct Z (Subgroup.inclusion hXN u) = 1 ↔ _
    rw [conjAct_eq_one_iff']
    exact ⟨fun hc => hPH.mem_core_of_centralizes u.2 hc, fun hc => hPH.core_le_centralizer hc⟩
  have hρcoe : ∀ (u : ↥X) (z : ↥Z), ((ρ u z : ↥Z) : G) = u * z * (u : G)⁻¹ := fun u z =>
    conjAct_coe_apply Z (Subgroup.inclusion hXN u) z
  obtain ⟨A, hA, hAR⟩ := exists_offender hJ
  have hAX : A ≤ X := hA.1.trans hPH.le_self
  obtain ⟨a, haA, haR⟩ : ∃ a ∈ A, a ∉ pCoreOf 2 X := by
    by_contra hcon
    push Not at hcon
    exact hAR hcon
  have hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hA.2.1.1.is_comm.comm (⟨b, hb⟩ : ↥A) ⟨c, hc⟩)
  have hsq : ∀ b ∈ A, b * b = 1 := fun b hb => by simpa [pow_two] using hA.2.1.2 b hb
  set aX : ↥X := ⟨a, hAX haA⟩ with haX
  have hinvA : ∀ b : ↥X, (b : G) ∈ A → φ b ≠ 1 → φ b * y * (φ b)⁻¹ = y⁻¹ := by
    intro b hb hb1
    refine hinv (φ b) ⟨b, rfl⟩ ?_ hb1
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hsq b hb)
    rw [this, map_one]
  have hφa : φ aX ≠ 1 := fun h1 => haR ((hφ1 aX).mp h1)
  have hkey : ∀ b : ↥X, (b : G) ∈ A → φ b = 1 ∨ φ aX * φ b = 1 := by
    intro b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨hb1, hab1⟩ := hcon
    have hab : ((aX * b : ↥X) : G) ∈ A := A.mul_mem haA hb
    have hab1' : φ (aX * b) ≠ 1 := by rw [map_mul]; exact hab1
    have e1 := hinvA aX haA hφa
    have e2 := hinvA b hb hb1
    have e3 := hinvA (aX * b) hab hab1'
    rw [map_mul] at e3
    have : φ aX * φ b * y * (φ aX * φ b)⁻¹ = y := by
      calc φ aX * φ b * y * (φ aX * φ b)⁻¹ = φ aX * (φ b * y * (φ b)⁻¹) * (φ aX)⁻¹ := by group
        _ = φ aX * y⁻¹ * (φ aX)⁻¹ := by rw [e2]
        _ = (φ aX * y * (φ aX)⁻¹)⁻¹ := by group
        _ = y := by rw [e1, inv_inv]
    rw [e3] at this
    have h2 : y ^ 2 = 1 := by
      have : y⁻¹ * y = y * y := by rw [this]
      rw [pow_two]
      simpa using this.symm
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy5] at this
    omega
  have hAidx : (A ⊓ pCoreOf 2 X).relIndex A = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haA⟩, fun b => ?_⟩
    have hbX : (b : G) ∈ X := hAX b.2
    by_cases hbR : (b : G) ∈ pCoreOf 2 X
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨b.2, hbR⟩, fun hba => ?_⟩
      have hba' := (Subgroup.mem_subgroupOf.mp hba).2
      have hba'' : (b : G) * a ∈ pCoreOf 2 X := hba'
      have h5 := (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hbR) hba''
      rw [inv_mul_cancel_left] at h5
      exact haR h5
    · left
      have hb1 : φ ⟨b, hbX⟩ ≠ 1 := fun h1 => hbR ((hφ1 _).mp h1)
      have h1 : φ aX * φ ⟨b, hbX⟩ = 1 := (hkey ⟨b, hbX⟩ b.2).resolve_left hb1
      rw [← map_mul, hφ1] at h1
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨A.mul_mem b.2 haA, ?_⟩, fun hb' => hbR
        (Subgroup.mem_subgroupOf.mp hb').2⟩
      have : (b : G) * a = a * b := hcomm b b.2 a haA
      show (b : G) * a ∈ pCoreOf 2 X
      rw [this]
      exact h1
  let _ : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with
      mul_comm := fun u v => Subtype.ext (by
        have := hPH.elemAbelian.1.is_comm.comm u v
        exact congrArg Subtype.val this) }
  have hZ2 : ∀ v : ↥Z, v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hPH.elemAbelian.2 (v : G) v.2)
  set D : Subgroup ↥Z := (Z ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Z with hD
  have hDidx : D.index ≤ 2 := by
    have h1 := offender_count hPH hA
    rw [hAidx] at h1
    exact h1
  have hρa : ρ aX ≠ 1 := fun h1 => hφa ((hρ1 aX).mp h1)
  have hfix : ∀ v ∈ D, ρ aX v = v := by
    intro v hv
    have hvc : (v : G) ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_subgroupOf.mp hv).2
    refine Subtype.ext ?_
    rw [hρcoe]
    have := Subgroup.mem_centralizer_iff.mp hvc a haA
    calc (aX : G) * v * (aX : G)⁻¹ = (v * a) * a⁻¹ := by rw [haX]; simp [this]
      _ = v := by group
  obtain ⟨w, hw⟩ := exists_transvectionWith (ρ aX) hρa D hDidx hfix
  have hρx1 : ρ x ≠ 1 := by
    intro h1
    have := (hρ1 x).mp h1
    rw [hxy] at this
    rw [this] at hy5
    simp at hy5
  have hρx5 : ρ x ^ 5 = 1 := by
    rw [← map_pow, hρ1, map_pow, hxy]
    have := pow_orderOf_eq_one y
    rwa [hy5] at this
  have hρtx : ρ aX * ρ x * (ρ aX)⁻¹ = (ρ x)⁻¹ := by
    have h1 : ρ (aX * x * aX⁻¹ * x) = 1 := by
      rw [hρ1, map_mul, map_mul, map_mul, map_inv, hxy]
      have e1 := hinvA aX haA hφa
      calc φ aX * y * (φ aX)⁻¹ * y = y⁻¹ * y := by rw [e1]
        _ = 1 := by group
    simp only [map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨-, -, -, hx3⟩ := B1.inverted_by_transvection hZ2 hw hρa (r := 5) (by decide) hρx5 hρx1 hρtx
  apply hρx1
  calc ρ x = (ρ x ^ 3) ^ 2 * (ρ x ^ 5)⁻¹ := by group
    _ = 1 := by rw [hx3, hρx5]; group


end CFSG.Quasithin.F53
