module

public import CFSG.Quasithin.H13.A6S1372L76Of2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Og

open A6L76Of

theorem cocyc_inv {W : Type*} [CommGroup W] {Γ : Type*} [Group Γ] {M : Type*} [CommGroup M]
    {Y : Subgroup (MulAut W)} (π : Γ →* ↥Y) (β : ↥(commV Y) →* M) (v : W) (γ : Γ) :
    cocyc π β v⁻¹ γ = (cocyc π β v γ)⁻¹ := by
  have h := cocyc_mul_left π β v v⁻¹ γ
  rw [mul_inv_cancel, cocyc_eq_one_of_fix π β (map_one _)] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem exists_fix_line {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn2 : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥Y}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ g : ↥(StatedSL 3 F), ∀ γ : ↥(StatedSL 3 F),
      (∀ x : Fin 3 → F, x 1 = 0 → x 2 = 0 →
        natHom (g * γ * g⁻¹) (Multiplicative.ofAdd x) = Multiplicative.ofAdd x) →
      ((π γ : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((π γ : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := A6L76Z.natRealizes_clean hπ
  have hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u) :=
    fun γ u hu => hβe0 γ u hu
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hβk' : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y := fun u hu => ((hβk u).1 hu).1
  have : Finite ↥Y := Finite.of_surjective π hs
  have haY' := inv_conj_mem haY
  set P' : Subgroup ↥(StatedSL 3 F) := (P.subgroupOf Y).comap π with hP'
  have hP'2 : IsPGroup 2 ↥P' :=
    (hP2.comap_of_injective Y.subtype Y.subtype_injective).comap_of_injective π hinj
  have hP'odd : Odd P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hs]
    exact hPodd
  have h2 : ∀ m : Multiplicative (Fin 3 → F), m * m = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  obtain ⟨m₁, hm₁⟩ := exists_coboundary_of_odd_index h2 natHom (f := cocyc π β v₂)
    (fun g h => cocyc_mul hβe v₂ g h) hP'odd
    (fun δ hδ => cocyc_eq_one_of_fix π β (hPv _ hδ))
  have hm₁P : ∀ δ ∈ P', natHom δ m₁ = m₁ := by
    intro δ hδ
    have h := hm₁ δ
    rw [cocyc_eq_one_of_fix π β (hPv _ hδ)] at h
    exact mul_inv_eq_one.1 h.symm
  have hm₁1 : m₁ ≠ 1 := by
    intro h1
    apply hv
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun γ => ?_
    rw [hm₁, h1, map_one, mul_inv_cancel]
  obtain ⟨f, hf⟩ := exists_lift hβs hβk haY haY'
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = f m₁ := ⟨_, rfl⟩
  have hcoc₂ : ∀ γ, cocyc π β (a v₂) γ = natHom γ m₂ * m₂⁻¹ := by
    rw [hm₂]
    exact cocyc_lift hβe hs hβs haY haY' hf hm₁
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_stated hP'2 (fun h => by
    obtain ⟨k, hk⟩ := hP'odd
    omega)
  have hgU : ∀ u : Matrix.SpecialLinearGroup (Fin 3) F,
      specialLinearGroupEquivStatedSL 3 F u * g =
        g * (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) := fun u => by group
  obtain ⟨x₁, hx₁⟩ : ∃ x, Multiplicative.toAdd (natHom g m₁) = x := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, Multiplicative.toAdd (natHom g m₂) = x := ⟨_, rfl⟩
  have hx₁fix : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₁ = x₁ := by
    intro u hu
    have h3 : natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₁) = natHom g m₁ := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply, hm₁P _ (hg u hu)]
    have h4 := congrArg Multiplicative.toAdd h3
    rw [natHom_apply (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₁), hx₁] at h4
    exact h4
  obtain ⟨hx₁1, hx₁2⟩ := unitriangular_fix hx₁fix
  have hx₁0 : x₁ ≠ 0 := by
    intro h0
    apply hm₁1
    rw [← hx₁, toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h0
    exact h0
  have hx₂mov : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₂ - x₂ = 0 ∨
      (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₂ - x₂ = x₁ := by
    intro u hu
    have hsP : ((π (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) : ↥Y) : MulAut W) ∈ P :=
      hg u hu
    have hcs : ∀ γ, cocyc π β (((π (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) : ↥Y) :
        MulAut W) (a v₂)) γ =
        natHom γ (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂) *
          (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂)⁻¹ := by
      intro γ
      rw [cocyc_conj hβe, hcoc₂, map_mul, map_inv, natHom_conj]
    have hb1 : natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂) =
        natHom g (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂) := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply]
    rcases hPa _ hsP with h | h
    · left
      have h3 : natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂ = m₂ := by
        refine eq_of_natCoboundary_eq fun γ => ?_
        rw [← hcs, h, hcoc₂]
      rw [← hx₂]
      show Multiplicative.toAdd (natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂)) -
        Multiplicative.toAdd (natHom g m₂) = 0
      rw [hb1, h3, sub_self]
    · right
      have h3 : natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂ = m₁ * m₂ := by
        refine eq_of_natCoboundary_eq fun γ => ?_
        rw [← hcs, h, cocyc_mul_left, hm₁, hcoc₂, map_mul, mul_inv_rev]
        ac_rfl
      rw [← hx₂, ← hx₁]
      show Multiplicative.toAdd (natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂)) -
        Multiplicative.toAdd (natHom g m₂) = Multiplicative.toAdd (natHom g m₁)
      rw [hb1, h3, map_mul, toAdd_mul, add_sub_cancel_right]
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hx₂1, hx₂2⟩ := unitriangular_comm hq hx₁0 ⟨hx₁1, hx₁2⟩ hx₂mov
  refine ⟨g, fun γ hγ => ?_⟩
  have hg1 : ∀ m : Multiplicative (Fin 3 → F), Multiplicative.toAdd (natHom g m) 1 = 0 →
      Multiplicative.toAdd (natHom g m) 2 = 0 → natHom γ m = m := by
    intro m h1 h2
    have h3 := hγ _ h1 h2
    rw [ofAdd_toAdd] at h3
    have h4 : natHom (g * γ * g⁻¹) (natHom g m) = natHom g (natHom γ m) := by
      rw [← MulAut.mul_apply, ← map_mul, show g * γ * g⁻¹ * g = g * γ by group, map_mul,
        MulAut.mul_apply]
    rw [h4] at h3
    exact (natHom g).injective h3
  have hγm₁ : natHom γ m₁ = m₁ := hg1 m₁ (by rw [hx₁]; exact hx₁1) (by rw [hx₁]; exact hx₁2)
  have hγm₂ : natHom γ m₂ = m₂ := hg1 m₂ (by rw [hx₂]; exact hx₂1) (by rw [hx₂]; exact hx₂2)
  have hfix : ∀ (v : W) (m : Multiplicative (Fin 3 → F)),
      (∀ δ, cocyc π β v δ = natHom δ m * m⁻¹) → natHom γ m = m →
        ((π γ : ↥Y) : MulAut W) v * v⁻¹ ∈ fixV Y := by
    intro v m hv' hm
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun δ => ?_
    rw [cocyc_mul_left, cocyc_inv, cocyc_conj hβe, hv', hv', map_mul, map_inv, natHom_conj, hm,
      mul_inv_cancel]
  exact ⟨hfix v₂ m₁ hm₁ hγm₁, hfix (a v₂) m₂ hcoc₂ hγm₂⟩

section Levi

variable {F : Type} [Field F]

@[expose] def leviMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem det_leviMat (A : Matrix (Fin 2) (Fin 2) F) : (leviMat A).det = A.det := by
  rw [leviMat, Matrix.det_fin_three, Matrix.det_fin_two]
  simp

theorem leviMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    leviMat A * leviMat B = leviMat (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

@[expose] def leviHom :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨leviMat (A : Matrix (Fin 2) (Fin 2) F), by rw [det_leviMat, A.2]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat]
  map_mul' A B := by
    ext i j
    show leviMat ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (leviMat (A : Matrix (Fin 2) (Fin 2) F) * leviMat (B : Matrix (Fin 2) (Fin 2) F)) i j
    rw [leviMat_mul]
    rfl

theorem leviHom_injective : Function.Injective (leviHom (F := F)) := by
  intro A B h
  have h1 : leviMat (A : Matrix (Fin 2) (Fin 2) F) = leviMat (B : Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun C : Matrix.SpecialLinearGroup (Fin 3) F => (C : Matrix (Fin 3) (Fin 3) F)) h
  ext i j
  have h2 := congrFun (congrFun h1 (i.succ)) (j.succ)
  fin_cases i <;> fin_cases j <;> simpa [leviMat] using h2

theorem leviMat_mulVec {A : Matrix (Fin 2) (Fin 2) F} {x : Fin 3 → F} (h1 : x 1 = 0)
    (h2 : x 2 = 0) : leviMat A *ᵥ x = x := by
  funext i
  fin_cases i <;> simp [leviMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

end Levi

end A6L76Og

end CFSG.Quasithin.H13.A6
