module

public import CFSG.RankThree.PartOne.KE6.Phi6A2
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Classical.SteinbergBYExchangedSL3
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open Matrix
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

section Exchange

variable {Fr : Ω →+* Ω}

theorem exists_sl3_root_permuting_12 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13, θ' g ∈ subsystemGroup Tag.E6 Ω support56,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₂ Ω ⟨θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₁ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot13_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) ∈ subsystemGroup Tag.E6 Ω support56 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot56_mem (π.injective.ne hij) _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      θ' g ∈ subsystemGroup Tag.E6 Ω support56 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support13 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support13 i).1 hi with rfl | rfl
        · rw [← pinnedX_neg_single, ← h10]
          exact hmemθ 1 0 (by decide) c
        · rw [← pinnedX_neg_single, ← h21]
          exact hmemθ 2 1 (by decide) c
    | one =>
      rw [map_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose s' hs' hρ' using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
  choose e he hθe using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t),
          pinnedX_chainRoot13_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ i j hij, ← mul_assoc, CFSG.RankThree.Classical2.sign_mul_self (hs i j hij),
      one_mul]
    rfl
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne (s' (π i) (π j) (π.injective.ne hij) * e i j hij * Fr (s i j hij))
      (s' (π i) (π j) (π.injective.ne hij) * e i j hij * Fr (s i j hij)) (by
        have h1 := hs' (π i) (π j) (π.injective.ne hij)
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, CFSG.RankThree.Classical2.sign_mul_self (hs i j hij), map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mkOfMulEqOne]
  rw [a2Equiv₂_apply, coe_a2Rep₂]
  change a2Mat₂ (θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₂ (θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t))) = _
  rw [hθe i j hij, hρ' (π i) (π j) (π.injective.ne hij), map_mul]
  congr 2
  ring

theorem exists_sl3_root_permuting_21 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π i) (π j)) (e * Fr c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56, θ' g ∈ subsystemGroup Tag.E6 Ω support13,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₁ Ω ⟨θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₂ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot56_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (π.injective.ne hij) _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_neg_single, ← h10]
          exact hmemθ 1 0 (by decide) c
        · rw [← pinnedX_neg_single, ← h21]
          exact hmemθ 2 1 (by decide) c
    | one =>
      rw [map_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
  choose s' hs' hρ' using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose e he hθe using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t),
          pinnedX_chainRoot56_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ i j hij, ← mul_assoc, hs i j hij, one_mul]
    rfl
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s' (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij *
        Fr (s i j hij))
      ((s' (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij * Fr (s i j hij)) (by
        have h1 := CFSG.RankThree.Classical2.sign_mul_self (R := Ω) (hs' (π i) (π j) (π.injective.ne hij))
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, hs i j hij, map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mkOfMulEqOne]
  rw [a2Equiv₁_apply, coe_a2Rep₁]
  change a2Mat₁ (θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t))) = _
  rw [hθe i j hij, hρ' (π i) (π j) (π.injective.ne hij), map_mul]
  congr 2
  ring

end Exchange

theorem exists_sl_conj_map_of_root_permuting [IsAlgClosed Ω] {n : ℕ} (hn : 3 ≤ n)
    (φ : Ω →+* Ω) (π : Equiv.Perm (Fin n)) (Ψ : SL(n, Ω) →* SL(n, Ω))
    (b : Fin n → Fin n → Ωˣ)
    (hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Ψ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * φ t)) :
    ∃ a : SL(n, Ω), ∀ X : SL(n, Ω), Ψ X = a * Matrix.SpecialLinearGroup.map φ X * a⁻¹ := by
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting hn φ π Ψ b hΨ
  obtain ⟨a, ha⟩ := exists_specialLinear_conj_eq (by omega : 1 ≤ n) A
  refine ⟨a, fun X => Subtype.ext ?_⟩
  rw [hA X, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ha]
  rfl

section Layer

variable {Fr : Ω →+* Ω}

theorem exists_exchanged_layer_pos [IsAlgClosed Ω] (hFrs : Function.Surjective Fr)
    (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω) (hinj : Function.Injective θ')
    (π π' : Equiv.Perm (Fin 3))
    (h12 : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c))
    (h21 : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π' i) (π' j)) (e * Fr c)) :
    ∃ θ : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) ≃*
        ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56),
      (∀ g, (θ g : ModGL Tag.E6 Ω) = θ' g) ∧
      ∃ a b : SL(3, Ω), ∀ A B : SL(3, Ω), θ (twoA2MulSup (A, B)) =
        twoA2MulSup (a * Matrix.SpecialLinearGroup.map Fr B * a⁻¹, b * Matrix.SpecialLinearGroup.map Fr A * b⁻¹) := by
  obtain ⟨hQ12, b₁₂, hb₁₂⟩ := exists_sl3_root_permuting_12 θ' π h12
  obtain ⟨hQ21, b₂₁, hb₂₁⟩ := exists_sl3_root_permuting_21 θ' π' h21
  let θ12 : subsystemGroup Tag.E6 Ω support13 →* subsystemGroup Tag.E6 Ω support56 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ12 g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  let θ21 : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support13 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ21 g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  let N₁₂ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₂ Ω).toMonoidHom.comp (θ12.comp (a2Equiv₁ Ω).symm.toMonoidHom)
  let N₂₁ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₁ Ω).toMonoidHom.comp (θ21.comp (a2Equiv₂ Ω).symm.toMonoidHom)
  obtain ⟨b, hb⟩ := exists_sl_conj_map_of_root_permuting (le_refl 3) Fr π N₁₂ b₁₂ hb₁₂
  obtain ⟨a, ha⟩ := exists_sl_conj_map_of_root_permuting (le_refl 3) Fr π' N₂₁ b₂₁ hb₂₁
  have hθ12 : ∀ A : SL(3, Ω), θ' ((a2Equiv₁ Ω).symm A) = (a2Equiv₂ Ω).symm (N₁₂ A) := fun A => by
    change θ' _ = ((a2Equiv₂ Ω).symm (a2Equiv₂ Ω (θ12 ((a2Equiv₁ Ω).symm A))) : ModGL Tag.E6 Ω)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hθ21 : ∀ B : SL(3, Ω), θ' ((a2Equiv₂ Ω).symm B) = (a2Equiv₁ Ω).symm (N₂₁ B) := fun B => by
    change θ' _ = ((a2Equiv₁ Ω).symm (a2Equiv₁ Ω (θ21 ((a2Equiv₂ Ω).symm B))) : ModGL Tag.E6 Ω)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
    have hle : subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ≤
        (subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56).comap θ' :=
      sup_le (fun g hg => Subgroup.mem_sup_right (hQ12 g hg))
        (fun g hg => Subgroup.mem_sup_left (hQ21 g hg))
    exact fun g hg => hle hg
  let θ₀ : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  have hNsurj : ∀ (N : SL(3, Ω) →* SL(3, Ω)) (σ₀ : Equiv.Perm (Fin 3)) (c : Fin 3 → Fin 3 → Ωˣ),
      (∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((N (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) = 1 + single (σ₀ i) (σ₀ j) ((c i j : Ω) * Fr t)) →
      Function.Surjective N := by
    intro N σ₀ c hN
    rw [← MonoidHom.range_eq_top]
    have hmem : ∀ (k l : Fin 3) (hkl : k ≠ l) (t : Ω),
        Matrix.SpecialLinearGroup.transvection hkl t ∈ N.range := by
      intro k l hkl t
      have hij : σ₀.symm k ≠ σ₀.symm l := σ₀.symm.injective.ne hkl
      obtain ⟨t', ht'⟩ := hFrs ((c (σ₀.symm k) (σ₀.symm l))⁻¹ * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t', Subtype.ext ?_⟩
      rw [hN, ht', Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rfl
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  have hN₁₂s := hNsurj N₁₂ π b₁₂ hb₁₂
  have hN₂₁s := hNsurj N₂₁ π' b₂₁ hb₂₁
  have hθ₀bij : Function.Bijective θ₀ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), ?_⟩
    intro y
    obtain ⟨⟨A, B⟩, rfl⟩ := twoA2MulSup_surjective y
    obtain ⟨A', hA'⟩ := hN₂₁s A
    obtain ⟨B', hB'⟩ := hN₁₂s B
    refine ⟨twoA2MulSup (B', A'), Subtype.ext ?_⟩
    change θ' (((a2Equiv₁ Ω).symm B' : ModGL Tag.E6 Ω) * (a2Equiv₂ Ω).symm A') = _
    rw [map_mul, hθ12, hθ21, hA', hB', coe_twoA2MulSup]
    exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm A).2 ((a2Equiv₂ Ω).symm B).2).eq.symm
  refine ⟨MulEquiv.ofBijective θ₀ hθ₀bij, fun g => rfl, a, b, fun A B => Subtype.ext ?_⟩
  change θ' (((a2Equiv₁ Ω).symm A : ModGL Tag.E6 Ω) * (a2Equiv₂ Ω).symm B) = _
  rw [map_mul, hθ12, hθ21, coe_twoA2MulSup, ← ha, ← hb]
  exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm (N₂₁ B)).2 ((a2Equiv₂ Ω).symm (N₁₂ A)).2).eq.symm

end Layer

end CFSG.RankThree.PartOne.KE6
