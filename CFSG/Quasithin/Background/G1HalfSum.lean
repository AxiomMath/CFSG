module

public import CFSG.Quasithin.Background.G1Half
public import CFSG.Quasithin.Background.G2SL2
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F]

theorem Rij_zero_one_eq_Rg : Rij F (0 : Fin 2) 1 = Rg F := by
  ext t
  show t ∈ rootGroup (Vi F 2 0) (Vhat F 2 1) ↔ t ∈ Rg F
  rw [mem_Rij_iff (zero_ne_one : (0 : Fin 2) ≠ 1), mem_Rg]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, (transvection_zero_one b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, (transvection_zero_one b).symm⟩

theorem lower_left_eq_zero_of_actSub {k : SL(2, F)} (hk : actSub k (Vi F 2 0) = Vi F 2 0) :
    k.1 1 0 = 0 := by
  have h1 : k • (Pi.single 0 1 : Fin 2 → F) ∈ actSub k (Vi F 2 0) :=
    mem_actSub.2 ⟨Pi.single 0 1, Submodule.mem_span_singleton_self _, rfl⟩
  rw [hk] at h1
  have h2 := mem_Vi.1 h1 1 (by decide)
  have h3 : (k • (Pi.single 0 1 : Fin 2 → F)) 1 = k.1 1 0 := by
    show ((k : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single 0 1 : Fin 2 → F)) 1 = _
    simp
  rw [← h3]
  exact h2

section Sum

variable [Finite F] [CharP F 2] {U : Type} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U]

theorem exists_equiv_of_halves (hG13 : Theorem_G_1_3 F 2 (le_refl 2))
    (hsq : ∀ u : U, u + u = 0) (Y : AddSubgroup U) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hg : g.1 1 0 ≠ 0)
    (hinv : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, k.1 1 0 = 0 → ∀ y ∈ Y, k • y ∈ Y)
    (hcomm : ∀ t ∈ Rg F, ∀ u : U, t • u - u ∈ Y)
    (hfix : ∀ t ∈ Rg F, ∀ y ∈ Y, t • y = y)
    (hdisj : Y ⊓ Y.map (actU g) = ⊥) (hsup : Y ⊔ Y.map (actU g) = ⊤) :
    ∃ (s : ℕ) (Θ : (Fin s → Fin 2 → F) ≃+ U),
      (∀ (k : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin s → Fin 2 → F),
        Θ (fun j => k • x j) = k • Θ x) ∧
      Nat.card Y = Nat.card F ^ s ∧ ∀ u : U, (∀ t ∈ Rg F, t • u = u) → u ∈ Y := by
  have hinv' : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, actSub k (Vi F 2 0) = Vi F 2 0 →
      ∀ y ∈ Y, k • y ∈ Y :=
    fun k hk y hy => hinv k (lower_left_eq_zero_of_actSub hk) y hy
  have hcomm' : commU (Rij F (0 : Fin 2) 1) ≤ Y := by
    refine AddSubgroup.closure_le _ |>.2 ?_
    rintro w ⟨t, ht, u, rfl⟩
    exact hcomm t (Rij_zero_one_eq_Rg (F := F) ▸ ht) u
  have hfix' : Y ≤ fixU (Rij F (0 : Fin 2) 1) := fun y hy t ht =>
    hfix t (Rij_zero_one_eq_Rg (F := F) ▸ ht) y hy
  obtain ⟨φ, hφ, hφ0⟩ := exists_G13Hyp_of_halves Y g hinv' hcomm' hfix' hdisj hsup
  obtain ⟨s, hs, W, hind, hsupW, hW⟩ := hG13 U hsq φ hφ
  have hφ0' : φ (Vi F 2 ⟨0, by omega⟩) = Y := hφ0
  rw [hφ0'] at hs
  choose hstab f hfinj hfrange hfeq using hW
  let Θ₀ : (Fin s → Fin 2 → F) →+ U :=
    ∑ j : Fin s, (f j).comp (Pi.evalAddMonoidHom (fun _ : Fin s => Fin 2 → F) j)
  have hΘ₀ : ∀ x, Θ₀ x = ∑ j, f j (x j) := fun x => by simp [Θ₀]
  have hinj : Function.Injective Θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    have h1 : f i (x i) ∈ W i := by
      rw [← hfrange i]
      exact ⟨x i, rfl⟩
    have h2 : f i (x i) ∈ ⨆ (j) (_ : j ≠ i), W j := by
      have e : f i (x i) = -∑ j ∈ Finset.univ.erase i, f j (x j) := by
        have h0 := Finset.add_sum_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)
        rw [hΘ₀] at hx
        rw [hx] at h0
        exact eq_neg_of_add_eq_zero_left h0
      rw [e]
      refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjW : f j (x j) ∈ W j := by
        rw [← hfrange j]
        exact ⟨x j, rfl⟩
      exact AddSubgroup.mem_iSup_of_mem j (AddSubgroup.mem_iSup_of_mem hji hjW)
    have h3 : f i (x i) ∈ (⊥ : AddSubgroup U) := (hind i).le_bot ⟨h1, h2⟩
    have h4 : f i (x i) = 0 := AddSubgroup.mem_bot.1 h3
    have h5 : x i = 0 := hfinj i (by rw [h4, map_zero])
    simpa using h5
  have hsurj : Function.Surjective Θ₀ := by
    intro u
    have hle : (⊤ : AddSubgroup U) ≤ Θ₀.range := by
      rw [← hsupW]
      refine iSup_le fun j => ?_
      rw [← hfrange j]
      rintro _ ⟨x, rfl⟩
      refine ⟨Pi.single j x, ?_⟩
      rw [hΘ₀]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · intro h
        exact absurd (Finset.mem_univ j) h
    exact hle (AddSubgroup.mem_top u)
  have hequiv : ∀ (k : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin s → Fin 2 → F),
      Θ₀ (fun j => k • x j) = k • Θ₀ x := by
    intro k x
    rw [hΘ₀, hΘ₀, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => hfeq j k (x j)
  have hC : ∀ u : U, (∀ t ∈ Rg F, t • u = u) → u ∈ Y := by
    intro u hu
    have hu' : u ∈ Y ⊔ Y.map (actU g) := by
      rw [hsup]
      exact AddSubgroup.mem_top u
    obtain ⟨y, hy, y', hy', rfl⟩ := AddSubgroup.mem_sup.1 hu'
    obtain ⟨y'', hy'', rfl⟩ := hy'
    have hR1 : ∀ t ∈ Rg F, t • (actU g y'') = actU g y'' := by
      intro t ht
      have h1 := hu t ht
      have h2 := hfix t ht y hy
      rw [smul_add, h2] at h1
      exact add_left_cancel h1
    have hstab : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, k • y'' = y'' := by
      intro k
      have hk : k ∈ Rg F ⊔ (Rg F).map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [Rg_sup_conj_eq_top g hg]
        exact Subgroup.mem_top k
      have hle : Rg F ⊔ (Rg F).map (MulAut.conj g⁻¹).toMonoidHom ≤
          MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) F) y'' := by
        refine sup_le (fun t ht => hfix t ht y'' hy'') ?_
        rintro _ ⟨t, ht, rfl⟩
        have h3 := hR1 t ht
        show (g⁻¹ * t * g⁻¹⁻¹) • y'' = y''
        rw [inv_inv, mul_smul, mul_smul]
        have h4 : t • g • y'' = g • y'' := h3
        rw [h4, inv_smul_smul]
      exact hle hk
    have h0 : actU g y'' = y'' := hstab g
    have hmem : actU g y'' ∈ Y ⊓ Y.map (actU g) :=
      ⟨by rw [h0]; exact hy'', ⟨y'', hy'', rfl⟩⟩
    rw [hdisj] at hmem
    have h5 : actU g y'' = 0 := AddSubgroup.mem_bot.1 hmem
    rw [h5, add_zero]
    exact hy
  exact ⟨s, AddEquiv.ofBijective Θ₀ ⟨hinj, hsurj⟩, hequiv, hs, hC⟩

end Sum

end CFSG.Quasithin.G1
