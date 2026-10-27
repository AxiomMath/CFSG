module

public import CFSG.RankThree.PartTwo.KFacts.K74Stabilizer
public import CFSG.RankThree.PartTwo.Sec12.Item124
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def colMat (w : Fin 3 → ZMod 3) : Mat33 :=
  if w 0 ≠ 0 then !![w 0, 0, 0; w 1, 1, 0; w 2, 0, 1]
  else if w 1 ≠ 0 then !![w 0, 1, 0; w 1, 0, 0; w 2, 0, 1]
  else !![w 0, 1, 0; w 1, 0, 1; w 2, 0, 0]

@[expose] def colMatInv (w : Fin 3 → ZMod 3) : Mat33 :=
  if w 0 ≠ 0 then !![w 0, 0, 0; -(w 0 * w 1), 1, 0; -(w 0 * w 2), 0, 1]
  else if w 1 ≠ 0 then !![0, w 1, 0; 1, -(w 1 * w 0), 0; 0, -(w 1 * w 2), 1]
  else !![0, 0, w 2; 1, 0, -(w 2 * w 0); 0, 1, -(w 2 * w 1)]

theorem colMat_facts : ∀ w : Fin 3 → ZMod 3, w ≠ 0 →
    colMat w * colMatInv w = 1 ∧ colMatInv w * colMat w = 1 ∧
      colMat w 0 0 = w 0 ∧ colMat w 1 0 = w 1 ∧ colMat w 2 0 = w 2 := by
  decide +kernel

theorem exists_basis_zero_eq [FiniteDimensional (ZMod 3) V] (hV : finrank (ZMod 3) V = 3)
    {u : V} (hu : u ≠ 0) : ∃ b : Basis (Fin 3) (ZMod 3) V, b 0 = u := by
  set b' := Module.finBasisOfFinrankEq (ZMod 3) V hV
  set w : Fin 3 → ZMod 3 := fun i => b'.repr u i with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hu
    have : b'.repr u = 0 := by
      ext i
      exact congrFun h i
    simpa using this
  obtain ⟨h1, h2, h00, h10, h20⟩ := colMat_facts w hw0
  refine ⟨b'.map (ofMat b' h1 h2), ?_⟩
  rw [Basis.map_apply]
  change Matrix.toLin b' b' (colMat w) (b' 0) = u
  rw [Matrix.toLin_self, Fin.sum_univ_three, h00, h10, h20]
  conv_rhs => rw [← b'.sum_repr u, Fin.sum_univ_three]

section Coords

variable {G : Type} [Group G] {A : Subgroup G}

theorem irreducible_coordHom (f : Multiplicative V ≃* A) {S : Subgroup (MulAut A)}
    (hS : Sec21.IsIrreducibleOn S) :
    ∀ W : Submodule (ZMod 3) V, (∀ g ∈ S.map (Sec12.coordHom f), ∀ x ∈ W, g x ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  set B : Subgroup A := (AddSubgroup.toSubgroup W.toAddSubgroup).map f.toMonoidHom with hB
  have hmem : ∀ v : V, f (Multiplicative.ofAdd v) ∈ B ↔ v ∈ W := by
    intro v
    constructor
    · rintro ⟨y, hy, hyv⟩
      have : y = Multiplicative.ofAdd v := f.injective hyv
      rw [this] at hy
      exact hy
    · intro hv
      exact ⟨Multiplicative.ofAdd v, hv, rfl⟩
  have hfa : ∀ a : A, f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm a))) = a := by
    intro a
    simp
  have hinv : ∀ φ ∈ S, ∀ a ∈ B, φ a ∈ B := by
    intro φ hφ a ha
    rw [← hfa a] at ha ⊢
    rw [hmem] at ha
    have h := hW _ ⟨φ, hφ, rfl⟩ _ ha
    rw [Sec12.coordHom_apply] at h
    rw [← hmem] at h
    simpa using h
  have hBinv : ∀ φ ∈ S, B.map φ.toMonoidHom = B := by
    intro φ hφ
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact hinv φ hφ a ha
    · intro a ha
      refine ⟨φ⁻¹ a, hinv φ⁻¹ (S.inv_mem hφ) a ha, ?_⟩
      simp
  rcases hS B hBinv with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [← hmem, h, Subgroup.mem_bot] at hv
    rw [Submodule.mem_bot]
    have : Multiplicative.ofAdd v = 1 := f.injective (hv.trans (map_one f).symm)
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hmem, h]
    exact Subgroup.mem_top _

theorem coordHom_coordVec (f : Multiplicative V ≃* A) (σ : MulAut A) (c : A) :
    Sec12.coordHom f σ (Sec12.coordVec f c) = Sec12.coordVec f (σ c) := by
  simp [Sec12.coordHom_apply, Sec12.coordVec]

theorem false_of_irreducible_of_normal_three [Finite A] (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {S : Subgroup (MulAut A)} (hirr : Sec21.IsIrreducibleOn S)
    {d : A} (hd : d ≠ 1) {r : MulAut A} (hrS : r ∈ S) (hr : r ∈ Sec12.transvectionGroup A d)
    (hr1 : r ≠ 1) {c : A} (hc : c ≠ 1) {N : Subgroup (MulAut A)} (hN3 : Nat.card N = 3)
    (hNfix : ∀ n ∈ N, n c ∈ Subgroup.zpowers c)
    (hnorm : ∀ σ ∈ S, σ c = c → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) : False := by
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := Sec12.exists_coords_module hA (n := 3) (by rw [h27]; norm_num)
  have : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_eq_succ hV
  set G' := S.map (Sec12.coordHom f) with hG'
  have hirr' := irreducible_coordHom f hirr
  obtain ⟨⟨v, φ, hvφ⟩, -⟩ := Sec12.coordHom_isTransvection f hd hr hr1
  have hSL := Sec3.det_eq_one_mem_of_irreducible hV G' hirr' ⟨r, hrS, rfl⟩ hvφ
  obtain ⟨b, hb⟩ := exists_basis_zero_eq hV (Sec12.coordVec_ne_zero f hc)
  have hinj := Sec12.coordHom_injective f
  refine false_of_normal_card_three b (G := G') (N := N.map (Sec12.coordHom f)) hSL
    (by rw [Subgroup.card_map_of_injective hinj, hN3]) ?_ ?_
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hNfix n hn)
    refine ⟨(k : ZMod 3), ?_⟩
    rw [hb, coordHom_coordVec, ← hk, Sec12.coordVec, Sec12.coordVec, map_zpow, toAdd_zpow,
      Int.cast_smul_eq_zsmul]
  · rintro _ ⟨σ, hσ, rfl⟩ hσb _ ⟨n, hn, rfl⟩
    have hσc : σ c = c := by
      rw [hb, coordHom_coordVec] at hσb
      have h := congrArg (fun w => f (Multiplicative.ofAdd w)) hσb
      simpa [Sec12.coordVec] using h
    exact ⟨σ * n * σ⁻¹, hnorm σ hσ hσc n hn, by simp⟩

end Coords

end CFSG.RankThree.PartTwo.KFacts
