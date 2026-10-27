module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSULift
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSUGeom

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.BorelTits CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Matrix

private noncomputable abbrev rckFlagSU_sigma (g : ℕ) :
    GaloisField 2 (2 * g) ≃+* GaloisField 2 (2 * g) :=
  unitaryInvolution (GaloisField 2 (2 * g)) 2 g

private abbrev rckFlagSU_K (g : ℕ) : Type := GaloisField 2 (2 * g)

private theorem rckFlagSU_fieldData (g : ℕ) (hg : 1 ≤ g) :
    UnitaryFieldData 2 g (GaloisField 2 (2 * g)) := by
  refine ⟨Nat.prime_two, hg, ?_⟩
  exact GaloisField.card 2 (2 * g) (by omega)

private theorem rckFlagSU_bar_apply (g : ℕ) (hg : 1 ≤ g) (c : GaloisField 2 (2 * g)) :
    (rckFlagSU_fieldData g hg).bar c = rckFlagSU_sigma g c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

private theorem rckFlagSU_card (g : ℕ) (hg : 1 ≤ g) :
    Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 := by
  rw [(rckFlagSU_fieldData g hg).card, ← pow_mul, Nat.mul_comm 2 g]

private theorem rckFlagSU_antidiag_mulVec (n g : ℕ) (y : Fin n → GaloisField 2 (2 * g)) :
    (antidiag n).mulVec y = fun i => y (Fin.rev i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, antidiag, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

private theorem rckFlagSU_suHerm_expand (n g : ℕ)
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x y = ∑ i, rckFlagSU_sigma g (x i) * y (Fin.rev i) := by
  rw [suHerm, dotProduct, rckFlagSU_antidiag_mulVec]

private theorem rckFlagSU_suHerm_add_left (n g : ℕ)
    (x x' y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g (x + x') y = suHerm n g x y + suHerm n g x' y := by
  simp only [suHerm, Pi.add_apply, map_add, dotProduct, add_mul, Finset.sum_add_distrib]

private theorem rckFlagSU_suHerm_smul_left (n g : ℕ) (c : GaloisField 2 (2 * g))
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g (c • x) y = rckFlagSU_sigma g c * suHerm n g x y := by
  simp only [suHerm, Pi.smul_apply, smul_eq_mul, map_mul, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem rckFlagSU_suHerm_add_right (n g : ℕ)
    (x y y' : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x (y + y') = suHerm n g x y + suHerm n g x y' := by
  simp only [suHerm, Matrix.mulVec_add, dotProduct, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

private theorem rckFlagSU_suHerm_smul_right (n g : ℕ) (c : GaloisField 2 (2 * g))
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x (c • y) = c * suHerm n g x y := by
  simp only [suHerm, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem rckFlagSU_suHerm_symm (n g : ℕ) (hg : 1 ≤ g)
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g y x = rckFlagSU_sigma g (suHerm n g x y) := by
  rw [rckFlagSU_suHerm_expand, rckFlagSU_suHerm_expand, map_sum]
  simp only [map_mul, unitaryInvolution_involutive (rckFlagSU_card g hg)]
  rw [← Equiv.sum_comp Fin.revPerm (fun i => rckFlagSU_sigma g (y i) * x (Fin.rev i))]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem rckFlagSU_suHerm_sep (n g : ℕ)
    {x : Fin n → GaloisField 2 (2 * g)} (h : ∀ y, suHerm n g x y = 0) : x = 0 := by
  funext i
  let e : Fin n → GaloisField 2 (2 * g) := Pi.single (Fin.rev i) 1
  have hx := h e
  rw [rckFlagSU_suHerm_expand] at hx
  have hsum : (∑ k, rckFlagSU_sigma g (x k) * e (Fin.rev k)) =
      rckFlagSU_sigma g (x i) := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro k _ hk
      have hkr : Fin.rev k ≠ Fin.rev i := fun hh => hk (Fin.rev_injective hh)
      simp [e, hkr]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  rw [hsum] at hx
  exact (map_eq_zero_iff _ (rckFlagSU_sigma g).injective).mp hx

private theorem rckFlagSU_map_mulVec (n g : ℕ)
    (A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)))
    (x : Fin n → GaloisField 2 (2 * g)) :
    (fun i => rckFlagSU_sigma g ((A *ᵥ x) i)) =
      (A.map (rckFlagSU_sigma g)) *ᵥ (fun i => rckFlagSU_sigma g (x i)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private theorem rckFlagSU_dotProduct_mulVec (n g : ℕ)
    (M : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)))
    (u v : Fin n → GaloisField 2 (2 * g)) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

private theorem rckFlagSU_suHerm_isometry (n g : ℕ)
    (A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)))
    (hA : conjTr (rckFlagSU_sigma g) A * antidiag n * A = antidiag n)
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g (A *ᵥ x) (A *ᵥ y) = suHerm n g x y := by
  rw [suHerm, suHerm, rckFlagSU_map_mulVec, rckFlagSU_dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [show (A.map (rckFlagSU_sigma g))ᵀ * antidiag n * A = antidiag n from hA]

private theorem rckFlagSU_irredW_aux (n g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype none := by
  classical
  intro R' W H hWH hv _hB r hr hr1 P hPW hPinv
  by_cases hdim : Module.finrank (rckFlagSU_K g) W ≤ 1
  · have hPle : Module.finrank (rckFlagSU_K g) P ≤ Module.finrank (rckFlagSU_K g) W :=
      Submodule.finrank_mono hPW
    have hP1 : Module.finrank (rckFlagSU_K g) P ≤ 1 := le_trans hPle hdim
    have hcases : Module.finrank (rckFlagSU_K g) P = 0 ∨
        Module.finrank (rckFlagSU_K g) P = 1 := by omega
    rcases hcases with h0 | h1
    · exact Or.inl ((Submodule.finrank_eq_zero).mp h0)
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hPW (by
        have hW1 : Module.finrank (rckFlagSU_K g) W = 1 := by omega
        rw [h1, hW1]))
  · push Not at hdim
    let P' : Submodule (rckFlagSU_K g) ↥W := P.comap W.subtype
    have hP'mem : ∀ y : ↥W, y ∈ P' ↔ (y : Fin n → rckFlagSU_K g) ∈ P :=
      fun y => Submodule.mem_comap
    have hmapP : P'.map W.subtype = P := by
      have h := Submodule.map_comap_subtype (p := W) (p' := P)
      rw [inf_eq_right.mpr hPW] at h
      exact h
    let Ar : Matrix (Fin n) (Fin n) (rckFlagSU_K g) :=
      ((r : GL (Fin n) (rckFlagSU_K g)) : Matrix (Fin n) (Fin n) (rckFlagSU_K g))
    let N : (Fin n → rckFlagSU_K g) →ₗ[rckFlagSU_K g] (Fin n → rckFlagSU_K g) :=
      Matrix.toLin' (Ar - 1)
    have hNr : N.range = W := by
      simpa only [N, Ar, Subgroup.subtype_apply] using (hv r hr hr1).1
    have hNk : N.ker = H := by
      simpa only [N, Ar, Subgroup.subtype_apply] using (hv r hr hr1).2
    have hA : Unitary.conjTr (rckFlagSU_sigma g) Ar * Unitary.antidiag n * Ar =
        Unitary.antidiag n := by
      have h := (Unitary.mem_SU (σ := rckFlagSU_sigma g) (n := n)
        (A := (r : GL (Fin n) (rckFlagSU_K g)))).mp r.2
      simpa only [Ar] using h.2
    have hpres : ∀ x y, suHerm n g (Ar.mulVec x) (Ar.mulVec y) = suHerm n g x y :=
      fun x y => rckFlagSU_suHerm_isometry n g Ar hA x y
    have hNr_apply : ∀ x, Ar.mulVec x = N x + x := by
      have hAr : Matrix.toLin' Ar = N + 1 := by
        have h : Matrix.toLin' Ar - 1 = N := by
          dsimp only [N]
          rw [map_sub, Matrix.toLin'_one]
          rfl
        exact sub_eq_iff_eq_add.mp h
      intro x
      have h := congrArg (fun L : (Fin n → rckFlagSU_K g) →ₗ[rckFlagSU_K g]
        (Fin n → rckFlagSU_K g) => L x) hAr
      simpa using h
    have hNw : ∀ w ∈ W, N w = 0 := by
      intro w hw
      have hwH : w ∈ N.ker := by rw [hNk]; exact hWH hw
      simpa using hwH
    have hNN : N * N = 0 := by
      apply LinearMap.ext
      intro x
      have hx : N x ∈ N.ker := by
        rw [hNk]
        exact hWH (by rw [← hNr]; exact LinearMap.mem_range_self N x)
      show N (N x) = 0
      exact hx
    have hU1 : ∀ w ∈ W, ∀ y, suHerm n g w (N y) = 0 := by
      intro w hw y
      have h := hpres w y
      rw [show Ar.mulVec w = w by rw [hNr_apply w, hNw w hw, zero_add],
        hNr_apply y, rckFlagSU_suHerm_add_right] at h
      have h2 : suHerm n g w (N y) + suHerm n g w y = 0 + suHerm n g w y := by
        simpa using h
      exact add_right_cancel h2
    have hWW : ∀ w ∈ W, ∀ w' ∈ W, suHerm n g w w' = 0 := by
      intro w hw w' hw'
      obtain ⟨z, hz⟩ := (show w' ∈ N.range by rw [hNr]; exact hw')
      rw [← hz]
      exact hU1 w hw z
    have hTot : ∀ x y, suHerm n g (N x) (N y) = 0 := by
      intro x y
      exact hU1 (N x) (by rw [← hNr]; exact LinearMap.mem_range_self N x) y
    have hU2 : ∀ x y, suHerm n g (N x) y = suHerm n g x (N y) := by
      intro x y
      have h := hpres x y
      simp only [hNr_apply, rckFlagSU_suHerm_add_left, rckFlagSU_suHerm_add_right, hTot x y,
        zero_add] at h
      have h0 : suHerm n g (N x) y + suHerm n g x (N y) = 0 := by
        have h1 : (suHerm n g (N x) y + suHerm n g x (N y)) + suHerm n g x y =
            0 + suHerm n g x y := by
          simpa [add_assoc, add_comm, add_left_comm] using h
        exact add_right_cancel h1
      exact (CharTwo.add_eq_zero).mp h0
    let N' : (Fin n → rckFlagSU_K g) →ₗ[rckFlagSU_K g] ↥W :=
      LinearMap.codRestrict W N (fun x => by rw [← hNr]; exact LinearMap.mem_range_self N x)
    have hN'range : N'.range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro w
      obtain ⟨x, hx⟩ := (show (w : Fin n → rckFlagSU_K g) ∈ N.range by
        rw [hNr]; exact w.2)
      refine ⟨x, Subtype.ext ?_⟩
      change N x = (w : Fin n → rckFlagSU_K g)
      exact hx
    obtain ⟨s, hs⟩ := N'.exists_rightInverse_of_surjective hN'range
    have hs_apply : ∀ w : ↥W, N' (s w) = w := fun w => by
      have h := congrArg (fun L : ↥W →ₗ[rckFlagSU_K g] ↥W => L w) hs
      simpa using h
    have hNs : ∀ w : ↥W, N (s w) = (w : Fin n → rckFlagSU_K g) := fun w =>
      congrArg Subtype.val (hs_apply w)
    have hbar : ∀ c : rckFlagSU_K g,
        (rckFlagSU_fieldData g hg).bar c = rckFlagSU_sigma g c :=
      fun c => rckFlagSU_bar_apply g hg c
    let t : ↥W →ₛₗ[(rckFlagSU_fieldData g hg).bar]
        (↥W →ₗ[rckFlagSU_K g] rckFlagSU_K g) :=
      { toFun := fun w =>
          { toFun := fun w' => suHerm n g (s w) w'
            map_add' := fun a b => rckFlagSU_suHerm_add_right n g (s w) a b
            map_smul' := fun c a => by
              change suHerm n g (s w) (c • (a : Fin n → rckFlagSU_K g)) =
                c • suHerm n g (s w) (a : Fin n → rckFlagSU_K g)
              rw [rckFlagSU_suHerm_smul_right n g c (s w) (a : Fin n → rckFlagSU_K g),
                smul_eq_mul] }
        map_add' := fun w₁ w₂ => by
          ext w'
          change suHerm n g (s (w₁ + w₂)) w' =
            suHerm n g (s w₁) w' + suHerm n g (s w₂) w'
          rw [map_add, rckFlagSU_suHerm_add_left n g (s w₁) (s w₂) w']
        map_smul' := fun c w => by
          ext w'
          change suHerm n g (s (c • w)) w' =
            (rckFlagSU_fieldData g hg).bar c • suHerm n g (s w) w'
          rw [map_smul, rckFlagSU_suHerm_smul_left n g c (s w) w', hbar, smul_eq_mul] }
    have ht_symm : t.IsSymm :=
      ⟨fun x y => by
        change (rckFlagSU_fieldData g hg).bar (suHerm n g (s x) y) = suHerm n g (s y) x
        rw [hbar, ← rckFlagSU_suHerm_symm n g hg (s x) y]
        calc suHerm n g y (s x) = suHerm n g (N (s y)) (s x) := by rw [hNs y]
          _ = suHerm n g (s y) (N (s x)) := hU2 (s y) (s x)
          _ = suHerm n g (s y) x := by rw [hNs x]⟩
    have ht_sep : t.SeparatingLeft := by
      intro x hx
      apply Subtype.ext
      apply rckFlagSU_suHerm_sep
      intro v
      rw [← hNs x, hU2 (s x) v]
      exact hx ⟨N v, by rw [← hNr]; exact LinearMap.mem_range_self N v⟩
    have hpivot : ∀ x ∈ P', ∀ u : ↥W, t u u = 0 → t u x ≠ 0 → u ∈ P' := by
      intro x hxP u huu hux
      have hxval : ((x : ↥W) : Fin n → rckFlagSU_K g) ∈ P := (hP'mem x).mp hxP
      have hxW : ((x : ↥W) : Fin n → rckFlagSU_K g) ∈ W := hPW hxval
      have hsu : suHerm n g (N (s u)) (s u) = 0 := by
        rw [hNs u, rckFlagSU_suHerm_symm n g hg (s u) (u : Fin n → rckFlagSU_K g)]
        have huu' : suHerm n g (s u) (u : Fin n → rckFlagSU_K g) = 0 := huu
        rw [huu', map_zero]
      have hm : suHerm n g ((((r : GL (Fin n) (rckFlagSU_K g)) :
          Matrix (Fin n) (Fin n) (rckFlagSU_K g)) - 1).mulVec (s u)) (s u) = 0 := by
        simpa only [N, Ar, Matrix.toLin'_apply] using hsu
      obtain ⟨c, hc, hact⟩ := rckFlagSU_lift n g hg R' W H hWH hv r hr hr1 (s u) hm
      have hNsu : (((r : GL (Fin n) (rckFlagSU_K g)) :
          Matrix (Fin n) (Fin n) (rckFlagSU_K g)) - 1).mulVec (s u) =
          ((u : ↥W) : Fin n → rckFlagSU_K g) := by
        simpa only [N, Ar, Matrix.toLin'_apply] using hNs u
      have hmem : ((x : ↥W) : Fin n → rckFlagSU_K g) +
          suHerm n g (s u) ((x : ↥W) : Fin n → rckFlagSU_K g) •
            ((u : ↥W) : Fin n → rckFlagSU_K g) ∈ P := by
        have h1 := hPinv c hc ((x : ↥W) : Fin n → rckFlagSU_K g) hxval
        have h1' : ((c : GL (Fin n) (rckFlagSU_K g)) :
            Matrix (Fin n) (Fin n) (rckFlagSU_K g)).mulVec
              ((x : ↥W) : Fin n → rckFlagSU_K g) ∈ P := h1
        have h2 := hact ((x : ↥W) : Fin n → rckFlagSU_K g) hxW
        rw [hNsu] at h2
        rw [h2] at h1'
        exact h1'
      have h1 : suHerm n g (s u) ((x : ↥W) : Fin n → rckFlagSU_K g) •
          ((u : ↥W) : Fin n → rckFlagSU_K g) ∈ P := by
        have h := P.sub_mem hmem hxval
        rwa [add_sub_cancel_left] at h
      have h2 : ((u : ↥W) : Fin n → rckFlagSU_K g) ∈ P := by
        have hcoef : suHerm n g (s u) ((x : ↥W) : Fin n → rckFlagSU_K g) ≠ 0 := hux
        have h := P.smul_mem (suHerm n g (s u) ((x : ↥W) : Fin n → rckFlagSU_K g))⁻¹ h1
        rwa [inv_smul_smul₀ hcoef] at h
      exact (hP'mem u).mpr h2
    rcases eq_or_ne P ⊥ with hPbot | hPne
    · exact Or.inl hPbot
    · right
      have hP'ne : P' ≠ ⊥ := by
        intro hbot
        exact hPne (by rw [← hmapP, hbot, Submodule.map_bot])
      have htop := rckFlagSUGeom_eq_top_of_ne_bot (f := g) (K := rckFlagSU_K g)
        (V := ↥W) (rckFlagSU_fieldData g hg) ht_symm ht_sep (by omega) hP'ne hpivot
      rw [← hmapP, htop, Submodule.map_top, Submodule.range_subtype]

theorem rckFlagIrredW_SU (n g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype none :=
  rckFlagSU_irredW_aux n g hg

theorem rckFlagCent_SU (n g : ℕ) (hg : 1 ≤ g) :
    FlagCentU (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype none := by
  exact flagCentU_of_irredW _ _
    (Subgroup.subtype_injective _) (rckFlagIrredW_SU n g hg)

end CFSG.StandardType.RCKFlag
