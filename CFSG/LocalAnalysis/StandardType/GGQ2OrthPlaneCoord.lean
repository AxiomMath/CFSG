module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCoord
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutBasic
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFrameDimensions

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.StandardType.ChoiceTwoOm
open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (t : ℕ) (δ : Fin 2)

@[expose] def planeW0 : Submodule K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) where
  carrier := {v | ∀ k, ((Sum.elim id id k : Fin (t + δ.val)) : ℕ) < t → v k = 0}
  add_mem' {v w} hv hw k hk := by simp [hv k hk, hw k hk]
  zero_mem' k _ := rfl
  smul_mem' c v hv k hk := by simp [hv k hk]

@[expose] def planeTorus :
    Subgroup ((Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) ≃ₗ[K]
      (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)) :=
  Subgroup.closure (Set.range fun u => toLinEquiv _ K (otau ζ t δ u))

private def opc_Z : Matrix (Fin 2) (Fin 2) K :=
  ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

private def opc_swap (Z : Matrix (Fin 2) (Fin 2) K) : Fin 2 → Fin 2 := by
  classical
  exact fun a => if Z 0 0 = 0 then a else if a = 0 then 1 else 0

private def opc_pair (Z : Matrix (Fin 2) (Fin 2) K) (c : K × K) : Fin 2 → K :=
  fun a => if opc_swap Z a = 0 then c.1 else c.2

private theorem opc_swap_invol (Z : Matrix (Fin 2) (Fin 2) K) (a : Fin 2) :
    opc_swap Z (opc_swap Z a) = a := by
  classical
  unfold opc_swap
  by_cases h : Z 0 0 = 0
  · simp [h]
  · simp [h]
    fin_cases a <;> simp

private theorem opc_pair_swap (Z : Matrix (Fin 2) (Fin 2) K) (c : K × K) (a : Fin 2) :
    opc_pair Z c (opc_swap Z a) = if a = 0 then c.1 else c.2 := by
  classical
  unfold opc_pair
  rw [opc_swap_invol]

private theorem opc_pair_cons {n : ℕ} (Z : Matrix (Fin 2) (Fin 2) K) (i : Fin n)
    (w : Fin n ⊕ Fin n → K) (a : Fin 2) :
    opc_pair Z (w (WitSpNs.coord (opc_swap Z 0) i), w (WitSpNs.coord (opc_swap Z 1) i)) a =
      w (WitSpNs.coord a i) := by
  classical
  unfold opc_pair
  by_cases h : Z 0 0 = 0
  · have h0 : opc_swap Z 0 = 0 := by simp [opc_swap, h]
    have h1 : opc_swap Z 1 = 1 := by simp [opc_swap, h]
    fin_cases a <;> simp [h0, h1, WitSpNs.coord]
  · have h0 : opc_swap Z 0 = 1 := by simp [opc_swap, h]
    have h1 : opc_swap Z 1 = 0 := by simp [opc_swap, h]
    fin_cases a <;> simp [h0, h1, WitSpNs.coord]

private theorem opc_pair_add (Z : Matrix (Fin 2) (Fin 2) K) (c c' : K × K) (a : Fin 2) :
    opc_pair Z (c + c') a = opc_pair Z c a + opc_pair Z c' a := by
  classical
  unfold opc_pair
  split_ifs <;> simp

private theorem opc_pair_smul (Z : Matrix (Fin 2) (Fin 2) K) (r : K) (c : K × K) (a : Fin 2) :
    opc_pair Z (r • c) a = r • opc_pair Z c a := by
  classical
  unfold opc_pair
  split_ifs <;> simp

private theorem opc_pair_nrm (Z : Matrix (Fin 2) (Fin 2) K) (c : K × K) :
    opc_pair Z c 0 * opc_pair Z c 1 + (opc_pair Z c 0 ^ 2 + opc_pair Z c 1 ^ 2) = nrm c := by
  classical
  by_cases h : Z 0 0 = 0
  · have h0 : opc_swap Z 0 = 0 := by simp [opc_swap, h]
    have h1 : opc_swap Z 1 = 1 := by simp [opc_swap, h]
    simp [opc_pair, h0, h1, nrm]
    ring
  · have h0 : opc_swap Z 0 = 1 := by simp [opc_swap, h]
    have h1 : opc_swap Z 1 = 0 := by simp [opc_swap, h]
    simp [opc_pair, h0, h1, nrm]
    ring

private theorem opc_pair_zero (Z : Matrix (Fin 2) (Fin 2) K) (a : Fin 2) :
    opc_pair Z (0 : K × K) a = 0 := by
  classical
  unfold opc_pair
  split_ifs <;> rfl

private theorem opc_pair_self (Z : Matrix (Fin 2) (Fin 2) K) (a : Fin 2) :
    opc_pair Z (if opc_swap Z a = 0 then (1, 0) else (0, 1)) a = 1 := by
  classical
  unfold opc_pair
  by_cases h : opc_swap Z a = 0 <;> simp [h]

private theorem opc_pair_other (Z : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2) (h : b ≠ a) :
    opc_pair Z (if opc_swap Z a = 0 then (1, 0) else (0, 1)) b = 0 := by
  classical
  have hne : opc_swap Z b ≠ opc_swap Z a := by
    intro hb
    apply h
    calc b = opc_swap Z (opc_swap Z b) := (opc_swap_invol Z b).symm
         _ = opc_swap Z (opc_swap Z a) := by rw [hb]
         _ = a := opc_swap_invol Z a
  unfold opc_pair
  by_cases ha : opc_swap Z a = 0
  · have hb : opc_swap Z b ≠ 0 := by rw [ha] at hne; exact hne
    simp [ha, hb]
  · have ha1 : opc_swap Z a = 1 := by
      apply Fin.ext
      have hlt : (opc_swap Z a : ℕ) < 2 := (opc_swap Z a).isLt
      have hne0 : (opc_swap Z a : ℕ) ≠ 0 := by
        intro h
        exact ha (Fin.ext h)
      omega
    have hb1 : opc_swap Z b ≠ 1 := by rw [ha1] at hne; exact hne
    have hb : opc_swap Z b = 0 := by
      apply Fin.ext
      have hlt : (opc_swap Z b : ℕ) < 2 := (opc_swap Z b).isLt
      have hne1 : (opc_swap Z b : ℕ) ≠ 1 := by
        intro h
        exact hb1 (Fin.ext h)
      omega
    simp [ha, hb]

private theorem opc_Z_mulVec [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (c : K × K) :
    opc_Z ζ *ᵥ opc_pair (opc_Z ζ) c = opc_pair (opc_Z ζ) (zL K c) := by
  classical
  obtain ⟨h01, h10, hsum⟩ := SpBlocks.zeta_one_entries (K := K) hK hζ
  change opc_Z ζ 0 1 = 1 at h01
  change opc_Z ζ 1 0 = 1 at h10
  change opc_Z ζ 0 0 + opc_Z ζ 1 1 = 1 at hsum
  rcases SpBlocks.eq_zero_or_eq_one hK (opc_Z ζ 0 0) with h0 | h0
  · have h11 : opc_Z ζ 1 1 = 1 := by
      have h := hsum
      rw [h0, zero_add] at h
      exact h
    funext a
    fin_cases a <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, opc_pair, opc_swap,
        h0, h01, h10, h11, zL_apply]
  · have h11 : opc_Z ζ 1 1 = 0 := by
      have h := hsum
      rw [h0] at h
      simpa using h
    funext a
    fin_cases a <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, opc_pair, opc_swap,
        h0, h01, h10, h11, zL_apply]
    ring

private theorem opc_Z_sq_mulVec [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (c : K × K) :
    (opc_Z ζ * opc_Z ζ) *ᵥ opc_pair (opc_Z ζ) c = opc_pair (opc_Z ζ) (zL K (zL K c)) := by
  rw [← Matrix.mulVec_mulVec, opc_Z_mulVec ζ hK hζ, opc_Z_mulVec ζ hK hζ]

private theorem opc_Zpow_mulVec [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (a : ZMod 3) (c : K × K) :
    (opc_Z ζ ^ a.val) *ᵥ opc_pair (opc_Z ζ) c = opc_pair (opc_Z ζ) (zpow a c) := by
  have hlt := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 ∨ a.val = 2 by omega) with h0 | h1 | h2
  · have ha : a = 0 := (ZMod.val_eq_zero a).mp h0
    subst ha
    rw [ZMod.val_zero, pow_zero, ChoiceTwoOm.zpow_zero]
    simp
  · have hz : zpow a c = zL K c := by rw [zpow, h1, pow_one]
    rw [hz, h1, pow_one]
    exact opc_Z_mulVec ζ hK hζ c
  · have hz : zpow a c = zL K (zL K c) := by
      rw [zpow, h2, _root_.sq, LinearEquiv.mul_apply]
    rw [hz, h2, _root_.sq]
    exact opc_Z_sq_mulVec ζ hK hζ c

private theorem opc_liftV_of_lt (u : PlaneRaw.V t) {i : Fin (t + δ.val)}
    (h : (i : ℕ) < t) : liftV t δ u i = u ⟨(i : ℕ), h⟩ := by
  have hlift : liftV t δ u i = Fin.append u 0 i := rfl
  rw [hlift]
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    congr 1
  | right j =>
    simp at h

private theorem opc_liftV_ge (u : PlaneRaw.V t) {i : Fin (t + δ.val)}
    (h : ¬ (i : ℕ) < t) : liftV t δ u i = 0 := by
  have hlift : liftV t δ u i = Fin.append u 0 i := rfl
  rw [hlift]
  induction i using Fin.addCases with
  | left j =>
    simp at h
  | right j =>
    rw [Fin.append_right]
    rfl

def planeCoordFun (d : Fin t → K × K) (x : planeW0 (K := K) t δ) :
    Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
  fun k =>
    (if h : (WitSpNs.plane k : ℕ) < t then
      opc_pair (opc_Z ζ) (d ⟨(WitSpNs.plane k : ℕ), h⟩) (WitSpNs.side k)
    else 0) + (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) k

def planeCoordInv (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    (Fin t → K × K) × planeW0 (K := K) t δ :=
  (fun j =>
    (w (WitSpNs.coord (opc_swap (opc_Z ζ) 0) (Fin.castAdd δ.val j)),
     w (WitSpNs.coord (opc_swap (opc_Z ζ) 1) (Fin.castAdd δ.val j))),
   ⟨fun k => if (WitSpNs.plane k : ℕ) < t then 0 else w k, by
     intro k hk
     dsimp only
     have hk' : (WitSpNs.plane k : ℕ) < t := by simpa [WitSpNs.plane] using hk
     rw [if_pos hk']⟩)

private theorem opc_fwd_coord (d : Fin t → K × K) (x : planeW0 t δ) (j : Fin t) (b : Fin 2) :
    planeCoordFun ζ t δ d x (WitSpNs.coord b (Fin.castAdd δ.val j)) =
      opc_pair (opc_Z ζ) (d j) b := by
  classical
  have hle : (WitSpNs.plane (WitSpNs.coord b (Fin.castAdd δ.val j)) : ℕ) < t := by simp
  rw [planeCoordFun, dif_pos hle]
  have hidx : (⟨(WitSpNs.plane (WitSpNs.coord b (Fin.castAdd δ.val j)) : ℕ), hle⟩ :
      Fin t) = j := Fin.ext (by simp)
  have hx : (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)
      (WitSpNs.coord b (Fin.castAdd δ.val j)) = 0 := x.2 _ hle
  rw [hidx, hx, add_zero]
  simp [WitSpNs.side_coord]

private theorem opc_fwd_apply_lt (d : Fin t → K × K) (x : planeW0 t δ)
    {k : Fin (t + δ.val) ⊕ Fin (t + δ.val)} (h : (WitSpNs.plane k : ℕ) < t) :
    planeCoordFun ζ t δ d x k =
      opc_pair (opc_Z ζ) (d ⟨(WitSpNs.plane k : ℕ), h⟩) (WitSpNs.side k) := by
  classical
  rw [planeCoordFun, dif_pos h]
  have hx : (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) k = 0 := x.2 k h
  rw [hx, add_zero]

private theorem opc_fwd_hyper (d : Fin t → K × K) (x : planeW0 t δ)
    (k : Fin (t + δ.val) ⊕ Fin (t + δ.val))
    (h : ¬ (WitSpNs.plane k : ℕ) < t) :
    planeCoordFun ζ t δ d x k = (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) k := by
  classical
  rw [planeCoordFun, dif_neg h, zero_add]

theorem planeCoordFun_add (d d' : Fin t → K × K) (x x' : planeW0 t δ) :
    planeCoordFun ζ t δ (d + d') (x + x') =
      planeCoordFun ζ t δ d x + planeCoordFun ζ t δ d' x' := by
  classical
  funext k
  by_cases h : (WitSpNs.plane k : ℕ) < t
  · rw [opc_fwd_apply_lt ζ t δ (d + d') (x + x') h]
    simp only [Pi.add_apply]
    rw [opc_fwd_apply_lt ζ t δ d x h, opc_fwd_apply_lt ζ t δ d' x' h, opc_pair_add]
  · rw [opc_fwd_hyper ζ t δ (d + d') (x + x') k h]
    simp only [Pi.add_apply]
    rw [opc_fwd_hyper ζ t δ d x k h, opc_fwd_hyper ζ t δ d' x' k h]
    rfl

theorem planeCoordFun_smul (r : K) (d : Fin t → K × K) (x : planeW0 t δ) :
    planeCoordFun ζ t δ (r • d) (r • x) = r • planeCoordFun ζ t δ d x := by
  classical
  funext k
  by_cases h : (WitSpNs.plane k : ℕ) < t
  · rw [opc_fwd_apply_lt ζ t δ (r • d) (r • x) h]
    simp only [Pi.smul_apply]
    rw [opc_fwd_apply_lt ζ t δ d x h, opc_pair_smul]
  · rw [opc_fwd_hyper ζ t δ (r • d) (r • x) k h]
    simp only [Pi.smul_apply]
    rw [opc_fwd_hyper ζ t δ d x k h]
    rfl

theorem planeCoordInv_planeCoordFun (d : Fin t → K × K) (x : planeW0 t δ) :
    planeCoordInv ζ t δ (planeCoordFun ζ t δ d x) = (d, x) := by
  classical
  apply Prod.ext
  · funext j
    apply Prod.ext
    · simp only [planeCoordInv]
      rw [opc_fwd_coord]
      simp [opc_pair_swap]
    · simp only [planeCoordInv]
      rw [opc_fwd_coord]
      simp [opc_pair_swap]
  · apply Subtype.ext
    funext k
    by_cases h : (WitSpNs.plane k : ℕ) < t
    · simp only [planeCoordInv]
      rw [if_pos h, x.2 k h]
    · simp only [planeCoordInv]
      rw [if_neg h, opc_fwd_hyper ζ t δ d x k h]

theorem planeCoordFun_planeCoordInv (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    planeCoordFun ζ t δ (planeCoordInv ζ t δ w).1 (planeCoordInv ζ t δ w).2 = w := by
  classical
  funext k
  by_cases h : (WitSpNs.plane k : ℕ) < t
  · have hcast : Fin.castAdd δ.val (⟨(WitSpNs.plane k : ℕ), h⟩ : Fin t) =
        WitSpNs.plane k := Fin.ext rfl
    rw [opc_fwd_apply_lt ζ t δ (planeCoordInv ζ t δ w).1 (planeCoordInv ζ t δ w).2 h]
    have hinv : (planeCoordInv ζ t δ w).1 ⟨(WitSpNs.plane k : ℕ), h⟩ =
        (w (WitSpNs.coord (opc_swap (opc_Z ζ) 0) (WitSpNs.plane k)),
         w (WitSpNs.coord (opc_swap (opc_Z ζ) 1) (WitSpNs.plane k))) := by
      simp only [planeCoordInv, hcast]
    rw [hinv, opc_pair_cons]
    congr 1
    rcases k with i | i <;> rfl
  · rw [opc_fwd_hyper ζ t δ (planeCoordInv ζ t δ w).1 (planeCoordInv ζ t δ w).2 k h]
    simp only [planeCoordInv]
    rw [if_neg h]

private theorem opc_planeQ_hyper (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)
    (hx : x ∈ planeW0 t δ) :
    planeQ t δ x =
      ∑ k : Fin δ.val, x (Sum.inl (Fin.natAdd t k)) * x (Sum.inr (Fin.natAdd t k)) := by
  classical
  have hx0 : ∀ k, (WitSpNs.plane k : ℕ) < t → x k = 0 := fun k hk => hx k hk
  rw [planeQ, Fin.sum_univ_add]
  have hzero : (∑ j : Fin t,
      (x (Sum.inl (Fin.castAdd δ.val j)) * x (Sum.inr (Fin.castAdd δ.val j)) +
        if (Fin.castAdd δ.val j : ℕ) < t then
          x (Sum.inl (Fin.castAdd δ.val j)) ^ 2 +
          x (Sum.inr (Fin.castAdd δ.val j)) ^ 2
        else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [if_pos (by simp)]
    have h1 := hx0 (Sum.inl (Fin.castAdd δ.val j)) (by simp)
    have h2 := hx0 (Sum.inr (Fin.castAdd δ.val j)) (by simp)
    simp [h1, h2]
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [if_neg (by simp)]
  ring

private theorem opc_planeQ_fwd (d : Fin t → K × K) (x : planeW0 t δ) :
    planeQ t δ (planeCoordFun ζ t δ d x) =
      (∑ j : Fin t, nrm (d j)) + planeQ t δ (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) := by
  classical
  rw [opc_planeQ_hyper t δ (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) x.2]
  conv_lhs => rw [planeQ, Fin.sum_univ_add]
  have haniso : (∑ j : Fin t,
      ((planeCoordFun ζ t δ d x (Sum.inl (Fin.castAdd δ.val j))) *
        (planeCoordFun ζ t δ d x (Sum.inr (Fin.castAdd δ.val j))) +
        if (Fin.castAdd δ.val j : ℕ) < t then
          (planeCoordFun ζ t δ d x (Sum.inl (Fin.castAdd δ.val j))) ^ 2 +
          (planeCoordFun ζ t δ d x (Sum.inr (Fin.castAdd δ.val j))) ^ 2 else 0)) =
      ∑ j : Fin t, nrm (d j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos (by simp)]
    have h1 : planeCoordFun ζ t δ d x (Sum.inl (Fin.castAdd δ.val j)) =
        opc_pair (opc_Z ζ) (d j) 0 := by
      simpa [WitSpNs.coord] using opc_fwd_coord ζ t δ d x j 0
    have h2 : planeCoordFun ζ t δ d x (Sum.inr (Fin.castAdd δ.val j)) =
        opc_pair (opc_Z ζ) (d j) 1 := by
      simpa [WitSpNs.coord] using opc_fwd_coord ζ t δ d x j 1
    rw [h1, h2, opc_pair_nrm]
  have hhyp : (∑ k : Fin δ.val,
      ((planeCoordFun ζ t δ d x (Sum.inl (Fin.natAdd t k))) *
        (planeCoordFun ζ t δ d x (Sum.inr (Fin.natAdd t k))) +
        if (Fin.natAdd t k : ℕ) < t then
          (planeCoordFun ζ t δ d x (Sum.inl (Fin.natAdd t k))) ^ 2 +
          (planeCoordFun ζ t δ d x (Sum.inr (Fin.natAdd t k))) ^ 2 else 0)) =
      ∑ k : Fin δ.val,
        (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (Sum.inl (Fin.natAdd t k)) *
        (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (Sum.inr (Fin.natAdd t k)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [if_neg (by simp)]
    rw [opc_fwd_hyper ζ t δ d x (Sum.inl (Fin.natAdd t k)) (by simp),
        opc_fwd_hyper ζ t δ d x (Sum.inr (Fin.natAdd t k)) (by simp)]
    ring
  rw [haniso, hhyp]

theorem apply_planeCoordFun [Finite K] [CharP K 2]
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (d : Fin t → K × K) (x : planeW0 t δ) :
    Q (planeCoordFun ζ t δ d x) =
      (∑ i, nrm (d i)) + Q (x : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) := by
  rw [hQ, opc_planeQ_fwd]

theorem toLinEquiv_otau_planeCoordFun [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (f : PlaneRaw.V t) (d : Fin t → K × K)
    (x : planeW0 t δ) :
    toLinEquiv _ K (otau ζ t δ f) (planeCoordFun ζ t δ d x) =
      planeCoordFun ζ t δ (torC f d) x := by
  classical
  funext k
  have hk : k = WitSpNs.coord (WitSpNs.side k) (WitSpNs.plane k) := by
    rcases k with i | i <;> rfl
  rw [hk, toLinEquiv_apply]
  have hmat : ((otau ζ t δ f : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
      Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val)) (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      WitSpNs.planeMat (fun j => ((ζ (Multiplicative.ofAdd (liftV t δ f j)) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :=
    SpBlocks.coe_tau ζ (t + δ.val) (liftV t δ f)
  rw [hmat, QTwoSymplecticCav.planeMat_mulVec_coord]
  by_cases h : (WitSpNs.plane k : ℕ) < t
  · have hcast : Fin.castAdd δ.val (⟨(WitSpNs.plane k : ℕ), h⟩ : Fin t) =
        WitSpNs.plane k := Fin.ext rfl
    have hv : (fun b => planeCoordFun ζ t δ d x (WitSpNs.coord b (WitSpNs.plane k))) =
        opc_pair (opc_Z ζ) (d ⟨(WitSpNs.plane k : ℕ), h⟩) := by
      funext b
      have harg : WitSpNs.coord b (Fin.castAdd δ.val (⟨(WitSpNs.plane k : ℕ), h⟩ : Fin t)) =
          WitSpNs.coord b (WitSpNs.plane k) := by rw [hcast]
      rw [← harg, opc_fwd_coord]
    rw [hv]
    have hM : ((ζ (Multiplicative.ofAdd (liftV t δ f (WitSpNs.plane k))) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        opc_Z ζ ^ (f ⟨(WitSpNs.plane k : ℕ), h⟩).val := by
      rw [opc_liftV_of_lt t δ f h]
      have hval : (f ⟨(WitSpNs.plane k : ℕ), h⟩).val • (1 : ZMod 3) =
          f ⟨(WitSpNs.plane k : ℕ), h⟩ := by
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      have hof : Multiplicative.ofAdd (f ⟨(WitSpNs.plane k : ℕ), h⟩) =
          Multiplicative.ofAdd (1 : ZMod 3) ^ (f ⟨(WitSpNs.plane k : ℕ), h⟩).val := by
        conv_lhs => rw [← hval]
        rw [ofAdd_nsmul]
      rw [hof, map_pow, Matrix.SpecialLinearGroup.coe_pow]
      rfl
    rw [hM, opc_Zpow_mulVec ζ hK hζ]
    have harg2 : WitSpNs.coord (WitSpNs.side k)
        (Fin.castAdd δ.val (⟨(WitSpNs.plane k : ℕ), h⟩ : Fin t)) =
        WitSpNs.coord (WitSpNs.side k) (WitSpNs.plane k) := by rw [hcast]
    rw [← harg2, opc_fwd_coord]
    simp only [torC]
  · have hlift : liftV t δ f (WitSpNs.plane k) = 0 := opc_liftV_ge t δ f h
    have hM : ((ζ (Multiplicative.ofAdd (liftV t δ f (WitSpNs.plane k))) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hlift, ofAdd_zero, map_one]
      rfl
    rw [hM, Matrix.one_mulVec]
    have hcoord : WitSpNs.coord (WitSpNs.side k) (WitSpNs.plane k) = k := by
      rcases k with i | i <;> rfl
    rw [hcoord, opc_fwd_hyper ζ t δ d x k h,
        opc_fwd_hyper ζ t δ (torC f d) x k h]

theorem toLinEquiv_otau_mem_planeTorus (f : PlaneRaw.V t) :
    toLinEquiv _ K (otau ζ t δ f) ∈ planeTorus ζ t δ :=
  Subgroup.subset_closure ⟨f, rfl⟩

theorem exists_toLinEquiv_otau_eq_of_mem_planeTorus
    (c : (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) ≃ₗ[K] (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K))
    (hc : c ∈ planeTorus ζ t δ) :
    ∃ f, toLinEquiv _ K (otau ζ t δ f) = c := by
  classical
  refine Subgroup.closure_induction
    (p := fun c _ => ∃ f, toLinEquiv _ K (otau ζ t δ f) = c) ?_ ?_ ?_ ?_ hc
  · rintro x ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · exact ⟨0, by rw [otau_zero, map_one]⟩
  · rintro x y _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f + g, ?_⟩
    rw [otau_add, map_mul]
  · rintro x _ ⟨f, rfl⟩
    refine ⟨-f, ?_⟩
    have h : otau ζ t δ f * otau ζ t δ (-f) = 1 := by
      rw [← otau_add, add_neg_cancel, otau_zero]
    rw [eq_inv_of_mul_eq_one_right h, map_inv]

@[expose] def planeCoord [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ) :
    ChoiceTwoOm.OmCoord K Q (planeTorus ζ t δ) where
  s := t
  W0 := planeW0 t δ
  Φ :=
    { toFun := fun p => planeCoordFun ζ t δ p.1 p.2
      invFun := fun w => planeCoordInv ζ t δ w
      left_inv := fun p => planeCoordInv_planeCoordFun ζ t δ p.1 p.2
      right_inv := fun w => planeCoordFun_planeCoordInv ζ t δ w
      map_add' := fun p q => planeCoordFun_add ζ t δ p.1 q.1 p.2 q.2
      map_smul' := fun r p => planeCoordFun_smul ζ t δ r p.1 p.2 }
  form := fun d x => apply_planeCoordFun ζ t δ hQ d x
  tor u := toLinEquiv _ K (otau ζ t δ u)
  tor_acts := fun f d x => toLinEquiv_otau_planeCoordFun ζ t δ hK hζ f d x
  tor_mem := fun f => toLinEquiv_otau_mem_planeTorus ζ t δ f
  mem_tor := fun c hc => exists_toLinEquiv_otau_eq_of_mem_planeTorus ζ t δ c hc

variable [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
  {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)

theorem planeCoord_tor (u : PlaneRaw.V t) :
    (planeCoord ζ t δ hK hζ hQ).tor u = toLinEquiv _ K (otau ζ t δ u) :=
  rfl

theorem planeCoord_W0_eq_bot (hδ : δ.val = 0) : (planeCoord ζ t δ hK hζ hQ).W0 = ⊥ := by
  have hδ' : δ = 0 := Fin.ext hδ
  subst hδ'
  have hW : (planeCoord ζ t 0 hK hζ hQ).W0 = planeW0 t 0 := rfl
  rw [hW]
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  funext k
  exact hv k (by simp)

theorem planeCoord_W0_ne_bot (hδ : δ.val ≠ 0) : (planeCoord ζ t δ hK hζ hQ).W0 ≠ ⊥ := by
  have hW : (planeCoord ζ t δ hK hζ hQ).W0 = planeW0 t δ := rfl
  rw [hW]
  let v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inl (⟨t, by omega⟩ : Fin (t + δ.val))) (1 : K)
  have hv : v ∈ planeW0 t δ := by
    intro k hk
    by_cases h : k = Sum.inl (⟨t, by omega⟩ : Fin (t + δ.val))
    · rw [h] at hk ⊢
      simp [Sum.elim] at hk
    · dsimp only [v]
      rw [Pi.single_eq_of_ne h]
  have hne : v ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl (⟨t, by omega⟩ : Fin (t + δ.val)))
    dsimp only [v] at h1
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  intro hbot
  rw [hbot, Submodule.mem_bot] at hv
  exact hne hv

theorem exists_planeCoord_Φ_eq_single (j : Fin t) (k : Fin (t + δ.val) ⊕ Fin (t + δ.val))
    (hk : Sum.elim id id k = Fin.castAdd δ.val j) :
    ∃ c : K × K, (planeCoord ζ t δ hK hζ hQ).Φ (Pi.single j c, 0) = Pi.single k 1 := by
  classical
  change ∃ c : K × K,
    planeCoordFun ζ t δ (Pi.single j c) (0 : planeW0 t δ) = Pi.single k 1
  refine ⟨if opc_swap (opc_Z ζ) (WitSpNs.side k) = 0 then (1, 0) else (0, 1), ?_⟩
  have hvalk : (WitSpNs.plane k : ℕ) = j.val := by
    have h1 := congrArg Fin.val hk
    simpa [WitSpNs.plane] using h1
  have hltk : (WitSpNs.plane k : ℕ) < t := by
    rw [hvalk]
    exact j.isLt
  have hidxk : (⟨(WitSpNs.plane k : ℕ), hltk⟩ : Fin t) = j := Fin.ext hvalk
  funext k'
  by_cases hkk : k' = k
  · rw [hkk]
    rw [opc_fwd_apply_lt ζ t δ (Pi.single j _) 0 hltk]
    rw [hidxk, Pi.single_eq_same, Pi.single_eq_same]
    exact opc_pair_self (opc_Z ζ) (WitSpNs.side k)
  · by_cases hlt : (WitSpNs.plane k' : ℕ) < t
    · rw [opc_fwd_apply_lt ζ t δ (Pi.single j _) 0 hlt]
      by_cases hj : (⟨(WitSpNs.plane k' : ℕ), hlt⟩ : Fin t) = j
      · rw [hj, Pi.single_eq_same]
        have hplane : WitSpNs.plane k' = WitSpNs.plane k := by
          apply Fin.ext
          exact (congrArg Fin.val hj).trans (congrArg Fin.val hidxk).symm
        have hside : WitSpNs.side k' ≠ WitSpNs.side k := by
          intro hs
          apply hkk
          have hk' : k' = WitSpNs.coord (WitSpNs.side k') (WitSpNs.plane k') := by
            rcases k' with i | i <;> rfl
          have hk0 : k = WitSpNs.coord (WitSpNs.side k) (WitSpNs.plane k) := by
            rcases k with i | i <;> rfl
          rw [hk', hk0, hs, hplane]
        rw [Pi.single_eq_of_ne hkk]
        exact opc_pair_other (opc_Z ζ) (WitSpNs.side k) (WitSpNs.side k') hside
      · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hkk]
        exact opc_pair_zero (opc_Z ζ) (WitSpNs.side k')
    · rw [opc_fwd_hyper ζ t δ (Pi.single j _) 0 k' hlt]
      rw [Pi.single_eq_of_ne hkk]
      simp

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
