module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Quasithin.Vol2.Ch10SecQ34MA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Quasithin CFSG.Open

theorem pow_eq_one_of_commute_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    (L : Subgroup (MulAut W)) (n : ℕ)
    (hnat : BinaryNaturalSL L ⊤ (CFSG.Quasithin.fixV L) 2 n)
    (hcommV : CFSG.Quasithin.commV L = ⊤) (c : MulAut W)
    (hc : ∀ l ∈ L, c * l = l * c) :
    c ^ (2 ^ n - 1) = 1 := by
  classical
  obtain ⟨K, _, _, hKcard, π, hD⟩ := hnat
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨B, hBs, hBk, hBe⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.exists_natHom hD
  have hcZ : ∀ v, B v = 1 → B (c v) = 1 := by
    intro v hv
    refine (hBk (c v)).mpr ?_
    intro l hl
    have hv' : l v = v := (hBk v).mp hv l hl
    have h := congrArg (fun g : MulAut W => g v) (hc l hl)
    simpa [MulAut.mul_apply, hv'] using h.symm
  obtain ⟨Y, hY⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.exists_induced B hBs c.toMonoidHom hcZ
  have hY' : ∀ w : W, Y (B w) = B (c w) := hY
  have hcπ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      c (((π γ : ↥L) : MulAut W) w) = ((π γ : ↥L) : MulAut W) (c w) := by
    intro γ w
    have h := congrArg (fun g : MulAut W => g w) (hc ((π γ : ↥L) : MulAut W) (π γ).2)
    simpa [MulAut.mul_apply] using h
  have hYc : ∀ (γ : ↥(StatedSL 2 K)) (y : Multiplicative (Fin 2 → K)),
      Y (natAct (StatedSL 2 K) γ y) = natAct (StatedSL 2 K) γ (Y y) := by
    intro γ y
    obtain ⟨w, rfl⟩ := hBs y
    rw [← hBe, hY', hY', ← hBe]
    exact congrArg B (hcπ γ w)
  obtain ⟨l, hl⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.eq_smul_of_comm_trv (by omega : 2 ≤ 2) Y
      (fun i j hij d y => hYc (B5.trvSL i j hij d) y)
  have hYsurj : Function.Surjective Y := by
    intro y
    obtain ⟨w, rfl⟩ := hBs y
    refine ⟨B (c.symm w), ?_⟩
    rw [hY', MulEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hYsurj (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K))
    have h1 := hl x
    rw [hx, h0, zero_smul] at h1
    have h2 : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) = 0 := by simpa using h1
    have h3 : (1 : K) = 0 := by simpa using congrFun h2 0
    exact one_ne_zero h3
  have hl1 : l ^ (2 ^ n - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one l hl0
    rwa [← Nat.card_eq_fintype_card, hKcard] at h
  have hit : ∀ (k : ℕ) (w : W), Y^[k] (B w) = B ((c ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply, hY', ih, pow_succ, MulAut.mul_apply]
  have hitl : ∀ (k : ℕ) (y : Multiplicative (Fin 2 → K)),
      Multiplicative.toAdd (Y^[k] y) = l ^ k • Multiplicative.toAdd y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply, ih, hl, smul_smul, pow_succ]
  have hYid : ∀ y : Multiplicative (Fin 2 → K), Y^[2 ^ n - 1] y = y := by
    intro y
    apply Multiplicative.toAdd.injective
    rw [hitl, hl1, one_smul]
  let b : MulAut W := c ^ (2 ^ n - 1)
  have hb : ∀ w : W, B (b w) = B w := by
    intro w
    have h1 := hit (2 ^ n - 1) w
    rw [hYid] at h1
    exact h1.symm
  have hbc : ∀ l ∈ L, b * l = l * b := by
    intro l hl
    exact (Commute.pow_left (show Commute c l from hc l hl) (2 ^ n - 1)).eq
  let δ : W →* W :=
    { toFun := fun w => b w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hδfix : ∀ v : W, δ v ∈ CFSG.Quasithin.fixV L := by
    intro v
    refine (hBk (δ v)).mp ?_
    show B (b v * v⁻¹) = 1
    rw [map_mul, map_inv, hb, mul_inv_cancel]
  have hδgen : ∀ x ∈ L, ∀ v : W, δ (x v * v⁻¹) = 1 := by
    intro x hx v
    have hbxv : b (x v) = x (b v) := by
      have h := congrArg (fun g : MulAut W => g v) (hbc x hx)
      simpa [MulAut.mul_apply] using h
    have hδv : x (b v * v⁻¹) = b v * v⁻¹ := hδfix v x hx
    have hδv' : x (b v) * (x v)⁻¹ = b v * v⁻¹ := by
      simpa [map_mul, map_inv] using hδv
    show b (x v * v⁻¹) * (x v * v⁻¹)⁻¹ = 1
    rw [map_mul, map_inv, hbxv, mul_inv_rev, inv_inv]
    calc
      x (b v) * (b v)⁻¹ * (v * (x v)⁻¹)
          = (x (b v) * (x v)⁻¹) * ((b v)⁻¹ * v) := by ac_rfl
      _ = (b v * v⁻¹) * ((b v)⁻¹ * v) := by rw [hδv']
      _ = 1 := by
        rw [mul_comm ((b v)⁻¹) v]
        group
  have hδ1 : ∀ w : W, δ w = 1 := by
    intro w
    have hmem : w ∈ CFSG.Quasithin.commV L := by
      rw [hcommV]
      exact Subgroup.mem_top w
    have hker : CFSG.Quasithin.commV L ≤ (⊥ : Subgroup W).comap δ := by
      rw [CFSG.Quasithin.commV]
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨x, hx, v, rfl⟩
      exact hδgen x hx v
    exact Subgroup.mem_bot.mp (hker hmem)
  have hb1 : b = 1 := by
    refine MulEquiv.ext fun w => ?_
    exact mul_inv_eq_one.mp (hδ1 w)
  exact hb1

theorem commV_eq_top_of_isBasicModule {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {n : ℕ} (hB : IsBasicModule Y)
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hnat : BinaryNaturalSL L ⊤ (CFSG.Quasithin.fixV L) 2 n) :
    CFSG.Quasithin.commV L = ⊤ := by
  classical
  obtain ⟨K, _, _, -, π, hD⟩ := hnat
  obtain ⟨B, hBs, hBk, hBe⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.exists_natHom hD
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hstableComm : StableUnder Y (CFSG.Quasithin.commV L) := fun y hy w hw =>
    CFSG.Quasithin.commV_apply_mem_of_mem_normalizer (hYnorm hy) hw
  have hstableFix : StableUnder Y (CFSG.Quasithin.fixV L) := fun y hy w hw =>
    CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hYnorm hy) hw
  have hmapStable : ∀ (γ : ↥(StatedSL 2 K)) (y : Multiplicative (Fin 2 → K)),
      y ∈ (CFSG.Quasithin.commV L).map B →
        natAct (StatedSL 2 K) γ y ∈ (CFSG.Quasithin.commV L).map B := by
    intro γ y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr
      ⟨((π γ : ↥L) : MulAut W) w,
        CFSG.Quasithin.commV_apply_mem_of_mem (π γ).2 hw, hBe γ w⟩
  have hmapNe : (CFSG.Quasithin.commV L).map B ≠ ⊥ := by
    intro hbot
    have hle : CFSG.Quasithin.commV L ≤ CFSG.Quasithin.fixV L := by
      intro w hw
      refine (hBk w).mp ?_
      have h1 : B w ∈ (CFSG.Quasithin.commV L).map B :=
        Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
      rw [hbot] at h1
      exact Subgroup.mem_bot.mp h1
    have htriv : ∀ (γ : ↥(StatedSL 2 K)) (y : Multiplicative (Fin 2 → K)),
        natAct (StatedSL 2 K) γ y = y := by
      intro γ y
      obtain ⟨v, rfl⟩ := hBs y
      have hmem : ((π γ : ↥L) : MulAut W) v * v⁻¹ ∈ CFSG.Quasithin.commV L :=
        Subgroup.subset_closure ⟨_, (π γ).2, v, rfl⟩
      have h1 : B (((π γ : ↥L) : MulAut W) v * v⁻¹) = 1 :=
        (hBk _).mpr (hle hmem)
      rw [map_mul, map_inv] at h1
      rw [← hBe]
      exact mul_inv_eq_one.mp h1
    have hbad := htriv (B5.trvSL (0 : Fin 2) 1 (by decide) (1 : K))
      (Multiplicative.ofAdd (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K))
    rw [B5.natAct_trvSL] at hbad
    have h2 : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) + Pi.single (0 : Fin 2) (1 : K) =
        Pi.single (1 : Fin 2) (1 : K) := by
      simpa using congrArg Multiplicative.toAdd hbad
    have h3 : (1 : K) = 0 := by simpa using congrFun h2 0
    exact one_ne_zero h3
  have hmapTop : (CFSG.Quasithin.commV L).map B = ⊤ := by
    rcases B5.natural_invariant_eq (by omega : 2 ≤ 2) ((CFSG.Quasithin.commV L).map B)
      hmapStable with h | h
    · exact absurd h hmapNe
    · exact h
  have htop : CFSG.Quasithin.commV L ⊔ CFSG.Quasithin.fixV L = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hBw : B w ∈ (CFSG.Quasithin.commV L).map B := by
      rw [hmapTop]
      exact Subgroup.mem_top w
    obtain ⟨s, hs, hBs'⟩ := Subgroup.mem_map.mp hBw
    have hz : w * s⁻¹ ∈ CFSG.Quasithin.fixV L := by
      refine (hBk _).mp ?_
      rw [map_mul, map_inv, hBs', mul_inv_cancel]
    have hws : w = (w * s⁻¹) * s := by group
    rw [hws]
    exact mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hs)
  have hfixNe : CFSG.Quasithin.fixV L ≠ ⊤ := by
    intro hfix
    have hB1 : B = 1 := by
      refine MonoidHom.ext fun w => ?_
      exact (hBk w).mpr (hfix ▸ Subgroup.mem_top w)
    obtain ⟨w₀, hw₀⟩ := hBs (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K))
    have h1 : B w₀ = 1 := by rw [hB1]; rfl
    rw [hw₀] at h1
    have h2 : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) = 0 := by
      simpa using congrArg Multiplicative.toAdd h1
    have h3 : (1 : K) = 0 := by simpa using congrFun h2 0
    exact one_ne_zero h3
  obtain ⟨hind, -⟩ := hB
  rcases hind (CFSG.Quasithin.commV L) (CFSG.Quasithin.fixV L) hstableComm hstableFix htop with
    h | h
  · exact h
  · exact absurd h hfixNe

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
