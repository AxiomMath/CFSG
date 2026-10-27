module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Schur

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private theorem s16e_d5_exists_notMem (hfr : s16e_d5_Frame L K Z) (i : Fin 4) :
    ∃ ξ : MulAut W, ξ ∈ L ∧ ξ ∉ K i := by
  have hnotsub : ¬ (L : Set (MulAut W)) ⊆ (K i : Set (MulAut W)) := by
    intro hsub
    have hLeq : L = K i := le_antisymm hsub (hfr.K_le i)
    have hcard : Nat.card ↥L = Nat.card ↥(K i) := by rw [hLeq]
    rw [hfr.card_L, hfr.K_card i] at hcard
    norm_num at hcard
  exact (Set.not_subset (s := (L : Set (MulAut W))) (t := (K i : Set (MulAut W)))).mp hnotsub

theorem s16e_d5_coord_one (hfr : s16e_d5_Frame L K Z) (i : Fin 4) :
    ∃ c : ↥(Subgroup.centralizer (L : Set (MulAut W))) →* Multiplicative (ZMod 3),
      (∀ g, Multiplicative.toAdd (c g) = 0 ↔ ∀ z ∈ Z i, (g : MulAut W) z = z) ∧
      (∀ g, Multiplicative.toAdd (c g) ≠ 0 → ∀ z ∈ Z i, (g : MulAut W) z = z → z = 1) := by
  classical
  let C := Subgroup.centralizer (L : Set (MulAut W))
  obtain ⟨ξ, hξL, hξK⟩ := s16e_d5_exists_notMem hfr i
  have hξ3 : ξ ^ 3 = 1 := hfr.pow_L ξ hξL
  have hξZ : ∀ z ∈ Z i, ξ z ∈ Z i := fun z hz => hfr.stable i hξL hz
  have hfix : ∀ z ∈ Z i, ξ z = z → z = 1 := fun z hz h => hfr.no_fix i hξL hξK hz h
  have hZ : Nat.card ↥(Z i) = 4 := hfr.card_Z i
  have hex : ∀ g : ↥C, ∃ e : ℕ, e < 3 ∧ ∀ z ∈ Z i, (g : MulAut W) z = (ξ ^ e) z := by
    intro g
    refine s16e_d5_schur_local hZ hξ3 hξZ hfix ?_ ?_
    · intro z hz
      rw [hfr.Z_eq i] at hz ⊢
      refine mem_fixV.mpr fun k hk => ?_
      have hkL : k ∈ L := hfr.K_le i hk
      have hkg : k * (g : MulAut W) = (g : MulAut W) * k :=
        (Subgroup.mem_centralizer_iff.mp g.2) k hkL
      have hkz : k z = z := (mem_fixV.mp hz) k hk
      calc k ((g : MulAut W) z) = (k * (g : MulAut W)) z := rfl
        _ = ((g : MulAut W) * k) z := by rw [hkg]
        _ = (g : MulAut W) (k z) := rfl
        _ = (g : MulAut W) z := by rw [hkz]
    · intro z hz
      have hgξ : ξ * (g : MulAut W) = (g : MulAut W) * ξ :=
        (Subgroup.mem_centralizer_iff.mp g.2) ξ hξL
      calc (g : MulAut W) (ξ z) = ((g : MulAut W) * ξ) z := rfl
        _ = (ξ * (g : MulAut W)) z := by rw [← hgξ]
        _ = ξ ((g : MulAut W) z) := rfl
  choose ε hε using hex
  have hε3 : ∀ g : ↥C, ε g < 3 := fun g => (hε g).1
  have hεz : ∀ g : ↥C, ∀ z ∈ Z i, (g : MulAut W) z = (ξ ^ ε g) z := fun g => (hε g).2
  have hε1 : ε 1 = 0 := by
    refine s16e_d5_pow_eq_on hZ hξ3 hfix (hε3 1) (by norm_num) (fun z hz => ?_)
    rw [← hεz 1 z hz, pow_zero]
    rfl
  have hεadd : ∀ g h : ↥C, ε (g * h) = (ε g + ε h) % 3 := by
    intro g h
    have hraw : ε (g * h) = (ε h + ε g) % 3 := by
      refine s16e_d5_pow_eq_on hZ hξ3 hfix (hε3 (g * h)) (Nat.mod_lt _ (by norm_num)) ?_
      intro z hz
      have hgξ : Commute (g : MulAut W) ξ :=
        ((Subgroup.mem_centralizer_iff.mp g.2) ξ hξL).symm
      have hcomm : Commute (g : MulAut W) (ξ ^ ε h) := hgξ.pow_right (ε h)
      have hcalc : ((g * h : ↥C) : MulAut W) z = (ξ ^ ((ε h + ε g) % 3)) z := by
        calc ((g * h : ↥C) : MulAut W) z
            = (g : MulAut W) ((h : MulAut W) z) := rfl
          _ = (g : MulAut W) ((ξ ^ ε h) z) := by rw [hεz h z hz]
          _ = (ξ ^ ε h) ((g : MulAut W) z) := by
                have h := congrArg (fun f : MulAut W => f z) hcomm.eq
                simpa only [MulAut.mul_apply] using h
          _ = (ξ ^ ε h) ((ξ ^ ε g) z) := by rw [hεz g z hz]
          _ = (ξ ^ (ε h + ε g)) z := by rw [pow_add, MulAut.mul_apply]
          _ = (ξ ^ ((ε h + ε g) % 3)) z := by rw [pow_eq_pow_mod (ε h + ε g) hξ3]
      rw [← hεz (g * h) z hz, hcalc]
    rw [hraw, Nat.add_comm (ε h) (ε g)]
  have hcast : ∀ g h : ↥C, ((ε (g * h) : ℕ) : ZMod 3)
      = ((ε g : ℕ) : ZMod 3) + ((ε h : ℕ) : ZMod 3) := by
    intro g h
    rw [hεadd g h, ZMod.natCast_mod, Nat.cast_add]
  have hzero : ∀ g : ↥C, ((ε g : ℕ) : ZMod 3) = 0 ↔ ε g = 0 := by
    intro g
    constructor
    · intro h
      have hdvd : 3 ∣ ε g := (ZMod.natCast_eq_zero_iff (ε g) 3).mp h
      obtain ⟨k, hk⟩ := hdvd
      have hlt : ε g < 3 := hε3 g
      omega
    · intro h
      rw [h]
      norm_num
  let c : ↥C →* Multiplicative (ZMod 3) :=
    { toFun := fun g => Multiplicative.ofAdd ((ε g : ℕ) : ZMod 3)
      map_one' := by
        have h0 : ((ε 1 : ℕ) : ZMod 3) = 0 := by rw [hε1]; norm_num
        rw [h0]
        rfl
      map_mul' := fun g h => by
        show Multiplicative.ofAdd ((ε (g * h) : ℕ) : ZMod 3)
            = Multiplicative.ofAdd ((ε g : ℕ) : ZMod 3)
              * Multiplicative.ofAdd ((ε h : ℕ) : ZMod 3)
        rw [hcast g h]
        rfl }
  refine ⟨c, ?_, ?_⟩
  · intro g
    have hcoe : Multiplicative.toAdd (c g) = ((ε g : ℕ) : ZMod 3) := rfl
    constructor
    · intro h
      rw [hcoe] at h
      have hε0 : ε g = 0 := (hzero g).mp h
      intro z hz
      rw [hεz g z hz, hε0, pow_zero]
      rfl
    · intro hfixall
      have hε0 : ε g = 0 := by
        refine s16e_d5_pow_eq_on hZ hξ3 hfix (hε3 g) (by norm_num) (fun z hz => ?_)
        rw [← hεz g z hz, hfixall z hz, pow_zero]
        rfl
      rw [hcoe, hε0]
      norm_num
  · intro g hne z hz hgz
    have hcoe : Multiplicative.toAdd (c g) = ((ε g : ℕ) : ZMod 3) := rfl
    have hεne : ε g ≠ 0 := by
      intro h
      apply hne
      rw [hcoe, h]
      norm_num
    have hεpos : 0 < ε g := Nat.pos_of_ne_zero hεne
    exact s16e_d5_pow_fix hξ3 hfix hεpos (hε3 g) z hz (by rw [← hεz g z hz, hgz])

theorem s16e_d5_coord (hfr : s16e_d5_Frame L K Z) :
    ∃ κ : ↥(Subgroup.centralizer (L : Set (MulAut W))) →* Multiplicative (Fin 4 → ZMod 3),
      Function.Injective κ ∧
      (∀ (g : ↥(Subgroup.centralizer (L : Set (MulAut W)))) (i : Fin 4),
        (Multiplicative.toAdd (κ g)) i = 0 ↔ ∀ z ∈ Z i, (g : MulAut W) z = z) ∧
      (∀ (g : ↥(Subgroup.centralizer (L : Set (MulAut W)))) (i : Fin 4),
        (Multiplicative.toAdd (κ g)) i ≠ 0 → ∀ z ∈ Z i, (g : MulAut W) z = z → z = 1) := by
  choose c hc0 hc1 using fun i => s16e_d5_coord_one hfr i
  let κ : ↥(Subgroup.centralizer (L : Set (MulAut W))) →* Multiplicative (Fin 4 → ZMod 3) :=
    { toFun := fun g => Multiplicative.ofAdd (fun i => Multiplicative.toAdd (c i g))
      map_one' := by
        refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
        simp
      map_mul' := fun g h => by
        refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
        simp }
  refine ⟨κ, ?_, fun g i => hc0 i g, fun g i => hc1 i g⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have h0 : ∀ i, Multiplicative.toAdd (c i g) = 0 := fun i =>
    congrFun (congrArg Multiplicative.toAdd hg) i
  have hfix : ∀ i, ∀ z ∈ Z i, (g : MulAut W) z = z := fun i => (hc0 i g).1 (h0 i)
  apply Subtype.ext
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ (⨆ i, Z i) := by rw [hfr.Z_top]; exact Subgroup.mem_top w
  refine Subgroup.iSup_induction Z (C := fun w => (g : MulAut W) w = (1 : MulAut W) w) hw
    (fun i x hx => by simpa using hfix i x hx) (by simp) (fun x y hx hy => ?_)
  simp only [MulAut.one_apply] at hx hy ⊢
  rw [map_mul, hx, hy]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
