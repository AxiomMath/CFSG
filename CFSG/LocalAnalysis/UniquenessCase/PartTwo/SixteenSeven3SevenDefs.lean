module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c167_card_of_isElemAbelianOfRank_seven {X : Type} [Group X]
    (h : IsElemAbelianOfRank 7 3 X) : Nat.card X = 343 := by
  rw [s16c167_card_isElemAbelianOfRank h]
  norm_num

theorem s16c167_pow_seven_of_isElemAbelianOfRank {X : Type} [Group X]
    (h : IsElemAbelianOfRank 7 3 X) (x : X) : x ^ 7 = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  generalize e x = v
  induction v using Multiplicative.rec with
  | ofAdd w =>
    rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 7) 7 w, ZMod.natCast_self 7,
      zero_smul, ofAdd_zero]

structure SevenCfg {W : Type} [CommGroup W] (M L : Subgroup (MulAut W)) (Z : Subgroup W) :
    Prop where
  sq : ∀ x : W, x * x = 1
  hZ : Nat.card Z = 8
  sup : sSup (conjSubs M Z) = ⊤
  ncard : (conjSubs M Z).ncard = 4
  perm : ∀ π : Equiv.Perm ↥(conjSubs M Z), ∃ g ∈ M, ∀ Y : ↥(conjSubs M Z),
    (Y : Subgroup W).map g.toMonoidHom = (π Y : Subgroup W)
  le : L ≤ M
  lrank : IsElemAbelianOfRank 7 3 ↥L
  commute : ∀ g ∈ M, g ∉ normalizer (L : Set (MulAut W)) →
    commSub (commSub ⊤ L) (L.map (MulAut.conj g).toMonoidHom) = ⊥

variable {W : Type} [CommGroup W] {M L : Subgroup (MulAut W)} {Z : Subgroup W}

theorem SevenCfg.map_mem {g : MulAut W} (hg : g ∈ M) {Y : Subgroup W}
    (hY : Y ∈ conjSubs M Z) : Y.map g.toMonoidHom ∈ conjSubs M Z := by
  obtain ⟨h, hh, rfl⟩ := hY
  refine ⟨g * h, M.mul_mem hg hh, ?_⟩
  rw [Subgroup.map_map]
  rfl

theorem SevenCfg.card_of_mem (h : SevenCfg M L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs M Z) :
    Nat.card Y = 8 := by
  obtain ⟨g, -, rfl⟩ := hY
  rw [Subgroup.card_map_of_injective (MulEquiv.injective g), h.hZ]

theorem SevenCfg.pow_seven (h : SevenCfg M L Z) {l : MulAut W} (hl : l ∈ L) : l ^ 7 = 1 := by
  have := s16c167_pow_seven_of_isElemAbelianOfRank h.lrank ⟨l, hl⟩
  exact congrArg Subtype.val this

theorem SevenCfg.card_L (h : SevenCfg M L Z) : Nat.card L = 343 :=
  s16c167_card_of_isElemAbelianOfRank_seven h.lrank

theorem s16c167_map_map_aut (a b : MulAut W) (Y : Subgroup W) :
    (Y.map b.toMonoidHom).map a.toMonoidHom = Y.map (a * b).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem s16c167_map_one_aut (Y : Subgroup W) :
    Y.map (1 : MulAut W).toMonoidHom = Y := by
  ext y
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩

theorem s16c167_map_coe_inv_mul (g : ↥M) (Y : Subgroup W) :
    (Y.map (g : MulAut W).toMonoidHom).map ((g⁻¹ : ↥M) : MulAut W).toMonoidHom = Y := by
  rw [s16c167_map_map_aut]
  have h : ((g⁻¹ : ↥M) : MulAut W) * (g : MulAut W) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  rw [h, s16c167_map_one_aut]

theorem s16c167_map_coe_mul_inv (g : ↥M) (Y : Subgroup W) :
    (Y.map ((g⁻¹ : ↥M) : MulAut W).toMonoidHom).map (g : MulAut W).toMonoidHom = Y := by
  rw [s16c167_map_map_aut]
  have h : (g : MulAut W) * ((g⁻¹ : ↥M) : MulAut W) = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  rw [h, s16c167_map_one_aut]

@[expose] noncomputable def sevenPerm (M : Subgroup (MulAut W)) (Z : Subgroup W) :
    ↥M →* Equiv.Perm ↥(conjSubs M Z) where
  toFun g :=
    { toFun := fun Y => ⟨(Y : Subgroup W).map (g : MulAut W).toMonoidHom,
        SevenCfg.map_mem g.2 Y.2⟩
      invFun := fun Y => ⟨(Y : Subgroup W).map ((g⁻¹ : ↥M) : MulAut W).toMonoidHom,
        SevenCfg.map_mem (g⁻¹).2 Y.2⟩
      left_inv := fun Y => Subtype.ext (s16c167_map_coe_inv_mul g (Y : Subgroup W))
      right_inv := fun Y => Subtype.ext (s16c167_map_coe_mul_inv g (Y : Subgroup W)) }
  map_one' := Equiv.ext fun Y => Subtype.ext (s16c167_map_one_aut (Y : Subgroup W))
  map_mul' := fun g h => Equiv.ext fun Y => Subtype.ext (by
    change (Y : Subgroup W).map ((g * h : ↥M) : MulAut W).toMonoidHom =
      ((Y : Subgroup W).map (h : MulAut W).toMonoidHom).map (g : MulAut W).toMonoidHom
    rw [s16c167_map_map_aut]
    rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
