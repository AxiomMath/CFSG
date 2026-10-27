module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.RonanH155Rest
public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def perpSub (y : MulAut V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, y (g v * v⁻¹) = g v * v⁻¹ ∧ g (y v * v⁻¹) = y v * v⁻¹}
  mul_mem' {g h} hg hh v := by
    refine ⟨?_, ?_⟩
    · have e : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
        rw [MulAut.mul_apply]
        group
      rw [e, map_mul, (hg (h v)).1, (hh v).1]
    · rw [MulAut.mul_apply, (hh v).2, (hg v).2]
  one_mem' v := by simp
  inv_mem' {g} hg v := by
    refine ⟨?_, ?_⟩
    · have e : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
        rw [MulAut.apply_inv_self]
        group
      rw [e, map_inv, (hg (g⁻¹ v)).1]
    · have h := congrArg (⇑g⁻¹) (hg v).2
      rw [MulAut.inv_apply_self] at h
      exact h.symm

theorem mem_perpSub {y g : MulAut V} :
    g ∈ perpSub y ↔ ∀ v : V, y (g v * v⁻¹) = g v * v⁻¹ ∧ g (y v * v⁻¹) = y v * v⁻¹ :=
  Iff.rfl

theorem mem_perpSub_comm {y g : MulAut V} : g ∈ perpSub y ↔ y ∈ perpSub g :=
  ⟨fun h v => ⟨(h v).2, (h v).1⟩, fun h v => ⟨(h v).2, (h v).1⟩⟩

theorem fixV_zpowers_sq_of_odd {s : MulAut V} (hs : Odd (orderOf s)) :
    fixV (Subgroup.zpowers (s ^ 2)) = fixV (Subgroup.zpowers s) := by
  congr 1
  refine le_antisymm (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 2)) ?_
  rw [Subgroup.zpowers_le]
  obtain ⟨k, hk⟩ := hs
  have e : s = (s ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf s + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h := Subgroup.pow_mem _ (Subgroup.mem_zpowers (s ^ 2)) (k + 1)
  rwa [← e] at h

variable [Finite V]

theorem index_fixV_mul_of_mem_perpSub (hV : ∀ v : V, v ^ 2 = 1) {s m : MulAut V}
    (hs : Odd (orderOf s)) (hm : m ∈ perpSub s) :
    (fixV (Subgroup.zpowers (s * m))).index =
      (fixV (Subgroup.zpowers s)).index * (fixV (Subgroup.zpowers m)).index := by
  have hP1 : ∀ v, s (m v * v⁻¹) = m v * v⁻¹ := fun v => (hm v).1
  have hP2 : ∀ v, m (s v * v⁻¹) = s v * v⁻¹ := fun v => (hm v).2
  have hodd : Odd (Nat.card (Subgroup.zpowers s)) := by rwa [Nat.card_zpowers]
  obtain ⟨hsup, hinf⟩ := coprime_decomp hodd hV (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at hsup hinf
  have hfix : fixV (Subgroup.zpowers (s * m)) =
      fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers m) := by
    ext v
    simp only [Subgroup.mem_inf, mem_fixV_zpowers_iff, MulAut.mul_apply]
    constructor
    · intro h
      have e1 : s (m v) = (m v * v⁻¹) * s v := by
        conv_lhs => rw [show m v = (m v * v⁻¹) * v by group]
        rw [map_mul, hP1]
      have h3 : (m v * v⁻¹) * s v = v := e1.symm.trans h
      have e2 : s v * v⁻¹ = (m v * v⁻¹)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc s v * v⁻¹ * (m v * v⁻¹) = (m v * v⁻¹ * s v) * v⁻¹ := by ac_rfl
          _ = 1 := by rw [h3, mul_inv_cancel]
      have hmem : s v * v⁻¹ ∈ commV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers s) := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, v, rfl⟩, ?_⟩
        rw [mem_fixV_zpowers_iff, e2, map_inv, hP1]
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem, mul_inv_cancel] at e2
      exact mul_inv_eq_one.mp (inv_eq_one.mp e2.symm)
    · rintro ⟨h1, h2⟩
      rw [h2, h1]
  have hsup' : fixV (Subgroup.zpowers s) ⊔ fixV (Subgroup.zpowers m) = ⊤ := by
    refine eq_top_iff.2 (le_trans hsup.symm.le (sup_le (fun w hw => ?_) le_sup_left))
    rw [commV_zpowers_eq_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    exact (le_sup_right : fixV (Subgroup.zpowers m) ≤ _) (mem_fixV_zpowers_iff.2 (hP2 v))
  rw [hfix, Subgroup.index_inf, ← Subgroup.relIndex_sup_left, hsup', Subgroup.relIndex_top_right]

theorem le_perpSub_of_sl2 (hV : ∀ v : V, v ^ 2 = 1) {F : Type*} [Field F] [Finite F]
    [CharP F 2] {k : ℕ} (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k) {y : MulAut V}
    {M : Subgroup (MulAut V)} (e : ↥M ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hMy : ∀ g ∈ M, g * y = y * g) (hlt : (fixV (Subgroup.zpowers y)).index < 2 ^ (2 * k)) :
    M ≤ perpSub y := by
  set W := commV (Subgroup.zpowers y) with hW
  have hWmem : ∀ v, y v * v⁻¹ ∈ W := fun v =>
    Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, rfl⟩
  have hgW : ∀ g ∈ M, ∀ v, g (y v * v⁻¹) = y (g v) * (g v)⁻¹ := by
    intro g hg v
    rw [map_mul, map_inv, ← MulAut.mul_apply, hMy g hg, MulAut.mul_apply]
  have hinv : ∀ g : ↥M, ∀ w ∈ W, (M.subtype g) w ∈ W := by
    intro g w hw
    rw [hW, commV_zpowers_eq_map] at hw ⊢
    obtain ⟨v, -, rfl⟩ := hw
    exact ⟨(g : MulAut V) v, Subgroup.mem_top _, (hgW g g.2 v).symm⟩
  have : Finite ↥M := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_rk (V := W) fun w => Subtype.ext (by simpa using hV (w : V))
  have hidx : Nat.card W = (fixV (Subgroup.zpowers y)).index := by
    rw [← ker_commHom, Subgroup.index_ker, hW, commV_zpowers_eq_map, ← MonoidHom.range_eq_map]
  have hd : rk W < 2 * k := by
    have h1 : 2 ^ rk W < 2 ^ (2 * k) := by rw [← hcard, hidx]; exact hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  have hρ := CFSG.LocalAnalysis.EvenBN.Common.sl2_eq_one_of_card_lt e hF hk
    (RonanH155.restrictAutHom M.subtype W hinv) hcard hd
  have hfix : ∀ g ∈ M, ∀ w ∈ W, g w = w := fun g hg w hw =>
    congrArg (fun φ : ↥M →* MulAut ↥W => ((φ ⟨g, hg⟩ ⟨w, hw⟩ : ↥W) : V)) hρ
  intro g hg v
  refine ⟨?_, hfix g hg _ (hWmem v)⟩
  have h1 : y (g v) * (g v)⁻¹ = y v * v⁻¹ := by rw [← hgW g hg v, hfix g hg _ (hWmem v)]
  rw [mul_inv_eq_iff_eq_mul] at h1
  rw [map_mul, map_inv, h1]
  calc y v * v⁻¹ * g v * (y v)⁻¹ = (y v * (y v)⁻¹) * (g v * v⁻¹) := by ac_rfl
    _ = g v * v⁻¹ := by rw [mul_inv_cancel, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
