module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLocK
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFKDef

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

section Datum

variable {D : Type} [Group D] (A : LieAmalgamExt D)

structure NFD (N N' : Subgroup (MulAut D)) (z0 v0 nr0 na0 : D) (Zd Qd Xd Yd : Subgroup D)
    (q n : ℕ) : Prop where
  TD_le_N : ∀ u ∈ A.TD, MulAut.conj u ∈ N
  TD_le_N' : ∀ u ∈ A.TD, MulAut.conj u ∈ N'
  Z_le_Q : Zd ≤ Qd
  Q_le_T : Qd ≤ A.TD
  Q_norm : ∀ s ∈ A.TD, ∀ x ∈ Qd, s * x * s⁻¹ ∈ Qd
  Z_central : ∀ x ∈ Zd, ∀ s ∈ A.TD, s * x = x * s
  Z_exp : ∀ x ∈ Zd, x * x = 1
  card_Z : Nat.card Zd = q
  z_mem : z0 ∈ Zd
  z_ne : z0 ≠ 1
  Q_comm : ∀ x ∈ Qd, ∀ y ∈ Qd, ⁅x, y⁆ ∈ Zd
  Q_sq : ∀ x ∈ Qd, x * x ∈ Zd
  card_Q : Nat.card Qd = q ^ (2 * n + 1)
  card_T : Nat.card A.TD = q ^ (3 * n)
  T_comm : ∀ x ∈ A.TD, ∀ y ∈ A.TD, ⁅x, y⁆ ∈ Qd
  elem_abelian : ∀ E : Subgroup D, E ≤ Qd → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ q ^ (n + 1)
  aut_Z : ∀ φ ∈ N, ∀ x ∈ Zd, φ x ∈ Zd
  aut_Q : ∀ φ ∈ N, ∀ x ∈ Qd, φ x ∈ Qd
  trans : ∀ x ∈ Zd, ∀ y ∈ Zd, x ≠ 1 → y ≠ 1 → ∃ d : D, MulAut.conj d ∈ N ∧ d * x * d⁻¹ = y
  X_le : Xd ≤ Qd
  Y_le : Yd ≤ Qd
  Z_le_comm : Zd ≤ ⁅Xd, Yd⁆
  v_mem : v0 ∈ Qd
  v_not_mem : v0 ∉ Zd
  v_comm_X : ∀ a ∈ Xd, a * v0 = v0 * a
  v_comm_Y : ∀ b ∈ Yd, b * v0 = v0 * b
  v_not_cent : ∀ φ ∈ N, ∃ s ∈ A.TD, ⁅s, φ v0⁆ ∉ Zd
  nr_mem : MulAut.conj nr0 ∈ N
  na_mem : MulAut.conj na0 ∈ N'
  X_eq : Xd = cj nr0 Yd
  Y_eq : Yd = cj na0 Zd

variable (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

omit [Group D] in
theorem map_cj_iK {D : Type} [Group D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (c : D) (H : Subgroup D) :
    cj (iK A hgen c) (H.map (iK A hgen)) = (cj c H).map (iK A hgen) := by
  ext x
  rw [mem_cj]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := h
    refine ⟨c * y * c⁻¹, ?_, ?_⟩
    · show c * y * c⁻¹ ∈ cj c H
      rw [mem_cj]
      have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      rw [e]
      exact hy
    · rw [map_mul, map_mul, map_inv, hyx]
      group
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c⁻¹ * y * c, mem_cj.mp hy, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem nfk_of_nfd [Finite D] (hcen : Subgroup.center D = ⊥) {N N' : Subgroup (MulAut D)}
    {z0 v0 nr0 na0 : D} {Zd Qd Xd Yd : Subgroup D} {q n : ℕ}
    (H : NFD A N N' z0 v0 nr0 na0 Zd Qd Xd Yd q n) :
    NFK (A.TD.map (iK A hgen)) (Qd.map (iK A hgen)) (Zd.map (iK A hgen)) (Xd.map (iK A hgen))
      (Yd.map (iK A hgen)) (N.subgroupOf A.K) (N'.subgroupOf A.K) (iK A hgen z0) (iK A hgen v0)
      (iK A hgen nr0) (iK A hgen na0) q n := by
  have hinj := iK_injective A hgen hcen
  have hmem : ∀ k : ↥A.K, ∀ M : Subgroup (MulAut D), k ∈ M.subgroupOf A.K ↔ (k : MulAut D) ∈ M :=
    fun k M => Iff.rfl
  have hcardmap : ∀ X : Subgroup D, Nat.card (X.map (iK A hgen)) = Nat.card X := fun X =>
    Subgroup.card_map_of_injective hinj
  have hcomm : ∀ x y : D, ⁅iK A hgen x, iK A hgen y⁆ = iK A hgen ⁅x, y⁆ := fun x y =>
    (map_commutatorElement _ x y).symm
  refine ⟨?_, ?_, Subgroup.map_mono H.Z_le_Q, Subgroup.map_mono H.Q_le_T, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Subgroup.map_mono H.X_le, Subgroup.map_mono H.Y_le, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (hmem _ _).mpr (H.TD_le_N u hu)
  · rintro _ ⟨u, hu, rfl⟩
    exact (hmem _ _).mpr (H.TD_le_N' u hu)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨s * x * s⁻¹, H.Q_norm s hs x hx, by simp [map_mul, map_inv]⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, H.Z_central x hx s hs]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, H.Z_exp x hx, map_one]
  · rw [hcardmap, H.card_Z]
  · exact ⟨z0, H.z_mem, rfl⟩
  · intro h
    exact H.z_ne (hinj (h.trans (map_one _).symm))
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hcomm]
    exact ⟨_, H.Q_comm x hx y hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    exact ⟨_, H.Q_sq x hx, rfl⟩
  · rw [hcardmap, H.card_Q]
  · rw [hcardmap, H.card_T]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hcomm]
    exact ⟨_, H.T_comm x hx y hy, rfl⟩
  · intro E hE h2 hab
    have hEr : E ≤ (iK A hgen).range := fun x hx => by
      obtain ⟨y, -, rfl⟩ := hE hx
      exact ⟨y, rfl⟩
    have hEc : E.comap (iK A hgen) ≤ Qd := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hE hx
      exact (hinj hyx) ▸ hy
    have hmapc : (E.comap (iK A hgen)).map (iK A hgen) = E := Subgroup.map_comap_eq_self hEr
    have := H.elem_abelian (E.comap (iK A hgen)) hEc
      (fun x hx => hinj (by rw [map_mul, map_one]; exact h2 _ hx))
      (fun x hx y hy => hinj (by rw [map_mul, map_mul]; exact hab _ hx _ hy))
    rw [← hmapc, hcardmap]
    exact this
  · rintro y hy _ ⟨x, hx, rfl⟩
    rw [conj_iK A hgen]
    exact ⟨_, H.aut_Z _ ((hmem _ _).mp hy) x hx, rfl⟩
  · rintro y hy _ ⟨x, hx, rfl⟩
    rw [conj_iK A hgen]
    exact ⟨_, H.aut_Q _ ((hmem _ _).mp hy) x hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hx1 hy1
    obtain ⟨d, hdN, hd⟩ := H.trans x hx y hy (fun h => hx1 (by rw [h, map_one]))
      (fun h => hy1 (by rw [h, map_one]))
    exact ⟨iK A hgen d, (hmem _ _).mpr hdN, by rw [← hd, map_mul, map_mul, map_inv]⟩
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono H.Z_le_comm
  · exact ⟨v0, H.v_mem, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    exact H.v_not_mem ((hinj hwv) ▸ hw)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, H.v_comm_X a ha]
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, H.v_comm_Y b hb]
  · intro y hy
    obtain ⟨s, hs, hsv⟩ := H.v_not_cent _ ((hmem _ _).mp hy)
    refine ⟨iK A hgen s, ⟨s, hs, rfl⟩, ?_⟩
    rw [conj_iK A hgen, hcomm]
    rintro ⟨w, hw, hwv⟩
    exact hsv ((hinj hwv) ▸ hw)
  · exact (hmem _ _).mpr H.nr_mem
  · exact (hmem _ _).mpr H.na_mem
  · rw [map_cj_iK, H.X_eq]
  · rw [map_cj_iK, H.Y_eq]

end Datum

end CFSG.Quasithin.H13.F431.Lift
