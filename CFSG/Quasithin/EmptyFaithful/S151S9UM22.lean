module

public import CFSG.Quasithin.EmptyFaithful.S151S9UTr
public import CFSG.Quasithin.EmptyFaithful.S151S9UM23Blocks
public import CFSG.Quasithin.EmptyFaithful.S151S9UM23Lat
public import CFSG.Quasithin.EmptyFaithful.S151S9UM22Iso

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat

theorem mem_centerOf_subgroupOf_of_le {G : Type} [Group G] {K S : Subgroup G} (hSK : S ≤ K)
    (x : ↥K) : x ∈ centerOf (S.subgroupOf K) ↔ (x : G) ∈ centerOf S := by
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : (⟨y, hSK hy⟩ : ↥K) ∈ S.subgroupOf K := hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx2 _ hy')
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx2 (y : G) hy)

theorem mldAtSylow_subgroupOf {G : Type} [Group G] {K S : Subgroup G} (hSK : S ≤ K) {z₀ : G}
    (hz2 : orderOf z₀ = 2) (hZ : centerOf S = Subgroup.zpowers z₀) {D : Subgroup G}
    (hDK : D ≤ K) (hD : D ≤ Subgroup.centralizer ({z₀} : Set G))
    (h : ∀ Y : Subgroup G, S ≤ Y → Y ≤ K → Y ≠ K → D < Y → ActionData Y) :
    MLDAtSylow (S.subgroupOf K) := by
  have hZK : centerOf S ≤ K := inf_le_left.trans hSK
  have hZc : centerOf (S.subgroupOf K) = (centerOf S).subgroupOf K := by
    ext x
    rw [mem_centerOf_subgroupOf_of_le hSK, Subgroup.mem_subgroupOf]
  refine ⟨?_, fun W hW _ Y' hSY' hY' hlt => ?_⟩
  · rw [hZc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ, Nat.card_zpowers, hz2]
  · have hWz : ∀ w ∈ W, (w : G) = 1 ∨ (w : G) = z₀ := fun w hw =>
      S151S9T.LatAux.eq_one_or_eq_of_mem_zpowers hz2
        (hZ ▸ (mem_centerOf_subgroupOf_of_le hSK w).mp (hW hw))
    have hDW : D.subgroupOf K ≤ Subgroup.centralizer (W : Set ↥K) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rcases hWz w hw with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        exact Subgroup.mem_centralizer_iff.mp (hD hd) z₀ rfl
    have hSY : S ≤ Y'.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hSK]
      exact Subgroup.map_mono hSY'
    have hne : Y'.map K.subtype ≠ K := by
      intro heq
      apply hY'
      ext x
      simp only [Subgroup.mem_top, iff_true]
      have hx : (x : G) ∈ Y'.map K.subtype := by
        rw [heq]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      exact (Subtype.ext hyx : y = x) ▸ hy
    have hDY : D < Y'.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hDK]
      exact (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr (lt_of_le_of_lt hDW hlt)
    exact ActionDataG.of_mulEquiv (Y'.equivMapOfInjective K.subtype K.subtype_injective).symm
      (h _ hSY (Subgroup.map_subtype_le Y') hne hDY)

theorem m23_sylow_subgroupOf_Y1 :
    IsSylowTwoOf (m23CtxB.S.subgroupOf (m23CtxB.Y 1)) ⊤ := by
  have hcS : Nat.card ↥(m23CtxB.S.subgroupOf (m23CtxB.Y 1)) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (m23CtxB.S_le_Y 1)).toEquiv, m23CtxB_S_card]
  refine K1.isSylowTwoOf_top_iff.mpr ⟨IsPGroup.of_card hcS, ?_⟩
  have h1 := Subgroup.card_mul_index (m23CtxB.S.subgroupOf (m23CtxB.Y 1))
  rw [hcS, m23_card_Y1] at h1
  have h2 : (m23CtxB.S.subgroupOf (m23CtxB.Y 1)).index = 3465 := by omega
  rw [h2]
  norm_num

theorem m22_mldAtSylow
    (h : S151S9T.m23CheckD) : MLDAtSylow (m23CtxB.S.subgroupOf (m23CtxB.Y 1)) := by
  obtain ⟨z₀, hz2, hZ, hczv⟩ := m23_centre_czv h
  refine mldAtSylow_subgroupOf (m23CtxB.S_le_Y 1) hz2 hZ (D := m23CtxB.Y 11)
    ((m23_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide))
    ((hczv 11 (by norm_num)).mp (by decide)) ?_
  intro Y hSY hY1 hY1ne hlt
  rcases m23_lat_cases hSY with ⟨j, hj16, rfl⟩ | htop
  · have h11 : j ∈ m23Incl[11]! := (m23_Y_le_iff (by norm_num) hj16).mp hlt.le
    have h1 : 1 ∈ m23Incl[j]! := (m23_Y_le_iff hj16 (by norm_num)).mp hY1
    have hj1 : j ≠ 1 := fun e => hY1ne (by rw [e])
    have hj11 : j ≠ 11 := fun e => lt_irrefl _ (e ▸ hlt)
    have hj3 : j = 3 := by
      have key : ∀ i < 16, i ∈ m23Incl[11]! → 1 ∈ m23Incl[i]! → i ≠ 1 → i ≠ 11 → i = 3 := by
        decide
      exact key j hj16 h11 h1 hj1 hj11
    subst hj3
    exact m23_actionData_y3
  · exact absurd (le_antisymm hY1 (by rw [htop]; exact le_top)) hY1ne

theorem mldAt_m22
    (h : S151S9T.m23CheckD) : MLDAt .M22 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  obtain ⟨e1⟩ := m23_equiv_y1_m22
  exact mldOver_of_sylow (Γ := ↥(m23CtxB.Y 1)) (e.trans e1.symm) m23_sylow_subgroupOf_Y1
    (m22_mldAtSylow h)

end CFSG.Quasithin.S151S9U
