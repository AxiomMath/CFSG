module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3P

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG

variable {G : Type} [Group G]

theorem commute_inv_mul_of_conj_eq {a a' c d : G} (h : a * c * a⁻¹ = d) (h' : a' * c * a'⁻¹ = d) :
    Commute (a⁻¹ * a') c := by
  show a⁻¹ * a' * c = c * (a⁻¹ * a')
  calc a⁻¹ * a' * c = a⁻¹ * (a' * c * a'⁻¹) * a' := by group
    _ = a⁻¹ * (a * c * a⁻¹) * a' := by rw [h, h']
    _ = c * (a⁻¹ * a') := by group

theorem isPGroup_conjBy {p : ℕ} {W : Subgroup G} (n : G) (hW : IsPGroup p W) :
    IsPGroup p (conjBy n W) := by
  intro z
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 z.2
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : w ^ (p ^ k) = 1 := congrArg Subtype.val hk
  show (z : G) ^ (p ^ k) = 1
  rw [← hwz]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, hk']
  group

theorem nor_conjBy [Finite G] {W : Subgroup G} {g : G} (hg : g ∈ Nor W) (n : G) :
    n * g * n⁻¹ ∈ Nor (conjBy n W) := by
  apply Subgroup.mem_normalizer_fintype
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  refine Subgroup.mem_map.2 ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg w).1 hw, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem nor_inf_cen [Finite G] {V : Subgroup G} {x g : G} (hg : g ∈ Nor V)
    (hx : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) : g ∈ Nor (V ⊓ Cen x) := by
  apply Subgroup.mem_normalizer_fintype
  intro w hw
  obtain ⟨hwV, hwx⟩ := Subgroup.mem_inf.1 hw
  have hwc : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 hwx
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hg w).1 hwV,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rcases hx with hx | hx
  · calc (g * w * g⁻¹) * x = (g * w * g⁻¹) * (g * x * g⁻¹) := by rw [hx]
      _ = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hwc]
      _ = (g * x * g⁻¹) * (g * w * g⁻¹) := by group
      _ = x * (g * w * g⁻¹) := by rw [hx]
  · have hx' : g * x⁻¹ * g⁻¹ = x := by
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group, hx, inv_inv]
    have hwc' : w * x⁻¹ = x⁻¹ * w := (Commute.inv_right (show Commute w x from hwc)).eq
    calc (g * w * g⁻¹) * x = (g * w * g⁻¹) * (g * x⁻¹ * g⁻¹) := by rw [hx']
      _ = g * (w * x⁻¹) * g⁻¹ := by group
      _ = g * (x⁻¹ * w) * g⁻¹ := by rw [hwc']
      _ = (g * x⁻¹ * g⁻¹) * (g * w * g⁻¹) := by group
      _ = x * (g * w * g⁻¹) := by rw [hx']

theorem zpow_eq_one_of_two_pow_S3 {b : G} (hb : orderOf b = 3) {k : ℤ} {n : ℕ}
    (h : (b ^ k) ^ (2 ^ n) = 1) : b ^ k = 1 := by
  rw [← zpow_natCast, ← zpow_mul] at h
  have h1 : (3 : ℤ) ∣ k * 2 ^ n := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h
    rw [hb] at this
    exact_mod_cast this
  have h3 : (3 : ℤ) ∣ k := by
    have hp : Prime (3 : ℤ) := Int.prime_three
    rcases hp.dvd_or_dvd h1 with h | h
    · exact h
    · exfalso
      have := hp.dvd_of_dvd_pow h
      omega
  exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hb]; exact_mod_cast h3)

theorem two_elt_mem_L {b : G} {L : Subgroup G} (hb : orderOf b = 3) (hbc : ∀ l ∈ L, b * l = l * b)
    (hbL : Subgroup.zpowers b ⊓ L = ⊥) {w : G} (hw : w ∈ Subgroup.zpowers b ⊔ L) {k : ℕ}
    (hk : w ^ (2 ^ k) = 1) : w ∈ L := by
  let M : Subgroup G :=
    { carrier := {x | ∃ i : ℤ, ∃ l ∈ L, x = b ^ i * l}
      mul_mem' := by
        rintro _ _ ⟨i, l, hl, rfl⟩ ⟨j, l', hl', rfl⟩
        refine ⟨i + j, l * l', mul_mem hl hl', ?_⟩
        have hc : Commute l (b ^ j) := (show Commute b l from hbc l hl).symm.zpow_right j
        rw [zpow_add]
        calc b ^ i * l * (b ^ j * l') = b ^ i * (l * b ^ j) * l' := by group
          _ = b ^ i * (b ^ j * l) * l' := by rw [hc.eq]
          _ = b ^ i * b ^ j * (l * l') := by group
      one_mem' := ⟨0, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, l, hl, rfl⟩
        refine ⟨-i, l⁻¹, inv_mem hl, ?_⟩
        have hc : Commute (b ^ i) l := ((show Commute b l from hbc l hl)).zpow_left i
        rw [mul_inv_rev, zpow_neg]
        exact hc.inv_inv.symm.eq }
  have hle : Subgroup.zpowers b ⊔ L ≤ M := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨i, 1, one_mem _, by simp⟩
    · intro l hl
      exact ⟨0, l, hl, by simp⟩
  obtain ⟨i, l, hl, rfl⟩ := hle hw
  have hc : Commute (b ^ i) l := (show Commute b l from hbc l hl).zpow_left i
  rw [hc.mul_pow, ← zpow_natCast, ← zpow_mul] at hk
  have h1 : b ^ (i * ((2 ^ k : ℕ) : ℤ)) = (l ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk
  have h2 : b ^ (i * ((2 ^ k : ℕ) : ℤ)) ∈ Subgroup.zpowers b ⊓ L :=
    Subgroup.mem_inf.2 ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _, by rw [h1]; exact inv_mem (pow_mem hl _)⟩
  rw [hbL, Subgroup.mem_bot] at h2
  have h3 : b ^ i = 1 := by
    refine zpow_eq_one_of_two_pow_S3 hb (n := k) ?_
    rw [← zpow_natCast, ← zpow_mul]
    exact h2
  rw [h3, one_mul]
  exact hl

section Ci

variable [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem F5_Ci (h : FF84Sec3 b L B b₁ b₂) (hbL : Subgroup.zpowers b ⊓ L = ⊥)
    (hCL : Subgroup.zpowers b ⊔ L = Cen b) (hCB : CenS B = B)
    {x y : G} (hxB : x ∈ B) (hBxy : B = Subgroup.closure {b, x, y})
    {n : G} (hn : n ∈ Nor B) (hn1 : n * b * n⁻¹ = x) (hn2 : n * x * n⁻¹ = b)
    (hn3 : n * y * n⁻¹ = y)
    {t : G} (htb : t * b * t⁻¹ = b⁻¹) (htx : t * x * t⁻¹ = x) (hty : t * y * t⁻¹ = y)
    (hnoY : ∀ Y : Subgroup G, Y ≤ L → IsPGroup 2 Y → B ⊓ L ≤ Nor Y → t ∈ Nor Y → Y = ⊥)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hBV : B ≤ Nor V)
    {s : G} (hs : s ∈ Nor V) (hsx : s * x * s⁻¹ = x⁻¹) (hsb : s * b * s⁻¹ = b)
    (hsy : s * y * s⁻¹ = y) : V ⊓ Cen x = ⊥ := by
  set W := V ⊓ Cen x with hW
  have hBx : ∀ c ∈ B, c * x * c⁻¹ = x := fun c hc =>
    mul_inv_eq_iff_eq_mul.2 (comm_of_mem_B h hc hxB).eq
  have hBW : B ≤ Nor W := fun c hc => nor_inf_cen (hBV hc) (Or.inl (hBx c hc))
  have hsW : s ∈ Nor W := nor_inf_cen hs (Or.inr hsx)
  have hnB : ∀ c ∈ B, n⁻¹ * c * n ∈ B := fun c hc => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) c).1 hc
    simpa using this
  have hBW' : B ≤ Nor (conjBy n W) := fun c hc => by
    have := nor_conjBy (hBW (hnB c hc)) n
    rwa [show n * (n⁻¹ * c * n) * n⁻¹ = c by group] at this
  obtain ⟨t', ht'⟩ : ∃ t' : G, t' = n * s * n⁻¹ := ⟨_, rfl⟩
  have hn1' : n⁻¹ * x * n = b := by rw [← hn1]; group
  have hn2' : n⁻¹ * b * n = x := by rw [← hn2]; group
  have hn3' : n⁻¹ * y * n = y := by
    calc n⁻¹ * y * n = n⁻¹ * (n * y * n⁻¹) * n := by rw [hn3]
      _ = y := by group
  have ht'b : t' * b * t'⁻¹ = b⁻¹ := by
    calc t' * b * t'⁻¹ = n * s * (n⁻¹ * b * n) * s⁻¹ * n⁻¹ := by rw [ht']; group
      _ = n * (s * x * s⁻¹) * n⁻¹ := by rw [hn2']; group
      _ = (n * x * n⁻¹)⁻¹ := by rw [hsx]; group
      _ = b⁻¹ := by rw [hn2]
  have ht'x : t' * x * t'⁻¹ = x := by
    calc t' * x * t'⁻¹ = n * s * (n⁻¹ * x * n) * s⁻¹ * n⁻¹ := by rw [ht']; group
      _ = n * (s * b * s⁻¹) * n⁻¹ := by rw [hn1']; group
      _ = x := by rw [hsb, hn1]
  have ht'y : t' * y * t'⁻¹ = y := by
    calc t' * y * t'⁻¹ = n * s * (n⁻¹ * y * n) * s⁻¹ * n⁻¹ := by rw [ht']; group
      _ = n * (s * y * s⁻¹) * n⁻¹ := by rw [hn3']; group
      _ = y := by rw [hsy, hn3]
  have hβ : t⁻¹ * t' ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [hBxy] at hc
    have hle : Subgroup.closure ({b, x, y} : Set G) ≤
        Subgroup.centralizer ({t⁻¹ * t'} : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (commute_inv_mul_of_conj_eq htb ht'b).symm.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (commute_inv_mul_of_conj_eq htx ht'x).symm.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (commute_inv_mul_of_conj_eq hty ht'y).symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hc)
  have hβB : t⁻¹ * t' ∈ B := by
    have := hβ
    rwa [hCB] at this
  have htW' : t ∈ Nor (conjBy n W) := by
    have h1 : t' ∈ Nor (conjBy n W) := by rw [ht']; exact nor_conjBy hsW n
    have h2 : t = t' * (t⁻¹ * t')⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem (hBW' hβB))
  have hW'c : conjBy n W ≤ Cen b := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    have hwx : w * x = x * w :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hw).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * w * n⁻¹ * b = n * w * (n⁻¹ * b * n) * n⁻¹ := by group
      _ = n * (w * x) * n⁻¹ := by rw [hn2']; group
      _ = n * (x * w) * n⁻¹ := by rw [hwx]
      _ = (n * x * n⁻¹) * (n * w * n⁻¹) := by group
      _ = b * (n * w * n⁻¹) := by rw [hn2]
  have hb3 := h.hyp.ord
  have hbc : ∀ l ∈ L, b * l = l * b := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 (P_b_mem_CenS h) l hl).symm
  have hW2 : IsPGroup 2 (conjBy n W) := isPGroup_conjBy n (hV.to_le (inf_le_left : W ≤ V))
  have hW'L : conjBy n W ≤ L := by
    intro z hz
    obtain ⟨k, hk⟩ := hW2 ⟨z, hz⟩
    refine two_elt_mem_L hb3 hbc hbL ?_ (k := k) (congrArg Subtype.val hk)
    rw [hCL]; exact hW'c hz
  have hBL : B ⊓ L ≤ Nor (conjBy n W) := inf_le_left.trans hBW'
  have hbot := hnoY (conjBy n W) hW'L hW2 hBL htW'
  rw [eq_bot_iff]
  intro w hw
  have hmem : n * w * n⁻¹ ∈ conjBy n W :=
    Subgroup.mem_map.2 ⟨w, hw, by simp [MulAut.conj_apply]⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
    _ = 1 := by rw [hmem]; group

end Ci

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
