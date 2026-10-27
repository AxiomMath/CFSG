module

public import CFSG.RankThree.PartOne.SEITZRF.Unip
public import CFSG.RankThree.PartOne.SEITZRF.LeviRatCoords

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair torusWeight
  torusWeight_apply torusExp1 torusPair_conj_pinnedX nTwo kTwo)

namespace LeviRat

section Radicals

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (K) in
abbrev V1 (a : ℕ) : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩

variable (K) in
abbrev V2 (a : ℕ) : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩

variable {a : ℕ}

theorem V1_le : V1 K a ≤ F4.reeFixedPosUnipotent K a :=
  reeFixedOrbitComplementUnipotent_le _

theorem V2_le : V2 K a ≤ F4.reeFixedPosUnipotent K a :=
  reeFixedOrbitComplementUnipotent_le _

theorem conj_mem_V1 {g x : ModGL F4.tag K} (hg : g ∈ F4.reeFixedPosUnipotent K a)
    (hx : x ∈ V1 K a) : g * x * g⁻¹ ∈ V1 K a :=
  (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer ⟨0, by decide⟩ hg) x).1 hx

theorem conj_mem_V2 {g x : ModGL F4.tag K} (hg : g ∈ F4.reeFixedPosUnipotent K a)
    (hx : x ∈ V2 K a) : g * x * g⁻¹ ∈ V2 K a :=
  (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer ⟨1, by decide⟩ hg) x).1 hx

theorem torus_conj_mem_V1 {T x : ModGL F4.tag K} (hT : T ∈ F4.reeFixedTorus K a)
    (hx : x ∈ V1 K a) : T * x * T⁻¹ ∈ V1 K a :=
  (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_complement ⟨0, by decide⟩ hT) x).1 hx

theorem torus_conj_mem_V2 {T x : ModGL F4.tag K} (hT : T ∈ F4.reeFixedTorus K a)
    (hx : x ∈ V2 K a) : T * x * T⁻¹ ∈ V2 K a :=
  (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_complement ⟨1, by decide⟩ hT) x).1 hx

end Radicals

section Parts

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem sylowA_mem_U (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s ∈ F4.reeFixedPosUnipotent K a :=
  reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK s)

theorem sylowB_mem_U (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c : K) :
    sylowB a K b c ∈ F4.reeFixedPosUnipotent K a :=
  reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK b c)

theorem exists_conj_sylowA_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) {u w : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (hw : w ∈ V1 K a) (s : K) :
    ∃ w' ∈ V1 K a, u * (sylowA a K s * w) * u⁻¹ = sylowA a K s * w' := by
  obtain ⟨z, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
  rw [sylowVec_eq_sylowA_mul]
  obtain ⟨n, hn, hn'⟩ := exists_conj_eq_mul (reeFixedPosUnipotent_le_normalizer ⟨0, by decide⟩)
    (sylowA_mem_U hK (z 0)) (sylowA_mem_U hK s)
    (sylowV_zero_mem_complement hK (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10)
      (z 11)) hw (by rw [sylowA_mul hK, sylowA_mul hK, add_comm])
  exact ⟨n, hn, hn'⟩

theorem exists_mul_sylowA_of_mem {w₁ w₂ : ModGL F4.tag K} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hw₁ : w₁ ∈ V1 K a) (hw₂ : w₂ ∈ V1 K a) (s : K) :
    ∃ w ∈ V1 K a, w₁ * sylowA a K s * w₂ = sylowA a K s * w := by
  refine ⟨(sylowA a K s)⁻¹ * w₁ * sylowA a K s * w₂, mul_mem ?_ hw₂, by group⟩
  have := conj_mem_V1 (inv_mem (sylowA_mem_U hK s)) hw₁
  rwa [inv_inv] at this

theorem map_eq_self_of_sylowA_mul_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {w : ModGL F4.tag K} (hw : w ∈ V1 K a) {s : K} (h : sylowA a K s * w ∈ Rf K a β) :
    β s = s := by
  have hgU : sylowA a K s * w ∈ F4.reeFixedPosUnipotent K a :=
    mul_mem (sylowA_mem_U hK s) (V1_le hw)
  obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 hgU
  have h0 : y 0 = s := coord_zero_eq hK hw hy
  have h' : sylowVec a K y ∈ Rf K a β := by rw [hy]; exact h
  have := (sylowVec_mem_Rf_iff hK β y).1 h' 0
  rwa [h0] at this

theorem sylowB_mul_sylowB (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c b' c' : K) :
    sylowB a K b c * sylowB a K b' c' =
      sylowB a K (b + b') (c + c' + largeReeSigma a b * b') := by
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact largeReeCoord_mul hK b c b' c'

theorem exists_conj_sylowB_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) {u w : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (hw : w ∈ V2 K a) (b c : K) :
    ∃ c', ∃ w' ∈ V2 K a, u * (sylowB a K b c * w) * u⁻¹ = sylowB a K b c' * w' := by
  obtain ⟨z, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
  obtain ⟨nz, hnz, hz⟩ := exists_sylowVec_eq_sylowB_mul hK z
  rw [hz]
  have hBw := sylowB_mem_U hK b c
  have hBu := sylowB_mem_U hK (z 1) (z 2)
  have hn : sylowB a K (z 1) (z 2) * (((sylowB a K b c)⁻¹ * nz * sylowB a K b c) * w * nz⁻¹) *
      (sylowB a K (z 1) (z 2))⁻¹ ∈ V2 K a := by
    refine conj_mem_V2 hBu (mul_mem (mul_mem ?_ hw) (inv_mem hnz))
    have := conj_mem_V2 (inv_mem hBw) hnz
    rwa [inv_inv] at this
  have e : sylowB a K (z 1) (z 2) * nz * (sylowB a K b c * w) *
      (sylowB a K (z 1) (z 2) * nz)⁻¹ =
      (sylowB a K (z 1) (z 2) * sylowB a K b c * (sylowB a K (z 1) (z 2))⁻¹) *
        (sylowB a K (z 1) (z 2) * (((sylowB a K b c)⁻¹ * nz * sylowB a K b c) * w * nz⁻¹) *
          (sylowB a K (z 1) (z 2))⁻¹) := by group
  rw [e]
  have hmem : sylowB a K (z 1) (z 2) * sylowB a K b c * (sylowB a K (z 1) (z 2))⁻¹ ∈
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ :=
    mul_mem (mul_mem (sylowB_mem_U2 hK _ _) (sylowB_mem_U2 hK _ _))
      (inv_mem (sylowB_mem_U2 hK _ _))
  obtain ⟨b'', c'', hbc⟩ := exists_largeReeCoord_eq hK hmem
  rw [← sylowB_eq_largeReeCoord] at hbc
  refine ⟨c'', _, hn, ?_⟩
  have hb : b'' = b := by
    have h1 : sylowB a K b'' c'' * sylowB a K (z 1) (z 2) =
        sylowB a K (z 1) (z 2) * sylowB a K b c := by
      rw [hbc]; group
    rw [sylowB_mul_sylowB hK, sylowB_mul_sylowB hK] at h1
    have := (sylowB_injective hK h1).1
    rw [add_comm b'' (z 1)] at this
    exact add_left_cancel this
  rw [← hbc, hb]

theorem exists_conj_sylowA (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (s : K) :
    ∃ w ∈ V1 K a, u * sylowA a K s * u⁻¹ = sylowA a K s * w := by
  obtain ⟨w, hw, e⟩ := exists_conj_sylowA_mul hK hu (one_mem _) s
  exact ⟨w, hw, by simpa only [mul_one] using e⟩

theorem map_eq_self_of_sylowB_mul_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {w : ModGL F4.tag K} (hw : w ∈ V2 K a) {b c : K} (h : sylowB a K b c * w ∈ Rf K a β) :
    β b = b ∧ β c = c := by
  have hgU : sylowB a K b c * w ∈ F4.reeFixedPosUnipotent K a :=
    mul_mem (sylowB_mem_U hK b c) (V2_le hw)
  obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 hgU
  obtain ⟨h1, h2⟩ := coord_one_two_eq hK hw hy
  have h' : sylowVec a K y ∈ Rf K a β := by rw [hy]; exact h
  have hr := (sylowVec_mem_Rf_iff hK β y).1 h'
  have e1 := hr 1
  have e2 := hr 2
  rw [h1] at e1
  rw [h2] at e2
  exact ⟨e1, e2⟩

theorem exists_mul_sylowB_of_mem {w₁ w₂ : ModGL F4.tag K} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hw₁ : w₁ ∈ V2 K a) (hw₂ : w₂ ∈ V2 K a) (b c : K) :
    ∃ w ∈ V2 K a, w₁ * sylowB a K b c * w₂ = sylowB a K b c * w := by
  refine ⟨(sylowB a K b c)⁻¹ * w₁ * sylowB a K b c * w₂, mul_mem ?_ hw₂, by group⟩
  have := conj_mem_V2 (inv_mem (sylowB_mem_U hK b c)) hw₁
  rwa [inv_inv] at this

end Parts

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] in
theorem eq_of_map_pow_two_pow_eq (β : K ≃+* K) (n : ℕ) {x : K} (h : β (x ^ 2 ^ n) = x ^ 2 ^ n) :
    β x = x := by
  rw [map_pow] at h
  have hinj : Function.Injective (fun y : K => y ^ 2 ^ n) := by
    have : CharP K 2 := ‹CharP K F4.prime›
    intro y z hyz
    have h' : (y - z) ^ 2 ^ n = 0 := by
      rw [sub_pow_char_pow, sub_eq_zero]
      exact hyz
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h')
  exact hinj h

omit [Finite K] [CharP K F4.prime] in
theorem coe_zpow_neg_two_pow (μ : Kˣ) (a : ℕ) :
    ((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) = ((μ : K) ^ 2 ^ a)⁻¹ := by
  rw [zpow_neg, show ((2 : ℤ) ^ a) = ((2 ^ a : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

omit [Finite K] in
theorem map_eq_self_of_zpow_neg (β : K ≃+* K) {μ : Kˣ}
    (h : β ((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) = ((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K)) : β (μ : K) = μ := by
  rw [coe_zpow_neg_two_pow, map_inv₀] at h
  exact eq_of_map_pow_two_pow_eq β a (inv_injective h)

omit [Finite K] [CharP K F4.prime] in
theorem pairedTorusHom_mem_fixGL (β : K ≃+* K) {u : Kˣ} (hu : β u = u) (j l : Fin F4.tag.rank) :
    pairedTorusHom a j l u ∈ fixGL K β := by
  rw [mem_fixGL, pairedTorusHom_apply, map_mul, entrywise_torusElt, entrywise_torusElt]
  have h1 : Units.map β.toRingHom.toMonoidHom u = u := Units.ext hu
  have h2 : Units.map β.toRingHom.toMonoidHom (u ^ 2 ^ a) = u ^ 2 ^ a := by rw [map_pow, h1]
  rw [h1, h2]

theorem torusOne_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {u : Kˣ}
    (hu : β u = u) : pairedTorusHom a (f4i 0) (f4i 3) u ∈ Rf K a β :=
  ⟨reeFixedTorus_le_reeGamma' (rankOneTorusOne_le hK ⟨u, rfl⟩), pairedTorusHom_mem_fixGL β hu _ _⟩

theorem torusTwo_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {u : Kˣ}
    (hu : β u = u) : pairedTorusHom a (f4i 1) (f4i 2) u ∈ Rf K a β :=
  ⟨reeFixedTorus_le_reeGamma' (rankOneTorusTwo_le hK ⟨u, rfl⟩), pairedTorusHom_mem_fixGL β hu _ _⟩

omit [CharP K F4.prime] in
theorem torusTwo_conj_sylowA (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u : Kˣ) (c : K) :
    pairedTorusHom a (f4i 1) (f4i 2) u * sylowA a K c * (pairedTorusHom a (f4i 1) (f4i 2) u)⁻¹ =
      sylowA a K (((u⁻¹ : Kˣ) : K) ^ 2 ^ a * c) := by
  obtain ⟨⟨-, h1, h2, -⟩, ⟨-, h1', h2', -⟩, -⟩ := cartanPair_A_B
  have w24 : ((torusWeight a (RootOps.orbitCertRoot F4.tag 24) (1, u) : Kˣ) : K) =
      ((u⁻¹ : Kˣ) : K) ^ 2 ^ a := by
    rw [torusWeight_apply, one_zpow, one_mul, ← Units.val_pow_eq_pow_val, inv_pow,
      ← zpow_natCast, ← zpow_neg]
    simp only [torusExp1]
    rw [h1, h2]
    push_cast
    ring_nf
  have w33 : ((torusWeight a (RootOps.orbitCertRoot F4.tag 33) (1, u) : Kˣ) : K) =
      largeReeSigma a (((u⁻¹ : Kˣ) : K) ^ 2 ^ a) := by
    rw [torusWeight_apply, one_zpow, one_mul, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← pow_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    simp only [torusExp1]
    rw [h1', h2']
    congr 1
    refine units_zpow_congr hK u 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * a + 1)) = 2 * (2 ^ a) ^ 2 by ring]
    ring
  rw [← rankOneTorusPair_right, sylowA, sylowA, sylowX, sylowX, sylowX, sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX a (1, u) (sylowRoot_pos (r := 24) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a (1, u) (sylowRoot_pos (r := 33) (by norm_num) (by norm_num)).1,
    w24, w33, largeReeSigma_mul]

end Torus

section Cells

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem nTwo_zero : nTwo K 0 = 1 := by
  have h : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl
  rw [nTwo, show kTwo 0 = ⟨0, by decide⟩ from rfl, h, canonicalRep_one]

theorem largeReeA1Hom_uSL_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    largeReeA1Hom K a (uSL c) = sylowA a K (c ^ 2 ^ a) := by
  rw [largeReeA1Hom_uSL, sylowA_eq, twoCoordG, nTwo_zero, one_mul, inv_one, mul_one,
    stdTwoG_eq_xUnit, largeReeSigma_pow hK]

omit [Finite K] in
theorem largeReeA1Hom_WSL_eq : largeReeA1Hom K a WSL = weylOne K := by
  change largeReeA1Hom K a WSL =
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)
  rw [largeReeA1Hom_WSL, canonicalRep_F4_fixedOrbitElement_zero]

theorem rankOneGroupOne_cells (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ModGL F4.tag K}
    (hr : r ∈ rankOneGroupOne K a) :
    (∃ (μ : Kˣ) (s : K), r = pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s) ∨
      ∃ (s₁ : K) (μ : Kˣ) (s₂ : K), r = sylowA a K s₁ * pairedTorusHom a (f4i 0) (f4i 3) μ *
        weylOne K * sylowA a K s₂ := by
  rw [rankOneGroupOne_eq_range hK] at hr
  obtain ⟨g, rfl⟩ := hr
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · obtain ⟨t, c, rfl⟩ : ∃ (t : Kˣ) (c : K), g = HSL t * uSL c := ⟨_, _, eq_HSL_mul_uSL hc⟩
    left
    exact ⟨t, c ^ 2 ^ a, by
      rw [map_mul, ← pairedTorusHom_eq_largeReeA1Hom, largeReeA1Hom_uSL_eq hK]⟩
  · obtain ⟨c₁, t, c₂, rfl⟩ : ∃ (c₁ : K) (t : Kˣ) (c₂ : K),
        g = uSL c₁ * HSL t * WSL * uSL c₂ :=
      ⟨_, _, _, eq_uSL_mul_HSL_mul_WSL_mul_uSL hc⟩
    right
    exact ⟨c₁ ^ 2 ^ a, t, c₂ ^ 2 ^ a, by
      rw [map_mul, map_mul, map_mul, ← pairedTorusHom_eq_largeReeA1Hom, largeReeA1Hom_uSL_eq hK,
        largeReeA1Hom_uSL_eq hK, largeReeA1Hom_WSL_eq]⟩

theorem rankOneGroupTwo_cells (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {r : ModGL F4.tag K} (hr : r ∈ rankOneGroupTwo K a) :
    (∃ (ν : Kˣ) (b c : K), r = pairedTorusHom a (f4i 1) (f4i 2) ν * sylowB a K b c) ∨
      ∃ (ν : Kˣ) (b c b' c' : K), r = pairedTorusHom a (f4i 1) (f4i 2) ν * sylowB a K b c *
        weylTwo K * sylowB a K b' c' := by
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  rw [rankOneGroupTwo_eq_map hK'] at hr
  obtain ⟨g, hg, rfl⟩ := hr
  have hT : ∀ t ∈ CFSG.SectionRank.LargeRee.blockT a hK' 1,
      ∃ ν : Kˣ, reeFixedEmb K a t = pairedTorusHom a (f4i 1) (f4i 2) ν := fun t ht => by
    have h : reeFixedEmb K a t ∈ rankOneTorusTwo K a := by
      rw [← map_blockT_one hK']
      exact Subgroup.mem_map_of_mem _ ht
    obtain ⟨ν, hν⟩ := h
    exact ⟨ν, hν.symm⟩
  have hX : ∀ y ∈ CFSG.SectionRank.LargeRee.blockX (K := K) a 1,
      ∃ b c : K, reeFixedEmb K a y = sylowB a K b c := fun y hy => by
    have h : reeFixedEmb K a y ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
      rw [← map_blockX_one]
      exact Subgroup.mem_map_of_mem _ hy
    obtain ⟨b, c, hbc⟩ := exists_largeReeCoord_eq hK h
    exact ⟨b, c, by rw [sylowB_eq_largeReeCoord, hbc]⟩
  rcases CFSG.SectionRank.LargeRee.r2_cells hK' ha hg with
    ⟨t, ht, y, hy, rfl⟩ | ⟨t, ht, y, hy, y', hy', rfl⟩
  · left
    obtain ⟨ν, hν⟩ := hT t ht
    obtain ⟨b, c, hb⟩ := hX y hy
    exact ⟨ν, b, c, by rw [map_mul, hν, hb]⟩
  · right
    obtain ⟨ν, hν⟩ := hT t ht
    obtain ⟨b, c, hb⟩ := hX y hy
    obtain ⟨b', c', hb'⟩ := hX y' hy'
    exact ⟨ν, b, c, b', c', by
      rw [map_mul, map_mul, map_mul, hν, hb, hb', reeFixedEmb_relNrepHom_one]⟩

end Cells

section MainOne

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem sylowH_zero_mem_U (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : K) :
    sylowH a K 0 i ∈ F4.reeFixedPosUnipotent K a := by
  rw [Unip.sylowH_eq_sylowV]
  exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _

theorem map_eq_self_of_A (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β)
    {g w : ModGL F4.tag K} (hgH : g ∈ H) (hw : w ∈ V1 K a) {s : K} (hg : g = sylowA a K s * w) :
    β s = s := by
  subst hg
  exact map_eq_self_of_sylowA_mul_mem hK β hw
    (hU ⟨hgH, mul_mem (sylowA_mem_U hK s) (V1_le hw)⟩)

theorem map_eq_self_of_B (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β)
    {g w : ModGL F4.tag K} (hgH : g ∈ H) (hw : w ∈ V2 K a) {b c : K}
    (hg : g = sylowB a K b c * w) : β b = b ∧ β c = c := by
  subst hg
  exact map_eq_self_of_sylowB_mul_mem hK β hw
    (hU ⟨hgH, mul_mem (sylowB_mem_U hK b c) (V2_le hw)⟩)

theorem Y1_borel (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) {v : ModGL F4.tag K} (hv : v ∈ V1 K a)
    {μ : Kˣ} {s : K}
    (h : v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s) ∈ H) :
    pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s ∈ Rf K a β := by
  have hvU : v ∈ F4.reeFixedPosUnipotent K a := V1_le hv
  have hz : sylowH a K 0 1 ∈ H :=
    hRH ((Unip.sylowH_mem_Rf_iff hK β 0 1).2 ⟨map_zero β, map_one β⟩)
  have hzc : ∀ {g : ModGL F4.tag K}, g ∈ F4.reeFixedPosUnipotent K a → ∀ i : K,
      g * sylowH a K 0 i = sylowH a K 0 i * g := fun hg i => by
    rw [sylowH_zero_eq_centralZ]
    exact commute_centralZ ha hK hg i
  have hμ : β (μ : K) = μ := by
    have h1 : (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s)) * sylowH a K 0 1 *
        (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem h hz) (H.inv_mem h)
    have e : (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s)) * sylowH a K 0 1 *
        (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s))⁻¹ =
        sylowH a K 0 ((μ : K) ^ 2 ^ a * 1) := by
      calc (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s)) * sylowH a K 0 1 *
            (v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s))⁻¹ =
          v * (pairedTorusHom a (f4i 0) (f4i 3) μ * (sylowA a K s * sylowH a K 0 1 *
            (sylowA a K s)⁻¹) * (pairedTorusHom a (f4i 0) (f4i 3) μ)⁻¹) * v⁻¹ := by group
        _ = v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowH a K 0 1 *
            (pairedTorusHom a (f4i 0) (f4i 3) μ)⁻¹) * v⁻¹ := by
          rw [hzc (sylowA_mem_U hK s), mul_inv_cancel_right]
        _ = v * sylowH a K 0 ((μ : K) ^ 2 ^ a * 1) * v⁻¹ := by rw [torusOne_conj_sylowH hK]
        _ = sylowH a K 0 ((μ : K) ^ 2 ^ a * 1) := by rw [hzc hvU, mul_inv_cancel_right]
    rw [e] at h1
    have hr := hU ⟨h1, sylowH_zero_mem_U hK _⟩
    have := ((Unip.sylowH_mem_Rf_iff hK β 0 _).1 hr).2
    rw [mul_one] at this
    exact eq_of_map_pow_two_pow_eq β a this
  have hT : pairedTorusHom a (f4i 0) (f4i 3) μ ∈ Rf K a β := torusOne_mem_Rf hK β hμ
  have hx : v * sylowA a K (largeReeSigma a (μ : K) * s) ∈ H := by
    have h1 := H.mul_mem h (H.inv_mem (hRH hT))
    have e : v * (pairedTorusHom a (f4i 0) (f4i 3) μ * sylowA a K s) *
        (pairedTorusHom a (f4i 0) (f4i 3) μ)⁻¹ =
        v * sylowA a K (largeReeSigma a (μ : K) * s) := by
      rw [← torusOne_conj_sylowA hK]
      group
    rwa [e] at h1
  obtain ⟨w, hw, hvw⟩ := exists_mul_sylowA_of_mem hK hv (one_mem _)
    (largeReeSigma a (μ : K) * s)
  rw [mul_one] at hvw
  have hs := map_eq_self_of_A hK β hU hx hw hvw
  rw [map_mul, map_largeReeSigma, hμ] at hs
  have hσ : largeReeSigma a (μ : K) ≠ 0 :=
    (largeReeSigma_eq_zero_iff _).not.2 (Units.ne_zero μ)
  have hs' : β s = s := mul_left_cancel₀ hσ hs
  exact mul_mem hT ((Unip.sylowA_mem_Rf_iff hK β s).2 hs')

variable (a) in
abbrev T1 (μ : Kˣ) : ModGL F4.tag K := pairedTorusHom a (f4i 0) (f4i 3) μ

variable (a) in
abbrev T2 (ν : Kˣ) : ModGL F4.tag K := pairedTorusHom a (f4i 1) (f4i 2) ν

theorem Y1_bigcell (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) {v : ModGL F4.tag K} (hv : v ∈ V1 K a)
    {s₁ s₂ : K} {μ : Kˣ}
    (h : v * (sylowA a K s₁ * T1 a μ * weylOne K * sylowA a K s₂) ∈ H) :
    sylowA a K s₁ * T1 a μ * weylOne K * sylowA a K s₂ ∈ Rf K a β := by
  have hn : weylOne K ∈ H := hRH (weylOne_mem_Rf β)
  have hTt : T1 a μ ∈ F4.reeFixedTorus K a := torusOne_mem hK μ
  obtain ⟨u, hudef⟩ : ∃ u, u = v * sylowA a K s₁ := ⟨_, rfl⟩
  have hu : u ∈ F4.reeFixedPosUnipotent K a := hudef ▸ mul_mem (V1_le hv) (sylowA_mem_U hK s₁)
  have hx : u * T1 a μ * weylOne K * sylowA a K s₂ ∈ H := by
    have e : v * (sylowA a K s₁ * T1 a μ * weylOne K * sylowA a K s₂) =
        u * T1 a μ * weylOne K * sylowA a K s₂ := by rw [hudef]; group
    rwa [e] at h
  have hmemH : ∀ Y ∈ Rf K a β, u * (T1 a μ * (weylOne K * (sylowA a K s₂ * Y *
      (sylowA a K s₂)⁻¹) * (weylOne K)⁻¹) * (T1 a μ)⁻¹) * u⁻¹ ∈ H := fun Y hY => by
    have e : u * T1 a μ * weylOne K * sylowA a K s₂ * Y *
        (u * T1 a μ * weylOne K * sylowA a K s₂)⁻¹ =
        u * (T1 a μ * (weylOne K * (sylowA a K s₂ * Y * (sylowA a K s₂)⁻¹) * (weylOne K)⁻¹) *
          (T1 a μ)⁻¹) * u⁻¹ := by group
    rw [← e]
    exact H.mul_mem (H.mul_mem hx (hRH hY)) (H.inv_mem hx)
  have hW : β ((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) = ((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) := by
    have hD : sylowD a K 1 0 ∈ Rf K a β :=
      (Unip.sylowD_mem_Rf_iff hK β 1 0).2 ⟨map_one β, map_zero β⟩
    have h1 := hmemH _ hD
    rw [(sylowA_commute_sylowD s₂ 1 0).eq, mul_inv_cancel_right, Unip.weylOne_conj_sylowD_full,
      torusOne_conj_sylowB_gen hK] at h1
    obtain ⟨c', w', hw', e⟩ := exists_conj_sylowB_mul hK hu (one_mem _)
      (((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) * 1) (((μ ^ ((-1 : ℤ) - 2 ^ a) : Kˣ) : K) * 0)
    rw [mul_one] at e
    rw [e] at h1
    have := (map_eq_self_of_B hK β hU h1 hw' rfl).1
    rwa [mul_one] at this
  have hμ : β (μ : K) = μ := map_eq_self_of_zpow_neg β hW
  have hT : T1 a μ ∈ Rf K a β := torusOne_mem_Rf hK β hμ
  have hs₂ : β s₂ = s₂ := by
    have hB : sylowB a K 1 0 ∈ Rf K a β :=
      (Unip.sylowB_mem_Rf_iff hK β 1 0).2 ⟨map_one β, map_zero β⟩
    have h1 := hmemH _ hB
    rw [sylowA_mul_sylowB_one_mul_inv hK] at h1
    have hV : sylowV a K 0 1 0 s₂ 0 s₂ 0 0 0 s₂ (s₂ * largeReeSigma a s₂) 0 =
        sylowB a K 1 0 * sylowD a K s₂ 0 * sylowF a K s₂ 0 * sylowJ a K s₂ *
          sylowK a K (s₂ * largeReeSigma a s₂) := by
      simp [sylowV, sylowA_zero, sylowH, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]
    rw [hV] at h1
    have hn1 : weylOne K * (sylowB a K 1 0 * sylowD a K s₂ 0 * sylowF a K s₂ 0 *
        sylowJ a K s₂ * sylowK a K (s₂ * largeReeSigma a s₂)) * (weylOne K)⁻¹ =
        sylowD a K 1 0 * sylowB a K s₂ 0 * sylowH a K s₂ 0 * sylowK a K s₂ *
          sylowJ a K (s₂ * largeReeSigma a s₂) := by
      simp only [weyl_conj_mul, Unip.weylOne_conj_sylowB_full, Unip.weylOne_conj_sylowD_full,
        Unip.weylOne_conj_sylowF_full, weylOne_conj_sylowJ, weylOne_conj_sylowK]
    rw [hn1] at h1
    obtain ⟨w, hw, e1⟩ := exists_mul_sylowB_of_mem hK
      (w₁ := sylowD a K 1 0) (w₂ := sylowH a K s₂ 0 * sylowK a K s₂ *
        sylowJ a K (s₂ * largeReeSigma a s₂)) (Unip.sylowD_mem_complement_one hK 1 0)
      (mul_mem (mul_mem (Unip.sylowH_mem_complement_one hK _ _)
        (Unip.sylowK_mem_complement_one hK _)) (Unip.sylowJ_mem_complement_one hK _)) s₂ 0
    have e2 : sylowD a K 1 0 * sylowB a K s₂ 0 * sylowH a K s₂ 0 * sylowK a K s₂ *
        sylowJ a K (s₂ * largeReeSigma a s₂) = sylowD a K 1 0 * sylowB a K s₂ 0 *
          (sylowH a K s₂ 0 * sylowK a K s₂ * sylowJ a K (s₂ * largeReeSigma a s₂)) := by
      simp only [mul_assoc]
    have hT1 : T1 a μ * (sylowB a K s₂ 0 * w) * (T1 a μ)⁻¹ =
        sylowB a K (((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) * s₂)
          (((μ ^ ((-1 : ℤ) - 2 ^ a) : Kˣ) : K) * 0) * (T1 a μ * w * (T1 a μ)⁻¹) := by
      rw [weyl_conj_mul, torusOne_conj_sylowB_gen hK]
    rw [e2, e1, hT1] at h1
    obtain ⟨c', w', hw', e⟩ := exists_conj_sylowB_mul hK hu (torus_conj_mem_V2 hTt hw)
      (((μ ^ (-(2 : ℤ) ^ a) : Kˣ) : K) * s₂) (((μ ^ ((-1 : ℤ) - 2 ^ a) : Kˣ) : K) * 0)
    rw [e] at h1
    have h2 := (map_eq_self_of_B hK β hU h1 hw' rfl).1
    rw [map_mul, hW] at h2
    exact mul_left_cancel₀ (Units.ne_zero _) h2
  have hA₂ : sylowA a K s₂ ∈ Rf K a β := (Unip.sylowA_mem_Rf_iff hK β s₂).2 hs₂
  have huH : u ∈ H := by
    have e : u * T1 a μ * weylOne K * sylowA a K s₂ * (sylowA a K s₂)⁻¹ * (weylOne K)⁻¹ *
        (T1 a μ)⁻¹ = u := by group
    rw [← e]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx (H.inv_mem (hRH hA₂))) (H.inv_mem hn))
      (H.inv_mem (hRH hT))
  obtain ⟨w, hw, hvw⟩ := exists_mul_sylowA_of_mem hK hv (one_mem _) s₁
  rw [mul_one] at hvw
  have hs₁ : β s₁ = s₁ := map_eq_self_of_A hK β hU huH hw (hudef.trans hvw)
  exact mul_mem (mul_mem (mul_mem ((Unip.sylowA_mem_Rf_iff hK β s₁).2 hs₁) hT)
    (weylOne_mem_Rf β)) hA₂

end MainOne

section MainTwo

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem exists_torus_conj_sylowB (hK : Nat.card K = 2 ^ (2 * a + 1)) {T : ModGL F4.tag K}
    (hT : T ∈ F4.reeFixedTorus K a) (b c : K) :
    ∃ b₁ c₁ : K, T * sylowB a K b c * T⁻¹ = sylowB a K b₁ c₁ := by
  have hmem : T * sylowB a K b c * T⁻¹ ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ :=
    (Subgroup.mem_normalizer_iff.1
      (reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent ⟨1, by decide⟩ hT) _).1
      (sylowB_mem_U2 hK b c)
  obtain ⟨b₁, c₁, h⟩ := exists_largeReeCoord_eq hK hmem
  exact ⟨b₁, c₁, by rw [sylowB_eq_largeReeCoord b₁ c₁]; exact h.symm⟩

omit [Finite K] [CharP K F4.prime] in
theorem map_inv_pow_eq_self (β : K ≃+* K) {ν : Kˣ} (hν : β (ν : K) = ν) :
    β (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a) = ((ν⁻¹ : Kˣ) : K) ^ 2 ^ a := by
  rw [map_pow, Units.val_inv_eq_inv_val, map_inv₀, hν]

omit [Finite K] in
theorem map_eq_self_of_inv_pow (β : K ≃+* K) {ν : Kˣ}
    (h : β (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * 1) = ((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * 1) : β (ν : K) = ν := by
  rw [mul_one] at h
  have h' := eq_of_map_pow_two_pow_eq β a h
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h'
  exact inv_injective h'

theorem Y2_borel (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) {v : ModGL F4.tag K} (hv : v ∈ V2 K a)
    {ν : Kˣ} {b c : K} (h : v * (T2 a ν * sylowB a K b c) ∈ H) :
    T2 a ν * sylowB a K b c ∈ Rf K a β := by
  have hvU : v ∈ F4.reeFixedPosUnipotent K a := V2_le hv
  have hTt : T2 a ν ∈ F4.reeFixedTorus K a := torusTwo_mem hK ν
  have hA1 : sylowA a K 1 ∈ H := hRH ((Unip.sylowA_mem_Rf_iff hK β 1).2 (map_one β))
  have hν : β (ν : K) = ν := by
    have h1 : (v * (T2 a ν * sylowB a K b c)) * sylowA a K 1 *
        (v * (T2 a ν * sylowB a K b c))⁻¹ ∈ H := H.mul_mem (H.mul_mem h hA1) (H.inv_mem h)
    have e : (v * (T2 a ν * sylowB a K b c)) * sylowA a K 1 *
        (v * (T2 a ν * sylowB a K b c))⁻¹ =
        v * (T2 a ν * (sylowB a K b c * sylowA a K 1 * (sylowB a K b c)⁻¹) * (T2 a ν)⁻¹) *
          v⁻¹ := by group
    rw [e] at h1
    obtain ⟨w₁, hw₁, e₁⟩ := exists_conj_sylowA hK (sylowB_mem_U hK b c) 1
    rw [e₁] at h1
    have e₂ : T2 a ν * (sylowA a K 1 * w₁) * (T2 a ν)⁻¹ =
        sylowA a K (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * 1) * (T2 a ν * w₁ * (T2 a ν)⁻¹) := by
      rw [weyl_conj_mul, torusTwo_conj_sylowA hK]
    rw [e₂] at h1
    obtain ⟨w₂, hw₂, e₃⟩ := exists_conj_sylowA_mul hK hvU (torus_conj_mem_V1 hTt hw₁)
      (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * 1)
    rw [e₃] at h1
    exact map_eq_self_of_inv_pow β (map_eq_self_of_A hK β hU h1 hw₂ rfl)
  have hT : T2 a ν ∈ Rf K a β := torusTwo_mem_Rf hK β hν
  obtain ⟨b₁, c₁, hB₁⟩ := exists_torus_conj_sylowB hK hTt b c
  have hx : v * sylowB a K b₁ c₁ ∈ H := by
    have h1 := H.mul_mem h (H.inv_mem (hRH hT))
    have e : v * (T2 a ν * sylowB a K b c) * (T2 a ν)⁻¹ = v * sylowB a K b₁ c₁ := by
      rw [← hB₁]
      group
    rwa [e] at h1
  obtain ⟨w, hw, hvw⟩ := exists_mul_sylowB_of_mem hK hv (one_mem _) b₁ c₁
  rw [mul_one] at hvw
  obtain ⟨hb₁, hc₁⟩ := map_eq_self_of_B hK β hU hx hw hvw
  have hB₁R : sylowB a K b₁ c₁ ∈ Rf K a β := (Unip.sylowB_mem_Rf_iff hK β b₁ c₁).2 ⟨hb₁, hc₁⟩
  have e : T2 a ν * sylowB a K b c = sylowB a K b₁ c₁ * T2 a ν := by
    rw [← hB₁]
    group
  rw [e]
  exact mul_mem hB₁R hT

theorem Y2_bigcell (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) {v : ModGL F4.tag K} (hv : v ∈ V2 K a)
    {ν : Kˣ} {b c b' c' : K}
    (h : v * (T2 a ν * sylowB a K b c * weylTwo K * sylowB a K b' c') ∈ H) :
    T2 a ν * sylowB a K b c * weylTwo K * sylowB a K b' c' ∈ Rf K a β := by
  have hn : weylTwo K ∈ H := hRH (weylTwo_mem_Rf β)
  have hTt : T2 a ν ∈ F4.reeFixedTorus K a := torusTwo_mem hK ν
  obtain ⟨b₁, c₁, hB₁⟩ := exists_torus_conj_sylowB hK hTt b c
  obtain ⟨u, hudef⟩ : ∃ u, u = v * sylowB a K b₁ c₁ := ⟨_, rfl⟩
  have hu : u ∈ F4.reeFixedPosUnipotent K a :=
    hudef ▸ mul_mem (V2_le hv) (sylowB_mem_U hK b₁ c₁)
  have hx : u * T2 a ν * weylTwo K * sylowB a K b' c' ∈ H := by
    have e : v * (T2 a ν * sylowB a K b c * weylTwo K * sylowB a K b' c') =
        u * T2 a ν * weylTwo K * sylowB a K b' c' := by
      rw [hudef, ← hB₁]
      group
    rwa [e] at h
  have hmemH : ∀ Y ∈ Rf K a β, u * (T2 a ν * (weylTwo K * (sylowB a K b' c' * Y *
      (sylowB a K b' c')⁻¹) * (weylTwo K)⁻¹) * (T2 a ν)⁻¹) * u⁻¹ ∈ H := fun Y hY => by
    have e : u * T2 a ν * weylTwo K * sylowB a K b' c' * Y *
        (u * T2 a ν * weylTwo K * sylowB a K b' c')⁻¹ =
        u * (T2 a ν * (weylTwo K * (sylowB a K b' c' * Y * (sylowB a K b' c')⁻¹) *
          (weylTwo K)⁻¹) * (T2 a ν)⁻¹) * u⁻¹ := by group
    rw [← e]
    exact H.mul_mem (H.mul_mem hx (hRH hY)) (H.inv_mem hx)
  have hAj : ∀ {j : K} {y : ModGL F4.tag K}, y ∈ Rf K a β →
      (∃ w₁ ∈ V1 K a, ∃ w₂ ∈ V1 K a, weylTwo K * (sylowB a K b' c' * y *
        (sylowB a K b' c')⁻¹) * (weylTwo K)⁻¹ = w₁ * sylowA a K j * w₂) →
      β (ν : K) = ν → β j = j := by
    intro j y hy ⟨w₁, hw₁, w₂, hw₂, e⟩ hν
    have h1 := hmemH y hy
    rw [e] at h1
    obtain ⟨w, hw, e1⟩ := exists_mul_sylowA_of_mem hK hw₁ hw₂ j
    rw [e1] at h1
    have hT1 : T2 a ν * (sylowA a K j * w) * (T2 a ν)⁻¹ =
        sylowA a K (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * j) * (T2 a ν * w * (T2 a ν)⁻¹) := by
      rw [weyl_conj_mul, torusTwo_conj_sylowA hK]
    rw [hT1] at h1
    obtain ⟨w', hw', e'⟩ := exists_conj_sylowA_mul hK hu (torus_conj_mem_V1 hTt hw)
      (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * j)
    rw [e'] at h1
    have h2 := map_eq_self_of_A hK β hU h1 hw' rfl
    rw [map_mul, map_inv_pow_eq_self β hν] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (Units.ne_zero _)) h2
  have hν : β (ν : K) = ν := by
    have hJ : sylowJ a K 1 ∈ Rf K a β := (Unip.sylowJ_mem_Rf_iff hK β 1).2 (map_one β)
    have h1 := hmemH _ hJ
    rw [(sylowB_commute_sylowJ b' c' 1).eq, mul_inv_cancel_right, weylTwo_conj_sylowJ,
      torusTwo_conj_sylowA hK] at h1
    obtain ⟨w₂, hw₂, e₃⟩ := exists_conj_sylowA hK hu (((ν⁻¹ : Kˣ) : K) ^ 2 ^ a * 1)
    rw [e₃] at h1
    exact map_eq_self_of_inv_pow β (map_eq_self_of_A hK β hU h1 hw₂ rfl)
  have hT : T2 a ν ∈ Rf K a β := torusTwo_mem_Rf hK β hν
  have hb' : β b' = b' := by
    have hF : sylowF a K 1 0 ∈ Rf K a β :=
      (Unip.sylowF_mem_Rf_iff hK β 1 0).2 ⟨map_one β, map_zero β⟩
    refine hAj (y := sylowF a K 1 0) hF ?_ hν
    rw [sylowB_mul_sylowF_one_mul_inv, weyl_conj_mul, Unip.weylTwo_conj_sylowF_full,
      weylTwo_conj_sylowJ]
    exact ⟨_, Unip.sylowD_mem_complement_zero hK 1 0, 1, one_mem _, by rw [mul_one]⟩
  have hc' : β c' = c' := by
    have hD : sylowD a K 1 0 ∈ Rf K a β :=
      (Unip.sylowD_mem_Rf_iff hK β 1 0).2 ⟨map_one β, map_zero β⟩
    have hj : β (b' * largeReeSigma a b' + c') = b' * largeReeSigma a b' + c' := by
      refine hAj (y := sylowD a K 1 0) hD ?_ hν
      rw [sylowB_mul_sylowD_one_mul_inv hK]
      have hV : sylowV a K 0 0 0 1 0 (largeReeSigma a b') (b' ^ 2 * largeReeSigma a b' + b' * c') b'
          c' (b' * largeReeSigma a b' + c') 0 (b' * largeReeSigma a b' + c') =
          sylowD a K 1 0 * sylowF a K (largeReeSigma a b') (b' ^ 2 * largeReeSigma a b' + b' * c') *
            sylowH a K b' c' * sylowJ a K (b' * largeReeSigma a b' + c') *
              sylowL a K (b' * largeReeSigma a b' + c') := by
        simp [sylowV, sylowA_zero, sylowB_zero_zero, sylowK_zero]
      rw [hV]
      have hn2 : weylTwo K * (sylowD a K 1 0 * sylowF a K (largeReeSigma a b')
          (b' ^ 2 * largeReeSigma a b' + b' * c') * sylowH a K b' c' *
            sylowJ a K (b' * largeReeSigma a b' + c') *
              sylowL a K (b' * largeReeSigma a b' + c')) * (weylTwo K)⁻¹ =
          sylowF a K 1 0 * sylowD a K (largeReeSigma a b') (b' ^ 2 * largeReeSigma a b' + b' * c') *
            sylowH a K b' c' * sylowA a K (b' * largeReeSigma a b' + c') *
              sylowK a K (b' * largeReeSigma a b' + c') := by
        simp only [weyl_conj_mul, Unip.weylTwo_conj_sylowD_full, Unip.weylTwo_conj_sylowF_full,
          Unip.weylTwo_conj_sylowH_full, weylTwo_conj_sylowJ, weylTwo_conj_sylowL]
      rw [hn2]
      exact ⟨_, mul_mem (mul_mem (Unip.sylowF_mem_complement_zero hK _ _)
        (Unip.sylowD_mem_complement_zero hK _ _)) (Unip.sylowH_mem_complement_zero hK _ _), _,
        Unip.sylowK_mem_complement_zero hK _, rfl⟩
    rw [map_add, map_mul, hb', map_largeReeSigma, hb'] at hj
    exact add_left_cancel hj
  have hB' : sylowB a K b' c' ∈ Rf K a β := (Unip.sylowB_mem_Rf_iff hK β b' c').2 ⟨hb', hc'⟩
  have huH : u ∈ H := by
    have e : u * T2 a ν * weylTwo K * sylowB a K b' c' * (sylowB a K b' c')⁻¹ *
        (weylTwo K)⁻¹ * (T2 a ν)⁻¹ = u := by group
    rw [← e]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx (H.inv_mem (hRH hB'))) (H.inv_mem hn))
      (H.inv_mem (hRH hT))
  obtain ⟨w, hw, hvw⟩ := exists_mul_sylowB_of_mem hK hv (one_mem _) b₁ c₁
  rw [mul_one] at hvw
  obtain ⟨hb₁, hc₁⟩ := map_eq_self_of_B hK β hU huH hw (hudef.trans hvw)
  have hB₁R : sylowB a K b₁ c₁ ∈ Rf K a β := (Unip.sylowB_mem_Rf_iff hK β b₁ c₁).2 ⟨hb₁, hc₁⟩
  have e : T2 a ν * sylowB a K b c = sylowB a K b₁ c₁ * T2 a ν := by
    rw [← hB₁]
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hB₁R hT) (weylTwo_mem_Rf β)) hB'

end MainTwo

end LeviRat

theorem Y1_le_Rf_of_inf_le
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)}
    (hRH : Rf K a β ≤ H) (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) :
    Y1 K a hK H ≤ Rf K a β := by
  rintro r ⟨hr, v, hv, hvr⟩
  rcases LeviRat.rankOneGroupOne_cells hK hr with ⟨μ, s, rfl⟩ | ⟨s₁, μ, s₂, rfl⟩
  · exact LeviRat.Y1_borel ha hK β hRH hU hv hvr
  · exact LeviRat.Y1_bigcell hK β hRH hU hv hvr

theorem Y2_le_Rf_of_inf_le
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)}
    (hRH : Rf K a β ≤ H) (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) :
    Y2 K a hK H ≤ Rf K a β := by
  rintro r ⟨hr, v, hv, hvr⟩
  rcases LeviRat.rankOneGroupTwo_cells ha hK hr with ⟨ν, b, c, rfl⟩ | ⟨ν, b, c, b', c', rfl⟩
  · exact LeviRat.Y2_borel hK β hRH hU hv hvr
  · exact LeviRat.Y2_bigcell hK β hRH hU hv hvr

end CFSG.RankThree.PartOne.SEITZRF
