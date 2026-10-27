module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagIntr

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}

theorem exists_flagSg (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K n) :
    ∃ y : FlagK K n, ∀ j, y.E j = sgS K f n (x.E j) := by
  refine ⟨⟨fun j => sgS K f n (x.E j), ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro i j hij
    exact sgS_mono (x.mono hij)
  · intro j hj
    rw [finrank_sgS hK, x.dim j hj]
  · intro j hj
    rw [x.top j hj, sgS_top]

@[expose] noncomputable def flagSg (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K n) : FlagK K n :=
  Classical.choose (exists_flagSg hK x)

theorem flagSg_E (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K n) (j : ℕ) :
    (flagSg hK x).E j = sgS K f n (x.E j) :=
  Classical.choose_spec (exists_flagSg hK x) j

theorem flagSg_flagSg (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K n) :
    flagSg hK (flagSg hK x) = x := by
  apply FlagK.ext
  intro j
  rw [flagSg_E, flagSg_E, sgS_sgS hK]

theorem cdist_flagSys_le (K : Type) [Field K] (m : ℕ) (E F : FlagK K (m + 1)) :
    cdist (flagSys K m) E F ≤ (m + 1) * m / 2 := by
  rw [← length_flagδ_eq_cdist (K := K) m E F]
  exact length_flagδ_le E F

variable {ι ι' C D : Type}

theorem intrSet_prod {X : ChamberSystem ι C} {Y : ChamberSystem ι' D} (hX : X.Connected)
    (hY : Y.Connected) {R₁ : Set C} {R₂ : Set D} (h₁ : R₁.Nonempty) (h₂ : R₂.Nonempty)
    {ψ₁ : C → C} {ψ₂ : D → D} {D₁ D₂ : ℕ} (hD₁ : ∀ x y, cdist X x y ≤ D₁)
    (hD₂ : ∀ x y, cdist Y x y ≤ D₂) :
    IntrSet (X.prod Y) (R₁ ×ˢ R₂) (Prod.map ψ₁ ψ₂) (D₁ + D₂) =
      IntrSet X R₁ ψ₁ D₁ ×ˢ IntrSet Y R₂ ψ₂ D₂ := by
  ext y
  constructor
  · rintro ⟨g, hg, hgate, hdist⟩
    obtain ⟨hg₁, hg₂⟩ := Set.mem_prod.mp hg
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · refine ⟨g.1, hg₁, ⟨hg₁, fun z₁ hz₁ => ?_⟩, ?_⟩
      · have hz : (z₁, g.2) ∈ R₁ ×ˢ R₂ := Set.mem_prod.mpr ⟨hz₁, hg₂⟩
        have h := hgate.2 (z₁, g.2) hz
        simp only [cdist_prod hX hY, cdist_self] at h
        omega
      · have hd : cdist (X.prod Y) y (Prod.map ψ₁ ψ₂ g) =
            cdist X y.1 (ψ₁ g.1) + cdist Y y.2 (ψ₂ g.2) :=
          cdist_prod hX hY y (Prod.map ψ₁ ψ₂ g)
        rw [hd] at hdist
        have h1 := hD₁ y.1 (ψ₁ g.1)
        have h2 := hD₂ y.2 (ψ₂ g.2)
        omega
    · refine ⟨g.2, hg₂, ⟨hg₂, fun z₂ hz₂ => ?_⟩, ?_⟩
      · have hz : (g.1, z₂) ∈ R₁ ×ˢ R₂ := Set.mem_prod.mpr ⟨hg₁, hz₂⟩
        have h := hgate.2 (g.1, z₂) hz
        simp only [cdist_prod hX hY, cdist_self] at h
        omega
      · have hd : cdist (X.prod Y) y (Prod.map ψ₁ ψ₂ g) =
            cdist X y.1 (ψ₁ g.1) + cdist Y y.2 (ψ₂ g.2) :=
          cdist_prod hX hY y (Prod.map ψ₁ ψ₂ g)
        rw [hd] at hdist
        have h1 := hD₁ y.1 (ψ₁ g.1)
        have h2 := hD₂ y.2 (ψ₂ g.2)
        omega
  · rintro ⟨hy₁, hy₂⟩
    obtain ⟨g₁, hg₁, hgate₁, hdist₁⟩ := hy₁
    obtain ⟨g₂, hg₂, hgate₂, hdist₂⟩ := hy₂
    refine ⟨(g₁, g₂), Set.mem_prod.mpr ⟨hg₁, hg₂⟩, ⟨Set.mem_prod.mpr ⟨hg₁, hg₂⟩, ?_⟩, ?_⟩
    · rintro ⟨z₁, z₂⟩ hz
      obtain ⟨hz₁, hz₂⟩ := Set.mem_prod.mp hz
      have h1 := hgate₁.2 z₁ hz₁
      have h2 := hgate₂.2 z₂ hz₂
      simp only [cdist_prod hX hY]
      rw [h1, h2]
      omega
    · have hd : cdist (X.prod Y) y (Prod.map ψ₁ ψ₂ (g₁, g₂)) =
          cdist X y.1 (ψ₁ g₁) + cdist Y y.2 (ψ₂ g₂) :=
        cdist_prod hX hY y (Prod.map ψ₁ ψ₂ (g₁, g₂))
      rw [hd, hdist₁, hdist₂]

@[expose] noncomputable def psiA1A1 (hK : Nat.card K = (2 ^ f) ^ 2)
    (c : FlagK K 2 × FlagK K 2) : FlagK K 2 × FlagK K 2 :=
  (flagSg hK c.2, flagSg hK c.1)

private theorem q2cFPr_flagSys_one_adj (x y : FlagK K 2) (i : Fin 1) :
    (flagSys K 1).adj i x y := by
  intro j hj
  have hi : i.val = 0 := Fin.val_eq_zero i
  rw [hi] at hj
  rcases Nat.lt_or_ge j 2 with h | h
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [FlagK.E_zero x, FlagK.E_zero y]
  · rw [x.top j h, y.top j h]

private theorem q2cFPr_cdist_flagSys_one_eq_zero_or_one (x y : FlagK K 2) :
    cdist (flagSys K 1) x y = 0 ∨ cdist (flagSys K 1) x y = 1 := by
  by_cases h : x = y
  · subst h
    exact Or.inl (cdist_self (flagSys K 1) x)
  · right
    have hle : cdist (flagSys K 1) x y ≤ 1 := by
      unfold cdist
      refine Nat.sInf_le ⟨[((0 : Fin 1), y)], ?_, rfl, rfl⟩
      exact ⟨q2cFPr_flagSys_one_adj x y 0, trivial⟩
    have hne : cdist (flagSys K 1) x y ≠ 0 := fun h0 =>
      h ((cdist_eq_zero_iff (flagSys K 1) (flagSys_connected K 1)).mp h0)
    omega

private theorem q2cFPr_cdist_flagSys_one_eq_one_iff (x y : FlagK K 2) :
    cdist (flagSys K 1) x y = 1 ↔ x ≠ y := by
  constructor
  · intro h heq
    subst heq
    rw [cdist_self] at h
    omega
  · intro h
    rcases q2cFPr_cdist_flagSys_one_eq_zero_or_one x y with h0 | h1
    · exact absurd ((cdist_eq_zero_iff (flagSys K 1) (flagSys_connected K 1)).mp h0) h
    · exact h1

private theorem q2cFPr_add_eq_two_iff {a b : ℕ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a + b = 2 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

private theorem q2cFPr_flagSys_one_sum_eq_two_iff (a b c d : FlagK K 2) :
    cdist (flagSys K 1) a b + cdist (flagSys K 1) c d = 2 ↔ a ≠ b ∧ c ≠ d := by
  rw [q2cFPr_add_eq_two_iff (q2cFPr_cdist_flagSys_one_eq_zero_or_one a b)
    (q2cFPr_cdist_flagSys_one_eq_zero_or_one c d)]
  simp only [q2cFPr_cdist_flagSys_one_eq_one_iff]

private theorem q2cFPr_eq_of_cdist_eq_zero_prod {I J : Type} {C₁ C₂ : Type}
    {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂} (hX : X.Connected) (hY : Y.Connected)
    {a b : C₁ × C₂} (h : cdist (X.prod Y) a b = 0) : a = b := by
  have hsum : cdist X a.1 b.1 + cdist Y a.2 b.2 = 0 := by
    rw [cdist_prod hX hY] at h
    exact h
  have h1 : cdist X a.1 b.1 = 0 := by omega
  have h2 : cdist Y a.2 b.2 = 0 := by omega
  exact Prod.ext ((cdist_eq_zero_iff X hX).mp h1) ((cdist_eq_zero_iff Y hY).mp h2)

private theorem q2cFPr_intrSet_univ_prod {I J : Type} {C₁ C₂ : Type}
    {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂} (hX : X.Connected) (hY : Y.Connected)
    (ψ : C₁ × C₂ → C₁ × C₂) (diam : ℕ) :
    IntrSet (X.prod Y) Set.univ ψ diam = {c | cdist (X.prod Y) c (ψ c) = diam} := by
  ext c
  constructor
  · rintro ⟨g, -, hgate, hdist⟩
    have h0 : cdist (X.prod Y) c g = 0 := by
      have h := hgate.2 c (Set.mem_univ c)
      rw [cdist_self] at h
      omega
    have hgc : g = c := (q2cFPr_eq_of_cdist_eq_zero_prod hX hY h0).symm
    rw [hgc] at hdist
    exact hdist
  · intro h
    exact ⟨c, Set.mem_univ c, ⟨Set.mem_univ c, fun z _ => by rw [cdist_self]; omega⟩, h⟩

theorem intrSet_exchA1A1 (hK : Nat.card K = (2 ^ f) ^ 2) :
    IntrSet ((flagSys K 1).prod (flagSys K 1)) Set.univ (psiA1A1 hK) 2 =
      {c | c.1.E 1 ≠ sgS K f 2 (c.2.E 1)} := by
  rw [q2cFPr_intrSet_univ_prod (flagSys_connected K 1) (flagSys_connected K 1)]
  ext c
  simp only [Set.mem_setOf_eq]
  have hcd : cdist ((flagSys K 1).prod (flagSys K 1)) c (psiA1A1 hK c) =
      cdist (flagSys K 1) c.1 (flagSg hK c.2) +
        cdist (flagSys K 1) c.2 (flagSg hK c.1) :=
    cdist_prod (flagSys_connected K 1) (flagSys_connected K 1) c (psiA1A1 hK c)
  rw [hcd, q2cFPr_flagSys_one_sum_eq_two_iff]
  have hflag : (c.1 = flagSg hK c.2) ↔ c.1.E 1 = sgS K f 2 (c.2.E 1) := by
    constructor
    · intro h
      rw [h, flagSg_E]
    · intro h
      apply FlagK.ext_of_mid
      intro j hj1 hj2
      have hj : j = 1 := by omega
      subst hj
      rw [flagSg_E]
      exact h
  have hswap : (c.2 = flagSg hK c.1) ↔ (flagSg hK c.2 = c.1) := by
    constructor
    · intro h
      rw [h, flagSg_flagSg]
    · intro h
      rw [← h, flagSg_flagSg]
  have hsecond : (¬ (c.2 = flagSg hK c.1)) ↔ (¬ c.1.E 1 = sgS K f 2 (c.2.E 1)) :=
    (not_congr hswap).trans
      ((not_congr (eq_comm (a := flagSg hK c.2) (b := c.1))).trans hflag.not)
  change (¬ c.1 = flagSg hK c.2) ∧ (¬ c.2 = flagSg hK c.1) ↔
    (¬ c.1.E 1 = sgS K f 2 (c.2.E 1))
  rw [hflag.not, hsecond]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
