module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MMembers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MFixDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16c2m_rk_le_one {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup W} (h : rk ↥H ≤ 1) : ∃ c ∈ H, ∀ x ∈ H, x = 1 ∨ x = c := by
  have hcard : Nat.card ↥H ≤ 2 := by
    rw [card_eq_two_pow hW H]
    calc 2 ^ rk ↥H ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
      _ = 2 := by norm_num
  by_cases hbot : H = ⊥
  · exact ⟨1, H.one_mem, fun x hx => Or.inl (Subgroup.mem_bot.1 (hbot ▸ hx))⟩
  · have hgt : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot H).2 hbot
    have h2 : Nat.card ↥H = 2 := le_antisymm hcard hgt
    obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    refine ⟨(c : W), c.2, fun x hx => ?_⟩
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).1 h2
      have h1 : c = y := hy c hc
      have h2' : (⟨x, hx⟩ : ↥H) = y := hy ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h2'.trans h1.symm)

private theorem s16c2m_perm_moves : ∀ a : Fin 3, ∃ σ : Equiv.Perm (Fin 3), σ a ≠ a := by
  decide

theorem s16c2m_invFix_abs {W : Type} [CommGroup W] [Finite W] {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) (hLX : L ≤ X) (hKX : K ≤ X)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hK : IsSym ↥K 3)
    (hdir : IsInternalDirect K L₀ X)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    (hfix : s16c2m_FixThree L J₀) : s16n9bInvFix X 3 3 := by
  classical
  obtain ⟨hr4, hfix3⟩ := hfix
  obtain ⟨G3, π, hinj, hrange, hJ0, hJ1, hact, hsurj, hfaith, hmeet, hrk, hcomm⟩ :=
    s16c2m_members F hKX hKL hK hE₀ hE₁
  obtain ⟨a, ha⟩ := hJ0
  have hKL0 : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := by
    intro k hk l hl
    have hkcent : k ∈ Subgroup.centralizer (L₀ : Set (MulAut W)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdir.1) hk
    exact (Subgroup.mem_centralizer_iff.1 hkcent l hl).symm
  have hL₀X : L₀ ≤ X := by rw [← hdir.2.2]; exact le_sup_right
  intro φ hφ _ hrkφ z hz hz1
  have hφsup : φ ∈ K ⊔ L₀ := by rw [hdir.2.2]; exact hφ
  obtain ⟨κ, hκ, l, hl, hκl⟩ := s16c2m_exists_mul_of_mem_sup hKL0 hφsup
  have hπl : π ⟨l, hL₀X hl⟩ = 1 := hcomm _ (fun k hk => (hKL0 k hk l hl).symm)
  have hπx : π ⟨φ, hφ⟩ = π ⟨κ, hKX hκ⟩ := by
    have : (⟨φ, hφ⟩ : ↥X) = ⟨κ, hKX hκ⟩ * ⟨l, hL₀X hl⟩ := Subtype.ext hκl.symm
    rw [this, map_mul, hπl, mul_one]
  by_cases hπ1 : π ⟨φ, hφ⟩ = 1
  ·
    have hπκ : π ⟨κ, hKX hκ⟩ = 1 := hπx ▸ hπ1
    have hκ1 : (⟨κ, hκ⟩ : ↥K) = 1 := hfaith ⟨κ, hκ⟩ hπκ
    have hκ1' : κ = 1 := congrArg Subtype.val hκ1
    have hφl : φ = l := by rw [← hκl, hκ1', one_mul]
    have hφK : ∀ k ∈ K, k * φ = φ * k := fun k hk => hφl ▸ hKL0 k hk l hl
    obtain ⟨σ, hσ⟩ := s16c2m_perm_moves a
    obtain ⟨kζ, hkζ⟩ := hsurj σ
    have hAζ : (G3 a).map (kζ : MulAut W).toMonoidHom = G3 (σ a) := by
      have := hact ⟨(kζ : MulAut W), hKX kζ.2⟩ a
      rwa [hkζ] at this
    have hAφ : (G3 a).map φ.toMonoidHom = G3 a := by
      have := hact ⟨φ, hφ⟩ a
      rw [hπ1, Equiv.Perm.one_apply] at this
      exact this
    have hζφ : (kζ : MulAut W) * φ = φ * (kζ : MulAut W) := hφK kζ kζ.2
    have hd : Disjoint (G3 a) ((G3 a).map (kζ : MulAut W).toMonoidHom) := by
      rw [hAζ]
      exact disjoint_iff.2 (hmeet a (σ a) (Ne.symm hσ)).1
    have hsup : G3 a ⊔ (G3 a).map (kζ : MulAut W).toMonoidHom = ⊤ := by
      rw [hAζ]
      exact (hmeet a (σ a) (Ne.symm hσ)).2
    obtain ⟨hcv, hdecomp⟩ := s16c2m_commV_two hζφ hAφ hd hsup
    obtain ⟨H, hHdef⟩ : ∃ H : Subgroup W, H = commSub (G3 a) (Subgroup.zpowers φ) := ⟨_, rfl⟩
    rw [← hHdef] at hcv hdecomp
    have hrkH : rk ↥H ≤ 1 := by omega
    obtain ⟨c, hcH, hc⟩ := s16c2m_rk_le_one F.sq hrkH
    obtain ⟨a', ha'H, b', hb'H, hzab⟩ := hdecomp z hz
    have hHle : H ≤ G3 a := by
      rw [hHdef]
      exact commSub_le_of_invariant (s16c2m_zpowers_inv hAφ)
    have hcJ : c ∈ J₀ := ha ▸ hHle hcH
    have hc1 : c ≠ 1 := by
      intro hc1
      apply hz1
      have ha1 : a' = 1 := by
        rcases hc a' ha'H with h | h
        · exact h
        · rw [h, hc1]
      have hb1 : b' = 1 := by
        rcases hc b' hb'H with h | h
        · exact h
        · rw [h, hc1]
      rw [hzab, ha1, hb1, map_one, mul_one]
    obtain ⟨y, hyL, hy3, hyc⟩ := hfix3 c hcJ hc1
    refine ⟨y, hLX hyL, hy3, ?_⟩
    have hyfix : ∀ x ∈ H, y x = x := by
      intro x hx
      rcases hc x hx with h | h
      · rw [h, map_one]
      · rw [h]
        exact hyc
    have hyζ : y * (kζ : MulAut W) = (kζ : MulAut W) * y := (hKL kζ kζ.2 y hyL).symm
    have hyζb : ∀ x : W, y ((kζ : MulAut W) x) = (kζ : MulAut W) (y x) := by
      intro x
      have := congrArg (fun f : MulAut W => f x) hyζ
      simpa [MulAut.mul_apply] using this
    rw [hzab, map_mul, hyζb, hyfix a' ha'H, hyfix b' hb'H]
  ·
    exfalso
    obtain ⟨j, hj⟩ : ∃ j, π ⟨φ, hφ⟩ j ≠ j := by
      by_contra hcon
      apply hπ1
      refine Equiv.ext fun j => ?_
      by_contra hj
      exact hcon ⟨j, hj⟩
    have hdisj : Disjoint (G3 j) (G3 (π ⟨φ, hφ⟩ j)) :=
      disjoint_iff.2 (hmeet j _ (Ne.symm hj)).1
    have hswap : rk ↥(G3 j) ≤ rkIdx (fixV (Subgroup.zpowers φ)) :=
      s16c2m_rkIdx_ge_swap hdisj (hact ⟨φ, hφ⟩ j)
    rw [hrk j] at hswap
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
