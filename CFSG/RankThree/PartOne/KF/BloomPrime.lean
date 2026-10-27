module

public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.KF.BloomCyclic
public import CFSG.RankThree.PartOne.KF.BloomAut
public import CFSG.RankThree.PartOne.KF.BloomOmega

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFBloom

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace KFBloom

theorem not_dvd_60 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hmod : p % 10 = 1 ∨ p % 10 = 9) :
    ¬ p ∣ 60 := by
  intro hd
  have hle : p ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> omega

theorem eleven_le_of_mod_seven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hmod : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem seven_le_of_mod_thirty {p : ℕ} (hmod : p % 30 = 1 ∨ p % 30 = 19) (h5 : 5 ≤ p) :
    7 ≤ p := by
  omega

theorem normalizerMonoidHom_pow_eq_one {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) {p : ℕ} (hgp : g ^ p = 1) :
    (H.normalizerMonoidHom ⟨g, hg⟩) ^ p = 1 := by
  rw [← map_pow]
  have : (⟨g, hg⟩ : Subgroup.normalizer (H : Set Γ)) ^ p = 1 := Subtype.ext (by simpa using hgp)
  rw [this, map_one]

theorem commute_of_normalizerMonoidHom_eq_one {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) (hα : H.normalizerMonoidHom ⟨g, hg⟩ = 1) :
    ∀ h ∈ H, h * g = g * h := by
  intro h hh
  have h1 := congrArg (fun a : MulAut H => ((a ⟨h, hh⟩ : H) : Γ)) hα
  have h2 : g * h * g⁻¹ = h := h1
  calc h * g = (g * h * g⁻¹) * g := by rw [h2]
    _ = g * h := by group

theorem mem_normalizer_of_closed {Γ : Type*} [Group Γ] {G H : Subgroup Γ} {g : Γ} (hgG : g ∈ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hnorm g hgG h hh, fun hh => ?_⟩
  have := hnorm g⁻¹ (G.inv_mem hgG) _ hh
  simpa [mul_assoc] using this

theorem eq_one_of_normalizer_aut_trivial {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 3) (ZMod p)))
    (hirr : ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ g : H, ∀ w ∈ W,
        ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    {g : GL (Fin 3) (ZMod p)}
    (hg : g ∈ Subgroup.normalizer (H : Set (GL (Fin 3) (ZMod p)))) (hgp : g ^ p = 1)
    (htriv : ∀ α : MulAut H, α ^ p = 1 → α = 1) : g = 1 :=
  eq_one_of_commute_irreducible (by norm_num) H hirr hgp
    (commute_of_normalizerMonoidHom_eq_one hg
      (htriv _ (normalizerMonoidHom_pow_eq_one hg hgp)))

end KFBloom

theorem extBloomPrime_of_mitchell (hBM : ExtBloomMitchell) : ExtBloomPrime := by
  intro p _ hp5 G hGirr hpG
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨H, hHG, hnorm, hHirr, hcases⟩ := hBM p hp2 hGirr
  have hHirr' : ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ g : H, ∀ w ∈ W,
        ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤ := hHirr
  have hGirr' : ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ g : G, ∀ w ∈ W,
        ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤ := hGirr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpG
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hpr.one_lt.ne' hx.symm
  set g : GL (Fin 3) (ZMod p) := (x : GL (Fin 3) (ZMod p)) with hgdef
  have hgG : g ∈ G := x.2
  have hgp : g ^ p = 1 := by
    have := congrArg (fun y : G => (y : GL (Fin 3) (ZMod p))) hxp
    simpa using this
  have hg1 : g ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hgH : g ∈ Subgroup.normalizer (H : Set (GL (Fin 3) (ZMod p))) :=
    mem_normalizer_of_closed hgG hnorm
  have hshape : H = StatedSL 3 (ZMod p) ∨
      ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M := by
    rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact Or.inl h1
    · exact Or.inr h2
    all_goals exfalso
    ·
      obtain ⟨⟨e⟩, hmod, hdec, hinter⟩ := h3
      obtain ⟨h, hh, z, hzG, hzc, hgz⟩ := hdec g hgG
      have hcomm : Commute h z := (hzc h (hHG hh)).symm
      have h1 : g ^ p = h ^ p * z ^ p := by rw [hgz]; exact hcomm.mul_pow p
      have hhpz : h ^ p * z ^ p = 1 := by rw [← h1]; exact hgp
      have hhpc : ∀ y ∈ G, h ^ p * y = y * h ^ p := by
        intro y hy
        have hc : Commute z y := hzc y hy
        have : h ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hhpz
        rw [this]
        exact ((hc.pow_left p).inv_left).eq
      have hhp1 : h ^ p = 1 := hinter _ (H.pow_mem hh p) hhpc
      have hzp : z ^ p = 1 := by
        rw [hhp1, one_mul] at hhpz
        exact hhpz
      have hz1 : z = 1 :=
        eq_one_of_commute_irreducible (by norm_num) G hGirr' hzp (fun y hy => (hzc y hy).symm)
      have hhg : h = g := by rw [hgz, hz1, mul_one]
      have hcard : Nat.card H = 60 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        norm_num [Fintype.card_fin, Nat.factorial]
      have hord : orderOf (⟨h, hh⟩ : H) ∣ 60 := hcard ▸ orderOf_dvd_natCard _
      have hord2 : orderOf (⟨h, hh⟩ : H) ∣ p :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hhp1))
      rcases (Nat.dvd_prime hpr).mp hord2 with h' | h'
      · have : (⟨h, hh⟩ : H) = 1 := orderOf_eq_one_iff.mp h'
        apply hg1
        rw [← hhg]
        exact congrArg Subtype.val this
      · rw [h'] at hord
        exact not_dvd_60 hpr hp5 hmod hord
    ·
      obtain ⟨⟨e⟩, hmod⟩ := h4
      have hp11 : 11 ≤ p := eleven_le_of_mod_seven hpr hp5 hmod
      exact hg1 (eq_one_of_normalizer_aut_trivial H hHirr' hgH hgp
        (fun α hα => aut_eq_one_of_gl_three_two e hp11 α hα))
    ·
      obtain ⟨hperf, -, ⟨e⟩, hmod⟩ := h5
      have hp7 : 7 ≤ p := seven_le_of_mod_thirty hmod hp5
      have : Group.IsPerfect H := hperf
      exact hg1 (eq_one_of_normalizer_aut_trivial H hHirr' hgH hgp
        (fun α hα => aut_eq_one_of_three_alt_six e hp7 α hα))
    ·
      obtain ⟨hcyc, -, -⟩ := h6
      obtain ⟨h0, hh0⟩ := hcyc.exists_generator
      set h0' : GL (Fin 3) (ZMod p) := (h0 : GL (Fin 3) (ZMod p)) with hh0'
      have hHeq : ∀ y, y ∈ H ↔ y ∈ Subgroup.zpowers h0' := by
        intro y
        constructor
        · intro hy
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hh0 ⟨y, hy⟩)
          refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
          have := congrArg Subtype.val hk
          simpa [hh0'] using this
        · intro hy
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact H.zpow_mem h0.2 k
      have hirr' : ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
          (∀ w ∈ W, (h0' : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
          (∀ w ∈ W, ((h0'⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
            W = ⊥ ∨ W = ⊤ := by
        intro W h1 h2
        have hpow : ∀ k : ℤ, ∀ w ∈ W,
            ((h0' ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W := by
          intro k
          induction k using Int.induction_on with
          | zero => intro w hw; simpa using hw
          | succ i ih =>
            intro w hw
            rw [_root_.zpow_add_one, Units.val_mul, ← Matrix.mulVec_mulVec]
            exact ih _ (h1 w hw)
          | pred i ih =>
            intro w hw
            rw [_root_.zpow_sub_one, Units.val_mul, ← Matrix.mulVec_mulVec]
            exact ih _ (h2 w hw)
        apply hHirr' W
        intro y w hw
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hHeq y).mp y.2)
        rw [← hk]
        exact hpow k w hw
      have hnormg : g * h0' * g⁻¹ ∈ Subgroup.zpowers h0' := (hHeq _).mp (hnorm g hgG h0' h0.2)
      have hcf : g * h0' * g⁻¹ = h0' := cyclic_conj_fixed (by omega) h0' hirr' hgp hnormg
      have hcomm : ∀ y ∈ H, y * g = g * y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hHeq y).mp hy)
        have : g * h0' ^ k * g⁻¹ = h0' ^ k := by rw [← conj_zpow, hcf]
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      exact hg1 (eq_one_of_commute_irreducible (by norm_num) H hHirr' hgp hcomm)
    ·
      obtain ⟨hcard, hext, -⟩ := h7
      have hZ : Nat.card (Subgroup.center H) = 3 := hext.2.2.2
      exact hg1 (eq_one_of_normalizer_aut_trivial H hHirr' hgH hgp
        (fun α hα => aut_eq_one_of_card_27 hcard hZ hp5 α hα))
    ·
      obtain ⟨-, L, hint, hdim, hperm, -⟩ := h8
      exact hg1 (eq_one_of_monomial (by omega) L hint hdim hgp (fun i => hperm g hgG i))
  refine ⟨H, hHG, hnorm, hHirr, ?_, hshape⟩
  rcases hshape with h1 | ⟨M, hM, hdet, h2⟩
  · rw [h1]
    have : Group.IsPerfect (SpecialLinearGroup (Fin 3) (ZMod p)) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
    exact Group.IsPerfect.ofSurjective
      (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod p) :
        SpecialLinearGroup (Fin 3) (ZMod p) →* StatedSL 3 (ZMod p))) (MulEquiv.surjective _)
  · rw [h2]
    exact omegaGL_isPerfect hp5 M hM hdet

end CFSG.RankThree.PartOne
