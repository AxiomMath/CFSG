module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfTorusFrame

theorem conj_of_mem_iff {G : Type} [Group G] {Bs X : Subgroup G} {N : ℕ}
    {T T' : Subgroup (SpecialLinearGroup (Fin (N + 1)) F2)}
    {ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X T ψ)
    (c : SpecialLinearGroup (Fin (N + 1)) F2) (hc : ∀ s, s ∈ T' ↔ c * s * c⁻¹ ∈ T) :
    GGHalfTorusFrame Bs X T' (ψ.comp (MulAut.conj c).toMonoidHom) where
  range := by
    rw [← hψ.range]
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨c⁻¹ * s * c, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
  inj := hψ.inj.comp (MulAut.conj c).injective
  torus_le := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := hz
    apply hψ.torus_le
    refine ⟨c * s * c⁻¹, (hc s).mp hs, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  act := by
    intro b hb
    obtain ⟨t, ht, hact⟩ := hψ.act b hb
    have hconj : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
    refine ⟨c⁻¹ * t * c, (hc _).mpr (by rw [hconj]; exact ht), fun l hl => ?_⟩
    have h1 : (ψ.comp (MulAut.conj c).toMonoidHom) (c⁻¹ * t * c) = ψ t := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj]
    rw [h1]
    exact hact l hl

end GGHalfTorusFrame

namespace GGHalf

theorem comp_conj_apply {G : Type} [Group G] {N : ℕ} (ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G)
    (c t : SpecialLinearGroup (Fin (N + 1)) F2) :
    (ψ.comp (MulAut.conj c).toMonoidHom) (c⁻¹ * t * c) = ψ t := by
  have hconj : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj]

theorem conj_inv_zpow {N : ℕ} (c a : SpecialLinearGroup (Fin (N + 1)) F2) (j : ℤ) :
    (c⁻¹ * a * c) ^ j = c⁻¹ * a ^ j * c := by
  have := map_zpow (MulAut.conj c⁻¹) a j
  simp only [MulAut.conj_apply, inv_inv] at this
  exact this.symm

theorem range_comp_conj {G : Type} [Group G] {N N' : ℕ}
    (ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) (c : SpecialLinearGroup (Fin (N + 1)) F2)
    (f : SpecialLinearGroup (Fin (N' + 1)) F2 →* SpecialLinearGroup (Fin (N + 1)) F2)
    (S : Subgroup (SpecialLinearGroup (Fin (N + 1)) F2))
    (hS : ∀ s, s ∈ f.range ↔ c * s * c⁻¹ ∈ S) :
    ((ψ.comp (MulAut.conj c).toMonoidHom).comp f).range = S.map ψ := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨c * f u * c⁻¹, (hS _).mp ⟨u, rfl⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rintro ⟨w, hw, rfl⟩
    have hconj : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
    obtain ⟨u, hu⟩ := (hS (c⁻¹ * w * c)).mpr (by rw [hconj]; exact hw)
    refine ⟨u, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu, hconj]

private theorem mem_iff_of_map_conj_eq {N : ℕ}
    {H K : Subgroup (SpecialLinearGroup (Fin N) F2)} (c : SpecialLinearGroup (Fin N) F2)
    (h : H.map (MulAut.conj c).toMonoidHom = K) :
    ∀ s, s ∈ H ↔ c * s * c⁻¹ ∈ K := by
  intro s
  have hc : (MulAut.conj c).toMonoidHom s = c * s * c⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hs
    have hmem : (MulAut.conj c).toMonoidHom s ∈ H.map (MulAut.conj c).toMonoidHom :=
      ⟨s, hs, rfl⟩
    rw [h] at hmem
    rwa [hc] at hmem
  · intro hs
    have hmem : (MulAut.conj c).toMonoidHom s ∈ H.map (MulAut.conj c).toMonoidHom := by
      rw [h, hc]
      exact hs
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hxs : x = s := (MulAut.conj c).injective hxeq
    rwa [hxs] at hx

theorem exists_conj_front (m : ℕ) (hm : 3 ≤ m) (P : Fin (m + 1 + 1)) (hP : P.val % 2 = 0) :
    ∃ c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      (∀ s, s ∈ halfTorus (m + 1 + 1) ↔ c * s * c⁻¹ ∈ halfTorus (m + 1 + 1)) ∧
      c * omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ * c⁻¹ = omegaBlock (m + 1 + 1) P ∧
      (∀ s, s ∈ (slLower2Hom m).range ↔
        c * s * c⁻¹ ∈ slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}) := by
  let A : Fin (m + 1 + 1 + 1) := P.castSucc
  let B : Fin (m + 1 + 1 + 1) := P.succ
  let π : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
    Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A * Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B
  let c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slPerm gf2_two π
  have hAval : A.val = P.val := rfl
  have hBval : B.val = P.val + 1 := rfl
  have hAB : A ≠ B := by
    intro h
    have hv := congrArg Fin.val h
    rw [hAval, hBval] at hv
    omega
  have hB0 : B ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [hBval, Fin.val_zero] at hv
    omega
  have hA1 : A ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    rw [hAval, Fin.val_one] at hv
    rw [hv] at hP
    norm_num at hP
  have h0fact : π (0 : Fin (m + 1 + 1 + 1)) = A := by
    rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
          Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
      Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.zero_ne_one' (n := m + 1 + 1)) hB0.symm,
      Equiv.swap_apply_left]
  have h1fact : π (1 : Fin (m + 1 + 1 + 1)) = B := by
    rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
          Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
      Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hB0 hAB.symm]
  have hAfact : π A = 0 := by
    rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
          Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
      Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hA1 hAB,
      Equiv.swap_apply_right]
  have hBfact : π B = 1 := by
    rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
          Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
      Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Fin.zero_ne_one' (n := m + 1 + 1)).symm hA1.symm]
  have hfix : ∀ k : Fin (m + 1 + 1), k.val % 2 = 0 → k ≠ 0 → k ≠ P →
      π k.castSucc = k.castSucc ∧ π k.succ = k.succ := by
    intro k hk2 hk0 hkP
    have hk0v : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv)
    have hkPv : k.val ≠ P.val := fun hv => hkP (Fin.ext hv)
    have hkc0 : k.castSucc ≠ (0 : Fin (m + 1 + 1 + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_zero] at hv
      exact hk0v hv
    have hkc1 : k.castSucc ≠ (1 : Fin (m + 1 + 1 + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_one] at hv
      rw [hv] at hk2
      norm_num at hk2
    have hkcB : k.castSucc ≠ B := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castSucc, hBval] at hv
      rw [hv] at hk2
      rw [Nat.add_mod, hP] at hk2
      norm_num at hk2
    have hkcA : k.castSucc ≠ A := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castSucc, hAval] at hv
      exact hkPv hv
    have hks0 : k.succ ≠ (0 : Fin (m + 1 + 1 + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hks1 : k.succ ≠ (1 : Fin (m + 1 + 1 + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_one] at hv
      omega
    have hksB : k.succ ≠ B := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, hBval] at hv
      exact hkPv (by omega)
    have hksA : k.succ ≠ A := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, hAval] at hv
      rw [← hv] at hP
      rw [Nat.add_mod, hk2] at hP
      norm_num at hP
    constructor
    · rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
            Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
          Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hkc1 hkcB,
          Equiv.swap_apply_of_ne_of_ne hkc0 hkcA]
    · rw [show π = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) A *
            Equiv.swap (1 : Fin (m + 1 + 1 + 1)) B from rfl,
          Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hks1 hksB,
          Equiv.swap_apply_of_ne_of_ne hks0 hksA]
  have hπcast : ∀ k : Fin (m + 1 + 1), k.val % 2 = 0 →
      π k.castSucc = (Equiv.swap (0 : Fin (m + 1 + 1)) P k).castSucc := by
    intro k hk2
    rcases eq_or_ne k (0 : Fin (m + 1 + 1)) with hk | hk
    · subst k
      rw [Fin.castSucc_zero, h0fact, Equiv.swap_apply_left]
    · rcases eq_or_ne k P with hkP | hkP
      · subst k
        rw [show P.castSucc = A from rfl, hAfact, Equiv.swap_apply_right, Fin.castSucc_zero]
      · rw [Equiv.swap_apply_of_ne_of_ne hk hkP, (hfix k hk2 hk hkP).1]
  have hπsucc : ∀ k : Fin (m + 1 + 1), k.val % 2 = 0 →
      π k.succ = (Equiv.swap (0 : Fin (m + 1 + 1)) P k).succ := by
    intro k hk2
    rcases eq_or_ne k (0 : Fin (m + 1 + 1)) with hk | hk
    · subst k
      rw [Fin.succ_zero_eq_one, h1fact, Equiv.swap_apply_left]
    · rcases eq_or_ne k P with hkP | hkP
      · subst k
        rw [show P.succ = B from rfl, hBfact, Equiv.swap_apply_right, Fin.succ_zero_eq_one]
      · rw [Equiv.swap_apply_of_ne_of_ne hk hkP, (hfix k hk2 hk hkP).2]
  have hgen : ∀ k : Fin (m + 1 + 1), k.val % 2 = 0 →
      (MulAut.conj c).toMonoidHom (omegaBlock (m + 1 + 1) k) =
        omegaBlock (m + 1 + 1) (Equiv.swap (0 : Fin (m + 1 + 1)) P k) := by
    intro k hk2
    have h := slPerm_conj_omegaBlock π (k := k) (k' := Equiv.swap (0 : Fin (m + 1 + 1)) P k)
      (hπcast k hk2) (hπsucc k hk2)
    simpa only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hκ_even : ∀ k : Fin (m + 1 + 1), k.val % 2 = 0 →
      (Equiv.swap (0 : Fin (m + 1 + 1)) P k).val % 2 = 0 := by
    intro k hk2
    rcases eq_or_ne k (0 : Fin (m + 1 + 1)) with hk | hk
    · subst k
      rw [Equiv.swap_apply_left]
      exact hP
    · rcases eq_or_ne k P with hkP | hkP
      · subst k
        rw [Equiv.swap_apply_right]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne hk hkP]
        exact hk2
  have hκ_invol : ∀ k : Fin (m + 1 + 1),
      Equiv.swap (0 : Fin (m + 1 + 1)) P (Equiv.swap (0 : Fin (m + 1 + 1)) P k) = k :=
    fun k => Equiv.swap_apply_self _ _ _
  let G : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    {t | ∃ k : Fin (m + 1 + 1), k.val % 2 = 0 ∧ t = omegaBlock (m + 1 + 1) k}
  have hhalf : halfTorus (m + 1 + 1) = Subgroup.closure G := rfl
  have hGens : (MulAut.conj c).toMonoidHom '' G = G := by
    apply Set.Subset.antisymm
    · rintro t ⟨x, ⟨k, hk2, rfl⟩, rfl⟩
      exact ⟨Equiv.swap (0 : Fin (m + 1 + 1)) P k, hκ_even k hk2, hgen k hk2⟩
    · rintro t ⟨k, hk2, rfl⟩
      refine ⟨omegaBlock (m + 1 + 1) (Equiv.swap (0 : Fin (m + 1 + 1)) P k),
        ⟨Equiv.swap (0 : Fin (m + 1 + 1)) P k, hκ_even k hk2, rfl⟩, ?_⟩
      rw [hgen (Equiv.swap (0 : Fin (m + 1 + 1)) P k) (hκ_even k hk2), hκ_invol k]
  have hmap1 : (halfTorus (m + 1 + 1)).map (MulAut.conj c).toMonoidHom =
      halfTorus (m + 1 + 1) := by
    rw [hhalf, MonoidHom.map_closure, hGens]
  have hset : π '' {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} =
      {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} := by
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor
      · intro h
        have hj0 : j = (0 : Fin (m + 1 + 1 + 1)) := π.injective (h.trans h0fact.symm)
        subst j
        rw [Set.mem_setOf_eq, Fin.val_zero] at hj
        omega
      · intro h
        have hj1 : j = (1 : Fin (m + 1 + 1 + 1)) := π.injective (h.trans h1fact.symm)
        subst j
        rw [Set.mem_setOf_eq, Fin.val_one] at hj
        omega
    · rintro ⟨hA', hB'⟩
      refine ⟨π.symm i, ?_, π.apply_symm_apply i⟩
      change 2 ≤ (π.symm i).val
      have hv0 : (π.symm i).val ≠ 0 := by
        intro hv
        have hzero : π.symm i = (0 : Fin (m + 1 + 1 + 1)) :=
          Fin.ext (by rw [hv, Fin.val_zero])
        have hAi : i = P.castSucc := by
          have hc := congrArg π hzero
          rw [Equiv.apply_symm_apply, h0fact] at hc
          exact hc
        exact hA' hAi
      have hv1 : (π.symm i).val ≠ 1 := by
        intro hv
        have hone : π.symm i = (1 : Fin (m + 1 + 1 + 1)) :=
          Fin.ext (by rw [hv, Fin.val_one])
        have hBi : i = P.succ := by
          have hc := congrArg π hone
          rw [Equiv.apply_symm_apply, h1fact] at hc
          exact hc
        exact hB' hBi
      omega
  have hmap3 : ((slLower2Hom m).range).map (MulAut.conj c).toMonoidHom =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} := by
    show ((slLower2Hom m).range).map (MulAut.conj (slPerm gf2_two π)).toMonoidHom =
        slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ}
    rw [range_slLower2Hom m, slOn_map_conj_slPerm π {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val}, hset]
  have h2 : c * omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ * c⁻¹ =
      omegaBlock (m + 1 + 1) P := by
    have h := hgen ⟨0, Nat.succ_pos _⟩ (by simp)
    rw [show Equiv.swap (0 : Fin (m + 1 + 1)) P ⟨0, Nat.succ_pos _⟩ = P from by
      rw [show (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)) = 0 from Fin.ext rfl,
        Equiv.swap_apply_left]] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  exact ⟨c, mem_iff_of_map_conj_eq c hmap1, h2, mem_iff_of_map_conj_eq c hmap3⟩

end GGHalf

end CFSG.StandardType

end
