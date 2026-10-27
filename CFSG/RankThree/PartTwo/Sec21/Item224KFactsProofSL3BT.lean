module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Mat
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3BT

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat

variable {K : Type} [Field K]

theorem proj_eq (d : Fin 3 → K) (v : Fin 3 → K) (i : Fin 3) :
    diagonal d *ᵥ (diagonal d *ᵥ v) - (d (i + 1) + d (i + 2)) • (diagonal d *ᵥ v) +
        (d (i + 1) * d (i + 2)) • v =
      ((d i - d (i + 1)) * (d i - d (i + 2)) * v i) • Pi.single i 1 := by
  ext l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul]
  fin_cases i <;> fin_cases l <;> simp <;> ring

theorem eq_top_of_invariant {d c : Fin 3 → K} (hd : Function.Injective d) (hc : ∀ i, c i ≠ 0)
    {W : Submodule K (Fin 3 → K)} (hW : W ≠ ⊥)
    (hx : ∀ v ∈ W, diagonal d *ᵥ v ∈ W) (hy : ∀ v ∈ W, (cycMat * diagonal c) *ᵥ v ∈ W) :
    W = ⊤ := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hsingle : ∀ j : Fin 3, Pi.single j (1 : K) ∈ W → Pi.single (j + 1) (1 : K) ∈ W := by
    intro j hj
    have h1 := hy _ hj
    rw [← mulVec_mulVec, diagonal_mulVec_single, mul_one, cycMat_mulVec_single] at h1
    have h2 : Pi.single (j + 1) (1 : K) = (c j)⁻¹ • Pi.single (j + 1) (c j) := by
      rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ (hc j)]
    rw [h2]
    exact W.smul_mem _ h1
  have hei : Pi.single i (1 : K) ∈ W := by
    have hw := proj_eq d v i
    have hmem : diagonal d *ᵥ (diagonal d *ᵥ v) - (d (i + 1) + d (i + 2)) • (diagonal d *ᵥ v) +
        (d (i + 1) * d (i + 2)) • v ∈ W :=
      W.add_mem (W.sub_mem (hx _ (hx _ hvW)) (W.smul_mem _ (hx _ hvW))) (W.smul_mem _ hvW)
    rw [hw] at hmem
    have hne : (d i - d (i + 1)) * (d i - d (i + 2)) * v i ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) hi
      · exact sub_ne_zero.mpr fun h => by
          have := hd h
          fin_cases i <;> simp at this
      · exact sub_ne_zero.mpr fun h => by
          have := hd h
          fin_cases i <;> simp at this
    have := W.smul_mem ((d i - d (i + 1)) * (d i - d (i + 2)) * v i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hall : ∀ j : Fin 3, Pi.single j (1 : K) ∈ W := by
    intro j
    have h1 := hsingle i hei
    have h2 := hsingle (i + 1) h1
    have h3 : j = i ∨ j = i + 1 ∨ j = i + 1 + 1 := by
      fin_cases i <;> fin_cases j <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact hei
    · exact h1
    · exact h2
  rw [Submodule.eq_top_iff']
  intro w
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem W fun j _ => ?_
  have : Pi.single j (w j) = w j • Pi.single j (1 : K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this]
  exact W.smul_mem _ (hall j)

@[expose] def fixSpace (U : Subgroup (SpecialLinearGroup (Fin 3) K)) :
    Submodule K (Fin 3 → K) where
  carrier := {v | ∀ u ∈ U, ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := fun ha hb u hu => by rw [mulVec_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => mulVec_zero _
  smul_mem' := fun c v hv u hu => by rw [mulVec_smul, hv u hu]

instance mulActionVec (U : Subgroup (SpecialLinearGroup (Fin 3) K)) :
    MulAction U (Fin 3 → K) where
  smul u v := ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
  one_smul v := by
    change ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v
    rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  mul_smul u w v := by
    change (((u * w : U) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((w : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
    rw [mulVec_mulVec, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem two_dvd_card [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.ne_zero

theorem eq_bot_of_isPGroup_normalized [Finite K] [CharP K 2] {d c : Fin 3 → K}
    (hd : Function.Injective d) (hc : ∀ i, c i ≠ 0) {x y : SpecialLinearGroup (Fin 3) K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hyc : (y : Matrix (Fin 3) (Fin 3) K) = cycMat * diagonal c)
    {U : Subgroup (SpecialLinearGroup (Fin 3) K)} (hU : IsPGroup 2 U)
    (hxU : x ∈ Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin 3) K)))
    (hyU : y ∈ Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin 3) K))) : U = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := hU.card_modEq_card_fixedPoints (Fin 3 → K)
  have hV : Nat.card (Fin 3 → K) ≡ 0 [MOD 2] := by
    rw [Nat.card_fun, Nat.card_fin]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_pow two_dvd_card (by norm_num))
  have hfix0 : (0 : Fin 3 → K) ∈ MulAction.fixedPoints U (Fin 3 → K) := fun u => mulVec_zero _
  have hlt : 1 < (MulAction.fixedPoints U (Fin 3 → K)).ncard := by
    have h0 : (MulAction.fixedPoints U (Fin 3 → K)).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨0, hfix0⟩ |>.ne'
    have h2 : (MulAction.fixedPoints U (Fin 3 → K)).ncard % 2 = 0 := by
      have := (hcard.symm.trans hV)
      rw [Nat.card_coe_set_eq] at this
      exact this
    omega
  obtain ⟨v, hv, hv0⟩ := Set.exists_ne_of_one_lt_ncard hlt 0
  have hvW : v ∈ fixSpace U := fun u hu => hv ⟨u, hu⟩
  have hW : fixSpace U ≠ ⊥ := fun h => hv0 (by rw [h] at hvW; exact hvW)
  have hinv : ∀ g : SpecialLinearGroup (Fin 3) K,
      g ∈ Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin 3) K)) →
      ∀ v ∈ fixSpace U, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ fixSpace U := by
    intro g hg v hv u hu
    have hg' : g⁻¹ ∈ Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin 3) K)) := inv_mem hg
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp hg' u).mp hu
      rwa [inv_inv] at this
    have h1 := hv _ hu'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ← mulVec_mulVec, ← mulVec_mulVec] at h1
    calc ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K).adjugate *ᵥ
            ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v))) := by
          rw [mulVec_mulVec (M := (g : Matrix (Fin 3) (Fin 3) K)), mul_adjugate, g.2, one_smul,
            one_mulVec]
      _ = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by rw [h1]
  have htop : fixSpace U = ⊤ := by
    refine eq_top_of_invariant hd hc hW (fun v hv => ?_) (fun v hv => ?_)
    · rw [← hxd]
      exact hinv x hxU v hv
    · rw [← hyc]
      exact hinv y hyU v hv
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.ext_of_mulVec_single
  intro i
  have h := (htop ▸ Submodule.mem_top : Pi.single i (1 : K) ∈ fixSpace U) u hu
  rw [h, one_mulVec]

theorem exists_pow_two_pow_eq_one {G : Type*} [Group G] {H : Subgroup G} (hH : IsPGroup 2 H)
    {g : G} (hg : g ∈ H) : ∃ m : ℕ, g ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := hH ⟨g, hg⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem eq_one_of_pow_three_of_pow_two_pow {G : Type*} [Group G] {g : G} (h3 : g ^ 3 = 1)
    {m : ℕ} (h2 : g ^ 2 ^ m = 1) : g = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one h2))

theorem mem_center_of_conj_eq_one {G : Type*} [Group G] {u : G} (h : MulAut.conj u = 1) :
    u ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun σ : MulAut G => σ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * u = u * g * u⁻¹ * u := by rw [this]
    _ = u * g := by group

theorem mem_center_of_conj_mem [Finite K] [CharP K 2] {d c : Fin 3 → K}
    (hd : Function.Injective d) (hc : ∀ i, c i ≠ 0) {x y : SpecialLinearGroup (Fin 3) K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hyc : (y : Matrix (Fin 3) (Fin 3) K) = cycMat * diagonal c)
    {P : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hP : IsPGroup 2 P)
    (hxP : MulAut.conj x ∈ Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))))
    (hyP : MulAut.conj y ∈ Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))))
    {u : SpecialLinearGroup (Fin 3) K} (hu : MulAut.conj u ∈ P) :
    u ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup (SpecialLinearGroup (Fin 3) K) := P.comap MulAut.conj with hUdef
  let f : U →* P := (MulAut.conj.comp U.subtype).codRestrict P fun v => v.2
  obtain ⟨S⟩ : Nonempty (Sylow 2 U) := Sylow.nonempty
  have hR : IsPGroup 2 f.range := hP.to_subgroup f.range
  set S' := S.mapSurjective f.rangeRestrict_surjective with hS'
  have hS'top : (S' : Subgroup f.range) = ⊤ :=
    (S'.is_maximal' (hR.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hdecomp : ∀ v : U, ∃ s ∈ (S : Subgroup U),
      ((s : U) : SpecialLinearGroup (Fin 3) K)⁻¹ * (v : SpecialLinearGroup (Fin 3) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro v
    have hv : f.rangeRestrict v ∈ (S' : Subgroup f.range) := by
      rw [hS'top]
      exact Subgroup.mem_top _
    rw [hS', Sylow.coe_mapSurjective] at hv
    obtain ⟨s, hs, hsv⟩ := hv
    refine ⟨s, hs, mem_center_of_conj_eq_one ?_⟩
    have h1 : MulAut.conj ((s : U) : SpecialLinearGroup (Fin 3) K) =
        MulAut.conj ((v : U) : SpecialLinearGroup (Fin 3) K) := by
      have := congrArg (fun w : f.range =>
        (((w : P) : MulAut (SpecialLinearGroup (Fin 3) K)))) hsv
      exact this
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  set SX : Subgroup (SpecialLinearGroup (Fin 3) K) := (S : Subgroup U).map U.subtype with hSX
  have hSX2 : IsPGroup 2 SX := S.isPGroup'.map _
  have h2el : ∀ v ∈ U, ∀ m : ℕ, v ^ 2 ^ m = 1 → v ∈ SX := by
    intro v hvU m hvm
    obtain ⟨s, hs, hz⟩ := hdecomp ⟨v, hvU⟩
    set z := ((s : U) : SpecialLinearGroup (Fin 3) K)⁻¹ * v with hzdef
    have hv : v = (s : U) * z := by rw [hzdef, mul_inv_cancel_left]
    have hcomm : Commute ((s : U) : SpecialLinearGroup (Fin 3) K) z :=
      (Subgroup.mem_center_iff.mp hz) _
    have hsSX : ((s : U) : SpecialLinearGroup (Fin 3) K) ∈ SX := ⟨s, hs, rfl⟩
    have hzm : z ^ 2 ^ m ∈ SX := by
      have h1 : ((s : U) : SpecialLinearGroup (Fin 3) K) ^ 2 ^ m * z ^ 2 ^ m = 1 := by
        rw [← hcomm.mul_pow, ← hv, hvm]
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (pow_mem hsSX _)
    have hzm1 : z ^ 2 ^ m = 1 := by
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hSX2 hzm
      have h3 : (z ^ 2 ^ m) ^ 3 = 1 := SL3Mat.pow_three_of_mem_center (pow_mem hz _)
      exact eq_one_of_pow_three_of_pow_two_pow h3 hk
    have hz1 : z = 1 :=
      eq_one_of_pow_three_of_pow_two_pow (SL3Mat.pow_three_of_mem_center hz) hzm1
    rw [hv, hz1, mul_one]
    exact hsSX
  have hnorm : ∀ g : SpecialLinearGroup (Fin 3) K,
      MulAut.conj g ∈ Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))) →
      ∀ h ∈ SX, g * h * g⁻¹ ∈ SX := by
    intro g hg h hh
    have hhU : h ∈ U := by
      obtain ⟨w, -, rfl⟩ := hh
      exact w.2
    have hU' : g * h * g⁻¹ ∈ U := by
      change MulAut.conj (g * h * g⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp hhU
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one hSX2 hh
    refine h2el _ hU' m ?_
    rw [conj_pow, hm, mul_one, mul_inv_cancel]
  have hnormSX : ∀ g : SpecialLinearGroup (Fin 3) K,
      MulAut.conj g ∈ Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))) →
      g ∈ Subgroup.normalizer (SX : Set (SpecialLinearGroup (Fin 3) K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hnorm g hg h, fun hh => ?_⟩
    have hg' : MulAut.conj g⁻¹ ∈
        Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))) := by
      rw [map_inv]
      exact inv_mem hg
    have h1 := hnorm g⁻¹ hg' _ hh
    have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [h2] at h1
  have hSXbot : SX = ⊥ :=
    eq_bot_of_isPGroup_normalized hd hc hxd hyc hSX2 (hnormSX x hxP) (hnormSX y hyP)
  obtain ⟨s, hs, hz⟩ := hdecomp ⟨u, hu⟩
  have hs1 : ((s : U) : SpecialLinearGroup (Fin 3) K) = 1 := by
    have : ((s : U) : SpecialLinearGroup (Fin 3) K) ∈ SX := ⟨s, hs, rfl⟩
    rw [hSXbot] at this
    exact this
  rwa [hs1, inv_one, one_mul] at hz

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3BT
