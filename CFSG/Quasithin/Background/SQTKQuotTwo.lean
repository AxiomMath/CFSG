module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open scoped Matrix

theorem sqtkGroup_quotient_of_isPGroup_two {X : Type} [Group X] [Finite X] (hX : SQTKGroup X)
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) : SQTKGroup (X ⧸ N) := by
  refine ⟨fun p hp hp2 => ?_, hX.2.quotient N⟩
  have : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ Nat.card N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := hX.1 p hp hp2
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ N)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hnd]
    exact h1
  exact h2

theorem fixV_inf_commV_eq_bot {V : Type*} [CommGroup V] (h2 : ∀ v : V, v * v = 1)
    {Y : Subgroup (MulAut V)} (hY : Group.IsPerfect ↥Y) {ζ : MulAut V} (hζY : ζ ∈ Y)
    (hζc : ∀ y ∈ Y, ζ * y = y * ζ) (hζ3 : ζ ^ 3 = 1)
    (hfix : ∀ u ∈ commV Y, ζ u = u → u ∈ fixV Y) : fixV Y ⊓ commV Y = ⊥ := by
  have hζζζ : ∀ v : V, ζ (ζ (ζ v)) = v := fun v => by
    have h := congrArg (fun φ : MulAut V => φ v) hζ3
    simpa [pow_succ, MulAut.mul_apply] using h
  let P : V →* V :=
    { toFun := fun v => v * ζ v * ζ (ζ v)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        ac_rfl }
  have hP : ∀ v, P v = v * ζ v * ζ (ζ v) := fun v => rfl
  have hζP : ∀ v, ζ (P v) = P v := fun v => by
    rw [hP, map_mul, map_mul, hζζζ]
    ac_rfl
  have hyP : ∀ y ∈ Y, ∀ v, y (P v) = P (y v) := fun y hy v => by
    have hc : ∀ w, ζ (y w) = y (ζ w) := fun w => by
      have h := congrArg (fun φ : MulAut V => φ w) (hζc y hy)
      simpa [MulAut.mul_apply] using h
    rw [hP, hP, map_mul, map_mul, ← hc, ← hc, ← hc]
  have hPfix : ∀ v, P v ∈ fixV Y := by
    intro v
    have hmem : ∀ y ∈ Y, y (P v) * (P v)⁻¹ ∈ fixV Y := fun y hy => by
      refine hfix _ (Subgroup.subset_closure ⟨y, hy, P v, rfl⟩) ?_
      have hc : ζ (y (P v)) = y (ζ (P v)) := by
        have h := congrArg (fun φ : MulAut V => φ (P v)) (hζc y hy)
        simpa [MulAut.mul_apply] using h
      rw [map_mul, map_inv, hc, hζP]
    let f : ↥Y →* ↥(fixV Y) :=
      { toFun := fun y => ⟨(y : MulAut V) (P v) * (P v)⁻¹, hmem y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => by
          apply Subtype.ext
          have hb := hmem b b.2
          set w := (b : MulAut V) (P v) * (P v)⁻¹ with hw
          have hbw : (b : MulAut V) (P v) = w * P v := by rw [hw]; group
          have haw : (a : MulAut V) w = w := hb a a.2
          show ((a * b : ↥Y) : MulAut V) (P v) * (P v)⁻¹ =
            ((a : MulAut V) (P v) * (P v)⁻¹) * w
          rw [Subgroup.coe_mul, MulAut.mul_apply, hbw, map_mul, haw]
          ac_rfl }
    intro y hy
    have h1 : f ⟨y, hy⟩ = 1 := by
      have htop : commutator ↥Y = ⊤ := Group.isPerfect_def.1 hY
      have hle : commutator ↥Y ≤ f.ker := Abelianization.commutator_subset_ker f
      rw [htop] at hle
      exact hle (Subgroup.mem_top _)
    have h2' : y (P v) * (P v)⁻¹ = 1 := congrArg Subtype.val h1
    exact mul_inv_eq_one.1 h2'
  have hPU : ∀ u ∈ commV Y, P u = 1 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨y, hy, v, rfl⟩ := hw
      rw [map_mul, map_inv, ← hyP y hy, hPfix v y hy, mul_inv_cancel]
    | one => exact map_one P
    | mul a b _ _ ha hb => rw [map_mul, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, ha, inv_one]
  rw [eq_bot_iff]
  rintro u ⟨huF, huU⟩
  have h1 := hPU u huU
  have hζu : ζ u = u := huF ζ hζY
  rw [hP, hζu, hζu, h2 u, one_mul] at h1
  exact Subgroup.mem_bot.2 h1

theorem eq_smul_of_commute_transvection {F : Type*} [Field F] {n : Type*} [Fintype n]
    [DecidableEq n] [Nontrivial n] (f : (n → F) →+ (n → F))
    (hf : ∀ i j, i ≠ j → ∀ (c : F) (v : n → F),
      f (Matrix.transvection i j c *ᵥ v) = Matrix.transvection i j c *ᵥ f v) :
    ∃ c : F, ∀ v, f v = c • v := by
  have htv : ∀ (i j : n) (c : F) (v : n → F),
      Matrix.transvection i j c *ᵥ v = v + Pi.single i (c * v j) := by
    intro i j c v
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
    congr 1
  have hkey : ∀ i j, i ≠ j → ∀ (c : F) (v : n → F),
      f (Pi.single i (c * v j)) = Pi.single i (c * f v j) := by
    intro i j hij c v
    have h := hf i j hij c v
    rw [htv, htv, map_add] at h
    exact add_left_cancel h
  set φ : n → F → F := fun j s => f (Pi.single j s) j with hφ
  have hsingle : ∀ i j, i ≠ j → ∀ c s : F, f (Pi.single i (c * s)) = Pi.single i (c * φ j s) := by
    intro i j hij c s
    have h := hkey i j hij c (Pi.single j s)
    rwa [Pi.single_eq_same] at h
  have hφeq : ∀ i j, i ≠ j → ∀ s : F, φ i s = φ j s := by
    intro i j hij s
    have h := hsingle i j hij 1 s
    rw [one_mul, one_mul] at h
    have h2 := congrFun h i
    rw [Pi.single_eq_same] at h2
    exact h2
  obtain ⟨j₀⟩ := (inferInstance : Nonempty n)
  have hφall : ∀ i s, φ i s = φ j₀ s := fun i s => by
    by_cases h : i = j₀
    · rw [h]
    · exact hφeq i j₀ h s
  have hlin : ∀ s : F, φ j₀ s = s * φ j₀ 1 := by
    intro s
    obtain ⟨i, hi⟩ := exists_ne j₀
    have h1 := hsingle i j₀ hi s 1
    have h2 := hsingle i j₀ hi 1 s
    rw [mul_one] at h1
    rw [one_mul, one_mul] at h2
    have h3 := congrFun (h2.symm.trans h1) i
    rw [Pi.single_eq_same, Pi.single_eq_same] at h3
    exact h3
  refine ⟨φ j₀ 1, fun v => ?_⟩
  have hfs : ∀ i, f (Pi.single i (v i)) = Pi.single i (φ j₀ 1 * v i) := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have h := hsingle i j hj.symm 1 (v i)
    rw [one_mul, one_mul, hφall, hlin, mul_comm] at h
    exact h
  have hsum : f (∑ i, Pi.single i (v i)) = ∑ i, Pi.single i (φ j₀ 1 * v i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hfs i
  calc f v = f (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, Pi.single i (φ j₀ 1 * v i) := hsum
    _ = φ j₀ 1 • v := by
      rw [← Finset.univ_sum_single (φ j₀ 1 • v)]
      rfl

theorem exists_coboundary_of_odd_index {G : Type*} [Group G] [Finite G] {M : Type*}
    [CommGroup M] (h2 : ∀ m : M, m * m = 1) (ρ : G →* MulAut M) {f : G → M}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) {P : Subgroup G} (hP : Odd P.index)
    (hfP : ∀ p ∈ P, f p = 1) : ∃ m : M, ∀ g, f g = ρ g m * m⁻¹ := by
  classical
  have : Fintype (G ⧸ P) := Fintype.ofFinite _
  have hconst : ∀ g p, p ∈ P → f (g * p) = f g := fun g p hp => by
    rw [hf, hfP p hp, map_one, mul_one]
  set m : M := ∏ c : G ⧸ P, f c.out with hm
  refine ⟨m, fun g => ?_⟩
  have hρ : ∀ x, ρ g (f x) = (f g)⁻¹ * f (g * x) := fun x => by
    rw [hf, inv_mul_cancel_left]
  have hout : ∀ c : G ⧸ P, f (g * c.out) = f (g • c).out := by
    intro c
    have h1 : (QuotientGroup.mk (g * c.out) : G ⧸ P) = g • c := by
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P (g * c.out)
    rw [h1] at hp
    rw [hp, hconst _ _ p.2]
  have hprod : ∏ c : G ⧸ P, f (g • c).out = m :=
    Fintype.prod_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  have hcard : Fintype.card (G ⧸ P) = P.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hpow : ∀ x : M, x ^ P.index = x := fun x => by
    obtain ⟨k, hk⟩ := hP
    rw [hk, pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  have hinv : ∀ x : M, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h2 x)
  have hρm : ρ g m = f g * m := by
    calc ρ g m = ∏ c : G ⧸ P, ρ g (f c.out) := by rw [hm, map_prod]
      _ = ∏ c : G ⧸ P, ((f g)⁻¹ * f (g • c).out) := by
          refine Finset.prod_congr rfl fun c _ => ?_
          rw [hρ, hout]
      _ = (f g)⁻¹ ^ P.index * m := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, hprod]
      _ = f g * m := by rw [hpow, hinv]
  rw [hρm, mul_inv_cancel_right]

end CFSG.Quasithin
