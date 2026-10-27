module

public import CFSG.Quasithin.EmptyFaithful.S151cDich
public import CFSG.Quasithin.EmptyFaithful.S152N2Fix

public section

namespace CFSG.Quasithin

open CFSG.Open

section Irr151c

variable {W : Type*} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {r : ℚ}

theorem card_invariant_modEq {P : Subgroup (MulAut W)} {p : ℕ} [Fact p.Prime] (hF : IsPGroup p P)
    (hfix : fixV P = ⊥) {B : Subgroup W} (hB : ∀ g ∈ P, ∀ b ∈ B, g b ∈ B) :
    Nat.card B ≡ 1 [MOD p] := by
  have h := S152N2.card_modEq_card_inf_fixV hF hB
  have : B ⊓ fixV P = ⊥ := by rw [hfix, inf_bot_eq]
  rw [this, Subgroup.card_bot] at h
  exact h

theorem eq_top_of_invariant_D3 (hV : ∀ v : W, v ^ 2 = 1) (hH : D217Hyp Y r)
    (hY : Nonempty (↥Y ≃* DihedralGroup 3)) (hrk : rk W = 2) {B : Subgroup W}
    (hB : ∀ g ∈ Y, ∀ b ∈ B, g b ∈ B) (hne : B ≠ ⊥) : B = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd := odd_card_fittingOf hH.o2
  have hF3 : IsPGroup 3 (fittingOf Y) := by
    refine isPGroup_of_card_dvd_of_odd (a := 1) (b := 1) Nat.prime_three hodd ?_
    have h1 := Subgroup.card_dvd_of_le (fittingOf_le Y)
    rw [card_of_dihedral hY] at h1
    simpa using h1
  have hfix := fixV_fittingOf_eq_bot hV hH.o2 hH.comm_fitting
  have hmod := card_invariant_modEq hF3 hfix (fun g hg b hb => hB g (fittingOf_le Y hg) b hb)
  have hdvd : Nat.card B ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card B
    rwa [card_eq_two_pow_rk hV, hrk] at this
  have hpos := Nat.card_pos (α := B)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : Nat.card B = 4 := by
    unfold Nat.ModEq at hmod
    have h1 : Nat.card B ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    generalize Nat.card B = n at *
    interval_cases n <;> omega
  refine (Subgroup.card_eq_iff_eq_top B).mp ?_
  rw [h4, card_eq_two_pow_rk hV, hrk]
  norm_num

theorem eq_top_of_invariant_D5 (hV : ∀ v : W, v ^ 2 = 1) (hH : D217Hyp Y r)
    (hY : Nonempty (↥Y ≃* DihedralGroup 5)) (hrk : rk W = 4) {B : Subgroup W}
    (hB : ∀ g ∈ Y, ∀ b ∈ B, g b ∈ B) (hne : B ≠ ⊥) : B = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hodd := odd_card_fittingOf hH.o2
  have hF5 : IsPGroup 5 (fittingOf Y) := by
    refine isPGroup_of_card_dvd_of_odd (a := 1) (b := 1) Nat.prime_five hodd ?_
    have h1 := Subgroup.card_dvd_of_le (fittingOf_le Y)
    rw [card_of_dihedral hY] at h1
    simpa using h1
  have hfix := fixV_fittingOf_eq_bot hV hH.o2 hH.comm_fitting
  have hmod := card_invariant_modEq hF5 hfix (fun g hg b hb => hB g (fittingOf_le Y hg) b hb)
  have hdvd : Nat.card B ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card B
    rwa [card_eq_two_pow_rk hV, hrk] at this
  have hpos := Nat.card_pos (α := B)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h16 : Nat.card B = 16 := by
    unfold Nat.ModEq at hmod
    have h1 : Nat.card B ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    generalize Nat.card B = n at *
    interval_cases n <;> omega
  refine (Subgroup.card_eq_iff_eq_top B).mp ?_
  rw [h16, card_eq_two_pow_rk hV, hrk]
  norm_num

omit [Finite W] in
theorem le_stabSub_of_invariant' {F : Subgroup (MulAut W)} {D : Subgroup W}
    (hD : ∀ g ∈ F, ∀ d ∈ D, g d ∈ D) : F ≤ stabSub D := by
  intro g hg u
  refine ⟨fun h => ?_, fun h => hD g hg u h⟩
  have := hD g⁻¹ (F.inv_mem hg) _ h
  simpa using this

theorem not_dvd_card_mulAut_of_rk_le_four (hV : ∀ v : W, v ^ 2 = 1) (hrk : rk W ≤ 4) :
    ¬ 27 ∣ Nat.card (MulAut W) := by
  rw [card_mulAut_eq hV]
  generalize rk W = n at hrk ⊢
  interval_cases n <;> decide

theorem eq_top_of_faithful (hV : ∀ v : W, v ^ 2 = 1) {F : Subgroup (MulAut W)}
    (hF27 : Nat.card F = 27) (hF3 : IsPGroup 3 F) (hfix : fixV F = ⊥) (hrk6 : rk W = 6)
    {D : Subgroup W} (hD : ∀ g ∈ F, ∀ d ∈ D, g d ∈ D) (hker : F ⊓ centSub D = ⊥) : D = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_invariant_modEq hF3 hfix hD
  have hcard := card_autSub_mul (le_stabSub_of_invariant' hD)
  rw [hker, Subgroup.card_bot, hF27, mul_one] at hcard
  have hdvd : 27 ∣ Nat.card (MulAut ↥D) := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hVD : ∀ v : ↥D, v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have hrk5 : 5 ≤ rk D := by
    by_contra hlt
    push Not at hlt
    exact not_dvd_card_mulAut_of_rk_le_four hVD (by omega) hdvd
  have hDW : Nat.card D ∣ Nat.card W := Subgroup.card_subgroup_dvd_card D
  rw [card_eq_two_pow hV, card_eq_two_pow_rk hV, hrk6] at hDW
  have hrkle : rk D ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hDW
  have hrk6' : rk D = 6 := by
    unfold Nat.ModEq at hmod
    rw [card_eq_two_pow hV] at hmod
    have : rk D = 5 ∨ rk D = 6 := by omega
    rcases this with h5 | h6
    · rw [h5] at hmod
      norm_num at hmod
    · exact h6
  refine (Subgroup.card_eq_iff_eq_top D).mp ?_
  rw [card_eq_two_pow hV, card_eq_two_pow_rk hV, hrk6, hrk6']

omit [Finite W] in
theorem shape4_center_card {F : Subgroup (MulAut W)} (hF27 : Nat.card F = 27)
    (hF3 : IsPGroup 3 F) (hnc : ∃ f ∈ F, ∃ g ∈ F, f * g ≠ g * f) :
    Nat.card (Subgroup.center ↥F) = 3 := by
  have hfin : Finite ↥F := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial ↥F := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hZnt : Nontrivial (Subgroup.center ↥F) := hF3.center_nontrivial
  have hdvd : Nat.card (Subgroup.center ↥F) ∣ 27 := hF27 ▸ Subgroup.card_subgroup_dvd_card _
  have hZgt : 1 < Nat.card (Subgroup.center ↥F) := by
    rw [← Finite.one_lt_card_iff_nontrivial] at hZnt
    exact hZnt
  have h327 : Nat.card (Subgroup.center ↥F) = 3 ∨ Nat.card (Subgroup.center ↥F) = 9 ∨
      Nat.card (Subgroup.center ↥F) = 27 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Subgroup.center ↥F) = n at *
    interval_cases n <;> omega
  obtain ⟨f, hf, g, hg, hfg⟩ := hnc
  rcases h327 with h | h | h
  · exact h
  · exfalso
    have hq : Nat.card (↥F ⧸ Subgroup.center ↥F) = 3 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥F)
      rw [hF27, h] at this
      omega
    have : IsCyclic (↥F ⧸ Subgroup.center ↥F) := isCyclic_of_prime_card hq
    have hc := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center ↥F)) (by rw [QuotientGroup.ker_mk'])
    exact hfg (congrArg Subtype.val (hc.is_comm.comm ⟨f, hf⟩ ⟨g, hg⟩))
  · exfalso
    have : Subgroup.center ↥F = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp (by rw [h, hF27])
    have hz : ∀ a b : ↥F, a * b = b * a := fun a b => by
      have := Subgroup.mem_center_iff.mp (this ▸ Subgroup.mem_top a) b
      exact this.symm
    exact hfg (congrArg Subtype.val (hz ⟨f, hf⟩ ⟨g, hg⟩))

omit [Finite W] in
theorem central_mem_centSub_of_ne_bot {F : Subgroup (MulAut W)} (hF27 : Nat.card F = 27)
    (hF3 : IsPGroup 3 F) (hnc : ∃ f ∈ F, ∃ g ∈ F, f * g ≠ g * f) {D : Subgroup W}
    (hD : ∀ g ∈ F, ∀ d ∈ D, g d ∈ D) (hker : F ⊓ centSub D ≠ ⊥) {z : MulAut W} (hzF : z ∈ F)
    (hzc : ∀ f ∈ F, f * z = z * f) : z ∈ centSub D := by
  have hfin : Finite ↥F := Nat.finite_of_card_ne_zero (by omega)
  have hcard := shape4_center_card hF27 hF3 hnc
  let K' : Subgroup ↥F := (centSub D).subgroupOf F
  have hKn : K'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    intro d hd
    have h1 : (g : MulAut W)⁻¹ d ∈ D := hD _ (F.inv_mem g.2) d hd
    have h2 : (n : MulAut W) ((g : MulAut W)⁻¹ d) = (g : MulAut W)⁻¹ d := hn _ h1
    show (g : MulAut W) ((n : MulAut W) ((g : MulAut W)⁻¹ d)) = d
    rw [h2]
    simp
  have hK' : K' ≠ ⊥ := by
    intro h
    apply hker
    refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
    have : (⟨k, hk.1⟩ : ↥F) ∈ K' := Subgroup.mem_subgroupOf.mpr hk.2
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hnil : Group.IsNilpotent ↥F := hF3.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hK'
  obtain ⟨⟨x, hxK, hxZ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hxo : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := by
      have := orderOf_dvd_natCard (⟨x, hxZ⟩ : Subgroup.center ↥F)
      rwa [Subgroup.orderOf_mk, hcard] at this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h
  have hle : Subgroup.zpowers x ≤ Subgroup.center ↥F := Subgroup.zpowers_le.mpr hxZ
  have heq : Subgroup.zpowers x = Subgroup.center ↥F :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hxo, hcard])
  have hzZ : (⟨z, hzF⟩ : ↥F) ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  rw [← heq] at hzZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzZ
  have : (⟨z, hzF⟩ : ↥F) ∈ K' := by
    rw [← hk]
    exact Subgroup.zpow_mem _ hxK k
  exact Subgroup.mem_subgroupOf.mp this

theorem eq_top_of_invariant_shape4 (hV : ∀ v : W, v ^ 2 = 1) {F : Subgroup (MulAut W)}
    (hF27 : Nat.card F = 27) (hexp : ∀ f ∈ F, f ^ 3 = 1)
    (hnc : ∃ f ∈ F, ∃ g ∈ F, f * g ≠ g * f) (hfix : fixV F = ⊥) (hrk6 : rk W = 6)
    {B : Subgroup W} (hB : ∀ g ∈ F, ∀ b ∈ B, g b ∈ B) (hne : B ≠ ⊥) : B = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : IsPGroup 3 F := fun a => ⟨1, Subtype.ext (by simpa using hexp (a : MulAut W) a.2)⟩
  have hfpf : ∀ z ∈ F, (∀ f ∈ F, f * z = z * f) → z ≠ 1 → ∀ b : W, z b = b → b = 1 := by
    intro z hzF hzc hz1 b hzb
    have hz3 : z ^ 3 = 1 := hexp z hzF
    have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
      rw [Nat.card_zpowers, hzo]; exact ⟨1, rfl⟩
    obtain ⟨hDC, hDC0⟩ := coprime_decomp hodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
    rw [← commV_eq_commSub, top_inf_eq] at hDC hDC0
    set D := commV (Subgroup.zpowers z) with hDdef
    set C := fixV (Subgroup.zpowers z) with hCdef
    have hcomm : ∀ g ∈ F, ∀ p ∈ Subgroup.zpowers z, g * p = p * g := by
      intro g hg p hp
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      exact (Commute.zpow_right (show Commute g z from hzc g hg) n).eq
    have hDinv : ∀ g ∈ F, ∀ d ∈ D, g d ∈ D := by
      intro g hg d hd
      induction hd using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨p, hp, v, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨p, hp, g v, ?_⟩
        have h1 : g (p v) = p (g v) := by
          have := congrArg (fun m : MulAut W => m v) (hcomm g hg p hp)
          simpa using this
        rw [map_mul, map_inv, h1]
      | one => rw [map_one]; exact D.one_mem
      | mul x y _ _ hx hy => rw [map_mul]; exact D.mul_mem hx hy
      | inv x _ hx => rw [map_inv]; exact D.inv_mem hx
    have hD0 : D ≠ ⊥ := by
      intro h
      have := eq_bot_of_commV_eq_bot h
      exact hz1 (Subgroup.zpowers_eq_bot.mp this)
    have hker : F ⊓ centSub D = ⊥ := by
      by_contra hker
      have hzD := central_mem_centSub_of_ne_bot hF27 hF3 hnc hDinv hker hzF hzc
      have hDC' : D ≤ C := by
        intro d hd p hp
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        have : z d = d := hzD d hd
        have h2 : ∀ m : ℤ, (z ^ m) d = d := by
          intro m
          induction m using Int.induction_on with
          | zero => simp
          | succ k ih =>
            rw [zpow_add_one]
            show (z ^ (k : ℤ)) (z d) = d
            rw [this]; exact ih
          | pred k ih =>
            rw [zpow_sub_one]
            show (z ^ (-(k : ℤ))) (z⁻¹ d) = d
            have : z⁻¹ d = d := by
              have h3 := congrArg (fun w => z⁻¹ w) this
              simpa using h3.symm
            rw [this]; exact ih
        exact h2 n
      apply hD0
      rw [eq_bot_iff, ← hDC0]
      exact le_inf le_rfl hDC'
    have hDtop := eq_top_of_faithful hV hF27 hF3 hfix hrk6 hDinv hker
    have hbC : b ∈ C := by
      intro p hp
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have h2 : ∀ m : ℤ, (z ^ m) b = b := by
        intro m
        induction m using Int.induction_on with
        | zero => simp
        | succ k ih =>
          rw [zpow_add_one]
          show (z ^ (k : ℤ)) (z b) = b
          rw [hzb]; exact ih
        | pred k ih =>
          rw [zpow_sub_one]
          show (z ^ (-(k : ℤ))) (z⁻¹ b) = b
          have : z⁻¹ b = b := by
            have h3 := congrArg (fun w => z⁻¹ w) hzb
            simpa using h3.symm
          rw [this]; exact ih
      exact h2 n
    have hbD : b ∈ D := by rw [hDtop]; exact Subgroup.mem_top b
    have : b ∈ D ⊓ C := ⟨hbD, hbC⟩
    rw [hDC0, Subgroup.mem_bot] at this
    exact this
  by_contra hBtop
  have hker : F ⊓ centSub B = ⊥ := by
    by_contra hker
    have hfin : Finite ↥F := Nat.finite_of_card_ne_zero (by omega)
    have hcard := shape4_center_card hF27 hF3 hnc
    obtain ⟨z, hzF, hzc, hz1⟩ : ∃ z ∈ F, (∀ f ∈ F, f * z = z * f) ∧ z ≠ 1 := by
      have hZnt : Nontrivial (Subgroup.center ↥F) := by
        have : Nontrivial ↥F := by
          rw [← Finite.one_lt_card_iff_nontrivial]; omega
        exact hF3.center_nontrivial
      obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥F)
      refine ⟨(z : MulAut W), z.2, fun f hf => ?_, fun e => hz1 (Subtype.ext (Subtype.ext e))⟩
      have := Subgroup.mem_center_iff.mp hz ⟨f, hf⟩
      exact congrArg Subtype.val this
    have hzB := central_mem_centSub_of_ne_bot hF27 hF3 hnc hB hker hzF hzc
    apply hne
    refine (Subgroup.eq_bot_iff_forall _).2 fun b hb => ?_
    exact hfpf z hzF hzc hz1 b (hzB b hb)
  exact hBtop (eq_top_of_faithful hV hF27 hF3 hfix hrk6 hB hker)

end Irr151c

end CFSG.Quasithin
