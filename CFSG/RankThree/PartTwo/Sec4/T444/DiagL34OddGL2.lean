module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.L34Odd

open CFSG.GorensteinWalter

theorem two_ne_zero_of_isOddPrimePower {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : (2 : K) ≠ 0 := by
  obtain ⟨p, n, hp, hpo, hn, hcard⟩ := hK
  haveI : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hpo.pow
  have hchar : ringChar K ≠ 2 := fun h => by
    have h1 := (FiniteField.even_card_iff_char_two).1 h
    have h2 := Nat.odd_iff.1 hodd
    omega
  exact Ring.two_ne_zero hchar

theorem odd_card_of_isOddPrimePower {K : Type*} (hK : IsOddPrimePower (Nat.card K)) :
    Odd (Nat.card K) := by
  obtain ⟨p, n, hp, hpo, hn, hcard⟩ := hK
  rw [hcard]
  exact hpo.pow

theorem fin_two_sq_eq_one_of_det {k : Type*} [Field k] {M : Matrix (Fin 2) (Fin 2) k}
    (h2 : (2 : k) ≠ 0) (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  rw [Matrix.mul_fin_two, Matrix.one_fin_two] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have hs : a + d ≠ 0 := fun hs => h2 (by linear_combination -e00 - hdet + a * hs)
  have hb : b = 0 :=
    (mul_eq_zero.1 (show b * (a + d) = 0 by linear_combination e01)).resolve_right hs
  have hc : c = 0 :=
    (mul_eq_zero.1 (show c * (a + d) = 0 by linear_combination e10)).resolve_right hs
  subst hb hc
  have ha0 : a ≠ 0 := fun ha => by rw [ha] at e00; simp at e00
  have hd : d = a := sub_eq_zero.1 ((mul_eq_zero.1 (show a * (d - a) = 0 by
    linear_combination hdet - e00)).resolve_left ha0)
  subst hd
  rcases mul_eq_zero.1 (show (d - 1) * (d + 1) = 0 by linear_combination e00) with ha | ha
  · left
    rw [sub_eq_zero.1 ha, Matrix.one_fin_two]
  · right
    rw [eq_neg_of_add_eq_zero_left ha, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem card_le_four_of_exp_two_gl2 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (F : Subgroup (GL (Fin 2) K)) (hF : ∀ x ∈ F, x ^ 2 = 1) : Nat.card F ≤ 4 := by
  classical
  let d : F →* Kˣ := (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).comp F.subtype
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hr : Nat.card d.range ≤ 2 := by
    have hsq : ∀ x : d.range, ((x : Kˣ) : K) = 1 ∨ ((x : Kˣ) : K) = -1 := by
      rintro ⟨_, g, rfl⟩
      refine mul_self_eq_one_iff.1 ?_
      have h := congrArg (fun u : GL (Fin 2) K => ((Matrix.GeneralLinearGroup.det u : Kˣ) : K))
        (hF g g.2)
      simpa [sq, d, Matrix.GeneralLinearGroup.val_det_apply] using h
    let f : d.range → Bool := fun x => decide (((x : Kˣ) : K) = 1)
    have hf : Function.Injective f := by
      intro x y hxy
      rcases hsq x with hx | hx <;> rcases hsq y with hy | hy
      · exact Subtype.ext (Units.ext (hx.trans hy.symm))
      · have h1 : f x = true := decide_eq_true hx
        have h2' : f y = false := decide_eq_false (fun h => hne (hy.symm.trans h))
        rw [h1, h2'] at hxy
        exact absurd hxy (by decide)
      · have h1 : f x = false := decide_eq_false (fun h => hne (hx.symm.trans h))
        have h2' : f y = true := decide_eq_true hy
        rw [h1, h2'] at hxy
        exact absurd hxy (by decide)
      · exact Subtype.ext (Units.ext (hx.trans hy.symm))
    calc Nat.card d.range ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hk : Nat.card d.ker ≤ 2 := by
    have hsq : ∀ g : d.ker, (((g : F) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        (((g : F) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
      intro g
      refine fin_two_sq_eq_one_of_det h2 ?_ ?_
      · have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K))
          (hF (g : F) (g : F).2)
        simpa [sq] using h
      · have h := congrArg (fun u : Kˣ => (u : K)) (MonoidHom.mem_ker.1 g.2)
        simpa [d, Matrix.GeneralLinearGroup.val_det_apply] using h
    let f : d.ker → Bool := fun g =>
      decide ((((g : F) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1)
    have hneM : (-1 : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h => by
      have h' := congrFun (congrFun h 0) 0
      simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h'
      exact hne h'
    have hf : Function.Injective f := by
      intro x y hxy
      have key : ∀ x y : d.ker, (((x : F) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (((y : F) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) → x = y := fun x y h =>
        Subtype.ext (Subtype.ext (Units.ext h))
      apply key
      rcases hsq x with hx | hx <;> rcases hsq y with hy | hy
      · rw [hx, hy]
      · have h1 : f x = true := decide_eq_true hx
        have h2' : f y = false := decide_eq_false (fun h => hneM (hy.symm.trans h))
        rw [h1, h2'] at hxy
        exact absurd hxy (by decide)
      · have h1 : f x = false := decide_eq_false (fun h => hneM (hx.symm.trans h))
        have h2' : f y = true := decide_eq_true hy
        rw [h1, h2'] at hxy
        exact absurd hxy (by decide)
      · rw [hx, hy]
    calc Nat.card d.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hcard : Nat.card d.ker * Nat.card d.range = Nat.card F := by
    rw [← Subgroup.index_ker d]
    exact Subgroup.card_mul_index d.ker
  rw [← hcard]
  exact (Nat.mul_le_mul hk hr).trans (by norm_num)

theorem commute_of_center_mul_zpow {G : Type*} [Group G] (c : G) {x y z w : G} {m n : ℤ}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G)
    (hx : x = z * c ^ m) (hy : y = w * c ^ n) : x * y = y * x := by
  subst hx hy
  rw [Subgroup.mem_center_iff] at hz hw
  have h1 : c ^ m * w = w * c ^ m := hw (c ^ m)
  have h2 : c ^ n * z = z * c ^ n := hz (c ^ n)
  have h3 : w * z = z * w := hz w
  have h4 : c ^ m * c ^ n = c ^ n * c ^ m := by rw [← zpow_add, ← zpow_add, add_comm]
  calc z * c ^ m * (w * c ^ n) = z * (c ^ m * w) * c ^ n := by simp only [mul_assoc]
    _ = z * (w * c ^ m) * c ^ n := by rw [h1]
    _ = (z * w) * (c ^ m * c ^ n) := by simp only [mul_assoc]
    _ = (w * z) * (c ^ n * c ^ m) := by rw [h3, h4]
    _ = w * (z * c ^ n) * c ^ m := by simp only [mul_assoc]
    _ = w * (c ^ n * z) * c ^ m := by rw [h2]
    _ = w * c ^ n * (z * c ^ m) := by simp only [mul_assoc]

theorem index_zpowers_r_one (n : ℕ) [NeZero n] :
    (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).index = 2 := by
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)))
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact Nat.eq_of_mul_eq_mul_left hn (by rw [h1, mul_comm])

theorem exists_zpowers_comap_index_le_two {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {T : Type*} [Group T] (f : T →* PGL2 K)
    (hf : IsPGroup 2 f.range) : ∃ c : PGL2 K, ((Subgroup.zpowers c).comap f).index ≤ 2 := by
  haveI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨P, hP⟩ := hf.exists_le_sylow
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK P
  set c₀ : (P : Subgroup (PGL2 K)) := e.symm (DihedralGroup.r 1) with hc₀
  refine ⟨(c₀ : PGL2 K), ?_⟩
  have h1 : (Subgroup.zpowers c₀).index = 2 := by
    rw [← Subgroup.index_map_equiv (H := Subgroup.zpowers c₀) e, MonoidHom.map_zpowers]
    have hmap : (e : (P : Subgroup (PGL2 K)) →* DihedralGroup (2 ^ m)) c₀ =
        DihedralGroup.r (1 : ZMod (2 ^ m)) := by
      simp [hc₀]
    rw [hmap]
    exact index_zpowers_r_one _
  have h2 : (Subgroup.zpowers (c₀ : PGL2 K)).subgroupOf (P : Subgroup (PGL2 K)) =
      Subgroup.zpowers c₀ := by
    have : Subgroup.zpowers (c₀ : PGL2 K) = (Subgroup.zpowers c₀).map (P : Subgroup (PGL2 K)).subtype := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [this]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective (P : Subgroup (PGL2 K))) _
  rw [Subgroup.index_comap]
  calc (Subgroup.zpowers (c₀ : PGL2 K)).relIndex f.range
      ≤ (Subgroup.zpowers (c₀ : PGL2 K)).relIndex (P : Subgroup (PGL2 K)) := by
        refine Subgroup.relIndex_le_of_le_right hP ?_
        exact Subgroup.index_ne_zero_of_finite
    _ = 2 := by rw [Subgroup.relIndex, h2, h1]

theorem gl2Type_of_isPGroup {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (S : Subgroup (GL (Fin 2) K)) (hS : IsPGroup 2 S) :
    GL2Type S := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isOddPrimePower hK
  let f : S →* PGL2 K := Matrix.ProjGenLinGroup.mk.comp S.subtype
  have hfr : IsPGroup 2 f.range := hS.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨cbar, hcbar⟩ := exists_zpowers_comap_index_le_two hK f hfr
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_surjective cbar
  have hcent : ∀ (a : S) (m : ℤ), f a = cbar ^ m →
      ((a : GL (Fin 2) K) * c ^ (-m)) ∈ Subgroup.center (GL (Fin 2) K) := by
    intro a m hm
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, map_zpow, hc, zpow_neg]
    have : Matrix.ProjGenLinGroup.mk (a : GL (Fin 2) K) = f a := rfl
    rw [this, hm, mul_inv_cancel]
  refine ⟨(Subgroup.zpowers cbar).comap f, ?_, hcbar, ?_⟩
  · intro a ha b hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
    apply Subtype.ext
    refine commute_of_center_mul_zpow c (hcent a m hm.symm) (hcent b n hn.symm) (m := m)
      (n := n) ?_ ?_
    · simp
    · simp
  · intro F _ hF2
    have h := card_le_four_of_exp_two_gl2 h2 (F.map S.subtype) (by
      rintro _ ⟨x, hx, rfl⟩
      have := hF2 x hx
      simpa using congrArg Subtype.val this)
    rwa [Subgroup.card_map_of_injective S.subtype_injective] at h

theorem gl2Type_of_injective {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {S : Type*} [Group S] (σ : S →* GL (Fin 2) K)
    (hσ : Function.Injective σ) (hS : IsPGroup 2 S) : GL2Type S :=
  GL2Type.of_injective σ.rangeRestrict
    (MonoidHom.rangeRestrict_injective_iff.2 hσ)
    (gl2Type_of_isPGroup hK σ.range (hS.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective))

end CFSG.RankThree.PartTwo.Sec4.L34Odd

end
