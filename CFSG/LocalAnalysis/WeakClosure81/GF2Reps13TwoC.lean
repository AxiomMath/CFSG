module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoCB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra
public import CFSG.Quasithin.EmptyFaithful.S145Cop

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

section Helpers

private theorem w16g_three_cube_dvd_card_of_noncomm {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 3 A) (hnab : ¬ ∀ x y : A, x * y = y * x) : 3 ^ 3 ∣ Nat.card A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hA
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k ≤ 2 := by omega
    have hk0 : 0 ≤ k := Nat.zero_le k
    apply hnab
    intro x y
    interval_cases k
    · have hcard1 : Nat.card A = 1 := by norm_num [hk]
      haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hcard1).1
      exact Subsingleton.elim _ _
    · have hcard3 : Nat.card A = 3 := by norm_num [hk]
      haveI : IsCyclic A := isCyclic_of_prime_card hcard3
      exact ((inferInstance : IsMulCommutative A)).is_comm.comm x y
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := A) hk).is_comm.comm x y
  rw [hk]
  exact pow_dvd_pow 3 hk3

private theorem w16g_card_mulAut_eq_card_GL_of_rk (hW : ∀ w : W, w ^ 2 = 1) :
    Nat.card (MulAut W) =
      Nat.card (GL (Fin (rk ↥(⊤ : Subgroup W))) (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardW : Nat.card W = 2 ^ rk ↥(⊤ : Subgroup W) := by
    rw [← Subgroup.card_top]
    exact card_eq_two_pow hW ⊤
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) hW hcardW
  exact CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e

private theorem w16g_card_mulAut_of_rk_eq_two (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 2) : Nat.card (MulAut W) = 6 := by
  rw [w16g_card_mulAut_eq_card_GL_of_rk hW, hrk,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 2]
  norm_num [Fin.prod_univ_succ]

private theorem w16g_card_mulAut_of_rk_eq_four (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 4) : Nat.card (MulAut W) = 20160 := by
  rw [w16g_card_mulAut_eq_card_GL_of_rk hW, hrk,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 4]
  norm_num [Fin.prod_univ_succ]

private theorem w16g_card_mulAut_of_rk_eq_six (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 6) : Nat.card (MulAut W) = 20158709760 := by
  rw [w16g_card_mulAut_eq_card_GL_of_rk hW, hrk,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 6]
  norm_num [Fin.prod_univ_succ]

private theorem w16g_isZ3WrZ3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsZ3WrZ3 X) : IsZ3WrZ3 Y := by
  obtain ⟨hcard, z, b, hz, hcomm, hb, hconj, hgen⟩ := h
  refine ⟨?_, fun i => e (z i), e b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hcard]
  · intro i; rw [← map_pow, hz i, map_one]
  · intro i j; exact (hcomm i j).map e
  · rw [← map_pow, hb, map_one]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hconj i]
  · have himg : Set.range (fun i => e (z i)) ∪ {e b} =
        (e : X →* Y) '' (Set.range z ∪ {b}) := by
      ext y
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨z i, Or.inl ⟨i, rfl⟩, rfl⟩
        · exact ⟨b, Or.inr rfl, rfl⟩
      · rintro ⟨x, hx | rfl, rfl⟩
        · obtain ⟨i, rfl⟩ := hx; exact Or.inl ⟨i, rfl⟩
        · exact Or.inr rfl
    have hmap := MonoidHom.map_closure (e : X →* Y) (Set.range z ∪ {b})
    rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    rw [← himg] at hmap
    exact hmap.symm

private theorem w16g_isPOnePlusTwo_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨isExtraspecial_of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_commSub_zpowers_eq_top {z : MulAut W}
    (hfix : ∀ u : W, z u = u → u = 1) :
    commSub ⊤ (Subgroup.zpowers z) = ⊤ := by
  have hmap := commSub_zpowers_eq_map (W := (⊤ : Subgroup W)) (g := z)
    (fun x _ w _ => Subgroup.mem_top (x w))
  rw [← MonoidHom.range_eq_map] at hmap
  have hker : (commHom z).ker = ⊥ := by
    rw [ker_commHom, eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    exact hfix u (mem_fixV_zpowers_iff.mp hu)
  have hcard : Nat.card (commHom z).range = Nat.card W := by
    have h := Subgroup.card_ker_mul_card_range (commHom z)
    rw [hker, Subgroup.card_bot, one_mul] at h
    exact h
  have htop : (commHom z).range = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hcard]
  rw [hmap, htop]

end Helpers

theorem w16h_inverted_rank (h : Cfg132 t P) (hind : NoDecomp132 t P)
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzi : t * z * t⁻¹ = z⁻¹) :
    (∀ u : W, z u = u → u = 1) ∧ rk ↥(⊤ : Subgroup W) = 6 ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
  classical
  have hW := h.hW
  have hz3pow : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz3] at this
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  let Z : Subgroup (MulAut W) := Subgroup.zpowers z
  have hzZ : z ∈ Z := Subgroup.mem_zpowers z
  have hPnorm : P ≤ Subgroup.normalizer (Z : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.zpowers z).map (MulAut.conj x) = Subgroup.zpowers z
    have hxz : x * z * x⁻¹ = z := by
      rw [hzc x hx]
      group
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * z * x⁻¹) = Subgroup.zpowers z
    rw [hxz]
  have ht_mem : t ∈ Subgroup.normalizer (Z : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.zpowers z).map (MulAut.conj t) = Subgroup.zpowers z
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * z * t⁻¹) = Subgroup.zpowers z
    rw [hzi]
    exact Subgroup.zpowers_inv
  have hGnorm : P ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (Z : Set (MulAut W)) :=
    sup_le hPnorm (Subgroup.zpowers_le.mpr ht_mem)
  have hstabFix : StableUnder (P ⊔ Subgroup.zpowers t) (fixV Z) := by
    intro x hx u hu
    exact CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hGnorm hx) hu
  have hstabComm : StableUnder (P ⊔ Subgroup.zpowers t) (commSub ⊤ Z) := by
    intro x hx u hu
    have hu' : u ∈ commV Z := by
      rw [commV_eq_commSub]
      exact hu
    rw [← commV_eq_commSub]
    exact CFSG.Quasithin.commV_apply_mem_of_mem_normalizer (hGnorm hx) hu'
  have hodd : Odd (Nat.card Z) := by
    change Odd (Nat.card (Subgroup.zpowers z))
    rw [Nat.card_zpowers, hz3]
    norm_num
  have hcompl : IsCompl (fixV Z) (commV Z) :=
    CFSG.Quasithin.isCompl_fixV_commV_of_odd Z hodd hW
  have hdecomp : fixV Z = ⊤ ∨ commSub ⊤ Z = ⊤ := by
    refine hind (fixV Z) (commSub ⊤ Z) hstabFix hstabComm ?_ ?_
    · rw [← commV_eq_commSub]
      exact hcompl.inf_eq_bot
    · rw [← commV_eq_commSub]
      exact hcompl.sup_eq_top
  have hcomm_ne_bot : commSub ⊤ Z ≠ ⊥ := by
    intro hbot
    have hfixall : ∀ u : W, z u = u := by
      intro u
      have hle : (⊤ : Subgroup W) ≤ fixV Z := (commSub_eq_bot_iff.mp hbot)
      exact hle (Subgroup.mem_top u) z hzZ
    exact hz1 (MulEquiv.ext hfixall)
  have hcomm_top : commSub ⊤ Z = ⊤ := by
    rcases hdecomp with htop | htop
    · exfalso
      apply hcomm_ne_bot
      have hcomm_bot : commV Z = ⊥ := by
        have := hcompl.inf_eq_bot
        simpa [htop] using this
      rwa [commV_eq_commSub] at hcomm_bot
    · exact htop
  have hfixZ : fixV Z = ⊥ := by
    have hct : commV Z = ⊤ := by
      rw [commV_eq_commSub]
      exact hcomm_top
    have := hcompl.inf_eq_bot
    simpa [hct] using this
  have hfix : ∀ u : W, z u = u → u = 1 := by
    intro u hu
    have hu' : u ∈ fixV (Subgroup.zpowers z) :=
      CFSG.Quasithin.mem_fixV_zpowers_iff.mpr hu
    have h2 : u ∈ (⊥ : Subgroup W) := by
      rw [← hfixZ]
      exact hu'
    exact Subgroup.mem_bot.mp h2
  have heven : Even (rk ↥(⊤ : Subgroup W)) :=
    w16h_even_rk_of_fixedFree hW hz3pow (S := (⊤ : Subgroup W))
      (fun u _ => Subgroup.mem_top (z u)) (fun u _ hu => hfix u hu)
  have hXrank : IsElemAbelianOfRank 3 1 ↥Z := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard1 : Nat.card ↥Z = 3 := by
      change Nat.card ↥(Subgroup.zpowers z) = 3
      rw [Nat.card_zpowers, hz3]
    have hcard2 : Nat.card (Multiplicative (Fin 1 → ZMod 3)) = 3 := by
      simp [Nat.card_eq_fintype_card]
    haveI : IsCyclic (Multiplicative (Fin 1 → ZMod 3)) := isCyclic_of_prime_card hcard2
    exact ⟨mulEquivOfCyclicCardEq (hcard1.trans hcard2.symm)⟩
  have hinv : ∀ x ∈ Z, t * x * t⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hconj : MulAut.conj t z = z⁻¹ := by rw [MulAut.conj_apply, hzi]
    calc t * z ^ k * t⁻¹ = MulAut.conj t (z ^ k) := (MulAut.conj_apply t (z ^ k)).symm
      _ = (MulAut.conj t z) ^ k := map_zpow (MulAut.conj t) z k
      _ = (z⁻¹) ^ k := by rw [hconj]
      _ = (z ^ k)⁻¹ := inv_zpow z k
  have h73 : rk ↥(commSub ⊤ Z) =
      2 * rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t)) :=
    rk_commSub_eq_two_mul_of_inverted hW h.ht Nat.prime_three (by norm_num) (by norm_num)
      hXrank hinv
  rw [hcomm_top] at h73
  have hPdvd : Nat.card P ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card P
  have hnab' : ¬ ∀ x y : ↥P, x * y = y * x := by
    intro hcomm
    apply hnab
    intro x hx y hy
    exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  have h27dvd : 3 ^ 3 ∣ Nat.card P := w16g_three_cube_dvd_card_of_noncomm h.hP hnab'
  have heven' : ∃ m, rk ↥(⊤ : Subgroup W) = 2 * m := by
    obtain ⟨m, hm⟩ := heven
    exact ⟨m, by omega⟩
  have hrk_le6 : rk ↥(⊤ : Subgroup W) ≤ 6 := by
    have := h.hrk
    omega
  have hrk_ne0 : rk ↥(⊤ : Subgroup W) ≠ 0 := by
    intro h0
    have hcardW : Nat.card W = 1 := by
      have h1 : Nat.card ↥(⊤ : Subgroup W) = 2 ^ rk ↥(⊤ : Subgroup W) :=
        card_eq_two_pow hW ⊤
      rw [Subgroup.card_top, h0] at h1
      simpa using h1
    haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.mp hcardW).1
    have hbot : P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact MulEquiv.ext (fun w => Subsingleton.elim (x w) w)
    exact h.hne hbot
  have hrk6 : rk ↥(⊤ : Subgroup W) = 6 := by
    obtain ⟨m, hm⟩ := heven'
    have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by
      have hm_le : m ≤ 3 := by omega
      have hm_ne : m ≠ 0 := by
        intro h0
        exact hrk_ne0 (by rw [hm, h0, mul_zero])
      omega
    rcases hm_cases with rfl | rfl | rfl
    · exfalso
      have hMu : Nat.card (MulAut W) = 6 := w16g_card_mulAut_of_rk_eq_two hW (by omega)
      have h27 : 3 ^ 3 ∣ Nat.card (MulAut W) := dvd_trans h27dvd hPdvd
      rw [hMu] at h27
      norm_num at h27
    · exfalso
      have hMu : Nat.card (MulAut W) = 20160 := w16g_card_mulAut_of_rk_eq_four hW (by omega)
      have h27 : 3 ^ 3 ∣ Nat.card (MulAut W) := dvd_trans h27dvd hPdvd
      rw [hMu] at h27
      norm_num at h27
    · omega
  have hrkT : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
    omega
  exact ⟨hfix, hrk6, hrkT⟩

theorem w16h_inverted_card (h : Cfg132 t P) (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hrk6 : rk ↥(⊤ : Subgroup W) = 6) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzi : t * z * t⁻¹ = z⁻¹) : Nat.card P = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMu : Nat.card (MulAut W) = 20158709760 :=
    w16g_card_mulAut_of_rk_eq_six h.hW hrk6
  have hPdvd : Nat.card P ∣ 20158709760 := by
    have h' := Subgroup.card_subgroup_dvd_card P
    rwa [hMu] at h'
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq h.hP
  have hkdvd : 3 ^ k ∣ 20158709760 := by rw [← hk]; exact hPdvd
  have hk4 : k ≤ 4 := by
    by_contra hc
    have h5 : 5 ≤ k := by omega
    exact (by norm_num : ¬ (3 : ℕ) ^ 5 ∣ 20158709760)
      (dvd_trans (pow_dvd_pow 3 h5) hkdvd)
  have hnab' : ¬ ∀ x y : ↥P, x * y = y * x := by
    intro hcomm
    apply hnab
    intro x hx y hy
    exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  have h27dvd : 3 ^ 3 ∣ Nat.card P := w16g_three_cube_dvd_card_of_noncomm h.hP hnab'
  have hcardge : 27 ≤ Nat.card P := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ Nat.card P := Nat.le_of_dvd hpos h27dvd
  have hcardle : Nat.card P ≤ 81 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 81 := by norm_num
  have hk3 : 3 ≤ k := by
    have h1 : (3 : ℕ) ^ 3 ≤ 3 ^ k := by
      rw [← hk]
      exact hcardge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have hk34 : k = 3 ∨ k = 4 := by omega
  rcases hk34 with rfl | rfl
  · exfalso
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [h.ht, pow_two] at this
      exact this
    have hcent := w16h_central_of_order_27 htt h.hn h.hc (by rw [hk]; norm_num) hnab
    have htz : t * z * t⁻¹ = z := hcent z hzP hzc
    have hzinv : z = z⁻¹ := by
      calc z = t * z * t⁻¹ := htz.symm
        _ = z⁻¹ := hzi
    have hz2 : z ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hzinv]
      exact mul_inv_cancel z
    have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    rw [hz3] at hdvd2
    norm_num at hdvd2
  · rw [hk]
    norm_num

section W16GWrConstruction

open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 RegularWreathProduct

private abbrev w16g_M : Type := Multiplicative (Fin 2 → ZMod 2)

private noncomputable def w16g_Aadd : (Fin 2 → ZMod 2) ≃+ (Fin 2 → ZMod 2) where
  toFun u := fun j => if j = 0 then u 1 else u 0 + u 1
  invFun u := fun j => if j = 0 then u 0 + u 1 else u 0
  left_inv u := by
    funext j
    fin_cases j <;> simp <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, show (3 : ZMod 2) = 1 by decide]
  right_inv u := by
    funext j
    fin_cases j <;> simp <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, show (3 : ZMod 2) = 1 by decide]
  map_add' u v := by
    funext j
    fin_cases j <;> simp <;> ring_nf

private noncomputable def w16g_A : MulAut w16g_M :=
  AddEquiv.toMultiplicative w16g_Aadd

@[simp] private theorem w16g_A_apply (u : w16g_M) (j : Fin 2) :
    (w16g_A u) j = if j = 0 then u 1 else u 0 + u 1 := rfl

private theorem w16g_A_cube : w16g_A ^ 3 = 1 := by
  show w16g_A * w16g_A * w16g_A = 1
  ext u j
  change (w16g_A (w16g_A (w16g_A u))) j = u j
  fin_cases j <;> simp [w16g_A_apply] <;> ring_nf <;>
    simp [CharTwo.two_eq_zero, show (3 : ZMod 2) = 1 by decide]

private theorem w16g_A_ne_one : w16g_A ≠ 1 := by
  intro h
  have hv := congrArg (fun f : MulAut w16g_M =>
      (f (Multiplicative.ofAdd (fun j : Fin 2 => if j = 0 then (1 : ZMod 2) else 0))) 0) h
  change (fun j : Fin 2 => if j = 0 then (1 : ZMod 2) else 0) 1 =
    (fun j : Fin 2 => if j = 0 then (1 : ZMod 2) else 0) 0 at hv
  simp at hv

private theorem w16g_Apow_val_add (x y : ZMod 3) :
    w16g_A ^ (x + y).val = w16g_A ^ x.val * w16g_A ^ y.val := by
  have h3 : orderOf w16g_A = 3 := orderOf_eq_prime w16g_A_cube w16g_A_ne_one
  have hmod : w16g_A ^ ((x.val + y.val) % 3) = w16g_A ^ (x.val + y.val) := by
    have := pow_mod_orderOf w16g_A (x.val + y.val)
    rwa [h3] at this
  rw [ZMod.val_add, hmod, pow_add]

private abbrev w16g_V : Type := ZMod 3 → w16g_M

private noncomputable def w16g_phiApply (g : ZWr 1) (v : w16g_V) : w16g_V :=
  fun i => (w16g_A ^ (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i))).val)
    (v (i - Multiplicative.toAdd g.right))

private theorem w16g_phiApply_one (v : w16g_V) : w16g_phiApply 1 v = v := by
  funext i
  simp only [w16g_phiApply, RegularWreathProduct.one_left, RegularWreathProduct.one_right,
    Pi.one_apply, toAdd_one]
  rw [ZMod.val_zero, pow_zero, MulAut.one_apply]
  congr 1
  ring

private theorem w16g_conj_index (s : Multiplicative (ZMod 3)) (i : ZMod 3) :
    s⁻¹ * Multiplicative.ofAdd i = Multiplicative.ofAdd (i - Multiplicative.toAdd s) := by
  apply Multiplicative.toAdd.injective
  simp [toAdd_mul, toAdd_inv]
  abel

private theorem w16g_phiApply_mul (g h : ZWr 1) (v : w16g_V) :
    w16g_phiApply (g * h) v = w16g_phiApply g (w16g_phiApply h v) := by
  funext i
  simp only [w16g_phiApply, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
    Pi.mul_apply, toAdd_mul]
  rw [w16g_Apow_val_add, MulAut.mul_apply,
    show (i - (Multiplicative.toAdd g.right + Multiplicative.toAdd h.right)) =
      (i - Multiplicative.toAdd g.right) - Multiplicative.toAdd h.right by ring,
    ← w16g_conj_index g.right i]
  rfl

private noncomputable def w16g_phiFun (g : ZWr 1) : MulAut w16g_V where
  toFun := w16g_phiApply g
  invFun := w16g_phiApply g⁻¹
  left_inv v := by
    rw [← w16g_phiApply_mul, inv_mul_cancel, w16g_phiApply_one]
  right_inv v := by
    rw [← w16g_phiApply_mul, mul_inv_cancel, w16g_phiApply_one]
  map_mul' v w := by
    funext i
    simp only [w16g_phiApply, Pi.mul_apply, map_mul]

private noncomputable def w16g_phi : ZWr 1 →* MulAut w16g_V where
  toFun := w16g_phiFun
  map_one' := by
    apply MulEquiv.ext
    intro v
    rw [MulAut.one_apply]
    exact w16g_phiApply_one v
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    rw [MulAut.mul_apply]
    exact w16g_phiApply_mul g h v

@[simp] private theorem w16g_phi_apply (g : ZWr 1) (v : w16g_V) :
    w16g_phi g v = w16g_phiApply g v := rfl

private def w16g_u0 : w16g_M :=
  Multiplicative.ofAdd (fun j : Fin 2 => if j = 0 then (1 : ZMod 2) else 0)

private theorem w16g_u0_ne_one : w16g_u0 ≠ 1 := by
  intro h
  have h0 : w16g_u0 0 = (1 : w16g_M) 0 := by rw [h]
  have hL : w16g_u0 0 = (1 : ZMod 2) := by
    change (if (0 : Fin 2) = 0 then (1 : ZMod 2) else 0) = 1
    simp
  have hR : (1 : w16g_M) 0 = (0 : ZMod 2) := rfl
  rw [hL, hR] at h0
  exact one_ne_zero h0

private def w16g_v0 : w16g_V := fun i => if i = 0 then w16g_u0 else 1

private theorem w16g_right_eq_one_of_phi_eq_one (g : ZWr 1) (hg : w16g_phi g = 1) :
    g.right = 1 := by
  by_contra hne
  have hσ : Multiplicative.toAdd g.right ≠ 0 := by
    intro h
    apply hne
    apply Multiplicative.toAdd.injective
    simpa using h
  have hsub : (0 : ZMod 3) - Multiplicative.toAdd g.right ≠ 0 := by
    intro h
    apply hσ
    have h' : (0 : ZMod 3) = Multiplicative.toAdd g.right := by
      have := sub_eq_zero.mp h
      simpa using this
    exact h'.symm
  have hv := congrFun (congrArg (fun f : MulAut w16g_V => f w16g_v0) hg) 0
  simp only [w16g_phi_apply, MulAut.one_apply, w16g_phiApply] at hv
  have harg : w16g_v0 ((0 : ZMod 3) - Multiplicative.toAdd g.right) = 1 := by
    unfold w16g_v0
    rw [if_neg hsub]
  rw [harg, map_one] at hv
  have h0 : w16g_v0 0 = w16g_u0 := by
    unfold w16g_v0
    rw [if_pos rfl]
  rw [h0] at hv
  exact w16g_u0_ne_one hv.symm

private theorem w16g_left_eq_one_of_phi_eq_one (g : ZWr 1) (hg : w16g_phi g = 1)
    (hr : g.right = 1) : g.left = 1 := by
  have hto : Multiplicative.toAdd g.right = 0 := by rw [hr]; rfl
  have hleft : ∀ i : ZMod 3, g.left (Multiplicative.ofAdd i) = 1 := by
    intro i
    have hA : ∀ u : w16g_M,
        (w16g_A ^ (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i))).val) u = u := by
      intro u
      let v : w16g_V := fun j => if j = i then u else 1
      have hv := congrFun (congrArg (fun f : MulAut w16g_V => f v) hg) i
      simp only [w16g_phi_apply, MulAut.one_apply, w16g_phiApply] at hv
      have hvi : v (i - Multiplicative.toAdd g.right) = v i := by
        apply congrArg v
        rw [hto]
        ring
      rw [hvi] at hv
      have hvi' : v i = u := by
        unfold v
        rw [if_pos rfl]
      rwa [hvi'] at hv
    have hp : w16g_A ^ (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i))).val = 1 :=
      MulEquiv.ext (fun u => by simpa using hA u)
    have h3 : orderOf w16g_A = 3 := orderOf_eq_prime w16g_A_cube w16g_A_ne_one
    have hdvd : 3 ∣ (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i))).val := by
      rwa [← orderOf_dvd_iff_pow_eq_one, h3] at hp
    have hzero : (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i))).val = 0 := by
      have hlt := ZMod.val_lt (Multiplicative.toAdd (g.left (Multiplicative.ofAdd i)))
      omega
    have hz : Multiplicative.toAdd (g.left (Multiplicative.ofAdd i)) = 0 :=
      (ZMod.val_eq_zero _).mp hzero
    apply Multiplicative.toAdd.injective
    simpa using hz
  funext q
  rw [show q = Multiplicative.ofAdd (Multiplicative.toAdd q) from
    (ofAdd_toAdd q).symm]
  exact hleft (Multiplicative.toAdd q)

private theorem w16g_phi_eq_one_iff (g : ZWr 1) (hg : w16g_phi g = 1) : g = 1 := by
  have hr := w16g_right_eq_one_of_phi_eq_one g hg
  have hl := w16g_left_eq_one_of_phi_eq_one g hg hr
  exact RegularWreathProduct.ext hl hr

private theorem w16g_phi_injective : Function.Injective w16g_phi := by
  intro g h hgh
  have h1 : w16g_phi (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  have := w16g_phi_eq_one_iff (g * h⁻¹) h1
  rwa [mul_inv_eq_one] at this

private theorem w16g_isZ3WrZ3_ZWr_one : IsZ3WrZ3 (ZWr 1) := by
  have hcard : Nat.card (ZWr 1) = 81 := by
    rw [RegularWreathProduct.card]
    norm_num [Nat.card_eq_fintype_card, ZMod.card]
  let z : Fin 3 → ZWr 1 := fun i =>
    el 1 (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0) 0
  let b : ZWr 1 := el 1 0 0 0 1
  have hb3 : b ^ 3 = 1 := by
    rw [show b = el 1 0 0 0 1 from rfl]
    rw [show (el 1 0 0 0 1 : ZWr 1) ^ 3 =
      el 1 0 0 0 1 * el 1 0 0 0 1 * el 1 0 0 0 1 by
        rw [pow_succ, pow_two]]
    rw [el_mul_one]
    rw [show (1 : ZMod 3) + 1 = 2 by decide]
    rw [el_mul_two]
    rw [← el_zero_zero]
    congr 1 <;> decide
  have hb_inv : b⁻¹ = el 1 0 0 0 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [show b = el 1 0 0 0 1 from rfl, el_mul_one]
    rw [← el_zero_zero]
    congr 1 <;> decide
  have hz3 : ∀ i, z i ^ 3 = 1 := by
    intro i
    fin_cases i <;> rw [el_pow_base] <;>
      rw [← el_zero_zero] <;> congr 1 <;> decide
  have hzcomm : ∀ i j, Commute (z i) (z j) := by
    intro i j
    exact base_comm (by simp [z]) (by simp [z])
  have hconj : ∀ i, b * z i * b⁻¹ = z (i + 1) := by
    intro i
    fin_cases i <;>
      simp [z, b, hb_inv, el_mul_one, el_mul_zero, el_left_zero, el_left_one, el_left_two,
        show (1 : ZMod 3) + 2 = 0 by decide]
  have hbe_all : ∀ e : ZMod 3, el 1 0 0 0 e = b ^ e.val := by
    intro e
    rcases zmod3_cases e with rfl | rfl | rfl
    · rw [show (0 : ZMod 3).val = 0 by decide, pow_zero, el_zero_zero]
    · rw [show (1 : ZMod 3).val = 1 by decide]
      simp
      rfl
    · rw [show (2 : ZMod 3).val = 2 by decide]
      rw [show b ^ 2 = el 1 0 0 0 2 by
        rw [show b = el 1 0 0 0 1 from rfl, pow_two, el_mul_one]
        norm_num [el_zero_zero]]
  have hgen : Subgroup.closure (Set.range z ∪ {b}) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [el_eta w]
    have hza : el 1 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) 0 0 0 =
        (z 0) ^ (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))).val := by
      rw [show z 0 = el 1 1 0 0 0 from rfl, el_pow_base]
      congr 1 <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hzb : el 1 0 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) 0 0 =
        (z 1) ^ (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))).val := by
      rw [show z 1 = el 1 0 1 0 0 from rfl, el_pow_base]
      congr 1 <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hzc : el 1 0 0 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))) 0 =
        (z 2) ^ (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))).val := by
      rw [show z 2 = el 1 0 0 1 0 from rfl, el_pow_base]
      congr 1 <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hbe : el 1 0 0 0 (Multiplicative.toAdd w.right) =
        b ^ (Multiplicative.toAdd w.right).val :=
      hbe_all (Multiplicative.toAdd w.right)
    rw [show el 1 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0)))
          (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1)))
          (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2)))
          (Multiplicative.toAdd w.right) =
        el 1 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) 0 0 0 *
        el 1 0 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) 0 0 *
        el 1 0 0 (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))) 0 *
        el 1 0 0 0 (Multiplicative.toAdd w.right) by
      rw [el_mul_zero, el_mul_zero, el_mul_zero]
      congr 1 <;> abel]
    rw [hza, hzb, hzc, hbe]
    let C : Subgroup (ZWr 1) := Subgroup.closure (Set.range z ∪ {b})
    have hz0C : z 0 ∈ C := Subgroup.subset_closure (show z 0 ∈ Set.range z ∪ {b} from
      Or.inl ⟨0, rfl⟩)
    have hz1C : z 1 ∈ C := Subgroup.subset_closure (show z 1 ∈ Set.range z ∪ {b} from
      Or.inl ⟨1, rfl⟩)
    have hz2C : z 2 ∈ C := Subgroup.subset_closure (show z 2 ∈ Set.range z ∪ {b} from
      Or.inl ⟨2, rfl⟩)
    have hbC : b ∈ C := Subgroup.subset_closure (show b ∈ Set.range z ∪ {b} from
      Or.inr rfl)
    exact Subgroup.mul_mem C
      (Subgroup.mul_mem C
        (Subgroup.mul_mem C
          (Subgroup.pow_mem C hz0C _)
          (Subgroup.pow_mem C hz1C _))
        (Subgroup.pow_mem C hz2C _))
      (Subgroup.pow_mem C hbC _)
  exact ⟨hcard, z, b, hz3, hzcomm, hb3, hconj, hgen⟩

private noncomputable def w16g_Viso1 :
    Multiplicative (Fin 6 → ZMod 2) ≃*
      Multiplicative ((Fin 3 × Fin 2) → ZMod 2) :=
  { Equiv.piCongrLeft' (fun _ => ZMod 2)
      (finProdFinEquiv (m := 3) (n := 2)).symm with
    map_mul' := fun _ _ => rfl }

private noncomputable def w16g_Viso2 :
    Multiplicative ((Fin 3 × Fin 2) → ZMod 2) ≃*
      Multiplicative (Fin 3 → Fin 2 → ZMod 2) :=
  { Equiv.curry (Fin 3) (Fin 2) (ZMod 2) with
    map_mul' := fun _ _ => rfl }

private noncomputable def w16g_Viso3 :
    Multiplicative (Fin 3 → Fin 2 → ZMod 2) ≃* (Fin 3 → w16g_M) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

private noncomputable def w16g_Viso4 :
    (Fin 3 → w16g_M) ≃* (ZMod 3 → w16g_M) :=
  { Equiv.piCongrLeft' (fun _ => w16g_M) (ZMod.finEquiv 3).toEquiv with
    map_mul' := fun _ _ => rfl }

private noncomputable def w16g_Viso :
    Multiplicative (Fin 6 → ZMod 2) ≃* w16g_V :=
  w16g_Viso1.trans (w16g_Viso2.trans (w16g_Viso3.trans w16g_Viso4))

private theorem w16g_exists_wr_subgroup_aux
    (hW : ∀ w : W, w ^ 2 = 1) (hrk6 : rk ↥(⊤ : Subgroup W) = 6) :
    ∃ S : Subgroup (MulAut W), Nat.card S = 81 ∧ IsZ3WrZ3 ↥S := by
  classical
  have hcardW : Nat.card W = 2 ^ 6 := by
    rw [← Subgroup.card_top, card_eq_two_pow hW ⊤, hrk6]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) hW hcardW
  let WV : W ≃* w16g_V := e.trans w16g_Viso
  let phiW : ZWr 1 →* MulAut W := (MulAut.congr WV.symm).toMonoidHom.comp w16g_phi
  have hinj : Function.Injective phiW := by
    intro g h hgh
    apply w16g_phi_injective
    apply (MulAut.congr WV.symm).injective
    exact hgh
  refine ⟨phiW.range, ?_, ?_⟩
  · have h := Subgroup.card_map_of_injective (K := ⊤) hinj
    rw [MonoidHom.range_eq_map, h, Subgroup.card_top, w16g_isZ3WrZ3_ZWr_one.1]
  · have hiso : ZWr 1 ≃* ↥phiW.range := by
      have h := (Subgroup.topEquiv (G := ZWr 1)).symm.trans
        (Subgroup.equivMapOfInjective (⊤ : Subgroup (ZWr 1)) phiW hinj)
      rwa [← MonoidHom.range_eq_map] at h
    exact w16g_isZ3WrZ3_of_mulEquiv hiso w16g_isZ3WrZ3_ZWr_one

end W16GWrConstruction

theorem w16g_exists_wr_subgroup (hW : ∀ w : W, w ^ 2 = 1)
    (hrk6 : rk ↥(⊤ : Subgroup W) = 6) :
    ∃ S : Subgroup (MulAut W), Nat.card S = 81 ∧ IsZ3WrZ3 ↥S :=
  w16g_exists_wr_subgroup_aux hW hrk6

private theorem w16g_sylow_conj (hW : ∀ w : W, w ^ 2 = 1) (hrk6 : rk ↥(⊤ : Subgroup W) = 6)
    {P Q : Subgroup (MulAut W)} (hP : Nat.card P = 81) (hQ : Nat.card Q = 81) :
    ∃ g : MulAut W, Q = P.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMu : Nat.card (MulAut W) = 20158709760 := w16g_card_mulAut_of_rk_eq_six hW hrk6
  have hPp : IsPGroup 3 ↥P := IsPGroup.of_card (n := 4) (by rw [hP]; norm_num)
  have hQp : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 4) (by rw [hQ]; norm_num)
  have hPidx : P.index = 248872960 := by
    have h := Subgroup.card_mul_index P
    rw [hP, hMu] at h
    omega
  have hQidx : Q.index = 248872960 := by
    have h := Subgroup.card_mul_index Q
    rw [hQ, hMu] at h
    omega
  have hPnot : ¬ 3 ∣ P.index := by rw [hPidx]; norm_num
  have hQnot : ¬ 3 ∣ Q.index := by rw [hQidx]; norm_num
  let SP : Sylow 3 (MulAut W) := hPp.toSylow hPnot
  let SQ : Sylow 3 (MulAut W) := hQp.toSylow hQnot
  have hSPcoe : (SP : Subgroup (MulAut W)) = P := by
    ext x
    exact IsPGroup.mem_toSylow hPp hPnot
  have hSQcoe : (SQ : Subgroup (MulAut W)) = Q := by
    ext x
    exact IsPGroup.mem_toSylow hQp hQnot
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut W) SP SQ
  refine ⟨g, ?_⟩
  have h : (↑(g • SP) : Subgroup (MulAut W)) = ↑SQ := by rw [hg]
  have hmap : (↑(g • SP) : Subgroup (MulAut W)) = P.map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hSPcoe]
    congr 1
  rw [hmap, hSQcoe] at h
  exact h.symm

private theorem w16g_wr_unique_extraspecial {X : Type} [Group X] (hX : IsZ3WrZ3 X) :
    ∃ M : Subgroup X, IsPOnePlusTwo 3 ↥M ∧ (∀ Q : Subgroup X, IsPOnePlusTwo 3 ↥Q → Q = M) ∧
      (∀ c ∈ Subgroup.center X, c ∈ M) := by
  obtain ⟨e⟩ := W16GTwoCB.w16g_nonempty_mulEquiv_zwr_one hX
  exact W16GTwoCB.w16g_wr_unique_of_mulEquiv e

theorem w16h_isZ3WrZ3_of_card_81 (hW : ∀ w : W, w ^ 2 = 1) (hrk6 : rk ↥(⊤ : Subgroup W) = 6)
    (hP : IsPGroup 3 ↥P) (hcard : Nat.card P = 81) : IsZ3WrZ3 ↥P := by
  obtain ⟨S, hScard, hSwr⟩ := w16g_exists_wr_subgroup hW hrk6
  obtain ⟨g, hg⟩ := w16g_sylow_conj hW hrk6 (P := S) (Q := P) hScard hcard
  have h := w16g_isZ3WrZ3_of_mulEquiv
    (Subgroup.equivMapOfInjective S (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hSwr
  rw [← hg] at h
  exact h

theorem w16h_wr_extraspecial (hrk6 : rk ↥(⊤ : Subgroup W) = 6) (hwr : IsZ3WrZ3 ↥P)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hfix : ∀ u : W, z u = u → u = 1) :
    ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6 := by
  classical
  obtain ⟨M, hMext, hMuniq, hMcent⟩ := w16g_wr_unique_extraspecial hwr
  have hzcent : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hzc y.1 y.2)
  have hzM : (⟨z, hzP⟩ : ↥P) ∈ M := hMcent _ hzcent
  refine ⟨M.map P.subtype, ⟨Subgroup.map_subtype_le M, ?_, ?_⟩, ?_⟩
  · exact w16g_isPOnePlusTwo_of_mulEquiv
      (Subgroup.equivMapOfInjective M P.subtype P.subtype_injective) hMext
  · have htop : commSub ⊤ (Subgroup.zpowers z) = ⊤ := w16g_commSub_zpowers_eq_top hfix
    have hzQ : z ∈ M.map P.subtype := Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, hzM, rfl⟩
    have hle : commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ (M.map P.subtype) :=
      commSub_mono le_rfl (Subgroup.zpowers_le.mpr hzQ)
    have htop' : commSub ⊤ (M.map P.subtype) = ⊤ := by
      apply top_le_iff.mp
      calc (⊤ : Subgroup W) = commSub ⊤ (Subgroup.zpowers z) := htop.symm
        _ ≤ commSub ⊤ (M.map P.subtype) := hle
    rw [htop']
    exact hrk6
  · rintro Q ⟨hQP, hQext, -⟩
    have hQsubext : IsPOnePlusTwo 3 ↥(Q.subgroupOf P) :=
      w16g_isPOnePlusTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQP).symm hQext
    have hQsub : Q.subgroupOf P = M := hMuniq _ hQsubext
    have h1 : (Q.subgroupOf P).map P.subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQP]
    rw [hQsub] at h1
    exact h1.symm

theorem w16h_inverted (h : Cfg132 t P) (hind : NoDecomp132 t P)
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzi : t * z * t⁻¹ = z⁻¹) :
    IsZ3WrZ3 ↥P ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
      ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6 := by
  obtain ⟨hfix, hrk6, hrkT⟩ := w16h_inverted_rank h hind hnab hzP hz3 hzc hzi
  have hcard : Nat.card P = 81 := w16h_inverted_card h hnab hrk6 hzP hz3 hzc hzi
  have hwr : IsZ3WrZ3 ↥P := w16h_isZ3WrZ3_of_card_81 h.hW hrk6 h.hP hcard
  have hext := w16h_wr_extraspecial hrk6 hwr hzP hz3 hzc hfix
  exact ⟨hwr, hrkT, hext⟩

end CFSG.LocalAnalysis.WeakClosure81
