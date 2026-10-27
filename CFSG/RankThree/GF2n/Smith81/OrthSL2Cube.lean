module

public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Centralizer

theorem orth_comm_entries {F : Type*} [Field F] [CharP F 2] {a b c d x y z w : F}
    (h11 : a * a + b * c = 1) (h12 : a * b + b * d = 0) (h21 : c * a + d * c = 0)
    (h22 : c * b + d * d = 1) (hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1))
    (e1 : a * x + b * z = x * a + y * c) (e2 : a * y + b * w = x * b + y * d)
    (e3 : c * x + d * z = z * a + w * c) (e4 : c * y + d * w = z * b + w * d) :
    (b ≠ 0 ∨ c ≠ 0) ∧ x = w ∧ y * c = z * b ∧ a = d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq1 : ∀ r : F, r * r = 1 → r = 1 := by
    intro r hr
    have : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination this
  have had : a = d := by
    by_contra hne'
    have hs : a + d ≠ 0 := fun h => hne' (by linear_combination h - d * h2)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination h12
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination h21
      exact (mul_eq_zero.mp this).resolve_right hs
    subst hb hc
    have ha1 : a = 1 := hsq1 a (by linear_combination h11)
    have hd1 : d = 1 := hsq1 d (by linear_combination h22)
    exact hne' (ha1.trans hd1.symm)
  subst had
  have hbc : b ≠ 0 ∨ c ≠ 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨hb, hc⟩ := hh
    subst hb hc
    have ha1 : a = 1 := hsq1 a (by linear_combination h11)
    exact hne ⟨ha1, rfl, rfl, ha1⟩
  have hxw : x = w := by
    have h2' : (x - w) * b = 0 := by linear_combination (-1 : F) * e2
    have h3' : (x - w) * c = 0 := by linear_combination e3
    rcases hbc with hb | hc
    · have := (mul_eq_zero.mp h2').resolve_right hb
      linear_combination this
    · have := (mul_eq_zero.mp h3').resolve_right hc
      linear_combination this
  exact ⟨hbc, hxw, by linear_combination (-1 : F) * e1, rfl⟩

theorem orth_centralizer_entries {F : Type*} [Field F] [CharP F 2] {a b c d : F}
    (hX2 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] = 1)
    (hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1)) (Y : Matrix (Fin 2) (Fin 2) F)
    (hY : Y.det = 1) (hc : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * Y =
      Y * !![a, b; c, d]) :
    (b ≠ 0 ∨ c ≠ 0) ∧ ∃ x y z : F, Y = !![x, y; z, x] ∧ y * c = z * b ∧ x * x + y * z = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h11 : a * a + b * c = 1 := by
    have := congrFun (congrFun hX2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h12 : a * b + b * d = 0 := by
    have := congrFun (congrFun hX2 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h21 : c * a + d * c = 0 := by
    have := congrFun (congrFun hX2 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h22 : c * b + d * d = 1 := by
    have := congrFun (congrFun hX2 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  obtain ⟨x, y, z, w, hYe⟩ : ∃ x y z w : F, Y = !![x, y; z, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two Y⟩
  subst hYe
  have e1 : a * x + b * z = x * a + y * c := by
    have := congrFun (congrFun hc 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e2 : a * y + b * w = x * b + y * d := by
    have := congrFun (congrFun hc 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e3 : c * x + d * z = z * a + w * c := by
    have := congrFun (congrFun hc 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e4 : c * y + d * w = z * b + w * d := by
    have := congrFun (congrFun hc 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  obtain ⟨hbc, hxw, hyz, had⟩ := orth_comm_entries h11 h12 h21 h22 hne e1 e2 e3 e4
  subst hxw
  refine ⟨hbc, x, y, z, rfl, hyz, ?_⟩
  have hd : x * x - y * z = 1 := by simpa [Matrix.det_fin_two] using hY
  linear_combination hd + (y * z) * h2

theorem orth_involution_entries {F : Type*} [Field F] [CharP F 2]
    (u : Matrix.SpecialLinearGroup (Fin 2) F) (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    ∃ a b c d : F, (u : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] ∧
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] = 1 ∧
      ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) := by
  obtain ⟨a, b, c, d, hX⟩ : ∃ a b c d : F, (u : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hsq : (u : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F)) hu2
    simpa using this
  rw [hX] at hsq
  refine ⟨a, b, c, d, hX, hsq, ?_⟩
  rintro ⟨rfl, rfl, rfl, rfl⟩
  apply hu1
  apply Subtype.ext
  rw [hX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem orth_centralizer_data {F : Type*} [Field F] [CharP F 2]
    {u : Matrix.SpecialLinearGroup (Fin 2) F} {a b c d : F}
    (hX : (u : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d])
    (hsq : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] = 1)
    (hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1))
    (g : Subgroup.centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    (b ≠ 0 ∨ c ≠ 0) ∧ ∃ x y z : F,
      ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![x, y; z, x] ∧ y * c = z * b ∧ x * x + y * z = 1 := by
  have hg := Subgroup.mem_centralizer_iff.mp g.2 u rfl
  have hg' : (u : Matrix (Fin 2) (Fin 2) F) *
      ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (u : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) F =>
      (h : Matrix (Fin 2) (Fin 2) F)) hg
    simpa using this
  rw [hX] at hg'
  exact orth_centralizer_entries hsq hne _ (g : Matrix.SpecialLinearGroup (Fin 2) F).det_coe hg'

theorem orth_centralizer_sq {F : Type*} [Field F] [CharP F 2]
    (u : Matrix.SpecialLinearGroup (Fin 2) F) (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (g : Subgroup.centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    (g : Matrix.SpecialLinearGroup (Fin 2) F) * (g : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  obtain ⟨a, b, c, d, hX, hsq, hne⟩ := orth_involution_entries u hu1 hu2
  obtain ⟨-, x, y, z, hg, -, hdet⟩ := orth_centralizer_data hX hsq hne g
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e2 : x * y + y * x = 0 := by linear_combination (x * y) * h2
  have e3 : z * x + x * z = 0 := by linear_combination (x * z) * h2
  have e4 : z * y + x * x = 1 := by linear_combination hdet
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.mul_fin_two, hdet, e2, e3, e4]
  simp [Matrix.one_fin_two]

end Centralizer

section StatedSL

theorem orth_isPGroup_centralizer_of_equiv {A F : Type} [Group A] [Field F] [CharP F 2]
    (eA : A ≃* StatedSL 2 F) {u : A} (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    IsPGroup 2 ↥(Subgroup.centralizer ({u} : Set A)) := by
  set e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    eA.trans (specialLinearGroupEquivStatedSL 2 F).symm with he
  have h1 : e u ≠ 1 := fun h => hu1 (by simpa using congrArg e.symm h)
  have h2 : e u * e u = 1 := by rw [← map_mul, hu2, map_one]
  intro g
  refine ⟨1, ?_⟩
  have hmem : e (g : A) ∈ Subgroup.centralizer ({e u} :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp g.2 u rfl]
  have hsq : (g : A) * (g : A) = 1 :=
    e.injective (by rw [map_mul, map_one]; exact orth_centralizer_sq (e u) h1 h2 ⟨e g, hmem⟩)
  exact Subtype.ext (by simpa [pow_two] using hsq)

theorem orth_odd_sq_sub_one {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) : Odd (q ^ 2 - 1) := by
  obtain ⟨r, hr⟩ := hq
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s := ⟨r, by omega⟩
  have hs : 1 ≤ s := by omega
  refine ⟨2 * s ^ 2 - 1, ?_⟩
  have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
  have h4 : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
  omega

open CFSG.Assembly.LowTwoRank in
theorem orth_not_pgroup_statedSL {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ¬ IsPGroup 2 ↥(StatedSL 2 F) := by
  intro h2
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hodd := orth_odd_sq_sub_one (orth_even_card F) (by omega)
  rw [CFSG.Open.StatedAPI.card_statedSL_two F] at hj
  have h16 : 16 ≤ Nat.card F ^ 2 := by nlinarith
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show Nat.card F ^ 2 - 1 ≠ 1 by omega)
  have h3 : p ∣ 2 ^ j := hj ▸ dvd_mul_of_dvd_right hpd _
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3)
  subst hp2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)

theorem orth_isPGroup_map {G H : Type*} [Group G] [Group H] {W : Subgroup G}
    (hW : IsPGroup 2 ↥W) (f : G →* H) : IsPGroup 2 ↥(W.map f) := by
  intro y
  obtain ⟨w, hw, hwy⟩ := y.2
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : w ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  show (y : H) ^ (2 ^ k) = 1
  rw [← hwy, ← map_pow, h1, map_one]

theorem orth_normal_pgroup_prod_eq_bot {Γ₂ Γ₃ : Type*} [Group Γ₂] [Group Γ₃] [IsSimpleGroup Γ₂]
    [IsSimpleGroup Γ₃] (h2 : ¬ IsPGroup 2 Γ₂) (h3 : ¬ IsPGroup 2 Γ₃)
    {W : Subgroup (Γ₂ × Γ₃)} [hWn : W.Normal] (hW : IsPGroup 2 ↥W) : W = ⊥ := by
  have hs1 : Function.Surjective (MonoidHom.fst Γ₂ Γ₃) := fun a => ⟨(a, 1), rfl⟩
  have hs2 : Function.Surjective (MonoidHom.snd Γ₂ Γ₃) := fun b => ⟨(1, b), rfl⟩
  haveI hn1 : (W.map (MonoidHom.fst Γ₂ Γ₃)).Normal := Subgroup.Normal.map hWn _ hs1
  haveI hn2 : (W.map (MonoidHom.snd Γ₂ Γ₃)).Normal := Subgroup.Normal.map hWn _ hs2
  have hb1 : W.map (MonoidHom.fst Γ₂ Γ₃) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map (MonoidHom.fst Γ₂ Γ₃)) with h | h
    · exact h
    · exfalso
      have hp := orth_isPGroup_map hW (MonoidHom.fst Γ₂ Γ₃)
      rw [h] at hp
      exact h2 (hp.of_equiv Subgroup.topEquiv)
  have hb2 : W.map (MonoidHom.snd Γ₂ Γ₃) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map (MonoidHom.snd Γ₂ Γ₃)) with h | h
    · exact h
    · exfalso
      have hp := orth_isPGroup_map hW (MonoidHom.snd Γ₂ Γ₃)
      rw [h] at hp
      exact h3 (hp.of_equiv Subgroup.topEquiv)
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hx
  have ha : a ∈ W.map (MonoidHom.fst Γ₂ Γ₃) := ⟨(a, b), hx, rfl⟩
  have hb : b ∈ W.map (MonoidHom.snd Γ₂ Γ₃) := ⟨(a, b), hx, rfl⟩
  rw [hb1, Subgroup.mem_bot] at ha
  rw [hb2, Subgroup.mem_bot] at hb
  rw [Subgroup.mem_bot]
  exact Prod.ext ha hb

theorem orth_normal_pgroup_eq_bot_of_equiv {B' : Type*} [Group B'] {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) (eB : B' ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K))
    {W : Subgroup B'} [hWn : W.Normal] (hW : IsPGroup 2 ↥W) : W = ⊥ := by
  haveI : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.RankThree.GF2n.Stroth80.isSimpleGroup_statedSL_two
      (CFSG.RankThree.GF2n.Stroth80.statedSL_quasisimple_of_card 2 K le_rfl hK)
  haveI : (W.map eB.toMonoidHom).Normal := Subgroup.Normal.map hWn _ eB.surjective
  have h := orth_normal_pgroup_prod_eq_bot (orth_not_pgroup_statedSL hK)
    (orth_not_pgroup_statedSL hK) (W := W.map eB.toMonoidHom) (orth_isPGroup_map hW _)
  exact (Subgroup.map_eq_bot_iff_of_injective W eB.injective).mp h

end StatedSL

section BarRt

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_bar_Rt_le_of_forall [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    {X : Subgroup (Mbar M Q)}
    (h : ∀ m : ↥M, t ∈ conjSubgroup (m : G) (LB M Q B) → ∀ y : ↥M,
      (y : G) ∈ conjSubgroup (m : G) (LB M Q B) → (QuotientGroup.mk y : Mbar M Q) ∈ X) :
    bar M Q (Rt M (LB M Q B) t) ≤ X := by
  set P : Subgroup G := (X.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype with hP
  have hRP : Rt M (LB M Q B) t ≤ P := by
    refine iSup_le fun m => iSup_le fun hm => iSup_le fun htm => ?_
    intro g hg
    have hgM : g ∈ M := by
      rw [mem_conjSubgroup] at hg
      have h1 : (m : G)⁻¹ * g * m ∈ M := hc.LB_le_M hg
      have h2 : g = m * ((m : G)⁻¹ * g * m) * m⁻¹ := by group
      rw [h2]
      exact M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
    exact Subgroup.mem_map.mpr ⟨⟨g, hgM⟩, h ⟨m, hm⟩ htm ⟨g, hgM⟩ hg, rfl⟩
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp (hRP (Subgroup.mem_subgroupOf.mp hy))
  have : y' = y := Subtype.ext hy'eq
  subst this
  exact hy'

end BarRt

section NtBar

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem orth_Nt_le_Rt (M L : Subgroup G) (t : G) : Nt M L t ≤ Rt M L t :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem orth_Nt_isPGroup (M L : Subgroup G) (t : G) : IsPGroup 2 ↥(Nt M L t) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Rt M L t))).of_equiv
    (Subgroup.equivMapOfInjective _ (Rt M L t).subtype (Subgroup.subtype_injective _))

omit [Finite G] in
theorem orth_Nt_conj_mem (M L : Subgroup G) (t : G) {r x : G} (hr : r ∈ Rt M L t)
    (hx : x ∈ Nt M L t) : r * x * r⁻¹ ∈ Nt M L t := by
  obtain ⟨x', hx', rfl⟩ := hx
  have h := (CFSG.pCore_normal (p := 2) (G := ↥(Rt M L t))).conj_mem x' hx' ⟨r, hr⟩
  exact ⟨⟨r, hr⟩ * x' * ⟨r, hr⟩⁻¹, h, by simp⟩

theorem orth_isPGroup_bar_Nt [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (t : G) :
    IsPGroup 2 ↥(bar M Q (Nt M (LB M Q B) t)) := by
  have hle : Nt M (LB M Q B) t ≤ M := (orth_Nt_le_Rt _ _ t).trans (hc.Rt_le_M t)
  have h1 : IsPGroup 2 ↥((Nt M (LB M Q B) t).subgroupOf M) :=
    (orth_Nt_isPGroup (M := M) (LB M Q B) t).of_equiv
      (Subgroup.subgroupOfEquivOfLe hle).symm
  exact orth_isPGroup_map h1 _

theorem orth_bar_Nt_conj_mem [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (t : G)
    {r : Mbar M Q} (hr : r ∈ bar M Q (Rt M (LB M Q B) t)) {n : Mbar M Q}
    (hn : n ∈ bar M Q (Nt M (LB M Q B) t)) : r * n * r⁻¹ ∈ bar M Q (Nt M (LB M Q B) t) := by
  obtain ⟨r', hr', rfl⟩ := hr
  obtain ⟨n', hn', rfl⟩ := hn
  have hr'' : (r' : G) ∈ Rt M (LB M Q B) t := hr'
  have hn'' : (n' : G) ∈ Nt M (LB M Q B) t := hn'
  refine ⟨r' * n' * r'⁻¹, ?_, by simp⟩
  show ((r' * n' * r'⁻¹ : ↥M) : G) ∈ Nt M (LB M Q B) t
  simpa using orth_Nt_conj_mem _ _ t hr'' hn''

theorem orth_bar_pgroup_le_bar_Nt [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {D : Subgroup (Mbar M Q)} (hD : D ≤ bar M Q (Rt M (LB M Q B) t))
    (hD2 : IsPGroup 2 ↥D)
    (hDn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ d ∈ D, r * d * r⁻¹ ∈ D) :
    D ≤ bar M Q (Nt M (LB M Q B) t) := by
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  let f : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hf : ∀ r : ↥(Rt M (LB M Q B) t),
      f r = QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hRM r.2⟩ := fun r => rfl
  have hfR : ∀ r : ↥(Rt M (LB M Q B) t), f r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  have hker : IsPGroup 2 ↥f.ker := by
    have hkle : f.ker ≤ Q.subgroupOf (Rt M (LB M Q B) t) := by
      intro r hr
      have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hRM r.2⟩ = 1 := hr
      have h2 : (⟨(r : G), hRM r.2⟩ : ↥M) ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h2)
    have hQ2 : IsPGroup 2 ↥(Q.subgroupOf (Rt M (LB M Q B) t)) :=
      (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
    exact hQ2.of_injective (Subgroup.inclusion hkle) (Subgroup.inclusion_injective _)
  have hp : IsPGroup 2 ↥(D.comap f) := hD2.comap_of_ker_isPGroup f hker
  haveI hnorm : (D.comap f).Normal := ⟨fun x hx r => by
    show f (r * x * r⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact hDn (f r) (hfR r) (f x) hx⟩
  have hle : D.comap f ≤ CFSG.pCore 2 ↥(Rt M (LB M Q B) t) := le_sSup ⟨hnorm, hp⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hD hz
  have hyR : (y : G) ∈ Rt M (LB M Q B) t := hy
  have hyD : f ⟨(y : G), hyR⟩ ∈ D := hz
  have hmem : ((⟨(y : G), hyR⟩ : ↥(Rt M (LB M Q B) t)) : G) ∈ Nt M (LB M Q B) t :=
    ⟨⟨(y : G), hyR⟩, hle hyD, rfl⟩
  exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩

theorem orth_card_mul_of_inf_eq_bot {H : Type*} [Group H] {R N X : Subgroup H}
    (hNR : N ≤ R) (hXR : X ≤ R) (hNX : N ⊓ X = ⊥)
    (h : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x) :
    Nat.card R = Nat.card N * Nat.card X := by
  have hbij : Function.Bijective (fun p : N × X =>
      (⟨(p.1 : H) * (p.2 : H), R.mul_mem (hNR p.1.2) (hXR p.2.2)⟩ : R)) := by
    constructor
    · intro p q hpq
      have h1 : (p.1 : H) * (p.2 : H) = (q.1 : H) * (q.2 : H) := congrArg Subtype.val hpq
      have h2 : (q.1 : H)⁻¹ * (p.1 : H) = (q.2 : H) * (p.2 : H)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
        exact h1.symm ▸ rfl
      have h3 : (q.1 : H)⁻¹ * (p.1 : H) ∈ N ⊓ X :=
        ⟨N.mul_mem (N.inv_mem q.1.2) p.1.2, h2 ▸ X.mul_mem q.2.2 (X.inv_mem p.2.2)⟩
      rw [hNX, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : p.1 = q.1 := Subtype.ext h3.symm
      have h5 : (p.2 : H) = q.2 := by
        have : (p.1 : H) * (p.2 : H) = (p.1 : H) * (q.2 : H) := by rw [h1, h3]
        exact mul_left_cancel this
      exact Prod.ext h4 (Subtype.ext h5)
    · rintro ⟨r, hr⟩
      obtain ⟨n, hn, x, hx, rfl⟩ := h r hr
      exact ⟨(⟨n, hn⟩, ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem orth_Q_le_Nt [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Q ≤ Nt M (LB M Q B) t := by
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hRM hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M (LB M Q B) t)) :=
    (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : Q.subgroupOf (Rt M (LB M Q B) t) ≤ CFSG.pCore 2 ↥(Rt M (LB M Q B) t) :=
    le_sSup ⟨inferInstance, hp⟩
  calc Q = (Q.subgroupOf (Rt M (LB M Q B) t)).map (Rt M (LB M Q B) t).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQR).symm
    _ ≤ Nt M (LB M Q B) t := Subgroup.map_mono hle

end NtBar

section Support

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_support [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {A B' : Type} [Group A] [Group B'] (ψ₀ : A × B' →* Mbar M Q) (hψ₀ : Function.Injective ψ₀)
    (hψ₀r : ψ₀.range = bar M Q (Lgen M (LB M Q B)))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (eA : A ≃* StatedSL 2 F)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (eB : B' ≃* StatedSL 2 K × StatedSL 2 K) :
    ∃ t : G, t ∈ LB M Q B ∧ t ∉ Q ∧ embProdSnd ψ₀ ≤ bar M Q (Rt M (LB M Q B) t) ∧
      (∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∃ k ∈ bar M Q (Nt M (LB M Q B) t),
        ∃ x ∈ embProdSnd ψ₀, r = k * x) ∧
      Nat.card ↥(Rt M (LB M Q B) t) = Nat.card B' * Nat.card ↥(Nt M (LB M Q B) t) := by
  classical
  haveI : IsSimpleGroup ↥(StatedSL 2 K) :=
    isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl hK)
  have hΛab := hc.isElemAbelian_bar_LB
  have hLQ : Q ≤ LB M Q B := le_sup_left
  have hG₁q : CFSG.IsQuasisimple ↥(embProdFst ψ₀) :=
    CFSG.IsQuasisimple.of_mulEquiv ((embProdFstEquiv ψ₀ hψ₀).symm.trans eA)
      (statedSL_quasisimple_of_card 2 F le_rfl hF)
  have hG₁n : bar M Q (LB M Q B) ≤ Subgroup.normalizer (embProdFst ψ₀ : Set (Mbar M Q)) := by
    intro l hl
    have hlr : l ∈ ψ₀.range := by rw [hψ₀r]; exact hc.bar_LB_le_bar_Lgen hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact embProdFst_normal ψ₀ hlr hy
    · intro hy
      have h := embProdFst_normal ψ₀ (ψ₀.range.inv_mem hlr) hy
      have e : l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y := by group
      rwa [e] at h
  have hne0 : bar M Q (LB M Q B) ⊓ embProdFst ψ₀ ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hG₁q hG₁n
  obtain ⟨tb, htb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne0
  have htbΛ : (tb : Mbar M Q) ∈ bar M Q (LB M Q B) := tb.2.1
  have htbX : (tb : Mbar M Q) ∈ embProdFst ψ₀ := tb.2.2
  have htbne : (tb : Mbar M Q) ≠ 1 := fun h => htb1 (Subtype.ext h)
  obtain ⟨t', ht'LB, ht'mk⟩ := Subgroup.mem_map.mp htbΛ
  have htLB : (t' : G) ∈ LB M Q B := ht'LB
  have hmk : (QuotientGroup.mk t' : Mbar M Q) = tb := ht'mk
  have htQ : (t' : G) ∉ Q := by
    intro hq
    apply htbne
    rw [← hmk]
    exact (QuotientGroup.eq_one_iff t').mpr (Subgroup.mem_subgroupOf.mpr hq)
  obtain ⟨u, hut⟩ := htbX
  have hut' : ψ₀ (u, 1) = (tb : Mbar M Q) := hut
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply htbne
    rw [← hut']
    exact map_one ψ₀
  have hu2 : u * u = 1 := by
    have h2 : (tb : Mbar M Q) * tb = 1 := by
      have := hΛab.2 _ htbΛ
      simpa [pow_two] using this
    have h3 : ψ₀ (u * u, 1) = ψ₀ (1, 1) := by
      have e1 : ψ₀ (u * u, 1) = ψ₀ (u, 1) * ψ₀ (u, 1) := by
        rw [← map_mul]
        simp
      rw [e1, hut', h2]
      exact (map_one ψ₀).symm
    exact (Prod.ext_iff.mp (hψ₀ h3)).1
  have hC2 := orth_isPGroup_centralizer_of_equiv eA hu1 hu2
  set C : Subgroup A := Subgroup.centralizer ({u} : Set A) with hCdef
  let ψ₂ : StatedSL 2 K × StatedSL 2 K →* Mbar M Q :=
    (ψ₀.comp (MonoidHom.inr A B')).comp eB.symm.toMonoidHom
  have hψ₂ : ∀ p, ψ₂ p = ψ₀ (1, eB.symm p) := fun p => rfl
  have hψ₂i : Function.Injective ψ₂ := fun a b h => by
    rw [hψ₂, hψ₂] at h
    exact eB.symm.injective (Prod.ext_iff.mp (hψ₀ h)).2
  have hSnd : embProdSnd ψ₀ = ψ₂.range := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨eB b, by simp [hψ₂]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨eB.symm p, by simp [hψ₂]⟩
  have hψ₂r : ψ₂.range ≤ ψ₀.range := by
    rw [← hSnd]
    exact embProdSnd_le_range ψ₀
  have hconj₂ : ∀ s ∈ ψ₀.range, ∃ g : StatedSL 2 K × StatedSL 2 K,
      ∀ p, s * ψ₂ p * s⁻¹ = ψ₂ (g * p * g⁻¹) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    refine ⟨eB b, fun p => ?_⟩
    rw [hψ₂, hψ₂, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hG₂n : ∀ s ∈ ψ₀.range, ∀ y ∈ embProdFst ψ₂, s * y * s⁻¹ ∈ embProdFst ψ₂ := by
    intro s hs y hy
    obtain ⟨g, hg⟩ := hconj₂ s hs
    obtain ⟨γ, rfl⟩ := hy
    refine ⟨g.1 * γ * g.1⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
    rw [hg]
    congr 1
    ext <;> simp
  have hG₃n : ∀ s ∈ ψ₀.range, ∀ y ∈ embProdSnd ψ₂, s * y * s⁻¹ ∈ embProdSnd ψ₂ := by
    intro s hs y hy
    obtain ⟨g, hg⟩ := hconj₂ s hs
    obtain ⟨γ, rfl⟩ := hy
    refine ⟨g.2 * γ * g.2⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
    rw [hg]
    congr 1
    ext <;> simp
  have hbarL : bar M Q (Lgen M (LB M Q B)) = ψ₀.range := hψ₀r.symm
  have hnormY : ∀ Y : Subgroup (Mbar M Q), Y ≤ ψ₀.range →
      (∀ s ∈ ψ₀.range, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) →
      (Y.subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal := by
    intro Y hY hYn
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : Mbar M Q) ∈ ψ₀.range := by rw [hψ₀r]; exact g.2
    simpa using hYn _ hg _ hn
  have hRt₂ : embProdFst ψ₂ ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := by
    have hcent : ∀ x ∈ embProdFst ψ₂, x * QuotientGroup.mk t' = QuotientGroup.mk t' * x := by
      intro x hx
      have hxS : x ∈ embProdSnd ψ₀ := by
        rw [hSnd]; exact embProdFst_le_range ψ₂ hx
      rw [hmk]
      exact (embProdFst_comm ψ₀ ⟨u, hut⟩ hxS).symm
    exact hc.le_bar_Rt_of_normal_centralizes h34 hw hn hno hgen
      (by rw [← hψ₀r]; exact (embProdFst_le_range ψ₂).trans hψ₂r)
      (hnormY _ ((embProdFst_le_range ψ₂).trans hψ₂r) hG₂n)
      (CFSG.IsQuasisimple.of_mulEquiv (embProdFstEquiv ψ₂ hψ₂i).symm
        (statedSL_quasisimple_of_card 2 K le_rfl hK)) htLB hcent
  have hRt₃ : embProdSnd ψ₂ ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := by
    have hcent : ∀ x ∈ embProdSnd ψ₂, x * QuotientGroup.mk t' = QuotientGroup.mk t' * x := by
      intro x hx
      have hxS : x ∈ embProdSnd ψ₀ := by
        rw [hSnd]; exact embProdSnd_le_range ψ₂ hx
      rw [hmk]
      exact (embProdFst_comm ψ₀ ⟨u, hut⟩ hxS).symm
    exact hc.le_bar_Rt_of_normal_centralizes h34 hw hn hno hgen
      (by rw [← hψ₀r]; exact (embProdSnd_le_range ψ₂).trans hψ₂r)
      (hnormY _ ((embProdSnd_le_range ψ₂).trans hψ₂r) hG₃n)
      (CFSG.IsQuasisimple.of_mulEquiv (embProdSndEquiv ψ₂ hψ₂i).symm
        (statedSL_quasisimple_of_card 2 K le_rfl hK)) htLB hcent
  have hXR : embProdSnd ψ₀ ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := by
    rw [hSnd, ← embProdFst_sup_prodSnd ψ₂]
    exact sup_le hRt₂ hRt₃
  have hup : bar M Q (Rt M (LB M Q B) (t' : G)) ≤ (C.prod ⊤).map ψ₀ := by
    refine orth_bar_Rt_le_of_forall hc (X := (C.prod ⊤).map ψ₀) (t := (t' : G)) fun m htm y hy => ?_
    have hmk1 : (QuotientGroup.mk y : Mbar M Q) ∈
        conjSubgroup (QuotientGroup.mk m : Mbar M Q) (bar M Q (LB M Q B)) :=
      (mk_mem_conj_bar_iff_sec4 hLQ m y).mpr hy
    have hmk2 : (QuotientGroup.mk t' : Mbar M Q) ∈
        conjSubgroup (QuotientGroup.mk m : Mbar M Q) (bar M Q (LB M Q B)) :=
      (mk_mem_conj_bar_iff_sec4 hLQ m t').mpr htm
    have hcomm : (QuotientGroup.mk y : Mbar M Q) * QuotientGroup.mk t' =
        QuotientGroup.mk t' * QuotientGroup.mk y := by
      rw [mem_conjSubgroup] at hmk1 hmk2
      have h := hΛab.1.is_comm.comm ⟨_, hmk1⟩ ⟨_, hmk2⟩
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h'
      have e1 : (QuotientGroup.mk y : Mbar M Q) * QuotientGroup.mk t' =
          (QuotientGroup.mk m : Mbar M Q) * (((QuotientGroup.mk m : Mbar M Q))⁻¹ *
            QuotientGroup.mk y * QuotientGroup.mk m * (((QuotientGroup.mk m : Mbar M Q))⁻¹ *
            QuotientGroup.mk t' * QuotientGroup.mk m)) * ((QuotientGroup.mk m : Mbar M Q))⁻¹ := by
        group
      have e2 : (QuotientGroup.mk t' : Mbar M Q) * QuotientGroup.mk y =
          (QuotientGroup.mk m : Mbar M Q) * (((QuotientGroup.mk m : Mbar M Q))⁻¹ *
            QuotientGroup.mk t' * QuotientGroup.mk m * (((QuotientGroup.mk m : Mbar M Q))⁻¹ *
            QuotientGroup.mk y * QuotientGroup.mk m)) * ((QuotientGroup.mk m : Mbar M Q))⁻¹ := by
        group
      rw [e1, e2, h']
    have hyL : (y : G) ∈ Lgen M (LB M Q B) :=
      (le_iSup₂_of_le (m : G) m.2 le_rfl : conjSubgroup (m : G) (LB M Q B) ≤
        Lgen M (LB M Q B)) hy
    have hmkr : (QuotientGroup.mk y : Mbar M Q) ∈ ψ₀.range := by
      rw [hψ₀r]
      exact (mk_mem_bar_iff_sec4 (hLQ.trans (le_Lgen_self M (LB M Q B))) y).mpr hyL
    obtain ⟨⟨a, b⟩, hab⟩ := hmkr
    have haC : a ∈ C := by
      rw [hCdef, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 : ψ₀ (h, 1) * ψ₀ (a, b) = ψ₀ (a, b) * ψ₀ (h, 1) := by
        rw [hab, hut', ← hmk]
        exact hcomm.symm
      rw [← map_mul, ← map_mul] at h1
      have h2 := hψ₀ h1
      simpa using (Prod.ext_iff.mp h2).1
    exact ⟨(a, b), ⟨haC, Subgroup.mem_top _⟩, hab⟩
  have hD2 : IsPGroup 2 ↥(bar M Q (Rt M (LB M Q B) (t' : G)) ⊓ embProdFst ψ₀) := by
    intro d
    obtain ⟨⟨a, b⟩, hpC, hab⟩ := hup d.2.1
    obtain ⟨a', ha'⟩ := d.2.2
    have h1 : ψ₀ (a', 1) = ψ₀ (a, b) := by
      show (ψ₀.comp (MonoidHom.inl A B')) a' = _
      rw [ha', hab]
    obtain ⟨hpa, hpb⟩ := Prod.ext_iff.mp (hψ₀ h1)
    have haC : a ∈ C := hpC.1
    obtain ⟨k, hk⟩ := hC2 ⟨a, haC⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    show (d : Mbar M Q) ^ (2 ^ k) = 1
    rw [← hab]
    have : ((a, b) : A × B') = (a, 1) := by
      refine Prod.ext rfl ?_
      simpa using hpb.symm
    have e : ((a, 1) : A × B') ^ (2 ^ k) = 1 := by simp [Prod.pow_def, h2]
    rw [this, ← map_pow, e, map_one]
  have hDn : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t' : G)),
      ∀ d ∈ bar M Q (Rt M (LB M Q B) (t' : G)) ⊓ embProdFst ψ₀,
        r * d * r⁻¹ ∈ bar M Q (Rt M (LB M Q B) (t' : G)) ⊓ embProdFst ψ₀ := by
    intro r hr d hd
    have hrr : r ∈ ψ₀.range := by
      rw [hψ₀r]
      exact Ctx.bar_Rt_le_bar_Lgen (t' : G) hr
    exact ⟨(bar M Q (Rt M (LB M Q B) (t' : G))).mul_mem
      ((bar M Q (Rt M (LB M Q B) (t' : G))).mul_mem hr hd.1)
      ((bar M Q (Rt M (LB M Q B) (t' : G))).inv_mem hr), embProdFst_normal ψ₀ hrr hd.2⟩
  have hDN := orth_bar_pgroup_le_bar_Nt hc htLB inf_le_left hD2 hDn
  have hRX : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t' : G)), ∃ k ∈ bar M Q (Nt M (LB M Q B) (t' : G)),
      ∃ x ∈ embProdSnd ψ₀, r = k * x := by
    intro r hr
    obtain ⟨⟨a, b⟩, -, hab⟩ := hup hr
    have hx : ψ₀ (1, b) ∈ bar M Q (Rt M (LB M Q B) (t' : G)) := hXR ⟨b, rfl⟩
    have hrab : r = ψ₀ (a, 1) * ψ₀ (1, b) := by
      rw [← map_mul, ← hab]
      simp
    have hk : ψ₀ (a, 1) ∈ bar M Q (Rt M (LB M Q B) (t' : G)) ⊓ embProdFst ψ₀ := by
      refine ⟨?_, ⟨a, rfl⟩⟩
      have : ψ₀ (a, 1) = r * (ψ₀ (1, b))⁻¹ := by rw [hrab]; group
      rw [this]
      exact (bar M Q (Rt M (LB M Q B) (t' : G))).mul_mem hr
        ((bar M Q (Rt M (LB M Q B) (t' : G))).inv_mem hx)
    exact ⟨ψ₀ (a, 1), hDN hk, ψ₀ (1, b), ⟨b, rfl⟩, hrab⟩
  have hXN : bar M Q (Nt M (LB M Q B) (t' : G)) ⊓ embProdSnd ψ₀ = ⊥ := by
    let W : Subgroup B' := (bar M Q (Nt M (LB M Q B) (t' : G))).comap (ψ₀.comp (MonoidHom.inr A B'))
    haveI hWn : W.Normal := ⟨fun w hw b' => by
      show ψ₀ (1, b' * w * b'⁻¹) ∈ bar M Q (Nt M (LB M Q B) (t' : G))
      have e : ψ₀ (1, b' * w * b'⁻¹) = ψ₀ (1, b') * ψ₀ (1, w) * (ψ₀ (1, b'))⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        simp
      rw [e]
      exact orth_bar_Nt_conj_mem hc (t' : G) (hXR ⟨b', rfl⟩) hw⟩
    have hW2 : IsPGroup 2 ↥W := by
      intro w
      obtain ⟨k, hk⟩ := orth_isPGroup_bar_Nt hc (t' : G) ⟨ψ₀ (1, (w : B')), w.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : ψ₀ (1, (w : B')) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have h2 : ψ₀ (1, (w : B') ^ (2 ^ k)) = ψ₀ 1 := by
        rw [map_one, ← h1, ← map_pow]
        simp [Prod.pow_def]
      have h3 := (Prod.ext_iff.mp (hψ₀ h2)).2
      simpa using h3
    have hWb : W = ⊥ := orth_normal_pgroup_eq_bot_of_equiv hK eB hW2
    rw [eq_bot_iff]
    rintro x ⟨hxN, b, rfl⟩
    have hbW : b ∈ W := hxN
    rw [hWb, Subgroup.mem_bot] at hbW
    rw [Subgroup.mem_bot]
    show ψ₀ (1, b) = 1
    rw [hbW]
    exact map_one ψ₀
  have hQN : Q ≤ Nt M (LB M Q B) (t' : G) := orth_Q_le_Nt hc htLB
  have hNM : Nt M (LB M Q B) (t' : G) ≤ M := (orth_Nt_le_Rt _ _ _).trans (hc.Rt_le_M _)
  have hbar : Nat.card ↥(bar M Q (Rt M (LB M Q B) (t' : G))) =
      Nat.card ↥(bar M Q (Nt M (LB M Q B) (t' : G))) * Nat.card B' := by
    have h := orth_card_mul_of_inf_eq_bot (R := bar M Q (Rt M (LB M Q B) (t' : G)))
      (N := bar M Q (Nt M (LB M Q B) (t' : G))) (X := embProdSnd ψ₀)
      (Subgroup.map_mono (fun x hx => orth_Nt_le_Rt _ _ _ hx)) hXR hXN hRX
    rw [h, ← Nat.card_congr (embProdSndEquiv ψ₀ hψ₀).toEquiv]
  have hR := bar_card_mul_card_of_le (M := M) (Q := Q) (hc.Q_le_Rt htLB) (hc.Rt_le_M (t' : G))
  have hN := bar_card_mul_card_of_le (M := M) (Q := Q) hQN hNM
  refine ⟨(t' : G), htLB, htQ, hXR, hRX, ?_⟩
  rw [← hR, ← hN, hbar]
  ring

theorem orth_exists_fixer [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {A B' : Type} [Group A] [Group B'] (ψ₀ : A × B' →* Mbar M Q) (hψ₀ : Function.Injective ψ₀)
    (hψ₀r : ψ₀.range = bar M Q (Lgen M (LB M Q B)))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (eA : A ≃* StatedSL 2 F)
    (x : ↥M) :
    ∃ s : ↥M, (s : G) ∈ LB M Q B ∧ (QuotientGroup.mk s : Mbar M Q) ≠ 1 ∧
      (QuotientGroup.mk (x * s * x⁻¹) : Mbar M Q) ∈ embProdFst ψ₀ := by
  classical
  have hG₁q : CFSG.IsQuasisimple ↥(embProdFst ψ₀) :=
    CFSG.IsQuasisimple.of_mulEquiv ((embProdFstEquiv ψ₀ hψ₀).symm.trans eA)
      (statedSL_quasisimple_of_card 2 F le_rfl hF)
  set g : Mbar M Q := (QuotientGroup.mk x : Mbar M Q)⁻¹ with hg
  have hYq : CFSG.IsQuasisimple ↥(conjSubgroup g (embProdFst ψ₀)) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (embProdFst ψ₀) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm hG₁q
  have hgr : ∀ l ∈ ψ₀.range, g⁻¹ * l * g ∈ ψ₀.range := by
    intro l hl
    rw [hψ₀r] at hl ⊢
    have := (hc.normal_bar_Lgen).conj_mem l hl (QuotientGroup.mk x)
    simpa [hg] using this
  have hconjY : ∀ l ∈ ψ₀.range, ∀ y ∈ conjSubgroup g (embProdFst ψ₀),
      l * y * l⁻¹ ∈ conjSubgroup g (embProdFst ψ₀) := by
    intro l hl y hy
    rw [mem_conjSubgroup] at hy ⊢
    have h := embProdFst_normal ψ₀ (hgr l hl) hy
    have e : g⁻¹ * (l * y * l⁻¹) * g =
        g⁻¹ * l * g * (g⁻¹ * y * g) * (g⁻¹ * l * g)⁻¹ := by group
    rw [e]
    exact h
  have hYn : bar M Q (LB M Q B) ≤ Subgroup.normalizer (conjSubgroup g (embProdFst ψ₀) :
      Set (Mbar M Q)) := by
    intro l hl
    have hlr : l ∈ ψ₀.range := by rw [hψ₀r]; exact hc.bar_LB_le_bar_Lgen hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconjY l hlr y hy
    · intro hy
      have h := hconjY l⁻¹ (ψ₀.range.inv_mem hlr) _ hy
      have e : l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y := by group
      rwa [e] at h
  have hne0 := hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hYq hYn
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne0
  obtain ⟨s, hsLB, hsmk⟩ := Subgroup.mem_map.mp z.2.1
  have hzY : (z : Mbar M Q) ∈ conjSubgroup g (embProdFst ψ₀) := z.2.2
  rw [mem_conjSubgroup] at hzY
  refine ⟨s, hsLB, ?_, ?_⟩
  · intro h
    apply hz1
    apply Subtype.ext
    show (z : Mbar M Q) = 1
    rw [← hsmk]
    exact h
  · have e : (QuotientGroup.mk (x * s * x⁻¹) : Mbar M Q) = g⁻¹ * (z : Mbar M Q) * g := by
      rw [← hsmk, hg]
      simp [QuotientGroup.mk_mul]
    rw [e]
    exact hzY

end Support

end CFSG.RankThree.GF2n.Smith81
