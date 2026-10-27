module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.QuasithinUnique.Setup.X6 (ResidualOvergroupsAt)
open scoped Pointwise

namespace Sec1211He

theorem sl2_sq_eq_one_of_pow_four {F : Type*} [Field F] [CharP F 2]
    (x : SpecialLinearGroup (Fin 2) F) (h : x ^ 4 = 1) : x ^ 2 = 1 := by
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact x.2
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  generalize hM : (x : Matrix (Fin 2) (Fin 2) F) = M at hdet
  have hsq : M ^ 2 = (M 0 0 + M 1 1) • M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hdet - htwo
    · ring
    · ring
    · linear_combination -hdet - htwo
  have h4 : M ^ 4 = 1 := by
    rw [← hM]
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  have hM4 : M ^ 4 = ((M 0 0 + M 1 1) • M + 1) * ((M 0 0 + M 1 1) • M + 1) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hsq]
  have e := hM4.symm.trans h4
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have ht4 : (M 0 0 + M 1 1) ^ 4 = 0 := by
    linear_combination e00 + e11 + ((M 0 0 + M 1 1) ^ 2 * M 0 0 * M 1 1 -
      (M 0 0 + M 1 1) * M 0 0 - (M 0 0 + M 1 1) * M 1 1 -
      (M 0 0 + M 1 1) ^ 2 * M 0 1 * M 1 0) * htwo
  have ht : M 0 0 + M 1 1 = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp ht4
  ext i j
  have := congrFun (congrFun hsq i) j
  rw [ht, zero_smul, zero_add] at this
  simpa [← hM] using this

theorem sq_eq_one_of_pow_two_pow {Q : Type*} [Group Q] (h4 : ∀ x : Q, x ^ 4 = 1 → x ^ 2 = 1) :
    ∀ (a : ℕ) (x : Q), x ^ 2 ^ a = 1 → x ^ 2 = 1
  | 0, x, hx => by rw [pow_zero, pow_one] at hx; rw [hx, one_pow]
  | a + 1, x, hx => by
    have h1 : (x ^ 2) ^ 2 ^ a = 1 := by rw [← pow_mul, ← pow_succ']; exact hx
    have h2 := sq_eq_one_of_pow_two_pow h4 a (x ^ 2) h1
    exact h4 x (by rw [← h2, ← pow_mul])

theorem exists_sl_three {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ t : SpecialLinearGroup (Fin m) (ZMod 2), t ^ 3 = 1 ∧ t ≠ 1 := by
  have h : ∃ t : SpecialLinearGroup (Fin m) (ZMod 2), t ^ 3 = 1 ∧ t ^ 1 ≠ 1 := by
    rcases hm with rfl | rfl
    · exact ⟨⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩, by decide, by decide⟩
    · exact ⟨⟨!![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1], by decide⟩, by decide,
        by decide⟩
  obtain ⟨t, ht3, ht1⟩ := h
  exact ⟨t, ht3, fun h => ht1 (by rw [h, one_pow])⟩

theorem exists_sl_four {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ J : SpecialLinearGroup (Fin m) (ZMod 2), J ^ 4 = 1 ∧ J ^ 2 ≠ 1 := by
  rcases hm with rfl | rfl
  · exact ⟨⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩, by decide, by decide⟩
  · exact ⟨⟨!![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩, by decide,
      by decide⟩

theorem sl_isSimple {m : ℕ} (hm : m = 3 ∨ m = 4) :
    IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) :=
  Vol2Native.A312L.sl_isSimple_of_card_two (by simp) (by omega)

theorem not_isSolvable_sl {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ¬ Group.IsSolvable (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  intro hsolv
  have := sl_isSimple hm
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
  obtain ⟨a, b, hab⟩ := Vol2Native.A312L.sl_nonabelian_of_card_two (K := ZMod 2) (by simp)
    (m := m) (by omega)
  exact hab (hcomm a b)

theorem false_of_target {Z Q : Type*} [Group Z] [Finite Z] [Group Q] {m : ℕ}
    (hm : m = 3 ∨ m = 4) (ρ : Z →* SpecialLinearGroup (Fin m) (ZMod 2))
    (hρ : Function.Surjective ρ) (g : Z →* Q) (hg : IsPGroup 2 g.ker)
    (hQ : (∀ x : Q, x ^ 4 = 1 → x ^ 2 = 1) ∨ ¬ 3 ∣ Nat.card Q) : False := by
  obtain ⟨t, ht3, ht1⟩ := exists_sl_three hm
  rcases hQ with h4 | h3
  · have hs := sl_isSimple hm
    have hN : g.ker.map ρ = ⊥ := by
      have hn : (g.ker.map ρ).Normal := (MonoidHom.normal_ker g).map ρ hρ
      rcases hn.eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have hp : IsPGroup 2 ↥(g.ker.map ρ) := hg.map ρ
        rw [h] at hp
        obtain ⟨k, hk⟩ := hp ⟨t, Subgroup.mem_top t⟩
        have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have h1 : t ^ (Nat.gcd 3 (2 ^ k)) = 1 := pow_gcd_eq_one.mpr ⟨ht3, hk'⟩
        rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h1
        exact ht1 (by simpa using h1)
    have hker : g.ker ≤ ρ.ker := by
      intro z hz
      have : ρ z ∈ g.ker.map ρ := ⟨z, hz, rfl⟩
      rw [hN] at this
      exact this
    obtain ⟨J, hJ4, hJ2⟩ := exists_sl_four hm
    obtain ⟨z, rfl⟩ := hρ J
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    have hw : (z ^ b) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have hgw : (g (z ^ b)) ^ 2 = 1 :=
      sq_eq_one_of_pow_two_pow h4 a _ (by rw [← map_pow, hw, map_one])
    have hw2 : (z ^ b) ^ 2 ∈ ρ.ker := hker (by rw [MonoidHom.mem_ker, map_pow]; exact hgw)
    rw [MonoidHom.mem_ker, map_pow, map_pow] at hw2
    obtain ⟨c, rfl⟩ := hb
    apply hJ2
    rw [← hw2, ← pow_mul, show (2 * c + 1) * 2 = 4 * c + 2 by ring, pow_add, pow_mul, hJ4,
      one_pow, one_mul]
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨z, rfl⟩ := hρ t
    have ht : orderOf (ρ z) = 3 := orderOf_eq_prime ht3 ht1
    have h3z : 3 ∣ orderOf z := ht ▸ orderOf_map_dvd ρ z
    obtain ⟨r, hr⟩ := h3z
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact (orderOf_pos z).ne' hr
    have hw : orderOf (z ^ r) = 3 := by
      rw [orderOf_pow_of_dvd hr0 ⟨3, by rw [hr, mul_comm]⟩, hr, Nat.mul_div_cancel _ (by omega)]
    have hgw : g (z ^ r) = 1 := by
      have h1 : orderOf (g (z ^ r)) ∣ 3 := hw ▸ orderOf_map_dvd g (z ^ r)
      have h2 : orderOf (g (z ^ r)) ∣ Nat.card Q := orderOf_dvd_natCard _
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ h2) h3
    obtain ⟨k, hk⟩ := hg ⟨z ^ r, hgw⟩
    have hk' : (z ^ r) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := hw ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)) (by norm_num)

variable {X : Type} [Group X]

@[expose] def NoLinOver (U : Subgroup X) : Prop :=
  ∀ M : Subgroup X, U ≤ M → M ≠ ⊤ → ∀ Y : Subgroup X, Y ≤ M → ∀ m : ℕ, (m = 3 ∨ m = 4) →
    ∀ ρ : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2), Function.Surjective ρ → False

theorem NoLinOver.map {X' : Type} [Group X'] {U : Subgroup X} (h : NoLinOver U) (e : X ≃* X') :
    NoLinOver (U.map e.toMonoidHom) := by
  intro M hUM hM Y hYM m hm ρ hρ
  refine h (M.map e.symm.toMonoidHom) ?_ ?_ (Y.map e.symm.toMonoidHom) (Subgroup.map_mono hYM) m
    hm (ρ.comp (e.symm.subgroupMap Y).symm.toMonoidHom)
    (hρ.comp (e.symm.subgroupMap Y).symm.surjective)
  · intro u hu
    exact ⟨e u, hUM ⟨u, hu, rfl⟩, by simp⟩
  · intro htop
    apply hM
    rw [eq_top_iff]
    intro x _
    have : e.symm x ∈ M.map e.symm.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := by
      have := congrArg e hyx
      simpa using this
    rwa [← this]

theorem noLinOver_of_solvable {U : Subgroup X}
    (h : ∀ M : Subgroup X, U ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) : NoLinOver U := by
  intro M hUM hM Y hYM m hm ρ hρ
  have := h M hUM hM
  have : Group.IsSolvable ↥Y := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hYM) (Subgroup.inclusion_injective hYM)
  exact not_isSolvable_sl hm (Group.isSolvable_of_surjective (f := ρ) hρ)

@[expose] def LeviTarget (P : Subgroup X) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (g : ↥(perfectCore P) →* Q), IsPGroup 2 g.ker ∧
    ((∀ x : Q, x ^ 4 = 1 → x ^ 2 = 1) ∨ ¬ 3 ∣ Nat.card Q)

theorem leviTarget_of_bot {P : Subgroup X} (h : perfectCore P = ⊥) : LeviTarget P := by
  refine ⟨Unit, inferInstance, 1, fun x => ⟨0, Subtype.ext ?_⟩, Or.inl fun _ _ => rfl⟩
  have hx : ((x : ↥(perfectCore P)) : X) ∈ (⊥ : Subgroup X) := h ▸ (x : ↥(perfectCore P)).2
  rw [Subgroup.mem_bot] at hx
  rw [pow_zero, pow_one]
  exact Subtype.ext hx

theorem leviTarget_of_sl2 {P : Subgroup X} {K : Type} [Field K] [CharP K 2]
    (g : ↥(perfectCore P) →* SpecialLinearGroup (Fin 2) K) (hg : IsPGroup 2 g.ker) :
    LeviTarget P :=
  ⟨SpecialLinearGroup (Fin 2) K, inferInstance, g, hg, Or.inl sl2_sq_eq_one_of_pow_four⟩

theorem noLinOver_of_residual [Finite X] {U : Subgroup X} {P : Fin 2 → Subgroup X}
    (hP : ResidualOvergroupsAt X U P) (hL : ∀ j, LeviTarget (P j)) : NoLinOver U := by
  intro M hUM hM Y hYM m hm ρ hρ
  by_cases hMs : Group.IsSolvable ↥M
  · have : Group.IsSolvable ↥Y := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hYM) (Subgroup.inclusion_injective hYM)
    exact not_isSolvable_sl hm (Group.isSolvable_of_surjective (f := ρ) hρ)
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 M hUM hM hMs
  have hMP : perfectCore M = perfectCore (P j) := by
    rw [← Vol2Native.A312L.dInf_eq_perfectCore, ← Vol2Native.A312L.dInf_eq_perfectCore, hd]
  obtain ⟨Q, _, g, hg, hQ⟩ := hL j
  set Z : Subgroup ↥Y := perfectCore (⊤ : Subgroup ↥Y) with hZ
  have hZY : Z.map Y.subtype = perfectCore Y := by
    rw [hZ, map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hρZ : Z.map ρ = ⊤ := by
    have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
      (K := ZMod 2) (n := m) (by omega)
    rw [hZ, map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hρ]
    exact perfectCore_eq_self_of_perfect hperf.commutator_eq_top
  have hZP : ∀ z : ↥Z, ((z : ↥Y) : X) ∈ perfectCore (P j) := fun z => by
    rw [← hMP]
    refine perfectCore_mono hYM ?_
    rw [← hZY]
    exact ⟨z, z.2, rfl⟩
  let ι : ↥Z →* ↥(perfectCore (P j)) :=
    (Y.subtype.comp Z.subtype).codRestrict (perfectCore (P j)) hZP
  have hι : Function.Injective ι := fun a b hab => by
    have := congrArg (fun x : ↥(perfectCore (P j)) => (x : X)) hab
    exact Subtype.ext (Subtype.ext this)
  refine false_of_target hm (ρ.comp Z.subtype) (fun s => ?_) (g.comp ι) ?_ hQ
  · have hs : s ∈ Z.map ρ := hρZ ▸ Subgroup.mem_top s
    obtain ⟨z, hz, rfl⟩ := hs
    exact ⟨⟨z, hz⟩, rfl⟩
  · rw [← MonoidHom.comap_ker]
    exact hg.comap_of_injective ι hι

theorem le_normalizer_sup' [Finite X] {A B C : Subgroup X}
    (hA : C ≤ Subgroup.normalizer (A : Set X)) (hB : C ≤ Subgroup.normalizer (B : Set X)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  intro y hy
  have hmap : ∀ H : Subgroup X, y ∈ Subgroup.normalizer (H : Set X) →
      H.map (MulAut.conj y).toMonoidHom ≤ H := by
    rintro H hH _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hH a).mp ha
  refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
  have h1 : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hmap A (hA hy)) (hmap B (hB hy))
  exact h1 ⟨x, hx, rfl⟩

theorem exists_conj_eq_of_sylow [Finite X] {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (S : Sylow 2 X) : ∃ g : X, U.map (MulAut.conj g).toMonoidHom = (S : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUi : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hU.2.1.toSylow hUi) S
  refine ⟨g, ?_⟩
  have h1 : ((g • hU.2.1.toSylow hUi : Sylow 2 X) : Subgroup X) =
      MulAut.conj g • ((hU.2.1.toSylow hUi : Sylow 2 X) : Subgroup X) := Sylow.coe_subgroup_smul
  rw [hg] at h1
  rw [h1]
  rfl

theorem not_heInspCfg_of_noLinOver [Finite X] (hBT : CFSG.LieType.BorelTits.HoldsTits X 2)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) (hN : NoLinOver U) {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  rintro ⟨Y, W₁, W₂, C₁, C₂, -, -, -, hE, -, -, -, -, -⟩
  have hW1 : W₁ ≠ ⊥ := by
    intro h
    have h1 := NatCoord.card_eq C₁
    rw [h, Subgroup.card_bot] at h1
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hV : W₁ ⊔ W₂ ≠ ⊥ := fun h => hW1 (le_bot_iff.mp (h ▸ le_sup_left))
  have hV2 : IsPGroup 2 ↥(W₁ ⊔ W₂) := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hYV : Y ≤ Subgroup.normalizer ((W₁ ⊔ W₂ : Subgroup X) : Set X) :=
    le_normalizer_sup' C₁.le C₂.le
  obtain ⟨S, P, hP, hNP, -, -, hSP⟩ := hBT _ hV hV2
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylow hU S
  have hN' : NoLinOver (S : Subgroup X) := hg ▸ hN.map (MulAut.conj g)
  exact hN' P hSP hP Y (hYV.trans hNP) m hm C₁.ρ C₁.ρ_surj

theorem isSylowTwoOf_top_map {X' : Type} [Group X'] (e : X ≃* X') {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  show ¬ 2 ∣ (U.map e.toMonoidHom).relIndex ⊤
  rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq _ e.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le)]
  have := hU.2.2
  rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this

theorem not_heInspCfg_of_model [Finite X] {X' : Type} [Group X'] (e : X ≃* X')
    (hBT : CFSG.LieType.BorelTits.HoldsTits X 2) {U : Subgroup X'} (hU : IsSylowTwoOf U ⊤)
    (hN : NoLinOver U) {m : ℕ} (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m :=
  not_heInspCfg_of_noLinOver hBT (isSylowTwoOf_top_map e.symm hU) (hN.map e.symm) hm

end Sec1211He

end CFSG.Quasithin.H13
