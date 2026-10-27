module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem sz5e1_kfo_eight {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : IsSz X n) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_twistedB2 h
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨-, -, hsq, hZ, -⟩ := hB Q
  set Z := Subgroup.center (Q : Subgroup X)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := Z) 2 (n := 3)
    (by rw [hZ]; exact pow_dvd_pow 2 hn)
  set f : Z →* X := (Q : Subgroup X).subtype.comp Z.subtype
  have hf : Function.Injective f :=
    (Q : Subgroup X).subtype_injective.comp Z.subtype_injective
  refine ⟨E.map f, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp y.2 (x : Q))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hsq x x.2)
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hf, hE]
    norm_num

private theorem sz5e1_kfo_pair {R : Type} [Group R] [Finite R] (h : 2 ≤ twoRank R) :
    ∃ a b : R, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, ⟨hcomm, hsq⟩, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (G := R) (p := 2) (by norm_num) ⊤
  have h' : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup R) := h
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup R) := Nat.pow_le_pow_right (by norm_num) h'
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : E = ⊥ := eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hno a ha)
    rw [this, Subgroup.card_bot] at h4
    omega
  have hao : orderOf a = 2 := orderOf_eq_prime (hsq a haE) ha1
  obtain ⟨b, hbE, hbn⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers a := fun b hb => hno b hb
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hao] at this
    omega
  have hb1 : b ≠ 1 := fun h1 => hbn (h1 ▸ Subgroup.one_mem _)
  refine ⟨a, b, hao, orderOf_eq_prime (hsq b hbE) hb1,
    fun hab => hbn (hab ▸ Subgroup.mem_zpowers a), ?_⟩
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)

private theorem sz5e1_kfo_two_gen_quat (m : ℕ) [NeZero m] :
    ∃ x y : QuaternionGroup m, ∀ g : QuaternionGroup m,
      g ∈ Subgroup.closure ({x, y} : Set (QuaternionGroup m)) := by
  refine ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, fun g => ?_⟩
  have ha : ∀ i : ZMod (2 * m), QuaternionGroup.a i ∈
      Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
        Set (QuaternionGroup m)) := by
    intro i
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective i
    rw [← QuaternionGroup.a_one_pow]
    exact pow_mem (Subgroup.subset_closure (by simp)) k
  cases g with
  | a i => exact ha i
  | xa i =>
    have : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [this]
    exact mul_mem (Subgroup.subset_closure (by simp)) (ha i)

private theorem sz5e1_kfo_two_gen_cyclic {R : Type} [Group R] [IsCyclic R] :
    ∃ x y : R, ∀ r : R, r ∈ Subgroup.closure ({x, y} : Set R) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  refine ⟨g, g, fun r => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg r)
  exact zpow_mem (Subgroup.subset_closure (by simp)) k

private theorem sz5e1_kfo_two_gen_map {R E : Type} [Group R] [Group E] (f : R →* E)
    (hf : Function.Surjective f)
    (h : ∃ x y : R, ∀ r : R, r ∈ Subgroup.closure ({x, y} : Set R)) :
    ∃ u v : E, ∀ e : E, e ∈ Subgroup.closure ({u, v} : Set E) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨f x, f y, fun e => ?_⟩
  obtain ⟨r, rfl⟩ := hf e
  have := Subgroup.mem_map_of_mem f (hxy r)
  rwa [MonoidHom.map_closure, Set.image_pair] at this

private theorem sz5e1_kfo_not_two_gen {E : Type} [Group E] [Finite E]
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a ^ 2 = 1) (hcard : Nat.card E = 8) :
    ¬ ∃ u v : E, ∀ e : E, e ∈ Subgroup.closure ({u, v} : Set E) := by
  rintro ⟨u, v, huv⟩
  have hu : u ^ 2 = 1 := hsq u
  have hv : v ^ 2 = 1 := hsq v
  have e1 : u * u = 1 := by rw [← pow_two]; exact hu
  have e2 : v * v = 1 := by rw [← pow_two]; exact hv
  have e3 : v * u = u * v := hcomm v u
  have e4 : u * (u * v) = v := by rw [← mul_assoc, e1, one_mul]
  have e6 : v * (u * v) = u := by rw [← mul_assoc, e3, mul_assoc, e2, mul_one]
  have e7 : u * v * u = v := by rw [mul_assoc, e3, e4]
  have e8 : u * v * v = u := by rw [mul_assoc, e2, mul_one]
  have e9 : u * v * (u * v) = 1 := by rw [mul_assoc, e6, e1]
  have hsub' : ∀ g ∈ Subgroup.closure ({u, v} : Set E), g = 1 ∨ g = u ∨ g = v ∨ g = u * v := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = u ∨ g = v ∨ g = u * v)
      ?_ ?_ ?_ ?_ hg
    · rintro x (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [e1, e2, e3, e4, e6, e7, e8, e9]
    · intro x _ hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inl (by rw [inv_eq_of_mul_eq_one_right e1]))
      · exact Or.inr (Or.inr (Or.inl (by rw [inv_eq_of_mul_eq_one_right e2])))
      · exact Or.inr (Or.inr (Or.inr (by rw [inv_eq_of_mul_eq_one_right e9])))
  have hsub : (Set.univ : Set E) ⊆ ({1, u, v, u * v} : Set E) := fun e _ => hsub' e (huv e)
  have h4 : Nat.card E ≤ 4 := by
    rw [← Set.ncard_univ]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ?_))
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  omega

private theorem sz5e1_kfo_klein {K : Type} [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) :
    ∃ a b : K, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEc, hEs, hE8⟩ := sz5e1_kfo_eight (X := K ⧸ R) (n := 3) (le_refl 3) hK.2.2
  set π : K →* K ⧸ R := QuotientGroup.mk' R with hπ
  set R' : Subgroup K := E.comap π with hR'
  have hRp : IsPGroup 2 R' := by
    intro g
    have hg2 : ((g : K) ^ 2) ∈ R := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hEs _ g.2
    obtain ⟨k, hk⟩ := hK.2.1 ⟨(g : K) ^ 2, hg2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_succ', pow_mul]
    simpa using this
  by_contra hno
  push Not at hno
  have hrank : twoRank R' ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, b, ha, hb, hab, hc⟩ := sz5e1_kfo_pair (R := R') h
    exact hno (a : K) (b : K) (by rw [Subgroup.orderOf_coe]; exact ha)
      (by rw [Subgroup.orderOf_coe]; exact hb) (fun h => hab (Subtype.ext h))
      (hc.map R'.subtype)
  let f : ↥R' →* ↥E := (π.comp R'.subtype).codRestrict E (fun r => r.2)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R (e : K ⧸ R)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ E
    rw [hπ, hx]
    exact e.2
  have hgen : ∃ x y : ↥R', ∀ r : ↥R', r ∈ Subgroup.closure ({x, y} : Set ↥R') := by
    rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion ↥R' hRp
      hrank with hcyc | ⟨e, -, ⟨iso⟩⟩
    · exact sz5e1_kfo_two_gen_cyclic
    · exact sz5e1_kfo_two_gen_map iso.symm.toMonoidHom iso.symm.surjective (sz5e1_kfo_two_gen_quat _)
  exact sz5e1_kfo_not_two_gen (fun a b => hEc.is_comm.comm a b)
    (fun a => Subtype.ext (hEs a a.2)) hE8 (sz5e1_kfo_two_gen_map f hf hgen)

theorem sz5e1_klein_four {K : Type} [Group K] [Finite K] (R : Subgroup K) [R.Normal]
    (hK : SzSetup K R) :
    ∃ a b : K, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a := by
  obtain ⟨a, b, hao, hbo, hab, hc⟩ := sz5e1_kfo_klein R hK
  refine ⟨a, b, ?_, ?_, hab, ?_, ?_, hc.eq⟩
  · rintro rfl
    rw [orderOf_one] at hao
    omega
  · rintro rfl
    rw [orderOf_one] at hbo
    omega
  · rw [← hao]
    exact pow_orderOf_eq_one a
  · rw [← hbo]
    exact pow_orderOf_eq_one b

open Module in
private theorem sz5e1_ksu_three_fix {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (a b : V →ₗ[F] V) (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    finrank F V ≤ finrank F (LinearMap.ker (a - 1)) + finrank F (LinearMap.ker (b - 1)) +
      finrank F (LinearMap.ker (a * b - 1)) := by
  have hax : ∀ v, a (a v) = v := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) ha
  have hbx : ∀ v, b (b v) = v := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) hb
  have habx : ∀ v, a (b v) = b (a v) := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) hab
  have hc : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have hcov : (⊤ : Submodule F V) ≤
      LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔ LinearMap.ker (a * b - 1) := by
    intro w _
    set c : F := (2 : F)⁻¹ with hcdef
    set u : V := c • (w - a w) with hu
    have hau : a u = -u := by
      rw [hu, map_smul, map_sub, hax, ← smul_neg]
      congr 1
      abel
    have hbu : a (b u) = -b u := by
      rw [habx, hau, map_neg]
    have h1 : c • (w + a w) ∈ LinearMap.ker (a - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_smul, map_add, hax]
      simp [add_comm]
    have h2' : c • (u + b u) ∈ LinearMap.ker (b - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_smul, map_add, hbx]
      simp [add_comm]
    have h3 : c • (u - b u) ∈ LinearMap.ker (a * b - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, map_smul, map_sub, hbx,
        map_smul, map_sub, hau, hbu, Module.End.one_apply]
      simp only [smul_sub, smul_neg]
      abel
    have e1 : c • (u + b u) + c • (u - b u) = u := by
      rw [← smul_add]
      have : u + b u + (u - b u) = (2 : F) • u := by rw [two_smul]; abel
      rw [this, smul_smul, hc, one_smul]
    have e2 : c • (w + a w) + u = w := by
      rw [hu, ← smul_add]
      have : w + a w + (w - a w) = (2 : F) • w := by rw [two_smul]; abel
      rw [this, smul_smul, hc, one_smul]
    have hsum : w = (c • (w + a w) + c • (u + b u)) + c • (u - b u) := by
      rw [add_assoc, e1, e2]
    rw [hsum]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup h1 h2') h3
  calc finrank F V = finrank F (⊤ : Submodule F V) := (finrank_top F V).symm
    _ ≤ finrank F (LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔
          LinearMap.ker (a * b - 1) : Submodule F V) := Submodule.finrank_mono hcov
    _ ≤ finrank F (LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) : Submodule F V) +
          finrank F (LinearMap.ker (a * b - 1)) := Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ (finrank F (LinearMap.ker (a - 1)) + finrank F (LinearMap.ker (b - 1))) +
          finrank F (LinearMap.ker (a * b - 1)) := by
        gcongr
        exact Submodule.finrank_add_le_finrank_add_finrank _ _

theorem sz5e1_klein_sum {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (a b : V ≃ₗ[F] V) (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    Module.finrank F V ≤ Module.finrank F (fixSpaceOf a) +
      Module.finrank F (fixSpaceOf b) + Module.finrank F (fixSpaceOf (a * b)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have ha' : a.toLinearMap * a.toLinearMap = 1 := by
    have h := congrArg (fun e : V ≃ₗ[F] V => (e : V →ₗ[F] V)) ha
    simpa [pow_two, LinearEquiv.coe_toLinearMap_mul, Module.End.one_eq_id] using h
  have hb' : b.toLinearMap * b.toLinearMap = 1 := by
    have h := congrArg (fun e : V ≃ₗ[F] V => (e : V →ₗ[F] V)) hb
    simpa [pow_two, LinearEquiv.coe_toLinearMap_mul, Module.End.one_eq_id] using h
  have hab' : a.toLinearMap * b.toLinearMap = b.toLinearMap * a.toLinearMap := by
    have h := congrArg (fun e : V ≃ₗ[F] V => (e : V →ₗ[F] V)) hab
    simpa [LinearEquiv.coe_toLinearMap_mul] using h
  have hmain := sz5e1_ksu_three_fix (F := F) (V := V) h2 a.toLinearMap b.toLinearMap ha' hb' hab'
  have e1 : fixSpaceOf a = LinearMap.ker (a.toLinearMap - 1) := by
    simp [fixSpaceOf, Module.End.one_eq_id]
  have e2 : fixSpaceOf b = LinearMap.ker (b.toLinearMap - 1) := by
    simp [fixSpaceOf, Module.End.one_eq_id]
  have e3 : fixSpaceOf (a * b) = LinearMap.ker (a.toLinearMap * b.toLinearMap - 1) := by
    simp [fixSpaceOf, LinearEquiv.coe_toLinearMap_mul, Module.End.one_eq_id]
  rw [e1, e2, e3]
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
