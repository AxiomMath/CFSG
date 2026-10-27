module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.Quasithin.SteinbergBQUniqueLocalWitnessCentralizers
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Swap20 (A V I₀ I₁ : Subgroup G) (a : G) : Prop where
  le₀ : I₀ ≤ V
  le₁ : I₁ ≤ V
  ne_bot : I₀ ≠ ⊥
  inf : I₀ ⊓ I₁ = ⊥
  sup : I₀ ⊔ I₁ = V
  mem : a ∈ A
  swap : conjSubgroup I₀ a = I₁
  acts : ∀ x ∈ A, (conjSubgroup I₀ x = I₀ ∧ conjSubgroup I₁ x = I₁) ∨
    (conjSubgroup I₀ x = I₁ ∧ conjSubgroup I₁ x = I₀)

private theorem s16c167_twenty_ne {A V I₀ I₁ : Subgroup G} {a : G} (hS : Swap20 A V I₀ I₁ a) :
    I₀ ≠ I₁ := by
  intro h
  have h1 : I₀ ⊓ I₁ = I₀ := by rw [h, inf_idem]
  rw [hS.inf] at h1
  exact hS.ne_bot h1.symm

private theorem s16c167_twenty_conj_I₁ {A V I₀ I₁ : Subgroup G} {a : G}
    (hS : Swap20 A V I₀ I₁ a) : conjSubgroup I₁ a = I₀ := by
  rcases hS.acts a hS.mem with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact absurd (h0.symm.trans hS.swap) (s16c167_twenty_ne hS)
  · exact h1

private theorem s16c167_twenty_mem_conjSubgroup {X Y : Subgroup G} {g x : G}
    (h : conjSubgroup X g = Y) (hx : x ∈ X) : g⁻¹ * x * g ∈ Y := by
  rw [← h]
  have := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
  simpa [conjSubgroup, MulAut.conj_apply] using this

private theorem s16c167_twenty_inf_centralizer_eq_bot {A V I₀ I₁ : Subgroup G} {a : G}
    (hS : Swap20 A V I₀ I₁ a) :
    I₀ ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxI₀, hxcent⟩ := Subgroup.mem_inf.1 hx
  have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.1 hxcent a hS.mem
  have hmem : a⁻¹ * x * a ∈ I₁ := s16c167_twenty_mem_conjSubgroup hS.swap hxI₀
  have hx_eq : a⁻¹ * x * a = x := by
    calc a⁻¹ * x * a = a⁻¹ * (x * a) := by rw [mul_assoc]
      _ = a⁻¹ * (a * x) := by rw [← hxa]
      _ = x := by group
  rw [hx_eq] at hmem
  have : x ∈ I₀ ⊓ I₁ := ⟨hxI₀, hmem⟩
  rw [hS.inf] at this
  exact Subgroup.mem_bot.1 this

private theorem s16c167_twenty_eq_left_of_mul_eq_mul {I J : Subgroup G} (hinf : I ⊓ J = ⊥)
    {x y x' y' : G} (hx : x ∈ I) (hy : y ∈ J) (hx' : x' ∈ I) (hy' : y' ∈ J)
    (h : x * y = x' * y') : x = x' := by
  have hmem : x'⁻¹ * x ∈ I ⊓ J := by
    refine ⟨I.mul_mem (I.inv_mem hx') hx, ?_⟩
    have hxy : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
        _ = y' * y⁻¹ := by group
    rw [hxy]
    exact J.mul_mem hy' (J.inv_mem hy)
  rw [hinf] at hmem
  have h1 : x'⁻¹ * x = 1 := Subgroup.mem_bot.1 hmem
  calc x = x' * (x'⁻¹ * x) := by group
    _ = x' := by rw [h1, mul_one]

private theorem s16c167_twenty_comm {A : Subgroup G} (hA : IsElemAbelian 2 A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem s16c167_twenty_conj_mul_inv {x y a : G} (h : x * a = a * x) :
    x * (a * y * a⁻¹) * x⁻¹ = a * (x * y * x⁻¹) * a⁻¹ := by
  have hx : a⁻¹ * x⁻¹ = x⁻¹ * a⁻¹ := by
    have := congrArg Inv.inv h
    simpa [mul_inv_rev] using this
  calc x * (a * y * a⁻¹) * x⁻¹ = (x * a) * y * (a⁻¹ * x⁻¹) := by group
    _ = (a * x) * y * (x⁻¹ * a⁻¹) := by rw [h, hx]
    _ = a * (x * y * x⁻¹) * a⁻¹ := by group

private theorem s16c167_twenty_centralizer_components {C I J : Subgroup G}
    (hCI : ∀ d ∈ C, conjSubgroup I d = I) (hCJ : ∀ d ∈ C, conjSubgroup J d = J)
    {w : G} (hw : w ∈ Subgroup.centralizer (C : Set G)) {wI : G} (hwI : wI ∈ I)
    {wJ : G} (hwJ : wJ ∈ J) (heq : wI * wJ = w) (hinf : I ⊓ J = ⊥) :
    wI ∈ Subgroup.centralizer (C : Set G) ∧ wJ ∈ Subgroup.centralizer (C : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hw
  have key : ∀ d ∈ C, d * wI * d⁻¹ = wI ∧ d * wJ * d⁻¹ = wJ := by
    intro d hd
    have hdI : d * wI * d⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.1 (conjSubgroup_eq_iff_mem_normalizer.1 (hCI d hd)) wI).1 hwI
    have hdJ : d * wJ * d⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.1 (conjSubgroup_eq_iff_mem_normalizer.1 (hCJ d hd)) wJ).1 hwJ
    have hdw : d * w = w * d := hw d hd
    have hprod : (d * wI * d⁻¹) * (d * wJ * d⁻¹) = wI * wJ := by
      calc (d * wI * d⁻¹) * (d * wJ * d⁻¹) = d * (wI * wJ) * d⁻¹ := by group
        _ = d * w * d⁻¹ := by rw [heq]
        _ = w := by
              calc d * w * d⁻¹ = w * d * d⁻¹ := by rw [hdw]
                _ = w := by group
        _ = wI * wJ := heq.symm
    have heqI : d * wI * d⁻¹ = wI :=
      s16c167_twenty_eq_left_of_mul_eq_mul hinf hdI hdJ hwI hwJ hprod
    have heqJ : d * wJ * d⁻¹ = wJ := by
      have h' := hprod
      rw [heqI] at h'
      exact mul_left_cancel h'
    exact ⟨heqI, heqJ⟩
  refine ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_iff]
  · intro d hd
    calc d * wI = d * wI * d⁻¹ * d := by group
      _ = wI * d := by rw [(key d hd).1]
  · intro d hd
    calc d * wJ = d * wJ * d⁻¹ * d := by group
      _ = wJ * d := by rw [(key d hd).2]

private theorem s16c167_twenty_mem_sup_of_commute {I J : Subgroup G}
    (hcomm : ∀ i ∈ I, ∀ j ∈ J, i * j = j * i) {x : G} (hx : x ∈ I ⊔ J) :
    ∃ i ∈ I, ∃ j ∈ J, i * j = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ i ∈ I, ∃ j ∈ J, i * j = x}
      one_mem' := ⟨1, I.one_mem, 1, J.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨i₁, hi₁, j₁, hj₁, rfl⟩ ⟨i₂, hi₂, j₂, hj₂, rfl⟩
        refine ⟨i₁ * i₂, I.mul_mem hi₁ hi₂, j₁ * j₂, J.mul_mem hj₁ hj₂, ?_⟩
        calc (i₁ * i₂) * (j₁ * j₂) = i₁ * (i₂ * j₁) * j₂ := by group
          _ = i₁ * (j₁ * i₂) * j₂ := by rw [hcomm i₂ hi₂ j₁ hj₁]
          _ = (i₁ * j₁) * (i₂ * j₂) := by group
      inv_mem' := by
        rintro x ⟨i, hi, j, hj, rfl⟩
        refine ⟨i⁻¹, I.inv_mem hi, j⁻¹, J.inv_mem hj, ?_⟩
        calc i⁻¹ * j⁻¹ = j⁻¹ * i⁻¹ := by rw [hcomm i⁻¹ (I.inv_mem hi) j⁻¹ (J.inv_mem hj)]
          _ = (i * j)⁻¹ := by group }
  have hle : I ⊔ J ≤ T :=
    sup_le (fun i hi => ⟨i, hi, 1, J.one_mem, by simp⟩)
      (fun j hj => ⟨1, I.one_mem, j, hj, by simp⟩)
  simpa [T] using hle hx

private theorem s16c167_twenty_card_sup_eq_mul {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥H × ↥K =>
      (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ K)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have hv : (h₁ : G) * k₁ = (h₂ : G) * k₂ := congrArg Subtype.val heq
    have key : (h₂ : G)⁻¹ * h₁ = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc (h₂ : G)⁻¹ * h₁
          = (h₂ : G)⁻¹ * ((h₁ : G) * k₁) * (k₁ : G)⁻¹ := by group
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * k₂) * (k₁ : G)⁻¹ := by rw [hv]
        _ = (k₂ : G) * (k₁ : G)⁻¹ := by group
    have hmem : (h₂ : G)⁻¹ * h₁ ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, key.symm ▸ K.mul_mem k₂.2 (K.inv_mem k₁.2)⟩
    rw [hinf] at hmem
    have h1eq : (h₂ : G)⁻¹ * h₁ = 1 := Subgroup.mem_bot.1 hmem
    have hHval : (h₁ : G) = (h₂ : G) := by
      calc (h₁ : G) = (h₂ : G) * ((h₂ : G)⁻¹ * (h₁ : G)) := by group
        _ = (h₂ : G) := by rw [h1eq, mul_one]
    have hKval : (k₁ : G) = (k₂ : G) := by
      have h' := hv
      rw [hHval] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hHval) (Subtype.ext hKval)
  · intro x
    obtain ⟨h, hh, k, hk, hk_eq⟩ := s16c167_twenty_mem_sup_of_commute hcomm x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hk_eq⟩

private theorem s16c167_twenty_relIndex_eq_two {A V I₀ I₁ B₀ : Subgroup G} {a : G}
    (hS : Swap20 A V I₀ I₁ a)
    (hB₀ : ∀ x : G, x ∈ B₀ ↔ x ∈ A ∧ conjSubgroup I₀ x = I₀) :
    B₀.relIndex A = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨a, hS.mem, ?_, ?_⟩
  · intro haB₀
    exact s16c167_twenty_ne hS (((hB₀ a).1 haB₀).2.symm.trans hS.swap)
  · intro x hx
    by_cases hxB : x ∈ B₀
    · exact Or.inr hxB
    · left
      have hc : conjSubgroup I₀ x ≠ I₀ := fun h => hxB ((hB₀ x).2 ⟨hx, h⟩)
      rcases hS.acts x hx with ⟨h0, -⟩ | ⟨h0, -⟩
      · exact absurd h0 hc
      · have hconj : conjSubgroup I₀ (x * a) = I₀ := by
          rw [← conjSubgroup_conjSubgroup I₀ x a, h0, s16c167_twenty_conj_I₁ hS]
        exact (hB₀ (x * a)).2 ⟨A.mul_mem hx hS.mem, hconj⟩

theorem s16c167_twenty_hyper {A V I₀ I₁ : Subgroup G} {a : G} (hS : Swap20 A V I₀ I₁ a)
    (hAel : IsElemAbelian 2 A) (hVel : IsElemAbelian 2 V) :
    ∃ B₀ : Subgroup G, (∀ x : G, x ∈ B₀ ↔ x ∈ A ∧ conjSubgroup I₀ x = I₀) ∧
      Hyperplane1618 V A B₀ (V ⊓ centralizer (B₀ : Set G)) := by
  classical
  have hB₀mem : ∀ x : G, x ∈ (A ⊓ Subgroup.normalizer (I₀ : Set G)) ↔
      x ∈ A ∧ conjSubgroup I₀ x = I₀ := by
    intro x
    rw [Subgroup.mem_inf, conjSubgroup_eq_iff_mem_normalizer]
  refine ⟨A ⊓ Subgroup.normalizer (I₀ : Set G), hB₀mem, inf_le_left, ?_, rfl, ?_⟩
  · unfold E3.mQuot
    rw [s16c167_twenty_relIndex_eq_two hS hB₀mem]
    norm_num
  · intro hbad
    obtain ⟨z, hzI₀, hz1, hzcent⟩ :=
      CFSG.Quasithin.SteinbergBQ.exists_central_ne_one_of_le_normalizer
        (B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono inf_le_left hAel))
        (B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hS.le₀ hVel)) hS.ne_bot inf_le_right
    have hzQ : z ∈ V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (I₀ : Set G) : Subgroup G) : Set G) :=
      ⟨hS.le₀ hzI₀, Subgroup.mem_centralizer_iff.2 hzcent⟩
    have hzcentA : z ∈ Subgroup.centralizer (A : Set G) := by
      have hzA : z ∈ V ⊓ Subgroup.centralizer (A : Set G) := by
        rw [← hbad]
        exact hzQ
      exact hzA.2
    have hza : a * z = z * a := Subgroup.mem_centralizer_iff.1 hzcentA a hS.mem
    have hmem : a⁻¹ * z * a ∈ I₁ := s16c167_twenty_mem_conjSubgroup hS.swap hzI₀
    have hz_eq : a⁻¹ * z * a = z := by
      calc a⁻¹ * z * a = a⁻¹ * (z * a) := by rw [mul_assoc]
        _ = a⁻¹ * (a * z) := by rw [← hza]
        _ = z := by group
    rw [hz_eq] at hmem
    have hzinf : z ∈ I₀ ⊓ I₁ := ⟨hzI₀, hmem⟩
    rw [hS.inf] at hzinf
    exact hz1 (Subgroup.mem_bot.1 hzinf)

theorem s16c167_twenty_chain {A V I₀ I₁ B₀ U : Subgroup G} {a : G} (hS : Swap20 A V I₀ I₁ a)
    (hAel : IsElemAbelian 2 A) (hVel : IsElemAbelian 2 V)
    (hB₀ : ∀ x : G, x ∈ B₀ ↔ x ∈ A ∧ conjSubgroup I₀ x = I₀)
    (hU : U = V ⊓ centralizer (B₀ : Set G)) {i : ℕ}
    (hi : E3.mQuot U (V ⊓ centralizer (A : Set G)) ≤ i) :
    2 ≤ Nat.card ↥(I₀ ⊓ centralizer (B₀ : Set G)) ∧
      Nat.card ↥(I₀ ⊓ centralizer (B₀ : Set G)) ≤ 2 ^ i := by
  classical
  have hBA : B₀ ≤ A := fun x hx => ((hB₀ x).1 hx).1
  have hB₀I₀ : ∀ x ∈ B₀, conjSubgroup I₀ x = I₀ := fun x hx => ((hB₀ x).1 hx).2
  have hBp : IsPGroup 2 B₀ := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hBA hAel)
  have hB₀norm : B₀ ≤ Subgroup.normalizer (I₀ : Set G) := fun x hx =>
    conjSubgroup_eq_iff_mem_normalizer.1 (hB₀I₀ x hx)
  have hIp : IsPGroup 2 I₀ := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hS.le₀ hVel)
  obtain ⟨z, hzI₀, hz1, hzcent⟩ :=
    CFSG.Quasithin.SteinbergBQ.exists_central_ne_one_of_le_normalizer hBp hIp hS.ne_bot hB₀norm
  have hzQ : z ∈ I₀ ⊓ Subgroup.centralizer (B₀ : Set G) :=
    ⟨hzI₀, Subgroup.mem_centralizer_iff.2 hzcent⟩
  have hQne : I₀ ⊓ Subgroup.centralizer (B₀ : Set G) ≠ ⊥ := by
    intro hbot
    exact hz1 (Subgroup.mem_bot.1 (hbot ▸ hzQ))
  refine ⟨?_, ?_⟩
  · have hcard := (Subgroup.one_lt_card_iff_ne_bot
        (I₀ ⊓ Subgroup.centralizer (B₀ : Set G))).2 hQne
    omega
  · have hUV : U ≤ V := by rw [hU]; exact inf_le_left
    have hUp : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hUV hVel)
    have hQU : I₀ ⊓ Subgroup.centralizer (B₀ : Set G) ≤ U := by
      rw [hU]
      exact inf_le_inf hS.le₀ le_rfl
    have hCU : V ⊓ Subgroup.centralizer (A : Set G) ≤ U := by
      rw [hU]
      exact inf_le_inf le_rfl (Subgroup.centralizer_le hBA)
    have hQC : (I₀ ⊓ Subgroup.centralizer (B₀ : Set G)) ⊓
        (V ⊓ Subgroup.centralizer (A : Set G)) = ⊥ := by
      have hle : (I₀ ⊓ Subgroup.centralizer (B₀ : Set G)) ⊓
          (V ⊓ Subgroup.centralizer (A : Set G)) ≤
          I₀ ⊓ Subgroup.centralizer (A : Set G) :=
        le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_right)
      rw [s16c167_twenty_inf_centralizer_eq_bot hS] at hle
      exact le_bot_iff.1 hle
    have hcard := CFSG.card_mul_card_le_of_inf_eq_bot hQU hCU hQC
    have hrel : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex U *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card ↥U := by
      simpa [inf_eq_left.2 hCU] using
        (Subgroup.relIndex_mul_card (H := V ⊓ Subgroup.centralizer (A : Set G)) (K := U))
    rw [← hrel] at hcard
    haveI : Nonempty ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
      ⟨1, (V ⊓ Subgroup.centralizer (A : Set G)).one_mem⟩
    have hQle := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    calc Nat.card ↥(I₀ ⊓ Subgroup.centralizer (B₀ : Set G))
        ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex U := hQle
      _ = 2 ^ E3.mQuot U (V ⊓ Subgroup.centralizer (A : Set G)) :=
            E3.relIndex_eq_two_pow hUp (V ⊓ Subgroup.centralizer (A : Set G))
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

theorem s16c167_twenty_extend {A V I₀ I₁ B₀ C : Subgroup G} {a : G} (hS : Swap20 A V I₀ I₁ a)
    (hAel : IsElemAbelian 2 A) (hVel : IsElemAbelian 2 V)
    (hB₀ : ∀ x : G, x ∈ B₀ ↔ x ∈ A ∧ conjSubgroup I₀ x = I₀) (hCB : C ≤ B₀)
    (hC1 : E3.mQuot B₀ C = 1)
    (hbad : V ⊓ centralizer (C : Set G) ≠ V ⊓ centralizer (B₀ : Set G)) :
    ∃ D' : Subgroup G, Hyperplane1618 V A D' (V ⊓ centralizer (D' : Set G)) ∧ D' ≠ B₀ := by
  classical
  have haA : a ∈ A := hS.mem
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one]
    simpa [pow_two] using ha2
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hBA : B₀ ≤ A := fun x hx => ((hB₀ x).1 hx).1
  have hCA : C ≤ A := hCB.trans hBA
  have hB₀I₀ : ∀ x ∈ B₀, conjSubgroup I₀ x = I₀ := fun x hx => ((hB₀ x).1 hx).2
  have hB₀I₁ : ∀ x ∈ B₀, conjSubgroup I₁ x = I₁ := by
    intro x hx
    have hxI₀ : conjSubgroup I₀ x = I₀ := hB₀I₀ x hx
    rcases hS.acts x (hBA hx) with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact h1
    · exact absurd (h0.symm.trans hxI₀) (fun h => s16c167_twenty_ne hS h.symm)
  have haB : a ∉ B₀ := by
    intro h
    exact s16c167_twenty_ne hS ((hB₀I₀ a h).symm.trans hS.swap)
  have haC : a ∉ C := fun h => haB (hCB h)
  have hD'A : C ⊔ Subgroup.zpowers a ≤ A := sup_le hCA (Subgroup.zpowers_le.2 haA)
  have hBp : IsPGroup 2 B₀ := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hBA hAel)
  have hrelBC : C.relIndex B₀ = 2 := by
    have h := E3.relIndex_eq_two_pow (V := B₀) hBp C
    rw [hC1] at h
    simpa using h
  have hcardB : Nat.card ↥B₀ = 2 * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := B₀)
    rw [hrelBC, inf_eq_left.2 hCB] at h
    exact h.symm
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥B₀ := by
    have h := Subgroup.relIndex_mul_card (H := B₀) (K := A)
    rw [s16c167_twenty_relIndex_eq_two hS hB₀, inf_eq_left.2 hBA] at h
    exact h.symm
  have horder : orderOf a = 2 := by
    have hdiv : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 ha2
    have hne : orderOf a ≠ 1 := by
      intro h
      have : a ∈ B₀ := by
        rw [orderOf_eq_one_iff.1 h]
        exact B₀.one_mem
      exact haB this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hcommCa : ∀ c ∈ C, ∀ z ∈ Subgroup.zpowers a, c * z = z * c :=
    fun c hc z hz => s16c167_twenty_comm hAel (hCA hc) (Subgroup.zpowers_le.2 haA hz)
  have hCinf : C ⊓ Subgroup.zpowers a = ⊥ := by
    have hdvd : Nat.card ↥(C ⊓ Subgroup.zpowers a) ∣ 2 := by
      have h := Subgroup.card_dvd_of_le (H := C ⊓ Subgroup.zpowers a)
        (K := Subgroup.zpowers a) inf_le_right
      rwa [Nat.card_zpowers, horder] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle_card : Nat.card ↥(Subgroup.zpowers a) ≤ Nat.card ↥(C ⊓ Subgroup.zpowers a) := by
        rw [Nat.card_zpowers, horder, h2]
      have heq : C ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right hle_card
      have ha_mem : a ∈ C ⊓ Subgroup.zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haC ha_mem.1
  have hcardD : Nat.card ↥(C ⊔ Subgroup.zpowers a) = 2 * Nat.card ↥C := by
    rw [s16c167_twenty_card_sup_eq_mul hcommCa hCinf, Nat.card_zpowers, horder]
    ring
  have hcardA2 : Nat.card ↥A = 2 * Nat.card ↥(C ⊔ Subgroup.zpowers a) := by
    rw [hcardA, hcardB, hcardD]
  have hTU : V ⊓ Subgroup.centralizer (B₀ : Set G) ≤ V ⊓ Subgroup.centralizer (C : Set G) :=
    inf_le_inf le_rfl (Subgroup.centralizer_le hCB)
  have hw_exists : ∃ w ∈ V ⊓ Subgroup.centralizer (C : Set G),
      w ∉ V ⊓ Subgroup.centralizer (B₀ : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hbad (le_antisymm hTU hcon).symm
  obtain ⟨w, hwT, hwU⟩ := hw_exists
  have hwV : w ∈ I₀ ⊔ I₁ := by rw [hS.sup]; exact hwT.1
  obtain ⟨w₀, hw₀I₀, w₁, hw₁I₁, hw_eq⟩ :=
    s16c167_twenty_mem_sup_of_commute
      (fun i hi j hj => s16c167_twenty_comm hVel (hS.le₀ hi) (hS.le₁ hj)) hwV
  have hCI₀ : ∀ d ∈ C, conjSubgroup I₀ d = I₀ := fun d hd => hB₀I₀ d (hCB hd)
  have hCI₁ : ∀ d ∈ C, conjSubgroup I₁ d = I₁ := fun d hd => hB₀I₁ d (hCB hd)
  have hwcent := s16c167_twenty_centralizer_components hCI₀ hCI₁ hwT.2 hw₀I₀ hw₁I₁ hw_eq hS.inf
  have hw₀cent : w₀ ∈ Subgroup.centralizer (C : Set G) := hwcent.1
  have hw₁cent : w₁ ∈ Subgroup.centralizer (C : Set G) := hwcent.2
  have hu_exists : ∃ u ∈ I₀, u ∈ Subgroup.centralizer (C : Set G) ∧
      u ∉ Subgroup.centralizer (B₀ : Set G) := by
    by_cases hw₀B : w₀ ∈ Subgroup.centralizer (B₀ : Set G)
    · have hw₁B : w₁ ∉ Subgroup.centralizer (B₀ : Set G) := by
        intro hw₁B
        have hwB : w ∈ Subgroup.centralizer (B₀ : Set G) := by
          rw [← hw_eq]
          rw [Subgroup.mem_centralizer_iff] at hw₀B hw₁B ⊢
          intro d hd
          calc d * (w₀ * w₁) = (d * w₀) * w₁ := by group
            _ = (w₀ * d) * w₁ := by rw [hw₀B d hd]
            _ = w₀ * (d * w₁) := by group
            _ = w₀ * (w₁ * d) := by rw [hw₁B d hd]
            _ = (w₀ * w₁) * d := by group
        exact hwU ⟨hwT.1, hwB⟩
      refine ⟨a * w₁ * a⁻¹, ?_, ?_, ?_⟩
      · have hmem : a⁻¹ * w₁ * a ∈ I₀ :=
          s16c167_twenty_mem_conjSubgroup (s16c167_twenty_conj_I₁ hS) hw₁I₁
        simpa only [hainv] using hmem
      · rw [Subgroup.mem_centralizer_iff]
        intro d hd
        have hdA : d ∈ A := hCA hd
        have hda : d * a = a * d := s16c167_twenty_comm hAel hdA haA
        have hdw₁ : d * w₁ * d⁻¹ = w₁ := by
          have h' := Subgroup.mem_centralizer_iff.1 hw₁cent d hd
          calc d * w₁ * d⁻¹ = w₁ * d * d⁻¹ := by rw [h']
            _ = w₁ := by group
        have hconj : d * (a * w₁ * a⁻¹) * d⁻¹ = a * w₁ * a⁻¹ := by
          calc d * (a * w₁ * a⁻¹) * d⁻¹ = a * (d * w₁ * d⁻¹) * a⁻¹ :=
            s16c167_twenty_conj_mul_inv hda
            _ = a * w₁ * a⁻¹ := by rw [hdw₁]
        calc d * (a * w₁ * a⁻¹) = d * (a * w₁ * a⁻¹) * d⁻¹ * d := by group
          _ = (a * w₁ * a⁻¹) * d := by rw [hconj]
      · intro huB
        apply hw₁B
        rw [Subgroup.mem_centralizer_iff] at huB ⊢
        intro b hb
        have hbA : b ∈ A := hBA hb
        have hba : b * a = a * b := s16c167_twenty_comm hAel hbA haA
        have hconj : b * (a * w₁ * a⁻¹) * b⁻¹ = a * (b * w₁ * b⁻¹) * a⁻¹ :=
          s16c167_twenty_conj_mul_inv hba
        have hbw : b * (a * w₁ * a⁻¹) * b⁻¹ = a * w₁ * a⁻¹ := by
          calc b * (a * w₁ * a⁻¹) * b⁻¹ = (b * (a * w₁ * a⁻¹)) * b⁻¹ := rfl
            _ = ((a * w₁ * a⁻¹) * b) * b⁻¹ := by rw [huB b hb]
            _ = a * w₁ * a⁻¹ := by group
        have hcancel : b * w₁ * b⁻¹ = w₁ := by
          rw [hconj] at hbw
          have h2 : a * ((b * w₁ * b⁻¹) * a⁻¹) = a * (w₁ * a⁻¹) := by
            simpa only [mul_assoc] using hbw
          exact mul_right_cancel (mul_left_cancel h2)
        calc b * w₁ = b * w₁ * b⁻¹ * b := by group
          _ = w₁ * b := by rw [hcancel]
    · exact ⟨w₀, hw₀I₀, hw₀cent, hw₀B⟩
  obtain ⟨u, huI₀, huCent, huNotB⟩ := hu_exists
  set e : G := u * (a * u * a⁻¹) with he_def
  have hauI₁ : a * u * a⁻¹ ∈ I₁ := by
    have hmem : a⁻¹ * u * a ∈ I₁ := s16c167_twenty_mem_conjSubgroup hS.swap huI₀
    simpa only [hainv] using hmem
  have heV : e ∈ V := by
    rw [he_def]
    exact V.mul_mem (hS.le₀ huI₀) (hS.le₁ hauI₁)
  have huVcent : a * u * a⁻¹ ∈ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdA : d ∈ A := hCA hd
    have hda : d * a = a * d := s16c167_twenty_comm hAel hdA haA
    have hdu : d * u * d⁻¹ = u := by
      have h' := Subgroup.mem_centralizer_iff.1 huCent d hd
      calc d * u * d⁻¹ = u * d * d⁻¹ := by rw [h']
        _ = u := by group
    have hconj : d * (a * u * a⁻¹) * d⁻¹ = a * u * a⁻¹ := by
      calc d * (a * u * a⁻¹) * d⁻¹ = a * (d * u * d⁻¹) * a⁻¹ :=
        s16c167_twenty_conj_mul_inv hda
        _ = a * u * a⁻¹ := by rw [hdu]
    calc d * (a * u * a⁻¹) = d * (a * u * a⁻¹) * d⁻¹ * d := by group
      _ = (a * u * a⁻¹) * d := by rw [hconj]
  have heCentC : e ∈ Subgroup.centralizer (C : Set G) := by
    rw [he_def]
    exact (Subgroup.centralizer (C : Set G)).mul_mem huCent huVcent
  have hae_eq : a * e = e * a := by
    have hconj : a * e * a⁻¹ = e := by
      rw [he_def]
      have hauFix : a * (a * u * a⁻¹) * a⁻¹ = u := by
        rw [hainv]
        rw [show a * (a * u * a) * a = (a * a) * u * (a * a) by group]
        rw [haa]
        group
      calc a * (u * (a * u * a⁻¹)) * a⁻¹
          = (a * u * a⁻¹) * (a * (a * u * a⁻¹) * a⁻¹) := by group
        _ = (a * u * a⁻¹) * u := by rw [hauFix]
        _ = u * (a * u * a⁻¹) :=
              s16c167_twenty_comm hVel (hS.le₁ hauI₁) (hS.le₀ huI₀)
    calc a * e = a * e * a⁻¹ * a := by group
      _ = e * a := by rw [hconj]
  have heCentZ : e ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (((commute_iff_eq a e).2 hae_eq).zpow_left m).eq
  have heCentD : e ∈
      Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨c, hcC, z, hz, hcz⟩ := s16c167_twenty_mem_sup_of_commute hcommCa hd
    rw [← hcz]
    have hce : c * e = e * c := Subgroup.mem_centralizer_iff.1 heCentC c hcC
    have hze : z * e = e * z := Subgroup.mem_centralizer_iff.1 heCentZ z hz
    calc (c * z) * e = c * (z * e) := by group
      _ = c * (e * z) := by rw [hze]
      _ = (c * e) * z := by group
      _ = (e * c) * z := by rw [hce]
      _ = e * (c * z) := by group
  have heNotB : e ∉ Subgroup.centralizer (B₀ : Set G) := by
    intro heB
    apply huNotB
    rw [Subgroup.mem_centralizer_iff] at heB ⊢
    intro b hb
    have hbI₀ : b * u * b⁻¹ ∈ I₀ :=
      (Subgroup.mem_normalizer_iff.1 (conjSubgroup_eq_iff_mem_normalizer.1 (hB₀I₀ b hb)) u).1
        huI₀
    have hbI₁ : b * (a * u * a⁻¹) * b⁻¹ ∈ I₁ :=
      (Subgroup.mem_normalizer_iff.1 (conjSubgroup_eq_iff_mem_normalizer.1 (hB₀I₁ b hb))
        (a * u * a⁻¹)).1 hauI₁
    have hbe : b * e * b⁻¹ = e := by
      have h' := heB b hb
      calc b * e * b⁻¹ = e * b * b⁻¹ := by rw [h']
        _ = e := by group
    have hprod : (b * u * b⁻¹) * (b * (a * u * a⁻¹) * b⁻¹) = u * (a * u * a⁻¹) := by
      calc (b * u * b⁻¹) * (b * (a * u * a⁻¹) * b⁻¹)
          = b * (u * (a * u * a⁻¹)) * b⁻¹ := by group
        _ = b * e * b⁻¹ := by rw [he_def]
        _ = e := hbe
        _ = u * (a * u * a⁻¹) := he_def.symm
    have hbu : b * u * b⁻¹ = u :=
      s16c167_twenty_eq_left_of_mul_eq_mul hS.inf hbI₀ hbI₁ huI₀ hauI₁ hprod
    calc b * u = b * u * b⁻¹ * b := by group
      _ = u * b := by rw [hbu]
  have heNotA : e ∉ Subgroup.centralizer (A : Set G) := fun h =>
    heNotB (Subgroup.centralizer_le hBA h)
  have heT : e ∈ V ⊓ Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) :=
    ⟨heV, heCentD⟩
  have heUnot : e ∉ V ⊓ Subgroup.centralizer (A : Set G) := fun h => heNotA h.2
  have hrelAD : (C ⊔ Subgroup.zpowers a).relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_card (H := C ⊔ Subgroup.zpowers a) (K := A)
    rw [inf_eq_left.2 hD'A, hcardA2] at h
    haveI : Nonempty ↥(C ⊔ Subgroup.zpowers a) :=
      ⟨1, (C ⊔ Subgroup.zpowers a).one_mem⟩
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hmQuot : E3.mQuot A (C ⊔ Subgroup.zpowers a) = 1 := by
    unfold E3.mQuot
    rw [hrelAD]
    norm_num
  have hD'ne : (C ⊔ Subgroup.zpowers a) ≠ B₀ := by
    intro h
    have ha_mem : a ∈ C ⊔ Subgroup.zpowers a :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    rw [h] at ha_mem
    exact haB ha_mem
  exact ⟨C ⊔ Subgroup.zpowers a, ⟨hD'A, hmQuot, rfl, fun heq => heUnot (heq ▸ heT)⟩, hD'ne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
