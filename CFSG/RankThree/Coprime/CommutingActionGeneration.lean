module

public import CFSG.RankThree.Coprime.SolvableFixedCommutator
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantMinimalNormal

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG.LocalAnalysis.ComponentInitial

universe u

section Helpers

variable {W H : Type*} [Group W] [Group H] [MulDistribMulAction W H]

theorem actionCommutator_mono {K L : Subgroup H} (h : K ≤ L) :
    actionCommutator W K ≤ actionCommutator W L :=
  closure_mono fun _ ⟨x, hx, w, hw⟩ => ⟨x, h hx, w, hw⟩

theorem actionCommutator_le_self {K : Subgroup H} (hK : ∀ (w : W), ∀ x ∈ K, w • x ∈ K) :
    actionCommutator W K ≤ K :=
  (closure_le _).2 fun _ ⟨x, hx, w, hw⟩ => hw ▸ K.mul_mem (K.inv_mem hx) (hK w x hx)

theorem map_actionCommutator {Q : Type*} [Group Q] [MulDistribMulAction W Q] (f : H →* Q)
    (hf : ∀ (w : W) (x : H), f (w • x) = w • f x) (K : Subgroup H) :
    (actionCommutator W K).map f = actionCommutator W (K.map f) := by
  rw [actionCommutator, MonoidHom.map_closure, actionCommutator]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, w, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, w, by rw [map_mul, map_inv, hf]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, w, rfl⟩
    exact ⟨x⁻¹ * (w • x), ⟨x, hx, w, rfl⟩, by rw [map_mul, map_inv, hf]⟩

theorem smul_mem_actionCommutator {K : Subgroup H} (hK : ∀ (w : W), ∀ x ∈ K, w • x ∈ K)
    (w : W) {y : H} (hy : y ∈ actionCommutator W K) : w • y ∈ actionCommutator W K := by
  have hle : actionCommutator W K ≤
      (actionCommutator W K).comap (MulDistribMulAction.toMonoidHom H w) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    change w • (x⁻¹ * (v • x)) ∈ actionCommutator W K
    have h : w • (x⁻¹ * (v • x)) = (w • x)⁻¹ * ((w * v * w⁻¹) • (w • x)) := by
      rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
    rw [h]
    exact gen_mem_actionCommutator (hK w x hx) _
  exact hle hy

omit [MulDistribMulAction W H] in
theorem mem_fixedPointSubgroup_zpowers_iff_smul_eq {B X : Type*} [Group B] [Group X]
    [MulDistribMulAction B X] {b : B} {x : X} :
    x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers b) X ↔ b • x = x := by
  constructor
  · intro h
    exact h ⟨b, mem_zpowers b⟩
  · intro h
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
    have hb : b ∈ MulAction.stabilizer B x := h
    exact (MulAction.stabilizer B x).zpow_mem hb m

end Helpers

section Steps

variable {B W H : Type*} [Group B] [Group W] [Group H] [MulDistribMulAction B H]
  [MulDistribMulAction W H]

theorem map_mk_fixedPointSubgroup_zpowers {p : ℕ} [Fact p.Prime] [Finite B] [Finite H]
    (hBp : IsPGroup p B) (N : Subgroup H) [N.Normal] (hNinv : CFSG.IsInvariant B H N)
    (hN : ¬ p ∣ Nat.card N) (b : B) :
    letI : MulDistribMulAction B (H ⧸ N) := quotientMulDistribMulAction N hNinv
    (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H).map (QuotientGroup.mk' N) =
      CFSG.fixedPointSubgroup (Subgroup.zpowers b) (H ⧸ N) := by
  let : MulDistribMulAction B (H ⧸ N) := quotientMulDistribMulAction N hNinv
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_fixedPointSubgroup_zpowers_iff_smul_eq] at hx
    rw [mem_fixedPointSubgroup_zpowers_iff_smul_eq]
    change ((b • x : H) : H ⧸ N) = x
    rw [hx]
  · intro q hq
    rw [mem_fixedPointSubgroup_zpowers_iff_smul_eq] at hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let α : Subgroup.zpowers b →* MulAut H :=
      (MulDistribMulAction.toMulAut B H).comp (Subgroup.zpowers b).subtype
    have hαN : ∀ a : Subgroup.zpowers b, ∀ n ∈ N, α a n ∈ N :=
      fun a n hn => (hNinv.invariant (a : B) n).1 hn
    have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting p
      (hBp.to_subgroup _) α N hαN hN
    have hmem : (x : H ⧸ N) ∈ {q : H ⧸ N |
        ∀ a, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
      rintro ⟨a, ha⟩
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      have hb : b ∈ MulAction.stabilizer B (x : H ⧸ N) := hq
      exact (MulAction.stabilizer B (x : H ⧸ N)).zpow_mem hb m
    rw [hlift] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    refine ⟨c, ?_, hcx⟩
    rw [SetLike.mem_coe, mem_fixedPointSubgroup_zpowers_iff_smul_eq]
    exact hc ⟨b, mem_zpowers b⟩

theorem actionCommutator_le_sup_of_quotient {p : ℕ} [Fact p.Prime] [Finite B] [Finite H]
    (hBp : IsPGroup p B) (N : Subgroup H) [N.Normal] (hNB : CFSG.IsInvariant B H N)
    (hNW : CFSG.IsInvariant W H N) (hN : ¬ p ∣ Nat.card N)
    (hQ : let : MulDistribMulAction B (H ⧸ N) := quotientMulDistribMulAction N hNB
      let : MulDistribMulAction W (H ⧸ N) := quotientMulDistribMulAction N hNW
      actionCommutator W (⊤ : Subgroup (H ⧸ N)) = ⨆ (b : B) (_ : b ≠ 1),
        actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) (H ⧸ N))) :
    actionCommutator W (⊤ : Subgroup H) ≤ (⨆ (b : B) (_ : b ≠ 1),
      actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H)) ⊔ N := by
  let : MulDistribMulAction B (H ⧸ N) := quotientMulDistribMulAction N hNB
  let : MulDistribMulAction W (H ⧸ N) := quotientMulDistribMulAction N hNW
  have hQ' : actionCommutator W (⊤ : Subgroup (H ⧸ N)) = ⨆ (b : B) (_ : b ≠ 1),
      actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) (H ⧸ N)) := hQ
  have hf : ∀ (w : W) (x : H), QuotientGroup.mk' N (w • x) = w • QuotientGroup.mk' N x :=
    fun _ _ => rfl
  have hmap : (actionCommutator W (⊤ : Subgroup H)).map (QuotientGroup.mk' N) =
      (⨆ (b : B) (_ : b ≠ 1),
        actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H)).map
          (QuotientGroup.mk' N) := by
    rw [map_actionCommutator _ hf,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), hQ', Subgroup.map_iSup]
    refine iSup_congr fun b => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun _ => ?_
    rw [map_actionCommutator _ hf, map_mk_fixedPointSubgroup_zpowers hBp N hNB hN b]
  have h := Subgroup.map_le_iff_le_comap.mp hmap.le
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h

theorem actionCommutator_le_of_abelian {p : ℕ} [Fact p.Prime] [Finite B]
    [IsElementaryAbelian p B] [Finite H] (hB : p ^ 2 ≤ Nat.card B) (N : Subgroup H)
    [IsMulCommutative N] (hNB : CFSG.IsInvariant B H N)
    (hNW : ∀ (w : W), ∀ x ∈ N, w • x ∈ N) (hN : ¬ p ∣ Nat.card N) :
    actionCommutator W N ≤ ⨆ (b : B) (_ : b ≠ 1),
      actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H) := by
  set Y := ⨆ (b : B) (_ : b ≠ 1),
    actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H) with hY
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := B) (H := N) hB hN
  have hNc : ∀ x y : H, x ∈ N → y ∈ N → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : N) ⟨y, hy⟩)
  refine (closure_le _).2 ?_
  rintro _ ⟨x, hx, w, rfl⟩
  let T : Subgroup N :=
    { carrier := {y | (y : H)⁻¹ * (w • (y : H)) ∈ Y}
      one_mem' := by simp [Y.one_mem]
      mul_mem' := by
        intro a b ha hb
        change ((a : H) * b)⁻¹ * (w • ((a : H) * b)) ∈ Y
        have hc := hNc (b : H)⁻¹ ((a : H)⁻¹ * (w • (a : H))) (N.inv_mem b.2)
          (N.mul_mem (N.inv_mem a.2) (hNW w _ a.2))
        have h : ((a : H) * b)⁻¹ * (w • ((a : H) * b)) =
            ((a : H)⁻¹ * (w • (a : H))) * ((b : H)⁻¹ * (w • (b : H))) := by
          rw [smul_mul', mul_inv_rev]
          calc (b : H)⁻¹ * (a : H)⁻¹ * (w • (a : H) * w • (b : H)) =
              (b : H)⁻¹ * ((a : H)⁻¹ * (w • (a : H))) * w • (b : H) := by group
            _ = ((a : H)⁻¹ * (w • (a : H))) * (b : H)⁻¹ * w • (b : H) := by rw [hc]
            _ = _ := by group
        rw [h]
        exact Y.mul_mem ha hb
      inv_mem' := by
        intro a ha
        change ((a : H)⁻¹)⁻¹ * (w • (a : H)⁻¹) ∈ Y
        have hc := hNc (a : H) (w • (a : H))⁻¹ a.2 (N.inv_mem (hNW w _ a.2))
        have h : ((a : H)⁻¹)⁻¹ * (w • (a : H)⁻¹) = ((a : H)⁻¹ * (w • (a : H)))⁻¹ := by
          rw [smul_inv', inv_inv, hc, mul_inv_rev, inv_inv]
        rw [h]
        exact Y.inv_mem ha }
  have hT : (⊤ : Subgroup N) ≤ T := by
    rw [← hgen]
    refine iSup₂_le fun b hb => ?_
    intro y hy
    have hyH : (y : H) ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers b) H := by
      rw [mem_fixedPointSubgroup_zpowers_iff_smul_eq] at hy ⊢
      exact congrArg Subtype.val hy
    exact le_iSup₂ (f := fun (b : B) (_ : b ≠ 1) =>
      actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H)) b hb
      (gen_mem_actionCommutator hyH w)
  exact hT (mem_top ⟨x, hx⟩)

theorem conj_mem_actionCommutator_of_fixed {N : Subgroup H} [N.Normal] {c : H}
    (hc : ∀ w : W, w • c = c) {x : H} (hx : x ∈ actionCommutator W N) :
    c * x * c⁻¹ ∈ actionCommutator W N := by
  have hle : actionCommutator W N ≤
      (actionCommutator W N).comap (MulAut.conj c).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨n, hn, w, rfl⟩
    change c * (n⁻¹ * (w • n)) * c⁻¹ ∈ actionCommutator W N
    have h : c * (n⁻¹ * (w • n)) * c⁻¹ = (c * n * c⁻¹)⁻¹ * (w • (c * n * c⁻¹)) := by
      rw [smul_mul', smul_mul', smul_inv', hc w]
      group
    rw [h]
    exact gen_mem_actionCommutator (‹N.Normal›.conj_mem n hn c) w
  exact hle hx

theorem le_of_minimal_of_actionCommutator_ne_bot [Finite W] [Finite H]
    (hH : Group.IsSolvable H) (hcop : Nat.Coprime (Nat.card H) (Nat.card W))
    (hcomm : ∀ (b : B) (w : W) (x : H), b • w • x = w • b • x) (N : Subgroup H) [N.Normal]
    [IsMulCommutative N] (hNB : ∀ (b : B), ∀ x ∈ N, b • x ∈ N)
    (hNW : ∀ (w : W), ∀ x ∈ N, w • x ∈ N)
    (hmin : ∀ M : Subgroup H, M ≤ N → M.Normal → M ≠ ⊥ → (∀ (b : B), ∀ x ∈ M, b • x ∈ M) →
      (∀ (w : W), ∀ x ∈ M, w • x ∈ M) → M = N)
    (Y : Subgroup H) (hne : actionCommutator W N ≠ ⊥) (hNWY : actionCommutator W N ≤ Y)
    (hDYN : actionCommutator W (⊤ : Subgroup H) ≤ Y ⊔ N) : N ≤ Y := by
  set K := actionCommutator W N with hK
  have hKN : K ≤ N := actionCommutator_le_self hNW
  have hKB : ∀ (b : B), ∀ x ∈ K, b • x ∈ K := by
    intro b x hx
    have hle : K ≤ K.comap (MulDistribMulAction.toMonoidHom H b) := by
      refine (closure_le _).2 ?_
      rintro _ ⟨n, hn, w, rfl⟩
      change b • (n⁻¹ * (w • n)) ∈ K
      rw [smul_mul', smul_inv', hcomm]
      exact gen_mem_actionCommutator (hNB b n hn) w
    exact hle hx
  have hKW : ∀ (w : W), ∀ x ∈ K, w • x ∈ K := fun w x hx => smul_mem_actionCommutator hNW w hx
  have hM : Subgroup.normalClosure (K : Set H) = N := by
    refine hmin _ (Subgroup.normalClosure_le_normal hKN) Subgroup.normalClosure_normal ?_
      (CFSG.SignalizerFunctor.Helpers.invariant_normal_closure K hKB)
      (CFSG.SignalizerFunctor.Helpers.invariant_normal_closure K hKW)
    intro hbot
    apply hne
    rw [eq_bot_iff]
    exact (show K ≤ Subgroup.normalClosure (K : Set H) from Subgroup.subset_normalClosure).trans
      hbot.le
  have hfac := (solvable_coprime_fixed_commutator_factorization (A := W) hH hcop).2.2.1
  have hNc : ∀ x y : H, x ∈ N → y ∈ N → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : N) ⟨y, hy⟩)
  rw [← hM]
  refine (closure_le Y).2 ?_
  intro z hz
  obtain ⟨x, hxK, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
  obtain ⟨h, rfl⟩ := isConj_iff.mp hconj
  obtain ⟨d, hd, c, hc, rfl⟩ := hfac h
  obtain ⟨y, hy, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hDYN hd)
  have hcx : c * x * c⁻¹ ∈ K := conj_mem_actionCommutator_of_fixed hc hxK
  have hn' : n * (c * x * c⁻¹) * n⁻¹ = c * x * c⁻¹ := by
    rw [hNc n _ hn (hKN hcx), mul_inv_cancel_right]
  have h : y * n * c * x * (y * n * c)⁻¹ = y * (n * (c * x * c⁻¹) * n⁻¹) * y⁻¹ := by group
  rw [h, hn']
  exact Y.mul_mem (Y.mul_mem hy (hNWY hcx)) (Y.inv_mem hy)

theorem le_of_actionCommutator_eq_bot [Finite W] [Finite H] (hH : Group.IsSolvable H)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card W)) (N : Subgroup H) [N.Normal]
    (hNW1 : actionCommutator W N = ⊥) (Y : Subgroup H) (hYW : ∀ (w : W), ∀ y ∈ Y, w • y ∈ Y)
    (hYD : Y ≤ actionCommutator W (⊤ : Subgroup H))
    (hDYN : actionCommutator W (⊤ : Subgroup H) ≤ Y ⊔ N) :
    actionCommutator W (⊤ : Subgroup H) ≤ Y := by
  set D := actionCommutator W (⊤ : Subgroup H) with hD
  have hfixN : ∀ (w : W), ∀ n ∈ N, w • n = n := by
    intro w n hn
    have h := gen_mem_actionCommutator (A := W) hn w
    rw [hNW1, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h.symm
  have hDcent : D ≤ centralizer (N : Set H) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨h, -, w, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro n hn
    have hm := hfixN w _ (‹N.Normal›.conj_mem n hn h)
    rw [smul_mul', smul_mul', smul_inv', hfixN w n hn] at hm
    calc n * (h⁻¹ * (w • h)) = h⁻¹ * (h * n * h⁻¹) * (w • h) := by group
      _ = h⁻¹ * (w • h * n * (w • h)⁻¹) * (w • h) := by rw [hm]
      _ = h⁻¹ * (w • h) * n := by group
  have hidem := (solvable_coprime_fixed_commutator_factorization (A := W) hH hcop).2.2.2
  refine le_trans (le_of_eq hidem.symm) ?_
  refine (closure_le _).2 ?_
  rintro _ ⟨d, hd, w, rfl⟩
  obtain ⟨y, hy, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hDYN hd)
  have hz : y⁻¹ * (w • y) ∈ Y := Y.mul_mem (Y.inv_mem hy) (hYW w y hy)
  have hzc := mem_centralizer_iff.mp (hDcent (hYD hz)) n hn
  have h : (y * n)⁻¹ * (w • (y * n)) = n⁻¹ * (y⁻¹ * (w • y) * n) := by
    rw [smul_mul', hfixN w n hn]
    group
  rw [h, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hz

end Steps

theorem solvable_commuting_action_fixed_commutator_generation {p : ℕ} [Fact p.Prime]
    {B : Type*} [Group B] [Finite B] [IsElementaryAbelian p B] (hB : p ^ 2 ≤ Nat.card B)
    {W : Type*} [Group W] [Finite W] {H : Type u} [Group H] [Finite H]
    (hH : Group.IsSolvable H) [MulDistribMulAction B H] [MulDistribMulAction W H]
    (hcomm : ∀ (b : B) (w : W) (x : H), b • w • x = w • b • x)
    (hcop : Nat.Coprime (Nat.card B * Nat.card W) (Nat.card H)) :
    actionCommutator W (⊤ : Subgroup H) = ⨆ (b : B) (_ : b ≠ 1),
      actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H) := by
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  have hpB : p ∣ Nat.card B := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := (Fact.out : p.Prime).one_lt
      rw [hk, pow_zero] at hB
      nlinarith
    rw [hk]
    exact dvd_pow_self p hk0
  suffices key : ∀ (n : ℕ) (H : Type u) [Group H] [Finite H] [MulDistribMulAction B H]
      [MulDistribMulAction W H], Nat.card H = n → Group.IsSolvable H →
      (∀ (b : B) (w : W) (x : H), b • w • x = w • b • x) →
      Nat.Coprime (Nat.card B * Nat.card W) (Nat.card H) →
      actionCommutator W (⊤ : Subgroup H) = ⨆ (b : B) (_ : b ≠ 1),
        actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H) from
    key _ H rfl hH hcomm hcop
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ _ hn hH hcomm hcop
  set Y := ⨆ (b : B) (_ : b ≠ 1),
    actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H) with hY
  have hYD : Y ≤ actionCommutator W (⊤ : Subgroup H) :=
    iSup₂_le fun b _ => actionCommutator_mono le_top
  refine le_antisymm ?_ hYD
  rcases subsingleton_or_nontrivial H with hs | hnt
  · intro x _
    rw [Subsingleton.elim x 1]
    exact Y.one_mem
  have := hH
  obtain ⟨N, hNn, hNbot, hNab, hNB, hNW, hNmin⟩ :=
    CFSG.SignalizerFunctor.Helpers.solvable_minimal_invariant_normal_exists
      (ActorType := B) (SecondActorType := W) (GroupType := H)
  have hNBinv : CFSG.IsInvariant B H N := ⟨fun b g => ⟨fun hg => hNB b g hg, fun hg => by
    simpa using hNB b⁻¹ _ hg⟩⟩
  have hNWinv : CFSG.IsInvariant W H N := ⟨fun w g => ⟨fun hg => hNW w g hg, fun hg => by
    simpa using hNW w⁻¹ _ hg⟩⟩
  have hpH : ¬ p ∣ Nat.card H := by
    intro h
    have h1 := Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_left hpB _) hcop
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 h)
  have hpN : ¬ p ∣ Nat.card N := fun h => hpH (h.trans (Subgroup.card_subgroup_dvd_card N))
  have hcopW : Nat.Coprime (Nat.card H) (Nat.card W) :=
    (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop).symm
  let : MulDistribMulAction B (H ⧸ N) := quotientMulDistribMulAction N hNBinv
  let : MulDistribMulAction W (H ⧸ N) := quotientMulDistribMulAction N hNWinv
  have hlt : Nat.card (H ⧸ N) < n := by
    rw [← hn, N.card_eq_card_quotient_mul_card_subgroup]
    have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot
    have h2 : 0 < Nat.card (H ⧸ N) := Nat.card_pos
    nlinarith
  have hQcomm : ∀ (b : B) (w : W) (x : H ⧸ N), b • w • x = w • b • x := by
    intro b w x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    change ((b • w • x : H) : H ⧸ N) = ((w • b • x : H) : H ⧸ N)
    rw [hcomm]
  have hQcop : Nat.Coprime (Nat.card B * Nat.card W) (Nat.card (H ⧸ N)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card N) hcop
  have hQ := ih _ hlt (H ⧸ N) rfl inferInstance hQcomm hQcop
  have hDYN := actionCommutator_le_sup_of_quotient hBp N hNBinv hNWinv hpN hQ
  have hNWY : actionCommutator W N ≤ Y := actionCommutator_le_of_abelian hB N hNBinv hNW hpN
  by_cases hNW1 : actionCommutator W N = ⊥
  · have hYW : ∀ (w : W), ∀ y ∈ Y, w • y ∈ Y := by
      intro w y hy
      have hle : Y ≤ Y.comap (MulDistribMulAction.toMonoidHom H w) := by
        refine iSup₂_le fun b hb x hx => ?_
        have hfixW : ∀ (v : W), ∀ z ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers b) H,
            v • z ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers b) H := by
          intro v z hz
          rw [mem_fixedPointSubgroup_zpowers_iff_smul_eq] at hz ⊢
          rw [hcomm, hz]
        exact le_iSup₂ (f := fun (b : B) (_ : b ≠ 1) =>
          actionCommutator W (CFSG.fixedPointSubgroup (Subgroup.zpowers b) H)) b hb
          (smul_mem_actionCommutator hfixW w hx)
      exact hle hy
    exact le_of_actionCommutator_eq_bot hH hcopW N hNW1 Y hYW hYD hDYN
  · have hNY := le_of_minimal_of_actionCommutator_ne_bot hH hcopW hcomm N hNB hNW hNmin Y hNW1
      hNWY hDYN
    exact hDYN.trans (sup_le le_rfl hNY)

end CFSG.RankThree.Coprime
