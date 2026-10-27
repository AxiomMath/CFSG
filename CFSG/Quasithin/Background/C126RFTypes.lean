module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem normal_le_center_of_quasisimple {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    (N : Subgroup Y) [N.Normal] (hN : N ≠ ⊤) : N ≤ Subgroup.center Y := by
  by_contra hnot
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Y)))
    with hbot | htop
  · apply hnot
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center Y) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center Y)) := Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · apply hN
    have hYN : ∀ y : Y, ∃ n ∈ N, ∃ z ∈ Subgroup.center Y, y = n * z := by
      intro y
      have : QuotientGroup.mk' (Subgroup.center Y) y ∈
          N.map (QuotientGroup.mk' (Subgroup.center Y)) := by rw [htop]; trivial
      obtain ⟨n, hn, hny⟩ := this
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hny
      exact ⟨n, hn, n⁻¹ * y, hny, by simp⟩
    have hab : ∀ a b : Y ⧸ N, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | _ y₁ =>
        induction b using QuotientGroup.induction_on with
        | _ y₂ =>
          obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hYN y₁
          obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hYN y₂
          have e1 : (QuotientGroup.mk (n₁ * z₁) : Y ⧸ N) = QuotientGroup.mk z₁ := by
            rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₁).2 hn₁, one_mul]
          have e2 : (QuotientGroup.mk (n₂ * z₂) : Y ⧸ N) = QuotientGroup.mk z₂ := by
            rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₂).2 hn₂, one_mul]
          rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.mp hz₂ z₁]
    have hcom : commutator Y ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' N ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab _ _
    exact eq_top_iff.2 (hY.1 ▸ hcom)

theorem map_center_le_center {Y W : Type*} [Group Y] [Group W] (f : Y →* W)
    (hf : Function.Surjective f) : (Subgroup.center Y).map f ≤ Subgroup.center W := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := hf g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]

theorem ker_eq_center_of_surjective {Y W : Type*} [Group Y] [Group W]
    (hY : CFSG.Open.IsQuasisimple Y) (f : Y →* W) (hf : Function.Surjective f) [Nontrivial W]
    (hW : Subgroup.center W = ⊥) : f.ker = Subgroup.center Y := by
  apply le_antisymm
  · refine normal_le_center_of_quasisimple hY f.ker ?_
    intro htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne W
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    apply hab
    have hx : x ∈ f.ker := htop ▸ Subgroup.mem_top x
    have hy : y ∈ f.ker := htop ▸ Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy]
  · intro z hz
    have h1 : f z ∈ Subgroup.center W := map_center_le_center f hf (Subgroup.mem_map_of_mem f hz)
    rw [hW, Subgroup.mem_bot] at h1
    exact h1

theorem center_sl2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem nonempty_sl2_mulEquiv_statedProj {F : Type} [Field F] [CharP F 2] :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans
    QuotientGroup.quotientBot).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (h : Nat.card F = 2 ^ n) : CharP F 2 := by
  have := Fintype.ofFinite F
  have hc : Fintype.card F % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card, h]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  exact ringChar.eq_iff.mp ((FiniteField.even_card_iff_char_two).2 hc)

theorem nontrivial_sl2 {F : Type} [Field F] : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => ?_⟩⟩
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  simp at this

theorem center_eq_bot_of_mulEquiv {L W : Type*} [Group L] [Group W] (e : L ≃* W)
    (h : Subgroup.center W = ⊥) : Subgroup.center L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro l hl
  have h1 : e l ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro s
    have := Subgroup.mem_center_iff.mp hl (e.symm s)
    calc s * e l = e (e.symm s * l) := by simp
      _ = e (l * e.symm s) := by rw [this]
      _ = e l * s := by simp
  rw [h, Subgroup.mem_bot] at h1
  exact e.injective (by rw [h1, map_one])

theorem center_eq_bot_of_sl2 {L F : Type} [Group L] [Field F] [CharP F 2]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Subgroup.center L = ⊥ :=
  center_eq_bot_of_mulEquiv e center_sl2_eq_bot

theorem c126_isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  push Not at hab
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hab⟩⟩
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ Subgroup.center Q)
      (f := QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q) inferInstance

theorem isPSL_two_two_quot_center {Y L : Type} [Group Y] [Group L]
    (hY : CFSG.Open.IsQuasisimple Y) (f : Y →* L) (hf : Function.Surjective f) {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.Quasithin.IsPSL 2 2 n (Y ⧸ Subgroup.center Y) := by
  have : CharP F 2 := charP_two_of_card (by omega) hF
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := nontrivial_sl2
  have : Nontrivial L := e.toEquiv.nontrivial
  have hker : f.ker = Subgroup.center Y :=
    ker_eq_center_of_surjective hY f hf (center_eq_bot_of_sl2 e)
  obtain ⟨e2⟩ := nonempty_sl2_mulEquiv_statedProj (F := F)
  have e1 : (Y ⧸ Subgroup.center Y) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨(e1.trans e).trans e2⟩⟩
  · intro h
    have h2 : (2 : ℕ) ^ n = 2 := congrArg Prod.snd h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · intro h
    have h2 : (2 : ℕ) ^ n = 3 := congrArg Prod.snd h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

end CFSG.Quasithin.C126
