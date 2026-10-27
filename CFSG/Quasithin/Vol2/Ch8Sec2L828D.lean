module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

section L828D

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_le_center_828 {K : Subgroup G} (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hperf : ⁅K, K⁆ = K) {D : Subgroup ↥K} (hD : D.Normal) (hDK : D ≠ ⊤) [Finite G] :
    D.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≤
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (hD.map _ (QuotientGroup.mk'_surjective _)) with h | h
  · exfalso
    apply hDK
    have hsurj : Function.Surjective ((QuotientGroup.mk' D).comp (CFSG.pCore 2 ↥K).subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective D q
      have hk : QuotientGroup.mk' (CFSG.pCore 2 ↥K) k ∈ D.map (QuotientGroup.mk' _) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdk⟩ := hk
      have hm : d⁻¹ * k ∈ CFSG.pCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk d : ↥K ⧸ CFSG.pCore 2 ↥K) = QuotientGroup.mk k := hdk
        rw [this, inv_mul_cancel]
      refine ⟨⟨d⁻¹ * k, hm⟩, ?_⟩
      show QuotientGroup.mk' D (d⁻¹ * k) = QuotientGroup.mk' D k
      have hd1 : QuotientGroup.mk' D d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      rw [map_mul, map_inv, hd1, inv_one, one_mul]
    have hO : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact @IsNilpotent.to_isSolvable _ _ (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).isNilpotent
    have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
    have hQp : Group.IsPerfect (↥K ⧸ D) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective D)
    have hQs : Group.IsSolvable (↥K ⧸ D) := Group.isSolvable_of_surjective hsurj
    have hsub : Subsingleton (↥K ⧸ D) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (↥K ⧸ D) hQs
    rw [eq_top_iff]
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  · exact h

theorem commutator_le_pCoreOf_828 {K X D : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hperf : ⁅K, K⁆ = K)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hDK : D ≤ K) (hDn : (D.subgroupOf K).Normal)
    (hDne : D ≠ K) (hKXD : ⁅K, X⁆ ≤ D) : ⁅K, X⁆ ≤ pCoreOf 2 K := by
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K
  have hDne' : D.subgroupOf K ≠ ⊤ := fun h => hDne (le_antisymm hDK
    (fun x hx => Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥K))))
  have hZ := map_le_center_828 hq hperf hDn hDne'
  rw [Subgroup.commutator_le]
  intro k hk x hx
  have hxk : ∀ l ∈ K, x * l * x⁻¹ ∈ K := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (hXK hx) l).mp hl
  have hcomm : ∀ l : ↥K, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ D := fun l =>
    hKXD (Subgroup.commutator_mem_commutator l.2 hx)
  let c : ↥K → Q := fun l => QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x * l * x⁻¹, hxk l l.2⟩ : ↥K) *
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K) l)⁻¹
  have hc : ∀ l : ↥K, c l ∈ Subgroup.center Q := by
    intro l
    have hmem : (⟨x * l * x⁻¹ * (l : G)⁻¹, K.mul_mem (hxk l l.2) (K.inv_mem l.2)⟩ : ↥K) ∈
        D.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      have h1 := D.inv_mem (hcomm l)
      have e : ((l : G) * x * (l : G)⁻¹ * x⁻¹)⁻¹ = x * l * x⁻¹ * (l : G)⁻¹ := by group
      rw [e] at h1
      exact h1
    have := hZ ⟨_, hmem, rfl⟩
    convert this using 1
    have e : (⟨x * l * x⁻¹ * (l : G)⁻¹, K.mul_mem (hxk l l.2) (K.inv_mem l.2)⟩ : ↥K) =
        ⟨x * l * x⁻¹, hxk l l.2⟩ * l⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv]
  have hcmul : ∀ a b : ↥K, c (a * b) = c a * c b := by
    intro a b
    have e : (⟨x * (a * b : ↥K) * x⁻¹, hxk _ (a * b).2⟩ : ↥K) =
        ⟨x * a * x⁻¹, hxk a a.2⟩ * ⟨x * b * x⁻¹, hxk b b.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have hcb := Subgroup.mem_center_iff.mp (hc b)
    simp only [c, e, map_mul, mul_inv_rev]
    have := hcb (QuotientGroup.mk' (CFSG.pCore 2 ↥K) a)⁻¹
    calc _ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x * a * x⁻¹, hxk a a.2⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x * b * x⁻¹, hxk b b.2⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥K) b)⁻¹) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K) a)⁻¹ := by group
      _ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x * a * x⁻¹, hxk a a.2⟩ *
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥K) a)⁻¹ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x * b * x⁻¹, hxk b b.2⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥K) b)⁻¹)) := by
          rw [mul_assoc, this]
      _ = _ := by group
  let cHom : ↥K →* ↥(Subgroup.center Q) :=
    { toFun := fun l => ⟨c l, hc l⟩
      map_one' := by
        apply Subtype.ext
        have e1 : (⟨x * ((1 : ↥K) : G) * x⁻¹, hxk 1 (1 : ↥K).2⟩ : ↥K) = 1 :=
          Subtype.ext (by simp)
        show c 1 = 1
        simp only [c, e1, map_one, inv_one, mul_one]
      map_mul' := fun a b => Subtype.ext (hcmul a b) }
  have hker : commutator ↥K ≤ cHom.ker := Abelianization.commutator_subset_ker cHom
  have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hk1 : c ⟨k, hk⟩ = 1 := by
    have h1 : (⟨k, hk⟩ : ↥K) ∈ cHom.ker := hker (Group.IsPerfect.mem_commutator)
    rw [MonoidHom.mem_ker] at h1
    exact congrArg Subtype.val h1
  simp only [c, mul_inv_eq_one] at hk1
  have h2 : (⟨x * k * x⁻¹, hxk k hk⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact mul_inv_eq_one.mpr hk1
  have h3 : (⁅k, x⁆ : G) = ((⟨x * k * x⁻¹, hxk k hk⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K)⁻¹ := by
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, commutatorElement_def]
    group
  rw [h3]
  have h4 : ((⟨x * k * x⁻¹, hxk k hk⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ ∈ CFSG.Open.pCore 2 ↥K := by
    exact Subgroup.inv_mem _ h2
  exact ⟨_, h4, rfl⟩

omit [Finite G] in
theorem eq_of_le_sup_828 {B K N T : Subgroup G} (hB : B ∈ cComp (B ⊔ T)) (hK : K ∈ cComp N)
    (hBK : B ≤ K) (hKBT : K ≤ B ⊔ T) : K = B := by
  have hBsub : IsSubnormal B K := A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hB) hBK hKBT
  have hBN : IsSubnormal B N := A3.subnormal_trans hBsub (subnormal_of_mem_cComp hK)
  by_contra hne
  exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hBK (Ne.symm hne))
    (ne_bot_of_mem_cComp hB) (perfect_of_mem_cComp hB) hBN

theorem le_sup_pCoreOf_828 {K B C : Subgroup G} (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hperf : ⁅K, K⁆ = K) (hBK : B ≤ K) (hCK : C ≤ K) (hCn : (C.subgroupOf K).Normal)
    (hCne : C ≠ K) (hKBC : ∀ k ∈ K, ∃ b ∈ B, b⁻¹ * k ∈ C) : K ≤ B ⊔ pCoreOf 2 K := by
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K
  have hCne' : C.subgroupOf K ≠ ⊤ := fun h => hCne (le_antisymm hCK
    (fun x hx => Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥K))))
  have hZ := map_le_center_828 hq hperf hCn hCne'
  set B' := (B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hall : ∀ q : Q, ∃ b ∈ B', ∃ z ∈ Subgroup.center Q, q = b * z := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
    obtain ⟨b, hb, hbk⟩ := hKBC k k.2
    refine ⟨QuotientGroup.mk' _ ⟨b, hBK hb⟩, ⟨⟨b, hBK hb⟩, hb, rfl⟩,
      QuotientGroup.mk' _ ⟨b⁻¹ * k, K.mul_mem (K.inv_mem (hBK hb)) k.2⟩,
      hZ ⟨⟨b⁻¹ * k, K.mul_mem (K.inv_mem (hBK hb)) k.2⟩, hbk, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp)
  have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hQp : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hcomm : commutator Q ≤ B' := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    obtain ⟨bx, hbx, zx, hzx, rfl⟩ := hall x
    obtain ⟨by', hby, zy, hzy, rfl⟩ := hall y
    have e : ⁅bx * zx, by' * zy⁆ = ⁅bx, by'⁆ := by
      have h1 := Subgroup.mem_center_iff.mp hzx
      have h2 := Subgroup.mem_center_iff.mp hzy
      simp only [commutatorElement_def, mul_inv_rev]
      calc bx * zx * (by' * zy) * (zx⁻¹ * bx⁻¹) * (zy⁻¹ * by'⁻¹)
          = bx * (zx * by') * zy * zx⁻¹ * bx⁻¹ * zy⁻¹ * by'⁻¹ := by group
        _ = bx * (by' * zx) * zy * zx⁻¹ * bx⁻¹ * zy⁻¹ * by'⁻¹ := by rw [h1 by']
        _ = bx * by' * (zx * zy) * zx⁻¹ * bx⁻¹ * zy⁻¹ * by'⁻¹ := by group
        _ = bx * by' * (zy * zx) * zx⁻¹ * bx⁻¹ * zy⁻¹ * by'⁻¹ := by rw [h1 zy]
        _ = bx * by' * (zy * bx⁻¹) * zy⁻¹ * by'⁻¹ := by group
        _ = bx * by' * (bx⁻¹ * zy) * zy⁻¹ * by'⁻¹ := by rw [h2 bx⁻¹]
        _ = bx * by' * bx⁻¹ * by'⁻¹ := by group
    rw [e, commutatorElement_def]
    exact B'.mul_mem (B'.mul_mem (B'.mul_mem hbx hby) (B'.inv_mem hbx)) (B'.inv_mem hby)
  have hB'top : B' = ⊤ := eq_top_iff.mpr (fun q _ => hcomm (Group.IsPerfect.mem_commutator))
  intro k hk
  have hq' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨k, hk⟩ : ↥K) ∈ B' := by
    rw [hB'top]; exact Subgroup.mem_top _
  obtain ⟨b, hb, hbk⟩ := hq'
  have hm : b⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (QuotientGroup.mk b : Q) = QuotientGroup.mk (⟨k, hk⟩ : ↥K) := hbk
    rw [this, inv_mul_cancel]
  have e : k = (b : G) * ((b⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
  rw [e]
  refine Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb) ⟨b⁻¹ * ⟨k, hk⟩, ?_, rfl⟩
  exact hm

theorem exists_mulAut_ne_one_828 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (h4 : 4 ≤ Nat.card W) : ∃ φ : MulAut W, φ ≠ 1 := by
  classical
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul, pow_two]
      exact hW _
    exact toMul_eq_one.1 h3
  have : Finite (Additive W) := inferInstanceAs (Finite W)
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  set d := Module.finrank (ZMod 2) (Additive W)
  have hcard : Nat.card W = 2 ^ d := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h1
    exact h1
  have hd : 2 ≤ d := by
    by_contra h
    push Not at h
    interval_cases d <;> simp [hcard] at h4
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) rfl
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let e : Additive W ≃ₗ[ZMod 2] Additive W := b.equiv b (Equiv.swap i0 i1)
  refine ⟨MulEquiv.toAdditive.symm e.toAddEquiv, fun h => ?_⟩
  have h1 : e (b i0) = b i1 := by
    simp [e, Module.Basis.equiv_apply, Equiv.swap_apply_left]
  have h2 : e (b i0) = b i0 := by
    have := congrArg (fun φ : MulAut W => Additive.ofMul (φ (Additive.toMul (b i0)))) h
    simpa using this
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  exact hne (b.injective (h1.symm.trans h2).symm)

theorem ne_bot_of_alternatingNatural_828 {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {n : ℕ} (hn : n = 5 ∨ n = 6) (hH : AlternatingNatural H ⊤ ⊥ n) : H ≠ ⊥ := by
  intro hbot
  obtain ⟨π, -, -, -, -, -, hsec, -, β, hβs, -, hβe⟩ := hH
  have key : ∀ (γ' : Equiv.Perm (Fin n)) (hγ' : γ' ∈ alternatingGroup (Fin n)) (m : G6.PermMod n)
      (hm : m ∈ G6.coreMod n), m⁻¹ * G6.permAct n γ' m ∈ Subgroup.zpowers (G6.allOnes n) := by
    intro γ' hγ' m hm
    let γ : ↥(alternatingGroup (Fin n)) := ⟨γ', hγ'⟩
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have hπ : ((π γ : ↥H) : MulAut W) = 1 :=
      Subgroup.mem_bot.mp ((le_of_eq hbot) (π γ).2)
    have hu' : ((π γ : ↥H) : MulAut W) (u : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
    have h1 := hβe γ u ⟨m, hm⟩ hu' (hsec γ m hm) hu
    have h2 : (⟨((π γ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥(⊤ : Subgroup W)) = u := by
      apply Subtype.ext
      rw [hπ]
      rfl
    rw [h2, hu] at h1
    have h3 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h3
    exact h3.1
  have hzp : ∀ (x : G6.PermMod n), x ∈ Subgroup.zpowers (G6.allOnes n) →
      x = 1 ∨ x = G6.allOnes n := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have ha2 : G6.allOnes n * G6.allOnes n = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      show (1 : ZMod 2) + 1 = 0
      decide
    have hinv : (G6.allOnes n)⁻¹ = G6.allOnes n := inv_eq_of_mul_eq_one_right ha2
    induction k using Int.induction_on with
    | zero => left; simp
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _) with h | h
      · right; rw [h, one_mul]
      · left; rw [h, ha2]
    | pred i ih =>
      rw [zpow_sub_one]
      rcases ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _) with h | h
      · right; rw [h, one_mul]; exact hinv
      · left; rw [h]; exact mul_inv_cancel _
  rcases hn with rfl | rfl
  · have hγ : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    have hm : (Multiplicative.ofAdd ![1, 0, 0, 1, 0] : G6.PermMod 5) ∈ G6.coreMod 5 := by
      show ∑ i, (![1, 0, 0, 1, 0] : Fin 5 → ZMod 2) i = 0
      decide
    rcases hzp _ (key _ hγ _ hm) with h | h
    · revert h
      decide
    · revert h
      decide
  · have hγ : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    have hm : (Multiplicative.ofAdd ![1, 0, 0, 1, 0, 0] : G6.PermMod 6) ∈ G6.coreMod 6 := by
      show ∑ i, (![1, 0, 0, 1, 0, 0] : Fin 6 → ZMod 2) i = 0
      decide
    rcases hzp _ (key _ hγ _ hm) with h | h
    · revert h
      decide
    · revert h
      decide

end L828D

end CFSG.Quasithin.H13
