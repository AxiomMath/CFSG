module

public import CFSG.Quasithin.H13.GoldschmidtC137L3Mod
public import CFSG.Quasithin.H13.GoldschmidtC137Concl
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPerfect_of_commutator_eq_gc {L : Subgroup G} (h : ⁅L, L⁆ = L) : Group.IsPerfect ↥L := by
  rw [Group.isPerfect_def]
  have e := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype
  have e2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [e2, h] at e
  rw [commutator_def]
  exact Subgroup.map_injective L.subtype_injective (e.trans e2.symm)

omit [Finite G] in
theorem subsingleton_of_perfect_of_isPGroup {H : Type} [Group H] [Finite H]
    (hp : Group.IsPerfect H) (h2 : IsPGroup 2 H) : Subsingleton H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have hnt : Nontrivial H := not_subsingleton_iff_nontrivial.1 hns
  have := hp
  exact Group.IsPerfect.not_isNilpotent H h2.isNilpotent

theorem autI_L_eq_top {X L W : Subgroup G} (hL : L ∈ cComp X)
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hXN : X ≤ normalizer (W : Set G)) (hWe : IsElemAbelian 2 W) (hWL : ⁅W, L⁆ = W)
    (hW8 : Nat.card W = 8) :
    autI hWe L = ⊤ ∧ L ⊓ centralizer (W : Set G) = pCoreOf 2 L := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLN : L ≤ normalizer (W : Set G) := hLX.trans hXN
  have hM8 : Nat.card (IntMod W hWe) = 8 := hW8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod W hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hA : Nat.card (MulAut (IntMod W hWe)) = 168 := card_mulAut φ
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlie
    exact (MulEquiv.isSimpleGroup_congr e).mpr HSType.isSimpleGroup_SL_three_two
  have hperf : Group.IsPerfect ↥L := isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp hL)
  set ρ : ↥L →* MulAut (IntMod W hWe) := convHom hWe L hLN with hρ
  have hrange : ρ.range = autI hWe L := range_convHom hWe L hLN
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h] at hW8
    simp at hW8
  have hD : L ⊓ centralizer (W : Set G) ≤ pCoreOf 2 L := by
    set D' : Subgroup ↥L := (L ⊓ centralizer (W : Set G)).subgroupOf L with hD'
    have hD'n : D'.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hD', Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
      exact C124.conj_mem_centralizer_of_le hLN g.2 hn.2
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    have hN1 : (D'.map π).Normal := Subgroup.Normal.map hD'n π (QuotientGroup.mk'_surjective _)
    have : (D'.map π).Normal := hN1
    rcases hsimp.eq_bot_or_eq_top_of_normal (D'.map π) with h | h
    · intro d hd
      have hd' : (⟨d, hd.1⟩ : ↥L) ∈ D' := Subgroup.mem_subgroupOf.2 hd
      have h1 : π ⟨d, hd.1⟩ ∈ D'.map π := ⟨_, hd', rfl⟩
      rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      rw [C124.pCoreOf_eq_map_pCore]
      exact ⟨_, h1, rfl⟩
    · exfalso
      have hp2 : IsPGroup 2 ↥ρ.range := by
        rintro ⟨_, l, rfl⟩
        obtain ⟨d, hd, hdl⟩ := (h ▸ Subgroup.mem_top (π l) : π l ∈ D'.map π)
        have hdl' : d⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdl
          exact hdl
        have hρd : ρ d = 1 := by
          have hd1 := Subgroup.mem_subgroupOf.1 hd
          exact (convI_eq_one_iff hWe ⟨d, hLN d.2⟩).2 hd1.2
        have hpc : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
        obtain ⟨j, hj⟩ := hpc ⟨_, hdl'⟩
        refine ⟨j, Subtype.ext ?_⟩
        have hj' : (d⁻¹ * l) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
        have h3 : ρ l = ρ (d⁻¹ * l) := by rw [map_mul, map_inv, hρd, inv_one, one_mul]
        show (ρ l) ^ 2 ^ j = 1
        rw [h3, ← map_pow, hj', map_one]
      have hperfK : Group.IsPerfect ↥ρ.range :=
        Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
      have hsub := subsingleton_of_perfect_of_isPGroup hperfK hp2
      have hLC : L ≤ centralizer (W : Set G) := by
        intro l hl
        have h1 : ρ ⟨l, hl⟩ = 1 := by
          have h2 : (⟨ρ ⟨l, hl⟩, ⟨_, rfl⟩⟩ : ↥ρ.range) = 1 := Subsingleton.elim _ _
          simpa using congrArg Subtype.val h2
        exact (convI_eq_one_iff hWe ⟨l, hLN hl⟩).1 h1
      have hcomm : ⁅W, L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hLC)
      exact hW1 (hWL.symm.trans hcomm)
  have hP : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) := by
    rw [C124.pCoreOf_eq_map_pCore]
    exact (Nat.card_congr ((CFSG.pCore 2 ↥L).equivMapOfInjective L.subtype
      L.subtype_injective).toEquiv).symm
  have hcardL : Nat.card ↥L = 168 * Nat.card (pCoreOf 2 L) := by
    rw [hP]
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
    rw [card_of_psl32 hlie] at this
    exact this
  have hKD := card_autI_mul_card_inf hWe hLN
  have hDle : Nat.card ↥(L ⊓ centralizer (W : Set G)) ≤ Nat.card (pCoreOf 2 L) :=
    Subgroup.card_le_of_le hD
  have hK168 : 168 ≤ Nat.card (autI hWe L) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (autI hWe L) * Nat.card ↥(L ⊓ centralizer (W : Set G)) <
        168 * Nat.card (pCoreOf 2 L) :=
      calc _ ≤ Nat.card (autI hWe L) * Nat.card (pCoreOf 2 L) := Nat.mul_le_mul_left _ hDle
        _ < 168 * Nat.card (pCoreOf 2 L) := Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos
    rw [hKD, hcardL] at h1
    exact lt_irrefl _ h1
  have hKle : Nat.card (autI hWe L) ≤ 168 := by
    rw [← hA]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hK : Nat.card (autI hWe L) = 168 := le_antisymm hKle hK168
  refine ⟨Subgroup.eq_top_of_card_eq _ (by rw [hK, hA]), ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hD ?_
  have h2 : 168 * Nat.card (pCoreOf 2 L) =
      168 * Nat.card ↥(L ⊓ centralizer (W : Set G)) := by
    rw [← hcardL, ← hKD, hK]
  have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 168) h2
  exact this.le

omit [Finite G] in
theorem isTwoReducedIn_of_autI_top {X L W : Subgroup G} (hLX : L ≤ X) (hWX : W ≤ X)
    (hXN : X ≤ normalizer (W : Set G)) (hWe : IsElemAbelian 2 W)
    (hsimp : IsSimpleGroup (MulAut (IntMod W hWe))) (hnp : ¬ IsPGroup 2 (MulAut (IntMod W hWe)))
    (htop : autI hWe L = ⊤) : IsTwoReducedIn X W := by
  refine ⟨hWX, hXN, hWe, fun D hDX hXD hD => ?_⟩
  have hDN : D ≤ normalizer (W : Set G) := hDX.trans hXN
  have hnormal : (autI hWe D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨d, hd, rfl⟩ := (mem_autI hWe).1 hn
    have hg : g ∈ autI hWe L := by rw [htop]; trivial
    obtain ⟨l, hl, rfl⟩ := (mem_autI hWe).1 hg
    refine (mem_autI hWe).2 ⟨l * d * l⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hlN : (l : G) ∈ normalizer (D : Set G) := hXD (hLX hl)
    have := (Subgroup.mem_normalizer_iff.1 hlN (d : G)).1 hd
    simpa using this
  rcases hsimp.eq_bot_or_eq_top_of_normal (autI hWe D) with h | h
  · exact (autI_eq_bot_iff hWe hDN).1 h
  · exfalso
    apply hnp
    intro a
    have ha : a ∈ autI hWe D := by rw [h]; trivial
    obtain ⟨d, hd, rfl⟩ := (mem_autI hWe).1 ha
    obtain ⟨k, hk⟩ := hD d hd
    refine ⟨k, ?_⟩
    show (convI hWe d) ^ 2 ^ k = 1
    rw [← map_pow]
    exact (convI_eq_one_iff hWe (d ^ 2 ^ k)).2 (by simpa using hk)

theorem l32_reduce {X L V : Subgroup G} (hL : L ∈ cComp X)
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) (hn : X ≤ normalizer (L : Set G))
    (hred : IsTwoReducedIn X V) (h8 : Nat.card ↥⁅V, L⁆ = 8) :
    ⁅V, L⁆ ≤ X ∧ X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) ∧
      IsElemAbelian 2 ⁅V, L⁆ ∧ ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ ∧ IsTwoReducedIn X ⁅V, L⁆ := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hVN : X ≤ normalizer (V : Set G) := hred.2.1
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hWV : ⁅V, L⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hVN)
  have hWX : ⁅V, L⁆ ≤ X := hWV.trans hred.1
  have hXW : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hVN hg) (hn hg)
  have hWe : IsElemAbelian 2 ⁅V, L⁆ := B2F.isElemAbelian_mono hWV hV
  have hWW : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self (perfect_of_mem_cComp hL) (hLX.trans hVN)
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have hLWN : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXW
  obtain ⟨htop, -⟩ := autI_L_eq_top hL hlie hXW hWe hWW h8
  have hM8 : Nat.card (IntMod ⁅V, L⁆ hWe) = 8 := h8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod ⁅V, L⁆ hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hnp : ¬ IsPGroup 2 (MulAut (IntMod ⁅V, L⁆ hWe)) := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [card_mulAut φ] at hk
    have h168 : ∀ j : ℕ, 2 ^ j ≠ 168 := by
      intro j hj
      have h1 : j < 8 := by
        by_contra hj8
        push Not at hj8
        have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj8
        omega
      interval_cases j <;> omega
    exact h168 k hk.symm
  exact ⟨hWX, hXW, hWe, hWW, isTwoReducedIn_of_autI_top hLX hWX hXW hWe
    (isSimpleGroup_mulAut φ) hnp htop⟩

omit [Finite G] in
theorem isQuasisimple_L32 {L : Subgroup G}
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlie
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr e).mpr HSType.isSimpleGroup_SL_three_two
  have hnp : ¬ (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := by
    rw [card_of_psl32 hlie]
    norm_num
  have hnc : ∃ a b : (↥L ⧸ CFSG.pCore 2 ↥L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      { (inferInstance : Group (↥L ⧸ CFSG.pCore 2 ↥L)) with mul_comm := h }
    exact hnp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect _)

end CFSG.Quasithin.H13.U3.GC137
