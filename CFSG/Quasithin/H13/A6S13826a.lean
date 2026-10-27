module

public import CFSG.Quasithin.Background.SmithB42Alt6Mod

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.S143 CFSG.Quasithin.B42Alt6
open scoped commutatorElement

namespace A6Md

variable {S : Type} [CommGroup S]

structure Ctx (G L : Subgroup (MulAut S)) : Prop where
  le : L ≤ G
  normal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L
  iso : Nonempty (↥L ≃* alternatingGroup (Fin 6))
  cent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1

namespace Ctx

variable {G L : Subgroup (MulAut S)} (C : Ctx G L)
include C

theorem simple : IsSimpleGroup ↥L := by
  obtain ⟨e⟩ := C.iso
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact e.isSimpleGroup

theorem center : Subgroup.center ↥L = ⊥ := by
  obtain ⟨e⟩ := C.iso
  have h4 : 4 ≤ Nat.card (Fin 6) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  have hc := alternatingGroup.center_eq_bot h4
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz k]
  rw [hc, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h1, map_one])

theorem nonab : ∃ a b : ↥L, a * b ≠ b * a := by
  have hc := C.center
  have := C.simple
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
  by_contra h
  push Not at h
  have hxc : x ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.2 fun g => h g x
  rw [hc] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

theorem perfect : Group.IsPerfect ↥L := by
  have := C.simple
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := C.nonab
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator ↥L :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

end Ctx

theorem card_le_index_pow [Finite S] {G L : Subgroup (MulAut S)} (C : Ctx G L)
    (hfix : fixV L = ⊥) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) :
    ∃ r m : ℕ, Nat.card B = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Nat.card S ≤ (fixV B).index ^ m := by
  classical
  obtain ⟨ι⟩ := C.iso
  have hLG := C.le
  set L' : Subgroup ↥G := L.subgroupOf G with hL'
  have hL'n : L'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := C.normal g g.2 n hn
    simpa using this⟩
  let eLL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hc' : Subgroup.center ↥L' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eLL z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k
      obtain ⟨k', rfl⟩ := eLL.surjective k
      rw [← map_mul, ← map_mul, hz k']
    rw [C.center, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact eLL.injective (by rw [h1, map_one])
  let eQ : (↥L' ⧸ Subgroup.center ↥L') ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hc').trans QuotientGroup.quotientBot).trans (eLL.trans ι)
  have : Group.IsPerfect ↥L := C.perfect
  have : Group.IsPerfect ↥L' :=
    Group.IsPerfect.ofSurjective (f := eLL.symm.toMonoidHom) eLL.symm.surjective
  have hker : ∀ h : ↥G, Setup.X3.outAct L' eQ h = 1 →
      h ∈ (Subgroup.center ↥L').map L'.subtype := by
    intro h hh
    have h1 := Setup.X3.mem_centralizer_of_outAct_eq_one L' eQ hh
    have h2 : (h : MulAut S) = 1 := by
      refine C.cent h h.2 fun l hl => ?_
      have h3 := Subgroup.mem_centralizer_iff.1 h1 ⟨l, hLG hl⟩ (Subgroup.mem_subgroupOf.2 hl)
      exact (congrArg Subtype.val h3).symm
    have : h = 1 := Subtype.ext h2
    rw [this]
    exact one_mem _
  have hinj : Function.Injective (Setup.X3.outAct L' eQ) := by
    rw [injective_iff_map_eq_one]
    intro h hh
    obtain ⟨z, hz, rfl⟩ := hker h hh
    have hz' : z ∈ Subgroup.center ↥L' := hz
    rw [hc', Subgroup.mem_bot] at hz'
    rw [hz', map_one]
  set A' : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (B.subgroupOf G).map (Setup.X3.outAct L' eQ) with hA'
  have hBc : Nat.card ↥(B.subgroupOf G) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv
  have hcardA' : Nat.card A' = Nat.card B := by
    rw [hA', Subgroup.card_map_of_injective hinj, hBc]
  have hA'1 : A' ≠ ⊥ := by
    intro h
    have h1 : Nat.card A' = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardA'] at h1
    exact hB1 (Subgroup.card_eq_one.1 h1)
  have hA'el : CFSG.IsElementaryAbelian 2 ↥A' := by
    refine { is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      apply Subtype.ext
      show Setup.X3.outAct L' eQ a * Setup.X3.outAct L' eQ b =
        Setup.X3.outAct L' eQ b * Setup.X3.outAct L' eQ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hB.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      apply Subtype.ext
      show Setup.X3.outAct L' eQ a ^ 2 = 1
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (hB.2 _ (Subgroup.mem_subgroupOf.1 ha))
      rw [this, map_one]
  obtain ⟨r, m, hcard, hr1, hr3, hmr, s, hgen⟩ :=
    Setup.X3Aut.a6ShortGeneration.2.2.2 A' hA'1 hA'el
  obtain ⟨l, hl⟩ := Setup.X3.L_le_closure_of_inner_generation L' eQ hker (B.subgroupOf G) s hgen
  refine ⟨r, m, by rw [← hcardA', hcard], hr1, hr3, hmr, ?_⟩
  let K : Fin m → Subgroup S := fun i =>
    fixV (B.map (MulAut.conj (((l i : ↥G) : MulAut S))).toMonoidHom)
  have hK : ⨅ i, K i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvK : ∀ i, v ∈ K i := fun i => (Subgroup.mem_iInf.1 hv) i
    let St : Subgroup ↥G := (MulAction.stabilizer (MulAut S) v).comap G.subtype
    have hcl : Subgroup.closure (⋃ i, (((B.subgroupOf G).map
        (MulAut.conj ((l i : ↥G))).toMonoidHom : Subgroup ↥G) : Set ↥G)) ≤ St := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨b, hb, rfl⟩ := hi
      have hmem : ((MulAut.conj ((l i : ↥G))).toMonoidHom b : MulAut S) ∈
          B.map (MulAut.conj (((l i : ↥G) : MulAut S))).toMonoidHom :=
        ⟨(b : MulAut S), Subgroup.mem_subgroupOf.1 hb, by simp⟩
      have := hvK i _ hmem
      show _ • v = v
      exact this
    have hvL : v ∈ fixV L := by
      intro x hx
      have h1 := hcl (hl (Subgroup.mem_subgroupOf.2 hx : (⟨x, hLG hx⟩ : ↥G) ∈ L'))
      exact h1
    rw [hfix] at hvL
    exact hvL
  have h1 := Subgroup.index_iInf_le K
  rw [hK, Subgroup.index_bot] at h1
  have h2 : ∀ i, (K i).index = (fixV B).index := fun i => B42A57.index_fixV_conj B _
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1

theorem card_le_of_index_le_sq [Finite S] {G L : Subgroup (MulAut S)} (C : Ctx G L)
    (hfix : fixV L = ⊥) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) (hle : (fixV B).index ≤ Nat.card B ^ 2) : Nat.card S ≤ 2 ^ 12 := by
  obtain ⟨r, m, hcard, -, -, hmr, hS⟩ := card_le_index_pow C hfix hBG hB1 hB
  rw [hcard] at hle
  calc Nat.card S ≤ (fixV B).index ^ m := hS
    _ ≤ ((2 ^ r) ^ 2) ^ m := Nat.pow_le_pow_left hle m
    _ = 2 ^ (2 * (m * r)) := by rw [← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_of_index_le [Finite S] {G L : Subgroup (MulAut S)} (C : Ctx G L)
    (hfix : fixV L = ⊥) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) (hle : (fixV B).index ≤ Nat.card B) : Nat.card S ≤ 2 ^ 6 := by
  obtain ⟨r, m, hcard, -, -, hmr, hS⟩ := card_le_index_pow C hfix hBG hB1 hB
  rw [hcard] at hle
  calc Nat.card S ≤ (fixV B).index ^ m := hS
    _ ≤ (2 ^ r) ^ m := Nat.pow_le_pow_left hle m
    _ = 2 ^ (m * r) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hmr

theorem exists_n6Model [Finite S] {L : Subgroup (MulAut S)} (hS : ∀ s : S, s * s = 1)
    (ι : ↥L ≃* alternatingGroup (Fin 6)) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hcard : Nat.card S < 2 ^ 16) : Nonempty (N6Model L) := by
  classical
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul, pow_two]
      exact hS _
    exact toMul_eq_one.1 h3
  let θ : S ≃* Multiplicative (Additive S) := (MulEquiv.multiplicativeAdditive S).symm
  let σ : S6 →* (Additive S ≃ₗ[ZMod 2] Additive S) :=
    (Setup.Layer.binPsi θ).toMonoidHom.comp (L.subtype.comp ι.symm.toMonoidHom)
  have hσ : ∀ γ w, σ γ w = Additive.ofMul ((ι.symm γ : MulAut S) (Additive.toMul w)) :=
    fun γ w => rfl
  have hsimple : Setup.X3.IsLSimple σ ⊤ ⊤ := by
    refine ⟨fun _ _ _ _ => trivial, ?_, fun U hU _ => ?_⟩
    · intro h
      obtain ⟨s, -, hs⟩ := IsConcreteLE.exists_of_lt hirr.1
      have h1 : Additive.ofMul s ∈ (⊤ : Submodule (ZMod 2) (Additive S)) := trivial
      rw [h, Submodule.mem_bot] at h1
      exact hs (Subgroup.mem_bot.2 (by simpa using h1))
    · let J : Subgroup S :=
        { carrier := {s | Additive.ofMul s ∈ U}
          one_mem' := U.zero_mem
          mul_mem' := fun ha hb => U.add_mem ha hb
          inv_mem' := fun ha => U.neg_mem ha }
      have hinv : XMod.IsInv ↥L J := by
        intro a j hj
        have h1 := hU (ι a) trivial (Additive.ofMul j) hj
        have h2 : σ (ι a) (Additive.ofMul j) = Additive.ofMul ((a : MulAut S) j) := by
          rw [hσ, MulEquiv.symm_apply_apply]
          rfl
        rw [h2] at h1
        exact h1
      rcases hirr.2 J hinv bot_le le_top with h | h
      · left
        rw [eq_bot_iff]
        intro w hw
        have h1 : Additive.toMul w ∈ J := hw
        rw [h, Subgroup.mem_bot] at h1
        rw [Submodule.mem_bot]
        exact h1
      · right
        rw [eq_top_iff]
        intro w _
        have h1 : Additive.toMul w ∈ J := by rw [h]; trivial
        exact h1
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_iso σ hsimple
  have hcardS : Nat.card S = 2 ^ (eNs.getD (i + 1) 0 - eNs.getD i 0) := by
    have h1 : Nat.card (Vec (eNs.getD (i + 1) 0 - eNs.getD i 0)) = Nat.card (Additive S) :=
      Nat.card_congr Ψ.toEquiv
    have h2 : Nat.card (Additive S) = Nat.card S := rfl
    rw [← h2, ← h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin _),
      Fintype.card_fin]
  have hone : ∀ b, (ι.symm (gen b) : MulAut S) ≠ 1 := by
    intro b h
    have h1 : ι.symm (gen b) = 1 := Subtype.ext h
    have h2 : gen b = 1 := by
      have := congrArg ι h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    cases b <;> exact absurd h2 (by decide)
  have htriv : (∀ b (s : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0)),
      lin _ (blkOf i b) s = s) → False := by
    intro hlin
    apply hone false
    apply MulEquiv.ext
    intro v
    obtain ⟨s, hs⟩ := Ψ.surjective (Additive.ofMul v)
    have h1 := hΨ false s
    rw [hlin, hs, hσ] at h1
    exact (congrArg Additive.toMul h1).symm
  interval_cases i
  · exact model_of_block blockOK_0 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_2 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_5 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact model_of_block blockOK_6 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_8 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_10 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exfalso
    have h16 : eNs.getD (11 + 1) 0 - eNs.getD 11 0 = 16 := by decide
    rw [hcardS, h16] at hcard
    exact lt_irrefl _ hcard

theorem exists_rank [Finite S] {G L : Subgroup (MulAut S)} (C : Ctx G L) (hfix : fixV L = ⊥)
    (hcard : Nat.card S = 16) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) :
    ∃ r i : ℕ, Nat.card B = 2 ^ r ∧ (fixV B).index = 2 ^ i ∧ 1 ≤ r ∧ r ≤ 3 ∧ 2 * r ≤ 3 * i := by
  obtain ⟨r, m, hr, hr1, hr3, hmr, hle⟩ := card_le_index_pow C hfix hBG hB1 hB
  have hdvd : (fixV B).index ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨r, i, hr, hi, hr1, hr3, ?_⟩
  rw [hcard, hi, ← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num] at hle
  have h1 : 4 ≤ i * m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have h2 : 4 * r ≤ i * m * r := Nat.mul_le_mul_right r h1
  have h3 : i * m * r ≤ i * 6 := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left i hmr
  omega

end A6Md

end CFSG.Quasithin.H13.A6
