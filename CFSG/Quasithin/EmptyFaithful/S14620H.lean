module

public import CFSG.Quasithin.EmptyFaithful.S14620G
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4IsPSL
import CFSG.Quasithin.EmptyFaithful.S14620HK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.C2Push CFSG.LieType.BorelTits
  CFSG.GroupTheory.AutAlternating

section Finite8

private abbrev P8 : Type := Equiv.Perm (Fin 8)

private def f8 : Subgroup P8 where
  carrier := {g | ∀ i j : Fin 8, (i.val / 4 = j.val / 4 ↔ (g i).val / 4 = (g j).val / 4)}
  mul_mem' := by
    intro a b ha hb i j
    exact (hb i j).trans (ha (b i) (b j))
  one_mem' := fun i j => Iff.rfl
  inv_mem' := by
    intro a ha i j
    have := ha (a⁻¹ i) (a⁻¹ j)
    simpa using this.symm

private instance : DecidablePred (· ∈ f8) := fun g =>
  inferInstanceAs (Decidable (∀ i j : Fin 8, (i.val / 4 = j.val / 4 ↔ (g i).val / 4 = (g j).val / 4)))

private theorem card_f8 : Fintype.card f8 = 1152 := by
  rw [← S14620HK.card_wr8, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun g => Iff.rfl)

private theorem card_perm8 : Nat.card P8 = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

private theorem isSolvable_f8 : Group.IsSolvable ↥f8 := by
  have : Finite ↥f8 := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (by rw [Nat.card_eq_fintype_card, card_f8]; norm_num [Nat.primeFactors])

private theorem isSolvable_of_le'' {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h) (Subgroup.inclusion_injective h)

private theorem exists_sylow_f8 : ∃ P₀ : Subgroup P8, P₀ ≤ f8 ∧ IsSylowTwoOf P₀ ⊤ := by
  obtain ⟨P₀, hP₀, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup P8) ≤ f8)
    (IsPGroup.of_card (p := 2) (n := 0) (by rw [Subgroup.card_bot]; rfl))
  refine ⟨P₀, hP₀.1, le_top, hP₀.2.1, ?_⟩
  have h1 : (P₀.subgroupOf ⊤).index = P₀.relIndex f8 * f8.relIndex ⊤ := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hP₀.1 le_top]
    rfl
  rw [h1, Subgroup.relIndex_top_right]
  have h2 : Nat.card f8 * f8.index = Nat.card P8 := Subgroup.card_mul_index f8
  rw [Nat.card_eq_fintype_card, card_f8, card_perm8] at h2
  have h3 : f8.index = 35 := by omega
  rw [h3]
  intro hdvd
  have hd : ¬ 2 ∣ P₀.relIndex f8 := hP₀.2.2
  have := (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd
  rcases this with h | h
  · exact hd h
  · omega

private def a8 : P8 := Equiv.swap 0 1 * Equiv.swap 1 2
private def b8 : P8 := Equiv.swap 4 5 * Equiv.swap 5 6

private theorem a8_pow : a8 ^ 3 = 1 := by decide +kernel
private theorem b8_pow : b8 ^ 3 = 1 := by decide +kernel
private theorem a8_ne : a8 ≠ 1 := by decide +kernel
private theorem b8_ne : b8 ≠ 1 := by decide +kernel
private theorem a8_comm : a8 * b8 = b8 * a8 := by decide +kernel
private theorem a8_even : a8 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
private theorem b8_even : b8 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
private theorem a8_mem_f8 : a8 ∈ f8 := by decide +kernel
private theorem b8_mem_f8 : b8 ∈ f8 := by decide +kernel

private theorem orderOf_a8 : orderOf a8 = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime a8_pow a8_ne
private theorem orderOf_b8 : orderOf b8 = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime b8_pow b8_ne

private theorem a8_zero : a8 0 ≠ 0 := by decide +kernel
private theorem a8sq_zero : (a8 ^ 2) 0 ≠ 0 := by decide +kernel
private theorem b8_zero : b8 0 = 0 := by decide +kernel
private theorem b8sq_zero : (b8 ^ 2) 0 = 0 := by decide +kernel

private theorem zpowers_inf_eq_bot : Subgroup.zpowers a8 ⊓ Subgroup.zpowers b8 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  rw [Subgroup.mem_bot]
  have hA := mem_zpowers_of_orderOf_eq_three orderOf_a8 hxA
  have hB := mem_zpowers_of_orderOf_eq_three orderOf_b8 hxB
  have hx0 : x 0 = 0 := by
    rcases hB with h | h | h
    · simp [h]
    · rw [h]; exact b8_zero
    · rw [h]; exact b8sq_zero
  rcases hA with h | h | h
  · exact h
  · exact absurd (h ▸ hx0) a8_zero
  · exact absurd (h ▸ hx0) a8sq_zero

private theorem two_le_pRank_E8 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a8 ⊔ Subgroup.zpowers b8) := by
  have hc : ∀ x ∈ Subgroup.zpowers a8, ∀ y ∈ Subgroup.zpowers b8, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a8 b8 from a8_comm) i j)).eq
  have h0 := pRank_add_le_pRank_sup Nat.prime_three hc zpowers_inf_eq_bot
  have h3 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a8) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one a8_pow) (k := 1) ?_
    rw [Nat.card_zpowers, orderOf_a8]; simp
  have h4 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers b8) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one b8_pow) (k := 1) ?_
    rw [Nat.card_zpowers, orderOf_b8]; simp
  omega

private theorem pRank_conjSub_eq (g : P8) (E : Subgroup P8) :
    CFSG.Open.pRank 3 (conjSub g E) = CFSG.Open.pRank 3 E := by
  have e : ↥E ≃* ↥(conjSub g E) := MulEquiv.subgroupMap (MulAut.conj g) E
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  rw [pRank_top_subtype, pRank_top_subtype] at h1
  exact h1.symm

private theorem alt8_mem_normalizer (x : P8) :
    x ∈ Subgroup.normalizer ((alternatingGroup (Fin 8) : Subgroup P8) : Set P8) :=
  (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (alternatingGroup (Fin 8)).Normal)) ▸
    Subgroup.mem_top x

private theorem alt8_conjSub (g : P8) :
    conjSub g (alternatingGroup (Fin 8)) = alternatingGroup (Fin 8) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (alt8_mem_normalizer g)

private theorem exists_normalized_overgroup_perm8 {T'' : Subgroup P8}
    (hT2 : IsPGroup 2 ↥T'') :
    ∃ P : Subgroup P8, P ≤ alternatingGroup (Fin 8) ∧ T'' ≤ Subgroup.normalizer (P : Set P8) ∧
      Group.IsSolvable ↥P ∧ 2 ≤ CFSG.Open.pRank 3 P := by
  obtain ⟨P₀, hP₀f, hP₀⟩ := exists_sylow_f8
  obtain ⟨S, hS, hTS⟩ := A4.exists_isSylowTwoOf_ge (le_top : T'' ≤ ⊤) hT2
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hP₀ hS
  have hTc : T'' ≤ conjSub g f8 := fun x hx => mem_conjSub.mpr (hP₀f ((hg x).mp (hTS hx)))
  refine ⟨conjSub g f8 ⊓ alternatingGroup (Fin 8), inf_le_right, ?_,
    isSolvable_of_le'' inf_le_left (isSolvable_conjSub g f8 isSolvable_f8), ?_⟩
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hTc hx), alt8_mem_normalizer x⟩
  · have hE : Subgroup.zpowers a8 ⊔ Subgroup.zpowers b8 ≤ f8 ⊓ alternatingGroup (Fin 8) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact ⟨a8_mem_f8, a8_even⟩
      · rw [Subgroup.zpowers_le]; exact ⟨b8_mem_f8, b8_even⟩
    have hE' : conjSub g (Subgroup.zpowers a8 ⊔ Subgroup.zpowers b8) ≤
        conjSub g f8 ⊓ alternatingGroup (Fin 8) := by
      have := conjSub_mono g hE
      rwa [conjSub_inf, alt8_conjSub] at this
    have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hE'
    rw [pRank_conjSub_eq] at h1
    exact two_le_pRank_E8.trans h1

end Finite8

section Embed8

private theorem exists_injective_perm_alt {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) {Y : Type*} [Group Y]
    {Kh : Subgroup Y} [Kh.Normal] (e : ↥Kh ≃* alternatingGroup (Fin n))
    (hC : ∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1) :
    ∃ ψ : Y →* Equiv.Perm (Fin n), Function.Injective ψ ∧ alternatingGroup (Fin n) ≤ ψ.range ∧
      ∀ k : ↥Kh, ψ k = ((e k : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  let φ : Y →* MulAut ↥Kh := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine hC x fun k hk => ?_
    have h1 : φ x = 1 := hx
    have h2 := congrArg (fun f : MulAut ↥Kh => (f ⟨k, hk⟩ : ↥Kh).1) h1
    simp [φ, MulAut.conjNormal_apply] at h2
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = k * x := by rw [h2]
  let c : Equiv.Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal
  have hc : Function.Bijective c := aut_alternatingGroup_bijective_conj n hn hn6
  let eAut : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective c hc
  let ψ : Y →* Equiv.Perm (Fin n) :=
    eAut.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp φ)
  have hψk : ∀ k : ↥Kh, ψ k = ((e k : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
    intro k
    show eAut.symm ((MulAut.congr e) (φ (k : Y))) = _
    rw [MulEquiv.symm_apply_eq]
    refine MulEquiv.ext fun b => ?_
    have hk : (MulAut.conjNormal (k : Y)) (e.symm b) = k * e.symm b * k⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    show e ((MulAut.conjNormal (k : Y)) (e.symm b)) = (c (e k : Equiv.Perm (Fin n))) b
    rw [hk, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [c, MulAut.conjNormal_apply]
  refine ⟨ψ, ?_, ?_, hψk⟩
  · intro x y hxy
    apply hφ
    have := eAut.symm.injective hxy
    exact (MulAut.congr e).injective this
  · intro σ hσ
    refine ⟨(e.symm ⟨σ, hσ⟩ : Kh), ?_⟩
    have := hψk (e.symm ⟨σ, hσ⟩)
    simpa using this

end Embed8

section L4

private theorem pRank_map_injective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (E : Subgroup A) :
    CFSG.Open.pRank 3 (E.map f) = CFSG.Open.pRank 3 E := by
  have e : ↥E ≃* ↥(E.map f) := E.equivMapOfInjective f hf
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  rw [pRank_top_subtype, pRank_top_subtype] at h1
  exact h1.symm

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a in
private theorem nonempty_mulEquiv_alt8_of_isPSL {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) :=
  CFSG.Quasithin.J4L4.alt8_of_isPSL h

theorem l4_core {Y : Type} [Group Y] [Finite Y] (Kh T' : Subgroup Y) [Kh.Normal]
    (hP : IsPSL 4 2 1 ↥Kh) (hC : ∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1)
    (hT : IsPGroup 2 ↥T') :
    ∃ P : Subgroup Y, P ≤ Kh ∧ T' ≤ Subgroup.normalizer (P : Set Y) ∧ Group.IsSolvable ↥P ∧
      2 ≤ CFSG.Open.pRank 3 P := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alt8_of_isPSL hP
  obtain ⟨ψ, hψ, hA, hψk⟩ := exists_injective_perm_alt (n := 8) (by norm_num) (by norm_num) e hC
  obtain ⟨P', hP'A, hTN, hs, hr⟩ := exists_normalized_overgroup_perm8 (T'' := T'.map ψ) (hT.map ψ)
  have hP'r : P' ≤ ψ.range := hP'A.trans hA
  have hmap : (P'.comap ψ).map ψ = P' := Subgroup.map_comap_eq_self hP'r
  refine ⟨P'.comap ψ, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hyA : ψ y ∈ alternatingGroup (Fin 8) := hP'A hy
    let k : ↥Kh := e.symm ⟨ψ y, hyA⟩
    have hk : ψ (k : Y) = ψ y := by
      have := hψk k
      rw [this]
      simp [k]
    have : (k : Y) = y := hψ hk
    rw [← this]
    exact k.2
  · intro s hs
    have h1 : ψ s ∈ Subgroup.normalizer (P' : Set (Equiv.Perm (Fin 8))) := hTN ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h1 (ψ x)
  · exact Group.isSolvable_of_isSolvable_injective (f := ψ.subgroupComap P') fun x y hxy =>
      Subtype.ext (hψ (congrArg Subtype.val hxy))
  · rw [← pRank_map_injective ψ hψ, hmap]
    exact hr

end L4


section Core

@[expose] def L5Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kh T' : Subgroup Y), Kh.Normal → IsPSL 5 2 1 ↥Kh →
    (∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1) → IsPGroup 2 ↥T' →
    ∃ P : Subgroup Y, P ≤ Kh ∧ T' ≤ Subgroup.normalizer (P : Set Y) ∧ Group.IsSolvable ↥P ∧
      2 ≤ CFSG.Open.pRank 3 P

theorem l45Core_of_l5Core (h5 : L5Core) : L45Core := by
  intro Y _ _ Kh T' hKh hP hC hT
  rcases hP with h4 | h5'
  · have := hKh
    exact l4_core Kh T' h4 hC hT
  · exact h5 Y Kh T' hKh h5' hC hT

theorem input14620L45_of_l5Core (h5 : L5Core) : Input14620L45 :=
  input14620L45_of_core (l45Core_of_l5Core h5)

end Core

end CFSG.Quasithin
