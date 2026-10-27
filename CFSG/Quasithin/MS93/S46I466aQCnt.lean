module

public import Mathlib.Tactic.Group
public import CFSG.Quasithin.MS93.S46I469Grp

public section

namespace CFSG.Quasithin.MS93.S46

open scoped commutatorElement

variable {𝔾 : Type*} [Group 𝔾]

@[expose] def radModSub (V 𝔷 : Subgroup 𝔾) (h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {y | y ∈ V ∧ ∀ w ∈ V, ⁅y, w⁆ ∈ 𝔷}
  one_mem' := ⟨V.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact 𝔷.one_mem⟩
  mul_mem' := fun {y y'} hy hy' => ⟨V.mul_mem hy.1 hy'.1, fun w hw => by
    have e : ⁅y * y', w⁆ = y * ⁅y', w⁆ * y⁻¹ * ⁅y, w⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact 𝔷.mul_mem ((Subgroup.mem_normalizer_iff.mp (h𝔷 hy.1) _).mp (hy'.2 w hw)) (hy.2 w hw)⟩
  inv_mem' := fun {y} hy => ⟨V.inv_mem hy.1, fun w hw => by
    have e : ⁅y⁻¹, w⁆ = y⁻¹ * ⁅y, w⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h𝔷 (V.inv_mem hy.1)) _).mp (𝔷.inv_mem (hy.2 w hw))⟩

@[expose] def commModRight (V 𝔷 : Subgroup 𝔾) (h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾)) (y : 𝔾) :
    Subgroup 𝔾 where
  carrier := {w | w ∈ V ∧ ⁅y, w⁆ ∈ 𝔷}
  one_mem' := ⟨V.one_mem, by rw [commutatorElement_one_right]; exact 𝔷.one_mem⟩
  mul_mem' := fun {w w'} hw hw' => ⟨V.mul_mem hw.1 hw'.1, by
    have e : ⁅y, w * w'⁆ = ⁅y, w⁆ * (w * ⁅y, w'⁆ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact 𝔷.mul_mem hw.2 ((Subgroup.mem_normalizer_iff.mp (h𝔷 hw.1) _).mp hw'.2)⟩
  inv_mem' := fun {w} hw => ⟨V.inv_mem hw.1, by
    have e : ⁅y, w⁻¹⁆ = w⁻¹ * ⁅y, w⁆⁻¹ * w⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h𝔷 (V.inv_mem hw.1)) _).mp (𝔷.inv_mem hw.2)⟩

@[expose] def commModLeft (V 𝔷 : Subgroup 𝔾) (h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾)) (b : 𝔾) :
    Subgroup 𝔾 where
  carrier := {y | y ∈ V ∧ ⁅y, b⁆ ∈ 𝔷}
  one_mem' := ⟨V.one_mem, by rw [commutatorElement_one_left]; exact 𝔷.one_mem⟩
  mul_mem' := fun {y y'} hy hy' => ⟨V.mul_mem hy.1 hy'.1, by
    have e : ⁅y * y', b⁆ = y * ⁅y', b⁆ * y⁻¹ * ⁅y, b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact 𝔷.mul_mem ((Subgroup.mem_normalizer_iff.mp (h𝔷 hy.1) _).mp hy'.2) hy.2⟩
  inv_mem' := fun {y} hy => ⟨V.inv_mem hy.1, by
    have e : ⁅y⁻¹, b⁆ = y⁻¹ * ⁅y, b⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h𝔷 (V.inv_mem hy.1)) _).mp (𝔷.inv_mem hy.2)⟩

theorem le_normalizer_radModSub {V 𝔷 : Subgroup 𝔾} (h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾)) :
    V ≤ Subgroup.normalizer (radModSub V 𝔷 h𝔷 : Set 𝔾) := by
  have key : ∀ v ∈ V, ∀ y ∈ radModSub V 𝔷 h𝔷, v * y * v⁻¹ ∈ radModSub V 𝔷 h𝔷 := by
    intro v hv y hy
    refine ⟨V.mul_mem (V.mul_mem hv hy.1) (V.inv_mem hv), fun w hw => ?_⟩
    have e : ⁅v * y * v⁻¹, w⁆ = v * ⁅y, v⁻¹ * w * v⁆ * v⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h𝔷 hv) _).mp
      (hy.2 _ (V.mul_mem (V.mul_mem (V.inv_mem hv) hw) hv))
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key v hv y, fun hy => ?_⟩
  have := key v⁻¹ (V.inv_mem hv) _ hy
  simpa [mul_assoc] using this

theorem relIndex_ne_zero_of_le_finite {V : Subgroup 𝔾} [Finite V] {H K : Subgroup 𝔾} (hK : K ≤ V) :
    H.relIndex K ≠ 0 := by
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hK)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

variable {V 𝔷 X : Subgroup 𝔾} (h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾))
  {ι : Type*} (W : ι → Subgroup 𝔾) (hW : ∀ i, W i ≤ V) (hgen : V = ⨆ i, W i)
  (P : ι → Subgroup 𝔾)
  (hKP : ∀ i j, ∀ a ∈ W i, ∀ b ∈ W j, ⁅a, b⁆ ∉ 𝔷 → P i = P j)

include hW hgen in
theorem mem_radModSub_of_forall {y : 𝔾} (hyV : y ∈ V) (hy : ∀ j, ∀ b ∈ W j, ⁅y, b⁆ ∈ 𝔷) :
    y ∈ radModSub V 𝔷 h𝔷 := by
  refine ⟨hyV, fun w hw => ?_⟩
  have hle : (⨆ i, W i) ≤ commModRight V 𝔷 h𝔷 y :=
    iSup_le fun j b hb => ⟨hW j hb, hy j b hb⟩
  exact (hle (hgen ▸ hw)).2

include h𝔷 hW hKP in
theorem commutator_mem_of_label_not_mem (𝒮 : Set (Subgroup 𝔾)) {j : ι} (hj : P j ∉ 𝒮)
    {y : 𝔾} (hy : y ∈ ⨆ i : {i // P i ∈ 𝒮}, W i) {b : 𝔾} (hb : b ∈ W j) : ⁅y, b⁆ ∈ 𝔷 := by
  have hle : (⨆ i : {i // P i ∈ 𝒮}, W i) ≤ commModLeft V 𝔷 h𝔷 b := by
    refine iSup_le fun i a ha => ⟨hW i ha, ?_⟩
    by_contra hab
    exact hj (hKP i j a ha b hb hab ▸ i.2)
  exact (hle hy).2

variable [Finite V] (hX𝔷 : X ≤ Subgroup.normalizer (𝔷 : Set 𝔾))
  (hperm : ∀ x ∈ X, ∀ i, ∃ j, (W i).map (MulAut.conj x).toMonoidHom = W j ∧
    P j = (P i).map (MulAut.conj x).toMonoidHom)

omit [Finite ↥V] in
include hW hgen hKP hX𝔷 hperm in
theorem inf_centralizer_le_radModSub (𝒪 : Set (Subgroup 𝔾))
    (hO : ∀ s ∈ 𝒪, ∃ x ∈ X, s.map (MulAut.conj x).toMonoidHom ∉ 𝒪) :
    (⨆ i : {i // P i ∈ 𝒪}, W i) ⊓ Subgroup.centralizer (X : Set 𝔾) ≤ radModSub V 𝔷 h𝔷 := by
  rintro y ⟨hyN, hyC⟩
  have hNV : (⨆ i : {i // P i ∈ 𝒪}, W i) ≤ V := iSup_le fun i => hW i
  refine mem_radModSub_of_forall h𝔷 W hW hgen (hNV hyN) fun j b hb => ?_
  by_cases hj : P j ∈ 𝒪
  · obtain ⟨x, hx, hxO⟩ := hO _ hj
    obtain ⟨j', hj'W, hj'P⟩ := hperm x hx j
    have hb' : x * b * x⁻¹ ∈ W j' := by
      rw [← hj'W]
      exact ⟨b, hb, by simp⟩
    have h1 := commutator_mem_of_label_not_mem h𝔷 W hW P hKP 𝒪 (hj'P ▸ hxO) hyN hb'
    have hxy : x * y = y * x := Subgroup.mem_centralizer_iff.mp hyC x hx
    have e : ⁅y, b⁆ = x⁻¹ * ⁅y, x * b * x⁻¹⁆ * x⁻¹⁻¹ := by
      have hy' : y = x⁻¹ * y * x := by rw [mul_assoc, ← hxy, ← mul_assoc, inv_mul_cancel, one_mul]
      conv_lhs => rw [hy']
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hX𝔷 (X.inv_mem hx)) _).mp h1
  · exact commutator_mem_of_label_not_mem h𝔷 W hW P hKP 𝒪 hj hyN hb

include hW hgen hKP in
theorem two_pow_card_le_relIndex_radModSub (𝒪 : Finset (Subgroup 𝔾))
    (hO : ∀ s ∈ 𝒪, ∃ i, P i = s ∧ ¬ W i ≤ radModSub V 𝔷 h𝔷) :
    2 ^ 𝒪.card ≤ (radModSub V 𝔷 h𝔷).relIndex
      ((⨆ i : {i // P i ∈ (𝒪 : Set (Subgroup 𝔾))}, W i) ⊔ radModSub V 𝔷 h𝔷) := by
  classical
  have hRV : radModSub V 𝔷 h𝔷 ≤ V := fun y hy => hy.1
  induction 𝒪 using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, pow_zero]
    rw [Nat.one_le_iff_ne_zero]
    exact relIndex_ne_zero_of_le_finite (sup_le (iSup_le fun i => hW i) hRV)
  | insert s 𝒪 hs ih =>
    have hO' : ∀ t ∈ 𝒪, ∃ i, P i = t ∧ ¬ W i ≤ radModSub V 𝔷 h𝔷 :=
      fun t ht => hO t (Finset.mem_insert_of_mem ht)
    have h1 := ih hO'
    set Mo := (⨆ i : {i // P i ∈ (𝒪 : Set (Subgroup 𝔾))}, W i) ⊔ radModSub V 𝔷 h𝔷 with hMo
    set Mn := (⨆ i : {i // P i ∈ ((insert s 𝒪 : Finset (Subgroup 𝔾)) : Set (Subgroup 𝔾))},
      W i) ⊔ radModSub V 𝔷 h𝔷 with hMn
    have hMoMn : Mo ≤ Mn := by
      refine sup_le_sup_right (iSup_le fun i => ?_) _
      exact le_iSup_of_le ⟨i.1, by
        simp only [Finset.coe_insert, Set.mem_insert_iff]
        exact Or.inr i.2⟩ le_rfl
    have hMnV : Mn ≤ V := sup_le (iSup_le fun i => hW i) hRV
    obtain ⟨i₀, hi₀, hi₀R⟩ := hO s (Finset.mem_insert_self s 𝒪)
    obtain ⟨a, haW, haR⟩ := Set.not_subset.mp hi₀R
    have haV := hW i₀ haW
    obtain ⟨j, b, hb, hab⟩ : ∃ j, ∃ b ∈ W j, ⁅a, b⁆ ∉ 𝔷 := by
      by_contra hno
      push Not at hno
      exact haR (mem_radModSub_of_forall h𝔷 W hW hgen haV hno)
    have hPj : P j = s := (hKP i₀ j a haW b hb hab).symm.trans hi₀
    have haMn : a ∈ Mn := Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem ⟨i₀, by
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      exact Or.inl hi₀⟩ haW)
    have haMo : a ∉ Mo := by
      intro haMo
      have hle : Mo ≤ commModLeft V 𝔷 h𝔷 b := by
        refine sup_le (iSup_le fun i c hc => ⟨hW i hc, ?_⟩) fun y hy => ⟨hy.1, hy.2 b (hW j hb)⟩
        by_contra hcb
        have := hKP i j c hc b hb hcb
        exact hs (by rw [← hPj, ← this]; exact i.2)
      exact hab (hle haMo).2
    have hlt : Mo.relIndex Mn ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun hle => haMo (hle haMn)
    have hne0 : Mo.relIndex Mn ≠ 0 := relIndex_ne_zero_of_le_finite hMnV
    have hmul := Subgroup.relIndex_mul_relIndex (radModSub V 𝔷 h𝔷) Mo Mn le_sup_right hMoMn
    rw [Finset.card_insert_of_notMem hs, pow_succ, ← hmul]
    exact Nat.mul_le_mul h1 (by omega)

include hW hgen hKP hX𝔷 hperm in
theorem two_pow_card_le_relIndex_centralizer (𝒪 : Finset (Subgroup 𝔾))
    (hO1 : ∀ s ∈ 𝒪, ∃ i, P i = s ∧ ¬ W i ≤ radModSub V 𝔷 h𝔷)
    (hO2 : ∀ s ∈ 𝒪, ∃ x ∈ X, s.map (MulAut.conj x).toMonoidHom ∉ 𝒪) :
    2 ^ 𝒪.card ≤ (Subgroup.centralizer (X : Set 𝔾)).relIndex V := by
  set N := ⨆ i : {i // P i ∈ (𝒪 : Set (Subgroup 𝔾))}, W i with hN
  have hNV : N ≤ V := iSup_le fun i => hW i
  have : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNV)
  have h1 := two_pow_card_le_relIndex_radModSub h𝔷 W hW hgen P hKP 𝒪 hO1
  rw [← hN, relIndex_sup_of_le_normalizer (hNV.trans (le_normalizer_radModSub h𝔷))] at h1
  have h2 := inf_centralizer_le_radModSub h𝔷 W hW hgen P hKP hX𝔷 hperm (𝒪 : Set (Subgroup 𝔾))
    (fun s hs => hO2 s hs)
  rw [← hN] at h2
  have h3 : (radModSub V 𝔷 h𝔷).relIndex N ≤ (Subgroup.centralizer (X : Set 𝔾)).relIndex N := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (X : Set 𝔾)) N]
    exact Subgroup.relIndex_le_of_le_left (le_trans (le_of_eq (inf_comm _ _)) h2)
      (relIndex_ne_zero_of_le_finite hNV)
  have h4 : (Subgroup.centralizer (X : Set 𝔾)).relIndex N ≤
      (Subgroup.centralizer (X : Set 𝔾)).relIndex V := by
    exact Subgroup.relIndex_le_of_le_right hNV (relIndex_ne_zero_of_le_finite le_rfl)
  exact h1.trans (h3.trans h4)

end CFSG.Quasithin.MS93.S46
