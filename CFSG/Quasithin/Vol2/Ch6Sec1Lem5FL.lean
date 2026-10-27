module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FJ
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FK
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.Quasithin.EmptyFaithful.S152He9W
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Transport

variable {Γ : Type*} [Group Γ] {F : Subgroup Γ} {X : Type*} [Group X]

theorem mem_map_subgroupOf_ch615 (e : ↥F ≃* X) {A : Subgroup Γ} {g : Γ} (hg : g ∈ F) :
    e ⟨g, hg⟩ ∈ (A.subgroupOf F).map e.toMonoidHom ↔ g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

theorem isSylowTwoOf_map_ch615 (e : ↥F ≃* X) {S : Subgroup Γ} (hS : IsSylowTwoOf S F) :
    IsSylowTwoOf ((S.subgroupOf F).map e.toMonoidHom) ⊤ := by
  have := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS e.toMonoidHom
  rwa [MonoidHom.range_eq_top.mpr e.surjective] at this

theorem isSolvable_map_ch615 (e : ↥F ≃* X) {R : Subgroup Γ} (hRF : R ≤ F)
    (hR : Group.IsSolvable ↥R) : Group.IsSolvable ↥((R.subgroupOf F).map e.toMonoidHom) := by
  have := hR
  exact Group.isSolvable_of_surjective
    (f := ((Subgroup.subgroupOfEquivOfLe hRF).symm.trans
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)).toMonoidHom)
    (MulEquiv.surjective _)

theorem map_conj_ch615 (e : ↥F ≃* X) {g a : Γ} (hg : g ∈ F) (ha : a ∈ F) :
    e ⟨g, hg⟩ * e ⟨a, ha⟩ * (e ⟨g, hg⟩)⁻¹ =
      e ⟨g * a * g⁻¹, F.mul_mem (F.mul_mem hg ha) (F.inv_mem hg)⟩ := by
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl

theorem conj_mem_map_ch615 (e : ↥F ≃* X) {A : Subgroup Γ} {g : Γ} (hg : g ∈ F)
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    ∀ x ∈ (A.subgroupOf F).map e.toMonoidHom,
      e ⟨g, hg⟩ * x * (e ⟨g, hg⟩)⁻¹ ∈ (A.subgroupOf F).map e.toMonoidHom := by
  rintro _ ⟨⟨a, haF⟩, ha, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, map_conj_ch615, mem_map_subgroupOf_ch615]
  exact h a (Subgroup.mem_subgroupOf.mp ha)

theorem borelFacts_of_mulEquiv_ch615 [Finite Γ] (e : ↥F ≃* X) (hX : ¬ Group.IsSolvable X)
    (hB : ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ R₀ : Subgroup X, S₀ ≤ R₀ →
      Group.IsSolvable ↥R₀ → ∀ r ∈ R₀, ∀ s ∈ S₀, r * s * r⁻¹ ∈ S₀) :
    BorelFacts_ch615 F := by
  refine ⟨fun hs => hX (by
    have := hs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective), ?_⟩
  intro S hS R hSR hRF hR r hr s hs
  have hSF := hS.le
  have h := hB _ (isSylowTwoOf_map_ch615 e hS) _
    (Subgroup.map_mono (fun x hx => hSR hx)) (isSolvable_map_ch615 e hRF hR)
    (e ⟨r, hRF hr⟩) ((mem_map_subgroupOf_ch615 e _).mpr hr)
    (e ⟨s, hSF hs⟩) ((mem_map_subgroupOf_ch615 e _).mpr hs)
  rwa [map_conj_ch615, mem_map_subgroupOf_ch615] at h

theorem dLemmaFacts_of_mulEquiv_ch615 [Finite Γ] (e : ↥F ≃* X) (hX : ¬ Group.IsSolvable X)
    (hA : ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g)
    (hN : ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ g : X, (∀ s ∈ S₀, g * s * g⁻¹ ∈ S₀) →
      g ∈ S₀)
    (hO : ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ R₀ : Subgroup X, S₀ ≤ R₀ → R₀ ≠ S₀ →
      Group.IsSolvable ↥R₀ → ∀ g : X, (∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀) → g ∈ R₀) :
    DLemmaFacts_ch615 F := by
  refine ⟨fun hs => hX (by
    have := hs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective), ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨x, hx⟩ := hA (MulAut.congr e α) (by rw [MulEquiv.orderOf_eq]; exact hα)
    refine ⟨e.symm x, MulEquiv.ext fun y => ?_⟩
    have h1 : x * e y * x⁻¹ = e (α y) := by
      have := congrArg (fun φ : MulAut X => φ (e y)) hx
      simpa [MulAut.congr_apply] using this.symm
    apply e.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
  · intro S hS g hg hgS
    exact (mem_map_subgroupOf_ch615 e hg).mp
      (hN _ (isSylowTwoOf_map_ch615 e hS) _ (conj_mem_map_ch615 e hg hgS))
  · intro S hS R hSR hRF hRS hR g hg hgR
    have hSF := hS.le
    refine (mem_map_subgroupOf_ch615 e hg).mp
      (hO _ (isSylowTwoOf_map_ch615 e hS) _ (Subgroup.map_mono (fun x hx => hSR hx)) ?_
        (isSolvable_map_ch615 e hRF hR) _ (conj_mem_map_ch615 e hg hgR))
    intro heq
    apply hRS
    have h1 := Subgroup.map_injective e.injective heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hRF, inf_eq_left.mpr hSF] at h1
    exact h1

theorem center_of_mulEquiv_ch615 (e : ↥F ≃* X)
    (hZ : ∀ x : X, (∀ y : X, x * y = y * x) → x = 1) :
    ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1 := by
  intro g hg h
  have h1 := hZ (e ⟨g, hg⟩) fun y => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (h x hx))
  have h2 : (⟨g, hg⟩ : ↥F) = 1 := e.injective (h1.trans (map_one e).symm)
  exact congrArg Subtype.val h2

end Transport

section AllSylow

variable {X : Type*} [Group X] [Finite X]

theorem borel_of_sylow_ch615 {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (hB : ∀ R : Subgroup X, U₀ ≤ R → Group.IsSolvable ↥R → ∀ r ∈ R, ∀ u ∈ U₀,
      r * u * r⁻¹ ∈ U₀) :
    ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ R₀ : Subgroup X, S₀ ≤ R₀ →
      Group.IsSolvable ↥R₀ → ∀ r ∈ R₀, ∀ s ∈ S₀, r * s * r⁻¹ ∈ S₀ := by
  intro S₀ hS₀ R₀ hSR hR r hr s hs
  obtain ⟨x, -, rfl⟩ := hU₀.exists_conj hS₀
  set R' := R₀.map (MulAut.conj x⁻¹).toMonoidHom with hR'
  have hUR' : U₀ ≤ R' := fun u hu => ⟨x * u * x⁻¹, by
    simpa [MulAut.conj_apply] using hSR ⟨u, hu, rfl⟩, by
      simp [mul_assoc]⟩
  have hsR' : Group.IsSolvable ↥R' := by
    have := hR
    exact Group.isSolvable_of_surjective ((MulAut.conj x⁻¹).toMonoidHom.subgroupMap_surjective R₀)
  obtain ⟨u, hu, rfl⟩ := hs
  have hr' : x⁻¹ * r * x ∈ R' := ⟨r, hr, by simp⟩
  refine ⟨_, hB R' hUR' hsR' _ hr' u hu, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem selfNormalizing_of_sylow_ch615 {P : Subgroup X} (hP : IsSylowTwoOf P ⊤)
    (hN : ∀ g : X, (∀ s ∈ P, g * s * g⁻¹ ∈ P) → g ∈ P) :
    ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ g : X, (∀ s ∈ S₀, g * s * g⁻¹ ∈ S₀) → g ∈ S₀ := by
  intro S₀ hS₀ g hg
  obtain ⟨x, -, rfl⟩ := hP.exists_conj hS₀
  refine ⟨x⁻¹ * g * x, hN _ fun s hs => ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨t, ht, he⟩ := hg _ ⟨s, hs, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
  have : x⁻¹ * g * x * s * (x⁻¹ * g * x)⁻¹ = t := by
    calc x⁻¹ * g * x * s * (x⁻¹ * g * x)⁻¹ = x⁻¹ * (g * (x * s * x⁻¹) * g⁻¹) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [he]
      _ = t := by group
  rw [this]
  exact ht

end AllSylow

section Indec

variable {Γ : Type*} [Group Γ] {F : Subgroup Γ}

theorem isIndec_of_normal_simple_ch615 {N₀ : Subgroup Γ} (hN₀F : N₀ ≤ F)
    (hnN : ∀ g ∈ F, ∀ n ∈ N₀, g * n * g⁻¹ ∈ N₀) (hs : IsSimpleGroup ↥N₀)
    (hC : ∀ g ∈ F, (∀ n ∈ N₀, g * n = n * g) → g = 1) : IsIndec_ch615 F := by
  intro A B hA hB hnA hnB hAB hinf hsup
  have hAN : ((A ⊓ N₀).subgroupOf N₀).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hnA g (hN₀F g.2) n hn.1, hnN g (hN₀F g.2) n hn.2⟩⟩
  rcases hAN.eq_bot_or_eq_top with h | h
  · left
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hC a (hA ha) fun n hn => ?_
    have h1 : a * n * a⁻¹ * n⁻¹ ∈ A ⊓ N₀ := by
      refine ⟨?_, N₀.mul_mem (hnN a (hA ha) n hn) (N₀.inv_mem hn)⟩
      have : n * a⁻¹ * n⁻¹ ∈ A := hnA n (hN₀F hn) a⁻¹ (A.inv_mem ha)
      have e : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
      rw [e]
      exact A.mul_mem ha this
    have h2 : (⟨a * n * a⁻¹ * n⁻¹, h1.2⟩ : ↥N₀) ∈ (A ⊓ N₀).subgroupOf N₀ := h1
    rw [h, Subgroup.mem_bot] at h2
    have h3 : a * n * a⁻¹ * n⁻¹ = 1 := congrArg Subtype.val h2
    calc a * n = a * n * a⁻¹ * n⁻¹ * (n * a) := by group
      _ = n * a := by rw [h3, one_mul]
  · right
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine hC b (hB hb) fun n hn => ?_
    have hnA : n ∈ A := by
      have : (⟨n, hn⟩ : ↥N₀) ∈ (A ⊓ N₀).subgroupOf N₀ := by rw [h]; exact Subgroup.mem_top _
      exact this.1
    exact (hAB n hnA b hb).symm

theorem center_of_isSimpleGroup_ch615 (hs : IsSimpleGroup ↥F) (hns : ¬ Group.IsSolvable ↥F) :
    ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1 := by
  intro g hg h
  have hc : (⟨g, hg⟩ : ↥F) ∈ Subgroup.center ↥F :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥F) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · exfalso
    apply hns
    refine Group.isSolvable_of_comm fun a b => ?_
    have := ht ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

end Indec

section S5

open Equiv

@[expose] def d8_ch615 : Fin 8 → Perm (Fin 5) :=
  ![1, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2,
    swap 0 1 * swap 1 2 * swap 2 3, swap 0 3 * swap 3 2 * swap 2 1, swap 0 2, swap 1 3]

theorem d8_mul_ch615 : ∀ i j : Fin 8, ∃ k, d8_ch615 i * d8_ch615 j = d8_ch615 k := by
  decide +kernel

theorem d8_inv_ch615 : ∀ i : Fin 8, ∃ k, (d8_ch615 i)⁻¹ = d8_ch615 k := by
  decide +kernel

theorem d8_injective_ch615 : Function.Injective d8_ch615 := by
  decide +kernel

theorem d8_normalizer_ch615 : ∀ σ : Perm (Fin 5), (∃ i, σ * d8_ch615 4 * σ⁻¹ = d8_ch615 i) →
    (∃ i, σ * d8_ch615 6 * σ⁻¹ = d8_ch615 i) → ∃ j, σ = d8_ch615 j := by
  decide +kernel

theorem eq_one_of_commute_three_cycles_ch615 : ∀ σ : Perm (Fin 5),
    σ * (swap 0 1 * swap 1 2) = swap 0 1 * swap 1 2 * σ →
    σ * (swap 2 3 * swap 3 4) = swap 2 3 * swap 3 4 * σ → σ = 1 := by
  decide +kernel

theorem three_cycles_mem_ch615 : swap (0 : Fin 5) 1 * swap 1 2 ∈ alternatingGroup (Fin 5) ∧
    swap (2 : Fin 5) 3 * swap 3 4 ∈ alternatingGroup (Fin 5) := by
  constructor <;> decide

@[expose] def d8Sub_ch615 : Subgroup (Perm (Fin 5)) where
  carrier := {x | ∃ i, d8_ch615 i = x}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := d8_mul_ch615 i j
    exact ⟨k, hk.symm⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := d8_inv_ch615 i
    exact ⟨k, hk.symm⟩

theorem card_d8Sub_ch615 : Nat.card d8Sub_ch615 = 8 := by
  let e : Fin 8 ≃ d8Sub_ch615 := Equiv.ofBijective (fun i => ⟨d8_ch615 i, i, rfl⟩)
    ⟨fun i j h => d8_injective_ch615 (congrArg Subtype.val h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩
  rw [← Nat.card_congr e, Nat.card_fin]

theorem card_perm_five_ch615 : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alternating_five_ch615 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [card_perm_five_ch615] at this
  omega

theorem isSylowTwoOf_d8Sub_ch615 : IsSylowTwoOf d8Sub_ch615 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_d8Sub_ch615]; norm_num), fun h2 => ?_⟩
  change 2 ∣ d8Sub_ch615.relIndex ⊤ at h2
  rw [Subgroup.relIndex_top_right] at h2
  have h := d8Sub_ch615.card_mul_index
  rw [card_d8Sub_ch615, card_perm_five_ch615] at h
  omega

theorem mem_d8Sub_of_conj_mem_ch615 (g : Perm (Fin 5))
    (hg : ∀ s ∈ d8Sub_ch615, g * s * g⁻¹ ∈ d8Sub_ch615) : g ∈ d8Sub_ch615 := by
  obtain ⟨i, hi⟩ := hg _ ⟨4, rfl⟩
  obtain ⟨k, hk⟩ := hg _ ⟨6, rfl⟩
  obtain ⟨j, hj⟩ := d8_normalizer_ch615 g ⟨i, hi.symm⟩ ⟨k, hk.symm⟩
  exact ⟨j, hj.symm⟩

theorem eq_bot_or_le_of_normal_perm_five_ch615 {N : Subgroup (Perm (Fin 5))} (hN : N.Normal) :
    N = ⊥ ∨ alternatingGroup (Fin 5) ≤ N := by
  have hn : ((N ⊓ alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hN.conj_mem _ hn.1 g, (alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).mul_mem g.2 hn.2) ((alternatingGroup (Fin 5)).inv_mem g.2)⟩⟩
  rcases hn.eq_bot_or_eq_top with h | h
  · left
    have hinf : N ⊓ alternatingGroup (Fin 5) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx.2⟩ : ↥(alternatingGroup (Fin 5))) ∈
          (N ⊓ alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5)) := hx
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    rw [eq_bot_iff]
    intro n hn
    have hc : n ∈ Subgroup.center (Perm (Fin 5)) := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := CFSG.Quasithin.H13.NQRigid.sign_injective_of_inf_alternating hinf
        (hN.conj_mem n hn g) hn (by rw [map_mul, map_mul, map_inv, mul_right_comm,
          mul_inv_cancel, one_mul])
      calc g * n = g * n * g⁻¹ * g := by group
        _ = n * g := by rw [h1]
    rwa [CFSG.Quasithin.H13.NQRigid.perm_five_center_eq_bot] at hc
  · right
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 5))) ∈
        (N ⊓ alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5)) := by
      rw [h]
      exact Subgroup.mem_top _
    exact h1.1

theorem exists_eq_conj_perm_five_ch615 (α : MulAut (Perm (Fin 5))) :
    ∃ σ : Perm (Fin 5), α = MulAut.conj σ := by
  have hmap : (alternatingGroup (Fin 5)).map α.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [← alternatingGroup.commutator_perm_eq (by simp)]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance α
  have hmem : ∀ a ∈ alternatingGroup (Fin 5), α a ∈ alternatingGroup (Fin 5) := fun a ha => by
    rw [← hmap]
    exact ⟨a, ha, rfl⟩
  let α' : MulAut ↥(alternatingGroup (Fin 5)) :=
    (α.subgroupMap (alternatingGroup (Fin 5))).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨σ, hσ⟩ := CFSG.Semidihedral.Principal.CyclicAlternatingFive.conjNormal_surjective α'
  have hA : ∀ a (ha : a ∈ alternatingGroup (Fin 5)), α a = σ * a * σ⁻¹ := fun a ha => by
    have := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 5)) =>
      ((φ ⟨a, ha⟩ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hσ
    simp only [MulAut.conjNormal_apply] at this
    exact this.symm
  refine ⟨σ, MulEquiv.ext fun x => ?_⟩
  rw [MulAut.conj_apply]
  have key : ∀ b ∈ alternatingGroup (Fin 5),
      (σ * x * σ⁻¹)⁻¹ * α x * b = b * ((σ * x * σ⁻¹)⁻¹ * α x) := by
    intro b hb
    have ha : σ⁻¹ * b * σ ∈ alternatingGroup (Fin 5) := by
      simpa using (alternatingGroup.normal (α := Fin 5)).conj_mem b hb σ⁻¹
    have h1 : α (σ⁻¹ * b * σ) = b := by
      rw [hA _ ha]
      group
    have hxa : x * (σ⁻¹ * b * σ) * x⁻¹ ∈ alternatingGroup (Fin 5) :=
      (alternatingGroup.normal (α := Fin 5)).conj_mem _ ha x
    have h2 := hA _ hxa
    rw [map_mul, map_mul, map_inv, h1] at h2
    calc (σ * x * σ⁻¹)⁻¹ * α x * b = (σ * x * σ⁻¹)⁻¹ * (α x * b * (α x)⁻¹) * α x := by group
      _ = (σ * x * σ⁻¹)⁻¹ * (σ * (x * (σ⁻¹ * b * σ) * x⁻¹) * σ⁻¹) * α x := by rw [h2]
      _ = b * ((σ * x * σ⁻¹)⁻¹ * α x) := by group
  have hz := eq_one_of_commute_three_cycles_ch615 ((σ * x * σ⁻¹)⁻¹ * α x)
    (key _ three_cycles_mem_ch615.1) (key _ three_cycles_mem_ch615.2)
  rw [inv_mul_eq_one] at hz
  exact hz.symm

theorem card_sylow_perm_five_ch615 {S₀ : Subgroup (Perm (Fin 5))} (hS₀ : IsSylowTwoOf S₀ ⊤) :
    Nat.card S₀ = 8 := by
  obtain ⟨-, hS2, hodd⟩ := hS₀
  change ¬ 2 ∣ S₀.relIndex ⊤ at hodd
  rw [Subgroup.relIndex_top_right] at hodd
  have h := S₀.card_mul_index
  rw [card_perm_five_ch615] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  rw [hk] at h ⊢
  have hk7 : k < 7 := by
    by_contra hk'
    have h1 : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk')
    have h2 : 2 ^ k ≤ 120 := Nat.le_of_dvd (by norm_num) ⟨_, h.symm⟩
    omega
  interval_cases k <;> omega

theorem mem_of_conj_mem_overgroup_perm_five_ch615 {S₀ : Subgroup (Perm (Fin 5))}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {R₀ : Subgroup (Perm (Fin 5))} (hSR : S₀ ≤ R₀) (hRS : R₀ ≠ S₀)
    (hR : Group.IsSolvable ↥R₀) (g : Perm (Fin 5)) (hg : ∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀) :
    g ∈ R₀ := by
  have h8 := card_sylow_perm_five_ch615 hS₀
  have hdvd : Nat.card R₀ ∣ 120 := card_perm_five_ch615 ▸ Subgroup.card_subgroup_dvd_card R₀
  have hle : Nat.card R₀ ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨k, hk⟩ : 8 ∣ Nat.card R₀ := h8 ▸ Subgroup.card_dvd_of_le hSR
  have hR120 : Nat.card R₀ ≠ 120 := fun h => by
    have htop : R₀ = ⊤ := Subgroup.eq_top_of_card_eq R₀ (h.trans card_perm_five_ch615.symm)
    subst htop
    have := hR
    exact Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (Perm (Fin 5))) ≃* _).toMonoidHom)
      (MulEquiv.surjective _))
  have hR8 : Nat.card R₀ ≠ 8 := fun h =>
    hRS (Subgroup.eq_of_le_of_card_ge hSR (by omega)).symm
  have hnA : ¬ alternatingGroup (Fin 5) ≤ R₀ := fun hA => by
    obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hA
    rw [card_alternating_five_ch615] at ha
    have h60 : 60 * a ≤ 120 := by
      rw [← ha]
      exact hle
    have ha2 : a ≤ 2 := by omega
    have hpos : 0 < Nat.card R₀ := Nat.card_pos
    interval_cases a
    · omega
    · omega
    · exact hR120 (by rw [ha])
  rw [hk] at hm hle hR120 hR8
  have hk15 : k ≤ 15 := by omega
  interval_cases k <;> try omega
  ·
    set N := Subgroup.normalizer (R₀ : Set (Perm (Fin 5))) with hN
    have hgN : g ∈ N := mem_normalizer_of_conj_mem_l32_ch615 hg
    have hRN : R₀ ≤ N := Subgroup.le_normalizer
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hRN
    have hdvdN : Nat.card N ∣ 120 := card_perm_five_ch615 ▸ Subgroup.card_subgroup_dvd_card N
    have hleN : Nat.card N ≤ 120 := Nat.le_of_dvd (by norm_num) hdvdN
    obtain ⟨l, hl⟩ := hdvdN
    rw [hk] at hj
    rw [hj] at hl hleN
    have hj5 : j ≤ 5 := by omega
    interval_cases j <;> try omega
    · have hNR : N = R₀ := (Subgroup.eq_of_le_of_card_ge hRN (by omega)).symm
      rw [← hNR]
      exact hgN
    · exfalso
      have htop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [hj, card_perm_five_ch615])
      have hn : R₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases eq_bot_or_le_of_normal_perm_five_ch615 hn with hb | hA
      · rw [hb, Subgroup.card_bot] at hk
        omega
      · exact hnA hA
  ·
    exfalso
    have hidx : R₀.index = 3 := by
      have h := R₀.card_mul_index
      rw [card_perm_five_ch615, hk] at h
      omega
    rcases eq_bot_or_le_of_normal_perm_five_ch615 (Subgroup.normalCore_normal R₀) with hb | hA
    · have hinj : Function.Injective (MulAction.toPermHom (Perm (Fin 5)) (Perm (Fin 5) ⧸ R₀)) := by
        rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_perm (α := Perm (Fin 5) ⧸ R₀), ← Subgroup.index, hidx,
        card_perm_five_ch615] at this
      norm_num [Nat.factorial] at this
    · exact hnA (hA.trans (Subgroup.normalCore_le R₀))

theorem eq_one_of_central_perm_five_ch615 (x : Perm (Fin 5)) (h : ∀ y, x * y = y * x) : x = 1 :=
  eq_one_of_commute_three_cycles_ch615 x (h _) (h _)

theorem factorFacts_perm_five_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    (e : ↥F ≃* Perm (Fin 5)) : FactorFacts_ch615 F := by
  set φ : Perm (Fin 5) →* Γ := F.subtype.comp e.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hφe : ∀ g (hg : g ∈ F), φ (e ⟨g, hg⟩) = g := fun g hg => by
    simp [hφ]
  set N₀ := (alternatingGroup (Fin 5)).map φ with hN₀
  have hC : ∀ g ∈ F, (∀ n ∈ N₀, g * n = n * g) → g = 1 := by
    intro g hg h
    have hc : ∀ c ∈ alternatingGroup (Fin 5), e ⟨g, hg⟩ * c = c * e ⟨g, hg⟩ := fun c hc => by
      have h1 := h (φ c) ⟨c, hc, rfl⟩
      apply hφinj
      rw [map_mul, map_mul, hφe]
      exact h1
    have h1 := eq_one_of_commute_three_cycles_ch615 _ (hc _ three_cycles_mem_ch615.1)
      (hc _ three_cycles_mem_ch615.2)
    have h2 : (⟨g, hg⟩ : ↥F) = 1 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2
  refine ⟨fun h => ?_, center_of_mulEquiv_ch615 e eq_one_of_central_perm_five_ch615, ?_, ?_⟩
  · have h1 := Subgroup.card_eq_one.mpr h
    rw [Nat.card_congr e.toEquiv, card_perm_five_ch615] at h1
    omega
  · refine isIndec_of_normal_simple_ch615 (N₀ := N₀) ?_ ?_ ?_ hC
    · rintro _ ⟨a, -, rfl⟩
      exact (e.symm a).2
    · rintro g hg _ ⟨a, ha, rfl⟩
      refine ⟨e ⟨g, hg⟩ * a * (e ⟨g, hg⟩)⁻¹,
        (alternatingGroup.normal (α := Fin 5)).conj_mem a ha _, ?_⟩
      rw [map_mul, map_mul, map_inv, hφe]
    · exact (Subgroup.equivMapOfInjective (alternatingGroup (Fin 5)) φ hφinj).symm.isSimpleGroup
  · exact Or.inr (Or.inl (dLemmaFacts_of_mulEquiv_ch615 e Equiv.Perm.not_isSolvable_fin_5
      (fun α _ => exists_eq_conj_perm_five_ch615 α)
      (selfNormalizing_of_sylow_ch615 isSylowTwoOf_d8Sub_ch615 mem_d8Sub_of_conj_mem_ch615)
      (fun _ hS₀ _ hSR hRS hR g hg =>
        mem_of_conj_mem_overgroup_perm_five_ch615 hS₀ hSR hRS hR g hg)))

end S5

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ}

theorem ne_bot_of_not_isSolvable_ch615 (hns : ¬ Group.IsSolvable ↥F) : F ≠ ⊥ := by
  intro h
  apply hns
  have h1 := (Subgroup.eq_bot_iff_forall F).mp h
  have : Subsingleton ↥F := ⟨fun a b => Subtype.ext (by rw [h1 _ a.2, h1 _ b.2])⟩
  infer_instance

noncomputable def slRingEquiv_ch615 {n : ℕ} {K K' : Type*} [CommRing K] [CommRing K']
    (φ : K ≃+* K') : SL(n, K) ≃* SL(n, K') where
  toFun := Matrix.SpecialLinearGroup.map φ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map φ.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

theorem charTwo_facts_ch615 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem exists_finset_four_ch615 {K : Type} [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
  exact ⟨s, hs⟩

theorem factorFacts_sl2_two_ch615 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥F ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : FactorFacts_ch615 F := by
  have : CharP K 2 := charTwo_facts_ch615 (n := 1) (by rw [hK, pow_one])
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have h6 : Nat.card F = 6 := by
    rw [Nat.card_congr e'.toEquiv, card_sl2_field_ch615, hK]
    norm_num
  have hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1 := by
    refine center_of_mulEquiv_ch615 e' fun A hA => ?_
    have hc : A ∈ Subgroup.center SL(2, K) :=
      Subgroup.mem_center_iff.mpr fun B => (hA B).symm
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    rw [Fintype.card_fin] at hr
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hr1 : r = 1 := by
      have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
      exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h3)
    apply Subtype.ext
    rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨fun h => ?_, hZ, isIndec_of_card_six_ch615 h6 hZ, Or.inl h6⟩
  have h1 := Subgroup.card_eq_one.mpr h
  omega

theorem factorFacts_sl2_ch615 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : ↥F ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) :
    FactorFacts_ch615 F := by
  have : CharP K 2 := charTwo_facts_ch615 hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 := exists_finset_four_ch615 h4
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have hs : IsSimpleGroup ↥F := e.isSimpleGroup
  have hns : ¬ Group.IsSolvable ↥F := fun h => not_isSolvable_sl2_ch615 hK4 (by
    have := h
    exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective)
  have hZ := center_of_isSimpleGroup_ch615 hs hns
  refine ⟨ne_bot_of_not_isSolvable_ch615 hns, hZ, isIndec_of_isSimpleGroup_ch615 hs hZ,
    Or.inr (Or.inr ?_)⟩
  exact borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl2_ch615 hK4)
    (borel_of_sylow_ch615 (isSylowTwoOf_unipSub_ch615 hK)
      fun R hUR hR => borel_unipSub_ch615 hK4 hUR hR)

theorem not_isSolvable_sl3_ch615 {K : Type*} [Field K] (hK : ∃ s : Finset K, s.card = 4) :
    ¬ Group.IsSolvable SL(3, K) := by
  intro hs
  have hle := le_upperTriangular_of_isSolvable_ch615 hK (R := ⊤) le_top (by
    have := hs
    infer_instance)
  have h := hle (Subgroup.mem_top
    (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : K)))
  have h10 := h 1 0 (by decide)
  simp [SpecialLinearGroup.transvection_coe] at h10

theorem factorFacts_sl3_ch615 {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (hmodd : Odd m) (hK : Nat.card K = 2 ^ m)
    (e : ↥F ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) : FactorFacts_ch615 F := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK4 := exists_finset_four_ch615 h4
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hK hmodd
  have hs : IsSimpleGroup ↥F := e.isSimpleGroup
  have hns : ¬ Group.IsSolvable ↥F := fun h => not_isSolvable_sl3_ch615 hK4 (by
    have := h
    exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective)
  have hZ := center_of_isSimpleGroup_ch615 hs hns
  refine ⟨ne_bot_of_not_isSolvable_ch615 hns, hZ, isIndec_of_isSimpleGroup_ch615 hs hZ,
    Or.inr (Or.inr ?_)⟩
  exact borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl3_ch615 hK4)
    (borel_of_sylow_ch615 (isSylowTwoOf_unitriangular_ch615 hK (by norm_num))
      fun R hUR hR => borel_unitriangular_ch615 hK4 hUR hR)

theorem mem_of_conj_mem_overgroup_l32_ch615 (e : ↥F ≃* CFSG.QuasithinUnique.Setup.Family.GL32)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S F) {R : Subgroup Γ} (hSR : S ≤ R) (hRF : R ≤ F)
    (hRS : R ≠ S) (hR : Group.IsSolvable ↥R) {g : Γ} (hg : g ∈ F)
    (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R) : g ∈ R := by
  have hRF' : R ≠ F := fun h => by
    subst h
    exact not_isSolvable_l32_ch615 e hR
  have h24 := card_eq_24_l32_ch615 e hS hSR hRF hRS hRF'
  have h168 := card_l32_ch615 e
  set N := F ⊓ Subgroup.normalizer (R : Set Γ) with hN
  have hRN : R ≤ N := fun r hr => ⟨hRF hr, Subgroup.le_normalizer hr⟩
  have hgN : g ∈ N := ⟨hg, mem_normalizer_of_conj_mem_l32_ch615 hgR⟩
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hRN
  have hdvdN : Nat.card N ∣ 168 := h168 ▸ Subgroup.card_dvd_of_le (inf_le_left : N ≤ F)
  have hleN : Nat.card N ≤ 168 := Nat.le_of_dvd (by norm_num) hdvdN
  obtain ⟨l, hl⟩ := hdvdN
  rw [h24] at hj
  rw [hj] at hl hleN
  have hj7 : j ≤ 7 := by omega
  interval_cases j <;> try omega
  · have hNR : N = R := (Subgroup.eq_of_le_of_card_ge hRN (by omega)).symm
    rw [← hNR]
    exact hgN
  · exfalso
    have hNF : N = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hn : (R.subgroupOf F).Normal := ⟨fun x hx y => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hNF.ge y.2).2 x).mp hx⟩
    have := isSimpleGroup_l32_ch615 e
    have hcR : Nat.card (R.subgroupOf F) = 24 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv, h24]
    rcases hn.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot] at hcR
      omega
    · rw [ht, Subgroup.card_top, h168] at hcR
      omega

theorem factorFacts_l32_ch615 (e : ↥F ≃* CFSG.QuasithinUnique.Setup.Family.GL32) :
    FactorFacts_ch615 F := by
  have hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1 := fun g hg h =>
    eq_one_of_commute_l32_ch615 e hg h
  refine ⟨fun h => ?_, hZ, isIndec_of_isSimpleGroup_ch615 (isSimpleGroup_l32_ch615 e) hZ,
    Or.inr (Or.inl ⟨not_isSolvable_l32_ch615 e, exists_eq_conj_l32_ch615 e,
      fun S hS g hg hgS => mem_of_conj_mem_l32_ch615 e hS hg hgS,
      fun S hS R hSR hRF hRS hR g hg hgR =>
        mem_of_conj_mem_overgroup_l32_ch615 e hS hSR hRF hRS hR hg hgR⟩)⟩
  have h1 := Subgroup.card_eq_one.mpr h
  rw [card_l32_ch615 e] at h1
  omega

omit [Finite Γ] in
theorem nonempty_l32_ch615 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥F ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) :
    Nonempty (↥F ≃* CFSG.QuasithinUnique.Setup.Family.GL32) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).trans
    ((slRingEquiv_ch615 (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm).trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).trans
        statedSLThreeTwoEquiv_ch615))⟩

end Linear

theorem factorFacts_of_b56FactorList_ch615 {Γ : Type} [Group Γ] [Finite Γ] (F : Subgroup Γ)
    (hF : B56FactorList ↥F) : FactorFacts_ch615 F := by
  rcases hF with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | he | ⟨m, K, _, _, hm1, hmodd, hK, ⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact factorFacts_sl2_two_ch615 (by rw [hK, pow_one]) e
    · exact factorFacts_sl2_ch615 h hK e
  · obtain ⟨e⟩ := he
    exact factorFacts_perm_five_ch615 e
  · rcases Nat.lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      obtain ⟨e'⟩ := nonempty_l32_ch615 (by rw [hK, pow_one]) e
      exact factorFacts_l32_ch615 e'
    · have hm3 : 3 ≤ m := by
        obtain ⟨k, rfl⟩ := hmodd
        omega
      exact factorFacts_sl3_ch615 hm3 hmodd hK e

theorem res615EFF_of_cases14 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (hB56 : AsB56)
    (hcases : ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      (B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) ∨ B56Case4 (ffJ (autI hU (borelL T L ⊔ H)))) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF :=
  res615EFF_of_cases134 h331 h432 hB56 fun G _ _ T M L V H n c hU hN h => by
    rcases h with h1 | h3 | h4
    · exact hcases G T M L V H n c hU hN (Or.inl h1)
    · exact (c.false_of_b56Case3_ch615 h331 h432 hU hN
        (fun F hF => factorFacts_of_b56FactorList_ch615 F hF) h3).elim
    · exact hcases G T M L V H n c hU hN (Or.inr h4)

end CFSG.Quasithin.H13
