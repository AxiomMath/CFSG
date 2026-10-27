module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN4

public section

namespace CFSG.Quasithin.H13.L829N

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem no_three_L829 {T : Type} (hT : Nat.card T = 2) (a b c : T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  obtain ⟨p, q, -, huniv⟩ := Nat.card_eq_two_iff.mp hT
  have hm : ∀ t : T, t = p ∨ t = q := fun t => by
    have ht : t ∈ ({p, q} : Set T) := by
      rw [huniv]
      exact Set.mem_univ t
    simpa using ht
  rcases hm a with rfl | rfl <;> rcases hm b with rfl | rfl <;> rcases hm c with rfl | rfl <;>
    first | exact hab rfl | exact hac rfl | exact hbc rfl

private def commMapL829 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (g : W ≃ₗ[ZMod 2] W)
    (hgA : ∀ (a : A) (u : W), g (a • u) = a • g u) : W →ₗ[A] W where
  toFun u := g u - u
  map_add' u w := by simp only [map_add]; abel
  map_smul' a u := by simp only [RingHom.id_apply, hgA, smul_sub]

theorem transv_of_conj
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg)
    (h : TransvConfig Sg Gg Tg Vg WB)
    (X : Submodule A W) [IsSimpleModule A X] (hXWB : ∀ x ∈ X, x ∈ WB)
    (hdim : Nat.card ↥X = 2 ∨ Nat.card ↥X = 16)
    (htop : isotypicComponent A W X = ⊤)
    (g : W ≃ₗ[ZMod 2] W) (hg : g ∈ Gg)
    (hgen : ∃ v ∈ Vg, ∃ x ∈ Gg ⊔ Tg, g = x * v * x⁻¹) (hne : g ≠ 1) :
    g * g = 1 ∧ ∃ Θ : Submodule A W, (∀ w, w ∈ Θ ↔ ∃ u, g u - u = w) ∧
      Nonempty (↥Θ ≃ₗ[A] ↥X) := by
  obtain ⟨v, hv, c, -, hgv⟩ := hgen
  have hgu : ∀ u, g u = c (v (c⁻¹ u)) := fun u => by rw [hgv]; rfl
  have hgg : g * g = 1 := by
    rw [hgv]
    calc c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
      _ = 1 := by rw [h.V_sq v hv]; group
  have hf : ∀ s ∈ Sg, (g : Module.End (ZMod 2) W) * (s : Module.End (ZMod 2) W) =
      (s : Module.End (ZMod 2) W) * (g : Module.End (ZMod 2) W) := by
    intro s hs
    ext y
    exact congrArg (fun e : W ≃ₗ[ZMod 2] W => e y) (h.comm g hg s hs)
  have hgA : ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W) := by
    rw [hA]
    exact commute_of_commute_gens Sg hf
  have hgA' : ∀ (a : A) (u : W), g (a • u) = a • g u := fun a u =>
    congrArg (fun F : Module.End (ZMod 2) W => F u) (hgA a a.2)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Submodule A W, ∀ w, w ∈ Θ ↔ ∃ u, g u - u = w :=
    ⟨LinearMap.range (commMapL829 A g hgA'), fun w => LinearMap.mem_range⟩
  refine ⟨hgg, Θ, hΘ, ?_⟩
  have hΘne : Θ ≠ ⊥ := by
    intro hbot
    apply hne
    apply LinearEquiv.ext
    intro u
    have hmem : g u - u ∈ Θ := (hΘ _).mpr ⟨u, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    simpa using hmem
  have hss : IsSemisimpleModule A W := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule
      (s := {isotypicComponent A W ↥X}) (p := fun c => c) ?_ ?_
    · intro c hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact inferInstance
    · simpa using htop
  have hiso : IsIsotypicOfType A W ↥X := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  have hisoΘ : IsIsotypicOfType A ↥Θ ↥X :=
    isIsotypicOfType_submodule_iff.mpr fun m _ _ => hiso m
  haveI : Finite ↥Θ := inferInstance
  haveI : Module.Finite A ↥Θ := Module.Finite.of_finite
  obtain ⟨k, ⟨e⟩⟩ := hisoΘ.linearEquiv_fun
  have hcardΘ : Nat.card ↥Θ = Nat.card ↥X ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hsub : Subsingleton ↥Θ := e.injective.subsingleton
    have hnt : Nontrivial ↥Θ := Θ.nontrivial_iff_ne_bot.mpr hΘne
    exact not_subsingleton _ hsub
  obtain ⟨Θ0, hΘ0⟩ : ∃ Θ0 : Submodule (ZMod 2) W, ∀ w, w ∈ Θ0 ↔ ∃ z, v z - z = w :=
    ⟨LinearMap.range (v.toLinearMap - LinearMap.id), fun w => LinearMap.mem_range⟩
  have hΘ0le : Θ0 ≤ WB := by
    intro w hw
    obtain ⟨z, hz⟩ := (hΘ0 w).mp hw
    rw [← hz]
    exact h.WB_V v hv z
  have hfin0 : Module.finrank (ZMod 2) Θ0 ≤ 5 :=
    (Submodule.finrank_mono hΘ0le).trans h.hb.dim_le
  have hΘT : ∀ w, w ∈ Θ ↔ w ∈ Θ0.map c.toLinearMap := by
    intro w
    rw [hΘ, Submodule.mem_map]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨v (c⁻¹ u) - c⁻¹ u, (hΘ0 _).mpr ⟨c⁻¹ u, rfl⟩, ?_⟩
      rw [hgu, map_sub]
      simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := (hΘ0 y).mp hy
      refine ⟨c z, ?_⟩
      rw [hgu, ← hz, map_sub]
      simp
  have hcardΘ2 : Nat.card ↥Θ = 2 ^ Module.finrank (ZMod 2) Θ0 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hΘT), Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, LinearEquiv.finrank_map_eq]
  have hk1 : k ≤ 1 := by
    rcases hdim with hX | hX
    ·
      have hSg : ∀ s ∈ Sg, ∀ w : W, s w = w := by
        intro s hs
        have hsA : (s : Module.End (ZMod 2) W) ∈ A := by
          rw [hA]
          exact mem_algOf_of_mem Sg hs
        have key : ∀ m : Submodule A W, Nonempty (↥m ≃ₗ[A] ↥X) → ∀ z ∈ m, s z = z := by
          rintro m ⟨em⟩ z hz
          have hm2 : Nat.card ↥m = 2 := (Nat.card_congr em.toEquiv).trans hX
          by_cases hz0 : z = 0
          · rw [hz0, map_zero]
          by_contra hsz
          have hzm : s z ∈ m := m.smul_mem (⟨(s : Module.End (ZMod 2) W), hsA⟩ : A) hz
          have hsz0 : s z ≠ 0 := fun h0 => hz0 (s.map_eq_zero_iff.mp h0)
          exact no_three_L829 hm2 ⟨0, m.zero_mem⟩ ⟨z, hz⟩ ⟨s z, hzm⟩
            (fun h0 => hz0 (congrArg Subtype.val h0).symm)
            (fun h0 => hsz0 (congrArg Subtype.val h0).symm)
            (fun h0 => hsz (congrArg Subtype.val h0).symm)
        have hall : ∀ z ∈ isotypicComponent A W ↥X, s z = z := by
          intro z hz
          have hz' : z ∈ ⨆ a : {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)},
              (a : Submodule A W) := by
            rw [← sSup_eq_iSup']
            exact hz
          refine Submodule.iSup_induction (motive := fun y => s y = y)
            (fun a : {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)} => (a : Submodule A W))
            hz' ?_ ?_ ?_
          · rintro ⟨m, hm⟩ y hy
            exact key m hm y hy
          · exact map_zero s
          · intro y y' hy hy'
            have hy1 : s y = y := hy
            have hy2 : s y' = y' := hy'
            show s (y + y') = y + y'
            rw [map_add, hy1, hy2]
        intro w
        exact hall w (by rw [htop]; exact Submodule.mem_top)
      have hfix : Module.finrank (ZMod 2) Θ0 ≤ 1 :=
        h.hb.fix_le Θ0 hΘ0le (fun s hs w _ => hSg s hs w)
      have hkeq : 2 ^ k = 2 ^ Module.finrank (ZMod 2) Θ0 := by
        rw [← hcardΘ2, hcardΘ, hX]
      have hle : 2 ^ k ≤ 2 ^ 1 := by
        rw [hkeq]
        exact Nat.pow_le_pow_right (by norm_num) hfix
      by_contra hcon
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (le_trans h4 hle) (by norm_num)
    ·
      have hkeq : 16 ^ k = 2 ^ Module.finrank (ZMod 2) Θ0 := by
        rw [← hcardΘ2, hcardΘ, hX]
      have hle : 16 ^ k ≤ 2 ^ 5 := by
        rw [hkeq]
        exact Nat.pow_le_pow_right (by norm_num) hfin0
      by_contra hcon
      have h256 : 16 ^ 2 ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (le_trans h256 hle) (by norm_num)
  have hk1' : k = 1 := by omega
  subst hk1'
  exact ⟨e.trans (LinearEquiv.funUnique (Fin 1) A ↥X)⟩

end CFSG.Quasithin.H13.L829N
