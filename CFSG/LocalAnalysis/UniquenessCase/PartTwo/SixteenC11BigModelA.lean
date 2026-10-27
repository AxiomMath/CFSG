module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigNat
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private lemma s16c11_big_modela_alt_data {n : ℕ} (hn : 5 ≤ n) {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) :
    ∃ (ρ : ↥(alternatingGroup (Fin n)) ≃* ↥L) (β : ↥J₀ ≃* (FFModel.altDn n).Mod),
      ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
        ∃ (hu : ((ρ γ : ↥L) : MulAut W) (u : W) ∈ J₀),
          β ⟨((ρ γ : ↥L) : MulAut W) (u : W), hu⟩ =
            (FFModel.altDn_isActionModel n).modAct
              (show (FFModel.altDn n).Gam from γ) (β u) := by
  obtain ⟨ρ₀, β, hβ⟩ := s16c11_big_realizes_equiv (FFModel.altDn_isActionModel n)
    (FFC.altDn_faithful hn) h.nat₀
  let ρ : ↥(alternatingGroup (Fin n)) ≃* ↥L := ρ₀
  refine ⟨ρ, β, fun γ u => ?_⟩
  let q := (FFModel.altDn_isActionModel n).modAct (show (FFModel.altDn n).Gam from γ) (β u)
  let v : ↥J₀ := β.symm q
  have hv : (v : W) = ((ρ γ : ↥L) : MulAut W) (u : W) :=
    hβ (show (FFModel.altDn n).Gam from γ) u
  have hsub : (⟨((ρ γ : ↥L) : MulAut W) (u : W), by rw [← hv]; exact v.2⟩ : ↥J₀) = v :=
    Subtype.ext hv.symm
  refine ⟨by rw [← hv]; exact v.2, ?_⟩
  rw [hsub]
  simpa only [v] using β.apply_symm_apply q

private lemma s16c11_big_modela_modAct_altDn (n : ℕ) (σ : ↥(alternatingGroup (Fin n)))
    (q : (FFModel.altDn n).Mod) :
    (FFModel.altDn_isActionModel n).modAct (show (FFModel.altDn n).Gam from σ) q =
      (FFModel.symDn_isActionModel n).modAct (σ : Equiv.Perm (Fin n)) q := rfl

theorem s16c11_big_card_J {n : ℕ} (hn : n = 9 ∨ n = 10) {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) : Nat.card ↥J₀ = 2 ^ 8 := by
  obtain ⟨ρ, β, -⟩ := s16c11_big_modela_alt_data (by omega) h
  have hβ : Nat.card ↥J₀ = Nat.card (FFModel.altDn n).Mod := Nat.card_congr β.toEquiv
  rw [hβ]
  exact s16c11BigCls_card n hn

theorem s16c11_big_threeCycle_J {n : ℕ} (hn : 9 ≤ n) {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) {a b : W} (ha : a ∈ J₀)
    (hb : b ∈ J₀) : ∃ φ ∈ L, orderOf φ = 3 ∧ φ a = a ∧ φ b = b := by
  obtain ⟨ρ, β, hdata⟩ := s16c11_big_modela_alt_data (by omega) h
  obtain ⟨c, hcA, hcorder, hcq, hcr⟩ :=
    s16c11_big_exists_threeCycle_fix hn (β ⟨a, ha⟩) (β ⟨b, hb⟩)
  let c' : ↥(alternatingGroup (Fin n)) := ⟨c, hcA⟩
  let φ : MulAut W := (ρ c' : ↥L)
  refine ⟨φ, (ρ c').2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    change orderOf (⟨c, hcA⟩ : ↥(alternatingGroup (Fin n))) = 3
    rw [Subgroup.orderOf_mk]
    exact hcorder
  · obtain ⟨hu, hβ⟩ := hdata c' ⟨a, ha⟩
    have halt : (FFModel.altDn_isActionModel n).modAct
        (show (FFModel.altDn n).Gam from c') (β ⟨a, ha⟩) = β ⟨a, ha⟩ := by
      rw [s16c11_big_modela_modAct_altDn]
      exact hcq
    have hbeq : β ⟨((ρ c' : ↥L) : MulAut W) a, hu⟩ = β ⟨a, ha⟩ := by
      rw [hβ, halt]
    exact congrArg Subtype.val (β.injective hbeq)
  · obtain ⟨hu, hβ⟩ := hdata c' ⟨b, hb⟩
    have halt : (FFModel.altDn_isActionModel n).modAct
        (show (FFModel.altDn n).Gam from c') (β ⟨b, hb⟩) = β ⟨b, hb⟩ := by
      rw [s16c11_big_modela_modAct_altDn]
      exact hcr
    have hbeq : β ⟨((ρ c' : ↥L) : MulAut W) b, hu⟩ = β ⟨b, hb⟩ := by
      rw [hβ, halt]
    exact congrArg Subtype.val (β.injective hbeq)

theorem s16c11_big_exists_fixed_order_three [Finite W] {n : ℕ} (hn : 9 ≤ n)
    {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) (w : W) : ∃ φ ∈ L, orderOf φ = 3 ∧ φ w = w := by
  obtain ⟨a, b, ha, hb, hfix⟩ := s16c11_big_fix_of_coords h w
  obtain ⟨φ, hφL, horder, hφa, hφb⟩ := s16c11_big_threeCycle_J hn h ha hb
  exact ⟨φ, hφL, horder, hfix φ (h.ll₀ hφL) hφa hφb⟩

theorem s16c11_big_exists_B {n : ℕ} (hn : n = 9 ∨ n = 10) {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) :
    ∃ B : Subgroup (MulAut W), B ≤ L ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      Nat.card ↥(J₀ ⊓ fixV B) = 16 := by
  obtain ⟨ρ, β, hdata⟩ := s16c11_big_modela_alt_data (by omega) h
  obtain ⟨B', hB'A, hB'p, hB'nc, hB'card⟩ := s16c11_big_exists_fixed_sixteen hn
  let A : Subgroup (Equiv.Perm (Fin n)) := alternatingGroup (Fin n)
  let B'' : Subgroup ↥A := B'.subgroupOf A
  let ψ : ↥A →* MulAut W := L.subtype.comp ρ.toMonoidHom
  let B : Subgroup (MulAut W) := B''.map ψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact ρ.injective (Subtype.ext hab)
  have hBL : B ≤ L := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    exact (ρ c).2
  have hBp : IsPGroup 3 ↥B := by
    have hp : IsPGroup 3 ↥B'' :=
      hB'p.of_equiv (Subgroup.subgroupOfEquivOfLe hB'A).symm
    exact hp.map ψ
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    have hcyc'' : IsCyclic ↥B'' :=
      (Subgroup.equivMapOfInjective B'' ψ hψinj).isCyclic.mpr hcyc
    exact hB'nc ((Subgroup.subgroupOfEquivOfLe hB'A).isCyclic.mp hcyc'')
  have hcard : Nat.card ↥(J₀ ⊓ fixV B) = 16 := by
    let T : Set (FFModel.altDn n).Mod :=
      {q | ∀ (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ B'),
        (FFModel.altDn_isActionModel n).modAct
          (show (FFModel.altDn n).Gam from (⟨σ, hB'A hσ⟩ : ↥A)) q = q}
    let S : Set (FFModel.altDn n).Mod :=
      {q | ∀ (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ B'),
        (FFModel.symDn_isActionModel n).modAct σ q = q}
    have hTS : T = S := by
      ext q
      simp only [T, S, Set.mem_setOf_eq]
      constructor
      · intro hq σ hσ
        have := hq σ hσ
        rw [s16c11_big_modela_modAct_altDn] at this
        exact this
      · intro hq σ hσ
        rw [s16c11_big_modela_modAct_altDn]
        exact hq σ hσ
    have hTcard : Nat.card ↥T = 16 := by
      rw [hTS]
      exact hB'card
    have hkey : ∀ u : ↥J₀, ((u : W) ∈ fixV B) ↔ (β u ∈ T) := by
      intro u
      have hfix' : ((u : W) ∈ fixV B) ↔
          ∀ c ∈ B'', ((ρ c : ↥L) : MulAut W) (u : W) = u := by
        rw [mem_fixV]
        constructor
        · intro hb c hc
          exact hb (ψ c) (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
        · intro hc b hb
          obtain ⟨c, hc', hcb⟩ := Subgroup.mem_map.mp hb
          rw [← hcb]
          exact hc c hc'
      rw [hfix']
      constructor
      · intro h σ hσ
        let c : ↥A := ⟨σ, hB'A hσ⟩
        have hcB : c ∈ B'' := by
          rw [Subgroup.mem_subgroupOf]
          exact hσ
        obtain ⟨hu, hβ⟩ := hdata c u
        have hsub : (⟨((ρ c : ↥L) : MulAut W) (u : W), hu⟩ : ↥J₀) = u :=
          Subtype.ext (h c hcB)
        rw [hsub] at hβ
        exact hβ.symm
      · intro hq c hcB
        obtain ⟨hu, hβ⟩ := hdata c u
        have hc' : (c : Equiv.Perm (Fin n)) ∈ B' := by
          rwa [← Subgroup.mem_subgroupOf]
        have halt : (FFModel.altDn_isActionModel n).modAct
            (show (FFModel.altDn n).Gam from c) (β u) = β u := by
          have := hq (c : Equiv.Perm (Fin n)) hc'
          simpa using this
        have hbeq : β ⟨((ρ c : ↥L) : MulAut W) (u : W), hu⟩ = β u := by
          rw [hβ, halt]
        exact congrArg Subtype.val (β.injective hbeq)
    let e1 : ↥(J₀ ⊓ fixV B) ≃ {u : ↥J₀ // (u : W) ∈ fixV B} :=
      { toFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
        invFun := fun u => ⟨u.1.1, ⟨u.1.2, u.2⟩⟩
        left_inv := fun u => Subtype.ext rfl
        right_inv := fun u => Subtype.ext rfl }
    let e2 : {u : ↥J₀ // (u : W) ∈ fixV B} ≃ {u : ↥J₀ // β u ∈ T} :=
      Equiv.subtypeEquivRight hkey
    let e3 : {u : ↥J₀ // β u ∈ T} ≃ T :=
      { toFun := fun u => ⟨β u.1, u.2⟩
        invFun := fun q => ⟨β.symm q.1, by
          have hq : β (β.symm q.1) = q.1 := β.apply_symm_apply q.1
          rw [hq]
          exact q.2⟩
        left_inv := fun u => Subtype.ext (β.symm_apply_apply u.1)
        right_inv := fun q => Subtype.ext (β.apply_symm_apply q.1) }
    have hcard_eq : Nat.card ↥(J₀ ⊓ fixV B) = Nat.card ↥T :=
      Nat.card_congr (e1.trans (e2.trans e3))
    rw [hcard_eq, hTcard]
  exact ⟨B, hBL, hBp, hBnc, hcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
