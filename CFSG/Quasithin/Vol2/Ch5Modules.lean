module

public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.G6
open scoped IsMulCommutative commutatorElement

section D5

@[expose] def d5w (i : Fin 5) : PermMod 5 := Multiplicative.ofAdd (Pi.single i 1 + Pi.single 4 1)

@[expose] def d5m : Fin 4 → PermMod 5 :=
  ![Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1),
    Multiplicative.ofAdd (Pi.single 1 1 + Pi.single 2 1),
    Multiplicative.ofAdd (Pi.single 2 1 + Pi.single 3 1),
    Multiplicative.ofAdd (Pi.single 3 1 + Pi.single 0 1)]

@[expose] def d5g : Fin 4 → Equiv.Perm (Fin 5) :=
  ![Equiv.swap 0 4 * Equiv.swap 0 1, Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 2 4 * Equiv.swap 2 3, Equiv.swap 3 4 * Equiv.swap 3 0]

theorem d5w_mem : ∀ i : Fin 5, d5w i ∈ coreMod 5 := by
  simp only [mem_coreMod]
  decide +kernel

theorem d5m_mem : ∀ i : Fin 4, d5m i ∈ coreMod 5 := by
  simp only [mem_coreMod]
  decide +kernel

theorem d5g_mem (i : Fin 4) : d5g i ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i <;> simp [d5g, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem d5g_pow_three : ∀ i : Fin 4, d5g i ^ 3 = 1 := by
  decide +kernel

theorem d5w_eq : ∀ i : Fin 4,
    d5w i.castSucc = d5m i * (permAct 5 (d5g i) (d5m i))⁻¹ := by
  decide +kernel

theorem d5_decomp : ∀ x : PermMod 5, x ∈ coreMod 5 →
    x = d5w 0 ^ (Multiplicative.toAdd x 0).val * d5w 1 ^ (Multiplicative.toAdd x 1).val *
      d5w 2 ^ (Multiplicative.toAdd x 2).val * d5w 3 ^ (Multiplicative.toAdd x 3).val := by
  simp only [mem_coreMod]
  decide +kernel

theorem d5_key : (d5m 0)⁻¹ * permAct 5 (d5g 0) (d5m 0) = d5w 0 := by
  decide +kernel

theorem d5w_zero_ne : d5w 0 ≠ 1 ∧ d5w 0 ≠ allOnes 5 := by
  decide +kernel

theorem allOnes_sq : allOnes 5 ^ 2 = 1 := by
  decide +kernel

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {a x : M} (ha : a ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact ha
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · left
    rw [hj, zpow_mul, ha2, one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

end D5

section Realize

variable {V : Type*} [CommGroup V]

theorem symDn_five_ne_one {X : Subgroup (MulAut V)} {π : Equiv.Perm (Fin 5) →* ↥X}
    (hS : (FFModel.symDn 5).RealizesVia X ⊤ ⊥ π) : ((π (d5g 0) : ↥X) : MulAut V) ≠ 1 := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, -, hβe⟩ := hS
  intro h1
  set m : ↥(coreMod 5) := ⟨d5m 0, d5m_mem 0⟩ with hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
  have hσm : permAct 5 (d5g 0) (d5m 0) ∈ coreMod 5 := hsec (d5g 0) (d5m 0) (d5m_mem 0)
  have hu' : ((π (d5g 0) : ↥X) : MulAut V) (u : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
  have he := hβe (d5g 0) u m hu' hσm hu
  have hfix : (⟨((π (d5g 0) : ↥X) : MulAut V) (u : V), hu'⟩ : ↥(⊤ : Subgroup V)) = u := by
    apply Subtype.ext
    show ((π (d5g 0) : ↥X) : MulAut V) (u : V) = u
    rw [h1]
    rfl
  have he' : β u = QuotientGroup.mk (⟨permAct 5 (d5g 0) (d5m 0), hσm⟩ : ↥(coreMod 5)) :=
    (congrArg β hfix).symm.trans he
  have h2 := QuotientGroup.eq.mp (hu.symm.trans he')
  rw [Subgroup.mem_subgroupOf] at h2
  have h4 : d5w 0 ∈ Subgroup.zpowers (allOnes 5) := by
    have h5 := h2.1
    rw [← d5_key]
    exact h5
  rcases eq_one_or_eq_of_mem_zpowers allOnes_sq h4 with h5 | h5
  · exact d5w_zero_ne.1 h5
  · exact d5w_zero_ne.2 h5

theorem not_isPGroup_of_symDn {X : Subgroup (MulAut V)} {π : Equiv.Perm (Fin 5) →* ↥X}
    (hS : (FFModel.symDn 5).RealizesVia X ⊤ ⊥ π) (h2 : IsPGroup 2 ↥X) : False := by
  apply symDn_five_ne_one hS
  obtain ⟨k, hk⟩ := h2 (π (d5g 0))
  have h3 : π (d5g 0) ^ 3 = 1 := by rw [← map_pow, d5g_pow_three 0, map_one]
  have hord1 : orderOf (π (d5g 0)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (π (d5g 0)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hord : orderOf (π (d5g 0)) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  rw [orderOf_eq_one_iff] at hord
  rw [hord]
  rfl

theorem alternatingNatural_of_symDn {X A : Subgroup (MulAut V)} {π : Equiv.Perm (Fin 5) →* ↥X}
    (hS : (FFModel.symDn 5).RealizesVia X ⊤ ⊥ π)
    (hA : A = (alternatingGroup (Fin 5)).map (X.subtype.comp π)) :
    AlternatingNatural A ⊤ ⊥ 5 := by
  obtain ⟨-, h1, h2, -, -, h5, h6, β, hβs, hβk, hβe⟩ := hS
  have hmem : ∀ σ : ↥(alternatingGroup (Fin 5)), ((π σ : ↥X) : MulAut V) ∈ A := fun σ =>
    hA.ge ⟨σ, σ.2, rfl⟩
  let π' : ↥(alternatingGroup (Fin 5)) →* ↥A :=
    { toFun := fun σ => ⟨((π σ : ↥X) : MulAut V), hmem σ⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun σ τ => by
        apply Subtype.ext
        simp }
  refine ⟨π', ?_, h1, h2, ?_, ?_, fun γ m hm => h5 (γ : ↥(alternatingGroup (Fin 5))).1 m hm,
    fun γ m hm => h6 (γ : ↥(alternatingGroup (Fin 5))).1 m hm, β, hβs, hβk, ?_⟩
  · intro a
    obtain ⟨σ, hσ, hσa⟩ := hA.le a.2
    exact ⟨⟨σ, hσ⟩, Subtype.ext hσa⟩
  · intro _ _ _
    exact Subgroup.mem_top _
  · intro _ z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ u m hu hm h
    exact hβe (γ : ↥(alternatingGroup (Fin 5))).1 u m hu hm h

theorem eq_map_alternatingGroup {X A : Subgroup (MulAut V)} {π : Equiv.Perm (Fin 5) →* ↥X}
    (hπ : Function.Surjective π) (hAX : A ≤ X) (hXA : X ≤ Subgroup.normalizer (A : Set (MulAut V)))
    (hperf : ⁅A, A⁆ = A) (hne : A ≠ ⊥) :
    A = (alternatingGroup (Fin 5)).map (X.subtype.comp π) := by
  set φ : Equiv.Perm (Fin 5) →* MulAut V := X.subtype.comp π with hφ
  have hrange : φ.range = X := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hle : A ≤ (alternatingGroup (Fin 5)).map φ := by
    rw [← hperf]
    calc ⁅A, A⁆ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hAX hAX
      _ = ⁅Subgroup.map φ ⊤, Subgroup.map φ ⊤⁆ := by rw [← MonoidHom.range_eq_map, hrange]
      _ = Subgroup.map φ
            ⁅(⊤ : Subgroup (Equiv.Perm (Fin 5))), (⊤ : Subgroup (Equiv.Perm (Fin 5)))⁆ :=
          (Subgroup.map_commutator ⊤ ⊤ φ).symm
      _ ≤ (alternatingGroup (Fin 5)).map φ := by
          apply Subgroup.map_mono
          rw [Subgroup.commutator_le]
          intro g _ h _
          rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
          exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  apply le_antisymm hle
  set N : Subgroup ↥(alternatingGroup (Fin 5)) :=
    (A.comap φ).subgroupOf (alternatingGroup (Fin 5)) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hn ⊢
    have hgX : φ g ∈ X := by
      rw [← hrange]
      exact ⟨g, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hXA hgX) (φ n)).mp hn
    simpa [map_mul, map_inv] using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨σ, hσ, rfl⟩ := hle ha
    have hσN : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact ha
    rw [hb, Subgroup.mem_bot] at hσN
    have : σ = 1 := congrArg Subtype.val hσN
    rw [this, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨σ, hσ, rfl⟩
    have hσN : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈ N := by
      rw [ht]
      exact Subgroup.mem_top _
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hσN
    exact hσN

end Realize

section Inside

variable {G : Type} [Group G]

theorem autOn_sup_eq_sup {L T W : Subgroup G} (hL : L ≤ Subgroup.normalizer (W : Set G))
    (hT : T ≤ Subgroup.normalizer (W : Set G)) : autOn (L ⊔ T) W = autOn L W ⊔ autOn T W :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hL hT

theorem autOn_perfect {L W : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : ⁅autOn L W, autOn L W⁆ = autOn L W := by
  have h1 : ⁅L.subgroupOf (Subgroup.normalizer (W : Set G)),
      L.subgroupOf (Subgroup.normalizer (W : Set G))⁆ =
        L.subgroupOf (Subgroup.normalizer (W : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (W : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLW, hL]
  unfold autOn
  rw [← Subgroup.map_commutator, h1]

theorem autOn_isPGroup {T W : Subgroup G} (hT : IsPGroup 2 T) : IsPGroup 2 ↥(autOn T W) := by
  unfold autOn
  exact (hT.comap_of_injective _ (Subgroup.normalizer (W : Set G)).subtype_injective).map _

theorem autOn_sup_le_normalizer_autOn {L T W : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    autOn (L ⊔ T) W ≤
      Subgroup.normalizer ((autOn L W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) := by
  unfold autOn
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
  exact le_normalizer_subgroupOf (sup_le Subgroup.le_normalizer hTL)

theorem isA5ModuleUnder_of_isS5ModCh5 {L T W : Subgroup G} (h : IsS5ModCh5 L T W)
    (hL : ⁅L, L⁆ = L) (hT : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsA5ModuleUnder L W := by
  obtain ⟨hN, hc, π, hπ⟩ := h
  refine ⟨le_sup_left.trans hN, hc, ?_⟩
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hN
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans hN
  have hAX : autOn L W ≤ autOn (L ⊔ T) W := A4.autOn_mono le_sup_left
  have hne : autOn L W ≠ ⊥ := by
    intro hb
    have hX : autOn (L ⊔ T) W = autOn T W := by
      rw [autOn_sup_eq_sup hLW hTW, hb, bot_sup_eq]
    have h2 : IsPGroup 2 ↥(autOn (L ⊔ T) W) := by
      rw [hX]
      exact autOn_isPGroup hT
    exact not_isPGroup_of_symDn hπ h2
  have heq := eq_map_alternatingGroup hπ.1 hAX (autOn_sup_le_normalizer_autOn hTL)
    (autOn_perfect hL hLW) hne
  exact alternatingNatural_of_symDn hπ heq

theorem isA5ModuleSum_of_s5 {L T W : Subgroup G}
    (h : IsS5ModCh5 L T W ∨ IsSumOfTwo (L ⊔ T) W (IsS5ModCh5 L T)) (hL : ⁅L, L⁆ = L)
    (hT : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) : IsA5ModuleSum L W := by
  rcases h with h | ⟨W₁, W₂, -, -, hinf, hsup, h1, h2⟩
  · exact Or.inl (isA5ModuleUnder_of_isS5ModCh5 h hL hT hTL)
  · exact Or.inr ⟨W₁, W₂, isA5ModuleUnder_of_isS5ModCh5 h1 hL hT hTL,
      isA5ModuleUnder_of_isS5ModCh5 h2 hL hT hTL, hinf, hsup⟩

theorem IsA5ModuleUnder.commutator_eq {L W : Subgroup G} (h : IsA5ModuleUnder L W) :
    ⁅W, L⁆ = W := by
  obtain ⟨hLW, hc, π, hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hLW)
  set Dsub : Subgroup ↥(⊤ : Subgroup ↥W) :=
    (⁅W, L⁆.subgroupOf W).comap (⊤ : Subgroup ↥W).subtype with hDsub
  set C : Subgroup ↥(FFModel.altDn 5).sec :=
    (Dsub.map β).comap (QuotientGroup.mk' ((FFModel.altDn 5).ker.subgroupOf
      (FFModel.altDn 5).sec)) with hC
  have hgen : ∀ i : Fin 4,
      (⟨d5w i.castSucc, d5w_mem _⟩ : ↥(FFModel.altDn 5).sec) ∈ C := by
    intro i
    set m : ↥(FFModel.altDn 5).sec := ⟨d5m i, d5m_mem i⟩ with hm
    set γ : ↥(alternatingGroup (Fin 5)) := ⟨d5g i, d5g_mem i⟩ with hγ
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    have hσm : (FFModel.altDn 5).act γ m.1 ∈ (FFModel.altDn 5).sec :=
      hsec γ (d5m i) (d5m_mem i)
    have hu' : ((π γ : ↥(autOn L W)) : MulAut ↥W) (u : ↥W) ∈ (⊤ : Subgroup ↥W) :=
      Subgroup.mem_top _
    have he := hβe γ u m hu' hσm hu
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLW).mp (π γ).2
    set c : ↥(⊤ : Subgroup ↥W) :=
      u * (⟨((π γ : ↥(autOn L W)) : MulAut ↥W) (u : ↥W), hu'⟩ : ↥(⊤ : Subgroup ↥W))⁻¹ with hc
    have hcD : c ∈ Dsub := by
      have hval : (((c : ↥W) : G)) = ⁅((u : ↥W) : G), (l : G)⁆ := by
        rw [hc]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hl, A4.actionOn_apply_coe]
        rw [commutatorElement_def]
        group
      show ((c : ↥W) : G) ∈ ⁅W, L⁆
      rw [hval]
      exact Subgroup.commutator_mem_commutator (u : ↥W).2 l.2
    have hβc : β c =
        QuotientGroup.mk (⟨d5w i.castSucc, d5w_mem _⟩ : ↥(FFModel.altDn 5).sec) := by
      rw [hc, map_mul, map_inv, hu, he, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (d5m i : PermMod 5) * (permAct 5 (d5g i) (d5m i))⁻¹ = d5w i.castSucc
      exact (d5w_eq i).symm
    exact Subgroup.mem_comap.mpr ⟨c, hcD, hβc⟩
  have hCtop : ∀ y : ↥(FFModel.altDn 5).sec, y ∈ C := by
    intro y
    have hy := d5_decomp y.1 y.2
    have hy' : y =
        (⟨d5w 0, d5w_mem 0⟩ : ↥(FFModel.altDn 5).sec) ^
            (Multiplicative.toAdd (y.1 : PermMod 5) 0).val *
          (⟨d5w 1, d5w_mem 1⟩ : ↥(FFModel.altDn 5).sec) ^
            (Multiplicative.toAdd (y.1 : PermMod 5) 1).val *
          (⟨d5w 2, d5w_mem 2⟩ : ↥(FFModel.altDn 5).sec) ^
            (Multiplicative.toAdd (y.1 : PermMod 5) 2).val *
          (⟨d5w 3, d5w_mem 3⟩ : ↥(FFModel.altDn 5).sec) ^
            (Multiplicative.toAdd (y.1 : PermMod 5) 3).val := by
      apply Subtype.ext
      exact hy
    rw [hy']
    exact C.mul_mem (C.mul_mem (C.mul_mem (C.pow_mem (hgen 0) _) (C.pow_mem (hgen 1) _))
      (C.pow_mem (hgen 2) _)) (C.pow_mem (hgen 3) _)
  intro w hw
  set u : ↥(⊤ : Subgroup ↥W) := ⟨⟨w, hw⟩, Subgroup.mem_top _⟩ with hu
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β u)
  obtain ⟨d, hdD, hd⟩ := Subgroup.mem_comap.mp (hCtop y)
  have hdu : d = u := by
    have h1 : β (d⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, hd]
      show (QuotientGroup.mk' _ y)⁻¹ * β u = 1
      rw [QuotientGroup.mk'_apply, hy, inv_mul_cancel]
    have h2 := (hβk (d⁻¹ * u)).mp h1
    rw [Subgroup.mem_bot] at h2
    have h3 : d⁻¹ * u = 1 := Subtype.ext h2
    exact (inv_mul_eq_one.mp h3)
  rw [hdu] at hdD
  exact hdD

theorem IsA5ModuleSum.commutator_eq {L W : Subgroup G} (h : IsA5ModuleSum L W) : ⁅W, L⁆ = W := by
  rcases h with h | ⟨W₁, W₂, h1, h2, -, hsup⟩
  · exact h.commutator_eq
  · apply le_antisymm
    · rw [← hsup]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((le_inf h1.1 h2.1).trans (Subgroup.inf_normalizer_le_normalizer_sup W₁ W₂))
    · rw [← hsup]
      refine sup_le ?_ ?_
      · calc W₁ = ⁅W₁, L⁆ := h1.commutator_eq.symm
          _ ≤ ⁅W₁ ⊔ W₂, L⁆ := Subgroup.commutator_mono le_sup_left le_rfl
      · calc W₂ = ⁅W₂, L⁆ := h2.commutator_eq.symm
          _ ≤ ⁅W₁ ⊔ W₂, L⁆ := Subgroup.commutator_mono le_sup_right le_rfl

theorem IsA5ModuleSum.commutator {L W : Subgroup G} (h : IsA5ModuleSum L W) :
    IsA5ModuleSum L ⁅W, L⁆ := by
  rw [h.commutator_eq]
  exact h

end Inside

end CFSG.Quasithin.H13
