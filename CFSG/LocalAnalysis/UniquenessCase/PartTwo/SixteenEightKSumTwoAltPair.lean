module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private lemma s16k_exists_three_const {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ZMod 2 × ZMod 2) (h : 8 < Fintype.card α) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by
  obtain ⟨y, hy⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := f) (n := 2) (by
      have hcard : Fintype.card (ZMod 2 × ZMod 2) = 4 := by simp [ZMod.card]
      rw [hcard]; omega)
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact ⟨a, b, c, hab, hac, hbc, ha.trans hb.symm, ha.trans hc.symm⟩

private lemma s16k_permAct_toAdd_eq_self {n : ℕ} (τ : Equiv.Perm (Fin n)) (w : G6.PermMod n)
    (h : ∀ i, Multiplicative.toAdd w (τ i) = Multiplicative.toAdd w i) :
    G6.permAct n τ w = w := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  simpa using (h (τ⁻¹ i)).symm

private lemma s16k_swap_mul_swap_maps_const {α β : Type*} [DecidableEq α] {p q r : α}
    {φ : α → β} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hpqφ : φ p = φ q)
    (hprφ : φ p = φ r) :
    ∀ i, φ ((Equiv.swap p q * Equiv.swap p r) i) = φ i := by
  intro i
  by_cases hip : i = p
  · rw [hip, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hpr.symm hqr.symm]
    exact hprφ.symm
  · by_cases hiq : i = q
    · rw [hiq, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpq.symm hqr,
        Equiv.swap_apply_right]
      exact hpqφ
    · by_cases hir : i = r
      · rw [hir, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
        exact hpqφ.symm.trans hprφ
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hip hir,
          Equiv.swap_apply_of_ne_of_ne hip hiq]

theorem s16k_alt_pair_fix {n : ℕ} (hn : 12 ≤ n) (m₁ m₂ : (FFModel.altDn n).Amb)
    (h₁ : m₁ ∈ (FFModel.altDn n).sec) (h₂ : m₂ ∈ (FFModel.altDn n).sec)
    (hm : m₁ ∉ (FFModel.altDn n).ker ∨ m₂ ∉ (FFModel.altDn n).ker) :
    ∃ B : Subgroup (FFModel.altDn n).Gam, IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ γ ∈ B,
      (FFModel.altDn n).act γ m₁ * m₁⁻¹ ∈ (FFModel.altDn n).ker ∧
        (FFModel.altDn n).act γ m₂ * m₂⁻¹ ∈ (FFModel.altDn n).ker := by
  classical
  set φ : Fin n → ZMod 2 × ZMod 2 :=
    fun i => (Multiplicative.toAdd m₁ i, Multiplicative.toAdd m₂ i) with hφ
  obtain ⟨a, b, c, hab, hac, hbc, hfab, hfac⟩ :=
    s16k_exists_three_const φ (by rw [Fintype.card_fin]; omega)
  set T1 : Finset (Fin n) := {a, b, c} with hT1
  have hT1c : T1.card = 3 := by simp [hT1, hab, hac, hbc]
  have hT1mem : ∀ x, x ∈ T1 ↔ x = a ∨ x = b ∨ x = c := by intro x; rw [hT1]; simp
  have hcard : Fintype.card {x : Fin n // x ∉ T1} = n - 3 := by
    rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ T1), Fintype.card_fin,
      Fintype.card_coe, hT1c]
  obtain ⟨d, e, g, hde, hdg, heg, hfde, hfdg⟩ :=
    s16k_exists_three_const (fun x : {x : Fin n // x ∉ T1} => φ x.1) (by rw [hcard]; omega)
  have hde' : d.1 ≠ e.1 := fun h => hde (Subtype.ext h)
  have hdg' : d.1 ≠ g.1 := fun h => hdg (Subtype.ext h)
  have heg' : e.1 ≠ g.1 := fun h => heg (Subtype.ext h)
  have hdT1 : d.1 ∉ T1 := d.2
  have heT1 : e.1 ∉ T1 := e.2
  have hgT1 : g.1 ∉ T1 := g.2
  set T2 : Finset (Fin n) := {d.1, e.1, g.1} with hT2
  have hT2mem : ∀ x, x ∈ T2 ↔ x = d.1 ∨ x = e.1 ∨ x = g.1 := by intro x; rw [hT2]; simp
  set σ₁ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c with hσ₁
  set σ₂ : Equiv.Perm (Fin n) := Equiv.swap d.1 e.1 * Equiv.swap d.1 g.1 with hσ₂
  have h3₁ : σ₁.IsThreeCycle := by
    rw [hσ₁]; exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have h3₂ : σ₂.IsThreeCycle := by
    rw [hσ₂]; exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hde' hdg' heg'
  have hout1 : ∀ x, x ∉ T1 → σ₁ x = x := by
    intro x hx
    have hxa : x ≠ a := fun h => hx ((hT1mem x).mpr (Or.inl h))
    have hxb : x ≠ b := fun h => hx ((hT1mem x).mpr (Or.inr (Or.inl h)))
    have hxc : x ≠ c := fun h => hx ((hT1mem x).mpr (Or.inr (Or.inr h)))
    simp [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxc,
      Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hout2 : ∀ x, x ∉ T2 → σ₂ x = x := by
    intro x hx
    have hxd : x ≠ d.1 := fun h => hx ((hT2mem x).mpr (Or.inl h))
    have hxe : x ≠ e.1 := fun h => hx ((hT2mem x).mpr (Or.inr (Or.inl h)))
    have hxg : x ≠ g.1 := fun h => hx ((hT2mem x).mpr (Or.inr (Or.inr h)))
    simp [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxd hxg,
      Equiv.swap_apply_of_ne_of_ne hxd hxe]
  let g₁ : ↥(alternatingGroup (Fin n)) := ⟨σ₁, h3₁.mem_alternatingGroup⟩
  let g₂ : ↥(alternatingGroup (Fin n)) := ⟨σ₂, h3₂.mem_alternatingGroup⟩
  let P : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {τ | ∀ i, φ (τ i) = φ i}
      mul_mem' := by
        intro a b ha hb i
        show φ ((a * b) i) = φ i
        rw [Equiv.Perm.mul_apply, ha (b i), hb i]
      one_mem' := by intro i; rfl
      inv_mem' := by
        intro a ha i
        show φ ((a⁻¹) i) = φ i
        have h := ha (a⁻¹ i)
        simpa using h.symm }
  have hσ₁P : σ₁ ∈ P := s16k_swap_mul_swap_maps_const hab hac hbc hfab hfac
  have hσ₂P : σ₂ ∈ P := s16k_swap_mul_swap_maps_const hde' hdg' heg' hfde hfdg
  let B : Subgroup (FFModel.altDn n).Gam := Subgroup.zpowers g₁ ⊔ Subgroup.zpowers g₂
  have hBP : B.map (Subgroup.subtype (alternatingGroup (Fin n))) ≤ P := by
    show (Subgroup.zpowers g₁ ⊔ Subgroup.zpowers g₂).map
        (Subgroup.subtype (alternatingGroup (Fin n))) ≤ P
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hσ₁P
    · rw [Subgroup.zpowers_le]; exact hσ₂P
  have hfix : ∀ γ ∈ B, ∀ i, φ (γ.val i) = φ i := by
    intro γ hγ
    have hmem : γ.val ∈ B.map (Subgroup.subtype (alternatingGroup (Fin n))) :=
      Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    exact hBP hmem
  have hord₁ : orderOf g₁ = 3 :=
    (Subgroup.orderOf_mk σ₁ h3₁.mem_alternatingGroup).trans h3₁.orderOf
  have hord₂ : orderOf g₂ = 3 :=
    (Subgroup.orderOf_mk σ₂ h3₂.mem_alternatingGroup).trans h3₂.orderOf
  have hpow₁ : g₁ ^ 3 = 1 := by rw [← hord₁]; exact pow_orderOf_eq_one g₁
  have hpow₂ : g₂ ^ 3 = 1 := by rw [← hord₂]; exact pow_orderOf_eq_one g₂
  have hg₁ne : g₁ ≠ 1 := fun h => h3₁.ne_one (Subtype.ext_iff.mp h)
  have hdisj : Equiv.Perm.Disjoint σ₁ σ₂ := by
    intro x
    by_cases hx : x ∈ T1
    · right
      apply hout2
      intro hx2
      rcases (hT2mem x).mp hx2 with h | h | h
      · exact hdT1 (h ▸ hx)
      · exact heT1 (h ▸ hx)
      · exact hgT1 (h ▸ hx)
    · left
      exact hout1 x hx
  have hcom : g₁ * g₂ = g₂ * g₁ := by
    apply Subtype.ext
    show σ₁ * σ₂ = σ₂ * σ₁
    exact hdisj.commute
  have hfixd : σ₁ d.1 = d.1 := hout1 d.1 hdT1
  have hσ₂d : σ₂ d.1 = g.1 := by
    rw [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hdg'.symm heg'.symm
  have hg₂notmem : g₂ ∉ Subgroup.zpowers g₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : σ₂ = σ₁ ^ k := by
      have hcoe := congrArg (fun x : ↥(alternatingGroup (Fin n)) =>
        (x : Equiv.Perm (Fin n))) hk
      simpa [Subgroup.coe_zpow] using hcoe.symm
    have hd2 : σ₂ d.1 = d.1 := by
      rw [hk']
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfixd k
    rw [hσ₂d] at hd2
    exact hdg' hd2.symm
  obtain ⟨hel, hcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers Nat.prime_three hpow₁ hpow₂
      hg₁ne hg₂notmem hcom
  haveI hGam : Finite (FFModel.altDn n).Gam :=
    inferInstanceAs (Finite ↥(alternatingGroup (Fin n)))
  haveI : Finite ↥B := Subtype.finite
  refine ⟨B, ?_, ?_, ?_⟩
  · exact hel.isPGroup
  · haveI : CFSG.IsElementaryAbelian 3 ↥B := hel.isElementaryAbelian
    refine CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (A := ↥B) (p := 3) ?_
    exact hcard
  · intro γ hγ
    have hfixγ := hfix γ hγ
    have hc₁ : ∀ i, Multiplicative.toAdd m₁ (γ.val i) = Multiplicative.toAdd m₁ i :=
      fun i => by simpa [hφ] using congrArg Prod.fst (hfixγ i)
    have hc₂ : ∀ i, Multiplicative.toAdd m₂ (γ.val i) = Multiplicative.toAdd m₂ i :=
      fun i => by simpa [hφ] using congrArg Prod.snd (hfixγ i)
    have hact₁ : (FFModel.altDn n).act γ m₁ = m₁ :=
      s16k_permAct_toAdd_eq_self γ.val m₁ hc₁
    have hact₂ : (FFModel.altDn n).act γ m₂ = m₂ :=
      s16k_permAct_toAdd_eq_self γ.val m₂ hc₂
    refine ⟨?_, ?_⟩
    · rw [hact₁, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [hact₂, mul_inv_cancel]; exact Subgroup.one_mem _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
