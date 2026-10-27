module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKSD
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKCoord
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinA
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKTens

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise
open Matrix

theorem natural_sum_embedding' {Γ : Type*} [Group Γ] {m n j k : ℕ} (hm : 2 ≤ m) (hn : n < 2 * m)
    (hk : 0 < k) (ρ : Γ →* GL (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (σ : Γ →* GL (Fin n) (ZMod 2))
    (ϑ : (Fin k → Fin m → ZMod 2) →+ (Fin j → Fin n → ZMod 2)) (hϑ : Function.Injective ϑ)
    (hequi : ∀ (γ : Γ) (t : Fin k → Fin m → ZMod 2) (i : Fin j),
      ϑ (fun s => (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) i =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ϑ t i)) :
    ∃ (Φ₀ : (Fin m → ZMod 2) →+ (Fin n → ZMod 2)) (c : Fin k → Fin j → ZMod 2),
      Function.Injective Φ₀ ∧ ∀ (t : Fin k → Fin m → ZMod 2) (i : Fin j),
        ϑ t i = ∑ s, c s i • Φ₀ (t s) := by
  classical
  let Φ : Fin j → Fin k → (Fin m → ZMod 2) →+ (Fin n → ZMod 2) := fun i s =>
    (Pi.evalAddMonoidHom (fun _ : Fin j => Fin n → ZMod 2) i).comp
      (ϑ.comp (AddMonoidHom.single (fun _ : Fin k => Fin m → ZMod 2) s))
  have hΦ : ∀ i s x, Φ i s x = ϑ (Pi.single s x) i := fun i s x => rfl
  have hsingle : ∀ (γ : Γ) (s : Fin k) (x : Fin m → ZMod 2),
      (fun s' => (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        ((Pi.single s x : Fin k → Fin m → ZMod 2) s')) =
        (Pi.single s ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) :
          Fin k → Fin m → ZMod 2) := by
    intro γ s x
    funext s'
    by_cases h : s' = s
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hΦequi : ∀ i s (γ : Γ) x,
      Φ i s ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ i s x) := by
    intro i s γ x
    rw [hΦ, hΦ, ← hsingle γ s x]
    exact hequi γ _ i
  have hsome : ∃ i s, Φ i s ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    have hzero : ∀ t, ϑ t = 0 := by
      intro t
      have ht : t = ∑ s, (Pi.single s (t s) : Fin k → Fin m → ZMod 2) :=
        (Finset.univ_sum_single t).symm
      funext i
      rw [ht, map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [← hΦ, hcon i s]
      rfl
    have h1 : (Pi.single (⟨0, hk⟩ : Fin k)
        (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) :
        Fin k → Fin m → ZMod 2) = 0 := by
      apply hϑ
      rw [map_zero]
      exact hzero _
    have h2 := congrFun (congrFun h1 ⟨0, hk⟩) ⟨0, by omega⟩
    simp at h2
  obtain ⟨i₀, s₀, h0⟩ := hsome
  have hall : ∀ i s, Φ i s = 0 ∨ Φ i s = Φ i₀ s₀ := by
    intro i s
    rcases natural_hom_zero_or_eq hm hn ρ hρ σ (Φ i s) (Φ i₀ s₀) (hΦequi i s) (hΦequi i₀ s₀) with
      h | h | h
    · exact Or.inl h
    · exact absurd h h0
    · exact Or.inr h
  refine ⟨Φ i₀ s₀, fun s i => if Φ i s = 0 then 0 else 1,
    natural_hom_injective ρ hρ σ _ (hΦequi i₀ s₀) h0, ?_⟩
  intro t i
  have ht : t = ∑ s, (Pi.single s (t s) : Fin k → Fin m → ZMod 2) :=
    (Finset.univ_sum_single t).symm
  have hsum : ϑ t i = ∑ s, Φ i s (t s) := by
    conv_lhs => rw [ht, map_sum]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun s _ => (hΦ i s (t s)).symm
  rw [hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show Φ i s (t s) = (if Φ i s = 0 then (0 : ZMod 2) else 1) • Φ i₀ s₀ (t s)
  rcases hall i s with h | h
  · rw [if_pos h, h]
    simp
  · have hne : Φ i s ≠ 0 := by rw [h]; exact h0
    rw [if_neg hne, h]
    simp


section VTensor

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k n j : ℕ}

theorem exists_V_tensor (hN31 : NotC31) (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hd : NoSumBigData G T M L Mm I H K m k) (hnm : n < 2 * m) (hk2 : 2 ≤ k)
    (D : StdData G T L I K m k n j) :
    ∃ w₀ w₁ : Fin j → ZMod 2, w₀ ≠ 0 ∧ w₁ ≠ 0 ∧ w₁ ≠ w₀ ∧
      (∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
        ∃ v ∈ vV T L, coG D v = tens a w₀) ∧
      (∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
        ∃ v ∈ vV T L, coG D v = tens a w₁) := by
  classical
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hVU := vV_le_uZero hN31 h22 h27 hd
  obtain ⟨-, -, -, hm34, hmk, -, -, hsum⟩ := id hd
  have hm2 : 2 ≤ m := by rcases hm34 with h | h <;> omega
  have hk0 : 0 < k := by omega
  have hAnorm : perfectCore (L ⊓ H) ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (vV T L : Set G) := by
    obtain ⟨_, _, _, hA, _⟩ := id hsum
    exact hA
  have hnormL : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (vV T L : Set G) :=
    le_sup_left.trans hAnorm
  obtain ⟨ρ, βV, hρs, hβVb, hβVe⟩ := V_coords_of_isSum hc hsum
  let eV : ↥(vV T L) ≃* Multiplicative (Fin k → Fin m → ZMod 2) :=
    MulEquiv.ofBijective βV hβVb
  let incl : ↥(vV T L) →* ↥(uZero I K) := Subgroup.inclusion hVU
  let θ : Multiplicative (Fin k → Fin m → ZMod 2) →* Multiplicative (Fin j → Fin n → ZMod 2) :=
    D.β.comp (incl.comp eV.symm.toMonoidHom)
  let ϑ : (Fin k → Fin m → ZMod 2) →+ (Fin j → Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun t => Multiplicative.toAdd (θ (Multiplicative.ofAdd t)))
      (fun a b => by simp [ofAdd_add, map_mul, toAdd_mul])
  have hϑ : ∀ t, ϑ t = Multiplicative.toAdd (D.β (incl (eV.symm (Multiplicative.ofAdd t)))) :=
    fun t => rfl
  have hϑinj : Function.Injective ϑ := by
    intro t t' h
    have h1 : D.β (incl (eV.symm (Multiplicative.ofAdd t))) =
        D.β (incl (eV.symm (Multiplicative.ofAdd t'))) := by
      apply Multiplicative.toAdd.injective
      exact h
    have h2 := D.bij.1 h1
    have h3 : eV.symm (Multiplicative.ofAdd t) = eV.symm (Multiplicative.ofAdd t') :=
      Subgroup.inclusion_injective hVU h2
    exact Multiplicative.ofAdd.injective (eV.symm.injective h3)
  let σ : ↥(perfectCore (L ⊓ H)) →* GL (Fin n) (ZMod 2) :=
    D.α.comp (Subgroup.inclusion hc.LH_le)
  have hϑequi : ∀ (γ : ↥(perfectCore (L ⊓ H))) (t : Fin k → Fin m → ZMod 2) (i : Fin j),
      ϑ (fun s => ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) i =
        ((σ γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ϑ t i) := by
    intro γ t i
    set u : ↥(vV T L) := eV.symm (Multiplicative.ofAdd t) with hu
    have hmem : (γ : G) * (u : G) * (γ : G)⁻¹ ∈ vV T L :=
      (Subgroup.mem_normalizer_iff.mp (hnormL γ.2) (u : G)).mp u.2
    set v : ↥(vV T L) := ⟨(γ : G) * (u : G) * (γ : G)⁻¹, hmem⟩ with hv
    have hvγ : (v : G) = (γ : G) * (u : G) * (γ : G)⁻¹ := rfl
    have hβu : βV u = Multiplicative.ofAdd t := by
      have : eV u = Multiplicative.ofAdd t := by
        rw [hu]
        exact eV.apply_symm_apply _
      exact this
    have hβv : βV v = Multiplicative.ofAdd (fun s =>
        ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) := by
      apply Multiplicative.toAdd.injective
      funext s
      rw [hβVe γ u v hvγ s, hβu]
      rfl
    have hvu : v = eV.symm (Multiplicative.ofAdd (fun s =>
        ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s))) := by
      rw [MulEquiv.eq_symm_apply]
      exact hβv
    rw [hϑ, hϑ, ← hvu]
    have h := D.equi ⟨(γ : G), hc.LH_le γ.2⟩ (incl u) (incl v) hvγ i
    exact h
  obtain ⟨Φ₀, c, hΦinj, hϑsum⟩ := natural_sum_embedding' hm2 hnm hk0 ρ hρs σ ϑ hϑinj hϑequi
  let vOf : (Fin k → Fin m → ZMod 2) → G := fun t => ((eV.symm (Multiplicative.ofAdd t) : ↥(vV T L)) : G)
  have hvOf_mem : ∀ t, vOf t ∈ vV T L := fun t => (eV.symm (Multiplicative.ofAdd t)).2
  have hcoG_vOf : ∀ t, coG D (vOf t) = ϑ t := by
    intro t
    have h1 : vOf t ∈ uZero I K := hVU (hvOf_mem t)
    have : (⟨vOf t, h1⟩ : ↥(uZero I K)) = incl (eV.symm (Multiplicative.ofAdd t)) := rfl
    rw [coG_of_mem D ⟨vOf t, h1⟩, this, hϑ]
  have hrange : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) → ∃ x, Φ₀ x = a := by
    intro a ha
    obtain ⟨v, hvV, i, hvi⟩ := D.cover a ha
    set t : Fin k → Fin m → ZMod 2 := Multiplicative.toAdd (βV ⟨(v : G), hvV⟩) with ht
    have h1 : eV.symm (Multiplicative.ofAdd t) = ⟨(v : G), hvV⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h2 : ϑ t i = Multiplicative.toAdd (D.β v) i := by
      rw [hϑ, h1]
      rfl
    rw [hϑsum t i, hvi] at h2
    have hmem : ∑ s, c s i • Φ₀ (t s) ∈ Φ₀.range := by
      refine AddSubgroup.sum_mem _ fun s _ => ?_
      have hcs : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases hcs (c s i) with h | h
      · rw [h, zero_smul]
        exact AddSubgroup.zero_mem _
      · rw [h, one_smul]
        exact ⟨t s, rfl⟩
    rw [h2] at hmem
    exact hmem
  set s₀ : Fin k := ⟨0, hk0⟩ with hs₀
  set s₁ : Fin k := ⟨1, by omega⟩ with hs₁
  have hs01 : s₁ ≠ s₀ := by
    intro h
    have := congrArg Fin.val h
    simp [hs₀, hs₁] at this
  set x₀ : Fin m → ZMod 2 := Pi.single ⟨0, by omega⟩ 1 with hx₀
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [hx₀] at this
  have hsingle : ∀ (s : Fin k) (x : Fin m → ZMod 2),
      coG D (vOf (Pi.single s x)) = tens (Φ₀ x) (c s) := by
    intro s x
    rw [hcoG_vOf]
    funext i
    rw [hϑsum]
    simp only [tens_apply]
    rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hs'
      simp [Pi.single_eq_of_ne hs']
    · intro h
      exact absurd (Finset.mem_univ s) h
  have hcne : ∀ s : Fin k, c s ≠ 0 := by
    intro s h0
    have h1 : ϑ (Pi.single s x₀) = ϑ 0 := by
      rw [map_zero]
      funext i
      rw [hϑsum]
      simp only [Pi.zero_apply]
      rw [Finset.sum_eq_single s]
      · rw [h0]
        simp
      · intro s' _ hs'
        simp [Pi.single_eq_of_ne hs']
      · intro h
        exact absurd (Finset.mem_univ s) h
    have h2 := hϑinj h1
    have h3 := congrFun (congrFun h2 s) ⟨0, by omega⟩
    simp [hx₀] at h3
  have hcdiff : c s₁ ≠ c s₀ := by
    intro h
    have h1 : ϑ (Pi.single s₁ x₀) = ϑ (Pi.single s₀ x₀) := by
      rw [← hcoG_vOf, ← hcoG_vOf, hsingle, hsingle, h]
    have h2 := hϑinj h1
    have h3 := congrFun (congrFun h2 s₁) ⟨0, by omega⟩
    simp [hx₀, Pi.single_eq_of_ne hs01] at h3
  refine ⟨c s₀, c s₁, hcne s₀, hcne s₁, hcdiff, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx⟩ := hrange a ha
    exact ⟨vOf (Pi.single s₀ x), hvOf_mem _, by rw [hsingle, hx]⟩
  · intro a ha
    obtain ⟨x, hx⟩ := hrange a ha
    exact ⟨vOf (Pi.single s₁ x), hvOf_mem _, by rw [hsingle, hx]⟩

end VTensor

end CFSG.Quasithin.H13.Ch4.NSB
