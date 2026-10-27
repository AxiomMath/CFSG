module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Pencil
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Minus4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.RankThree.GF2n

namespace HS6

section Glue

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q₀ : QuadraticForm K W} {Ĝ : Type} [Group Ĝ]

theorem pencil_glue_false {s : ℕ} (hs : 2 ≤ s) (hq : Nat.card K = 2 ^ s) (hmin : IsMinus Q₀ 2)
    (N : Type) [CommGroup N] [Finite N] (ν : N →* Ĝ) (hν : Function.Injective ν)
    (ε : Multiplicative W →* Ĝ) (hε : Function.Injective ε)
    (hN2 : ∀ n : N, n * n = 1) (hNcard : Nat.card N = Nat.card K)
    (hcomm : ∀ (n : N) (w : Multiplicative W), ν n * ε w = ε w * ν n)
    (hdisj : ∀ (n : N) (w : Multiplicative W), ν n = ε w → n = 1)
    (A Hh : Subgroup Ĝ) (hA : ∀ x, x ∈ A ↔ ∃ (n : N) (w : Multiplicative W), x = ν n * ε w)
    (hHA : ∀ h ∈ Hh, ∀ x ∈ A, h * x * h⁻¹ ∈ A)
    (hTI : ∀ h ∈ Hh, conjSubgroup h ν.range ≠ ν.range →
      ν.range ⊓ conjSubgroup h ν.range = ⊥)
    (hlineOf : ∀ h ∈ Hh, conjSubgroup h ν.range ≠ ν.range →
      ∃ w₀ : W, Q₀ w₀ = 0 ∧ w₀ ≠ 0 ∧
        conjSubgroup h ν.range ≤ ν.range ⊔ (lineGrp K w₀).map ε)
    (htrans : ∀ w w' : W, Q₀ w = 0 → w ≠ 0 → Q₀ w' = 0 → w' ≠ 0 →
      ∃ h ∈ Hh, (∀ n : N, h * ν n * h⁻¹ = ν n) ∧
        conjSubgroup h ((lineGrp K w).map ε) = (lineGrp K w').map ε)
    (htorus : ∀ w : W, Q₀ w = 0 → w ≠ 0 → ∀ c : K, c ≠ 0 →
      ∃ h ∈ Hh, (∀ n : N, h * ν n * h⁻¹ = ν n) ∧
        ∀ a : K, h * ε (Multiplicative.ofAdd (a • w)) * h⁻¹ =
          ε (Multiplicative.ofAdd ((c * a) • w)))
    (hnontriv : ∃ h ∈ Hh, conjSubgroup h ν.range ≠ ν.range) : False := by
  classical
  haveI : Finite W := Module.finite_of_finite K
  let Φ : N × Multiplicative W →* Ĝ := MonoidHom.mk' (fun p => ν p.1 * ε p.2) (fun p q => by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc ν p.1 * ν q.1 * (ε p.2 * ε q.2) = ν p.1 * (ν q.1 * ε p.2) * ε q.2 := by
          simp only [mul_assoc]
      _ = ν p.1 * (ε p.2 * ν q.1) * ε q.2 := by rw [hcomm q.1 p.2]
      _ = ν p.1 * ε p.2 * (ν q.1 * ε q.2) := by simp only [mul_assoc])
  have hΦ : ∀ p, Φ p = ν p.1 * ε p.2 := fun p => rfl
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    rw [hΦ, hΦ] at hpq
    have h1 : ν (q.1⁻¹ * p.1) = ε (q.2 * p.2⁻¹) := by
      rw [map_mul, map_inv, map_mul, map_inv]
      calc (ν q.1)⁻¹ * ν p.1 = (ν q.1)⁻¹ * (ν p.1 * ε p.2) * (ε p.2)⁻¹ := by group
        _ = (ν q.1)⁻¹ * (ν q.1 * ε q.2) * (ε p.2)⁻¹ := by rw [hpq]
        _ = ε q.2 * (ε p.2)⁻¹ := by group
    have h2 : q.1⁻¹ * p.1 = 1 := hdisj _ _ h1
    have h3 : p.1 = q.1 := (inv_mul_eq_one.mp h2).symm
    have h4 : ε p.2 = ε q.2 := by
      have := hpq
      rw [h3] at this
      exact mul_left_cancel this
    exact Prod.ext h3 (hε h4)
  have hΦA : ∀ p, Φ p ∈ A := fun p => (hA _).mpr ⟨p.1, p.2, rfl⟩
  let Φe : N × Multiplicative W ≃* ↥A :=
    MulEquiv.ofBijective (Φ.codRestrict A hΦA) ⟨fun p q h => hΦinj (congrArg Subtype.val h),
      fun x => by
        obtain ⟨n, w, hx⟩ := (hA x).mp x.2
        exact ⟨(n, w), Subtype.ext hx.symm⟩⟩
  have hΦe : ∀ p, (Φe p : Ĝ) = Φ p := fun p => rfl
  have hHle : Hh ≤ Subgroup.normalizer (A : Set Ĝ) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hHA h hh x hx
    · intro hx
      have := hHA h⁻¹ (Hh.inv_mem hh) _ hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  let ρ : ↥Hh →* MulAut (N × Multiplicative W) :=
    (MulAut.congr Φe.symm).toMonoidHom.comp (A.normalizerMonoidHom.comp (Subgroup.inclusion hHle))
  have hρ : ∀ (h : ↥Hh) (x : N × Multiplicative W), Φ (ρ h x) = (h : Ĝ) * Φ x * (h : Ĝ)⁻¹ := by
    intro h x
    have h1 : (Φe (ρ h x) : Ĝ) = (h : Ĝ) * (Φe x : Ĝ) * (h : Ĝ)⁻¹ := by
      have : Φe (ρ h x) = A.normalizerMonoidHom (Subgroup.inclusion hHle h) (Φe x) := by
        show Φe (Φe.symm (A.normalizerMonoidHom (Subgroup.inclusion hHle h) (Φe x))) = _
        exact Φe.apply_symm_apply _
      rw [this]
      rfl
    exact h1
  have hmapA : ∀ (h : ↥Hh) (S : Subgroup (N × Multiplicative W)),
      (mapA (ρ h) S).map Φ = conjSubgroup (h : Ĝ) (S.map Φ) := by
    intro h S
    ext y
    rw [mem_conjSubgroup]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨x, hx, ?_⟩
      have := hρ h x
      rw [show (ρ h) x = (ρ h : MulAut (N × Multiplicative W)) x from rfl] at this
      show Φ x = (h : Ĝ)⁻¹ * Φ (ρ h x) * (h : Ĝ)
      rw [hρ h x]
      group
    · rintro ⟨x, hx, hxy⟩
      refine ⟨ρ h x, ⟨x, hx, rfl⟩, ?_⟩
      rw [hρ h x, hxy]
      group
  have hinj : Function.Injective (Subgroup.map Φ : Subgroup (N × Multiplicative W) → _) :=
    Subgroup.map_injective hΦinj
  have himgN : (N0 N (Multiplicative W)).map Φ = ν.range := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp1 : p.2 = 1 := mem_N0.mp hp
      exact ⟨p.1, by rw [hΦ, hp1, map_one, mul_one]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(n, 1), mem_N0.mpr rfl, by rw [hΦ, map_one, mul_one]⟩
  have himgE : ∀ ℓ : Subgroup (Multiplicative W), (Esub N ℓ).map Φ = ℓ.map ε := by
    intro ℓ
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := mem_Esub.mp hp
      exact ⟨p.2, hp2, by rw [hΦ, hp1, map_one, one_mul]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(1, w), mem_Esub.mpr ⟨rfl, hw⟩, by rw [hΦ, map_one, one_mul]⟩
  have himgNs : ∀ ℓ : Subgroup (Multiplicative W), (Nsub N ℓ).map Φ = ν.range ⊔ ℓ.map ε := by
    intro ℓ
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      rw [hΦ]
      exact Subgroup.mul_mem_sup ⟨p.1, rfl⟩ ⟨p.2, mem_Nsub.mp hp, rfl⟩
    · refine sup_le ?_ ?_
      · rintro y ⟨n, rfl⟩
        exact ⟨(n, 1), mem_Nsub.mpr ℓ.one_mem, by rw [hΦ, map_one, mul_one]⟩
      · rintro y ⟨w, hw, rfl⟩
        exact ⟨(1, w), mem_Nsub.mpr hw, by rw [hΦ, map_one, one_mul]⟩
  have hfin : (singLines K Q₀).Finite := Set.toFinite _
  have hmemL : ∀ ℓ, ℓ ∈ hfin.toFinset ↔ ∃ w, Q₀ w = 0 ∧ w ≠ 0 ∧ ℓ = lineGrp K w := by
    intro ℓ
    rw [Set.Finite.mem_toFinset]
    rfl
  have hfix : ∀ (h : ↥Hh), (∀ n : N, (h : Ĝ) * ν n * (h : Ĝ)⁻¹ = ν n) →
      ∀ n : N, ρ h (n, 1) = (n, 1) := by
    intro h hh n
    apply hΦinj
    rw [hρ h (n, 1)]
    simp only [hΦ, map_one, mul_one]
    exact hh n
  have D : PencilData K N (Multiplicative W) hfin.toFinset ρ.range :=
    { cardN := hNcard
      N2 := hN2
      M2 := fun x => by
        have h2 : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
          rw [← two_smul K, CharTwo.two_eq_zero, zero_smul]
        exact Multiplicative.toAdd.injective (by rw [toAdd_mul, h2]; rfl)
      cardM := by
        rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative W ≃ W),
          Module.natCard_eq_pow_finrank (K := K), hmin.finrank_eq]
      cardLine := fun ℓ hℓ => by
        obtain ⟨w, -, hw0, rfl⟩ := (hmemL ℓ).mp hℓ
        exact card_lineGrp hw0
      infLine := fun ℓ hℓ ℓ' hℓ' hne => by
        obtain ⟨w, -, hw0, rfl⟩ := (hmemL ℓ).mp hℓ
        obtain ⟨w', -, hw0', rfl⟩ := (hmemL ℓ').mp hℓ'
        exact lineGrp_inf_eq_bot hw0 hw0' hne
      cardLines := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact ncard_singLines hmin
      lineSum := fun ℓ₀ h₀ ℓ₁ h₁ hne ℓ hℓ hle => by
        obtain ⟨w₀, hQ₀, hw₀, rfl⟩ := (hmemL ℓ₀).mp h₀
        obtain ⟨w₁, hQ₁, hw₁, rfl⟩ := (hmemL ℓ₁).mp h₁
        obtain ⟨w, hQ, hw, rfl⟩ := (hmemL ℓ).mp hℓ
        exact lineGrp_sum_of_isMinus hmin hQ₀ hQ₁ hQ hw₀ hw₁ hw hne hle
      span := fun ℓ₀ h₀ => by
        have h₀' : ℓ₀ ∈ singLines K Q₀ := (Set.Finite.mem_toFinset hfin).mp h₀
        have := singLines_span hmin h₀'
        simpa only [Set.Finite.mem_toFinset] using this
      TI := fun γ hγ hne => by
        obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hγ
        have hne' : conjSubgroup (h : Ĝ) ν.range ≠ ν.range := by
          intro hc
          apply hne
          apply hinj
          rw [hmapA, himgN, hc]
        have h1 := hTI h h.2 hne'
        apply hinj
        rw [Subgroup.map_inf_eq _ _ _ hΦinj, hmapA, himgN, h1, Subgroup.map_bot]
      lineOf := fun γ hγ hne => by
        obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hγ
        have hne' : conjSubgroup (h : Ĝ) ν.range ≠ ν.range := by
          intro hc
          apply hne
          apply hinj
          rw [hmapA, himgN, hc]
        obtain ⟨w₀, hQ, hw0, hle⟩ := hlineOf h h.2 hne'
        refine ⟨lineGrp K w₀, (hmemL _).mpr ⟨w₀, hQ, hw0, rfl⟩, ?_⟩
        rw [← Subgroup.map_le_map_iff_of_injective hΦinj, hmapA, himgN, himgNs]
        exact hle
      trans := fun ℓ hℓ ℓ' hℓ' => by
        obtain ⟨w, hQ, hw0, rfl⟩ := (hmemL ℓ).mp hℓ
        obtain ⟨w', hQ', hw0', rfl⟩ := (hmemL ℓ').mp hℓ'
        obtain ⟨h, hh, hfixh, hline⟩ := htrans w w' hQ hw0 hQ' hw0'
        refine ⟨ρ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, hfix ⟨h, hh⟩ hfixh, ?_⟩
        apply hinj
        rw [hmapA, himgE, himgE]
        exact hline
      torus := fun ℓ hℓ => by
        obtain ⟨w, hQ, hw0, rfl⟩ := (hmemL ℓ).mp hℓ
        refine ⟨(lineEquiv hw0).symm, fun c hc => ?_⟩
        obtain ⟨h, hh, hfixh, hact⟩ := htorus w hQ hw0 c hc
        refine ⟨ρ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, hfix ⟨h, hh⟩ hfixh, fun e => ?_⟩
        set a : K := Multiplicative.toAdd ((lineEquiv hw0).symm e) with ha
        have he : (e : Multiplicative W) = Multiplicative.ofAdd (a • w) := by
          have h1 : e = lineEquiv hw0 (Multiplicative.ofAdd a) := by
            rw [ha, ofAdd_toAdd, MulEquiv.apply_symm_apply]
          rw [h1]
          rfl
        apply hΦinj
        rw [hρ ⟨h, hh⟩ _, hΦ, hΦ]
        simp only [map_one, one_mul]
        rw [he]
        rw [hact a]
        have h2 : (((lineEquiv hw0).symm).symm (Multiplicative.ofAdd (c * a)) :
            lineGrp K w) = lineEquiv hw0 (Multiplicative.ofAdd (c * a)) := rfl
        have : ((((lineEquiv hw0).symm).symm (Multiplicative.ofAdd (c * Multiplicative.toAdd
            ((lineEquiv hw0).symm e))) : lineGrp K w) : Multiplicative W) =
            Multiplicative.ofAdd ((c * a) • w) := by
          rw [← ha]
          rfl
        rw [this]
      nontriv := by
        obtain ⟨h, hh, hne⟩ := hnontriv
        refine ⟨ρ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, fun hc => hne ?_⟩
        have := congrArg (Subgroup.map Φ) hc
        rwa [hmapA, himgN] at this }
  exact D.false_of_data hs hq

theorem pencil_glue_false' [Finite Ĝ] {s : ℕ} (hs : 2 ≤ s) (hq : Nat.card K = 2 ^ s)
    (hmin : IsMinus Q₀ 2) (N0 : Subgroup Ĝ)
    (hN0comm : ∀ n ∈ N0, ∀ n' ∈ N0, n * n' = n' * n) (hN0sq : ∀ n ∈ N0, n * n = 1)
    (hN0card : Nat.card N0 = Nat.card K) (ε : Multiplicative W →* Ĝ)
    (hε : Function.Injective ε)
    (hcomm : ∀ n ∈ N0, ∀ w : Multiplicative W, n * ε w = ε w * n)
    (hdisj : ∀ n ∈ N0, ∀ w : Multiplicative W, n = ε w → n = 1)
    (A Hh : Subgroup Ĝ) (hA : ∀ x, x ∈ A ↔ ∃ n ∈ N0, ∃ w : Multiplicative W, x = n * ε w)
    (hHA : ∀ h ∈ Hh, ∀ x ∈ A, h * x * h⁻¹ ∈ A)
    (hTI : ∀ h ∈ Hh, conjSubgroup h N0 ≠ N0 → N0 ⊓ conjSubgroup h N0 = ⊥)
    (hlineOf : ∀ h ∈ Hh, conjSubgroup h N0 ≠ N0 →
      ∃ w₀ : W, Q₀ w₀ = 0 ∧ w₀ ≠ 0 ∧ conjSubgroup h N0 ≤ N0 ⊔ (lineGrp K w₀).map ε)
    (htrans : ∀ w w' : W, Q₀ w = 0 → w ≠ 0 → Q₀ w' = 0 → w' ≠ 0 →
      ∃ h ∈ Hh, (∀ n ∈ N0, h * n * h⁻¹ = n) ∧
        conjSubgroup h ((lineGrp K w).map ε) = (lineGrp K w').map ε)
    (htorus : ∀ w : W, Q₀ w = 0 → w ≠ 0 → ∀ c : K, c ≠ 0 →
      ∃ h ∈ Hh, (∀ n ∈ N0, h * n * h⁻¹ = n) ∧
        ∀ a : K, h * ε (Multiplicative.ofAdd (a • w)) * h⁻¹ =
          ε (Multiplicative.ofAdd ((c * a) • w)))
    (hnontriv : ∃ h ∈ Hh, conjSubgroup h N0 ≠ N0) : False := by
  letI : CommGroup ↥N0 :=
    { (inferInstance : Group ↥N0) with mul_comm := fun a b => Subtype.ext (hN0comm a a.2 b b.2) }
  have hr : N0.subtype.range = N0 := Subgroup.range_subtype N0
  refine pencil_glue_false hs hq hmin ↥N0 N0.subtype N0.subtype_injective ε hε
    (fun n => Subtype.ext (hN0sq n n.2)) hN0card (fun n w => hcomm n n.2 w)
    (fun n w h => Subtype.ext (hdisj n n.2 w h)) A Hh (fun x => ?_) hHA ?_ ?_ ?_ ?_ ?_
  · rw [hA x]
    exact ⟨fun ⟨n, hn, w, h⟩ => ⟨⟨n, hn⟩, w, h⟩, fun ⟨n, w, h⟩ => ⟨n, n.2, w, h⟩⟩
  · rw [hr]
    exact hTI
  · rw [hr]
    exact hlineOf
  · intro w w' hw hw0 hw' hw0'
    obtain ⟨h, hh, hfix, hl⟩ := htrans w w' hw hw0 hw' hw0'
    exact ⟨h, hh, fun n => hfix n n.2, hl⟩
  · intro w hw hw0 c hc
    obtain ⟨h, hh, hfix, hact⟩ := htorus w hw hw0 c hc
    exact ⟨h, hh, fun n => hfix n n.2, hact⟩
  · rw [hr]
    exact hnontriv

end Glue

end HS6

end CFSG.RankThree.GF2n.Stroth80
