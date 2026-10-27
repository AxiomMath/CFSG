module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux3
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

section Abelian

variable [Finite Γ]

theorem exists_cyclic_of_abelian_chief {p : ℕ} (hp : p.Prime) {A X : Subgroup Γ}
    (hA : IsElemAbelian p A) (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X))
    (hmin : ∀ Y : Subgroup Γ, Y ≤ X → Admits A Y → Y = ⊥ ∨ Y = X) (hXne : X ≠ ⊥) :
    ∃ a ∈ A, A ≤ (A ⊓ Subgroup.centralizer (X : Set Γ)) ⊔ Subgroup.zpowers a := by
  by_contra hcon
  push Not at hcon
  set C := A ⊓ Subgroup.centralizer (X : Set Γ) with hC
  have hCA : C ≤ A := inf_le_left
  obtain ⟨E, hEA, hE1, hE2⟩ := exists_isCompl_of_le hp hA (D := C) (F := A) hCA le_rfl
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElemAbelian p E := ⟨isMulCommutative_of_le hA.1 hEA, fun x hx => hA.2 x (hEA hx)⟩
  have hEcard : p ^ 2 ≤ Nat.card E := by
    by_contra hlt
    push Not at hlt
    have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEel.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      omega
    have hdvd : Nat.card E ∣ p := by
      rw [hk]
      interval_cases k
      · simp
      · simp
    have hcyc : IsCyclic E := isCyclic_of_card_dvd_prime hdvd
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine hcon (g : Γ) (hEA g.2) ?_
    rw [← hE2]
    refine sup_le le_sup_left fun z hz => Subgroup.mem_sup_right ?_
    obtain ⟨k', hk'⟩ := hg ⟨z, hz⟩
    exact ⟨k', congrArg Subtype.val hk'⟩
  have hEX : A ⊓ E ≤ A := inf_le_left
  have hgen := iSup_centralizer_nonidentity hp hEel hEcard (fun e he => hAX (hEA he)) hcop
  apply hXne
  rw [← hgen, eq_bot_iff]
  refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
  have hAa : Admits A (X ⊓ Subgroup.centralizer {a}) := by
    have := admits_cenIn hA.1 hAX (S := Subgroup.zpowers a) (Subgroup.zpowers_le.mpr (hEA ha))
    unfold cenIn at this
    rwa [centralizer_zpowers_eq] at this
  rcases hmin _ inf_le_left hAa with h | h
  · rw [h]
  · exfalso
    have hX : X ≤ Subgroup.centralizer {a} := h ▸ inf_le_right
    have haC : a ∈ C := Subgroup.mem_inf.mpr ⟨hEA ha, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hX hx)⟩
    have : a ∈ C ⊓ E := Subgroup.mem_inf.mpr ⟨haC, ha⟩
    rw [hE1, Subgroup.mem_bot] at this
    exact ha1 this

end Abelian

theorem exists_actionHom {M N D : Subgroup Γ} [(N.subgroupOf M).Normal] (hNM : N ≤ M)
    (hDM : D ≤ Subgroup.normalizer (M : Set Γ)) (hDN : D ≤ Subgroup.normalizer (N : Set Γ)) :
    ∃ ρ : ↥D →* MulAut (↥M ⧸ N.subgroupOf M),
      ∀ d : ↥D, ρ d = 1 ↔ (d : Γ) ∈ sectionCentralizer N M := by
  let φ : ↥D →* MulAut ↥M := M.normalizerMonoidHom.comp (Subgroup.inclusion hDM)
  have hφ : ∀ (d : ↥D) (m : ↥M), ((φ d m : ↥M) : Γ) = (d : Γ) * m * (d : Γ)⁻¹ := fun d m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M (Subgroup.inclusion hDM d) m
  have hmapN : ∀ d : ↥D, ∀ n ∈ N.subgroupOf M, φ d n ∈ N.subgroupOf M := by
    intro d n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp (hDN d.2) n).mp hn
  have hmap : ∀ d : ↥D, (N.subgroupOf M).map (φ d : ↥M →* ↥M) = N.subgroupOf M := by
    intro d
    refine le_antisymm ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hmapN d n hn
    · intro z hz
      refine ⟨φ d⁻¹ z, hmapN d⁻¹ z hz, ?_⟩
      change φ d (φ d⁻¹ z) = z
      rw [← MulAut.mul_apply, ← map_mul]
      simp
  let ρ : ↥D →* MulAut (↥M ⧸ N.subgroupOf M) :=
    { toFun := fun d => QuotientGroup.congr (N.subgroupOf M) (N.subgroupOf M) (φ d) (hmap d)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | _ m => simp [QuotientGroup.congr_mk]
      map_mul' := by
        intro d₁ d₂
        ext q
        induction q using QuotientGroup.induction_on with
        | _ m =>
          simp only [MulAut.mul_apply, QuotientGroup.congr_mk, map_mul] }
  refine ⟨ρ, fun d => ?_⟩
  have hρ : ∀ m : ↥M, ρ d (QuotientGroup.mk m) = QuotientGroup.mk (φ d m) := fun m =>
    QuotientGroup.congr_mk (N.subgroupOf M) (N.subgroupOf M) (φ d) (hmap d) m
  have hMN : M ≤ Subgroup.normalizer (N : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp inferInstance
  constructor
  · intro h
    refine ⟨hDN d.2, hDM d.2, fun y hy => ?_⟩
    have h1 := hρ ⟨y, hy⟩
    rw [h, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : y⁻¹ * ((d : Γ) * y * (d : Γ)⁻¹) ∈ N := by
      have := hφ d ⟨y, hy⟩
      simpa [this] using h2
    have h4 := (Subgroup.mem_normalizer_iff.mp (hMN hy) _).mp h3
    have h5 : y * (y⁻¹ * ((d : Γ) * y * (d : Γ)⁻¹)) * y⁻¹ = ⁅(d : Γ), y⁆ := by
      simp only [commutatorElement_def]; group
    rw [← h5]
    exact h4
  · rintro ⟨-, -, h⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | _ m =>
      rw [hρ, MulAut.one_apply]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have h1 := h (m : Γ)⁻¹ (inv_mem m.2)
      have h2 : (((φ d m)⁻¹ * m : ↥M) : Γ) = ⁅(d : Γ), (m : Γ)⁻¹⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
        simp only [commutatorElement_def]; group
      rw [h2]
      exact h1

theorem exists_cyclic_acting {p : ℕ} {A M N D : Subgroup Γ} [(N.subgroupOf M).Normal]
    (hNM : N ≤ M) (hA : IsElemAbelian p A) (hDA : D ≤ A)
    (hDM : D ≤ Subgroup.normalizer (M : Set Γ)) (hDN : D ≤ Subgroup.normalizer (N : Set Γ))
    (hcyc : ∀ P : Subgroup (MulAut (↥M ⧸ N.subgroupOf M)), IsPGroup p P → IsCyclic P) :
    ∃ n ∈ D, D ≤ (D ⊓ sectionCentralizer N M) ⊔ Subgroup.zpowers n := by
  obtain ⟨ρ, hρ⟩ := exists_actionHom hNM hDM hDN
  have hDp : IsPGroup p D := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g (hDA g.2))⟩
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective hDp ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := (hcyc ρ.range hRp).exists_generator
  obtain ⟨n, hn⟩ := g.2
  refine ⟨n, n.2, fun d hd => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨ρ ⟨d, hd⟩, ⟨_, rfl⟩⟩
  have hk' : (g : MulAut (↥M ⧸ N.subgroupOf M)) ^ k = ρ ⟨d, hd⟩ := congrArg Subtype.val hk
  have hker : ρ (⟨d, hd⟩ * n ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, hn, ← hk', zpow_neg, mul_inv_cancel]
  have hmem := (hρ _).mp hker
  have hmem' : (d : Γ) * (n : Γ) ^ (-k) ∈ D ⊓ sectionCentralizer N M :=
    ⟨mul_mem hd (zpow_mem n.2 _), hmem⟩
  have : d = (d * (n : Γ) ^ (-k)) * (n : Γ) ^ k := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hmem')
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
