module

public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigDirect_conj_mem_sup {S T : Subgroup G} {r : G} (hS : ∀ s ∈ S, r * s * r⁻¹ ∈ S ⊔ T)
    (hT : ∀ t ∈ T, r * t * r⁻¹ ∈ S ⊔ T) : ∀ x ∈ S ⊔ T, r * x * r⁻¹ ∈ S ⊔ T := by
  intro x hx
  have hle : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj r).toMonoidHom :=
    sup_le (fun s hs => Subgroup.mem_comap.mpr (hS s hs))
      (fun t ht => Subgroup.mem_comap.mpr (hT t ht))
  exact hle hx

theorem bigDirect_conj_mem_commutator {P M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (P : Set G)) :
    ∀ m ∈ M, ∀ z ∈ ⁅P, P⁆, m * z * m⁻¹ ∈ ⁅P, P⁆ := by
  intro m hm
  have hle : ⁅P, P⁆ ≤ (⁅P, P⁆ : Subgroup G).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap]
    show m * ⁅x, y⁆ * m⁻¹ ∈ ⁅P, P⁆
    have hx' : m * x * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hM hm) x).mp hx
    have hy' : m * y * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hM hm) y).mp hy
    have e : m * ⁅x, y⁆ * m⁻¹ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx' hy'
  intro z hz
  exact hle hz

theorem bigDirect_P_le_M [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) : P ≤ M := by
  refine hc.P_le_Q.trans ?_
  rw [hc.hQ]
  exact (inSubgroup_pCore_two M).2.1

theorem bigDirect_conj_invariant {Q P F R A : Subgroup G} {e : G}
    (hRQ : ∀ r ∈ R, ∃ r' ∈ R, ∃ k ∈ Q, e⁻¹ * r * e = r' * k)
    (hFP : F ≤ P) (hAF : A ≤ F) (hPQ : ∀ k ∈ Q, ∀ x ∈ P, ⁅k, x⁆ ∈ A)
    (hRF : ∀ r ∈ R, ∀ f ∈ F, r * f * r⁻¹ ∈ F) :
    ∀ r ∈ R, ∀ x ∈ conjSubgroup e F, r * x * r⁻¹ ∈ conjSubgroup e F := by
  intro r hr x hx
  rw [mem_conjSubgroup] at hx ⊢
  obtain ⟨r', hr', k, hk, hrk⟩ := hRQ r hr
  have e1 : e⁻¹ * (r * x * r⁻¹) * e = (e⁻¹ * r * e) * (e⁻¹ * x * e) * (e⁻¹ * r * e)⁻¹ := by
    group
  rw [e1, hrk]
  have hkf : k * (e⁻¹ * x * e) * k⁻¹ ∈ F := by
    have h1 : ⁅k, e⁻¹ * x * e⁆ ∈ A := hPQ k hk _ (hFP hx)
    have h2 : k * (e⁻¹ * x * e) * k⁻¹ = ⁅k, e⁻¹ * x * e⁆ * (e⁻¹ * x * e) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact F.mul_mem (hAF h1) hx
  have e2 : r' * k * (e⁻¹ * x * e) * (r' * k)⁻¹ = r' * (k * (e⁻¹ * x * e) * k⁻¹) * r'⁻¹ := by
    group
  rw [e2]
  exact hRF r' hr' _ hkf

theorem bigDirect_inf_sup_le [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    {R : Subgroup G} {e : G} (he : e ∈ M)
    (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ = v)
    (hRF : ∀ r ∈ R, ∀ f ∈ P ⊓ wOf V H, r * f * r⁻¹ ∈ P ⊓ wOf V H)
    (hRFe : ∀ r ∈ R, ∀ x ∈ conjSubgroup e (P ⊓ wOf V H),
      r * x * r⁻¹ ∈ conjSubgroup e (P ⊓ wOf V H))
    (htrans : ∀ x ∈ P ⊓ wOf V H, x ∉ V → ∀ y ∈ P ⊓ wOf V H, y ∉ V →
      ∃ r ∈ R, ∃ α ∈ V ⊓ wOf V H, r * x * r⁻¹ = y * α)
    (hnle : ¬ conjSubgroup e (P ⊓ wOf V H) ≤ (P ⊓ wOf V H) ⊔ V) :
    ((P ⊓ wOf V H) ⊔ V) ⊓ (conjSubgroup e (P ⊓ wOf V H) ⊔ V) ≤ V := by
  set F : Subgroup G := P ⊓ wOf V H with hF
  set Fe : Subgroup G := conjSubgroup e F with hFe
  have hcomm : ∀ s ∈ F, ∀ t ∈ V, s * t = t * s := fun s hs t ht =>
    (hc.commute_of_mem_P (Subgroup.mem_inf.mp hs).1 ht).symm
  set S₁ : Subgroup G := (F ⊔ V) ⊓ (Fe ⊔ V) with hS₁
  have hVS : V ≤ S₁ := le_inf le_sup_right le_sup_right
  have hRS : ∀ r ∈ R, ∀ y ∈ S₁, r * y * r⁻¹ ∈ S₁ := by
    intro r hr y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact bigDirect_conj_mem_sup (fun s hs => Subgroup.mem_sup_left (hRF r hr s hs))
        (fun t ht => by rw [hRV r hr t ht]; exact Subgroup.mem_sup_right ht) y hy1
    · exact bigDirect_conj_mem_sup (fun s hs => Subgroup.mem_sup_left (hRFe r hr s hs))
        (fun t ht => by rw [hRV r hr t ht]; exact Subgroup.mem_sup_right ht) y hy2
  intro x hx
  by_contra hxV
  obtain ⟨hxU, hxU'⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨f, hf, v, hv, rfl⟩ := exists_mul_of_mem_sup hcomm hxU
  have hfS : f ∈ S₁ := by
    have := S₁.mul_mem hx (S₁.inv_mem (hVS hv))
    simpa using this
  have hfV : f ∉ V := fun h => hxV (V.mul_mem h hv)
  have hFS : F ≤ S₁ := by
    intro y hy
    by_cases hyV : y ∈ V
    · exact hVS hyV
    obtain ⟨r, hr, α, hα, hrα⟩ := htrans f hf hfV y hy hyV
    have hy' : y = (r * f * r⁻¹) * α⁻¹ := by rw [hrα]; group
    rw [hy']
    exact S₁.mul_mem (hRS r hr f hfS) (S₁.inv_mem (hVS (Subgroup.mem_inf.mp hα).1))
  have hUU' : F ⊔ V ≤ Fe ⊔ V := fun z hz => (Subgroup.mem_inf.mp (sup_le hFS hVS hz)).2
  have hcard : Nat.card ↥(Fe ⊔ V) = Nat.card ↥(F ⊔ V) := by
    have heV : e ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact he
    have hV : conjSubgroup e V = V := mem_normalizer_iff_conjSubgroup_eq.mp heV
    have : Fe ⊔ V = conjSubgroup e (F ⊔ V) := by
      rw [conjSubgroup_sup_eq_sup, hV]
    rw [this]
    exact card_conjSubgroup e _
  have heq : F ⊔ V = Fe ⊔ V := Subgroup.eq_of_le_of_card_ge hUU' hcard.le
  exact hnle (le_sup_left.trans heq.ge)

end CFSG.RankThree.GF2n.Tim79a
