
module

public import CFSG.Sporadic.J4.QT2LocUniqBase

public import CFSG.Sporadic.J4.QT2LocUniqCheck
public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix
open scoped Classical

theorem card_inter_le
    (hF : J4Facts) {g : J} (hg : g ∉ Hj) :
    {x : J | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11}.ncard ≤ 8 := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hg
    have : pathElt (repPaths.getD 0 []) = 1 := by simp [repPaths, pathElt]
    rw [this]
    simpa using Hj.mul_mem hh hh'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cands_parts
  have hcz : (candZ (locMats ()) (locInvs ()) ℓ).length ≤ 7 := by
    interval_cases ℓ <;> simp_all
  have hZE : (ZE' ℓ).card ≤ 7 := ZE'_card_le hM hℓ (pathInv_get hℓ) hcz
  set u := pathElt (repPaths.getD ℓ []) with hu
  have hmap : ∀ x ∈ {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11},
      h⁻¹ * x * h ∈ insert (1 : J) (↑(ZE' ℓ) : Set J) := by
    rintro x ⟨hxE, hxg⟩
    have hx' : h⁻¹ * x * h ∈ Eg uJ 11 := by
      have := Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) x hxE
      simpa using this
    have hx'' : u * (h⁻¹ * x * h) * u⁻¹ ∈ Eg uJ 11 := by
      have e : u * (h⁻¹ * x * h) * u⁻¹ = h' * ((h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h')) * h'⁻¹ := by
        group
      rw [e]
      exact Hj_normalizes_Eg hM h' hh' _ hxg
    by_cases h1 : h⁻¹ * x * h = 1
    · exact Or.inl h1
    · right
      obtain ⟨c, hcl, hc⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx'
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact h1 (by rw [hc, eta_zero])
      rcases mask_cover c hcl with h0 | hT | hZ
      · exact absurd h0 hc0
      · exfalso
        have hxT : h⁻¹ * x * h ∈ tSet := ⟨c, hT, hc⟩
        exact not_mem_Eg_conj hM (by omega) (by omega) hxT hx''
      · have hxZ : h⁻¹ * x * h ∈ Zl := mem_Zl.2 ⟨c, hZ, hc.symm⟩
        rw [Finset.mem_coe, ZE', Finset.mem_filter]
        exact ⟨hxZ, hx''⟩
  have hinj : Set.InjOn (fun x : J => h⁻¹ * x * h)
      {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11} := by
    intro a _ b _ e
    simpa using e
  have hfin : (insert (1 : J) (↑(ZE' ℓ) : Set J)).Finite :=
    Set.Finite.insert _ (Finset.finite_toSet _)
  calc {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11}.ncard
      ≤ (insert (1 : J) (↑(ZE' ℓ) : Set J)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun x : J => h⁻¹ * x * h) hmap hinj hfin
    _ ≤ (↑(ZE' ℓ) : Set J).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 8 := by
      rw [Set.ncard_coe_finset]
      omega

theorem mem_Hj_of_big_inter
    (hF : J4Facts) {g : J} {V : Subgroup J} (hVE : V ≤ Eg uJ 11)
    (hVg : ∀ v ∈ V, g⁻¹ * v * g ∈ Eg uJ 11) (hcard : 8 < Nat.card V) : g ∈ Hj := by
  by_contra hg
  have hsub : (V : Set J) ⊆ {x : J | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11} :=
    fun v hv => ⟨hVE hv, hVg v hv⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := card_inter_le hF hg
  have h3 : Nat.card V = (V : Set J).ncard := Nat.card_coe_set_eq (V : Set J)
  omega

end CFSG.Sporadic.J4.QT2
