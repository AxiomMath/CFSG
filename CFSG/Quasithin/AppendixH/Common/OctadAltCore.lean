module

public import CFSG.Quasithin.AppendixH.Common.OctadAltBasic
public import CFSG.Quasithin.AppendixH.Common.OctadAltFix

public section

namespace CFSG.ASVolI.AppH

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

theorem commute_of_normal_isPGroup_two (Z : Finset Q) (hQ : 5 ≤ Fintype.card Q - Z.card)
    {H : Subgroup (Equiv.Perm Q)} (hHalt : H ≤ alternatingGroup Q)
    (hHZ : ∀ σ ∈ H, ∀ z, σ z ∈ Z ↔ z ∈ Z)
    (hHA : ∀ σ ∈ alternatingGroup Q, (∀ z ∈ Z, σ z = z) → σ ∈ H)
    {N : Subgroup (Equiv.Perm Q)} (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) {n c : Equiv.Perm Q} (hn : n ∈ N) (hc : c ∈ alternatingGroup Q)
    (hcZ : ∀ z ∈ Z, c z = z) : n * c = c * n := by
  let P := {x : Q // x ∉ Z}
  let φ : ↥(alternatingGroup P) →* Equiv.Perm Q :=
    (Equiv.Perm.ofSubtype : Equiv.Perm P →* Equiv.Perm Q).comp (alternatingGroup P).subtype
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact (alternatingGroup P).subtype_injective (Equiv.Perm.ofSubtype_injective hab)
  have hφmem : ∀ g : ↥(alternatingGroup P), φ g ∈ H := by
    intro g
    have h := ofSubtype_mem_alt Z g
    exact hHA (φ g) h.1 h.2
  have hMnorm : (N.comap φ).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_comap] at hm ⊢
    rw [map_mul, map_mul, map_inv]
    exact hNn (φ g) (hφmem g) (φ m) hm
  let ψ : ↥(N.comap φ) →* Equiv.Perm Q := φ.comp (N.comap φ).subtype
  have hψinj : Function.Injective ψ := hφinj.comp (N.comap φ).subtype_injective
  have hM2 : IsPGroup 2 (N.comap φ) := by
    intro m
    have hmN : φ (m : ↥(alternatingGroup P)) ∈ N := Subgroup.mem_comap.mp m.2
    obtain ⟨k, hk⟩ := hN2 ⟨φ (m : ↥(alternatingGroup P)), hmN⟩
    have hpow : ψ m ^ (2 ^ k) = (1 : Equiv.Perm Q) := by
      have := congrArg (fun x : N => (x : Equiv.Perm Q)) hk
      simpa [ψ, MonoidHom.comp_apply] using this
    exact ⟨k, hψinj (by rw [map_pow, map_one]; exact hpow)⟩
  have hcardP : Fintype.card P = Fintype.card Q - Z.card := by
    change Fintype.card {x : Q // x ∉ Z} = Fintype.card Q - Z.card
    rw [Fintype.card_subtype_compl (fun x : Q => x ∈ Z), Fintype.card_coe]
  have hMbot : N.comap φ = ⊥ :=
    eq_bot_of_normal_isPGroup_alt (P := P) (by rw [hcardP]; exact hQ) hMnorm hM2
  have hcH : c ∈ H := hHA c hc hcZ
  set d : Equiv.Perm Q := n * c * n⁻¹ * c⁻¹ with hd
  have hdAlt : d ∈ alternatingGroup Q := by
    rw [hd]
    exact mul_mem (mul_mem (mul_mem (hHalt (hNH hn)) hc) (inv_mem (hHalt (hNH hn))))
      (inv_mem hc)
  have hdZ : ∀ z ∈ Z, d z = z := by
    intro z hz
    have hcinv : c⁻¹ z = z := by
      apply c.injective
      rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hcZ z hz]
    have hninvZ : n⁻¹ z ∈ Z :=
      (hHZ n (hNH hn) (n⁻¹ z)).mp (by simpa using hz)
    rw [hd]
    simp only [Equiv.Perm.mul_apply, hcinv, hcZ (n⁻¹ z) hninvZ]
    exact Equiv.apply_symm_apply n z
  obtain ⟨d', hd'⟩ := exists_alt_ofSubtype Z hdAlt hdZ
  have hd'N : φ d' ∈ N := by
    have hφd' : φ d' = d := by
      show Equiv.Perm.ofSubtype (d' : Equiv.Perm P) = d
      exact hd'
    rw [hφd', hd]
    simpa only [mul_assoc] using N.mul_mem hn (hNn c hcH n⁻¹ (N.inv_mem hn))
  have hd'M : d' ∈ N.comap φ := Subgroup.mem_comap.mpr hd'N
  have hd'1 : d' = 1 := by
    have : d' ∈ (⊥ : Subgroup ↥(alternatingGroup P)) := by rwa [hMbot] at hd'M
    exact Subgroup.mem_bot.mp this
  have hd1 : n * c * n⁻¹ * c⁻¹ = 1 := by
    rw [← hd, ← hd', hd'1]
    simp
  have hdc : n * c * n⁻¹ = c := mul_inv_eq_one.mp hd1
  exact mul_inv_eq_iff_eq_mul.mp hdc

theorem eq_bot_of_normal_isPGroup_two (Z : Finset Q) (hZ : Z.card ≤ 2)
    (hQ : 5 ≤ Fintype.card Q - Z.card) {H : Subgroup (Equiv.Perm Q)}
    (hHalt : H ≤ alternatingGroup Q) (hHZ : ∀ σ ∈ H, ∀ z, σ z ∈ Z ↔ z ∈ Z)
    (hHA : ∀ σ ∈ alternatingGroup Q, (∀ z ∈ Z, σ z = z) → σ ∈ H)
    {N : Subgroup (Equiv.Perm Q)} (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have hnH : n ∈ H := hNH hn
  have hnAlt : n ∈ alternatingGroup Q := hHalt hnH
  have hfix : ∀ x, x ∉ Z → n x = x :=
    fixes_of_commute_alt Z (by omega) (hHZ n hnH)
      (fun c hc hcZ => commute_of_normal_isPGroup_two Z hQ hHalt hHZ hHA hNH hNn hN2 hn hc hcZ)
  exact eq_one_of_even_of_fix_compl Z hZ hnAlt hfix

end CFSG.ASVolI.AppH
