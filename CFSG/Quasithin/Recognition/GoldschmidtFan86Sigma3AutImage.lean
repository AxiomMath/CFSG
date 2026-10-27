module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutWrap
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutKey2

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup

theorem isKleinFour_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsKleinFour A) : IsKleinFour B :=
  ⟨(Nat.card_congr e.toEquiv).symm.trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans hA.exponent_two⟩

variable {H : Type*} [Group H] {S V D Q0 : Subgroup H}

theorem image_pow_mem (hVk : IsKleinFour ↥V) (hVD : V ≤ D) (hDS : D ≤ S) (hQS : Q0 ≤ S)
    (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d) (hDQ : D ⊓ Q0 = ⊥) (h : D ⊔ Q0 = S)
    (eD : ↥D ≃* DihedralGroup 4) (f : ↥S ≃* ↥S) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hfq : orderOf f = q) (i : ℕ) (v : ↥S) (hv : (v : H) ∈ V) :
    ∃ a b : H, a ∈ V ∧ b ∈ Q0 ∧ (((f ^ i) v : ↥S) : H) = a * b := by
  set e := splitEquiv hDS hQS hc hDQ h eD with he
  set f' : MulAut (DihedralGroup 4 × ↥(Q0.subgroupOf S)) := MulAut.congr e f with hf'
  set K' : Subgroup (DihedralGroup 4) := (V.subgroupOf D).map eD.toMonoidHom with hK'
  have hKk : IsKleinFour ↥K' := by
    have e1 : ↥(V.subgroupOf D) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVD
    have e2 : ↥(V.subgroupOf D) ≃* ↥K' :=
      (V.subgroupOf D).equivMapOfInjective eD.toMonoidHom eD.injective
    exact isKleinFour_of_mulEquiv (e1.symm.trans e2) hVk
  have hford : orderOf f' = q := by
    have := orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective f
    simpa [hf', hfq] using this
  have hclosed : ∀ x ∈ K', (f' ^ i) (x, 1) ∈ K'.prod ⊤ := by
    intro x hx
    rcases kleinFour_cases K' hKk with hA | hB
    · rw [hA] at hx ⊢; exact (key_aut f' q hq hq2 hford i).1 x hx
    · rw [hB] at hx ⊢; exact (key_aut f' q hq hq2 hford i).2 x hx
  have hvD : (v : H) ∈ D := hVD hv
  have hev : e v = (eD ⟨v, hvD⟩, 1) := splitEquiv_apply_of_mem hDS hQS hc hDQ h eD v hvD
  have hmem : eD ⟨v, hvD⟩ ∈ K' := ⟨⟨v, hvD⟩, hv, rfl⟩
  have hpow : (f' ^ i) (e v) = e ((f ^ i) v) := by
    have : f' ^ i = MulAut.congr e (f ^ i) := (map_pow (MulAut.congr e) f i).symm
    rw [this, MulAut.congr_apply]; simp
  have hin := hclosed _ hmem
  rw [← hev, hpow] at hin
  set s := (f ^ i) v with hs
  have hs1 : (e s).1 ∈ K' := (Subgroup.mem_prod.1 hin).1
  obtain ⟨d, hd, hdeq⟩ := hs1
  have hsymm : (s : H) = ((eD.symm (e s).1 : ↥D) : H) * (((e s).2 : ↥(Q0.subgroupOf S)) : S) := by
    have := splitEquiv_symm_apply hDS hQS hc hDQ h eD (e s).1 (e s).2
    rw [he] at this ⊢
    simpa using this
  refine ⟨((eD.symm (e s).1 : ↥D) : H), (((e s).2 : ↥(Q0.subgroupOf S)) : S), ?_, ?_, hsymm⟩
  · have : eD.symm (e s).1 = d := by rw [← hdeq]; simp
    rw [this]; exact hd
  · exact ((e s).2).2

theorem conj_mem_V (hVk : IsKleinFour ↥V) (hVD : V ≤ D) (eD : ↥D ≃* DihedralGroup 4)
    (d : ↥D) (v : H) (hv : v ∈ V) : (d : H) * v * (d : H)⁻¹ ∈ V := by
  set K' : Subgroup (DihedralGroup 4) := (V.subgroupOf D).map eD.toMonoidHom with hK'
  have hKk : IsKleinFour ↥K' := by
    have e1 : ↥(V.subgroupOf D) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVD
    have e2 : ↥(V.subgroupOf D) ≃* ↥K' :=
      (V.subgroupOf D).equivMapOfInjective eD.toMonoidHom eD.injective
    exact isKleinFour_of_mulEquiv (e1.symm.trans e2) hVk
  have hvD : v ∈ D := hVD hv
  have hmem : eD ⟨v, hvD⟩ ∈ K' := ⟨⟨v, hvD⟩, hv, rfl⟩
  have hcl : eD (d * ⟨v, hvD⟩ * d⁻¹) ∈ K' := by
    rw [map_mul, map_mul, map_inv]
    rcases kleinFour_cases K' hKk with hA | hB
    · rw [hA] at hmem ⊢
      exact mem_kleinA.2 (normal_inA _ _ (mem_kleinA.1 hmem))
    · rw [hB] at hmem ⊢
      exact mem_kleinB.2 (normal_inB _ _ (mem_kleinB.1 hmem))
  obtain ⟨w, hw, hwe⟩ := hcl
  have : w = d * ⟨v, hvD⟩ * d⁻¹ := eD.injective hwe
  have hw' : (w : H) ∈ V := hw
  rw [this] at hw'
  exact hw'

end CFSG.Quasithin.Fan86.Sigma3
