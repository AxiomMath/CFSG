module

public import CFSG.Quasithin.EmptyFaithful.ModHSolv
public import CFSG.Quasithin.EmptyFaithful.ModHA6

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin.ModG CFSG.Blueprint CFSG.QuasithinUnique

theorem solvNine_M22 :
    SolvNine Mg := by
  obtain ⟨E, hL⟩ := m22Lat
  have hS₀ : IsSylowTwoOf Sg ⊤ := K1.isSylowTwoOf_top_iff.mpr hL.sylow
  refine solvNine_of_sylow hS₀ ?_
  intro Y hN hs h9
  have hZs : Group.IsSolvable ↥(Y ⊔ Sg) := isSolvable_sup_of_le_normalizer hs hL.sylow.1 hN
  have hZD : Y ⊔ Sg ≤ Dg := hL.lat _ le_sup_right hZs
  obtain ⟨α, -, hαk⟩ := hL.alt.hom
  set Z := Y ⊔ Sg with hZ
  have h128 : 128 ∣ Nat.card ↥Z := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Sg ≤ Z)
    rwa [card_Sg] at this
  have h9Z : 9 ∣ Nat.card ↥Z := h9.trans (Subgroup.card_dvd_of_le (le_sup_left : Y ≤ Z))
  have h1152 : 128 * 9 ∣ Nat.card ↥Z := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h128 h9Z
  let β : ↥(Z.subgroupOf Dg) →* alternatingGroup (Fin 6) := α.comp (Z.subgroupOf Dg).subtype
  have hcardZ : Nat.card ↥(Z.subgroupOf Dg) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv
  have hsolvD : Group.IsSolvable ↥(Z.subgroupOf Dg) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hZD).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hZD).injective
  have hsolvR : Group.IsSolvable ↥β.range := Group.isSolvable_of_surjective β.rangeRestrict_surjective
  have hker : Nat.card ↥β.ker ∣ 16 := by
    let g₀ : ↥β.ker →* ↥Dg := (Z.subgroupOf Dg).subtype.comp β.ker.subtype
    let κ : ↥β.ker →* ↥α.ker := g₀.codRestrict α.ker (fun x => by
      have := MonoidHom.mem_ker.1 x.2
      exact MonoidHom.mem_ker.2 this)
    have hinj : Function.Injective κ := by
      intro x y hxy
      have h1 := congrArg (fun w : ↥α.ker => ((w : ↥Dg) : ↥Dg)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have h2 := Subgroup.card_dvd_of_injective κ hinj
    have h3 : Nat.card ↥α.ker = 16 := by
      rw [hαk]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.alt.le).toEquiv).trans hL.alt.card
    rwa [h3] at h2
  have hprod := Subgroup.card_ker_mul_card_range β
  have h72 : 72 ∣ Nat.card ↥β.range := by
    have h1 : 72 * 16 ∣ Nat.card ↥β.ker * Nat.card ↥β.range := by
      rw [hprod, hcardZ]
      exact h1152
    have h2 : Nat.card ↥β.ker * Nat.card ↥β.range ∣ 16 * Nat.card ↥β.range :=
      Nat.mul_dvd_mul_right hker _
    have h3 : 16 * 72 ∣ 16 * Nat.card ↥β.range := by
      rw [mul_comm 16 72]
      exact h1.trans h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  exact a6_no_solvable_72 _ hsolvR h72

end CFSG.Quasithin.ModH
