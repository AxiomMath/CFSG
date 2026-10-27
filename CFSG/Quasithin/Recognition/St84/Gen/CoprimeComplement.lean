module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public section

namespace CFSG.Quasithin.F112R.St84

variable {G : Type*} [Group G]

theorem exists_mul_mem_inf_centralizer_of_coprime [Finite G] {L Q H : Subgroup G}
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card Q))
    (hcomm : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ * l⁻¹ ∈ Q)
    {l : G} (hl : l ∈ L) :
    ∃ q ∈ Q, ∃ c ∈ L ⊓ Subgroup.centralizer (H : Set G), l = q * c := by
  classical
  let X : Subgroup G := Q ⊔ H
  let K : Subgroup G := H.map (MulAut.conj l).toMonoidHom
  have hQX : Q ≤ X := le_sup_left
  have hHX : H ≤ X := le_sup_right
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hHQ
  have hQHinf : Q ⊓ H = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop.symm
  have hHinfQ : H ⊓ Q = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hKX : K ≤ X := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨h, hh, hx⟩
    have hxh : (MulAut.conj l).toMonoidHom h = l * h * l⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hx, hxh]
    have hQmem : l * h * l⁻¹ * h⁻¹ ∈ Q := by
      have := Q.inv_mem (hcomm h hh l hl)
      simpa [mul_assoc] using this
    have hprod : l * h * l⁻¹ = (l * h * l⁻¹ * h⁻¹) * h := by group
    rw [hprod]
    exact X.mul_mem (Subgroup.mem_sup_left hQmem) (Subgroup.mem_sup_right hh)
  have hQKsup : Q ⊔ K = X := by
    apply le_antisymm (sup_le hQX hKX)
    apply sup_le le_sup_left
    intro h hh
    have hQmem : h * l * h⁻¹ * l⁻¹ ∈ Q := hcomm h hh l hl
    have hKmem : l * h * l⁻¹ ∈ K := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj l).toMonoidHom hh
      have hxh : (MulAut.conj l).toMonoidHom h = l * h * l⁻¹ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [hxh] at hmem
    have heq : h = (h * l * h⁻¹ * l⁻¹) * (l * h * l⁻¹) := by group
    rw [heq]
    exact (Q ⊔ K).mul_mem (Subgroup.mem_sup_left hQmem) (Subgroup.mem_sup_right hKmem)
  haveI hN : (Q.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hXQ
  have hHcompX : (Q.subgroupOf X).IsComplement' (H.subgroupOf X) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxQ, hxH⟩
        apply Subtype.ext
        have hx : ((x : X) : G) ∈ Q ⊓ H := ⟨hxQ, hxH⟩
        rwa [hQHinf, Subgroup.mem_bot] at hx
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(Q.subgroupOf X).one_mem, (H.subgroupOf X).one_mem⟩
    · have hsup : Q.subgroupOf X ⊔ H.subgroupOf X = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQX hHX]
        rw [show Q ⊔ H = X from rfl, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (Q.subgroupOf X) (H.subgroupOf X), hsup]
      rfl
  have hKcompX : (Q.subgroupOf X).IsComplement' (K.subgroupOf X) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxQ, hxK⟩
        apply Subtype.ext
        have hxg : ((x : X) : G) ∈ Q := hxQ
        rcases Subgroup.mem_map.mp (show ((x : X) : G) ∈ K from hxK) with
          ⟨h, hh, hhx⟩
        have hlinv : l⁻¹ * ((x : X) : G) * l ∈ Q := by
          have hnorm : ((x : X) : G) ∈ Q ↔ l⁻¹ * ((x : X) : G) * l ∈ Q := by
            simpa using (Subgroup.mem_normalizer_iff.mp
              (Subgroup.inv_mem (Subgroup.normalizer (Q : Set G)) (hLQ hl)) ((x : X) : G))
          exact hnorm.mp hxg
        have hhQ : h ∈ Q := by
          have hxeq : l⁻¹ * ((x : X) : G) * l = h := by
            rw [← hhx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
          rwa [hxeq] at hlinv
        have hh1 : h = 1 := by
          have hmem : h ∈ H ⊓ Q := ⟨hh, hhQ⟩
          rwa [hHinfQ, Subgroup.mem_bot] at hmem
        rw [← hhx, hh1]
        simp
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(Q.subgroupOf X).one_mem, (K.subgroupOf X).one_mem⟩
    · have hsup : Q.subgroupOf X ⊔ K.subgroupOf X = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQX hKX, hQKsup, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (Q.subgroupOf X) (K.subgroupOf X), hsup]
      rfl
  have hcopX : Nat.Coprime (Nat.card (Q.subgroupOf X)) (Q.subgroupOf X).index := by
    rw [hHcompX.symm.index_eq_card]
    have hQcard : Nat.card (Q.subgroupOf X) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv
    have hHcard : Nat.card (H.subgroupOf X) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv
    rw [hQcard, hHcard]
    exact hcop.symm
  obtain ⟨q, hq⟩ :=
    CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      (Q.subgroupOf X) (H.subgroupOf X) (K.subgroupOf X) hN hHcompX hKcompX hcopX
  have hconj : K = H.map (MulAut.conj ((q : X) : G)).toMonoidHom := by
    have hmap := congrArg (fun S : Subgroup X => S.map X.subtype) hq
    rw [Subgroup.map_subgroupOf_eq_of_le hKX, Subgroup.map_map] at hmap
    have hcomp : (X.subtype.comp (MulAut.conj (q : X)).toMonoidHom) =
        ((MulAut.conj ((q : X) : G)).toMonoidHom.comp X.subtype) := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHX] at hmap
    exact hmap
  let n : G := ((q : X) : G)⁻¹ * l
  have hnL : n ∈ L :=
    L.mul_mem (L.inv_mem (hQL (Subgroup.mem_subgroupOf.mp q.2))) hl
  have hnH : ∀ h ∈ H, n * h * n⁻¹ ∈ H := by
    intro h hh
    have hK : (MulAut.conj l) h ∈ K :=
      Subgroup.mem_map_of_mem (MulAut.conj l).toMonoidHom hh
    rw [hconj] at hK
    rcases Subgroup.mem_map.mp hK with ⟨h', hh', hEq⟩
    have hEq' : ((q : X) : G)⁻¹ * ((MulAut.conj l) h) * ((q : X) : G) = h' := by
      rw [← hEq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have he : n * h * n⁻¹ =
        ((q : X) : G)⁻¹ * ((MulAut.conj l) h) * ((q : X) : G) := by
      simp only [n, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [he, hEq']
    exact hh'
  have hnCent : n ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hHn : n * h * n⁻¹ ∈ H := hnH h hh
    have hQn : n * h * n⁻¹ * h⁻¹ ∈ Q := by
      have hc := hcomm h hh n hnL
      have hc' : n * h * n⁻¹ * h⁻¹ = (h * n * h⁻¹ * n⁻¹)⁻¹ := by group
      rw [hc']
      exact Q.inv_mem hc
    have hbot : n * h * n⁻¹ * h⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hHinfQ]
      exact ⟨H.mul_mem hHn (H.inv_mem hh), hQn⟩
    rw [Subgroup.mem_bot] at hbot
    have heq : n * h * n⁻¹ = h := by
      have := congrArg (fun x => x * h) hbot
      simpa [mul_assoc] using this
    have hcomm' : n * h = h * n := by
      have := congrArg (fun x => x * n) heq
      simpa [mul_assoc] using this
    exact hcomm'.symm
  refine ⟨((q : X) : G), Subgroup.mem_subgroupOf.mp q.2, n, ⟨hnL, hnCent⟩, ?_⟩
  simp only [n]
  group

theorem sup_inf_centralizer_eq_of_coprime [Finite G] {L Q H : Subgroup G}
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card Q))
    (hcomm : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ * l⁻¹ ∈ Q) :
    Q ⊔ (L ⊓ Subgroup.centralizer (H : Set G)) = L := by
  apply le_antisymm
  · exact sup_le hQL inf_le_left
  · intro l hl
    obtain ⟨q, hqQ, c, hcC, rfl⟩ :=
      exists_mul_mem_inf_centralizer_of_coprime hQL hLQ hHQ hcop hcomm hl
    exact (Q ⊔ (L ⊓ Subgroup.centralizer (H : Set G))).mul_mem
      (Subgroup.mem_sup_left hqQ) (Subgroup.mem_sup_right hcC)

theorem inf_centralizer_inf_eq_bot_of_fixed {L Q H : Subgroup G}
    (hfix : ∀ x ∈ Q, (∀ h ∈ H, h * x * h⁻¹ = x) → x = 1) :
    L ⊓ Subgroup.centralizer (H : Set G) ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨⟨hxL, hxC⟩, hxQ⟩ := hx
  rw [Subgroup.mem_bot]
  refine hfix x hxQ ?_
  intro h hh
  have hcx : h * x = x * h := (Subgroup.mem_centralizer_iff.mp hxC) h hh
  calc h * x * h⁻¹ = (x * h) * h⁻¹ := by rw [hcx]
    _ = x := by group

end CFSG.Quasithin.F112R.St84

end
