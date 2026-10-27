module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Three_cocycle_fixes {V V₁ : Subgroup G} (hV : IsElemAbelian 2 V) (hV₁ : V₁ ≤ V)
    {v q : G} (hq1 : ∀ w ∈ V₁, q * w * q⁻¹ = w) (hq3 : ∃ n : ℕ, q ^ (3 ^ n) = 1)
    (hqv : q * v * q⁻¹ * v⁻¹ ∈ V₁) : q * v * q⁻¹ = v := by
  obtain ⟨n, hn⟩ := hq3
  set c : G := q * v * q⁻¹ * v⁻¹ with hc
  have hpow : ∀ k : ℕ, q ^ k * v * (q ^ k)⁻¹ * v⁻¹ = c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : c ^ k ∈ V₁ := V₁.pow_mem hqv k
      have h1 := hq1 _ hck
      calc q ^ (k + 1) * v * (q ^ (k + 1))⁻¹ * v⁻¹
          = (q * (q ^ k * v * (q ^ k)⁻¹ * v⁻¹) * q⁻¹) * (q * v * q⁻¹ * v⁻¹) := by group
        _ = c ^ (k + 1) := by rw [ih, h1, pow_succ]
  have hc3 : c ^ (3 ^ n) = 1 := by rw [← hpow, hn]; group
  have hc2 : c ^ 2 = 1 := hV.2 c (hV₁ hqv)
  have hcop : Nat.Coprime (3 ^ n) 2 := Nat.Coprime.pow_left n (by norm_num)
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.2 ⟨hc3, hc2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  have : q * v * q⁻¹ = c * v := by rw [hc]; group
  rw [this, hc1, one_mul]

theorem s15_Three_two_le_pRank {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 3 Q)
    (hnc : ¬ IsCyclic Q) : 2 ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥Q) := ⟨hQ⟩
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hel
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map Q.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE Q.subtype
  have hcard' : Nat.card (E.map Q.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard]
  have hle : E.map Q.subtype ≤ H := by
    rintro x ⟨y, -, rfl⟩
    exact hQH y.2
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hE' hcard'

private theorem s15_Three_isCyclic_of_map {S : Type*} [Group S] {H : Subgroup S} {P : Subgroup H}
    (hc : IsCyclic ↥(P.map H.subtype)) : IsCyclic ↥P :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.surjective

theorem s15_Three_lift_sylow {S A : Type} [Group S] [Finite S] [Group A] (ρ : S →* A)
    {E : Subgroup A} (hE : E ≤ ρ.range) (hE3 : IsPGroup 3 E) (hnc : ¬ IsCyclic E) :
    ∃ Q : Subgroup S, IsPGroup 3 Q ∧ ¬ IsCyclic Q ∧ Q ≤ E.comap ρ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup S := E.comap ρ with hT
  let f : T →* E := (ρ.domRestrict T).codRestrict E (fun t => t.2)
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := hE ha
    exact ⟨⟨s, by rw [hT, Subgroup.mem_comap, hs]; exact ha⟩, Subtype.ext hs⟩
  haveI : Finite E := Finite.of_surjective f hf
  have htop : IsPGroup 3 (⊤ : Subgroup ↥E) := by
    intro x
    obtain ⟨k, hk⟩ := hE3 x.1
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 3
    (htop.toSylow (by simp : ¬ 3 ∣ (⊤ : Subgroup ↥E).index))
  have hPtop : (P : Subgroup ↥T).map f = ⊤ := by
    have := congrArg (fun R : Sylow 3 ↥E => (R : Subgroup ↥E)) hP
    simpa using this
  refine ⟨(P : Subgroup ↥T).map T.subtype, P.isPGroup'.map _, ?_, ?_⟩
  · intro hcyc
    have hPc : IsCyclic (P : Subgroup ↥T) := s15_Three_isCyclic_of_map hcyc
    have hsurj : Function.Surjective (f.domRestrict (P : Subgroup ↥T)) := by
      intro a
      have : a ∈ (P : Subgroup ↥T).map f := by rw [hPtop]; trivial
      obtain ⟨t, ht, hta⟩ := this
      exact ⟨⟨t, ht⟩, hta⟩
    exact hnc (isCyclic_of_surjective (f.domRestrict (P : Subgroup ↥T)) hsurj)
  · rintro x ⟨t, -, rfl⟩
    exact t.2

theorem s15_Three_lift_rank {M V₁ V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hV₁ : V₁ ≤ V)
    (hYM : Y ≤ M) (hYst : Y ≤ stabTil V₁ V)
    (hYV₁ : ∀ y ∈ Y, ∀ w ∈ V₁, y * w * y⁻¹ = w) {v : G} (hvV : v ∈ V)
    {E : Subgroup (MulAut (Vtil V₁ V hV))} (hE : E ≤ barSub V₁ V hV Y) (hE3 : IsPGroup 3 E)
    (hEnc : ¬ IsCyclic E)
    (hEv : ∀ e ∈ E, e (mkTil V₁ V hV (IntMod.mk hV ⟨v, hvV⟩)) =
      mkTil V₁ V hV (IntMod.mk hV ⟨v, hvV⟩)) :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({v} : Set G)) := by
  let ρ : ↥Y →* MulAut (Vtil V₁ V hV) :=
    (actTil V₁ V hV).comp (Subgroup.inclusion hYst)
  have hrange : E ≤ ρ.range := by
    intro e he
    obtain ⟨g, hgY, rfl⟩ := (mem_barSub V₁ V hV Y e).1 (hE he)
    exact ⟨⟨(g : G), hgY⟩, rfl⟩
  obtain ⟨Q, hQ3, hQnc, hQE⟩ := s15_Three_lift_sylow ρ hrange hE3 hEnc
  have hQ3' : IsPGroup 3 (Q.map Y.subtype) := hQ3.map _
  have hQnc' : ¬ IsCyclic (Q.map Y.subtype) := fun hc =>
    hQnc (s15_Three_isCyclic_of_map hc)
  have hle : Q.map Y.subtype ≤ M ⊓ centralizer ({v} : Set G) := by
    rintro x ⟨q, hq, rfl⟩
    refine ⟨hYM q.2, ?_⟩
    show (q : G) ∈ centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqE : ρ q ∈ E := hQE hq
    have h1 := hEv _ hqE
    have h2 : actTil V₁ V hV ⟨(q : G), hYst q.2⟩ (mkTil V₁ V hV (IntMod.mk hV ⟨v, hvV⟩)) =
        mkTil V₁ V hV (IntMod.mk hV ⟨v, hvV⟩) := h1
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h2
    have h3 : (q : G) * v * (q : G)⁻¹ * v⁻¹ ∈ V₁ := h2
    obtain ⟨n, hn⟩ := hQ3 ⟨q, hq⟩
    have hq3 : ∃ n : ℕ, (q : G) ^ (3 ^ n) = 1 :=
      ⟨n, by simpa using congrArg (fun z : ↥Y => (z : G)) (congrArg Subtype.val hn)⟩
    have h4 := s15_Three_cocycle_fixes hV hV₁ (fun w hw => hYV₁ q q.2 w hw) hq3 h3
    calc (q : G) * v = ((q : G) * v * (q : G)⁻¹) * (q : G) := by group
      _ = v * (q : G) := by rw [h4]
  exact s15_Three_two_le_pRank hle hQ3' hQnc'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
