module

public import CFSG.GH74.Generic.S3.L3Cover
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.GH74.Generic CFSG.GH74.Generic.S3

theorem bt_eq_of_inv_mul_mem_center {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (a b : G →* H) (hab : ∀ g, (a g)⁻¹ * b g ∈ Subgroup.center H) : a = b := by
  let χ : G →* Subgroup.center H :=
    { toFun := fun g => ⟨(a g)⁻¹ * b g, hab g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hab g)
        have hc' : (a g')⁻¹ * ((a g)⁻¹ * b g) = ((a g)⁻¹ * b g) * (a g')⁻¹ := hc ((a g')⁻¹)
        change (a (g * g'))⁻¹ * b (g * g') = (a g)⁻¹ * b g * ((a g')⁻¹ * b g')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a g')⁻¹ * (a g)⁻¹ * (b g * b g') = ((a g')⁻¹ * ((a g)⁻¹ * b g)) * b g' := by
              simp only [mul_assoc]
          _ = ((a g)⁻¹ * b g) * (a g')⁻¹ * b g' := by rw [hc']
          _ = (a g)⁻¹ * b g * ((a g')⁻¹ * b g') := by simp only [mul_assoc] }
  have hker : _root_.commutator G ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator G = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ χ.ker := hker (htop ▸ Subgroup.mem_top g)
  have h1 : (a g)⁻¹ * b g = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
  exact inv_mul_eq_one.1 h1

theorem bt_case_split {E P X : Type} [Group E] [Group P] [Group X] [Finite E] [Finite X]
    (πE : E →* P) (hπE : Function.Surjective πE) (hkerE : πE.ker ≤ Subgroup.center E)
    (hEperf : Group.IsPerfect E) (hXperf : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* P)
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier P) = Nat.card πE.ker)
    (hdvd : Nat.card (Subgroup.center X) ∣ Nat.card πE.ker)
    (hprime : Nat.card πE.ker = 1 ∨ (Nat.card πE.ker).Prime) :
    Subgroup.center X = ⊥ ∨
      (Nat.card (Subgroup.center X) = Nat.card πE.ker ∧ Nonempty (X ≃* E)) := by
  have hcX : Nat.card (Subgroup.center X) = 1 ∨
      Nat.card (Subgroup.center X) = Nat.card πE.ker := by
    rcases hprime with h1 | hp
    · left
      rw [h1] at hdvd
      exact Nat.dvd_one.1 hdvd
    · rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact Or.inl h
      · exact Or.inr h
  rcases hcX with h1 | h2
  · left
    exact Subgroup.eq_bot_of_card_eq _ h1
  · right
    refine ⟨h2, ?_⟩
    set pX : X →* P := CFSG.GH74.Generic.centralQuotientMap e with hpX
    have hpXs : Function.Surjective pX := CFSG.GH74.Generic.centralQuotientMap_surjective e
    have hpXk : pX.ker = Subgroup.center X := CFSG.GH74.Generic.centralQuotientMap_ker e
    obtain ⟨α, hαs, hαc⟩ := exists_lift_of_card_eq hEperf hXperf πE hπE hkerE pX hpXs
      hpXk.le hM
    have hE : Nat.card E = Nat.card P * Nat.card πE.ker :=
      CFSG.GH74.Generic.card_eq_card_mul_card_ker πE hπE
    have hX : Nat.card X = Nat.card P * Nat.card (Subgroup.center X) := by
      have := CFSG.GH74.Generic.card_eq_card_mul_card_ker pX hpXs
      rwa [hpXk] at this
    have hcard : Nat.card E = Nat.card X := by rw [hE, hX, h2]
    have hbij : Function.Bijective α := hαs.bijective_of_nat_card_le (le_of_eq hcard)
    exact ⟨(MulEquiv.ofBijective α hbij).symm⟩

end CFSG.Quasithin.H13.P31X
