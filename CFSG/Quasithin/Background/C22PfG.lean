module

public import CFSG.Quasithin.Background.C22PfE
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Sporadic.Schreier.Tits

namespace C22Pf

theorem normalizer_le_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (P₀ : Sylow 2 Y) (hN : Subgroup.normalizer ((P₀ : Subgroup Y) : Set Y) ≤ P₀)
    (S : Sylow 2 X) : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set S' : Sylow 2 Y := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S with hS'
  have hS'c : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have h1 : (Subgroup.normalizer ((S' : Subgroup Y) : Set Y)).index =
      (Subgroup.normalizer ((P₀ : Subgroup Y) : Set Y)).index :=
    (Sylow.card_eq_index_normalizer S').symm.trans (Sylow.card_eq_index_normalizer P₀)
  have h2 : Subgroup.normalizer ((P₀ : Subgroup Y) : Set Y) = P₀ :=
    le_antisymm hN Subgroup.le_normalizer
  have h3 : Nat.card (S' : Subgroup Y) = Nat.card (P₀ : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h4 : Nat.card (Subgroup.normalizer ((S' : Subgroup Y) : Set Y)) =
      Nat.card (S' : Subgroup Y) := by
    have e1 := Subgroup.card_mul_index (Subgroup.normalizer ((S' : Subgroup Y) : Set Y))
    have e2 := Subgroup.card_mul_index (P₀ : Subgroup Y)
    rw [h1, h2] at e1
    rw [h3]
    have hpos : 0 < (P₀ : Subgroup Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
  have h5 : Subgroup.normalizer ((S' : Subgroup Y) : Set Y) = S' :=
    (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer h4.le).symm
  intro g hg
  have hg' : e g ∈ Subgroup.normalizer ((S' : Subgroup Y) : Set Y) := by
    rw [hS'c, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨g, hg, rfl⟩
  rw [h5, hS'c] at hg'
  obtain ⟨g', hg'S, he⟩ := hg'
  have : g' = g := e.injective he
  rw [← this]
  exact hg'S

theorem titsSylowSelfNormalizing_holds :
    TitsSylowSelfNormalizing := by
  intro X _ _ n f hm S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : ReeTitsModel X .Tits 2 f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  obtain ⟨e⟩ := titsModelEquiv X 2 f hR
  have hS2 : IsPGroup 2 ↥titsSD := IsPGroup.of_card (n := 11) (by rw [card_titsSD]; norm_num)
  have hSi : ¬ 2 ∣ titsSD.index := by
    have h := Subgroup.card_mul_index titsSD
    rw [card_titsSD, card_titsD] at h
    have hi : titsSD.index = 8775 := by omega
    rw [hi]
    decide
  exact normalizer_le_of_mulEquiv e (hS2.toSylow hSi) titsSD_normalizer_le S

end C22Pf

end CFSG.Quasithin
