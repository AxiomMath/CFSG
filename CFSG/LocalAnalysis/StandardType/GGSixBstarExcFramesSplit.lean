module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFix
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFrames

section Elem

variable {H H' : Type*} [Group H] [Group H'] {p : ℕ}

theorem isElemAbelian_range_frame {k : ℕ} (φ : Multiplicative (Fin k → ZMod p) →* H) :
    IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have h : a ^ p = 1 := by
      refine Multiplicative.toAdd.injective ?_
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    rw [h, map_one]

theorem isElemAbelian_map_frame (χ : H →* H') {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map χ) := CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_comap_frame (χ : H →* H') (hχ : Function.Injective χ) {E : Subgroup H'}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap χ) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hχ ?_)⟩⟩, fun x hx => hχ ?_⟩
  · have h := congrArg Subtype.val (hE.1.1.1 ⟨χ x, x.2⟩ ⟨χ y, y.2⟩)
    simpa only [map_mul, Subgroup.coe_mul] using h
  · rw [map_pow, hE.2 _ hx, map_one]

theorem card_comap_of_le_range (χ : H →* H')
    (hχ : Function.Injective χ) {Bs : Subgroup H'} (hBsR : Bs ≤ χ.range) :
    Nat.card (Bs.comap χ) = Nat.card Bs := by
  have h := Subgroup.card_map_of_injective (K := Bs.comap χ) hχ
  rw [Subgroup.map_comap_eq_self hBsR] at h
  exact h.symm

end Elem

section Rank


theorem rank_le_twoLocalRank {τ : Tag} (hr : 0 < τ.rank) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p)) {G : Type} [Group G] [Finite G]
    (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ) :
    τ.rank ≤ LargeEvenTwoLocalRank p G := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨U, hU, hU2, hTU⟩ := TableBExc.exists_rootGroup_normalized ⟨0, hr⟩ ζ hζ
  set φ := χ.comp (CFSG.RankThree.CentralCover.chevTorus τ ζ hζ) with hφ
  have hφinj : Function.Injective φ :=
    hχ.comp (CFSG.RankThree.CentralCover.chevTorus_injective hζo hζ hdet)
  have hcard : Nat.card φ.range = p ^ τ.rank := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr
      Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hUne : U.map χ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hχ]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  refine TableB.le_twoLocalRank hp.one_lt hTL (TableB.le_pRank_of_le hp.one_lt ?_
    (isElemAbelian_range_frame φ) hcard)
  rintro _ ⟨v, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, hTU v u hu, ?_⟩
    simp [hφ]
  · rintro ⟨u', hu', hyu⟩
    have hy : y = χ ((CFSG.RankThree.CentralCover.chevTorus τ ζ hζ v)⁻¹ * u' *
        CFSG.RankThree.CentralCover.chevTorus τ ζ hζ v) := by
      have h1 : φ v * y * (φ v)⁻¹ = χ u' := hyu.symm
      simp only [hφ, MonoidHom.comp_apply] at h1
      simp only [map_mul, map_inv, ← h1]
      group
    refine ⟨_, ?_, hy.symm⟩
    have h2 := hTU v⁻¹ u' hu'
    have e : CFSG.RankThree.CentralCover.chevTorus τ ζ hζ v⁻¹ =
        (CFSG.RankThree.CentralCover.chevTorus τ ζ hζ v)⁻¹ :=
      map_inv (CFSG.RankThree.CentralCover.chevTorus τ ζ hζ) v
    rwa [e, inv_inv] at h2

end Rank

section Toral


theorem exists_weylFrame_of_toral {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (hpq : p ∣ Nat.card K - 1)
    (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K)
    (hfix : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 → ∃ a : adjointGroup τ K,
      ∀ v ∈ TableBExc.torusPow τ K p, α v = a * v * a⁻¹)
    {G : Type} [Group G] (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ)
    {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hT : ∃ c : adjointGroup τ K,
      (Bs.comap χ).map (MulAut.conj c).toMonoidHom = TableBExc.torusPow τ K p) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  refine exists_weylFrame hfull (isUnit_det_symmetrizedCartan hτ hp2) hζo χ hχ c
    (fun b => ?_) hfix
  constructor
  · intro hb
    obtain ⟨e, rfl⟩ := hBsR hb
    refine ⟨c * e * c⁻¹, ?_, by rw [show c⁻¹ * (c * e * c⁻¹) * c = e by group]⟩
    rw [← hc]
    exact ⟨e, hb, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    rw [← hc] at hv
    obtain ⟨e, he, rfl⟩ := hv
    have h1 : c⁻¹ * (MulAut.conj c).toMonoidHom e * c = e := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1]
    exact he

theorem exists_weylFrame_F4 {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {G : Type} [Group G]
    (χ : adjointGroup .F4 K →* G) (hχ : Function.Injective χ) {Bs : Subgroup G}
    (hBsR : Bs ≤ χ.range) (hBs : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card Bs) :
    ∃ ι : Multiplicative (Fin Tag.F4.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .F4 p w s)) := by
  have hp : p.Prime := Fact.out
  have hT : GGF4ToralRankInput K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBF4.ggF4ToralRankInput_three hpq
    · exact TableBF4.ggF4ToralRankInput_of_five_le hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
        hpq
  obtain ⟨c, hc⟩ := hT (Bs.comap χ) (isElemAbelian_comap_frame χ hχ hBs)
    (by rw [card_comap_of_le_range χ hχ hBsR]; exact h4)
  exact exists_weylFrame_of_toral hp2 (Or.inl rfl) hpq
    (fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a)
    (fun α hα => exists_inner_on_torusPow_F4 hf hK hp2 α hα) χ hχ hBsR ⟨c, hc⟩

theorem exists_weylFrame_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {G : Type} [Group G]
    (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ) {Bs : Subgroup G}
    (hBsR : Bs ≤ χ.range) (hBs : IsElemAbelian p Bs) (hr : p ^ τ.rank ≤ Nat.card Bs) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := IOneRest.ggExcToralRankInput_E7E8 hτ hp hp2 hpq (Bs.comap χ)
    (isElemAbelian_comap_frame χ hχ hBs) (by rw [card_comap_of_le_range χ hχ hBsR]; exact hr)
  exact exists_weylFrame_of_toral hp2 (Or.inr hτ) hpq (TableBExc.full_of_E7_E8 hτ)
    (fun α hα => exists_inner_on_torusPow_E7E8 hf hK hτ α hα) χ hχ hBsR ⟨c, hc⟩

end Toral

end ExcFrames

end CFSG.StandardType
