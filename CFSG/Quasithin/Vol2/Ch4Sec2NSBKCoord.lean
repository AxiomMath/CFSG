module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBU0
public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

theorem vV_le_uZero (hN31 : NotC31) (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hd : NoSumBigData G T M L Mm I H K m k) : vV T L ≤ uZero I K := by
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  rcases hc.described with ⟨hcomp, h31'⟩ | ⟨hKc, hCT, hqs, hKM, h41'⟩
  · exact (hN31 G T M L Mm I H K m k hd hcomp h31').elim
  · have h4 := c41Case4_of_conclusion hd h41'
    exact (C48Pf.le_commutator (h22 G) (h27 G) hc.hypC28 hKc hCT hqs hKM h41' h4).1

theorem V_coords_of_isSum (c : Conf4212 G T M L I H K)
    (hsum : IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
      (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k) :
    ∃ (ρ : ↥(perfectCore (L ⊓ H)) →* GL (Fin m) (ZMod 2))
      (βV : ↥(vV T L) →* Multiplicative (Fin k → Fin m → ZMod 2)),
      Function.Surjective ρ ∧ Function.Bijective βV ∧
      ∀ (l : ↥(perfectCore (L ⊓ H))) (u v : ↥(vV T L)), (v : G) = l * u * (l : G)⁻¹ → ∀ s : Fin k,
        Multiplicative.toAdd (βV v) s =
          ((ρ l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
            (Multiplicative.toAdd (βV u) s) := by
  obtain ⟨α, hαs, hαk, -, -, β, hβs, hβk, hβe⟩ := hsum
  have hLR : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
    c.perfectCore_le_normalizer_pCoreOf_I
  let ρ : ↥(perfectCore (L ⊓ H)) →* GL (Fin m) (ZMod 2) :=
    (Subgroup.subtype _).comp (α.comp (Subgroup.inclusion le_sup_left))
  refine ⟨ρ, β, ?_, ?_, ?_⟩
  · intro g
    have hgΓ : g ∈ CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2) :=
      CFSG.Open.StatedAPI.mem_statedSL_zmod_two g
    obtain ⟨x, hx⟩ := hαs ⟨g, hgΓ⟩
    have hxmem : (x : G) ∈ (perfectCore (L ⊓ H) : Set G) * (pCoreOf 2 I : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLR]
      exact x.2
    obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hxmem
    have hlA : l ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_left hl
    have hrA : r ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_right hr
    set a : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := ⟨l, hlA⟩ with ha
    set y : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := ⟨r, hrA⟩ with hy
    have hyker : y ∈ α.ker := by
      rw [hαk]
      exact Subgroup.mem_subgroupOf.mpr hr
    have hxay : x = a * y := Subtype.ext (by simp [a, y, hlr.symm])
    have hαa : α a = ⟨g, hgΓ⟩ := by
      have h1 : α x = α a := by
        rw [hxay, map_mul, MonoidHom.mem_ker.mp hyker, mul_one]
      rw [← h1, hx]
    refine ⟨⟨l, hl⟩, ?_⟩
    show ((α a : CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) : GL (Fin m) (ZMod 2)) = g
    rw [hαa]
  · refine ⟨?_, hβs⟩
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ β.ker := MonoidHom.mem_ker.mpr hx
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  · intro l u v huv s
    have h := hβe ⟨l, Subgroup.mem_sup_left l.2⟩ u v huv s
    simp only [moduleAct, if_neg Bool.false_ne_true] at h
    exact h

end CFSG.Quasithin.H13.Ch4.NSB
