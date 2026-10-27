module

public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCases2
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommute

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S14110

@[expose] def Theorem1391Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → T ≤ M →
      ¬ Nonempty (↥M ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2))

theorem stageLemma14110_of_theorem1391 (h1391 : Theorem1391Statement) : StageLemma14110 := by
  intro G _ _ T Mc h M X R hM hblock hA hQR hRT hJ
  obtain ⟨hs, hXM, hsn⟩ := hblock
  obtain ⟨c, hX⟩ := A4Data.of_isShort2 hs hA
  have hTM : T ≤ M := hM.2
  have hMloc : IsTwoLocal M := hM.1.1
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hcharM : CharTwo M := h.qtke.2.1 M hMloc ⟨S, hS ▸ hTM⟩
  have hW2 : IsPGroup 2 (blockU X) := fun u => ⟨1, by
    have := hX.sq_eq_one u u.2
    simpa [Subtype.ext_iff] using this⟩
  have hWQ : blockU X ≤ pCoreOf 2 M :=
    le_pCoreOf_of_isSubnormal hXM hsn hW2 hX.le hX.le_normalizer
  have hrank : CFSG.Open.pRank 3 M ≤ 2 :=
    pRank_le_two_of_isTwoLocal h.qtke hMloc Nat.prime_three (by norm_num)
  by_cases hnorm : ∀ m ∈ M, m ∈ Subgroup.normalizer (X : Set G)
  · exact case_normal h hM hX hXM hnorm hRT hJ
  · have : ∃ m₀ ∈ M, m₀ ∉ Subgroup.normalizer (X : Set G) := by
      by_contra hcon
      exact hnorm fun m hm => by_contra fun hm' => hcon ⟨m, hm, hm'⟩
    obtain ⟨m₀, hm₀, hm₀n⟩ := this
    have hne : cj m₀ X ≠ X := fun e => hm₀n (mem_normalizer_iff_cj.2 e)
    have hDC : ∀ m ∈ M, cj m X = X ∨ ∀ x ∈ X, ∀ y ∈ cj m X, x * y = y * x := fun m hm =>
      (commute_or_eq_of_isSubnormal hcharM hXM (cj_le hXM hm) hsn (isSubnormal_cj hsn hm) hX
        (hX.map (MulAut.conj m))).imp_left Eq.symm
    have hno := h1391 G T h.simple h.nonabelian h.qtke h.sylow M hM.1 hTM
    exact case_nonnormal h hM hX hXM hWQ hQR hRT hJ hDC hrank hno hm₀ hne

end CFSG.Quasithin
