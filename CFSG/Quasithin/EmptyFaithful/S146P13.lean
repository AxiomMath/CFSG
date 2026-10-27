module

public import CFSG.Quasithin.EmptyFaithful.S146C26Solv
public import CFSG.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146P2
public import CFSG.Quasithin.EmptyFaithful.T1515Der4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

theorem stage14615_of_fine_inputsPM4
    (h12 : Stage14612PartP) (h13 : Stage14613LabP) (h14 : Stage14614)
    (iS : Input14615SetupP) (iG : Input14615GP) (iH : Input14615HypP) (iA : Input14615A3P)
    (iJ : Input14615JP) (iO : Input14615ContraOuterP) (iI : Input14615ContraInnerP) :
    Stage14615 := by
  intro G _ _ T M S H PQ p hred hmax
  obtain ⟨hp, H₀, H₁, H₂, t, hdec⟩ := h12 G T M S H PQ p hred hmax
  by_contra hne
  have hp5 : p = 5 := by omega
  have hAt := (stage14614At_iff T H p).mp (stage14614At_of h14 S hred hmax)
  have h14' : Stage14614C1 T H p ∨ Stage14614C4 T H p := by
    rcases hAt with c1 | c2 | c3 | c4
    · exact Or.inl c1
    · exact absurd c2.1 hne
    · exact absurd c3.1 hne
    · exact Or.inr c4
  have hctx : ∃ (H₀' H₁' H₂' : Subgroup G) (t' : G), IsDecP T M H p H₀' H₁' H₂' t' ∧
      Ctx15 T M H p H₁' := by
    rcases h13 G T M S H PQ p hred H₀ H₁ H₂ t hdec with (h1 | h1) | (h1 | h1)
    · exact absurd h1.1 hne
    · exact ⟨H₀, H₁, H₂, t, hdec, hp5, h1, h14'⟩
    · exact absurd h1.1 hne
    · exact ⟨H₀, H₂, H₁, t⁻¹, hdec.swap, hp5, h1, h14'⟩
  obtain ⟨H₀', H₁', H₂', t', hdec', hctx'⟩ := hctx
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨K₁, K₂, s, hset⟩ := iS G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx'
  have hctxc := hctx'
  obtain ⟨-, ⟨-, -, γ, γ', g, hF8, -, -, hA, hZ⟩, -⟩ := hctxc
  have hcentA : K₂ ≤ Subgroup.centralizer
      (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G) := hset.centralizes S hred hA
  have hgN : (g : G) ∈ g2_14615 K₂ :=
    iG G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset γ γ' g hF8 hA hZ hcentA
  have hgG : (g : G) ∉ mcOf T := by
    intro hg
    obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
    apply S.conj_not_mem_Z hH hF8 hz hz1
    have hgN' : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
      rw [S.normalizer_Z]
      exact hg
    exact (Subgroup.mem_normalizer_iff.mp hgN' z).mp hz
  have hG₂ : ¬ g2_14615 K₂ ≤ mcOf T := fun hle => hgG (hle hgN)
  obtain ⟨hHyp, hchar, hnot⟩ :=
    iH G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset hG₂
  have hFchar : CharTwo (oTwoFIn (g2_14615 K₂)) :=
    charTwo_oTwoFIn_of_charTwo hchar
  have hF₂ : oTwoFIn (g2_14615 K₂) ≤ g12_14615 T K₂ := by
    obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two_solv_P16 hHyp hFchar
    have hLbM : ∀ i, Lb i ≤ g12_14615 T K₂ := fun i =>
      iA G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset hG₂ (Lb i)
        (hLb i).1 (hLb i).2
    intro x hx
    obtain ⟨m, hm, y, hy, hxy⟩ := hprod x hx
    rw [hxy]
    refine (g12_14615 T K₂).mul_mem hm.1 (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hLbM i (hy i)
  have hPcore : pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ := C2Six.pCoreOf_le_oTwoFIn.trans hF₂
  have hJex : ∃ J : Subgroup G, J ∈ cComp (g2_14615 K₂) ∧
      CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) ∧ ¬ J ≤ g12_14615 T K₂ := by
    by_contra hno
    have hno' : ∀ L : Subgroup G, L ∈ cComp (g2_14615 K₂) →
        CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → L ≤ g12_14615 T K₂ := by
      intro L hL hq
      by_contra hLle
      exact hno ⟨L, hL, hq, hLle⟩
    exact hnot (oTwoFstarIn_le_of_components1516 hPcore hF₂ hno')
  obtain ⟨J, hJc, hJq, hJle⟩ := hJex
  obtain ⟨hJK, hJ5⟩ := iJ G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset hG₂ J
    hJc hJq hJle
  by_cases hK : K₁ ≤ J
  · exact iI G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset hG₂ J hJc hJq hJle
      hJK hJ5 hK
  · exact iO G T M S H PQ p hred hmax H₀' H₁' H₂' t' hdec' hctx' K₁ K₂ s hset hG₂ J hJc hJq hJle
      hJK hJ5 hK

end CFSG.Quasithin
