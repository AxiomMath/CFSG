module

public import CFSG.LocalAnalysis.StandardType.GGSpNbrApriori
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflFrames
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeA
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeD
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeE
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofJoin

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.StandardType.SpJoin CFSG.StandardType.SpJoinRefl

section Join

variable {G : Type} [Group G] [Finite G]

theorem ggWeylJoin_typeB {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    (hNoTr : GGNoTransvection p Bs) {AL AK R : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) (AL ⊔ AK))
    {x y y' : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hy' : y' ∈ Bs)
    (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hfy : ∀ ψ ∈ AK, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hfy' : ∀ ψ ∈ R, ((ψ ⟨y', hy'⟩ : ↥Bs) : G) = y')
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL) (hcK : 2 ^ n * n.factorial ≤ Nat.card AK)
    (hcR : 2 ^ n * n.factorial ≤ Nat.card R)
    (hCR : ∀ b : ↥Bs, (∀ ψ ∈ R, ψ b = b) → (b : G) ∈ Subgroup.zpowers y')
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hy'x : y' ∉ Subgroup.zpowers x)
    (hy'D : y' ∈ Subgroup.closure ({x, y} : Set G))
    (hind : ∀ φ ∈ AL ⊔ R, φ ∈ ggInduced ⊤ Bs)
    (hW : GGWeylReflectionGroup p (AL ⊔ R)) :
    GGWeylOfType p (CoxeterMatrix.B (n + 1)) (AL ⊔ R) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ n := by omega
  have hAL : AL ≤ AL ⊔ AK := le_sup_left
  have hAK : AK ≤ AL ⊔ AK := le_sup_right
  have hALR : AL ≤ AL ⊔ R := le_sup_left
  have hcard : Nat.card AL = 2 ^ n * n.factorial :=
    card_eq_two_pow_mul_factorial_of_frame hp hp2 hn3 hBs hrank hA hAL hx hfx hcL hx1
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ AL ⊔ R, ψ b = b) → b = 1 :=
    eq_one_of_fixed_weylJoin hp hp2 hn3 hBs hrank hA hAL hx hy' hfx hcL hCR hx1 hy'x
  have hrk : ∀ {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}, GGWeylOfType p M (AL ⊔ R) →
      n + 1 ≤ Fintype.card ι := by
    intro ι _ M hM
    have h := card_le_pow_of_weylOfType hM hfix
    rw [hrank] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ιV.toEquiv)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) V = n + 1 := by
    have h1 : Nat.card V = p ^ (n + 1) := by rw [← card_eq_of_ggLin ιV, hrank]
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [h1, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective hp.two_le h2).symm
  rcases ggWeylReflectionGroup_cases hW with ⟨r, hr, hA'⟩ | ⟨r, hr, hB⟩ | ⟨r, hr, hD⟩ | hE6 | hE7 |
    hE8 | hF4 | hG2
  ·
    exfalso
    have h1 : n + 1 ≤ r := by simpa using hrk hA'
    obtain ⟨h, α, hP⟩ := exists_cartan_pairing_A hp2 hNoTr hr hA' hind ιV
    have h2 : r ≤ n + 2 := by
      have := le_finrank_add_one_of_cartanA h α hP
      omega
    exact not_weylOfType_A_of_card hn h1 h2 hA' hALR hcard
  ·
    have h1 : n + 1 ≤ r := by simpa using hrk hB
    have h2 : r ≤ n + 1 := by
      have := pow_le_card_of_weylOfType_B hp hp2 hBs hr hB
      rw [hrank] at this
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp this
    obtain rfl : r = n + 1 := le_antisymm h2 h1
    exact hB
  ·
    exfalso
    have h1 : n + 1 ≤ r := by simpa using hrk hD
    obtain ⟨h, α, hP⟩ := exists_cartan_pairing_D hp2 hNoTr hr hD hind ιV
    have h2 : r ≤ n + 1 := by
      have := le_finrank_of_cartanD hp2 (by omega) h α hP
      omega
    obtain rfl : r = n + 1 := le_antisymm h2 h1
    exact not_weylOfType_D_of_orbit (by omega) hD hy' hfy' hcR
      (two_mul_le_card_orbit_of_frame hp hp2 hn3 hBs hrank hA hAL hAK hx hy hy' hfx hfy hcL hcK
        hx1 hyx hy'x hy'D)
  ·
    exfalso
    obtain ⟨t, ht, s, hs, htr, hsr, hts⟩ :=
      exists_order_four_of_frame hp hp2 hn3 hBs hrank hA hAL hx hfx hcL hx1
    exact not_weylOfType_tag_of_order_four hp2 hBs hNoTr (Or.inl rfl) (weylOfType_tag_E6 hE6)
      hind (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_left hs) htr hsr hts
  ·
    exfalso
    obtain ⟨t, ht, s, hs, htr, hsr, hts⟩ :=
      exists_order_four_of_frame hp hp2 hn3 hBs hrank hA hAL hx hfx hcL hx1
    exact not_weylOfType_tag_of_order_four hp2 hBs hNoTr (Or.inr (Or.inl rfl))
      (weylOfType_tag_E7 hE7) hind (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_left hs) htr hsr
      hts
  ·
    exfalso
    obtain ⟨t, ht, s, hs, htr, hsr, hts⟩ :=
      exists_order_four_of_frame hp hp2 hn3 hBs hrank hA hAL hx hfx hcL hx1
    exact not_weylOfType_tag_of_order_four hp2 hBs hNoTr (Or.inr (Or.inr rfl))
      (weylOfType_tag_E8 hE8) hind (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_left hs) htr hsr
      hts
  ·
    exfalso
    have := hrk hF4
    simp only [Fintype.card_fin] at this
    omega
  ·
    exfalso
    have := hrk hG2
    simp only [Fintype.card_fin] at this
    omega

theorem ggSpLine_of_weylJoin {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    (hNoTr : GGNoTransvection p Bs) {AL AK R : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) (AL ⊔ AK))
    {x y y' : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hy' : y' ∈ Bs)
    (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hfy : ∀ ψ ∈ AK, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hfy' : ∀ ψ ∈ R, ((ψ ⟨y', hy'⟩ : ↥Bs) : G) = y')
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL) (hcK : 2 ^ n * n.factorial ≤ Nat.card AK)
    (hcR : 2 ^ n * n.factorial ≤ Nat.card R)
    (hCR : ∀ b : ↥Bs, (∀ ψ ∈ R, ψ b = b) → (b : G) ∈ Subgroup.zpowers y')
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hy'x : y' ∉ Subgroup.zpowers x)
    (hy'D : y' ∈ Subgroup.closure ({x, y} : Set G))
    (hind : ∀ φ ∈ AL ⊔ R, φ ∈ ggInduced ⊤ Bs)
    (hW : GGWeylReflectionGroup p (AL ⊔ R)) :
    Subgroup.zpowers y' = Subgroup.zpowers y :=
  zpowers_eq_of_two_frames hp hp2 (by omega) hBs hrank hA
    (ggWeylJoin_typeB hp hp2 hn hBs hrank hNoTr hA hx hy hy' hfx hfy hfy' hcL hcK hcR hCR hx1 hyx
      hy'x hy'D hind hW)
    (le_inf le_sup_left le_sup_left) le_sup_right le_sup_right hx hy hy' hfx hfy hfy' hcL hcK hcR
    hx1 hyx hy'x hy'D

end Join

end CFSG.StandardType
