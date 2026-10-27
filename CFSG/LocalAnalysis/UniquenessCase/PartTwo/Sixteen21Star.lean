module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

private theorem one_le_pRank_of_dvd_card {Q : Type*} [Group Q] [Finite Q] (J : Subgroup Q)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card J) : 1 ≤ CFSG.Open.pRank r J := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hd
  have hx' : orderOf (x : Q) = r := (Subgroup.orderOf_coe x).trans hx
  refine CFSG.SectionRank.le_pRank (p := r) (H := J) (E := Subgroup.zpowers (x : Q)) (k := 1)
    hr.one_lt (Subgroup.zpowers_le.2 x.2) ?_ ?_
  · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hx']; exact pow_orderOf_eq_one (x : Q))
  · rw [Nat.card_zpowers, hx', pow_one]

theorem card_le_four_of_hyp16 {D : Data G} {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    Nat.card V₀ ≤ 4 := by
  have hV₀ : IsPGroup 2 V₀ := h.hyp125.pairFacts.elemAbelian₀.isPGroup
  rw [card_eq_two_pow_mSub hV₀]
  exact Nat.pow_le_pow_right (by norm_num) h.small

theorem one_le_pRank_of_fix_mod {M T V₀ V V' X : Subgroup G} (h : Hyp123 M T V₀ V)
    (hV : IsElemAbelian 2 V) (hV₀ : Nat.card V₀ ≤ 4) (hXM : X ≤ M)
    (hV' : V' = V₀ ∨ ∀ x ∈ X, ∀ u ∈ V', x * u = u * x)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrk : 2 ≤ CFSG.Open.pRank p M)
    {φ : MulAut (Vtil V' V hV)} (hφ : φ ∈ barSub V' V hV X) (hord : orderOf φ = p)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hfix : φ (mkTil V' V hV (IntMod.mk hV ⟨v, hv⟩)) = mkTil V' V hV (IntMod.mk hV ⟨v, hv⟩)) :
    1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  rcases hV' with rfl | hcomm
  · by_cases hv0 : v ∈ V'
    · exact one_le_pRank_of_mem_small (hyp123_pairFacts h).le_normalizer₀ hV₀ hp hrk hv0 hv1
    · exact one_le_pRank_of_dvd_cElt h hV₀ hp hp2 hv hv0
        (dvd_card_cElt_of_mem_mbar hV (barSub_mono V' V hV hXM hφ) hord hv hfix)
  · obtain ⟨g, hgX, hgact⟩ := (mem_barSub V' V hV X φ).1 hφ
    have hfix' : actTil V' V hV g (mkTil V' V hV (IntMod.mk hV ⟨v, hv⟩)) =
        mkTil V' V hV (IntMod.mk hV ⟨v, hv⟩) := by
      rw [hgact]; exact hfix
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix'
    have hu : (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ V' := hfix'
    have hguV : (g : G) * v * (g : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer V' V g.2) v).1 hv
    have huV : (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ V := V.mul_mem hguV (V.inv_mem hv)
    generalize hu_def : (g : G) * v * (g : G)⁻¹ * v⁻¹ = u at hu huV
    have hgu : (g : G) * u = u * (g : G) := hcomm (g : G) hgX u hu
    have hu2 : u * u = 1 := by rw [← pow_two]; exact hV.2 u huV
    have hav : (g : G) * v = u * v * (g : G) := by rw [← hu_def]; group
    have hg2 : (g : G) ^ 2 * v = v * (g : G) ^ 2 := by
      rw [pow_two]
      calc (g : G) * (g : G) * v = (g : G) * ((g : G) * v) := mul_assoc _ _ _
        _ = (g : G) * (u * v * (g : G)) := by rw [hav]
        _ = ((g : G) * u) * v * (g : G) := by group
        _ = (u * (g : G)) * v * (g : G) := by rw [hgu]
        _ = u * ((g : G) * v) * (g : G) := by group
        _ = u * (u * v * (g : G)) * (g : G) := by rw [hav]
        _ = (u * u) * v * ((g : G) * (g : G)) := by group
        _ = v * ((g : G) * (g : G)) := by rw [hu2, one_mul]
    have hmem : (g : G) ^ 2 ∈ M ⊓ centralizer ({v} : Set G) :=
      ⟨M.pow_mem (hXM hgX) 2, Subgroup.mem_centralizer_singleton_iff.2 hg2⟩
    have hcop : (orderOf φ).Coprime 2 := by
      rw [hord]
      exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
    have hord2 : orderOf (actTil V' V hV (g ^ 2)) = p := by
      rw [map_pow, hgact, Nat.Coprime.orderOf_pow hcop, hord]
    have hdvd1 : p ∣ orderOf (g ^ 2 : stabTil V' V) := by
      rw [← hord2]
      exact orderOf_map_dvd (actTil V' V hV) (g ^ 2)
    have hdvd2 : orderOf ((g : G) ^ 2) ∣ Nat.card (M ⊓ centralizer ({v} : Set G) : Subgroup G) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have hdvd3 : orderOf (g ^ 2 : stabTil V' V) = orderOf ((g : G) ^ 2) :=
      (Subgroup.orderOf_coe (g ^ 2)).symm
    exact one_le_pRank_of_dvd_card _ hp (hdvd1.trans (hdvd3 ▸ hdvd2))

theorem commute_of_mem_v1Sub {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp151 D V₀ V L) (h0 : V₀ = ⊥) {x : G} (hx : x ∈ L) {u : G}
    (hu : u ∈ v1Sub D.M V₀ V hV L) : x * u = u * x := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have huV : u ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hu
  have hxstab : x ∈ stabTil V₀ V := hMs (h.le hx)
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) ∈
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
    rw [mem_imgTil]
    exact ⟨IntMod.mk hV ⟨u, huV⟩, hu, rfl⟩
  have hxbar : actTil V₀ V hV ⟨x, hxstab⟩ ∈ barSub V₀ V hV (conjSubgroup L (1 : G)) := by
    rw [conjSubgroup_one]
    exact actTil_mem_barSub V₀ V hV hx hxstab
  have h1 := mem_fixV.mp (hfix hmem) (actTil V₀ V hV ⟨x, hxstab⟩) hxbar
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
  have h2 : x * u * x⁻¹ * u⁻¹ ∈ V₀ := h1
  rw [h0, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
  exact h2

theorem one_le_pRank_of_fix_vStar {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 2 ≤ CFSG.Open.pRank p D.M) {φ : MulAut (vStar D.M V₀ V hV L)}
    (hφ : φ ∈ lStar D.M V₀ V hV L) (hord : orderOf φ = p) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hfix : φ (mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩)) =
      mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩)) :
    1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
  refine one_le_pRank_of_fix_mod h16.hyp125.1 hV (card_le_four_of_hyp16 h16) h151.le
    (V' := v1Sub D.M V₀ V hV L) (X := L) ?_ hp hp2 hrk hφ hord hv hv1 hfix
  by_cases h0 : V₀ = ⊥
  · exact Or.inr fun x hx u hu => commute_of_mem_v1Sub hV h151 h0 hx hu
  · exact Or.inl (v1Sub_of_ne_bot D.M V₀ V hV L h0)

theorem one_le_pRank_of_forall_fix_vStar {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : 2 ≤ CFSG.Open.pRank p D.M)
    (hfix : ∀ w : vStar D.M V₀ V hV L, ∃ φ ∈ lStar D.M V₀ V hV L, orderOf φ = p ∧ φ w = w) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  obtain ⟨φ, hφ, hord, hφw⟩ := hfix (mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩))
  exact one_le_pRank_of_fix_vStar hV h16 h151 hp hp2 hrk hφ hord hv hv1 hφw

theorem one_le_pRank_of_forall_fix_vTil {D : Data G} {V₀ V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (h16 : Hyp16 D V₀ V) (hXM : X ≤ D.M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : 2 ≤ CFSG.Open.pRank p D.M)
    (hfix : ∀ w : Vtil V₀ V hV, w ≠ 1 → ∃ φ ∈ barSub V₀ V hV X, orderOf φ = p ∧ φ w = w) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact one_le_pRank_of_mem_small h16.hyp125.pairFacts.le_normalizer₀
      (card_le_four_of_hyp16 h16) hp hrk hv0 hv1
  · have hw : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ≠ 1 := by
      intro h1
      rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff] at h1
      have h2 : v * (1 : G)⁻¹ ∈ V₀ := h1
      exact hv0 (by simpa using h2)
    obtain ⟨φ, hφ, hord, hφw⟩ := hfix _ hw
    exact one_le_pRank_of_dvd_cElt h16.hyp125.1 (card_le_four_of_hyp16 h16) hp hp2 hv hv0
      (dvd_card_cElt_of_mem_mbar hV (barSub_mono V₀ V hV hXM hφ) hord hv hφw)

theorem one_le_pRank_of_not_dvd_mbar {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h16 : Hyp16 D V₀ V) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 2 ≤ CFSG.Open.pRank p D.M) (hk : k ≤ CFSG.Open.pRank p D.M)
    (hcard : ¬ p ^ k ∣ Nat.card (Mbar D.M V₀ V hV)) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
  obtain ⟨y, hy, hord⟩ := exists_mem_cTilde_of_not_dvd hV
    (le_stabTil h16.hyp125.pairFacts.le_normalizer h16.hyp125.pairFacts.le_normalizer₀)
    hp hk hcard
  exact one_le_pRank_of_mem_cTilde h16.hyp125.1 (card_le_four_of_hyp16 h16) hp hp2 hrk hy hord

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
