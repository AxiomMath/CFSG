module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
import CFSG.LocalAnalysis.UniquenessCase.UC22S13c
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.LocalAnalysis.UniquenessCase.UC22S13e
import CFSG.LocalAnalysis.UniquenessCase.UC22S13f
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen4a
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F13 Subgroup
open CFSG.RankThree.PartOne.Sec66T (fixSub mem_fixSub)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartTwo.Sec11 (CyclicSylowThreeOutAbelian)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s13g_orderOf_mk {M : Subgroup G} {x₀ : G} (hx₀M : x₀ ∈ M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hx₀r : orderOf x₀ = r) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ : Bar2 M) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine orderOf_eq_prime ?_ ?_
  · have hx₀1 : x₀ ^ r = 1 := by
      rw [← hx₀r]
      exact pow_orderOf_eq_one x₀
    have h1 : (⟨x₀, hx₀M⟩ : ↥M) ^ r = 1 := Subtype.ext (by simpa using hx₀1)
    rw [← map_pow, h1, map_one]
  · intro h1
    obtain ⟨k, hk⟩ := uc22s13b_isPGroup_pCoreOf M ⟨x₀, (uc22s13b_mem_pCoreOf_iff hx₀M).2 h1⟩
    have h3 : x₀ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h4 : r ∣ 2 ^ k := by
      rw [← hx₀r]
      exact orderOf_dvd_of_pow_eq_one h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h4))

theorem uc22s13g_L_side (hThin : PartTwo.ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (D : Data G) (hS : PartTwo.Setting13 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) {x : Bar2 D.M}
    (hxJ : x ∈ barImage D.M L) (hxr : orderOf x = r) :
    ⁅⁅centralizer ({x} : Set (Bar2 D.M)), centralizer ({x} : Set (Bar2 D.M))⁆,
        ⁅centralizer ({x} : Set (Bar2 D.M)), centralizer ({x} : Set (Bar2 D.M))⁆⁆ ≤
      centralizer (barImage D.M L : Set (Bar2 D.M)) ∧
    (Odd n → ∀ t : Bar2 D.M, t * x = x * t → ∀ k : ℕ, t ^ (2 ^ k) = 1 →
      t ∈ centralizer (barImage D.M L : Set (Bar2 D.M))) := by
  haveI : (barImage D.M L).Normal := PartTwo.s13_barImage_normal (hS.hyp131.normal L hL)
  obtain ⟨e⟩ := PartTwo.s13_bar_equiv hL
  have hTL : IsL2 ↥(barImage D.M L) n ∨ IsSz ↥(barImage D.M L) n :=
    hshape.imp (fun h => LieModel.of_mulEquiv e h) (fun h => LieModel.of_mulEquiv e h)
  obtain ⟨hC, hC2⟩ := uc22s13d_cent hTL hr hr2 hrn (x := ⟨x, hxJ⟩)
    (by rw [Subgroup.orderOf_mk, hxr])
  have hC' : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M L, a * x = x * a → b * x = x * b →
      a * b = b * a := fun a ha b hb hax hbx =>
    congrArg Subtype.val (hC ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext hax) (Subtype.ext hbx))
  have hC2' : ∀ a ∈ barImage D.M L, a * x = x * a → ∀ k : ℕ, a ^ (2 ^ k) = 1 → a = 1 :=
    fun a ha hax k hak =>
      congrArg Subtype.val (hC2 ⟨a, ha⟩ (Subtype.ext hax) k (Subtype.ext (by simpa using hak)))
  refine ⟨uc22s13d_commutator_le_centralizer _ (PartTwo.s13_outAbelian_barImage hThin hCyc D hS hL)
    hxJ hC', fun hn t htx k htk => ?_⟩
  have hna : ∃ a b : ↥(barImage D.M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := PartTwo.s13_nonabelian_bar hL
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  exact uc22s13d_mem_centralizer_of_two _
    (uc22s13d_center (PartTwo.s13_isSimple_barImage hThin D hS hL) hna)
    (fun β k hβ => uc22s13d_inner_of_two hTL hn β hβ) hxJ hC2' htx htk

theorem uc22s13g_exists_w (hThin : PartTwo.ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (D : Data G) (hS : PartTwo.Setting13 D)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hthin : Thin13 K) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (hexc : ¬ ((IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r) ∧ Even n))
    {x₀ g : G} (hx₀L : x₀ ∈ L) (hx₀r : orderOf x₀ = r)
    (hCM : centralizer ({x₀} : Set G) ≤ D.M) (hyM : g * x₀ * g⁻¹ ∈ D.M)
    (hyN : g * x₀ * g⁻¹ ∉ K ⊔ cMStar D.M K) :
    ∃ w ∈ K, ∃ hw : w ∈ D.M, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hw⟩ : Bar2 D.M) = q ∧
        g⁻¹ * w * g ∈ cMStar D.M L := by
  have hKM : K ≤ D.M := PartTwo.s13_le_of_mem_calC hK
  have hLM : L ≤ D.M := PartTwo.s13_le_of_mem_calC hL
  have hKn := hS.hyp131.normal K hK
  have hLn := hS.hyp131.normal L hL
  haveI : (barImage D.M K).Normal := PartTwo.s13_barImage_normal hKn
  have hx₀M : x₀ ∈ D.M := hLM hx₀L
  have hyr : (g * x₀ * g⁻¹) ^ r = 1 := by
    rw [conj_pow, ← hx₀r, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨hP, hT⟩ := uc22s13g_L_side hThin hCyc D hS hL hshape hr hr2 hrn
    (uc22s13b_mk_mem_barImage hx₀M hx₀L) (uc22s13g_orderOf_mk hx₀M hr hr2 hx₀r)
  set u : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g * x₀ * g⁻¹, hyM⟩ with hu
  set α : MulAut ↥(barImage D.M K) := MulAut.conjNormal (H := barImage D.M K) u with hα
  have hinn : α ∉ (MulAut.conj : ↥(barImage D.M K) →* MulAut ↥(barImage D.M K)).range :=
    fun h => hyN (uc22s13c_mem_sup_of_inner hKn hyM h)
  have hyr' : (⟨g * x₀ * g⁻¹, hyM⟩ : ↥D.M) ^ r = 1 := Subtype.ext (by simpa using hyr)
  have hαr : α ^ r = 1 := by rw [hα, hu, ← map_pow, ← map_pow, hyr', map_one, map_one]
  have hα1 : α ≠ 1 := fun h => hinn (by rw [h]; exact one_mem _)
  haveI : Fact r.Prime := ⟨hr⟩
  have hord : orderOf α = r := orderOf_eq_prime hαr hα1
  have hcomm : ∀ f ∈ fixSub α, u * (f : Bar2 D.M) = f * u := by
    intro f hf
    have h1 : ((α f : ↥(barImage D.M K)) : Bar2 D.M) = f := congrArg Subtype.val (mem_fixSub.1 hf)
    rw [hα, MulAut.conjNormal_apply] at h1
    calc u * (f : Bar2 D.M) = u * f * u⁻¹ * u := by group
      _ = f * u := by rw [h1]
  obtain ⟨e⟩ := PartTwo.s13_bar_equiv hK
  have hodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨a, ha⟩ : ∃ a : ℕ, IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a := by
    rcases (PartTwo.s13_list_bar hThin D hK hthin).2 with ⟨a, ha⟩ | ⟨p, hp, hp2, hpL⟩ | ⟨a, ha⟩ | hJ
    · exact ⟨a, Or.inl ha⟩
    · exact absurd (uc22s13e_inner_of_odd (T := ↥(barImage D.M K))
        (Or.inl ⟨p, hp, hp2, LieModel.of_mulEquiv e hpL⟩) hodd hαr) hinn
    · exact ⟨a, Or.inr ha⟩
    · obtain ⟨f⟩ := hJ
      exact absurd (uc22s13e_inner_of_odd (T := ↥(barImage D.M K))
        (Or.inr (Nonempty.intro (e.symm.trans f))) hodd hαr) hinn
  have hTa : IsL2 ↥(barImage D.M K) a ∨ IsSz ↥(barImage D.M K) a :=
    ha.imp (fun h => LieModel.of_mulEquiv e h) (fun h => LieModel.of_mulEquiv e h)
  obtain ⟨hfix1, hfix2⟩ := uc22s13e_fix hTa hr hr2 hord hinn
  by_cases har : a = r
  · have hn : Odd n := Nat.not_even_iff_odd.1 fun hev => hexc ⟨by rw [← har]; exact ha, hev⟩
    obtain ⟨z, hz, t, ht, ⟨k, htk⟩, q, hq, hq2, hzt⟩ := hfix2 har
    have htk' : (t : Bar2 D.M) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val htk
    obtain ⟨w, hwK, hwM, hwz, hwL⟩ := uc22s13f_exists_two hKM hKn hLM hLn hx₀M hyM hCM hr hr2 hyr
      (hT hn) z.2 t.2 (hcomm z hz) (hcomm t ht) htk'
    refine ⟨w, hwK, hwM, q, hq, hq2, ?_, hwL⟩
    have h1 : ((⁅z, t⁆ : ↥(barImage D.M K)) : Bar2 D.M) = ⁅(z : Bar2 D.M), (t : Bar2 D.M)⁆ :=
      map_commutatorElement (barImage D.M K).subtype z t
    rw [hwz, ← h1, Subgroup.orderOf_coe, hzt]
  · obtain ⟨hperf, z, hz, q, hq, hq2, hzq⟩ := hfix1 har
    have hFF : ⁅(fixSub α).map (barImage D.M K).subtype,
        (fixSub α).map (barImage D.M K).subtype⁆ = (fixSub α).map (barImage D.M K).subtype := by
      rw [← map_commutator, hperf]
    obtain ⟨w, hw, hwM, hwz⟩ := uc22s13f_exists_perfect hKM hKn hyM hr hr2 hyr
      (F := (fixSub α).map (barImage D.M K).subtype) (by rintro _ ⟨f, -, rfl⟩; exact f.2)
      (by rintro _ ⟨f, hf, rfl⟩; exact hcomm f hf) hFF (z := (z : Bar2 D.M)) ⟨z, hz, rfl⟩
    have hwK : w ∈ K :=
      ((commutator_le_self _).trans ((commutator_le_self _).trans inf_le_left)) hw
    exact ⟨w, hwK, hwM, q, hq, hq2, by rw [hwz, Subgroup.orderOf_coe, hzq],
      uc22s13f_mem_cMStar_of_derived hx₀M hCM hP hw⟩

theorem uc22s13g_endgame (hThin : PartTwo.ThinList13) (hCyc : CyclicSylowThreeOutAbelian)
    (D : Data G) (hS : PartTwo.Setting13 D) (h847 : R847Four D) (hsig : D.sig.Nonempty)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hthin : Thin13 K) {g x₀ : G}
    (hx₀L : x₀ ∈ L) (hyM : g * x₀ * g⁻¹ ∈ D.M) (hyo : Odd (orderOf (g * x₀ * g⁻¹))) {w : G}
    (hwK : w ∈ K) (hwM : w ∈ D.M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hwq : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hwM⟩ : Bar2 D.M) = q)
    (hwL : g⁻¹ * w * g ∈ cMStar D.M L) : g * x₀ * g⁻¹ ∈ K ⊔ cMStar D.M K := by
  have hqw : q ∣ orderOf w := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) (⟨w, hwM⟩ : ↥D.M)
    rwa [hwq, Subgroup.orderOf_mk] at h1
  have hwk : orderOf (w ^ (orderOf w / q)) = q := orderOf_pow_orderOf_div (orderOf_pos w).ne' hqw
  have hAK : zpowers (w ^ (orderOf w / q)) ≤ K := (zpowers_le).2 (K.pow_mem hwK _)
  have hAq : Nat.card (zpowers (w ^ (orderOf w / q))) = q := by rw [Nat.card_zpowers, hwk]
  obtain ⟨p, hp⟩ := hsig
  have hNA : normalizer ((zpowers (w ^ (orderOf w / q)) : Subgroup G) : Set G) ≤ D.M :=
    h847 K hK _ hAK q hq hq2 hAq p hp hthin
  have hconj : ∀ u : G, (MulAut.conj g⁻¹).toMonoidHom u = g⁻¹ * u * g := fun u => by
    simp [MulAut.conj_apply]
  set A := (zpowers (w ^ (orderOf w / q))).map (MulAut.conj g⁻¹).toMonoidHom with hA
  have hAL : A ≤ cMStar D.M L := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    rw [map_zpow, map_pow, hconj]
    exact zpow_mem (pow_mem hwL _) i
  have hAp : IsPGroup q A :=
    IsPGroup.of_card (n := 1) (by rw [hA, PartTwo.s13_card_map_conj, hAq, pow_one])
  have hcent : L ⊓ centralizer (A : Set G) ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom :=
    inf_le_right.trans ((centralizer_le_normalizer _).trans
      (PartTwo.s13_normalizer_map_conj_le g⁻¹ hNA))
  exact uc22s13b_mem_of_odd hq hq2 (PartTwo.s13_le_of_mem_calC hL) (hS.hyp131.normal L hL)
    hL.2.1 hAp (hAL.trans (uc22s13f_cMStar_le _ _)) hAL hcent
    (sup_le (PartTwo.s13_le_of_mem_calC hK) (uc22s13f_cMStar_le _ _))
    (uc22s13b_commutator_le (hS.hyp131.normal K hK)
      (PartTwo.s13_outAbelian_barImage hThin hCyc D hS hK)) hyM
    ⟨x₀, hx₀L, by simp [MulAut.conj_apply]⟩ hyo

theorem uc22s13g_mem (hThin : PartTwo.ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (D : Data G) (hS : PartTwo.Setting13 D)
    (h847 : R847Four D) (hsig : D.sig.Nonempty) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hthin : Thin13 K) {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hexc : ¬ ((IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r) ∧ Even n)) {x₀ g : G} (hx₀L : x₀ ∈ L)
    (hx₀r : orderOf x₀ = r) (hCM : centralizer ({x₀} : Set G) ≤ D.M)
    (hyM : g * x₀ * g⁻¹ ∈ D.M) : g * x₀ * g⁻¹ ∈ K ⊔ cMStar D.M K := by
  by_contra hyN
  obtain ⟨w, hwK, hwM, q, hq, hq2, hwq, hwL⟩ :=
    uc22s13g_exists_w hThin hCyc D hS hL hK hthin hshape hr hr2 hrn hexc hx₀L hx₀r hCM hyM hyN
  have hyo : Odd (orderOf (g * x₀ * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx₀r]
    exact hr.odd_of_ne_two hr2
  exact hyN (uc22s13g_endgame hThin hCyc D hS h847 hsig hL hK hthin hx₀L hyM hyo hwK hwM hq hq2
    hwq hwL)

theorem r133_of (hThin : PartTwo.ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (D : Data G) (h846 : F08.R846 D) (h847 : R847Four D)
    (hsig : D.sig.Nonempty) : PartTwo.R133 D := by
  intro sig_eq hH L hL K hK n hshape s hs hsn r hr hrs X hXL hXr g hg hYM
  have hS : PartTwo.Setting13 D := ⟨sig_eq, hH⟩
  have hnu := uc22s13c_not_isU3 D hH h846 hL hK hshape hs hsn hr hrs hXL hXr hg hYM
  refine ⟨?_, hnu⟩
  by_cases hexc : (IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r) ∧ Even n
  · exact Or.inr hexc
  refine Or.inl ?_
  have hr2 : r ≠ 2 := by
    have := PartTwo.s13_seven_le_of_dvd hs hr hrs
    omega
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hthin := PartTwo.s13_thin_of_not_unitary D hS hK hnu
  rintro _ ⟨x₀, hx₀X, rfl⟩
  have hconj : (MulAut.conj g).toMonoidHom x₀ = g * x₀ * g⁻¹ := by simp [MulAut.conj_apply]
  have hyM : g * x₀ * g⁻¹ ∈ D.M := by
    rw [← hconj]
    exact hYM ⟨x₀, hx₀X, rfl⟩
  rw [hconj]
  by_cases hx1 : x₀ = 1
  · rw [hx1, mul_one, mul_inv_cancel]
    exact one_mem _
  have hx₀r : orderOf x₀ = r := by
    haveI : Fact r.Prime := ⟨hr⟩
    refine orderOf_eq_prime ?_ hx1
    have h1 := Subgroup.orderOf_dvd_natCard X hx₀X
    rw [hXr] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hZL : zpowers x₀ ≤ L := (zpowers_le).2 (hXL hx₀X)
  have hZr : Nat.card (zpowers x₀) = r := by rw [Nat.card_zpowers, hx₀r]
  have hNZ := (hH.uniq L hL n hshape s hs hsn r hr hrs (zpowers x₀) hZL hZr).1
  have hCM : centralizer ({x₀} : Set G) ≤ D.M := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact (centralizer_le_normalizer _).trans hNZ
  exact uc22s13g_mem hThin hCyc D hS h847 hsig hL hK hthin hshape hr hr2 hrn hexc (hXL hx₀X) hx₀r
    hCM hyM

end CFSG.LocalAnalysis.UniquenessCase.UC22
