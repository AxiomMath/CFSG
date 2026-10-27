module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch4Sec4W443
import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
import CFSG.Quasithin.Vol2.KGFact4413Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem uc22s2114_rhoInf_eq (L : Subgroup G) (m : ↥(normalizer (L : Set G))) :
    rhoInf L m = inducedBarInfAutHom L m :=
  rfl

theorem uc22s2114_exists_map_eq {L T : Subgroup G} (hTL : IsSylowOf 2 (T ⊓ L) L) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (T : Set G)) :
    ∃ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ ∧
      U.map (inducedBarInfAutHom L ⟨b, hbL⟩).toMonoidHom = U := by
  obtain ⟨Q, hQ⟩ := hTL
  refine ⟨(Q : Subgroup ↥L).map (piInf L), isSylowTwoOf_map_piInf L Q, ?_⟩
  have hbS : b ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 hbT y, ← mem_normalizer_iff.1 hbL y]
  have htS : b ∈ normalizer (((Q : Subgroup ↥L).map L.subtype ⊔ OInf L : Subgroup G) : Set G) := by
    rw [hQ]
    exact mem_normalizer_sup_of_mem hbS (normalizer_le_normalizer_OInf L hbL)
  rw [← uc22s2114_rhoInf_eq]
  exact rhoInf_map_eq L Q hbL htS

theorem uc22s2114_exists_of_inner {Y : Type} [Group Y] (hZ : center Y = ⊥) {U : Subgroup Y}
    {α : MulAut Y} (hαU : U.map α.toMonoidHom = U) (hin : α ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hα1 : α ≠ 1) {r : ℕ} (hαr : α ^ r = 1) :
    ∃ y ∈ normalizer (U : Set Y), y ≠ 1 ∧ y ^ r = 1 := by
  obtain ⟨y, rfl⟩ := hin
  refine ⟨y, ?_, fun hy => hα1 (by rw [hy, map_one]), ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h := mem_map_of_mem (MulAut.conj y).toMonoidHom hx
      rwa [hαU] at h
    · intro hx
      rw [← hαU] at hx
      obtain ⟨u, hu, hux⟩ := mem_map.1 hx
      have e : u = x := by
        simpa [MulAut.conj_apply] using hux
      rwa [← e]
  · rw [← map_pow] at hαr
    have hc : y ^ r ∈ center Y := by
      rw [mem_center_iff]
      intro x
      have h := DFunLike.congr_fun hαr x
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * y ^ r = y ^ r * x * (y ^ r)⁻¹ * y ^ r := by rw [h]
        _ = y ^ r * x := by group
    rwa [hZ, mem_bot] at hc

theorem uc22s2114_card_outer_dvd {Y : Type} [Group Y] [Finite Y] {n m : ℕ}
    (h : FieldBorel Y n (2 ^ m - 1)) : Nat.card (Outer Y) ∣ m := by
  obtain ⟨U, H, F, D⟩ := h
  have hsurj : Function.Surjective ((QuotientGroup.mk' (inner Y)).comp F.subtype) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, σ, hσ, rfl⟩ := exists_conj_mul_of_borel D.borel α
    refine ⟨⟨σ, hσ⟩, ?_⟩
    have h1 : QuotientGroup.mk' (inner Y) (MulAut.conj y) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨y, rfl⟩)
    show QuotientGroup.mk' _ σ = QuotientGroup.mk' _ (MulAut.conj y * σ)
    rw [map_mul, h1, one_mul]
  exact (Subgroup.card_dvd_of_surjective hsurj).trans D.card_F_dvd

theorem uc22s2114_not_dvd_of_dvd {r f d m : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hf : IsPowTwo f)
    (hd : 0 < d) (hd6 : d ≤ 6) (hm : m ∣ 2 * f * d) : ¬ r ∣ m := by
  intro hrm
  obtain ⟨k, rfl⟩ := hf
  rcases (Nat.Prime.dvd_mul hr).1 (hrm.trans hm) with h | h
  · have h2 : r ∣ 2 ^ (k + 1) := by rwa [pow_succ']
    have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd hd h
    omega

theorem uc22s2114_eq_one_of_pow_mem {Y : Type} [Group Y] {U : Subgroup Y} (hU : IsPGroup 2 U)
    {y : Y} {r m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrm : ¬ r ∣ m) (hym : y ^ m ∈ U)
    (hyr : y ^ r = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hU ⟨_, hym⟩
  have h1 : y ^ (m * 2 ^ k) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime r (m * 2 ^ k) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hr).2 hrm)
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).2 hr2))
  have h2 := pow_gcd_eq_one.2 ⟨hyr, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at h2

theorem uc22s2114_exists_of_borel {M L T : Subgroup G} (hL : L ∈ calC M)
    (hTL : IsSylowOf 2 (T ⊓ L) L) {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hbT : b ∈ normalizer (T : Set G)) {r : ℕ} (hbr : b ^ r = 1)
    (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1)
    (hin : ∀ α : MulAut (BarInf L), α ^ r = 1 →
      α ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    ∃ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ ∧
      ∃ y ∈ normalizer (U : Set (BarInf L)), y ≠ 1 ∧ y ^ r = 1 := by
  obtain ⟨U, hU, hαU⟩ := uc22s2114_exists_map_eq hTL hbL hbT
  have hαr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := Subtype.ext (by simpa using hbr)
    rw [this, map_one]
  exact ⟨U, hU, uc22s2114_exists_of_inner (center_barInf_eq_bot hL.2.2) hαU (hin _ hαr) hb1 hαr⟩

theorem uc22s2114_dvd_of_borel_l3 {M L T : Subgroup G} (hL : L ∈ calC M)
    (hTL : IsSylowOf 2 (T ⊓ L) L) {f : ℕ} (hX : IsL3 (BarInf L) f) (hf : IsPowTwo f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (T : Set G)) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) (hbr : b ^ r = 1) (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1) :
    r ∣ 2 ^ f - 1 := by
  have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl Nat.prime_two (LieModel.admissible hX).2.1
    (LieModel.statedClassicalModel hX (by decide))).1
  obtain ⟨U, hU, y, hy, hy1, hyr⟩ := uc22s2114_exists_of_borel hL hTL hbL hbT hbr hb1
    fun _ => uc22p2214_out_mem_of_card_dvd hd hr (uc22s2114_not_dvd_of_dvd hr hr7 hf
      (Nat.gcd_pos_of_pos_left _ (by norm_num)) ((Nat.gcd_le_left _ (by norm_num)).trans
        (by norm_num)) dvd_rfl)
  exact by_contra fun hrn =>
    hy1 (uc22s218_l3_eq_one_of_pow_eq_one hX hr (by omega) hrn hU hy hyr)

section Borel


theorem uc22s2114_dvd_of_borel {M L T : Subgroup G} (hL : L ∈ calC M)
    (hTL : IsSylowOf 2 (T ⊓ L) L) {f : ℕ} (hX : LieRankTwoEven (BarInf L) f) (hf : IsPowTwo f)
    {b : G} (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (T : Set G)) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) (hbr : b ^ r = 1) (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1) :
    r ∣ 2 ^ (2 * f) - 1 ∨ (Is3D4 (BarInf L) f ∧ r ∣ 2 ^ (3 * f) - 1) := by
  have hr2 : r ≠ 2 := by omega
  have key := uc22s2114_exists_of_borel hL hTL hbL hbT hbr hb1
  have h2f : 2 ^ f - 1 ∣ 2 ^ (2 * f) - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left f 2)
  rcases hX with hX | hX | hX | hX | hX | hX | hX
  · exact Or.inl ((uc22s2114_dvd_of_borel_l3 hL hTL hX hf hbL hbT hr hr7 hbr hb1).trans h2f)
  · obtain ⟨U, hU, y, hy, hy1, hyr⟩ := key fun _ => uc22p2214_inner_of_prime_Sp4 hX hr
      (uc22s2114_not_dvd_of_dvd hr hr7 hf one_pos (by norm_num) (by rw [mul_one]))
    refine Or.inl (by_contra fun hrn => hy1 ?_)
    exact uc22s2114_eq_one_of_pow_mem hU.2.1 hr hr2 (fun h => hrn (h.trans h2f))
      (uc22p218d_pow_sub_one_mem_sp4 hX hU hy) hyr
  · have hFB := uc22s218_g2_fieldBorel hX
    obtain ⟨U, hU, y, hy, hy1, hyr⟩ := key fun _ => uc22p2214_out_mem_of_card_dvd
      (uc22s2114_card_outer_dvd hFB) hr
      (uc22s2114_not_dvd_of_dvd hr hr7 hf one_pos (by norm_num) (Dvd.intro_left 2 (by ring)))
    obtain ⟨H, F, D⟩ := hFB.exists_of_sylow hU
    exact Or.inl (by_contra fun hrn =>
      hy1 (D.eq_one_of_pow_eq_one hr hr2 (fun h => hrn (h.trans h2f)) hy hyr))
  · have hFB := uc22s218_d4_fieldBorel hX
    obtain ⟨U, hU, y, hy, hy1, hyr⟩ := key fun _ => uc22p2214_out_mem_of_card_dvd
      (uc22s2114_card_outer_dvd hFB) hr (uc22s2114_not_dvd_of_dvd hr hr7 hf (by norm_num : 0 < 3)
        (by norm_num) (Dvd.intro_left 2 (by ring)))
    obtain ⟨H, F, D⟩ := hFB.exists_of_sylow hU
    exact Or.inr ⟨hX, by_contra fun hrn => hy1 (D.eq_one_of_pow_eq_one hr hr2 hrn hy hyr)⟩
  · exfalso
    obtain ⟨-, -, -, -, hodd, hf3⟩ := LieModel.admissible hX
    obtain ⟨k, rfl⟩ := hf
    rcases k with _ | k
    · norm_num at hf3
    · exact Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, k.succ_ne_zero⟩) hodd
  · have hFB := uc22s218_u4_fieldBorel hX
    obtain ⟨U, hU, y, hy, hy1, hyr⟩ := key fun _ => uc22p2214_out_mem_of_card_dvd
      (uc22s2114_card_outer_dvd hFB) hr
      (uc22s2114_not_dvd_of_dvd hr hr7 hf one_pos (by norm_num) (by rw [mul_one]))
    obtain ⟨H, F, D⟩ := hFB.exists_of_sylow hU
    exact Or.inl (by_contra fun hrn => hy1 (D.eq_one_of_pow_eq_one hr hr2 hrn hy hyr))
  · have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) (by norm_num) Nat.prime_two (LieModel.admissible hX).2.1
      (LieModel.statedClassicalModel hX (by decide))).1
    obtain ⟨U, hU, y, hy, hy1, hyr⟩ := key fun _ => uc22p2214_out_mem_of_card_dvd hd hr
      (uc22s2114_not_dvd_of_dvd hr hr7 hf (Nat.gcd_pos_of_pos_left _ (by norm_num))
        ((Nat.gcd_le_left _ (by norm_num)).trans (by norm_num)) dvd_rfl)
    obtain ⟨H, F, Eg, D⟩ := (uc22s218_u5_fieldBorelDiag hX).exists_of_sylow hU
    exact Or.inl (by_contra fun hrn => hy1 (D.eq_one_of_pow_eq_one hr hr2 hrn hy hyr))

end Borel

end CFSG.LocalAnalysis.UniquenessCase.UC22
