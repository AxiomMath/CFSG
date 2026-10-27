module

public import CFSG.Sporadic.Recognition.JankoWongLemma14Classify
public import CFSG.Sporadic.Recognition.JankoWongPSLEight
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem card_NG_eq_Kbar_mul :
    Nat.card c.NG = Nat.card c.Kbar * 81 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥c.NG)
  rw [c.card_oddCore_NG] at h
  exact h

theorem card_Kbar_eq (L : Subgroup c.Kbar) (hL : L.index = 2) :
    Nat.card c.Kbar = 2 * Nat.card L := by
  have := Subgroup.card_mul_index L
  rw [hL] at this
  omega

theorem factorization_two_Kbar :
    (Nat.card c.Kbar).factorization 2 = 4 := by
  have h := c.card_NG_eq_Kbar_mul
  have h4 := c.factorization_two_NG
  have hne : Nat.card c.Kbar ≠ 0 := Nat.card_pos.ne'
  rw [h, Nat.factorization_mul hne (by norm_num), Finsupp.add_apply] at h4
  have h81 : (81 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h81] at h4
  omega

theorem not_isPGroup_Kbar
    : ¬ IsPGroup 2 c.Kbar := by
  intro hK
  obtain ⟨g, hgNG, hgO, n, hgn⟩ := c.exists_three_element_NG
  have h1 : (c.Kπ ⟨g, hgNG⟩) ^ (3 ^ n) = 1 := by
    rw [← map_pow]
    have : (⟨g, hgNG⟩ : ↥c.NG) ^ (3 ^ n) = 1 := Subtype.ext (by simpa using hgn)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hK (c.Kπ ⟨g, hgNG⟩)
  have hd : 2 ^ k ∣ 3 ^ n := hk ▸ orderOf_dvd_of_pow_eq_one h1
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 3 ^ n := (dvd_pow_self 2 hk0).trans hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have hmem : (⟨g, hgNG⟩ : ↥c.NG) ∈ CFSG.oddCore ↥c.NG := by
    rw [← c.ker_Kπ]; exact hk
  exact hgO ((c.mem_oddCore_iff_mem_OG _).mp hmem)

theorem card_dihedral_kernel
    {L : Subgroup c.Kbar} (hLn : L.Normal) (hLidx : L.index = 2)
    (hLno : ∀ M : Subgroup L, M.index ≠ 2) (hLD : HasDihedralSylowTwo L)
    (hzL : c.zbar ∈ L) :
    Nat.card L = 168 ∨ (Nat.card L = 360 ∧ IsSimpleGroup L ∧
      Nonempty (L ≃* alternatingGroup (Fin 6))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard := c.card_Kbar_eq L hLidx
  have hLne : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hf2 : (Nat.card L).factorization 2 = 3 := by
    have h := c.factorization_two_Kbar
    rw [hKcard, Nat.factorization_mul (by norm_num) hLne, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at h
    omega
  have h8 : 2 ^ 3 ∣ Nat.card L ∧ ¬ 2 ^ 4 ∣ Nat.card L := by
    constructor
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hLne).mpr (by omega)
    · intro h
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hLne).mp h
      omega
  have hLO : CFSG.oddCore L = ⊥ := by
    have hbot : CFSG.oddCore c.Kbar = ⊥ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot
    set X : Subgroup c.Kbar := (CFSG.oddCore L).map L.subtype with hX
    have hXn : X.Normal := ⟨fun y hy g =>
      oddCore_conj_mem L g (fun y hy => hLn.conj_mem y hy g) (fun y hy => by
        simpa using hLn.conj_mem y hy g⁻¹) y hy⟩
    have hXodd : Odd (Nat.card X) := by
      rw [hX, Subgroup.card_map_of_injective L.subtype_injective]
      exact CFSG.ABGDGroups.odd_card_oddCore _
    have hXle : X ≤ CFSG.oddCore c.Kbar := le_oddCore_of_normal_odd X hXn hXodd
    rw [hbot] at hXle
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp (le_bot_iff.mp hXle)
  have hLNC : ¬ CFSG.HasNormalPComplement 2 L := by
    rintro ⟨W, hWn, hcop, hq⟩
    have hWodd : Odd (Nat.card W) := Nat.coprime_two_left.mp hcop
    have hWbot : W = ⊥ := le_bot_iff.mp (hLO ▸ le_oddCore_of_normal_odd W hWn hWodd)
    have hW1 : Nat.card W = 1 := by rw [hWbot]; simp
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hq
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    rw [hj, hW1, mul_one] at h1
    apply c.not_isPGroup_Kbar
    exact IsPGroup.of_card (n := j + 1) (by rw [hKcard, h1]; ring)
  have hu2 : (⟨c.zbar, hzL⟩ : L) ^ 2 = 1 := Subtype.ext c.zbar_sq
  have hu1 : (⟨c.zbar, hzL⟩ : L) ≠ 1 := fun e => c.zbar_ne_one (congrArg Subtype.val e)
  have hcz : centralizer ({c.zbar} : Set c.Kbar) = (c.SBar : Subgroup c.Kbar) := by
    apply le_antisymm
    · intro g hg
      exact c.centralizer_zbar_le g (Subgroup.mem_centralizer_singleton_iff.mp hg)
    · intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (c.SBar_comm_zbar y hy)
  have hSBcard : Nat.card (c.SBar : Subgroup c.Kbar) = 16 := by
    obtain ⟨e⟩ := c.nonempty_SD_equiv_SBar
    have : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
    rw [← Nat.card_congr e.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
    norm_num
  have hrel : L.relIndex (c.SBar : Subgroup c.Kbar) = 2 := by
    have hd : L.relIndex (c.SBar : Subgroup c.Kbar) ∣ L.index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    rw [hLidx] at hd
    have hne1 : L.relIndex (c.SBar : Subgroup c.Kbar) ≠ 1 := fun h1 =>
      PGLStep.sylow_not_le_of_index_two c.SBar hLidx (Subgroup.relIndex_eq_one.mp h1)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h hne1
    · exact h
  have hcu : Nat.card (centralizer ({(⟨c.zbar, hzL⟩ : L)} : Set L)) = 8 := by
    rw [card_centralizer_subtype]
    show Nat.card (L ⊓ centralizer ({c.zbar} : Set c.Kbar) : Subgroup c.Kbar) = 8
    rw [hcz]
    have := Subgroup.relIndex_mul_card L (c.SBar : Subgroup c.Kbar)
    rw [hrel, hSBcard] at this
    omega
  rcases card_eq_of_psl_step_eight hLD h8 hLNC hLO hLno hu2 hu1 hcu with h | ⟨h, hs⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, hs, ?_⟩
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
      exists_mulEquiv_psl_nine_of_psl_step_eight hLD h8 hLNC hLO hLno hu2 hu1 hcu h
    obtain ⟨e'⟩ := nonempty_mulEquiv_alternatingGroup_six_of_card_nine hF
    exact ⟨e.trans e'⟩

theorem lemma14 :
    ¬ CFSG.HasNormalPComplement 2 ↥c.Cg ∧ Nat.card c.Cg = 972 ∧ Nat.card c.NG = 58320 ∧
      ∃ L : Subgroup c.Kbar, L.Normal ∧ L.index = 2 ∧ Nat.card L = 360 ∧ IsSimpleGroup L ∧
        Nonempty (L ≃* alternatingGroup (Fin 6)) ∧
        c.zbar ∈ L ∧ (∀ u : c.Kbar, u ^ 2 = 1 → u ≠ 1 → u ∈ L) ∧ HasDihedralSylowTwo L := by
  obtain ⟨L, hLn, hLidx, hLno, hLD, hzL, hcls⟩ := c.exists_dihedral_kernel
  have hLcard := c.card_dihedral_kernel hLn hLidx hLno hLD hzL
  have hKcard := c.card_Kbar_eq L hLidx
  have hNG := c.card_NG_eq_Kbar_mul
  have hle := c.card_NG_le_mul_card_Cg
  have hII : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg ∧ Nat.card c.Cg = 972 := by
    rcases c.card_Cg_cases with ⟨-, hC⟩ | h
    · exfalso
      rw [hNG, hKcard, hC] at hle
      rcases hLcard with h | ⟨h, -, -⟩ <;> omega
    · exact h
  have hL360 : Nat.card L = 360 ∧ IsSimpleGroup L ∧ Nonempty (L ≃* alternatingGroup (Fin 6)) := by
    rcases hLcard with h168 | h
    · exfalso
      have h81 := c.card_OG_eq_81
      have h7 : 7 ∣ Nat.card c.NG := by rw [hNG, hKcard, h168]; norm_num
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.NG) 7 h7
      have hr7 : (r : G) ^ 7 = 1 := by
        have := pow_orderOf_eq_one r
        rw [hr] at this
        simpa using congrArg Subtype.val this
      have hrN : ∀ q ∈ c.OG, (r : G) * q * (r : G)⁻¹ ∈ c.OG := fun q hq =>
        c.conj_mem_OG_of_mem_NG r.2 hq
      have hmod := card_modEq_card_inf_centralizer_of_pow_prime (Q := c.OG) (p := 7) hr7 hrN
      have hdvd : Nat.card ↥(c.OG ⊓ centralizer ({(r : G)} : Set G)) ∣ 81 := by
        rw [← h81]; exact Subgroup.card_dvd_of_le inf_le_left
      have hdvd' : Nat.card ↥(c.OG ⊓ centralizer ({(r : G)} : Set G)) ∣ 3 ^ 4 := by
        rw [show (3 : ℕ) ^ 4 = 81 by norm_num]; exact hdvd
      obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
      have hj4 : j = 4 := by
        rw [h81, hj3] at hmod
        unfold Nat.ModEq at hmod
        interval_cases j <;> simp_all
      have hfull : c.OG ⊓ centralizer ({(r : G)} : Set G) = c.OG := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hj3, hj4, h81]; norm_num
      have hrO : (r : G) ∈ c.OG := c.centralizer_OG_le (r : G) (fun y hy => by
        have : y ∈ c.OG ⊓ centralizer ({(r : G)} : Set G) := by rw [hfull]; exact hy
        exact Subgroup.mem_centralizer_singleton_iff.mp this.2)
      have h1 := orderOf_dvd_natCard (⟨(r : G), hrO⟩ : c.OG)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hr, h81] at h1
      omega
    · exact h
  refine ⟨hII.1, hII.2, by rw [hNG, hKcard, hL360.1], L, hLn, hLidx, hL360.1, hL360.2.1,
    hL360.2.2, hzL, ?_, hLD⟩
  intro u hu2 hu1
  obtain ⟨g, hg⟩ := isConj_iff.mp (hcls u hu2 hu1)
  have hu : u = g⁻¹ * c.zbar * g := by
    rw [← hg]; group
  rw [hu]
  have := hLn.conj_mem c.zbar hzL g⁻¹
  simpa using this

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
