module

public import CFSG.Quasithin.H13.A6S13821zz6
public import CFSG.Quasithin.H13.A6S13821zl
public import CFSG.Quasithin.H13.A6S13821zz5
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5Setup

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

namespace A6S20

theorem false_of_quot_b42_psu3 {Q R : Type} [Group Q] [Group R] [Finite Q] [Finite R]
    (hperf : commutator Q = ⊤) (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hoddQ : Odd (Nat.card (Subgroup.center Q))) {n : ℕ} (hn : 2 ≤ n)
    (hcardQ : Nat.card (Q ⧸ Subgroup.center Q) = ordTwistedA 2 (2 ^ n))
    (hqR : CFSG.IsQuasisimple R) {φ : Q →* R} (hφ : φ.range = ⊤) (hR : Bridge.B42Types R) :
    False := by
  have hnt : Nontrivial R := by
    obtain ⟨-, -, a, b, hab⟩ := hqR
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨a' * b', b' * a', fun h => hab ?_⟩⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  obtain ⟨hcard, hdvd⟩ := card_quot_center_of_surjective hperf hs (MonoidHom.range_eq_top.mp hφ)
  exact false_of_b42Types_psu3 hR hn (hcard.trans hcardQ) (Odd.of_dvd_nat hoddQ hdvd)

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_u3_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (ha : S.Case13820aHyp H K)
    (hU3 : IsPSU 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, I, hV₁I, hIU, hirrT, hTI, hFF⟩ :=
    S.exists_ff_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hC ha
  obtain ⟨hS, hH, hK, hKn, -, hn, -⟩ := hC
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  have := factElem hF hIU
  obtain ⟨hB4, hexp, hFF2⟩ := A6S20.ff_data_gen hA21 (S.sqtkGroup_of_mem_Hz hH) hF hK₀
    hV₁I hIU hirrT hTI hFF
  obtain ⟨φ, hφr⟩ := A6S20.exists_surj_autSec (S.sqtkGroup_of_mem_Hz hH) hF hK₀ hV₁I hIU hirrT hTI
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K with hQ
  have h1 : IsPSU 3 2 n (Q ⧸ Subgroup.center Q) :=
    IsPSU.of_mulEquiv (QuotientGroup.congr _ _ e₁.symm (Subgroup.map_center_eq e₁.symm)) hU3
  have hperf : commutator Q = ⊤ := by
    have hK' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    have : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.isPerfect_def.mp this
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := by
    obtain ⟨⟨-, -, -, hne⟩, K', _, _, hK', ⟨e⟩⟩ := h1
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K' 2 n hK' 3 le_rfl
      hne
    exact e.isSimpleGroup
  have hcardQ : Nat.card (Q ⧸ Subgroup.center Q) = ordTwistedA 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h1).2.1 rfl
  have hoddQ : Odd (Nat.card (Subgroup.center Q)) := E1.ThinA5.odd_card_center_quot_pCore
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF2
  have hTypes := Bridge.asB42Types_of_asB42With (Bridge.asB42With_kGroup.mpr h42) _ hexp
    _ _ hB4 ⟨A, hA⟩
  exact A6S20.false_of_quot_b42_psu3 hperf hs hoddQ hn hcardQ hB4.2.2.1 hφr hTypes

end Setting4

end CFSG.Quasithin.H13.A6
