module

public import CFSG.Quasithin.Vol2.Ch12Sec7Excl
public import CFSG.Quasithin.Vol2.Ch12Sec2SettingK
public import CFSG.Quasithin.Vol2.Ch12Sec7Ident
public import CFSG.Quasithin.Vol2.Ch12Sec7Lemmas
public import CFSG.Quasithin.Background.BlueprintB2Reduced
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_one_of_mem {T L V : Subgroup G} (h : Hyp1223 G T L V) {v : G} (hv : v ∈ V) :
    v ^ 2 = 1 := by
  obtain ⟨r, hr, rfl⟩ := h.irrPlus.1 hv
  obtain ⟨-, -, hRc⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥(L ⊔ T)) 2
  obtain ⟨-, -, h3⟩ := BlueprintB2.mem_centerTorsion_iff.1 (hRc hr)
  simpa using congrArg Subtype.val h3

omit [Finite G] in
theorem card_of_isPSL_three_four {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem le_card_centralizer (h125 : Lemma12_7_5) {T L V : Subgroup G} (h : Hyp1271 G T L V)
    {t : G} (ht : t ∈ V) (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18)
    (hGt : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    40320 ≤ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  rcases h125 G T L V h t ht h18 with hle | ⟨-, hZ, hK⟩
  · exact absurd hle hGt
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set K := conjClosure (oTwoUpper (L ⊓ C)) C with hKdef
  have hKC : K ≤ C := conjClosure_le fun c hc a ha =>
    C.mul_mem (C.mul_mem hc ((oTwoUpper_le _).trans inf_le_right ha)) (C.inv_mem hc)
  have htZ : t ∈ (Subgroup.center ↥K).map K.subtype := by
    rw [hZ]
    exact le_conjClosure _ _ (Subgroup.mem_zpowers t)
  obtain ⟨k, hk, hkt⟩ := htZ
  have hZ2 : 1 < Nat.card ↥(Subgroup.center ↥K) := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).2 fun hb => ?_
    rw [hb, SetLike.mem_coe, Subgroup.mem_bot] at hk
    rw [hk] at hkt
    exact ne_one_of_relIndex h18 (by decide) (by simpa using hkt.symm)
  have hcard := (Subgroup.center ↥K).card_eq_card_quotient_mul_card_subgroup
  rw [card_of_isPSL_three_four hK] at hcard
  have hle := Subgroup.card_le_of_le hKC
  omega

end S127

open S127 in
theorem theorem12_7_7_of
    (hAsc : Asc94_M24He_L52TypeK) (hId : Ident1277)
    (h125 : Lemma12_7_5) : Theorem12_7_7 := by
  intro G _ _ T L V h t ht h18 hGt
  obtain ⟨z, hz2, hC, hwc⟩ := hId G T L V h t ht h18 hGt
  obtain ⟨hcl, -⟩ := hAsc G z h.hyp.simple h.hyp.qtke.1 hz2 hC hwc
  rcases hcl with hL52 | hM24 | hHe
  · exact absurd hL52 (not_lieModel_psl_five_two h)
  · exfalso
    obtain ⟨φ⟩ := hM24
    have ht2 : orderOf t = 2 :=
      orderOf_eq_prime (sq_eq_one_of_mem h.hyp ht) (ne_one_of_relIndex h18 (by decide))
    have h1 := card_centralizer_le_of_m24 φ ht2
    have h2 := le_card_centralizer h125 h ht h18 hGt
    omega
  · exact hHe

end CFSG.Quasithin.H13
