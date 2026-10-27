
module

public import CFSG.Quasithin.Background.A312SporRuBase
import all CFSG.Quasithin.Background.A312SporRuBase

public import CFSG.Quasithin.Background.A312SporAlt5
public import CFSG.Quasithin.Background.A312SporE8
public import CFSG.Quasithin.Background.A312SporRuInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import Certificates.Certificate7130
public import CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.SmallF2 CFSG.Quasithin.A312S.Ru
open CFSG.Sporadic.Ru.Native (ruData)
open Matrix

section Ru

theorem ru_a312_cert :
    (∃ ψ : ↥(ruCtx.Y 2) →* SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective ψ) ∧
      ∀ (N : Subgroup ↥(ruCtx.Y 2)) [N.Normal], IsPGroup 2 (↥(ruCtx.Y 2) ⧸ N) →
        Nat.card (↥(ruCtx.Y 2) ⧸ N) ≤ 1 :=
  Certificates.certificate7130

theorem ru_case2
    {B : Subgroup (J ruData)}
    (hB : B ∈ lFamily ruCtx.S) (hY : B ⊔ ruCtx.S = ruCtx.Y 2) : A312Case B ⊤ := by
  have hcard : Nat.card ↥(ruCtx.Y 2) = 168 * 2 ^ 11 := by
    rw [ru_member_card 2 (by norm_num)]
    rfl
  obtain ⟨⟨ψ, hψ⟩, hquot⟩ := ru_a312_cert
  obtain ⟨hpsl, hO2B⟩ := lFamily_psl32_of_hom hB hY ψ hψ hcard hquot
  iterate 18 right
  exact ⟨Or.inr hpsl, hO2B, ⟨Subgroup.topEquiv.trans (seedEquiv ru_facts.toBaseFacts).symm⟩⟩

theorem a312For_Ru
    (hq : CFSG.IsQuasisimple (J ruData)) : A312For (J ruData) := by
  refine a312For_of_members hq ru_S_sylow (L := #[1, 15, 21, 3, 3]) ru_complete
    fun j hj B hB hY => ?_
  have hj5 : j < 5 := hj
  have hc := ru_member_card j hj5
  have h23 : ∀ {a b : ℕ}, Nat.card (ruCtx.Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    not_isSolvable_sup hB (hY ▸ isSolvable_of_card_pq Nat.prime_two Nat.prime_three
      (by norm_num) h)
  interval_cases j
  · exact (h23 (a := 14) (b := 0) (by rw [hc]; rfl)).elim
  · exact ru_case1 hB hY
  · exact ru_case2 hB hY
  · exact (h23 (a := 14) (b := 1) (by rw [hc]; rfl)).elim
  · exact (h23 (a := 14) (b := 1) (by rw [hc]; rfl)).elim

theorem famRu :
    FamRu :=
  @famRu_of (J ruData) inferInstance inferInstance (seedEquiv ru_facts.toBaseFacts) a312For_Ru

end Ru

end CFSG.Quasithin.A312S
