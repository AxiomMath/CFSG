module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ClsMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Aut
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelRad
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Ctr

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.Sec53F.G2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem g2_stdTwo {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    StdTwo (C K) (U K) (Pmin K ⟨1, by decide⟩) (Pmin K ⟨0, by decide⟩) (xc 1) (xv 1) where
  z_mem := xc_mem_U 1
  t_mem := xv_mem_U 1
  z_two := orderOf_eq_prime (by rw [sq]; exact xc_mul_self 1)
    (fun h => one_ne_zero (xc_eq_one_iff.mp h))
  t_two := orderOf_eq_prime (by rw [sq]; exact xv_mul_self 1)
    (fun h => one_ne_zero (xv_eq_one_iff.mp h))
  cls := fun _ hx => cls_involution hx
  noconj := fun φ => Cent.no_aut_xc_xv 1 φ
  center := by
    intro w hw hc hw1
    obtain ⟨s, rfl⟩ := (mem_Xc_iff).mp (center_U hw hc)
    have hs : s ≠ 0 := fun h => hw1 (by rw [h, xc_zero])
    obtain ⟨τ, hτ⟩ := exists_torus_conj (K := K) (one_ne_zero) hs
    have h3 := three_le_card_of_pow hf hK
    refine ⟨⟨torusElt Tag.G2 K i0 τ, torusElt_mem_adjointGroup i0 τ⟩, ?_, ?_⟩
    · rw [Pmin_one_inf_Pmin_zero h3]
      exact torusGroup_le_borelGroup (torusElt_mem_torusGroup _ _)
    · apply Subtype.ext
      exact hτ
  aut_z := fun φ h1 h2 => by
    obtain ⟨b, hb, σ, -, hz, -⟩ := exists_of_autStab_Pr_Pa hf hK ⟨h1, h2⟩
    exact ⟨b, hb, hz⟩
  aut_t := fun φ h1 h2 => by
    obtain ⟨b, hb, σ, -, -, ht⟩ := exists_of_autStab_Pr_Pa hf hK ⟨h1, h2⟩
    exact ⟨b, hb, ht⟩
  cent_z := Or.inl (Cent.cz one_ne_zero)
  cent_t := Or.inr Cent.ct

end CFSG.Quasithin.H13.F431.G2
