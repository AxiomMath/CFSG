module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qTorusConj
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qTorusWt

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.GH74.BNPair CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage4.Hex
  CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.F45


theorem finite_d4Model {K : Type} [Field K] [Finite K] (σ : K →+* K) :
    Finite (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) := by
  have : Finite (adjointGroup d4 K) := inferInstance
  have : Finite (twistedGroup σ) := inferInstance
  infer_instance


variable {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q)
  (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)
  (hU : IsSylowTwoOf (d4ModelSystem σ hq hK hσq).U ⊤)
  {D : Type} [Group D] (hfin : Finite D) (A : LieAmalgamExt D)

include hU

theorem cartanFPF_d4Model (hq4 : 4 ≤ q)
    {Φ : (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) →*
      (A.setting hfin 6 (by norm_num)).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin 6 (by norm_num)) Φ (Γ (d4ModelSystem σ hq hK hσq))
      (v (d4ModelSystem σ hq hK hσq) b) (v (d4ModelSystem σ hq hK hσq) (!b))) :
    (A.setting hfin 6 (by norm_num)).CartanFPF := by
  have := finite_d4Model σ
  obtain ⟨s, t, hw⟩ := exists_fpf hq4 hK hσq
  exact cartanFPF_of_rankTwo (d4ModelSystem σ hq hK hσq) hU hfin (by norm_num) A b XD
    (modelTor_mem_cartan hq hK hσq (sigma_three_of_card hK hσq) s t)
    fun y hy hfix => modelTor_fix_U hq hK hσq (sigma_three_of_card hK hσq) s t hw hy hfix

theorem faithfulOnType_d4Model
    {Φ : (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) →*
      (A.setting hfin 6 (by norm_num)).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin 6 (by norm_num)) Φ (Γ (d4ModelSystem σ hq hK hσq))
      (v (d4ModelSystem σ hq hK hσq) b) (v (d4ModelSystem σ hq hK hσq) (!b)))
    (hcent : ∀ k : (A.setting hfin 6 (by norm_num)).ι.G0, (∀ y, k * Φ y = Φ y * k) → k = 1)
    (s : Bool) : (A.setting hfin 6 (by norm_num)).FaithfulOnType s := by
  have := finite_d4Model σ
  have := isSimpleGroup_d4Model σ hq hK hσq
  exact faithfulOnType_of_rankTwo (d4ModelSystem σ hq hK hσq) hU hfin (by norm_num) A b XD hcent s

end CFSG.Quasithin.H13.F431.D4q.F48
