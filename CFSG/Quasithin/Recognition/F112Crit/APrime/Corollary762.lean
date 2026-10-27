module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Transport
public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConfigLocal
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma757
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758One
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Theorem761PQ
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Theorem761

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.F7
open CFSG.Quasithin.F112Crit

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem AmalgamS3.localS3 (hA : AmalgamS3 G₀ G₁ G₂ T L) : LocalS3 G₀ G₁ G₂ :=
  LocalS3.of_s3Point_γ₁ hA.hyp hA.s3Point_γ₁

theorem ConfigA.false_of_not_le_normalizer (hA : ConfigA G₀ G₁ G₂ T L E)
    (hD : ¬ G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    False := by
  have hL := hA.localA hA.localS3 (hA.relIndex_pCoreOf_inf hA.relIndex_pCoreOf_T.le) hD
  have hb : 3 ≤ critDist G₀ G₁ G₂ E := by
    obtain ⟨k, hk⟩ := hA.odd
    have h1 := hA.critDist_ne_one hL
    omega
  exact hA.false_of_three_le hL hb fun _ _ _ hγ hγδ hγ' => hA.Vv_inf_pCoreOf_le hL hγ hγδ hγ'

end CFSG.Quasithin.F112Crit.APrime

end
