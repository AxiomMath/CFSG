module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp
public import CFSG.Quasithin.Vol2.Ch10SecBCoord
public import CFSG.Quasithin.Recognition.St84.Sec7S3Group
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem pu_hyp111R {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : Hyp111R L1 L2 S :=
  Hyp111R.of_hyp111 rankOneListedFacts hF.1

private theorem pu_Q2_le_S {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le
    (F112W.isSylowTwoOf_parabolic' (pu_hyp111R hF))

private theorem pu_hn2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hB2 : VBig L2) {n : ℕ}
    (hL2 : IsL2Quot n (oTwoQuot ↥L2)) : 2 ≤ n :=
  two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2

private theorem pu_hE2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {n : ℕ} (hn2 : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    S = (S ⊓ L2) ⊔ Q2 L1 L2 S := by
  have hL : VSzBig L2 ∨ VU3Big L2 ∨ (∃ m : ℕ, 2 ≤ m ∧ IsL2Quot m (oTwoQuot ↥L2)) :=
    Or.inr (Or.inr ⟨n, hn2, hL2⟩)
  exact eq_sup_pCoreOf_of_bender_right hF.1 hSB hL

private theorem pu_S_le_L2_sup_Q2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) : S ≤ L2 ⊔ Q2 L1 L2 S := by
  obtain ⟨n, hL2⟩ := h2
  have hn2 : 2 ≤ n := pu_hn2 hF hB2 hL2
  have hE2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := pu_hE2 hF hSB hn2 hL2
  calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hE2
    _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right

private theorem pu_X_le_L2_sup_Q2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G)) :
    conjClosure P (P2 L1 L2 S) ≤ L2 ⊔ Q2 L1 L2 S := by
  have hR := pu_hyp111R hF
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (F1.bigB_le_normalizer_left hR).2
  have hQ2S : Q2 L1 L2 S ≤ S := pu_Q2_le_S hF
  have hSL : S ≤ L2 ⊔ Q2 L1 L2 S := pu_S_le_L2_sup_Q2 hF hSB hB2 h2
  have hL2NQ2 : L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hL2NL : L2 ≤ Subgroup.normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup Subgroup.le_normalizer hL2NQ2
  refine conjClosure_le fun h hh z hz => ?_
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := L2)
      (K := bigB L1 L2 S) hBL2).mp hh
  have hbzP : b * z * b⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hPB hb) z).mp hz
  have hbzL : b * z * b⁻¹ ∈ L2 ⊔ Q2 L1 L2 S := hSL (hPS hbzP)
  have hconj : l * (b * z * b⁻¹) * l⁻¹ ∈ L2 ⊔ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hL2NL hl) (b * z * b⁻¹)).mp hbzL
  simpa [mul_assoc] using hconj

private theorem pu_L2_inf_Q2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L2 ⊓ Q2 L1 L2 S = pCoreOf 2 L2 := by
  refine le_antisymm ?_ ?_
  · simpa [inf_comm] using
      (F7.pCoreOf_inf_le (K := L2) (H := P2 L1 L2 S) le_sup_left)
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨(pCoreOf_le 2 L2) hx, ?_⟩
    simpa [bigB_comm] using
      (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hx

private theorem pu_pCoreOf_subgroupOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    (Q2 L1 L2 S).subgroupOf L2 = pCore 2 ↥L2 := by
  have hpc : (pCoreOf 2 L2).subgroupOf L2 = pCore 2 ↥L2 := by
    change ((pCore 2 ↥L2).map L2.subtype).subgroupOf L2 = pCore 2 ↥L2
    rw [← Subgroup.comap_subtype (H := (pCore 2 ↥L2).map L2.subtype) (K := L2)]
    exact Subgroup.comap_map_eq_self_of_injective L2.subtype_injective _
  rw [← Subgroup.inf_subgroupOf_right (H := Q2 L1 L2 S) (K := L2)]
  rw [inf_comm, pu_L2_inf_Q2 hF]
  exact hpc

private theorem pu_X_sup_Q2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S) :
    conjClosure P (P2 L1 L2 S) ⊔ Q2 L1 L2 S = L2 ⊔ Q2 L1 L2 S := by
  classical
  obtain ⟨n, hL2e⟩ := h2
  have h2' : VL2 L2 := ⟨n, hL2e⟩
  have hn2 : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2e
  obtain ⟨eL2⟩ := hL2e
  let X : Subgroup G := conjClosure P (P2 L1 L2 S)
  let Lhat : Subgroup G := L2 ⊔ Q2 L1 L2 S
  have hX_le_Lhat : X ≤ Lhat := pu_X_le_L2_sup_Q2 hF hSB hB2 h2' hPS hPB
  have hQ2leS : Q2 L1 L2 S ≤ S := pu_Q2_le_S hF
  have hS_le_Lhat : S ≤ Lhat := pu_S_le_L2_sup_Q2 hF hSB hB2 h2'
  have hLhat_le_P2 : Lhat ≤ P2 L1 L2 S := by
    refine sup_le le_sup_left ?_
    exact hQ2leS.trans (le_sup_right.trans le_sup_right)
  have hXnorm : Lhat ≤ Subgroup.normalizer (X : Set G) :=
    hLhat_le_P2.trans (le_normalizer_conjClosure P (P2 L1 L2 S))
  have hQ2norm : Lhat ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hLhat_le_P2.trans
      ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
  have hXQ2_le_Lhat : X ⊔ Q2 L1 L2 S ≤ Lhat :=
    sup_le hX_le_Lhat le_sup_right
  have hXQ2norm : Lhat ≤
      Subgroup.normalizer ((X ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hXnorm hQ2norm
  have hL2NQ2 : L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hQ2subnorm : ((Q2 L1 L2 S).subgroupOf Lhat).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hQ2norm
  letI := hQ2subnorm
  have hsub : (Q2 L1 L2 S).subgroupOf L2 = pCore 2 ↥L2 := pu_pCoreOf_subgroupOf hF
  letI : ((Q2 L1 L2 S).subgroupOf L2).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL2NQ2
  let e : oTwoQuot ↥L2 ≃* (↥Lhat ⧸ (Q2 L1 L2 S).subgroupOf Lhat) :=
    (QuotientGroup.quotientMulEquivOfEq hsub).symm.trans
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient L2 (Q2 L1 L2 S) hL2NQ2)
  have hsimple : IsSimpleGroup (↥Lhat ⧸ (Q2 L1 L2 S).subgroupOf Lhat) :=
    (MulEquiv.isSimpleGroup_congr e).mp
      (BenderType.isSimple (BenderType.linear n hn2 eL2))
  let Y : Type := ↥Lhat ⧸ (Q2 L1 L2 S).subgroupOf Lhat
  let π : ↥Lhat →* Y := QuotientGroup.mk' ((Q2 L1 L2 S).subgroupOf Lhat)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let H : Subgroup ↥Lhat := (X ⊔ Q2 L1 L2 S).subgroupOf Lhat
  have hHnorm : H.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXQ2_le_Lhat).mpr hXQ2norm
  have hmapnorm : (H.map π).Normal := hHnorm.map π hπsurj
  letI := hmapnorm
  have hS_le_XQ2 : S ≤ X ⊔ Q2 L1 L2 S := by
    have hX : P ≤ X := le_conjClosure P (P2 L1 L2 S)
    intro s hs
    have h1 : s ∈ P ⊔ Q2 L1 L2 S := by
      rw [str86_cartan_supplement hF hSB hB2 h2' hPS hPB hPQ]
      exact hs
    have hP : P ≤ X ⊔ Q2 L1 L2 S := hX.trans le_sup_left
    have hQ : Q2 L1 L2 S ≤ X ⊔ Q2 L1 L2 S := le_sup_right
    exact (sup_le hP hQ) h1
  have hmap_ne : H.map π ≠ ⊥ := by
    obtain ⟨p, hpP, hpQ⟩ := Set.not_subset.mp hPQ
    have hpS : p ∈ S := hPS hpP
    have hpL : p ∈ Lhat := hS_le_Lhat hpS
    have hpXQ : p ∈ X ⊔ Q2 L1 L2 S := hS_le_XQ2 hpS
    let pL : ↥Lhat := ⟨p, hpL⟩
    have hπne : π pL ≠ 1 := by
      intro h
      apply hpQ
      have hmem : pL ∈ (Q2 L1 L2 S).subgroupOf Lhat :=
        (QuotientGroup.eq_one_iff pL).mp h
      exact Subgroup.mem_subgroupOf.mp hmem
    have hpH : pL ∈ H := Subgroup.mem_subgroupOf.mpr hpXQ
    have hmem : π pL ∈ H.map π :=
      Subgroup.mem_map.mpr ⟨pL, hpH, rfl⟩
    intro hbot
    exact hπne (Subgroup.mem_bot.mp (hbot ▸ hmem))
  have htop : H.map π = ⊤ :=
    (hsimple.eq_bot_or_eq_top_of_normal (H.map π)).resolve_left hmap_ne
  have hker_le : π.ker ≤ H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxQ : (x : ↥Lhat) ∈ (Q2 L1 L2 S).subgroupOf Lhat :=
      (QuotientGroup.eq_one_iff x).mp hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : Q2 L1 L2 S ≤ X ⊔ Q2 L1 L2 S)
        (Subgroup.mem_subgroupOf.mp hxQ))
  have hHtop : H = ⊤ := by
    have h1 : Subgroup.comap π (H.map π) = H ⊔ π.ker :=
      Subgroup.comap_map_eq π H
    rw [htop, Subgroup.comap_top, sup_eq_left.mpr hker_le] at h1
    exact h1.symm
  have hLhat_le : Lhat ≤ X ⊔ Q2 L1 L2 S := Subgroup.subgroupOf_eq_top.mp hHtop
  exact le_antisymm hXQ2_le_Lhat hLhat_le

private theorem pu_D2_le_X {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {P D2 : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S)
    (hD2cart : IsCartanOf D2 (borelOf L2 S)) :
    D2 ≤ conjClosure P (P2 L1 L2 S) := by
  classical
  let X : Subgroup G := conjClosure P (P2 L1 L2 S)
  let Lhat : Subgroup G := L2 ⊔ Q2 L1 L2 S
  have hX_le_Lhat : X ≤ Lhat := pu_X_le_L2_sup_Q2 hF hSB hB2 h2 hPS hPB
  have hQ2leS : Q2 L1 L2 S ≤ S := pu_Q2_le_S hF
  have hLhat_le_P2 : Lhat ≤ P2 L1 L2 S := by
    refine sup_le le_sup_left ?_
    exact hQ2leS.trans (le_sup_right.trans le_sup_right)
  have hXsup : X ⊔ Q2 L1 L2 S = Lhat := pu_X_sup_Q2 hF hSB hB2 h2 hPS hPB hPQ
  have hQ2N_X : X ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (hX_le_Lhat.trans hLhat_le_P2).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hXnormLhat : Lhat ≤ Subgroup.normalizer (X : Set G) :=
    hLhat_le_P2.trans (le_normalizer_conjClosure P (P2 L1 L2 S))
  have hsubnorm : (X.subgroupOf Lhat).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX_le_Lhat).mpr hXnormLhat
  letI := hsubnorm
  have hidx : ∃ k : ℕ, (X.subgroupOf Lhat).index = 2 ^ k := by
    have hrel : (X.subgroupOf Lhat).index = (X ⊓ Q2 L1 L2 S).relIndex (Q2 L1 L2 S) := by
      have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := X) (K := Q2 L1 L2 S) hQ2N_X).1
      rwa [hXsup] at h
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (pCoreOf_isPGroup 2 (P2 L1 L2 S))
    have hdiv : (X ⊓ Q2 L1 L2 S).relIndex (Q2 L1 L2 S) ∣ Nat.card (Q2 L1 L2 S) :=
      Subgroup.relIndex_dvd_card _ _
    rw [hm] at hdiv
    obtain ⟨j, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    exact ⟨j, hrel.trans hj.2⟩
  intro d hd
  have hdLhat : d ∈ Lhat :=
    (le_sup_left : L2 ≤ Lhat) ((hD2cart.1.trans (F1.borelOf_le L2 S)) hd)
  have hodd : Odd (orderOf (⟨d, hdLhat⟩ : ↥Lhat)) := by
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat hD2cart.2.1 (Subgroup.orderOf_dvd_natCard D2 hd)
  have hmem := CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_two_pow_index
    (X.subgroupOf Lhat) hidx hodd
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem pu_PM_eq_X_inf_S {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S) (hPQ2S : P ⊔ Q2 L1 L2 S = S) :
    P ⊔ (conjClosure P (P2 L1 L2 S) ⊓ Q2 L1 L2 S) =
      conjClosure P (P2 L1 L2 S) ⊓ S := by
  let X : Subgroup G := conjClosure P (P2 L1 L2 S)
  have hPX : P ≤ X := le_conjClosure P (P2 L1 L2 S)
  have hQ2leS : Q2 L1 L2 S ≤ S := pu_Q2_le_S hF
  have hQ2NP : Q2 L1 L2 S ≤ Subgroup.normalizer (P : Set G) :=
    (hQ2leS.trans le_sup_right).trans hPB
  refine le_antisymm ?_ ?_
  · refine sup_le (le_inf hPX hPS) (le_inf inf_le_left (inf_le_right.trans hQ2leS))
  · intro x hx
    obtain ⟨hxX, hxS⟩ := Subgroup.mem_inf.mp hx
    have hxPQ : x ∈ P ⊔ Q2 L1 L2 S := by rw [hPQ2S]; exact hxS
    obtain ⟨p, hpP, q, hqQ2, hx_eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ2NP).mp hxPQ
    have hpX : p ∈ X := hPX hpP
    have hqX : q ∈ X := by
      have h1 : q = p⁻¹ * x := by rw [hx_eq]; group
      rw [h1]
      exact X.mul_mem (X.inv_mem hpX) hxX
    have hqM : q ∈ X ⊓ Q2 L1 L2 S := Subgroup.mem_inf.mpr ⟨hqX, hqQ2⟩
    rw [hx_eq]
    exact (P ⊔ (X ⊓ Q2 L1 L2 S)).mul_mem
      ((le_sup_left : P ≤ P ⊔ (X ⊓ Q2 L1 L2 S)) hpP)
      ((le_sup_right : (X ⊓ Q2 L1 L2 S) ≤ P ⊔ (X ⊓ Q2 L1 L2 S)) hqM)

private theorem pu_PM_sylow {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S) (hPQ2S : P ⊔ Q2 L1 L2 S = S) :
    IsSylowTwoOf (P ⊔ (conjClosure P (P2 L1 L2 S) ⊓ Q2 L1 L2 S))
      (conjClosure P (P2 L1 L2 S)) := by
  classical
  let X : Subgroup G := conjClosure P (P2 L1 L2 S)
  let Lhat : Subgroup G := L2 ⊔ Q2 L1 L2 S
  let M : Subgroup G := X ⊓ Q2 L1 L2 S
  have hX_le_Lhat : X ≤ Lhat := pu_X_le_L2_sup_Q2 hF hSB hB2 h2 hPS hPB
  have hQ2leS : Q2 L1 L2 S ≤ S := pu_Q2_le_S hF
  have hS_le_Lhat : S ≤ Lhat := pu_S_le_L2_sup_Q2 hF hSB hB2 h2
  have hLhat_le_P2 : Lhat ≤ P2 L1 L2 S := by
    refine sup_le le_sup_left ?_
    exact hQ2leS.trans (le_sup_right.trans le_sup_right)
  have hXsup : X ⊔ Q2 L1 L2 S = Lhat := pu_X_sup_Q2 hF hSB hB2 h2 hPS hPB hPQ
  have hPM_eq : P ⊔ M = X ⊓ S := pu_PM_eq_X_inf_S hF hSB hB2 h2 hPS hPB hPQ hPQ2S
  refine F7.isSylowTwoOf_of_relIndex ?_ ?_ ?_
  · exact sup_le (le_conjClosure P (P2 L1 L2 S)) inf_le_left
  · have hPM_le_S : P ⊔ M ≤ S :=
      sup_le hPS (inf_le_right.trans hQ2leS)
    exact hF.1.h1.pgroup.to_le hPM_le_S
  · have hS_sylow_Lhat : IsSylowTwoOf S Lhat :=
      F7.isSylowTwoOf_mono_right
        (F112W.isSylowTwoOf_parabolic' (pu_hyp111R hF)) hS_le_Lhat hLhat_le_P2
    have hQ2subnorm : ((Q2 L1 L2 S).subgroupOf Lhat).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
        (hLhat_le_P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
    letI := hQ2subnorm
    let Yq : Type := ↥Lhat ⧸ (Q2 L1 L2 S).subgroupOf Lhat
    let πL : ↥Lhat →* Yq := QuotientGroup.mk' ((Q2 L1 L2 S).subgroupOf Lhat)
    have hU_sylow : IsSylowTwoOf
        ((S.subgroupOf Lhat).map πL) (⊤ : Subgroup Yq) :=
      CFSG.Quasithin.Vol2.Ch10.SecB.isSylowTwoOf_map_of_surjective
        hS_sylow_Lhat πL (QuotientGroup.mk'_surjective _)
    have hU_odd : ¬ 2 ∣ ((S.subgroupOf Lhat).map πL).index := by
      have h := hU_sylow.2.2
      change ¬ 2 ∣ ((S.subgroupOf Lhat).map πL).relIndex ⊤ at h
      rwa [Subgroup.relIndex_top_right] at h
    have hmapX : (X.subgroupOf Lhat).map πL = ⊤ := by
      refine top_unique ?_
      intro z _
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective ((Q2 L1 L2 S).subgroupOf Lhat) z
      have hl : (l : G) ∈ X ⊔ Q2 L1 L2 S :=
        (le_of_eq hXsup.symm) l.2
      have hQ2NX : Q2 L1 L2 S ≤ Subgroup.normalizer (X : Set G) :=
        (hQ2leS.trans (le_sup_right.trans le_sup_right)).trans
          (le_normalizer_conjClosure P (P2 L1 L2 S))
      obtain ⟨x, hxX, q, hqQ2, hl_eq⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hQ2NX).mp hl
      refine Subgroup.mem_map.mpr
        ⟨⟨x, hX_le_Lhat hxX⟩, Subgroup.mem_subgroupOf.mpr hxX, ?_⟩
      apply QuotientGroup.eq.mpr
      show ((⟨x, hX_le_Lhat hxX⟩ : ↥Lhat)⁻¹ * l) ∈ (Q2 L1 L2 S).subgroupOf Lhat
      rw [Subgroup.mem_subgroupOf]
      have hcoe : (((⟨x, hX_le_Lhat hxX⟩ : ↥Lhat)⁻¹ * l : ↥Lhat) : G) = x⁻¹ * (l : G) := by
        simp
      rw [hcoe, hl_eq]
      group
      exact hqQ2
    have hcomap : Subgroup.comap πL ((S.subgroupOf Lhat).map πL) = S.subgroupOf Lhat := by
      rw [QuotientGroup.comap_map_mk']
      exact sup_eq_right.mpr (Subgroup.subgroupOf_mono Lhat hQ2leS)
    have hrel := Subgroup.relIndex_comap (f := πL) (K := (X.subgroupOf Lhat))
      (H := (S.subgroupOf Lhat).map πL)
    rw [hcomap, hmapX, Subgroup.relIndex_top_right] at hrel
    have hrelS : (S.subgroupOf Lhat).relIndex (X.subgroupOf Lhat) = S.relIndex X :=
      Subgroup.relIndex_subgroupOf hX_le_Lhat
    have hSX : S.subgroupOf X = (X ⊓ S).subgroupOf X := by
      rw [← Subgroup.inf_subgroupOf_right (H := S) (K := X), inf_comm]
    have hodd : ¬ 2 ∣ ((P ⊔ M).subgroupOf X).index := by
      rw [hPM_eq, ← hSX]
      change ¬ 2 ∣ S.relIndex X
      rw [← hrelS, hrel]
      exact hU_odd
    simpa only [Subgroup.relIndex, M, X] using hodd

private theorem pu_elemAbelian_of_transitive_conj {V D : Subgroup G}
    (hVne : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 →
      ∃ d ∈ D, d⁻¹ * x * d = y) :
    IsElemAbelian 2 V := by
  classical
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hV2 z
  have hk0 : k ≠ 0 := by
    intro h0
    apply hz1
    rw [← orderOf_eq_one_iff, hk, h0, pow_zero]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  let u : ↥V := z ^ (2 ^ m)
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    simp only [u, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← pow_mul]
    have h2m : 2 ^ m * 2 = 2 ^ (m + 1) := by ring
    rw [h2m, ← hk]
    exact congrArg Subtype.val (pow_orderOf_eq_one z)
  have hu1 : u ≠ 1 := by
    intro h
    have hdvd : 2 ^ (m + 1) ∣ 2 ^ m := by
      rw [← hk]
      apply orderOf_dvd_of_pow_eq_one
      have hz : z ^ (2 ^ m) = 1 := by
        simpa [u] using h
      simpa using hz
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  have hord_eq_two : ∀ x : ↥V, x ≠ 1 → orderOf x = 2 := by
    intro x hx1
    obtain ⟨d, hd, hdu⟩ :=
      htrans (x : G) x.2 (by simpa using hx1) (u : G) u.2 (by simpa using hu1)
    have hxu : orderOf x = orderOf u := by
      rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe u]
      have h := orderOf_injective (f := (MulAut.conj d).toMonoidHom)
        (MulAut.conj d).injective (u : G)
      have h' : ((MulAut.conj d).toMonoidHom) (u : G) = d * (u : G) * d⁻¹ := by
        simp [MulAut.conj_apply]
      rw [h'] at h
      have hx_eq : (x : G) = d * (u : G) * d⁻¹ := by rw [← hdu]; group
      rw [hx_eq]
      exact h
    rw [hxu]
    exact orderOf_eq_prime (p := 2) hu2 hu1
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := by
    intro x
    by_cases hx1 : x = 1
    · rw [hx1, one_pow]
    · exact (orderOf_eq_prime_iff.mp (hord_eq_two x hx1)).1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · have ha : a * a = 1 := by simpa [pow_two] using hsq a
    have hb : b * b = 1 := by simpa [pow_two] using hsq b
    have hab : (a * b) * (a * b) = 1 := by simpa [pow_two] using hsq (a * b)
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hab
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by
        have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
        rw [hbi, hai]
  · intro x hx
    simpa using congrArg Subtype.val (hsq (⟨x, hx⟩ : ↥V))

private theorem pu_Qcard {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hB2 : VBig L2) (h2 : VL2 L2) {n : ℕ}
    (hn2 : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    2 < Nat.card (((S ⊓ L2).subgroupOf L2).map
      (QuotientGroup.mk' (pCore 2 ↥L2))) := by
  classical
  let K : Type := oTwoQuot ↥L2
  let Qimg : Subgroup K := ((S ⊓ L2).subgroupOf L2).map
    (QuotientGroup.mk' (pCore 2 ↥L2))
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := hmapB
  let Q : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQcoe : (Q : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨eL2⟩ := hL2
  have hBT : BenderType K n 1 1 := BenderType.linear n hn2 eL2
  obtain ⟨t, hc⟩ := hBT.exists_benderCore Q
  have hcard : Nat.card Qimg = 2 ^ n := by
    rw [← hQcoe, hc.card_eq, pow_one]
  rw [hcard]
  have h2n : 2 < 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact h2n

theorem str86_pu_sylow {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2)
    {P : Subgroup G} (hPS : P ≤ S) (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S)
    (hR : P2 L1 L2 S ≤ Subgroup.normalizer ((P ⊓ Q2 L1 L2 S : Subgroup G) : Set G)) :
    IsSylowTwoOf P (conjClosure P (P2 L1 L2 S)) ∧
      pCoreOf 2 (conjClosure P (P2 L1 L2 S)) = P ⊓ Q2 L1 L2 S ∧
      conjClosure P (P2 L1 L2 S) ⊔ Q2 L1 L2 S = L2 ⊔ Q2 L1 L2 S := by
  classical
  let Q : Subgroup G := Q2 L1 L2 S
  let R : Subgroup G := P ⊓ Q
  let X : Subgroup G := conjClosure P (P2 L1 L2 S)
  let M : Subgroup G := X ⊓ Q
  have hPQ2S : P ⊔ Q = S := str86_cartan_supplement hF hSB hB2 h2 hPS hPB hPQ
  have hQleS : Q ≤ S := pu_Q2_le_S hF
  have hQleB : Q ≤ bigB L1 L2 S :=
    hQleS.trans (le_sup_right : S ≤ bigB L1 L2 S)
  have hS_le_L2_sup_Q : S ≤ L2 ⊔ Q := pu_S_le_L2_sup_Q2 hF hSB hB2 h2
  have hS_le_P2 : S ≤ P2 L1 L2 S :=
    hS_le_L2_sup_Q.trans
      (sup_le le_sup_left (hQleB.trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)))
  have hP_le_P2 : P ≤ P2 L1 L2 S := hPS.trans hS_le_P2
  have hX_le_L2_sup_Q : X ≤ L2 ⊔ Q := pu_X_le_L2_sup_Q2 hF hSB hB2 h2 hPS hPB
  have hX_le_P2 : X ≤ P2 L1 L2 S :=
    hX_le_L2_sup_Q.trans
      (sup_le le_sup_left (hQleB.trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)))
  have hP2NQ : P2 L1 L2 S ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hP2NX : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_conjClosure P (P2 L1 L2 S)
  have hP2NR : P2 L1 L2 S ≤ Subgroup.normalizer (R : Set G) := hR
  have hQN_P : Q ≤ Subgroup.normalizer (P : Set G) := hQleB.trans hPB
  have hP_NQ : P ≤ Subgroup.normalizer (Q : Set G) := hP_le_P2.trans hP2NQ
  have hPX : P ≤ X := le_conjClosure P (P2 L1 L2 S)
  obtain ⟨D2, hD2cart, hD2inf, hD2sup⟩ := F1.exists_cartan hF.1.h2.sylow
  have hD2_le_X : D2 ≤ X :=
    pu_D2_le_X hF hSB hB2 h2 hPS hPB hPQ hD2cart
  have hD2_le_P2 : D2 ≤ P2 L1 L2 S := hD2_le_X.trans hX_le_P2
  have hD2_le_B : D2 ≤ bigB L1 L2 S :=
    hD2cart.1.trans
      ((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left)
  have hD2_NP : D2 ≤ Subgroup.normalizer (P : Set G) := hD2_le_B.trans hPB
  have hD2_NR : D2 ≤ Subgroup.normalizer (R : Set G) := hD2_le_P2.trans hR
  have hPMsyl : IsSylowTwoOf (P ⊔ M) X :=
    pu_PM_sylow hF hSB hB2 h2 hPS hPB hPQ hPQ2S
  have hPM_eq : P ⊔ M = X ⊓ S :=
    pu_PM_eq_X_inf_S hF hSB hB2 h2 hPS hPB hPQ hPQ2S
  obtain ⟨n, hL2n⟩ := h2
  have h2 : VL2 L2 := ⟨n, hL2n⟩
  have hn2 : 2 ≤ n := pu_hn2 hF hB2 hL2n
  have hE2 : S = (S ⊓ L2) ⊔ Q := pu_hE2 hF hSB hn2 hL2n
  have hL2NQ : L2 ≤ Subgroup.normalizer (Q : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans hP2NQ
  let S2 : Subgroup G := S ⊓ L2
  let K : Type := oTwoQuot ↥L2
  let π : ↥L2 →* K := QuotientGroup.mk' (pCore 2 ↥L2)
  let Qimg : Subgroup K := (S2.subgroupOf L2).map π
  have hRM : R ≤ X := inf_le_left.trans hPX
  have hRn : X ≤ Subgroup.normalizer (R : Set G) := hX_le_P2.trans hP2NR
  haveI hRsubnorm : (R.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hRn
  let Y : Type := ↥X ⧸ (R.subgroupOf X)
  let q : ↥X →* Y := QuotientGroup.mk' (R.subgroupOf X)
  let V : Subgroup Y := (P.subgroupOf X).map q
  let D : Subgroup Y := (D2.subgroupOf X).map q
  have hPgrp : IsPGroup 2 P := hF.1.h1.pgroup.to_le hPS
  have hV2 : IsPGroup 2 V := by
    have hsub : IsPGroup 2 (P.subgroupOf X) :=
      hPgrp.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
    exact hsub.map q
  have hVne : V ≠ ⊥ := by
    obtain ⟨p, hpP, hpQ⟩ := Set.not_subset.mp hPQ
    have hpR : p ∉ R := fun h => hpQ (Subgroup.mem_inf.mp h).2
    let pX : ↥X := ⟨p, hPX hpP⟩
    have hpPsub : pX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hpP
    have hmkV : q pX ∈ V := Subgroup.mem_map.mpr ⟨pX, hpPsub, rfl⟩
    have hne : q pX ≠ 1 := by
      intro h
      apply hpR
      change (pX : Y) = 1 at h
      rw [QuotientGroup.eq_one_iff] at h
      exact Subgroup.mem_subgroupOf.mp h
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨q pX, hmkV⟩, fun h => hne (congrArg Subtype.val h)⟩
  have htransV : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 →
      ∃ d ∈ D, d⁻¹ * x * d = y := by
    intro x hxV hx1 y hyV hy1
    obtain ⟨px, hpxPsub, hpxeq⟩ := Subgroup.mem_map.mp hxV
    obtain ⟨py, hpyPsub, hpyeq⟩ := Subgroup.mem_map.mp hyV
    have hpxP : (px : G) ∈ P := Subgroup.mem_subgroupOf.mp hpxPsub
    have hpyP : (py : G) ∈ P := Subgroup.mem_subgroupOf.mp hpyPsub
    have hpxQ : (px : G) ∉ Q := by
      intro hQ
      have hRmem : ((px : ↥X) : G) ∈ R := Subgroup.mem_inf.mpr ⟨hpxP, hQ⟩
      have hker : px ∈ (R.subgroupOf X) := Subgroup.mem_subgroupOf.mpr hRmem
      have hzero : q px = 1 := by
        change (px : Y) = 1
        rw [QuotientGroup.eq_one_iff]
        exact hker
      exact hx1 (hpxeq.symm.trans hzero)
    have hpyQ : (py : G) ∉ Q := by
      intro hQ
      have hRmem : ((py : ↥X) : G) ∈ R := Subgroup.mem_inf.mpr ⟨hpyP, hQ⟩
      have hker : py ∈ (R.subgroupOf X) := Subgroup.mem_subgroupOf.mpr hRmem
      have hzero : q py = 1 := by
        change (py : Y) = 1
        rw [QuotientGroup.eq_one_iff]
        exact hker
      exact hy1 (hpyeq.symm.trans hzero)
    obtain ⟨d, hdD2, hcomm⟩ := str86_cartan_transitive hF hSB hB2 h2 hPS hPB hPQ
      hD2cart hD2inf hD2sup (px : G) hpxP hpxQ (py : G) hpyP hpyQ
    let dX : ↥X := ⟨d, hD2_le_X hdD2⟩
    have hdDsub : dX ∈ D2.subgroupOf X := Subgroup.mem_subgroupOf.mpr hdD2
    have hdD : q dX ∈ D := Subgroup.mem_map.mpr ⟨dX, hdDsub, rfl⟩
    have hcommP : d⁻¹ * (px : G) * d * (py : G)⁻¹ ∈ P := by
      have hd_inv_N : d⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem (hD2_NP hdD2)
      have hdp : d⁻¹ * (px : G) * d ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp hd_inv_N (px : G)).mp hpxP
      simpa [mul_assoc] using P.mul_mem hdp (P.inv_mem hpyP)
    have hcommR : d⁻¹ * (px : G) * d * (py : G)⁻¹ ∈ R :=
      Subgroup.mem_inf.mpr ⟨hcommP, hcomm⟩
    have hker : q (dX⁻¹ * px * dX * py⁻¹) = 1 := by
      change ((dX⁻¹ * px * dX * py⁻¹ : ↥X) : Y) = 1
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hcommR
    have hEq : q (dX⁻¹ * px * dX) = q py := by
      have h1 : q (dX⁻¹ * px * dX) * (q py)⁻¹ = 1 := by
        simpa [map_mul, map_inv] using hker
      exact mul_inv_eq_one.mp h1
    refine ⟨q dX, hdD, ?_⟩
    rw [← hpxeq, ← hpyeq]
    calc (q dX)⁻¹ * q px * q dX = q (dX⁻¹ * px * dX) := by
          simp only [map_mul, map_inv]
      _ = q py := hEq
  have hUab : ∀ a ∈ P, ∀ b ∈ P, ⁅a,b⁆ ∈ R := by
    have hVab : IsElemAbelian 2 V :=
      pu_elemAbelian_of_transitive_conj hVne hV2 htransV
    intro a ha b hb
    let aX : ↥X := ⟨a, hPX ha⟩
    let bX : ↥X := ⟨b, hPX hb⟩
    have haPsub : aX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr ha
    have hbPsub : bX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb
    have haV : q aX ∈ V := Subgroup.mem_map.mpr ⟨aX, haPsub, rfl⟩
    have hbV : q bX ∈ V := Subgroup.mem_map.mpr ⟨bX, hbPsub, rfl⟩
    letI : IsMulCommutative ↥V := hVab.1
    have hcommV : (⟨q aX, haV⟩ : ↥V) * ⟨q bX, hbV⟩ =
        ⟨q bX, hbV⟩ * ⟨q aX, haV⟩ :=
      (IsMulCommutative.is_comm (M := ↥V)).comm _ _
    have hcommY : q aX * q bX = q bX * q aX := congrArg Subtype.val hcommV
    have hqcomm : q ⁅aX, bX⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def, hcommY]
      group
    change ((⁅aX, bX⁆ : ↥X) : Y) = 1 at hqcomm
    rw [QuotientGroup.eq_one_iff] at hqcomm
    have hcoe : ((⁅aX, bX⁆ : ↥X) : G) = ⁅a, b⁆ := rfl
    simpa [hcoe] using Subgroup.mem_subgroupOf.mp hqcomm
  have hZc : ∀ z ∈ M, ∀ x ∈ X, ⁅z,x⁆ ∈ R := by
    have hMn : P2 L1 L2 S ≤ Subgroup.normalizer (M : Set G) := by
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hP2NX hg, hP2NQ hg⟩
    have hbase : ∀ m ∈ M, ∀ p ∈ P, ⁅m,p⁆ ∈ R := by
      intro m hm p hp
      have hmQ : m ∈ Q := (Subgroup.mem_inf.mp hm).2
      have hmp : m * p * m⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hQN_P hmQ) p).mp hp
      have hpm : p * m⁻¹ * p⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hP_NQ hp) m⁻¹).mp (Q.inv_mem hmQ)
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact P.mul_mem hmp (P.inv_mem hp)
      · rw [commutatorElement_def]
        simpa [mul_assoc] using Q.mul_mem hmQ hpm
    intro z hz x hx
    change x ∈ Subgroup.closure
      {y | ∃ g ∈ P2 L1 L2 S, ∃ p ∈ P, g * p * g⁻¹ = y} at hx
    refine Subgroup.closure_induction (p := fun x _ => ⁅z,x⁆ ∈ R) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨g, hg, p, hp, rfl⟩
      have hgm : g⁻¹ * z * g ∈ M := by
        have hginv : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
          (Subgroup.normalizer (M : Set G)).inv_mem (hMn hg)
        simpa using (Subgroup.mem_normalizer_iff.mp hginv z).mp hz
      have hcomm : ⁅g⁻¹ * z * g, p⁆ ∈ R := hbase _ hgm p hp
      have hconj : g * ⁅g⁻¹ * z * g, p⁆ * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hP2NR hg) _).mp hcomm
      have heq : ⁅z, g * p * g⁻¹⁆ = g * ⁅g⁻¹ * z * g, p⁆ * g⁻¹ := by
        have h := conjugate_commutatorElement (g₁ := g⁻¹ * z * g) (g₂ := p) g
        simpa [mul_assoc] using h.symm
      rw [heq]
      exact hconj
    · simp
    · intro a b ha hb haR hbR
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hconj : a * ⁅z,b⁆ * a⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hP2NR (hX_le_P2 ha)) ⁅z,b⁆).mp hbR
      simpa [mul_assoc] using R.mul_mem haR hconj
    · intro a ha haR
      rw [commutatorElement_inv_right]
      have hza : ⁅a,z⁆ ∈ R := by
        simpa [commutatorElement_inv] using R.inv_mem haR
      have haP2 : a ∈ P2 L1 L2 S := hX_le_P2 ha
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hP2NR ((P2 L1 L2 S).inv_mem haP2)) ⁅a,z⁆).mp hza
  have hcardVgt : 2 < Nat.card V := by
    letI : (R.subgroupOf P).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hPX.trans hRn)
    letI : (Q.subgroupOf P).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hP_NQ
    letI : (Q.subgroupOf S).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hS_le_P2.trans hP2NQ)
    let φP : ↥P →* Y := q.comp (Subgroup.inclusion hPX)
    have hφPker : φP.ker = R.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        change ((⟨(x : G), hPX x.2⟩ : ↥X) : Y) = 1 at hx
        rw [QuotientGroup.eq_one_iff] at hx
        exact Subgroup.mem_subgroupOf.mp hx
      · intro hx
        change ((⟨(x : G), hPX x.2⟩ : ↥X) : Y) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hx
    have hφPrange : φP.range = V := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
        exact Subgroup.mem_map.mpr
          ⟨⟨(x : G), hPX x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact MonoidHom.mem_range.mpr
          ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    have eV : ↥P ⧸ R.subgroupOf P ≃* V :=
      (QuotientGroup.quotientMulEquivOfEq hφPker).symm.trans
        ((QuotientGroup.quotientKerEquivRange φP).trans
          (MulEquiv.subgroupCongr hφPrange))
    have hcardV : Nat.card V = Nat.card (↥P ⧸ R.subgroupOf P) :=
      (Nat.card_congr eV.toEquiv).symm
    have hRQ : R.subgroupOf P = Q.subgroupOf P := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨x.2, hx⟩
    letI : (Q.subgroupOf (P ⊔ Q)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le hP_NQ (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G)))
    have hcardA : Nat.card (↥P ⧸ Q.subgroupOf P) =
        Nat.card (↥S ⧸ Q.subgroupOf S) := by
      rw [← hPQ2S]
      exact Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient P Q hP_NQ).toEquiv
    have hS2NQ : S2 ≤ Subgroup.normalizer (Q : Set G) :=
      (inf_le_right : S2 ≤ L2).trans hL2NQ
    letI : (Q.subgroupOf S2).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hS2NQ
    letI : (Q.subgroupOf (S2 ⊔ Q)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le hS2NQ (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G)))
    have hcardB : Nat.card (↥S ⧸ Q.subgroupOf S) =
        Nat.card (↥S2 ⧸ Q.subgroupOf S2) := by
      rw [hE2]
      exact (Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient S2 Q hS2NQ).toEquiv).symm
    let φS2 : ↥S2 →* K := π.comp (Subgroup.inclusion (inf_le_right : S2 ≤ L2))
    have hφS2ker : φS2.ker = Q.subgroupOf S2 := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have hxL : (x : G) ∈ L2 := (Subgroup.mem_inf.mp x.2).2
        change ((⟨(x : G), hxL⟩ : ↥L2) : K) = 1 at hx
        rw [QuotientGroup.eq_one_iff] at hx
        have hmem : (⟨(x : G), hxL⟩ : ↥L2) ∈ pCore 2 ↥L2 := hx
        have hO : (x : G) ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
        have hxQ : (x : G) ∈ Q := by
          have hle : pCoreOf 2 L2 ≤ Q := by
            rw [← pu_L2_inf_Q2 hF]
            exact inf_le_right
          exact hle hO
        exact Subgroup.mem_subgroupOf.mpr hxQ
      · intro hx
        have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
        have hxL : (x : G) ∈ L2 := (Subgroup.mem_inf.mp x.2).2
        have hxO : (x : G) ∈ pCoreOf 2 L2 := by
          rw [← pu_L2_inf_Q2 hF]
          exact ⟨hxL, hxQ⟩
        have hmem : (⟨(x : G), hxL⟩ : ↥L2) ∈ pCore 2 ↥L2 :=
          (F1.mem_pCore_iff_coe _).mpr hxO
        change ((⟨(x : G), hxL⟩ : ↥L2) : K) = 1
        rw [QuotientGroup.eq_one_iff]
        exact hmem
    have hφS2range : φS2.range = Qimg := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
        have hxL : (x : G) ∈ L2 := (Subgroup.mem_inf.mp x.2).2
        let l : ↥L2 := ⟨(x : G), hxL⟩
        have hl : l ∈ S2.subgroupOf L2 := Subgroup.mem_subgroupOf.mpr x.2
        exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      · intro hy
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
        have hlS2 : (l : G) ∈ S2 := Subgroup.mem_subgroupOf.mp hl
        exact MonoidHom.mem_range.mpr ⟨⟨(l : G), hlS2⟩, rfl⟩
    have eC : ↥S2 ⧸ Q.subgroupOf S2 ≃* Qimg :=
      (QuotientGroup.quotientMulEquivOfEq hφS2ker).symm.trans
        ((QuotientGroup.quotientKerEquivRange φS2).trans
          (MulEquiv.subgroupCongr hφS2range))
    have hcardC : Nat.card (↥S2 ⧸ Q.subgroupOf S2) = Nat.card Qimg :=
      Nat.card_congr eC.toEquiv
    rw [hcardV, hRQ, hcardA, hcardB, hcardC]
    exact pu_Qcard hF hB2 ⟨n, hL2n⟩ hn2 hL2n
  have hX_le_KR : X ≤ ⁅X,X⁆ ⊔ R := by
    letI : Fintype ↥V := Fintype.ofFinite _
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hcardV' : 2 < Fintype.card ↥V := by
      rwa [← Nat.card_eq_fintype_card]
    have hfs : ({w, (1 : ↥V)} : Finset ↥V).card < Fintype.card ↥V := by
      have hc : ({w, (1 : ↥V)} : Finset ↥V).card ≤ 2 := by
        by_cases h : w = 1
        · have hsing : ({w, (1 : ↥V)} : Finset ↥V) = {1} := by simp [h]
          rw [hsing]; simp
        · have htwo : ({w, (1 : ↥V)} : Finset ↥V).card = 2 := by
            rw [Finset.card_insert_of_notMem]
            · simp
            · simp [h]
          omega
      omega
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hfs
    have hv1 : v ≠ 1 := by
      intro h
      apply hv
      simp [h]
    have hwv : v ≠ w := by
      intro h
      apply hv
      simp [h]
    obtain ⟨px, hpxPsub, hpxeq⟩ := Subgroup.mem_map.mp w.2
    obtain ⟨py, hpyPsub, hpyeq⟩ := Subgroup.mem_map.mp v.2
    have hpxP : (px : G) ∈ P := Subgroup.mem_subgroupOf.mp hpxPsub
    have hpyP : (py : G) ∈ P := Subgroup.mem_subgroupOf.mp hpyPsub
    have hpxQ : (px : G) ∉ Q := by
      intro hQ
      have hR : (px : G) ∈ R := Subgroup.mem_inf.mpr ⟨hpxP, hQ⟩
      have hzero : q px = 1 := by
        change ((px : ↥X) : Y) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hR
      have hw0 : w = 1 := by
        apply Subtype.ext
        show (w : Y) = ((1 : ↥V) : Y)
        rw [← hpxeq]
        exact hzero
      exact hw1 hw0
    have hpyQ : (py : G) ∉ Q := by
      intro hQ
      have hR : (py : G) ∈ R := Subgroup.mem_inf.mpr ⟨hpyP, hQ⟩
      have hzero : q py = 1 := by
        change ((py : ↥X) : Y) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hR
      have hv0 : v = 1 := by
        apply Subtype.ext
        show (v : Y) = ((1 : ↥V) : Y)
        rw [← hpyeq]
        exact hzero
      exact hv1 hv0
    let Ksub : Subgroup G := ⁅P, D2⁆ ⊔ R
    have hKleP : Ksub ≤ P := by
      have hcomm : ⁅P, D2⁆ ≤ P := by
        rw [Subgroup.commutator_le]
        intro p hp d hd
        have hdp : d * p⁻¹ * d⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hD2_NP hd) p⁻¹).mp (P.inv_mem hp)
        rw [commutatorElement_def]
        simpa [mul_assoc] using P.mul_mem hp hdp
      exact sup_le hcomm inf_le_left
    have hKinv : D2 ≤ Subgroup.normalizer (Ksub : Set G) := by
      have hcomm : D2 ≤ Subgroup.normalizer (((⁅P, D2⁆ : Subgroup G)) : Set G) :=
        Subgroup.normalizer_commutator_ge_right P D2
      exact F1.le_normalizer_sup hcomm hD2_NR
    have hKneR : Ksub ≠ R := by
      intro hKR
      have hcommRle : ⁅P, D2⁆ ≤ R := by
        have : ⁅P, D2⁆ ≤ Ksub := le_sup_left
        rwa [hKR] at this
      obtain ⟨d, hdD2, hcomm⟩ := str86_cartan_transitive hF hSB hB2 h2 hPS hPB hPQ
        hD2cart hD2inf hD2sup (px : G) hpxP hpxQ (py : G) hpyP hpyQ
      have hdp : d⁻¹ * (px : G) * d * (py : G)⁻¹ ∈ P := by
        have hd_inv_N : d⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
          (Subgroup.normalizer (P : Set G)).inv_mem (hD2_NP hdD2)
        have h1 : d⁻¹ * (px : G) * d ∈ P := by
          simpa using (Subgroup.mem_normalizer_iff.mp hd_inv_N (px : G)).mp hpxP
        simpa [mul_assoc] using P.mul_mem h1 (P.inv_mem hpyP)
      have hcommRP : d⁻¹ * (px : G) * d * (py : G)⁻¹ ∈ R :=
        Subgroup.mem_inf.mpr ⟨hdp, hcomm⟩
      have hcommPmem : ⁅(px : G), d⁆ ∈ R :=
        hcommRle (Subgroup.commutator_mem_commutator hpxP hdD2)
      have hconjR : d⁻¹ * ((px : G) * d * (px : G)⁻¹ * d⁻¹) * d ∈ R := by
        simpa [commutatorElement_def, mul_assoc] using
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (R : Set G)).inv_mem (hD2_NR hdD2)) _).mp hcommPmem
      have hconjR' : (d⁻¹ * (px : G) * d) * (px : G)⁻¹ ∈ R := by
        simpa [commutatorElement_def, mul_assoc] using hconjR
      have hpyx : (py : G) * (px : G)⁻¹ ∈ R := by
        have h1 := R.mul_mem (R.inv_mem hcommRP) hconjR'
        simpa [mul_assoc] using h1
      have hpxpy : (px : G) * (py : G)⁻¹ ∈ R := by
        simpa using R.inv_mem hpyx
      have hqeq : q px = q py := by
        have hker : q (px * py⁻¹) = 1 := by
          change (((px * py⁻¹ : ↥X) : Y)) = 1
          rw [QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hpxpy
        have h1 : q px * (q py)⁻¹ = 1 := by
          simpa [map_mul, map_inv] using hker
        exact mul_inv_eq_one.mp h1
      have hwvY : (w : Y) = (v : Y) := hpxeq.symm.trans (hqeq.trans hpyeq)
      exact hwv (Subtype.ext hwvY.symm)
    have hKnotR : ¬ Ksub ≤ R := fun hle =>
      hKneR (le_antisymm hle le_sup_right)
    obtain ⟨k, hkK, hkR⟩ := Set.not_subset.mp hKnotR
    have hkP : k ∈ P := hKleP hkK
    have hkQ : k ∉ Q := fun hQ =>
      hkR (Subgroup.mem_inf.mpr ⟨hkP, hQ⟩)
    have hPleK : P ≤ Ksub := by
      intro p hp
      by_cases hpR : p ∈ R
      · exact (le_sup_right : R ≤ Ksub) hpR
      · have hpQ : p ∉ Q := fun hQ =>
          hpR (Subgroup.mem_inf.mpr ⟨hp, hQ⟩)
        obtain ⟨d, hdD2, hcomm⟩ := str86_cartan_transitive hF hSB hB2 h2 hPS hPB hPQ
          hD2cart hD2inf hD2sup k hkP hkQ p hp hpQ
        have hdkK : d⁻¹ * k * d ∈ Ksub := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (Ksub : Set G)).inv_mem (hKinv hdD2)) k).mp hkK
        have hdp : d⁻¹ * k * d * p⁻¹ ∈ P := by
          have hd_inv_N : d⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
            (Subgroup.normalizer (P : Set G)).inv_mem (hD2_NP hdD2)
          have h1 : d⁻¹ * k * d ∈ P := by
            simpa using (Subgroup.mem_normalizer_iff.mp hd_inv_N k).mp hkP
          simpa [mul_assoc] using P.mul_mem h1 (P.inv_mem hp)
        have hdpR : d⁻¹ * k * d * p⁻¹ ∈ R :=
          Subgroup.mem_inf.mpr ⟨hdp, hcomm⟩
        have hdpK : d⁻¹ * k * d * p⁻¹ ∈ Ksub := (le_sup_right : R ≤ Ksub) hdpR
        have hp_eq : p = (d⁻¹ * k * d * p⁻¹)⁻¹ * (d⁻¹ * k * d) := by group
        rw [hp_eq]
        exact Ksub.mul_mem (Ksub.inv_mem hdpK) hdkK
    have hK_eq_P : Ksub = P := le_antisymm hKleP hPleK
    have hcomm_le : ⁅P, D2⁆ ≤ ⁅X,X⁆ := Subgroup.commutator_mono hPX hD2_le_X
    have hP_le_KR : P ≤ ⁅X,X⁆ ⊔ R := by
      calc P = Ksub := hK_eq_P.symm
        _ = ⁅P, D2⁆ ⊔ R := rfl
        _ ≤ ⁅X,X⁆ ⊔ R := sup_le (hcomm_le.trans le_sup_left)
          (le_sup_right : R ≤ ⁅X,X⁆ ⊔ R)
    have hXXnorm : P2 L1 L2 S ≤ Subgroup.normalizer (((⁅X,X⁆ : Subgroup G)) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmapX : Subgroup.map (↑(MulAut.conj g)) X = X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP2NX hg)
      simpa [Subgroup.map_commutator, hmapX]
    have hK'norm : P2 L1 L2 S ≤ Subgroup.normalizer
        (((⁅X,X⁆ : Subgroup G) ⊔ R : Subgroup G) : Set G) :=
      F1.le_normalizer_sup hXXnorm hP2NR
    refine conjClosure_le ?_
    intro g hg p hp
    exact (Subgroup.mem_normalizer_iff.mp (hK'norm hg) p).mp (hP_le_KR hp)
  have hM2 : IsPGroup 2 M :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le (inf_le_right : M ≤ Q)
  have hZM : M ≤ X := inf_le_left
  have htransfer := CFSG.Quasithin.St84.inf_commutator_sup_le_of_central
    (M := X) (R := R) (Z := M) (U := P) (P := P ⊔ M)
    hRM hRn hZM hM2 hZc hPX hUab hPMsyl le_rfl
  have hM_le_inf : M ≤ M ⊓ (⁅X,X⁆ ⊔ R) :=
    le_inf le_rfl (hZM.trans hX_le_KR)
  have hM_le_R : M ≤ R := hM_le_inf.trans htransfer
  have hR_le_M : R ≤ M := le_inf hRM inf_le_right
  have hM_eq_R : M = R := le_antisymm hM_le_R hR_le_M
  have hO2X_le_Q : pCoreOf 2 X ≤ Q :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hX_le_P2 hP2NX
  have hO2X_le_M : pCoreOf 2 X ≤ M := le_inf (pCoreOf_le 2 X) hO2X_le_Q
  have hO2X_le_R : pCoreOf 2 X ≤ R := by
    rw [hM_eq_R] at hO2X_le_M
    exact hO2X_le_M
  have hR2 : IsPGroup 2 R := hF.1.h1.pgroup.to_le (inf_le_left.trans hPS)
  have hR_le_O2X : R ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 hRM hRn hR2
  have hO2X_eq_R : pCoreOf 2 X = R := le_antisymm hO2X_le_R hR_le_O2X
  have hPsylow : IsSylowTwoOf P X := by
    have hsup : P ⊔ M = P := by
      rw [hM_eq_R]
      exact sup_eq_left.mpr inf_le_left
    rwa [hsup] at hPMsyl
  exact ⟨hPsylow, hO2X_eq_R, pu_X_sup_Q2 hF hSB hB2 h2 hPS hPB hPQ⟩

end CFSG.Quasithin.Stroth

end
