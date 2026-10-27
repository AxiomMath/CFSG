module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem commutator_inf_centralizer_y_Z_ne_bot :
    ⁅c.L ⊓ t.d.N ⊓ Subgroup.centralizer ({t.y} : Set G), t.Z⁆ ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Subgroup G := c.L ⊓ t.d.N
  let P₂ : Subgroup G := X ⊓ Subgroup.centralizer ({t.y} : Set G)
  intro hbot
  have hbot' : ⁅P₂, t.Z⁆ = ⊥ := by simpa [P₂, X] using hbot
  have hdvd : 3 ∣ Nat.card t.Z := by rw [t.card_Z]
  obtain ⟨zD, hzDord⟩ := exists_prime_orderOf_dvd_card' (G := ↥t.Z) 3 hdvd
  let z : G := (zD : G)
  have hzZ : z ∈ t.Z := zD.2
  have hzord : orderOf z = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hzDord
  have hSL : t.d.S ≤ c.L := t.hdL ▸ t.d.hS.le
  have hSP : t.d.S ≤ t.P := by rw [t.hdS]; exact inf_le_left
  have hzAA : z ∈ t.d.AA := t.Z_le_AA hzZ
  have hzS : z ∈ t.d.S := t.d.AA_le_S hzAA
  have hzP : z ∈ t.P := hSP hzS
  have hzL : z ∈ c.L := hSL hzS
  have hzM : z ∈ c.S.M := c.hyp81.1 hzL
  have hzCy : z ∈ Subgroup.centralizer ({t.y} : Set G) := t.Z_le_centralizer hzZ
  have hZcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  have hZcentP : ∀ p ∈ t.P, z * p = p * z := by
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp (t.le_centralizer_Z hp) z hzZ
  have hP₂Cz : P₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro p hp
    have hp' : p ∈ Subgroup.centralizer (t.Z : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot') hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hp' z hzZ).symm
  let E : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers t.y
  have hy_not_z : t.y ∉ Subgroup.zpowers z := by
    intro hyz
    exact t.y_not_mem_L (Subgroup.zpowers_le.mpr hzL hyz)
  have hzy : ∀ a ∈ Subgroup.zpowers z, a * t.y = t.y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcz : Commute z t.y := Subgroup.mem_centralizer_singleton_iff.mp hzCy
    exact (hcz.zpow_left n).eq
  have hpair := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (X := Subgroup.zpowers z) (v := t.y) hZcard t.orderOf_y hy_not_z hzy
  have hEelt : CFSG.Open.IsElemAbelian 3 E := hpair.1
  have hEcard : Nat.card E = 3 ^ 2 := hpair.2
  have hE_M : E ≤ c.S.M := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr hzM
    · exact Subgroup.zpowers_le.mpr (t.hP.le t.hyP)
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    simpa [t.hdM] using SylowThreeData.N_normal t.d
  have hENormL : E ≤ Subgroup.normalizer (c.L : Set G) := hE_M.trans c.le_normalizer_L
  have hENormN : E ≤ Subgroup.normalizer (t.d.N : Set G) := hE_M.trans hMN
  have hENormX : E ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hENormL hENormN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQ2 : IsPGroup 2 t.d.N := SylowThreeData.N_isPGroup t.d
  have hX2 : IsPGroup 2 X := hQ2.to_le inf_le_right
  obtain ⟨nX, hnX⟩ := hX2.exists_card_eq
  have hXcop : Nat.Coprime 3 (Nat.card X) := by
    rw [hnX]
    exact Nat.Coprime.pow_right nX (by norm_num : Nat.Coprime 3 2)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (p := 3) Nat.prime_three (A := E) (X := X) hEelt (by rw [hEcard]) hENormX hXcop
  have hXleCz : X ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
    by_cases haz : a ∈ Subgroup.zpowers z
    ·
      have haord : orderOf a = 3 := by
        have hdvd' : orderOf a ∣ 3 := by
          rw [← hzord]
          exact orderOf_dvd_of_mem_zpowers haz
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h1 | h3
        · exact absurd (orderOf_eq_one_iff.mp h1) ha1
        · exact h3
      have hzp : Subgroup.zpowers a = Subgroup.zpowers z := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, haord, hzord]
      have hCeq : Subgroup.centralizer ({a} : Set G) =
          Subgroup.centralizer ({z} : Set G) := by
        calc
          Subgroup.centralizer ({a} : Set G)
              = Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
                  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          _ = Subgroup.centralizer (Subgroup.zpowers z : Set G) := by rw [hzp]
          _ = Subgroup.centralizer ({z} : Set G) := by
                  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hCeq]
      exact inf_le_right
    ·
      have haP : a ∈ t.P := by
        have hE_P : E ≤ t.P :=
          sup_le (Subgroup.zpowers_le.mpr hzP) (Subgroup.zpowers_le.mpr t.hyP)
        exact hE_P haE
      have ha3 : a ^ 3 = 1 := hEelt.2 a haE
      have haord : orderOf a = 3 := by
        have hdvd' : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha3
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h1 | h3
        · exact absurd (orderOf_eq_one_iff.mp h1) ha1
        · exact h3
      have haCommZ : ∀ c' ∈ Subgroup.zpowers z, c' * a = a * c' := by
        intro c' hc'
        have hc'E : c' ∈ E := Subgroup.mem_sup_left hc'
        haveI : IsMulCommutative ↥E := hEelt.1
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨c', hc'E⟩ ⟨a, haE⟩)
      have hpairA := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
        (r := 3) (X := Subgroup.zpowers z) (v := a) hZcard haord haz haCommZ
      have hsupEq : Subgroup.zpowers z ⊔ Subgroup.zpowers a = E := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · refine sup_le ?_ ?_
          · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
          · exact Subgroup.zpowers_le.mpr haE
        · rw [hEcard, hpairA.2]
      have haS : a ∉ t.d.S := by
        intro haS
        have hE_le_S : E ≤ t.d.S := by
          rw [← hsupEq]
          exact sup_le (Subgroup.zpowers_le.mpr hzS) (Subgroup.zpowers_le.mpr haS)
        exact t.y_not_mem_L
          (hSL (hE_le_S (Subgroup.mem_sup_right (Subgroup.mem_zpowers t.y))))
      rcases t.mem_AA_or_exists_conj_eq haP ha3 with haAA | ⟨s, hsS, hsconj⟩
      · exact absurd (t.d.AA_le_S haAA) haS
      · rintro x ⟨hxX, hxa⟩
        have hxca : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxa
        have hsM : s ∈ c.S.M := c.hyp81.1 (hSL hsS)
        have hsNX : s ∈ Subgroup.normalizer (X : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_inf
            (show s ∈ Subgroup.normalizer (c.L : Set G) ⊓
                Subgroup.normalizer (t.d.N : Set G) from
              ⟨c.le_normalizer_L hsM, hMN hsM⟩)
        have hsxX : s * x * s⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp hsNX x).mp hxX
        have hconj_comm : (s * x * s⁻¹) * (s * a * s⁻¹) =
            (s * a * s⁻¹) * (s * x * s⁻¹) := by
          calc
            (s * x * s⁻¹) * (s * a * s⁻¹) = s * (x * a) * s⁻¹ := by group
            _ = s * (a * x) * s⁻¹ := by rw [hxca]
            _ = (s * a * s⁻¹) * (s * x * s⁻¹) := by group
        have hcomm_y : (s * x * s⁻¹) * t.y = t.y * (s * x * s⁻¹) := by
          rcases hsconj with h | h
          · rwa [h] at hconj_comm
          · rw [h] at hconj_comm
            have hc : Commute (s * x * s⁻¹) t.y⁻¹ := hconj_comm
            simpa using hc.inv_right.eq
        have hxP₂ : s * x * s⁻¹ ∈ P₂ :=
          ⟨hsxX, Subgroup.mem_centralizer_singleton_iff.mpr hcomm_y⟩
        have hzu : Commute z (s * x * s⁻¹) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (hP₂Cz hxP₂)).symm
        have hzs : Commute z s := hZcentP s (hSP hsS)
        have hx_eq : x = s⁻¹ * (s * x * s⁻¹) * s := by group
        have hzx : z * x = x * z := by
          rw [hx_eq]
          exact ((hzs.inv_right.mul_right hzu).mul_right hzs).eq
        exact Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
  have hQM : t.d.N ≤ c.S.M := by
    rw [SylowThreeData.N, t.hdM]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 c.S.M
  have hQL_le_Q : ⁅t.d.N, c.L⁆ ≤ t.d.N :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := c.L) (K := t.d.N)).mp
      (c.hyp81.1.trans hMN)
  have hQL_le_L : ⁅t.d.N, c.L⁆ ≤ c.L :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := t.d.N) (K := c.L)).mp
      (hQM.trans c.le_normalizer_L)
  have hQZ_le_X : ⁅t.d.N, Subgroup.zpowers z⁆ ≤ X :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hzL)).trans
      (le_inf hQL_le_L hQL_le_Q)
  have hX_le_Czp : X ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hXleCz
  have hX_comm_bot : ⁅X, Subgroup.zpowers z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hX_le_Czp
  have hdouble : ⁅⁅t.d.N, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc
      ⁅⁅t.d.N, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆
          ≤ ⁅X, Subgroup.zpowers z⁆ := Subgroup.commutator_mono hQZ_le_X le_rfl
      _ = ⊥ := hX_comm_bot
  have hZN : t.Z ≤ Subgroup.normalizer (t.d.N : Set G) :=
    ((t.Z_le_AA.trans t.d.AA_le_S).trans (hSP.trans t.hP.le)).trans hMN
  have hRnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (t.d.N : Set G) :=
    Subgroup.zpowers_le.mpr (hZN hzZ)
  obtain ⟨nQ, hnQ⟩ := hQ2.exists_card_eq
  have hcopQ : Nat.Coprime (Nat.card (Subgroup.zpowers z)) (Nat.card t.d.N) := by
    rw [Nat.card_zpowers, hzord, hnQ]
    exact Nat.Coprime.pow_right nQ (by norm_num : Nat.Coprime 3 2)
  have hcommQ_bot : ⁅t.d.N, Subgroup.zpowers z⁆ = ⊥ :=
    CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot
      (Q := G) t.d.N (Subgroup.zpowers z) hRnorm hcopQ hdouble
  have hQ_le_Cz : t.d.N ≤ Subgroup.centralizer ({z} : Set G) := by
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommQ_bot
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  have hzCQ : z ∈ Subgroup.centralizer (t.d.N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQ_le_Cz hq)
  have hQeq : t.d.N = CFSG.Open.pCoreOf 2 c.S.M := by
    rw [SylowThreeData.N, t.hdM]
  have hzQ' : z ∈ CFSG.Open.pCoreOf 2 c.S.M := by
    refine c.standing.charTwo c.S.M c.S.maxLocal.1 ⟨hzM, ?_⟩
    rwa [hQeq] at hzCQ
  have hzQ : z ∈ t.d.N := by
    rwa [← hQeq] at hzQ'
  have hzP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    hQ2.to_le (Subgroup.zpowers_le.mpr hzQ)
  obtain ⟨n, hn⟩ := hzP2.exists_card_eq
  rw [Nat.card_zpowers, hzord] at hn
  rcases n with _ | m
  · norm_num at hn
  · have hdvd2 : 2 ∣ 3 := by
      rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero m)
    norm_num at hdvd2

theorem commutator_inf_centralizer_y_Z_le :
    ⁅c.L ⊓ t.d.N ⊓ Subgroup.centralizer ({t.y} : Set G), t.Z⁆ ≤ t.Ky ⊓ t.d.N := by
  classical
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({t.y} : Set G)
  let P₂ : Subgroup G := c.L ⊓ t.d.N ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hSL : t.d.S ≤ c.L := t.hdL ▸ t.d.hS.le
  have hSP : t.d.S ≤ t.P := by rw [t.hdS]; exact inf_le_left
  have hZK : t.Z ≤ t.Ky :=
    (le_inf (t.Z_le_AA.trans t.d.AA_le_S) t.Z_le_centralizer).trans
      t.inf_centralizer_le_Ky
  have hP₂H : P₂ ≤ H := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hHnorm : H ≤ Subgroup.normalizer (t.Ky : Set G) := by
    rw [CaseTwoTransitive.Ky]
    exact (Subgroup.le_normalizer (H := H)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore H)
  have hP₂norm : P₂ ≤ Subgroup.normalizer (t.Ky : Set G) := hP₂H.trans hHnorm
  have hKy : ⁅P₂, t.Ky⁆ ≤ t.Ky :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := P₂) (K := t.Ky)).mp hP₂norm
  have hP₂Q : P₂ ≤ t.d.N := inf_le_left.trans inf_le_right
  have hQM : t.d.N ≤ c.S.M := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 c.S.M
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hZM : t.Z ≤ c.S.M :=
    (t.Z_le_AA.trans t.d.AA_le_S).trans (hSP.trans t.hP.le)
  have hZN : t.Z ≤ Subgroup.normalizer (t.d.N : Set G) := hZM.trans hMN
  have hQZ : ⁅t.d.N, t.Z⁆ ≤ t.d.N :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := t.Z) (K := t.d.N)).mp hZN
  have hQ : ⁅P₂, t.Z⁆ ≤ t.d.N :=
    (Subgroup.commutator_mono hP₂Q le_rfl).trans hQZ
  exact le_inf ((Subgroup.commutator_mono le_rfl hZK).trans hKy) hQ

theorem commutator_Ky_inf_N_Z_ne_bot : ⁅t.Ky ⊓ t.d.N, t.Z⁆ ≠ ⊥ := by
  classical
  intro hbot
  let P₂ : Subgroup G := c.L ⊓ t.d.N ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hP₂ne : ⁅P₂, t.Z⁆ ≠ ⊥ := by
    simpa [P₂] using commutator_inf_centralizer_y_Z_ne_bot (t := t)
  have hP₂Q : P₂ ≤ t.d.N := inf_le_left.trans inf_le_right
  have hQ2 : IsPGroup 2 t.d.N := SylowThreeData.N_isPGroup t.d
  have hP₂2 : IsPGroup 2 P₂ := hQ2.to_le hP₂Q
  have hZL : t.Z ≤ c.L := (t.Z_le_AA.trans t.d.AA_le_S).trans (t.hdS ▸ inf_le_right)
  have hSP : t.d.S ≤ t.P := by rw [t.hdS]; exact inf_le_left
  have hZM : t.Z ≤ c.S.M :=
    (t.Z_le_AA.trans t.d.AA_le_S).trans (hSP.trans t.hP.le)
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    simpa [t.hdM] using SylowThreeData.N_normal t.d
  have hML : c.S.M ≤ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L
  have hZN : t.Z ≤ Subgroup.normalizer ((c.L ⊓ t.d.N : Subgroup G) : Set G) :=
    (hZM.trans (le_inf hML hMN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZC : t.Z ≤ Subgroup.normalizer
      (Subgroup.centralizer ({t.y} : Set G) : Set G) :=
    t.Z_le_centralizer.trans
      (Subgroup.le_normalizer (H := Subgroup.centralizer ({t.y} : Set G)))
  have hZnormP₂ : t.Z ≤ Subgroup.normalizer (P₂ : Set G) :=
    (le_inf hZN hZC).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨k, hk⟩ := hP₂2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card t.Z) (Nat.card P₂) := by
    rw [t.card_Z, hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  have hdouble : ⁅⁅P₂, t.Z⁆, t.Z⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅⁅P₂, t.Z⁆, t.Z⁆ ≤ ⁅t.Ky ⊓ t.d.N, t.Z⁆ :=
          Subgroup.commutator_mono (by simpa [P₂] using commutator_inf_centralizer_y_Z_le (t := t))
            le_rfl
      _ = ⊥ := hbot
  exact hP₂ne (CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot
    (Q := G) P₂ t.Z hZnormP₂ hcop hdouble)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
