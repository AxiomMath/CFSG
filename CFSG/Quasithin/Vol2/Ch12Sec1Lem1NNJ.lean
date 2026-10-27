module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNI
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNM
public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.EmptyFaithful.SzN15Br1
public import CFSG.Quasithin.EmptyFaithful.T1515dA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Sec1211Nq

variable {G : Type} [Group G] [Finite G]

theorem b51Hyp_of_offender (hA21 : AsA21SQTKSection) {K Q U : Subgroup G} [IsMulCommutative ↥U]
    (hSQ : SQTKGroup ↥K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hQ2 : IsPGroup 2 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (h1a : pCoreOf 2 (K ⊔ Q) ≤ (K ⊔ Q) ⊓ Subgroup.centralizer (U : Set G))
    (hred : IsTwoReducedIn (K ⊔ Q) U) (hnt : ¬ K ≤ Subgroup.centralizer (U : Set G))
    {A : Subgroup (MulAut ↥U)} (hAQ : A ≤ autOn Q U)
    (hA : IsFFStarOffender (autOn (K ⊔ Q) U) A) :
    B51Hyp (ffJ (autOn (K ⊔ Q) U)) (autOn K U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYL : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hQK
  have hYW : K ⊔ Q ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hYW
  have hO2 : pCoreOf 2 (autOn (K ⊔ Q) U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hD := SzN15.autOn_inf_centralizer_eq_bot hQ2 hQK hYW hO2
  have hker : pCoreOf 2 K ≤ Subgroup.centralizer (U : Set G) := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Q) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
        (hYL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact (h1.trans h1a).trans inf_le_right
  have hqa : CFSG.IsQuasisimple ↥(autOn K U) := S153D.isQuasisimple_autOn hKU hq hker hnt
  have hSQa : SQTKGroup ↥(autOn K U) := by
    refine B69.sqtk_of_surj hA21 hSQ (Hs := ⊤)
      ((S153D.autOnHom hKU).comp (⊤ : Subgroup ↥K).subtype) ?_ hqa
    intro y
    obtain ⟨l, rfl⟩ := S153D.autOnHom_surjective hKU y
    exact ⟨⟨l, trivial⟩, rfl⟩
  have hnormA : A ≤ Subgroup.normalizer (autOn K U : Set (MulAut ↥U)) :=
    hAQ.trans (SzN15.autOn_le_normalizer hQK)
  have hLA : ⁅autOn K U, A⁆ = autOn K U := by
    rcases commutator_eq_or_eq_bot1527d hqa hnormA with h | h
    · exact h
    · exfalso
      apply hA.2.1
      rw [eq_bot_iff, ← hD]
      refine le_inf hAQ fun a ha => Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have h1 : autOn K U ≤ Subgroup.centralizer (A : Set (MulAut ↥U)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      exact (Subgroup.mem_centralizer_iff.1 (h1 hk) a ha).symm
  have h2 : ∀ y ∈ K ⊔ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K ⊔ Subgroup.centralizer (U : Set G) :=
    fun y hy => by
      obtain ⟨e, he⟩ := InternalSec.two_of_sup hQ2 hQK y hy
      exact ⟨e, Subgroup.mem_sup_left he⟩
  exact (InternalSec.b51Hyp_ffJ_autOn hYW le_sup_left hYL h2 hO2 hqa hSQa hA hLA).1

end Sec1211Nq

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

theorem false_of_lt (h331 : Stmt3_3_1) (hC27 : ASC27Statement G) (hParab : Lem1211NNParab)
    (hG2 : Lem1211NNG2) (hSL3 : Lem1211NNSL3) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (hMod : Lem1211NNMod) (F : Frame S m) (hm : 3 ≤ m)
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K)
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  set Mv := Subgroup.normalizer (L : Set G) ⊓ H with hMvdef
  set U := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hUdef
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQMv : Q ≤ Mv := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := (inf_le_right.trans hCV).trans hKn
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hSQH : SQTKGroup ↥H := (S.hypC23_of_le h331 F hm le_rfl (Sec1216Lv.lv_le_centralizer L _)
    hR (hR.1.trans inf_le_right) hQR).sqtk
  obtain ⟨t, htR, hta, htc⟩ := S.exists_swap_mem_sylow hR
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := S.le_normalizer_Q hR hQR htR
  have htM : t ∈ Subgroup.normalizer (L : Set G) := (hR.1 htR).1
  obtain ⟨hm3, hiso, htU, hτout⟩ :=
    S.caseH_of_c27 h331 hC27 hParab hG2 hSL3 F hm hchar hK hlt hKn hq htM hta htc htQ
  subst hm3
  obtain ⟨⟨h1a, -, hred⟩, ⟨hUe, A, hAQ, hA⟩, -, hpar, -⟩ :=
    S.c27_caseH h331 hC27 hG2 hSL3 F hm hchar hK hlt hKn hq hQdef hMvdef hUdef
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hXU : K ⊔ Q ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hXU
  have hLvK : Lv ≤ K := hlt.le
  have hLvU : Lv ≤ Subgroup.normalizer (U : Set G) := hLvK.trans hKU
  have hLvMv : Lv ≤ Mv :=
    le_inf ((Sec1216Lv.lv_le_L L _).trans Subgroup.le_normalizer) (Sec1216Lv.lv_le_centralizer L _)
  have hWU : S.W₁ ⊔ S.W₂ ≤ U :=
    (sup_le (S.W₁_le.trans S.le₁) (S.W₂_le.trans S.le₂)).trans
      (S.le_omegaOneCenterOf h331 F hm hchar hKH hKn)
  obtain ⟨π, hπs, hπk, hπ⟩ := S.exists_pi_autOn F hWU hLvU
  have hDP : autOn Lv U ≤ autOn (Mv ⊓ K) U := A4.autOn_mono (le_inf hLvMv hLvK)
  have htH : t ∈ H := S.mem_centralizer_of_swap hta htc
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hKn htH
  have hMvLv : Mv ≤ Subgroup.normalizer (Lv : Set G) :=
    Sec1216Lv.le_normalizer_lv inf_le_left inf_le_right
  have htMv : t ∈ Mv := ⟨htM, htH⟩
  have htLv : t ∈ Subgroup.normalizer (Lv : Set G) := hMvLv htMv
  have hτX := conjAct_mem_normalizer_autOn ⟨t, htU⟩ htK
  have hτP := conjAct_mem_normalizer_autOn ⟨t, htU⟩
    (Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer htMv) htK)
  have hτD := conjAct_mem_normalizer_autOn ⟨t, htU⟩ htLv
  have hPD : autOn (Mv ⊓ K) U ≤ Subgroup.normalizer (autOn Lv U : Set (MulAut ↥U)) :=
    autOn_le_normalizer_autOn (inf_le_left.trans hMvLv)
  have hout := S.swap_not_inner_autOn F hm hLvU π hπ htM hta htc htU htLv hτD
  have hnt : ¬ K ≤ Subgroup.centralizer (U : Set G) := by
    intro hc
    apply hτout
    refine ⟨1, (autOn K U).one_mem, fun y hy => ?_⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    rw [A4.conjAct_eq_one_iff.mpr (hc (Subgroup.mem_subgroupOf.mp hg))]
    group
  have hB := Sec1211Nq.b51Hyp_of_offender hA21 (InternalSec.sqtkGroup_mono hSQH hKH) hq hQ2 hQK h1a
    hred hnt hAQ hA
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hred.2.2.1.2 u u.2)
  obtain ⟨hP1, hP2, -⟩ := hB51 ↥U hU2 _ _ hB
  have hcen := hMod ↥U hU2 _ (autOn K U) (autOn (Mv ⊓ K) U) (autOn Lv U) (conjAct U ⟨t, htU⟩)
    hiso hP1 hP2 hτX hτout hpar hτP hDP hPD π hπs hπk hτD hout
  obtain ⟨a, ha, ha1⟩ := S.exists_ne_one_W₁ F (by omega)
  have haU : a ∈ U := hWU (Subgroup.mem_sup_left ha)
  apply ha1
  refine S.eq_one_of_fixed₁ ha fun l hl => ?_
  have hker : ∀ d : ↥(autOn Lv U), d ∈ π.ker → (d : MulAut ↥U) ⟨a, haU⟩ = ⟨a, haU⟩ := by
    intro d hd
    obtain ⟨l', rfl⟩ := InternalSec.autOnHom_surjective hLvU d
    have h1 : psi F S.lv_le_Xv l' = 1 := by rw [← hπ]; exact hd
    rw [psi_eq_one_iff_gen] at h1
    apply Subtype.ext
    show (l' : G) * a * (l' : G)⁻¹ = a
    rw [(Subgroup.mem_centralizer_iff.mp h1 a (Subgroup.mem_sup_left ha)).symm,
      mul_inv_cancel_right]
  have h2 := congrArg Subtype.val (hcen ⟨a, haU⟩ hker (InternalSec.autOnHom hLvU ⟨l, hl⟩))
  exact h2

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
