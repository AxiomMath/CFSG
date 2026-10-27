module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.GGL45NtRecExU
import CFSG.LocalAnalysis.StandardType.KGLangS1EToralLift
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridge
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcModel
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcTorus
import CFSG.LocalAnalysis.StandardType.KGLangS1AGlue
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc


private theorem kgLangS1EExcAux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private theorem kgLangS1EExcAux_prod_range_three {K : Type} [Group K] (ξ : MulAut K) (e : K)
    (hξe : ξ e = e) (he : e ^ 3 = 1) :
    ((List.range 3).map fun i => (ξ ^ i) e).prod = 1 := by
  have hpow : ∀ i : ℕ, (ξ ^ i) e = e := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, MulAut.mul_apply, hξe, ih]
  have hlist : (List.range 3).map (fun i => (ξ ^ i) e) = [e, e, e] := by
    rw [show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, hpow 0, hpow 1, hpow 2]
  rw [hlist]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  have h3 : e * (e * e) = e ^ 3 := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
  rw [h3, he]

private noncomputable def kgLangS1EExcAux_I (K₁ : Type) [Field K₁] :
    Set (MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false))) :=
  LargeEvenChevIDImage (LargeEvenCartanE 7) K₁ (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)

theorem kgLangS1E_cont_E7
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E7) (h3 : 3 ∣ lab.n) :
    LargeEvenLabelAll lab (KGLangAxisS1ExcCont 3) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  subst htag
  let L : Type := AlgebraicClosure (ZMod 2)
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure (ZMod 2)))
  letI : IsAlgClosed L := inferInstanceAs (IsAlgClosed (AlgebraicClosure (ZMod 2)))
  letI : CharP L 2 := inferInstanceAs (CharP (AlgebraicClosure (ZMod 2)) 2)
  have hkg : GGL45KGLabel 3 ⟨.E7, l, n⟩ := by simp [GGL45KGLabel]
  have hbrAll : LargeEvenLabelAll ⟨.E7, l, n⟩ (ExcBridgeCont 3 L .E7) :=
    excBridge_U L 3 (by norm_num) (by norm_num) ⟨.E7, l, n⟩ hlab hkg
      (Or.inr (Or.inr (Or.inl rfl)))
  have hrecAll : LargeEvenLabelAll ⟨.E7, l, n⟩ (GGL45NtRec 3) :=
    ggL45NtRecOn_E7 3 (by norm_num) (by norm_num) ⟨.E7, l, n⟩ hlab hkg rfl
  have hfcAll : LargeEvenLabelAll ⟨.E7, l, n⟩ (GGRawFieldConj 3) :=
    ggRawFieldConjOn_chev 3 (by norm_num) (by norm_num) ⟨.E7, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hifAll : LargeEvenLabelAll ⟨.E7, l, n⟩ (GGRawInnField 3) :=
    ggRawInnFieldOn_excInn 3 (by norm_num) (by norm_num) ⟨.E7, l, n⟩ hlab
      (Or.inr (Or.inl rfl))
  have hpcAll : LargeEvenLabelAll ⟨.E7, l, n⟩ (GGRawPCyclic 3) :=
    ggRawPCyclicOn_excCyclic 3 (by norm_num) (by norm_num) ⟨.E7, l, n⟩ hlab
      (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
  have hall := largeEvenLabelAll_and hbrAll
    (largeEvenLabelAll_and hrecAll (largeEvenLabelAll_and hfcAll
      (largeEvenLabelAll_and hifAll hpcAll)))
  have hraw := hall Q hQ
  unfold CFSG.StandardType.LargeEvenRawDatum CFSG.Assembly.LargeEvenRecipeChevalley at hraw
  unfold CFSG.StandardType.LargeEvenRawDatum CFSG.Assembly.LargeEvenRecipeChevalley
  obtain ⟨K₁, hf₁, hfin₁, hK₁, hQ₁, hbr₁, hrec₁, hfc₁, hif₁, hpc₁⟩ := hraw
  refine ⟨K₁, hf₁, hfin₁, hK₁, hQ₁, ?_⟩
  letI : Field K₁ := hf₁
  letI : Finite K₁ := hfin₁
  have hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K₁) :=
    chev_isQuasisimple (τ := .E7) (Or.inr (Or.inl rfl)) K₁
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K₁ .E7
  have hs : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E7 K₁) := hq.2.1
    exact eQ.isSimpleGroup
  have hna : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false),
      a * b ≠ b * a := kgLangS1EExcAux_nonabelian eQ.symm hq.2.2
  intro K _ _ θ hcomm A hA hAIF α₀ hα₀ hα₀I hcard2 ξ hξ hξI J₀ hJ₀ hTor
  have hA0 : ∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁ := by
    classical
    letI : Finite (MulAut K) :=
      Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
    letI : Fintype {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁} :=
      Fintype.ofFinite _
    have hgt : 1 < Fintype.card {α : MulAut K // α ∈ A ∧
        kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁} := by
      rw [← Nat.card_eq_fintype_card]
      have hcard9 : 9 ≤ Nat.card {α : MulAut K // α ∈ A ∧
          kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁} := by
        change 9 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈
          LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
            (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)}
        exact hcard2
      omega
    have h1I : kgInducedAut θ (1 : MulAut K) ∈ kgLangS1EExcAux_I K₁ := by
      rw [map_one]
      exact Subgroup.one_mem _
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hgt
      (⟨(1 : MulAut K), A.one_mem, h1I⟩ :
        {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁})
    exact ⟨b.1, b.2.1, fun h => hb (Subtype.ext h), b.2.2⟩
  obtain ⟨u, hu, f, hf, huf⟩ := hAIF ξ hξ
  have hufI : u * f ∉ kgLangS1EExcAux_I K₁ := by rw [← huf]; exact hξI
  have hufp : (u * f) ^ 3 = 1 := by rw [← huf, ← map_pow, hA.2 ξ hξ, map_one]
  obtain ⟨f', hf'F, u', -, hf'ord, -⟩ := hfc₁ hs hna u hu f hf hufI hufp
  obtain ⟨eb, Qb, he1, hQmat, hIsBridge, -, hfinB⟩ := hbr₁ hs ⟨f', hf'F, hf'ord⟩
  simp only [excTagOf] at hIsBridge
  let F₀ : ModGL .E7 L →* ModGL .E7 L := frobTwistGL .E7 L 2 eb Qb
  let G : Subgroup (ModGL .E7 L) := ratPts .E7 L (endPow F₀ 3)
  obtain ⟨ρ, Θ, hρ, hρG, hΘ, hI, hconjΘ, hFj⟩ := hIsBridge.2
  haveI : Finite G := hfinB
  have hstab : ∀ g ∈ G, F₀ g ∈ G := hIsBridge.stab
  have hfix : ∀ g ∈ G, endPow F₀ 3 g = g := fun g hg => ratPts_fix hg
  have hPconj : ∀ g ∈ G, ∀ E : Subgroup (ModGL .E7 L),
      ExcFramesHalf.IsToralSubgroup .E7 L E →
      ExcFramesHalf.IsToralSubgroup .E7 L
        (E.map (MulAut.conj (g : ModGL .E7 L)⁻¹).toMonoidHom) := by
    intro g hg E hE
    obtain ⟨h, hh, hEt⟩ := hE
    refine ⟨g⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hg).1) hh, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hconj : (g⁻¹ * h)⁻¹ * ((MulAut.conj (g : ModGL .E7 L)⁻¹) x) * (g⁻¹ * h) =
        h⁻¹ * x * h := by
      rw [MulAut.conj_apply, inv_inv]
      group
    exact hconj ▸ hEt x hx
  have hT : ∀ E : Subgroup (ModGL .E7 L), IsElemAbelian 3 E →
      (∀ x ∈ E, x ∈ G ∧ F₀ x = x) → ExcFramesHalf.IsToralSubgroup .E7 L E →
      ∃ N : Subgroup (ModGL .E7 L), N ≤ G ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
        (∀ x ∈ N, F₀ x ∈ N) ∧
        (∀ c ∈ N, ((List.range 3).map fun i => endPow F₀ i c).prod = 1 →
          ∃ s ∈ N, c = s⁻¹ * F₀ s) ∧ E ≤ N := by
    intro E hEab hEG htoral
    exact kgLangExcTorusInput_of_toral (hM2 := CFSG.StandardType.LieCore.ggLieLangPosition_holds)
      (hp := by norm_num) (hp2 := by norm_num) (he := he1) (hQ := hQmat) (hfin := hfinB)
      E hEab hEG htoral
  have hPtoral : ExcFramesHalf.IsToralSubgroup .E7 L (Subgroup.closure {x : ModGL .E7 L |
      x ∈ G ∧ ∃ α ∈ A, kgInducedAut θ α ∈ kgLangS1EExcAux_I K₁ ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}) :=
    kgLangS1E_toral_lift_E7 (n := n) hlab.1 (K₁ := K₁) hK₁ (L := L) (e := eb) he1 (Q := Qb) hQmat
      ρ Θ hρ hρG hΘ hI hconjΘ hFj θ hcomm A hA hAIF hξ hξI hJ₀ hTor
  obtain ⟨M, -, -, hMfix, hM90, eM, heM, heM1, heMp, hξe⟩ :=
    kgLangTorusMPart_at_of_bridge (p := 3) (by norm_num) hs hna hfc₁ hrec₁
      (G := G) (F₀ := F₀) hstab hfix ρ Θ hρ hρG hΘ hI hconjΘ hFj
      (P := fun E => ExcFramesHalf.IsToralSubgroup .E7 L E) hPconj hT
      θ hcomm A hA hAIF hA0 hPtoral ξ hξ hξI
  have hprod : ((List.range 3).map fun i => (ξ ^ i) eM).prod = 1 :=
    kgLangS1EExcAux_prod_range_three ξ eM hξe heMp
  obtain ⟨s, hsM, hse⟩ := hM90 eM heM hprod
  let k : K := s⁻¹
  have hke : k * (ξ k)⁻¹ = eM := by
    show s⁻¹ * (ξ s⁻¹)⁻¹ = eM
    rw [map_inv, inv_inv]
    exact hse.symm
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, -, -, -, -, -, -, -, hXβ⟩ :=
    kgLangTorA_setup (p := 3) (by norm_num) hs hna hif₁ hpc₁ hfc₁ θ hcomm hA hAIF hξ hξI
  obtain ⟨hB₀AI, -⟩ := kgLangS1A_setup_eq θ hcomm hmem hXcard hXβ
  have hB₀A : B₀ ≤ A := fun β hβ => (hB₀AI β hβ).1
  have hB₀I : ∀ β ∈ B₀, kgInducedAut θ β ∈ kgLangS1EExcAux_I K₁ := fun β hβ => (hB₀AI β hβ).2
  have hBk : ∀ β ∈ B₀, β k = k := by
    intro β hβ
    have hβs : β s = s := hMfix β (hB₀A hβ) (hB₀I β hβ) s hsM
    show β s⁻¹ = s⁻¹
    rw [map_inv, hβs]
  have hAe : ∀ α ∈ A, α eM = eM := by
    intro α hα
    obtain ⟨β, hβ, j, rfl⟩ := hdec α hα
    clear hα
    rw [MulAut.mul_apply]
    have hβe : β eM = eM := hMfix β (hB₀A hβ) (hB₀I β hβ) eM heM
    have hξje : (ξ ^ j) eM = eM := by
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, MulAut.mul_apply, hξe, ih]
    rw [hξje, hβe]
  have hα₀B₀ : α₀ ∉ B₀ := fun h => hα₀I (hB₀I α₀ h)
  obtain ⟨e', he'1, he'p, hAe', hke'⟩ :=
    kgLangS1A_concl_of_xi (p := 3) (by norm_num) hA hB₀A hξ hdec hα₀ hα₀B₀ heM1 heMp hAe hBk hke
  refine ⟨k, e', he'1, he'p, hAe', ?_, hke'⟩
  intro α hα hαI
  exact hBk α (hmem α hα hαI)

end CFSG.StandardType
