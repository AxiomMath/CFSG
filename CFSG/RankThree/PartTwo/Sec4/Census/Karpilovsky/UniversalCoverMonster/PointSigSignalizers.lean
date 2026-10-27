module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem le_normalizer_iSup {ι : Sort*} {X : Subgroup Γ} {S : ι → Subgroup Γ}
    (h : ∀ i, X ≤ Subgroup.normalizer (S i : Set Γ)) :
    X ≤ Subgroup.normalizer ((⨆ i, S i : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ X, ∀ c ∈ ⨆ i, S i, g * c * g⁻¹ ∈ ⨆ i, S i := by
    intro g hg c hc
    have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun i => ?_
      intro d hd
      rw [Subgroup.mem_comap]
      exact le_iSup S i ((Subgroup.mem_normalizer_iff.mp (h i hg) d).mp hd)
    exact hle hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem le_of_perfect_of_le_sup_solvable {K J C : Subgroup Γ} (hKp : Group.IsPerfect K)
    (hJK : J ≤ K) (hCK : C ≤ K) (hKN : K ≤ Subgroup.normalizer (J : Set Γ))
    (hKCJ : K ≤ C ⊔ J) (hsol : Group.IsSolvable ↥C) : K ≤ J := by
  have hJn : (J.subgroupOf K).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hKN h.2) a).mp ha
  set mk := QuotientGroup.mk' (J.subgroupOf K) with hmk
  have hperf : Group.IsPerfect (K ⧸ J.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := mk) (QuotientGroup.mk'_surjective _)
  set I : Subgroup (K ⧸ J.subgroupOf K) := (C.subgroupOf K).map mk with hI
  have hItop : I = ⊤ := by
    set T : Subgroup K := I.comap mk with hT
    have hT1 : C.subgroupOf K ≤ T := fun c hc => ⟨c, hc, rfl⟩
    have hT2 : J.subgroupOf K ≤ T := fun j hj => by
      have : mk j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
      show mk j ∈ I
      rw [this]; exact one_mem _
    have hTK : K ≤ T.map K.subtype := by
      refine hKCJ.trans (sup_le ?_ ?_)
      · intro c hc
        exact ⟨⟨c, hCK hc⟩, hT1 (by simpa [Subgroup.mem_subgroupOf] using hc), rfl⟩
      · intro j hj
        exact ⟨⟨j, hJK hj⟩, hT2 (by simpa [Subgroup.mem_subgroupOf] using hj), rfl⟩
    have hTtop : T = ⊤ := by
      rw [eq_top_iff]
      intro k _
      obtain ⟨t, ht, htk⟩ := hTK k.2
      have : t = k := Subtype.ext htk
      exact this ▸ ht
    rw [eq_top_iff]
    intro u _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective u
    have : k ∈ T := hTtop ▸ Subgroup.mem_top k
    exact this
  have hsolQ : Group.IsSolvable (K ⧸ J.subgroupOf K) := by
    have : Group.IsSolvable ↥C := hsol
    refine Group.isSolvable_of_surjective (f := mk.comp (Subgroup.inclusion hCK)) ?_
    intro u
    have hu : u ∈ I := hItop ▸ Subgroup.mem_top u
    obtain ⟨c, hc, rfl⟩ := hu
    exact ⟨⟨c.1, hc⟩, rfl⟩
  have hsub : Subsingleton (K ⧸ J.subgroupOf K) := by
    by_contra hne
    have hn : Nontrivial (K ⧸ J.subgroupOf K) := not_subsingleton_iff_nontrivial.mp hne
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial (K ⧸ J.subgroupOf K)
    rw [hperf.commutator_eq_top] at this
    exact lt_irrefl _ this
  intro k hk
  have h1 : mk ⟨k, hk⟩ = mk 1 := Subsingleton.elim _ _
  have : (⟨k, hk⟩ : K) ∈ J.subgroupOf K := by
    have := (QuotientGroup.eq (a := (⟨k, hk⟩ : K)) (b := 1)).mp h1
    simpa using this
  simpa [Subgroup.mem_subgroupOf] using this

theorem le_sSup_signalizers [Finite Γ] {A K : Subgroup Γ} {S : Set Γ} (hA : Late.IsE27 A) (hSA : S ⊆ A)
    (hAK : A ≤ Subgroup.normalizer (K : Set Γ)) (hKp : Group.IsPerfect K)
    (hgen : K ≤ ⨆ (x : Γ) (_ : x ∈ S), pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)))
    (hsol : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (A : Set Γ))) :
    K ≤ sSup {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
      V = ⁅V, A⁆} := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.1.2 g g.2)⟩
  have hAC : ∀ x ∈ A, A ≤ Subgroup.centralizer ({x} : Set Γ) := fun x hx a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha x hx)
  set P : Γ → Subgroup Γ := fun x => pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ))
    with hPdef
  set Cc : Subgroup Γ := K ⊓ Subgroup.centralizer (A : Set Γ) with hCcdef
  have hAP : ∀ x ∈ A, A ≤ Subgroup.normalizer (P x : Set Γ) := fun x hx a ha =>
    normalizer_le_normalizer_pPrimeCoreOf 3 _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAK ha, Subgroup.le_normalizer (hAC x hx ha)⟩)
  have hPK : ∀ x, P x ≤ K := fun x => (pPrimeCoreOf_le 3 _).trans inf_le_left
  have hP3 : ∀ x, ¬ 3 ∣ Nat.card (P x) := fun x h => by
    have := coprime_card_pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp this h
  set V : Γ → Subgroup Γ := fun x => ⁅P x, A⁆ with hVdef
  have hVP : ∀ x ∈ A, V x ≤ P x := fun x hx =>
    CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized (P x) A (hAP x hx)
  have hCcP : ∀ x ∈ A, Cc ≤ Subgroup.normalizer (P x : Set Γ) := by
    intro x hx
    have hle : Cc ≤ K ⊓ Subgroup.centralizer ({x} : Set Γ) :=
      le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr hx)))
    exact hle.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hCcV : ∀ x ∈ A, Cc ≤ Subgroup.normalizer (V x : Set Γ) := fun x hx =>
    CFSG.LargeEvenClassification.Helpers.normalizes_commutator_pair Cc (P x) A (hCcP x hx)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  set J : Subgroup Γ := ⨆ (x : Γ) (_ : x ∈ S), V x with hJdef
  have hVJ : ∀ x ∈ S, V x ≤ J := fun x hx =>
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hJK : J ≤ K := iSup_le fun x => iSup_le fun hx => ((hVP x (hSA hx)).trans (hPK x))
  have hCcJ : Cc ≤ Subgroup.normalizer (J : Set Γ) :=
    le_normalizer_iSup fun x => le_normalizer_iSup fun hx => hCcV x (hSA hx)
  have hPCJ : ∀ x ∈ S, P x ≤ Cc ⊔ J := by
    intro x hx q hq
    obtain ⟨f, hf, t, ht, hft⟩ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_fixed_decomposition
        Nat.prime_three A (P x) hAp (hP3 x) (hAP x (hSA hx)) ⟨q, hq⟩
    have hq' : q = (f : Γ) * (t : Γ) := by rw [← Subgroup.coe_mul, hft]
    rw [hq']
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hPK x f.2, hf⟩))
      (Subgroup.mem_sup_right (hVJ x hx ht))
  have hKCJ : K ≤ Cc ⊔ J := hgen.trans (iSup_le fun x => iSup_le fun hx => hPCJ x hx)
  have hCJN : Cc ⊔ J ≤ Subgroup.normalizer (J : Set Γ) :=
    sup_le hCcJ Subgroup.le_normalizer
  have hKN : K ≤ Subgroup.normalizer (J : Set Γ) := hKCJ.trans hCJN
  have hKJ : K ≤ J := le_of_perfect_of_le_sup_solvable hKp hJK inf_le_left hKN hKCJ hsol
  refine hKJ.trans (iSup_le fun x => iSup_le fun hx => le_sSup ?_)
  refine ⟨(hVP x (hSA hx)).trans (hPK x), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact le_top
  · intro q hq
    have hq3 : ¬ 3 ∣ Nat.card (V x) := fun h =>
      hP3 x (h.trans (Subgroup.card_dvd_of_le (hVP x (hSA hx))))
    show (q : ℕ) ≠ 3
    intro h
    exact hq3 (h ▸ hq)
  · exact Subgroup.normalizer_commutator_ge_right (P x) A
  · exact (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three A (P x) hAp (hP3 x) (hAP x (hSA hx))).symm

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig
