module

public import CFSG.RankThree.PartOne.K159.InnLayerFive
public import CFSG.RankThree.PartOne.S13K.KFLiftRows

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

theorem pPower_mem_commutator {p : ℕ} (hp : p.Prime) (hsup : commutator X ⊔ Subgroup.center X = ⊤)
    (hZ : ∀ z ∈ Subgroup.center X, ¬ p ∣ orderOf z) {x : X} {k : ℕ} (hk : orderOf x = p ^ k) :
    x ∈ commutator X := by
  have hx : x ∈ commutator X ⊔ Subgroup.center X := hsup ▸ Subgroup.mem_top x
  obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have : a * z = 1 := orderOf_eq_one_iff.1 (by simpa using hk)
    rw [this]
    exact Subgroup.one_mem _
  · have hcomm : Commute a z := Subgroup.mem_center_iff.1 hz a
    set m := orderOf z with hm
    have hxm : (a * z) ^ m = a ^ m := by
      rw [hcomm.mul_pow, hm, pow_orderOf_eq_one, mul_one]
    have hcop : Nat.Coprime m (orderOf (a * z)) := by
      rw [hk]
      exact (((Nat.Prime.coprime_iff_not_dvd hp).2 (hZ z hz)).pow_left k).symm
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hu, hxm]
    exact pow_mem (pow_mem ha m) u

theorem map_mem_inner_of_perfect {Z : Type*} [Group Z] (hZ : Group.IsPerfect Z) (ρ : Z →* MulAut X)
    (hOut : Group.IsSolvable (Outer X)) (z : Z) : ρ z ∈ inner X := by
  classical
  let ψ : Z →* Outer X := (QuotientGroup.mk' (inner X)).comp ρ
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsolv : Group.IsSolvable ↥ψ.range := inferInstance
  have htriv : ∀ z : Z, ψ z = 1 := by
    intro z
    by_contra hz
    have : Nontrivial ↥ψ.range :=
      ⟨⟨⟨ψ z, z, rfl⟩, 1, fun h => hz (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) hsolv
  exact (QuotientGroup.eq_one_iff _).1 (htriv z)

end Abstract

section Five

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commI_eq_commutator (I : Subgroup G) : U5K.commI I = ⁅I, I⁆ := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥I) ⊤ I.subtype
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  rw [← h, ← commutator_def ↥I]
  rfl

theorem isPerfect_lieGenerated_five (hEin : U5K.U5EInndiag) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    Group.IsPerfect ↥(lieGenerated p E) := by
  set I := lieGenerated p E with hI
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hZI := not_dvd_inf_centralizer_five hEin h15 hF hout
  have hsup : commutator ↥I ⊔ Subgroup.center ↥I = ⊤ :=
    U5K.commutator_sup_center_eq_top (U5K.isPerfect_quotient e hf)
  have hZ : ∀ z ∈ Subgroup.center ↥I, ¬ p ∣ orderOf z := by
    intro z hz hdvd
    apply hZI
    have hzmem : (z : G) ∈ I ⊓ Subgroup.centralizer (I : Set G) := by
      refine ⟨z.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    have hdvd' : p ∣ orderOf (z : G) := by rw [Subgroup.orderOf_coe]; exact hdvd
    exact hdvd'.trans (Subgroup.orderOf_dvd_natCard _ hzmem)
  have hK : ∀ K : Subgroup G, (∃ t ∈ reflectionSet p E, IsKt p E t K) → K ≤ ⁅I, I⁆ := by
    rintro K ⟨t, ht, hKt⟩
    have hKI : K ≤ I := le_sSup ⟨t, ht, hKt⟩
    by_cases hex : ∃ f', kExceptional p (kZero p E t) f'
    · obtain ⟨f', hf'⟩ := hex
      obtain ⟨-, hmod, -⟩ := hKt.1 f' hf'
      have hKperf : Group.IsPerfect ↥K := (S13K.isQuasisimple_of_model_psl_two hmod).1
      calc K = ⁅K, K⁆ := ((Subgroup.isPerfect_iff).1 hKperf).symm
        _ ≤ ⁅I, I⁆ := Subgroup.commutator_mono hKI hKI
    · have hKeq : K = kZero p E t := hKt.2 hex
      rw [hKeq]
      unfold kZero pElementSubgroup
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hxX, k, hk⟩
      have hxK : x ∈ kZero p E t := by
        unfold kZero pElementSubgroup
        exact Subgroup.subset_closure ⟨hxX, k, hk⟩
      have hxI : x ∈ I := hKI (hKeq ▸ hxK)
      have h1 := pPower_mem_commutator (X := ↥I) hp hsup hZ (x := ⟨x, hxI⟩) (k := k)
        (by rw [← hk]; exact (Subgroup.orderOf_coe (⟨x, hxI⟩ : ↥I)).symm)
      rw [← commI_eq_commutator]
      exact U5K.mem_commI.2 ⟨⟨x, hxI⟩, h1, rfl⟩
  have hIle : I ≤ ⁅I, I⁆ := sSup_le fun K hK' => hK K hK'
  have hcomm : commutator ↥I = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have h1 : (g : G) ∈ U5K.commI I := by rw [commI_eq_commutator]; exact hIle g.2
    obtain ⟨j, hj, hjg⟩ := U5K.mem_commI.1 h1
    have : j = g := Subtype.ext hjg
    rwa [this] at hj
  exact ⟨hcomm⟩

theorem catalog_projSU_five {f : ℕ} (hf : 1 ≤ f) : CFSG.Blueprint.Catalog (projSU 5 2 f) := by
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hmod : StatedClassicalModel (projSU 5 2 f) .PSU 5 2 f :=
    ⟨⟨Nat.prime_two, hf, by norm_num, by simp⟩, GaloisField 2 (2 * f), inferInstance, inferInstance,
      hcard, ⟨CFSG.RankThree.PartTwo.Sec4.projSUEquivStatedProj 5 2 f⟩⟩
  exact Or.inr (Or.inr (Or.inl ⟨.PSU, 5, 2, f, hmod⟩))

theorem kfPerfNormalizerFive_of_schreier (hS : SchreierFor CFSG.Blueprint.Catalog) (hMod : KFU5Mod)
    (hAt : KFU5At) (h5 : U5FiveInndiag) : KFPerfNormalizerFive := by
  intro G _ _ p A c L E h15 hF hout Z hZperf hZN
  have hEin := U5K.u5EInndiag_of hMod hAt h5
  have hIperf := isPerfect_lieGenerated_five hEin h15 hF hout
  set I := lieGenerated p E with hI
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hPfin := U5K.u5_finite f hf
  have hPsimple := U5K.u5_isSimpleGroup f hf
  have hPperf := U5K.u5_isPerfect f hf
  have hPnonab : ∃ a b : projSU 5 2 f, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative (projSU 5 2 f) := ⟨⟨fun a b => hcon a b⟩⟩
    have h3 : Group.IsNilpotent (projSU 5 2 f) := inferInstance
    exact (Group.IsPerfect.not_isNilpotent (G := projSU 5 2 f)) h3
  have hOut : Group.IsSolvable (Outer (projSU 5 2 f)) := hS _ hPnonab (catalog_projSU_five hf)
  let ρ : ↥Z →* MulAut (projSU 5 2 f) := (U5K.U5Act I e).comp (Subgroup.inclusion hZN)
  intro z hz
  obtain ⟨q, hq⟩ := map_mem_inner_of_perfect hZperf ρ hOut ⟨z, hz⟩
  obtain ⟨w, rfl⟩ := e.surjective q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
  have hjN : (j : G) ∈ Subgroup.normalizer (I : Set G) := I.le_normalizer j.2
  have hzN : z ∈ Subgroup.normalizer (I : Set G) := hZN hz
  have hjz : U5K.U5Act I e ⟨z, hzN⟩ = U5K.U5Act I e ⟨(j : G), hjN⟩ := by
    rw [U5K.U5Act_of_mem I e j]
    exact hq.symm
  have hker : (j : G)⁻¹ * z ∈ U5K.kerG I e := by
    refine U5K.mem_kerG.2 ⟨(Subgroup.normalizer (I : Set G)).mul_mem
      ((Subgroup.normalizer (I : Set G)).inv_mem hjN) hzN, ?_⟩
    have h1 : (⟨(j : G)⁻¹ * z, (Subgroup.normalizer (I : Set G)).mul_mem
        ((Subgroup.normalizer (I : Set G)).inv_mem hjN) hzN⟩ : ↥(Subgroup.normalizer (I : Set G))) =
        (⟨(j : G), hjN⟩ : ↥(Subgroup.normalizer (I : Set G)))⁻¹ * ⟨z, hzN⟩ := rfl
    rw [h1, map_mul, map_inv, ← hjz]
    exact inv_mul_cancel _
  have hcI : U5K.commI I = I := by
    unfold U5K.commI
    rw [hIperf.commutator_eq_top, Subgroup.map_top, Subgroup.range_subtype]
  have hc : (j : G)⁻¹ * z ∈ Subgroup.centralizer (I : Set G) := by
    have := U5K.kerG_le_centralizer_commI e hker
    rwa [hcI] at this
  have hmem := Subgroup.mul_mem_sup j.2 hc
  have hz' : (j : G) * ((j : G)⁻¹ * z) = z := by group
  rwa [hz'] at hmem

theorem kfInnLayerFive_of_schreier (hS : SchreierFor CFSG.Blueprint.Catalog) (hMod : KFU5Mod)
    (hAt : KFU5At) (h5 : U5FiveInndiag) (hComp : KFCompLayerFive) (hP5 : KFInnLayerFiveP5) :
    KFInnLayerFive :=
  kfInnLayerFive_of_facts hMod hAt h5 (kfPerfNormalizerFive_of_schreier hS hMod hAt h5) hComp hP5

end Five

end CFSG.RankThree.PartOne.K159
