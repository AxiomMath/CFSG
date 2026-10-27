module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernelBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G]

theorem mem_rightConjugate_iff' (A : Subgroup G) (g x : G) :
    x ∈ rightConjugate A g ↔ g * x * g⁻¹ ∈ A := by
  change x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]

theorem proper_pair_suzuki_data
    [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k)) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (hk : Nat.card k = 2 ^ (2 * m + 1)),
      1 ≤ m ∧ Nat.card Q = 2 ^ (2 * m + 1) ∧ K ⊓ B = X ∧
      ∃ ψ : K ≃* suzukiGroup m k,
        (H.subgroupOf K).map ψ.toMonoidHom = suzukiB m k ∧
        (B.subgroupOf K).map ψ.toMonoidHom = suzukiT m k ∧
        (ψ ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t⟩)⁻¹ •
            (⟨suzukiInfty k, suzukiInfty_mem_suzukiOmega m k⟩ : suzukiOmegaSub hk) =
          ⟨suzukiLine m k 0 0, suzukiLine_mem_suzukiOmega m k 0 0⟩ ∧
        Nat.card (baseOrbit H K) = Nat.card Q ^ 2 + 1 := by
  intro B X K Q
  obtain ⟨-, hO, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨m, k₀, _, _, hk₀, -, ⟨e'⟩⟩ := hSz
  obtain ⟨hQ, hKB, k, _, _, hk, ψ, hψ₀, -, hψB, f, hf, -, -, hfβ, hdeg⟩ :=
    proper_pair_suzuki_branch h hcomm hsmallerR1 hbeta ht hproper hO
      (e'.trans (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hk₀))
  obtain ⟨-, hQ4, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hm : 1 ≤ m := by
    by_contra hm0
    have hQ4' : 4 ≤ Nat.card Q := hQ4
    rw [show m = 0 by omega] at hQ
    omega
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  let ωβ : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} :=
    ⟨beta, t, htK, (flip_coset_eq H ht).symm⟩
  exact ⟨m, k, inferInstance, inferInstance, hk, hm, hQ, hKB, ψ, hψ₀, hψB,
    (hf ⟨t, htK⟩ ωβ (flip_coset_eq H ht)).symm.trans (hfβ ωβ rfl), hdeg⟩

section Model

variable {m : ℕ} {k : Type} [Field k] [Finite k]

theorem le_suzukiU_of_isPGroup (hk : Nat.card k = 2 ^ (2 * m + 1))
    {P : Subgroup (suzukiGroup m k)} (hP : IsPGroup 2 P) (hPB : P ≤ suzukiB m k) :
    P ≤ suzukiU m k := by
  have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
  obtain ⟨S, hS⟩ := hSPA.exists_sylow
  have hPN : P ≤ Subgroup.normalizer (suzukiU m k : Set (suzukiGroup m k)) :=
    hPB.trans ((suzuki_ovoid_stabilizer hk).2.symm.le.trans hSPA.stabilizer_le_normalizer)
  have hsup : IsPGroup 2 (P ⊔ suzukiU m k : Subgroup (suzukiGroup m k)) :=
    IsPGroup.to_sup_of_normal_right' hP (hS ▸ S.isPGroup') hPN
  have heq := S.is_maximal' (hS ▸ hsup) (hS ▸ le_sup_right)
  rw [hS] at heq
  exact le_sup_left.trans heq.le

theorem mem_suzukiZ0_of_mem_suzukiB
    (hk : Nat.card k = 2 ^ (2 * m + 1))
    {g : suzukiGroup m k} (hg : g ∈ suzukiB m k) (hg2 : orderOf g = 2) : g ∈ suzukiZ0 m k := by
  have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
  have hgU := (hSPA.involution_mem_center g ((suzuki_ovoid_stabilizer hk).2 ▸ hg) hg2).1
  exact (SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hk).2 ⟨hgU, hg2 ▸ pow_orderOf_eq_one g⟩

end Model

variable {m : ℕ} {k : Type} [Field k] [Finite k]

theorem mem_map_subgroupOf_iff {K : Subgroup G} {P : Type*} [Group P] (ψ : K ≃* P)
    (A : Subgroup G) (y : K) : ψ y ∈ (A.subgroupOf K).map ψ.toMonoidHom ↔ (y : G) ∈ A := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

theorem map_point_sylow_eq_suzukiU
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {H K T : Subgroup G}
    (ψ : K ≃* suzukiGroup m k) (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = suzukiB m k)
    (hTHK : T ≤ H ⊓ K) (hT2 : IsPGroup 2 T) (hTcard : Nat.card T = Nat.card k ^ 2) :
    (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k := by
  have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
  have hle : (T.subgroupOf K).map ψ.toMonoidHom ≤ suzukiU m k := by
    refine le_suzukiU_of_isPGroup hk ((hT2.comap_subtype (K := K)).map _) ?_
    rw [← hψ₀]
    exact Subgroup.map_mono fun x hx => (hTHK hx).1
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hSPA.card_U, Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun x hx => (hTHK hx).2).toEquiv, hTcard, hk]

theorem map_point_root_eq_suzukiZ0
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {H K Q : Subgroup G}
    (ψ : K ≃* suzukiGroup m k) (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = suzukiB m k)
    (hinv : {x : G | x ∈ H ⊓ K ∧ orderOf x = 2} = (Q : Set G) \ {1}) :
    (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k := by
  ext g
  obtain ⟨y, rfl⟩ := ψ.surjective g
  rw [mem_map_subgroupOf_iff]
  constructor
  · intro hy
    by_cases hy1 : (y : G) = 1
    · rw [show y = 1 from Subtype.ext hy1, map_one]
      exact Subgroup.one_mem _
    have hyinv : (y : G) ∈ {x : G | x ∈ H ⊓ K ∧ orderOf x = 2} := hinv ▸ ⟨hy, hy1⟩
    have hyB : ψ y ∈ suzukiB m k := by
      rw [← hψ₀, mem_map_subgroupOf_iff]
      exact hyinv.1.1
    refine mem_suzukiZ0_of_mem_suzukiB hk hyB ?_
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hyinv.2
  · intro hy
    by_contra hyQ
    have hy1 : ψ y ≠ 1 := fun h1 => hyQ (by
      rw [ψ.map_eq_one_iff.mp h1]
      exact Q.one_mem)
    have hyU := suzukiZ0_le_suzukiU hy
    have hyB : ψ y ∈ suzukiB m k := suzukiU_le_suzukiB m k hyU
    rw [← hψ₀, mem_map_subgroupOf_iff] at hyB
    have hsq := ((SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hk).1 hy).2
    have hy2 : orderOf (ψ y) = 2 :=
      orderOf_eq_prime hsq hy1
    have hmem : (y : G) ∈ {x : G | x ∈ H ⊓ K ∧ orderOf x = 2} :=
      ⟨⟨hyB, y.2⟩, by rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ]; exact hy2⟩
    rw [hinv] at hmem
    exact hyQ hmem.1

theorem point_root_le_center_point_sylow
    (hk : Nat.card k = 2 ^ (2 * m + 1))
    {K T Q : Subgroup G} (ψ : K ≃* suzukiGroup m k) (hTK : T ≤ K) (hQK : Q ≤ K)
    (hTU : (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k)
    (hQZ : (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k) :
    Q ≤ T ∧ T ≤ Subgroup.centralizer (Q : Set G) ∧ ∀ x ∈ T, x ^ 2 = 1 → x ∈ Q := by
  have hT : ∀ y : K, (y : G) ∈ T ↔ ψ y ∈ suzukiU m k := fun y => by
    rw [← hTU, mem_map_subgroupOf_iff]
  have hQ : ∀ y : K, (y : G) ∈ Q ↔ ψ y ∈ suzukiZ0 m k := fun y => by
    rw [← hQZ, mem_map_subgroupOf_iff]
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun x hx hx2 => ?_⟩
  · exact (hT ⟨y, hQK hy⟩).2 (suzukiZ0_le_suzukiU ((hQ ⟨y, hQK hy⟩).1 hy))
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hc := (suzuki_unipotent_structure hk).2.2.2.2.2.1 _ ((hQ ⟨y, hQK hy⟩).1 hy) _
      ((hT ⟨x, hTK hx⟩).1 hx)
    rw [← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (ψ.injective hc)
  · have hsq : ψ ⟨x, hTK hx⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨x, hTK hx⟩ : K) ^ 2 = 1 from Subtype.ext hx2, map_one]
    exact (hQ ⟨x, hTK hx⟩).2 ((SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hk).2
      ⟨(hT ⟨x, hTK hx⟩).1 hx, hsq⟩)

theorem map_flip_point_sylow_eq
    (hm : 1 ≤ m) (hk : Nat.card k = 2 ^ (2 * m + 1))
    {K T : Subgroup G} (ψ : K ≃* suzukiGroup m k)
    (hTU : (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k) {t : G} (htK : t ∈ K)
    (hψt : (ψ ⟨t, htK⟩)⁻¹ •
        (⟨suzukiInfty k, suzukiInfty_mem_suzukiOmega m k⟩ : suzukiOmegaSub hk) =
      ⟨suzukiLine m k 0 0, suzukiLine_mem_suzukiOmega m k 0 0⟩) :
    ((rightConjugate T t).subgroupOf K).map ψ.toMonoidHom =
      (suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom := by
  obtain ⟨P, hPU, -, hPW, ⟨φ, hφ, hφi, hφ0, -, -⟩, -, -⟩ :=
    Suzuki_model_opposite_root_interface hm hk
  have hV : (suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom =
      (suzukiU m k).map (MulAut.conj (ψ ⟨t, htK⟩)⁻¹).toMonoidHom := by
    rw [← hPU, hPW, ← hφ0, ← hψt, hφ, hφi, coe_smul_sylow']
  rw [hV]
  ext g
  obtain ⟨y, rfl⟩ := ψ.surjective g
  rw [mem_map_subgroupOf_iff, mem_rightConjugate_iff', Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul, ← hTU,
    mem_map_subgroupOf_iff]
  rfl

theorem exists_point_root_coordinates
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {K Q : Subgroup G}
    (ψ : K ≃* suzukiGroup m k) (hQK : Q ≤ K)
    (hQZ : (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k) :
    ∃ e : Multiplicative k ≃* Q, ∀ b : k,
      ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G) := by
  have hmem : ∀ b : k, (ψ.symm (suzukiSElt m k 0 b) : G) ∈ Q := fun b => by
    have h0 : suzukiSElt m k 0 b ∈ suzukiZ0 m k := (mem_suzukiZ0_iff hk).2 ⟨b, rfl⟩
    rw [← hQZ, Subgroup.mem_map_equiv] at h0
    exact h0
  have hadd : ∀ b b' : k,
      suzukiSElt m k 0 (b + b') = suzukiSElt m k 0 b * suzukiSElt m k 0 b' := fun b b' => by
    rw [suzukiSElt_mul hk]
    simp
  let f : Multiplicative k →* Q :=
    { toFun := fun b => ⟨(ψ.symm (suzukiSElt m k 0 b.toAdd) : G), hmem _⟩
      map_one' := Subtype.ext (by simp [suzukiSElt_zero_zero hk])
      map_mul' := fun b b' => Subtype.ext (by simp [toAdd_mul, hadd]) }
  have hinj : Function.Injective f := fun b b' hbb => by
    have h1 : ψ.symm (suzukiSElt m k 0 b.toAdd) = ψ.symm (suzukiSElt m k 0 b'.toAdd) :=
      Subtype.ext (congrArg (fun x : Q => (x : G)) hbb)
    exact Multiplicative.toAdd.injective (suzukiSElt_inj.1 (ψ.symm.injective h1)).2
  have hsurj : Function.Surjective f := fun y => by
    have hy : ψ ⟨y, hQK y.2⟩ ∈ suzukiZ0 m k := by
      rw [← hQZ, mem_map_subgroupOf_iff]
      exact y.2
    obtain ⟨b, hb⟩ := (mem_suzukiZ0_iff hk).1 hy
    refine ⟨.ofAdd b, Subtype.ext ?_⟩
    change (ψ.symm (suzukiSElt m k 0 b) : G) = y
    rw [hb, MulEquiv.symm_apply_apply]
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun b => rfl⟩

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
