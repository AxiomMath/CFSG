module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Aux

variable {G : Type} [Group G]

theorem commutator_le_inf_of_normalizer {Q A : Subgroup G}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQA : Q ≤ Subgroup.normalizer (A : Set G)) :
    ⁅Q, A⁆ ≤ Q ⊓ A := by
  rw [Subgroup.commutator_le]
  intro q hq a ha
  refine ⟨?_, ?_⟩
  · have h1 : a * q⁻¹ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAQ ha) q⁻¹).mp (Subgroup.inv_mem _ hq)
    have : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hq h1
  · have h1 : q * a * q⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hQA hq) a).mp ha
    have : ⁅q, a⁆ = (q * a * q⁻¹) * a⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact mul_mem h1 (Subgroup.inv_mem _ ha)

theorem commutator_le_of_le_normalizer {N A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) : ⁅N, A⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro n hn a ha
  have h1 : a * n⁻¹ * a⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hA ha) n⁻¹).mp (Subgroup.inv_mem _ hn)
  have : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact mul_mem hn h1

theorem le_normalizer_sup {A X Y : Subgroup G} (hX : A ≤ Subgroup.normalizer (X : Set G))
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY ha)]

theorem le_normalizer_inf {A X Y : Subgroup G} (hX : A ≤ Subgroup.normalizer (X : Set G))
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY ha)]

theorem le_normalizer_commutator {X A : Subgroup G} (hX : A ≤ Subgroup.normalizer (X : Set G)) :
    A ≤ Subgroup.normalizer ((⁅X, A⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)]

end Aux

section Main

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_le_isPGroup {Q A : Subgroup G} (hQ2 : IsPGroup 2 Q) (h : A ≤ Q) :
    Group.IsSolvable ↥A := by
  have hA2 : IsPGroup 2 ↥A := hQ2.to_le h
  have : Group.IsNilpotent ↥A := hA2.isNilpotent
  infer_instance

theorem inf_ne_bot_of_levi {Q A L : Subgroup G} (hAL : A ≤ L) (hQ2 : IsPGroup 2 Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQA : Q ≤ Subgroup.normalizer (A : Set G))
    (hcent : L ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) (hAns : ¬ Group.IsSolvable ↥A) :
    Q ⊓ A ≠ ⊥ := by
  intro h
  have h1 : ⁅Q, A⁆ = ⊥ := le_bot_iff.1 ((commutator_le_inf_of_normalizer hAQ hQA).trans h.le)
  have h2 : A ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact h1)
  exact hAns (isSolvable_of_le_isPGroup hQ2 fun x hx => hcent ⟨hAL hx, h2 hx⟩)

@[expose] def BlockIrred (A : Subgroup G) : Prop :=
  blockZ A < blockU A ∧ ∀ W : Subgroup G, blockZ A ≤ W → W ≤ blockU A →
    A ≤ Subgroup.normalizer (W : Set G) → W = blockZ A ∨ W = blockU A

omit [Finite G] in
theorem IsShort2.blockIrred {A : Subgroup G} (h : IsShort2 A) : BlockIrred A := h.2.2.2.2

theorem not_blockIrred_of_levi {Q A L : Subgroup G} {J : Type} [Group J] [Finite J]
    (hAL : A ≤ L) (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) (hcent : L ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hperf : ⁅A, A⁆ = A) (θ : ↥A →* J) (hθ : Function.Surjective θ) (hθk : IsPGroup 2 θ.ker)
    (hθQ : ∀ x : ↥A, (x : G) ∈ Q → θ x = 1)
    (hJ : Subgroup.centralizer (CFSG.Open.pCore 2 J : Set J) ≤ CFSG.Open.pCore 2 J)
    (hJs : ¬ Group.IsSolvable J) :
    ¬ BlockIrred A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hirr'
  obtain ⟨-, hirr⟩ := hirr'
  set QA : Subgroup G := pCoreOf 2 A with hQAdef
  set U : Subgroup G := ⁅QA, A⁆ with hUdef
  set Z : Subgroup G := U ⊓ Subgroup.centralizer (A : Set G) with hZdef
  have hQAn : A ≤ Subgroup.normalizer (QA : Set G) := le_normalizer_pCoreOf 2 A
  have hQAA : QA ≤ A := pCoreOf_le 2 A
  set R : Subgroup G := θ.ker.map A.subtype with hRdef
  have hRA : R ≤ A := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := hθk.map _
  have hRsub : R.subgroupOf A = θ.ker :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  have hRnormal : (R.subgroupOf A).Normal := hRsub ▸ θ.normal_ker
  have hRn : A ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRA).mp hRnormal
  have hRQA : R ≤ QA := le_pCoreOf 2 hRA hRnormal hR2
  have hQ0R : Q ⊓ A ≤ R := by
    rintro x ⟨hxQ, hxA⟩
    exact ⟨⟨x, hxA⟩, MonoidHom.mem_ker.2 (hθQ ⟨x, hxA⟩ hxQ), rfl⟩
  have hUA : U ≤ A := (Subgroup.commutator_mono hQAA le_rfl).trans hperf.le
  have hZU : Z ≤ U := inf_le_left
  have hZc : Z ≤ Subgroup.centralizer (A : Set G) := inf_le_right
  have hUn : A ≤ Subgroup.normalizer (U : Set G) := le_normalizer_commutator hQAn
  have hZn : A ≤ Subgroup.normalizer (Z : Set G) := by
    have hAZ : A ≤ Subgroup.centralizer (Z : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun z hz => (Subgroup.mem_centralizer_iff.1 (hZc hz) a ha).symm
    exact hAZ.trans (Subgroup.centralizer_le_normalizer _)
  have hWn : A ≤ Subgroup.normalizer (((U ⊓ R) ⊔ Z : Subgroup G) : Set G) :=
    le_normalizer_sup (le_normalizer_inf hUn hRn) hZn
  rcases hirr ((U ⊓ R) ⊔ Z) le_sup_right (sup_le inf_le_left hZU) hWn with hW | hW
  ·
    have hUR : U ⊓ R ≤ Z := le_sup_left.trans hW.le
    set N : Subgroup G := ⁅Q, A⁆ with hNdef
    have hNle : N ≤ Q ⊓ A := commutator_le_inf_of_normalizer hAQ hQA
    have hNR : N ≤ R := hNle.trans hQ0R
    have h1 : ⁅N, A⁆ ≤ U ⊓ R :=
      le_inf (Subgroup.commutator_mono (hNR.trans hRQA) le_rfl)
        ((Subgroup.commutator_mono hNR le_rfl).trans (commutator_le_of_le_normalizer hRn))
    have hNAA : ⁅⁅N, A⁆, A⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 ((h1.trans hUR).trans hZc)
    have hAN : ⁅A, N⁆ = ⊥ := by
      have := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := N)
        (by rw [Subgroup.commutator_comm A N]; exact hNAA) hNAA
      rwa [hperf] at this
    have hNA : ⁅N, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hAN
    have hAQ' : ⁅A, Q⁆ = ⊥ := by
      have := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := Q)
        (by rw [Subgroup.commutator_comm A Q]; exact hNA) hNA
      rwa [hperf] at this
    have hAC : A ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hAQ'
    have hAsolv : Group.IsSolvable ↥A :=
      isSolvable_of_le_isPGroup hQ2 fun x hx => hcent ⟨hAL hx, hAC hx⟩
    exact hJs (Group.isSolvable_of_surjective hθ)
  ·
    have hUW : U ≤ (U ⊓ R) ⊔ Z := hW.ge
    let K0 : Subgroup ↥A := (Subgroup.center J).comap θ
    have hK0R : R ≤ K0.map A.subtype := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 hk]; exact Subgroup.one_mem _),
        rfl⟩
    have hK0Z : Z ≤ K0.map A.subtype := by
      intro z hz
      have hzA : z ∈ A := hUA (hZU hz)
      refine ⟨⟨z, hzA⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := hθ y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hZc hz) w w.2)
    have hUK : U ≤ K0.map A.subtype := hUW.trans (sup_le (inf_le_right.trans hK0R) hK0Z)
    set QA' : Subgroup ↥A := CFSG.Open.pCore 2 ↥A with hQA'
    have hQAmap : QA = QA'.map A.subtype := rfl
    have hAtop : (⊤ : Subgroup ↥A).map A.subtype = A := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hUmap : Subgroup.map A.subtype ⁅QA', (⊤ : Subgroup ↥A)⁆ = U := by
      rw [Subgroup.map_commutator, hAtop, ← hQAmap]
    have hUK' : ⁅QA', (⊤ : Subgroup ↥A)⁆ ≤ K0 :=
      (Subgroup.map_le_map_iff_of_injective A.subtype_injective).1 (hUmap.le.trans hUK)
    have hθtop : (⊤ : Subgroup ↥A).map θ = ⊤ := Subgroup.map_top_of_surjective θ hθ
    have hcomm : ⁅QA'.map θ, (⊤ : Subgroup J)⁆ ≤ Subgroup.center J :=
      calc ⁅QA'.map θ, (⊤ : Subgroup J)⁆ = ⁅QA'.map θ, (⊤ : Subgroup ↥A).map θ⁆ := by rw [hθtop]
        _ = Subgroup.map θ ⁅QA', (⊤ : Subgroup ↥A)⁆ := (Subgroup.map_commutator _ _ _).symm
        _ ≤ K0.map θ := Subgroup.map_mono hUK'
        _ ≤ Subgroup.center J := Subgroup.map_comap_le θ _
    set O : Subgroup J := CFSG.Open.pCore 2 J with hO
    have hOle : O ≤ QA'.map θ := by
      have hN : (O.comap θ).Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap θ
      have hp : IsPGroup 2 ↥(O.comap θ) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_ker_isPGroup θ hθk
      have h1 := CFSG.LieType.BorelTits.le_pCore 2 hN hp
      calc O = (O.comap θ).map θ := (Subgroup.map_comap_eq_self_of_surjective hθ O).symm
        _ ≤ QA'.map θ := Subgroup.map_mono h1
    have hOJ : ⁅O, (⊤ : Subgroup J)⁆ ≤ Subgroup.center J :=
      (Subgroup.commutator_mono hOle le_rfl).trans hcomm
    have hOJJ : ⁅⁅O, (⊤ : Subgroup J)⁆, (⊤ : Subgroup J)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hOJ.trans (Subgroup.center_le_centralizer _))
    have hJperf : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
      have h1 : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤ := by
        apply Subgroup.map_injective A.subtype_injective
        rw [Subgroup.map_commutator, hAtop, hperf]
      calc ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆
          = ⁅(⊤ : Subgroup ↥A).map θ, (⊤ : Subgroup ↥A).map θ⁆ := by rw [hθtop]
        _ = Subgroup.map θ ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ :=
            (Subgroup.map_commutator _ _ _).symm
        _ = ⊤ := by rw [h1, hθtop]
    have hOJ' : ⁅(⊤ : Subgroup J), O⁆ = ⊥ := by
      have := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup J))
        (H₂ := ⊤) (H₃ := O) (by rw [Subgroup.commutator_comm ⊤ O]; exact hOJJ) hOJJ
      rwa [hJperf] at this
    have htopO : (⊤ : Subgroup J) ≤ O :=
      le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hOJ') hJ
    have hJ2 : IsPGroup 2 J := fun x => by
      obtain ⟨k, hk⟩ :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 J))
          ⟨x, htopO (Subgroup.mem_top x)⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Group.IsNilpotent J := hJ2.isNilpotent
    exact hJs inferInstance

end Main

end CFSG.Quasithin.Rk2
