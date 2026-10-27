module

public import CFSG.Quasithin.MS93.PUCrit
public import CFSG.Quasithin.Background.C2Blocks
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

section Normalizers

theorem le_normalizer_inf {M A B : Subgroup G} (hA : M ≤ Subgroup.normalizer (A : Set G))
    (hB : M ≤ Subgroup.normalizer (B : Set G)) : M ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) :
      Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 (hA hg) x,
    Subgroup.mem_normalizer_iff.1 (hB hg) x]

theorem le_normalizer_centralizer {M A : Subgroup G} (hA : M ≤ Subgroup.normalizer (A : Set G)) :
    M ≤ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  have key : ∀ g ∈ M, ∀ c ∈ Subgroup.centralizer (A : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (hA (inv_mem hg)) a).1 ha
    rw [inv_inv] at ha'
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ ha'
    calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * a := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_commutator {M A B : Subgroup G} (hA : M ≤ Subgroup.normalizer (A : Set G))
    (hB : M ≤ Subgroup.normalizer (B : Set G)) :
    M ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hg
    have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj g) ⁅a, b⁆ ∈ ⁅A, B⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hA hg) a).1 ha)
        ((Subgroup.mem_normalizer_iff.1 (hB hg) b).1 hb)
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem commutator_le_of_le {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) : ⁅A, B⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact M.mul_mem (M.mul_mem (M.mul_mem (hA ha) (hB hb)) (M.inv_mem (hA ha))) (M.inv_mem (hB hb))

theorem commutator_le_left_of_le_normalizer {K L : Subgroup G}
    (h : L ≤ Subgroup.normalizer (K : Set G)) : ⁅K, L⁆ ≤ K :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 h

theorem le_centralizer_of_card_eq_two {M N : Subgroup G}
    (hN : M ≤ Subgroup.normalizer (N : Set G)) (h2 : Nat.card N = 2) :
    N ≤ Subgroup.centralizer (M : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  have hmx : m * x * m⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hN hm) x).1 hx
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).1 h2
  have e1 : (⟨x, hx⟩ : N) = y := huniq _ fun h => hx1 (congrArg Subtype.val h)
  have e2 : (⟨m * x * m⁻¹, hmx⟩ : N) = y := huniq _ fun h => by
    have h' : m * x * m⁻¹ = 1 := congrArg Subtype.val h
    have h'' : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    exact hx1 (by rw [h'', h']; group)
  have e : m * x * m⁻¹ = x := congrArg Subtype.val (e2.trans e1.symm)
  calc m * x = m * x * m⁻¹ * m := by group
    _ = x * m := by rw [e]

end Normalizers

section Hypothesis

variable [Finite G]

structure PUHyp (M T L : Subgroup G) : Prop where
  le : T ≤ M
  isPGroup : IsPGroup 2 T
  ne_bot : T ≠ ⊥
  noChar : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
    ¬ M ≤ Subgroup.normalizer (C : Set G)
  pCore_le : pCoreOf 2 M ≤ T
  charTwo : CharTwo M
  L_le : L ≤ M
  le_normalizer : M ≤ Subgroup.normalizer (L : Set G)
  eq_sup : M = L ⊔ T
  perfect : ⁅L, L⁆ = L
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  rankTwo : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  sqtk : IsSQTKIn M

@[expose] def PUMin (M T L : Subgroup G) : Prop :=
  ∀ T₁ : Subgroup G, T₁ ≤ T → (T₁.subgroupOf T).Characteristic →
    (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁ → T₁ = T

end Hypothesis

section Objects

abbrev Z0q (M T : Subgroup G) : Subgroup G := normalClosureIn M (omegaOneCenterOf T)

abbrev Xq (M : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 M)

abbrev Uq (M T L : Subgroup G) : Subgroup G := ⁅Z0q M T, L⁆

abbrev Dq (M L : Subgroup G) : Subgroup G := pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G)

abbrev Zq (M L : Subgroup G) : Subgroup G := Xq M ⊓ Subgroup.centralizer (L : Set G)

abbrev Vq (M L : Subgroup G) : Subgroup G := ⁅pCoreOf 2 M, L⁆

abbrev Cq (M T : Subgroup G) : Subgroup G := M ⊓ Subgroup.centralizer (Z0q M T : Set G)

theorem pCoreOf_le' (M : Subgroup G) : pCoreOf 2 M ≤ M := CFSG.openPCoreOf_le 2 M

theorem le_normalizer_pCoreOf (M : Subgroup G) :
    M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M

theorem Z0q_le (M T : Subgroup G) : Z0q M T ≤ M := normalClosureIn_le M _

theorem le_normalizer_Z0q (M T : Subgroup G) :
    M ≤ Subgroup.normalizer (Z0q M T : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Z0q_le M T)).1 (normalClosureIn_normal M _)

theorem Xq_le_pCoreOf (M : Subgroup G) : Xq M ≤ pCoreOf 2 M := PU.omegaOneCenterOf_le _

theorem Xq_le (M : Subgroup G) : Xq M ≤ M := (Xq_le_pCoreOf M).trans (pCoreOf_le' M)

theorem Xq_normal (M : Subgroup G) : ((Xq M).subgroupOf M).Normal := by
  have : (CFSG.Open.pCore 2 ↥M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rw [Xq, pCoreOf, PU.omegaOneCenterOf_map M.subtype_injective, PU.map_subtype_subgroupOf]
  exact PU.omegaOneCenterOf_normal _

theorem le_normalizer_Xq (M : Subgroup G) : M ≤ Subgroup.normalizer (Xq M : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Xq_le M)).1 (Xq_normal M)

variable {M T L : Subgroup G}

theorem Uq_le_Z0q (hL : L ≤ M) : Uq M T L ≤ Z0q M T :=
  commutator_le_left_of_le_normalizer (hL.trans (le_normalizer_Z0q M T))

theorem Uq_le (hL : L ≤ M) : Uq M T L ≤ M := (Uq_le_Z0q hL).trans (Z0q_le M T)

theorem le_normalizer_Uq (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  le_normalizer_commutator (le_normalizer_Z0q M T) hLn

theorem Vq_le_pCoreOf (hL : L ≤ M) : Vq M L ≤ pCoreOf 2 M :=
  commutator_le_left_of_le_normalizer (hL.trans (le_normalizer_pCoreOf M))

theorem Vq_le (hL : L ≤ M) : Vq M L ≤ M := (Vq_le_pCoreOf hL).trans (pCoreOf_le' M)

theorem le_normalizer_Vq (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (Vq M L : Set G) :=
  le_normalizer_commutator (le_normalizer_pCoreOf M) hLn

theorem Dq_le : Dq M L ≤ M := inf_le_left.trans (pCoreOf_le' M)

theorem le_normalizer_Dq (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (Dq M L : Set G) :=
  le_normalizer_inf (le_normalizer_pCoreOf M) (le_normalizer_centralizer hLn)

theorem Zq_le : Zq M L ≤ M := inf_le_left.trans (Xq_le M)

theorem le_normalizer_Zq (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (Zq M L : Set G) :=
  le_normalizer_inf (le_normalizer_Xq M) (le_normalizer_centralizer hLn)

theorem Cq_le : Cq M T ≤ M := inf_le_left

theorem le_normalizer_Cq : M ≤ Subgroup.normalizer (Cq M T : Set G) :=
  le_normalizer_inf (Subgroup.le_normalizer) (le_normalizer_centralizer (le_normalizer_Z0q M T))

end Objects

section Consequences

variable [Finite G] {M T L : Subgroup G}

theorem PUHyp.hyp20 (h : PUHyp M T L) : Hyp20 (puAmalgam h.le) :=
  hyp20_puAmalgam h.le h.isPGroup h.ne_bot h.noChar

theorem PUHyp.critDist_pos (h : PUHyp M T L) : 0 < critDist (puAmalgam h.le) :=
  puAmalgam.critDist_pos h.le h.isPGroup h.ne_bot h.noChar h.pCore_le h.charTwo

theorem PUHyp.normalCoreIn_eq (h : PUHyp M T L) : normalCoreIn M T = pCoreOf 2 M :=
  normalCoreIn_eq_pCoreOf h.le h.isPGroup h.pCore_le

theorem PUHyp.Z0q_le_Xq (h : PUHyp M T L) : Z0q M T ≤ Xq M := by
  refine normalClosureIn_le_of (Xq_le M) (Xq_normal M) (inf_le_left.trans ?_)
  have hZQ := PU.omegaOneCenterOf_le_pCoreOf h.le h.pCore_le h.charTwo
  unfold omegaOneCenterOf omegaOneOf
  rw [Subgroup.closure_le]
  rintro x ⟨⟨hxT, hxC⟩, hx2⟩
  refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hx2⟩
  · exact hZQ (Subgroup.subset_closure ⟨⟨hxT, hxC⟩, hx2⟩)
  · exact Subgroup.centralizer_le h.pCore_le hxC

theorem PUHyp.Z0q_le_pCoreOf (h : PUHyp M T L) : Z0q M T ≤ pCoreOf 2 M :=
  h.Z0q_le_Xq.trans (Xq_le_pCoreOf M)

theorem PUHyp.Uq_le_Xq (h : PUHyp M T L) : Uq M T L ≤ Xq M :=
  (Uq_le_Z0q h.L_le).trans h.Z0q_le_Xq

theorem PUHyp.Uq_inf_Dq (h : PUHyp M T L) :
    Uq M T L ⊓ Dq M L = Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  rw [Dq, ← inf_assoc, inf_eq_left.2 (h.Uq_le_Xq.trans (Xq_le_pCoreOf M))]

theorem PUHyp.Uq_inf_Zq (h : PUHyp M T L) :
    Uq M T L ⊓ Zq M L = Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  rw [Zq, ← inf_assoc, inf_eq_left.2 h.Uq_le_Xq]

theorem PUHyp.L_ne_bot (h : PUHyp M T L) : L ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, a, b, hab⟩ := h.quasisimple
  exact hab (Subsingleton.elim _ _)

theorem PUHyp.ne_bot_of_inf_le (h : PUHyp M T L) {T₁ : Subgroup G}
    (hT₁ : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁) : T₁ ≠ ⊥ := by
  rintro rfl
  rw [sup_bot_eq, le_bot_iff] at hT₁
  have hcomm : ⁅L, pCoreOf 2 M⁆ ≤ L ⊓ pCoreOf 2 M := by
    refine le_inf (commutator_le_left_of_le_normalizer ((pCoreOf_le' M).trans h.le_normalizer))
      ?_
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (h.L_le.trans (le_normalizer_pCoreOf M))
  rw [hT₁, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  have hLQ : L ≤ pCoreOf 2 M := (le_inf h.L_le hcomm).trans h.charTwo
  exact h.L_ne_bot (by rw [← inf_eq_left.2 hLQ, hT₁])

end Consequences

section Transport

variable {M T : Subgroup G} (hTM : T ≤ M)

theorem commutator_subgroupOf {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    (⁅K, K'⁆).subgroupOf M = ⁅K.subgroupOf M, K'.subgroupOf M⁆ := by
  conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hK, ← Subgroup.map_subgroupOf_eq_of_le hK',
    ← Subgroup.map_commutator]
  exact PU.map_subtype_subgroupOf _

theorem imM_commutator {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM ⁅K, K'⁆ = ⁅imM hTM K, imM hTM K'⁆ := by
  rw [imM, imM, imM, commutator_subgroupOf hK hK', Subgroup.map_commutator]

theorem imM_inf_centralizer (K : Subgroup G) {K' : Subgroup G} (hK' : K' ≤ M) :
    imM hTM (K ⊓ Subgroup.centralizer (K' : Set G)) =
      imM hTM K ⊓ Subgroup.centralizer (imM hTM K' : Set (puAmalgam hTM).Universal) := by
  have hC : imM hTM (Subgroup.centralizer (K' : Set G)) =
      (puAmalgam hTM).ofA.range ⊓
        Subgroup.centralizer (imM hTM K' : Set (puAmalgam hTM).Universal) := by
    have h1 : (Subgroup.centralizer (K' : Set G)).subgroupOf M =
        Subgroup.centralizer ((K'.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      have h2 := PU.inf_centralizer_subgroupOf (K'.subgroupOf M)
      rw [Subgroup.map_subgroupOf_eq_of_le hK'] at h2
      rw [← h2]
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [imM, h1, ← PU.range_inf_centralizer_map (puAmalgam hTM).ofA_injective]
    rfl
  rw [imM_inf, hC, ← inf_assoc, inf_eq_left.2 (show imM hTM K ≤ (puAmalgam hTM).ofA.range from
    Subgroup.map_le_range _ _)]

variable {hTM}

theorem puTrans_commutator {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M)
    (hKn : M ≤ Subgroup.normalizer (K : Set G)) (hK'n : M ≤ Subgroup.normalizer (K' : Set G))
    {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    puTrans hTM ⁅K, K'⁆ α = ⁅puTrans hTM K α, puTrans hTM K' α⁆ := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hα
  have hn : ∀ {N : Subgroup G}, N ≤ M → M ≤ Subgroup.normalizer (N : Set G) →
      (N.subgroupOf M).Normal := fun hN hNn =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 hNn
  rw [puTrans_smul_baseA (hn (commutator_le_of_le hK hK') (le_normalizer_commutator hKn hK'n)),
    puTrans_smul_baseA (hn hK hKn), puTrans_smul_baseA (hn hK' hK'n), imM_commutator hTM hK hK',
    Subgroup.map_commutator]

theorem puTrans_inf_centralizer {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M)
    (hKn : M ≤ Subgroup.normalizer (K : Set G)) (hK'n : M ≤ Subgroup.normalizer (K' : Set G))
    {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    puTrans hTM (K ⊓ Subgroup.centralizer (K' : Set G)) α =
      puTrans hTM K α ⊓
        Subgroup.centralizer (puTrans hTM K' α : Set (puAmalgam hTM).Universal) := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hα
  have hn : ∀ {N : Subgroup G}, N ≤ M → M ≤ Subgroup.normalizer (N : Set G) →
      (N.subgroupOf M).Normal := fun hN hNn =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 hNn
  rw [puTrans_smul_baseA (hn (inf_le_left.trans hK)
      (le_normalizer_inf hKn (le_normalizer_centralizer hK'n))),
    puTrans_smul_baseA (hn hK hKn), puTrans_smul_baseA (hn hK' hK'n),
    imM_inf_centralizer hTM K hK',
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    PU.centralizer_map_mulEquiv]

end Transport

section VertexObjects

variable [Finite G] {M T L : Subgroup G}

theorem PUHyp.qv_eq (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Qv _ α = puTrans h.le (pCoreOf 2 M) α := by
  rw [qv_eq_puTrans h.le hα, h.normalCoreIn_eq]

theorem PUHyp.xm_eq (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    XM _ α = puTrans h.le (Xq M) α := by
  rw [xm_eq_puTrans h.le hα, h.normalCoreIn_eq]

theorem PUHyp.puTrans_Uq (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    puTrans h.le (Uq M T L) α = ⁅ZM _ α, puTrans h.le L α⁆ := by
  rw [Uq, puTrans_commutator (Z0q_le M T) h.L_le (le_normalizer_Z0q M T) h.le_normalizer hα,
    ← zm_eq_puTrans h.le hα]

theorem PUHyp.puTrans_Dq (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    puTrans h.le (Dq M L) α =
      Qv _ α ⊓ Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal) := by
  rw [Dq, puTrans_inf_centralizer (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M)
    h.le_normalizer hα, ← h.qv_eq hα]

theorem PUHyp.puTrans_Zq (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    puTrans h.le (Zq M L) α =
      XM _ α ⊓ Subgroup.centralizer (puTrans h.le L α : Set (puAmalgam h.le).Universal) := by
  rw [Zq, puTrans_inf_centralizer (Xq_le M) h.L_le (le_normalizer_Xq M) h.le_normalizer hα,
    ← h.xm_eq hα]

end VertexObjects

section Parabolic

@[expose] def IsParRadOver (L A X : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsMaxParabolic2 L P ∧ A ≤ P ∧ X = pCoreOf 2 P

@[expose] def IsOddRadical (M T : Subgroup G) : Prop :=
  T = pCoreOf 2 (M ⊓ Subgroup.normalizer (T : Set G)) ∧
    ¬ 2 ∣ (Subgroup.normalizer (T : Set G)).relIndex M

end Parabolic

end CFSG.Quasithin.MS93
