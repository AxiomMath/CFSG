module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Uniqueness
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

universe u

section General

variable {X G : Type u} [Group X] [Group G] (f : X →* G) (hf : Function.Injective f)

include hf in
theorem inSubgroup_map_of_injective (F : ∀ (K : Type u) [Group K], Subgroup K)
    (hF : ∀ (A B : Type u) [Group A] [Group B] (e : A ≃* B), (F A).map e.toMonoidHom = F B)
    (K : Subgroup X) : inSubgroup F (K.map f) = (inSubgroup F K).map f := by
  rw [inSubgroup, inSubgroup, ← hF _ _ (K.equivMapOfInjective f hf), Subgroup.map_map,
    Subgroup.map_map]
  rfl

include hf in
theorem inSubgroup_perfectResidual_map (K : Subgroup X) :
    inSubgroup perfectResidual (K.map f) = (inSubgroup perfectResidual K).map f :=
  inSubgroup_map_of_injective f hf _ (fun _ _ _ _ e => perfectResidual_map_mulEquiv e) K

include hf in
theorem pCoreOf_map (p : ℕ) (K : Subgroup X) :
    CFSG.Open.pCoreOf p (K.map f) = (CFSG.Open.pCoreOf p K).map f :=
  inSubgroup_map_of_injective f hf (CFSG.Open.pCore p)
    (fun _ _ _ _ e => CFSG.LieType.BorelTits.map_pCore_mulEquiv p e) K

include hf in
theorem inSubgroup_pPrimeCore_map (p : ℕ) (K : Subgroup X) :
    inSubgroup (CFSG.pPrimeCore p) (K.map f) = (inSubgroup (CFSG.pPrimeCore p) K).map f :=
  inSubgroup_map_of_injective f hf (CFSG.pPrimeCore p)
    (fun _ _ _ _ e => CFSG.pPrimeCore_map_iso p e) K

include hf in
theorem map_mem_oTwoComponentsIn_iff {K L : Subgroup X} :
    L.map f ∈ oTwoComponentsIn (K.map f) ↔ L ∈ oTwoComponentsIn K := by
  constructor
  · rintro ⟨L', hL', hLL'⟩
    set e := K.equivMapOfInjective f hf
    refine ⟨L'.map e.symm.toMonoidHom, map_mulEquiv_mem_oTwoComponents e.symm hL', ?_⟩
    apply Subgroup.map_injective hf
    change Subgroup.map (Subgroup.map f K).subtype L' = Subgroup.map f L at hLL'
    change Subgroup.map f (Subgroup.map K.subtype (Subgroup.map e.symm.toMonoidHom L')) = _
    rw [← hLL', Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    have h := congrArg Subtype.val (e.apply_symm_apply x)
    rw [Subgroup.coe_equivMapOfInjective_apply] at h
    exact h
  · rintro ⟨L', hL', rfl⟩
    refine ⟨L'.map (K.equivMapOfInjective f hf).toMonoidHom,
      map_mulEquiv_mem_oTwoComponents _ hL', ?_⟩
    change Subgroup.map _ (Subgroup.map _ L') = Subgroup.map f (Subgroup.map K.subtype L')
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl

include hf in
theorem map_mem_scriptH₀_iff {A M H : Subgroup X} :
    H.map f ∈ scriptH₀ (A.map f) (M.map f) ↔ H ∈ scriptH₀ A M := by
  simp only [mem_scriptH₀_iff, ← Subgroup.map_inf _ _ f hf, pCoreOf_map f hf,
    inSubgroup_perfectResidual_map f hf, ← Subgroup.map_sup,
    (Subgroup.map_injective hf).eq_iff, (Subgroup.map_injective hf).ne_iff,
    map_mem_oTwoComponentsIn_iff f hf]

end General

section Ranks

variable {G : Type u} [Group G]

theorem isE27_subgroupOf {A X : Subgroup G} (hA : IsE27 A) (hAX : A ≤ X) :
    IsE27 (A.subgroupOf X) := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G)
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
  · simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp hx)
  · rw [← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv

variable [Finite G]

theorem pRank_subgroupOf_le (p : ℕ) (hp : p.Prime) {X : Subgroup G} (K : Subgroup X) :
    CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (K.map X.subtype) :=
  CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp X.subtype
    X.subtype_injective K

theorem pRank_le_localRank_of_isTwoLocal {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hM : CFSG.Assembly.IsTwoLocal M) :
    CFSG.Open.pRank p M ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨M, hM, rfl⟩
  rintro _ ⟨Z, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
    (Subgroup.card_le_card_group Z)

theorem gamma_subgroupOf_le {X A : Subgroup G} (A' : Subgroup X) (hA' : A'.map X.subtype = A) :
    (gamma 2 A').map X.subtype ≤ gamma 2 A ⊓ X := by
  refine le_inf ?_ (Subgroup.map_subtype_le _)
  rw [Subgroup.map_le_iff_le_comap, gamma_le_iff]
  intro B' hB' hk
  rw [← Subgroup.map_le_iff_le_comap]
  refine (Subgroup.le_normalizer_map X.subtype).trans (normalizer_le_gamma ?_ ?_)
  · rw [← hA']
    exact Subgroup.map_mono hB'
  · exact hk.trans (pRank_subgroupOf_le 3 Nat.prime_three B')

end Ranks

section Sylow

variable {X G : Type*} [Group X] [Group G] [Finite X] [Finite G]

theorem IsSylowOf.map_of_injective {p : ℕ} [Fact p.Prime] {f : X →* G}
    (hf : Function.Injective f) {P K : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  exact ⟨Subgroup.map_mono hle, hP.map f, by rwa [Subgroup.relIndex_map_map_of_injective _ _ hf]⟩

end Sylow


section Ctx

variable {G : Type} [Group G] [Finite G]

theorem sec18Std_le {A M : Subgroup G} (h : Sec18Std G A M) : A ≤ M :=
  le_of_mem_scriptM_gamma (isE27_of_mem_partTwoE h.mem_partTwoE) h.mem_scriptM

theorem ctx444_subgroupOf {A M X : Subgroup G} (h : Sec18Std G A M) (hAX : A ≤ X)
    (hX : X ≠ ⊤) (hXM : X ⊓ M ≠ X) :
    Sec4.Ctx444 X (A.subgroupOf X) ((X ⊓ M).subgroupOf X) where
  sectionFourHyp := h.toTheoremFourHyp.sectionFourHyp hX
  isE27 := isE27_subgroupOf (isE27_of_mem_partTwoE h.mem_partTwoE) hAX
  lt_top := by
    refine lt_top_iff_ne_top.mpr fun heq => hXM (le_antisymm inf_le_left fun x hx => ?_)
    have hmem : (⟨x, hx⟩ : X) ∈ (X ⊓ M).subgroupOf X := heq ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  pRank_eq := by
    have hA' := isE27_subgroupOf (isE27_of_mem_partTwoE h.mem_partTwoE) hAX
    apply le_antisymm
    · calc CFSG.Open.pRank 3 ((X ⊓ M).subgroupOf X)
          ≤ CFSG.Open.pRank 3 (((X ⊓ M).subgroupOf X).map X.subtype) :=
            pRank_subgroupOf_le 3 Nat.prime_three _
        _ = CFSG.Open.pRank 3 (X ⊓ M) := by rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        _ ≤ CFSG.Open.pRank 3 M :=
            CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three inf_le_right
        _ ≤ CFSG.Assembly.RankThreeEven.localRank 3 G :=
            pRank_le_localRank_of_isTwoLocal Nat.prime_three h.mem_scriptM.1.1
        _ = 3 := h.toTheoremFourHyp.localRank_three
    · have hsub : A.subgroupOf X ≤ (X ⊓ M).subgroupOf X := fun x hx =>
        Subgroup.mem_subgroupOf.mpr ⟨x.2, sec18Std_le h (Subgroup.mem_subgroupOf.mp hx)⟩
      calc 3 = CFSG.Open.pRank 3 (A.subgroupOf X) := hA'.pRank_eq.symm
        _ ≤ _ := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three hsub
  gamma_le := by
    intro y hy
    have hmem := gamma_subgroupOf_le (X := X) (A := A) (A.subgroupOf X)
      (Subgroup.map_subgroupOf_eq_of_le hAX) (Subgroup.mem_map_of_mem X.subtype hy)
    exact Subgroup.mem_subgroupOf.mpr ⟨y.2, h.mem_scriptM.2 (Subgroup.mem_inf.mp hmem).1⟩

omit [Finite G] in
theorem mem_scriptH_of_subgroupOf {A M X : Subgroup G} (hAX : A ≤ X) (hX : X ≠ ⊤)
    {H : Subgroup X} (hH : H ∈ scriptH₀ (A.subgroupOf X) ((X ⊓ M).subgroupOf X)) :
    H.map X.subtype ∈ scriptH A M := by
  have h1 := (map_mem_scriptH₀_iff X.subtype X.subtype_injective).mpr hH
  rw [Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
  have hle : H.map X.subtype ≤ X := Subgroup.map_subtype_le H
  have hinf : H.map X.subtype ⊓ (X ⊓ M) = H.map X.subtype ⊓ M := by
    rw [← inf_assoc, inf_eq_left.mpr hle]
  refine mem_scriptH_iff_mem_scriptH₀.mpr ⟨?_, fun htop => hX (top_le_iff.mp (htop ▸ hle))⟩
  rw [mem_scriptH₀_iff] at h1 ⊢
  rwa [hinf] at h1

end Ctx

end CFSG.RankThree.PartTwo.Sec18
