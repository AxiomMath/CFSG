module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SH1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.LocalBalance

open scoped commutatorElement

section Central

theorem centerQuot_equiv {J : Type*} [Group J] (hJ : commutator J = ⊤) (N : Subgroup J) [N.Normal]
    (hN : N ≤ Subgroup.center J) :
    Nonempty ((J ⧸ N) ⧸ Subgroup.center (J ⧸ N) ≃* J ⧸ Subgroup.center J) := by
  have hk : (QuotientGroup.mk' N).ker ≤ Subgroup.center J := by
    rw [QuotientGroup.ker_mk']
    exact hN
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hJ (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hk
  exact ⟨e.symm⟩

theorem pCore_two_le_center {J : Type*} [Group J] [Finite J] (hJ : CFSG.Open.IsQuasisimple J) :
    CFSG.pCore 2 J ≤ Subgroup.center J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases normal_eq_top_or_le_center hJ (inferInstance : (CFSG.pCore 2 J).Normal) with h | h
  · exfalso
    have h2 : IsPGroup 2 J := by
      have hp : IsPGroup 2 (CFSG.pCore 2 J) := CFSG.pCore_isPGroup
      intro g
      obtain ⟨k, hk⟩ := hp ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hsol : Group.IsSolvable J := by
      haveI := h2.isNilpotent
      infer_instance
    obtain ⟨a, b, hab⟩ := exists_ne_comm_of_isQuasisimple hJ
    haveI : Group.IsPerfect J := ⟨hJ.1⟩
    haveI : Nontrivial J := ⟨⟨a * b, b * a, hab⟩⟩
    exact Group.IsPerfect.not_isSolvable J hsol
  · exact h

end Central

section At

variable {S : Type} [Group S] [Finite S]

@[expose] def NoA5ONAt (β : MulAut S) : Prop :=
  ∀ J : Subgroup S, J ≤ Sec4.autFix β → CFSG.IsQuasisimple ↥J →
    (J.subgroupOf (Sec4.autFix β)).IsSubnormal →
    ¬ (Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* Blueprint.NativeSporadic.ON))

theorem noA5ONAt_of_data {β : MulAut S} {q : ℕ}
    (h : ∀ J : Subgroup S, CFSG.Open.GLAPComponent 3 (Lemma510Ns.fixSub β) J →
      LieCompData q (barOf 3 J))
    (hA5 : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (alternatingGroup (Fin 5)))
    (hON : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q Blueprint.NativeSporadic.ON)
    (hON3 : 3 ∣ Nat.card Blueprint.NativeSporadic.ON) : NoA5ONAt β := by
  intro J hJ hq hsn hX
  have hJo : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq)
  have h3Q : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rcases hX with h5 | hO
    · obtain ⟨e⟩ := h5
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    · obtain ⟨e⟩ := hO
      rw [Nat.card_congr e.toEquiv]
      exact hON3
  have h3 : 3 ∣ Nat.card J := h3Q.trans (Subgroup.card_quotient_dvd_card _)
  have hd := h J (glaPComponent_of_autFix hJ hq hsn h3)
  obtain ⟨e₁⟩ := centerQuot_equiv hJo.1 (CFSG.Open.GLAPPrimeCore 3 ↥J)
    (glaPPrimeCore_le_center hJo h3)
  have hchev := hd.chev
  rcases hX with h5 | hO
  · obtain ⟨e⟩ := h5
    exact hA5 (isChevSimple_congr (e₁.trans e) hchev)
  · obtain ⟨e⟩ := hO
    exact hON (isChevSimple_congr (e₁.trans e) hchev)

end At

section Row

theorem centerQuot_A5 {K : Type*} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (h : Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5))) :
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := h
  obtain ⟨e₁⟩ := centerQuot_equiv hK.1 (CFSG.pCore 2 K) (pCore_two_le_center hK)
  have hZ : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hZ' : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g']
    rw [hZ, Subgroup.mem_bot] at this
    exact (map_eq_one_iff e e.injective).1 this
  let e₂ : (K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K) ≃* K ⧸ CFSG.pCore 2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
  exact ⟨(e₁.symm.trans e₂).trans e⟩

theorem centerQuot_ON {K : Type*} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hZON : Subgroup.center Blueprint.NativeSporadic.ON = ⊥)
    (h : IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))) :
    Nonempty (K ⧸ Subgroup.center K ≃* Blueprint.NativeSporadic.ON) := by
  have hk : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact pCore_two_le_center hK
  have hKn : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hK)
  have hM : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) :=
    (CFSG.LocalCores.quasisimple_central_quotient hKn _ (pCore_two_le_center hK)).1
  have hT := (isTripleCover_iff_isExtOf hM hZON).2 h
  obtain ⟨e₁⟩ := centerQuot_equiv hK.1 (CFSG.pCore 2 K) (pCore_two_le_center hK)
  obtain ⟨e⟩ := hT.2
  exact ⟨e₁.symm.trans e⟩


theorem row427_of_noA5ON {S : Type} [Group S] [Finite S]
    (h : ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* S) → ∀ τ : MulAut T, τ ^ 3 = 1 →
      NoA5ONAt τ) : Row427 S := by
  intro G _ _ _ A hA _ _ L hL ⟨e⟩ d hdA _ _ hLd K hK hKt
  obtain ⟨K', hK'def⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK'def ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have hK'eq : K'.subgroupOf (L ⊓ Subgroup.centralizer {d}) = K := by
    rw [hK'def]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) K
  let eK : ↥K ≃* ↥K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'def.symm)
  have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK'eq]; exact hK.2
  have hK'o : CFSG.Open.IsQuasisimple ↥K' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hK'q)
  obtain ⟨a₀, b₀, hab₀⟩ := exists_ne_comm_of_isQuasisimple hK'o
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := by
    by_contra hdN
    set L' : Subgroup G := L.map (MulAut.conj d).toMonoidHom with hL'def
    have hL' : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d) hL
    have hne : L ≠ L' := by
      intro hLL
      apply hdN
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hLL]
        exact ⟨x, hx, rfl⟩
      · intro hx
        rw [hLL] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := by
          have := hyx
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
          exact mul_left_cancel (mul_right_cancel this)
        rw [← this]
        exact hy
    rcases CFSG.LocalCores.distinct_components_commute hL hL' with h1 | h1
    · exact hne h1
    ·
      apply hab₀
      have hmem : ∀ x : ↥K', (x : G) ∈ L' := by
        intro x
        refine ⟨x, hK'L x.2, ?_⟩
        have hxd := Subgroup.mem_centralizer_singleton_iff.mp (hK'd x.2)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hxd]
        group
      apply Subtype.ext
      have hc : ⁅((b₀ : ↥K') : G), ((a₀ : ↥K') : G)⁆ ∈ ⁅L, L'⁆ :=
        Subgroup.commutator_mem_commutator (hK'L b₀.2) (hmem a₀)
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hτ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  set K₀ : Subgroup ↥L := K'.subgroupOf L with hK₀
  let eK₀ : ↥K₀ ≃* ↥K' := Subgroup.subgroupOfEquivOfLe hK'L
  have hK₀q : CFSG.IsQuasisimple ↥K₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK₀.symm hK'q
  have hK₀o : CFSG.Open.IsQuasisimple ↥K₀ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hK₀q)
  have hnot : ¬ K₀ ≤ (QuotientGroup.mk' (Subgroup.center ↥L)).ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    apply hab₀
    have hc : (⟨b₀, hK'L b₀.2⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hle (show (⟨b₀, hK'L b₀.2⟩ : ↥L) ∈ K₀ from b₀.2)
    apply Subtype.ext
    show (a₀ : G) * (b₀ : G) = (b₀ : G) * (a₀ : G)
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨a₀, hK'L a₀.2⟩)
    exact this
  have hKbq : CFSG.IsQuasisimple ↥(K₀.map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
    CFSG.LocalCores.isQuasisimple_map hK₀q _ hnot
  set ψ := (QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap K₀ with hψ
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap_surjective K₀
  have hψk : ψ.ker ≤ Subgroup.center ↥K₀ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : ↥L) ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 hx' (y : ↥L))
  obtain ⟨eψ⟩ := nonempty_centralQuotient_mulEquiv hK₀o.1 ψ hψs hψk
  have heK : Nonempty (↥K₀ ⧸ Subgroup.center ↥K₀ ≃* ↥K ⧸ Subgroup.center ↥K) :=
    ⟨QuotientGroup.congr _ _ (eK₀.trans eK.symm)
      (Subgroup.map_center_eq (eK₀.trans eK.symm))⟩
  obtain ⟨eKK⟩ := heK
  have hKo : CFSG.Open.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hK.1)
  have hX : Nonempty (↥(K₀.map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥(K₀.map (QuotientGroup.mk' (Subgroup.center ↥L))) ≃*
        alternatingGroup (Fin 5)) ∨
      Nonempty (↥(K₀.map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥(K₀.map (QuotientGroup.mk' (Subgroup.center ↥L))) ≃*
        Blueprint.NativeSporadic.ON) := by
    rcases hKt with h5 | ⟨-, hON⟩
    · obtain ⟨f⟩ := centerQuot_A5 hKo h5
      exact Or.inl ⟨(eψ.symm.trans eKK).trans f⟩
    · obtain ⟨f⟩ := centerQuot_ON hKo Item426.center_J3_McL_ON.2.2 hON
      exact Or.inr ⟨(eψ.symm.trans eKK).trans f⟩
  exact h _ ⟨e⟩ _ hτ3 _ (map_le_autFix hdN hK'd) hKbq (isSubnormal_bar hdN hK'M hK'sn) hX

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
