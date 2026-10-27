module

public import CFSG.Quasithin.Background.E6NineteenA
public import CFSG.Quasithin.H13.KGFact68Spor

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open CFSG.Blueprint

@[expose] def LieInvolCentCharTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SQTKCharTwoLie X → ∀ t : X, t ≠ 1 → t * t = 1 →
    CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({t} : Set X))

section Facts

theorem center_qbar_eq_bot {Y : Type} [Group Y] {K : Subgroup Y} (hK : CFSG.IsQuasisimple ↥K) :
    Subgroup.center (Bar.Qbar K) = ⊥ := by
  obtain ⟨-, hs, a, b, hab⟩ := hK
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar.Qbar K)) with h1 | h1
  · exact h1
  · exact absurd (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a) hab

theorem involFixInner_of_lie (hE : EvenLieAutInner) {X : Type} [Group X] [Finite X]
    (h : SQTKCharTwoLie X) : Inn.InvolFixInner X := by
  intro Q hQ β hβ2 hβ
  have hidx : ¬ 2 ∣ Q.index := by
    have h1 : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right Q
    have := hQ.2.2
    rwa [h1] at this
  exact hE X h β hβ2 ⟨hQ.2.1.toSylow hidx, hβ⟩

theorem oddInvertFree_of_lie (hE : EvenLieAutInner) (hC : LieInvolCentCharTwo) {X : Type}
    [Group X] [Finite X] (h : SQTKCharTwoLie X) (hZ : Subgroup.center X = ⊥) :
    OddInvertFree X :=
  oddInvertFree_of_charTwo hZ (involFixInner_of_lie hE h) (fun t ht1 htt => hC X h t ht1 htt)

theorem oddInvertFree_of_sporadic (hInn : SporadicAutInner)
    (hcyc : H13.KG68.SporadicSylowCenterCyclic) {s : TauCeti.SporadicName}
    (hs : IsLemma115SporadicName s) {X : Type} [Group X] [Finite X]
    (e : X ≃* NativeSporadic.Carrier s) (hZ : Subgroup.center X = ⊥) : OddInvertFree X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsq, hne⟩ := H13.KG68.isSQTK_of_isLemma115 hs
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  refine oddInvertFree_of_cyclic hZ ?_ ?_
  · intro Q hQ β hβ2 hβ
    have hidx : ¬ 2 ∣ Q.index := by
      have h1 : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right Q
      have := hQ.2.2
      rwa [h1] at this
    exact hInn s hsq hne X ⟨e⟩ β hβ2 ⟨hQ.2.1.toSylow hidx, hβ⟩
  · intro S hS
    have hidx : ¬ 2 ∣ S.index := by
      have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
      have := hS.2.2
      rwa [h1] at this
    let P : Sylow 2 X := hS.2.1.toSylow hidx
    let P' : Sylow 2 (NativeSporadic.Carrier s) := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hc := hcyc s hs P'
    have hSS : (P' : Subgroup (NativeSporadic.Carrier s)) = S.map e.toMonoidHom := rfl
    let f : ↥S ≃* ↥(P' : Subgroup (NativeSporadic.Carrier s)) :=
      (S.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hSS.symm)
    exact isCyclic_of_surjective
      ((Subgroup.centerCongr f).symm.toMonoidHom) (Subgroup.centerCongr f).symm.surjective

theorem center_eq_of_quot_simple {K : Type*} [Group K] (hK : CFSG.IsQuasisimple K)
    {N : Subgroup K} [N.Normal] (hNZ : N ≤ Subgroup.center K) (hs : IsSimpleGroup (K ⧸ N)) :
    Subgroup.center K = N := by
  refine le_antisymm ?_ hNZ
  have : ((Subgroup.center K).map (QuotientGroup.mk' N)).Normal :=
    (inferInstance : (Subgroup.center K).Normal).map _ (QuotientGroup.mk'_surjective N)
  rcases hs.eq_bot_or_eq_top_of_normal ((Subgroup.center K).map (QuotientGroup.mk' N)) with
    h1 | h1
  · intro c hc
    have h2 : (QuotientGroup.mk' N c) ∈ (Subgroup.center K).map (QuotientGroup.mk' N) :=
      ⟨c, hc, rfl⟩
    rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · exfalso
    have hall : ∀ k : K, k ∈ Subgroup.center K := by
      intro k
      obtain ⟨c, hc, hck⟩ := (h1 ▸ Subgroup.mem_top (QuotientGroup.mk' N k) :
        QuotientGroup.mk' N k ∈ (Subgroup.center K).map (QuotientGroup.mk' N))
      have h2 : c⁻¹ * k ∈ N := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hck
        exact hck
      have h3 : k = c * (c⁻¹ * k) := by group
      rw [h3]
      exact Subgroup.mul_mem _ hc (hNZ h2)
    obtain ⟨-, hsK, -⟩ := hK
    obtain ⟨a, b, hab⟩ := hsK.toNontrivial.exists_pair_ne
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.eq]
    exact hall _

end Facts

open Bar in
theorem e619Insp_of_facts (hE : EvenLieAutInner) (hC : LieInvolCentCharTwo)
    (hA6 : OddInvertFree (alternatingGroup (Fin 6)))
    (hU33 : ∀ (X : Type) [Group X] [Finite X],
      Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 → OddInvertFree X)
    (hL33 : ∀ (X : Type) [Group X] [Finite X],
      Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 3 1 → OddInvertFree X)
    (hL2p : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), IsFermatOrMersennePrime p →
      Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1 → OddInvertFree X)
    (hInn : SporadicAutInner) (hcyc : H13.KG68.SporadicSylowCenterCyclic)
    (hspor : ∀ s : TauCeti.SporadicName, IsLemma115SporadicName s →
      IsSimpleGroup (NativeSporadic.Carrier s)) : E619Insp := by
  refine e619Insp_of_oddInvertFree fun Y _ _ K z hKq hcases hD => ?_
  have hZ := center_qbar_eq_bot hKq
  rcases hcases with hA | hB | hC' | hD' | hE' | hF
  ·
    obtain ⟨hs, hlie, -⟩ := hA
    have hc : Subgroup.center ↥K = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple hKq hs
    let e : Qbar K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    refine OddInvertFree.of_mulEquiv e ?_
    rcases hlie with hsq | h6 | hu33
    · exact oddInvertFree_of_lie hE hC hsq hc
    · obtain ⟨e6⟩ := h6
      exact OddInvertFree.of_mulEquiv e6 hA6
    · exact hU33 _ hu33
  ·
    obtain ⟨-, hZO, hL, -⟩ := hB
    let e : Qbar K ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := QuotientGroup.quotientMulEquivOfEq hZO
    have hsq : SQTKCharTwoLie (Qbar K) := by
      rcases hL with h | h
      · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num,
          CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩)⟩)
      · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl,
          CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e h⟩))))⟩)
    exact oddInvertFree_of_lie hE hC hsq hZ
  ·
    obtain ⟨φ, -, -, -, -⟩ := hC'
    exact OddInvertFree.of_mulEquiv φ hA6
  · exact absurd hD' hD
  ·
    obtain ⟨hmodel, -⟩ := hE'
    have hs : IsSimpleGroup ↥K := by
      rcases hmodel with h33 | ⟨p, -, hp⟩
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 h33).2
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hp).2
    have hc : Subgroup.center ↥K = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple hKq hs
    let e : Qbar K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    refine OddInvertFree.of_mulEquiv e ?_
    rcases hmodel with h33 | ⟨p, hFM, hp⟩
    · exact hL33 _ h33
    · exact hL2p _ p hFM hp
  ·
    obtain ⟨⟨s, hs, ⟨ψ⟩⟩, -⟩ := hF
    have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      ψ.isSimpleGroup_congr.mpr (hspor s hs)
    have hO2 : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq
          (N := CFSG.pCore 2 ↥K) CFSG.pCore_normal with hN | hN
      · exfalso
        have : Group.IsPerfect ↥K := hKq.1
        have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
        have hp : IsPGroup 2 ↥K := by
          have h1 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
          rw [hN] at h1
          exact h1.of_equiv Subgroup.topEquiv
        exact Group.IsPerfect.not_isNilpotent ↥K hp.isNilpotent
      · exact hN
    have hZO : Subgroup.center ↥K = CFSG.pCore 2 ↥K :=
      center_eq_of_quot_simple hKq hO2 hsimple
    exact oddInvertFree_of_sporadic hInn hcyc hs
      ((QuotientGroup.quotientMulEquivOfEq hZO).trans ψ) hZ

end E6

end CFSG.Quasithin
