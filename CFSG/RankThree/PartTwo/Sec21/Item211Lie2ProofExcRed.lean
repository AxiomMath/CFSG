module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofExc
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

namespace Item211Lie2Proof

@[expose] def ExcPlusFor (Y : Type) [Group Y] : Prop :=
  ∀ D : Subgroup (MulAut Y), D ≤ (MulAut.conj : Y →* MulAut Y).range → IsElemAbelian 3 D →
    Nat.card D = 9 → ∀ d ∈ D, d ≠ 1 → ∀ T : Subgroup (MulAut Y), IsPGroup 2 T →
      T ≤ Subgroup.centralizer (D : Set (MulAut Y)) →
      D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
        (conjClosure D ((MulAut.conj : Y →* MulAut Y).range ⊓
          Subgroup.centralizer ({d} : Set (MulAut Y))) ⊓
            Subgroup.centralizer (T : Set (MulAut Y))) : Subgroup (MulAut Y)) : Set (MulAut Y))

@[expose] def ExcMinusFor (Y : Type) [Group Y] : Prop :=
  ∀ D T : Subgroup (MulAut Y), D ≤ (MulAut.conj : Y →* MulAut Y).range →
    T ≤ (MulAut.conj : Y →* MulAut Y).range → IsElemAbelian 3 D → Nat.card D = 9 →
    IsElemAbelian 2 T → Nat.card T = 4 → D ≤ Subgroup.normalizer (T : Set (MulAut Y)) →
    ⁅T, D⁆ = T → ∀ u ∈ T, u ≠ 1 →
      D ⊓ Subgroup.centralizer (T : Set (MulAut Y)) ≤ Subgroup.centralizer ((inSubgroup
        (CFSG.pCore 2) (threeGen ((MulAut.conj : Y →* MulAut Y).range ⊓
          Subgroup.centralizer ({u} : Set (MulAut Y))) ⊓
            Subgroup.centralizer (T : Set (MulAut Y))) : Subgroup (MulAut Y)) : Set (MulAut Y))

section Transport

variable {M M' : Type} [Group M] [Group M'] (Ψ : M ≃* M')

theorem map_centralizer_mulEquiv (s : Set M) :
    (Subgroup.centralizer s).map Ψ.toMonoidHom = Subgroup.centralizer (Ψ '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx a ha]
  · intro hy
    refine ⟨Ψ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro a ha
    apply Ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hy (Ψ a) ⟨a, ha, rfl⟩

theorem map_centralizer_subgroup_mulEquiv (S : Subgroup M) :
    (Subgroup.centralizer (S : Set M)).map Ψ.toMonoidHom =
      Subgroup.centralizer ((S.map Ψ.toMonoidHom : Subgroup M') : Set M') := by
  rw [map_centralizer_mulEquiv, Subgroup.coe_map]
  rfl

theorem map_centralizer_singleton_mulEquiv (d : M) :
    (Subgroup.centralizer ({d} : Set M)).map Ψ.toMonoidHom =
      Subgroup.centralizer ({Ψ d} : Set M') := by
  rw [map_centralizer_mulEquiv, Set.image_singleton]

theorem map_conjClosure_mulEquiv (D H : Subgroup M) :
    (conjClosure D H).map Ψ.toMonoidHom =
      conjClosure (D.map Ψ.toMonoidHom) (H.map Ψ.toMonoidHom) := by
  unfold conjClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, hg, x, hx, rfl⟩, rfl⟩
    exact ⟨Ψ g, ⟨g, hg, rfl⟩, Ψ x, ⟨x, hx, rfl⟩, by simp [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g * x * g⁻¹, ⟨g, hg, x, hx, rfl⟩, by simp [map_mul, map_inv]⟩

theorem map_threeGen_mulEquiv (H : Subgroup M) :
    (threeGen H).map Ψ.toMonoidHom = threeGen (H.map Ψ.toMonoidHom) := by
  unfold threeGen
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, n, hn⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, n, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hn, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, n, hn⟩
    refine ⟨x, ⟨hx, n, ?_⟩, rfl⟩
    apply Ψ.injective
    rw [map_pow, map_one]
    exact hn

theorem map_inSubgroup_pCore_mulEquiv (H : Subgroup M) :
    (inSubgroup (CFSG.pCore 2) H).map Ψ.toMonoidHom =
      inSubgroup (CFSG.pCore 2) (H.map Ψ.toMonoidHom) := by
  unfold inSubgroup
  have e : Ψ.toMonoidHom = (Ψ : M →* M') := rfl
  rw [e, ← CFSG.pCore_map_iso 2 (Ψ.subgroupMap H), Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_inf_mulEquiv (H K : Subgroup M) :
    (H ⊓ K).map Ψ.toMonoidHom = H.map Ψ.toMonoidHom ⊓ K.map Ψ.toMonoidHom :=
  Subgroup.map_inf_eq H K Ψ.toMonoidHom Ψ.injective

end Transport

theorem map_range_conj_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (MulAut.conj : X →* MulAut X).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : Y →* MulAut Y).range :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e

theorem isElemAbelian_map_mulEquiv {M M' : Type} [Group M] [Group M'] (Ψ : M ≃* M') {p : ℕ}
    {D : Subgroup M} (hD : IsElemAbelian p D) : IsElemAbelian p (D.map Ψ.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hD _

theorem excPlusFor_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ExcPlusFor Y) : ExcPlusFor X := by
  intro D hDi hDe hD9 d hd hd1 T hT2 hTD
  set Ψ := MulAut.congr e with hΨ
  have hInn := map_range_conj_congr e
  rw [← hΨ] at hInn
  have hDi' : D.map Ψ.toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
    rw [← hInn]
    exact Subgroup.map_mono hDi
  have hTD' : T.map Ψ.toMonoidHom ≤
      Subgroup.centralizer ((D.map Ψ.toMonoidHom : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    rw [← map_centralizer_subgroup_mulEquiv]
    exact Subgroup.map_mono hTD
  have key := hY (D.map Ψ.toMonoidHom) hDi' (isElemAbelian_map_mulEquiv Ψ hDe)
    (by rw [Subgroup.card_map_of_injective Ψ.injective, hD9]) (Ψ d) ⟨d, hd, rfl⟩
    (fun h => hd1 (Ψ.injective (by rw [h, map_one]))) (T.map Ψ.toMonoidHom) (hT2.map _) hTD'
  have hEq : (Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D ((MulAut.conj : X →* MulAut X).range ⊓
        Subgroup.centralizer ({d} : Set (MulAut X))) ⊓
          Subgroup.centralizer (T : Set (MulAut X))) : Subgroup (MulAut X)) :
            Set (MulAut X))).map Ψ.toMonoidHom = Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure (D.map Ψ.toMonoidHom) ((MulAut.conj : Y →* MulAut Y).range ⊓
        Subgroup.centralizer ({Ψ d} : Set (MulAut Y))) ⊓
          Subgroup.centralizer ((T.map Ψ.toMonoidHom : Subgroup (MulAut Y)) :
            Set (MulAut Y))) : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    rw [map_centralizer_subgroup_mulEquiv, map_inSubgroup_pCore_mulEquiv, map_inf_mulEquiv,
      map_conjClosure_mulEquiv, map_inf_mulEquiv, hInn, map_centralizer_singleton_mulEquiv,
      map_centralizer_subgroup_mulEquiv]
  rw [← hEq] at key
  exact (Subgroup.map_le_map_iff_of_injective Ψ.injective).mp key

theorem excMinusFor_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ExcMinusFor Y) : ExcMinusFor X := by
  intro D T hDi hTi hDe hD9 hTe hT4 hDT hTD u hu hu1
  set Ψ := MulAut.congr e with hΨ
  have hInn := map_range_conj_congr e
  rw [← hΨ] at hInn
  have hDi' : D.map Ψ.toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
    rw [← hInn]
    exact Subgroup.map_mono hDi
  have hTi' : T.map Ψ.toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
    rw [← hInn]
    exact Subgroup.map_mono hTi
  have key := hY (D.map Ψ.toMonoidHom) (T.map Ψ.toMonoidHom) hDi' hTi'
    (isElemAbelian_map_mulEquiv Ψ hDe)
    (by rw [Subgroup.card_map_of_injective Ψ.injective, hD9])
    (isElemAbelian_map_mulEquiv Ψ hTe)
    (by rw [Subgroup.card_map_of_injective Ψ.injective, hT4])
    ((Subgroup.map_mono hDT).trans (Subgroup.le_normalizer_map _))
    (by rw [← Subgroup.map_commutator, hTD]) (Ψ u) ⟨u, hu, rfl⟩
    (fun h => hu1 (Ψ.injective (by rw [h, map_one])))
  have hEq : (Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (threeGen ((MulAut.conj : X →* MulAut X).range ⊓
        Subgroup.centralizer ({u} : Set (MulAut X))) ⊓
          Subgroup.centralizer (T : Set (MulAut X))) : Subgroup (MulAut X)) :
            Set (MulAut X))).map Ψ.toMonoidHom = Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (threeGen ((MulAut.conj : Y →* MulAut Y).range ⊓
        Subgroup.centralizer ({Ψ u} : Set (MulAut Y))) ⊓
          Subgroup.centralizer ((T.map Ψ.toMonoidHom : Subgroup (MulAut Y)) :
            Set (MulAut Y))) : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    rw [map_centralizer_subgroup_mulEquiv, map_inSubgroup_pCore_mulEquiv, map_inf_mulEquiv,
      map_threeGen_mulEquiv, map_inf_mulEquiv, hInn, map_centralizer_singleton_mulEquiv,
      map_centralizer_subgroup_mulEquiv]
  have hEq2 : (D ⊓ Subgroup.centralizer (T : Set (MulAut X))).map Ψ.toMonoidHom =
      D.map Ψ.toMonoidHom ⊓ Subgroup.centralizer ((T.map Ψ.toMonoidHom : Subgroup (MulAut Y)) :
        Set (MulAut Y)) := by
    rw [map_inf_mulEquiv, map_centralizer_subgroup_mulEquiv]
  rw [← hEq, ← hEq2] at key
  exact (Subgroup.map_le_map_iff_of_injective Ψ.injective).mp key

end Item211Lie2Proof

open Item211Lie2Proof

@[expose] def KS211ExcPlusG2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p →
    ExcPlusFor (CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K)

@[expose] def KS211ExcPlusSp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ExcPlusFor (projSp 2 (GaloisField p 1))

@[expose] def KS211ExcPlusU4 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ExcPlusFor (projSU 4 p 1)

@[expose] def KS211ExcPlusL4 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → ExcPlusFor (projSL 4 (GaloisField p 1))

@[expose] def KS211ExcMinusG2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p →
    ExcMinusFor (CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K)

@[expose] def KS211ExcMinusSp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ExcMinusFor (projSp 2 (GaloisField p 1))

@[expose] def KS211ExcMinusU4 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ExcMinusFor (projSU 4 p 1)

@[expose] def KS211ExcMinusL4 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → ExcMinusFor (projSL 4 (GaloisField p 1))

theorem ks211ExcPlus_of_models (hG2 : KS211ExcPlusG2) (hSp : KS211ExcPlusSp)
    (hU4 : KS211ExcPlusU4) (hL4 : KS211ExcPlusL4) : KS211ExcPlus := by
  intro X _ _ _ hM
  obtain ⟨p, hp, hp3, hcase⟩ := hM
  change ExcPlusFor X
  rcases hcase with hG | hS | ⟨hp1, hU⟩ | ⟨hp2, hL⟩
  · obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hG
    exact excPlusFor_of_mulEquiv φ (hG2 p hp3 K (by rw [hK, pow_one]))
  · obtain ⟨φ⟩ := hS
    exact excPlusFor_of_mulEquiv φ (hSp p hp3)
  · obtain ⟨φ⟩ := hU
    exact excPlusFor_of_mulEquiv φ (hU4 p hp3 hp1)
  · obtain ⟨φ⟩ := hL
    exact excPlusFor_of_mulEquiv φ (hL4 p hp3 hp2)

theorem ks211ExcMinus_of_models (hG2 : KS211ExcMinusG2) (hSp : KS211ExcMinusSp)
    (hU4 : KS211ExcMinusU4) (hL4 : KS211ExcMinusL4) : KS211ExcMinus := by
  intro X _ _ _ hM
  obtain ⟨p, hp, hp3, hcase⟩ := hM
  change ExcMinusFor X
  rcases hcase with hG | hS | ⟨hp1, hU⟩ | ⟨hp2, hL⟩
  · obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hG
    exact excMinusFor_of_mulEquiv φ (hG2 p hp3 K (by rw [hK, pow_one]))
  · obtain ⟨φ⟩ := hS
    exact excMinusFor_of_mulEquiv φ (hSp p hp3)
  · obtain ⟨φ⟩ := hU
    exact excMinusFor_of_mulEquiv φ (hU4 p hp3 hp1)
  · obtain ⟨φ⟩ := hL
    exact excMinusFor_of_mulEquiv φ (hL4 p hp3 hp2)

end CFSG.RankThree.PartTwo.Sec21
