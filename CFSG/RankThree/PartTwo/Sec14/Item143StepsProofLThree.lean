module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
public import CFSG.RankThree.PartTwo.Sec13.Item137ProofTau
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS142SignalLThreePi : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      ∀ b ∈ E, b ≠ 1 → SignalAt E b

@[expose] def Step142LThreePiPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) → Inspect142At A c

variable {G : Type} [Group G] [Finite G]

theorem inspect142At_of_signalAt {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hsig : ∀ b ∈ A ⊓ L, b ≠ 1 → ∀ hbL : b ∈ L,
      SignalAt ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩)) :
    Inspect142At A c := by
  intro Q hQ B hB hcB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27'
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hCL := centralizer_le_normalizer_of_three_dvd h h3
  have hQc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hQ.prop
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  set Y' := Q ⊓ Subgroup.centralizer (B : Set G) with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans hQc
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    le_normalizer_inf_centralizer hA.1.1 hQ.prop.2.2 hB.1
  obtain ⟨b, hbBE, hb1, hBeq⟩ :=
    exists_eq_closure_pair hA hB inf_le_left h9 hcB fun hc => hcL hc.2
  have hbA : b ∈ A := hbBE.2.1
  have hbL : b ∈ L := hbBE.2.2
  have hCBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbBE.1)
  have hCBc : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  set Z := ⁅Y', A⁆ with hZdef
  have hZY' : Z ≤ Y' := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y' A hAY'
  have hZL : Z ≤ L := commutator_le_of_eq_zpowers_sup hAc hcA hAab hLc hY'c (hY'c.trans hCL)
  have hZb : Z ≤ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hZL (hZY'.trans (inf_le_right.trans hCBb))
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hY'3 (h3.trans (Subgroup.card_dvd_of_le hZY'))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A Y' hAY'
  have hBC : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hCBc.trans hCL) (hCBb.trans Subgroup.le_normalizer)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ebar := (A.subgroupOf L).map π with hEbar
  obtain ⟨W, hW3, hWN, hWle⟩ := hsig b hbBE.2 hb1 hbL
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  set U := (Z.subgroupOf L).map π with hU
  have hUC : U ≤ Subgroup.centralizer ({π b'} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hZb (Subgroup.mem_subgroupOf.mp hx)).2)
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
  have hEU : Ebar ≤ Subgroup.normalizer (U : Set (↥L ⧸ θ)) := map_le_normalizer_map π hAZ
  exact le_pPrimeCoreOf_of_signal hbL hW3 hWN hBC hCB hZb (hWle U hUC hU3 hEU)

theorem exists_quaternion_hom_slTwoThree :
    ∃ f : QuaternionGroup 2 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      Function.Injective f := by
  have hdet : ∀ q : QuaternionGroup 2,
      ((CFSG.RankThree.Asc83Table.quatHom q : GL (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    decide +kernel
  let f : QuaternionGroup 2 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    { toFun := fun q => ⟨_, hdet q⟩
      map_one' := by
        apply Subtype.ext
        change ((CFSG.RankThree.Asc83Table.quatHom 1 : GL (Fin 2) (ZMod 3)) :
          Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        change ((CFSG.RankThree.Asc83Table.quatHom (x * y) : GL (Fin 2) (ZMod 3)) :
          Matrix (Fin 2) (Fin 2) (ZMod 3)) =
            ((CFSG.RankThree.Asc83Table.quatHom x : GL (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)) *
            ((CFSG.RankThree.Asc83Table.quatHom y : GL (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3))
        rw [map_mul, Units.val_mul] }
  refine ⟨f, fun x y hxy => CFSG.RankThree.Asc83Table.quatHom_injective (Units.ext ?_)⟩
  exact congrArg Subtype.val hxy

theorem exists_conj_eq_of_autIn {A L : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hcL : c ∉ L)
    (hLc : ∀ l ∈ L, l * c = c * l) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    {y₀ y₁ : G} (hy₀ : y₀ ∈ A ⊓ L) (hy₁ : y₁ ∈ A ⊓ L) (h0 : y₀ ≠ 1) (h1 : y₁ ≠ 1) :
    ∃ w ∈ L, w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧ w * y₀ * w⁻¹ = y₁ := by
  have hYeq : (Subgroup.zpowers c ⊔ (A ⊓ L)) ⊓ L = A ⊓ L :=
    zpowers_sup_inf_eq hc3 hcL inf_le_right (fun y hy => (hLc y hy.2).symm)
  obtain ⟨e₁⟩ := nonempty_autIn_sup_equiv hLc hYeq
  rw [← hAc] at e₁
  obtain ⟨g, hg⟩ : ∃ g : QuaternionGroup 2 →* Sec4.autIn L A, Function.Injective g := by
    rcases hQ with hQ | hQ
    · obtain ⟨e⟩ := hQ
      exact ⟨e.symm.toMonoidHom, e.symm.injective⟩
    · obtain ⟨e⟩ := hQ
      obtain ⟨ι, hι⟩ := exists_quaternion_hom_slTwoThree
      exact ⟨e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι⟩
  set f : QuaternionGroup 2 →* MulAut (A ⊓ L : Subgroup G) :=
    (Sec4.autIn L (A ⊓ L)).subtype.comp (e₁.toMonoidHom.comp g) with hf
  have hfinj : Function.Injective f :=
    Subtype.val_injective.comp (e₁.injective.comp hg)
  have hfL : ∀ q, f q ∈ Sec4.autIn L (A ⊓ L) := fun q => (e₁ (g q)).2
  obtain ⟨q, hq⟩ := exists_quaternion_apply_eq hB h9 hfinj (y₀ := ⟨y₀, hy₀⟩) (y₁ := ⟨y₁, hy₁⟩)
    (fun h => h0 (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
  obtain ⟨w, hwN, hwL, hw⟩ := Sec4.mem_autIn_iff.mp (hfL q)
  refine ⟨w, hwL, hwN, ?_⟩
  have := congrArg Subtype.val hq
  rw [← hw, Sec4.normalizerMonoidHom_apply_coe] at this
  exact this

theorem center_eq_bot_of_isLThreePi {X : Type} [Group X] (hX : IsLThreePi X)
    (hXp : Group.IsPerfect X) [Nontrivial X] : Subgroup.center X = ⊥ := by
  obtain ⟨p, e, hp, he, hcase⟩ := hX
  rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq).2
  · by_cases hq2 : 2 < p ^ e
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq hq2).2
    · exfalso
      have h2 : p ^ e = 2 := by
        have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
        omega
      obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
      have := isSolvable_projSU_two
      have : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      exact Group.IsPerfect.not_isSolvable X inferInstance

theorem step142LThreePi_of (h131 : Item131) (hspor : SporadicModels131)
    (hsig : KS142SignalLThreePi) (hPGL : Step142LThreePiPGL) : Step142LThreePi := by
  intro G _ _ A c L h hL3 hLB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL' : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases cases131 h131 hspor slTwoCenter hD with
      ⟨hcL, h9, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGLA, hstar, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    ·
      have hA : Late.IsE27 A := h.isE27'
      have hcA := hD.mem_A
      have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
      have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl))
      have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
        have hcAL : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
        have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
        have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
          hD.commute (hcAL hx) hy.1
        have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
          rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
            hD.orderOf_eq hcL]
          exact fun x hx => ⟨hx.2.2, hx.1⟩
        have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
        rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm
      have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
        ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
          fun x hx => hD.isElemAbelian.2 x hx.1⟩
      set θ := aschbacherSolvableCore 3 ↥L with hθ
      set π := QuotientGroup.mk' θ with hπ
      set Ebar := (A.subgroupOf L).map π with hEbar
      have hE9 : Nat.card Ebar = 9 := by rw [hEbar, card_map_mk_subgroupOf hD.isElemAbelian, h9]
      have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar :=
        CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
          (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L
            hD.isElemAbelian)
      have hpt : ∀ z ∈ Ebar, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
        rintro z ⟨y', hy', rfl⟩ hz1
        refine ⟨y', ⟨Subgroup.mem_subgroupOf.mp hy', y'.2⟩, fun hy1 => hz1 ?_, y'.2, rfl⟩
        have : y' = 1 := Subtype.ext hy1
        rw [this, map_one]
      have htrans : ∀ y₀ ∈ Ebar, y₀ ≠ 1 → ∀ y₁ ∈ Ebar, y₁ ≠ 1 →
          ∃ w ∈ Subgroup.normalizer (Ebar : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
        intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
        obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
        obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
        obtain ⟨w, hwL, hwN, hw⟩ :=
          exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9 hQ hy₀ hy₁ hy₀1 hy₁1
        refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
        · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
              (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
            rw [Subgroup.mem_normalizer_iff]
            intro x
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
          have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := by
            rw [Subgroup.inf_subgroupOf_right]
          rw [hEq] at hwN'
          exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
        · rw [← map_mul, ← map_inv, ← map_mul]
          congr 1
          exact Subtype.ext hw
      refine inspect142At_of_signalAt h hcL h9 hAc fun b hb hb1 hbL => ?_
      refine hsig _ hL3 Ebar hEe hE9 htrans _ ⟨⟨b, hbL⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩
        ?_
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hb1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
        (Subtype.ext (by simpa using hD.isElemAbelian.2 b hb.1))))
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  ·
    obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
    rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  ·
    exact hPGL G A c L h hPGLA hstar hx hLB
  · exact absurd hcL hcL'

end CFSG.RankThree.PartTwo.Sec14
