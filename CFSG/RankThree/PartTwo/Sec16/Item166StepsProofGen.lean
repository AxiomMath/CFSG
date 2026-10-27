module

public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KSzGen166 : Prop :=
  ∀ (T : Type) [Group T] (n : ℕ), CFSG.Blueprint.SuzukiModel T 2 n → ∀ α : MulAut T, α ^ 3 = 1 →
    ∀ S : Sylow 2 T, fixedSubgroupOf α ⊔ (S : Subgroup T) = ⊤

@[expose] def DeltaSz166 {G : Type} [Group G] [Finite G] (A : Subgroup G) : Prop :=
  ∀ X ∈ scriptY A, X = delta A (lB A) X → ∀ K ∈ thetaComponentsIn X,
    (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
      CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K → K = delta A (lB A) K

@[expose] def Step166DeltaSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → DeltaSz166 A

@[expose] def Step166DeltaSzHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        DeltaSz166 A

namespace Steps166

section Gen

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem not_three_dvd_card_of_suzukiModel {K : Subgroup G} {n : ℕ}
    (hn : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) :
    ¬ 3 ∣ Nat.card K := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥K) :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  have hq3 := KFacts.KP7.three_not_dvd_card hn
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥K)]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · exact hq3 h
  · exact hθ3 h

theorem gen166_of (h : Sec17Std G A c L Y₀)
    (h146 : Item146 A (lB A)) (hΔ : DeltaSz166 A) (hgen : KSzGen166) : Gen166 A c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro X hX hXΔ K hK hSz hθ
  obtain ⟨n, hn⟩ := hSz
  have hKΔ := hΔ X hX hXΔ K hK ⟨n, hn⟩ hθ
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKΔ]
    exact le_normalizer_sSup fun _ hQ => hQ.1.1.2.2
  have hA : IsE27 A := isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := HeadProof.pow_three_of_std h hcA
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, HeadProof.pow_three_of_std h x.2, Subgroup.coe_one])⟩
  have h3K := not_three_dvd_card_of_suzukiModel hn
  have hKinv : K ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr h3K, hAK⟩
  have hKQ : K ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hKinv
    rwa [← hKΔ] at this
  obtain ⟨U, hUsyl, -, hAU⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 h3K hAK (bot_le : (⊥ : Subgroup G) ≤ K)
    IsPGroup.of_bot (fun a _ => Subgroup.mem_normalizer_iff.mpr fun x => by
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro hx
        calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
          _ = 1 := by rw [hx]; group)
  have hUK : U ≤ K := hUsyl.1
  have hU2 : IsPGroup 2 U := hUsyl.2.1
  have hUmem : U ∈ scriptQPi A (lB A) K (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hKQ hUK hAU, hUK⟩, (isPiSubgroup_piOf_iff Nat.prime_two U).mpr hU2⟩
  have hUstar : U ∈ scriptQPiStar A (lB A) K (piOf 2) := by
    refine ⟨hUmem, fun P hP hUP => ?_⟩
    have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hP
    exact (hUsyl.2.2 P hP.1.2 hP2 hUP).le
  refine ⟨U, hUstar, le_antisymm ?_ (sup_le inf_le_right hUK)⟩
  set θ := aschbacherSolvableCore 3 ↥K with hθdef
  have hθ2 : IsPGroup 2 θ := hθ ▸ CFSG.pCore_isPGroup
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  let α : ↥(Subgroup.zpowers c) →* MulAut ↥K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hcN))
  have hα_apply : ∀ (a : Subgroup.zpowers c) (x : ↥K),
      ((α a x : ↥K) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => Subgroup.normalizerMonoidHom_apply_apply_coe K _ x
  have hNα : ∀ a : Subgroup.zpowers c, ∀ x ∈ θ, α a x ∈ θ := fun a x hx => by
    have h := Subgroup.characteristic_iff_map_eq.mp (inferInstance : θ.Characteristic) (α a)
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hZ3 : IsPGroup 3 (Subgroup.zpowers c) := fun a => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hZ3 α θ hNα hθ3
  set αT := CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α θ hNα
    ⟨c, Subgroup.mem_zpowers c⟩ with hαT
  have hαT3 : αT ^ 3 = 1 := by
    rw [hαT, ← map_pow]
    have : (⟨c, Subgroup.mem_zpowers c⟩ : Subgroup.zpowers c) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hc3, Subgroup.coe_one])
    rw [this, map_one]
  set UK := U.subgroupOf K with hUKdef
  have hUKmap : UK.map K.subtype = U := by
    rw [hUKdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUK]
  have hUK2 : IsPGroup 2 UK := hU2.comap_of_injective K.subtype K.subtype_injective
  have hUmaxK : ∀ P : Subgroup ↥K, IsPGroup 2 P → UK ≤ P → P ≤ UK := by
    intro P hP hUP
    have hPmap : P.map K.subtype ≤ K := Subgroup.map_subtype_le P
    have hP2 : IsPGroup 2 (P.map K.subtype) := hP.map K.subtype
    have hUP' : U ≤ P.map K.subtype := hUKmap ▸ Subgroup.map_mono hUP
    have heq := hUsyl.2.2 _ hPmap hP2 hUP'
    intro x hx
    have : (x : G) ∈ U := heq ▸ ⟨x, hx, rfl⟩
    exact this
  have hθUK : θ ≤ UK := by
    have h2 : IsPGroup 2 ↥(θ ⊔ UK : Subgroup ↥K) := by
      have : θ.Normal := inferInstance
      exact hθ2.to_sup_of_normal_left hUK2
    exact le_sup_left.trans (hUmaxK _ h2 le_sup_right)
  set Ubar := UK.map (QuotientGroup.mk' θ) with hUbar
  have hUbar2 : IsPGroup 2 Ubar := hUK2.map _
  have hUbarmax : ∀ {P : Subgroup (↥K ⧸ θ)}, IsPGroup 2 P → Ubar ≤ P → P = Ubar := by
    intro P hP hle
    have hker : IsPGroup 2 (QuotientGroup.mk' θ).ker := by
      rw [QuotientGroup.ker_mk']
      exact hθ2
    have hP' : IsPGroup 2 (P.comap (QuotientGroup.mk' θ)) := hP.comap_of_ker_isPGroup _ hker
    have hUP' : UK ≤ P.comap (QuotientGroup.mk' θ) := Subgroup.map_le_iff_le_comap.mp hle
    have h1 := hUmaxK _ hP' hUP'
    refine le_antisymm ?_ hle
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
    exact ⟨x, h1 hq, rfl⟩
  let S : Sylow 2 (↥K ⧸ θ) := ⟨Ubar, hUbar2, fun hP hle => hUbarmax hP hle⟩
  have hgenK := hgen (↥K ⧸ θ) n hn αT hαT3 S
  set CK := (Subgroup.centralizer ({c} : Set G)).subgroupOf K with hCK
  have hfixle : fixedSubgroupOf αT ≤ CK.map (QuotientGroup.mk' θ) := by
    intro q hq
    have hq' : αT q = q := hq
    have hqall : ∀ a : Subgroup.zpowers c,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α θ hNα a q = q := by
      rintro ⟨a, ha⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hk : (⟨c ^ k, ha⟩ : Subgroup.zpowers c) = ⟨c, Subgroup.mem_zpowers c⟩ ^ k :=
        Subtype.ext (by rw [Subgroup.coe_zpow])
      rw [hk, map_zpow, ← hαT]
      have hst : αT ∈ MulAction.stabilizer (MulAut (↥K ⧸ θ)) q := hq'
      exact (MulAction.stabilizer (MulAut (↥K ⧸ θ)) q).zpow_mem hst k
    have hmem : q ∈ {q : ↥K ⧸ θ | ∀ a : Subgroup.zpowers c,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α θ hNα a q = q} := hqall
    rw [hlift] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    refine ⟨x, ?_, rfl⟩
    have h2 : ((α ⟨c, Subgroup.mem_zpowers c⟩ x : ↥K) : G) = x :=
      congrArg Subtype.val (hx ⟨c, Subgroup.mem_zpowers c⟩)
    rw [hα_apply] at h2
    rw [SetLike.mem_coe, hCK, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * c = (c * x * c⁻¹) * c := by rw [h2]
      _ = c * x := by group
  have htop : (⊤ : Subgroup (↥K ⧸ θ)) ≤ (CK ⊔ UK).map (QuotientGroup.mk' θ) := by
    rw [← hgenK, Subgroup.map_sup]
    exact sup_le_sup_right hfixle _
  have hKtop : ∀ x : ↥K, x ∈ CK ⊔ UK := by
    intro x
    have hx : QuotientGroup.mk' θ x ∈ (CK ⊔ UK).map (QuotientGroup.mk' θ) :=
      htop (Subgroup.mem_top _)
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx
    exact (sup_le le_rfl (hθUK.trans le_sup_right)) hx
  intro x hx
  have hmem := Subgroup.mem_map_of_mem K.subtype (hKtop ⟨x, hx⟩)
  rw [Subgroup.map_sup] at hmem
  have hle1 : CK.map K.subtype ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨centralizer_singleton_le_normalizer_zpowers c hy, y.2⟩
  have hle : CK.map K.subtype ⊔ UK.map K.subtype ≤
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ K) ⊔ U :=
    sup_le_sup hle1 hUKmap.le
  exact hle hmem

end Gen

end Steps166

theorem step166Gen_of (h146 : Item146S14) (hΔ : Step166DeltaSz)
    (hgen : KSzGen166) : Step166Gen :=
  fun G _ _ A c L Y₀ h => Steps166.gen166_of h (h146 G A c L h.toSec14Std) (hΔ G A c L Y₀ h) hgen

theorem step166GenHJ_of (h146 : Item146S14)
    (hΔ : Step166DeltaSzHJ) (hgen : KSzGen166) : Step166GenHJ :=
  fun G _ _ A c L Y₀ h hJ =>
    Steps166.gen166_of h (h146 G A c L h.toSec14Std) (hΔ G A c L Y₀ h hJ) hgen

end CFSG.RankThree.PartTwo.Sec16
