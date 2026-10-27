module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_6

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe u v

noncomputable def theorem_6_8_uliftRepresentation
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) :
    Representation ℂ X (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

theorem theorem_6_8_uliftRepresentation_character
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) (g : X) :
    (theorem_6_8_uliftRepresentation ρ).character g = ρ.character g := by
  dsimp [theorem_6_8_uliftRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

public theorem theorem_6_8_isCharacter_of_irreducible
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsCharacter χ := by
  rcases hχ with ⟨n, ρ, _hρirr, hχeq⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    theorem_6_8_uliftRepresentation ρ, ?_⟩
  rw [hχeq]
  ext g
  exact (theorem_6_8_uliftRepresentation_character ρ g).symm

theorem theorem_6_8_left_normal_of_semidirect_top
    {L : Type u} [Group L]
    {H W1 : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1) :
    H.Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rcases hsemi.mul_surjective g trivial with ⟨h, hh, w, hw, hg⟩
  rw [hg]
  have hwh : Section2.conjBy w n ∈ H := hsemi.right_normalizes_left w hw n hn
  have hconj : h * (w * n * w⁻¹) * h⁻¹ ∈ H := by
    exact H.mul_mem (H.mul_mem hh hwh) (H.inv_mem hh)
  simpa [Section2.conjBy, mul_assoc] using hconj

public theorem theorem_6_8_nilpotentQuotient_bot
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L)
    (hHnorm : H.Normal)
    (hnil : Group.IsNilpotent H) :
    nilpotentQuotient (⊥ : Subgroup L) H := by
  refine ⟨bot_le, ?_, inferInstance, hHnorm, ?_⟩
  · infer_instance
  · infer_instance

theorem theorem_6_8_subgroupOf_commutator_eq
    {L : Type u} [Group L]
    (H : Subgroup L) :
    (⁅H, H⁆.subgroupOf H) = (commutator H) := by
  ext x
  constructor
  · intro hx
    have hxmap : (x : L) ∈ (commutator H).map H.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hx
    rcases hxmap with ⟨y, hycomm, hyx⟩
    have hy_eq : y = x := Subtype.ext hyx
    simpa [hy_eq] using hycomm
  · intro hx
    have hxmap : (x : L) ∈ (commutator H).map H.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at hxmap

theorem theorem_6_8_representationCharacter_mul_of_fin_one
    {G : Type u} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g h : G) :
    ρ.character (g * h) = ρ.character g * ρ.character h := by
  have hdim : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  obtain ⟨d, hd, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ h)
  have hρgh : ρ (g * h) = (c * d) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
    rw [map_mul, hc, hd]
    ext v i
    simp [mul_smul, mul_left_comm]
  have hρg : ρ.character g = c := by
    rw [Representation.character, hc]
    simp [hdim]
  have hρh : ρ.character h = d := by
    rw [Representation.character, hd]
    simp [hdim]
  rw [Representation.character, hρgh, hρg, hρh]
  simp [hdim]

theorem theorem_6_8_representationCharacter_ne_zero_of_fin_one
    {G : Type u} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g : G) :
    ρ.character g ≠ 0 := by
  have hmul := theorem_6_8_representationCharacter_mul_of_fin_one ρ g g⁻¹
  have hone : ρ.character (g * g⁻¹) = 1 := by simp [Representation.character]
  intro hzero
  rw [hone, hzero] at hmul
  simp at hmul

noncomputable def theorem_6_8_linearCharacterOfFinOneRepresentation
    {G : Type u} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) : G →* ℂˣ where
  toFun g :=
    Units.mk0 (ρ.character g)
      (theorem_6_8_representationCharacter_ne_zero_of_fin_one ρ g)
  map_one' := by
    apply Units.ext
    simp [Representation.character]
  map_mul' g h := by
    apply Units.ext
    simp [theorem_6_8_representationCharacter_mul_of_fin_one ρ g h]

public theorem theorem_6_8_subgroupInKernel_commutator_of_irreducible_degree_one
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθdeg : Section1.degree θ = 1) :
    Section1.subgroupInKernel' θ (commutator G) := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, Section1.degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : G →* ℂˣ := theorem_6_8_linearCharacterOfFinOneRepresentation ρ
  intro a
  have hlam : lam (a : G) = 1 :=
    Abelianization.commutator_subset_ker lam a.2
  have hchar : ρ.character (a : G) = 1 := by
    have hcoe := congrArg (fun z : ℂˣ => (z : ℂ)) hlam
    simpa [lam, theorem_6_8_linearCharacterOfFinOneRepresentation] using hcoe
  simpa [hθeq, Section1.degree_representation_character ρ] using hchar

theorem theorem_6_8_not_le_commutator_of_nontrivial_nilpotent
    {L : Type u} [Group L]
    {H : Subgroup L}
    (hHne : H ≠ ⊥)
    (hnil : Group.IsNilpotent H) :
    ¬ H ≤ ⁅H,H⁆ := by
  intro hle
  have htop_ne : (⊤ : Subgroup H) ≠ ⊥ := by
    intro htop_bot
    apply hHne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxH
    have hx_sub : (⟨x, hxH⟩ : H) ∈ (⊥ : Subgroup H) := by
      simp [← htop_bot]
    have hx_eq : (⟨x, hxH⟩ : H) = 1 := by
      simpa using hx_sub
    exact congrArg Subtype.val hx_eq
  have hcomm_lt : commutator H < (⊤ : Subgroup H) := by
    have : Group.IsNilpotent H := hnil
    simpa [show commutator H =
        ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ from rfl] using
      (nilpotent_commutator_lt_self_of_normal (⊤ : Subgroup H) htop_ne)
  have hcomm_eq_top : commutator H = (⊤ : Subgroup H) := by
    rw [← theorem_6_8_subgroupOf_commutator_eq H]
    apply le_antisymm le_top
    intro x _hx
    exact hle x.property
  exact hcomm_lt.ne hcomm_eq_top

public theorem theorem_6_8_commutatorQuotient_bot_commutator
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L)
    (hHnorm : H.Normal) :
    commutatorQuotientHypothesis (⊥ : Subgroup L) ⁅H, H⁆ H := by
  have : H.Normal := hHnorm
  have hcomm_le_H : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  refine ⟨bot_le, hcomm_le_H, bot_le, ?_, inferInstance, ?_, hHnorm, ?_⟩
  · infer_instance
  · infer_instance
  · let q : H →* H ⧸ (⊥ : Subgroup L).subgroupOf H :=
      QuotientGroup.mk' ((⊥ : Subgroup L).subgroupOf H)
    have htop_map : (⊤ : Subgroup H).map q =
        (⊤ : Subgroup (H ⧸ (⊥ : Subgroup L).subgroupOf H)) := by
      exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
    calc
      (⁅H, H⁆.subgroupOf H).map q = (commutator H).map q := by
        rw [theorem_6_8_subgroupOf_commutator_eq H]
      _ = commutator (H ⧸ (⊥ : Subgroup L).subgroupOf H) := by
        rw [show commutator H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ from rfl]
        rw [Subgroup.map_commutator]
        rw [htop_map]
        rfl

theorem theorem_6_8_familyData_of_Z
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hHnorm : H.Normal)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hZH : Z ≤ H) :
    theorem_6_8_familyData H Z S
      (inducedKernelFamilyOf H Z S)
      (S \ inducedKernelFamilyOf H Z S)
      (inducedKernelFamilyOf H ⁅H, H⁆ S) := by
  have : H.Normal := hHnorm
  have hcomm_le_H : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  exact ⟨hZH,
    inducedKernelFamilyOf_isFamily hSbot hZH,
    rfl,
    inducedKernelFamilyOf_isFamily hSbot hcomm_le_H⟩

theorem theorem_6_8_caseAData_bot
    {L : Type u} [Group L]
    (H : Subgroup L) :
    theorem_6_8_caseAData H (⊥ : Subgroup L) (centerIn H ⊓ ⁅H, H⁆) := by
  exact ⟨by simp, rfl⟩

theorem theorem_6_8_caseAData_of_center_inf_bot
    {L : Type u} [Group L]
    {H W2 : Subgroup L}
    (hA : centerIn H ⊓ W2 = ⊥) :
    theorem_6_8_caseAData H W2 (centerIn H ⊓ ⁅H, H⁆) := by
  exact ⟨hA, rfl⟩

theorem theorem_6_8_caseA_Z_inf_W2_eq_bot
    {L : Type u} [Group L]
    {H W2 Z : Subgroup L}
    (hA : theorem_6_8_caseAData H W2 Z) :
    Z ⊓ W2 = ⊥ := by
  rcases hA with ⟨hcenterW2, hZeq⟩
  subst Z
  apply le_antisymm
  · intro x hx
    have hxcenterW2 : x ∈ centerIn H ⊓ W2 := ⟨hx.1.1, hx.2⟩
    simpa [hcenterW2] using hxcenterW2
  · exact bot_le

theorem theorem_6_8_natCard_map_mk'_eq_of_inf_eq_bot
    {L : Type u} [Group L] [Finite L]
    (K Z : Subgroup L) [Z.Normal]
    (hZK : Z ⊓ K = ⊥) :
    Nat.card (K.map (QuotientGroup.mk' Z)) = Nat.card K := by
  rw [natCard_map_mk'_eq K Z]
  have hsubBot : Z.subgroupOf K = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxZ : (x : L) ∈ Z := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxInf : (x : L) ∈ Z ⊓ K := ⟨hxZ, x.property⟩
      have hxBot : (x : L) ∈ (⊥ : Subgroup L) := by
        simpa [hZK] using hxInf
      have hxOne : (x : L) = 1 := by
        simpa using hxBot
      exact Subtype.ext hxOne
    · intro hx
      have hxOne : x = 1 := by
        simpa using hx
      simp [hxOne]
  rw [hsubBot]
  exact Nat.card_congr (QuotientGroup.quotientBot (G := K)).toEquiv

theorem theorem_6_8_caseA_card_W2_map_mk'_eq
    {L : Type u} [Group L] [Finite L]
    {H W2 Z : Subgroup L} [Z.Normal]
    (hA : theorem_6_8_caseAData H W2 Z) :
    Nat.card (W2.map (QuotientGroup.mk' Z)) = Nat.card W2 := by
  exact theorem_6_8_natCard_map_mk'_eq_of_inf_eq_bot W2 Z
    (theorem_6_8_caseA_Z_inf_W2_eq_bot hA)

public theorem theorem_6_8_internalSemidirectProduct_top_of_normal_isComplement'
    {L : Type u} [Group L]
    {H K : Subgroup L} [H.Normal]
    (hcomp : H.IsComplement' K) :
    Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K := by
  refine ⟨by intro x _; trivial, by intro x _; trivial, ?_, ?_, ?_⟩
  · intro k _ h hh
    simpa [Section2.conjBy] using
      (inferInstance : H.Normal).conj_mem h hh k
  · apply le_antisymm
    · intro x hx
      exact (Subgroup.disjoint_def.mp hcomp.disjoint) hx.1 hx.2
    · exact bot_le
  · intro c _hc
    rcases hcomp.2 c with ⟨⟨⟨h, hhH⟩, ⟨k, hkK⟩⟩, hck⟩
    refine ⟨h, hhH, k, hkK, ?_⟩
    exact hck.symm

theorem theorem_6_8_internalDirectProduct_map_mk'_of_inf_eq_bot
    {L : Type u} [Group L]
    (W W1 W2 Z : Subgroup L) [Z.Normal]
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    (hZW : Z ⊓ W = ⊥) :
    let q : L →* L ⧸ Z := QuotientGroup.mk' Z
    Section2.IsInternalDirectProduct (W.map q) (W1.map q) (W2.map q) := by
  classical
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  change Section2.IsInternalDirectProduct (W.map q) (W1.map q) (W2.map q)
  refine ⟨Subgroup.map_mono hW.left_le, Subgroup.map_mono hW.right_le, ?_, ?_, ?_⟩
  · intro a ha b hb
    rcases ha with ⟨a0, ha0, hqa⟩
    rcases hb with ⟨b0, hb0, hqb⟩
    calc
      a * b = q a0 * q b0 := by rw [← hqa, ← hqb]
      _ = q (a0 * b0) := by simp [q]
      _ = q (b0 * a0) := by rw [hW.commute a0 ha0 b0 hb0]
      _ = q b0 * q a0 := by simp [q]
      _ = b * a := by rw [hqa, hqb]
  · apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨a, haW1, hax⟩
      rcases hx.2 with ⟨b, hbW2, hbx⟩
      have hbaZ : b⁻¹ * a ∈ Z := by
        exact QuotientGroup.eq.mp (hbx.trans hax.symm)
      have hbaW : b⁻¹ * a ∈ W := by
        exact W.mul_mem (W.inv_mem (hW.right_le hbW2)) (hW.left_le haW1)
      have hbaBot : b⁻¹ * a ∈ (⊥ : Subgroup L) := by
        have hbaInf : b⁻¹ * a ∈ Z ⊓ W := ⟨hbaZ, hbaW⟩
        simpa [hZW] using hbaInf
      have hba_one : b⁻¹ * a = 1 := by
        simpa using hbaBot
      have hab : a = b := by
        calc
          a = b * (b⁻¹ * a) := by simp
          _ = b := by simp [hba_one]
      have haInf : a ∈ W1 ⊓ W2 := ⟨haW1, by simpa [hab] using hbW2⟩
      have haBot : a ∈ (⊥ : Subgroup L) := by
        simpa [hW.inf_eq_bot] using haInf
      have hqa_one : q a = 1 := by
        have ha_one : a = 1 := by
          simpa using haBot
        simp [q, ha_one]
      have hx_one : x = 1 := by
        calc
          x = q a := hax.symm
          _ = 1 := hqa_one
      simp [hx_one]
    · exact bot_le
  · intro c hc
    rcases hc with ⟨w, hwW, hcw⟩
    rcases hW.mul_surjective w hwW with ⟨a, haW1, b, hbW2, hwab⟩
    refine ⟨q a, ⟨a, haW1, rfl⟩, q b, ⟨b, hbW2, rfl⟩, ?_⟩
    calc
      c = q w := hcw.symm
      _ = q (a * b) := by rw [hwab]
      _ = q a * q b := by simp [q]

theorem theorem_6_8_isHallSubgroup_map_of_surjective
    {G G' : Type u} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set Nat.Primes} {H : Subgroup G}
    (hHall : IsHallSubgroup π H)
    (f : G →* G') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := G') (π := π) (H := H.map f)
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    exact hHall.p_in_pi_of_p_dvd_card q
      (hq_dvd.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.map f).index ∣ H.index :=
      Subgroup.index_map_dvd (H := H) hf
    exact (hHall.p_in_pi_of_p_dvd_index q
      (hq_dvd_idx.trans hidx_dvd)) hq_mem

theorem theorem_6_8_caseBData_of_center
    {L : Type u} [Group L] [Finite L]
    {H W2 Z : Subgroup L}
    (hprime : ∃ p : ℕ, Nat.Prime p ∧ Nat.card W2 = p)
    (hW2center : W2 ≤ centerIn H)
    (hW2comm : W2 ≤ ⁅H, H⁆)
    (hZ : Z = W2) :
    theorem_6_8_caseBData H W2 Z := by
  rcases hprime with ⟨p, hp, hcard⟩
  have hW2ne : W2 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card W2 = 1 := by simp [hbot]
    have hp1 : p = 1 := by omega
    exact hp.ne_one hp1
  exact ⟨hW2ne, hW2center, hW2comm, hZ⟩

theorem theorem_6_8_case_split_of_caseC2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : caseC2Hypothesis L H W1 W2 W T) :
    theorem_6_8_caseAData H W2 (centerIn H ⊓ ⁅H, H⁆) ∨
      theorem_6_8_caseBData H W2 W2 := by
  rcases hcase with ⟨_h46, hprime, hW2comm⟩
  by_cases hA : centerIn H ⊓ W2 = ⊥
  · exact Or.inl (theorem_6_8_caseAData_of_center_inf_bot hA)
  · right
    have hW2center : W2 ≤ centerIn H := by
      let I : Subgroup W2 := (centerIn H ⊓ W2).subgroupOf W2
      have hI_ne : I ≠ ⊥ := by
        intro hIbot
        apply hA
        apply le_antisymm
        · intro x hx
          have hxI : (⟨x, hx.2⟩ : W2) ∈ I := hx
          have hxbot : (⟨x, hx.2⟩ : W2) ∈ (⊥ : Subgroup W2) := by
            simpa [I, hIbot] using hxI
          have hxone : x = 1 := by
            simpa using congrArg Subtype.val
              (show (⟨x, hx.2⟩ : W2) = 1 from by simpa using hxbot)
          simp [hxone]
        · exact bot_le
      rcases hprime with ⟨p, hp, hcard⟩
      have hprimeW2 : Nat.Prime (Nat.card W2) := by
        rw [hcard]
        exact hp
      have : Fact (Nat.Prime (Nat.card W2)) := ⟨hprimeW2⟩
      have hItop : I = ⊤ := by
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card I with hbot | htop
        · exact (hI_ne hbot).elim
        · exact htop
      intro x hxW2
      have hxI : (⟨x, hxW2⟩ : W2) ∈ I := by
        simp [hItop]
      exact hxI.1
    exact theorem_6_8_caseBData_of_center hprime hW2center hW2comm rfl

theorem theorem_6_8_caseA_Z_inf_W_eq_bot
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z) :
    Z ⊓ W = ⊥ := by
  classical
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, _hbranch⟩
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      _hcentW1, _hW1W, _hW2W, hWprod, _hWodd⟩
  have hZ_le_H : Z ≤ H := by
    rcases hA with ⟨_hcenterW2, hZeq⟩
    rw [hZeq]
    exact inf_le_right.trans (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
  apply le_antisymm
  · intro x hx
    rcases hWprod.mul_surjective x hx.2 with ⟨a, haW1, b, hbW2, hxab⟩
    have hxH : x ∈ H := hZ_le_H hx.1
    have hbH : b ∈ H := hW2H hbW2
    have haH : a ∈ H := by
      have hxb : x * b⁻¹ ∈ H := H.mul_mem hxH (H.inv_mem hbH)
      have hxbinv : x * b⁻¹ = a := by
        rw [hxab, mul_assoc, mul_inv_cancel, mul_one]
      simpa [hxbinv] using hxb
    have haInf : a ∈ H ⊓ W1 := ⟨haH, haW1⟩
    have haBot : a ∈ (⊥ : Subgroup L) := by
      simpa [hsemi.inf_eq_bot] using haInf
    have haOne : a = 1 := by
      simpa using haBot
    have hxW2 : x ∈ W2 := by
      have hxb : x = b := by
        simpa [haOne] using hxab
      simpa [hxb] using hbW2
    have hxZW2 : x ∈ Z ⊓ W2 := ⟨hx.1, hxW2⟩
    have hxBot : x ∈ (⊥ : Subgroup L) := by
      simpa [theorem_6_8_caseA_Z_inf_W2_eq_bot hA] using hxZW2
    exact hxBot
  · exact bot_le

theorem theorem_6_8_hypothesis_with_bot_W2_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    theorem_6_8_hypothesis L H W1 (⊥ : Subgroup L) W S T := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, _hcase⟩
  exact ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, Or.inl hfrob⟩

theorem theorem_6_8_hypothesis_6_1_of_hypothesis_5_2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T) :
    hypothesis_6_1_statement H S T := by
  rcases h68 with ⟨hsemi, _hodd, _hHne, hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have hHsolv : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  exact ⟨h52, hHnorm, hHsolv, hSbot⟩

theorem theorem_6_8_hypothesis_5_2_setup_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.hypothesis_5_2_setup_statement S := by
  rcases h68 with ⟨hsemi, _hodd, hHne, hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHsolv : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  have hbotNorm : (⊥ : Subgroup L).Normal := inferInstance
  have hbotlt : (⊥ : Subgroup L) < H := by
    exact lt_of_le_of_ne bot_le (Ne.symm hHne)
  rcases inducedKernelFamily_nonempty_of_solvable_proper
      hHsolv hbotNorm hbotlt hSbot with
    ⟨χ0, hχ0⟩
  refine ⟨⟨χ0, hχ0⟩, ?_⟩
  intro X
  rcases X with ⟨χ, hχ⟩
  rcases (hSbot.2 χ).mp hχ with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  change Section1.IsCharacter χ
  rw [hχeq]
  exact Section1.isCharacter_inducedCF_of_isCharacter H θ
    (theorem_6_8_isCharacter_of_irreducible hθirr)

theorem theorem_6_8_isVirtualCharacter_zsmul
    {X : Type u} [Group X]
    (z : ℤ) {χ : Section1.ClassFunction X}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter ((z : ℂ) • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => z * m i, k, ρ, ?_⟩
  ext x
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

theorem theorem_6_8_isVirtualCharacter_finset_sum
    {X : Type u} [Group X]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction X)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), ?_⟩
      ext x
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) := hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
        refine ih ?_
        intro i hi
        exact hΦ i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

theorem theorem_6_8_isVirtualCharacter_evalCoeff
    {X : Type u} [Group X]
    {ι : Type*} [Fintype ι]
    (μ : ι → Section1.ClassFunction X)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  refine theorem_6_8_isVirtualCharacter_finset_sum (Finset.univ : Finset ι)
    (fun i => ((v i : ℂ) • μ i)) ?_
  intro i _hi
  simpa using theorem_6_8_isVirtualCharacter_zsmul (v i) (hμ i)

theorem theorem_6_8_isClassFunction_evalCoeff
    {X : Type u} [Group X]
    {ι : Type*} [Fintype ι]
    (μ : ι → Section1.ClassFunction X)
    (hμ : ∀ i, Section1.IsClassFunction (μ i))
    (v : Section1.CoeffVector ι) :
    Section1.IsClassFunction (Section1.evalCoeff μ v) := by
  classical
  unfold Section1.evalCoeff
  intro x g
  have hterm :
      ∀ i, (v i : ℂ) * μ i (x * g * x⁻¹) = (v i : ℂ) * μ i g := by
    intro i
    rw [hμ i x g]
  simpa using Finset.sum_congr rfl (fun i _ => hterm i)

public theorem theorem_6_8_subgroupImagePuncturedSet_mem_iff
    {G : Type u} [Group G]
    (L : Subgroup G) (H : Subgroup L) (l : L) :
    ((l : G) ∈ subgroupImagePuncturedSet L H) ↔
      l ∈ H ∧ l ≠ 1 := by
  constructor
  · rintro ⟨h, hhl, hhne⟩
    have hval : (h : L) = l := Subtype.ext hhl
    constructor
    · simp [← hval]
    · intro hlone
      exact hhne (by simp [hval, hlone])
  · rintro ⟨hlH, hlne⟩
    exact ⟨⟨l, hlH⟩, rfl, by simpa using hlne⟩

theorem theorem_6_8_virtualCharacter_of_integerSpan
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (hsrc : Section5.sourceVirtualCharacters S)
    {χ : Section1.ClassFunction L}
    (hχ : Section5.integerSpan S χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨v, rfl⟩
  exact theorem_6_8_isVirtualCharacter_evalCoeff
    (fun X : S => (X : Section1.ClassFunction L))
    (fun X => hsrc (X : Section1.ClassFunction L) X.2) v

public theorem theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H : Subgroup L} [H.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    {χ : Section1.ClassFunction L}
    (hχ : Section5.integerSpanOn S Section5.puncturedSet χ) :
    Section2.CFOn L (subgroupImagePuncturedSet L H) χ := by
  classical
  rcases hχ with ⟨hχspan, hχpunct⟩
  constructor
  · rcases hχspan with ⟨v, rfl⟩
    refine theorem_6_8_isClassFunction_evalCoeff
      (fun X : S => (X : Section1.ClassFunction L)) ?_ v
    intro X
    rcases (hSbot.2 (X : Section1.ClassFunction L)).mp X.2 with
      ⟨θ, _hθirr, _hθker, _hθne, hXeq⟩
    simpa [hXeq] using Section1.inducedCF_isClassFunction H θ
  · intro l hlnot
    by_cases hlone : l = 1
    · exact (Section1.supportedOn_iff.mp hχpunct) l
        (by simp [Section5.puncturedSet, hlone])
    · have hlnotH : ¬ l ∈ H := by
        intro hlH
        exact hlnot ((theorem_6_8_subgroupImagePuncturedSet_mem_iff L H l).2
          ⟨hlH, hlone⟩)
      rcases hχspan with ⟨v, rfl⟩
      rw [Section1.evalCoeff]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero ?_
      intro X _hX
      have hXzero : (X : Section1.ClassFunction L) l = 0 := by
        rcases (hSbot.2 (X : Section1.ClassFunction L)).mp X.2 with
          ⟨θ, _hθirr, _hθker, _hθne, hXeq⟩
        rw [hXeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal H θ hlnotH
      simp [hXzero]

theorem theorem_6_8_hypothesis_5_2_a_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.hypothesis_5_2_a_statement S := by
  rcases h68 with ⟨hsemi, hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  intro X
  constructor
  · exact inducedKernelFamily_conjugate_mem hSbot X.2
  · intro hreal
    rcases (hSbot.2 (X : Section1.ClassFunction L)).mp X.2 with
      ⟨θ, hθirr, _hθker, hθne, hXeq⟩
    rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
    have hθne' : ρ.character ≠ Section1.principalCharacter H := by
      intro hprin
      exact hθne (by rw [hθeq, hprin])
    have horth :=
      Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        H ρ hodd hρirr hθne'
    have horth0 :
        Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
      simpa [Section1.orthogonal, hXeq, hθeq] using horth
    have hself0 :
        Section1.scalarProduct L
          (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) = 0 := by
      simpa [← hreal] using horth0
    have hself :
        Section1.scalarProduct L
          (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) =
            (H.relIndex (Section1.inertiaSubgroup H ρ.character) : ℂ) := by
      simpa [hXeq, hθeq] using
        (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical H ρ hρirr)
    have hrel_ne :
        (H.relIndex (Section1.inertiaSubgroup H ρ.character) : ℂ) ≠ 0 := by
      have hrel_nat_ne :
          H.relIndex (Section1.inertiaSubgroup H ρ.character) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      exact_mod_cast hrel_nat_ne
    exact hrel_ne (by rw [← hself, hself0])

theorem theorem_6_8_sourceVirtualCharacters_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.sourceVirtualCharacters S := by
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  intro χ hχ
  rcases (hSbot.2 χ).mp hχ with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  rw [hχeq]
  exact Section5.isVirtualCharacter_of_isCharacter
    (Section1.isCharacter_inducedCF_of_isCharacter H θ
      (theorem_6_8_isCharacter_of_irreducible hθirr))

theorem theorem_6_8_hypothesis_5_2_b_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.hypothesis_5_2_b_statement S T := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  let A : Set G := subgroupImagePuncturedSet L H
  have hTI_A : Section2.IsTISubsetWithNormalizer A L := by
    simpa [A] using hTI
  have hHyp2 : Section2.Hypothesis2 A L (fun _ : G => ⊥) :=
    (Section2.proposition_2_3 A L hTI_A.1).1 hTI_A
  have hAL : ∀ a ∈ A, a ∈ L := hHyp2.subset_L
  have h26 := Section2.theorem_2_6 A L (fun _ : G => ⊥) hHyp2 hAL
  constructor
  · intro φ ψ hφ hψ
    have hφCF : Section2.CFOn L A φ := by
      simpa [A] using
        theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
          (L := L) (H := H) hSbot hφ
    have hψCF : Section2.CFOn L A ψ := by
      simpa [A] using
        theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
          (L := L) (H := H) hSbot hψ
    have hTφ : T φ = Section1.inducedCF L φ := hT φ hφ
    have hTψ : T ψ = Section1.inducedCF L ψ := hT ψ hψ
    have hφInd :
        Section1.inducedCF L φ =
          Section2.dadeTransform (fun _ : G => ⊥) hAL φ :=
      Section3.inducedCF_eq_dadeTransform_trivial A L hHyp2 hAL φ hφCF
    have hψInd :
        Section1.inducedCF L ψ =
          Section2.dadeTransform (fun _ : G => ⊥) hAL ψ :=
      Section3.inducedCF_eq_dadeTransform_trivial A L hHyp2 hAL ψ hψCF
    rw [hTφ, hTψ, hφInd, hψInd]
    exact h26.1 φ ψ hφCF hψCF
  · intro χ hχ
    have hχCF : Section2.CFOn L A χ := by
      simpa [A] using
        theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
          (L := L) (H := H) hSbot hχ
    have hχVirt : Theory.Character.IsVirtualCharacter χ :=
      theorem_6_8_virtualCharacter_of_integerSpan
        (theorem_6_8_sourceVirtualCharacters_of_hypothesis h68') hχ.1
    have hχVirtOn : Section2.virtualCharacterOn L A χ := ⟨hχVirt, hχCF.2⟩
    have hTχ : T χ = Section1.inducedCF L χ := hT χ hχ
    have hχInd :
        Section1.inducedCF L χ =
          Section2.dadeTransform (fun _ : G => ⊥) hAL χ :=
      Section3.inducedCF_eq_dadeTransform_trivial A L hHyp2 hAL χ hχCF
    constructor
    · rw [hTχ, hχInd]
      exact h26.2 χ hχVirtOn
    · have hχdeg : Section1.degree χ = 0 :=
        (Section5.supportedOn_puncturedSet_iff_degree_eq_zero χ).1 hχ.2
      have hTχdeg : Section1.degree (T χ) = 0 := by
        rw [hTχ, Section1.degree_inducedClassFunction L χ, hχdeg, mul_zero]
      exact (Section5.supportedOn_puncturedSet_iff_degree_eq_zero (T χ)).2 hTχdeg

theorem theorem_6_8_hypothesis_5_2_of_hypothesis_and_irreducible
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hIrr : ∀ X : S,
      Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    Section5.hypothesis_5_2_statement S T := by
  have hsetup : Section5.hypothesis_5_2_setup_statement S :=
    theorem_6_8_hypothesis_5_2_setup_of_hypothesis h68
  exact Section5.theorem_5_3_a hsetup.1
    (theorem_6_8_hypothesis_5_2_a_of_hypothesis h68)
    (theorem_6_8_hypothesis_5_2_b_of_hypothesis h68)
    hIrr

theorem theorem_6_8_not_subgroupInKernel_top_of_ne_principal
    {H : Type u} [Group H] [Finite H]
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H) :
    ¬ Section1.subgroupInKernel' θ (⊤ : Subgroup H) := by
  intro hker
  have horth :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hθirr hθne
  have hspdeg :
      Section1.scalarProduct H θ (Section1.principalCharacter H) =
        Section1.degree θ := by
    unfold Section1.scalarProduct Section1.principalCharacter Section1.degree
    have hsum :
        (∑ g : H, θ g * star (1 : ℂ)) =
          ∑ _g : H, Section1.degree θ := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      have hg := hker ⟨g, by simp⟩
      simpa only [map_one, star_one, mul_one] using hg
    rw [hsum]
    simp [Section1.degree]
  have hdeg0 : Section1.degree θ = 0 := by
    rw [← hspdeg, horth]
  rcases hθirr with ⟨_n, ρ, hρirr, hθeq⟩
  have hself : Section1.scalarProduct H θ θ = 1 := by
    rw [hθeq]
    exact Section1.scalarProduct_representation_char_self ρ hρirr
  have hself0 : Section1.scalarProduct H θ θ = 0 := by
    unfold Section1.scalarProduct Section1.degree at hdeg0
    unfold Section1.scalarProduct
    have hzero : ∀ g : H, θ g = 0 := by
      intro g
      have hg := hker ⟨g, by simp⟩
      simpa [Section1.degree, hdeg0] using hg
    simp [hzero]
  norm_num [hself0] at hself

public theorem theorem_6_8_inducedFromNonkernelFamily_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.inducedFromNonkernelFamily_statement H H S := by
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  intro X hX
  rcases (hSbot.2 X).mp hX with ⟨θ, hθirr, _hθker, hθne, hXeq⟩
  refine ⟨θ, hθirr, ?_, hXeq⟩
  intro hker
  exact theorem_6_8_not_subgroupInKernel_top_of_ne_principal
    hθirr hθne (by
      intro a
      exact hker ⟨(a : H), by simp⟩)

theorem theorem_6_8_hypothesis_5_2_of_caseC2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T) :
    Section5.hypothesis_5_2_statement S T := by
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hsetup : Section5.hypothesis_5_2_setup_statement S :=
    theorem_6_8_hypothesis_5_2_setup_of_hypothesis h68
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := L)
      d.fullHypothesis
  have hpack :=
    Section5.theorem_5_3_b_core
      (K := H)
      (W1 := W1)
      (W2 := W2)
      (W := W)
      (H := H)
      (A := ({h : L | h ∈ H ∧ h ≠ 1}))
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaL)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := T)
      (S := S)
      hCtx
      hsetup.1
      (theorem_6_8_hypothesis_5_2_a_of_hypothesis h68)
      (theorem_6_8_inducedFromNonkernelFamily_of_hypothesis h68)
  rcases hpack with ⟨R, hsetup', h52a, h52b, h52c, h52d, h52e, _hextra⟩
  exact ⟨hsetup', R, h52a, h52b, h52c, h52d, h52e⟩

public theorem theorem_6_8_caseC2_nonirreducible_mem_piColumn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ d : caseC2FullData L H W1 W2 W T,
      letI : Fintype d.I := d.instFintypeI
      letI : Fintype d.J := d.instFintypeJ
      letI : DecidableEq d.I := d.instDecidableEqI
      letI : DecidableEq d.J := d.instDecidableEqJ
      ∃ j : d.J, j ≠ d.j0 ∧
        χ = Section4Scratch.piColumn d.piChar j := by
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm⟩
  refine ⟨d, ?_⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, _h43c, _h43d, h45a, h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  exact Section5.theorem_5_3_b_nonbase_piColumn_pf53
    (K := H) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := d.i0) (j0 := d.j0) (ω := d.omega) (σL := d.sigmaL)
    (piChar := d.piChar) (xChar := d.xChar) (deltaSign := d.deltaSign)
    (S := S)
    hω h43b h45a h45b
    (theorem_6_8_inducedFromNonkernelFamily_of_hypothesis h68)
    ⟨χ, hχS⟩ hχnotirr

theorem theorem_6_8_caseC2_nonbase_piColumn_mem_S
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    ∀ j : d.J, j ≠ d.j0 →
      Section4Scratch.piColumn d.piChar j ∈ S := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  intro j hj
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, h43c, _h43d, h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  let A : Set L := {h : L | h ∈ H ∧ h ≠ 1}
  have h47 : Section4Scratch.theorem_4_7_statement H H A :=
    Section4Scratch.theorem_4_7 H W1 W2 W H A h46
  have hnonker :
      ¬ Section1.subgroupInKernel' (d.xChar j) (H.subgroupOf H) :=
    (Section4Scratch.theorem_4_7_nonbase_column H W1 W2 W H A d.i0 d.j0
      d.omega d.sigmaL d.piChar d.xChar d.deltaSign
      h46 h45a hω h43b h43c h47 j hj).1
  have hne_principal : d.xChar j ≠ Section1.principalCharacter H := by
    intro hprincipal
    apply hnonker
    rw [hprincipal]
    intro a
    simp [Section1.principalCharacter, Section1.degree]
  have hker_bot :
      Section1.subgroupInKernel' (d.xChar j) ((⊥ : Subgroup L).subgroupOf H) := by
    intro a
    have haL : ((a : H) : L) = 1 := by
      simpa using a.2
    have haH : (a : H) = 1 := Subtype.ext haL
    simp [Section1.degree, haH]
  exact (hSbot.2 (Section4Scratch.piColumn d.piChar j)).mpr
    ⟨d.xChar j, h45a.2.1 j, hker_bot, hne_principal, (h45a.2.2 j).symm⟩

theorem theorem_6_8_caseC2_nonbase_piColumn_not_irreducible
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    ∀ j : d.J,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section4Scratch.piColumn d.piChar j) := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  intro j
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  exact Section5.piColumn_not_irreducible_pf53 h46 hω h43b j

theorem theorem_6_8_caseC2_xChar_injective
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    Function.Injective d.xChar := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, _h43c, _h43d, h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  exact Section4Scratch.xChar_injective_pf45
    H d.piChar d.xChar h45a d.i0 d.j0 d.omega d.sigmaL d.deltaSign hω h43b


theorem theorem_6_8_caseC2_piColumn_injective
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    Function.Injective (fun j : d.J => Section4Scratch.piColumn d.piChar j) := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  have hresCol :
      ∀ j : d.J,
        Section1.subgroupRestriction H (Section4Scratch.piColumn d.piChar j) =
          (Fintype.card d.I : ℂ) • d.xChar j := by
    intro j
    ext t
    calc
      Section1.subgroupRestriction H (Section4Scratch.piColumn d.piChar j) t =
          ∑ i : d.I, d.piChar i j t := by
            simp [Section4Scratch.piColumn, Section1.subgroupRestriction]
      _ = ∑ _i : d.I, d.xChar j t := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Section1.subgroupRestriction] using congrFun (h45a.1 i j) t
      _ = (Fintype.card d.I : ℂ) * d.xChar j t := by
            simp [Finset.sum_const]
      _ = ((Fintype.card d.I : ℂ) • d.xChar j) t := by
            simp
  have hcardI_ne : (Fintype.card d.I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨d.i0⟩).ne'
  intro j k hEq
  have hsmul :
      (Fintype.card d.I : ℂ) • d.xChar j =
        (Fintype.card d.I : ℂ) • d.xChar k := by
    calc
      (Fintype.card d.I : ℂ) • d.xChar j =
          Section1.subgroupRestriction H (Section4Scratch.piColumn d.piChar j) :=
        (hresCol j).symm
      _ = Section1.subgroupRestriction H (Section4Scratch.piColumn d.piChar k) := by
        exact congrArg (Section1.subgroupRestriction H) hEq
      _ = (Fintype.card d.I : ℂ) • d.xChar k :=
        hresCol k
  have hxEq : d.xChar j = d.xChar k := by
    ext t
    have ht := congrFun hsmul t
    exact mul_left_cancel₀ hcardI_ne (by simpa using ht)
  exact theorem_6_8_caseC2_xChar_injective d hxEq

theorem theorem_6_8_caseC2_nonirreducible_mem_piColumn_of_fullData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (d : caseC2FullData L H W1 W2 W T)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup χ) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    ∃ j : d.J, j ≠ d.j0 ∧
      χ = Section4Scratch.piColumn d.piChar j := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, _h43c, _h43d, h45a, h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  exact Section5.theorem_5_3_b_nonbase_piColumn_pf53
    (K := H) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := d.i0) (j0 := d.j0) (ω := d.omega) (σL := d.sigmaL)
    (piChar := d.piChar) (xChar := d.xChar) (deltaSign := d.deltaSign)
    (S := S)
    hω h43b h45a h45b
    (theorem_6_8_inducedFromNonkernelFamily_of_hypothesis h68)
    ⟨χ, hχS⟩ hχnotirr

theorem theorem_6_8_caseC2_reducible_subfamily_card_S_eq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    (S.filter fun χ =>
      ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
        Nat.card W2 - 1 := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  let redS : Finset (Section1.ClassFunction L) :=
    S.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ
  let nonbaseJ : Finset d.J := Finset.univ.erase d.j0
  have hpreimage :
      ∀ χ : {χ : Section1.ClassFunction L // χ ∈ redS},
        ∃ j : {j : d.J // j ∈ nonbaseJ},
          (χ : Section1.ClassFunction L) =
            Section4Scratch.piColumn d.piChar (j : d.J) := by
    intro χ
    have hχS : (χ : Section1.ClassFunction L) ∈ S := by
      have hχred :
          (χ : Section1.ClassFunction L) ∈
            S.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
        simp [redS]
      exact (Finset.mem_filter.mp hχred).1
    have hχnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
        (χ : Section1.ClassFunction L) := by
      have hχred :
          (χ : Section1.ClassFunction L) ∈
            S.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
        simp [redS]
      exact (Finset.mem_filter.mp hχred).2
    rcases theorem_6_8_caseC2_nonirreducible_mem_piColumn_of_fullData
        h68 d hχS hχnotirr with ⟨j, hj, hχeq⟩
    refine ⟨⟨j, ?_⟩, hχeq⟩
    simp [nonbaseJ, hj]
  let e :
      {j : d.J // j ∈ nonbaseJ} ≃
        {χ : Section1.ClassFunction L // χ ∈ redS} :=
    { toFun := fun j =>
        ⟨Section4Scratch.piColumn d.piChar (j : d.J), by
          have hj : (j : d.J) ≠ d.j0 := by
            have hmem : (j : d.J) ∈ nonbaseJ := j.2
            change (j : d.J) ∈ Finset.univ.erase d.j0 at hmem
            exact (Finset.mem_erase.mp hmem).1
          have hmem :
              Section4Scratch.piColumn d.piChar (j : d.J) ∈
                S.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
            rw [Finset.mem_filter]
            exact ⟨theorem_6_8_caseC2_nonbase_piColumn_mem_S h68 d (j : d.J) hj,
              theorem_6_8_caseC2_nonbase_piColumn_not_irreducible d (j : d.J)⟩
          simpa [redS] using hmem⟩
      invFun := fun χ => Classical.choose (hpreimage χ)
      left_inv := by
        intro j
        apply Subtype.ext
        have hspec := Classical.choose_spec (hpreimage
          (⟨Section4Scratch.piColumn d.piChar (j : d.J), by
            have hj : (j : d.J) ≠ d.j0 := by
              have hmem : (j : d.J) ∈ nonbaseJ := j.2
              change (j : d.J) ∈ Finset.univ.erase d.j0 at hmem
              exact (Finset.mem_erase.mp hmem).1
            have hmem :
                Section4Scratch.piColumn d.piChar (j : d.J) ∈
                  S.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
              rw [Finset.mem_filter]
              exact ⟨theorem_6_8_caseC2_nonbase_piColumn_mem_S h68 d (j : d.J) hj,
                theorem_6_8_caseC2_nonbase_piColumn_not_irreducible d (j : d.J)⟩
            simpa [redS] using hmem⟩ :
            {χ : Section1.ClassFunction L // χ ∈ redS}))
        exact theorem_6_8_caseC2_piColumn_injective d hspec.symm
      right_inv := by
        intro χ
        apply Subtype.ext
        exact (Classical.choose_spec (hpreimage χ)).symm }
  have hcardEquiv :
      Fintype.card {j : d.J // j ∈ nonbaseJ} =
        Fintype.card {χ : Section1.ClassFunction L // χ ∈ redS} :=
    Fintype.card_congr e
  have hleft :
      Fintype.card {j : d.J // j ∈ nonbaseJ} = nonbaseJ.card :=
    Fintype.card_of_subtype nonbaseJ (fun j => Iff.rfl)
  have hright :
      Fintype.card {χ : Section1.ClassFunction L // χ ∈ redS} = redS.card :=
    Fintype.card_of_subtype redS (fun χ => Iff.rfl)
  have hredCard : redS.card = nonbaseJ.card := by
    omega
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  have hnonbaseCard : nonbaseJ.card = Nat.card W2 - 1 := by
    have hJcard : Fintype.card d.J = Nat.card W2 := by
      exact hω.card_right
    have hcardErase : nonbaseJ.card = Fintype.card d.J - 1 := by
      simp [nonbaseJ]
    rw [hcardErase, hJcard]
  simpa [redS] using hredCard.trans hnonbaseCard

theorem theorem_6_8_reducible_mem_of_reducible_subfamily_card_eq
    {L : Type u} [Group L] [Finite L]
    {S SZ : Finset (Section1.ClassFunction L)}
    (hSZsubS : SZ ⊆ S)
    (hcard :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
      (S.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχred : ¬ Section1.IsIrreducibleCharacterOnGroup χ) :
    χ ∈ SZ := by
  classical
  let red : Section1.ClassFunction L → Prop :=
    fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ
  have hsub :
      SZ.filter red ⊆ S.filter red := by
    intro ψ hψ
    rw [Finset.mem_filter] at hψ ⊢
    exact ⟨hSZsubS hψ.1, hψ.2⟩
  have hEq : SZ.filter red = S.filter red := by
    exact Finset.eq_of_subset_of_card_le hsub (by simp [red, hcard])
  have hχredS : χ ∈ S.filter red := by
    rw [Finset.mem_filter]
    exact ⟨hχS, hχred⟩
  have hχredSZ : χ ∈ SZ.filter red := by
    simpa [hEq] using hχredS
  exact (Finset.mem_filter.mp hχredSZ).1

theorem theorem_6_8_reducible_subfamily_card_lower_of_injective
    {L : Type u} [Group L] [Finite L]
    {SZ : Finset (Section1.ClassFunction L)}
    {ι : Type*} [Fintype ι]
    (f : ι → Section1.ClassFunction L)
    (hmem : ∀ i, f i ∈ SZ)
    (hred : ∀ i, ¬ Section1.IsIrreducibleCharacterOnGroup (f i))
    (hinj : Function.Injective f) :
    Fintype.card ι ≤
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
  classical
  let red : Section1.ClassFunction L → Prop :=
    fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ
  let redSZ : Finset (Section1.ClassFunction L) := SZ.filter red
  let g : ι → {χ : Section1.ClassFunction L // χ ∈ redSZ} :=
    fun i => ⟨f i, by
      rw [Finset.mem_filter]
      exact ⟨hmem i, hred i⟩⟩
  have hginj : Function.Injective g := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard :
      Fintype.card ι ≤ Fintype.card {χ : Section1.ClassFunction L // χ ∈ redSZ} :=
    Fintype.card_le_of_injective g hginj
  have hredCard :
      Fintype.card {χ : Section1.ClassFunction L // χ ∈ redSZ} = redSZ.card :=
    Fintype.card_of_subtype redSZ (fun χ => Iff.rfl)
  simpa [redSZ, red, hredCard] using hcard


theorem theorem_6_8_caseC2_nonbase_piColumn_mem_SZ_of_reducible_card_eq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hcard :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
      (S.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    ∀ j : d.J, j ≠ d.j0 →
      Section4Scratch.piColumn d.piChar j ∈ SZ := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  intro j hj
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  rcases hfamily with ⟨_hZH, hSZ, _hXeq, _hY⟩
  have hSZsubS : SZ ⊆ S := inducedKernelFamily_subset_base hSbot hSZ
  exact theorem_6_8_reducible_mem_of_reducible_subfamily_card_eq
    (S := S) (SZ := SZ) hSZsubS hcard
    (theorem_6_8_caseC2_nonbase_piColumn_mem_S
      (L := L) (H := H) (W1 := W1) (W2 := W2) (W := W)
      (S := S) (T := T)
      ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩ d j hj)
    (theorem_6_8_caseC2_nonbase_piColumn_not_irreducible d j)


theorem theorem_6_8_caseC2_nonirreducible_mem_SZ_piColumn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (d : caseC2FullData L H W1 W2 W T)
    {χ : Section1.ClassFunction L}
    (hχSZ : χ ∈ SZ)
    (hχnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup χ) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    ∃ j : d.J, j ≠ d.j0 ∧
      χ = Section4Scratch.piColumn d.piChar j := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases hfamily with ⟨_hZH, hSZ, _hXeq, _hY⟩
  have hInd : Section5.inducedFromNonkernelFamily_statement H H SZ := by
    intro X hX
    rcases (hSZ.2 X).mp hX with ⟨θ, hθirr, _hθker, hθne, hXeq⟩
    refine ⟨θ, hθirr, ?_, hXeq⟩
    intro hker
    exact theorem_6_8_not_subgroupInKernel_top_of_ne_principal
      hθirr hθne (by
        intro a
        exact hker ⟨(a : H), by simp⟩)
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, _h43c, _h43d, h45a, h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  exact Section5.theorem_5_3_b_nonbase_piColumn_pf53
    (K := H) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := d.i0) (j0 := d.j0) (ω := d.omega) (σL := d.sigmaL)
    (piChar := d.piChar) (xChar := d.xChar) (deltaSign := d.deltaSign)
    (S := SZ)
    hω h43b h45a h45b hInd ⟨χ, hχSZ⟩ hχnotirr

theorem theorem_6_8_caseC2_reducible_subfamily_card_SZ_le
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    (SZ.filter fun χ =>
      ¬ Section1.IsIrreducibleCharacterOnGroup χ).card ≤
        Nat.card W2 - 1 := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  let redSZ : Finset (Section1.ClassFunction L) :=
    SZ.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ
  let nonbaseJ : Finset d.J := Finset.univ.erase d.j0
  have hpreimage :
      ∀ χ : {χ : Section1.ClassFunction L // χ ∈ redSZ},
        ∃ j : {j : d.J // j ∈ nonbaseJ},
          (χ : Section1.ClassFunction L) =
            Section4Scratch.piColumn d.piChar (j : d.J) := by
    intro χ
    have hχSZ : (χ : Section1.ClassFunction L) ∈ SZ := by
      have hχred :
          (χ : Section1.ClassFunction L) ∈
            SZ.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
        simp [redSZ]
      exact (Finset.mem_filter.mp hχred).1
    have hχnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
        (χ : Section1.ClassFunction L) := by
      have hχred :
          (χ : Section1.ClassFunction L) ∈
            SZ.filter (fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ) := by
        simp [redSZ]
      exact (Finset.mem_filter.mp hχred).2
    rcases theorem_6_8_caseC2_nonirreducible_mem_SZ_piColumn
        hfamily d hχSZ hχnotirr with ⟨j, hj, hχeq⟩
    refine ⟨⟨j, ?_⟩, hχeq⟩
    simp [nonbaseJ, hj]
  let f :
      {χ : Section1.ClassFunction L // χ ∈ redSZ} →
        {j : d.J // j ∈ nonbaseJ} :=
    fun χ => Classical.choose (hpreimage χ)
  have hf_inj : Function.Injective f := by
    intro χ ψ hEq
    apply Subtype.ext
    have hχspec := Classical.choose_spec (hpreimage χ)
    have hψspec := Classical.choose_spec (hpreimage ψ)
    have hjEq : ((f χ : {j : d.J // j ∈ nonbaseJ}) : d.J) =
        ((f ψ : {j : d.J // j ∈ nonbaseJ}) : d.J) :=
      congrArg Subtype.val hEq
    calc
      (χ : Section1.ClassFunction L) =
          Section4Scratch.piColumn d.piChar ((f χ : {j : d.J // j ∈ nonbaseJ}) : d.J) :=
        hχspec
      _ = Section4Scratch.piColumn d.piChar
          ((f ψ : {j : d.J // j ∈ nonbaseJ}) : d.J) := by
        rw [hjEq]
      _ = (ψ : Section1.ClassFunction L) := hψspec.symm
  have hcard_le :
      Fintype.card {χ : Section1.ClassFunction L // χ ∈ redSZ} ≤
        Fintype.card {j : d.J // j ∈ nonbaseJ} :=
    Fintype.card_le_of_injective f hf_inj
  have hleft :
      Fintype.card {χ : Section1.ClassFunction L // χ ∈ redSZ} = redSZ.card :=
    Fintype.card_of_subtype redSZ (fun χ => Iff.rfl)
  have hright :
      Fintype.card {j : d.J // j ∈ nonbaseJ} = nonbaseJ.card :=
    Fintype.card_of_subtype nonbaseJ (fun j => Iff.rfl)
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  have hnonbaseCard : nonbaseJ.card = Nat.card W2 - 1 := by
    have hJcard : Fintype.card d.J = Nat.card W2 := hω.card_right
    have hcardErase : nonbaseJ.card = Fintype.card d.J - 1 := by
      simp [nonbaseJ]
    rw [hcardErase, hJcard]
  have hredCardLeNonbase : redSZ.card ≤ nonbaseJ.card := by
    rw [← hleft, ← hright]
    exact hcard_le
  simpa [redSZ, hnonbaseCard] using hredCardLeNonbase

theorem theorem_6_8_caseC2_reducible_subfamily_card_SZ_eq_of_lower_bound
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (d : caseC2FullData L H W1 W2 W T)
    (hlower :
      Nat.card W2 - 1 ≤
        (SZ.filter fun χ =>
          ¬ Section1.IsIrreducibleCharacterOnGroup χ).card) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    (SZ.filter fun χ =>
      ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
        Nat.card W2 - 1 := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hupper :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card ≤
          Nat.card W2 - 1 :=
    theorem_6_8_caseC2_reducible_subfamily_card_SZ_le hfamily d
  exact le_antisymm hupper hlower


theorem theorem_6_8_isComplement_of_semidirect_top
    {L : Type u} [Group L]
    {H R : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H R) :
    H.IsComplement' R := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    have hxInf : x ∈ H ⊓ R := ⟨hxH, hxR⟩
    simpa [hsemi.inf_eq_bot] using hxInf
  · rw [Set.eq_univ_iff_forall]
    intro x
    rcases hsemi.mul_surjective x trivial with ⟨h, hh, r, hr, hx⟩
    exact ⟨h, hh, r, hr, hx.symm⟩

theorem theorem_6_8_card_coprime_kernel_complement_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {H W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement H W1 W2 W) :
    Nat.Coprime (Nat.card H) (Nat.card W1) := by
  rcases h42 with
    ⟨hsemi, hHall, _hcyc1, _hcard1, _hcyc2, _hcard2, _hcent,
      _hW1, _hW2, _hW, _hodd⟩
  rcases hHall with ⟨π, hHall⟩
  have hcomp : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hindex_eq : W1.index = Nat.card H := hcomp.index_eq_card
  simpa [hindex_eq] using
    (IsHallSubgroup.card_coprime_index (π := π) (H := W1) hHall).symm

theorem theorem_6_8_frobeniusQuotient_commutator_of_caseC2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T) :
    frobeniusQuotientWithKernel H ⁅H,H⁆ := by
  classical
  rcases h68 with ⟨hsemi, _hodd, hHne, hnil, _hTI, _hSbot, _hT, _hcase⟩
  rcases hcase with ⟨⟨d⟩, _hprime, hW2comm⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  have h42copy : Section4.hypothesis_4_2_statement H W1 W2 W := h42
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, hW1card_ne, _hcyc2, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hW, _hWodd⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  let H1 : Subgroup L := ⁅H,H⁆
  have hH1_le_H : H1 ≤ H :=
    Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have : H1.Normal := by
    dsimp [H1]
    infer_instance
  have hH_not_le_H1 : ¬ H ≤ H1 := by
    intro hle
    have htop_ne : (⊤ : Subgroup H) ≠ ⊥ := by
      intro htop_bot
      apply hHne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxH
      have hx_sub : (⟨x, hxH⟩ : H) ∈ (⊥ : Subgroup H) := by
        simp [← htop_bot]
      have hx_eq : (⟨x, hxH⟩ : H) = 1 := by
        simpa using hx_sub
      exact congrArg Subtype.val hx_eq
    have hcomm_lt : commutator H < (⊤ : Subgroup H) := by
      have : Group.IsNilpotent H := hnil
      simpa [show commutator H =
          ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ from rfl] using
        (nilpotent_commutator_lt_self_of_normal (⊤ : Subgroup H) htop_ne)
    have hcomm_eq_top : commutator H = (⊤ : Subgroup H) := by
      rw [← theorem_6_8_subgroupOf_commutator_eq H]
      apply le_antisymm le_top
      intro x _hx
      exact hle x.property
    exact hcomm_lt.ne hcomm_eq_top
  have hcomp : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hcopHW1 : Nat.Coprime (Nat.card H) (Nat.card W1) :=
    theorem_6_8_card_coprime_kernel_complement_of_hypothesis_4_2 h42copy
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  have hcompQuot :
      (H.map q).IsComplement' (W1.map q) :=
    isComplement'_map_mk'_of_le_isComplement' H W1 H1 hH1_le_H hcomp
  have hHmap_ne : H.map q ≠ ⊥ := by
    intro hbot
    apply hH_not_le_H1
    intro h hhH
    have hhq_bot : q h ∈ (⊥ : Subgroup (L ⧸ H1)) := by
      rw [← hbot]
      exact ⟨h, hhH, rfl⟩
    have hhq_one : q h = 1 := by
      simpa using hhq_bot
    exact (QuotientGroup.eq_one_iff (N := H1) h).mp hhq_one
  have hW1map_card : Nat.card (W1.map q) = Nat.card W1 :=
    natCard_map_mk'_eq_of_le_isComplement' H W1 H1 hH1_le_H hcomp
  have hW1map_ne : W1.map q ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card (W1.map q) = 1 := by
      simp [hbot]
    exact hW1card_ne (hW1map_card ▸ hcard1)
  refine ⟨by infer_instance, hH1_le_H, hHnorm, W1.map q, hcompQuot,
    hHmap_ne, hW1map_ne, ?_⟩
  intro r hr
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyElem :
      y ∈ elementCentralizerIn (H.map q) (r : L ⧸ H1) := by
    simpa [q, H1, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hy
  rcases r.property with ⟨w, hwW1, hwq⟩
  have hw_sub_ne : (⟨w, hwW1⟩ : W1) ≠ 1 := by
    intro hwone
    apply hr
    apply Subtype.ext
    calc
      (r : L ⧸ H1) = q w := hwq.symm
      _ = 1 := by
        have hwoneL : w = 1 := congrArg Subtype.val hwone
        simp [q, hwoneL]
  let R0 : Subgroup L := Subgroup.zpowers w
  have hR0_le_W1 : R0 ≤ W1 := by
    exact (Subgroup.zpowers_le).2 hwW1
  have hR0normH : R0 ≤ Subgroup.normalizer (H : Set L) := by
    exact hR0_le_W1.trans (Subgroup.le_normalizer_of_normal (H := H))
  have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card W1 := by
    rw [← natCard_subgroupOf_eq R0 W1 hR0_le_W1]
    exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf W1)
  have hcopHR0 : Nat.Coprime (Nat.card H) (Nat.card R0) :=
    Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopHW1
  have hH1inv : ∀ r0 : R0, ∀ x ∈ H1, (r0 : L) * x * (r0 : L)⁻¹ ∈ H1 := by
    intro r0 x hx
    exact (inferInstance : H1.Normal).conj_mem x hx (r0 : L)
  have hcentSubQuot :
      subgroupCentralizerIn (H.map q) (R0.map q) =
        (subgroupCentralizerIn H R0).map q :=
    subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
      H R0 H1 hR0normH hsolvH hcopHR0 hH1inv
  have hySub :
      y ∈ subgroupCentralizerIn (H.map q) (R0.map q) := by
    refine ⟨hyElem.1, ?_⟩
    change y ∈ Subgroup.centralizer
      ((R0.map q : Subgroup (L ⧸ H1)) : Set (L ⧸ H1))
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with ⟨a, haR0, haz⟩
    rcases Subgroup.mem_zpowers_iff.mp haR0 with ⟨n, hn⟩
    have hcomm_r : y * (r : L ⧸ H1) = (r : L ⧸ H1) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
    have hcomm_qw : Commute y (q w) := by
      change y * q w = q w * y
      rw [hwq]
      exact hcomm_r
    have hcomm_qa : Commute y (q a) := by
      rw [← hn]
      simpa [q] using hcomm_qw.zpow_right n
    calc
      z * y = q a * y := by rw [haz]
      _ = y * q a := hcomm_qa.eq.symm
      _ = y * z := by rw [haz]
  have hymap : y ∈ (subgroupCentralizerIn H R0).map q := by
    simpa [hcentSubQuot] using hySub
  rcases hymap with ⟨z, hzcent, hzy⟩
  have hcent_w : elementCentralizerIn H w = W2 := by
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
  have hzElem : z ∈ elementCentralizerIn H w := by
    refine ⟨hzcent.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm :
        w * z = z * w :=
      Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
    exact hcomm.symm
  have hzW2 : z ∈ W2 := by
    simpa [hcent_w] using hzElem
  have hzH1 : z ∈ H1 := hW2comm hzW2
  have hy_eq_one : y = 1 := by
    calc
      y = q z := hzy.symm
      _ = 1 := by
        simpa [q] using (QuotientGroup.eq_one_iff (N := H1) z).2 hzH1
  exact hy_eq_one

public theorem theorem_6_8_frobeniusQuotient_commutator_of_complement
    {L : Type u} [Group L] [Finite L]
    {H R : Subgroup L} [H.Normal]
    (hHne : H ≠ ⊥)
    (hnil : Group.IsNilpotent H)
    (hcomp : H.IsComplement' R)
    (hRne : R ≠ ⊥)
    (hcentElem : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥) :
    frobeniusQuotientWithKernel H ⁅H,H⁆ := by
  classical
  have hHnorm : H.Normal := inferInstance
  have hfrobHR : IsFrobeniusGroupWithKernelComplement H R := by
    exact (lemma_3_1 (K := H) (R := R) hHne hRne hHnorm hcomp).2 hcentElem
  let H1 : Subgroup L := ⁅H,H⁆
  have hH1_le_H : H1 ≤ H :=
    Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have : H1.Normal := by
    dsimp [H1]
    infer_instance
  have hH_not_le_H1 : ¬ H ≤ H1 := by
    simpa [H1] using theorem_6_8_not_le_commutator_of_nontrivial_nilpotent
      hHne hnil
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  have hfrobQuot :
      IsFrobeniusGroupWithKernelComplement (H.map q) (R.map q) :=
    lemma_3_2_b (K := H) (R := R) (N := H1) hfrobHR hsolvH hH_not_le_H1
  refine ⟨by infer_instance, hH1_le_H, hHnorm, R.map q, ?_, ?_, ?_, ?_⟩
  · simpa [q, H1] using hfrobQuot.isComplement'
  · simpa [q, H1] using hfrobQuot.kernel_ne_bot
  · simpa [q, H1] using hfrobQuot.complement_ne_bot
  · have hcentQuotElem :
        ∀ r : R.map q, r ≠ 1 →
          elementCentralizerIn (H.map q) (r : L ⧸ H1) = ⊥ :=
      (lemma_3_1 (G := L ⧸ H1) (K := H.map q) (R := R.map q)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [q, H1, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentQuotElem r hr

public theorem theorem_6_8_frobeniusQuotient_commutator_of_frobenius
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    (hHne : H ≠ ⊥)
    (hnil : Group.IsNilpotent H)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    frobeniusQuotientWithKernel H ⁅H,H⁆ := by
  classical
  rcases hfrob with
    ⟨_hHtop, hHtopNorm, Rtop, hcompTop, _hHtop_ne, hRtop_ne, hcentTop⟩
  have hHnorm : H.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    have hn_top :
        (⟨n, trivial⟩ : (⊤ : Subgroup L)) ∈
          H.subgroupOf (⊤ : Subgroup L) := hn
    have hconj_top :=
      hHtopNorm.conj_mem (⟨n, trivial⟩ : (⊤ : Subgroup L)) hn_top
        (⟨g, trivial⟩ : (⊤ : Subgroup L))
    exact hconj_top
  have : H.Normal := hHnorm
  let R : Subgroup L := Rtop.map (⊤ : Subgroup L).subtype
  have hcomp : H.IsComplement' R := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxH hxR
      rcases hxR with ⟨rtop, hrtop, hrtopx⟩
      have hx_top :
          (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
            (⊥ : Subgroup (⊤ : Subgroup L)) := by
        have hxHtop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
              H.subgroupOf (⊤ : Subgroup L) := hxH
        have hxRtop : (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈ Rtop := by
          have hsubeq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = rtop := by
            apply Subtype.ext
            change x = (rtop : L)
            exact hrtopx.symm
          rw [hsubeq]
          exact hrtop
        exact (Subgroup.disjoint_def.mp hcompTop.disjoint) hxHtop hxRtop
      have hx_top_eq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 := by
        simpa using hx_top
      exact congrArg Subtype.val hx_top_eq
    · rw [Set.eq_univ_iff_forall]
      intro x
      rcases hcompTop.2 (⟨x, trivial⟩ : (⊤ : Subgroup L)) with ⟨p, hp⟩
      rcases p with ⟨h, r⟩
      refine ⟨((h : (⊤ : Subgroup L)) : L), h.property,
        ((r : (⊤ : Subgroup L)) : L), ?_, ?_⟩
      · exact ⟨(r : (⊤ : Subgroup L)), r.property, rfl⟩
      · exact congrArg Subtype.val hp
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRtop_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    have hrmap : (r : L) ∈ R := ⟨r, hr, rfl⟩
    have hrbot : (r : L) ∈ (⊥ : Subgroup L) := by
      simpa [R, hRbot] using hrmap
    apply Subtype.ext
    simpa using hrbot
  have hcentElem : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥ := by
    intro r hrne
    rcases r.property with ⟨rtop, hrtop, hrtopr⟩
    have hrtopr_val : (rtop : L) = (r : L) := hrtopr
    have hrtop_sub_ne : (⟨rtop, hrtop⟩ : Rtop) ≠ 1 := by
      intro hrtop_one
      apply hrne
      apply Subtype.ext
      calc
        (r : L) = (rtop : L) := hrtopr_val.symm
        _ = 1 := by simpa using congrArg Subtype.val hrtop_one
    have hcent_top := hcentTop ⟨rtop, hrtop⟩ hrtop_sub_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_top :
        (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          Section2.centralizerIn (H.subgroupOf (⊤ : Subgroup L))
            (rtop : (⊤ : Subgroup L)) := by
      have hx_comm : (x : L) * (r : L) = (r : L) * x := by
        exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
      constructor
      · exact hx.1
      · change (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          Subgroup.centralizer ({rtop} : Set (⊤ : Subgroup L))
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        dsimp
        calc
          x * (rtop : L) = x * (r : L) := by rw [hrtopr_val]
          _ = (r : L) * x := hx_comm
          _ = (rtop : L) * x := by rw [hrtopr_val]
    have hx_top_bot :
        (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          (⊥ : Subgroup (⊤ : Subgroup L)) := by
      simpa [hcent_top] using hx_top
    have hx_top_eq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 := by
      simpa using hx_top_bot
    exact congrArg Subtype.val hx_top_eq
  have hfrobHR : IsFrobeniusGroupWithKernelComplement H R := by
    exact (lemma_3_1 (K := H) (R := R) hHne hRne hHnorm hcomp).2 hcentElem
  let H1 : Subgroup L := ⁅H,H⁆
  have hH1_le_H : H1 ≤ H :=
    Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have : H1.Normal := by
    dsimp [H1]
    infer_instance
  have hH_not_le_H1 : ¬ H ≤ H1 := by
    intro hle
    have htop_ne : (⊤ : Subgroup H) ≠ ⊥ := by
      intro htop_bot
      apply hHne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxH
      have hx_sub : (⟨x, hxH⟩ : H) ∈ (⊥ : Subgroup H) := by
        simp [← htop_bot]
      have hx_eq : (⟨x, hxH⟩ : H) = 1 := by
        simpa using hx_sub
      exact congrArg Subtype.val hx_eq
    have hcomm_lt : commutator H < (⊤ : Subgroup H) := by
      have : Group.IsNilpotent H := hnil
      simpa [show commutator H =
          ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ from rfl] using
        (nilpotent_commutator_lt_self_of_normal (⊤ : Subgroup H) htop_ne)
    have hcomm_eq_top : commutator H = (⊤ : Subgroup H) := by
      rw [← theorem_6_8_subgroupOf_commutator_eq H]
      apply le_antisymm le_top
      intro x _hx
      exact hle x.property
    exact hcomm_lt.ne hcomm_eq_top
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  have hfrobQuot :
      IsFrobeniusGroupWithKernelComplement (H.map q) (R.map q) :=
    lemma_3_2_b (K := H) (R := R) (N := H1) hfrobHR hsolvH hH_not_le_H1
  refine ⟨by infer_instance, hH1_le_H, hHnorm, R.map q, ?_, ?_, ?_, ?_⟩
  · simpa [q, H1] using hfrobQuot.isComplement'
  · simpa [q, H1] using hfrobQuot.kernel_ne_bot
  · simpa [q, H1] using hfrobQuot.complement_ne_bot
  · have hcentQuotElem :
        ∀ r : R.map q, r ≠ 1 →
          elementCentralizerIn (H.map q) (r : L ⧸ H1) = ⊥ :=
      (lemma_3_1 (G := L ⧸ H1) (K := H.map q) (R := R.map q)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [q, H1, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentQuotElem r hr

theorem theorem_6_8_complement_card_coprime_kernel_of_frobenius
    {L : Type u} [Group L] [Finite L]
    {H R : Subgroup L} [H.Normal]
    (hcent : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥) :
    Nat.Coprime (Nat.card R) (Nat.card H) := by
  have hcent' :
      ∀ r : R, r ≠ 1 → Section2.centralizerIn H (r : L) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcent r hr
  have hdvd : Nat.card R ∣ Nat.card H - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := H) (R := R) (N := H) le_rfl hcent'
  have hle_one : 1 ≤ Nat.card H := Nat.succ_le_of_lt (Nat.card_pos (α := H))
  have hcop_sub : Nat.Coprime (Nat.card H - 1) (Nat.card H) := by
    rw [Nat.coprime_self_sub_left hle_one]
    exact Nat.coprime_one_left (Nat.card H)
  exact Nat.Coprime.of_dvd_left hdvd hcop_sub

theorem theorem_6_8_conjugateOnNormal_ne_of_frobenius_complement
    {L : Type u} [Group L] [Finite L]
    {H R : Subgroup L} [H.Normal]
    (hcent : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥)
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H)
    (r : R) (hrne : r ≠ 1) :
    Section1.conjugateOnNormal H θ (r : L) ≠ θ := by
  intro hfix
  have hcopRH : Nat.Coprime (Nat.card R) (Nat.card H) :=
    theorem_6_8_complement_card_coprime_kernel_of_frobenius hcent
  have hcoprH : Nat.Coprime (orderOf (r : L)) (Nat.card H) :=
    Nat.Coprime.of_dvd_left
      (Subgroup.orderOf_dvd_natCard R r.property) hcopRH
  have hcent' : Section2.centralizerIn H (r : L) = ⊥ := by
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcent r hrne
  have hcard_cent : Nat.card (Section2.centralizerIn H (r : L)) = 1 := by
    simp [hcent']
  have hcard_cent_ft : Fintype.card (Section2.centralizerIn H (r : L)) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_cent
  have hle :
      Nat.card {X : Section1.ClassFunction H |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal H X (r : L) = X} ≤ 1 := by
    have hle0 :=
      Section4Scratch.fixed_irreducible_card_le_centralizerIn_of_coprime_pf45
        H (r : L) hcoprH
    simpa [hcard_cent_ft] using hle0
  have hsub :
      Subsingleton {X : Section1.ClassFunction H |
          Section1.IsIrreducibleCharacterOnGroup X ∧
            Section1.conjugateOnNormal H X (r : L) = X} :=
    Section4Scratch.fixed_irreducible_subsingleton_of_card_le_one_pf45
      H (r : L) hle
  let fixedθ : {X : Section1.ClassFunction H |
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.conjugateOnNormal H X (r : L) = X} :=
    ⟨θ, hθirr, hfix⟩
  let fixedPrincipal : {X : Section1.ClassFunction H |
      Section1.IsIrreducibleCharacterOnGroup X ∧
        Section1.conjugateOnNormal H X (r : L) = X} :=
    ⟨Section1.principalCharacter H,
      Section3.principalCharacter_isIrreducibleCharacterOnGroup,
      by
        funext h
        simp [Section1.conjugateOnNormal, Section1.principalCharacter]⟩
  have hEq : fixedθ = fixedPrincipal := @Subsingleton.elim _ hsub fixedθ fixedPrincipal
  exact hθne (congrArg Subtype.val hEq)

public theorem theorem_6_8_inertiaSubgroup_eq_of_frobenius_complement
    {L : Type u} [Group L] [Finite L]
    {H R : Subgroup L} [H.Normal]
    (hcomp : H.IsComplement' R)
    (hcent : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥)
    {θ : Section1.ClassFunction H}
    (hθclass : Section1.IsClassFunction θ)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H) :
    Section1.inertiaSubgroup H θ = H := by
  have hHleI : H ≤ Section1.inertiaSubgroup H θ := by
    intro x hx
    change Section1.conjugateOnNormal H θ x = θ
    funext h
    change θ ⟨x * (h : L) * x⁻¹, by
      exact (inferInstance : H.Normal).conj_mem (h : L) h.2 x⟩ = θ h
    calc
      θ ⟨x * (h : L) * x⁻¹, _⟩ =
          θ (⟨x, hx⟩ * h * ⟨x, hx⟩⁻¹) := by
        congr 1
      _ = θ h := hθclass ⟨x, hx⟩ h
  apply le_antisymm
  · intro g hgI
    rcases hcomp.2 g with ⟨p, hp⟩
    rcases p with ⟨h, r⟩
    have hgr : (h : L) * (r : L) = g := by
      simpa using hp
    have hhI : (h : L) ∈ Section1.inertiaSubgroup H θ :=
      hHleI h.property
    have hrI : (r : L) ∈ Section1.inertiaSubgroup H θ := by
      have htmp :
          (h : L)⁻¹ * g ∈ Section1.inertiaSubgroup H θ :=
        (Section1.inertiaSubgroup H θ).mul_mem
          ((Section1.inertiaSubgroup H θ).inv_mem hhI) hgI
      have heq : (h : L)⁻¹ * g = (r : L) := by
        rw [← hgr]
        simp
      simpa [heq] using htmp
    have hr_one : r = 1 := by
      by_contra hrne
      have hfix : Section1.conjugateOnNormal H θ (r : L) = θ := by
        simpa [Section1.inertiaSubgroup] using hrI
      exact theorem_6_8_conjugateOnNormal_ne_of_frobenius_complement
        hcent hθirr hθne r hrne hfix
    have hg_eq : g = (h : L) := by
      rw [← hgr, hr_one]
      simp
    rw [hg_eq]
    exact h.property
  · exact hHleI

public theorem theorem_6_8_frobeniusWithKernel_top_complement_data
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    ∃ hHnorm : H.Normal,
      letI : H.Normal := hHnorm
      ∃ R : Subgroup L,
        H.IsComplement' R ∧
          R ≠ ⊥ ∧
          ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥ := by
  classical
  rcases hfrob with
    ⟨_hHtop, hHtopNorm, Rtop, hcompTop, _hHtop_ne, hRtop_ne, hcentTop⟩
  have hHnorm : H.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    have hn_top :
        (⟨n, trivial⟩ : (⊤ : Subgroup L)) ∈
          H.subgroupOf (⊤ : Subgroup L) := hn
    have hconj_top :=
      hHtopNorm.conj_mem (⟨n, trivial⟩ : (⊤ : Subgroup L)) hn_top
        (⟨g, trivial⟩ : (⊤ : Subgroup L))
    exact hconj_top
  let R : Subgroup L := Rtop.map (⊤ : Subgroup L).subtype
  have hcomp : H.IsComplement' R := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxH hxR
      rcases hxR with ⟨rtop, hrtop, hrtopx⟩
      have hx_top :
          (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
            (⊥ : Subgroup (⊤ : Subgroup L)) := by
        have hxHtop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
              H.subgroupOf (⊤ : Subgroup L) := hxH
        have hxRtop : (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈ Rtop := by
          have hsubeq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = rtop := by
            apply Subtype.ext
            change x = (rtop : L)
            exact hrtopx.symm
          rw [hsubeq]
          exact hrtop
        exact (Subgroup.disjoint_def.mp hcompTop.disjoint) hxHtop hxRtop
      have hx_top_eq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 := by
        simpa using hx_top
      exact congrArg Subtype.val hx_top_eq
    · rw [Set.eq_univ_iff_forall]
      intro x
      rcases hcompTop.2 (⟨x, trivial⟩ : (⊤ : Subgroup L)) with ⟨p, hp⟩
      rcases p with ⟨h, r⟩
      refine ⟨((h : (⊤ : Subgroup L)) : L), h.property,
        ((r : (⊤ : Subgroup L)) : L), ?_, ?_⟩
      · exact ⟨(r : (⊤ : Subgroup L)), r.property, rfl⟩
      · exact congrArg Subtype.val hp
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRtop_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    have hrmap : (r : L) ∈ R := ⟨r, hr, rfl⟩
    have hrbot : (r : L) ∈ (⊥ : Subgroup L) := by
      simpa [R, hRbot] using hrmap
    apply Subtype.ext
    simpa using hrbot
  have hcentElem : ∀ r : R, r ≠ 1 → elementCentralizerIn H (r : L) = ⊥ := by
    intro r hrne
    rcases r.property with ⟨rtop, hrtop, hrtopr⟩
    have hrtopr_val : (rtop : L) = (r : L) := hrtopr
    have hrtop_sub_ne : (⟨rtop, hrtop⟩ : Rtop) ≠ 1 := by
      intro hrtop_one
      apply hrne
      apply Subtype.ext
      calc
        (r : L) = (rtop : L) := hrtopr_val.symm
        _ = 1 := by simpa using congrArg Subtype.val hrtop_one
    have hcent_top := hcentTop ⟨rtop, hrtop⟩ hrtop_sub_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_top :
        (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          Section2.centralizerIn (H.subgroupOf (⊤ : Subgroup L))
            (rtop : (⊤ : Subgroup L)) := by
      have hx_comm : (x : L) * (r : L) = (r : L) * x := by
        exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
      constructor
      · exact hx.1
      · change (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          Subgroup.centralizer ({rtop} : Set (⊤ : Subgroup L))
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        dsimp
        calc
          x * (rtop : L) = x * (r : L) := by rw [hrtopr_val]
          _ = (r : L) * x := hx_comm
          _ = (rtop : L) * x := by rw [hrtopr_val]
    have hx_top_bot :
        (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
          (⊥ : Subgroup (⊤ : Subgroup L)) := by
      simpa [hcent_top] using hx_top
    have hx_top_eq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 := by
      simpa using hx_top_bot
    exact congrArg Subtype.val hx_top_eq
  exact ⟨hHnorm, R, hcomp, hRne, hcentElem⟩

theorem theorem_6_8_frobenius_card_dvd_Z_sub_one
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H)
    (hZH : Z ≤ H)
    (hZnorm : Z.Normal) :
    Nat.card W1 ∣ Nat.card Z - 1 := by
  classical
  rcases theorem_6_8_frobeniusWithKernel_top_complement_data hfrob with
    ⟨hHnorm, R, hcompR, _hRne, hcentElem⟩
  have : H.Normal := hHnorm
  have : Z.Normal := hZnorm
  have hcent :
      ∀ r : R, r ≠ 1 → Section2.centralizerIn H (r : L) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentElem r hr
  have hdvdR : Nat.card R ∣ Nat.card Z - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := H) (R := R) (N := Z) hZH hcent
  have hcompW1 : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hcardR : Nat.card R = Nat.card W1 :=
    (hcompR.symm.index_eq_card).symm.trans hcompW1.symm.index_eq_card
  rw [hcardR] at hdvdR
  exact hdvdR

public theorem theorem_6_8_inducedKernelFamily_irreducible_of_frobenius_complement
    {L : Type u} [Group L] [Finite L]
    {H R : Subgroup L} [H.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hcomp : H.IsComplement' R)
    (hcent : ∀ r : R, r ≠ 1 →
      Section2.centralizerIn H (r : L) = ⊥) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup χ := by
  classical
  have hcentElem : ∀ r : R, r ≠ 1 →
      elementCentralizerIn H (r : L) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcent r hr
  intro χ hχS
  rcases (hSbot.2 χ).mp hχS with
    ⟨θ, hθirr, _hθker, hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθclass : Section1.IsClassFunction θ := by
    rw [hθeq]
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hIeq :
      Section1.inertiaSubgroup H θ = H :=
    theorem_6_8_inertiaSubgroup_eq_of_frobenius_complement
      hcomp hcentElem hθclass ⟨n, ρ, hρirr, hθeq⟩ hθne
  have hIeqρ :
      Section1.inertiaSubgroup H ρ.character = H := by
    simpa [hθeq] using hIeq
  have hrel :
      H.relIndex (Section1.inertiaSubgroup H ρ.character) = 1 := by
    rw [hIeqρ]
    simp [Subgroup.relIndex]
  have hInd :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF H ρ.character) :=
    Section1.proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      H ρ hρirr hrel
  simpa [hχeq, hθeq] using hInd

public theorem theorem_6_8_inducedKernelFamily_irreducible_of_frobenius
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup χ := by
  classical
  rcases theorem_6_8_frobeniusWithKernel_top_complement_data hfrob with
    ⟨hHnorm, R, hcomp, _hRne, hcent⟩
  have : H.Normal := hHnorm
  refine theorem_6_8_inducedKernelFamily_irreducible_of_frobenius_complement
    hSbot hcomp ?_
  intro r hr
  simpa [Section2.centralizerIn, Section2.elementCentralizer,
    elementCentralizerIn] using hcent r hr

theorem theorem_6_8_irreducible_members_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    ∀ X : S,
      Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L) := by
  classical
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  intro X
  rcases X with ⟨χ, hχS⟩
  exact theorem_6_8_inducedKernelFamily_irreducible_of_frobenius hSbot hfrob χ hχS

theorem theorem_6_8_hypothesis_5_2_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H) :
    Section5.hypothesis_5_2_statement S T :=
  theorem_6_8_hypothesis_5_2_of_hypothesis_and_irreducible h68
    (theorem_6_8_irreducible_members_of_frobenius h68 hfrob)

theorem theorem_6_8_hypothesis_6_4_of_source_bridges
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W H1 : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hbotH1 : (⊥ : Subgroup L) ≤ H1)
    (hcomm : commutatorQuotientHypothesis (⊥ : Subgroup L) H1 H)
    (hfrob : frobeniusQuotientWithKernel H H1) :
    hypothesis_6_4_statement H ⊥ H1 S T := by
  rcases h68 with ⟨hsemi, hodd, _hHne, hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have h61 : hypothesis_6_1_statement H S T := by
    exact theorem_6_8_hypothesis_6_1_of_hypothesis_5_2
      (L := L) (H := H) (W1 := W1) (W2 := W2) (W := W)
      (S := S) (T := T)
      ⟨hsemi, hodd, _hHne, hnil, _hTI, hSbot, _hT, _hcase⟩ h52
  have hnilQuot : nilpotentQuotient (⊥ : Subgroup L) H :=
    theorem_6_8_nilpotentQuotient_bot H hHnorm hnil
  exact ⟨h61, hodd, hbotH1, bot_le, hnilQuot, hcomm, hfrob⟩

theorem theorem_6_8_hypothesis_6_4_commutator_of_source_bridges
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hfrob : frobeniusQuotientWithKernel H ⁅H, H⁆) :
    hypothesis_6_4_statement H ⊥ ⁅H, H⁆ S T := by
  exact theorem_6_8_hypothesis_6_4_of_source_bridges
    (L := L) (H := H) (W1 := W1) (W2 := W2) (W := W)
    (H1 := ⁅H, H⁆) (S := S) (T := T)
    h68 h52 bot_le
    (theorem_6_8_commutatorQuotient_bot_commutator H
      (theorem_6_8_left_normal_of_semidirect_top h68.1))
    hfrob

theorem theorem_6_8_hypothesis_5_2_of_branch
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section5.hypothesis_5_2_statement S T := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  rcases hcase with hfrob | hcaseC2
  · exact theorem_6_8_hypothesis_5_2_of_frobenius h68' hfrob
  · exact theorem_6_8_hypothesis_5_2_of_caseC2 h68' hcaseC2

theorem theorem_6_8_frobeniusQuotient_commutator_of_branch
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    frobeniusQuotientWithKernel H ⁅H,H⁆ := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  rcases hcase with hfrob | hcaseC2
  · exact theorem_6_8_frobeniusQuotient_commutator_of_frobenius hHne hnil hfrob
  · exact theorem_6_8_frobeniusQuotient_commutator_of_caseC2 h68' hcaseC2

theorem theorem_6_8_hypothesis_6_4_commutator_of_branch
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    hypothesis_6_4_statement H ⊥ ⁅H,H⁆ S T :=
  theorem_6_8_hypothesis_6_4_commutator_of_source_bridges h68
    (theorem_6_8_hypothesis_5_2_of_branch h68)
    (theorem_6_8_frobeniusQuotient_commutator_of_branch h68)

theorem theorem_6_8_familyData_X_subset_S
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    X ⊆ S := by
  intro χ hχ
  rcases hfamily with ⟨_hZH, _hSZ, hXeq, _hY⟩
  have hχdiff : χ ∈ S \ SZ := by
    simpa [hXeq] using hχ
  exact (Finset.mem_sdiff.mp hχdiff).1

theorem theorem_6_8_caseC2_X_irreducible_of_nonbase_piColumn_mem_SZ
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hpiSZ : ∀ d : caseC2FullData L H W1 W2 W T,
      letI : Fintype d.I := d.instFintypeI
      letI : Fintype d.J := d.instFintypeJ
      letI : DecidableEq d.I := d.instDecidableEqI
      letI : DecidableEq d.J := d.instDecidableEqJ
      ∀ j : d.J, j ≠ d.j0 →
        Section4Scratch.piColumn d.piChar j ∈ SZ) :
    ∀ χ : Section1.ClassFunction L, χ ∈ X →
      Section1.IsIrreducibleCharacterOnGroup χ := by
  intro χ hχX
  by_contra hχnotirr
  have hχS : χ ∈ S := theorem_6_8_familyData_X_subset_S hfamily hχX
  rcases theorem_6_8_caseC2_nonirreducible_mem_piColumn
      h68 hcase hχS hχnotirr with
    ⟨d, hχpi⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases hχpi with ⟨j, hj, hχeq⟩
  have hχSZ : χ ∈ SZ := by
    rw [hχeq]
    exact hpiSZ d j hj
  rcases hfamily with ⟨_hZH, _hSZ, hXeq, _hY⟩
  have hχnotSZ : χ ∉ SZ := by
    have hχdiff : χ ∈ S \ SZ := by
      simpa [hXeq] using hχX
    exact (Finset.mem_sdiff.mp hχdiff).2
  exact hχnotSZ hχSZ

theorem theorem_6_8_familyData_Y_subset_S
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    Y ⊆ S := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  exact inducedKernelFamily_subset_base hSbot hY

theorem theorem_6_8_familyData_Y_subset_SZ_of_Z_le_commutator
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆) :
    Y ⊆ SZ := by
  rcases hfamily with ⟨_hZH, hSZ, _hXeq, hY⟩
  exact inducedKernelFamily_subset_of_le hY hSZ hZcomm

theorem theorem_6_8_familyData_not_mem_X_of_mem_Y
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    η ∉ X := by
  intro hηX
  rcases hfamily with ⟨_hZH, hSZ, hXeq, hY⟩
  have hηSZ : η ∈ SZ :=
    theorem_6_8_familyData_Y_subset_SZ_of_Z_le_commutator
      ⟨_hZH, hSZ, hXeq, hY⟩ hZcomm hηY
  have hηnotSZ : η ∉ SZ := by
    have hηdiff : η ∈ S \ SZ := by
      simpa [hXeq] using hηX
    exact (Finset.mem_sdiff.mp hηdiff).2
  exact hηnotSZ hηSZ

theorem theorem_6_8_mem_Y_subgroupInKernel_commutator
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    Section1.subgroupInKernel' η ⁅H,H⁆ := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  exact theorem_6_6_mem_SZ_subgroupInKernel
    (K := H) (Z := ⁅H,H⁆) (SZ := Y)
    (Subgroup.commutator_normal H H)
    (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
    hY hηY

theorem theorem_6_8_caseB_mem_Y_subgroupInKernel_Z
    {L : Type u} [Group L] [Finite L]
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    Section1.subgroupInKernel' η Z := by
  rcases hB with ⟨_hW2ne, _hW2center, hW2comm, hZeq⟩
  subst Z
  have hηcomm : Section1.subgroupInKernel' η ⁅H,H⁆ :=
    theorem_6_8_mem_Y_subgroupInKernel_commutator
      (H := H) (Z := W2) hfamily hηY
  intro z
  exact hηcomm ⟨(z : L), hW2comm z.property⟩

theorem theorem_6_8_caseB_Z_prime_card
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    Nat.Prime (Nat.card Z) := by
  rcases hcase with ⟨_hfull, ⟨p, hp, hW2card⟩, _hW2comm⟩
  rcases hB with ⟨_hW2ne, _hW2center, _hW2commB, hZeq⟩
  have hZcard : Nat.card Z = p := by
    simpa [hZeq] using hW2card
  rw [hZcard]
  exact hp


theorem theorem_6_8_constantOnSubgroupImageNonidentity_of_prime_card_zpow_nontrivial
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    {ψ : Section1.ClassFunction G}
    (hprime : Nat.Prime (Nat.card Z))
    (hpow : ∀ z : Z, z ≠ 1 → ∀ n : ℤ, (z ^ n : Z) ≠ 1 →
      ψ ((((z ^ n : Z) : L) : G)) = ψ ((z : L) : G)) :
    constantOnSubgroupImageNonidentity L Z ψ := by
  intro z1 z2 hz1 hz2
  have : Fact (Nat.Prime (Nat.card Z)) := ⟨hprime⟩
  have hz2pow : z2 ∈ Subgroup.zpowers z1 := by
    exact mem_zpowers_of_prime_card (G := Z) (p := Nat.card Z) rfl hz1
  rcases Subgroup.mem_zpowers_iff.mp hz2pow with ⟨n, hn⟩
  have hzpow_ne : (z1 ^ n : Z) ≠ 1 := by
    simpa [hn] using hz2
  subst z2
  exact (hpow z1 hz1 n hzpow_ne).symm

theorem theorem_6_8_constantCentralizerOrderOnNonidentity_of_prime_card
    {L : Type u} [Group L] [Finite L]
    {Z L0 : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z)) :
    constantCentralizerOrderOnNonidentity Z L0 := by
  intro z1 z2 hz1 hz2
  have : Fact (Nat.Prime (Nat.card Z)) := ⟨hprime⟩
  have hz2pow : z2 ∈ Subgroup.zpowers z1 := by
    exact mem_zpowers_of_prime_card (G := Z) (p := Nat.card Z) rfl hz1
  have hz1pow : z1 ∈ Subgroup.zpowers z2 := by
    exact mem_zpowers_of_prime_card (G := Z) (p := Nat.card Z) rfl hz2
  have hcent_eq :
      Section2.centralizerIn L0 (z1 : L) =
        Section2.centralizerIn L0 (z2 : L) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_zpowers_iff.mp hz2pow with ⟨n, hn⟩
      rw [Section2.centralizerIn, Section2.elementCentralizer] at hx ⊢
      rcases hx with ⟨hxL0, hxcent⟩
      refine ⟨hxL0, ?_⟩
      have hxcomm : x * (z1 : L) = (z1 : L) * x := by
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (show x ∈ Subgroup.centralizer ({(z1 : L)} : Set L) from hxcent)
      change x ∈ Subgroup.centralizer ({(z2 : L)} : Set L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute x (z1 : L) := hxcomm
      subst z2
      simpa using (Commute.zpow_right hcomm n).eq
    · intro hx
      rcases Subgroup.mem_zpowers_iff.mp hz1pow with ⟨n, hn⟩
      rw [Section2.centralizerIn, Section2.elementCentralizer] at hx ⊢
      rcases hx with ⟨hxL0, hxcent⟩
      refine ⟨hxL0, ?_⟩
      have hxcomm : x * (z2 : L) = (z2 : L) * x := by
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (show x ∈ Subgroup.centralizer ({(z2 : L)} : Set L) from hxcent)
      change x ∈ Subgroup.centralizer ({(z1 : L)} : Set L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute x (z2 : L) := hxcomm
      subst z1
      simpa using (Commute.zpow_right hcomm n).eq
  rw [hcent_eq]


theorem theorem_6_8_sylow_of_nonabelianPQuotient_bot
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    {p : ℕ} (hpQ : nonabelianPQuotient (⊥ : Subgroup L) H p) :
    ∃ P : Sylow p L, (P : Subgroup L) = H := by
  rcases hpQ with
    ⟨hbotH, hbotnormH, hbotnorm, hHnorm, hpprime, hQp, hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hpQ' : nonabelianPQuotient (⊥ : Subgroup L) H p :=
    ⟨hbotH, hbotnormH, hbotnorm, hHnorm, hpprime, hQp, hnoncomm⟩
  have hHp : IsPGroup p H :=
    theorem_6_6_isPGroup_of_nonabelianPQuotient_bot hpQ'
  have hcop :
      Nat.Coprime (H.relIndex (⊤ : Subgroup L)) p :=
    theorem_6_6_relIndex_top_coprime_prime_of_nonabelianPQuotient
      (theorem_6_8_hypothesis_6_4_commutator_of_branch h68) hpQ'
  have hnot : ¬ p ∣ H.index := by
    have hnotRel : ¬ p ∣ H.relIndex (⊤ : Subgroup L) :=
      (Nat.Prime.coprime_iff_not_dvd hpprime).1 hcop.symm
    simpa [Subgroup.relIndex_top_right] using hnotRel
  let P : Sylow p L := IsPGroup.toSylow hHp hnot
  exact ⟨P, by simp [P, IsPGroup.toSylow_coe]⟩

public theorem theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured
    {G : Type u} [Group G]
    {L : Subgroup G} {H : Subgroup L} :
    subgroupImagePuncturedSet L H =
      {g : G | g ∈ (H.map L.subtype : Subgroup G) ∧ g ≠ 1} := by
  ext x
  constructor
  · rintro ⟨h, hheq, hhne⟩
    constructor
    · exact ⟨(h : L), h.property, hheq⟩
    · intro hx1
      apply hhne
      ext
      simp [hheq, hx1]
  · rintro ⟨hxH, hxne⟩
    rcases hxH with ⟨l, hlH, hlEq⟩
    refine ⟨⟨l, hlH⟩, hlEq, ?_⟩
    intro hl1
    apply hxne
    rw [← hlEq]
    simpa [hl1]

public theorem theorem_6_8_normalizer_map_subtype_eq_setNormalizer_punctured
    {G : Type u} [Group G]
    {L : Subgroup G} {H : Subgroup L} :
    Subgroup.normalizer (((H.map L.subtype : Subgroup G) : Set G)) =
      Section2.setNormalizer (subgroupImagePuncturedSet L H) := by
  classical
  let Hmap : Subgroup G := H.map L.subtype
  let A : Set G := subgroupImagePuncturedSet L H
  have hAiff : ∀ x : G, x ∈ A ↔ x ∈ Hmap ∧ x ≠ 1 := by
    intro x
    change x ∈ subgroupImagePuncturedSet L H ↔
      x ∈ (H.map L.subtype : Subgroup G) ∧ x ≠ 1
    rw [theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured]
    rfl
  ext g
  constructor
  · intro hg
    change Section2.normalizesSet A g
    intro x
    rw [hAiff, hAiff]
    have hnorm := (Subgroup.mem_normalizer_iff.mp hg x)
    constructor
    · rintro ⟨hcx, hcxne⟩
      constructor
      · exact hnorm.2 hcx
      · intro hx1
        apply hcxne
        simp [Section2.conjBy, hx1]
    · rintro ⟨hxH, hxne⟩
      constructor
      · exact hnorm.1 hxH
      · intro hcx1
        apply hxne
        have h := congrArg (fun y : G => g⁻¹ * y * g) hcx1
        simpa [Section2.conjBy, mul_assoc] using h
  · intro hg
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hxH
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxA : x ∈ A := (hAiff x).2 ⟨hxH, hx1⟩
        have hcxA : Section2.conjBy g x ∈ A := (hg x).2 hxA
        exact (hAiff (Section2.conjBy g x)).1 hcxA |>.1
    · intro hcxH
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hcxne : Section2.conjBy g x ≠ 1 := by
          intro hcx1
          apply hx1
          have h := congrArg (fun y : G => g⁻¹ * y * g) hcx1
          simpa [Section2.conjBy, mul_assoc] using h
        have hcxA : Section2.conjBy g x ∈ A :=
          (hAiff (Section2.conjBy g x)).2 ⟨hcxH, hcxne⟩
        have hxA : x ∈ A := (hg x).1 hcxA
        exact (hAiff x).1 hxA |>.1

theorem theorem_6_8_sylow_map_subtype_of_sylow_normalizer
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {H : Subgroup L}
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p L) (hP : (P : Subgroup L) = H)
    (hnorm : Subgroup.normalizer (((H.map L.subtype : Subgroup G) : Set G)) = L) :
    ∃ Pamb : Sylow p G, (Pamb : Subgroup G) = H.map L.subtype := by
  classical
  let Hmap : Subgroup G := H.map L.subtype
  have hnormHmap : Subgroup.normalizer ((Hmap : Set G)) = L := by
    simpa [Hmap] using hnorm
  have hHcard : Nat.card H = p ^ (Nat.card L).factorization p := by
    simpa [← hP] using (Sylow.card_eq_multiplicity P)
  have hHmapcard : Nat.card Hmap = p ^ (Nat.card L).factorization p := by
    calc
      Nat.card Hmap = Nat.card H := by
        simpa [Hmap] using
          (Subgroup.card_map_of_injective (K := H) (f := L.subtype)
            L.subtype_injective)
      _ = p ^ (Nat.card L).factorization p := hHcard
  have hHp : IsPGroup p Hmap := by
    have hPp : IsPGroup p (Subgroup.map L.subtype (P : Subgroup L)) :=
      P.isPGroup'.map L.subtype
    rw [hP] at hPp
    simpa [Hmap] using hPp
  have hnotidx : ¬ p ∣ Hmap.index := by
    intro hpidx
    let n : ℕ := (Nat.card L).factorization p
    have hpowdvdG : p ^ (n + 1) ∣ Nat.card G := by
      rw [← Subgroup.index_mul_card Hmap, hHmapcard]
      change p ^ (((Nat.card L).factorization p) + 1) ∣
        Hmap.index * p ^ ((Nat.card L).factorization p)
      rcases hpidx with ⟨k, hk⟩
      rw [hk]
      use k
      rw [Nat.pow_succ]
      ac_rfl
    have hpowdvdN :
        p ^ (n + 1) ∣ Nat.card (Subgroup.normalizer ((Hmap : Set G))) := by
      exact Sylow.prime_pow_dvd_card_normalizer hpowdvdG hHmapcard
    have hpowdvdL : p ^ ((Nat.card L).factorization p + 1) ∣ Nat.card L := by
      rw [hnormHmap] at hpowdvdN
      simpa [n] using hpowdvdN
    exact Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := L)).ne'
      (Fact.out : Nat.Prime p) hpowdvdL
  let Pamb : Sylow p G := IsPGroup.toSylow hHp hnotidx
  exact ⟨Pamb, by
    simp [Pamb, Hmap, IsPGroup.toSylow_coe]⟩

theorem theorem_6_8_map_subtype_ne_bot
    {G : Type u} [Group G] {L : Subgroup G} {Z : Subgroup L}
    (hZne : Z ≠ ⊥) :
    Z.map L.subtype ≠ (⊥ : Subgroup G) := by
  intro hmap
  apply hZne
  have hpre : Subgroup.comap L.subtype (Z.map L.subtype) = Z :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective Z
  rw [← hpre, hmap]
  ext z
  simp

theorem theorem_6_8_map_subtype_le_centerIn
    {G : Type u} [Group G] {L : Subgroup G} {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H) :
    Z.map L.subtype ≤ centerIn (H.map L.subtype) := by
  intro x hx
  rcases hx with ⟨z, hzZ, rfl⟩
  have hzcent : (z : L) ∈ centerIn H := hZcent hzZ
  constructor
  · exact ⟨(z : L), hzcent.1, rfl⟩
  · change (L.subtype z) ∈
      Subgroup.centralizer (((H.map L.subtype : Subgroup G) : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyHmap
    rcases hyHmap with ⟨h, hhH, rfl⟩
    have hcommL : h * (z : L) = (z : L) * h := by
      exact Subgroup.mem_centralizer_iff.mp hzcent.2 h hhH
    exact congrArg (fun t : L => (t : G)) hcommL

theorem theorem_6_8_map_subtype_normal_subgroupOf
    {G : Type u} [Group G] {L : Subgroup G} {Z : Subgroup L}
    [Z.Normal] :
    ∃ _hZL : Z.map L.subtype ≤ L,
      ((Z.map L.subtype).subgroupOf L).Normal := by
  have hZL : Z.map L.subtype ≤ L := Subgroup.map_subtype_le Z
  refine ⟨hZL, ?_⟩
  have hpre : (Z.map L.subtype).subgroupOf L = Z := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective Z
  rw [hpre]
  infer_instance

theorem theorem_6_8_constantOnSubgroupImageNonidentity_map_subtype
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    {ψ : Section1.ClassFunction G}
    (hconst : constantOnSubgroupImageNonidentity L Z ψ) :
    constantOnNonidentitySubgroup (Z.map L.subtype) ψ := by
  intro z1 z2 hz1 hz2
  rcases z1 with ⟨g1, hg1⟩
  rcases z2 with ⟨g2, hg2⟩
  rcases hg1 with ⟨l1, hl1Z, hl1eq⟩
  rcases hg2 with ⟨l2, hl2Z, hl2eq⟩
  subst g1
  subst g2
  have hl1ne : (⟨l1, hl1Z⟩ : Z) ≠ 1 := by
    intro hl1
    apply hz1
    ext
    simpa using congrArg (fun z : Z => ((z : L) : G)) hl1
  have hl2ne : (⟨l2, hl2Z⟩ : Z) ≠ 1 := by
    intro hl2
    apply hz2
    ext
    simpa using congrArg (fun z : Z => ((z : L) : G)) hl2
  exact hconst ⟨l1, hl1Z⟩ ⟨l2, hl2Z⟩ hl1ne hl2ne


public theorem theorem_6_8_subgroupOf_top_normal_of_normal
    {L : Type u} [Group L] {Z : Subgroup L} [Z.Normal] :
    (Z.subgroupOf (⊤ : Subgroup L)).Normal := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (show Z ≤ (⊤ : Subgroup L) from le_top)).2
    (Subgroup.le_normalizer_of_normal (H := Z))


theorem theorem_6_8_2_1_of_zpow_invariance_nontrivial
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hpow :
      theorem_6_8_hypothesis L H W1 W2 W S T →
        (∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) →
          caseC2Hypothesis L H W1 W2 W T →
            theorem_6_8_caseBData H W2 Z →
              theorem_6_8_familyData H Z S SZ X Y →
                coherentExtension Y T τ₁ →
                  ∀ η : Section1.ClassFunction L, η ∈ Y →
                    ∀ z : Z, z ≠ 1 → ∀ n : ℤ, (z ^ n : Z) ≠ 1 →
                      (τ₁ η) ((((z ^ n : Z) : L) : G)) =
                        (τ₁ η) ((z : L) : G)) :
    theorem_6_8_2_1_statement L H W1 W2 W Z S SZ X Y T τ₁ := by
  intro h68 hpQ hcase hB hfamily hτ₁ η hηY
  exact theorem_6_8_constantOnSubgroupImageNonidentity_of_prime_card_zpow_nontrivial
    (theorem_6_8_caseB_Z_prime_card hcase hB)
    (hpow h68 hpQ hcase hB hfamily hτ₁ η hηY)

theorem theorem_6_8_pow_mem_normal_subgroup_iff_of_coprime_natCard
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L} [H.Normal] {e : ℕ}
    (he : e.Coprime (Nat.card L)) (l : L) :
    l ^ e ∈ H ↔ l ∈ H := by
  classical
  have heQ : e.Coprime (Nat.card (L ⧸ H)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card H) he
  have hsurj : Function.Surjective (fun q : L ⧸ H => q ^ e) :=
    Section5.pow_surjective_of_coprime_natCard_pf59 (G := L ⧸ H) (e := e) heQ
  have hinj : Function.Injective (fun q : L ⧸ H => q ^ e) := by
    rw [Finite.injective_iff_surjective]
    exact hsurj
  constructor
  · intro hl
    have hqpow : (QuotientGroup.mk' H l) ^ e = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := H) (x := l ^ e)).2 hl
    have hq : QuotientGroup.mk' H l = 1 := by
      apply hinj
      simpa using hqpow
    exact (QuotientGroup.eq_one_iff (N := H) (x := l)).1 hq
  · intro hl
    exact H.pow_mem hl e

theorem theorem_6_8_inducedCF_argumentPow_of_normal
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L} [H.Normal]
    (θ : Section1.ClassFunction H) {e : ℕ}
    (he : e.Coprime (Nat.card L)) :
    Section3.classFunctionArgumentPow
      (Section1.inducedCF H θ)
      (Section1.inducedCF H (fun h : H => θ (h ^ e))) e := by
  classical
  intro l
  unfold Section1.inducedCF Section1.inducedClassFunction
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hxH : x * l * x⁻¹ ∈ H
  · have hxpowH : x * (l ^ e) * x⁻¹ ∈ H := by
      simpa [conj_pow] using H.pow_mem hxH e
    simp [hxH, hxpowH, conj_pow]
  · have hxpowH : ¬ x * (l ^ e) * x⁻¹ ∈ H := by
      intro hxpowH
      have hpowConj : (x * l * x⁻¹) ^ e ∈ H := by
        simpa [conj_pow] using hxpowH
      exact hxH
        ((theorem_6_8_pow_mem_normal_subgroup_iff_of_coprime_natCard
          (H := H) he (x * l * x⁻¹)).1 hpowConj)
    simp [hxH, hxpowH]

public theorem theorem_6_8_coprime_of_valueOrderCardPart
    {a c n : ℕ} (hpart : Section3.valueOrderCardPart a c)
    (hn : n.Coprime a) :
    n.Coprime c := by
  by_contra hnc
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnc with ⟨p, hp, hpn, hpc⟩
  have hpa : p ∣ a := (hpart.2 p hp).1 hpc
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpn, hpa⟩) hn

public theorem theorem_6_8_natAbs_coprime_of_int_isCoprime
    {k : ℤ} {a : ℕ} (hk : IsCoprime k (a : ℤ)) :
    k.natAbs.Coprime a := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : k.gcd (a : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hk
  rw [Int.gcd_eq_natAbs] at hg
  simpa using hg

public theorem theorem_6_8_int_isCoprime_of_natAbs_coprime
    {k : ℤ} {c : ℕ} (hkc : k.natAbs.Coprime c) :
    IsCoprime k (c : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  simpa using (Nat.Coprime.gcd_eq_one hkc)

public theorem theorem_6_8_exists_valueOrderCardPart_factorization
    {a n : ℕ} (ha0 : 0 < a) (han : a ∣ n) (hn0 : n ≠ 0) :
    ∃ c b : ℕ, Section3.valueOrderCardPart a c ∧ n = c * b ∧ c.Coprime b := by
  classical
  let fA : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∣ a)
  let fB : ℕ →₀ ℕ := n.factorization.filter (fun p => ¬ p ∣ a)
  let c : ℕ := fA.prod (fun p e => p ^ e)
  let b : ℕ := fB.prod (fun p e => p ^ e)
  have hfA_le : fA ≤ n.factorization := by
    intro p
    by_cases hp : p ∣ a <;> simp [fA, hp]
  have hfB_le : fB ≤ n.factorization := by
    intro p
    by_cases hp : p ∣ a <;> simp [fB, hp]
  have hc_factor : c.factorization = fA := by
    simpa [c] using Nat.factorization_prod_pow_eq_self_of_le_factorization hfA_le
  have hb_factor : b.factorization = fB := by
    simpa [b] using Nat.factorization_prod_pow_eq_self_of_le_factorization hfB_le
  have hcb : c * b = n := by
    calc
      c * b = n.factorization.prod (fun p e => p ^ e) := by
        simp [c, b, fA, fB, Finsupp.prod_filter_mul_prod_filter_not]
      _ = n := Nat.prod_factorization_pow_eq_self hn0
  have hc0 : c ≠ 0 := by
    intro hc
    apply hn0
    rw [← hcb, hc]
    simp
  have hb0 : b ≠ 0 := by
    intro hb
    apply hn0
    rw [← hcb, hb]
    simp
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha0
  have ha_fac_le_n : a.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd ha_ne hn0).2 han
  have ha_fac_le_c : a.factorization ≤ c.factorization := by
    rw [hc_factor]
    intro p
    by_cases hpa : p ∣ a
    · simpa [fA, hpa] using ha_fac_le_n p
    · have hazero : a.factorization p = 0 := by
        by_cases hpprime : p.Prime
        · by_contra hnonzero
          have hone : 1 ≤ a.factorization p := Nat.pos_of_ne_zero hnonzero
          exact hpa ((Nat.Prime.dvd_iff_one_le_factorization hpprime ha_ne).2 hone)
        · exact Nat.factorization_eq_zero_of_not_prime a hpprime
      simp [fA, hpa, hazero]
  have ha_dvd_c : a ∣ c := (Nat.factorization_le_iff_dvd ha_ne hc0).1 ha_fac_le_c
  have hprime_c_iff : ∀ p : ℕ, p.Prime → (p ∣ c ↔ p ∣ a) := by
    intro p hp
    constructor
    · intro hpc
      have hone : 1 ≤ c.factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hp hc0).1 hpc
      by_contra hpa
      have hfzero : fA p = 0 := by
        simp [fA, hpa]
      rw [hc_factor, hfzero] at hone
      omega
    · intro hpa
      exact dvd_trans hpa ha_dvd_c
  have hcop : c.Coprime b := by
    by_contra hnot
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨p, hp, hpc, hpb⟩
    have hpa : p ∣ a := (hprime_c_iff p hp).1 hpc
    have hone : 1 ≤ b.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hb0).1 hpb
    have hfzero : fB p = 0 := by
      simp [fB, hpa]
    rw [hb_factor, hfzero] at hone
    omega
  exact ⟨c, b, ⟨ha_dvd_c, hprime_c_iff⟩, hcb.symm, hcop⟩

public theorem theorem_6_8_exists_coprime_natCard_intModEq_orderOf
    {G : Type u} [Group G] [Finite G] (z : G) {n : ℤ}
    (hn : IsCoprime n (orderOf z : ℤ)) :
    ∃ e : ℕ, e.Coprime (Nat.card G) ∧ (e : ℤ) ≡ n [ZMOD orderOf z] := by
  classical
  have horder_pos : 0 < orderOf z := orderOf_pos z
  have horder_dvd : orderOf z ∣ Nat.card G := orderOf_dvd_natCard z
  have hcard_ne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨c, b, hcpart, hcard, hcop⟩ :=
    theorem_6_8_exists_valueOrderCardPart_factorization
      horder_pos horder_dvd hcard_ne
  have hnc_nat : n.natAbs.Coprime c :=
    theorem_6_8_coprime_of_valueOrderCardPart hcpart
      (theorem_6_8_natAbs_coprime_of_int_isCoprime hn)
  have hnc : IsCoprime n (c : ℤ) :=
    theorem_6_8_int_isCoprime_of_natAbs_coprime hnc_nat
  have hcb_ne : c * b ≠ 0 := by
    rw [← hcard]
    exact hcard_ne
  obtain ⟨w, hwa, _hwb⟩ :=
    Section1.zmod_units_crt_exists_of_coprime hcop (ZMod.unitOfIsCoprime n hnc)
  let e : ℕ := (w : ZMod (c * b)).val
  have hec : e.Coprime (c * b) := by
    simpa [e] using ZMod.val_coe_unit_coprime w
  have hmodc : (e : ℤ) ≡ n [ZMOD c] :=
    Section1.zmod_units_crt_val_modEq_left_int hcb_ne hnc hwa
  have hcardF : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  refine ⟨e, ?_, ?_⟩
  · simpa [Nat.card_eq_fintype_card, hcardF] using hec
  · exact Int.ModEq.of_dvd (by exact_mod_cast hcpart.1) hmodc

theorem theorem_6_8_isCoprime_int_orderOf_of_prime_card_zpow_ne_one
    {Z : Type u} [Group Z]
    (hprime : Nat.Prime (Nat.card Z)) {z : Z} (hz : z ≠ 1)
    {n : ℤ} (hzn : z ^ n ≠ 1) :
    IsCoprime n (orderOf z : ℤ) := by
  classical
  have : Fact (Nat.Prime (Nat.card Z)) := ⟨hprime⟩
  have horder : orderOf z = Nat.card Z := by
    exact orderOf_eq_card_of_forall_mem_zpowers
      (fun x : Z => mem_zpowers_of_prime_card (G := Z) (p := Nat.card Z) rfl hz)
  have hprime_order : Nat.Prime (orderOf z) := by
    simpa [horder] using hprime
  have hmod_ne : ¬ n ≡ 0 [ZMOD (orderOf z : ℤ)] := by
    intro hmod
    apply hzn
    calc
      z ^ n = z ^ (0 : ℤ) := (zpow_eq_zpow_iff_modEq).2 hmod
      _ = 1 := by simp
  have hnot_dvd : ¬ orderOf z ∣ n.natAbs := by
    intro hdiv
    apply hmod_ne
    have hdivIntAbs : (orderOf z : ℤ) ∣ (n.natAbs : ℤ) := by
      exact_mod_cast hdiv
    have hdivInt : (orderOf z : ℤ) ∣ n := (Int.dvd_natAbs).1 hdivIntAbs
    exact Int.modEq_zero_iff_dvd.mpr hdivInt
  have hcop_left : (orderOf z).Coprime n.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hprime_order).2 hnot_dvd
  exact theorem_6_8_int_isCoprime_of_natAbs_coprime hcop_left.symm


theorem theorem_6_8_argumentPow_diff_integerSpanOn_punctured
    {L : Type u} [Group L]
    {Y : Finset (Section1.ClassFunction L)}
    {η ηu : Section1.ClassFunction L} {e : ℕ}
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (harg : Section3.classFunctionArgumentPow η ηu e) :
    Section5.integerSpanOn Y Section5.puncturedSet (ηu - η) := by
  have hspan : Section5.integerSpan Y (ηu - η) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem Y hηuY)
      (Section5.integerSpan_of_mem Y hηY)
  have hdeg : Section1.degree (ηu - η) = 0 := by
    rw [Section1.degree_apply]
    have hηu1 : ηu 1 = η 1 := by
      simpa using harg 1
    simp [hηu1]
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩

theorem theorem_6_8_subgroupInKernel_argumentPow_diff_vanish
    {L : Type u} [Group L]
    {Z : Subgroup L}
    {η ηu : Section1.ClassFunction L} {e : ℕ}
    (hker : Section1.subgroupInKernel' η Z)
    (harg : Section3.classFunctionArgumentPow η ηu e) :
    ∀ z : Z, (ηu - η) z = 0 := by
  intro z
  have hzpow : η ((⟨(z : L) ^ e, Z.pow_mem z.property e⟩ : Z) : L) = η 1 :=
    hker ⟨(z : L) ^ e, Z.pow_mem z.property e⟩
  have hz : η (z : L) = η 1 := hker z
  have hηu : ηu (z : L) = η ((z : L) ^ e) := harg (z : L)
  change ηu (z : L) - η (z : L) = 0
  rw [hηu, hzpow, hz, sub_self]

theorem theorem_6_8_caseB_Y_argumentPow_diff_data
    {L : Type u} [Group L] [Finite L]
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η ηu : Section1.ClassFunction L} {e : ℕ}
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (harg : Section3.classFunctionArgumentPow η ηu e) :
    Section5.integerSpanOn Y Section5.puncturedSet (ηu - η) ∧
      ∀ z : Z, (ηu - η) z = 0 := by
  have hker : Section1.subgroupInKernel' η Z :=
    theorem_6_8_caseB_mem_Y_subgroupInKernel_Z hB hfamily hηY
  exact ⟨
    theorem_6_8_argumentPow_diff_integerSpanOn_punctured hηY hηuY harg,
    theorem_6_8_subgroupInKernel_argumentPow_diff_vanish hker harg⟩

theorem theorem_6_8_isClassFunction_of_inducedKernelFamily
    {L : Type u} [Group L] [Finite L]
    {H A : Subgroup L} {S : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily H A S)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S) :
    Section1.IsClassFunction χ := by
  rcases (hS.2 χ).mp hχS with
    ⟨θ, _hθirr, _hθker, _hθne, hχeq⟩
  simpa [hχeq] using Section1.inducedCF_isClassFunction H θ

theorem theorem_6_8_zpow_invariance_of_argumentPow_target_diff_zero
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    {η ηu : Section1.ClassFunction L}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {z : Z} {e : ℕ} {n : ℤ}
    (harg :
      Section3.classFunctionArgumentPow (τ₁ η) (τ₁ ηu) e)
    (hpow :
      (((z : L) : G) ^ e) = ((((z ^ n : Z) : L) : G)))
    (hdiff : (τ₁ (ηu - η)) ((z : L) : G) = 0) :
    (τ₁ η) ((((z ^ n : Z) : L) : G)) =
      (τ₁ η) ((z : L) : G) := by
  have hdiff' : (τ₁ ηu - τ₁ η) ((z : L) : G) = 0 := by
    simpa [map_sub] using hdiff
  have hsame : (τ₁ ηu) ((z : L) : G) = (τ₁ η) ((z : L) : G) := by
    simpa using sub_eq_zero.mp hdiff'
  have hargz := harg ((z : L) : G)
  rw [hpow] at hargz
  exact hargz.symm.trans hsame

theorem theorem_6_8_subtype_pow_eq_zpow_of_intModEq
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    (z : Z) {e : ℕ} {n : ℤ}
    (hmod : (e : ℤ) ≡ n [ZMOD orderOf z]) :
    (((z : L) : G) ^ e) = ((((z ^ n : Z) : L) : G)) := by
  have hz : z ^ (e : ℤ) = z ^ n := by
    rw [zpow_eq_zpow_iff_modEq]
    exact hmod
  calc
    (((z : L) : G) ^ e) = (((z ^ (e : ℕ) : Z) : L) : G) := by
      simp
    _ = (((z ^ (e : ℤ) : Z) : L) : G) := by
      simp
    _ = ((((z ^ n : Z) : L) : G)) := by
      rw [hz]

theorem theorem_6_8_caseB_argumentPow_dade_zero_of_mem_A
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {Hfun : G → Subgroup G}
    {hAL : ∀ a ∈ A, a ∈ L}
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {η ηu : Section1.ClassFunction L} {e : ℕ} {z : Z}
    (h22 : Section2.Hypothesis2 A L Hfun)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (hzA : (((z : L) : G)) ∈ A) :
    (Section2.dadeTransform Hfun hAL (ηu - η)) ((z : L) : G) = 0 := by
  have hfamily' := hfamily
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  rcases theorem_6_8_caseB_Y_argumentPow_diff_data
      hB hfamily' hηY hηuY hargSource with
    ⟨_hspan, hvanishZ⟩
  have hηclass : Section1.IsClassFunction η :=
    theorem_6_8_isClassFunction_of_inducedKernelFamily hY hηY
  have hηuclass : Section1.IsClassFunction ηu :=
    theorem_6_8_isClassFunction_of_inducedKernelFamily hY hηuY
  have hdiffclass : Section1.IsClassFunction (ηu - η) :=
    by
      intro x g
      simp [hηuclass x g, hηclass x g]
  have hgpiece :
      ((z : L) : G) ∈
        Section2.conjugateSet
          (Section2.cosetProduct ((z : L) : G) (Hfun ((z : L) : G))) := by
    refine ⟨((z : L) : G), ?_, ?_⟩
    · refine ⟨((z : L) : G), by simp, 1, (Hfun ((z : L) : G)).one_mem, ?_⟩
      simp
    · refine ⟨1, ?_⟩
      simp [Section2.conjBy]
  have hval :
      Section2.dadeTransform Hfun hAL (ηu - η) ((z : L) : G) =
        (ηu - η) ⟨((z : L) : G), hAL ((z : L) : G) hzA⟩ :=
    Section2.dadeTransform_eq_on_conjugateSet_cosetProduct
      A L Hfun h22 hAL (ηu - η) hdiffclass hzA hgpiece
  have hsub :
      (⟨((z : L) : G), hAL ((z : L) : G) hzA⟩ : L) = (z : L) := by
    ext
    rfl
  rw [hval, hsub]
  exact hvanishZ z

theorem theorem_6_8_Y_punctured_span_iff_subgroupImage
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y
          (Section4Scratch.subgroupPullbackSet L (subgroupImagePuncturedSet L H)) χ := by
  intro χ
  constructor
  · intro hχ
    have hYsubS : Y ⊆ S :=
      theorem_6_8_familyData_Y_subset_S hSbot hfamily
    have hχS : Section5.integerSpanOn S Section5.puncturedSet χ :=
      Section5.integerSpanOn_mono hYsubS hχ
    have hχCF : Section2.CFOn L (subgroupImagePuncturedSet L H) χ :=
      theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
        (L := L) (H := H) hSbot hχS
    refine ⟨hχ.1, ?_⟩
    rw [Section1.supportedOn_iff]
    intro l hl
    exact hχCF.2 l (by
      simpa [Section4Scratch.subgroupPullbackSet] using hl)
  · intro hχ
    refine ⟨hχ.1, ?_⟩
    rw [Section1.supportedOn_iff]
    intro l hl
    exact (Section1.supportedOn_iff.mp hχ.2) l (by
      intro hlA
      have hlA' : ((l : L) : G) ∈ subgroupImagePuncturedSet L H := by
        simpa [Section4Scratch.subgroupPullbackSet] using hlA
      have hlne : l ≠ 1 :=
        (theorem_6_8_subgroupImagePuncturedSet_mem_iff L H l).1 hlA' |>.2
      exact hl (by simpa [Section5.puncturedSet] using hlne))

theorem theorem_6_8_hypothesis2_subgroupImagePuncturedSet
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T) :
    Section2.Hypothesis2 (subgroupImagePuncturedSet L H) L (fun _ : G => ⊥) := by
  rcases h68 with
    ⟨_hsemi, _hodd, _hHne, _hnil, hTI, _hSbot, _hT, _hcase⟩
  exact (Section2.proposition_2_3
    (subgroupImagePuncturedSet L H) L hTI.1).1 hTI

theorem theorem_6_8_caseB_z_mem_subgroupImagePuncturedSet
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {z : Z} (hz : z ≠ 1) :
    (((z : L) : G)) ∈ subgroupImagePuncturedSet L H := by
  rcases hfamily with ⟨hZH, _hSZ, _hXeq, _hY⟩
  exact (theorem_6_8_subgroupImagePuncturedSet_mem_iff L H (z : L)).2
    ⟨hZH z.property, by
      intro hzL
      exact hz (Subtype.ext hzL)⟩

theorem theorem_6_8_caseB_Y_dade_agreement_subgroupImage
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hAL : ∀ a ∈ subgroupImagePuncturedSet L H, a ∈ L) :
    ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y
          (Section4Scratch.subgroupPullbackSet L (subgroupImagePuncturedSet L H)) χ →
        τ₁ χ =
          Section2.dadeTransform (fun _ : G => ⊥) hAL χ := by
  intro χ hχA
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, hT, hcase⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, hT, hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hχpunct : Section5.integerSpanOn Y Section5.puncturedSet χ :=
    (theorem_6_8_Y_punctured_span_iff_subgroupImage hSbot hfamily χ).mpr hχA
  have hYsubS : Y ⊆ S :=
    theorem_6_8_familyData_Y_subset_S hSbot hfamily
  have hχS : Section5.integerSpanOn S Section5.puncturedSet χ :=
    Section5.integerSpanOn_mono hYsubS hχpunct
  have hτT : τ₁ χ = T χ := hτ₁.2.2 χ hχpunct
  have hTχ : T χ = Section1.inducedCF L χ := hT χ hχS
  have hHyp2 : Section2.Hypothesis2
      (subgroupImagePuncturedSet L H) L (fun _ : G => ⊥) :=
    theorem_6_8_hypothesis2_subgroupImagePuncturedSet h68'
  have hχCF : Section2.CFOn L (subgroupImagePuncturedSet L H) χ :=
    theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn hSbot hχS
  have hInd :
      Section1.inducedCF L χ =
        Section2.dadeTransform (fun _ : G => ⊥) hAL χ :=
    Section3.inducedCF_eq_dadeTransform_trivial
      (subgroupImagePuncturedSet L H) L hHyp2 hAL χ hχCF
  rw [hτT, hTχ, hInd]

theorem theorem_6_8_argumentPow_target_of_pf59_statement
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {Hfun : G → Subgroup G}
    {hAL : ∀ a ∈ A, a ∈ L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h59 : Section5.theorem_5_9_a_statement A L Hfun hAL Y)
    (h22 : Section2.Hypothesis2 A L Hfun)
    (hIrrY : ∀ X : Section1.ClassFunction L,
      X ∈ Y → Section1.IsIrreducibleCharacterOnGroup X)
    (hSpanEq : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ)
    (hcard : 1 < Y.card)
    (hτ₁ : coherentExtension Y T τ₁)
    (hDade : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ →
        τ₁ χ = Section2.dadeTransform Hfun hAL χ)
    {e : ℕ}
    (he : e.Coprime (Nat.card G))
    (hClosed : ∀ φ : Section1.ClassFunction L,
      φ ∈ Y →
        ∃ φu : Section1.ClassFunction L,
          φu ∈ Y ∧ Section3.classFunctionArgumentPow φ φu e)
    {η ηu : Section1.ClassFunction L}
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e) :
    Section3.classFunctionArgumentPow (τ₁ η) (τ₁ ηu) e := by
  exact h59 h22 hIrrY hSpanEq hcard τ₁ hτ₁.1 hτ₁.2.1 hDade
    he hClosed hηY hηuY hargSource

theorem theorem_6_8_caseB_zpow_invariance_of_argumentPow_step
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η ηu : Section1.ClassFunction L}
    {z : Z} {e : ℕ} {n : ℤ}
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (hargTarget :
      Section3.classFunctionArgumentPow (τ₁ η) (τ₁ ηu) e)
    (hpow :
      (((z : L) : G) ^ e) = ((((z ^ n : Z) : L) : G)))
    (hTzero : (T (ηu - η)) ((z : L) : G) = 0) :
    (τ₁ η) ((((z ^ n : Z) : L) : G)) =
      (τ₁ η) ((z : L) : G) := by
  rcases theorem_6_8_caseB_Y_argumentPow_diff_data
      hB hfamily hηY hηuY hargSource with
    ⟨hspan, _hvanishZ⟩
  have hagree : τ₁ (ηu - η) = T (ηu - η) := hτ₁.2.2 (ηu - η) hspan
  have hdiff : (τ₁ (ηu - η)) ((z : L) : G) = 0 := by
    rw [hagree]
    exact hTzero
  exact theorem_6_8_zpow_invariance_of_argumentPow_target_diff_zero
    hargTarget hpow hdiff

theorem theorem_6_8_Tzero_of_caseB_argumentPow_dade_zero
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {Hfun : G → Subgroup G}
    {hAL : ∀ a ∈ A, a ∈ L}
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η ηu : Section1.ClassFunction L} {e : ℕ} {z : Z}
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (hSpanEq : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ)
    (hDade : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ →
        τ₁ χ = Section2.dadeTransform Hfun hAL χ)
    (hDadeZero :
      (Section2.dadeTransform Hfun hAL (ηu - η)) ((z : L) : G) = 0) :
    (T (ηu - η)) ((z : L) : G) = 0 := by
  rcases theorem_6_8_caseB_Y_argumentPow_diff_data
      hB hfamily hηY hηuY hargSource with
    ⟨hspan, _hvanishZ⟩
  have hspanA :
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A)
        (ηu - η) :=
    (hSpanEq (ηu - η)).mp hspan
  have hτT : τ₁ (ηu - η) = T (ηu - η) := hτ₁.2.2 (ηu - η) hspan
  have hτDade :
      τ₁ (ηu - η) = Section2.dadeTransform Hfun hAL (ηu - η) :=
    hDade (ηu - η) hspanA
  have hTDade :
      T (ηu - η) = Section2.dadeTransform Hfun hAL (ηu - η) := by
    rw [← hτT, hτDade]
  rw [hTDade]
  exact hDadeZero

theorem theorem_6_8_Tzero_of_caseB_argumentPow_mem_A
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {Hfun : G → Subgroup G}
    {hAL : ∀ a ∈ A, a ∈ L}
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η ηu : Section1.ClassFunction L} {e : ℕ} {z : Z}
    (h22 : Section2.Hypothesis2 A L Hfun)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (hSpanEq : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ)
    (hDade : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ →
        τ₁ χ = Section2.dadeTransform Hfun hAL χ)
    (hzA : (((z : L) : G)) ∈ A) :
    (T (ηu - η)) ((z : L) : G) = 0 := by
  exact theorem_6_8_Tzero_of_caseB_argumentPow_dade_zero
    hB hfamily hτ₁ hηY hηuY hargSource hSpanEq hDade
    (theorem_6_8_caseB_argumentPow_dade_zero_of_mem_A
      h22 hB hfamily hηY hηuY hargSource hzA)

theorem theorem_6_8_caseB_zpow_invariance_of_pf59_step
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {Hfun : G → Subgroup G}
    {hAL : ∀ a ∈ A, a ∈ L}
    {H W2 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η ηu : Section1.ClassFunction L}
    {z : Z} {e : ℕ} {n : ℤ}
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (h59 : Section5.theorem_5_9_a_statement A L Hfun hAL Y)
    (h22 : Section2.Hypothesis2 A L Hfun)
    (hIrrY : ∀ X : Section1.ClassFunction L,
      X ∈ Y → Section1.IsIrreducibleCharacterOnGroup X)
    (hSpanEq : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ)
    (hcard : 1 < Y.card)
    (hDade : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ →
        τ₁ χ = Section2.dadeTransform Hfun hAL χ)
    (he : e.Coprime (Nat.card G))
    (hClosed : ∀ φ : Section1.ClassFunction L,
      φ ∈ Y →
        ∃ φu : Section1.ClassFunction L,
          φu ∈ Y ∧ Section3.classFunctionArgumentPow φ φu e)
    (hmod : (e : ℤ) ≡ n [ZMOD orderOf z])
    (hTzero : (T (ηu - η)) ((z : L) : G) = 0) :
    (τ₁ η) ((((z ^ n : Z) : L) : G)) =
      (τ₁ η) ((z : L) : G) := by
  have hargTarget :
      Section3.classFunctionArgumentPow (τ₁ η) (τ₁ ηu) e :=
    theorem_6_8_argumentPow_target_of_pf59_statement
      h59 h22 hIrrY hSpanEq hcard hτ₁ hDade he hClosed
      hηY hηuY hargSource
  have hpow :
      (((z : L) : G) ^ e) = ((((z ^ n : Z) : L) : G)) :=
    theorem_6_8_subtype_pow_eq_zpow_of_intModEq z hmod
  exact theorem_6_8_caseB_zpow_invariance_of_argumentPow_step
    hB hfamily hτ₁ hηY hηuY hargSource hargTarget hpow hTzero

theorem theorem_6_8_2_1_constantOn_image_subgroup_of_statement
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h821 : theorem_6_8_2_1_statement L H W1 W2 W Z S SZ X Y T τ₁)
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    constantOnNonidentitySubgroup (Z.map L.subtype) (τ₁ η) := by
  exact theorem_6_8_constantOnSubgroupImageNonidentity_map_subtype
    (h821 h68 hpQ hcase hB hfamily hτ₁ η hηY)

theorem theorem_6_8_2_2_restriction_regular_add_of_821_statement
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h821 : theorem_6_8_2_1_statement L H W1 W2 W Z S SZ X Y T τ₁)
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
        a • regularCharacter (Z.map L.subtype) +
          b • Section1.principalCharacter (Z.map L.subtype) := by
  rcases hB with ⟨hW2ne, hW2center, hW2comm, hZeq⟩
  subst Z
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨z, hz⟩
  let zG : W2.map L.subtype :=
    ⟨((z : L) : G), ⟨z, z.property, rfl⟩⟩
  have hzG : zG ≠ 1 := by
    intro hzG
    apply hz
    ext
    simpa [zG] using congrArg Subtype.val hzG
  exact constantOnNonidentitySubgroup_restriction_eq_regular_add
    (theorem_6_8_2_1_constantOn_image_subgroup_of_statement
      h821 h68 hpQ hcase
      (show theorem_6_8_caseBData H W2 W2 from
        ⟨hW2ne, hW2center, hW2comm, rfl⟩)
      hfamily hτ₁ hηY)
    zG hzG


theorem theorem_6_8_centerIn_normal_of_normal
    {L : Type u} [Group L] {H : Subgroup L} [H.Normal] :
    (centerIn H).Normal := by
  refine Subgroup.Normal.mk ?_
  intro z hz g
  rcases hz with ⟨hzH, hzcent⟩
  constructor
  · exact (inferInstance : H.Normal).conj_mem z hzH g
  · change g * z * g⁻¹ ∈ Subgroup.centralizer (H : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro h hhH
    have hzcent' : z ∈ Subgroup.centralizer (H : Set L) := hzcent
    rw [Subgroup.mem_centralizer_iff] at hzcent'
    have hpreH : g⁻¹ * h * g ∈ H := by
      have hconj : g⁻¹ * h * (g⁻¹)⁻¹ ∈ H :=
        (inferInstance : H.Normal).conj_mem h hhH g⁻¹
      simpa using hconj
    have hzcomm := hzcent' (g⁻¹ * h * g) hpreH
    calc
      h * (g * z * g⁻¹) = g * (g⁻¹ * h * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hzcomm]
      _ = (g * z * g⁻¹) * h := by group

theorem theorem_6_8_commutator_ne_bot_of_nonabelianPQuotient_bot
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) :
    commutator H ≠ ⊥ := by
  rcases hpQ with
    ⟨_p, _hbotH, _hbotNormH, _hbotNorm, _hHnorm, _hp, _hpgroup, hnoncomm⟩
  intro hcommbot
  have hcenter : Subgroup.center H = ⊤ := by
    rwa [commutator_eq_bot_iff_center_eq_top] at hcommbot
  let : CommGroup H := Group.commGroupOfCenterEqTop hcenter
  apply hnoncomm
  refine ⟨Std.Commutative.mk ?_⟩
  intro a b
  refine QuotientGroup.induction_on a ?_
  intro x
  refine QuotientGroup.induction_on b ?_
  intro y
  let M : Subgroup H := (⊥ : Subgroup L).subgroupOf H
  change (QuotientGroup.mk' M) x * (QuotientGroup.mk' M) y =
    (QuotientGroup.mk' M) y * (QuotientGroup.mk' M) x
  simp [mul_comm]

theorem theorem_6_8_caseA_Z_ne_bot
    {L : Type u} [Group L] [Finite L]
    {H W2 Z : Subgroup L}
    (hnil : Group.IsNilpotent H)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z) :
    Z ≠ ⊥ := by
  rcases hA with ⟨_hcenterW2, hZeq⟩
  subst Z
  have : Group.IsNilpotent H := hnil
  have hcomm_ne : commutator H ≠ ⊥ :=
    theorem_6_8_commutator_ne_bot_of_nonabelianPQuotient_bot hpQ
  let N : Subgroup H := commutator H
  have : N.Normal := by
    dsimp [N]
    infer_instance
  have hInf_ne : N ⊓ Subgroup.center H ≠ ⊥ :=
    nilpotent_normal_inf_center_ne_bot N (by simpa [N] using hcomm_ne)
  intro hbot
  apply hInf_ne
  rw [eq_bot_iff]
  intro x hx
  have hxcomm_ambient : (x : L) ∈ ⁅H,H⁆ := by
    have hxmap : (x : L) ∈ (commutator H).map H.subtype :=
      ⟨x, by simpa [N] using hx.1, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at hxmap
  have hxcenter_ambient : (x : L) ∈ centerIn H := by
    constructor
    · exact x.2
    · change (x : L) ∈ Subgroup.centralizer (H : Set L)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyH
      have hxy := (Subgroup.mem_center_iff.mp hx.2) ⟨y, hyH⟩
      exact congrArg Subtype.val hxy
  have hxinf : (x : L) ∈ centerIn H ⊓ ⁅H,H⁆ :=
    ⟨hxcenter_ambient, hxcomm_ambient⟩
  have hxbot : (x : L) ∈ (⊥ : Subgroup L) := by
    rwa [hbot] at hxinf
  have hxambient_one : (x : L) = 1 := by simpa using hxbot
  exact Subtype.ext hxambient_one

theorem theorem_6_8_caseA_Z_center_normal
    {L : Type u} [Group L]
    {H W2 Z : Subgroup L} [H.Normal]
    (hA : theorem_6_8_caseAData H W2 Z) :
    Z ≤ centerIn H ∧ Z.Normal := by
  rcases hA with ⟨_hcenterW2, hZeq⟩
  subst Z
  constructor
  · exact inf_le_left
  · have : (centerIn H).Normal := theorem_6_8_centerIn_normal_of_normal
    have : ⁅H,H⁆.Normal := Subgroup.commutator_normal H H
    exact Subgroup.normal_inf_normal (centerIn H) ⁅H,H⁆

theorem theorem_6_8_caseB_Z_center_normal_ne_bot
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcaseC2 : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    Z ≠ ⊥ ∧ Z ≤ centerIn H ∧ Z.Normal := by
  classical
  rcases hB with ⟨hW2ne, hW2center, _hW2comm, hZeq⟩
  subst Z
  refine ⟨hW2ne, hW2center, ?_⟩
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, _hcase⟩
  rcases hcaseC2 with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      _hcentW1, _hW1W, _hW2W, hdirect, _hWodd⟩
  refine Subgroup.Normal.mk ?_
  intro z hzW2 g
  rcases hsemi.mul_surjective g trivial with ⟨h, hhH, w, hwW1, hg⟩
  have hzw : w * z * w⁻¹ = z := by
    have hcomm : w * z = z * w := hdirect.commute w hwW1 z hzW2
    calc
      w * z * w⁻¹ = z * w * w⁻¹ := by rw [hcomm]
      _ = z := by simp [mul_assoc]
  have hhz : h * z * h⁻¹ = z := by
    have hzcent : z ∈ centerIn H := hW2center hzW2
    have hzcentralizer : z ∈ Subgroup.centralizer (H : Set L) := hzcent.2
    rw [Subgroup.mem_centralizer_iff] at hzcentralizer
    have hcomm : h * z = z * h := hzcentralizer h hhH
    calc
      h * z * h⁻¹ = z * h * h⁻¹ := by rw [hcomm]
      _ = z := by simp [mul_assoc]
  have hconj_eq : g * z * g⁻¹ = z := by
    rw [hg]
    calc
      h * w * z * (h * w)⁻¹ = h * (w * z * w⁻¹) * h⁻¹ := by group
      _ = h * z * h⁻¹ := by rw [hzw]
      _ = z := hhz
  simpa [hconj_eq] using hzW2

theorem theorem_6_8_inducing_character_not_Z_kernel_of_mem_X
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχX : χ ∈ X) :
    ∃ θ : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ¬ Section1.subgroupInKernel' θ (Z.subgroupOf H) ∧
          θ ≠ Section1.principalCharacter H ∧
            χ = Section1.inducedCF H θ := by
  classical
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hbranch⟩
  rcases hfamily with ⟨hZH, hSZ, hXeq, hY⟩
  have hχS : χ ∈ S := theorem_6_8_familyData_X_subset_S
    (H := H) (Z := Z) (SZ := SZ) (X := X) (Y := Y)
    ⟨hZH, hSZ, hXeq, hY⟩ hχX
  have hχnotSZ : χ ∉ SZ := by
    have hχdiff : χ ∈ S \ SZ := by
      simpa [hXeq] using hχX
    exact (Finset.mem_sdiff.mp hχdiff).2
  rcases (hSbot.2 χ).mp hχS with ⟨θ, hθirr, _hθbot, hθne, hχeq⟩
  have hθnotZ :
      ¬ Section1.subgroupInKernel' θ (Z.subgroupOf H) := by
    intro hθZ
    exact hχnotSZ ((hSZ.2 χ).mpr ⟨θ, hθirr, hθZ, hθne, hχeq⟩)
  exact ⟨θ, hθirr, hθnotZ, hθne, hχeq⟩

theorem theorem_6_8_restriction_smul_nonprincipal_of_not_Z_kernel
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {θ : Section1.ClassFunction H}
    {φ : Section1.ClassFunction Z}
    (hθnotZ : ¬ Section1.subgroupInKernel' θ (Z.subgroupOf H))
    (hres : Section1.subgroupRestriction (Z.subgroupOf H) θ =
      Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ) :
    φ ≠ Section1.principalCharacter Z := by
  intro hφ
  apply hθnotZ
  intro z
  have hz := congrFun hres z
  rw [hφ] at hz
  simpa [Section1.subgroupRestriction, Section1.subgroupOfClassFunction,
    Section1.principalCharacter] using hz

theorem theorem_6_8_not_subgroupInKernel_of_restriction_eq_nonprincipal
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZH : Z ≤ H)
    {ψ : Section1.ClassFunction H} {φ : Section1.ClassFunction Z}
    {e : ℕ}
    (hdegree : Section1.degree ψ = (e : ℂ))
    (he : e ≠ 0)
    (hφne : φ ≠ Section1.principalCharacter Z)
    (hres : Section1.subgroupRestriction (Z.subgroupOf H) ψ =
      (e : ℂ) • Section1.subgroupOfClassFunction (T := H) φ) :
    ¬ Section1.subgroupInKernel' ψ (Z.subgroupOf H) := by
  intro hker
  apply hφne
  ext z
  let zH : Z.subgroupOf H := ⟨⟨(z : L), hZH z.2⟩, z.2⟩
  have hpoint := congrFun hres zH
  have hkerz : ψ (zH : H) = Section1.degree ψ := hker zH
  have hec : (e : ℂ) ≠ 0 := by
    exact_mod_cast he
  have hphi : φ z = 1 := by
    have hmul : (e : ℂ) * φ z = (e : ℂ) := by
      simpa [Section1.subgroupRestriction, Section1.subgroupOfClassFunction,
        hkerz, hdegree, zH] using hpoint.symm
    exact (mul_right_inj' hec).mp (by simpa [mul_comm] using hmul)
  simp [Section1.principalCharacter, hphi]

set_option backward.isDefEq.respectTransparency false in
theorem theorem_6_8_center_restriction_smul_of_irreducible
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H)
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ) :
    ∃ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ ∧
        Section1.subgroupRestriction (Z.subgroupOf H) θ =
          Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ := by
  classical
  have hZH : Z ≤ H := fun z hz => (hZcent hz).1
  rcases hθ with ⟨n, ρ, hρirr, hθeq⟩
  have : Representation.IsIrreducible ρ := hρirr
  have : Nontrivial (Fin n → ℂ) := Theory.Character.irreducible_nontrivial (ρ := ρ)
  have hdim_ne : ((Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0) := by
    have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
    exact_mod_cast Nat.ne_of_gt hdim_pos
  let zToH : Z → H := fun z => ⟨(z : L), hZH z.2⟩
  have hcenterH : ∀ z : Z, zToH z ∈ Subgroup.center H := by
    intro z
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hzcent : (z : L) ∈ centerIn H := hZcent z.2
    have hzcentralizer : (z : L) ∈ Subgroup.centralizer (H : Set L) :=
      hzcent.2
    rw [Subgroup.mem_centralizer_iff] at hzcentralizer
    exact hzcentralizer (y : L) y.2
  have hscalar_exists : ∀ z : Z,
      ∃ a : ℂ, (ρ (zToH z) : Module.End ℂ (Fin n → ℂ)) =
        a • (1 : Module.End ℂ (Fin n → ℂ)) := by
    intro z
    let φc := Representation.IntertwiningMap.centralMul (ρ := ρ) (zToH z)
      (by
        rw [Submonoid.mem_center_iff]
        intro y
        exact (Subgroup.mem_center_iff.mp (hcenterH z)) y)
    obtain ⟨a, ha⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).surjective φc
    refine ⟨a, ?_⟩
    have hlin :
        ((algebraMap ℂ (Representation.IntertwiningMap ρ ρ) a :
            Representation.IntertwiningMap ρ ρ) : Module.End ℂ (Fin n → ℂ)) =
          (φc : Module.End ℂ (Fin n → ℂ)) := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ =>
        (f : Module.End ℂ (Fin n → ℂ))) ha
    calc
      (ρ (zToH z) : Module.End ℂ (Fin n → ℂ)) =
          (φc : Module.End ℂ (Fin n → ℂ)) := rfl
      _ = ((algebraMap ℂ (Representation.IntertwiningMap ρ ρ) a :
          Representation.IntertwiningMap ρ ρ) :
            Module.End ℂ (Fin n → ℂ)) := hlin.symm
      _ = a • (1 : Module.End ℂ (Fin n → ℂ)) := by
        rw [Representation.IntertwiningMap.algebraMap_apply]
        change (a • (1 : Representation.IntertwiningMap ρ ρ)).toLinearMap =
          a • (1 : Module.End ℂ (Fin n → ℂ))
        rw [Representation.IntertwiningMap.toLinearMap_smul]
        congr 1
  let scalar : Z → ℂ := fun z => Classical.choose (hscalar_exists z)
  have hscalar_spec : ∀ z : Z,
      (ρ (zToH z) : Module.End ℂ (Fin n → ℂ)) =
        scalar z • (1 : Module.End ℂ (Fin n → ℂ)) := by
    intro z
    exact Classical.choose_spec (hscalar_exists z)
  have hscalar_eq_of_smul_one_eq : ∀ {a b : ℂ},
      a • (1 : Module.End ℂ (Fin n → ℂ)) =
        b • (1 : Module.End ℂ (Fin n → ℂ)) → a = b := by
    intro a b h
    have htrace := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) h
    have hcalc : a * (Module.finrank ℂ (Fin n → ℂ) : ℂ) =
        b * (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
      simpa [LinearMap.trace_id] using htrace
    exact mul_right_cancel₀ hdim_ne hcalc
  have hscalar_one : scalar 1 = 1 := by
    apply hscalar_eq_of_smul_one_eq
    have hspec := hscalar_spec (1 : Z)
    have hz : zToH (1 : Z) = 1 := by
      ext
      rfl
    simpa [hz] using hspec.symm
  have hscalar_mul : ∀ x y : Z, scalar (x * y) = scalar x * scalar y := by
    intro x y
    apply hscalar_eq_of_smul_one_eq
    have hxy : zToH (x * y) = zToH x * zToH y := by
      ext
      rfl
    calc
      scalar (x * y) • (1 : Module.End ℂ (Fin n → ℂ)) =
          ρ (zToH (x * y)) :=
        (hscalar_spec (x * y)).symm
      _ = ρ (zToH x * zToH y) := by rw [hxy]
      _ = ρ (zToH x) * ρ (zToH y) := by
            exact map_mul ρ (zToH x) (zToH y)
      _ = (scalar x • (1 : Module.End ℂ (Fin n → ℂ))) *
          (scalar y • (1 : Module.End ℂ (Fin n → ℂ))) := by
            rw [hscalar_spec x, hscalar_spec y]
      _ = (scalar x * scalar y) • (1 : Module.End ℂ (Fin n → ℂ)) := by
            ext v i
            simp [mul_smul, mul_assoc, mul_comm, mul_left_comm]
  have hscalar_ne_zero : ∀ z : Z, scalar z ≠ 0 := by
    intro z hz
    have hmul := hscalar_mul z z⁻¹
    have hzero : (1 : ℂ) = 0 := by
      simp [hscalar_one, hz] at hmul
    exact one_ne_zero hzero
  let lambda : Z →* ℂˣ :=
    { toFun := fun z => Units.mk0 (scalar z) (hscalar_ne_zero z)
      map_one' := by
        ext
        exact hscalar_one
      map_mul' := by
        intro x y
        ext
        exact hscalar_mul x y }
  let φ : Section1.ClassFunction Z :=
    Section1.characterInflationByHom (MonoidHom.id Z) lambda
  have hφirr : Section1.IsIrreducibleCharacterOnGroup φ := by
    simpa [φ] using
      characterInflationByHom_isIrreducibleCharacterOnGroup (MonoidHom.id Z) lambda
  refine ⟨φ, hφirr, ?_⟩
  ext z
  let zZ : Z := ⟨((z : Z.subgroupOf H) : H), z.2⟩
  have hzToH : zToH zZ = (z : H) := by
    ext
    rfl
  have hdeg : Section1.degree θ = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    rw [hθeq, Section1.degree_representation_character]
  have htrace : θ (z : H) =
      scalar zZ * (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    rw [hθeq]
    rw [← hzToH]
    rw [Representation.character, hscalar_spec zZ]
    simp
  have hright :
      (Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ) z =
        (Module.finrank ℂ (Fin n → ℂ) : ℂ) * scalar zZ := by
    change Section1.degree θ * φ zZ =
      (Module.finrank ℂ (Fin n → ℂ) : ℂ) * scalar zZ
    rw [hdeg]
    change (Module.finrank ℂ (Fin n → ℂ) : ℂ) * (lambda zZ : ℂ) =
      (Module.finrank ℂ (Fin n → ℂ) : ℂ) * scalar zZ
    simp [lambda]
  calc
    Section1.subgroupRestriction (Z.subgroupOf H) θ z = θ (z : H) := by
      rfl
    _ = scalar zZ * (Module.finrank ℂ (Fin n → ℂ) : ℂ) := htrace
    _ = (Module.finrank ℂ (Fin n → ℂ) : ℂ) * scalar zZ := by ring
    _ = (Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ) z :=
      hright.symm

theorem theorem_6_8_center_restriction_nonprincipal_of_not_Z_kernel
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H)
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotZ : ¬ Section1.subgroupInKernel' θ (Z.subgroupOf H)) :
    ∃ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ ∧
        φ ≠ Section1.principalCharacter Z ∧
          Section1.subgroupRestriction (Z.subgroupOf H) θ =
            Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ := by
  rcases theorem_6_8_center_restriction_smul_of_irreducible hZcent hθ with
    ⟨φ, hφ, hres⟩
  exact ⟨φ, hφ,
    theorem_6_8_restriction_smul_nonprincipal_of_not_Z_kernel hθnotZ hres,
    hres⟩

theorem theorem_6_8_degree_ratio_eq_of_induced_from_H
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction H}
    (hχeq : χ = Section1.inducedCF H θ) :
    Section1.degree χ / (Nat.card W1 : ℂ) = Section1.degree θ := by
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
    simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hdeg : Section1.degree χ = (Nat.card W1 : ℂ) * Section1.degree θ := by
    rw [hχeq, Section1.degree_inducedClassFunction H θ]
    rw [Subgroup.relIndex_top_right] at hHindex
    rw [hHindex]
  have hW1card_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.card_pos (α := W1)))
  rw [hdeg]
  field_simp [hW1card_ne]

theorem theorem_6_8_scalarProduct_induced_subgroup_eq_degree_of_restriction
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZH : Z ≤ H)
    {θ : Section1.ClassFunction H} {φ : Section1.ClassFunction Z}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hres : Section1.subgroupRestriction (Z.subgroupOf H) θ =
      Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ) :
    Section1.scalarProduct H
      (Section1.inducedCF (Z.subgroupOf H)
        (Section1.subgroupOfClassFunction (T := H) φ)) θ =
      Section1.degree θ := by
  have hθclass : Section1.IsClassFunction θ := by
    rcases hθ with ⟨_n, ρ, _hρ, hθeq⟩
    intro x g
    rw [hθeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hfrob := Section1.inducedClassFunction_frobenius_general
    (Z.subgroupOf H) (Section1.subgroupOfClassFunction (T := H) φ) θ hθclass
  rw [hfrob, hres, Section1.scalarProduct_smul_right]
  rw [Section1.scalarProduct_subgroupOfClassFunction hZH]
  have hφself : Section1.scalarProduct Z φ φ = 1 := by
    rcases hφ with ⟨_n, ρ, hρirr, hφeq⟩
    rw [hφeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hstar : star (Section1.degree θ) = Section1.degree θ := by
    rcases hθ with ⟨_n, ρ, _hρirr, hθeq⟩
    rw [hθeq, Section1.degree_representation_character]
    simp
  rw [hφself, hstar]
  simp

theorem theorem_6_8_selected_coeff_eq_degree_of_restriction_decomposition
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZH : Z ≤ H)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H) (i0 : ι)
    {θ : Section1.ClassFunction H} {φ : Section1.ClassFunction Z}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hres : Section1.subgroupRestriction (Z.subgroupOf H) θ =
      Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ)
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (horth : ∀ i j : ι,
      Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0)
    (hi0 : ψ i0 = θ) :
    (e i0 : ℂ) = Section1.degree θ := by
  have hcoeff := theorem_6_8_scalarProduct_induced_subgroup_eq_degree_of_restriction
    hZH hθ hφ hres
  calc
    (e i0 : ℂ) =
        Section1.scalarProduct H (Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
          (ψ i0) := by
          exact (Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (fun i => (e i : ℂ)) ψ horth i0).symm
    _ = Section1.scalarProduct H
        (Section1.inducedCF (Z.subgroupOf H)
          (Section1.subgroupOfClassFunction (T := H) φ)) θ := by
          rw [← hdecomp, hi0]
    _ = Section1.degree θ := hcoeff

theorem theorem_6_8_degree_eq_coeff_of_nonzero_central_decomposition
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i))
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (horth : ∀ i j : ι,
      Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0)
    (i : ι) (hei : e i ≠ 0) :
    Section1.degree (ψ i) = (e i : ℂ) := by
  classical
  have hZH : Z ≤ H := by
    intro z hz
    exact (show z ∈ H ∧ z ∈ Subgroup.centralizer (H : Set L) from by
      simpa [centerIn] using hZcent hz).1
  have hψclass : Section1.IsClassFunction (ψ i) := by
    rcases hψirr i with ⟨_n, ρ, _hρirr, hψeq⟩
    intro x g
    rw [hψeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hcoeff :
      Section1.scalarProduct H
          (Section1.inducedCF (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ)) (ψ i) =
        (e i : ℂ) :=
    Section1.proposition_1_7_multiplicity_from_decomposition e ψ
      (Section1.inducedCF (Z.subgroupOf H)
        (Section1.subgroupOfClassFunction (T := H) φ))
      horth hdecomp i
  rcases theorem_6_8_center_restriction_smul_of_irreducible
      hZcent (hψirr i) with
    ⟨φi, hφi, hresψ⟩
  have hφi_eq : φi = φ := by
    by_contra hne
    have hscalar0 : Section1.scalarProduct Z φ φi = 0 := by
      rcases hφ with ⟨_nφ, ρφ, hρφ, hφeq⟩
      rcases hφi with ⟨_nφi, ρφi, hρφi, hφieq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        φ φi ρφ ρφi hφeq hφieq hρφ hρφi
        (by intro h; exact hne h.symm)
    have hcoeff0 : (e i : ℂ) = 0 := by
      calc
        (e i : ℂ) =
            Section1.scalarProduct H
              (Section1.inducedCF (Z.subgroupOf H)
                (Section1.subgroupOfClassFunction (T := H) φ)) (ψ i) :=
          hcoeff.symm
        _ = Section1.scalarProduct (Z.subgroupOf H)
              (Section1.subgroupOfClassFunction (T := H) φ)
              (Section1.subgroupRestriction (Z.subgroupOf H) (ψ i)) := by
          rw [Section1.inducedClassFunction_frobenius_general
            (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ)
            (ψ i) hψclass]
        _ = 0 := by
          rw [hresψ, Section1.scalarProduct_smul_right]
          rw [Section1.scalarProduct_subgroupOfClassFunction hZH]
          rw [hscalar0]
          simp
    have hei0 : e i = 0 := by
      exact_mod_cast hcoeff0
    exact hei hei0
  have hφself : Section1.scalarProduct Z φ φ = 1 := by
    rcases hφ with ⟨_n, ρ, hρirr, hφeq⟩
    rw [hφeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hstar : star (Section1.degree (ψ i)) = Section1.degree (ψ i) := by
    rcases hψirr i with ⟨_n, ρ, _hρirr, hψeq⟩
    rw [hψeq, Section1.degree_representation_character]
    simp
  have hcoeff_degree : (e i : ℂ) = Section1.degree (ψ i) := by
    calc
      (e i : ℂ) =
          Section1.scalarProduct H
            (Section1.inducedCF (Z.subgroupOf H)
              (Section1.subgroupOfClassFunction (T := H) φ)) (ψ i) :=
        hcoeff.symm
      _ = Section1.scalarProduct (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ)
            (Section1.subgroupRestriction (Z.subgroupOf H) (ψ i)) := by
        rw [Section1.inducedClassFunction_frobenius_general
          (Z.subgroupOf H)
          (Section1.subgroupOfClassFunction (T := H) φ)
          (ψ i) hψclass]
      _ = Section1.degree (ψ i) := by
        rw [hresψ, Section1.scalarProduct_smul_right]
        rw [Section1.scalarProduct_subgroupOfClassFunction hZH]
        rw [hφi_eq, hφself, hstar]
        simp
  exact hcoeff_degree.symm

theorem theorem_6_8_restriction_eq_coeff_smul_of_nonzero_central_decomposition
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i))
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (horth : ∀ i j : ι,
      Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0)
    (i : ι) (hei : e i ≠ 0) :
    Section1.subgroupRestriction (Z.subgroupOf H) (ψ i) =
      (e i : ℂ) • Section1.subgroupOfClassFunction (T := H) φ := by
  classical
  have hZH : Z ≤ H := by
    intro z hz
    exact (show z ∈ H ∧ z ∈ Subgroup.centralizer (H : Set L) from by
      simpa [centerIn] using hZcent hz).1
  have hψclass : Section1.IsClassFunction (ψ i) := by
    rcases hψirr i with ⟨_n, ρ, _hρirr, hψeq⟩
    intro x g
    rw [hψeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hcoeff :
      Section1.scalarProduct H
          (Section1.inducedCF (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ)) (ψ i) =
        (e i : ℂ) :=
    Section1.proposition_1_7_multiplicity_from_decomposition e ψ
      (Section1.inducedCF (Z.subgroupOf H)
        (Section1.subgroupOfClassFunction (T := H) φ))
      horth hdecomp i
  rcases theorem_6_8_center_restriction_smul_of_irreducible
      hZcent (hψirr i) with
    ⟨φi, hφi, hresψ⟩
  have hφi_eq : φi = φ := by
    by_contra hne
    have hscalar0 : Section1.scalarProduct Z φ φi = 0 := by
      rcases hφ with ⟨_nφ, ρφ, hρφ, hφeq⟩
      rcases hφi with ⟨_nφi, ρφi, hρφi, hφieq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        φ φi ρφ ρφi hφeq hφieq hρφ hρφi
        (by intro h; exact hne h.symm)
    have hcoeff0 : (e i : ℂ) = 0 := by
      calc
        (e i : ℂ) =
            Section1.scalarProduct H
              (Section1.inducedCF (Z.subgroupOf H)
                (Section1.subgroupOfClassFunction (T := H) φ)) (ψ i) :=
          hcoeff.symm
        _ = Section1.scalarProduct (Z.subgroupOf H)
              (Section1.subgroupOfClassFunction (T := H) φ)
              (Section1.subgroupRestriction (Z.subgroupOf H) (ψ i)) := by
          rw [Section1.inducedClassFunction_frobenius_general
            (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ)
            (ψ i) hψclass]
        _ = 0 := by
          rw [hresψ, Section1.scalarProduct_smul_right]
          rw [Section1.scalarProduct_subgroupOfClassFunction hZH]
          rw [hscalar0]
          simp
    have hei0 : e i = 0 := by
      exact_mod_cast hcoeff0
    exact hei hei0
  have hdegree : Section1.degree (ψ i) = (e i : ℂ) :=
    theorem_6_8_degree_eq_coeff_of_nonzero_central_decomposition
      hZcent e ψ hφ hψirr hdecomp horth i hei
  rw [hresψ, hφi_eq, hdegree]

theorem theorem_6_8_induced_constituent_mem_X_of_nonzero_central_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    (hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i))
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (horth : ∀ i j : ι,
      Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0)
    (i : ι) (hei : e i ≠ 0) :
    Section1.inducedCF H (ψ i) ∈ X := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  rcases hfamily with ⟨hZH, hSZ, hXeq, _hY⟩
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68' hcase hB with
    ⟨_hZne, hZcent, hZnorm⟩
  have : Z.Normal := hZnorm
  have hdegree : Section1.degree (ψ i) = (e i : ℂ) :=
    theorem_6_8_degree_eq_coeff_of_nonzero_central_decomposition
      hZcent e ψ hφ hψirr hdecomp horth i hei
  have hres :
      Section1.subgroupRestriction (Z.subgroupOf H) (ψ i) =
        (e i : ℂ) • Section1.subgroupOfClassFunction (T := H) φ :=
    theorem_6_8_restriction_eq_coeff_smul_of_nonzero_central_decomposition
      hZcent e ψ hφ hψirr hdecomp horth i hei
  have hψnotZ : ¬ Section1.subgroupInKernel' (ψ i) (Z.subgroupOf H) :=
    theorem_6_8_not_subgroupInKernel_of_restriction_eq_nonprincipal
      hZH hdegree hei hφne hres
  have hψne : ψ i ≠ Section1.principalCharacter H := by
    intro hprincipal
    apply hψnotZ
    intro z
    simp [hprincipal, Section1.degree]
  have hψbot :
      Section1.subgroupInKernel' (ψ i) ((⊥ : Subgroup L).subgroupOf H) := by
    intro a
    have haL : (((a : (⊥ : Subgroup L).subgroupOf H) : H) : L) = 1 := by
      have hmem :
          (((a : (⊥ : Subgroup L).subgroupOf H) : H) : L) ∈
            (⊥ : Subgroup L) :=
        Subgroup.mem_subgroupOf.mp a.2
      simpa using hmem
    have haH : (a : H) = 1 := Subtype.ext haL
    simp [Section1.degree, haH]
  have hIndS : Section1.inducedCF H (ψ i) ∈ S :=
    (hSbot.2 (Section1.inducedCF H (ψ i))).mpr
      ⟨ψ i, hψirr i, hψbot, hψne, rfl⟩
  have hIndNotZ :
      ¬ Section1.subgroupInKernel' (Section1.inducedCF H (ψ i)) Z := by
    intro hIndZ
    apply hψnotZ
    rcases hψirr i with ⟨n, ρ, _hρirr, hψeq⟩
    have hρIndZ :
        Section1.subgroupInKernel' (Section1.inducedCF H ρ.character) Z := by
      simpa [hψeq] using hIndZ
    have hρZ : Section1.subgroupInKernel' ρ.character (Z.subgroupOf H) :=
      (Section1.proposition_1_6_a H Z hZH ρ).mpr hρIndZ
    simpa [hψeq] using hρZ
  exact theorem_6_6_mem_Xset_of_mem_S_not_subgroupInKernel
    hZnorm hZH hSZ hXeq hIndS hIndNotZ

theorem theorem_6_8_center_restriction_nonprincipal_of_mem_X_caseB
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχX : χ ∈ X) :
    ∃ θ : Section1.ClassFunction H,
      ∃ φ : Section1.ClassFunction Z,
          Section1.IsIrreducibleCharacterOnGroup θ ∧
          Section1.IsIrreducibleCharacterOnGroup φ ∧
            φ ≠ Section1.principalCharacter Z ∧
              χ = Section1.inducedCF H θ ∧
                Section1.degree χ / (Nat.card W1 : ℂ) =
                  Section1.degree θ ∧
                  Section1.subgroupRestriction (Z.subgroupOf H) θ =
                    Section1.degree θ •
                      Section1.subgroupOfClassFunction (T := H) φ := by
  rcases theorem_6_8_inducing_character_not_Z_kernel_of_mem_X
      h68 hfamily hχX with
    ⟨θ, hθ, hθnotZ, _hθne, hχeq⟩
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68 hcase hB with
    ⟨_hZne, hZcent, _hZnorm⟩
  rcases theorem_6_8_center_restriction_nonprincipal_of_not_Z_kernel
      hZcent hθ hθnotZ with
    ⟨φ, hφ, hφne, hres⟩
  exact ⟨θ, φ, hθ, hφ, hφne, hχeq,
    theorem_6_8_degree_ratio_eq_of_induced_from_H h68.1 hχeq, hres⟩


theorem theorem_6_8_theorem_6_7_base_hypothesis_ambient_card_of_caseB
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    {p : ℕ} [Fact p.Prime]
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    ∃ P : Sylow p G,
      theorem_6_7_base_hypothesis p P L (Z.map L.subtype) ∧
        Nat.card (P : Subgroup G) =
          Nat.card (Z.map L.subtype) * Z.relIndex H := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases theorem_6_8_sylow_of_nonabelianPQuotient_bot h68' hpQ with
    ⟨PL, hPL⟩
  have hnormHmap :
      Subgroup.normalizer (((H.map L.subtype : Subgroup G) : Set G)) = L := by
    rw [theorem_6_8_normalizer_map_subtype_eq_setNormalizer_punctured]
    exact hTI.2.2.2
  rcases theorem_6_8_sylow_map_subtype_of_sylow_normalizer PL hPL hnormHmap with
    ⟨Pamb, hPamb⟩
  refine ⟨Pamb, ?_, ?_⟩
  · rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68' hcase hB with
      ⟨hZne, hZcent, hZnorm⟩
    have : Z.Normal := hZnorm
    have hZprimeMap : Nat.Prime (Nat.card (Z.map L.subtype)) := by
      have hcard : Nat.card (Z.map L.subtype) = Nat.card Z := by
        exact Subgroup.card_map_of_injective (K := Z) (f := L.subtype)
          L.subtype_injective
      rw [hcard]
      exact theorem_6_8_caseB_Z_prime_card hcase hB
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hPamb]
      exact hnormHmap.symm
    · exact hodd
    · simpa [hPamb, theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured
        (L := L) (H := H)] using hTI
    · exact theorem_6_8_map_subtype_ne_bot hZne
    · simpa [hPamb] using
        theorem_6_8_map_subtype_le_centerIn
          (G := G) (L := L) (H := H) (Z := Z) hZcent
    · exact theorem_6_8_map_subtype_normal_subgroupOf (G := G) (L := L) (Z := Z)
    · exact theorem_6_8_constantCentralizerOrderOnNonidentity_of_prime_card
        (L0 := L) hZprimeMap
  · have hZcent : Z ≤ centerIn H :=
      (theorem_6_8_caseB_Z_center_normal_ne_bot h68' hcase hB).2.1
    have hZH : Z ≤ H := fun z hz => (hZcent hz).1
    have hHcard : Nat.card H = Nat.card Z * Z.relIndex H := by
      have hidx :
          (Z.subgroupOf H).index * Nat.card (Z.subgroupOf H) = Nat.card H := by
        exact Subgroup.index_mul_card (H := Z.subgroupOf H)
      have hcard : Nat.card (Z.subgroupOf H) = Nat.card Z := by
        exact natCard_subgroupOf_eq Z H hZH
      have hidx_eq : (Z.subgroupOf H).index = Z.relIndex H := by
        rfl
      rw [hidx_eq, hcard] at hidx
      simpa [mul_comm] using hidx.symm
    have hPcardH : Nat.card (Pamb : Subgroup G) = Nat.card H := by
      calc
        Nat.card (Pamb : Subgroup G) = Nat.card (H.map L.subtype) := by rw [hPamb]
        _ = Nat.card H := by
          simpa using
            (Subgroup.card_map_of_injective (K := H) (f := L.subtype)
              L.subtype_injective)
    have hZmapcard : Nat.card (Z.map L.subtype) = Nat.card Z := by
      exact Subgroup.card_map_of_injective (K := Z) (f := L.subtype)
        L.subtype_injective
    rw [hPcardH, hHcard, hZmapcard]

theorem theorem_6_8_frobeniusQuotient_Z_of_caseB
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    frobeniusQuotientWithKernel H Z := by
  classical
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68 hcase hB with
    ⟨_hZne, hZcenter, hZnorm⟩
  rcases h68 with ⟨hsemi, _hodd, hHne, hnil, _hTI, _hSbot, _hT, _hcase⟩
  rcases hB with ⟨_hW2ne, _hW2center, hW2comm, hZeq⟩
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  have h42copy : Section4.hypothesis_4_2_statement H W1 W2 W := h42
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, hW1card_ne, _hcyc2, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hW, _hWodd⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have : Z.Normal := hZnorm
  have hZ_le_H : Z ≤ H := by
    intro z hz
    exact (hZcenter hz).1
  have hZ_le_comm : Z ≤ ⁅H,H⁆ := by
    rw [hZeq]
    exact hW2comm
  have hH_not_le_Z : ¬ H ≤ Z := by
    intro hHZ
    exact theorem_6_8_not_le_commutator_of_nontrivial_nilpotent
      hHne hnil (hHZ.trans hZ_le_comm)
  have hcomp : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hcopHW1 : Nat.Coprime (Nat.card H) (Nat.card W1) :=
    theorem_6_8_card_coprime_kernel_complement_of_hypothesis_4_2 h42copy
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  have hcompQuot :
      (H.map q).IsComplement' (W1.map q) :=
    isComplement'_map_mk'_of_le_isComplement' H W1 Z hZ_le_H hcomp
  have hHmap_ne : H.map q ≠ ⊥ := by
    intro hbot
    apply hH_not_le_Z
    intro h hhH
    have hhq_bot : q h ∈ (⊥ : Subgroup (L ⧸ Z)) := by
      rw [← hbot]
      exact ⟨h, hhH, rfl⟩
    have hhq_one : q h = 1 := by
      simpa using hhq_bot
    exact (QuotientGroup.eq_one_iff (N := Z) h).mp hhq_one
  have hW1map_card : Nat.card (W1.map q) = Nat.card W1 :=
    natCard_map_mk'_eq_of_le_isComplement' H W1 Z hZ_le_H hcomp
  have hW1map_ne : W1.map q ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card (W1.map q) = 1 := by
      simp [hbot]
    exact hW1card_ne (hW1map_card ▸ hcard1)
  refine ⟨hZnorm, hZ_le_H, hHnorm, W1.map q, hcompQuot,
    hHmap_ne, hW1map_ne, ?_⟩
  intro r hr
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyElem :
      y ∈ elementCentralizerIn (H.map q) (r : L ⧸ Z) := by
    simpa [q, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hy
  rcases r.property with ⟨w, hwW1, hwq⟩
  have hw_sub_ne : (⟨w, hwW1⟩ : W1) ≠ 1 := by
    intro hwone
    apply hr
    apply Subtype.ext
    calc
      (r : L ⧸ Z) = q w := hwq.symm
      _ = 1 := by
        have hwoneL : w = 1 := congrArg Subtype.val hwone
        simp [q, hwoneL]
  let R0 : Subgroup L := Subgroup.zpowers w
  have hR0_le_W1 : R0 ≤ W1 := by
    exact (Subgroup.zpowers_le).2 hwW1
  have hR0normH : R0 ≤ Subgroup.normalizer (H : Set L) := by
    exact hR0_le_W1.trans (Subgroup.le_normalizer_of_normal (H := H))
  have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card W1 := by
    rw [← natCard_subgroupOf_eq R0 W1 hR0_le_W1]
    exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf W1)
  have hcopHR0 : Nat.Coprime (Nat.card H) (Nat.card R0) :=
    Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopHW1
  have hZinv : ∀ r0 : R0, ∀ x ∈ Z, (r0 : L) * x * (r0 : L)⁻¹ ∈ Z := by
    intro r0 x hx
    exact (inferInstance : Z.Normal).conj_mem x hx (r0 : L)
  have hcentSubQuot :
      subgroupCentralizerIn (H.map q) (R0.map q) =
        (subgroupCentralizerIn H R0).map q :=
    subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
      H R0 Z hR0normH hsolvH hcopHR0 hZinv
  have hySub :
      y ∈ subgroupCentralizerIn (H.map q) (R0.map q) := by
    refine ⟨hyElem.1, ?_⟩
    change y ∈ Subgroup.centralizer
      ((R0.map q : Subgroup (L ⧸ Z)) : Set (L ⧸ Z))
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with ⟨a, haR0, haz⟩
    rcases Subgroup.mem_zpowers_iff.mp haR0 with ⟨n, hn⟩
    have hcomm_r : y * (r : L ⧸ Z) = (r : L ⧸ Z) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
    have hcomm_qw : Commute y (q w) := by
      change y * q w = q w * y
      rw [hwq]
      exact hcomm_r
    have hcomm_qa : Commute y (q a) := by
      rw [← hn]
      simpa [q] using hcomm_qw.zpow_right n
    calc
      z * y = q a * y := by rw [haz]
      _ = y * q a := hcomm_qa.eq.symm
      _ = y * z := by rw [haz]
  have hymap : y ∈ (subgroupCentralizerIn H R0).map q := by
    simpa [hcentSubQuot] using hySub
  rcases hymap with ⟨z, hzcent, hzy⟩
  have hcent_w : elementCentralizerIn H w = W2 := by
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
  have hzElem : z ∈ elementCentralizerIn H w := by
    refine ⟨hzcent.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm :
        w * z = z * w :=
      Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
    exact hcomm.symm
  have hzW2 : z ∈ W2 := by
    simpa [hcent_w] using hzElem
  have hzZ : z ∈ Z := by
    simpa [hZeq] using hzW2
  have hy_eq_one : y = 1 := by
    calc
      y = q z := hzy.symm
      _ = 1 := by
        simpa [q] using (QuotientGroup.eq_one_iff (N := Z) z).2 hzZ
  exact hy_eq_one

theorem theorem_6_8_caseA_quotient_centralizerIn_eq_W2_map
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hZnorm : Z.Normal) :
    let q : L →* L ⧸ Z := QuotientGroup.mk' Z
    ∀ r : W1.map q, r ≠ 1 →
      Section2.centralizerIn (H.map q) (r : L ⧸ Z) = W2.map q := by
  classical
  rcases h68 with ⟨hsemi, _hodd, _hHne, hnil, _hTI, _hSbot, _hT, _hbranch⟩
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, hW2H, _hHH, _hcentA, _hA⟩
  have h42copy : Section4.hypothesis_4_2_statement H W1 W2 W := h42
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hW, _hWodd⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have : Z.Normal := hZnorm
  have hZ_le_H : Z ≤ H := by
    rcases hA with ⟨_hcenterW2, hZeq⟩
    rw [hZeq]
    exact inf_le_right.trans (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
  have hcomp : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hcopHW1 : Nat.Coprime (Nat.card H) (Nat.card W1) :=
    theorem_6_8_card_coprime_kernel_complement_of_hypothesis_4_2 h42copy
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  change ∀ r : W1.map q, r ≠ 1 →
    Section2.centralizerIn (H.map q) (r : L ⧸ Z) = W2.map q
  intro r hr
  apply le_antisymm
  · intro y hy
    have hyElem :
        y ∈ elementCentralizerIn (H.map q) (r : L ⧸ Z) := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : L ⧸ Z) = q w := hwq.symm
        _ = 1 := by
          have hwoneL : w = 1 := congrArg Subtype.val hwone
          simp [q, hwoneL]
    let R0 : Subgroup L := Subgroup.zpowers w
    have hR0_le_W1 : R0 ≤ W1 := by
      exact (Subgroup.zpowers_le).2 hwW1
    have hR0normH : R0 ≤ Subgroup.normalizer (H : Set L) := by
      exact hR0_le_W1.trans (Subgroup.le_normalizer_of_normal (H := H))
    have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card W1 := by
      rw [← natCard_subgroupOf_eq R0 W1 hR0_le_W1]
      exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf W1)
    have hcopHR0 : Nat.Coprime (Nat.card H) (Nat.card R0) :=
      Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopHW1
    have hZinv : ∀ r0 : R0, ∀ x ∈ Z, (r0 : L) * x * (r0 : L)⁻¹ ∈ Z := by
      intro r0 x hx
      exact (inferInstance : Z.Normal).conj_mem x hx (r0 : L)
    have hcentSubQuot :
        subgroupCentralizerIn (H.map q) (R0.map q) =
          (subgroupCentralizerIn H R0).map q :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        H R0 Z hR0normH hsolvH hcopHR0 hZinv
    have hySub :
        y ∈ subgroupCentralizerIn (H.map q) (R0.map q) := by
      refine ⟨hyElem.1, ?_⟩
      change y ∈ Subgroup.centralizer
        ((R0.map q : Subgroup (L ⧸ Z)) : Set (L ⧸ Z))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with ⟨a, haR0, haz⟩
      rcases Subgroup.mem_zpowers_iff.mp haR0 with ⟨n, hn⟩
      have hcomm_r : y * (r : L ⧸ Z) = (r : L ⧸ Z) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
      have hcomm_qw : Commute y (q w) := by
        change y * q w = q w * y
        rw [hwq]
        exact hcomm_r
      have hcomm_qa : Commute y (q a) := by
        rw [← hn]
        simpa [q] using hcomm_qw.zpow_right n
      calc
        z * y = q a * y := by rw [haz]
        _ = y * q a := hcomm_qa.eq.symm
        _ = y * z := by rw [haz]
    have hymap : y ∈ (subgroupCentralizerIn H R0).map q := by
      simpa [hcentSubQuot] using hySub
    rcases hymap with ⟨z, hzcent, hzy⟩
    have hcent_w : elementCentralizerIn H w = W2 := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem : z ∈ elementCentralizerIn H w := by
      refine ⟨hzcent.1, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm :
          w * z = z * w :=
        Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
      exact hcomm.symm
    have hzW2 : z ∈ W2 := by
      simpa [hcent_w] using hzElem
    exact ⟨z, hzW2, hzy⟩
  · intro y hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    rcases hy with ⟨z, hzW2, hzy⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : L ⧸ Z) = q w := hwq.symm
        _ = 1 := by
          have hwoneL : w = 1 := congrArg Subtype.val hwone
          simp [q, hwoneL]
    have hyH : y ∈ H.map q := by
      exact ⟨z, hW2H hzW2, hzy⟩
    have hcent_w : elementCentralizerIn H w = W2 := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem : z ∈ elementCentralizerIn H w := by
      simpa [hcent_w] using hzW2
    have hcomm_zw : z * w = w * z :=
      Subgroup.mem_centralizer_singleton_iff.mp hzElem.2
    have hycomm : y * (r : L ⧸ Z) = (r : L ⧸ Z) * y := by
      calc
        y * (r : L ⧸ Z) = q z * q w := by rw [hzy, hwq]
        _ = q (z * w) := by rw [map_mul]
        _ = q (w * z) := by rw [hcomm_zw]
        _ = q w * q z := by rw [map_mul]
        _ = (r : L ⧸ Z) * y := by rw [hzy, hwq]
    refine ⟨hyH, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm

theorem theorem_6_8_caseA_quotient_hypothesis_4_2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hZnorm : Z.Normal) :
    let q : L →* L ⧸ Z := QuotientGroup.mk' Z
    Section4.hypothesis_4_2_statement
      (H.map q) (W1.map q) (W2.map q) (W.map q) := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases hcase with ⟨⟨d⟩, hprime, hW2comm'⟩
  have hcase' : caseC2Hypothesis L H W1 W2 W T :=
    ⟨⟨d⟩, hprime, hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, hHall, hcyc1, hW1card_ne, hcyc2, hW2card_ne,
      _hcentW1, hW1W, hW2W, hWprod, hWodd⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have : Z.Normal := hZnorm
  have hZ_le_H : Z ≤ H := by
    rcases hA with ⟨_hcenterW2, hZeq⟩
    rw [hZeq]
    exact inf_le_right.trans (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  change Section4.hypothesis_4_2_statement
    (H.map q) (W1.map q) (W2.map q) (W.map q)
  have hcomp : H.IsComplement' W1 :=
    theorem_6_8_isComplement_of_semidirect_top hsemi
  have hcompQuot : (H.map q).IsComplement' (W1.map q) :=
    isComplement'_map_mk'_of_le_isComplement' H W1 Z hZ_le_H hcomp
  have : (H.map q).Normal :=
    hHnorm.map q (QuotientGroup.mk'_surjective Z)
  have hsemiQuot :
      Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup (L ⧸ Z)) (H.map q) (W1.map q) :=
    theorem_6_8_internalSemidirectProduct_top_of_normal_isComplement'
      hcompQuot
  have hHallQuot : ∃ π : Set Nat.Primes, IsHallSubgroup π (W1.map q) := by
    rcases hHall with ⟨π, hπ⟩
    exact ⟨π, theorem_6_8_isHallSubgroup_map_of_surjective hπ q
      (QuotientGroup.mk'_surjective Z)⟩
  have hcyc1Quot : IsCyclic (W1.map q) :=
    isCyclic_of_surjective (f := q.subgroupMap W1)
      (MonoidHom.subgroupMap_surjective q W1)
  have hW1map_card : Nat.card (W1.map q) = Nat.card W1 :=
    natCard_map_mk'_eq_of_le_isComplement' H W1 Z hZ_le_H hcomp
  have hW1map_ne : Nat.card (W1.map q) ≠ 1 := by
    intro hcard
    rw [hW1map_card] at hcard
    exact hW1card_ne hcard
  have hcyc2Quot : IsCyclic (W2.map q) :=
    isCyclic_of_surjective (f := q.subgroupMap W2)
      (MonoidHom.subgroupMap_surjective q W2)
  have hW2map_card : Nat.card (W2.map q) = Nat.card W2 :=
    theorem_6_8_caseA_card_W2_map_mk'_eq hA
  have hW2map_ne : Nat.card (W2.map q) ≠ 1 := by
    intro hcard
    rw [hW2map_card] at hcard
    exact hW2card_ne hcard
  have hcentQuot :
      ∀ r : W1.map q, r ≠ 1 →
        Section2.centralizerIn (H.map q) (r : L ⧸ Z) = W2.map q := by
    exact theorem_6_8_caseA_quotient_centralizerIn_eq_W2_map
      h68' hcase' hA hZnorm
  have hZW : Z ⊓ W = ⊥ :=
    theorem_6_8_caseA_Z_inf_W_eq_bot h68' hcase' hA
  have hWprodQuot :
      Section2.IsInternalDirectProduct (W.map q) (W1.map q) (W2.map q) :=
    theorem_6_8_internalDirectProduct_map_mk'_of_inf_eq_bot W W1 W2 Z
      hWprod hZW
  have hWmap_card : Nat.card (W.map q) = Nat.card W :=
    theorem_6_8_natCard_map_mk'_eq_of_inf_eq_bot W Z hZW
  have hWoddQuot : Odd (Nat.card (W.map q)) := by
    rw [hWmap_card]
    exact hWodd
  exact ⟨hsemiQuot, hHallQuot, hcyc1Quot, hW1map_ne, hcyc2Quot,
    hW2map_ne, hcentQuot, Subgroup.map_mono hW1W, Subgroup.map_mono hW2W,
    hWprodQuot, hWoddQuot⟩

public noncomputable def theorem_6_8_map_mk'_equiv_of_inf_eq_bot
    {L : Type u} [Group L]
    (K Z : Subgroup L) [Z.Normal]
    (hZK : Z ⊓ K = ⊥) :
    K ≃* K.map (QuotientGroup.mk' Z) where
  toFun k := ⟨QuotientGroup.mk' Z (k : L), ⟨k, k.2, rfl⟩⟩
  invFun y := ⟨Classical.choose y.2, (Classical.choose_spec y.2).1⟩
  left_inv k := by
    apply Subtype.ext
    let y : K.map (QuotientGroup.mk' Z) :=
      ⟨QuotientGroup.mk' Z (k : L), ⟨k, k.2, rfl⟩⟩
    have hspec := Classical.choose_spec y.2
    have hq : QuotientGroup.mk' Z (Classical.choose y.2) =
        QuotientGroup.mk' Z (k : L) := hspec.2
    have hdiffZ : (Classical.choose y.2)⁻¹ * (k : L) ∈ Z :=
      QuotientGroup.eq.mp hq
    have hdiffK : (Classical.choose y.2)⁻¹ * (k : L) ∈ K :=
      K.mul_mem (K.inv_mem hspec.1) k.2
    have hdiffBot : (Classical.choose y.2)⁻¹ * (k : L) ∈
        (⊥ : Subgroup L) := by
      have hdiffInf : (Classical.choose y.2)⁻¹ * (k : L) ∈ Z ⊓ K :=
        ⟨hdiffZ, hdiffK⟩
      simpa [hZK] using hdiffInf
    have hdiffOne : (Classical.choose y.2)⁻¹ * (k : L) = 1 := by
      simpa using hdiffBot
    exact inv_mul_eq_one.mp hdiffOne
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec y.2).2
  map_mul' a b := by
    apply Subtype.ext
    simp


@[expose] public def theorem_6_8_transportClassFunction
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (χ : Section1.ClassFunction G) :
    Section1.ClassFunction H :=
  fun h => χ (e.symm h)

public theorem theorem_6_8_transportClassFunction_isClass
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) {χ : Section1.ClassFunction G}
    (hχ : Section1.IsClassFunction χ) :
    Section1.IsClassFunction (theorem_6_8_transportClassFunction e χ) := by
  intro x g
  change χ (e.symm (x * g * x⁻¹)) = χ (e.symm g)
  simpa using hχ (e.symm x) (e.symm g)

public theorem theorem_6_8_transportClassFunction_irreducible
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (theorem_6_8_transportClassFunction e χ) := by
  classical
  rcases hχ with ⟨n, ρ, hρirr, hχeq⟩
  refine ⟨n, ρ.comp e.symm.toMonoidHom, ?_, ?_⟩
  · exact representation_isIrreducible_comp_surjective ρ e.symm.toMonoidHom
      e.symm.surjective hρirr
  · ext h
    simp [theorem_6_8_transportClassFunction, hχeq, Representation.character]

public theorem theorem_6_8_scalarProduct_transportClassFunction
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (χ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct H (theorem_6_8_transportClassFunction e χ)
        (theorem_6_8_transportClassFunction e ψ) =
      Section1.scalarProduct G χ ψ := by
  rw [Section1.scalarProduct, Section1.scalarProduct]
  have hcard : Nat.card H = Nat.card G := Nat.card_congr e.symm.toEquiv
  rw [hcard]
  congr 1
  simpa [theorem_6_8_transportClassFunction] using
    (Equiv.sum_comp e.toEquiv
      (fun h : H => χ (e.symm h) * star (ψ (e.symm h)))).symm

public theorem theorem_6_8_notation_3_3_transport
    {L M : Type u} [Group L] [Finite L] [Group M] [Finite M]
    {W1 W2 W : Subgroup L} {V1 V2 V : Subgroup M}
    (e : W ≃* V)
    (hcard1 : Nat.card V1 = Nat.card W1)
    (hcard2 : Nat.card V2 = Nat.card W2)
    (hV1 : ∀ x : W, ((x : L) ∈ W1) ↔ (((e x : V) : M) ∈ V1))
    (hV2 : ∀ x : W, ((x : L) ∈ W2) ↔ (((e x : V) : M) ∈ V2))
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    Section3.notation_3_3_statement V1 V2 V I J i0 j0
      (fun i j => theorem_6_8_transportClassFunction e (ω i j)) := by
  classical
  change Section3.OmegaSystem W1 W2 W I J i0 j0 ω at hω
  change Section3.OmegaSystem V1 V2 V I J i0 j0
    (fun i j => theorem_6_8_transportClassFunction e (ω i j))
  refine
    { card_left := ?_
      card_right := ?_
      principal := ?_
      left_kernel := ?_
      right_kernel := ?_
      left_kernel_exact := ?_
      right_kernel_exact := ?_
      product := ?_
      degree_one := ?_
      is_class := ?_
      irreducible := ?_
      orthonormal := ?_
      pairwise_eq := ?_
      all_irreducibles := ?_ }
  · rw [hcard1]
    exact hω.card_left
  · rw [hcard2]
    exact hω.card_right
  · ext x
    simp [theorem_6_8_transportClassFunction, hω.principal,
      Section1.principalCharacter]
  · intro i a
    have haV2 : (((a : V) : M) ∈ V2) := Subgroup.mem_subgroupOf.mp a.2
    have ha : ((e.symm (a : V) : W) : L) ∈ W2 := by
      have hv : (((e (e.symm (a : V)) : V) : M) ∈ V2) := by
        simpa using haV2
      exact (hV2 (e.symm (a : V))).2 hv
    simpa [theorem_6_8_transportClassFunction, Section1.degree] using
      hω.left_kernel i ⟨e.symm (a : V), ha⟩
  · intro j a
    have haV1 : (((a : V) : M) ∈ V1) := Subgroup.mem_subgroupOf.mp a.2
    have ha : ((e.symm (a : V) : W) : L) ∈ W1 := by
      have hv : (((e (e.symm (a : V)) : V) : M) ∈ V1) := by
        simpa using haV1
      exact (hV1 (e.symm (a : V))).2 hv
    simpa [theorem_6_8_transportClassFunction, Section1.degree] using
      hω.right_kernel j ⟨e.symm (a : V), ha⟩
  · intro χ hχ
    constructor
    · intro hker
      let χW : Section1.ClassFunction W := fun w => χ (e w)
      have hχW : Section1.IsIrreducibleCharacterOnGroup χW := by
        have hχW_eq :
            χW = theorem_6_8_transportClassFunction e.symm χ := by
          ext w
          simp [χW, theorem_6_8_transportClassFunction]
        rw [hχW_eq]
        exact theorem_6_8_transportClassFunction_irreducible e.symm hχ
      have hkerW : Section1.subgroupInKernel' χW (W2.subgroupOf W) := by
        intro a
        have ha : (((e (a : W) : V) : M) ∈ V2) :=
          (hV2 (a : W)).1 (Subgroup.mem_subgroupOf.mp a.2)
        simpa [χW, Section1.degree] using hker ⟨e (a : W), ha⟩
      rcases (hω.left_kernel_exact χW hχW).1 hkerW with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      ext v
      have hv := congrFun hi (e.symm v)
      simpa [χW, theorem_6_8_transportClassFunction] using hv
    · rintro ⟨i, rfl⟩ a
      have haV2 : (((a : V) : M) ∈ V2) := Subgroup.mem_subgroupOf.mp a.2
      have ha : ((e.symm (a : V) : W) : L) ∈ W2 := by
        have hv : (((e (e.symm (a : V)) : V) : M) ∈ V2) := by
          simpa using haV2
        exact (hV2 (e.symm (a : V))).2 hv
      simpa [theorem_6_8_transportClassFunction, Section1.degree] using
        hω.left_kernel i ⟨e.symm (a : V), ha⟩
  · intro χ hχ
    constructor
    · intro hker
      let χW : Section1.ClassFunction W := fun w => χ (e w)
      have hχW : Section1.IsIrreducibleCharacterOnGroup χW := by
        have hχW_eq :
            χW = theorem_6_8_transportClassFunction e.symm χ := by
          ext w
          simp [χW, theorem_6_8_transportClassFunction]
        rw [hχW_eq]
        exact theorem_6_8_transportClassFunction_irreducible e.symm hχ
      have hkerW : Section1.subgroupInKernel' χW (W1.subgroupOf W) := by
        intro a
        have ha : (((e (a : W) : V) : M) ∈ V1) :=
          (hV1 (a : W)).1 (Subgroup.mem_subgroupOf.mp a.2)
        simpa [χW, Section1.degree] using hker ⟨e (a : W), ha⟩
      rcases (hω.right_kernel_exact χW hχW).1 hkerW with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      ext v
      have hv := congrFun hj (e.symm v)
      simpa [χW, theorem_6_8_transportClassFunction] using hv
    · rintro ⟨j, rfl⟩ a
      have haV1 : (((a : V) : M) ∈ V1) := Subgroup.mem_subgroupOf.mp a.2
      have ha : ((e.symm (a : V) : W) : L) ∈ W1 := by
        have hv : (((e (e.symm (a : V)) : V) : M) ∈ V1) := by
          simpa using haV1
        exact (hV1 (e.symm (a : V))).2 hv
      simpa [theorem_6_8_transportClassFunction, Section1.degree] using
        hω.right_kernel j ⟨e.symm (a : V), ha⟩
  · intro i j x
    simpa [theorem_6_8_transportClassFunction] using hω.product i j (e.symm x)
  · intro i j
    simpa [theorem_6_8_transportClassFunction, Section1.degree] using
      hω.degree_one i j
  · intro i j
    exact theorem_6_8_transportClassFunction_isClass e (hω.is_class i j)
  · intro i j
    exact theorem_6_8_transportClassFunction_irreducible e (hω.irreducible i j)
  · intro p q
    simpa [theorem_6_8_transportClassFunction] using
      (theorem_6_8_scalarProduct_transportClassFunction e (ω p.1 p.2)
        (ω q.1 q.2)).trans (hω.orthonormal p q)
  · intro i i' j j' hEq
    have hEqW : ω i j = ω i' j' := by
      ext w
      have hw := congrFun hEq (e w)
      simpa [theorem_6_8_transportClassFunction] using hw
    exact hω.pairwise_eq hEqW
  · intro χ hχ
    let χW : Section1.ClassFunction W := fun w => χ (e w)
    have hχW : Section1.IsIrreducibleCharacterOnGroup χW := by
      have hχW_eq :
          χW = theorem_6_8_transportClassFunction e.symm χ := by
        ext w
        simp [χW, theorem_6_8_transportClassFunction]
      rw [hχW_eq]
      exact theorem_6_8_transportClassFunction_irreducible e.symm hχ
    rcases hω.all_irreducibles χW hχW with ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    ext v
    have hv := congrFun hij (e.symm v)
    simpa [χW, theorem_6_8_transportClassFunction] using hv

theorem theorem_6_8_subgroupMap_mk'_injective_of_inf_eq_bot
    {L : Type u} [Group L] [Finite L]
    (K Z : Subgroup L) [Z.Normal]
    (hZK : Z ⊓ K = ⊥) :
    Function.Injective ((QuotientGroup.mk' Z).subgroupMap K) := by
  intro a b hab
  apply Subtype.ext
  have hqeq : QuotientGroup.mk' Z (a : L) = QuotientGroup.mk' Z (b : L) := by
    simpa using congrArg Subtype.val hab
  have hdiffZ : (a : L)⁻¹ * (b : L) ∈ Z := QuotientGroup.eq.mp hqeq
  have hdiffK : (a : L)⁻¹ * (b : L) ∈ K := K.mul_mem (K.inv_mem a.2) b.2
  have hdiffBot : (a : L)⁻¹ * (b : L) ∈ (⊥ : Subgroup L) := by
    have hdiffInf : (a : L)⁻¹ * (b : L) ∈ Z ⊓ K := ⟨hdiffZ, hdiffK⟩
    simpa [hZK] using hdiffInf
  have hdiff_one : (a : L)⁻¹ * (b : L) = 1 := by
    simpa using hdiffBot
  calc
    (a : L) = (a : L) * ((a : L)⁻¹ * (b : L)) := by simp [hdiff_one]
    _ = (b : L) := by simp

theorem theorem_6_8_subgroupMap_mk'_mem_map_iff_of_inf_eq_bot
    {L : Type u} [Group L] [Finite L]
    {A K Z : Subgroup L} [Z.Normal]
    (hAK : A ≤ K) (hZK : Z ⊓ K = ⊥) (x : K) :
    ((((QuotientGroup.mk' Z).subgroupMap K) x :
        K.map (QuotientGroup.mk' Z)) : L ⧸ Z) ∈
        A.map (QuotientGroup.mk' Z) ↔
      (x : L) ∈ A := by
  constructor
  · intro hx
    rcases hx with ⟨a, haA, hqa⟩
    have haK : a ∈ K := hAK haA
    have hqeq : QuotientGroup.mk' Z a = QuotientGroup.mk' Z (x : L) := by
      simpa using hqa
    have hdiffZ : a⁻¹ * (x : L) ∈ Z := QuotientGroup.eq.mp hqeq
    have hdiffK : a⁻¹ * (x : L) ∈ K := K.mul_mem (K.inv_mem haK) x.2
    have hdiffBot : a⁻¹ * (x : L) ∈ (⊥ : Subgroup L) := by
      have hdiffInf : a⁻¹ * (x : L) ∈ Z ⊓ K := ⟨hdiffZ, hdiffK⟩
      simpa [hZK] using hdiffInf
    have hdiff_one : a⁻¹ * (x : L) = 1 := by
      simpa using hdiffBot
    have hx_eq : (x : L) = a := by
      calc
        (x : L) = a * (a⁻¹ * (x : L)) := by simp
        _ = a := by simp [hdiff_one]
    simpa [hx_eq] using haA
  · intro hxA
    exact ⟨(x : L), hxA, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem theorem_6_8_caseA_quotient_notation_3_3
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    [Z.Normal]
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    let q : L →* L ⧸ Z := QuotientGroup.mk' Z
    Section3.notation_3_3_statement (W1.map q) (W2.map q) (W.map q)
      d.I d.J d.i0 d.j0
      (fun i j => theorem_6_8_transportClassFunction
        (MulEquiv.ofBijective ((QuotientGroup.mk' Z).subgroupMap W)
          ⟨theorem_6_8_subgroupMap_mk'_injective_of_inf_eq_bot W Z
              (theorem_6_8_caseA_Z_inf_W_eq_bot h68 hcase hA),
            MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) W⟩)
        (d.omega i j)) := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA46⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      _hcentW1, hW1W, hW2W, _hWprod, _hWodd⟩
  have hZW : Z ⊓ W = ⊥ := theorem_6_8_caseA_Z_inf_W_eq_bot h68 hcase hA
  have hZW1 : Z ⊓ W1 = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxZW : x ∈ Z ⊓ W := ⟨hx.1, hW1W hx.2⟩
      simpa [hZW] using hxZW
    · exact bot_le
  have hZW2 : Z ⊓ W2 = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxZW : x ∈ Z ⊓ W := ⟨hx.1, hW2W hx.2⟩
      simpa [hZW] using hxZW
    · exact bot_le
  let eW : W ≃* W.map q :=
    MulEquiv.ofBijective (q.subgroupMap W)
      ⟨theorem_6_8_subgroupMap_mk'_injective_of_inf_eq_bot W Z hZW,
        MonoidHom.subgroupMap_surjective q W⟩
  have hcard1 : Nat.card (W1.map q) = Nat.card W1 :=
    theorem_6_8_natCard_map_mk'_eq_of_inf_eq_bot W1 Z hZW1
  have hcard2 : Nat.card (W2.map q) = Nat.card W2 :=
    theorem_6_8_natCard_map_mk'_eq_of_inf_eq_bot W2 Z hZW2
  have hV1 :
      ∀ x : W, ((x : L) ∈ W1) ↔
        (((eW x : W.map q) : L ⧸ Z) ∈ W1.map q) := by
    intro x
    have hx := theorem_6_8_subgroupMap_mk'_mem_map_iff_of_inf_eq_bot
      (A := W1) (K := W) (Z := Z) hW1W hZW x
    simpa [eW, q] using hx.symm
  have hV2 :
      ∀ x : W, ((x : L) ∈ W2) ↔
        (((eW x : W.map q) : L ⧸ Z) ∈ W2.map q) := by
    intro x
    have hx := theorem_6_8_subgroupMap_mk'_mem_map_iff_of_inf_eq_bot
      (A := W2) (K := W) (Z := Z) hW2W hZW x
    simpa [eW, q] using hx.symm
  exact theorem_6_8_notation_3_3_transport eW hcard1 hcard2 hV1 hV2 hω


theorem theorem_6_8_quotientInducedCF_eq_of_inducedCF_eq
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    {θ η : Section1.ClassFunction H}
    (h : Section1.inducedCF H θ = Section1.inducedCF H η) :
    Section1.quotientInducedCF H Z θ = Section1.quotientInducedCF H Z η := by
  classical
  ext q
  simp [Section1.quotientInducedCF, h]

theorem theorem_6_8_quotientInflatedCharacter_irreducible
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.IsIrreducibleCharacterOnGroup
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) := by
  classical
  rcases hθbar with ⟨n, ρ, hρirr, hθeq⟩
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  refine ⟨n, ρ.comp qH, ?_, ?_⟩
  · exact representation_isIrreducible_comp_surjective ρ qH
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) H) hρirr
  · ext h
    simp [qH, hθeq, Representation.character]

theorem theorem_6_8_quotientInflatedCharacter_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    (θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))) :
    Section1.subgroupInKernel'
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))
      (Z.subgroupOf H) := by
  classical
  intro z
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  have hzq : qH z = 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' Z ((z : H) : L) = 1
    exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
  change θbar (qH z) = θbar (qH 1)
  rw [hzq]
  rfl

theorem theorem_6_8_quotientInflatedCharacter_ne_principal
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar_ne :
      θbar ≠ Section1.principalCharacter (H.map (QuotientGroup.mk' Z))) :
    (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) ≠
      Section1.principalCharacter H := by
  classical
  intro hEq
  apply hθbar_ne
  ext y
  rcases MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) H y with ⟨h, rfl⟩
  exact congrFun hEq h

theorem theorem_6_8_inducedCF_mem_SZ_of_quotient_irreducible
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {SZ : Finset (Section1.ClassFunction L)}
    (hSZ : inducedKernelFamily H Z SZ)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hθbar_ne :
      θbar ≠ Section1.principalCharacter (H.map (QuotientGroup.mk' Z))) :
    Section1.inducedCF H
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) ∈ SZ := by
  classical
  refine (hSZ.2 _).mpr ?_
  exact ⟨fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h),
    theorem_6_8_quotientInflatedCharacter_irreducible hθbar,
    theorem_6_8_quotientInflatedCharacter_subgroupInKernel θbar,
    theorem_6_8_quotientInflatedCharacter_ne_principal hθbar_ne, rfl⟩

theorem theorem_6_8_quotientInducedCF_inflated_eq_inducedCF
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.quotientInducedCF H Z
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨n, ρ, _hρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin n → ℂ) := ρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    intro z
    let qH : H →* H.map (QuotientGroup.mk' Z) :=
      (QuotientGroup.mk' Z).subgroupMap H
    have hzq : qH z = 1 := by
      apply Subtype.ext
      change QuotientGroup.mk' Z ((z : H) : L) = 1
      exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
    change θbar (qH z) = θbar (qH 1)
    rw [hzq]
    rfl
  have hkerRep : Section1.subgroupInRepresentationKernel θrep (Z.subgroupOf H) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
      (Z.subgroupOf H)).mp hker
  have hthetaQuot_eq : Section1.quotientThetaCharacter H Z θrep = θbar := by
    ext y
    rcases Section1.quotientImageSubgroup_exists_preimage H Z y with ⟨h, hy⟩
    let hmem : ((h : L) : L ⧸ Z) ∈ Section1.quotientImageSubgroup H Z :=
      ⟨(h : L), h.2, rfl⟩
    have hy' : y = ⟨((h : L) : L ⧸ Z), hmem⟩ := by
      ext
      exact hy.symm
    rw [hy']
    calc
      Section1.quotientThetaCharacter H Z θrep ⟨((h : L) : L ⧸ Z), hmem⟩ =
          θrep.character h := by
            exact Section1.quotientThetaCharacter_mk H Z θrep hkerRep h hmem
      _ = θbar (qH h) := by rw [hθrep_char]
      _ = θbar ⟨((h : L) : L ⧸ Z), hmem⟩ := by rfl
  calc
    Section1.quotientInducedCF H Z
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.quotientInducedCF H Z θrep.character := by
          rw [hθrep_char]
    _ = Section1.inducedCF (Section1.quotientImageSubgroup H Z)
          (Section1.quotientThetaCharacter H Z θrep) := by
          exact Section1.proposition_1_6_b_classFunction H Z hZH θrep hker
    _ = Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
          simp [Section1.quotientImageSubgroup, hthetaQuot_eq]

theorem theorem_6_8_quotientInflatedInducedCF_irreducible_of_quotient
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    intro z
    have hzq : qH z = 1 := by
      apply Subtype.ext
      change QuotientGroup.mk' Z ((z : H) : L) = 1
      exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
    change θbar (qH z) = θbar (qH 1)
    rw [hzq]
    rfl
  have hqeq := theorem_6_8_quotientInducedCF_inflated_eq_inducedCF
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    simpa [qH, hqeq] using hquotIrr
  rcases hquotIrr' with ⟨n, ρq, hρqirr, hρqeq⟩
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρorig : Representation ℂ L (Fin n → ℂ) := ρq.comp q
  refine ⟨n, ρorig, ?_, ?_⟩
  · exact representation_isIrreducible_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z) hρqirr
  · ext g
    calc
      Section1.inducedCF H (fun h : H => θbar (qH h)) g =
          Section1.quotientInducedCF H Z (fun h : H => θbar (qH h)) (q g) := by
        rw [← hθrep_char]
        exact (Section1.quotientInducedCF_mk H Z hZH θrep
          ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
            (Z.subgroupOf H)).mp hθker) g).symm
      _ = ρq.character (q g) := by
        exact congrFun hρqeq (q g)
      _ = ρorig.character g := by
        simp [ρorig, q, Representation.character]

public theorem theorem_6_8_inducedKernelFamily_irreducible_of_frobeniusQuotient
    {L : Type u} [Group L] [Finite L]
    {H H1 : Subgroup L} {Y : Finset (Section1.ClassFunction L)}
    (hY : inducedKernelFamily H H1 Y)
    (hfrob : frobeniusQuotientWithKernel H H1) :
    ∀ η : Section1.ClassFunction L,
      η ∈ Y → Section1.IsIrreducibleCharacterOnGroup η := by
  classical
  rcases hfrob with
    ⟨hH1norm, hH1H, hHnorm, R, hcomp, _hHbar_ne, _hRne, hcent⟩
  have : H1.Normal := hH1norm
  have : H.Normal := hHnorm
  intro η hηY
  rcases (hY.2 η).mp hηY with ⟨θ, hθirr, hθker, hθne, hηeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Hbar : Subgroup (L ⧸ H1) := H.map q
  have : Hbar.Normal := QuotientGroup.map_normal H1 H
  have hθkerρ : Section1.subgroupInKernel' ρ.character (H1.subgroupOf H) := by
    simpa [hθeq] using hθker
  have hkerRep : Section1.subgroupInRepresentationKernel ρ (H1.subgroupOf H) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (H1.subgroupOf H)).mp hθkerρ
  let H1sub : Subgroup H := H1.subgroupOf H
  let qH0 : H →* H ⧸ H1sub := QuotientGroup.mk' H1sub
  let ρqH : Representation ℂ (H ⧸ H1sub) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ H1sub hkerRep
  have hρqH_comp : ρqH.comp qH0 = ρ := by
    apply MonoidHom.ext
    intro h
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ H1sub hkerRep h
  have hρqH_irr : Representation.IsIrreducible ρqH := by
    apply representation_isIrreducible_of_comp_surjective ρqH qH0
      (QuotientGroup.mk'_surjective H1sub)
    simpa [hρqH_comp] using hρirr
  let θbarRep : Representation ℂ Hbar (Fin n → ℂ) :=
    Section1.quotientThetaRepresentation H H1 ρ hkerRep
  have hθbar_irr : Representation.IsIrreducible θbarRep := by
    let e : H ⧸ H1sub ≃* Hbar := quotientSubgroupRangeEquiv H H1
    have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    change Representation.IsIrreducible (ρqH.comp e.symm.toMonoidHom)
    exact representation_isIrreducible_comp_surjective ρqH e.symm.toMonoidHom
      hsurj hρqH_irr
  let qH : H →* Hbar := q.subgroupMap H
  have hθbar_mk : ∀ h : H, θbarRep.character (qH h) = ρ.character h := by
    intro h
    have hmem : ((h : L) : L ⧸ H1) ∈ Section1.quotientImageSubgroup H H1 := by
      exact ⟨(h : L), h.2, rfl⟩
    have hqH : qH h = ⟨((h : L) : L ⧸ H1), hmem⟩ := by
      apply Subtype.ext
      rfl
    rw [hqH]
    exact Section1.quotientThetaRepresentation_character_mk H H1 ρ hkerRep h hmem
  have hθbar_ne :
      θbarRep.character ≠ Section1.principalCharacter Hbar := by
    intro hprin
    apply hθne
    rw [hθeq]
    ext h
    calc
      ρ.character h = θbarRep.character (qH h) := (hθbar_mk h).symm
      _ = Section1.principalCharacter Hbar (qH h) := by rw [hprin]
      _ = Section1.principalCharacter H h := by
        simp [Section1.principalCharacter]
  have hθbar_class : Section1.IsClassFunction θbarRep.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := θbarRep) g x
  have hIbar :
      Section1.inertiaSubgroup Hbar θbarRep.character = Hbar :=
    theorem_6_8_inertiaSubgroup_eq_of_frobenius_complement
      (L := L ⧸ H1) (H := Hbar) (R := R)
      hcomp hcent hθbar_class
      ⟨n, θbarRep, hθbar_irr, rfl⟩ hθbar_ne
  have hrelbar :
      Hbar.relIndex (Section1.inertiaSubgroup Hbar θbarRep.character) = 1 := by
    rw [hIbar]
    simp [Subgroup.relIndex]
  have hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF Hbar θbarRep.character) :=
    Section1.proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      Hbar θbarRep hθbar_irr hrelbar
  have hθbarIrr : Section1.IsIrreducibleCharacterOnGroup θbarRep.character :=
    ⟨n, θbarRep, hθbar_irr, rfl⟩
  have hOrig : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H (fun h : H => θbarRep.character (qH h))) :=
    theorem_6_8_quotientInflatedInducedCF_irreducible_of_quotient
      (H := H) (Z := H1) hH1H hθbarIrr hquotIrr
  have hInfl : (fun h : H => θbarRep.character (qH h)) = θ := by
    ext h
    calc
      θbarRep.character (qH h) = ρ.character h := hθbar_mk h
      _ = θ h := by rw [hθeq]
  simpa [hηeq, hInfl] using hOrig

theorem theorem_6_8_quotientInflatedInducedCF_not_irreducible_of_quotient
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotRed : ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  intro horig
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    intro z
    have hzq : qH z = 1 := by
      apply Subtype.ext
      change QuotientGroup.mk' Z ((z : H) : L) = 1
      exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
    change θbar (qH z) = θbar (qH 1)
    rw [hzq]
    rfl
  have hindKer : Section1.subgroupInKernel'
      (Section1.inducedCF H θrep.character) Z :=
    (Section1.proposition_1_6_a H Z hZH θrep).mp hθker
  have hindKer' : Section1.subgroupInKernel'
      (Section1.inducedCF H (fun h : H => θbar (qH h))) Z := by
    simpa [hθrep_char] using hindKer
  rcases horig with ⟨n, ρ, hρirr, hρeq⟩
  have hρkerCF : Section1.subgroupInKernel' ρ.character Z := by
    simpa [← hρeq, qH] using hindKer'
  have hρkerRep : Section1.subgroupInRepresentationKernel ρ Z :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ Z).mp hρkerCF
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρq : Representation ℂ (L ⧸ Z) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ Z hρkerRep
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro g
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g
  have hρqirr : Representation.IsIrreducible ρq := by
    apply representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z)
    simpa [hcomp_eq] using hρirr
  have hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    refine ⟨n, ρq, hρqirr, ?_⟩
    symm
    ext y
    rcases QuotientGroup.mk'_surjective Z y with ⟨g, rfl⟩
    calc
      ρq.character (QuotientGroup.mk' Z g) = ρ.character g := by
        simpa [ρq, Representation.character] using
          congrArg (LinearMap.trace ℂ (Fin n → ℂ))
            (Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g)
      _ = Section1.inducedCF H (fun h : H => θbar (qH h)) g := by
        change ρ.character g =
          Section1.inducedCF H
            (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) g
        exact (congrFun hρeq g).symm
      _ = Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))
            (QuotientGroup.mk' Z g) := by
        rw [← hθrep_char]
        exact (Section1.quotientInducedCF_mk H Z hZH θrep
          ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
            (Z.subgroupOf H)).mp hθker) g).symm
  have hqeq := theorem_6_8_quotientInducedCF_inflated_eq_inducedCF
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar) := by
    simpa [qH, hqeq] using hquotIrr
  exact hquotRed hquotIrr'

public theorem theorem_6_8_reducible_subfamily_card_SZ_lower_of_quotient_family
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    {SZ : Finset (Section1.ClassFunction L)}
    {ι : Type*} [Fintype ι]
    (hZH : Z ≤ H)
    (hSZ : inducedKernelFamily H Z SZ)
    (θbar : ι → Section1.ClassFunction (H.map (QuotientGroup.mk' Z)))
    (hirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (θbar i))
    (hne : ∀ i, θbar i ≠ Section1.principalCharacter (H.map (QuotientGroup.mk' Z)))
    (hred : ∀ i, ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) (θbar i)))
    (hinj : Function.Injective
      (fun i => Section1.inducedCF (H.map (QuotientGroup.mk' Z)) (θbar i))) :
    Fintype.card ι ≤
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
  classical
  let f : ι → Section1.ClassFunction L := fun i =>
    Section1.inducedCF H
      (fun h : H => θbar i (((QuotientGroup.mk' Z).subgroupMap H) h))
  have hmem : ∀ i, f i ∈ SZ := by
    intro i
    exact theorem_6_8_inducedCF_mem_SZ_of_quotient_irreducible hSZ
      (hirr i) (hne i)
  have hredf : ∀ i, ¬ Section1.IsIrreducibleCharacterOnGroup (f i) := by
    intro i
    exact theorem_6_8_quotientInflatedInducedCF_not_irreducible_of_quotient
      hZH (hirr i) (hred i)
  have hinjf : Function.Injective f := by
    intro i j hij
    apply hinj
    have hqeq := theorem_6_8_quotientInducedCF_eq_of_inducedCF_eq
      (H := H) (Z := Z)
      (θ := fun h : H => θbar i (((QuotientGroup.mk' Z).subgroupMap H) h))
      (η := fun h : H => θbar j (((QuotientGroup.mk' Z).subgroupMap H) h)) hij
    have hi := theorem_6_8_quotientInducedCF_inflated_eq_inducedCF
      (H := H) (Z := Z) hZH (θbar := θbar i) (hirr i)
    have hj := theorem_6_8_quotientInducedCF_inflated_eq_inducedCF
      (H := H) (Z := Z) hZH (θbar := θbar j) (hirr j)
    simpa [f, hi, hj] using hqeq
  exact theorem_6_8_reducible_subfamily_card_lower_of_injective f hmem hredf hinjf

theorem theorem_6_8_exists_ne_one_mem_of_natCard_ne_one
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) (hK : Nat.card K ≠ 1) :
    ∃ x, x ∈ K ∧ x ≠ 1 := by
  by_contra hcontra
  have hforall : ∀ x : K, x = 1 := by
    intro x
    by_contra hx
    have hx' : (x : L) ≠ 1 := by
      intro hx1
      exact hx (Subtype.ext hx1)
    exact hcontra ⟨x, x.2, hx'⟩
  have hcard : Nat.card K = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨1, fun x => hforall x⟩
  exact hK hcard

theorem theorem_6_8_w2_le_K_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
    hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases theorem_6_8_exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with
    ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

theorem theorem_6_8_hypothesis_4_6_self_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    Section4Scratch.hypothesis_4_6_statement K W1 W2 W K
      ({x : L | x ∈ K ∧ x ≠ 1}) := by
  classical
  have h42' := h42
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
    _hcent, _hW1, _hW2, _hW, _hodd⟩
  have hKnorm : K.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have hW2K : W2 ≤ K := theorem_6_8_w2_le_K_of_hypothesis_4_2 h42'
  refine ⟨h42', hKnorm, hW2K, le_rfl, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
    exact ⟨(Subgroup.mem_inf.mp hxk.1).1, by simpa using hxk.2⟩
  · intro x hx
    exact hx

theorem theorem_6_8_piColumn_injective_of_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) := by
  classical
  have hresCol :
      ∀ j : J,
        Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) =
          (Fintype.card I : ℂ) • xChar j := by
    intro j
    ext t
    calc
      Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) t =
          ∑ i : I, piChar i j t := by
            simp [Section4Scratch.piColumn, Section1.subgroupRestriction]
      _ = ∑ _i : I, xChar j t := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Section1.subgroupRestriction] using congrFun (h45a.1 i j) t
      _ = (Fintype.card I : ℂ) * xChar j t := by
            simp [Finset.sum_const]
      _ = ((Fintype.card I : ℂ) • xChar j) t := by
            simp
  have hcardI_ne : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
  have hxInj : Function.Injective xChar :=
    Section4Scratch.xChar_injective_pf45 K piChar xChar h45a i0 j0 ω σ
      deltaSign hω h43b
  intro j k hEq
  have hsmul :
      (Fintype.card I : ℂ) • xChar j =
        (Fintype.card I : ℂ) • xChar k := by
    calc
      (Fintype.card I : ℂ) • xChar j =
          Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) :=
        (hresCol j).symm
      _ = Section1.subgroupRestriction K (Section4Scratch.piColumn piChar k) := by
        exact congrArg (Section1.subgroupRestriction K) hEq
      _ = (Fintype.card I : ℂ) • xChar k :=
        hresCol k
  have hxEq : xChar j = xChar k := by
    ext t
    have ht := congrFun hsmul t
    exact mul_left_cancel₀ hcardI_ne (by simpa using ht)
  exact hxInj hxEq

theorem theorem_6_8_base_xChar_principal_of_pf45
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    xChar j0 = Section1.principalCharacter K := by
  classical
  have h44 := Section4.proposition_4_4 K W1 W2 W I J i0 j0 ω σ
    piChar deltaSign h42 hω h43b h43c
  have hbasePi : piChar i0 j0 = Section1.principalCharacter L := h44.2.2
  calc
    xChar j0 = Section1.subgroupRestriction K (piChar i0 j0) := by
      symm
      exact h45a.1 i0 j0
    _ = Section1.subgroupRestriction K (Section1.principalCharacter L) := by
      rw [hbasePi]
    _ = Section1.principalCharacter K := by
      ext k
      simp [Section1.subgroupRestriction, Section1.principalCharacter]

public theorem theorem_6_8_reducible_subfamily_card_SZ_lower_of_quotient_pf45
    {L : Type u} [Group L] [Finite L]
    {H W1 W2 W Z : Subgroup L} [H.Normal] [Z.Normal]
    {SZ : Finset (Section1.ClassFunction L)}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction (W.map (QuotientGroup.mk' Z))}
    {σ : Section1.ClassFunction (W.map (QuotientGroup.mk' Z)) →ₗ[ℂ]
      Section1.ClassFunction (L ⧸ Z)}
    {piChar : I → J → Section1.ClassFunction (L ⧸ Z)}
    {xChar : J → Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    {deltaSign : J → ℂ}
    (hZH : Z ≤ H)
    (hSZ : inducedKernelFamily H Z SZ)
    (h42 : Section4.hypothesis_4_2_statement
      (H.map (QuotientGroup.mk' Z))
      (W1.map (QuotientGroup.mk' Z))
      (W2.map (QuotientGroup.mk' Z))
      (W.map (QuotientGroup.mk' Z)))
    (hω : Section3.notation_3_3_statement
      (W1.map (QuotientGroup.mk' Z))
      (W2.map (QuotientGroup.mk' Z))
      (W.map (QuotientGroup.mk' Z)) I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      (W1.map (QuotientGroup.mk' Z))
      (W2.map (QuotientGroup.mk' Z))
      (W.map (QuotientGroup.mk' Z)) I J i0 j0 ω σ piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement
      (W2.map (QuotientGroup.mk' Z))
      (W.map (QuotientGroup.mk' Z)) I J piChar deltaSign ω)
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (H.map (QuotientGroup.mk' Z)) piChar xChar) :
    (Finset.univ.erase j0).card ≤
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
  classical
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let : Fintype {j : J // j ∈ Finset.univ.erase j0} :=
    Finset.Subtype.fintype (Finset.univ.erase j0)
  let θbar : {j : J // j ∈ Finset.univ.erase j0} →
      Section1.ClassFunction (H.map q) :=
    fun j => xChar (j : J)
  have hbase :
      xChar j0 = Section1.principalCharacter (H.map q) :=
    theorem_6_8_base_xChar_principal_of_pf45
      (K := H.map q) (W1 := W1.map q) (W2 := W2.map q) (W := W.map q)
      (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (piChar := piChar)
      (xChar := xChar) (deltaSign := deltaSign) h42 hω h43b h43c h45a
  have hxInj : Function.Injective xChar :=
    Section4Scratch.xChar_injective_pf45 (H.map q) piChar xChar h45a
      i0 j0 ω σ deltaSign hω h43b
  have hneq : ∀ j, θbar j ≠ Section1.principalCharacter (H.map q) := by
    intro j hj
    have hjne : (j : J) ≠ j0 := by
      exact (Finset.mem_erase.mp j.2).1
    exact hjne (hxInj (hj.trans hbase.symm))
  have hred : ∀ j,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF (H.map q) (θbar j)) := by
    intro j
    have h46 : Section4Scratch.hypothesis_4_6_statement
        (H.map q) (W1.map q) (W2.map q) (W.map q) (H.map q)
        ({x : L ⧸ Z | x ∈ H.map q ∧ x ≠ 1}) :=
      theorem_6_8_hypothesis_4_6_self_of_hypothesis_4_2 h42
    have hpiRed :
        ¬ Section1.IsIrreducibleCharacterOnGroup
          (Section4Scratch.piColumn piChar (j : J)) :=
      Section5.piColumn_not_irreducible_pf53 h46 hω h43b (j : J)
    simpa [θbar, q, h45a.2.2 (j : J)] using hpiRed
  have hpiInj : Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) :=
    theorem_6_8_piColumn_injective_of_pf45
      (K := H.map q) (W1 := W1.map q) (W2 := W2.map q) (W := W.map q)
      (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (piChar := piChar)
      (xChar := xChar) (deltaSign := deltaSign) hω h43b h45a
  have hindInj :
      Function.Injective
        (fun j : {j : J // j ∈ Finset.univ.erase j0} =>
          Section1.inducedCF (H.map q) (θbar j)) := by
    intro j k hEq
    apply Subtype.ext
    apply hpiInj
    calc
      Section4Scratch.piColumn piChar (j : J) =
          Section1.inducedCF (H.map q) (xChar (j : J)) := by
            exact (h45a.2.2 (j : J)).symm
      _ = Section1.inducedCF (H.map q) (xChar (k : J)) := by
            simpa [θbar] using hEq
      _ = Section4Scratch.piColumn piChar (k : J) :=
            h45a.2.2 (k : J)
  have hlower := theorem_6_8_reducible_subfamily_card_SZ_lower_of_quotient_family
    (H := H) (Z := Z) (SZ := SZ) hZH hSZ θbar
    (fun j => h45a.2.1 (j : J)) hneq hred hindInj
  have hcard :
      Fintype.card {j : J // j ∈ Finset.univ.erase j0} =
        (Finset.univ.erase j0).card :=
    Fintype.card_of_subtype (Finset.univ.erase j0) (fun j => Iff.rfl)
  simpa [hcard] using hlower

public theorem theorem_6_8_caseA_reducible_subfamily_card_SZ_lower_of_quotient_pf45
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    [H.Normal] [Z.Normal]
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hSZ : inducedKernelFamily H Z SZ)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    (Finset.univ.erase d.j0).card ≤
      (SZ.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let eW : W ≃* W.map q :=
    MulEquiv.ofBijective (q.subgroupMap W)
      ⟨theorem_6_8_subgroupMap_mk'_injective_of_inf_eq_bot W Z
          (theorem_6_8_caseA_Z_inf_W_eq_bot h68 hcase hA),
        MonoidHom.subgroupMap_surjective q W⟩
  let omegaQ : d.I → d.J → Section1.ClassFunction (W.map q) :=
    fun i j => theorem_6_8_transportClassFunction eW (d.omega i j)
  have h42q := theorem_6_8_caseA_quotient_hypothesis_4_2 h68 hcase hA inferInstance
  have hωq : Section3.notation_3_3_statement (W1.map q) (W2.map q) (W.map q)
      d.I d.J d.i0 d.j0 omegaQ := by
    simpa [omegaQ, eW, q] using
      theorem_6_8_caseA_quotient_notation_3_3 h68 hcase hA d
  rcases Section4.theorem_4_3 (H.map q) (W1.map q) (W2.map q) (W.map q)
      d.I d.J d.i0 d.j0 omegaQ h42q hωq with
    ⟨_h43a, σq, piCharq, deltaSignq, h43bq, h43cq, _h43dq⟩
  rcases Section4Scratch.theorem_4_5 (H.map q) (W1.map q) (W2.map q) (W.map q)
      d.i0 d.j0 omegaQ σq piCharq deltaSignq h42q hωq h43bq h43cq with
    ⟨xCharq, h45aq, _h45bq⟩
  have hZH : Z ≤ H := by
    exact (theorem_6_8_caseA_Z_center_normal hA).1.trans inf_le_left
  exact theorem_6_8_reducible_subfamily_card_SZ_lower_of_quotient_pf45
    (H := H) (W1 := W1) (W2 := W2) (W := W) (Z := Z) (SZ := SZ)
    (I := d.I) (J := d.J) (i0 := d.i0) (j0 := d.j0) (ω := omegaQ)
    (σ := σq) (piChar := piCharq) (xChar := xCharq) (deltaSign := deltaSignq)
    hZH hSZ h42q hωq h43bq h43cq h45aq

public theorem theorem_6_8_caseA_reducible_subfamily_card_SZ_nat_lower_of_quotient_pf45
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    [H.Normal] [Z.Normal]
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hSZ : inducedKernelFamily H Z SZ)
    (d : caseC2FullData L H W1 W2 W T) :
    Nat.card W2 - 1 ≤
      (SZ.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hlower :=
    theorem_6_8_caseA_reducible_subfamily_card_SZ_lower_of_quotient_pf45
      h68 hcase hA hSZ d
  rcases d.fullHypothesis with
    ⟨_h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  have hnonbaseCard : (Finset.univ.erase d.j0).card = Nat.card W2 - 1 := by
    have herase : (Finset.univ.erase d.j0).card = Fintype.card d.J - 1 := by
      simp
    rw [herase, hω.card_right]
  simpa [hnonbaseCard] using hlower

public theorem theorem_6_8_caseA_reducible_subfamily_card_SZ_eq_of_quotient_pf45
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (d : caseC2FullData L H W1 W2 W T) :
    letI : Fintype d.I := d.instFintypeI
    letI : Fintype d.J := d.instFintypeJ
    letI : DecidableEq d.I := d.instDecidableEqI
    letI : DecidableEq d.J := d.instDecidableEqJ
    (SZ.filter fun χ =>
      ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
        Nat.card W2 - 1 := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hHnorm : H.Normal := by
    rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, _hbranch⟩
    exact theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hZnorm : Z.Normal := (theorem_6_8_caseA_Z_center_normal hA).2
  have : Z.Normal := hZnorm
  have hSZ : inducedKernelFamily H Z SZ := by
    rcases hfamily with ⟨_hZH, hSZ, _hXeq, _hY⟩
    exact hSZ
  have hlower :
      Nat.card W2 - 1 ≤
        (SZ.filter fun χ =>
          ¬ Section1.IsIrreducibleCharacterOnGroup χ).card :=
    theorem_6_8_caseA_reducible_subfamily_card_SZ_nat_lower_of_quotient_pf45
      h68 hcase hA hSZ d
  exact theorem_6_8_caseC2_reducible_subfamily_card_SZ_eq_of_lower_bound
    hfamily d hlower

theorem theorem_6_8_Z_center_normal_ne_bot_of_caseData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : theorem_6_8_caseAData H W2 Z ∨
      (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z)) :
    Z ≠ ⊥ ∧ Z ≤ centerIn H ∧ Z.Normal := by
  rcases h68 with ⟨hsemi, _hodd, _hHne, hnil, _hTI, _hSbot, _hT, _hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, _hodd, _hHne, hnil, _hTI, _hSbot, _hT, _hbranch⟩
  rcases hcase with hA | hB
  · have : H.Normal := hHnorm
    have hZne : Z ≠ ⊥ := theorem_6_8_caseA_Z_ne_bot hnil hpQ hA
    have hZdata := theorem_6_8_caseA_Z_center_normal hA
    exact ⟨hZne, hZdata.1, hZdata.2⟩
  · exact theorem_6_8_caseB_Z_center_normal_ne_bot h68' hB.1 hB.2


theorem theorem_6_8_X_data_of_Z_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hZne : Z ≠ ⊥)
    (hZcenter : Z ≤ centerIn H)
    (hZnorm : Z.Normal)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hXirr : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      Section1.IsIrreducibleCharacterOnGroup χ) :
    (∀ χ : Section1.ClassFunction L, χ ∈ X ↔
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          ¬ Section1.subgroupInKernel' χ Z) ∧
      coherentFamily X T := by
  rcases hfamily with ⟨_hZH, hSZ, hXeq, _hY⟩
  exact theorem_6_6 H ⁅H,H⁆ Z S SZ X T
    (theorem_6_8_hypothesis_6_4_commutator_of_branch h68)
    hZne hZcenter hZnorm hSZ hXeq hXirr


theorem theorem_6_8_X_irreducible_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∀ χ : Section1.ClassFunction L, χ ∈ X →
      Section1.IsIrreducibleCharacterOnGroup χ := by
  intro χ hχX
  exact theorem_6_8_irreducible_members_of_frobenius h68 hfrob
    ⟨χ, theorem_6_8_familyData_X_subset_S hfamily hχX⟩


theorem theorem_6_8_caseA_X_data_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    (∀ χ : Section1.ClassFunction L, χ ∈ X ↔
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          ¬ Section1.subgroupInKernel' χ Z) ∧
      coherentFamily X T := by
  rcases theorem_6_8_Z_center_normal_ne_bot_of_caseData h68 hpQ
      (Or.inl hA) with
    ⟨hZne, hZcenter, hZnorm⟩
  exact theorem_6_8_X_data_of_Z_data
    h68 hZne hZcenter hZnorm hfamily
    (theorem_6_8_X_irreducible_of_frobenius h68 hfrob hfamily)

theorem theorem_6_8_caseA_X_data_of_caseC2_SZ_count
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hSZcount :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
          Nat.card W2 - 1) :
    (∀ χ : Section1.ClassFunction L, χ ∈ X ↔
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          ¬ Section1.subgroupInKernel' χ Z) ∧
      coherentFamily X T := by
  classical
  rcases theorem_6_8_Z_center_normal_ne_bot_of_caseData h68 hpQ
      (Or.inl hA) with
    ⟨hZne, hZcenter, hZnorm⟩
  rcases hcase with ⟨⟨d⟩, hprime, hW2comm⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hScount :
      (S.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
          Nat.card W2 - 1 := by
    simpa using theorem_6_8_caseC2_reducible_subfamily_card_S_eq h68 d
  have hcard :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
      (S.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card := by
    exact hSZcount.trans hScount.symm
  have hcase' : caseC2Hypothesis L H W1 W2 W T :=
    ⟨⟨d⟩, hprime, hW2comm⟩
  have hpiSZ :
      ∀ d' : caseC2FullData L H W1 W2 W T,
        letI : Fintype d'.I := d'.instFintypeI
        letI : Fintype d'.J := d'.instFintypeJ
        letI : DecidableEq d'.I := d'.instDecidableEqI
        letI : DecidableEq d'.J := d'.instDecidableEqJ
        ∀ j : d'.J, j ≠ d'.j0 →
          Section4Scratch.piColumn d'.piChar j ∈ SZ := by
    intro d'
    exact theorem_6_8_caseC2_nonbase_piColumn_mem_SZ_of_reducible_card_eq
      h68 hfamily hcard d'
  exact theorem_6_8_X_data_of_Z_data
    h68 hZne hZcenter hZnorm hfamily
    (theorem_6_8_caseC2_X_irreducible_of_nonbase_piColumn_mem_SZ
      h68 hcase' hfamily hpiSZ)

theorem theorem_6_8_caseA_X_data_of_quotient_pf45
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (d : caseC2FullData L H W1 W2 W T) :
    (∀ χ : Section1.ClassFunction L, χ ∈ X ↔
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          ¬ Section1.subgroupInKernel' χ Z) ∧
      coherentFamily X T := by
  classical
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  have hSZcount :
      (SZ.filter fun χ =>
        ¬ Section1.IsIrreducibleCharacterOnGroup χ).card =
          Nat.card W2 - 1 := by
    simpa using
      theorem_6_8_caseA_reducible_subfamily_card_SZ_eq_of_quotient_pf45
        h68 hcase hA hfamily d
  exact theorem_6_8_caseA_X_data_of_caseC2_SZ_count
    h68 hcase hpQ hA hfamily hSZcount


theorem theorem_6_8_Y_coherent_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    coherentFamily Y T := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have h64 : hypothesis_6_4_statement H ⊥ ⁅H,H⁆ S T :=
    theorem_6_8_hypothesis_6_4_commutator_of_branch h68
  rcases h64 with ⟨h61, _hoddL, _hbotH1, _hbotK, _hnil, hcomm, hfrob⟩
  rcases hcomm with
    ⟨hMK, hH1K, hMH1, hMnormK, hMnorm, hH1norm, hKnorm, hcommEq⟩
  have hcomm' : commutatorQuotientHypothesis (⊥ : Subgroup L) ⁅H,H⁆ H :=
    ⟨hMK, hH1K, hMH1, hMnormK, hMnorm, hH1norm, hKnorm, hcommEq⟩
  exact theorem_6_5_a_coherent_H1 h61 hH1norm hcomm' hfrob hY

theorem theorem_6_8_Y_irreducible_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∀ η : Section1.ClassFunction L,
      η ∈ Y → Section1.IsIrreducibleCharacterOnGroup η := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  exact theorem_6_8_inducedKernelFamily_irreducible_of_frobeniusQuotient
    hY (theorem_6_8_frobeniusQuotient_commutator_of_branch h68)

theorem theorem_6_8_Y_argumentPow_closed_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    ∀ φ : Section1.ClassFunction L,
      φ ∈ Y →
        ∃ φu : Section1.ClassFunction L,
          φu ∈ Y ∧ Section3.classFunctionArgumentPow φ φu e := by
  classical
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have hH_dvd_G : Nat.card H ∣ Nat.card G :=
    dvd_trans (Subgroup.card_subgroup_dvd_card H) (Subgroup.card_subgroup_dvd_card L)
  have heH : e.Coprime (Nat.card H) :=
    Nat.Coprime.of_dvd_right hH_dvd_G he
  have heL : e.Coprime (Nat.card L) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card L) he
  intro φ hφY
  rcases (hY.2 φ).mp hφY with ⟨θ, hθirr, hθker, hθne, hφeq⟩
  let θu : Section1.ClassFunction H := fun h : H => θ (h ^ e)
  let φu : Section1.ClassFunction L := Section1.inducedCF H θu
  have hθuIrr : Section1.IsIrreducibleCharacterOnGroup θu := by
    exact Section5.isIrreducibleCharacterOnGroup_argumentPow_pf59
      (G := H) (χ := θ) hθirr heH
  have hθuKer : Section1.subgroupInKernel' θu (⁅H, H⁆.subgroupOf H) := by
    intro a
    change θ ((a : H) ^ e) = θ ((1 : H) ^ e)
    have haPow : ((a : H) ^ e) ∈ ⁅H, H⁆.subgroupOf H :=
      (⁅H, H⁆.subgroupOf H).pow_mem a.property e
    calc
      θ ((a : H) ^ e) = Section1.degree θ :=
        hθker ⟨(a : H) ^ e, haPow⟩
      _ = θ ((1 : H) ^ e) := by simp [Section1.degree]
  have hθuNe : θu ≠ Section1.principalCharacter H := by
    intro hθuPrin
    apply hθne
    ext h
    obtain ⟨x, hx⟩ :=
      Section5.pow_surjective_of_coprime_natCard_pf59 (G := H) (e := e) heH h
    calc
      θ h = θ (x ^ e) := by rw [← hx]
      _ = θu x := rfl
      _ = Section1.principalCharacter H x := by rw [hθuPrin]
      _ = Section1.principalCharacter H h := by simp [Section1.principalCharacter]
  refine ⟨φu, ?_, ?_⟩
  · exact (hY.2 φu).mpr ⟨θu, hθuIrr, hθuKer, hθuNe, rfl⟩
  · rw [hφeq]
    exact theorem_6_8_inducedCF_argumentPow_of_normal θ heL

theorem theorem_6_8_exists_Y_degree_relIndex
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∃ η : Section1.ClassFunction L,
      η ∈ Y ∧ Section1.degree η = (H.relIndex (⊤ : Subgroup L) : ℂ) := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have h64 : hypothesis_6_4_statement H ⊥ ⁅H,H⁆ S T :=
    theorem_6_8_hypothesis_6_4_commutator_of_branch h68
  rcases h64 with ⟨h61, _hoddL, _hbotH1, _hbotK, _hnil, hcomm, hfrob⟩
  rcases hcomm with
    ⟨_hMK, _hH1K, _hMH1, _hMnormK, _hMnorm, hH1norm, _hKnorm, _hcommEq⟩
  have hH1ltH : ⁅H,H⁆ < H := frobeniusQuotientWithKernel_left_lt hfrob
  exact inducedKernelFamily_exists_degree_relIndex_of_lt
    h61.2.2.1 hH1norm hH1ltH hY

theorem theorem_6_8_Y_card_gt_one_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    1 < Y.card := by
  classical
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T := h68
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  rcases theorem_6_8_exists_Y_degree_relIndex h68' hfamily with
    ⟨η, hηY, _hηdeg⟩
  have hY : inducedKernelFamily H ⁅H,H⁆ Y := hfamily.2.2.2
  have hηbarY : Section1.conjugateCharacter η ∈ Y :=
    inducedKernelFamily_conjugate_mem hY hηY
  have hYsubS : Y ⊆ S :=
    theorem_6_8_familyData_Y_subset_S hSbot hfamily
  have hηS : η ∈ S := hYsubS hηY
  have hne : η ≠ Section1.conjugateCharacter η :=
    (theorem_6_8_hypothesis_5_2_a_of_hypothesis h68' ⟨η, hηS⟩).2
  exact Finset.one_lt_card.mpr
    ⟨η, hηY, Section1.conjugateCharacter η, hηbarY, hne⟩

theorem theorem_6_8_caseB_zpow_invariance_of_pf59_Hsharp_step
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η ηu : Section1.ClassFunction L}
    {z : Z} {e : ℕ} {n : ℤ}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y) (hηuY : ηu ∈ Y)
    (hargSource : Section3.classFunctionArgumentPow η ηu e)
    (hIrrY : ∀ X : Section1.ClassFunction L,
      X ∈ Y → Section1.IsIrreducibleCharacterOnGroup X)
    (he : e.Coprime (Nat.card G))
    (hClosed : ∀ φ : Section1.ClassFunction L,
      φ ∈ Y →
        ∃ φu : Section1.ClassFunction L,
          φu ∈ Y ∧ Section3.classFunctionArgumentPow φ φu e)
    (hmod : (e : ℤ) ≡ n [ZMOD orderOf z])
    (hz : z ≠ 1) :
    (τ₁ η) ((((z ^ n : Z) : L) : G)) =
      (τ₁ η) ((z : L) : G) := by
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T := h68
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  let A : Set G := subgroupImagePuncturedSet L H
  have h22 : Section2.Hypothesis2 A L (fun _ : G => ⊥) := by
    simpa [A] using theorem_6_8_hypothesis2_subgroupImagePuncturedSet h68'
  have hAL : ∀ a ∈ A, a ∈ L := h22.subset_L
  have hSpanEq : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y Section5.puncturedSet χ ↔
        Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ := by
    intro χ
    simpa [A] using
      theorem_6_8_Y_punctured_span_iff_subgroupImage hSbot hfamily χ
  have hcard : 1 < Y.card :=
    theorem_6_8_Y_card_gt_one_of_familyData h68' hfamily
  have hDade : ∀ χ : Section1.ClassFunction L,
      Section5.integerSpanOn Y (Section4Scratch.subgroupPullbackSet L A) χ →
        τ₁ χ = Section2.dadeTransform (fun _ : G => ⊥) hAL χ := by
    intro χ hχ
    simpa [A] using
      theorem_6_8_caseB_Y_dade_agreement_subgroupImage
        h68' hfamily hτ₁ hAL χ hχ
  have hTzero : (T (ηu - η)) ((z : L) : G) = 0 :=
    theorem_6_8_Tzero_of_caseB_argumentPow_mem_A
      h22 hB hfamily hτ₁ hηY hηuY hargSource hSpanEq hDade
      (by
        simpa [A] using
          theorem_6_8_caseB_z_mem_subgroupImagePuncturedSet hfamily hz)
  exact theorem_6_8_caseB_zpow_invariance_of_pf59_step
    hB hfamily hτ₁ hηY hηuY hargSource
    (Section5.theorem_5_9_a A L (fun _ : G => ⊥) hAL Y)
    h22 hIrrY hSpanEq hcard hDade he hClosed hmod hTzero

theorem theorem_6_8_caseB_zpow_invariance_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y)
    {z : Z} (hz : z ≠ 1) {n : ℤ} (hzn : (z ^ n : Z) ≠ 1) :
    (τ₁ η) ((((z ^ n : Z) : L) : G)) =
      (τ₁ η) ((z : L) : G) := by
  have hprimeZ : Nat.Prime (Nat.card Z) :=
    theorem_6_8_caseB_Z_prime_card hcase hB
  have hcopZ : IsCoprime n (orderOf z : ℤ) :=
    theorem_6_8_isCoprime_int_orderOf_of_prime_card_zpow_ne_one
      hprimeZ hz hzn
  have hcopG : IsCoprime n (orderOf (((z : L) : G)) : ℤ) := by
    simpa [Subgroup.orderOf_coe] using hcopZ
  rcases theorem_6_8_exists_coprime_natCard_intModEq_orderOf
      (((z : L) : G)) hcopG with
    ⟨e, he, hmodG⟩
  have hmodZ : (e : ℤ) ≡ n [ZMOD orderOf z] := by
    simpa [Subgroup.orderOf_coe] using hmodG
  rcases theorem_6_8_Y_argumentPow_closed_of_familyData
      h68 hfamily he η hηY with
    ⟨ηu, hηuY, harg⟩
  exact theorem_6_8_caseB_zpow_invariance_of_pf59_Hsharp_step
    h68 hB hfamily hτ₁ hηY hηuY harg
    (theorem_6_8_Y_irreducible_of_familyData h68 hfamily)
    he (theorem_6_8_Y_argumentPow_closed_of_familyData h68 hfamily he)
    hmodZ hz

theorem theorem_6_8_2_1_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    theorem_6_8_2_1_statement L H W1 W2 W Z S SZ X Y T τ₁ := by
  exact theorem_6_8_2_1_of_zpow_invariance_nontrivial
    (fun h68 _hpQ hcase hB hfamily hτ₁ η hηY z hz n hzn =>
      theorem_6_8_caseB_zpow_invariance_of_familyData
        h68 hcase hB hfamily hτ₁ hηY hz hzn)

theorem theorem_6_8_2_2_restriction_regular_add_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
        a • regularCharacter (Z.map L.subtype) +
          b • Section1.principalCharacter (Z.map L.subtype) := by
  exact theorem_6_8_2_2_restriction_regular_add_of_821_statement
    theorem_6_8_2_1_of_familyData h68 hpQ hcase hB hfamily hτ₁ hηY

theorem theorem_6_8_scalarProduct_regularCharacter_right
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (regularCharacter G) = φ 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  unfold Section1.scalarProduct regularCharacter
  rw [Finset.sum_eq_single (1 : G)]
  · simp only [if_true]
    have hstar : star ((Nat.card G : ℂ)) = (Nat.card G : ℂ) := by simp
    rw [hstar]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    field_simp [hcard, Nat.card_eq_fintype_card]
  · intro g _hg hgne
    simp [hgne]
  · intro hone
    simp at hone

theorem theorem_6_8_scalarProduct_regular_add_principal_right
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφone : φ 1 = 1)
    (hprincipal : Section1.scalarProduct G φ (Section1.principalCharacter G) = 0)
    {a b : ℂ} (ha : star a = a) :
    Section1.scalarProduct G φ
      (a • regularCharacter G + b • Section1.principalCharacter G) = a := by
  have hadd :
      Section1.scalarProduct G φ
        (a • regularCharacter G + b • Section1.principalCharacter G) =
        Section1.scalarProduct G φ (a • regularCharacter G) +
          Section1.scalarProduct G φ (b • Section1.principalCharacter G) := by
    simp [Section1.scalarProduct, Finset.sum_add_distrib, mul_add]
  rw [hadd, Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_right,
    theorem_6_8_scalarProduct_regularCharacter_right, hprincipal, hφone, ha]
  simp

theorem theorem_6_8_scalarProduct_regular_add_principal_right_star
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφone : φ 1 = 1)
    (hprincipal : Section1.scalarProduct G φ (Section1.principalCharacter G) = 0)
    {a b : ℂ} :
    Section1.scalarProduct G φ
      (a • regularCharacter G + b • Section1.principalCharacter G) = star a := by
  have hadd :
      Section1.scalarProduct G φ
        (a • regularCharacter G + b • Section1.principalCharacter G) =
        Section1.scalarProduct G φ (a • regularCharacter G) +
          Section1.scalarProduct G φ (b • Section1.principalCharacter G) := by
    simp [Section1.scalarProduct, Finset.sum_add_distrib, mul_add]
  rw [hadd, Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_right,
    theorem_6_8_scalarProduct_regularCharacter_right, hprincipal, hφone]
  simp

theorem theorem_6_8_subgroupRestriction_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    {φ : Section1.ClassFunction G}
    (hφ : Theory.Character.IsVirtualCharacter φ) :
    Theory.Character.IsVirtualCharacter (Section1.subgroupRestriction H φ) := by
  classical
  rcases hφ with ⟨r, m, n, ρ, hφeq⟩
  refine ⟨r, m, n, fun i => (ρ i).comp H.subtype, ?_⟩
  ext h
  rw [hφeq]
  simp [Theory.Character.virtualCharacterOfRepresentations,
    Section1.subgroupRestriction, Representation.character]

theorem theorem_6_8_source_scalarProduct_star_eq_self_of_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    {ψ : Section1.ClassFunction G}
    (hψvirt : Theory.Character.IsVirtualCharacter ψ) :
    star (Section1.scalarProduct L χ (Section1.subgroupRestriction L ψ)) =
      Section1.scalarProduct L χ (Section1.subgroupRestriction L ψ) := by
  have hχvirt : Theory.Character.IsVirtualCharacter χ :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hχirr
  have hresvirt :
      Theory.Character.IsVirtualCharacter (Section1.subgroupRestriction L ψ) :=
    theorem_6_8_subgroupRestriction_isVirtualCharacter L hψvirt
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hχvirt hresvirt with
    ⟨n, hn⟩
  rw [hn]
  simp

theorem theorem_6_8_regular_add_coefficient_eq_sub_values
    {G : Type u} [Group G] [Finite G]
    {Z : Subgroup G}
    {ψ : Section1.ClassFunction G}
    {a b : ℂ}
    (hres : Section1.subgroupRestriction Z ψ =
      a • regularCharacter Z + b • Section1.principalCharacter Z)
    (z : Z) (hz : z ≠ 1) :
    a = (ψ 1 - ψ (z : G)) / (Nat.card Z : ℂ) := by
  have hcard_ne : (Nat.card Z : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Z)).ne'
  have h1 : ψ 1 = a * (Nat.card Z : ℂ) + b := by
    have h := congrFun hres (1 : Z)
    simpa [Section1.subgroupRestriction, regularCharacter,
      Section1.principalCharacter] using h
  have hzval : ψ (z : G) = b := by
    have h := congrFun hres z
    simpa [Section1.subgroupRestriction, regularCharacter,
      Section1.principalCharacter, hz] using h
  rw [h1, hzval]
  field_simp [hcard_ne]
  ring


theorem theorem_6_8_regular_add_coefficient_multiple_of_congruent_values
    {G : Type u} [Group G] [Finite G]
    {Z : Subgroup G}
    {ψ : Section1.ClassFunction G}
    {a b : ℂ}
    (hres : Section1.subgroupRestriction Z ψ =
      a • regularCharacter Z + b • Section1.principalCharacter Z)
    (z : Z) (hz : z ≠ 1)
    {n q : ℕ}
    (hn : n ≠ 0)
    (hfactor : n = Nat.card Z * q)
    (hψ1 : ψ 1 ∈ Set.range (fun m : ℤ => (m : ℂ)))
    (hψz : ψ (z : G) ∈ Set.range (fun m : ℤ => (m : ℂ)))
    (hcongr : algebraicIntegerCongruentModNat n (ψ (z : G)) (ψ 1)) :
    ∃ k : ℤ, a = (q : ℂ) * (k : ℂ) := by
  rcases theorem_6_7_int_difference_of_congruent_mod_nat
      hn hψz hψ1 hcongr with
    ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  have hcard_ne : (Nat.card Z : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Z)).ne'
  have hcoeff := theorem_6_8_regular_add_coefficient_eq_sub_values hres z hz
  rw [hcoeff]
  have hdiff : ψ 1 - ψ (z : G) = (n : ℂ) * ((-k : ℤ) : ℂ) := by
    calc
      ψ 1 - ψ (z : G) = -(ψ (z : G) - ψ 1) := by ring
      _ = -((n : ℂ) * (k : ℂ)) := by rw [hk]
      _ = (n : ℂ) * ((-k : ℤ) : ℂ) := by norm_num [mul_neg]
  rw [hdiff, hfactor]
  field_simp [hcard_ne]
  norm_num [Nat.cast_mul]
  ring

theorem theorem_6_8_source_coeff_multiple_of_regular_coeff_multiple
    {a q c r : ℂ}
    (hq : q ≠ 0)
    (hlink : r * a = q * c)
    (hr : ∃ k : ℤ, r = q * ((k : ℤ) : ℂ)) :
    ∃ k : ℤ, c = a * ((k : ℤ) : ℂ) := by
  rcases hr with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hcancel : a * ((k : ℤ) : ℂ) = c := by
    apply mul_left_cancel₀ hq
    calc
      q * (a * ((k : ℤ) : ℂ)) = (q * ((k : ℤ) : ℂ)) * a := by ring
      _ = r * a := by rw [hk]
      _ = q * c := hlink
  exact hcancel.symm


theorem theorem_6_8_theorem_6_7_signed_outputs
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 Z : Subgroup G)
    {ψ : Section1.ClassFunction G}
    (hbase : theorem_6_7_base_hypothesis p P L0 Z)
    (hsigned : Section3.IsSignedIrreducibleCharacter ψ)
    (hconst : constantOnNonidentitySubgroup Z ψ) :
    ψ 1 ∈ Set.range (fun m : ℤ => (m : ℂ)) ∧
      (∀ z : Z, z ≠ 1 → ψ (z : G) ∈ Set.range (fun m : ℤ => (m : ℂ))) ∧
        (∀ z : Z, z ≠ 1 →
          algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
            (ψ (z : G)) (ψ 1)) := by
  rcases hsigned with ⟨ε, hε, μ, hμ, hψeq⟩
  rcases hε with rfl | rfl
  · have hconstμ : constantOnNonidentitySubgroup Z μ := by
      intro z1 z2 hz1 hz2
      simpa [hψeq] using hconst z1 z2 hz1 hz2
    have h67 : theorem_6_7_hypothesis p P L0 Z μ :=
      ⟨hbase, hμ, hconstμ⟩
    rcases theorem_6_7 p P L0 Z μ h67 with ⟨hint, hcongr⟩
    rcases theorem_6_7_degree_nat_of_irreducible hμ with ⟨d, hd⟩
    constructor
    · exact ⟨d, by simpa [hψeq] using hd.symm⟩
    constructor
    · intro z hz
      simpa [hψeq] using hint z hz
    · intro z hz
      simpa [hψeq] using hcongr z hz
  · have hconstμ : constantOnNonidentitySubgroup Z μ := by
      intro z1 z2 hz1 hz2
      have h := congrArg Neg.neg (hconst z1 z2 hz1 hz2)
      simpa [hψeq] using h
    have h67 : theorem_6_7_hypothesis p P L0 Z μ :=
      ⟨hbase, hμ, hconstμ⟩
    rcases theorem_6_7 p P L0 Z μ h67 with ⟨hint, hcongr⟩
    rcases theorem_6_7_degree_nat_of_irreducible hμ with ⟨d, hd⟩
    constructor
    · refine ⟨-(d : ℤ), ?_⟩
      calc
        ((-(d : ℤ) : ℤ) : ℂ) = - (d : ℂ) := by norm_num
        _ = - μ 1 := by rw [hd]
        _ = ψ 1 := by simp [hψeq]
    constructor
    · intro z hz
      rcases hint z hz with ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      calc
        ((-m : ℤ) : ℂ) = - (m : ℂ) := by norm_num
        _ = - μ (z : G) := congrArg Neg.neg hm
        _ = ψ (z : G) := by simp [hψeq]
    · intro z hz
      rcases hcongr z hz with ⟨hzint, h1int, hq⟩
      unfold algebraicIntegerCongruentModNat
      constructor
      · simpa [hψeq] using hzint.neg
      constructor
      · simpa [hψeq] using h1int.neg
      · convert hq.neg using 1
        simp [hψeq]
        ring

theorem theorem_6_8_regular_add_coefficient_multiple_of_theorem_6_7_signed
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 Z : Subgroup G)
    {ψ : Section1.ClassFunction G}
    {a b : ℂ}
    (hbase : theorem_6_7_base_hypothesis p P L0 Z)
    (hsigned : Section3.IsSignedIrreducibleCharacter ψ)
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (hres : Section1.subgroupRestriction Z ψ =
      a • regularCharacter Z + b • Section1.principalCharacter Z)
    (z : Z) (hz : z ≠ 1)
    {q : ℕ}
    (hfactor : Nat.card (P : Subgroup G) = Nat.card Z * q) :
    ∃ k : ℤ, a = (q : ℂ) * (k : ℂ) := by
  rcases theorem_6_8_theorem_6_7_signed_outputs
      P L0 Z hbase hsigned hconst with
    ⟨hψ1, hψz, hcongr⟩
  exact theorem_6_8_regular_add_coefficient_multiple_of_congruent_values
    hres z hz (Nat.card_pos (α := (P : Subgroup G))).ne'
    hfactor hψ1 (hψz z hz) (hcongr z hz)

theorem theorem_6_8_source_coeff_multiple_of_pf67_signed_regular_add
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 Z : Subgroup G)
    {ψ : Section1.ClassFunction G}
    {a b ratio c : ℂ}
    (hbase : theorem_6_7_base_hypothesis p P L0 Z)
    (hsigned : Section3.IsSignedIrreducibleCharacter ψ)
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (hres : Section1.subgroupRestriction Z ψ =
      a • regularCharacter Z + b • Section1.principalCharacter Z)
    (z : Z) (hz : z ≠ 1)
    {q : ℕ}
    (hfactor : Nat.card (P : Subgroup G) = Nat.card Z * q)
    (hlink : a * ratio = (q : ℂ) * c) :
    ∃ k : ℤ, c = ratio * ((k : ℤ) : ℂ) := by
  have hq : (q : ℂ) ≠ 0 := by
    have hqnat : q ≠ 0 := by
      intro hq0
      have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
      rw [hq0, mul_zero] at hfactor
      omega
    exact_mod_cast hqnat
  have hr : ∃ k : ℤ, a = (q : ℂ) * ((k : ℤ) : ℂ) :=
    theorem_6_8_regular_add_coefficient_multiple_of_theorem_6_7_signed
      P L0 Z hbase hsigned hconst hres z hz hfactor
  exact theorem_6_8_source_coeff_multiple_of_regular_coeff_multiple hq hlink hr

theorem theorem_6_8_degree_one_of_prime_card_irreducible
    {Z : Type u} [Group Z] [Finite Z]
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ) :
    φ 1 = 1 := by
  classical
  rcases hφ with ⟨n, ρ, hρirr, hφeq⟩
  have : Fact (Nat.Prime (Nat.card Z)) := ⟨hprime⟩
  have hcyc : IsCyclic Z := isCyclic_of_prime_card (α := Z) (p := Nat.card Z) rfl
  let : CommGroup Z := hcyc.commGroup
  let : Std.Commutative (α := Z) (· * ·) := ⟨mul_comm⟩
  let : IsMulCommutative Z := ⟨inferInstance⟩
  let : Representation.IsIrreducible ρ := hρirr
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
  rw [hφeq]
  simp [Representation.character, hfin]

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card
    {Z : Type u} [Group Z] [Finite Z]
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {a b : ℂ} (ha : star a = a) :
    Section1.scalarProduct Z φ
      (a • regularCharacter Z + b • Section1.principalCharacter Z) = a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right
    (theorem_6_8_degree_one_of_prime_card_irreducible hprime hφ)
    (Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hφ hφne)
    ha

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_star
    {Z : Type u} [Group Z] [Finite Z]
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {a b : ℂ} :
    Section1.scalarProduct Z φ
      (a • regularCharacter Z + b • Section1.principalCharacter Z) = star a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right_star
    (theorem_6_8_degree_one_of_prime_card_irreducible hprime hφ)
    (Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hφ hφne)

theorem theorem_6_8_prime_card_map_subtype
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (Z : Subgroup L)
    (hprime : Nat.Prime (Nat.card Z)) :
    Nat.Prime (Nat.card (Z.map L.subtype)) := by
  have hcard : Nat.card (Z.map L.subtype) = Nat.card Z := by
    exact Subgroup.card_map_of_injective (K := Z) (f := L.subtype) L.subtype_injective
  rw [hcard]
  exact hprime

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_map
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction (Z.map L.subtype)}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter (Z.map L.subtype))
    {a b : ℂ} (ha : star a = a) :
    Section1.scalarProduct (Z.map L.subtype) φ
      (a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) = a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card
    (theorem_6_8_prime_card_map_subtype L Z hprime) hφ hφne ha

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_map_star
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction (Z.map L.subtype)}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter (Z.map L.subtype))
    {a b : ℂ} :
    Section1.scalarProduct (Z.map L.subtype) φ
      (a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) = star a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_star
    (theorem_6_8_prime_card_map_subtype L Z hprime) hφ hφne

noncomputable def theorem_6_8_subtypeMapEquiv
    {G : Type u} [Group G]
    (L : Subgroup G) (Z : Subgroup L) :
    Z ≃* Z.map L.subtype := by
  refine MulEquiv.ofBijective (L.subtype.subgroupMap Z) ?_
  constructor
  · intro a b h
    apply Subtype.ext
    apply L.subtype_injective
    exact congrArg (fun y : Z.map L.subtype => (y : G)) h
  · exact MonoidHom.subgroupMap_surjective L.subtype Z

theorem theorem_6_8_transport_subtypeMap_ne_principal
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    {φ : Section1.ClassFunction Z}
    (hφne : φ ≠ Section1.principalCharacter Z) :
    theorem_6_8_transportClassFunction (theorem_6_8_subtypeMapEquiv L Z) φ ≠
      Section1.principalCharacter (Z.map L.subtype) := by
  intro h
  apply hφne
  ext z
  have hz := congrFun h ((theorem_6_8_subtypeMapEquiv L Z) z)
  change φ ((theorem_6_8_subtypeMapEquiv L Z).symm
      ((theorem_6_8_subtypeMapEquiv L Z) z)) = 1 at hz
  simpa [Section1.principalCharacter] using hz

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_subtypeMap
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {a b : ℂ} (ha : star a = a) :
    Section1.scalarProduct (Z.map L.subtype)
      (theorem_6_8_transportClassFunction (theorem_6_8_subtypeMapEquiv L Z) φ)
      (a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) = a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_map
    hprime
    (theorem_6_8_transportClassFunction_irreducible
      (theorem_6_8_subtypeMapEquiv L Z) hφ)
    (theorem_6_8_transport_subtypeMap_ne_principal hφne)
    ha

theorem theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_subtypeMap_star
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {a b : ℂ} :
    Section1.scalarProduct (Z.map L.subtype)
      (theorem_6_8_transportClassFunction (theorem_6_8_subtypeMapEquiv L Z) φ)
      (a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) = star a := by
  exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_map_star
    hprime
    (theorem_6_8_transportClassFunction_irreducible
      (theorem_6_8_subtypeMapEquiv L Z) hφ)
    (theorem_6_8_transport_subtypeMap_ne_principal hφne)

theorem theorem_6_8_transport_subtypeMap_subgroupRestriction
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    (ψ : Section1.ClassFunction G) :
    theorem_6_8_transportClassFunction (theorem_6_8_subtypeMapEquiv L Z)
      (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ)) =
        Section1.subgroupRestriction (Z.map L.subtype) ψ := by
  ext y
  rcases (theorem_6_8_subtypeMapEquiv L Z).surjective y with ⟨z, rfl⟩
  have hval :
      (((theorem_6_8_subtypeMapEquiv L Z) z : Z.map L.subtype) : G) =
        ((z : L) : G) := rfl
  simp [theorem_6_8_transportClassFunction, Section1.subgroupRestriction, hval]

theorem theorem_6_8_constantOnNonidentitySubgroup_subtypeMap_of_local
    {G : Type u} [Group G]
    {L : Subgroup G} {Z : Subgroup L}
    {ψ : Section1.ClassFunction G}
    (hconst :
      constantOnNonidentitySubgroup Z
        (Section1.subgroupRestriction L ψ)) :
    constantOnNonidentitySubgroup (Z.map L.subtype) ψ := by
  let e := theorem_6_8_subtypeMapEquiv L Z
  intro y1 y2 hy1 hy2
  have hz1 : e.symm y1 ≠ 1 := by
    intro hz
    apply hy1
    have := congrArg e hz
    simpa [e] using this
  have hz2 : e.symm y2 ≠ 1 := by
    intro hz
    apply hy2
    have := congrArg e hz
    simpa [e] using this
  have hlocal := hconst (e.symm y1) (e.symm y2) hz1 hz2
  calc
    ψ (y1 : G) =
        ψ (((e (e.symm y1) : Z.map L.subtype) : G)) := by
          rw [e.apply_symm_apply]
    _ = ψ ((((e.symm y1 : Z) : L) : G)) := rfl
    _ = ψ ((((e.symm y2 : Z) : L) : G)) := by
          simpa [Section1.subgroupRestriction] using hlocal
    _ = ψ (((e (e.symm y2) : Z.map L.subtype) : G)) := rfl
    _ = ψ (y2 : G) := by
          rw [e.apply_symm_apply]

theorem theorem_6_8_regular_add_local_of_subtypeMap
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    {ψ : Section1.ClassFunction G}
    {a b : ℂ}
    (hresMap : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ) =
      a • regularCharacter Z + b • Section1.principalCharacter Z := by
  ext z
  have h := congrFun hresMap ((theorem_6_8_subtypeMapEquiv L Z) z)
  have hcard : Nat.card (Z.map L.subtype) = Nat.card Z := by
    exact Subgroup.card_map_of_injective (K := Z) (f := L.subtype)
      L.subtype_injective
  have hcardF : Fintype.card (Z.map L.subtype) = Fintype.card Z := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  by_cases hz : z = 1
  · subst z
    have hmap_one :
        ψ 1 = a * (Fintype.card (Z.map L.subtype) : ℂ) + b := by
      simpa [Section1.subgroupRestriction, regularCharacter,
        Section1.principalCharacter] using h
    have hlocal_one :
        ψ 1 = a * (Fintype.card Z : ℂ) + b := by
      rw [← hcardF]
      exact hmap_one
    simpa [Section1.subgroupRestriction, regularCharacter,
      Section1.principalCharacter] using hlocal_one
  · have hzmap : (theorem_6_8_subtypeMapEquiv L Z) z ≠ 1 := by
      intro hmap
      apply hz
      have := congrArg (theorem_6_8_subtypeMapEquiv L Z).symm hmap
      simpa using this
    have hval :
        (((theorem_6_8_subtypeMapEquiv L Z) z : Z.map L.subtype) : G) =
          ((z : L) : G) := rfl
    simpa [Section1.subgroupRestriction, regularCharacter,
      Section1.principalCharacter, hcard, hcardF, hz, hzmap, hval] using h

public theorem theorem_6_8_frobenius_complement_centralizerIn_eq_bot
    {L : Type u} [Group L] [Finite L]
    {K R : Subgroup L} [K.Normal]
    (hcomp : K.IsComplement' R)
    (hcent : ∀ r : R, r ≠ 1 → Section2.centralizerIn K (r : L) = ⊥)
    {x : L} (hxnotK : x ∉ K) :
    Section2.centralizerIn K x = ⊥ := by
  classical
  have hxSup : x ∈ K ⊔ R := by
    simp [hcomp.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := R) (x := x)).1 hxSup with
    ⟨k, hkK, r, hrR, hkr⟩
  let rR : R := ⟨r, hrR⟩
  have hrne : rR ≠ 1 := by
    intro hr1
    apply hxnotK
    rw [← hkr]
    have hr_eq : r = 1 := by simpa [rR] using congrArg Subtype.val hr1
    simp [hr_eq, hkK]
  let f : K → K := fun a =>
    ⟨(a : L) * r * (a : L)⁻¹ * r⁻¹, by
      have hconjK : r * (a : L)⁻¹ * r⁻¹ ∈ K :=
        (inferInstance : K.Normal).conj_mem ((a : L)⁻¹) (K.inv_mem a.2) r
      simpa [mul_assoc] using K.mul_mem a.2 hconjK⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have habG : (a : L) * r * (a : L)⁻¹ * r⁻¹ =
        (b : L) * r * (b : L)⁻¹ * r⁻¹ := congrArg Subtype.val hab
    have hcomm : (b : L)⁻¹ * (a : L) * r = r * ((b : L)⁻¹ * (a : L)) := by
      have hab1 :
          (a : L) * r * (a : L)⁻¹ = (b : L) * r * (b : L)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : L => t * r) habG
      have hab2 := congrArg (fun t : L => (b : L)⁻¹ * t * (a : L)) hab1
      simpa [mul_assoc] using hab2
    let c : K := ⟨(b : L)⁻¹ * (a : L), K.mul_mem (K.inv_mem b.2) a.2⟩
    have hcCent : (c : L) ∈ Section2.centralizerIn K (rR : L) := by
      refine ⟨c.2, ?_⟩
      change (c : L) ∈ Subgroup.centralizer ({(rR : L)} : Set L)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [c, rR] using hcomm)
    have hcBot : (c : L) ∈ (⊥ : Subgroup L) := by
      simpa [hcent rR hrne] using hcCent
    have hc_eq : (c : L) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : L => (b : L) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  rcases hf_surj ⟨k, hkK⟩ with ⟨a, ha⟩
  have haG : (a : L) * r * (a : L)⁻¹ * r⁻¹ = k := congrArg Subtype.val ha
  have hconj_x : (a : L)⁻¹ * x * (a : L) = r := by
    rw [← hkr]
    have hk_eq : k = (a : L) * r * (a : L)⁻¹ * r⁻¹ := haG.symm
    rw [hk_eq]
    group
  have hx_a : x * (a : L) = (a : L) * r := by
    calc
      x * (a : L) = (a : L) * ((a : L)⁻¹ * x * (a : L)) := by group
      _ = (a : L) * r := by rw [hconj_x]
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hycent⟩
  have hycomm : y * x = x * y := by
    simpa [Section2.elementCentralizer] using
      Subgroup.mem_centralizer_singleton_iff.mp hycent
  let z : K := ⟨(a : L)⁻¹ * y * (a : L), by
    simpa using (inferInstance : K.Normal).conj_mem y hyK (a : L)⁻¹⟩
  have hzComm : (z : L) * r = r * (z : L) := by
    calc
      (z : L) * r = ((a : L)⁻¹ * y * (a : L)) * r := rfl
      _ = (a : L)⁻¹ * y * ((a : L) * r) := by group
      _ = (a : L)⁻¹ * y * (x * (a : L)) := by rw [hx_a]
      _ = (a : L)⁻¹ * (y * x) * (a : L) := by group
      _ = (a : L)⁻¹ * (x * y) * (a : L) := by rw [hycomm]
      _ = ((a : L)⁻¹ * x * (a : L)) *
          ((a : L)⁻¹ * y * (a : L)) := by group
      _ = r * (z : L) := by rw [hconj_x]
  have hzCent : (z : L) ∈ Section2.centralizerIn K (rR : L) := by
    refine ⟨z.2, ?_⟩
    change (z : L) ∈ Subgroup.centralizer ({(rR : L)} : Set L)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [rR] using hzComm)
  have hzBot : (z : L) ∈ (⊥ : Subgroup L) := by
    simpa [hcent rR hrne] using hzCent
  have hz_eq : (z : L) = 1 := by simpa using hzBot
  have hy_eq : y = 1 := by
    have := congrArg (fun t : L => (a : L) * t * (a : L)⁻¹) hz_eq
    simpa [z, mul_assoc] using this
  simp [hy_eq]

public theorem theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
    {L : Type u} [Group L] [Finite L] {L0 H : Subgroup L}
    (hfrob : frobeniusWithKernel L0 H) :
    ∀ x : L, x ∈ L0 → x ∉ H → Section2.centralizerIn H x = ⊥ := by
  intro x hxL hxnotH
  rcases hfrob with ⟨hHL, hHnormal, R, hcomp, _hHne, _hRne, hfixedR⟩
  let Hloc : Subgroup L0 := H.subgroupOf L0
  have : Hloc.Normal := by simpa [Hloc] using hHnormal
  let xL : L0 := ⟨x, hxL⟩
  have hxnotHloc : xL ∉ Hloc := by
    intro hxHloc
    exact hxnotH (by simpa [Hloc, xL, Subgroup.mem_subgroupOf] using hxHloc)
  have hloc : Section2.centralizerIn Hloc xL = ⊥ :=
    theorem_6_8_frobenius_complement_centralizerIn_eq_bot
      (K := Hloc) (R := R) hcomp hfixedR hxnotHloc
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyH, hycent⟩
  have hyL : y ∈ L0 := hHL hyH
  let yL : L0 := ⟨y, hyL⟩
  have hyLoc : yL ∈ Section2.centralizerIn Hloc xL := by
    refine ⟨?_, ?_⟩
    · simpa [Hloc, yL, Subgroup.mem_subgroupOf] using hyH
    · change yL ∈ Subgroup.centralizer ({xL} : Set L0)
      have hycomm : y * x = x * y := by
        simpa [Section2.elementCentralizer] using
          Subgroup.mem_centralizer_singleton_iff.mp hycent
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        apply Subtype.ext
        exact hycomm)
  have hyBot : (yL : L0) ∈ (⊥ : Subgroup L0) := by
    simpa [hloc] using hyLoc
  have hy_eq : y = 1 := by
    simpa [yL] using congrArg Subtype.val (by simpa using hyBot : yL = 1)
  simp [hy_eq]

theorem theorem_6_8_caseA_centralizerIn_top_eq_H_of_W1_fixed
    {L : Type u} [Group L]
    {H W1 Z : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hZcenter : Z ≤ centerIn H)
    (hfixed : ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥)
    (z : Z) (hz : z ≠ 1) :
    Section2.centralizerIn (⊤ : Subgroup L) (z : L) = H := by
  apply le_antisymm
  · intro x hx
    rcases hsemi.mul_surjective x trivial with ⟨h, hhH, r, hrW1, hx_eq⟩
    have hzcenter : (z : L) ∈ centerIn H := hZcenter z.2
    have hxcomm : x * (z : L) = (z : L) * x := by
      exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hhcomm : h * (z : L) = (z : L) * h := by
      exact (Subgroup.mem_centralizer_iff.mp hzcenter.2) h hhH
    have hrcomm : r * (z : L) = (z : L) * r := by
      have hxcomm' : (h * r) * (z : L) = (z : L) * (h * r) := by
        simpa [hx_eq] using hxcomm
      calc
        r * (z : L) = h⁻¹ * (h * (r * (z : L))) := by group
        _ = h⁻¹ * ((h * r) * (z : L)) := by group
        _ = h⁻¹ * ((z : L) * (h * r)) := by rw [hxcomm']
        _ = h⁻¹ * (((z : L) * h) * r) := by group
        _ = h⁻¹ * ((h * (z : L)) * r) := by rw [← hhcomm]
        _ = (z : L) * r := by group
    have hzcentR : (z : L) ∈ Section2.centralizerIn Z (r : L) := by
      constructor
      · exact z.2
      · change (z : L) ∈ Subgroup.centralizer ({(r : L)} : Set L)
        exact Subgroup.mem_centralizer_singleton_iff.mpr hrcomm.symm
    have hr_eq : r = 1 := by
      by_contra hrne
      let rW : W1 := ⟨r, hrW1⟩
      have hrWne : rW ≠ 1 := by
        intro hrW
        apply hrne
        simpa [rW] using congrArg Subtype.val hrW
      have hbot := hfixed rW hrWne
      have hzbot : (z : L) ∈ (⊥ : Subgroup L) := by
        simpa [rW, hbot] using
          (show (z : L) ∈ Section2.centralizerIn Z (rW : L) from hzcentR)
      apply hz
      apply Subtype.ext
      simpa using hzbot
    rw [hx_eq, hr_eq, mul_one]
    exact hhH
  · intro h hhH
    have hzcenter : (z : L) ∈ centerIn H := hZcenter z.2
    constructor
    · trivial
    · change h ∈ Subgroup.centralizer ({(z : L)} : Set L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hzcenter.2) h hhH

theorem theorem_6_8_centralizerIn_top_map_subtype
    {G : Type u} [Group G]
    {L : Subgroup G} (z : L) :
    (Section2.centralizerIn (⊤ : Subgroup L) z).map L.subtype =
      Section2.centralizerIn L ((z : L) : G) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    constructor
    · exact y.2
    · change ((y : L) : G) ∈ Subgroup.centralizer ({((z : L) : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hycomm : y * z = z * y := by
        exact Subgroup.mem_centralizer_singleton_iff.mp hy.2
      exact congrArg Subtype.val hycomm
  · intro hx
    let y : L := ⟨x, hx.1⟩
    refine ⟨y, ?_, rfl⟩
    constructor
    · trivial
    · change y ∈ Subgroup.centralizer ({z} : Set L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxcomm : x * ((z : L) : G) = ((z : L) : G) * x := by
        exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
      apply Subtype.ext
      exact hxcomm

theorem theorem_6_8_natCard_centralizerIn_subtypeMap
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L} (z : Z) :
    Nat.card (Section2.centralizerIn L
      (((theorem_6_8_subtypeMapEquiv L Z) z : Z.map L.subtype) : G)) =
      Nat.card (Section2.centralizerIn (⊤ : Subgroup L) (z : L)) := by
  rw [show (((theorem_6_8_subtypeMapEquiv L Z) z : Z.map L.subtype) : G) =
      ((z : L) : G) from rfl]
  rw [← theorem_6_8_centralizerIn_top_map_subtype (L := L) (z := (z : L))]
  exact Subgroup.card_map_of_injective
    (K := Section2.centralizerIn (⊤ : Subgroup L) (z : L))
    (f := L.subtype) L.subtype_injective

theorem theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_frobenius
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H)
    (hZH : Z ≤ H) :
    ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥ := by
  intro r hrne
  have hrnotH : (r : L) ∉ H := by
    intro hrH
    have hrInf : (r : L) ∈ H ⊓ W1 := ⟨hrH, r.2⟩
    have hrBot : (r : L) ∈ (⊥ : Subgroup L) := by
      simpa [hsemi.inf_eq_bot] using hrInf
    apply hrne
    apply Subtype.ext
    simpa using hrBot
  have hcentH : Section2.centralizerIn H (r : L) = ⊥ :=
    theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      hfrob (r : L) trivial hrnotH
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxcentH : (x : L) ∈ Section2.centralizerIn H (r : L) :=
    ⟨hZH hx.1, hx.2⟩
  have hxbot : (x : L) ∈ (⊥ : Subgroup L) := by
    simpa [hcentH] using hxcentH
  simpa using hxbot

theorem theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_caseC2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z) :
    ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥ := by
  classical
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hdirect, _hWodd⟩
  rcases hA with ⟨hcenterW2, hZeq⟩
  have hZcenter : Z ≤ centerIn H := by
    rw [hZeq]
    exact inf_le_left
  intro r hr
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxZ : x ∈ Z := hx.1
  have hxCenter : x ∈ centerIn H := hZcenter hxZ
  have hxH : x ∈ H := hxCenter.1
  have hxcentH : x ∈ Section2.centralizerIn H (r : L) := ⟨hxH, hx.2⟩
  have hxW2 : x ∈ W2 := by
    have hcent_eq := hcentW1 r hr
    simpa [hcent_eq] using hxcentH
  have hxInf : x ∈ centerIn H ⊓ W2 := ⟨hxCenter, hxW2⟩
  have hxbot : x ∈ (⊥ : Subgroup L) := by
    simpa [hcenterW2] using hxInf
  simpa using hxbot

theorem theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_branch
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥ := by
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, hbranch⟩
  rcases hbranch with hfrob | hcaseC2
  · exact theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_frobenius
      hsemi hfrob hfamily.1
  · exact theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_caseC2 hcaseC2 hA

theorem theorem_6_8_caseA_constantCentralizerOrderOnNonidentity_local
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    constantCentralizerOrderOnNonidentity Z (⊤ : Subgroup L) := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hZcenter : Z ≤ centerIn H := (theorem_6_8_caseA_Z_center_normal hA).1
  have hfixed : ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥ :=
    theorem_6_8_caseA_W1_centralizerIn_Z_eq_bot_of_branch
      (h68 := ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩) hA hfamily
  intro z1 z2 hz1 hz2
  rw [theorem_6_8_caseA_centralizerIn_top_eq_H_of_W1_fixed
      hsemi hZcenter hfixed z1 hz1,
    theorem_6_8_caseA_centralizerIn_top_eq_H_of_W1_fixed
      hsemi hZcenter hfixed z2 hz2]

theorem theorem_6_8_caseA_constantCentralizerOrderOnNonidentity_ambient
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    constantCentralizerOrderOnNonidentity (Z.map L.subtype) L := by
  let e := theorem_6_8_subtypeMapEquiv L Z
  have hlocal :=
    theorem_6_8_caseA_constantCentralizerOrderOnNonidentity_local h68 hA hfamily
  intro y1 y2 hy1 hy2
  have hz1 : e.symm y1 ≠ 1 := by
    intro hz
    apply hy1
    have := congrArg e hz
    simpa [e] using this
  have hz2 : e.symm y2 ≠ 1 := by
    intro hz
    apply hy2
    have := congrArg e hz
    simpa [e] using this
  have hloc := hlocal (e.symm y1) (e.symm y2) hz1 hz2
  calc
    Nat.card (Section2.centralizerIn L (y1 : G)) =
        Nat.card (Section2.centralizerIn L
          ((e (e.symm y1) : Z.map L.subtype) : G)) := by simp [e]
    _ = Nat.card (Section2.centralizerIn (⊤ : Subgroup L)
        ((e.symm y1 : Z) : L)) :=
        theorem_6_8_natCard_centralizerIn_subtypeMap (L := L) (Z := Z) (e.symm y1)
    _ = Nat.card (Section2.centralizerIn (⊤ : Subgroup L)
        ((e.symm y2 : Z) : L)) := hloc
    _ = Nat.card (Section2.centralizerIn L
        ((e (e.symm y2) : Z.map L.subtype) : G)) := by
        rw [theorem_6_8_natCard_centralizerIn_subtypeMap
          (L := L) (Z := Z) (e.symm y2)]
    _ = Nat.card (Section2.centralizerIn L (y2 : G)) := by simp [e]

theorem theorem_6_8_theorem_6_7_base_hypothesis_ambient_card_of_caseA
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    {p : ℕ} [Fact p.Prime]
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∃ P : Sylow p G,
      theorem_6_7_base_hypothesis p P L (Z.map L.subtype) ∧
        Nat.card (P : Subgroup G) =
          Nat.card (Z.map L.subtype) * Z.relIndex H := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hZne : Z ≠ ⊥ := theorem_6_8_caseA_Z_ne_bot hnil ⟨p, hpQ⟩ hA
  have hZdata := theorem_6_8_caseA_Z_center_normal hA
  have : Z.Normal := hZdata.2
  rcases theorem_6_8_sylow_of_nonabelianPQuotient_bot h68' hpQ with
    ⟨PL, hPL⟩
  have hnormHmap :
      Subgroup.normalizer (((H.map L.subtype : Subgroup G) : Set G)) = L := by
    rw [theorem_6_8_normalizer_map_subtype_eq_setNormalizer_punctured]
    exact hTI.2.2.2
  rcases theorem_6_8_sylow_map_subtype_of_sylow_normalizer PL hPL hnormHmap with
    ⟨Pamb, hPamb⟩
  refine ⟨Pamb, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hPamb]
      exact hnormHmap.symm
    · exact hodd
    · simpa [hPamb, theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured
        (L := L) (H := H)] using hTI
    · exact theorem_6_8_map_subtype_ne_bot hZne
    · simpa [hPamb] using
        theorem_6_8_map_subtype_le_centerIn
          (G := G) (L := L) (H := H) (Z := Z) hZdata.1
    · exact theorem_6_8_map_subtype_normal_subgroupOf (G := G) (L := L) (Z := Z)
    · exact theorem_6_8_caseA_constantCentralizerOrderOnNonidentity_ambient
        h68' hA hfamily
  · have hZH : Z ≤ H := fun z hz => (hZdata.1 hz).1
    have hHcard : Nat.card H = Nat.card Z * Z.relIndex H := by
      have hidx :
          (Z.subgroupOf H).index * Nat.card (Z.subgroupOf H) = Nat.card H := by
        exact Subgroup.index_mul_card (H := Z.subgroupOf H)
      have hcard : Nat.card (Z.subgroupOf H) = Nat.card Z := by
        exact natCard_subgroupOf_eq Z H hZH
      have hidx_eq : (Z.subgroupOf H).index = Z.relIndex H := by
        rfl
      rw [hidx_eq, hcard] at hidx
      simpa [mul_comm] using hidx.symm
    have hPcardH : Nat.card (Pamb : Subgroup G) = Nat.card H := by
      calc
        Nat.card (Pamb : Subgroup G) = Nat.card (H.map L.subtype) := by rw [hPamb]
        _ = Nat.card H := by
          simpa using
            (Subgroup.card_map_of_injective (K := H) (f := L.subtype)
              L.subtype_injective)
    have hZmapcard : Nat.card (Z.map L.subtype) = Nat.card Z := by
      exact Subgroup.card_map_of_injective (K := Z) (f := L.subtype)
        L.subtype_injective
    rw [hPcardH, hHcard, hZmapcard]

theorem theorem_6_8_scalarProduct_subgroupRestriction_regular_add_of_prime_card
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {ψ : Section1.ClassFunction G}
    {a b : ℂ} (ha : star a = a)
    (hres : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    Section1.scalarProduct Z φ
      (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ)) = a := by
  let e := theorem_6_8_subtypeMapEquiv L Z
  have htransport :
      theorem_6_8_transportClassFunction e
        (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ)) =
          Section1.subgroupRestriction (Z.map L.subtype) ψ := by
    simpa [e] using theorem_6_8_transport_subtypeMap_subgroupRestriction
      (L := L) (Z := Z) ψ
  have hcoeff :
      Section1.scalarProduct (Z.map L.subtype)
        (theorem_6_8_transportClassFunction e φ)
        (theorem_6_8_transportClassFunction e
          (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ))) = a := by
    rw [htransport, hres]
    exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_subtypeMap
      hprime hφ hφne ha
  have hpreserve :=
    theorem_6_8_scalarProduct_transportClassFunction e φ
      (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ))
  rw [hpreserve] at hcoeff
  exact hcoeff

theorem theorem_6_8_regular_add_coefficient_mem_int_of_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {ψ : Section1.ClassFunction G}
    (hψvirt : Theory.Character.IsVirtualCharacter ψ)
    {a b : ℂ}
    (hres : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    a ∈ Set.range (fun n : ℤ => (n : ℂ)) := by
  let e := theorem_6_8_subtypeMapEquiv L Z
  have hφvirt :
      Theory.Character.IsVirtualCharacter (theorem_6_8_transportClassFunction e φ) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (theorem_6_8_transportClassFunction_irreducible e hφ)
  have hresvirt :
      Theory.Character.IsVirtualCharacter
        (Section1.subgroupRestriction (Z.map L.subtype) ψ) :=
    theorem_6_8_subgroupRestriction_isVirtualCharacter (Z.map L.subtype) hψvirt
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hφvirt hresvirt with
    ⟨n, hn⟩
  have hcoeff :
      Section1.scalarProduct (Z.map L.subtype)
        (theorem_6_8_transportClassFunction e φ)
        (Section1.subgroupRestriction (Z.map L.subtype) ψ) = star a := by
    rw [hres]
    exact theorem_6_8_scalarProduct_regular_add_principal_right_of_prime_card_subtypeMap_star
      hprime hφ hφne
  have hstar_int : star a = (n : ℂ) := hcoeff.symm.trans hn
  have ha_int : a = (n : ℂ) := by
    calc
      a = star (star a) := by simp
      _ = star (n : ℂ) := by rw [hstar_int]
      _ = (n : ℂ) := by simp
  exact ⟨n, ha_int.symm⟩

theorem theorem_6_8_regular_add_coefficient_star_eq_self_of_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    (hprime : Nat.Prime (Nat.card Z))
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {ψ : Section1.ClassFunction G}
    (hψvirt : Theory.Character.IsVirtualCharacter ψ)
    {a b : ℂ}
    (hres : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    star a = a := by
  rcases theorem_6_8_regular_add_coefficient_mem_int_of_virtual
      hprime hφ hφne hψvirt hres with
    ⟨n, hn⟩
  rw [← hn]
  simp

theorem theorem_6_8_scalarProduct_transform_eq_restriction_of_induction
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {α : Section1.ClassFunction L} {ψ : Section1.ClassFunction G}
    (hTα : T α = Section1.inducedCF L α)
    (hψclass : Section1.IsClassFunction ψ) :
    Section1.scalarProduct G (T α) ψ =
      Section1.scalarProduct L α (Section1.subgroupRestriction L ψ) := by
  rw [hTα]
  exact Section1.inducedClassFunction_frobenius_general L α ψ hψclass

theorem theorem_6_8_subgroupRestriction_isClassFunction
    {G : Type u} [Group G] {H : Subgroup G}
    {φ : Section1.ClassFunction G}
    (hφ : Section1.IsClassFunction φ) :
    Section1.IsClassFunction (Section1.subgroupRestriction H φ) := by
  intro x h
  exact hφ x h

theorem theorem_6_8_isClassFunction_of_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Section1.IsClassFunction χ := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  rw [hχeq]
  intro x g
  simp [Theory.Character.virtualCharacterOfRepresentations]

theorem theorem_6_8_coherentExtension_mem_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    Section1.IsClassFunction (τ₁ η) := by
  exact theorem_6_8_isClassFunction_of_isVirtualCharacter
    (hτ₁.2.1 η (Section5.integerSpan_of_mem Y hηY))

theorem theorem_6_8_coherentExtension_scalarProduct_of_mem
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    Section1.scalarProduct G (τ₁ η₁) (τ₁ η) =
      Section1.scalarProduct L η₁ η := by
  exact Section5.isCFLinearIsometryOnSpan_apply_of_mem
    hτ₁.1 hη₁Y hηY

public theorem theorem_6_8_coherentExtension_mem_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y)
    (hηirr : Section1.IsIrreducibleCharacterOnGroup η) :
    Section3.IsSignedIrreducibleCharacter (τ₁ η) := by
  have hvirt : Theory.Character.IsVirtualCharacter (τ₁ η) :=
    hτ₁.2.1 η (Section5.integerSpan_of_mem Y hηY)
  have hself_src : Section1.scalarProduct L η η = 1 := by
    rcases hηirr with ⟨_n, ρ, hρirr, hηeq⟩
    rw [hηeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hself : Section1.scalarProduct G (τ₁ η) (τ₁ η) = 1 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ hηY hηY,
      hself_src]
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself

theorem theorem_6_8_regular_add_coefficient_multiple_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y)
    {a b : ℂ}
    (hres : Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    ∃ k : ℤ, a = (Z.relIndex H : ℂ) * (k : ℂ) := by
  classical
  rcases hpQ with ⟨p, hpQp⟩
  rcases hpQp with
    ⟨hbotH, hbotnormH, hbotnorm, hHnorm, hpprime, hQp, hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hpQp' : nonabelianPQuotient (⊥ : Subgroup L) H p :=
    ⟨hbotH, hbotnormH, hbotnorm, hHnorm, hpprime, hQp, hnoncomm⟩
  rcases theorem_6_8_theorem_6_7_base_hypothesis_ambient_card_of_caseB
      h68 hpQp' hcase hB with
    ⟨P, hbase, hPcard⟩
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68 hcase hB with
    ⟨hZne, _hZcent, _hZnorm⟩
  have hZmapne : Z.map L.subtype ≠ (⊥ : Subgroup G) :=
    theorem_6_8_map_subtype_ne_bot hZne
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hZmapne with ⟨z, hz⟩
  have hconst : constantOnNonidentitySubgroup (Z.map L.subtype) (τ₁ η) :=
    theorem_6_8_2_1_constantOn_image_subgroup_of_statement
      theorem_6_8_2_1_of_familyData h68 ⟨p, hpQp'⟩ hcase hB
      hfamily hτ₁ hηY
  have hsigned : Section3.IsSignedIrreducibleCharacter (τ₁ η) :=
    theorem_6_8_coherentExtension_mem_signedIrreducible hτ₁ hηY
      (theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY)
  exact theorem_6_8_regular_add_coefficient_multiple_of_theorem_6_7_signed
    P L (Z.map L.subtype) hbase hsigned hconst hres z hz hPcard

theorem theorem_6_8_scalarProduct_inducedCF_subgroupRestriction_left
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) (H : Subgroup K)
    {φ : Section1.ClassFunction H} {ψ : Section1.ClassFunction G}
    (hψclass : Section1.IsClassFunction ψ) :
    Section1.scalarProduct K (Section1.inducedCF H φ)
      (Section1.subgroupRestriction K ψ) =
    Section1.scalarProduct H φ
      (Section1.subgroupRestriction H (Section1.subgroupRestriction K ψ)) := by
  exact Section1.inducedClassFunction_frobenius_general H φ
    (Section1.subgroupRestriction K ψ)
    (theorem_6_8_subgroupRestriction_isClassFunction hψclass)

theorem theorem_6_8_scalarProduct_transform_sub_induced_eq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction Z} {η₁ : Section1.ClassFunction L}
    {ψ : Section1.ClassFunction G}
    {c a : ℂ}
    (hTα : T (Section1.inducedCF Z φ - c • η₁) =
      Section1.inducedCF L (Section1.inducedCF Z φ - c • η₁))
    (hψclass : Section1.IsClassFunction ψ)
    (hcoeff : Section1.scalarProduct Z φ
      (Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ)) = a) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - c • η₁)) ψ =
      a - c * Section1.scalarProduct L η₁
        (Section1.subgroupRestriction L ψ) := by
  rw [theorem_6_8_scalarProduct_transform_eq_restriction_of_induction
    hTα hψclass]
  rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left]
  rw [theorem_6_8_scalarProduct_inducedCF_subgroupRestriction_left
    L Z hψclass, hcoeff]

theorem theorem_6_8_scalarProduct_transform_sub_regular_add_of_prime_card
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction Z} {η₁ : Section1.ClassFunction L}
    {ψ : Section1.ClassFunction G}
    (hprime : Nat.Prime (Nat.card Z))
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {c a b : ℂ} (ha : star a = a)
    (hTα : T (Section1.inducedCF Z φ - c • η₁) =
      Section1.inducedCF L (Section1.inducedCF Z φ - c • η₁))
    (hψclass : Section1.IsClassFunction ψ)
    (hres : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - c • η₁)) ψ =
      a - c * Section1.scalarProduct L η₁
        (Section1.subgroupRestriction L ψ) := by
  exact theorem_6_8_scalarProduct_transform_sub_induced_eq hTα hψclass
    (theorem_6_8_scalarProduct_subgroupRestriction_regular_add_of_prime_card
      hprime hφ hφne ha hres)

theorem theorem_6_8_scalarProduct_transform_sub_tau1_regular_add_of_prime_card
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction Z} {η₁ η : Section1.ClassFunction L}
    (hτ₁ : coherentExtension Y T τ₁)
    (hηY : η ∈ Y)
    (hprime : Nat.Prime (Nat.card Z))
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {c a b : ℂ} (ha : star a = a)
    (hTα : T (Section1.inducedCF Z φ - c • η₁) =
      Section1.inducedCF L (Section1.inducedCF Z φ - c • η₁))
    (hres : Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
      a • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype)) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - c • η₁)) (τ₁ η) =
      a - c * Section1.scalarProduct L η₁
        (Section1.subgroupRestriction L (τ₁ η)) := by
  exact theorem_6_8_scalarProduct_transform_sub_regular_add_of_prime_card
    hprime hφ hφne ha hTα
    (theorem_6_8_coherentExtension_mem_isClassFunction hτ₁ hηY) hres

theorem theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L} (hηY : η ∈ Y)
    {c : ℂ}
    (hTα : T (Section1.inducedCF Z φ - c • η₁) =
      Section1.inducedCF L (Section1.inducedCF Z φ - c • η₁)) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
          a • regularCharacter (Z.map L.subtype) +
            b • Section1.principalCharacter (Z.map L.subtype) ∧
        (star a = a →
          Section1.scalarProduct G
            (T (Section1.inducedCF Z φ - c • η₁)) (τ₁ η) =
            a - c * Section1.scalarProduct L η₁
              (Section1.subgroupRestriction L (τ₁ η))) := by
  rcases theorem_6_8_2_2_restriction_regular_add_of_familyData
      h68 hpQ hcase hB hfamily hτ₁ hηY with
    ⟨a, b, hres⟩
  refine ⟨a, b, hres, ?_⟩
  intro ha
  exact theorem_6_8_scalarProduct_transform_sub_tau1_regular_add_of_prime_card
    hτ₁ hηY (theorem_6_8_caseB_Z_prime_card hcase hB)
    hφ hφne ha hTα hres

theorem theorem_6_8_decomposition_of_orthogonal_add_smul
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {A Ycf : Section1.ClassFunction G} {c : ℂ}
    (horth : orthogonalToTransformedFinset Y τ₁ (A + c • Ycf)) :
    ∃ X : Section1.ClassFunction G,
      orthogonalToTransformedFinset Y τ₁ X ∧ A = X - c • Ycf := by
  refine ⟨A + c • Ycf, horth, ?_⟩
  simp

theorem theorem_6_8_2_2_commonY_of_left_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hdecomp : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          ∃ X : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X ∧
              T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
                X - (Z.relIndex H : ℂ) • (τ₁ η₁)) :
    theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ (τ₁ η₁) := by
  exact ⟨hη₁Y, Or.inl rfl, hdecomp⟩

theorem theorem_6_8_2_2_commonY_of_left_orthogonal_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (horth : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          orthogonalToTransformedFinset Y τ₁
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
              (Z.relIndex H : ℂ) • τ₁ η₁)) :
    theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ (τ₁ η₁) := by
  refine theorem_6_8_2_2_commonY_of_left_data hη₁Y ?_
  intro φ hφirr hφne
  exact theorem_6_8_decomposition_of_orthogonal_add_smul
    (horth φ hφirr hφne)

theorem theorem_6_8_2_2_commonY_of_right_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ η₂ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hcard : Y.card = 2)
    (hη₂Y : η₂ ∈ Y)
    (hη₂ne : η₂ ≠ η₁)
    (hdecomp : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          ∃ X : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X ∧
              T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
                X - (Z.relIndex H : ℂ) • (-τ₁ η₂)) :
    theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ (-τ₁ η₂) := by
  exact ⟨hη₁Y, Or.inr ⟨η₂, hcard, hη₂Y, hη₂ne, rfl⟩, hdecomp⟩

theorem theorem_6_8_2_2_commonY_of_right_orthogonal_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ η₂ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hcard : Y.card = 2)
    (hη₂Y : η₂ ∈ Y)
    (hη₂ne : η₂ ≠ η₁)
    (horth : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          orthogonalToTransformedFinset Y τ₁
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
              (Z.relIndex H : ℂ) • (-τ₁ η₂))) :
    theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ (-τ₁ η₂) := by
  refine theorem_6_8_2_2_commonY_of_right_data hη₁Y hcard hη₂Y hη₂ne ?_
  intro φ hφirr hφne
  exact theorem_6_8_decomposition_of_orthogonal_add_smul
    (horth φ hφirr hφne)


theorem theorem_6_8_coherentFamily_of_hypothesis_5_2_and_extension
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {T T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hext : coherentExtension S T T') :
    coherentFamily S T := by
  rcases h52 with ⟨hsetup, R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  rcases hsetup.1 with ⟨χ, hχ⟩
  have hsrc : Section5.sourceVirtualCharacters S := by
    intro ψ hψ
    exact Section5.isVirtualCharacter_of_isCharacter
      (hsetup.2 ⟨ψ, hψ⟩)
  have hnonempty : Section5.integerSpanOnNonempty S Section5.puncturedSet := by
    exact Section5.integerSpanOnNonempty_of_conjugate_pair hχ
      (h52a ⟨χ, hχ⟩).1 (h52a ⟨χ, hχ⟩).2
      (hsetup.2 ⟨χ, hχ⟩)
  rcases hext with ⟨hIso, hvirt, hagree⟩
  exact ⟨hsrc, hnonempty, T', hIso, hvirt, hagree⟩


theorem theorem_6_8_scalarProduct_self_ne_zero_of_character_not_conjugate
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχchar : Section1.IsCharacter χ)
    (hχnotconj : χ ≠ Section1.conjugateCharacter χ) :
    Section1.scalarProduct L χ χ ≠ 0 := by
  intro hzero
  have hself : Section1.scalarProduct L χ χ = (Section5.cfNormSq χ : ℂ) :=
    Section5.scalarProduct_self_eq_cfNormSq_of_character hχchar
  have hcf_complex : (Section5.cfNormSq χ : ℂ) = 0 := by
    simpa [hself] using hzero
  have hcf : Section5.cfNormSq χ = 0 := by
    exact_mod_cast hcf_complex
  have hχzero : χ = 0 := Section5.cfNormSq_eq_zero hcf
  apply hχnotconj
  ext g
  simp [hχzero, Section1.conjugateCharacter]


theorem theorem_6_8_X_degree_eq_cardW1_mul
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ X) :
    ∃ a : ℕ, Section1.degree χ = (a * Nat.card W1 : ℂ) := by
  rcases hfamily with ⟨_hZH, _hSZ, hXeq, _hY⟩
  have hχS : χ ∈ S := by
    have hχdiff : χ ∈ S \ SZ := by
      simpa [hXeq] using hχX
    exact (Finset.mem_sdiff.mp hχdiff).1
  rcases inducedKernelFamily_degree_data hSbot hχS with
    ⟨dθ, dχ, hdeg, hdχ, _hdvd⟩
  refine ⟨dθ, ?_⟩
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
    simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  rw [hdeg, hdχ, hHindex]
  simp [Nat.mul_comm]

theorem theorem_6_8_X_degree_div_cardW1
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ X) :
    ∃ a : ℕ,
      Section1.degree χ = (a * Nat.card W1 : ℂ) ∧
        Section1.degree χ / (Nat.card W1 : ℂ) = (a : ℂ) := by
  rcases theorem_6_8_X_degree_eq_cardW1_mul
      hSbot hsemi hfamily hχX with ⟨a, hχdeg⟩
  refine ⟨a, hχdeg, ?_⟩
  have hW1card_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.card_pos (α := W1)))
  rw [hχdeg]
  field_simp [hW1card_ne]

theorem theorem_6_8_X_degree_ratio_gt_one
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    {χ : Section1.ClassFunction L} {c : ℕ}
    (hχX : χ ∈ X)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ)) :
    1 < c := by
  classical
  rcases hfamily with ⟨_hZH, hSZ, hXeq, _hY⟩
  have hχdiff : χ ∈ S \ SZ := by
    simpa [hXeq] using hχX
  have hχS : χ ∈ S := (Finset.mem_sdiff.mp hχdiff).1
  have hχnotSZ : χ ∉ SZ := (Finset.mem_sdiff.mp hχdiff).2
  rcases (hSbot.2 χ).mp hχS with
    ⟨θ, hθirr, hθbot, hθne, hχeq⟩
  have hχdeg_ind :
      Section1.degree χ =
        (H.relIndex (⊤ : Subgroup L) : ℂ) * Section1.degree θ := by
    rw [hχeq, Section1.degree_inducedClassFunction H θ]
    simp [Subgroup.relIndex_top_right]
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
    simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hW1card_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hθdegree_eq_c : Section1.degree θ = (c : ℂ) := by
    have hratio_eq :
        Section1.degree χ / (Nat.card W1 : ℂ) = Section1.degree θ := by
      rw [hχdeg_ind, hHindex]
      field_simp [hW1card_ne]
    exact hratio_eq.symm.trans hχratio
  by_contra hcnot
  have hc_le : c ≤ 1 := Nat.le_of_not_gt hcnot
  rcases theorem_6_6_positive_degree_nat_of_irreducible hθirr with
    ⟨d, hdpos, hθdegree_nat⟩
  have hdc : d = c := by
    have hcast : (d : ℂ) = (c : ℂ) := by
      rw [← hθdegree_nat, hθdegree_eq_c]
    exact_mod_cast hcast
  have hcpos : 0 < c := by omega
  have hc_eq_one : c = 1 := by omega
  have hθdegree_one : Section1.degree θ = 1 := by
    simpa [hc_eq_one] using hθdegree_eq_c
  have hθcomm : Section1.subgroupInKernel' θ (commutator H) :=
    theorem_6_8_subgroupInKernel_commutator_of_irreducible_degree_one
      hθirr hθdegree_one
  have hθcomm' : Section1.subgroupInKernel' θ (⁅H,H⁆.subgroupOf H) := by
    simpa [theorem_6_8_subgroupOf_commutator_eq H] using hθcomm
  have hθZ : Section1.subgroupInKernel' θ (Z.subgroupOf H) := by
    intro z
    exact hθcomm' ⟨(z : H), hZcomm z.property⟩
  have hχSZ : χ ∈ SZ :=
    (hSZ.2 χ).mpr ⟨θ, hθirr, hθZ, hθne, hχeq⟩
  exact hχnotSZ hχSZ

theorem theorem_6_8_mem_Y_degree_eq_cardW1
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    Section1.degree η = (Nat.card W1 : ℂ) := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hH1norm : ⁅H,H⁆.Normal := Subgroup.commutator_normal H H
  have hcommHyp : commutatorQuotientHypothesis (⊥ : Subgroup L) ⁅H,H⁆ H :=
    theorem_6_8_commutatorQuotient_bot_commutator H hHnorm
  have hcomm : IsMulCommutative (H ⧸ ⁅H,H⁆.subgroupOf H) :=
    commutatorQuotientHypothesis_quotient_commutative hH1norm hcommHyp
  have hdeg : Section1.degree η = (H.relIndex (⊤ : Subgroup L) : ℂ) :=
    inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      hY hH1norm hcomm hηY
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
    simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  simpa [hHindex] using hdeg

theorem theorem_6_8_induced_constituent_shift_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {ι : Type*}
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    (i : ι)
    (hdegree : Section1.degree (ψ i) = (e i : ℂ))
    (hIndX : Section1.inducedCF H (ψ i) ∈ X)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y) :
    Section1.degree (Section1.inducedCF H (ψ i)) / (Nat.card W1 : ℂ) =
        (e i : ℂ) ∧
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) := by
  classical
  have hIndDeg :
      Section1.degree (Section1.inducedCF H (ψ i)) =
        (Nat.card W1 : ℂ) * (e i : ℂ) := by
    have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
      simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
    rw [Section1.degree_inducedClassFunction H (ψ i)]
    rw [Subgroup.relIndex_top_right] at hHindex
    rw [hHindex, hdegree]
  have hW1card_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.card_pos (α := W1)))
  have hratio :
      Section1.degree (Section1.inducedCF H (ψ i)) / (Nat.card W1 : ℂ) =
        (e i : ℂ) := by
    rw [hIndDeg]
    field_simp [hW1card_ne]
  have hχU : Section1.inducedCF H (ψ i) ∈ X ∪ Y :=
    Finset.mem_union.mpr (Or.inl hIndX)
  have hηU : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
  have hχspan : Section5.integerSpan (X ∪ Y) (Section1.inducedCF H (ψ i)) :=
    Section5.integerSpan_of_mem (X ∪ Y) hχU
  have hηspan : Section5.integerSpan (X ∪ Y) η₁ :=
    Section5.integerSpan_of_mem (X ∪ Y) hηU
  have hηsmul : Section5.integerSpan (X ∪ Y) ((e i : ℂ) • η₁) := by
    simpa using
      Section5.integerSpan_zsmul (S := X ∪ Y) (φ := η₁) (e i : ℤ) hηspan
  have hspan :
      Section5.integerSpan (X ∪ Y)
        (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) :=
    Section5.integerSpan_sub hχspan hηsmul
  have hηdeg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hη₁Y
  have hdeg0 :
      Section1.degree (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) = 0 := by
    rw [Section1.degree_apply] at hIndDeg hηdeg ⊢
    simp [hIndDeg, hηdeg]
    ring
  exact ⟨hratio,
    ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩⟩

theorem theorem_6_8_familyData_X_conjugate_mem
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχX : χ ∈ X) :
    Section1.conjugateCharacter χ ∈ X := by
  rcases hfamily with ⟨_hZH, hSZ, hXeq, _hY⟩
  exact theorem_6_6_diff_conjugate_closed hSbot hSZ hXeq χ hχX

theorem theorem_6_8_X_smul_Y_source_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    {χ η : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hηY : η ∈ Y) (e : ℕ) :
    Section1.scalarProduct L χ ((e : ℂ) • η) = 0 ∧
      Section1.scalarProduct L
        (Section1.conjugateCharacter χ) ((e : ℂ) • η) = 0 := by
  have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
  have hηU : η ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hηY)
  have hηnotX : η ∉ X :=
    theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
  have hχη_zero : Section1.scalarProduct L χ η = 0 := by
    have hχneη : χ ≠ η := by
      intro hχeq
      exact hηnotX (by simpa [← hχeq] using hχX)
    exact h52c hχU hηU hχneη
  have hχbarX : Section1.conjugateCharacter χ ∈ X :=
    theorem_6_8_familyData_X_conjugate_mem hSbot hfamily hχX
  have hχbarU : Section1.conjugateCharacter χ ∈ X ∪ Y :=
    Finset.mem_union.mpr (Or.inl hχbarX)
  have hχbarη_zero :
      Section1.scalarProduct L (Section1.conjugateCharacter χ) η = 0 := by
    have hχbarneη : Section1.conjugateCharacter χ ≠ η := by
      intro hχbareq
      exact hηnotX (by simpa [← hχbareq] using hχbarX)
    exact h52c hχbarU hηU hχbarneη
  constructor
  · rw [Section1.scalarProduct_smul_right]
    simp [hχη_zero]
  · rw [Section1.scalarProduct_smul_right]
    simp [hχbarη_zero]

theorem theorem_6_8_conjugate_diff_integerSpanOn_of_hypothesis_5_2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {U : Finset (Section1.ClassFunction L)}
    (hsetup : Section5.hypothesis_5_2_setup_statement U)
    (h52a : Section5.hypothesis_5_2_a_statement U)
    (χ : U) :
    Section5.integerSpanOn U Section5.puncturedSet
      ((χ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (χ : Section1.ClassFunction L)) := by
  have hχspan : Section5.integerSpan U (χ : Section1.ClassFunction L) :=
    Section5.integerSpan_of_mem U χ.2
  have hχbarspan :
      Section5.integerSpan U
        (Section1.conjugateCharacter (χ : Section1.ClassFunction L)) :=
    Section5.integerSpan_of_mem U (h52a χ).1
  have hspan :
      Section5.integerSpan U
        ((χ : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χ : Section1.ClassFunction L)) :=
    Section5.integerSpan_sub hχspan hχbarspan
  have hdeg0 :
      Section1.degree
        ((χ : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χ : Section1.ClassFunction L)) = 0 := by
    change Section1.degree (χ : Section1.ClassFunction L) -
        Section1.degree
          (Section1.conjugateCharacter (χ : Section1.ClassFunction L)) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter (hsetup.2 χ)]
    simp
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩

theorem theorem_6_8_induced_constituent_pf54_projection_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    {ι : Type*}
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    (i : ι)
    (hdegree : Section1.degree (ψ i) = (e i : ℂ))
    (hIndX : Section1.inducedCF H (ψ i) ∈ X)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y) :
    ∃ Xbig Yrem : Section1.ClassFunction G,
      Section5.integerSpan
          (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
          Xbig ∧
        Section5.orthogonalToFinset
          (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
          Yrem ∧
        T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) = Xbig - Yrem ∧
        Section5.cfNormSq Xbig ≥ Section5.cfNormSq (Section1.inducedCF H (ψ i)) ∧
        (Section5.cfNormSq Yrem ≥ Section5.cfNormSq ((e i : ℂ) • η₁) →
          Section5.cfNormSq Xbig = Section5.cfNormSq (Section1.inducedCF H (ψ i)) ∧
            Section5.cfNormSq Yrem = Section5.cfNormSq ((e i : ℂ) • η₁) ∧
              Section5.isSubsetSumOf
                (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
                Xbig) := by
  classical
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  let χsub : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} :=
    ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩
  have hηU : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
  have hηspan : Section5.integerSpan (X ∪ Y) η₁ :=
    Section5.integerSpan_of_mem (X ∪ Y) hηU
  have hψanchor_span :
      Section5.integerSpan (X ∪ Y) ((e i : ℂ) • η₁) := by
    simpa using
      Section5.integerSpan_zsmul (S := X ∪ Y) (φ := η₁) (e i : ℤ) hηspan
  have hshift_span :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) :=
    (theorem_6_8_induced_constituent_shift_integerSpanOn
      hsemi hfamily e ψ i hdegree hIndX hη₁Y).2
  have hdiff_conj :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        ((χsub : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χsub : Section1.ClassFunction L)) :=
    theorem_6_8_conjugate_diff_integerSpanOn_of_hypothesis_5_2
      hsetup h52a χsub
  have horth :=
    theorem_6_8_X_smul_Y_source_orthogonal
      hSbot hfamily hZcomm h52c hIndX hη₁Y (e i)
  simpa [χsub] using
    Section5.theorem_5_4_projection_data_pf57
      (S := X ∪ Y) (T := T) (R := R)
      hsetup h52a h52b h52c h52d h52e
      χsub ((e i : ℂ) • η₁)
      hψanchor_span hshift_span hdiff_conj horth.1 horth.2

theorem theorem_6_8_scalarProduct_subsetSum_right_eq_zero_of_orthogonalToFinset
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G}
    (horth : Section5.orthogonalToFinset R φ)
    (hsubset : Section5.isSubsetSumOf R ψ) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  rcases hsubset with ⟨E, hE, rfl⟩
  revert hE
  induction E using Finset.induction_on with
  | empty =>
      intro _hE
      simp [Section1.scalarProduct]
  | @insert a E ha ih =>
      intro hE
      rw [Finset.sum_insert ha, Section5.scalarProduct_add_right]
      have ha0 : Section1.scalarProduct G φ a = 0 :=
        horth (hE (Finset.mem_insert_self a E))
      have hEsub : E ⊆ R := by
        intro χ hχ
        exact hE (Finset.mem_insert_of_mem hχ)
      have hE0 : Section1.scalarProduct G φ (Finset.sum E fun χ => χ) = 0 :=
        ih hEsub
      simp [ha0, hE0]

set_option maxHeartbeats 1000000 in
theorem theorem_6_8_tau1_mem_subsetSum_R_of_union_hypothesis_5_2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (_h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (_h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    (hτ₁ : coherentExtension Y T τ₁)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    Section5.isSubsetSumOf
      (R ⟨η, Finset.mem_union.mpr (Or.inr hηY)⟩) (τ₁ η) := by
  classical
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have hηbarY : Section1.conjugateCharacter η ∈ Y :=
    inducedKernelFamily_conjugate_mem hY hηY
  let ηU : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} :=
    ⟨η, Finset.mem_union.mpr (Or.inr hηY)⟩
  let pair : Finset (Section1.ClassFunction L) :=
    {(ηU : Section1.ClassFunction L),
      Section1.conjugateCharacter (ηU : Section1.ClassFunction L)}
  have hpairSubY :
      pair ⊆ Y := by
    intro χ hχ
    simp [pair, ηU] at hχ
    rcases hχ with rfl | rfl
    · exact hηY
    · exact hηbarY
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan pair τ₁ := by
    exact Section5.isCFLinearIsometryOnSpan_mono hpairSubY hτ₁.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters pair τ₁ := by
    exact Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSubY hτ₁.2.1
  have hpairη : Section5.integerSpan pair (ηU : Section1.ClassFunction L) := by
    exact Section5.integerSpan_of_mem pair (by simp [pair])
  have hpairηbar :
      Section5.integerSpan pair
        (Section1.conjugateCharacter (ηU : Section1.ClassFunction L)) := by
    exact Section5.integerSpan_of_mem pair (by simp [pair])
  have hpairDiff :
      Section5.integerSpan pair
        ((ηU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (ηU : Section1.ClassFunction L)) :=
    Section5.integerSpan_sub hpairη hpairηbar
  have hηspan : Section5.integerSpan Y η :=
    Section5.integerSpan_of_mem Y hηY
  have hηbarspan :
      Section5.integerSpan Y (Section1.conjugateCharacter η) :=
    Section5.integerSpan_of_mem Y hηbarY
  have hdiff_span :
      Section5.integerSpan Y (η - Section1.conjugateCharacter η) :=
    Section5.integerSpan_sub hηspan hηbarspan
  have hηchar : Section1.IsCharacter η := hsetup.2 ηU
  have hdiff_degree :
      Section1.degree (η - Section1.conjugateCharacter η) = 0 := by
    change Section1.degree η -
        Section1.degree (Section1.conjugateCharacter η) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hηchar]
    simp
  have hdiffY :
      Section5.integerSpanOn Y Section5.puncturedSet
        (η - Section1.conjugateCharacter η) :=
    ⟨hdiff_span,
      (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdiff_degree⟩
  have hagree :
      τ₁ ((ηU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (ηU : Section1.ClassFunction L)) =
        T ((ηU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (ηU : Section1.ClassFunction L)) := by
    simpa [ηU] using hτ₁.2.2
      (η - Section1.conjugateCharacter η) hdiffY
  simpa [ηU, pair] using
    Section5.theorem_5_5_core_on_pair
      (S := X ∪ Y) (T := T) (R := R)
      h52a h52c h52d ηU pair τ₁ hpairη hpairDiff
      hIsoPair hVirtPair hagree

set_option maxHeartbeats 1000000 in
theorem theorem_6_8_tau2_mem_subsetSum_R_of_union_hypothesis_5_2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (_h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (_h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    (hτ₂ : coherentExtension X T τ₂)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ X) :
    Section5.isSubsetSumOf
      (R ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩) (τ₂ χ) := by
  classical
  rcases hfamily with ⟨hZH, hSZ, hXeq, hY⟩
  have hfamily' : theorem_6_8_familyData H Z S SZ X Y :=
    ⟨hZH, hSZ, hXeq, hY⟩
  have hχbarX : Section1.conjugateCharacter χ ∈ X :=
    theorem_6_8_familyData_X_conjugate_mem hSbot hfamily' hχX
  let χU : {ξ : Section1.ClassFunction L // ξ ∈ X ∪ Y} :=
    ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩
  let pair : Finset (Section1.ClassFunction L) :=
    {(χU : Section1.ClassFunction L),
      Section1.conjugateCharacter (χU : Section1.ClassFunction L)}
  have hpairSubX :
      pair ⊆ X := by
    intro ψ hψ
    simp [pair, χU] at hψ
    rcases hψ with rfl | rfl
    · exact hχX
    · exact hχbarX
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan pair τ₂ := by
    exact Section5.isCFLinearIsometryOnSpan_mono hpairSubX hτ₂.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters pair τ₂ := by
    exact Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSubX hτ₂.2.1
  have hpairχ : Section5.integerSpan pair (χU : Section1.ClassFunction L) := by
    exact Section5.integerSpan_of_mem pair (by simp [pair])
  have hpairχbar :
      Section5.integerSpan pair
        (Section1.conjugateCharacter (χU : Section1.ClassFunction L)) := by
    exact Section5.integerSpan_of_mem pair (by simp [pair])
  have hpairDiff :
      Section5.integerSpan pair
        ((χU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χU : Section1.ClassFunction L)) :=
    Section5.integerSpan_sub hpairχ hpairχbar
  have hχspan : Section5.integerSpan X χ :=
    Section5.integerSpan_of_mem X hχX
  have hχbarspan :
      Section5.integerSpan X (Section1.conjugateCharacter χ) :=
    Section5.integerSpan_of_mem X hχbarX
  have hdiff_span :
      Section5.integerSpan X (χ - Section1.conjugateCharacter χ) :=
    Section5.integerSpan_sub hχspan hχbarspan
  have hχchar : Section1.IsCharacter χ := hsetup.2 χU
  have hdiff_degree :
      Section1.degree (χ - Section1.conjugateCharacter χ) = 0 := by
    change Section1.degree χ -
        Section1.degree (Section1.conjugateCharacter χ) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
    simp
  have hdiffX :
      Section5.integerSpanOn X Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) :=
    ⟨hdiff_span,
      (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdiff_degree⟩
  have hagree :
      τ₂ ((χU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χU : Section1.ClassFunction L)) =
        T ((χU : Section1.ClassFunction L) -
          Section1.conjugateCharacter (χU : Section1.ClassFunction L)) := by
    simpa [χU] using hτ₂.2.2
      (χ - Section1.conjugateCharacter χ) hdiffX
  simpa [χU, pair] using
    Section5.theorem_5_5_core_on_pair
      (S := X ∪ Y) (T := T) (R := R)
      h52a h52c h52d χU pair τ₂ hpairχ hpairDiff
      hIsoPair hVirtPair hagree

theorem theorem_6_8_integerSpan_R_X_orthogonal_tau1Y
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hηY : η ∈ Y)
    {Xbig : Section1.ClassFunction G}
    (hXbig_span :
      Section5.integerSpan
        (R ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩) Xbig) :
    Section1.scalarProduct G Xbig (τ₁ η) = 0 := by
  classical
  rcases hfamily with ⟨hZH, hSZ, hXeq, hY⟩
  have hfamily' : theorem_6_8_familyData H Z S SZ X Y :=
    ⟨hZH, hSZ, hXeq, hY⟩
  let χU : {ξ : Section1.ClassFunction L // ξ ∈ X ∪ Y} :=
    ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩
  let ηU : {ξ : Section1.ClassFunction L // ξ ∈ X ∪ Y} :=
    ⟨η, Finset.mem_union.mpr (Or.inr hηY)⟩
  have hηnotX : η ∉ X :=
    theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily' hZcomm hηY
  have hχη_zero : Section1.scalarProduct L χ η = 0 := by
    have hχneη : χ ≠ η := by
      intro hχeq
      exact hηnotX (by simpa [← hχeq] using hχX)
    exact h52c χU.2 ηU.2 hχneη
  have hηbarY : Section1.conjugateCharacter η ∈ Y :=
    inducedKernelFamily_conjugate_mem hY hηY
  have hηbarnotX : Section1.conjugateCharacter η ∉ X :=
    theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily' hZcomm hηbarY
  have hχηbar_zero :
      Section1.scalarProduct L χ (Section1.conjugateCharacter η) = 0 := by
    have hχneηbar : χ ≠ Section1.conjugateCharacter η := by
      intro hχeq
      exact hηbarnotX (by simpa [← hχeq] using hχX)
    exact h52c χU.2
      (Finset.mem_union.mpr (Or.inr hηbarY)) hχneηbar
  have horth :
      Section5.orthogonalFinsets (R χU) (R ηU) :=
    h52e ηU χU hχη_zero hχηbar_zero
  have hXbig_orth :
      Section5.orthogonalToFinset (R ηU) Xbig := by
    simpa [χU, ηU] using
      Section5.orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57
        hXbig_span horth
  have hη_subset :
      Section5.isSubsetSumOf (R ηU) (τ₁ η) := by
    simpa [ηU] using
      theorem_6_8_tau1_mem_subsetSum_R_of_union_hypothesis_5_2
        hfamily' R hsetup h52a h52b h52c h52d h52e hτ₁ hηY
  exact theorem_6_8_scalarProduct_subsetSum_right_eq_zero_of_orthogonalToFinset
    hXbig_orth hη_subset

theorem theorem_6_8_integerSpan_of_subsetSum
    {G : Type u} [Group G]
    {R : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (hsubset : Section5.isSubsetSumOf R φ) :
    Section5.integerSpan R φ := by
  classical
  rcases hsubset with ⟨E, hE, rfl⟩
  revert hE
  induction E using Finset.induction_on with
  | empty =>
      intro _hE
      refine ⟨0, ?_⟩
      ext g
      simp [Section1.evalCoeff]
  | @insert a E ha ih =>
      intro hE
      rw [Finset.sum_insert ha]
      exact Section5.integerSpan_add
        (Section5.integerSpan_of_mem R (hE (Finset.mem_insert_self a E)))
        (ih (fun χ hχ => hE (Finset.mem_insert_of_mem hχ)))

theorem theorem_6_8_transformed_X_Y_orthogonal_of_extensions
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hηY : η ∈ Y) :
    Section1.scalarProduct G (τ₂ χ) (τ₁ η) = 0 := by
  classical
  rcases h52union with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hχ_subset :
      Section5.isSubsetSumOf
        (R ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩) (τ₂ χ) :=
    theorem_6_8_tau2_mem_subsetSum_R_of_union_hypothesis_5_2
      hSbot hfamily R hsetup h52a h52b h52c h52d h52e hτ₂ hχX
  have hχ_span :
      Section5.integerSpan
        (R ⟨χ, Finset.mem_union.mpr (Or.inl hχX)⟩) (τ₂ χ) :=
    theorem_6_8_integerSpan_of_subsetSum hχ_subset
  exact theorem_6_8_integerSpan_R_X_orthogonal_tau1Y
    hfamily hZcomm R hsetup h52a h52b h52c h52d h52e hτ₁
    hχX hηY hχ_span

theorem theorem_6_8_orthogonalToTransformedFinset_Y_of_X_extension
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ X) :
    orthogonalToTransformedFinset Y τ₁ (τ₂ χ) := by
  intro η hηY
  exact theorem_6_8_transformed_X_Y_orthogonal_of_extensions
    hSbot hfamily hZcomm h52union hτ₂ hτ₁ hχX hηY

theorem theorem_6_8_projection_scalar_eq_neg_remainder
    {G : Type u} [Finite G]
    {A Xbig Yrem ψ : Section1.ClassFunction G}
    (hA : A = Xbig - Yrem)
    (hXzero : Section1.scalarProduct G Xbig ψ = 0) :
    Section1.scalarProduct G A ψ =
      -Section1.scalarProduct G Yrem ψ := by
  rw [hA, Section5.scalarProduct_sub_left, hXzero]
  ring

theorem theorem_6_8_induced_constituent_pf54_projection_scalar_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    (hτ₁ : coherentExtension Y T τ₁)
    {ι : Type*}
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    (i : ι)
    (hdegree : Section1.degree (ψ i) = (e i : ℂ))
    (hIndX : Section1.inducedCF H (ψ i) ∈ X)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y) :
    ∃ Xbig Yrem : Section1.ClassFunction G,
      Section5.integerSpan
          (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
          Xbig ∧
        Section5.orthogonalToFinset
          (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
          Yrem ∧
        T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) = Xbig - Yrem ∧
        Section5.cfNormSq Xbig ≥ Section5.cfNormSq (Section1.inducedCF H (ψ i)) ∧
        (Section5.cfNormSq Yrem ≥ Section5.cfNormSq ((e i : ℂ) • η₁) →
          Section5.cfNormSq Xbig = Section5.cfNormSq (Section1.inducedCF H (ψ i)) ∧
            Section5.cfNormSq Yrem = Section5.cfNormSq ((e i : ℂ) • η₁) ∧
              Section5.isSubsetSumOf
                (R ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩)
                Xbig) ∧
        ∀ η : Section1.ClassFunction L, η ∈ Y →
          Section1.scalarProduct G
              (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η) =
            -Section1.scalarProduct G Yrem (τ₁ η) := by
  classical
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  rcases theorem_6_8_induced_constituent_pf54_projection_data
      hSbot hsemi hfamily hZcomm R hsetup h52a h52b h52c h52d h52e
      e ψ i hdegree hIndX hη₁Y with
    ⟨Xbig, Yrem, hXbig_span, hYrem_orth, hT, hXbig_norm, hnorm_eq⟩
  refine ⟨Xbig, Yrem, hXbig_span, hYrem_orth, hT, hXbig_norm, hnorm_eq, ?_⟩
  intro η hηY
  have hXzero :
      Section1.scalarProduct G Xbig (τ₁ η) = 0 :=
    theorem_6_8_integerSpan_R_X_orthogonal_tau1Y
      hfamily hZcomm R hsetup h52a h52b h52c h52d h52e hτ₁
      hIndX hηY hXbig_span
  exact theorem_6_8_projection_scalar_eq_neg_remainder hT hXzero


theorem theorem_6_8_integerSpan_sum_zsmul_of_nonzero
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℤ) (φ : ι → Section1.ClassFunction L)
    (hφ : ∀ i, i ∈ s → z i ≠ 0 → Section5.integerSpan S (φ i)) :
    Section5.integerSpan S (s.sum fun i => (z i : ℂ) • φ i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨0, ?_⟩
      ext g
      simp [Section1.evalCoeff]
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      have hterm : Section5.integerSpan S ((z a : ℂ) • φ a) := by
        by_cases hz : z a = 0
        · refine ⟨0, ?_⟩
          ext g
          simp [Section1.evalCoeff, hz]
        · exact Section5.integerSpan_zsmul (z a)
            (hφ a (Finset.mem_insert_self a s) hz)
      exact Section5.integerSpan_add hterm
        (ih (fun i hi hzi => hφ i (Finset.mem_insert_of_mem hi) hzi))

theorem theorem_6_8_integerSpan_weightedFamilySum_nat_of_nonzero
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (φ : ι → Section1.ClassFunction L)
    (hφ : ∀ i, e i ≠ 0 → Section5.integerSpan S (φ i)) :
    Section5.integerSpan S
      (Section1.weightedFamilySum (fun i => (e i : ℂ)) φ) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hsum :=
    theorem_6_8_integerSpan_sum_zsmul_of_nonzero
      (S := S) (s := Finset.univ) (z := fun i => (e i : ℤ)) (φ := φ)
      (fun i _hi hzi => hφ i (by
        intro hzero
        apply hzi
        simpa using congrArg (fun n : ℕ => (n : ℤ)) hzero))
  convert hsum using 1
  ext g
  simp [Section1.weightedFamilySum, Finset.sum_apply]


theorem theorem_6_8_induced_shift_eq_weighted_alpha_of_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    (hZH : Z ≤ H)
    {ι : Type*} [Finite ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z} {η₁ : Section1.ClassFunction L}
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (hsq : (letI : Fintype ι := Fintype.ofFinite ι
      (∑ i : ι, (e i : ℂ) * (e i : ℂ)) = (Z.relIndex H : ℂ))) :
    Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁ =
      Section1.weightedFamilySum (fun i => (e i : ℂ))
        (fun i => Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hdecompL :
      Section1.inducedCF Z φ =
        Section1.weightedFamilySum (fun i => (e i : ℂ))
          (fun i => Section1.inducedCF H (ψ i)) :=
    Section1.proposition_1_7_a_decomposition_from_subgroup Z H hZH e ψ φ hdecomp
  ext g
  rw [hdecompL]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Section1.weightedFamilySum]
  rw [← hsq, Finset.sum_mul]
  change (∑ x : ι, (e x : ℂ) * Section1.inducedCF H (ψ x) g) -
      (∑ x : ι, ((e x : ℂ) * (e x : ℂ)) * η₁ g) =
    ∑ x : ι, (e x : ℂ) *
      (Section1.inducedCF H (ψ x) g - (e x : ℂ) * η₁ g)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem theorem_6_8_linearMap_weightedFamilySum
    {L : Type u} {G : Type v}
    {ι : Type*} [Finite ι]
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (w : ι → ℂ) (φ : ι → Section1.ClassFunction L) :
    T (Section1.weightedFamilySum w φ) =
      Section1.weightedFamilySum w (fun i => T (φ i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hsum :
      Section1.weightedFamilySum w φ = ∑ i : ι, w i • φ i := by
    ext l
    simp [Section1.weightedFamilySum]
  rw [hsum, map_sum]
  ext g
  simp [Section1.weightedFamilySum]

theorem theorem_6_8_scalarProduct_weightedFamilySum_left
    {G ι : Type*} [Finite G] [Finite ι]
    (w : ι → ℂ) (φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.weightedFamilySum w φ) ψ =
      ∑ i : ι, w i * Section1.scalarProduct G (φ i) ψ := by
  classical
  change Section1.scalarProduct G (fun g => ∑ i : ι, w i * φ i g) ψ =
    ∑ i : ι, w i * Section1.scalarProduct G (φ i) ψ
  rw [Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change Section1.scalarProduct G (w i • φ i) ψ =
    w i * Section1.scalarProduct G (φ i) ψ
  rw [Section1.scalarProduct_smul_left]


theorem theorem_6_8_sum_sq_coeff_eq_relIndex_of_subgroup_decomposition_nonzero
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    {ι : Type*} [Finite ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z}
    (hφone : Section1.degree φ = 1)
    (hψdegree : ∀ i, e i ≠ 0 → Section1.degree (ψ i) = (e i : ℂ))
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ) :
    (letI : Fintype ι := Fintype.ofFinite ι;
      (∑ i : ι, (e i : ℂ) * (e i : ℂ)) = (Z.relIndex H : ℂ)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hpoint := congrFun hdecomp (1 : H)
  have hleft :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) (1 : H) =
        (Z.relIndex H : ℂ) := by
    have hdeg := Section1.degree_inducedClassFunction (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ)
    rw [Section1.degree_apply, Section1.degree_subgroupOfClassFunction, hφone] at hdeg
    simpa [Subgroup.relIndex] using hdeg
  have hterm : ∀ i,
      (e i : ℂ) * ψ i 1 = (e i : ℂ) * (e i : ℂ) := by
    intro i
    by_cases hei : e i = 0
    · simp [hei]
    · have hdeg := hψdegree i hei
      have happ : ψ i 1 = (e i : ℂ) := by
        simpa [Section1.degree_apply] using hdeg
      rw [happ]
  have hright :
      Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ (1 : H) =
        ∑ i : ι, (e i : ℂ) * (e i : ℂ) := by
    unfold Section1.weightedFamilySum
    exact Finset.sum_congr rfl (fun i _hi => hterm i)
  rw [hleft, hright] at hpoint
  exact hpoint.symm

theorem theorem_6_8_central_subgroup_induction_decomposition
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZcent : Z ≤ centerIn H)
    {θ : Section1.ClassFunction H} {φ : Section1.ClassFunction Z}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφone : Section1.degree φ = 1)
    (hres : Section1.subgroupRestriction (Z.subgroupOf H) θ =
      Section1.degree θ • Section1.subgroupOfClassFunction (T := H) φ) :
    ∃ ι : Type, ∃ hι : Fintype ι, ∃ hdec : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ ψ : ι → Section1.ClassFunction H, ∃ i0 : ι,
        letI : Fintype ι := hι
        letI : DecidableEq ι := hdec
        letI : Finite ι := Finite.of_fintype ι
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i)) ∧
          (∀ i j : ι,
            Section1.scalarProduct H (ψ i) (ψ j) =
              if i = j then 1 else 0) ∧
          (∀ i, e i ≠ 0 → Section1.degree (ψ i) = (e i : ℂ)) ∧
          Section1.inducedCF (Z.subgroupOf H)
              (Section1.subgroupOfClassFunction (T := H) φ) =
            Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ ∧
          ψ i0 = θ ∧
          (letI : Fintype ι := Fintype.ofFinite ι;
            (∑ i : ι, (e i : ℂ) * (e i : ℂ)) = (Z.relIndex H : ℂ)) ∧
          (e i0 : ℂ) = Section1.degree θ := by
  classical
  have hZH : Z ≤ H := by
    intro z hz
    exact (show z ∈ H ∧ z ∈ Subgroup.centralizer (H : Set L) from by
      simpa [centerIn] using hZcent hz).1
  let indZH : Section1.ClassFunction H :=
    Section1.inducedCF (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ)
  rcases Theory.Character.irreducible_characters_form_basis (G := H) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  let : Fintype ι := hι
  let : Finite ι := Finite.of_fintype ι
  let : DecidableEq ι := Classical.decEq ι
  rcases hχ with ⟨hirr, hall, hinj⟩
  let ψ : ι → Section1.ClassFunction H := fun i => Section1.ofConjClassFunction (χ i)
  have hχcomplete :
      Theory.Character.IsCompleteIrreducibleCharacterFamily χ :=
    ⟨hirr, hall, hinj⟩
  have hψclass : ∀ i, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.ofConjClassFunction_isClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr i)
  have hψchar : ∀ i, Section1.IsCharacter (ψ i) := by
    intro i
    exact theorem_6_8_isCharacter_of_irreducible (hψirr i)
  have horthψ :
      ∀ i j,
        Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    change Section1.scalarProduct H
      (Section1.ofConjClassFunction (χ i))
      (Section1.ofConjClassFunction (χ j)) = if i = j then 1 else 0
    rw [Section1.scalarProduct_ofConjClassFunction]
    exact Section1.representation_completeFamily_orthonormal
      (chi := χ) hχcomplete i j
  have hφchar : Section1.IsCharacter φ :=
    theorem_6_8_isCharacter_of_irreducible hφ
  have hφsubChar :
      Section1.IsCharacter
        (Section1.subgroupOfClassFunction (T := H) φ) :=
    Section1.isCharacter_subgroupOfClassFunction_of_le hZH φ hφchar
  have hIndChar : Section1.IsCharacter indZH := by
    exact Section1.isCharacter_inducedCF_of_isCharacter (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ) hφsubChar
  have hcoeff_nat :
      ∀ i, ∃ n : ℕ, Section1.scalarProduct H indZH (ψ i) = (n : ℂ) := by
    intro i
    exact Section1.scalarProduct_character_character_eq_nat indZH (ψ i)
      hIndChar (hψchar i)
  let e : ι → ℕ := fun i => Classical.choose (hcoeff_nat i)
  have he : ∀ i, Section1.scalarProduct H indZH (ψ i) = (e i : ℂ) := by
    intro i
    exact Classical.choose_spec (hcoeff_nat i)
  let φsum : Section1.ClassFunction H :=
    Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ
  have hφsumclass : Section1.IsClassFunction φsum := by
    intro x g
    unfold φsum Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [hψclass i x g]
  have hIndClass : Section1.IsClassFunction indZH := by
    exact Section1.inducedCF_isClassFunction (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ)
  have hdecomp : indZH = φsum := by
    apply Section1.classFunction_eq_of_inner_irreducible
      (phi := indZH) (psi := φsum) hIndClass hφsumclass
    intro ξ hξ
    rcases hall ξ hξ with ⟨i, rfl⟩
    calc
      Theory.Character.classFunctionInner
          (Section1.toConjClassFunction indZH hIndClass) (χ i) =
        Section1.scalarProduct H indZH (ψ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact Section1.classFunctionInner_toConjClassFunction
            indZH (ψ i) hIndClass (hψclass i)
      _ = (e i : ℂ) := he i
      _ = Section1.scalarProduct H φsum (ψ i) := by
          exact (Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (e i : ℂ)) (chi := ψ) horthψ i).symm
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φsum hφsumclass) (χ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact (Section1.classFunctionInner_toConjClassFunction
            φsum (ψ i) hφsumclass (hψclass i)).symm
  have hθclass : Section1.IsClassFunction θ := by
    rcases hθ with ⟨_n, ρ, _hρirr, hθeq⟩
    intro x g
    rw [hθeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hθconj : Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction θ hθclass) := by
    rcases hθ with ⟨n, ρ, hρirr, hθeq⟩
    have hchar :
        Section1.toConjClassFunction θ hθclass =
          (Theory.Character.characterClassFunction ρ) :=
      Section1.toConjClassFunction_eq_of_apply θ hθclass
        ((Theory.Character.characterClassFunction ρ)) (by
          intro g
          rw [hθeq]
          rfl)
    refine ⟨⟨n, ρ, hchar⟩, ?_⟩
    rw [hchar]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  rcases hall (Section1.toConjClassFunction θ hθclass) hθconj with
    ⟨i0, hi0χ⟩
  have hi0 : ψ i0 = θ := by
    ext h
    dsimp [ψ]
    rw [hi0χ]
    rfl
  have hψdegree :
      ∀ i, e i ≠ 0 → Section1.degree (ψ i) = (e i : ℂ) := by
    intro i hei
    exact theorem_6_8_degree_eq_coeff_of_nonzero_central_decomposition
      hZcent e ψ hφ hψirr hdecomp horthψ i hei
  have hsq :
      (letI : Fintype ι := Fintype.ofFinite ι;
        (∑ i : ι, (e i : ℂ) * (e i : ℂ)) = (Z.relIndex H : ℂ)) :=
    theorem_6_8_sum_sq_coeff_eq_relIndex_of_subgroup_decomposition_nonzero
      e ψ hφone hψdegree hdecomp
  have hsel : (e i0 : ℂ) = Section1.degree θ :=
    theorem_6_8_selected_coeff_eq_degree_of_restriction_decomposition
      hZH e ψ i0 hθ hφ hres hdecomp horthψ hi0
  exact ⟨ι, hι, Classical.decEq ι, e, ψ, i0,
    hψirr, horthψ, hψdegree, hdecomp, hi0, hsq, hsel⟩

theorem theorem_6_8_induced_span_of_subgroup_decomposition_nonzero
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hZH : Z ≤ H)
    (hSbot : inducedKernelFamily H ⊥ S)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    {φ : Section1.ClassFunction Z}
    (hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i))
    (hψne : ∀ i, e i ≠ 0 → ψ i ≠ Section1.principalCharacter H)
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ) :
    Section5.integerSpan S (Section1.inducedCF Z φ) := by
  have hdecompL :
      Section1.inducedCF Z φ =
        Section1.weightedFamilySum (fun i => (e i : ℂ))
          (fun i => Section1.inducedCF H (ψ i)) :=
    Section1.proposition_1_7_a_decomposition_from_subgroup Z H hZH e ψ φ hdecomp
  rw [hdecompL]
  exact theorem_6_8_integerSpan_weightedFamilySum_nat_of_nonzero e
    (fun i => Section1.inducedCF H (ψ i))
    (fun i hei =>
      Section5.integerSpan_of_mem S <|
        (hSbot.2 (Section1.inducedCF H (ψ i))).mpr
          ⟨ψ i, hψirr i, by
            intro a
            have ha : (a : H) = 1 := by
              have hbot : (a : H) ∈ (⊥ : Subgroup L).subgroupOf H := a.property
              simpa using hbot
            rw [ha]
            exact rfl,
            hψne i hei, rfl⟩)

theorem theorem_6_8_induced_span_of_principal_scalar_zero
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hZH : Z ≤ H)
    (hSbot : inducedKernelFamily H ⊥ S)
    {φ : Section1.ClassFunction Z}
    (hφchar : Section1.IsCharacter φ)
    (hprincipal :
      Section1.scalarProduct H
          (Section1.inducedCF (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ))
          (Section1.principalCharacter H) = 0) :
    Section5.integerSpan S (Section1.inducedCF Z φ) := by
  classical
  let indZH : Section1.ClassFunction H :=
    Section1.inducedCF (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ)
  rcases Theory.Character.irreducible_characters_form_basis (G := H) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  let : Fintype ι := hι
  let : Finite ι := Finite.of_fintype ι
  let : DecidableEq ι := Classical.decEq ι
  rcases hχ with ⟨hirr, hall, hinj⟩
  let ψ : ι → Section1.ClassFunction H := fun i => Section1.ofConjClassFunction (χ i)
  have hχcomplete :
      Theory.Character.IsCompleteIrreducibleCharacterFamily χ :=
    ⟨hirr, hall, hinj⟩
  have hψclass : ∀ i, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.ofConjClassFunction_isClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr i)
  have hψchar : ∀ i, Section1.IsCharacter (ψ i) := by
    intro i
    exact theorem_6_8_isCharacter_of_irreducible (hψirr i)
  have horthψ :
      ∀ i j,
        Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    change Section1.scalarProduct H
      (Section1.ofConjClassFunction (χ i))
      (Section1.ofConjClassFunction (χ j)) = if i = j then 1 else 0
    rw [Section1.scalarProduct_ofConjClassFunction]
    exact Section1.representation_completeFamily_orthonormal
      (chi := χ) hχcomplete i j
  have hφsubChar :
      Section1.IsCharacter
        (Section1.subgroupOfClassFunction (T := H) φ) :=
    Section1.isCharacter_subgroupOfClassFunction_of_le hZH φ hφchar
  have hIndChar : Section1.IsCharacter indZH := by
    exact Section1.isCharacter_inducedCF_of_isCharacter (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ) hφsubChar
  have hcoeff_nat :
      ∀ i, ∃ n : ℕ, Section1.scalarProduct H indZH (ψ i) = (n : ℂ) := by
    intro i
    exact Section1.scalarProduct_character_character_eq_nat indZH (ψ i)
      hIndChar (hψchar i)
  let e : ι → ℕ := fun i => Classical.choose (hcoeff_nat i)
  have he : ∀ i, Section1.scalarProduct H indZH (ψ i) = (e i : ℂ) := by
    intro i
    exact Classical.choose_spec (hcoeff_nat i)
  let φsum : Section1.ClassFunction H :=
    Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ
  have hφsumclass : Section1.IsClassFunction φsum := by
    intro x g
    unfold φsum Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [hψclass i x g]
  have hIndClass : Section1.IsClassFunction indZH := by
    exact Section1.inducedCF_isClassFunction (Z.subgroupOf H)
      (Section1.subgroupOfClassFunction (T := H) φ)
  have hdecomp : indZH = φsum := by
    apply Section1.classFunction_eq_of_inner_irreducible
      (phi := indZH) (psi := φsum) hIndClass hφsumclass
    intro ξ hξ
    rcases hall ξ hξ with ⟨i, rfl⟩
    calc
      Theory.Character.classFunctionInner
          (Section1.toConjClassFunction indZH hIndClass) (χ i) =
        Section1.scalarProduct H indZH (ψ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact Section1.classFunctionInner_toConjClassFunction
            indZH (ψ i) hIndClass (hψclass i)
      _ = (e i : ℂ) := he i
      _ = Section1.scalarProduct H φsum (ψ i) := by
          exact (Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (e i : ℂ)) (chi := ψ) horthψ i).symm
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φsum hφsumclass) (χ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact (Section1.classFunctionInner_toConjClassFunction
            φsum (ψ i) hφsumclass (hψclass i)).symm
  have hψne : ∀ i, e i ≠ 0 → ψ i ≠ Section1.principalCharacter H := by
    intro i hei hprin
    have hcoef := he i
    rw [hprin, hprincipal] at hcoef
    have hzero_complex : (e i : ℂ) = 0 := hcoef.symm
    have hzero : e i = 0 := by
      exact_mod_cast hzero_complex
    exact hei hzero
  exact theorem_6_8_induced_span_of_subgroup_decomposition_nonzero
    hZH hSbot e ψ hψirr hψne hdecomp

theorem theorem_6_8_induced_span_of_nonprincipal_subgroup_induction
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hZH : Z ≤ H)
    (hSbot : inducedKernelFamily H ⊥ S)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z) :
    Section5.integerSpan S (Section1.inducedCF Z φ) := by
  have hφchar : Section1.IsCharacter φ :=
    theorem_6_8_isCharacter_of_irreducible hφ
  have hprincipal :
      Section1.scalarProduct H
          (Section1.inducedCF (Z.subgroupOf H)
            (Section1.subgroupOfClassFunction (T := H) φ))
          (Section1.principalCharacter H) = 0 := by
    have hfrob :=
      Section1.inducedClassFunction_frobenius_general
        (Z.subgroupOf H)
        (Section1.subgroupOfClassFunction (T := H) φ)
        (Section1.principalCharacter H)
        (by intro x g; simp [Section1.principalCharacter])
    have hres :
        Section1.subgroupRestriction (Z.subgroupOf H)
            (Section1.principalCharacter H) =
          Section1.subgroupOfClassFunction (T := H)
            (Section1.principalCharacter Z) := by
      ext z
      simp [Section1.subgroupRestriction, Section1.subgroupOfClassFunction,
        Section1.principalCharacter]
    rw [hfrob, hres]
    rw [Section1.scalarProduct_subgroupOfClassFunction hZH]
    exact Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hφ hφne
  exact theorem_6_8_induced_span_of_principal_scalar_zero
    hZH hSbot hφchar hprincipal

theorem theorem_6_8_alpha_integerSpanOn_of_induced_span
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hprime : Nat.Prime (Nat.card Z))
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y)
    (hIndSpan : Section5.integerSpan S (Section1.inducedCF Z φ)) :
    Section5.integerSpanOn S Section5.puncturedSet
      (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) := by
  rcases hfamily with ⟨hZH, _hSZ, _hXeq, hY⟩
  have hfamily' : theorem_6_8_familyData H Z S SZ X Y :=
    ⟨hZH, _hSZ, _hXeq, hY⟩
  have hYsubS : Y ⊆ S :=
    theorem_6_8_familyData_Y_subset_S hSbot hfamily'
  have hηS : η₁ ∈ S := hYsubS hη₁Y
  have hηSpan : Section5.integerSpan S η₁ :=
    Section5.integerSpan_of_mem S hηS
  have hηSmul : Section5.integerSpan S ((Z.relIndex H : ℂ) • η₁) := by
    simpa using
      Section5.integerSpan_zsmul (S := S) (φ := η₁) (Z.relIndex H : ℤ) hηSpan
  have hspan :
      Section5.integerSpan S
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    Section5.integerSpan_sub hIndSpan hηSmul
  have hφone : φ 1 = 1 :=
    theorem_6_8_degree_one_of_prime_card_irreducible hprime hφ
  have hηdeg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily' hη₁Y
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 := by
    simpa using Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hrel :
      Z.relIndex (⊤ : Subgroup L) = Z.relIndex H * H.relIndex (⊤ : Subgroup L) := by
    exact (Subgroup.relIndex_mul_relIndex Z H (⊤ : Subgroup L) hZH le_top).symm
  have hIndOne :
      (Section1.inducedCF Z φ) 1 = (Z.relIndex (⊤ : Subgroup L) : ℂ) := by
    have hdeg := Section1.degree_inducedClassFunction Z φ
    rw [Section1.degree_apply] at hdeg
    rw [Section1.degree_apply, hφone] at hdeg
    simpa [hφone] using hdeg
  have hdeg0 :
      Section1.degree
          (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) = 0 := by
    rw [Section1.degree_apply]
    rw [Section1.degree_apply] at hηdeg
    simp [hIndOne, hηdeg, hrel, hHindex, Nat.cast_mul, mul_comm]
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩

theorem theorem_6_8_transform_sub_induced_eq_of_induced_span
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hprime : Nat.Prime (Nat.card Z))
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y)
    (hIndSpan : Section5.integerSpan S (Section1.inducedCF Z φ)) :
    T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
      Section1.inducedCF L
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) := by
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, hT, _hcase⟩
  exact hT _
    (theorem_6_8_alpha_integerSpanOn_of_induced_span
      hprime hSbot hsemi hfamily hφ hη₁Y hIndSpan)

theorem theorem_6_8_transform_sub_induced_eq_of_nonprincipal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hprime : Nat.Prime (Nat.card Z))
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y) :
    T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
      Section1.inducedCF L
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) := by
  rcases h68 with ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩
  rcases hfamily with ⟨hZH, hSZ, hXeq, hY⟩
  exact theorem_6_8_transform_sub_induced_eq_of_induced_span
    (h68 := ⟨_hsemi, _hodd, _hHne, _hnil, _hTI, hSbot, _hT, _hcase⟩)
    hprime ⟨hZH, hSZ, hXeq, hY⟩ hφ hη₁Y
    (theorem_6_8_induced_span_of_nonprincipal_subgroup_induction
      hZH hSbot hφ hφne)

theorem theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_nonprincipal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
          a • regularCharacter (Z.map L.subtype) +
            b • Section1.principalCharacter (Z.map L.subtype) ∧
        (star a = a →
          Section1.scalarProduct G
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) =
            a - (Z.relIndex H : ℂ) * Section1.scalarProduct L η₁
              (Section1.subgroupRestriction L (τ₁ η))) := by
  exact theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_familyData
    h68 hpQ hcase hB hfamily hτ₁ hφ hφne hηY
    (theorem_6_8_transform_sub_induced_eq_of_nonprincipal
      h68 (theorem_6_8_caseB_Z_prime_card hcase hB)
      hfamily hφ hφne hη₁Y)

theorem theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_nonprincipal_real_coeff
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η) =
          a • regularCharacter (Z.map L.subtype) +
            b • Section1.principalCharacter (Z.map L.subtype) ∧
        Section1.scalarProduct G
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) =
          a - (Z.relIndex H : ℂ) * Section1.scalarProduct L η₁
            (Section1.subgroupRestriction L (τ₁ η)) := by
  rcases theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_nonprincipal
      h68 hpQ hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY with
    ⟨a, b, hres, hscalar⟩
  have hvirt : Theory.Character.IsVirtualCharacter (τ₁ η) :=
    hτ₁.2.1 η (Section5.integerSpan_of_mem Y hηY)
  have ha : star a = a :=
    theorem_6_8_regular_add_coefficient_star_eq_self_of_virtual
      (theorem_6_8_caseB_Z_prime_card hcase hB) hφ hφne hvirt hres
  exact ⟨a, b, hres, hscalar ha⟩

theorem theorem_6_8_scalarProduct_transform_sub_tau1_relIndex_multiple_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    ∃ k : ℤ,
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) =
        (Z.relIndex H : ℂ) *
          ((k : ℂ) - Section1.scalarProduct L η₁
            (Section1.subgroupRestriction L (τ₁ η))) := by
  rcases theorem_6_8_exists_scalarProduct_transform_sub_tau1_eq_of_nonprincipal_real_coeff
      h68 hpQ hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY with
    ⟨a, b, hres, hscalar⟩
  rcases theorem_6_8_regular_add_coefficient_multiple_of_caseB_familyData
      h68 hpQ hcase hB hfamily hτ₁ hηY hres with
    ⟨k, ha⟩
  refine ⟨k, ?_⟩
  rw [hscalar, ha]
  ring

theorem theorem_6_8_scalarProduct_transform_sub_tau1_int_relIndex_multiple_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    ∃ k : ℤ,
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) =
        (Z.relIndex H : ℂ) * (k : ℂ) := by
  rcases theorem_6_8_scalarProduct_transform_sub_tau1_relIndex_multiple_of_caseB_familyData
      h68 hpQ hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY with
    ⟨k, hk⟩
  have hη₁virt : Theory.Character.IsVirtualCharacter η₁ :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y)
  have hτηvirt : Theory.Character.IsVirtualCharacter (τ₁ η) :=
    hτ₁.2.1 η (Section5.integerSpan_of_mem Y hηY)
  have hresvirt :
      Theory.Character.IsVirtualCharacter
        (Section1.subgroupRestriction L (τ₁ η)) :=
    theorem_6_8_subgroupRestriction_isVirtualCharacter L hτηvirt
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int
      hη₁virt hresvirt with
    ⟨m, hm⟩
  refine ⟨k - m, ?_⟩
  rw [hk, hm]
  norm_num

theorem theorem_6_8_scalarProduct_transform_sub_tau1_independent_of_nonprincipal_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ φ' : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    (hφ' : Section1.IsIrreducibleCharacterOnGroup φ')
    (hφ'ne : φ' ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) =
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ' - (Z.relIndex H : ℂ) • η₁)) (τ₁ η) := by
  rcases theorem_6_8_2_2_restriction_regular_add_of_familyData
      h68 hpQ hcase hB hfamily hτ₁ hηY with
    ⟨a, b, hres⟩
  have hvirt : Theory.Character.IsVirtualCharacter (τ₁ η) :=
    hτ₁.2.1 η (Section5.integerSpan_of_mem Y hηY)
  have ha : star a = a :=
    theorem_6_8_regular_add_coefficient_star_eq_self_of_virtual
      (theorem_6_8_caseB_Z_prime_card hcase hB) hφ hφne hvirt hres
  have hprime : Nat.Prime (Nat.card Z) :=
    theorem_6_8_caseB_Z_prime_card hcase hB
  have hTφ :
      T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
        Section1.inducedCF L
          (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    theorem_6_8_transform_sub_induced_eq_of_nonprincipal
      h68 hprime hfamily hφ hφne hη₁Y
  have hTφ' :
      T (Section1.inducedCF Z φ' - (Z.relIndex H : ℂ) • η₁) =
        Section1.inducedCF L
          (Section1.inducedCF Z φ' - (Z.relIndex H : ℂ) • η₁) :=
    theorem_6_8_transform_sub_induced_eq_of_nonprincipal
      h68 hprime hfamily hφ' hφ'ne hη₁Y
  have hleft :=
    theorem_6_8_scalarProduct_transform_sub_tau1_regular_add_of_prime_card
      hτ₁ hηY hprime hφ hφne ha hTφ hres
  have hright :=
    theorem_6_8_scalarProduct_transform_sub_tau1_regular_add_of_prime_card
      hτ₁ hηY hprime hφ' hφ'ne ha hTφ' hres
  rw [hleft, hright]

theorem theorem_6_8_scalarProduct_inducedCF_nonprincipal_Y_eq_zero_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η : Section1.ClassFunction L}
    (hηY : η ∈ Y) :
    Section1.scalarProduct L (Section1.inducedCF Z φ) η = 0 := by
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY
  have hηclass : Section1.IsClassFunction η :=
    theorem_6_8_isClassFunction_of_isVirtualCharacter
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hηirr)
  rw [Section1.inducedClassFunction_frobenius_general Z φ η hηclass]
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top h68.1
  have : H.Normal := hHnorm
  have hker : Section1.subgroupInKernel' η Z :=
    theorem_6_8_caseB_mem_Y_subgroupInKernel_Z hB hfamily hηY
  have hres :
      Section1.subgroupRestriction Z η =
        (η 1) • Section1.principalCharacter Z := by
    ext z
    simp [Section1.subgroupRestriction, Section1.principalCharacter,
      Section1.degree_apply, hker z]
  rw [hres, Section1.scalarProduct_smul_right]
  rw [Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hφ hφne]
  simp

theorem theorem_6_8_scalarProduct_source_alpha_Y_diff_eq_relIndex_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) (hηne : η ≠ η₁) :
    Section1.scalarProduct L
      (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) (η - η₁) =
        (Z.relIndex H : ℂ) := by
  have hIndη :
      Section1.scalarProduct L (Section1.inducedCF Z φ) η = 0 :=
    theorem_6_8_scalarProduct_inducedCF_nonprincipal_Y_eq_zero_of_caseB_familyData
      h68 hB hfamily hφ hφne hηY
  have hIndη₁ :
      Section1.scalarProduct L (Section1.inducedCF Z φ) η₁ = 0 :=
    theorem_6_8_scalarProduct_inducedCF_nonprincipal_Y_eq_zero_of_caseB_familyData
      h68 hB hfamily hφ hφne hη₁Y
  have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY
  have hη₁η : Section1.scalarProduct L η₁ η = 0 :=
    by
      rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
      rcases hηirr with ⟨n, ρ, hρ, hηeq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        η₁ η ρ₁ ρ hη₁eq hηeq hρ₁ hρ hηne.symm
  have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 :=
    by
      rcases hη₁irr with ⟨_n, ρ, hρirr, hη₁eq⟩
      rw [hη₁eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
    Section5.scalarProduct_sub_right]
  simp [Section1.scalarProduct_smul_left, hIndη, hIndη₁, hη₁η, hη₁self]

theorem theorem_6_8_scalarProduct_transform_sub_tau1_Y_diff_eq_relIndex_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) (hηne : η ≠ η₁) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
      (τ₁ η - τ₁ η₁) =
        (Z.relIndex H : ℂ) := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases theorem_6_8_hypothesis_5_2_of_caseC2 h68' hcase with
    ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  have hprime : Nat.Prime (Nat.card Z) :=
    theorem_6_8_caseB_Z_prime_card hcase hB
  have hIndSpan : Section5.integerSpan S (Section1.inducedCF Z φ) :=
    theorem_6_8_induced_span_of_nonprincipal_subgroup_induction
      hfamily.1 hSbot hφ hφne
  have hαspan :
      Section5.integerSpanOn S Section5.puncturedSet
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    theorem_6_8_alpha_integerSpanOn_of_induced_span
      hprime hSbot hsemi hfamily hφ hη₁Y hIndSpan
  have hdiffY :
      Section5.integerSpanOn Y Section5.puncturedSet (η - η₁) :=
    by
      have hηspan : Section5.integerSpan Y η :=
        Section5.integerSpan_of_mem Y hηY
      have hη₁span : Section5.integerSpan Y η₁ :=
        Section5.integerSpan_of_mem Y hη₁Y
      have hspan : Section5.integerSpan Y (η - η₁) :=
        Section5.integerSpan_sub hηspan hη₁span
      have hηdeg : Section1.degree η = (Nat.card W1 : ℂ) :=
        theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hηY
      have hη₁deg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
        theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hη₁Y
      have hdeg0 : Section1.degree (η - η₁) = 0 := by
        rw [Section1.degree_apply] at hηdeg hη₁deg ⊢
        simp [hηdeg, hη₁deg]
      exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩
  have hYsubS : Y ⊆ S :=
    theorem_6_8_familyData_Y_subset_S hSbot hfamily
  have hdiffS :
      Section5.integerSpanOn S Section5.puncturedSet (η - η₁) :=
    Section5.integerSpanOn_mono hYsubS hdiffY
  have hiso :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (T (η - η₁)) =
      Section1.scalarProduct L
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) (η - η₁) :=
    h52b.1 _ _ hαspan hdiffS
  have htarget :
      τ₁ η - τ₁ η₁ = T (η - η₁) := by
    calc
      τ₁ η - τ₁ η₁ = τ₁ (η - η₁) := by rw [map_sub]
      _ = T (η - η₁) :=
        hτ₁.2.2 (η - η₁) hdiffY
  rw [htarget]
  calc
    Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (T (η - η₁)) =
      Section1.scalarProduct L
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) (η - η₁) := hiso
    _ = (Z.relIndex H : ℂ) :=
      theorem_6_8_scalarProduct_source_alpha_Y_diff_eq_relIndex_of_caseB_familyData
        h68' hB hfamily hφ hφne hη₁Y hηY hηne

theorem theorem_6_8_cfNormSq_transform_sub_eq_source_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) :
    Section5.cfNormSq
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) =
      Section5.cfNormSq
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases theorem_6_8_hypothesis_5_2_of_caseC2 h68' hcase with
    ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  have hprime : Nat.Prime (Nat.card Z) :=
    theorem_6_8_caseB_Z_prime_card hcase hB
  have hIndSpan : Section5.integerSpan S (Section1.inducedCF Z φ) :=
    theorem_6_8_induced_span_of_nonprincipal_subgroup_induction
      hfamily.1 hSbot hφ hφne
  have hαspan :
      Section5.integerSpanOn S Section5.puncturedSet
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    theorem_6_8_alpha_integerSpanOn_of_induced_span
      hprime hSbot hsemi hfamily hφ hη₁Y hIndSpan
  have hiso :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) =
      Section1.scalarProduct L
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    h52b.1 _ _ hαspan hαspan
  unfold Section5.cfNormSq
  rw [hiso]

theorem theorem_6_8_cfNormSq_source_alpha_eq_induced_add_relIndex_sq_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) :
    Section5.cfNormSq
        (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
      Section5.cfNormSq (Section1.inducedCF Z φ) +
        (Z.relIndex H : ℝ) ^ (2 : ℕ) := by
  have hIndη :
      Section1.scalarProduct L (Section1.inducedCF Z φ)
          ((Z.relIndex H : ℂ) • η₁) = 0 := by
    rw [Section1.scalarProduct_smul_right]
    rw [theorem_6_8_scalarProduct_inducedCF_nonprincipal_Y_eq_zero_of_caseB_familyData
      h68 hB hfamily hφ hφne hη₁Y]
    simp
  have hηInd :
      Section1.scalarProduct L ((Z.relIndex H : ℂ) • η₁)
          (Section1.inducedCF Z φ) = 0 := by
    have hbase :
        Section1.scalarProduct L η₁ (Section1.inducedCF Z φ) = 0 := by
      have hright :
          Section1.scalarProduct L (Section1.inducedCF Z φ) η₁ = 0 :=
        theorem_6_8_scalarProduct_inducedCF_nonprincipal_Y_eq_zero_of_caseB_familyData
          h68 hB hfamily hφ hφne hη₁Y
      simpa [Section1.scalarProduct_star_swap] using congrArg star hright
    rw [Section1.scalarProduct_smul_left, hbase]
    simp
  rw [Section5.cfNormSq_sub_eq_add_of_orthogonal hIndη hηInd]
  have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 := by
    rcases theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y with
      ⟨_n, ρ, hρirr, hη₁eq⟩
    rw [hη₁eq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hη₁norm : Section5.cfNormSq η₁ = 1 := by
    unfold Section5.cfNormSq
    rw [hη₁self]
    simp
  have hrelNorm :
      Complex.normSq (Z.relIndex H : ℂ) =
        (Z.relIndex H : ℝ) ^ (2 : ℕ) := by
    norm_num [Complex.normSq]
    ring
  rw [Section5.cfNormSq_smul, hη₁norm, hrelNorm]
  ring

theorem theorem_6_8_caseB_conj_mem_Z_eq_self
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (g : L) (z : Z) :
    g * (z : L) * g⁻¹ = (z : L) := by
  rcases h68 with ⟨hsemi, _hodd, _hHne, _hnil, _hTI, _hSbot, _hT, _hbranch⟩
  rcases hB with ⟨_hW2ne, hW2center, _hW2comm, hZeq⟩
  subst Z
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      _hcentW1, _hW1W, _hW2W, hdirect, _hWodd⟩
  rcases hsemi.mul_surjective g trivial with ⟨h, hhH, w, hwW1, hg⟩
  have hzw : w * (z : L) * w⁻¹ = (z : L) := by
    have hcomm : w * (z : L) = (z : L) * w :=
      hdirect.commute w hwW1 (z : L) z.property
    calc
      w * (z : L) * w⁻¹ = (z : L) * w * w⁻¹ := by rw [hcomm]
      _ = (z : L) := by simp [mul_assoc]
  have hhz : h * (z : L) * h⁻¹ = (z : L) := by
    have hzcent : (z : L) ∈ centerIn H := hW2center z.property
    have hzcentralizer : (z : L) ∈ Subgroup.centralizer (H : Set L) := hzcent.2
    rw [Subgroup.mem_centralizer_iff] at hzcentralizer
    have hcomm : h * (z : L) = (z : L) * h := hzcentralizer h hhH
    calc
      h * (z : L) * h⁻¹ = (z : L) * h * h⁻¹ := by rw [hcomm]
      _ = (z : L) := by simp [mul_assoc]
  rw [hg]
  calc
    h * w * (z : L) * (h * w)⁻¹ = h * (w * (z : L) * w⁻¹) * h⁻¹ := by group
    _ = h * (z : L) * h⁻¹ := by rw [hzw]
    _ = (z : L) := hhz

theorem theorem_6_8_cfNormSq_inducedCF_eq_relIndex_top_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ) :
    Section5.cfNormSq (Section1.inducedCF Z φ) =
      (Z.relIndex (⊤ : Subgroup L) : ℝ) := by
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68 hcase hB with
    ⟨_hZne, _hZcenter, hZnorm⟩
  have : Z.Normal := hZnorm
  have hInertia : Section1.inertiaSubgroup Z φ = (⊤ : Subgroup L) := by
    apply le_antisymm le_top
    intro g _hg
    change Section1.conjugateOnNormal Z φ g = φ
    ext z
    exact congrArg φ
      (Subtype.ext (theorem_6_8_caseB_conj_mem_Z_eq_self h68 hcase hB g z))
  rcases hφ with ⟨n, ρ, hρirr, hφeq⟩
  rw [hφeq] at hInertia
  unfold Section5.cfNormSq
  rw [hφeq]
  rw [Section1.proposition_1_5_b_rep_orbit_relIndex_canonical Z ρ hρirr]
  rw [hInertia]
  simp

theorem theorem_6_8_caseB_cardW1_lt_ZrelIndex
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    Nat.card W1 < Z.relIndex H := by
  classical
  rcases theorem_6_8_frobeniusQuotient_Z_of_caseB h68 hcase hB with
    ⟨hZnorm, hZH, _hHnorm, R, hcomp, hHbar_ne, _hRne, hcent⟩
  have : Z.Normal := hZnorm
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let Hbar : Subgroup (L ⧸ Z) := H.map q
  have hdivR : Nat.card R ∣ Nat.card Hbar - 1 := by
    dsimp [Hbar, q]
    exact frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := H.map (QuotientGroup.mk' Z)) (R := R)
      (N := H.map (QuotientGroup.mk' Z)) le_rfl hcent
  have hRcard : Nat.card R = H.relIndex (⊤ : Subgroup L) :=
    theorem_6_5_a_complement_card_eq_relIndex_top hZnorm hZH hcomp
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right h68.1
  have hHbarcard : Nat.card Hbar = Z.relIndex H := by
    dsimp [Hbar, q]
    exact theorem_6_5_a_map_card_eq_relIndex (N := H) hZnorm
  have hdiv : Nat.card W1 ∣ Z.relIndex H - 1 := by
    rw [hRcard, hHindex, hHbarcard] at hdivR
    exact hdivR
  have hrel_ne_one : Z.relIndex H ≠ 1 := by
    intro hrel
    apply hHbar_ne
    have hcard : Nat.card Hbar = 1 := by
      rw [hHbarcard, hrel]
    exact Subgroup.card_eq_one.mp hcard
  have hrelpos : 0 < Z.relIndex H := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos
  have hrelgt : 1 < Z.relIndex H := by omega
  have hle : Nat.card W1 ≤ Z.relIndex H - 1 :=
    Nat.le_of_dvd (by omega) hdiv
  omega

theorem theorem_6_8_caseB_relIndex_top_lt_relIndex_sq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    (Z.relIndex (⊤ : Subgroup L) : ℝ) <
      (Z.relIndex H : ℝ) ^ (2 : ℕ) := by
  have hrel :
      Z.relIndex (⊤ : Subgroup L) =
        Z.relIndex H * H.relIndex (⊤ : Subgroup L) := by
    exact (Subgroup.relIndex_mul_relIndex Z H (⊤ : Subgroup L)
      hfamily.1 le_top).symm
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right h68.1
  have hW1lt : Nat.card W1 < Z.relIndex H :=
    theorem_6_8_caseB_cardW1_lt_ZrelIndex h68 hcase hB
  have hrelpos : 0 < Z.relIndex H := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos
  have hnat :
      Z.relIndex (⊤ : Subgroup L) < (Z.relIndex H) ^ (2 : ℕ) := by
    rw [hrel, hHindex, pow_two]
    exact Nat.mul_lt_mul_of_pos_left hW1lt hrelpos
  exact_mod_cast hnat

theorem theorem_6_8_norm_bound_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) :
    ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          Section5.cfNormSq
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) <
              2 * (Z.relIndex H : ℝ) ^ (2 : ℕ) := by
  intro φ hφ hφne
  have htransport :
      Section5.cfNormSq
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) =
        Section5.cfNormSq
          (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) :=
    theorem_6_8_cfNormSq_transform_sub_eq_source_caseB_familyData
      h68 hcase hB hfamily hφ hφne hη₁Y
  have hsource :
      Section5.cfNormSq
          (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
        Section5.cfNormSq (Section1.inducedCF Z φ) +
          (Z.relIndex H : ℝ) ^ (2 : ℕ) :=
    theorem_6_8_cfNormSq_source_alpha_eq_induced_add_relIndex_sq_caseB_familyData
      h68 hB hfamily hφ hφne hη₁Y
  have hind :
      Section5.cfNormSq (Section1.inducedCF Z φ) =
        (Z.relIndex (⊤ : Subgroup L) : ℝ) :=
    theorem_6_8_cfNormSq_inducedCF_eq_relIndex_top_caseB_familyData
      h68 hcase hB hφ
  have htoplt :
      (Z.relIndex (⊤ : Subgroup L) : ℝ) <
        (Z.relIndex H : ℝ) ^ (2 : ℕ) :=
    theorem_6_8_caseB_relIndex_top_lt_relIndex_sq h68 hcase hB hfamily
  calc
    Section5.cfNormSq
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        = Section5.cfNormSq
          (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) := htransport
    _ = Section5.cfNormSq (Section1.inducedCF Z φ) +
          (Z.relIndex H : ℝ) ^ (2 : ℕ) := hsource
    _ = (Z.relIndex (⊤ : Subgroup L) : ℝ) +
          (Z.relIndex H : ℝ) ^ (2 : ℕ) := by rw [hind]
    _ < 2 * (Z.relIndex H : ℝ) ^ (2 : ℕ) := by nlinarith

theorem theorem_6_8_left_candidate_scalarProduct_Y_diff_eq_zero_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) (hηne : η ≠ η₁) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • τ₁ η₁)
      (τ₁ η - τ₁ η₁) = 0 := by
  have hdiff :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (τ₁ η - τ₁ η₁) =
          (Z.relIndex H : ℂ) :=
    theorem_6_8_scalarProduct_transform_sub_tau1_Y_diff_eq_relIndex_of_caseB_familyData
      h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY hηne
  have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY
  have hη₁η : Section1.scalarProduct L η₁ η = 0 :=
    by
      rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
      rcases hηirr with ⟨n, ρ, hρ, hηeq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        η₁ η ρ₁ ρ hη₁eq hηeq hρ₁ hρ hηne.symm
  have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 :=
    by
      rcases hη₁irr with ⟨_n, ρ, hρirr, hη₁eq⟩
      rw [hη₁eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hτ₁η₁η : Section1.scalarProduct G (τ₁ η₁) (τ₁ η) = 0 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ hη₁Y hηY,
      hη₁η]
  have hτ₁η₁self : Section1.scalarProduct G (τ₁ η₁) (τ₁ η₁) = 1 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ hη₁Y hη₁Y,
      hη₁self]
  have hτ₁diff :
      Section1.scalarProduct G (τ₁ η₁) (τ₁ η - τ₁ η₁) = -1 := by
    rw [Section5.scalarProduct_sub_right, hτ₁η₁η, hτ₁η₁self]
    norm_num
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
    hdiff, hτ₁diff]
  ring

theorem theorem_6_8_left_candidate_scalarProduct_Y_eq_anchor_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • τ₁ η₁)
      (τ₁ η) =
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • τ₁ η₁)
      (τ₁ η₁) := by
  by_cases hηne : η ≠ η₁
  · have hdiff0 :
        Section1.scalarProduct G
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
            (Z.relIndex H : ℂ) • τ₁ η₁)
          (τ₁ η - τ₁ η₁) = 0 :=
      theorem_6_8_left_candidate_scalarProduct_Y_diff_eq_zero_of_caseB_familyData
        h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY hηne
    rw [Section5.scalarProduct_sub_right] at hdiff0
    exact sub_eq_zero.mp hdiff0
  · have hηeq : η = η₁ := not_not.mp hηne
    simp [hηeq]

theorem theorem_6_8_left_candidate_orthogonal_of_anchor_zero_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
          (Z.relIndex H : ℂ) • τ₁ η₁)
        (τ₁ η₁) = 0) :
    orthogonalToTransformedFinset Y τ₁
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • τ₁ η₁) := by
  intro η hηY
  rw [theorem_6_8_left_candidate_scalarProduct_Y_eq_anchor_of_caseB_familyData
    h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY, hanchor]

theorem theorem_6_8_right_candidate_scalarProduct_Y_eq_anchor_of_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η₂ η : Section1.ClassFunction L}
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    (hηY : η ∈ Y) :
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • (-τ₁ η₂))
      (τ₁ η) =
    Section1.scalarProduct G
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • (-τ₁ η₂))
      (τ₁ η₁) := by
  have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
  have hη₂irr : Section1.IsIrreducibleCharacterOnGroup η₂ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₂ hη₂Y
  have hη₂η₁ : Section1.scalarProduct L η₂ η₁ = 0 :=
    by
      rcases hη₂irr with ⟨n₂, ρ₂, hρ₂, hη₂eq⟩
      rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        η₂ η₁ ρ₂ ρ₁ hη₂eq hη₁eq hρ₂ hρ₁ hη₂ne
  have hη₂self : Section1.scalarProduct L η₂ η₂ = 1 :=
    by
      rcases hη₂irr with ⟨_n, ρ, hρirr, hη₂eq⟩
      rw [hη₂eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hτ₂η₁ : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₁) = 0 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ hη₂Y hη₁Y,
      hη₂η₁]
  have hτ₂self : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) = 1 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ hη₂Y hη₂Y,
      hη₂self]
  have hnegη₁ : Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₁) = 0 := by
    rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
      hτ₂η₁]
    simp
  have hnegη₂ : Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₂) = -1 := by
    rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
      hτ₂self]
    norm_num
  have hcases : η = η₁ ∨ η = η₂ := by
    classical
    let pair : Finset (Section1.ClassFunction L) := {η₁, η₂}
    have hpair_subset : pair ⊆ Y := by
      intro χ hχ
      simp [pair] at hχ
      rcases hχ with rfl | rfl
      · exact hη₁Y
      · exact hη₂Y
    have hpair_card : pair.card = 2 := by
      have hη₁ne : η₁ ≠ η₂ := hη₂ne.symm
      simp [pair, hη₁ne]
    have hpair_eq : pair = Y := by
      apply Finset.eq_of_subset_of_card_le hpair_subset
      simp [hpair_card, hcard]
    have hηpair : η ∈ pair := by
      simpa [hpair_eq] using hηY
    simpa [pair] using hηpair
  rcases hcases with hηeq | hηeq
  · subst η
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hnegη₁]
  · subst η
    have hdiff :
        Section1.scalarProduct G
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
          (τ₁ η₂ - τ₁ η₁) =
            (Z.relIndex H : ℂ) :=
      theorem_6_8_scalarProduct_transform_sub_tau1_Y_diff_eq_relIndex_of_caseB_familyData
        h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y hη₂Y hη₂ne
    have hAdiff :
        Section1.scalarProduct G
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
          (τ₁ η₂) -
        Section1.scalarProduct G
          (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
          (τ₁ η₁) =
            (Z.relIndex H : ℂ) := by
      simpa [Section5.scalarProduct_sub_right] using hdiff
    set A2 : ℂ :=
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (τ₁ η₂)
    set A1 : ℂ :=
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (τ₁ η₁)
    have hAdiff' : A2 - A1 = (Z.relIndex H : ℂ) := by
      simpa [A2, A1] using hAdiff
    have hAeq : A2 - (Z.relIndex H : ℂ) = A1 := by
      rw [← hAdiff']
      ring
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left,
      hnegη₂, hnegη₁]
    change A2 + (Z.relIndex H : ℂ) * (-1) =
      A1 + (Z.relIndex H : ℂ) * 0
    calc
      A2 + (Z.relIndex H : ℂ) * (-1) =
          A2 - (Z.relIndex H : ℂ) := by ring
      _ = A1 := hAeq
      _ = A1 + (Z.relIndex H : ℂ) * 0 := by ring

theorem theorem_6_8_right_candidate_orthogonal_of_anchor_zero_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η₁ η₂ : Section1.ClassFunction L}
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    (hanchor :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
          (Z.relIndex H : ℂ) • (-τ₁ η₂))
        (τ₁ η₁) = 0) :
    orthogonalToTransformedFinset Y τ₁
      (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
        (Z.relIndex H : ℂ) • (-τ₁ η₂)) := by
  intro η hηY
  rw [theorem_6_8_right_candidate_scalarProduct_Y_eq_anchor_of_caseB_familyData
    h68 hcase hB hfamily hτ₁ hφ hφne hcard hη₁Y hη₂Y hη₂ne hηY, hanchor]

theorem theorem_6_8_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0) :
    Section5.cfNormSq (Section1.weightedFamilySum w χ) =
      ∑ i : ι, Complex.normSq (w i) := by
  classical
  have hself :
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
        ∑ i : ι, star (w i) * w i := by
    calc
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ)
          = ∑ i : ι, star (w i) *
              Section1.scalarProduct G (Section1.weightedFamilySum w χ) (χ i) := by
            rw [Section1.scalarProduct_weightedFamilySum_right]
      _ = ∑ i : ι, star (w i) * w i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i]
  unfold Section5.cfNormSq
  rw [hself, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hnorm : star (w i) * w i = ((Complex.normSq (w i) : ℝ) : ℂ) := by
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hnorm]
  simp

theorem theorem_6_8_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (Y : Section1.ClassFunction G) :
    ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) ≤
      Section5.cfNormSq Y := by
  classical
  let w : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
  let P : Section1.ClassFunction G := Section1.weightedFamilySum w χ
  let R : Section1.ClassFunction G := Y - P
  have hPχ : ∀ i : ι, Section1.scalarProduct G P (χ i) = w i := by
    intro i
    dsimp [P]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i
  have hRχ : ∀ i : ι, Section1.scalarProduct G R (χ i) = 0 := by
    intro i
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hPχ i]
    dsimp [w]
    simp
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hRχ i]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      Section5.cfNormSq Y = Section5.cfNormSq R + Section5.cfNormSq P := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRP hPR
  have hPnorm_le : Section5.cfNormSq P ≤ Section5.cfNormSq Y := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hPnorm :
      Section5.cfNormSq P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact theorem_6_8_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq w χ horth
  simpa [w, hPnorm] using hPnorm_le

theorem theorem_6_8_tau1_Y_orthonormal_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁) :
    ∀ η ξ : Y,
      Section1.scalarProduct G (τ₁ (η : Section1.ClassFunction L))
        (τ₁ (ξ : Section1.ClassFunction L)) =
          if η = ξ then 1 else 0 := by
  intro η ξ
  rw [theorem_6_8_coherentExtension_scalarProduct_of_mem hτ₁ η.2 ξ.2]
  by_cases hηξ : η = ξ
  · subst ξ
    rw [if_pos rfl]
    rcases theorem_6_8_Y_irreducible_of_familyData
        h68 hfamily (η : Section1.ClassFunction L) η.2 with
      ⟨_n, ρ, hρirr, hξeq⟩
    rw [hξeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  · rw [if_neg hηξ]
    have hval_ne :
        (η : Section1.ClassFunction L) ≠ (ξ : Section1.ClassFunction L) := by
      intro hval
      exact hηξ (Subtype.ext hval)
    rcases theorem_6_8_Y_irreducible_of_familyData
        h68 hfamily (η : Section1.ClassFunction L) η.2 with
      ⟨nη, ρη, hρη, hηeq⟩
    rcases theorem_6_8_Y_irreducible_of_familyData
        h68 hfamily (ξ : Section1.ClassFunction L) ξ.2 with
      ⟨nξ, ρξ, hρξ, hξeq⟩
    exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      (η : Section1.ClassFunction L) (ξ : Section1.ClassFunction L)
      ρη ρξ hηeq hξeq hρη hρξ hval_ne

theorem theorem_6_8_tau1_Y_coeff_normSq_sum_le_cfNormSq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (A : Section1.ClassFunction G) :
    ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
      Complex.normSq
        (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) ≤
      Section5.cfNormSq A := by
  classical
  exact theorem_6_8_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
    (G := G) (ι := Y)
    (fun η : Y => τ₁ (η : Section1.ClassFunction L))
    (theorem_6_8_tau1_Y_orthonormal_of_familyData h68 hfamily hτ₁)
    A

theorem theorem_6_8_coeff_eq_nat_mul_x_of_anchor_and_diff
    {G : Type u} [Finite G]
    {A ψη η₁ : Section1.ClassFunction G}
    {c : ℕ} {x : ℤ}
    (hanchor :
      Section1.scalarProduct G A η₁ = (c : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : Section1.scalarProduct G A (ψη - η₁) = (c : ℂ)) :
    Section1.scalarProduct G A ψη = (c : ℂ) * ((x : ℤ) : ℂ) := by
  have hsub :
      Section1.scalarProduct G A ψη - Section1.scalarProduct G A η₁ =
        (c : ℂ) := by
    simpa [Section5.scalarProduct_sub_right] using hdiff
  calc
    Section1.scalarProduct G A ψη =
        (Section1.scalarProduct G A ψη - Section1.scalarProduct G A η₁) +
          Section1.scalarProduct G A η₁ := by ring
    _ = (c : ℂ) + (c : ℂ) * ((x - 1 : ℤ) : ℂ) := by
          rw [hsub, hanchor]
    _ = (c : ℂ) * ((x : ℤ) : ℂ) := by
          have hxcast : ((x - 1 : ℤ) : ℂ) = ((x : ℤ) : ℂ) - 1 := by
            norm_num
          rw [hxcast]
          ring

theorem theorem_6_8_tau1_Y_coeff_normSq_sum_eq_anchor_quadratic_nat
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L]
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {c : ℕ} {x : ℤ}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (c : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (c : ℂ)) :
    (c : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) =
      ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) := by
  classical
  let η₁s : Y := ⟨η₁, hη₁Y⟩
  let f : Y → ℝ := fun η =>
    Complex.normSq
      (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L)))
  let s : Finset Y := @Finset.univ Y (Fintype.ofFinite Y)
  have hη₁s_mem : η₁s ∈ s := by simp [s]
  have hanchor_norm :
      f η₁s = (c : ℝ) ^ (2 : ℕ) *
          ((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) := by
    dsimp [f, η₁s]
    rw [hanchor, Complex.normSq_mul]
    norm_num [Complex.normSq]
    ring
  have hnonanchor : ∀ η ∈ s.erase η₁s,
      f η = (c : ℝ) ^ (2 : ℕ) * ((x : ℤ) : ℝ) ^ (2 : ℕ) := by
    intro η hη
    have hηne : η ≠ η₁s := (Finset.mem_erase.mp hη).1
    have hηval_ne : (η : Section1.ClassFunction L) ≠ η₁ := by
      intro h
      exact hηne (Subtype.ext h)
    have hcoeff :
        Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L)) =
          (c : ℂ) * ((x : ℤ) : ℂ) :=
      theorem_6_8_coeff_eq_nat_mul_x_of_anchor_and_diff
        (A := A) (ψη := τ₁ (η : Section1.ClassFunction L)) (η₁ := τ₁ η₁)
        (c := c) (x := x) hanchor
        (hdiff (η : Section1.ClassFunction L) η.2 hηval_ne)
    dsimp [f]
    rw [hcoeff, Complex.normSq_mul]
    norm_num [Complex.normSq]
    ring
  have hcard : (s.erase η₁s).card = Y.card - 1 := by
    have hscard : s.card = Y.card := by
      dsimp [s]
      rw [(@Nat.card_eq_fintype_card Y (Fintype.ofFinite Y)).symm]
      exact Nat.card_eq_finsetCard Y
    rw [Finset.card_erase_of_mem hη₁s_mem, hscard]
  have hsum_erase :
      (s.erase η₁s).sum f =
        ((Y.card - 1 : ℕ) : ℝ) *
          ((c : ℝ) ^ (2 : ℕ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) := by
    rw [Finset.sum_eq_card_nsmul (s := s.erase η₁s)
      (f := f)
      (b := (c : ℝ) ^ (2 : ℕ) * ((x : ℤ) : ℝ) ^ (2 : ℕ))]
    · rw [hcard]
      simp [nsmul_eq_mul]
    · exact hnonanchor
  have hsum : s.sum f = f η₁s + (s.erase η₁s).sum f := by
    rw [← Finset.add_sum_erase s f hη₁s_mem]
  calc
    (c : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ))
        = f η₁s + (s.erase η₁s).sum f := by
          rw [hanchor_norm, hsum_erase]
          ring
    _ = s.sum f := hsum.symm
    _ = ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) := by
          simp [s, f]

theorem theorem_6_8_tau1_Y_anchor_quadratic_le_cfNormSq_nat
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {c : ℕ} {x : ℤ}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (c : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (c : ℂ)) :
    (c : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) ≤
      Section5.cfNormSq A := by
  calc
    (c : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ))
        =
      ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) :=
          theorem_6_8_tau1_Y_coeff_normSq_sum_eq_anchor_quadratic_nat
            hη₁Y hanchor hdiff
    _ ≤ Section5.cfNormSq A :=
          theorem_6_8_tau1_Y_coeff_normSq_sum_le_cfNormSq
            h68 hfamily hτ₁ A

theorem theorem_6_8_anchor_quadratic_bound_of_nat_coefficients_and_norm
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {c : ℕ} {x : ℤ}
    (hc : 1 < c)
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (c : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (c : ℂ))
    (hnorm : Section5.cfNormSq A ≤ 1 + (c : ℝ) ^ (2 : ℕ)) :
    ((x - 1) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1 := by
  have hlower :
      (c : ℝ) ^ (2 : ℕ) *
          (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
            ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) ≤
        Section5.cfNormSq A :=
    theorem_6_8_tau1_Y_anchor_quadratic_le_cfNormSq_nat
      h68 hfamily hτ₁ hη₁Y hanchor hdiff
  have hc_sq_gt_one : (1 : ℝ) < (c : ℝ) ^ (2 : ℕ) := by
    have hcR : (1 : ℝ) < c := by exact_mod_cast hc
    nlinarith
  have hquad_lt :
      (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) < 2 := by
    by_contra hnot
    have hge :
        2 ≤ (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) :=
      le_of_not_gt hnot
    nlinarith [sq_nonneg ((c : ℝ))]
  let q : ℤ :=
    (x - 1) ^ (2 : ℕ) +
      ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ)
  have hqR : (q : ℝ) =
      ((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ) := by
    dsimp [q]
    norm_num
  have hqRlt : (q : ℝ) < 2 := by
    rw [hqR]
    exact hquad_lt
  have hq_lt : q < 2 := by
    exact_mod_cast hqRlt
  omega

theorem theorem_6_8_coeff_eq_relIndex_mul_x_of_anchor_and_diff
    {G : Type u} [Finite G]
    {L : Type u} [Group L]
    {H Z : Subgroup L}
    {A ψη η₁ : Section1.ClassFunction G}
    {x : ℤ}
    (hanchor :
      Section1.scalarProduct G A η₁ =
        (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff :
      Section1.scalarProduct G A (ψη - η₁) = (Z.relIndex H : ℂ)) :
    Section1.scalarProduct G A ψη =
      (Z.relIndex H : ℂ) * ((x : ℤ) : ℂ) := by
  have hsub :
      Section1.scalarProduct G A ψη - Section1.scalarProduct G A η₁ =
        (Z.relIndex H : ℂ) := by
    simpa [Section5.scalarProduct_sub_right] using hdiff
  calc
    Section1.scalarProduct G A ψη =
        (Section1.scalarProduct G A ψη - Section1.scalarProduct G A η₁) +
          Section1.scalarProduct G A η₁ := by ring
    _ = (Z.relIndex H : ℂ) +
        (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ) := by
          rw [hsub, hanchor]
    _ = (Z.relIndex H : ℂ) * ((x : ℤ) : ℂ) := by
          have hxcast : ((x - 1 : ℤ) : ℂ) = ((x : ℤ) : ℂ) - 1 := by
            norm_num
          rw [hxcast]
          ring

theorem theorem_6_8_tau1_Y_coeff_normSq_sum_eq_anchor_quadratic
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L]
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {x : ℤ}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (Z.relIndex H : ℂ)) :
    (Z.relIndex H : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) =
      ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) := by
  classical
  let η₁s : Y := ⟨η₁, hη₁Y⟩
  let f : Y → ℝ := fun η =>
    Complex.normSq
      (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L)))
  let s : Finset Y := @Finset.univ Y (Fintype.ofFinite Y)
  have hη₁s_mem : η₁s ∈ s := by simp [s]
  have hanchor_norm :
      f η₁s = (Z.relIndex H : ℝ) ^ (2 : ℕ) *
          ((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) := by
    dsimp [f, η₁s]
    rw [hanchor, Complex.normSq_mul]
    norm_num [Complex.normSq]
    ring
  have hnonanchor : ∀ η ∈ s.erase η₁s,
      f η = (Z.relIndex H : ℝ) ^ (2 : ℕ) *
          ((x : ℤ) : ℝ) ^ (2 : ℕ) := by
    intro η hη
    have hηne : η ≠ η₁s := (Finset.mem_erase.mp hη).1
    have hηval_ne : (η : Section1.ClassFunction L) ≠ η₁ := by
      intro h
      exact hηne (Subtype.ext h)
    have hcoeff :
        Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L)) =
          (Z.relIndex H : ℂ) * ((x : ℤ) : ℂ) :=
      theorem_6_8_coeff_eq_relIndex_mul_x_of_anchor_and_diff
        (G := G) (L := L) (H := H) (Z := Z)
        (A := A) (ψη := τ₁ (η : Section1.ClassFunction L)) (η₁ := τ₁ η₁)
        (x := x) hanchor (hdiff (η : Section1.ClassFunction L) η.2 hηval_ne)
    dsimp [f]
    rw [hcoeff, Complex.normSq_mul]
    norm_num [Complex.normSq]
    ring
  have hcard : (s.erase η₁s).card = Y.card - 1 := by
    have hscard : s.card = Y.card := by
      dsimp [s]
      rw [(@Nat.card_eq_fintype_card Y (Fintype.ofFinite Y)).symm]
      exact Nat.card_eq_finsetCard Y
    rw [Finset.card_erase_of_mem hη₁s_mem, hscard]
  have hsum_erase :
      (s.erase η₁s).sum f =
        ((Y.card - 1 : ℕ) : ℝ) *
          ((Z.relIndex H : ℝ) ^ (2 : ℕ) *
            ((x : ℤ) : ℝ) ^ (2 : ℕ)) := by
    rw [Finset.sum_eq_card_nsmul (s := s.erase η₁s)
      (f := f)
      (b := (Z.relIndex H : ℝ) ^ (2 : ℕ) *
        ((x : ℤ) : ℝ) ^ (2 : ℕ))]
    · rw [hcard]
      simp [nsmul_eq_mul]
    · exact hnonanchor
  have hsum : s.sum f = f η₁s + (s.erase η₁s).sum f := by
    rw [← Finset.add_sum_erase s f hη₁s_mem]
  calc
    (Z.relIndex H : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ))
        = f η₁s + (s.erase η₁s).sum f := by
          rw [hanchor_norm, hsum_erase]
          ring
    _ = s.sum f := hsum.symm
    _ = ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) := by
          simp [s, f]

theorem theorem_6_8_tau1_Y_anchor_quadratic_le_cfNormSq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {x : ℤ}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (Z.relIndex H : ℂ)) :
    (Z.relIndex H : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) ≤
      Section5.cfNormSq A := by
  calc
    (Z.relIndex H : ℝ) ^ (2 : ℕ) *
        (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ))
        =
      ∑ η ∈ (@Finset.univ Y (Fintype.ofFinite Y)),
        Complex.normSq
          (Section1.scalarProduct G A (τ₁ (η : Section1.ClassFunction L))) :=
          theorem_6_8_tau1_Y_coeff_normSq_sum_eq_anchor_quadratic
            (H := H) (Z := Z) hη₁Y hanchor hdiff
    _ ≤ Section5.cfNormSq A :=
          theorem_6_8_tau1_Y_coeff_normSq_sum_le_cfNormSq
            h68 hfamily hτ₁ A

theorem theorem_6_8_anchor_quadratic_bound_of_coefficients_and_norm
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {A : Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {x : ℤ}
    (hη₁Y : η₁ ∈ Y)
    (hanchor :
      Section1.scalarProduct G A (τ₁ η₁) =
        (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ))
    (hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G A (τ₁ η - τ₁ η₁) = (Z.relIndex H : ℂ))
    (hnorm : Section5.cfNormSq A < 2 * (Z.relIndex H : ℝ) ^ (2 : ℕ)) :
    ((x - 1) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1 := by
  have hlower :
      (Z.relIndex H : ℝ) ^ (2 : ℕ) *
          (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
            ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) ≤
        Section5.cfNormSq A :=
    theorem_6_8_tau1_Y_anchor_quadratic_le_cfNormSq
      h68 hfamily hτ₁ hη₁Y hanchor hdiff
  have hrelpos : 0 < (Z.relIndex H : ℝ) := by
    have hrelposNat : 0 < Z.relIndex H := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
      exact Nat.card_pos
    exact_mod_cast hrelposNat
  have hrel_sq_pos : 0 < (Z.relIndex H : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hquad_lt :
      (((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ)) < 2 := by
    nlinarith
  let q : ℤ :=
    (x - 1) ^ (2 : ℕ) +
      ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ)
  have hqR : (q : ℝ) =
      ((x - 1 : ℤ) : ℝ) ^ (2 : ℕ) +
        ((Y.card - 1 : ℕ) : ℝ) * ((x : ℤ) : ℝ) ^ (2 : ℕ) := by
    dsimp [q]
    norm_num
  have hqRlt : (q : ℝ) < 2 := by
    rw [hqR]
    exact hquad_lt
  have hq_lt : q < 2 := by
    exact_mod_cast hqRlt
  omega

theorem theorem_6_8_anchor_quadratic_bound_of_norm_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hnorm : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          Section5.cfNormSq
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) <
              2 * (Z.relIndex H : ℝ) ^ (2 : ℕ)) :
    ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          ∃ x : ℤ,
            Section1.scalarProduct G
              (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
              (τ₁ η₁) =
                (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ) ∧
              ((x - 1) ^ (2 : ℕ) +
                  ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1 := by
  intro φ hφ hφne
  rcases theorem_6_8_scalarProduct_transform_sub_tau1_int_relIndex_multiple_of_caseB_familyData
      h68 hpQ hcase hB hfamily hτ₁ hφ hφne hη₁Y hη₁Y with
    ⟨k, hk⟩
  let x : ℤ := k + 1
  have hanchor :
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) (τ₁ η₁) =
          (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ) := by
    have hxcast : ((x - 1 : ℤ) : ℂ) = (k : ℂ) := by
      dsimp [x]
      norm_num
    rw [hk, hxcast]
  have hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (τ₁ η - τ₁ η₁) = (Z.relIndex H : ℂ) := by
    intro η hηY hηne
    exact theorem_6_8_scalarProduct_transform_sub_tau1_Y_diff_eq_relIndex_of_caseB_familyData
      h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y hηY hηne
  refine ⟨x, hanchor, ?_⟩
  exact theorem_6_8_anchor_quadratic_bound_of_coefficients_and_norm
    h68 hfamily hτ₁ hη₁Y hanchor hdiff (hnorm φ hφ hφne)

theorem theorem_6_8_anchor_integer_dichotomy_of_quadratic_bound
    {m : ℕ} {x : ℤ} (hm : 1 < m)
    (hquad :
      ((x - 1) ^ (2 : ℕ) + ((m - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1) :
    x = 0 ∨ x = 1 ∧ m = 2 := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have hm1 : (1 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) := by omega
    have hx_sq_pos : (0 : ℤ) < x ^ (2 : ℕ) := by
      exact sq_pos_of_ne_zero hx0
    have hx_sq_one : (1 : ℤ) ≤ x ^ (2 : ℕ) := by omega
    have hterm_ge : (1 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) := by
      nlinarith
    have hfirst_nonneg : (0 : ℤ) ≤ (x - 1) ^ (2 : ℕ) := by
      exact sq_nonneg (x - 1)
    have hterm_le : ((m - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) ≤ 1 := by
      nlinarith
    have hterm_eq : ((m - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) = 1 := by
      omega
    have hfirst_zero : (x - 1) ^ (2 : ℕ) = 0 := by
      nlinarith
    have hx1 : x - 1 = 0 := by
      exact sq_eq_zero_iff.mp hfirst_zero
    constructor
    · omega
    · have hmminus : ((m - 1 : ℕ) : ℤ) = 1 := by
        nlinarith
      omega

theorem theorem_6_8_2_2_commonY_of_anchor_dichotomy_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hdich :
      (∀ φ : Section1.ClassFunction Z,
        Section1.IsIrreducibleCharacterOnGroup φ →
          φ ≠ Section1.principalCharacter Z →
            Section1.scalarProduct G
              (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
                (Z.relIndex H : ℂ) • τ₁ η₁)
              (τ₁ η₁) = 0) ∨
      (∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∀ φ : Section1.ClassFunction Z,
            Section1.IsIrreducibleCharacterOnGroup φ →
              φ ≠ Section1.principalCharacter Z →
                Section1.scalarProduct G
                  (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) +
                    (Z.relIndex H : ℂ) • (-τ₁ η₂))
                  (τ₁ η₁) = 0)) :
    ∃ Ycf : Section1.ClassFunction G,
      theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf := by
  rcases hdich with hleft | hright
  · refine ⟨τ₁ η₁, ?_⟩
    refine theorem_6_8_2_2_commonY_of_left_orthogonal_data hη₁Y ?_
    intro φ hφ hφne
    exact theorem_6_8_left_candidate_orthogonal_of_anchor_zero_caseB_familyData
      h68 hcase hB hfamily hτ₁ hφ hφne hη₁Y (hleft φ hφ hφne)
  · rcases hright with ⟨η₂, hcard, hη₂Y, hη₂ne, hanchor⟩
    refine ⟨-τ₁ η₂, ?_⟩
    refine theorem_6_8_2_2_commonY_of_right_orthogonal_data
      hη₁Y hcard hη₂Y hη₂ne ?_
    intro φ hφ hφne
    exact theorem_6_8_right_candidate_orthogonal_of_anchor_zero_caseB_familyData
      h68 hcase hB hfamily hτ₁ hφ hφne hcard hη₁Y hη₂Y hη₂ne
      (hanchor φ hφ hφne)

theorem theorem_6_8_2_2_commonY_of_anchor_quadratic_bound_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hquad :
      ∀ φ : Section1.ClassFunction Z,
        Section1.IsIrreducibleCharacterOnGroup φ →
          φ ≠ Section1.principalCharacter Z →
            ∃ x : ℤ,
              Section1.scalarProduct G
                (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
                (τ₁ η₁) =
                  (Z.relIndex H : ℂ) * ((x - 1 : ℤ) : ℂ) ∧
                ((x - 1) ^ (2 : ℕ) +
                    ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1) :
    ∃ Ycf : Section1.ClassFunction G,
      theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf := by
  classical
  by_cases hex :
      ∃ φ : Section1.ClassFunction Z,
        Section1.IsIrreducibleCharacterOnGroup φ ∧
          φ ≠ Section1.principalCharacter Z
  · rcases hex with ⟨φ₀, hφ₀, hφ₀ne⟩
    rcases hquad φ₀ hφ₀ hφ₀ne with ⟨x, hxcoef, hxquad⟩
    have hYcard_gt : 1 < Y.card :=
      theorem_6_8_Y_card_gt_one_of_familyData h68 hfamily
    have hxsplit :
        x = 0 ∨ x = 1 ∧ Y.card = 2 :=
      theorem_6_8_anchor_integer_dichotomy_of_quadratic_bound
        hYcard_gt hxquad
    have hη₁self_src : Section1.scalarProduct L η₁ η₁ = 1 := by
      rcases theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y with
        ⟨_n, ρ, hρirr, hη₁eq⟩
      rw [hη₁eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
    have hτη₁self : Section1.scalarProduct G (τ₁ η₁) (τ₁ η₁) = 1 := by
      rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
        hτ₁ hη₁Y hη₁Y, hη₁self_src]
    rcases hxsplit with hx0 | hx1
    · have hanchor₀ :
          Section1.scalarProduct G
            (T (Section1.inducedCF Z φ₀ - (Z.relIndex H : ℂ) • η₁) +
              (Z.relIndex H : ℂ) • τ₁ η₁)
            (τ₁ η₁) = 0 := by
        rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
          hxcoef, hτη₁self, hx0]
        norm_num
      refine theorem_6_8_2_2_commonY_of_anchor_dichotomy_caseB_familyData
        h68 hcase hB hfamily hτ₁ hη₁Y ?_
      left
      intro φ hφ hφne
      have hind :
          Section1.scalarProduct G
              (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
              (τ₁ η₁) =
            Section1.scalarProduct G
              (T (Section1.inducedCF Z φ₀ - (Z.relIndex H : ℂ) • η₁))
              (τ₁ η₁) :=
        theorem_6_8_scalarProduct_transform_sub_tau1_independent_of_nonprincipal_caseB_familyData
          h68 hpQ hcase hB hfamily hτ₁ hφ hφne hφ₀ hφ₀ne hη₁Y hη₁Y
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left] at hanchor₀
      rw [hind]
      exact hanchor₀
    · rcases hx1 with ⟨hxone, hcard⟩
      rcases Finset.one_lt_card.mp hYcard_gt with
        ⟨ηa, hηaY, ηb, hηbY, hηab⟩
      obtain ⟨η₂, hη₂Y, hη₂ne⟩ :
          ∃ η₂ : Section1.ClassFunction L, η₂ ∈ Y ∧ η₂ ≠ η₁ := by
        by_cases hηa : ηa = η₁
        · refine ⟨ηb, hηbY, ?_⟩
          intro hηb
          exact hηab (by rw [hηa, hηb])
        · exact ⟨ηa, hηaY, hηa⟩
      have hη₂η₁_src : Section1.scalarProduct L η₂ η₁ = 0 := by
        have hη₂irr : Section1.IsIrreducibleCharacterOnGroup η₂ :=
          theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₂ hη₂Y
        have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
          theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
        rcases hη₂irr with ⟨n₂, ρ₂, hρ₂, hη₂eq⟩
        rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
        exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
          η₂ η₁ ρ₂ ρ₁ hη₂eq hη₁eq hρ₂ hρ₁ hη₂ne
      have hτη₂η₁ : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₁) = 0 := by
        rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
          hτ₁ hη₂Y hη₁Y, hη₂η₁_src]
      have hnegτη₂η₁ :
          Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₁) = 0 := by
        rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
          hτη₂η₁]
        simp
      have hanchor₀ :
          Section1.scalarProduct G
            (T (Section1.inducedCF Z φ₀ - (Z.relIndex H : ℂ) • η₁) +
              (Z.relIndex H : ℂ) • (-τ₁ η₂))
            (τ₁ η₁) = 0 := by
        rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
          hxcoef, hnegτη₂η₁, hxone]
        norm_num
      refine theorem_6_8_2_2_commonY_of_anchor_dichotomy_caseB_familyData
        h68 hcase hB hfamily hτ₁ hη₁Y ?_
      right
      refine ⟨η₂, hcard, hη₂Y, hη₂ne, ?_⟩
      intro φ hφ hφne
      have hind :
          Section1.scalarProduct G
              (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
              (τ₁ η₁) =
            Section1.scalarProduct G
              (T (Section1.inducedCF Z φ₀ - (Z.relIndex H : ℂ) • η₁))
              (τ₁ η₁) :=
        theorem_6_8_scalarProduct_transform_sub_tau1_independent_of_nonprincipal_caseB_familyData
          h68 hpQ hcase hB hfamily hτ₁ hφ hφne hφ₀ hφ₀ne hη₁Y hη₁Y
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left] at hanchor₀
      rw [hind]
      exact hanchor₀
  · refine theorem_6_8_2_2_commonY_of_anchor_dichotomy_caseB_familyData
      h68 hcase hB hfamily hτ₁ hη₁Y ?_
    left
    intro φ hφ hφne
    exact (hex ⟨φ, hφ, hφne⟩).elim

theorem theorem_6_8_2_2_commonY_of_norm_bound_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hnorm : ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          Section5.cfNormSq
            (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁)) <
              2 * (Z.relIndex H : ℝ) ^ (2 : ℕ)) :
    ∃ Ycf : Section1.ClassFunction G,
      theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf := by
  exact theorem_6_8_2_2_commonY_of_anchor_quadratic_bound_caseB_familyData
    h68 hpQ hcase hB hfamily hτ₁ hη₁Y
    (theorem_6_8_anchor_quadratic_bound_of_norm_caseB_familyData
      h68 hpQ hcase hB hfamily hτ₁ hη₁Y hnorm)

theorem theorem_6_8_2_2_of_norm_bound_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L} :
    theorem_6_8_2_2_statement L H W1 W2 W Z S SZ X Y T τ₁ η₁ := by
  intro h68 hpQ hcase hB hfamily hτ₁ hη₁Y
  exact theorem_6_8_2_2_commonY_of_norm_bound_caseB_familyData
    h68 hpQ hcase hB hfamily hτ₁ hη₁Y
    (theorem_6_8_norm_bound_caseB_familyData h68 hcase hB hfamily hη₁Y)

theorem theorem_6_8_scalarProduct_commonY_induced_shift_eq_neg
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    Section1.scalarProduct G
        (T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁))
        (τ₁ η) =
      -(Z.relIndex H : ℂ) * Section1.scalarProduct G Ycf (τ₁ η) := by
  rcases hcommon with ⟨_hη₁Y, _hYcf, hφdata⟩
  rcases hφdata φ hφ hφne with ⟨Xφ, horth, hTφ⟩
  rw [hTφ, Section5.scalarProduct_sub_left,
    Section1.scalarProduct_smul_left, horth η hηY]
  ring

theorem theorem_6_8_weighted_shift_scalar_sum_eq_commonY_of_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {φ : Section1.ClassFunction Z}
    {ι : Type*} [Finite ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H)
    (hshift :
      Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁ =
        Section1.weightedFamilySum (fun i => (e i : ℂ))
          (fun i => Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁))
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    (∑ i : ι, (e i : ℂ) *
        Section1.scalarProduct G
          (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η)) =
      -(Z.relIndex H : ℂ) * Section1.scalarProduct G Ycf (τ₁ η) := by
  have hscalar :=
    theorem_6_8_scalarProduct_commonY_induced_shift_eq_neg
      hcommon hφ hφne hηY
  rw [hshift] at hscalar
  rw [theorem_6_8_linearMap_weightedFamilySum] at hscalar
  rw [theorem_6_8_scalarProduct_weightedFamilySum_left] at hscalar
  exact hscalar


theorem theorem_6_8_mem_Y_cfNormSq_eq_one
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) :
    Section5.cfNormSq η = 1 := by
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY
  have hηself : Section1.scalarProduct L η η = 1 := by
    rcases hηirr with ⟨_n, ρ, hρirr, hηeq⟩
    rw [hηeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  unfold Section5.cfNormSq
  rw [hηself]
  simp

theorem theorem_6_8_mem_Y_smul_cfNormSq_eq_sq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η : Section1.ClassFunction L} (hηY : η ∈ Y) (e : ℕ) :
    Section5.cfNormSq ((e : ℂ) • η) = (e : ℝ) ^ (2 : ℕ) := by
  have hηnorm : Section5.cfNormSq η = 1 :=
    theorem_6_8_mem_Y_cfNormSq_eq_one h68 hfamily hηY
  rw [Section5.cfNormSq_smul, hηnorm]
  norm_num [Complex.normSq]
  ring

theorem theorem_6_8_projection_remainder_norm_le_of_pf54
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Yrem : Section1.ClassFunction G} {ψ : Section1.ClassFunction L}
    {P Q : Prop}
    (hpf54 :
      Section5.cfNormSq Yrem ≥ Section5.cfNormSq ψ →
        P ∧ Section5.cfNormSq Yrem = Section5.cfNormSq ψ ∧ Q) :
    Section5.cfNormSq Yrem ≤ Section5.cfNormSq ψ := by
  by_cases hge : Section5.cfNormSq Yrem ≥ Section5.cfNormSq ψ
  · rw [(hpf54 hge).2.1]
  · linarith

theorem theorem_6_8_isVirtualCharacter_of_integerSpan_signedOrthonormalFinset
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    {A : Section1.ClassFunction G}
    (hA : Section5.integerSpan R A) :
    Theory.Character.IsVirtualCharacter A := by
  classical
  rcases hA with ⟨v, rfl⟩
  exact theorem_6_8_isVirtualCharacter_evalCoeff
    (fun X : R => (X : Section1.ClassFunction G))
    (fun X => Section3.isVirtualCharacter_of_signedIrreducible_pf35
      (hR.1 (X : Section1.ClassFunction G) X.2))
    v

theorem theorem_6_8_pf54_remainder_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R : Finset (Section1.ClassFunction G)}
    (h52b : Section5.hypothesis_5_2_b_statement U T)
    (hR : Section5.signedOrthonormalFinset R)
    {α : Section1.ClassFunction L}
    (hαspan : Section5.integerSpanOn U Section5.puncturedSet α)
    {Xbig Yrem : Section1.ClassFunction G}
    (hXbig_span : Section5.integerSpan R Xbig)
    (hT : T α = Xbig - Yrem) :
    Theory.Character.IsVirtualCharacter Yrem := by
  have hTvirt : Theory.Character.IsVirtualCharacter (T α) :=
    (h52b.2 α hαspan).1
  have hXvirt : Theory.Character.IsVirtualCharacter Xbig :=
    theorem_6_8_isVirtualCharacter_of_integerSpan_signedOrthonormalFinset
      hR hXbig_span
  have hYeq : Yrem = Xbig - T α := by
    rw [hT]
    ext g
    simp [sub_eq_add_neg]
  simpa [hYeq] using Section3.isVirtualCharacter_sub hXvirt hTvirt

theorem theorem_6_8_projection_integer_coeff_sq_le_norm
    {G : Type u} [Group G] [Finite G]
    {A Ycf : Section1.ClassFunction G}
    (hAvirt : Theory.Character.IsVirtualCharacter A)
    (hYcfvirt : Theory.Character.IsVirtualCharacter Ycf)
    (hYself : Section1.scalarProduct G Ycf Ycf = 1) :
    ∃ b : ℤ,
      Section1.scalarProduct G A Ycf = (b : ℂ) ∧
        ((b : ℝ) ^ (2 : ℕ)) ≤ Section5.cfNormSq A := by
  classical
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hAvirt hYcfvirt with
    ⟨b, hb⟩
  refine ⟨b, hb, ?_⟩
  let R : Section1.ClassFunction G := A - (b : ℂ) • Ycf
  have hRYcf : Section1.scalarProduct G R Ycf = 0 := by
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hb, Section1.scalarProduct_smul_left,
      hYself]
    norm_num
  have hYcfR : Section1.scalarProduct G Ycf R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRYcf
  have hR_scaled :
      Section1.scalarProduct G R ((b : ℂ) • Ycf) = 0 := by
    rw [Section1.scalarProduct_smul_right, hRYcf]
    simp
  have hscaled_R :
      Section1.scalarProduct G ((b : ℂ) • Ycf) R = 0 := by
    rw [Section1.scalarProduct_smul_left, hYcfR]
    simp
  have hA :
      A = R + (b : ℂ) • Ycf := by
    dsimp [R]
    ext g
    simp [sub_eq_add_neg, add_assoc]
  have hYnorm : Section5.cfNormSq Ycf = 1 := by
    unfold Section5.cfNormSq
    rw [hYself]
    norm_num
  have hscaled_norm :
      Section5.cfNormSq ((b : ℂ) • Ycf) = (b : ℝ) ^ (2 : ℕ) := by
    rw [Section5.cfNormSq_smul, hYnorm]
    norm_num [Complex.normSq]
    ring
  have hnorm :
      Section5.cfNormSq A =
        Section5.cfNormSq R + Section5.cfNormSq ((b : ℂ) • Ycf) := by
    rw [hA]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hR_scaled hscaled_R
  have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
  nlinarith

theorem theorem_6_8_projection_int_coeff_le_of_pf54_norm
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y)
    {Yrem Ycf : Section1.ClassFunction G} {e : ℕ}
    {P Q : Prop}
    (hYremvirt : Theory.Character.IsVirtualCharacter Yrem)
    (hYcfvirt : Theory.Character.IsVirtualCharacter Ycf)
    (hYself : Section1.scalarProduct G Ycf Ycf = 1)
    (hpf54 :
      Section5.cfNormSq Yrem ≥ Section5.cfNormSq ((e : ℂ) • η₁) →
        P ∧ Section5.cfNormSq Yrem =
            Section5.cfNormSq ((e : ℂ) • η₁) ∧ Q) :
    ∃ b : ℤ,
      Section1.scalarProduct G Yrem Ycf = (b : ℂ) ∧ b ≤ (e : ℤ) := by
  have hYrem_le :
      Section5.cfNormSq Yrem ≤ Section5.cfNormSq ((e : ℂ) • η₁) :=
    theorem_6_8_projection_remainder_norm_le_of_pf54
      (Yrem := Yrem) (ψ := (e : ℂ) • η₁) hpf54
  have hanchor_norm :
      Section5.cfNormSq ((e : ℂ) • η₁) = (e : ℝ) ^ (2 : ℕ) :=
    theorem_6_8_mem_Y_smul_cfNormSq_eq_sq h68 hfamily hη₁Y e
  rcases theorem_6_8_projection_integer_coeff_sq_le_norm
      hYremvirt hYcfvirt hYself with
    ⟨b, hcoeff, hb_sq_norm⟩
  refine ⟨b, hcoeff, ?_⟩
  have hb_sq_le : (b : ℝ) ^ (2 : ℕ) ≤ (e : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hb_abs : |(b : ℝ)| ≤ |(e : ℝ)| :=
    (sq_le_sq.mp hb_sq_le)
  have he_abs : |(e : ℝ)| = (e : ℝ) := by
    exact abs_of_nonneg (by positivity)
  have hb_real : (b : ℝ) ≤ (e : ℝ) := by
    exact (abs_le.mp (by simpa [he_abs] using hb_abs)).2
  exact_mod_cast hb_real

theorem theorem_6_8_eq_smul_of_scalarProduct_eq_and_cfNormSq_eq
    {G : Type u} [Group G] [Finite G]
    {A Ycf : Section1.ClassFunction G} {b : ℤ}
    (hYself : Section1.scalarProduct G Ycf Ycf = 1)
    (hcoeff : Section1.scalarProduct G A Ycf = (b : ℂ))
    (hnorm : Section5.cfNormSq A = (b : ℝ) ^ (2 : ℕ)) :
    A = (b : ℂ) • Ycf := by
  classical
  let R : Section1.ClassFunction G := A - (b : ℂ) • Ycf
  have hRYcf : Section1.scalarProduct G R Ycf = 0 := by
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hcoeff, Section1.scalarProduct_smul_left,
      hYself]
    norm_num
  have hYcfR : Section1.scalarProduct G Ycf R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRYcf
  have hR_scaled :
      Section1.scalarProduct G R ((b : ℂ) • Ycf) = 0 := by
    rw [Section1.scalarProduct_smul_right, hRYcf]
    simp
  have hscaled_R :
      Section1.scalarProduct G ((b : ℂ) • Ycf) R = 0 := by
    rw [Section1.scalarProduct_smul_left, hYcfR]
    simp
  have hA :
      A = R + (b : ℂ) • Ycf := by
    dsimp [R]
    ext g
    simp [sub_eq_add_neg, add_assoc]
  have hYnorm : Section5.cfNormSq Ycf = 1 := by
    unfold Section5.cfNormSq
    rw [hYself]
    norm_num
  have hscaled_norm :
      Section5.cfNormSq ((b : ℂ) • Ycf) = (b : ℝ) ^ (2 : ℕ) := by
    rw [Section5.cfNormSq_smul, hYnorm]
    norm_num [Complex.normSq]
    ring
  have hnorm_decomp :
      Section5.cfNormSq A =
        Section5.cfNormSq R + Section5.cfNormSq ((b : ℂ) • Ycf) := by
    rw [hA]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hR_scaled hscaled_R
  have hRnorm : Section5.cfNormSq R = 0 := by
    nlinarith [Section5.cfNormSq_nonneg R]
  have hRzero : R = 0 := Section5.cfNormSq_eq_zero hRnorm
  rw [hA, hRzero]
  simp

theorem theorem_6_8_eq_nat_smul_of_scalarProduct_eq_and_cfNormSq_le
    {G : Type u} [Group G] [Finite G]
    {A Ycf : Section1.ClassFunction G} {e : ℕ}
    (hYself : Section1.scalarProduct G Ycf Ycf = 1)
    (hcoeff : Section1.scalarProduct G A Ycf = (e : ℂ))
    (hnorm_le : Section5.cfNormSq A ≤ (e : ℝ) ^ (2 : ℕ)) :
    A = (e : ℂ) • Ycf := by
  classical
  let R : Section1.ClassFunction G := A - (e : ℂ) • Ycf
  have hRYcf : Section1.scalarProduct G R Ycf = 0 := by
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hcoeff, Section1.scalarProduct_smul_left,
      hYself]
    norm_num
  have hYcfR : Section1.scalarProduct G Ycf R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRYcf
  have hR_scaled :
      Section1.scalarProduct G R ((e : ℂ) • Ycf) = 0 := by
    rw [Section1.scalarProduct_smul_right, hRYcf]
    simp
  have hscaled_R :
      Section1.scalarProduct G ((e : ℂ) • Ycf) R = 0 := by
    rw [Section1.scalarProduct_smul_left, hYcfR]
    simp
  have hA :
      A = R + (e : ℂ) • Ycf := by
    dsimp [R]
    ext g
    simp [sub_eq_add_neg, add_assoc]
  have hYnorm : Section5.cfNormSq Ycf = 1 := by
    unfold Section5.cfNormSq
    rw [hYself]
    norm_num
  have hscaled_norm :
      Section5.cfNormSq ((e : ℂ) • Ycf) = (e : ℝ) ^ (2 : ℕ) := by
    rw [Section5.cfNormSq_smul, hYnorm]
    norm_num [Complex.normSq]
    ring
  have hnorm_decomp :
      Section5.cfNormSq A =
        Section5.cfNormSq R + Section5.cfNormSq ((e : ℂ) • Ycf) := by
    rw [hA]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hR_scaled hscaled_R
  have hproj : (e : ℝ) ^ (2 : ℕ) ≤ Section5.cfNormSq A := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hnorm_eq : Section5.cfNormSq A = (e : ℝ) ^ (2 : ℕ) :=
    le_antisymm hnorm_le hproj
  have hcoeff_int :
      Section1.scalarProduct G A Ycf = (((e : ℤ) : ℂ)) := by
    simpa using hcoeff
  have hnorm_int :
      Section5.cfNormSq A = (((e : ℤ) : ℝ)) ^ (2 : ℕ) := by
    simpa using hnorm_eq
  have hAeq :=
    theorem_6_8_eq_smul_of_scalarProduct_eq_and_cfNormSq_eq
      (A := A) (Ycf := Ycf) (b := (e : ℤ))
      hYself hcoeff_int hnorm_int
  simpa using hAeq


theorem theorem_6_8_int_coeff_eq_of_weighted_sum_eq
    {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (b : ι → ℤ) (i0 : ι)
    (hb_le : ∀ i, b i ≤ (e i : ℤ))
    (hsum : (∑ i : ι, (e i : ℤ) * b i) =
      ∑ i : ι, (e i : ℤ) * (e i : ℤ))
    (hei0 : e i0 ≠ 0) :
    b i0 = (e i0 : ℤ) := by
  classical
  let d : ι → ℕ := fun i => Int.toNat ((e i : ℤ) - b i)
  have hd : ∀ i, (d i : ℤ) = (e i : ℤ) - b i := by
    intro i
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (hb_le i))
  have hsumd_int : (∑ i : ι, (e i : ℤ) * (d i : ℤ)) = 0 := by
    calc
      (∑ i : ι, (e i : ℤ) * (d i : ℤ)) =
          ∑ i : ι, (e i : ℤ) * ((e i : ℤ) - b i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hd i]
      _ = (∑ i : ι, (e i : ℤ) * (e i : ℤ)) -
            (∑ i : ι, (e i : ℤ) * b i) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = 0 := by rw [← hsum]; ring
  have hsumd_nat : (∑ i : ι, e i * d i) = 0 := by
    exact_mod_cast hsumd_int
  have hterm0 : e i0 * d i0 = 0 := by
    exact (Finset.sum_eq_zero_iff.mp hsumd_nat) i0 (Finset.mem_univ i0)
  have hd0 : d i0 = 0 := by
    rcases Nat.mul_eq_zero.mp hterm0 with he | hd'
    · exact False.elim (hei0 he)
    · exact hd'
  have hdiff0 : (e i0 : ℤ) - b i0 = 0 := by
    have hd_cast := hd i0
    rw [hd0] at hd_cast
    exact hd_cast.symm
  omega

theorem theorem_6_8_selected_scalar_eq_of_weighted_projection_int_coefficients
    {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (b : ι → ℤ) (i0 : ι)
    {y : ℂ} {s : ι → ℂ}
    (hscalar : ∀ i, s i = -(b i : ℂ) * y)
    (hweighted : (∑ i : ι, (e i : ℂ) * s i) =
      -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y)
    (hb_le : ∀ i, b i ≤ (e i : ℤ))
    (hei0 : e i0 ≠ 0) :
    s i0 = -(e i0 : ℂ) * y := by
  classical
  by_cases hy : y = 0
  · simp [hscalar i0, hy]
  · have hweighted' :
        (∑ i : ι, (e i : ℂ) * (-(b i : ℂ) * y)) =
          -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y := by
      simpa [hscalar] using hweighted
    have hleft_factor :
        (∑ i : ι, (e i : ℂ) * (-(b i : ℂ) * y)) =
          -(∑ i : ι, (((e i : ℤ) * b i : ℤ) : ℂ)) * y := by
      calc
        (∑ i : ι, (e i : ℂ) * (-(b i : ℂ) * y)) =
            ∑ i : ι, (-(((e i : ℤ) * b i : ℤ) : ℂ) * y) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              norm_num [Int.cast_mul]
              ring
        _ = -(∑ i : ι, (((e i : ℤ) * b i : ℤ) : ℂ)) * y := by
              rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    have hright_factor :
        -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y =
          -(∑ i : ι, (((e i : ℤ) * (e i : ℤ) : ℤ) : ℂ)) * y := by
      congr 2
      refine Finset.sum_congr rfl ?_
      intro i _hi
      norm_num [Int.cast_mul]
    have hcancel :
        -(∑ i : ι, (((e i : ℤ) * b i : ℤ) : ℂ)) =
          -(∑ i : ι, (((e i : ℤ) * (e i : ℤ) : ℤ) : ℂ)) := by
      apply mul_right_cancel₀ hy
      rw [← hleft_factor, hweighted', hright_factor]
    have hcomplex :
        (∑ i : ι, (((e i : ℤ) * b i : ℤ) : ℂ)) =
          (∑ i : ι, (((e i : ℤ) * (e i : ℤ) : ℤ) : ℂ)) :=
      neg_injective hcancel
    have hsum : (∑ i : ι, (e i : ℤ) * b i) =
        ∑ i : ι, (e i : ℤ) * (e i : ℤ) := by
      exact_mod_cast hcomplex
    have hb_eq : b i0 = (e i0 : ℤ) :=
      theorem_6_8_int_coeff_eq_of_weighted_sum_eq e b i0 hb_le hsum hei0
    simp [hscalar i0, hb_eq]


theorem theorem_6_8_shift_orthogonal_of_scalarProduct_eq_neg
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {A Ycf : Section1.ClassFunction G} {a : ℂ}
    (hscalar : ∀ η : Section1.ClassFunction L, η ∈ Y →
      Section1.scalarProduct G A (τ₁ η) =
        -a * Section1.scalarProduct G Ycf (τ₁ η)) :
    orthogonalToTransformedFinset Y τ₁ (A + a • Ycf) := by
  intro η hηY
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
    hscalar η hηY]
  ring

theorem theorem_6_8_2_3_of_shift_orthogonality_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (horth : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
      orthogonalToTransformedFinset Y τ₁
        (T (χ - a • η₁) + a • Ycf)) :
    theorem_6_8_2_3_statement L H W1 W2 W Z S SZ X Y T τ₁ η₁ Ycf := by
  intro _h68 _hpQ _hcase _hB _hfamily _hcommon χ hχX
  exact theorem_6_8_decomposition_of_orthogonal_add_smul
    (Y := Y) (τ₁ := τ₁)
    (A := T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
    (Ycf := Ycf)
        (c := Section1.degree χ / (Nat.card W1 : ℂ))
        (horth χ hχX)

theorem theorem_6_8_2_3_of_shift_scalarProduct_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hscalar : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∀ η : Section1.ClassFunction L, η ∈ Y →
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        Section1.scalarProduct G (T (χ - a • η₁)) (τ₁ η) =
          -a * Section1.scalarProduct G Ycf (τ₁ η)) :
    theorem_6_8_2_3_statement L H W1 W2 W Z S SZ X Y T τ₁ η₁ Ycf := by
  refine theorem_6_8_2_3_of_shift_orthogonality_caseB_familyData ?_
  intro χ hχX
  exact theorem_6_8_shift_orthogonal_of_scalarProduct_eq_neg
    (Y := Y) (τ₁ := τ₁)
    (A := T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
    (Ycf := Ycf)
    (a := Section1.degree χ / (Nat.card W1 : ℂ))
    (hscalar χ hχX)

theorem theorem_6_8_X_shift_eta_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ η₁ : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y) :
    ∃ a : ℕ,
      Section1.degree χ = (a * Nat.card W1 : ℂ) ∧
        Section1.degree χ / (Nat.card W1 : ℂ) = (a : ℂ) ∧
          Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
            (χ - (a : ℂ) • η₁) := by
  rcases theorem_6_8_X_degree_div_cardW1
      hSbot hsemi hfamily hχX with ⟨a, hχdeg, hχdiv⟩
  refine ⟨a, hχdeg, hχdiv, ?_⟩
  have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
  have hηU : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
  have hχspan : Section5.integerSpan (X ∪ Y) χ :=
    Section5.integerSpan_of_mem (X ∪ Y) hχU
  have hηspan : Section5.integerSpan (X ∪ Y) η₁ :=
    Section5.integerSpan_of_mem (X ∪ Y) hηU
  have hηsmul : Section5.integerSpan (X ∪ Y) ((a : ℂ) • η₁) := by
    simpa using Section5.integerSpan_zsmul (S := X ∪ Y) (φ := η₁) (a : ℤ) hηspan
  have hspan : Section5.integerSpan (X ∪ Y) (χ - (a : ℂ) • η₁) :=
    Section5.integerSpan_sub hχspan hηsmul
  have hηdeg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hη₁Y
  have hdeg0 : Section1.degree (χ - (a : ℂ) • η₁) = 0 := by
    rw [Section1.degree_apply] at hχdeg hηdeg ⊢
    simp [hχdeg, hηdeg]
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩

theorem theorem_6_8_Y_diff_eta_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η η₁ : Section1.ClassFunction L}
    (hηY : η ∈ Y) (hη₁Y : η₁ ∈ Y) :
    Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet (η - η₁) := by
  have hηU : η ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hηY)
  have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
  have hηspan : Section5.integerSpan (X ∪ Y) η :=
    Section5.integerSpan_of_mem (X ∪ Y) hηU
  have hη₁span : Section5.integerSpan (X ∪ Y) η₁ :=
    Section5.integerSpan_of_mem (X ∪ Y) hη₁U
  have hspan : Section5.integerSpan (X ∪ Y) (η - η₁) :=
    Section5.integerSpan_sub hηspan hη₁span
  have hηdeg : Section1.degree η = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hηY
  have hη₁deg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hη₁Y
  have hdeg0 : Section1.degree (η - η₁) = 0 := by
    rw [Section1.degree_apply] at hηdeg hη₁deg ⊢
    simp [hηdeg, hη₁deg]
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩

theorem theorem_6_8_Y_diff_eta_integerSpanOn_Y
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {η η₁ : Section1.ClassFunction L}
    (hηY : η ∈ Y) (hη₁Y : η₁ ∈ Y) :
    Section5.integerSpanOn Y Section5.puncturedSet (η - η₁) := by
  have hηspan : Section5.integerSpan Y η :=
    Section5.integerSpan_of_mem Y hηY
  have hη₁span : Section5.integerSpan Y η₁ :=
    Section5.integerSpan_of_mem Y hη₁Y
  have hspan : Section5.integerSpan Y (η - η₁) :=
    Section5.integerSpan_sub hηspan hη₁span
  have hηdeg : Section1.degree η = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hηY
  have hη₁deg : Section1.degree η₁ = (Nat.card W1 : ℂ) :=
    theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hη₁Y
  have hdeg0 : Section1.degree (η - η₁) = 0 := by
    rw [Section1.degree_apply] at hηdeg hη₁deg ⊢
    simp [hηdeg, hη₁deg]
  exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg0⟩

theorem theorem_6_8_caseB_Y_generator_agreement
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {η η₁ : Section1.ClassFunction L}
    (hηY : η ∈ Y) (hη₁Y : η₁ ∈ Y) :
    τ₁ (η - η₁) = T (η - η₁) := by
  exact hτ₁.2.2 (η - η₁)
    (theorem_6_8_Y_diff_eta_integerSpanOn_Y hsemi hfamily hηY hη₁Y)


noncomputable def theorem_6_8_caseB_unionImage
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (η₁ : Section1.ClassFunction L)
    (Ycf : Section1.ClassFunction G)
    (hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y}) :
    Section1.ClassFunction G :=
  if hηY : (η : Section1.ClassFunction L) ∈ Y then
    τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf
  else
    Classical.choose
      (hshift (η : Section1.ClassFunction L) (by
        rcases Finset.mem_union.mp η.2 with hηX | hηY'
        · exact hηX
        · exact (hηY hηY').elim))

theorem theorem_6_8_caseB_unionImage_of_mem_Y
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η =
      τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf := by
  simp [theorem_6_8_caseB_unionImage, hηY]

theorem theorem_6_8_caseB_unionImage_X_spec
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηX : (η : Section1.ClassFunction L) ∈ X)
    (hηnotY : (η : Section1.ClassFunction L) ∉ Y) :
    let a : ℂ := Section1.degree (η : Section1.ClassFunction L) /
      (Nat.card W1 : ℂ)
    orthogonalToTransformedFinset Y τ₁
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) ∧
      T ((η : Section1.ClassFunction L) - a • η₁) =
        theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η - a • Ycf := by
  simpa [theorem_6_8_caseB_unionImage, hηnotY] using
    Classical.choose_spec (hshift (η : Section1.ClassFunction L) hηX)


theorem theorem_6_8_scalarProduct_eq_nat_mul_base_of_left_sub_orthogonal
    {L : Type u} [Group L] [Finite L]
    {ψ χ χ₀ : Section1.ClassFunction L} {d : ℕ}
    (horth : Section1.scalarProduct L (χ - (d : ℂ) • χ₀) ψ = 0) :
    Section1.scalarProduct L χ ψ =
      (d : ℂ) * Section1.scalarProduct L χ₀ ψ := by
  have h : Section1.scalarProduct L χ ψ -
      (d : ℂ) * Section1.scalarProduct L χ₀ ψ = 0 := by
    rw [← horth]
    rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left]
  calc
    Section1.scalarProduct L χ ψ =
        (Section1.scalarProduct L χ ψ -
          (d : ℂ) * Section1.scalarProduct L χ₀ ψ) +
            (d : ℂ) * Section1.scalarProduct L χ₀ ψ := by ring
    _ = (d : ℂ) * Section1.scalarProduct L χ₀ ψ := by rw [h]; ring

theorem theorem_6_8_caseA_source_coeff_eq_nat_mul_base_of_degree_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ χ₀ η₁ : Section1.ClassFunction L} {d : ℕ}
    (hχX : χ ∈ X) (hχ₀X : χ₀ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχdeg : Section1.degree χ = (d : ℂ) * Section1.degree χ₀) :
    Section1.scalarProduct L χ (Section1.subgroupRestriction L (τ₁ η₁)) =
      (d : ℂ) * Section1.scalarProduct L χ₀
        (Section1.subgroupRestriction L (τ₁ η₁)) := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot68, hT, hbranch⟩
  have hχspan : Section5.integerSpan X χ :=
    Section5.integerSpan_of_mem X hχX
  have hχ₀span : Section5.integerSpan X χ₀ :=
    Section5.integerSpan_of_mem X hχ₀X
  have hχ₀smul : Section5.integerSpan X ((d : ℂ) • χ₀) := by
    simpa using Section5.integerSpan_zsmul (S := X) (φ := χ₀) (d : ℤ) hχ₀span
  have hdiffSpan : Section5.integerSpan X (χ - (d : ℂ) • χ₀) :=
    Section5.integerSpan_sub hχspan hχ₀smul
  have hdiffDeg : Section1.degree (χ - (d : ℂ) • χ₀) = 0 := by
    rw [Section1.degree_apply] at hχdeg ⊢
    simp [Section1.degree_apply, hχdeg]
  have hdiffOnX :
      Section5.integerSpanOn X Section5.puncturedSet (χ - (d : ℂ) • χ₀) :=
    ⟨hdiffSpan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdiffDeg⟩
  have hdiffOnS :
      Section5.integerSpanOn S Section5.puncturedSet (χ - (d : ℂ) • χ₀) := by
    rcases hdiffOnX with ⟨hspan, hsupp⟩
    exact ⟨Section5.integerSpan_mono
      (theorem_6_8_familyData_X_subset_S hfamily) hspan, hsupp⟩
  have hTdiff :
      T (χ - (d : ℂ) • χ₀) =
        Section1.inducedCF L (χ - (d : ℂ) • χ₀) :=
    hT _ hdiffOnS
  have hτη₁class : Section1.IsClassFunction (τ₁ η₁) :=
    theorem_6_8_coherentExtension_mem_isClassFunction hτ₁ hη₁Y
  have hrestrict :
      Section1.scalarProduct G (T (χ - (d : ℂ) • χ₀)) (τ₁ η₁) =
        Section1.scalarProduct L (χ - (d : ℂ) • χ₀)
          (Section1.subgroupRestriction L (τ₁ η₁)) :=
    theorem_6_8_scalarProduct_transform_eq_restriction_of_induction
      hTdiff hτη₁class
  have htarget_zero :
      Section1.scalarProduct G (T (χ - (d : ℂ) • χ₀)) (τ₁ η₁) = 0 := by
    have hagree :
        τ₂ (χ - (d : ℂ) • χ₀) = T (χ - (d : ℂ) • χ₀) :=
      hτ₂.2.2 (χ - (d : ℂ) • χ₀) hdiffOnX
    rw [← hagree, map_sub, map_smul, Section5.scalarProduct_sub_left,
      Section1.scalarProduct_smul_left]
    have hχorth :
        Section1.scalarProduct G (τ₂ χ) (τ₁ η₁) = 0 :=
      theorem_6_8_transformed_X_Y_orthogonal_of_extensions
        hSbot hfamily hZcomm h52union hτ₂ hτ₁ hχX hη₁Y
    have hχ₀orth :
        Section1.scalarProduct G (τ₂ χ₀) (τ₁ η₁) = 0 :=
      theorem_6_8_transformed_X_Y_orthogonal_of_extensions
        hSbot hfamily hZcomm h52union hτ₂ hτ₁ hχ₀X hη₁Y
    simp [hχorth, hχ₀orth]
  have hsource_zero :
      Section1.scalarProduct L (χ - (d : ℂ) • χ₀)
          (Section1.subgroupRestriction L (τ₁ η₁)) = 0 := by
    rw [← hrestrict]
    exact htarget_zero
  exact theorem_6_8_scalarProduct_eq_nat_mul_base_of_left_sub_orthogonal
    hsource_zero

theorem theorem_6_8_caseA_source_X_shift_Y_diff_scalar
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    {χ η₁ η : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y)
    (hηne : η ≠ η₁) :
    Section1.scalarProduct L
      (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) (η - η₁) =
        Section1.degree χ / (Nat.card W1 : ℂ) := by
  rcases theorem_6_8_X_degree_div_cardW1
      hSbot hsemi hfamily hχX with
    ⟨a, _hχdeg, hχratio⟩
  have hχη : Section1.scalarProduct L χ η = 0 := by
    have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
    have hηU : η ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hηY)
    have hηnotX : η ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
    have hχneη : χ ≠ η := by
      intro hχeq
      exact hηnotX (by simpa [hχeq] using hχX)
    exact h52c hχU hηU hχneη
  have hχη₁ : Section1.scalarProduct L χ η₁ = 0 := by
    have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hη₁notX : η₁ ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
    have hχneη₁ : χ ≠ η₁ := by
      intro hχeq
      exact hη₁notX (by simpa [hχeq] using hχX)
    exact h52c hχU hη₁U hχneη₁
  have hη₁η : Section1.scalarProduct L η₁ η = 0 := by
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hηU : η ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hηY)
    exact h52c hη₁U hηU hηne.symm
  have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 := by
    rcases theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y with
      ⟨_n, ρ, hρirr, hη₁eq⟩
    rw [hη₁eq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hχratio' :
      Section1.degree χ / (Fintype.card W1 : ℂ) = (a : ℂ) := by
    simpa [Nat.card_eq_fintype_card] using hχratio
  rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
    Section5.scalarProduct_sub_right]
  simp [Section1.scalarProduct_smul_left, hχη, hχη₁, hη₁η, hη₁self,
    Nat.card_eq_fintype_card, hχratio']

theorem theorem_6_8_caseA_transform_X_shift_Y_diff_scalar
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ η : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y)
    (hηne : η ≠ η₁) :
    Section1.scalarProduct G
      (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
      (τ₁ η - τ₁ η₁) =
        Section1.degree χ / (Nat.card W1 : ℂ) := by
  rcases h52union with ⟨_hsetup, _R, _h52a, h52b, h52c, _h52d, _h52e⟩
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hχX hη₁Y with
    ⟨a, _hχdeg, hχratio, hχspan⟩
  have hχspan_ratio :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) := by
    have hχratio' :
        Section1.degree χ / (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hχratio
    simpa [Nat.card_eq_fintype_card, hχratio'] using hχspan
  have hdiffY :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet (η - η₁) :=
    theorem_6_8_Y_diff_eta_integerSpanOn hsemi hfamily hηY hη₁Y
  have hiso :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (T (η - η₁)) =
      Section1.scalarProduct L
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) (η - η₁) :=
    h52b.1 _ _ hχspan_ratio hdiffY
  have htarget : τ₁ η - τ₁ η₁ = T (η - η₁) := by
    calc
      τ₁ η - τ₁ η₁ = τ₁ (η - η₁) := by rw [map_sub]
      _ = T (η - η₁) :=
        hτ₁.2.2 (η - η₁)
          (theorem_6_8_Y_diff_eta_integerSpanOn_Y hsemi hfamily hηY hη₁Y)
  rw [htarget]
  calc
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (T (η - η₁)) =
      Section1.scalarProduct L
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) (η - η₁) := hiso
    _ = Section1.degree χ / (Nat.card W1 : ℂ) :=
      theorem_6_8_caseA_source_X_shift_Y_diff_scalar
        h68 hSbot hsemi hfamily hZcomm h52c hχX hη₁Y hηY hηne

theorem theorem_6_8_caseA_source_X_shift_cfNormSq_eq_one_add_nat_sq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ)) :
    Section5.cfNormSq
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
      1 + (c : ℝ) ^ (2 : ℕ) := by
  have hχη₁ : Section1.scalarProduct L χ η₁ = 0 :=
    by
      have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
      have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
      have hη₁notX : η₁ ∉ X :=
        theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
      have hχneη₁ : χ ≠ η₁ := by
        intro hχeq
        exact hη₁notX (by simpa [hχeq] using hχX)
      exact h52c hχU hη₁U hχneη₁
  have hη₁χ : Section1.scalarProduct L η₁ χ = 0 :=
    by
      have hχU : χ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hχX)
      have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
      have hη₁notX : η₁ ∉ X :=
        theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
      have hη₁neχ : η₁ ≠ χ := by
        intro hη₁eq
        exact hη₁notX (by simpa [← hη₁eq] using hχX)
      exact h52c hη₁U hχU hη₁neχ
  have hχ_norm : Section5.cfNormSq χ = 1 := by
    have hχself : Section1.scalarProduct L χ χ = 1 := by
      rcases hχirr with ⟨_n, ρ, hρirr, hχeq⟩
      rw [hχeq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
    unfold Section5.cfNormSq
    rw [hχself]
    simp
  have hη₁_norm : Section5.cfNormSq η₁ = 1 :=
    theorem_6_8_mem_Y_cfNormSq_eq_one h68 hfamily hη₁Y
  have hright :
      Section1.scalarProduct L χ ((c : ℂ) • η₁) = 0 := by
    rw [Section1.scalarProduct_smul_right, hχη₁]
    simp
  have hleft :
      Section1.scalarProduct L ((c : ℂ) • η₁) χ = 0 := by
    rw [Section1.scalarProduct_smul_left, hη₁χ]
    simp
  have hnorm_c :
      Section5.cfNormSq (χ - (c : ℂ) • η₁) =
        1 + (c : ℝ) ^ (2 : ℕ) := by
    rw [Section5.cfNormSq_sub_eq_add_of_orthogonal hright hleft,
      hχ_norm, Section5.cfNormSq_smul, hη₁_norm]
    norm_num [Complex.normSq]
    ring
  have hχratioF :
      Section1.degree χ / (Fintype.card W1 : ℂ) = (c : ℂ) := by
    simpa [Nat.card_eq_fintype_card] using hχratio
  simpa [Nat.card_eq_fintype_card, hχratioF] using hnorm_c

theorem theorem_6_8_caseA_transform_X_shift_cfNormSq_eq_one_add_nat_sq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ)) :
    Section5.cfNormSq
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)) =
      1 + (c : ℝ) ^ (2 : ℕ) := by
  rcases h52union with ⟨_hsetup, _R, _h52a, h52b, h52c, _h52d, _h52e⟩
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hχX hη₁Y with
    ⟨a, _hχdeg, hχratio_a, hχspan⟩
  have hχspan_ratio :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) := by
    have hχratio_a' :
        Section1.degree χ / (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hχratio_a
    simpa [Nat.card_eq_fintype_card, hχratio_a'] using hχspan
  have hiso :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)) =
      Section1.scalarProduct L
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) :=
    h52b.1 _ _ hχspan_ratio hχspan_ratio
  unfold Section5.cfNormSq
  rw [hiso]
  exact theorem_6_8_caseA_source_X_shift_cfNormSq_eq_one_add_nat_sq
    h68 hfamily hZcomm h52c hχirr hχX hη₁Y hχratio

theorem theorem_6_8_caseA_anchor_quadratic_bound_of_nat_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ))
    (hc : 1 < c)
    (hanchor_multiple :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (c : ℂ) * ((k : ℤ) : ℂ)) :
    ∃ x : ℤ,
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
          (c : ℂ) * ((x - 1 : ℤ) : ℂ) ∧
      ((x - 1) ^ (2 : ℕ) +
          ((Y.card - 1 : ℕ) : ℤ) * x ^ (2 : ℕ) : ℤ) ≤ 1 := by
  rcases hanchor_multiple with ⟨k, hk⟩
  let x : ℤ := k + 1
  have hanchor :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
          (c : ℂ) * ((x - 1 : ℤ) : ℂ) := by
    have hxcast : ((x - 1 : ℤ) : ℂ) = (k : ℂ) := by
      dsimp [x]
      norm_num
    rw [hk, hxcast]
  have hdiff : ∀ η : Section1.ClassFunction L, η ∈ Y → η ≠ η₁ →
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η - τ₁ η₁) = (c : ℂ) := by
    intro η hηY hηne
    rw [← hχratio]
    exact theorem_6_8_caseA_transform_X_shift_Y_diff_scalar
      h68 hSbot hsemi hfamily hZcomm h52union hτ₁
      hχX hη₁Y hηY hηne
  have hnorm_eq :
      Section5.cfNormSq
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)) =
        1 + (c : ℝ) ^ (2 : ℕ) :=
    theorem_6_8_caseA_transform_X_shift_cfNormSq_eq_one_add_nat_sq
      h68 hSbot hsemi hfamily hZcomm h52union hχirr hχX hη₁Y hχratio
  have hnorm_le :
      Section5.cfNormSq
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)) ≤
        1 + (c : ℝ) ^ (2 : ℕ) := by
    rw [hnorm_eq]
  refine ⟨x, hanchor, ?_⟩
  exact theorem_6_8_anchor_quadratic_bound_of_nat_coefficients_and_norm
    h68 hfamily hτ₁ hc hη₁Y hanchor hdiff hnorm_le

theorem theorem_6_8_caseA_anchor_dichotomy_of_nat_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ))
    (hc : 1 < c)
    (hanchor_multiple :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (c : ℂ) * ((k : ℤ) : ℂ)) :
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • τ₁ η₁)
        (τ₁ η₁) = 0 ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          Section1.scalarProduct G
            (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
              (c : ℂ) • (-τ₁ η₂))
            (τ₁ η₁) = 0 := by
  classical
  rcases theorem_6_8_caseA_anchor_quadratic_bound_of_nat_multiple
      h68 hSbot hsemi hfamily hZcomm h52union hτ₁
      hχirr hχX hη₁Y hχratio hc hanchor_multiple with
    ⟨x, hxcoef, hxquad⟩
  have hYcard_gt : 1 < Y.card :=
    theorem_6_8_Y_card_gt_one_of_familyData h68 hfamily
  have hxsplit : x = 0 ∨ x = 1 ∧ Y.card = 2 :=
    theorem_6_8_anchor_integer_dichotomy_of_quadratic_bound
      hYcard_gt hxquad
  have hη₁self_src : Section1.scalarProduct L η₁ η₁ = 1 := by
    rcases theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y with
      ⟨_n, ρ, hρirr, hη₁eq⟩
    rw [hη₁eq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hτη₁self : Section1.scalarProduct G (τ₁ η₁) (τ₁ η₁) = 1 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
      hτ₁ hη₁Y hη₁Y, hη₁self_src]
  rcases hxsplit with hx0 | hx1
  · left
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hxcoef, hτη₁self, hx0]
    norm_num
  · right
    rcases hx1 with ⟨hxone, hcard⟩
    rcases Finset.one_lt_card.mp hYcard_gt with
      ⟨ηa, hηaY, ηb, hηbY, hηab⟩
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ :
        ∃ η₂ : Section1.ClassFunction L, η₂ ∈ Y ∧ η₂ ≠ η₁ := by
      by_cases hηa : ηa = η₁
      · refine ⟨ηb, hηbY, ?_⟩
        intro hηb
        exact hηab (by rw [hηa, hηb])
      · exact ⟨ηa, hηaY, hηa⟩
    have hη₂η₁_src : Section1.scalarProduct L η₂ η₁ = 0 := by
      have hη₂irr : Section1.IsIrreducibleCharacterOnGroup η₂ :=
        theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₂ hη₂Y
      have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
        theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
      rcases hη₂irr with ⟨n₂, ρ₂, hρ₂, hη₂eq⟩
      rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        η₂ η₁ ρ₂ ρ₁ hη₂eq hη₁eq hρ₂ hρ₁ hη₂ne
    have hτη₂η₁ : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₁) = 0 := by
      rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
        hτ₁ hη₂Y hη₁Y, hη₂η₁_src]
    have hnegτη₂η₁ :
        Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₁) = 0 := by
      rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
        hτη₂η₁]
      simp
    refine ⟨η₂, hcard, hη₂Y, hη₂ne, ?_⟩
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hxcoef, hnegτη₂η₁, hxone]
    norm_num

theorem theorem_6_8_caseA_left_candidate_scalarProduct_Y_eq_anchor
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ η : Section1.ClassFunction L} {c : ℕ}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y) (hηY : η ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ)) :
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • τ₁ η₁)
        (τ₁ η) =
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • τ₁ η₁)
        (τ₁ η₁) := by
  by_cases hηne : η ≠ η₁
  · have hdiff :
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η - τ₁ η₁) = (c : ℂ) := by
      rw [← hχratio]
      exact theorem_6_8_caseA_transform_X_shift_Y_diff_scalar
        h68 hSbot hsemi hfamily hZcomm h52union hτ₁
        hχX hη₁Y hηY hηne
    have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
      theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
    have hηirr : Section1.IsIrreducibleCharacterOnGroup η :=
      theorem_6_8_Y_irreducible_of_familyData h68 hfamily η hηY
    have hη₁η : Section1.scalarProduct L η₁ η = 0 := by
      rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
      rcases hηirr with ⟨n, ρ, hρ, hηeq⟩
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        η₁ η ρ₁ ρ hη₁eq hηeq hρ₁ hρ hηne.symm
    have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 := by
      rcases hη₁irr with ⟨_n, ρ, hρirr, hη₁eq⟩
      rw [hη₁eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
    have hτ₁η₁η : Section1.scalarProduct G (τ₁ η₁) (τ₁ η) = 0 := by
      rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
        hτ₁ hη₁Y hηY, hη₁η]
    have hτ₁η₁self : Section1.scalarProduct G (τ₁ η₁) (τ₁ η₁) = 1 := by
      rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
        hτ₁ hη₁Y hη₁Y, hη₁self]
    have hτ₁diff :
        Section1.scalarProduct G (τ₁ η₁) (τ₁ η - τ₁ η₁) = -1 := by
      rw [Section5.scalarProduct_sub_right, hτ₁η₁η, hτ₁η₁self]
      norm_num
    have hdiff0 :
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
            (c : ℂ) • τ₁ η₁)
          (τ₁ η - τ₁ η₁) = 0 := by
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
        hdiff, hτ₁diff]
      ring
    rw [Section5.scalarProduct_sub_right] at hdiff0
    exact sub_eq_zero.mp hdiff0
  · have hηeq : η = η₁ := not_not.mp hηne
    simp [hηeq]

theorem theorem_6_8_caseA_left_candidate_orthogonal_of_anchor_zero
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ))
    (hanchor :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • τ₁ η₁)
        (τ₁ η₁) = 0) :
    orthogonalToTransformedFinset Y τ₁
      (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
        (c : ℂ) • τ₁ η₁) := by
  intro η hηY
  rw [theorem_6_8_caseA_left_candidate_scalarProduct_Y_eq_anchor
    h68 hSbot hsemi hfamily hZcomm h52union hτ₁
    hχX hη₁Y hηY hχratio, hanchor]

theorem theorem_6_8_caseA_right_candidate_scalarProduct_Y_eq_anchor
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ η₂ η : Section1.ClassFunction L} {c : ℕ}
    (hχX : χ ∈ X)
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    (hηY : η ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ)) :
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • (-τ₁ η₂))
        (τ₁ η) =
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • (-τ₁ η₂))
        (τ₁ η₁) := by
  have hη₂irr : Section1.IsIrreducibleCharacterOnGroup η₂ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₂ hη₂Y
  have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hη₁Y
  have hη₂η₁ : Section1.scalarProduct L η₂ η₁ = 0 := by
    rcases hη₂irr with ⟨n₂, ρ₂, hρ₂, hη₂eq⟩
    rcases hη₁irr with ⟨n₁, ρ₁, hρ₁, hη₁eq⟩
    exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      η₂ η₁ ρ₂ ρ₁ hη₂eq hη₁eq hρ₂ hρ₁ hη₂ne
  have hη₂self : Section1.scalarProduct L η₂ η₂ = 1 := by
    rcases hη₂irr with ⟨_n, ρ, hρirr, hη₂eq⟩
    rw [hη₂eq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  have hτ₂η₁ : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₁) = 0 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
      hτ₁ hη₂Y hη₁Y, hη₂η₁]
  have hτ₂self : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) = 1 := by
    rw [theorem_6_8_coherentExtension_scalarProduct_of_mem
      hτ₁ hη₂Y hη₂Y, hη₂self]
  have hnegη₁ : Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₁) = 0 := by
    rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
      hτ₂η₁]
    simp
  have hnegη₂ : Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₂) = -1 := by
    rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left,
      hτ₂self]
    norm_num
  have hcases : η = η₁ ∨ η = η₂ := by
    classical
    let pair : Finset (Section1.ClassFunction L) := {η₁, η₂}
    have hpair_subset : pair ⊆ Y := by
      intro ξ hξ
      simp [pair] at hξ
      rcases hξ with rfl | rfl
      · exact hη₁Y
      · exact hη₂Y
    have hpair_card : pair.card = 2 := by
      have hη₁ne : η₁ ≠ η₂ := hη₂ne.symm
      simp [pair, hη₁ne]
    have hpair_eq : pair = Y := by
      apply Finset.eq_of_subset_of_card_le hpair_subset
      simp [hpair_card, hcard]
    have hηpair : η ∈ pair := by
      simpa [hpair_eq] using hηY
    simpa [pair] using hηpair
  rcases hcases with hηeq | hηeq
  · subst η
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hnegη₁]
  · subst η
    have hdiff :
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₂ - τ₁ η₁) = (c : ℂ) := by
      rw [← hχratio]
      exact theorem_6_8_caseA_transform_X_shift_Y_diff_scalar
        h68 hSbot hsemi hfamily hZcomm h52union hτ₁
        hχX hη₁Y hη₂Y hη₂ne
    have hAdiff :
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₂) -
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (c : ℂ) := by
      simpa [Section5.scalarProduct_sub_right] using hdiff
    set A2 : ℂ :=
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₂)
    set A1 : ℂ :=
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁)
    have hAdiff' : A2 - A1 = (c : ℂ) := by
      simpa [A2, A1] using hAdiff
    have hAeq : A2 - (c : ℂ) = A1 := by
      rw [← hAdiff']
      ring
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left,
      hnegη₂, hnegη₁]
    change A2 + (c : ℂ) * (-1) = A1 + (c : ℂ) * 0
    calc
      A2 + (c : ℂ) * (-1) = A2 - (c : ℂ) := by ring
      _ = A1 := hAeq
      _ = A1 + (c : ℂ) * 0 := by ring

theorem theorem_6_8_caseA_right_candidate_orthogonal_of_anchor_zero
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ η₂ : Section1.ClassFunction L} {c : ℕ}
    (hχX : χ ∈ X)
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ))
    (hanchor :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
          (c : ℂ) • (-τ₁ η₂))
        (τ₁ η₁) = 0) :
    orthogonalToTransformedFinset Y τ₁
      (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) +
        (c : ℂ) • (-τ₁ η₂)) := by
  intro η hηY
  rw [theorem_6_8_caseA_right_candidate_scalarProduct_Y_eq_anchor
    h68 hSbot hsemi hfamily hZcomm h52union hτ₁
    hχX hcard hη₁Y hη₂Y hη₂ne hηY hχratio, hanchor]

theorem theorem_6_8_caseA_anchor_multiple_of_source_coeff_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L}
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hsource_multiple :
      ∃ k : ℤ,
        Section1.scalarProduct L χ
          (Section1.subgroupRestriction L (τ₁ η₁)) =
            (Section1.degree χ / (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ)) :
    ∃ k : ℤ,
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
          (Section1.degree χ / (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ) := by
  rcases h68 with ⟨hsemi68, hodd, hHne, hnil, hTI, hSbot68, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi68, hodd, hHne, hnil, hTI, hSbot68, hT, hbranch⟩
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hχX hη₁Y with
    ⟨a, _hχdeg, hχratio, hspan⟩
  have hχratioF :
      Section1.degree χ / (Fintype.card W1 : ℂ) = (a : ℂ) := by
    simpa [Nat.card_eq_fintype_card] using hχratio
  have hspan_ratio_union :
      Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) := by
    simpa [Nat.card_eq_fintype_card, hχratioF] using hspan
  have hsubUS : X ∪ Y ⊆ S := by
    intro φ hφ
    rcases Finset.mem_union.mp hφ with hφX | hφY
    · exact theorem_6_8_familyData_X_subset_S hfamily hφX
    · exact theorem_6_8_familyData_Y_subset_S hSbot hfamily hφY
  have hspan_ratio_S :
      Section5.integerSpanOn S Section5.puncturedSet
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) := by
    rcases hspan_ratio_union with ⟨hspanInt, hsupp⟩
    exact ⟨Section5.integerSpan_mono hsubUS hspanInt, hsupp⟩
  have hTα :
      T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
        Section1.inducedCF L
          (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) :=
    hT _ hspan_ratio_S
  have hτη₁class : Section1.IsClassFunction (τ₁ η₁) :=
    theorem_6_8_coherentExtension_mem_isClassFunction hτ₁ hη₁Y
  have hanchor_restrict :
      Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
      Section1.scalarProduct L
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)
        (Section1.subgroupRestriction L (τ₁ η₁)) :=
    theorem_6_8_scalarProduct_transform_eq_restriction_of_induction
      hTα hτη₁class
  have hη₁virt : Theory.Character.IsVirtualCharacter η₁ :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (theorem_6_8_Y_irreducible_of_familyData h68' hfamily η₁ hη₁Y)
  have hτη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
    hτ₁.2.1 η₁ (Section5.integerSpan_of_mem Y hη₁Y)
  have hresvirt :
      Theory.Character.IsVirtualCharacter
        (Section1.subgroupRestriction L (τ₁ η₁)) :=
    theorem_6_8_subgroupRestriction_isVirtualCharacter L hτη₁virt
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hη₁virt hresvirt with
    ⟨m, hm⟩
  rcases hsource_multiple with ⟨k, hk⟩
  refine ⟨k - m, ?_⟩
  calc
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
      Section1.scalarProduct L
        (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)
        (Section1.subgroupRestriction L (τ₁ η₁)) := hanchor_restrict
    _ =
      Section1.scalarProduct L χ (Section1.subgroupRestriction L (τ₁ η₁)) -
        (Section1.degree χ / (Nat.card W1 : ℂ)) *
          Section1.scalarProduct L η₁
            (Section1.subgroupRestriction L (τ₁ η₁)) := by
          rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left]
    _ = (Section1.degree χ / (Nat.card W1 : ℂ)) * ((k - m : ℤ) : ℂ) := by
          have hkm : ((k - m : ℤ) : ℂ) = (k : ℂ) - (m : ℂ) := by
            norm_num
          rw [hk, hm]
          rw [hkm]
          ring

theorem theorem_6_8_caseA_base_shift_data_of_nat_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L} {c : ℕ}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hχratio : Section1.degree χ / (Nat.card W1 : ℂ) = (c : ℂ))
    (hc : 1 < c)
    (hanchor_multiple :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (c : ℂ) * ((k : ℤ) : ℂ)) :
    (∃ X₁ : Section1.ClassFunction G,
      orthogonalToTransformedFinset Y τ₁ X₁ ∧
        T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (c : ℂ) • τ₁ η₁) ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∃ X₁ : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X₁ ∧
              T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
                X₁ - (c : ℂ) • (-τ₁ η₂) := by
  rcases theorem_6_8_caseA_anchor_dichotomy_of_nat_multiple
      h68 hSbot hsemi hfamily hZcomm h52union hτ₁
      hχirr hχX hη₁Y hχratio hc hanchor_multiple with
    hleft | hright
  · left
    exact theorem_6_8_decomposition_of_orthogonal_add_smul
      (Y := Y) (τ₁ := τ₁)
      (A := T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
      (Ycf := τ₁ η₁) (c := (c : ℂ))
      (theorem_6_8_caseA_left_candidate_orthogonal_of_anchor_zero
        h68 hSbot hsemi hfamily hZcomm h52union hτ₁
        hχX hη₁Y hχratio hleft)
  · right
    rcases hright with ⟨η₂, hcard, hη₂Y, hη₂ne, hanchor⟩
    refine ⟨η₂, hcard, hη₂Y, hη₂ne, ?_⟩
    exact theorem_6_8_decomposition_of_orthogonal_add_smul
      (Y := Y) (τ₁ := τ₁)
      (A := T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
      (Ycf := -τ₁ η₂) (c := (c : ℂ))
      (theorem_6_8_caseA_right_candidate_orthogonal_of_anchor_zero
        h68 hSbot hsemi hfamily hZcomm h52union hτ₁
        hχX hcard hη₁Y hη₂Y hη₂ne hχratio hanchor)

theorem theorem_6_8_caseA_base_shift_data_of_anchor_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {χ η₁ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχX : χ ∈ X) (hη₁Y : η₁ ∈ Y)
    (hanchor_multiple :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (Section1.degree χ / (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ)) :
    (∃ X₁ : Section1.ClassFunction G,
      orthogonalToTransformedFinset Y τ₁ X₁ ∧
        T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (Section1.degree χ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∃ X₁ : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X₁ ∧
              T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
                X₁ - (Section1.degree χ / (Nat.card W1 : ℂ)) • (-τ₁ η₂) := by
  rcases theorem_6_8_X_degree_div_cardW1 hSbot hsemi hfamily hχX with
    ⟨c, _hχdeg, hχratio⟩
  have hc : 1 < c :=
    theorem_6_8_X_degree_ratio_gt_one hSbot hsemi hfamily hZcomm hχX hχratio
  have hanchor_c :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (c : ℂ) * ((k : ℤ) : ℂ) := by
    rcases hanchor_multiple with ⟨k, hk⟩
    refine ⟨k, hk.trans ?_⟩
    rw [hχratio]
  rcases theorem_6_8_caseA_base_shift_data_of_nat_multiple
      h68 hSbot hsemi hfamily hZcomm h52union hτ₁
      hχirr hχX hη₁Y hχratio hc hanchor_c with hleft | hright
  · left
    rcases hleft with ⟨X₁, horth, hEq⟩
    refine ⟨X₁, horth, ?_⟩
    calc
      T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (c : ℂ) • τ₁ η₁ := hEq
      _ = X₁ - (Section1.degree χ / (Nat.card W1 : ℂ)) • τ₁ η₁ := by
          rw [hχratio]
  · right
    rcases hright with ⟨η₂, hcard, hη₂Y, hη₂ne, X₁, horth, hEq⟩
    refine ⟨η₂, hcard, hη₂Y, hη₂ne, X₁, horth, ?_⟩
    calc
      T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (c : ℂ) • (-τ₁ η₂) := hEq
      _ = X₁ - (Section1.degree χ / (Nat.card W1 : ℂ)) • (-τ₁ η₂) := by
          rw [hχratio]

theorem theorem_6_8_caseB_orthogonal_commonY_right
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf X₁ : Section1.ClassFunction G}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (horthX : orthogonalToTransformedFinset Y τ₁ X₁) :
    Section1.scalarProduct G X₁ Ycf = 0 := by
  rcases hcommon with ⟨hη₁Y, hYcf, _hphi⟩
  rcases hYcf with hYcf | hYcf
  · simpa [hYcf] using horthX η₁ hη₁Y
  · rcases hYcf with ⟨η₂, _hcard, hη₂Y, _hη₂ne, hYcf⟩
    rw [hYcf]
    have hneg :
        Section1.scalarProduct G X₁ (-τ₁ η₂) =
          -Section1.scalarProduct G X₁ (τ₁ η₂) := by
      simp [Section1.scalarProduct, Finset.sum_neg_distrib]
    rw [hneg, horthX η₂ hη₂Y]
    simp

theorem theorem_6_8_caseB_orthogonal_commonY_left
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf X₁ : Section1.ClassFunction G}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (horthX : orthogonalToTransformedFinset Y τ₁ X₁) :
    Section1.scalarProduct G Ycf X₁ = 0 := by
  have hright :
      Section1.scalarProduct G X₁ Ycf = 0 :=
    theorem_6_8_caseB_orthogonal_commonY_right hcommon horthX
  simpa [Section1.scalarProduct_star_swap] using congrArg star hright

theorem theorem_6_8_caseB_unionImage_X_Y_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) = 0 := by
  have hη₁Y : η₁ ∈ Y := hcommon.1
  have hχorth :
      orthogonalToTransformedFinset Y τ₁
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ) :=
    (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      χ hχX hχnotY).1
  have hYcf0 :
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ) Ycf = 0 :=
    theorem_6_8_caseB_orthogonal_commonY_right hcommon hχorth
  rw [theorem_6_8_caseB_unionImage_of_mem_Y
    (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY]
  rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right]
  simp [hχorth (η : Section1.ClassFunction L) hηY, hχorth η₁ hη₁Y,
    hYcf0]

theorem theorem_6_8_caseB_unionImage_Y_X_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ) = 0 := by
  have hright :
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ)
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) = 0 :=
    theorem_6_8_caseB_unionImage_X_Y_orthogonal
      (W1 := W1) hcommon χ η hχX hχnotY hηY
  simpa [Section1.scalarProduct_star_swap] using congrArg star hright

theorem theorem_6_8_caseB_unionImage_X_Y_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) =
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (η : Section1.ClassFunction L) := by
  rw [theorem_6_8_caseB_unionImage_X_Y_orthogonal
    (W1 := W1) hcommon χ η hχX hχnotY hηY]
  have hsrc :
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (η : Section1.ClassFunction L) = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hηU : (η : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inr hηY)
    have hηnotX : (η : Section1.ClassFunction L) ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
    have hχneη :
        (χ : Section1.ClassFunction L) ≠ (η : Section1.ClassFunction L) := by
      intro hχeq
      exact hηnotX (by simpa [hχeq] using hχX)
    exact h52c hχU hηU hχneη
  rw [hsrc]

theorem theorem_6_8_caseB_unionImage_Y_X_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ) =
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (χ : Section1.ClassFunction L) := by
  rw [theorem_6_8_caseB_unionImage_Y_X_orthogonal
    (W1 := W1) hcommon χ η hχX hχnotY hηY]
  have hsrc :
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (χ : Section1.ClassFunction L) = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hηU : (η : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inr hηY)
    have hηnotX : (η : Section1.ClassFunction L) ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
    have hηneχ :
        (η : Section1.ClassFunction L) ≠ (χ : Section1.ClassFunction L) := by
      intro hηeq
      exact hηnotX (by simpa [← hηeq] using hχX)
    exact h52c hηU hχU hηneχ
  rw [hsrc]

theorem theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Y : Finset (Section1.ClassFunction L)}
    {η₁ η₂ η : Section1.ClassFunction L}
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    (hηY : η ∈ Y) :
    η = η₁ ∨ η = η₂ := by
  classical
  let pair : Finset (Section1.ClassFunction L) := {η₁, η₂}
  have hpair_subset : pair ⊆ Y := by
    intro χ hχ
    simp [pair] at hχ
    rcases hχ with rfl | rfl
    · exact hη₁Y
    · exact hη₂Y
  have hpair_card : pair.card = 2 := by
    have hη₁ne : η₁ ≠ η₂ := hη₂ne.symm
    simp [pair, hη₁ne]
  have hpair_eq : pair = Y := by
    apply Finset.eq_of_subset_of_card_le hpair_subset
    simp [hpair_card, hcard]
  have hηpair : η ∈ pair := by
    simpa [hpair_eq] using hηY
  simpa [pair] using hηpair

theorem theorem_6_8_caseB_other_eq_conjugate_of_card_two
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    {η₁ η₂ : Section1.ClassFunction L}
    (hcard : Y.card = 2)
    (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁) :
    η₂ = Section1.conjugateCharacter η₁ := by
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have hbarY : Section1.conjugateCharacter η₁ ∈ Y :=
    inducedKernelFamily_conjugate_mem hY hη₁Y
  have hη₁nebar : η₁ ≠ Section1.conjugateCharacter η₁ :=
    (h52a ⟨η₁, Finset.mem_union.mpr (Or.inr hη₁Y)⟩).2
  have hcases := theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
    (Y := Y) (η₁ := η₁) (η₂ := Section1.conjugateCharacter η₁)
    hcard hη₁Y hbarY hη₁nebar.symm hη₂Y
  rcases hcases with hη₂eq | hη₂eq
  · exact (hη₂ne hη₂eq).elim
  · exact hη₂eq

theorem theorem_6_8_scalarProduct_conjugateCharacter_self
    {L : Type u} [Group L] [Finite L]
    (χ : Section1.ClassFunction L) :
    Section1.scalarProduct L (Section1.conjugateCharacter χ)
      (Section1.conjugateCharacter χ) =
    Section1.scalarProduct L χ χ := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter, mul_comm]

theorem theorem_6_8_scalarProduct_neg_neg
    {G : Type u} [Group G] [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (-φ) (-ψ) = Section1.scalarProduct G φ ψ := by
  have hnegφ : -φ = (-1 : ℂ) • φ := by
    ext g
    simp
  have hnegψ : -ψ = (-1 : ℂ) • ψ := by
    ext g
    simp
  rw [hnegφ, hnegψ]
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
  simp

theorem theorem_6_8_caseB_commonY_self_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    Section1.scalarProduct G Ycf Ycf =
      Section1.scalarProduct L η₁ η₁ := by
  rcases hτ₁ with ⟨hIso, _hvirt, _hagree⟩
  rcases hcommon with ⟨hη₁Y, hYcf, _hphi⟩
  rcases hYcf with hYcf | hYcf
  · simpa [hYcf] using
      Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₁Y
  · rcases hYcf with ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩
    have hη₂eq : η₂ = Section1.conjugateCharacter η₁ :=
      theorem_6_8_caseB_other_eq_conjugate_of_card_two
        hfamily h52a hcard hη₁Y hη₂Y hη₂ne
    have hIsoη₂ :
        Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) =
          Section1.scalarProduct L η₂ η₂ :=
      Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₂Y hη₂Y
    calc
      Section1.scalarProduct G Ycf Ycf =
          Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) := by
            rw [hYcf, theorem_6_8_scalarProduct_neg_neg]
      _ = Section1.scalarProduct L η₂ η₂ := hIsoη₂
      _ = Section1.scalarProduct L η₁ η₁ := by
            simpa [hη₂eq] using
              theorem_6_8_scalarProduct_conjugateCharacter_self η₁


theorem theorem_6_8_caseB_commonY_self_eq_one
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    Section1.scalarProduct G Ycf Ycf = 1 := by
  have : H.Normal := theorem_6_8_left_normal_of_semidirect_top h68.1
  have hself :
      Section1.scalarProduct G Ycf Ycf =
        Section1.scalarProduct L η₁ η₁ :=
    theorem_6_8_caseB_commonY_self_gram hfamily h52a hτ₁ hcommon
  have hη₁irr : Section1.IsIrreducibleCharacterOnGroup η₁ :=
    theorem_6_8_Y_irreducible_of_familyData h68 hfamily η₁ hcommon.1
  have hη₁self : Section1.scalarProduct L η₁ η₁ = 1 := by
    rcases hη₁irr with ⟨_n, ρ, hρirr, hη₁eq⟩
    rw [hη₁eq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
  rw [hself, hη₁self]

theorem theorem_6_8_caseB_unionImage_Y_Y_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (η ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηY : (η : Section1.ClassFunction L) ∈ Y)
    (hξY : (ξ : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift ξ) =
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G := fun ζ =>
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift ζ
  change Section1.scalarProduct G (img η) (img ξ) =
    Section1.scalarProduct L (η : Section1.ClassFunction L)
      (ξ : Section1.ClassFunction L)
  rcases hτ₁ with ⟨hIso, hvirt, hagree⟩
  have hτ₁' : coherentExtension Y T τ₁ := ⟨hIso, hvirt, hagree⟩
  rcases hcommon with ⟨hη₁Y, hYcf, hphi⟩
  rcases hYcf with hYcf | hYcf
  · have himgη : img η = τ₁ (η : Section1.ClassFunction L) := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    have himgξ : img ξ = τ₁ (ξ : Section1.ClassFunction L) := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) ξ hξY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    rw [himgη, himgξ]
    exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hηY hξY
  · rcases hYcf with ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩
    have hη₂conj : η₂ = Section1.conjugateCharacter η₁ :=
      theorem_6_8_caseB_other_eq_conjugate_of_card_two
        hfamily h52a hcard hη₁Y hη₂Y hη₂ne
    have hcommon' : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf :=
      ⟨hη₁Y, Or.inr ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩, hphi⟩
    have hselfYcf : Section1.scalarProduct G Ycf Ycf =
        Section1.scalarProduct L η₁ η₁ :=
      theorem_6_8_caseB_commonY_self_gram hfamily h52a hτ₁' hcommon'
    have hsrc_self : Section1.scalarProduct L η₂ η₂ =
        Section1.scalarProduct L η₁ η₁ := by
      rw [hη₂conj, theorem_6_8_scalarProduct_conjugateCharacter_self]
    have hηcases := theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
      (Y := Y) (η₁ := η₁) (η₂ := η₂)
      hcard hη₁Y hη₂Y hη₂ne hηY
    have hξcases := theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
      (Y := Y) (η₁ := η₁) (η₂ := η₂)
      hcard hη₁Y hη₂Y hη₂ne hξY
    have himgη_formula : img η =
        τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ - τ₁ η₂ := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    have himgξ_formula : img ξ =
        τ₁ (ξ : Section1.ClassFunction L) - τ₁ η₁ - τ₁ η₂ := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) ξ hξY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    rcases hηcases with hηeq | hηeq <;> rcases hξcases with hξeq | hξeq
    · have himgη : img η = Ycf := by
        rw [himgη_formula, hηeq, hYcf]
        ext g
        simp [sub_eq_add_neg]
      have himgξ : img ξ = Ycf := by
        rw [himgξ_formula, hξeq, hYcf]
        ext g
        simp [sub_eq_add_neg]
      rw [himgη, himgξ, hηeq, hξeq]
      exact hselfYcf
    · have himgη : img η = -τ₁ η₂ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg]
      have himgξ : img ξ = -τ₁ η₁ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg]
      have htarget : Section1.scalarProduct G (img η) (img ξ) =
          Section1.scalarProduct L η₂ η₁ := by
        rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg]
        exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₂Y hη₁Y
      have hsrc21 : Section1.scalarProduct L η₂ η₁ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₂Y))
          (Finset.mem_union.mpr (Or.inr hη₁Y)) hη₂ne
      have hsrc12 : Section1.scalarProduct L η₁ η₂ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₁Y))
          (Finset.mem_union.mpr (Or.inr hη₂Y)) hη₂ne.symm
      rw [htarget, hηeq, hξeq, hsrc21, hsrc12]
    · have himgη : img η = -τ₁ η₁ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      have himgξ : img ξ = -τ₁ η₂ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg]
      have htarget : Section1.scalarProduct G (img η) (img ξ) =
          Section1.scalarProduct L η₁ η₂ := by
        rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg]
        exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₂Y
      have hsrc12 : Section1.scalarProduct L η₁ η₂ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₁Y))
          (Finset.mem_union.mpr (Or.inr hη₂Y)) hη₂ne.symm
      have hsrc21 : Section1.scalarProduct L η₂ η₁ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₂Y))
          (Finset.mem_union.mpr (Or.inr hη₁Y)) hη₂ne
      rw [htarget, hηeq, hξeq, hsrc12, hsrc21]
    · have himgη : img η = -τ₁ η₁ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      have himgξ : img ξ = -τ₁ η₁ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg, hηeq, hξeq]
      rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₁Y]
      rw [hsrc_self]

theorem theorem_6_8_caseB_commonY_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    Theory.Character.IsVirtualCharacter Ycf := by
  rcases hcommon with ⟨hη₁Y, hYcf, _hphi⟩
  rcases hτ₁ with ⟨_hIso, hvirt, _hagree⟩
  rcases hYcf with hYcf | hYcf
  · have hη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
      hvirt η₁ (Section5.integerSpan_of_mem Y hη₁Y)
    simpa [hYcf] using hη₁virt
  · rcases hYcf with ⟨η₂, _hcard, hη₂Y, _hη₂ne, hYcf⟩
    have hη₂virt : Theory.Character.IsVirtualCharacter (τ₁ η₂) :=
      hvirt η₂ (Section5.integerSpan_of_mem Y hη₂Y)
    simpa [hYcf] using Section3.isVirtualCharacter_neg hη₂virt

theorem theorem_6_8_selected_shift_scalar_eq_of_projection_int_coefficients
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (R : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} →
      Finset (Section1.ClassFunction G))
    (hsetup : Section5.hypothesis_5_2_setup_statement (X ∪ Y))
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52b : Section5.hypothesis_5_2_b_statement (X ∪ Y) T)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (h52d : Section5.hypothesis_5_2_d_statement (X ∪ Y) T R)
    (h52e : Section5.hypothesis_5_2_e_statement (X ∪ Y) R)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y)
    {Ycf : Section1.ClassFunction G}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    {φ : Section1.ClassFunction Z}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hφne : φ ≠ Section1.principalCharacter Z)
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (ψ : ι → Section1.ClassFunction H) (i0 : ι)
    (hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i))
    (horth : ∀ i j : ι,
      Section1.scalarProduct H (ψ i) (ψ j) = if i = j then 1 else 0)
    (hdegree : ∀ i, e i ≠ 0 → Section1.degree (ψ i) = (e i : ℂ))
    (hdecomp :
      Section1.inducedCF (Z.subgroupOf H) (Section1.subgroupOfClassFunction φ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ)
    (hsq : (letI : Fintype ι := Fintype.ofFinite ι
      (∑ i : ι, (e i : ℂ) * (e i : ℂ)) = (Z.relIndex H : ℂ)))
    (hei0 : e i0 ≠ 0) :
    ∀ η : Section1.ClassFunction L, η ∈ Y →
      Section1.scalarProduct G
          (T (Section1.inducedCF H (ψ i0) - (e i0 : ℂ) • η₁)) (τ₁ η) =
        -(e i0 : ℂ) * Section1.scalarProduct G Ycf (τ₁ η) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hZcomm : Z ≤ ⁅H,H⁆ := by
    rcases hB with ⟨_hW2ne, _hW2center, hW2comm, hZeq⟩
    rw [hZeq]
    exact hW2comm
  have hshift :
      Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁ =
        Section1.weightedFamilySum (fun i => (e i : ℂ))
          (fun i => Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) :=
    theorem_6_8_induced_shift_eq_weighted_alpha_of_decomposition
      hfamily.1 e ψ hdecomp hsq
  have hYself : Section1.scalarProduct G Ycf Ycf = 1 :=
    theorem_6_8_caseB_commonY_self_eq_one h68' hfamily h52a hτ₁ hcommon
  have hYcfvirt : Theory.Character.IsVirtualCharacter Ycf :=
    theorem_6_8_caseB_commonY_virtual
      (T := T) (τ₁ := τ₁) hτ₁ hcommon
  have hproj :
      ∀ i : ι, e i ≠ 0 →
        ∃ Yrem : Section1.ClassFunction G, ∃ b : ℤ,
          b ≤ (e i : ℤ) ∧
            Section1.scalarProduct G Yrem Ycf = (b : ℂ) ∧
              (∀ η : Section1.ClassFunction L, η ∈ Y →
                Section1.scalarProduct G
                    (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η) =
                  -Section1.scalarProduct G Yrem (τ₁ η)) ∧
                Section5.cfNormSq Yrem ≤ (e i : ℝ) ^ (2 : ℕ) := by
    intro i hei
    have hIndX : Section1.inducedCF H (ψ i) ∈ X :=
      theorem_6_8_induced_constituent_mem_X_of_nonzero_central_decomposition
        h68' hcase hB hfamily e ψ hφ hφne hψirr hdecomp horth i hei
    rcases theorem_6_8_induced_constituent_pf54_projection_scalar_data
        hSbot hsemi hfamily hZcomm R hsetup h52a h52b h52c h52d h52e
        hτ₁ e ψ i (hdegree i hei) hIndX hη₁Y with
      ⟨Xbig, Yrem, hXbig_span, _hYrem_orth, hTproj, _hXbig_norm,
        hpf54, hscalar_neg⟩
    let χU : {χ : Section1.ClassFunction L // χ ∈ X ∪ Y} :=
      ⟨Section1.inducedCF H (ψ i), Finset.mem_union.mpr (Or.inl hIndX)⟩
    have hshift_span :
        Section5.integerSpanOn (X ∪ Y) Section5.puncturedSet
          (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁) :=
      (theorem_6_8_induced_constituent_shift_integerSpanOn
        hsemi hfamily e ψ i (hdegree i hei) hIndX hη₁Y).2
    have hYremvirt : Theory.Character.IsVirtualCharacter Yrem :=
      theorem_6_8_pf54_remainder_virtual
        (U := X ∪ Y) (T := T) (R := R χU) h52b (h52d χU).1
        hshift_span hXbig_span hTproj
    rcases theorem_6_8_projection_int_coeff_le_of_pf54_norm
        h68' hfamily hη₁Y hYremvirt hYcfvirt hYself hpf54 with
      ⟨b, hbcoeff, hble⟩
    have hYrem_le :
        Section5.cfNormSq Yrem ≤ Section5.cfNormSq ((e i : ℂ) • η₁) :=
      theorem_6_8_projection_remainder_norm_le_of_pf54
        (Yrem := Yrem) (ψ := (e i : ℂ) • η₁) hpf54
    have hanchor_norm :
        Section5.cfNormSq ((e i : ℂ) • η₁) = (e i : ℝ) ^ (2 : ℕ) :=
      theorem_6_8_mem_Y_smul_cfNormSq_eq_sq h68' hfamily hη₁Y (e i)
    have hnorm_le : Section5.cfNormSq Yrem ≤ (e i : ℝ) ^ (2 : ℕ) := by
      simpa [hanchor_norm] using hYrem_le
    exact ⟨Yrem, b, hble, hbcoeff, hscalar_neg, hnorm_le⟩
  choose Yrem b hb_le hbcoeff hscalar_neg hnorm_le using hproj
  let b0 : ι → ℤ := fun i => if h : e i = 0 then 0 else b i h
  have hb0_le : ∀ i : ι, b0 i ≤ (e i : ℤ) := by
    intro i
    by_cases hei : e i = 0
    · simp [b0, hei]
    · simpa [b0, hei] using hb_le i hei
  have hcommon' : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf := hcommon
  rcases hcommon with ⟨_hη₁Ycommon, hYcfCases, _hphiData⟩
  rcases hYcfCases with hYcf_eq | hYcf_alt
  · let y : ℂ := Section1.scalarProduct G Ycf (τ₁ η₁)
    let s : ι → ℂ := fun i =>
      if h : e i = 0 then 0 else
        Section1.scalarProduct G
          (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₁)
    have hy_eq : y = 1 := by
      dsimp [y]
      simpa [hYcf_eq] using hYself
    have hy_ne : y ≠ 0 := by
      rw [hy_eq]
      norm_num
    have hscalar_all : ∀ i : ι, s i = -(b0 i : ℂ) * y := by
      intro i
      by_cases hei : e i = 0
      · simp [s, b0, hei]
      · have hrem :
            Section1.scalarProduct G (Yrem i hei) (τ₁ η₁) = (b i hei : ℂ) := by
          simpa [hYcf_eq] using hbcoeff i hei
        rw [show s i =
            Section1.scalarProduct G
              (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₁) by
              simp [s, hei]]
        rw [hscalar_neg i hei η₁ hη₁Y, hrem]
        simp [b0, hei, hy_eq]
    have hsum_s_actual :
        (∑ i : ι, (e i : ℂ) * s i) =
          ∑ i : ι, (e i : ℂ) *
            Section1.scalarProduct G
              (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₁) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hei : e i = 0
      · simp [s, hei]
      · simp [s, hei]
    have hweighted_actual :=
      theorem_6_8_weighted_shift_scalar_sum_eq_commonY_of_decomposition
        (Y := Y) (T := T) (τ₁ := τ₁) (η₁ := η₁) (Ycf := Ycf)
        e ψ hshift hcommon' hφ hφne hη₁Y
    have hweighted_s :
        (∑ i : ι, (e i : ℂ) * s i) =
          -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y := by
      calc
        (∑ i : ι, (e i : ℂ) * s i) =
            ∑ i : ι, (e i : ℂ) *
              Section1.scalarProduct G
                (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₁) :=
              hsum_s_actual
        _ = -(Z.relIndex H : ℂ) * y := by
              dsimp [y]
              exact hweighted_actual
        _ = -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y := by
              rw [hsq]
    have hselected :
        s i0 = -(e i0 : ℂ) * y :=
      theorem_6_8_selected_scalar_eq_of_weighted_projection_int_coefficients
        e b0 i0 (s := s) (y := y) hscalar_all hweighted_s hb0_le hei0
    have hb_cast : (b0 i0 : ℂ) = (e i0 : ℂ) := by
      have hmul_neg : -(b0 i0 : ℂ) * y = -(e i0 : ℂ) * y := by
        rw [← hscalar_all i0, hselected]
      have hmul : (b0 i0 : ℂ) * y = (e i0 : ℂ) * y := by
        have h := congrArg Neg.neg hmul_neg
        simpa using h
      exact mul_right_cancel₀ hy_ne hmul
    have hb_eq_int : b0 i0 = (e i0 : ℤ) := by
      exact_mod_cast hb_cast
    have hb0_i0 : b0 i0 = b i0 hei0 := by
      simp [b0, hei0]
    have hcoeff_selected :
        Section1.scalarProduct G (Yrem i0 hei0) Ycf = (e i0 : ℂ) := by
      calc
        Section1.scalarProduct G (Yrem i0 hei0) Ycf = (b i0 hei0 : ℂ) :=
          hbcoeff i0 hei0
        _ = (b0 i0 : ℂ) := by rw [hb0_i0]
        _ = (e i0 : ℂ) := by exact_mod_cast hb_eq_int
    have hYrem_eq :
        Yrem i0 hei0 = (e i0 : ℂ) • Ycf :=
      theorem_6_8_eq_nat_smul_of_scalarProduct_eq_and_cfNormSq_le
        hYself hcoeff_selected (hnorm_le i0 hei0)
    intro η hηY
    have hsneg := hscalar_neg i0 hei0 η hηY
    rw [hsneg, hYrem_eq, Section1.scalarProduct_smul_left]
    ring
  · rcases hYcf_alt with ⟨η₂, _hcard, hη₂Y, _hη₂ne, hYcf_eq⟩
    let y : ℂ := Section1.scalarProduct G Ycf (τ₁ η₂)
    let s : ι → ℂ := fun i =>
      if h : e i = 0 then 0 else
        Section1.scalarProduct G
          (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₂)
    have hτη₂self : Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) = 1 := by
      have htmp := hYself
      rw [hYcf_eq, theorem_6_8_scalarProduct_neg_neg] at htmp
      exact htmp
    have hy_eq : y = -1 := by
      dsimp [y]
      have hneg_left :
          Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₂) =
            -Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) := by
        rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_left]
        simp
      calc
        Section1.scalarProduct G Ycf (τ₁ η₂) =
            Section1.scalarProduct G (-τ₁ η₂) (τ₁ η₂) := by rw [hYcf_eq]
        _ = -Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) := hneg_left
        _ = -1 := by rw [hτη₂self]
    have hy_ne : y ≠ 0 := by
      rw [hy_eq]
      norm_num
    have hscalar_all : ∀ i : ι, s i = -(b0 i : ℂ) * y := by
      intro i
      by_cases hei : e i = 0
      · simp [s, b0, hei]
      · have hbneg :
            Section1.scalarProduct G (Yrem i hei) (-τ₁ η₂) = (b i hei : ℂ) := by
          simpa [hYcf_eq] using hbcoeff i hei
        have hneg_right :
            Section1.scalarProduct G (Yrem i hei) (-τ₁ η₂) =
              -Section1.scalarProduct G (Yrem i hei) (τ₁ η₂) := by
          rw [← neg_one_smul ℂ (τ₁ η₂), Section1.scalarProduct_smul_right]
          simp
        have hrem :
            Section1.scalarProduct G (Yrem i hei) (τ₁ η₂) = -(b i hei : ℂ) := by
          rw [hneg_right] at hbneg
          have h := congrArg Neg.neg hbneg
          simpa using h
        rw [show s i =
            Section1.scalarProduct G
              (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₂) by
              simp [s, hei]]
        rw [hscalar_neg i hei η₂ hη₂Y, hrem]
        simp [b0, hei, hy_eq]
    have hsum_s_actual :
        (∑ i : ι, (e i : ℂ) * s i) =
          ∑ i : ι, (e i : ℂ) *
            Section1.scalarProduct G
              (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₂) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hei : e i = 0
      · simp [s, hei]
      · simp [s, hei]
    have hweighted_actual :=
      theorem_6_8_weighted_shift_scalar_sum_eq_commonY_of_decomposition
        (Y := Y) (T := T) (τ₁ := τ₁) (η₁ := η₁) (Ycf := Ycf)
        e ψ hshift hcommon' hφ hφne hη₂Y
    have hweighted_s :
        (∑ i : ι, (e i : ℂ) * s i) =
          -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y := by
      calc
        (∑ i : ι, (e i : ℂ) * s i) =
            ∑ i : ι, (e i : ℂ) *
              Section1.scalarProduct G
                (T (Section1.inducedCF H (ψ i) - (e i : ℂ) • η₁)) (τ₁ η₂) :=
              hsum_s_actual
        _ = -(Z.relIndex H : ℂ) * y := by
              dsimp [y]
              exact hweighted_actual
        _ = -(∑ i : ι, (e i : ℂ) * (e i : ℂ)) * y := by
              rw [hsq]
    have hselected :
        s i0 = -(e i0 : ℂ) * y :=
      theorem_6_8_selected_scalar_eq_of_weighted_projection_int_coefficients
        e b0 i0 (s := s) (y := y) hscalar_all hweighted_s hb0_le hei0
    have hb_cast : (b0 i0 : ℂ) = (e i0 : ℂ) := by
      have hmul_neg : -(b0 i0 : ℂ) * y = -(e i0 : ℂ) * y := by
        rw [← hscalar_all i0, hselected]
      have hmul : (b0 i0 : ℂ) * y = (e i0 : ℂ) * y := by
        have h := congrArg Neg.neg hmul_neg
        simpa using h
      exact mul_right_cancel₀ hy_ne hmul
    have hb_eq_int : b0 i0 = (e i0 : ℤ) := by
      exact_mod_cast hb_cast
    have hb0_i0 : b0 i0 = b i0 hei0 := by
      simp [b0, hei0]
    have hcoeff_selected :
        Section1.scalarProduct G (Yrem i0 hei0) Ycf = (e i0 : ℂ) := by
      calc
        Section1.scalarProduct G (Yrem i0 hei0) Ycf = (b i0 hei0 : ℂ) :=
          hbcoeff i0 hei0
        _ = (b0 i0 : ℂ) := by rw [hb0_i0]
        _ = (e i0 : ℂ) := by exact_mod_cast hb_eq_int
    have hYrem_eq :
        Yrem i0 hei0 = (e i0 : ℂ) • Ycf :=
      theorem_6_8_eq_nat_smul_of_scalarProduct_eq_and_cfNormSq_le
        hYself hcoeff_selected (hnorm_le i0 hei0)
    intro η hηY
    have hsneg := hscalar_neg i0 hei0 η hηY
    rw [hsneg, hYrem_eq, Section1.scalarProduct_smul_left]
    ring

theorem theorem_6_8_shift_scalarProduct_caseB_projection_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L} (hη₁Y : η₁ ∈ Y)
    {Ycf : Section1.ClassFunction G}
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∀ η : Section1.ClassFunction L, η ∈ Y →
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        Section1.scalarProduct G (T (χ - a • η₁)) (τ₁ η) =
          -a * Section1.scalarProduct G Ycf (τ₁ η) := by
  classical
  rcases h52union with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  intro χ hχX η hηY
  rcases theorem_6_8_center_restriction_nonprincipal_of_mem_X_caseB
      h68 hcase hB hfamily hχX with
    ⟨θ, φ, hθ, hφ, hφne, hχeq, hratio, hres⟩
  rcases theorem_6_8_caseB_Z_center_normal_ne_bot h68 hcase hB with
    ⟨_hZne, hZcent, _hZnorm⟩
  have hprime : Nat.Prime (Nat.card Z) :=
    theorem_6_8_caseB_Z_prime_card hcase hB
  have hφone : Section1.degree φ = 1 := by
    rw [Section1.degree_apply]
    exact theorem_6_8_degree_one_of_prime_card_irreducible hprime hφ
  rcases theorem_6_8_central_subgroup_induction_decomposition
      hZcent hθ hφ hφone hres with
    ⟨ι, hι, hdec, e, ψ, i0, hψirr, horth, hdegree, hdecomp, hi0, hsq,
      hsel⟩
  let : Fintype ι := hι
  let : DecidableEq ι := hdec
  let : Finite ι := Finite.of_fintype ι
  have hei0 : e i0 ≠ 0 := by
    intro hzero
    have hθdeg0 : Section1.degree θ = 0 := by
      rw [← hsel]
      simp [hzero]
    exact (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup θ hθ) hθdeg0
  have hselected :=
    theorem_6_8_selected_shift_scalar_eq_of_projection_int_coefficients
      h68 hcase hB hfamily R hsetup h52a h52b h52c h52d h52e hτ₁ hη₁Y
      hcommon hφ hφne e ψ i0 hψirr horth hdegree hdecomp hsq hei0
  have ha :
      Section1.degree χ / (Nat.card W1 : ℂ) = (e i0 : ℂ) := by
    rw [hratio, ← hsel]
  have harg :
      χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁ =
        Section1.inducedCF H (ψ i0) - (e i0 : ℂ) • η₁ := by
    rw [ha, hχeq, hi0]
  calc
    Section1.scalarProduct G
        (T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)) (τ₁ η) =
      Section1.scalarProduct G
        (T (Section1.inducedCF H (ψ i0) - (e i0 : ℂ) • η₁)) (τ₁ η) := by
        rw [harg]
    _ = -(e i0 : ℂ) * Section1.scalarProduct G Ycf (τ₁ η) :=
        hselected η hηY
    _ = -(Section1.degree χ / (Nat.card W1 : ℂ)) *
        Section1.scalarProduct G Ycf (τ₁ η) := by
        rw [ha]

theorem theorem_6_8_2_3_of_projection_caseB_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G} :
    theorem_6_8_2_3_statement L H W1 W2 W Z S SZ X Y T τ₁ η₁ Ycf := by
  intro h68 hpQ hcase hB hfamily hcommon
  exact (theorem_6_8_2_3_of_shift_scalarProduct_caseB_familyData
    (theorem_6_8_shift_scalarProduct_caseB_projection_familyData
      h68 hcase hB hfamily h52union hτ₁ hcommon.1 hcommon))
    h68 hpQ hcase hB hfamily hcommon

theorem theorem_6_8_caseB_unionImage_Y_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Theory.Character.IsVirtualCharacter
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) := by
  have hYcfvirt : Theory.Character.IsVirtualCharacter Ycf :=
    theorem_6_8_caseB_commonY_virtual
      (T := T) (τ₁ := τ₁) hτ₁ hcommon
  rcases hcommon with ⟨hη₁Y, hcommonY, hphi⟩
  rcases hτ₁ with ⟨_hIso, hvirt, _hagree⟩
  have hηvirt :
      Theory.Character.IsVirtualCharacter
        (τ₁ (η : Section1.ClassFunction L)) :=
    hvirt (η : Section1.ClassFunction L)
      (Section5.integerSpan_of_mem Y hηY)
  have hη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
    hvirt η₁ (Section5.integerSpan_of_mem Y hη₁Y)
  have himg :
      theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η =
      τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf :=
    theorem_6_8_caseB_unionImage_of_mem_Y
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η hηY
  simpa [himg] using
    Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hηvirt hη₁virt) hYcfvirt

theorem theorem_6_8_caseB_unionImage_X_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηX : (η : Section1.ClassFunction L) ∈ X)
    (hηnotY : (η : Section1.ClassFunction L) ∉ Y) :
    Theory.Character.IsVirtualCharacter
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) := by
  rcases hcommon with ⟨hη₁Y, hcommonY, hphi⟩
  have hcommon' :
      theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf :=
    ⟨hη₁Y, hcommonY, hphi⟩
  rcases h52union with ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  let img : Section1.ClassFunction G :=
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift η
  have hspec :
      T ((η : Section1.ClassFunction L) -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁) =
        img -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • Ycf := by
    simpa [img] using
      (theorem_6_8_caseB_unionImage_X_spec
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η hηX hηnotY).2
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hηX hη₁Y with
    ⟨a, _hηdeg, hηdiv, hspan⟩
  have hshift_a :
      T ((η : Section1.ClassFunction L) - (a : ℂ) • η₁) =
        img - (a : ℂ) • Ycf := by
    have hηdiv' :
        Section1.degree (η : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hηdiv
    simpa [hηdiv'] using hspec
  have hTvirt :
      Theory.Character.IsVirtualCharacter
        (T ((η : Section1.ClassFunction L) - (a : ℂ) • η₁)) :=
    (h52b.2 ((η : Section1.ClassFunction L) - (a : ℂ) • η₁) hspan).1
  have hdiffvirt : Theory.Character.IsVirtualCharacter (img - (a : ℂ) • Ycf) := by
    simpa [hshift_a] using hTvirt
  have hYcfvirt : Theory.Character.IsVirtualCharacter Ycf :=
    theorem_6_8_caseB_commonY_virtual
      (T := T) (τ₁ := τ₁) hτ₁ hcommon'
  have hYcfScaled : Theory.Character.IsVirtualCharacter ((a : ℂ) • Ycf) := by
    simpa using theorem_6_8_isVirtualCharacter_zsmul (a : ℤ) hYcfvirt
  have hsum :
      Theory.Character.IsVirtualCharacter
        ((img - (a : ℂ) • Ycf) + (a : ℂ) • Ycf) :=
    Section3.isVirtualCharacter_add hdiffvirt hYcfScaled
  have hcancel : (img - (a : ℂ) • Ycf) + (a : ℂ) • Ycf = img := by
    ext g
    simp [sub_eq_add_neg, add_assoc]
  simpa [img, hcancel] using hsum

theorem theorem_6_8_caseB_unionImage_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    ∀ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Theory.Character.IsVirtualCharacter
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) := by
  intro η
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · exact theorem_6_8_caseB_unionImage_Y_virtual
      (W1 := W1) (X := X) (T := T) (τ₁ := τ₁)
      (hshift := hshift) hτ₁ hcommon η hηY
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    exact theorem_6_8_caseB_unionImage_X_virtual
      (W1 := W1) (hshift := hshift)
      hSbot hsemi hfamily h52union hτ₁ hcommon η hηX hηY


theorem theorem_6_8_caseB_unionImage_split
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y}) :
    T ((η : Section1.ClassFunction L) -
        (Section1.degree (η : Section1.ClassFunction L) /
          (Nat.card W1 : ℂ)) • η₁) =
      theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η -
        (Section1.degree (η : Section1.ClassFunction L) /
          (Nat.card W1 : ℂ)) • Ycf := by
  rcases hcommon with ⟨hη₁Y, _hcommonY, _hphi⟩
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · have hηdeg :
        Section1.degree (η : Section1.ClassFunction L) =
          (Nat.card W1 : ℂ) :=
      theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hηY
    have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := W1)).ne'
    have hratio :
        Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ) = 1 := by
      rw [hηdeg, div_self hW1ne]
    have hratioFintype :
        Section1.degree (η : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = 1 := by
      simpa [Nat.card_eq_fintype_card] using hratio
    have hτagree :
        τ₁ ((η : Section1.ClassFunction L) - η₁) =
          T ((η : Section1.ClassFunction L) - η₁) :=
      theorem_6_8_caseB_Y_generator_agreement
        hsemi hfamily hτ₁ hηY hη₁Y
    have himg :
        theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η =
        τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf :=
      theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η hηY
    calc
      T ((η : Section1.ClassFunction L) -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁)
          = T ((η : Section1.ClassFunction L) - η₁) := by
              simp [hratioFintype]
      _ = τ₁ ((η : Section1.ClassFunction L) - η₁) := hτagree.symm
      _ = theorem_6_8_caseB_unionImage
            (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
            η₁ Ycf hshift η -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • Ycf := by
              rw [map_sub, himg, hratio]
              simp [sub_eq_add_neg, add_assoc]
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η hηX hηY).2

theorem theorem_6_8_caseB_unionImage_X_X_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (χ ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hξX : (ξ : Section1.ClassFunction L) ∈ X) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift ξ) =
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  rcases hcommon with ⟨hη₁Y, hcommonY, hphi⟩
  have hcommon' : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf :=
    ⟨hη₁Y, hcommonY, hphi⟩
  rcases h52union with ⟨_hsetup, _R, h52a, h52b, h52c, _h52d, _h52e⟩
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G := fun ζ =>
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift ζ
  change Section1.scalarProduct G (img χ) (img ξ) =
    Section1.scalarProduct L (χ : Section1.ClassFunction L)
      (ξ : Section1.ClassFunction L)
  have hχnotY : (χ : Section1.ClassFunction L) ∉ Y := by
    intro hχY
    exact theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hχY hχX
  have hξnotY : (ξ : Section1.ClassFunction L) ∉ Y := by
    intro hξY
    exact theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hξY hξX
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hχX hη₁Y with
    ⟨a, _hχdeg, hχdiv, hχspan⟩
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hξX hη₁Y with
    ⟨b, _hξdeg, hξdiv, hξspan⟩
  let χ0 : Section1.ClassFunction L :=
    (χ : Section1.ClassFunction L) - (a : ℂ) • η₁
  let ξ0 : Section1.ClassFunction L :=
    (ξ : Section1.ClassFunction L) - (b : ℂ) • η₁
  have hTχ : T χ0 = img χ - (a : ℂ) • Ycf := by
    dsimp [χ0, img]
    have hsplit := theorem_6_8_caseB_unionImage_split
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      (hshift := hshift)
      hsemi hfamily hτ₁ hcommon' χ
    have hχdiv' :
        Section1.degree (χ : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hχdiv
    simpa [hχdiv'] using hsplit
  have hTξ : T ξ0 = img ξ - (b : ℂ) • Ycf := by
    dsimp [ξ0, img]
    have hsplit := theorem_6_8_caseB_unionImage_split
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      (hshift := hshift)
      hsemi hfamily hτ₁ hcommon' ξ
    have hξdiv' :
        Section1.degree (ξ : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (b : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hξdiv
    simpa [hξdiv'] using hsplit
  have hχorth : orthogonalToTransformedFinset Y τ₁ (img χ) := by
    dsimp [img]
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      χ hχX hχnotY).1
  have hξorth : orthogonalToTransformedFinset Y τ₁ (img ξ) := by
    dsimp [img]
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      ξ hξX hξnotY).1
  have hχYcf : Section1.scalarProduct G (img χ) Ycf = 0 :=
    theorem_6_8_caseB_orthogonal_commonY_right hcommon' hχorth
  have hYcfξ : Section1.scalarProduct G Ycf (img ξ) = 0 :=
    theorem_6_8_caseB_orthogonal_commonY_left hcommon' hξorth
  have hχY : Section1.scalarProduct L (χ : Section1.ClassFunction L) η₁ = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hη₁notX : η₁ ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
    have hχneη₁ : (χ : Section1.ClassFunction L) ≠ η₁ := by
      intro hχeq
      exact hη₁notX (by simpa [hχeq] using hχX)
    exact h52c hχU hη₁U hχneη₁
  have hYξ : Section1.scalarProduct L η₁ (ξ : Section1.ClassFunction L) = 0 := by
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hξU : (ξ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hξX)
    have hη₁notX : η₁ ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
    have hη₁neξ : η₁ ≠ (ξ : Section1.ClassFunction L) := by
      intro hη₁eq
      exact hη₁notX (by simpa [← hη₁eq] using hξX)
    exact h52c hη₁U hξU hη₁neξ
  have hself :
      Section1.scalarProduct G Ycf Ycf = Section1.scalarProduct L η₁ η₁ :=
    theorem_6_8_caseB_commonY_self_gram hfamily h52a hτ₁ hcommon'
  have hleft :
      Section1.scalarProduct G (img χ - (a : ℂ) • Ycf)
          (img ξ - (b : ℂ) • Ycf) =
        Section1.scalarProduct G (img χ) (img ξ) +
          ((a : ℂ) * (b : ℂ)) * Section1.scalarProduct G Ycf Ycf := by
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hχYcf, hYcfξ, mul_assoc]
  have hright :
      Section1.scalarProduct L χ0 ξ0 =
        Section1.scalarProduct L (χ : Section1.ClassFunction L)
          (ξ : Section1.ClassFunction L) +
          ((a : ℂ) * (b : ℂ)) * Section1.scalarProduct L η₁ η₁ := by
    dsimp [χ0, ξ0]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hχY, hYξ, mul_assoc]
  have hiso : Section1.scalarProduct G (T χ0) (T ξ0) =
      Section1.scalarProduct L χ0 ξ0 :=
    h52b.1 χ0 ξ0 hχspan hξspan
  rw [hTχ, hTξ, hleft, hright, hself] at hiso
  exact add_right_cancel hiso

theorem theorem_6_8_caseB_unionImage_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    ∀ η ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η)
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift ξ) =
        Section1.scalarProduct L
          (η : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  intro η ξ
  have h52union' : Section5.hypothesis_5_2_statement (X ∪ Y) T := h52union
  rcases h52union with ⟨_hsetup, _R, h52a, _h52b, h52c, _h52d, _h52e⟩
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · by_cases hξY : (ξ : Section1.ClassFunction L) ∈ Y
    · exact theorem_6_8_caseB_unionImage_Y_Y_gram
        (W1 := W1) (hshift := hshift)
        hfamily h52a h52c hτ₁ hcommon η ξ hηY hξY
    · have hξX : (ξ : Section1.ClassFunction L) ∈ X := by
        rcases Finset.mem_union.mp ξ.2 with hξX | hξY'
        · exact hξX
        · exact (hξY hξY').elim
      exact theorem_6_8_caseB_unionImage_Y_X_gram
        (W1 := W1) hfamily hZcomm h52c hcommon ξ η hξX hξY hηY
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    by_cases hξY : (ξ : Section1.ClassFunction L) ∈ Y
    · exact theorem_6_8_caseB_unionImage_X_Y_gram
        (W1 := W1) hfamily hZcomm h52c hcommon η ξ hηX hηY hξY
    · have hξX : (ξ : Section1.ClassFunction L) ∈ X := by
        rcases Finset.mem_union.mp ξ.2 with hξX | hξY'
        · exact hξX
        · exact (hξY hξY').elim
      exact theorem_6_8_caseB_unionImage_X_X_gram
        (W1 := W1) (hshift := hshift)
        hSbot hsemi hfamily hZcomm h52union' hτ₁ hcommon η ξ hηX hξX

theorem theorem_6_8_map_evalCoeff
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {ι : Type*} [Fintype ι]
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (μ : ι → Section1.ClassFunction L)
    (v : Section1.CoeffVector ι) :
    T (Section1.evalCoeff μ v) = Section1.evalCoeff (fun i => T (μ i)) v := by
  ext g
  simp [Section1.evalCoeff, Finset.sum_apply]

theorem theorem_6_8_unionImage_agreesOnIntegerSpanOn_of_split
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {U : Finset (Section1.ClassFunction L)}
    {Tnew T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {img : U → Section1.ClassFunction G}
    (hsplit : ∀ η : U,
      T ((η : Section1.ClassFunction L) -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁) =
        img η -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • Ycf)
    (hTnew : ∀ η : U,
      Tnew (η : Section1.ClassFunction L) = img η) :
    Section5.agreesOnIntegerSpanOn U Section5.puncturedSet T Tnew := by
  classical
  intro χ hχ
  rcases hχ with ⟨hχspan, hχon⟩
  rcases hχspan with ⟨v, hv⟩
  let μU : U → Section1.ClassFunction L := fun η => (η : Section1.ClassFunction L)
  let ratio : U → ℂ := fun η =>
    Section1.degree (η : Section1.ClassFunction L) / (Nat.card W1 : ℂ)
  let gen : U → Section1.ClassFunction L := fun η =>
    (η : Section1.ClassFunction L) - ratio η • η₁
  let s : ℂ := ∑ η : U, (v η : ℂ) * ratio η
  have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hdegχ : Section1.degree χ = 0 :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero χ).1 hχon
  have hdeg_eval :
      Section1.degree χ =
        ∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L)) := by
    rw [hv, Section1.evalCoeff, Section1.degree_apply]
    simp [Section1.degree_apply]
  have hfactor :
      (∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L))) =
        s * (Nat.card W1 : ℂ) := by
    calc
      (∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L))) =
          ∑ η : U, ((v η : ℂ) * ratio η * (Nat.card W1 : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro η _hη
            dsimp [ratio]
            field_simp [hW1ne]
      _ = s * (Nat.card W1 : ℂ) := by
            simp [s, Finset.sum_mul, mul_assoc]
  have hs0 : s = 0 := by
    have hs_mul : s * (Nat.card W1 : ℂ) = 0 := by
      rw [← hfactor, ← hdeg_eval, hdegχ]
    exact (mul_eq_zero.mp hs_mul).resolve_right hW1ne
  have hsource_eval :
      Section1.evalCoeff gen v = χ - s • η₁ := by
    rw [hv]
    ext g
    simp [Section1.evalCoeff, gen, ratio, s, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have htarget_eval :
      Section1.evalCoeff (fun η : U => T (gen η)) v =
        Section1.evalCoeff img v - s • Ycf := by
    have hsplit_eval :
        Section1.evalCoeff (fun η : U => T (gen η)) v =
          Section1.evalCoeff (fun η : U => img η - ratio η • Ycf) v := by
      congr 1
      funext η
      exact hsplit η
    rw [hsplit_eval]
    ext g
    simp [Section1.evalCoeff, ratio, s, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have himg_eval : Section1.evalCoeff img v = T χ := by
    have hEq :
        Section1.evalCoeff img v - s • Ycf = T (χ - s • η₁) := by
      calc
        Section1.evalCoeff img v - s • Ycf =
            Section1.evalCoeff (fun η : U => T (gen η)) v := by
              exact htarget_eval.symm
        _ = T (Section1.evalCoeff gen v) := by
              exact (theorem_6_8_map_evalCoeff T gen v).symm
        _ = T (χ - s • η₁) := by rw [hsource_eval]
    have hEq' := hEq
    rw [hs0, zero_smul, sub_zero] at hEq'
    simpa using hEq'
  calc
    Tnew χ = Tnew (Section1.evalCoeff μU v) := by rw [hv]
    _ = Section1.evalCoeff (fun η : U => Tnew (η : Section1.ClassFunction L)) v := by
          exact theorem_6_8_map_evalCoeff Tnew μU v
    _ = Section1.evalCoeff img v := by
          congr 1
          funext η
          ext g
          exact congrArg (fun f : Section1.ClassFunction G => f g) (hTnew η)
    _ = T χ := himg_eval

theorem theorem_6_8_caseB_unionImage_agreesOnIntegerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {Tnew T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf)
    (hTnew : ∀ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Tnew (η : Section1.ClassFunction L) =
        theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) :
    Section5.agreesOnIntegerSpanOn (X ∪ Y) Section5.puncturedSet T Tnew := by
  classical
  intro χ hχ
  rcases hχ with ⟨hχspan, hχon⟩
  rcases hχspan with ⟨v, hv⟩
  let U : Finset (Section1.ClassFunction L) := X ∪ Y
  let μU : U → Section1.ClassFunction L := fun η => (η : Section1.ClassFunction L)
  let img : U → Section1.ClassFunction G := fun η =>
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift η
  let ratio : U → ℂ := fun η =>
    Section1.degree (η : Section1.ClassFunction L) / (Nat.card W1 : ℂ)
  let gen : U → Section1.ClassFunction L := fun η =>
    (η : Section1.ClassFunction L) - ratio η • η₁
  let s : ℂ := ∑ η : U, (v η : ℂ) * ratio η
  have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hdegχ : Section1.degree χ = 0 :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero χ).1 hχon
  have hdeg_eval :
      Section1.degree χ =
        ∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L)) := by
    rw [hv, Section1.evalCoeff, Section1.degree_apply]
    simp [U, Section1.degree_apply]
  have hfactor :
      (∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L))) =
        s * (Nat.card W1 : ℂ) := by
    calc
      (∑ η : U,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction L))) =
          ∑ η : U, ((v η : ℂ) * ratio η * (Nat.card W1 : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro η _hη
            dsimp [ratio]
            field_simp [hW1ne]
      _ = s * (Nat.card W1 : ℂ) := by
            simp [s, Finset.sum_mul, mul_assoc]
  have hs0 : s = 0 := by
    have hs_mul : s * (Nat.card W1 : ℂ) = 0 := by
      rw [← hfactor, ← hdeg_eval, hdegχ]
    exact (mul_eq_zero.mp hs_mul).resolve_right hW1ne
  have hsource_eval :
      Section1.evalCoeff gen v = χ - s • η₁ := by
    rw [hv]
    ext g
    simp [Section1.evalCoeff, gen, ratio, s, U, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have htarget_eval :
      Section1.evalCoeff (fun η : U => T (gen η)) v =
        Section1.evalCoeff img v - s • Ycf := by
    have hsplit_eval :
        Section1.evalCoeff (fun η : U => T (gen η)) v =
          Section1.evalCoeff (fun η : U => img η - ratio η • Ycf) v := by
      congr 1
      funext η
      exact theorem_6_8_caseB_unionImage_split
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        hsemi hfamily hτ₁ hcommon η
    rw [hsplit_eval]
    ext g
    simp [Section1.evalCoeff, img, ratio, s, U, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have himg_eval : Section1.evalCoeff img v = T χ := by
    have hEq :
        Section1.evalCoeff img v - s • Ycf = T (χ - s • η₁) := by
      calc
        Section1.evalCoeff img v - s • Ycf =
            Section1.evalCoeff (fun η : U => T (gen η)) v := by
              exact htarget_eval.symm
        _ = T (Section1.evalCoeff gen v) := by
              exact (theorem_6_8_map_evalCoeff T gen v).symm
        _ = T (χ - s • η₁) := by rw [hsource_eval]
    have hEq' := hEq
    rw [hs0, zero_smul, sub_zero] at hEq'
    simpa using hEq'
  calc
    Tnew χ = Tnew (Section1.evalCoeff μU v) := by rw [hv]
    _ = Section1.evalCoeff (fun η : U => Tnew (η : Section1.ClassFunction L)) v := by
          exact theorem_6_8_map_evalCoeff Tnew μU v
    _ = Section1.evalCoeff img v := by
          congr 1
          funext η
          ext g
          exact congrArg (fun f : Section1.ClassFunction G => f g) (hTnew η)
    _ = T χ := himg_eval

theorem theorem_6_8_exists_coherentExtension_of_image_family
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {img : U → Section1.ClassFunction G}
    (horth : Section5.hypothesis_5_2_c_statement U)
    (hself_ne_zero :
      ∀ η : U,
        Section1.scalarProduct L (η : Section1.ClassFunction L)
          (η : Section1.ClassFunction L) ≠ 0)
    (himg_virt : ∀ η : U, Theory.Character.IsVirtualCharacter (img η))
    (hgram :
      ∀ η ξ : U,
        Section1.scalarProduct G (img η) (img ξ) =
          Section1.scalarProduct L (η : Section1.ClassFunction L)
            (ξ : Section1.ClassFunction L))
    (hagree :
      ∀ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
        (∀ η : U, Tnew (η : Section1.ClassFunction L) = img η) →
          Section5.agreesOnIntegerSpanOn U Section5.puncturedSet T Tnew) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      coherentExtension U T Tnew := by
  rcases Section5.exists_extension_fields_of_image_family_pf57
      U T img horth hself_ne_zero himg_virt hgram hagree with
    ⟨Tnew, hIso, hvirt, hagree'⟩
  exact ⟨Tnew, hIso, hvirt, hagree'⟩

theorem theorem_6_8_coherentFamily_of_hypothesis_5_2_and_image_family
    {G : Type u} [Group G] [Finite G]
    {L : Type u} [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {img : U → Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement U T)
    (himg_virt : ∀ η, Theory.Character.IsVirtualCharacter (img η))
    (hgram : ∀ η ξ,
      Section1.scalarProduct G (img η) (img ξ) =
        Section1.scalarProduct L (η : Section1.ClassFunction L)
          (ξ : Section1.ClassFunction L))
    (hagree :
      ∀ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
        (∀ η : U, Tnew (η : Section1.ClassFunction L) = img η) →
          Section5.agreesOnIntegerSpanOn U Section5.puncturedSet T Tnew) :
    coherentFamily U T := by
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have h52' : Section5.hypothesis_5_2_statement U T :=
    ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hself_ne_zero :
      ∀ η : U,
        Section1.scalarProduct L (η : Section1.ClassFunction L)
          (η : Section1.ClassFunction L) ≠ 0 := by
    intro η
    exact theorem_6_8_scalarProduct_self_ne_zero_of_character_not_conjugate
      (hsetup.2 η) (h52a η).2
  rcases theorem_6_8_exists_coherentExtension_of_image_family
      h52c hself_ne_zero himg_virt hgram hagree with
    ⟨Tnew, hext⟩
  exact theorem_6_8_coherentFamily_of_hypothesis_5_2_and_extension h52' hext


theorem theorem_6_8_caseA_shift_data_all_of_base_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ χ₀ : Section1.ClassFunction L}
    {Ycf X₀ : Section1.ClassFunction G}
    (hτ₂ : coherentExtension X T τ₂)
    (hχ₀X : χ₀ ∈ X)
    (hbase :
      T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
        X₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • Ycf)
    (horth₀ : orthogonalToTransformedFinset Y τ₁ X₀)
    (horthτ₂ : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      orthogonalToTransformedFinset Y τ₁ (τ₂ χ))
    (hmul : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀) :
    ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ Xχ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ Xχ ∧
          T (χ - a • η₁) = Xχ - a • Ycf := by
  intro χ hχX
  rcases hmul χ hχX with ⟨d, hχdeg⟩
  have hχspan : Section5.integerSpan X χ :=
    Section5.integerSpan_of_mem X hχX
  have hχ₀span : Section5.integerSpan X χ₀ :=
    Section5.integerSpan_of_mem X hχ₀X
  have hχ₀smul : Section5.integerSpan X ((d : ℂ) • χ₀) := by
    simpa using Section5.integerSpan_zsmul (S := X) (φ := χ₀) (d : ℤ) hχ₀span
  have hdiffSpan : Section5.integerSpan X (χ - (d : ℂ) • χ₀) :=
    Section5.integerSpan_sub hχspan hχ₀smul
  have hdiffDeg : Section1.degree (χ - (d : ℂ) • χ₀) = 0 := by
    rw [Section1.degree_apply] at hχdeg ⊢
    simp [Section1.degree_apply, hχdeg]
  have hdiffOn :
      Section5.integerSpanOn X Section5.puncturedSet (χ - (d : ℂ) • χ₀) :=
    ⟨hdiffSpan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdiffDeg⟩
  have hagree :
      τ₂ (χ - (d : ℂ) • χ₀) = T (χ - (d : ℂ) • χ₀) :=
    hτ₂.2.2 (χ - (d : ℂ) • χ₀) hdiffOn
  let c₀ : ℂ := Section1.degree χ₀ / (Nat.card W1 : ℂ)
  have hratio :
      Section1.degree χ / (Nat.card W1 : ℂ) = (d : ℂ) * c₀ := by
    simp [c₀, hχdeg]
    ring
  let Xχ : Section1.ClassFunction G :=
    τ₂ χ - (d : ℂ) • τ₂ χ₀ + (d : ℂ) • X₀
  have horthχ : orthogonalToTransformedFinset Y τ₁ Xχ := by
    intro η hηY
    have hτχ := horthτ₂ χ hχX η hηY
    have hτχ₀ := horthτ₂ χ₀ hχ₀X η hηY
    have hX₀ := horth₀ η hηY
    dsimp [Xχ]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    simp [hτχ, hτχ₀, hX₀]
  refine ⟨Xχ, horthχ, ?_⟩
  have hdecomp :
      χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁ =
        (χ - (d : ℂ) • χ₀) + (d : ℂ) • (χ₀ - c₀ • η₁) := by
    rw [hratio, smul_sub, smul_smul]
    simp [c₀]
  calc
    T (χ - (Section1.degree χ / (Nat.card W1 : ℂ)) • η₁)
        = T (χ - (d : ℂ) • χ₀) + (d : ℂ) • T (χ₀ - c₀ • η₁) := by
          rw [hdecomp, map_add, map_smul]
    _ = τ₂ (χ - (d : ℂ) • χ₀) +
          (d : ℂ) • (X₀ - c₀ • Ycf) := by
          rw [← hagree]
          simpa [c₀] using congrArg ((d : ℂ) • ·) hbase
    _ = Xχ - (Section1.degree χ / (Nat.card W1 : ℂ)) • Ycf := by
          rw [map_sub, map_smul, hratio, smul_sub, smul_smul]
          simp [Xχ, c₀, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem theorem_6_8_caseA_shift_data_all_of_base_shift_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ χ₀ : Section1.ClassFunction L}
    (hτ₂ : coherentExtension X T τ₂)
    (hχ₀X : χ₀ ∈ X)
    (horthτ₂ : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      orthogonalToTransformedFinset Y τ₁ (τ₂ χ))
    (hmul : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀)
    (hbaseData :
      (∃ X₁ : Section1.ClassFunction G,
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
            X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
        ∃ η₂ : Section1.ClassFunction L,
          Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
            ∃ X₁ : Section1.ClassFunction G,
              orthogonalToTransformedFinset Y τ₁ X₁ ∧
                T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
                  X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • (-τ₁ η₂)) :
    (∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ Xχ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ Xχ ∧
          T (χ - a • η₁) = Xχ - a • τ₁ η₁) ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∀ χ : Section1.ClassFunction L, χ ∈ X →
            ∃ Xχ : Section1.ClassFunction G,
              let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
              orthogonalToTransformedFinset Y τ₁ Xχ ∧
                T (χ - a • η₁) = Xχ - a • (-τ₁ η₂) := by
  rcases hbaseData with hleft | hright
  · left
    rcases hleft with ⟨X₁, horth₁, hEq⟩
    exact theorem_6_8_caseA_shift_data_all_of_base_decomposition
      hτ₂ hχ₀X hEq horth₁ horthτ₂ hmul
  · right
    rcases hright with ⟨η₂, hcard, hη₂Y, hη₂ne, X₁, horth₁, hEq⟩
    refine ⟨η₂, hcard, hη₂Y, hη₂ne, ?_⟩
    exact theorem_6_8_caseA_shift_data_all_of_base_decomposition
      hτ₂ hχ₀X hEq horth₁ horthτ₂ hmul

theorem theorem_6_8_caseA_exists_base_degree_multiple
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hXnonempty : X.Nonempty) :
    ∃ χ₀ : Section1.ClassFunction L, χ₀ ∈ X ∧
      ∀ χ : Section1.ClassFunction L, χ ∈ X →
        ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀ := by
  classical
  rcases hfamily with ⟨_hZH, _hSZ, hXeq, _hY⟩
  let expX : X → ℕ := fun χ =>
    Classical.choose
      (theorem_6_6_degree_eq_relIndex_mul_prime_power
        (K := H) (Z := Z) (S := S) (SZ := SZ) (Xset := X)
        hSbot hXeq hpQ χ.2)
  let degX : X → ℕ := fun χ =>
    Classical.choose
      (Classical.choose_spec
        (theorem_6_6_degree_eq_relIndex_mul_prime_power
          (K := H) (Z := Z) (S := S) (SZ := SZ) (Xset := X)
          hSbot hXeq hpQ χ.2))
  have hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (degX χ : ℂ) ∧
        degX χ = H.relIndex (⊤ : Subgroup L) * p ^ expX χ := by
    intro χ
    exact Classical.choose_spec
      (Classical.choose_spec
        (theorem_6_6_degree_eq_relIndex_mul_prime_power
          (K := H) (Z := Z) (S := S) (SZ := SZ) (Xset := X)
          hSbot hXeq hpQ χ.2))
  have huniv_nonempty : (Finset.univ : Finset X).Nonempty := by
    rcases hXnonempty with ⟨χ, hχX⟩
    exact ⟨⟨χ, hχX⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset X) expX
      huniv_nonempty with
    ⟨χ₀, _hχ₀univ, hχ₀min⟩
  refine ⟨(χ₀ : Section1.ClassFunction L), χ₀.2, ?_⟩
  intro χ hχX
  let χx : X := ⟨χ, hχX⟩
  have hle : expX χ₀ ≤ expX χx :=
    hχ₀min χx (Finset.mem_univ χx)
  let d : ℕ := p ^ (expX χx - expX χ₀)
  have hpow : p ^ expX χx = d * p ^ expX χ₀ := by
    dsimp [d]
    rw [← pow_add]
    rw [Nat.sub_add_cancel hle]
  have hdegNat : degX χx = d * degX χ₀ := by
    calc
      degX χx = H.relIndex (⊤ : Subgroup L) * p ^ expX χx :=
        (hdegX χx).2
      _ = H.relIndex (⊤ : Subgroup L) * (d * p ^ expX χ₀) := by
        rw [hpow]
      _ = d * (H.relIndex (⊤ : Subgroup L) * p ^ expX χ₀) := by
        ring
      _ = d * degX χ₀ := by
        rw [(hdegX χ₀).2]
  refine ⟨d, ?_⟩
  calc
    Section1.degree χ = (degX χx : ℂ) := (hdegX χx).1
    _ = (d * degX χ₀ : ℕ) := by rw [hdegNat]
    _ = (d : ℂ) * (degX χ₀ : ℂ) := by norm_num [Nat.cast_mul]
    _ = (d : ℂ) * Section1.degree (χ₀ : Section1.ClassFunction L) := by
      rw [(hdegX χ₀).1]


theorem theorem_6_8_caseB_union_coherent_of_commonY_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hcommon : theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf) :
    coherentFamily (X ∪ Y) T := by
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G :=
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  exact theorem_6_8_coherentFamily_of_hypothesis_5_2_and_image_family
    (U := X ∪ Y) (T := T) (img := img) h52union
    (theorem_6_8_caseB_unionImage_virtual
      (hshift := hshift) hSbot hsemi hfamily h52union hτ₁ hcommon)
    (theorem_6_8_caseB_unionImage_gram
      (hshift := hshift) hSbot hsemi hfamily hZcomm h52union hτ₁ hcommon)
    (fun Tnew hTnew =>
      theorem_6_8_caseB_unionImage_agreesOnIntegerSpanOn
        (hshift := hshift) hsemi hfamily hτ₁ hcommon hTnew)

def theorem_6_8_caseA_signedYShape
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (η₁ : Section1.ClassFunction L) (Ycf : Section1.ClassFunction G) : Prop :=
  η₁ ∈ Y ∧
    (Ycf = τ₁ η₁ ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧ Ycf = -τ₁ η₂)

theorem theorem_6_8_caseA_signedYShape_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf) :
    Theory.Character.IsVirtualCharacter Ycf := by
  rcases hshape with ⟨hη₁Y, hYcf⟩
  rcases hτ₁ with ⟨_hIso, hvirt, _hagree⟩
  rcases hYcf with hYcf | hYcf
  · have hη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
      hvirt η₁ (Section5.integerSpan_of_mem Y hη₁Y)
    simpa [hYcf] using hη₁virt
  · rcases hYcf with ⟨η₂, _hcard, hη₂Y, _hη₂ne, hYcf⟩
    have hη₂virt : Theory.Character.IsVirtualCharacter (τ₁ η₂) :=
      hvirt η₂ (Section5.integerSpan_of_mem Y hη₂Y)
    simpa [hYcf] using Section3.isVirtualCharacter_neg hη₂virt

theorem theorem_6_8_caseA_signedYShape_self_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf) :
    Section1.scalarProduct G Ycf Ycf =
      Section1.scalarProduct L η₁ η₁ := by
  rcases hτ₁ with ⟨hIso, _hvirt, _hagree⟩
  rcases hshape with ⟨hη₁Y, hYcf⟩
  rcases hYcf with hYcf | hYcf
  · simpa [hYcf] using
      Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₁Y
  · rcases hYcf with ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩
    have hη₂eq : η₂ = Section1.conjugateCharacter η₁ :=
      theorem_6_8_caseB_other_eq_conjugate_of_card_two
        hfamily h52a hcard hη₁Y hη₂Y hη₂ne
    have hIsoη₂ :
        Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) =
          Section1.scalarProduct L η₂ η₂ :=
      Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₂Y hη₂Y
    calc
      Section1.scalarProduct G Ycf Ycf =
          Section1.scalarProduct G (τ₁ η₂) (τ₁ η₂) := by
            rw [hYcf, theorem_6_8_scalarProduct_neg_neg]
      _ = Section1.scalarProduct L η₂ η₂ := hIsoη₂
      _ = Section1.scalarProduct L η₁ η₁ := by
            simpa [hη₂eq] using
              theorem_6_8_scalarProduct_conjugateCharacter_self η₁

theorem theorem_6_8_caseA_signedYShape_orthogonal_right
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf X₁ : Section1.ClassFunction G}
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (horthX : orthogonalToTransformedFinset Y τ₁ X₁) :
    Section1.scalarProduct G X₁ Ycf = 0 := by
  rcases hshape with ⟨hη₁Y, hYcf⟩
  rcases hYcf with hYcf | hYcf
  · simpa [hYcf] using horthX η₁ hη₁Y
  · rcases hYcf with ⟨η₂, _hcard, hη₂Y, _hη₂ne, hYcf⟩
    rw [hYcf]
    have hneg :
        Section1.scalarProduct G X₁ (-τ₁ η₂) =
          -Section1.scalarProduct G X₁ (τ₁ η₂) := by
      simp [Section1.scalarProduct, Finset.sum_neg_distrib]
    rw [hneg, horthX η₂ hη₂Y]
    simp

theorem theorem_6_8_caseA_signedYShape_orthogonal_left
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Y : Finset (Section1.ClassFunction L)}
    {τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf X₁ : Section1.ClassFunction G}
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (horthX : orthogonalToTransformedFinset Y τ₁ X₁) :
    Section1.scalarProduct G Ycf X₁ = 0 := by
  have hright :
      Section1.scalarProduct G X₁ Ycf = 0 :=
    theorem_6_8_caseA_signedYShape_orthogonal_right hshape horthX
  simpa [Section1.scalarProduct_star_swap] using congrArg star hright

theorem theorem_6_8_caseA_signed_unionImage_Y_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Theory.Character.IsVirtualCharacter
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) := by
  have hYcfvirt : Theory.Character.IsVirtualCharacter Ycf :=
    theorem_6_8_caseA_signedYShape_virtual hτ₁ hshape
  rcases hshape with ⟨hη₁Y, _hYcf⟩
  rcases hτ₁ with ⟨_hIso, hvirt, _hagree⟩
  have hηvirt :
      Theory.Character.IsVirtualCharacter
        (τ₁ (η : Section1.ClassFunction L)) :=
    hvirt (η : Section1.ClassFunction L)
      (Section5.integerSpan_of_mem Y hηY)
  have hη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
    hvirt η₁ (Section5.integerSpan_of_mem Y hη₁Y)
  have himg :
      theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η =
      τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf :=
    theorem_6_8_caseB_unionImage_of_mem_Y
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η hηY
  simpa [himg] using
    Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hηvirt hη₁virt) hYcfvirt

theorem theorem_6_8_caseA_signed_unionImage_X_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηX : (η : Section1.ClassFunction L) ∈ X)
    (hηnotY : (η : Section1.ClassFunction L) ∉ Y) :
    Theory.Character.IsVirtualCharacter
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) := by
  rcases hshape with ⟨hη₁Y, hYshape⟩
  have hshape' : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf :=
    ⟨hη₁Y, hYshape⟩
  rcases h52union with ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  let img : Section1.ClassFunction G :=
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift η
  have hspec :
      T ((η : Section1.ClassFunction L) -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁) =
        img -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • Ycf := by
    simpa [img] using
      (theorem_6_8_caseB_unionImage_X_spec
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η hηX hηnotY).2
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hηX hη₁Y with
    ⟨a, _hηdeg, hηdiv, hspan⟩
  have hshift_a :
      T ((η : Section1.ClassFunction L) - (a : ℂ) • η₁) =
        img - (a : ℂ) • Ycf := by
    have hηdiv' :
        Section1.degree (η : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hηdiv
    simpa [hηdiv'] using hspec
  have hTvirt :
      Theory.Character.IsVirtualCharacter
        (T ((η : Section1.ClassFunction L) - (a : ℂ) • η₁)) :=
    (h52b.2 ((η : Section1.ClassFunction L) - (a : ℂ) • η₁) hspan).1
  have hdiffvirt : Theory.Character.IsVirtualCharacter (img - (a : ℂ) • Ycf) := by
    simpa [hshift_a] using hTvirt
  have hYcfvirt : Theory.Character.IsVirtualCharacter Ycf :=
    theorem_6_8_caseA_signedYShape_virtual hτ₁ hshape'
  have hYcfScaled : Theory.Character.IsVirtualCharacter ((a : ℂ) • Ycf) := by
    simpa using theorem_6_8_isVirtualCharacter_zsmul (a : ℤ) hYcfvirt
  have hsum :
      Theory.Character.IsVirtualCharacter
        ((img - (a : ℂ) • Ycf) + (a : ℂ) • Ycf) :=
    Section3.isVirtualCharacter_add hdiffvirt hYcfScaled
  have hcancel : (img - (a : ℂ) • Ycf) + (a : ℂ) • Ycf = img := by
    ext g
    simp [sub_eq_add_neg, add_assoc]
  simpa [img, hcancel] using hsum

theorem theorem_6_8_caseA_signed_unionImage_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf) :
    ∀ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Theory.Character.IsVirtualCharacter
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) := by
  intro η
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · exact theorem_6_8_caseA_signed_unionImage_Y_virtual
      (W1 := W1) (X := X) (T := T) (τ₁ := τ₁)
      (hshift := hshift) hτ₁ hshape η hηY
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    exact theorem_6_8_caseA_signed_unionImage_X_virtual
      (W1 := W1) (hshift := hshift)
      hSbot hsemi hfamily h52union hτ₁ hshape η hηX hηY

theorem theorem_6_8_caseA_signed_unionImage_split
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (η : {η : Section1.ClassFunction L // η ∈ X ∪ Y}) :
    T ((η : Section1.ClassFunction L) -
        (Section1.degree (η : Section1.ClassFunction L) /
          (Nat.card W1 : ℂ)) • η₁) =
      theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η -
        (Section1.degree (η : Section1.ClassFunction L) /
          (Nat.card W1 : ℂ)) • Ycf := by
  rcases hshape with ⟨hη₁Y, _hYshape⟩
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · have hηdeg :
        Section1.degree (η : Section1.ClassFunction L) =
          (Nat.card W1 : ℂ) :=
      theorem_6_8_mem_Y_degree_eq_cardW1 hsemi hfamily hηY
    have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := W1)).ne'
    have hratio :
        Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ) = 1 := by
      rw [hηdeg, div_self hW1ne]
    have hratioFintype :
        Section1.degree (η : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = 1 := by
      simpa [Nat.card_eq_fintype_card] using hratio
    have hτagree :
        τ₁ ((η : Section1.ClassFunction L) - η₁) =
          T ((η : Section1.ClassFunction L) - η₁) :=
      theorem_6_8_caseB_Y_generator_agreement
        hsemi hfamily hτ₁ hηY hη₁Y
    have himg :
        theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η =
        τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ + Ycf :=
      theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η hηY
    calc
      T ((η : Section1.ClassFunction L) -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁)
          = T ((η : Section1.ClassFunction L) - η₁) := by
              simp [hratioFintype]
      _ = τ₁ ((η : Section1.ClassFunction L) - η₁) := hτagree.symm
      _ = theorem_6_8_caseB_unionImage
            (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
            η₁ Ycf hshift η -
          (Section1.degree (η : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • Ycf := by
              rw [map_sub, himg, hratio]
              simp [sub_eq_add_neg, add_assoc]
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η hηX hηY).2

theorem theorem_6_8_caseA_signed_unionImage_X_Y_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) = 0 := by
  have hη₁Y : η₁ ∈ Y := hshape.1
  have hχorth :
      orthogonalToTransformedFinset Y τ₁
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ) :=
    (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      χ hχX hχnotY).1
  have hYcf0 :
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ) Ycf = 0 :=
    theorem_6_8_caseA_signedYShape_orthogonal_right hshape hχorth
  rw [theorem_6_8_caseB_unionImage_of_mem_Y
    (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY]
  rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right]
  simp [hχorth (η : Section1.ClassFunction L) hηY, hχorth η₁ hη₁Y,
    hYcf0]

theorem theorem_6_8_caseA_signed_unionImage_Y_X_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {W1 : Subgroup L}
    {X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ) = 0 := by
  have hright :
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift χ)
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) = 0 :=
    theorem_6_8_caseA_signed_unionImage_X_Y_orthogonal
      (W1 := W1) hshape χ η hχX hχnotY hηY
  simpa [Section1.scalarProduct_star_swap] using congrArg star hright

theorem theorem_6_8_caseA_signed_unionImage_X_Y_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η) =
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (η : Section1.ClassFunction L) := by
  rw [theorem_6_8_caseA_signed_unionImage_X_Y_orthogonal
    (W1 := W1) hshape χ η hχX hχnotY hηY]
  have hsrc :
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (η : Section1.ClassFunction L) = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hηU : (η : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inr hηY)
    have hηnotX : (η : Section1.ClassFunction L) ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
    have hχneη :
        (χ : Section1.ClassFunction L) ≠ (η : Section1.ClassFunction L) := by
      intro hχeq
      exact hηnotX (by simpa [hχeq] using hχX)
    exact h52c hχU hηU hχneη
  rw [hsrc]

theorem theorem_6_8_caseA_signed_unionImage_Y_X_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (χ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hχnotY : (χ : Section1.ClassFunction L) ∉ Y)
    (hηY : (η : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ) =
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (χ : Section1.ClassFunction L) := by
  rw [theorem_6_8_caseA_signed_unionImage_Y_X_orthogonal
    (W1 := W1) hshape χ η hχX hχnotY hηY]
  have hsrc :
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (χ : Section1.ClassFunction L) = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hηU : (η : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inr hηY)
    have hηnotX : (η : Section1.ClassFunction L) ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
    have hηneχ :
        (η : Section1.ClassFunction L) ≠ (χ : Section1.ClassFunction L) := by
      intro hηeq
      exact hηnotX (by simpa [← hηeq] using hχX)
    exact h52c hηU hχU hηneχ
  rw [hsrc]

theorem theorem_6_8_caseA_signed_unionImage_Y_Y_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52a : Section5.hypothesis_5_2_a_statement (X ∪ Y))
    (h52c : Section5.hypothesis_5_2_c_statement (X ∪ Y))
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (η ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hηY : (η : Section1.ClassFunction L) ∈ Y)
    (hξY : (ξ : Section1.ClassFunction L) ∈ Y) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift η)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift ξ) =
      Section1.scalarProduct L
        (η : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G := fun ζ =>
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift ζ
  change Section1.scalarProduct G (img η) (img ξ) =
    Section1.scalarProduct L (η : Section1.ClassFunction L)
      (ξ : Section1.ClassFunction L)
  rcases hτ₁ with ⟨hIso, hvirt, hagree⟩
  have hτ₁' : coherentExtension Y T τ₁ := ⟨hIso, hvirt, hagree⟩
  rcases hshape with ⟨hη₁Y, hYcf⟩
  rcases hYcf with hYcf | hYcf
  · have himgη : img η = τ₁ (η : Section1.ClassFunction L) := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    have himgξ : img ξ = τ₁ (ξ : Section1.ClassFunction L) := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) ξ hξY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    rw [himgη, himgξ]
    exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hηY hξY
  · rcases hYcf with ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩
    have hη₂conj : η₂ = Section1.conjugateCharacter η₁ :=
      theorem_6_8_caseB_other_eq_conjugate_of_card_two
        hfamily h52a hcard hη₁Y hη₂Y hη₂ne
    have hshape' : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf :=
      ⟨hη₁Y, Or.inr ⟨η₂, hcard, hη₂Y, hη₂ne, hYcf⟩⟩
    have hselfYcf : Section1.scalarProduct G Ycf Ycf =
        Section1.scalarProduct L η₁ η₁ :=
      theorem_6_8_caseA_signedYShape_self_gram hfamily h52a hτ₁' hshape'
    have hsrc_self : Section1.scalarProduct L η₂ η₂ =
        Section1.scalarProduct L η₁ η₁ := by
      rw [hη₂conj, theorem_6_8_scalarProduct_conjugateCharacter_self]
    have hηcases := theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
      (Y := Y) (η₁ := η₁) (η₂ := η₂)
      hcard hη₁Y hη₂Y hη₂ne hηY
    have hξcases := theorem_6_8_caseB_card_two_mem_eq_anchor_or_other
      (Y := Y) (η₁ := η₁) (η₂ := η₂)
      hcard hη₁Y hη₂Y hη₂ne hξY
    have himgη_formula : img η =
        τ₁ (η : Section1.ClassFunction L) - τ₁ η₁ - τ₁ η₂ := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) η hηY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    have himgξ_formula : img ξ =
        τ₁ (ξ : Section1.ClassFunction L) - τ₁ η₁ - τ₁ η₂ := by
      dsimp [img]
      rw [theorem_6_8_caseB_unionImage_of_mem_Y
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁) ξ hξY, hYcf]
      ext g
      simp [sub_eq_add_neg, add_assoc]
    rcases hηcases with hηeq | hηeq <;> rcases hξcases with hξeq | hξeq
    · have himgη : img η = Ycf := by
        rw [himgη_formula, hηeq, hYcf]
        ext g
        simp [sub_eq_add_neg]
      have himgξ : img ξ = Ycf := by
        rw [himgξ_formula, hξeq, hYcf]
        ext g
        simp [sub_eq_add_neg]
      rw [himgη, himgξ, hηeq, hξeq]
      exact hselfYcf
    · have himgη : img η = -τ₁ η₂ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg]
      have himgξ : img ξ = -τ₁ η₁ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg]
      have htarget : Section1.scalarProduct G (img η) (img ξ) =
          Section1.scalarProduct L η₂ η₁ := by
        rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg]
        exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₂Y hη₁Y
      have hsrc21 : Section1.scalarProduct L η₂ η₁ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₂Y))
          (Finset.mem_union.mpr (Or.inr hη₁Y)) hη₂ne
      have hsrc12 : Section1.scalarProduct L η₁ η₂ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₁Y))
          (Finset.mem_union.mpr (Or.inr hη₂Y)) hη₂ne.symm
      rw [htarget, hηeq, hξeq, hsrc21, hsrc12]
    · have himgη : img η = -τ₁ η₁ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      have himgξ : img ξ = -τ₁ η₂ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg]
      have htarget : Section1.scalarProduct G (img η) (img ξ) =
          Section1.scalarProduct L η₁ η₂ := by
        rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg]
        exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₂Y
      have hsrc12 : Section1.scalarProduct L η₁ η₂ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₁Y))
          (Finset.mem_union.mpr (Or.inr hη₂Y)) hη₂ne.symm
      have hsrc21 : Section1.scalarProduct L η₂ η₁ = 0 := by
        exact h52c (Finset.mem_union.mpr (Or.inr hη₂Y))
          (Finset.mem_union.mpr (Or.inr hη₁Y)) hη₂ne
      rw [htarget, hηeq, hξeq, hsrc12, hsrc21]
    · have himgη : img η = -τ₁ η₁ := by
        rw [himgη_formula, hηeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      have himgξ : img ξ = -τ₁ η₁ := by
        rw [himgξ_formula, hξeq]
        ext g
        simp [sub_eq_add_neg, add_assoc]
      rw [himgη, himgξ, theorem_6_8_scalarProduct_neg_neg, hηeq, hξeq]
      rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso hη₁Y hη₁Y]
      rw [hsrc_self]

theorem theorem_6_8_caseA_signed_unionImage_X_X_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (χ ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y})
    (hχX : (χ : Section1.ClassFunction L) ∈ X)
    (hξX : (ξ : Section1.ClassFunction L) ∈ X) :
    Section1.scalarProduct G
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift χ)
      (theorem_6_8_caseB_unionImage
        (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
        η₁ Ycf hshift ξ) =
      Section1.scalarProduct L
        (χ : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  have hη₁Y : η₁ ∈ Y := hshape.1
  rcases h52union with ⟨_hsetup, _R, h52a, h52b, h52c, _h52d, _h52e⟩
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G := fun ζ =>
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift ζ
  change Section1.scalarProduct G (img χ) (img ξ) =
    Section1.scalarProduct L (χ : Section1.ClassFunction L)
      (ξ : Section1.ClassFunction L)
  have hχnotY : (χ : Section1.ClassFunction L) ∉ Y := by
    intro hχY
    exact theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hχY hχX
  have hξnotY : (ξ : Section1.ClassFunction L) ∉ Y := by
    intro hξY
    exact theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hξY hξX
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hχX hη₁Y with
    ⟨a, _hχdeg, hχdiv, hχspan⟩
  rcases theorem_6_8_X_shift_eta_integerSpanOn
      hSbot hsemi hfamily hξX hη₁Y with
    ⟨b, _hξdeg, hξdiv, hξspan⟩
  let χ0 : Section1.ClassFunction L :=
    (χ : Section1.ClassFunction L) - (a : ℂ) • η₁
  let ξ0 : Section1.ClassFunction L :=
    (ξ : Section1.ClassFunction L) - (b : ℂ) • η₁
  have hTχ : T χ0 = img χ - (a : ℂ) • Ycf := by
    dsimp [χ0, img]
    have hsplit := theorem_6_8_caseA_signed_unionImage_split
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      (hshift := hshift)
      hsemi hfamily hτ₁ hshape χ
    have hχdiv' :
        Section1.degree (χ : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (a : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hχdiv
    simpa [hχdiv'] using hsplit
  have hTξ : T ξ0 = img ξ - (b : ℂ) • Ycf := by
    dsimp [ξ0, img]
    have hsplit := theorem_6_8_caseA_signed_unionImage_split
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      (hshift := hshift)
      hsemi hfamily hτ₁ hshape ξ
    have hξdiv' :
        Section1.degree (ξ : Section1.ClassFunction L) /
            (Fintype.card W1 : ℂ) = (b : ℂ) := by
      simpa [Nat.card_eq_fintype_card] using hξdiv
    simpa [hξdiv'] using hsplit
  have hχorth : orthogonalToTransformedFinset Y τ₁ (img χ) := by
    dsimp [img]
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      χ hχX hχnotY).1
  have hξorth : orthogonalToTransformedFinset Y τ₁ (img ξ) := by
    dsimp [img]
    exact (theorem_6_8_caseB_unionImage_X_spec
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      ξ hξX hξnotY).1
  have hχYcf : Section1.scalarProduct G (img χ) Ycf = 0 :=
    theorem_6_8_caseA_signedYShape_orthogonal_right hshape hχorth
  have hYcfξ : Section1.scalarProduct G Ycf (img ξ) = 0 :=
    theorem_6_8_caseA_signedYShape_orthogonal_left hshape hξorth
  have hχY : Section1.scalarProduct L (χ : Section1.ClassFunction L) η₁ = 0 := by
    have hχU : (χ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hχX)
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hη₁notX : η₁ ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
    have hχneη₁ : (χ : Section1.ClassFunction L) ≠ η₁ := by
      intro hχeq
      exact hη₁notX (by simpa [hχeq] using hχX)
    exact h52c hχU hη₁U hχneη₁
  have hYξ : Section1.scalarProduct L η₁ (ξ : Section1.ClassFunction L) = 0 := by
    have hη₁U : η₁ ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hη₁Y)
    have hξU : (ξ : Section1.ClassFunction L) ∈ X ∪ Y :=
      Finset.mem_union.mpr (Or.inl hξX)
    have hη₁notX : η₁ ∉ X :=
      theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hη₁Y
    have hη₁neξ : η₁ ≠ (ξ : Section1.ClassFunction L) := by
      intro hη₁eq
      exact hη₁notX (by simpa [← hη₁eq] using hξX)
    exact h52c hη₁U hξU hη₁neξ
  have hself :
      Section1.scalarProduct G Ycf Ycf = Section1.scalarProduct L η₁ η₁ :=
    theorem_6_8_caseA_signedYShape_self_gram hfamily h52a hτ₁ hshape
  have hleft :
      Section1.scalarProduct G (img χ - (a : ℂ) • Ycf)
          (img ξ - (b : ℂ) • Ycf) =
        Section1.scalarProduct G (img χ) (img ξ) +
          ((a : ℂ) * (b : ℂ)) * Section1.scalarProduct G Ycf Ycf := by
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hχYcf, hYcfξ, mul_assoc]
  have hright :
      Section1.scalarProduct L χ0 ξ0 =
        Section1.scalarProduct L (χ : Section1.ClassFunction L)
          (ξ : Section1.ClassFunction L) +
          ((a : ℂ) * (b : ℂ)) * Section1.scalarProduct L η₁ η₁ := by
    dsimp [χ0, ξ0]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hχY, hYξ, mul_assoc]
  have hiso : Section1.scalarProduct G (T χ0) (T ξ0) =
      Section1.scalarProduct L χ0 ξ0 :=
    h52b.1 χ0 ξ0 hχspan hξspan
  rw [hTχ, hTξ, hleft, hright, hself] at hiso
  exact add_right_cancel hiso

theorem theorem_6_8_caseA_signed_unionImage_gram
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L} [H.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf) :
    ∀ η ξ : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Section1.scalarProduct G
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η)
        (theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift ξ) =
        Section1.scalarProduct L
          (η : Section1.ClassFunction L) (ξ : Section1.ClassFunction L) := by
  intro η ξ
  have h52union' : Section5.hypothesis_5_2_statement (X ∪ Y) T := h52union
  rcases h52union with ⟨_hsetup, _R, h52a, _h52b, h52c, _h52d, _h52e⟩
  by_cases hηY : (η : Section1.ClassFunction L) ∈ Y
  · by_cases hξY : (ξ : Section1.ClassFunction L) ∈ Y
    · exact theorem_6_8_caseA_signed_unionImage_Y_Y_gram
        (W1 := W1) (hshift := hshift)
        hfamily h52a h52c hτ₁ hshape η ξ hηY hξY
    · have hξX : (ξ : Section1.ClassFunction L) ∈ X := by
        rcases Finset.mem_union.mp ξ.2 with hξX | hξY'
        · exact hξX
        · exact (hξY hξY').elim
      exact theorem_6_8_caseA_signed_unionImage_Y_X_gram
        (W1 := W1) hfamily hZcomm h52c hshape ξ η hξX hξY hηY
  · have hηX : (η : Section1.ClassFunction L) ∈ X := by
      rcases Finset.mem_union.mp η.2 with hηX | hηY'
      · exact hηX
      · exact (hηY hηY').elim
    by_cases hξY : (ξ : Section1.ClassFunction L) ∈ Y
    · exact theorem_6_8_caseA_signed_unionImage_X_Y_gram
        (W1 := W1) hfamily hZcomm h52c hshape η ξ hηX hηY hξY
    · have hξX : (ξ : Section1.ClassFunction L) ∈ X := by
        rcases Finset.mem_union.mp ξ.2 with hξX | hξY'
        · exact hξX
        · exact (hξY hξY').elim
      exact theorem_6_8_caseA_signed_unionImage_X_X_gram
        (W1 := W1) (hshift := hshift)
        hSbot hsemi hfamily hZcomm h52union' hτ₁ hshape η ξ hηX hξX

theorem theorem_6_8_caseA_signed_unionImage_agreesOnIntegerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {Tnew T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf)
    (hTnew : ∀ η : {η : Section1.ClassFunction L // η ∈ X ∪ Y},
      Tnew (η : Section1.ClassFunction L) =
        theorem_6_8_caseB_unionImage
          (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
          η₁ Ycf hshift η) :
    Section5.agreesOnIntegerSpanOn (X ∪ Y) Section5.puncturedSet T Tnew := by
  exact theorem_6_8_unionImage_agreesOnIntegerSpanOn_of_split
    (W1 := W1) (U := X ∪ Y) (Tnew := Tnew) (T := T)
    (η₁ := η₁) (Ycf := Ycf)
    (img := theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift)
    (theorem_6_8_caseA_signed_unionImage_split
      (hshift := hshift) hsemi hfamily hτ₁ hshape)
    hTnew

theorem theorem_6_8_caseA_union_coherent_of_signed_shift_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {η₁ : Section1.ClassFunction L}
    {Ycf : Section1.ClassFunction G}
    {hshift : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ X₁ : Section1.ClassFunction G,
        let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ - a • η₁) = X₁ - a • Ycf}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hshape : theorem_6_8_caseA_signedYShape (Y := Y) (τ₁ := τ₁) η₁ Ycf) :
    coherentFamily (X ∪ Y) T := by
  let img : {η : Section1.ClassFunction L // η ∈ X ∪ Y} →
      Section1.ClassFunction G :=
    theorem_6_8_caseB_unionImage
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₁ := τ₁)
      η₁ Ycf hshift
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  exact theorem_6_8_coherentFamily_of_hypothesis_5_2_and_image_family
    (U := X ∪ Y) (T := T) (img := img) h52union
    (theorem_6_8_caseA_signed_unionImage_virtual
      (hshift := hshift) hSbot hsemi hfamily h52union hτ₁ hshape)
    (theorem_6_8_caseA_signed_unionImage_gram
      (hshift := hshift) hSbot hsemi hfamily hZcomm h52union hτ₁ hshape)
    (fun Tnew hTnew =>
      theorem_6_8_caseA_signed_unionImage_agreesOnIntegerSpanOn
        (hshift := hshift) hsemi hfamily hτ₁ hshape hTnew)

theorem theorem_6_8_caseA_union_coherent_of_base_shift_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ χ₀ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hχ₀X : χ₀ ∈ X)
    (hmul : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀)
    (hbaseData :
      (∃ X₁ : Section1.ClassFunction G,
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
            X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
        ∃ η₂ : Section1.ClassFunction L,
          Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
            ∃ X₁ : Section1.ClassFunction G,
              orthogonalToTransformedFinset Y τ₁ X₁ ∧
                T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
                  X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • (-τ₁ η₂)) :
    coherentFamily (X ∪ Y) T := by
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have horthτ₂ : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      orthogonalToTransformedFinset Y τ₁ (τ₂ χ) := by
    intro χ hχX
    exact theorem_6_8_orthogonalToTransformedFinset_Y_of_X_extension
      hSbot hfamily hZcomm h52union hτ₂ hτ₁ hχX
  have hall :=
    theorem_6_8_caseA_shift_data_all_of_base_shift_data
      (W1 := W1) (X := X) (Y := Y) (T := T) (τ₂ := τ₂) (τ₁ := τ₁)
      (η₁ := η₁) (χ₀ := χ₀)
      hτ₂ hχ₀X horthτ₂ hmul hbaseData
  rcases hall with hleft | hright
  · exact theorem_6_8_caseA_union_coherent_of_signed_shift_data
      (W1 := W1) (Ycf := τ₁ η₁) (hshift := hleft)
      hSbot hsemi hfamily hZcomm h52union hτ₁
      ⟨hη₁Y, Or.inl rfl⟩
  · rcases hright with ⟨η₂, hcard, hη₂Y, hη₂ne, hshift⟩
    exact theorem_6_8_caseA_union_coherent_of_signed_shift_data
      (W1 := W1) (Ycf := -τ₁ η₂) (hshift := hshift)
      hSbot hsemi hfamily hZcomm h52union hτ₁
      ⟨hη₁Y, Or.inr ⟨η₂, hcard, hη₂Y, hη₂ne, rfl⟩⟩

theorem theorem_6_8_caseA_union_coherent_of_selected_base_shift_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    {η₁ : Section1.ClassFunction L}
    (hη₁Y : η₁ ∈ Y)
    (hXnonempty : X.Nonempty)
    (hbaseData : ∀ χ₀ : Section1.ClassFunction L, χ₀ ∈ X →
      (∀ χ : Section1.ClassFunction L, χ ∈ X →
        ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀) →
      (∃ X₁ : Section1.ClassFunction G,
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
            X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
        ∃ η₂ : Section1.ClassFunction L,
          Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
            ∃ X₁ : Section1.ClassFunction G,
              orthogonalToTransformedFinset Y τ₁ X₁ ∧
                T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
                  X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • (-τ₁ η₂)) :
    coherentFamily (X ∪ Y) T := by
  rcases theorem_6_8_caseA_exists_base_degree_multiple
      hSbot hfamily hpQ hXnonempty with
    ⟨χ₀, hχ₀X, hmul⟩
  exact theorem_6_8_caseA_union_coherent_of_base_shift_data
    hSbot hsemi hfamily hZcomm h52union hτ₂ hτ₁ hη₁Y hχ₀X hmul
    (hbaseData χ₀ hχ₀X hmul)

theorem theorem_6_8_exists_intermediate_degree_relIndex
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hunionS1 : X ∪ Y ⊆ S1) :
    ∃ η1 : S1,
      Section1.degree (η1 : Section1.ClassFunction L) =
        (H.relIndex (⊤ : Subgroup L) : ℂ) := by
  rcases theorem_6_8_exists_Y_degree_relIndex h68 hfamily with
    ⟨η, hηY, hηdeg⟩
  have hηS1 : η ∈ S1 := hunionS1 (Finset.mem_union.mpr (Or.inr hηY))
  exact ⟨⟨η, hηS1⟩, hηdeg⟩

theorem theorem_6_8_exists_intermediate_not_X_degree_relIndex
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (hunionS1 : X ∪ Y ⊆ S1) :
    ∃ η1 : S1,
      (η1 : Section1.ClassFunction L) ∉ X ∧
        Section1.degree (η1 : Section1.ClassFunction L) =
          (H.relIndex (⊤ : Subgroup L) : ℂ) := by
  rcases theorem_6_8_exists_Y_degree_relIndex h68 hfamily with
    ⟨η, hηY, hηdeg⟩
  have hηS1 : η ∈ S1 := hunionS1 (Finset.mem_union.mpr (Or.inr hηY))
  have hηnotX : η ∉ X :=
    theorem_6_8_familyData_not_mem_X_of_mem_Y hfamily hZcomm hηY
  exact ⟨⟨η, hηS1⟩, hηnotX, hηdeg⟩

public theorem theorem_6_8_coherentExtension_of_coherentFamily
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcoh : coherentFamily S T) :
    ∃ T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      coherentExtension S T T' := by
  rcases hcoh with ⟨_hsrc, _hnonempty, T', hIso, hvirt, hagree⟩
  exact ⟨T', hIso, hvirt, hagree⟩

theorem theorem_6_8_Y_coherentExtension_of_familyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∃ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      coherentExtension Y T τ₁ :=
  theorem_6_8_coherentExtension_of_coherentFamily
    (theorem_6_8_Y_coherent_of_familyData h68 hfamily)


theorem theorem_6_8_caseB_commonY_shift_data_of_projection
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    ∃ τ₁ η₁ Ycf,
      coherentExtension Y T τ₁ ∧ η₁ ∈ Y ∧
        theorem_6_8_2_2_commonY L H Z Y T τ₁ η₁ Ycf ∧
          ∀ χ : Section1.ClassFunction L, χ ∈ X →
            ∃ X₁ : Section1.ClassFunction G,
              let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
              orthogonalToTransformedFinset Y τ₁ X₁ ∧
                T (χ - a • η₁) = X₁ - a • Ycf := by
  rcases theorem_6_8_Y_coherentExtension_of_familyData h68 hfamily with
    ⟨τ₁, hτ₁⟩
  rcases theorem_6_8_exists_Y_degree_relIndex h68 hfamily with
    ⟨η₁, hη₁Y, _hη₁deg⟩
  rcases theorem_6_8_2_2_of_norm_bound_caseB_familyData
      h68 hpQ hcase hB hfamily hτ₁ hη₁Y with
    ⟨Ycf, hcommon⟩
  have h823 :
      theorem_6_8_2_3_statement L H W1 W2 W Z S SZ X Y T τ₁ η₁ Ycf :=
    theorem_6_8_2_3_of_projection_caseB_familyData h52union hτ₁
  have hshift :
      ∀ χ : Section1.ClassFunction L, χ ∈ X →
        ∃ X₁ : Section1.ClassFunction G,
          let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
          orthogonalToTransformedFinset Y τ₁ X₁ ∧
            T (χ - a • η₁) = X₁ - a • Ycf :=
    h823 h68 hpQ hcase hB hfamily hcommon
  exact ⟨τ₁, η₁, Ycf, hτ₁, hη₁Y, hcommon, hshift⟩

theorem theorem_6_8_caseB_union_coherent_of_projection
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    coherentFamily (X ∪ Y) T := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases theorem_6_8_caseB_commonY_shift_data_of_projection
      h52union h68' hpQ hcase hB hfamily with
    ⟨τ₁, η₁, Ycf, hτ₁, _hη₁Y, hcommon, hshift⟩
  have hZcomm : Z ≤ ⁅H,H⁆ := by
    rcases hB with ⟨_hW2ne, _hW2center, hW2comm, hZeq⟩
    rw [hZeq]
    exact hW2comm
  exact theorem_6_8_caseB_union_coherent_of_commonY_data
    (hshift := hshift) hSbot hsemi hfamily hZcomm h52union hτ₁ hcommon


theorem theorem_6_8_union_eq_S_of_Z_eq_commutator
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZeq : Z = ⁅H,H⁆) :
    X ∪ Y = S := by
  rcases hfamily with ⟨_hZH, hSZ, hXeq, hY⟩
  subst Z
  have hSZeqY : SZ = Y := by
    apply Finset.ext
    intro χ
    exact (hSZ.2 χ).trans (hY.2 χ).symm
  have hSZsubS : SZ ⊆ S := inducedKernelFamily_subset_base hSbot hSZ
  subst X
  rw [← hSZeqY]
  ext χ
  by_cases hχSZ : χ ∈ SZ
  · simp [hχSZ, hSZsubS hχSZ]
  · simp [hχSZ]

theorem theorem_6_8_Z_ne_commutator_of_not_coherent
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hunion : coherentFamily (X ∪ Y) T)
    (hnotS : ¬ coherentFamily S T) :
    Z ≠ ⁅H,H⁆ := by
  intro hZeq
  have hEq : X ∪ Y = S :=
    theorem_6_8_union_eq_S_of_Z_eq_commutator
      (H := H) (Z := Z) (S := S) (SZ := SZ) (X := X) (Y := Y)
      hSbot hfamily hZeq
  exact hnotS (by simpa [hEq] using hunion)

theorem theorem_6_8_Z_le_commutator_of_caseData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : theorem_6_8_caseAData H W2 Z ∨
      (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z)) :
    Z ≤ ⁅H,H⁆ := by
  rcases hcase with hA | hB
  · rcases hA with ⟨_hcentW2, hZeq⟩
    rw [hZeq]
    exact inf_le_right
  · rcases hB with ⟨_hcaseC2, hBdata⟩
    rcases hBdata with ⟨_hW2ne, _hW2center, hW2comm, hZeq⟩
    rw [hZeq]
    exact hW2comm

theorem theorem_6_8_endpoint_basic_inputs_of_not_coherent
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : theorem_6_8_caseAData H W2 Z ∨
      (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z))
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hunion : coherentFamily (X ∪ Y) T)
    (hnotS : ¬ coherentFamily S T) :
    Section5.hypothesis_5_2_statement S T ∧
      inducedKernelFamily H ⊥ S ∧
        Z.Normal ∧ Z ≤ ⁅H,H⁆ ∧ Z ≠ ⁅H,H⁆ := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h52 : Section5.hypothesis_5_2_statement S T :=
    theorem_6_8_hypothesis_5_2_of_branch h68'
  have hZnorm : Z.Normal :=
    (theorem_6_8_Z_center_normal_ne_bot_of_caseData h68' hpQ hcase).2.2
  have hZcomm : Z ≤ ⁅H,H⁆ :=
    theorem_6_8_Z_le_commutator_of_caseData hcase
  have hZneComm : Z ≠ ⁅H,H⁆ :=
    theorem_6_8_Z_ne_commutator_of_not_coherent
      hSbot hfamily hunion hnotS
  exact ⟨h52, hSbot, hZnorm, hZcomm, hZneComm⟩

theorem theorem_6_8_mem_SZ_of_mem_S_not_union
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotUnion : χ ∉ X ∪ Y) :
    χ ∈ SZ := by
  classical
  rcases hfamily with ⟨_hZH, _hSZ, hXeq, _hY⟩
  have hχnotX : χ ∉ X := by
    intro hχX
    exact hχnotUnion (Finset.mem_union.mpr (Or.inl hχX))
  by_contra hχnotSZ
  have hχX : χ ∈ X := by
    have hχdiff : χ ∈ S \ SZ := Finset.mem_sdiff.mpr ⟨hχS, hχnotSZ⟩
    simpa [hXeq] using hχdiff
  exact hχnotX hχX

theorem theorem_6_8_inducing_character_of_mem_S_not_union
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotUnion : χ ∉ X ∪ Y) :
    ∃ θ : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.subgroupInKernel' θ (Z.subgroupOf H) ∧
          θ ≠ Section1.principalCharacter H ∧
            χ = Section1.inducedCF H θ := by
  have hχSZ : χ ∈ SZ :=
    theorem_6_8_mem_SZ_of_mem_S_not_union hfamily hχS hχnotUnion
  rcases hfamily with ⟨_hZH, hSZ, _hXeq, _hY⟩
  exact (hSZ.2 χ).mp hχSZ

theorem theorem_6_8_inducing_character_not_commutator_kernel_of_mem_S_not_union
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotUnion : χ ∉ X ∪ Y) :
    ∃ θ : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.subgroupInKernel' θ (Z.subgroupOf H) ∧
          ¬ Section1.subgroupInKernel' θ ((⁅H,H⁆).subgroupOf H) ∧
            θ ≠ Section1.principalCharacter H ∧
              χ = Section1.inducedCF H θ := by
  rcases theorem_6_8_inducing_character_of_mem_S_not_union
      hfamily hχS hχnotUnion with
    ⟨θ, hθirr, hθZ, hθne, hχeq⟩
  rcases hfamily with ⟨_hZH, _hSZ, _hXeq, hY⟩
  have hχnotY : χ ∉ Y := by
    intro hχY
    exact hχnotUnion (Finset.mem_union.mpr (Or.inr hχY))
  have hθnotComm :
      ¬ Section1.subgroupInKernel' θ ((⁅H,H⁆).subgroupOf H) := by
    intro hθcomm
    have hχY : χ ∈ Y := (hY.2 χ).mpr ⟨θ, hθirr, hθcomm, hθne, hχeq⟩
    exact hχnotY hχY
  exact ⟨θ, hθirr, hθZ, hθnotComm, hθne, hχeq⟩

theorem theorem_6_8_irreducible_degree_sq_le_relIndex_of_kernel
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L}
    (hZnorm : Z.Normal)
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθZ : Section1.subgroupInKernel' θ (Z.subgroupOf H)) :
    ∃ d : ℕ,
      Section1.degree θ = (d : ℂ) ∧ d ^ (2 : ℕ) ≤ Z.relIndex H := by
  classical
  let : (Z.subgroupOf H).Normal := hZnorm.subgroupOf H
  rcases hθirr with ⟨d, ρ, hρirr, hθeq⟩
  refine ⟨d, ?_, ?_⟩
  · rw [hθeq, Section1.degree_representation_character]
    simp
  · let q : H →* H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H)
    have hθkerρ : Section1.subgroupInKernel' ρ.character (Z.subgroupOf H) := by
      simpa [hθeq] using hθZ
    have hker : Section1.subgroupInRepresentationKernel ρ (Z.subgroupOf H) :=
      (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
        (Z.subgroupOf H)).mp hθkerρ
    let ρq : Representation ℂ (H ⧸ Z.subgroupOf H) (Fin d → ℂ) :=
      Section1.quotientRepresentationOfKernelSubgroup ρ (Z.subgroupOf H) hker
    have hcomp_eq : ρq.comp q = ρ := by
      apply MonoidHom.ext
      intro h
      exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
        (Z.subgroupOf H) hker h
    have hρqirr : Representation.IsIrreducible ρq := by
      apply representation_isIrreducible_of_comp_surjective ρq q
        (QuotientGroup.mk'_surjective (Z.subgroupOf H))
      simpa [hcomp_eq] using hρirr
    have : Representation.IsIrreducible ρq := hρqirr
    have hscalar :
        ∀ z : (⊥ : Subgroup (H ⧸ Z.subgroupOf H)),
          ∃ a : ℂ, ρq z = a • (1 : Module.End ℂ (Fin d → ℂ)) := by
      intro z
      refine ⟨1, ?_⟩
      have hz : (z : H ⧸ Z.subgroupOf H) = 1 := Subgroup.mem_bot.mp z.2
      ext v i
      simp [hz]
    have hle :
        Module.finrank ℂ (Fin d → ℂ) ^ (2 : ℕ) ≤
          (⊥ : Subgroup (H ⧸ Z.subgroupOf H)).index :=
      Theory.Character.irreducible_finrank_sq_le_index_of_scalar_on_subgroup
        (ρ := ρq) (⊥ : Subgroup (H ⧸ Z.subgroupOf H)) hscalar
    have hleQbot :
        d ^ (2 : ℕ) ≤
          Fintype.card ((H ⧸ Z.subgroupOf H) ⧸
            (⊥ : Subgroup (H ⧸ Z.subgroupOf H))) := by
      simpa [Subgroup.index_eq_card] using hle
    have hcardQbot :
        Fintype.card ((H ⧸ Z.subgroupOf H) ⧸
            (⊥ : Subgroup (H ⧸ Z.subgroupOf H))) =
          Fintype.card (H ⧸ Z.subgroupOf H) := by
      exact Fintype.card_congr (QuotientGroup.quotientBot :
        ((H ⧸ Z.subgroupOf H) ⧸ (⊥ : Subgroup (H ⧸ Z.subgroupOf H))) ≃*
          (H ⧸ Z.subgroupOf H))
    have hleQ : d ^ (2 : ℕ) ≤ Fintype.card (H ⧸ Z.subgroupOf H) := by
      simpa [hcardQbot] using hleQbot
    simpa [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card] using hleQ

theorem theorem_6_8_obstruction_degree_data_of_mem_S_not_union
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    (hZnorm : Z.Normal)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S)
    (hχnotUnion : χ ∉ X ∪ Y) :
    ∃ θ : Section1.ClassFunction H,
      ∃ d dχ : ℕ,
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          Section1.subgroupInKernel' θ (Z.subgroupOf H) ∧
            ¬ Section1.subgroupInKernel' θ ((⁅H,H⁆).subgroupOf H) ∧
              θ ≠ Section1.principalCharacter H ∧
                χ = Section1.inducedCF H θ ∧
                  Section1.degree θ = (d : ℂ) ∧
                    d ^ (2 : ℕ) ≤ Z.relIndex H ∧
                      Section1.degree χ = (dχ : ℂ) ∧
                        dχ = H.relIndex (⊤ : Subgroup L) * d := by
  rcases theorem_6_8_inducing_character_not_commutator_kernel_of_mem_S_not_union
      hfamily hχS hχnotUnion with
    ⟨θ, hθirr, hθZ, hθnotComm, hθne, hχeq⟩
  rcases theorem_6_8_irreducible_degree_sq_le_relIndex_of_kernel
      hZnorm hθirr hθZ with
    ⟨d, hθdeg, hdsq⟩
  let dχ : ℕ := H.relIndex (⊤ : Subgroup L) * d
  have hχdeg : Section1.degree χ = (dχ : ℂ) := by
    rw [hχeq, Section1.degree_inducedClassFunction H θ, hθdeg]
    simp [dχ, Subgroup.relIndex_top_right, Nat.cast_mul]
  exact ⟨θ, d, dχ, hθirr, hθZ, hθnotComm, hθne, hχeq, hθdeg, hdsq,
    hχdeg, rfl⟩

theorem theorem_6_8_intermediate_degree_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H : Subgroup L}
    {S S1 : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hS1sub : S1 ⊆ S) :
    ∃ dS1 : S1 → ℕ,
      ∀ η : S1,
        Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ) := by
  classical
  have hdegree : ∀ η : S1,
      ∃ dη : ℕ,
        Section1.degree (η : Section1.ClassFunction L) = (dη : ℂ) := by
    intro η
    rcases inducedKernelFamily_degree_data hSbot (hS1sub η.2) with
      ⟨_dθ, dη, hηdeg, _hηmul, _hηdvd⟩
    exact ⟨dη, hηdeg⟩
  exact ⟨fun η => Classical.choose (hdegree η),
    fun η => Classical.choose_spec (hdegree η)⟩

theorem theorem_6_8_pf56_numeric_obstruction_of_mem_S_not_union
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hZnorm : Z.Normal)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hS1sub : S1 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (hS1coh : coherentFamily S1 T)
    {ψ : Section1.ClassFunction L}
    (hψS : ψ ∈ S)
    (hψnotS1 : ψ ∉ S1)
    (hψnotUnion : ψ ∉ X ∪ Y)
    (hnotPair : ¬ coherentFamily
      (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
        Finset (Section1.ClassFunction L))) T)
    (η1 : S1)
    (hηdeg : Section1.degree (η1 : Section1.ClassFunction L) =
      (H.relIndex (⊤ : Subgroup L) : ℂ))
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ η : S1,
      Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ)) :
    ∃ d dψ : ℕ,
      d ^ (2 : ℕ) ≤ Z.relIndex H ∧
        Section1.degree ψ = (dψ : ℂ) ∧
          dψ = H.relIndex (⊤ : Subgroup L) * d ∧
            (∑ η : S1,
              (((dS1 η : ℝ) ^ (2 : ℕ)) /
                Section5.cfNormSq (η : Section1.ClassFunction L))) ≤
              2 * (dψ : ℝ) *
                (H.relIndex (⊤ : Subgroup L) : ℝ) := by
  classical
  rcases theorem_6_8_obstruction_degree_data_of_mem_S_not_union
      hZnorm hfamily hψS hψnotUnion with
    ⟨_θ, d, dψ, _hθirr, _hθZ, _hθnotComm, _hθne, _hψeq, _hθdeg,
      hdsq, hψdeg, hdψ⟩
  have hψbarNotS1 :
      Section1.conjugateCharacter ψ ∉ S1 := by
    intro hψbarS1
    have hψS1 : ψ ∈ S1 := by
      have hconj := hS1closed (Section1.conjugateCharacter ψ) hψbarS1
      have hconj_eq :
          Section1.conjugateCharacter (Section1.conjugateCharacter ψ) = ψ := by
        ext g
        simp [Section1.conjugateCharacter]
      simpa [hconj_eq] using hconj
    exact hψnotS1 hψS1
  have hdvd : H.relIndex (⊤ : Subgroup L) ∣ dψ := by
    exact ⟨d, hdψ⟩
  let : Fintype L := Fintype.ofFinite L
  let ψS : S := ⟨ψ, hψS⟩
  have hnotPair' : ¬ coherentFamily
      (S1 ∪ ({(ψS : Section1.ClassFunction L),
        Section1.conjugateCharacter (ψS : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L))) T := by
    intro hcoh
    apply hnotPair
    convert hcoh using 1
    ext χ
    simp [ψS]
  have hineq :=
    theorem_6_2_pf56_numeric_obstruction
      (L := L) (G := G) (S := S) (S1 := S1) (T := T)
      h52 hS1sub hS1closed ψS hψbarNotS1 η1
      hS1coh hnotPair' hηdeg hψdeg hdvd dS1 hdS1
  exact ⟨d, dψ, hdsq, hψdeg, hdψ, hineq⟩

theorem theorem_6_8_pf56_numeric_obstruction_with_degree_data
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hZnorm : Z.Normal)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hS1sub : S1 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (hS1coh : coherentFamily S1 T)
    {ψ : Section1.ClassFunction L}
    (hψS : ψ ∈ S)
    (hψnotS1 : ψ ∉ S1)
    (hψnotUnion : ψ ∉ X ∪ Y)
    (hnotPair : ¬ coherentFamily
      (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
        Finset (Section1.ClassFunction L))) T)
    (η1 : S1)
    (hηdeg : Section1.degree (η1 : Section1.ClassFunction L) =
      (H.relIndex (⊤ : Subgroup L) : ℂ)) :
    ∃ dS1 : S1 → ℕ,
      (∀ η : S1,
        Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ)) ∧
        ∃ d dψ : ℕ,
          d ^ (2 : ℕ) ≤ Z.relIndex H ∧
            Section1.degree ψ = (dψ : ℂ) ∧
              dψ = H.relIndex (⊤ : Subgroup L) * d ∧
                (∑ η : S1,
                  (((dS1 η : ℝ) ^ (2 : ℕ)) /
                    Section5.cfNormSq (η : Section1.ClassFunction L))) ≤
                  2 * (dψ : ℝ) *
                    (H.relIndex (⊤ : Subgroup L) : ℝ) := by
  rcases theorem_6_8_intermediate_degree_data hSbot hS1sub with
    ⟨dS1, hdS1⟩
  rcases theorem_6_8_pf56_numeric_obstruction_of_mem_S_not_union
      h52 hZnorm hfamily hS1sub hS1closed hS1coh
      hψS hψnotS1 hψnotUnion hnotPair η1 hηdeg dS1 hdS1 with
    ⟨d, dψ, hdsq, hψdeg, hdψ, hineq⟩
  exact ⟨dS1, hdS1, d, dψ, hdsq, hψdeg, hdψ, hineq⟩

theorem theorem_6_8_scalarProduct_self_irreducible
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct L χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρirr, hχchar⟩
  rw [hχchar]
  exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr


theorem theorem_6_8_X_degree_sq_sum_add_quotient_card
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ)) :
    (∑ χ : X, dX χ ^ (2 : ℕ)) + Nat.card (L ⧸ Z) = Nat.card L :=
  theorem_6_6_Xset_sum_degree_sq_add_quotient_card hXchar dX hdegX

theorem theorem_6_8_X_weighted_degree_sum_apply_one
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ)) :
      Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
        (fun χ : X => (χ : Section1.ClassFunction L)) (1 : L) =
      (Nat.card L : ℂ) - (Nat.card (L ⧸ Z) : ℂ) := by
  rw [Section1.weightedFamilySum]
  have huniv : (@Finset.univ X (Fintype.ofFinite X)) =
      (@Finset.univ X (Finset.Subtype.fintype X)) := by
    ext χ
    simp
  rw [huniv]
  exact theorem_6_6_Xset_weighted_degree_sum_eq_card_sub_quotient_at_one
    hXchar dX hdegX

theorem theorem_6_8_X_weighted_degree_sum_apply_mem_Z_ne_one
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    (z : Z) (hz : z ≠ 1) :
      Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
        (fun χ : X => (χ : Section1.ClassFunction L)) (z : L) =
      - (Nat.card (L ⧸ Z) : ℂ) := by
  rw [Section1.weightedFamilySum]
  have huniv : (@Finset.univ X (Fintype.ofFinite X)) =
      (@Finset.univ X (Finset.Subtype.fintype X)) := by
    ext χ
    simp
  rw [huniv]
  exact theorem_6_6_Xset_weighted_degree_sum_eq_neg_quotient_card_of_mem_Z_ne_one
    hXchar dX hdegX z hz

theorem theorem_6_8_isClassFunction_weightedFamilySum
    {G : Type u} [Group G]
    {ι : Type*} [Finite ι]
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (hφ : ∀ i : ι, Section1.IsClassFunction (φ i)) :
    Section1.IsClassFunction (Section1.weightedFamilySum w φ) := by
  classical
  intro x g
  rw [Section1.weightedFamilySum]
  exact Finset.sum_congr rfl fun i _hi => by
    simp [hφ i x g]

theorem theorem_6_8_X_weighted_degree_sum_scalarProduct
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ) (χ : X) :
    Section1.scalarProduct L
      (Section1.weightedFamilySum (fun ξ : X => (dX ξ : ℂ))
        (fun ξ : X => (ξ : Section1.ClassFunction L)))
      (χ : Section1.ClassFunction L) = (dX χ : ℂ) := by
  classical
  have horth : ∀ i j : X,
      Section1.scalarProduct L (i : Section1.ClassFunction L)
        (j : Section1.ClassFunction L) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact theorem_6_8_scalarProduct_self_irreducible
        ((hXchar (i : Section1.ClassFunction L)).1 i.2).1
    · have hi : Section1.IsIrreducibleCharacterOnGroup
          (i : Section1.ClassFunction L) :=
        ((hXchar (i : Section1.ClassFunction L)).1 i.2).1
      have hj : Section1.IsIrreducibleCharacterOnGroup
          (j : Section1.ClassFunction L) :=
        ((hXchar (j : Section1.ClassFunction L)).1 j.2).1
      have hne : (i : Section1.ClassFunction L) ≠
          (j : Section1.ClassFunction L) := by
        intro h
        exact hij (Subtype.ext h)
      rcases hi with ⟨ni, ρi, hρi, hiEq⟩
      rcases hj with ⟨nj, ρj, hρj, hjEq⟩
      rw [if_neg hij]
      exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
        (i : Section1.ClassFunction L) (j : Section1.ClassFunction L) ρi ρj
        hiEq hjEq hρi hρj hne
  exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
    (fun ξ : X => (dX ξ : ℂ))
    (fun ξ : X => (ξ : Section1.ClassFunction L)) horth χ

theorem theorem_6_8_caseA_source_residual_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    {ψ : Section1.ClassFunction L}
    (hψclass : Section1.IsClassFunction ψ)
    (χ₀ : X) {c : ℂ}
    (hcstar : star c = c)
    (hdeg0_ne : (dX χ₀ : ℂ) ≠ 0)
    (hcoeff : ∀ χ : X,
      Section1.scalarProduct L (χ : Section1.ClassFunction L) ψ =
        ((dX χ : ℂ) / (dX χ₀ : ℂ)) * c) :
    Section1.subgroupInKernel'
      (ψ - (c / (dX χ₀ : ℂ)) •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z := by
  classical
  let W : Section1.ClassFunction L :=
    Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
      (fun χ : X => (χ : Section1.ClassFunction L))
  have hWclass : Section1.IsClassFunction W := by
    dsimp [W]
    exact theorem_6_8_isClassFunction_weightedFamilySum
      (fun χ : X => (dX χ : ℂ))
      (fun χ : X => (χ : Section1.ClassFunction L))
      (fun χ => Section1.isCharacter_isClassFunction
        (χ : Section1.ClassFunction L)
        (theorem_6_8_isCharacter_of_irreducible
          ((hXchar (χ : Section1.ClassFunction L)).1 χ.2).1))
  have hφclass : Section1.IsClassFunction
      (ψ - (c / (dX χ₀ : ℂ)) • W) := by
    intro x g
    change ψ (x * g * x⁻¹) -
        (c / (dX χ₀ : ℂ)) * W (x * g * x⁻¹) =
      ψ g - (c / (dX χ₀ : ℂ)) * W g
    rw [hψclass x g, hWclass x g]
  have horth : ∀ χ : X,
      Section1.scalarProduct L (ψ - (c / (dX χ₀ : ℂ)) • W)
        (χ : Section1.ClassFunction L) = 0 := by
    intro χ
    have hψχ : Section1.scalarProduct L ψ
        (χ : Section1.ClassFunction L) =
          ((dX χ : ℂ) / (dX χ₀ : ℂ)) * c := by
      calc
        Section1.scalarProduct L ψ (χ : Section1.ClassFunction L) =
            star (Section1.scalarProduct L
              (χ : Section1.ClassFunction L) ψ) := by
          exact (Section1.scalarProduct_star_swap (G := L)
            (phi := ψ) (psi := (χ : Section1.ClassFunction L))).symm
        _ = star (((dX χ : ℂ) / (dX χ₀ : ℂ)) * c) := by
          rw [hcoeff χ]
        _ = ((dX χ : ℂ) / (dX χ₀ : ℂ)) * c := by
          simp [hcstar]
    have hWχ : Section1.scalarProduct L W
        (χ : Section1.ClassFunction L) = (dX χ : ℂ) := by
      dsimp [W]
      exact theorem_6_8_X_weighted_degree_sum_scalarProduct hXchar dX χ
    rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left,
      hψχ, hWχ]
    field_simp [hdeg0_ne]
    ring
  simpa [W] using theorem_6_6_orthogonal_Xset_complement_subgroupInKernel
    hXchar hφclass horth

theorem theorem_6_8_sub_values_of_residual_kernel_weighted_X
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {ψ : Section1.ClassFunction L} {A : ℂ}
    (hker : Section1.subgroupInKernel'
      (ψ - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1) :
    ψ 1 - ψ (z : L) = A * (Nat.card L : ℂ) := by
  classical
  let W : Section1.ClassFunction L :=
    Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
      (fun χ : X => (χ : Section1.ClassFunction L))
  have hker' : Section1.subgroupInKernel' (ψ - A • W) Z := by
    simpa [W] using hker
  have hkerz :
      (ψ - A • W) (z : L) = (ψ - A • W) (1 : L) := by
    exact (hker' z).trans (hker' (1 : Z)).symm
  have hW1 : W (1 : L) =
      (Nat.card L : ℂ) - (Nat.card (L ⧸ Z) : ℂ) := by
    dsimp [W]
    exact theorem_6_8_X_weighted_degree_sum_apply_one hXchar dX hdegX
  have hWz : W (z : L) = - (Nat.card (L ⧸ Z) : ℂ) := by
    dsimp [W]
    exact theorem_6_8_X_weighted_degree_sum_apply_mem_Z_ne_one
      hXchar dX hdegX z hz
  have hsub : ψ 1 - ψ (z : L) = A * (W 1 - W (z : L)) := by
    have hψ1 : ψ 1 = ψ (z : L) - A * W (z : L) + A * W 1 := by
      have h := hkerz
      change ψ (z : L) - A * W (z : L) = ψ 1 - A * W 1 at h
      calc
        ψ 1 = (ψ 1 - A * W 1) + A * W 1 := by ring
        _ = (ψ (z : L) - A * W (z : L)) + A * W 1 := by rw [← h]
        _ = ψ (z : L) - A * W (z : L) + A * W 1 := by ring
    rw [hψ1]
    ring
  have hWdiff : W 1 - W (z : L) = (Nat.card L : ℂ) := by
    rw [hW1, hWz]
    ring
  rw [hsub, hWdiff]

theorem theorem_6_8_constantOnNonidentitySubgroup_of_residual_kernel_weighted_X
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {ψ : Section1.ClassFunction L} {A : ℂ}
    (hker : Section1.subgroupInKernel'
      (ψ - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z) :
    constantOnNonidentitySubgroup Z ψ := by
  intro z1 z2 hz1 hz2
  have h1 :
      ψ 1 - ψ (z1 : L) = A * (Nat.card L : ℂ) :=
    theorem_6_8_sub_values_of_residual_kernel_weighted_X
      hXchar dX hdegX hker z1 hz1
  have h2 :
      ψ 1 - ψ (z2 : L) = A * (Nat.card L : ℂ) :=
    theorem_6_8_sub_values_of_residual_kernel_weighted_X
      hXchar dX hdegX hker z2 hz2
  calc
    ψ (z1 : L) = ψ 1 - (ψ 1 - ψ (z1 : L)) := by ring
    _ = ψ 1 - A * (Nat.card L : ℂ) := by rw [h1]
    _ = ψ 1 - (ψ 1 - ψ (z2 : L)) := by rw [h2]
    _ = ψ (z2 : L) := by ring

theorem theorem_6_8_regular_add_restrictions_of_residual_kernel_subtypeMap
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {ψ : Section1.ClassFunction G} {A : ℂ}
    (hker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction L ψ - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z0 : Z) (hz0 : z0 ≠ 1) :
    constantOnNonidentitySubgroup (Z.map L.subtype) ψ ∧
      ∃ regularCoeff b : ℂ,
        Section1.subgroupRestriction (Z.map L.subtype) ψ =
            regularCoeff • regularCharacter (Z.map L.subtype) +
              b • Section1.principalCharacter (Z.map L.subtype) ∧
          Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ) =
            regularCoeff • regularCharacter Z +
              b • Section1.principalCharacter Z := by
  have hconstLocal :
      constantOnNonidentitySubgroup Z
        (Section1.subgroupRestriction L ψ) :=
    theorem_6_8_constantOnNonidentitySubgroup_of_residual_kernel_weighted_X
      hXchar dX hdegX hker
  have hconstMap :
      constantOnNonidentitySubgroup (Z.map L.subtype) ψ :=
    theorem_6_8_constantOnNonidentitySubgroup_subtypeMap_of_local
      hconstLocal
  let zmap : Z.map L.subtype := (theorem_6_8_subtypeMapEquiv L Z) z0
  have hzmap : zmap ≠ 1 := by
    intro hzmap
    apply hz0
    have := congrArg (theorem_6_8_subtypeMapEquiv L Z).symm hzmap
    simpa [zmap] using this
  rcases constantOnNonidentitySubgroup_restriction_eq_regular_add
      hconstMap zmap hzmap with
    ⟨regularCoeff, b, hresMap⟩
  have hresLocal :
      Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ) =
        regularCoeff • regularCharacter Z +
          b • Section1.principalCharacter Z :=
    theorem_6_8_regular_add_local_of_subtypeMap hresMap
  exact ⟨hconstMap, regularCoeff, b, hresMap, hresLocal⟩

theorem theorem_6_8_regular_coeff_ratio_link_of_residual_sub_values
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L} [Z.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hZH : Z ≤ H)
    {ψ : Section1.ClassFunction L}
    {regularCoeff b ratio c A : ℂ}
    (hres : Section1.subgroupRestriction Z ψ =
      regularCoeff • regularCharacter Z + b • Section1.principalCharacter Z)
    (z : Z) (hz : z ≠ 1)
    (hsub : ψ 1 - ψ (z : L) = A * (Nat.card L : ℂ))
    (hscale : A * (Nat.card W1 : ℂ) * ratio = c) :
    regularCoeff * ratio = (Z.relIndex H : ℂ) * c := by
  have hcardL_nat : Nat.card L = Nat.card (L ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hquot_nat : Nat.card (L ⧸ Z) =
      Z.relIndex H * Nat.card W1 := by
    have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
    have hquot0 : Nat.card (L ⧸ Z) =
        Z.relIndex H * H.relIndex (⊤ : Subgroup L) := by
      rw [← Subgroup.index_eq_card Z]
      have hrel := Subgroup.relIndex_mul_index hZH
      simpa [Subgroup.relIndex_top_right] using hrel.symm
    rw [hquot0, hHindex]
  have hcardL : (Nat.card L : ℂ) =
      (Nat.card (L ⧸ Z) : ℂ) * (Nat.card Z : ℂ) := by
    exact_mod_cast hcardL_nat
  have hquot : (Nat.card (L ⧸ Z) : ℂ) =
      (Z.relIndex H : ℂ) * (Nat.card W1 : ℂ) := by
    exact_mod_cast hquot_nat
  have hZcard_ne : (Nat.card Z : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Z)).ne'
  calc
    regularCoeff * ratio =
        ((ψ 1 - ψ (z : L)) / (Nat.card Z : ℂ)) * ratio := by
          rw [theorem_6_8_regular_add_coefficient_eq_sub_values hres z hz]
    _ = ((A * (Nat.card L : ℂ)) / (Nat.card Z : ℂ)) * ratio := by
          rw [hsub]
    _ = ((A * ((Nat.card (L ⧸ Z) : ℂ) * (Nat.card Z : ℂ))) /
          (Nat.card Z : ℂ)) * ratio := by
          rw [hcardL]
    _ = (A * (Nat.card (L ⧸ Z) : ℂ)) * ratio := by
          field_simp [hZcard_ne]
    _ = (A * ((Z.relIndex H : ℂ) * (Nat.card W1 : ℂ))) * ratio := by
          rw [hquot]
    _ = (Z.relIndex H : ℂ) * (A * (Nat.card W1 : ℂ) * ratio) := by
          ring
    _ = (Z.relIndex H : ℂ) * c := by
          rw [hscale]

theorem theorem_6_8_scale_identity_of_div_eq_mul
    {A c d ratio w : ℂ}
    (hd_ne : d ≠ 0)
    (hA : A = c / d)
    (hd : d = ratio * w) :
    A * w * ratio = c := by
  rw [hA]
  have hmul_ne : ratio * w ≠ 0 := by
    simpa [hd] using hd_ne
  have hratio_ne : ratio ≠ 0 := left_ne_zero_of_mul hmul_ne
  have hw_ne : w ≠ 0 := right_ne_zero_of_mul hmul_ne
  rw [hd]
  field_simp [hratio_ne, hw_ne]

theorem theorem_6_8_caseA_regular_coeff_link_of_residual_kernel
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hZH : Z ≤ H)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {ψ : Section1.ClassFunction L}
    {regularCoeff b ratio c A : ℂ}
    (hres : Section1.subgroupRestriction Z ψ =
      regularCoeff • regularCharacter Z + b • Section1.principalCharacter Z)
    (χ₀ : X)
    (hA : A = c / (dX χ₀ : ℂ))
    (hdeg0_ne : (dX χ₀ : ℂ) ≠ 0)
    (hratio : (dX χ₀ : ℂ) = ratio * (Nat.card W1 : ℂ))
    (hker : Section1.subgroupInKernel'
      (ψ - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1) :
    regularCoeff * ratio = (Z.relIndex H : ℂ) * c := by
  have hsub : ψ 1 - ψ (z : L) = A * (Nat.card L : ℂ) :=
    theorem_6_8_sub_values_of_residual_kernel_weighted_X
      hXchar dX hdegX hker z hz
  have hscale : A * (Nat.card W1 : ℂ) * ratio = c :=
    theorem_6_8_scale_identity_of_div_eq_mul hdeg0_ne hA hratio
  exact theorem_6_8_regular_coeff_ratio_link_of_residual_sub_values
    hsemi hZH hres z hz hsub hscale


theorem theorem_6_8_caseA_source_coeff_multiple_of_residual_kernel_pf67_ambient
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 : Subgroup G)
    {H W1 Z : Subgroup L} [Z.Normal]
    {X : Finset (Section1.ClassFunction L)}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hZH : Z ≤ H)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {ψ : Section1.ClassFunction G}
    {regularCoeff b ratio c A : ℂ}
    (hbase : theorem_6_7_base_hypothesis p P L0 (Z.map L.subtype))
    (hsigned : Section3.IsSignedIrreducibleCharacter ψ)
    (hconst : constantOnNonidentitySubgroup (Z.map L.subtype) ψ)
    (hresMap : Section1.subgroupRestriction (Z.map L.subtype) ψ =
      regularCoeff • regularCharacter (Z.map L.subtype) +
        b • Section1.principalCharacter (Z.map L.subtype))
    (hresLocal :
      Section1.subgroupRestriction Z (Section1.subgroupRestriction L ψ) =
        regularCoeff • regularCharacter Z + b • Section1.principalCharacter Z)
    (χ₀ : X)
    (hA : A = c / (dX χ₀ : ℂ))
    (hdeg0_ne : (dX χ₀ : ℂ) ≠ 0)
    (hratio : (dX χ₀ : ℂ) = ratio * (Nat.card W1 : ℂ))
    (hker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction L ψ - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1)
    (hfactor : Nat.card (P : Subgroup G) =
      Nat.card (Z.map L.subtype) * Z.relIndex H) :
    ∃ k : ℤ, c = ratio * ((k : ℤ) : ℂ) := by
  let zmap : Z.map L.subtype := (theorem_6_8_subtypeMapEquiv L Z) z
  have hzmap : zmap ≠ 1 := by
    intro hzmap
    apply hz
    apply Subtype.ext
    apply L.subtype_injective
    exact congrArg (fun x : Z.map L.subtype => (x : G)) hzmap
  have hlink : regularCoeff * ratio = (Z.relIndex H : ℂ) * c :=
    theorem_6_8_caseA_regular_coeff_link_of_residual_kernel
      hsemi hZH hXchar dX hdegX hresLocal χ₀ hA hdeg0_ne hratio hker z hz
  exact theorem_6_8_source_coeff_multiple_of_pf67_signed_regular_add
    P L0 (Z.map L.subtype) hbase hsigned hconst hresMap zmap hzmap
    hfactor hlink


theorem theorem_6_8_caseA_anchor_multiple_of_residual_kernel_pf67_ambient
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 : Subgroup G)
    {H W1 W2 W Z : Subgroup L} [Z.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hτ₁ : coherentExtension Y T τ₁)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {η₁ : Section1.ClassFunction L}
    {regularCoeff b A : ℂ}
    (hbase : theorem_6_7_base_hypothesis p P L0 (Z.map L.subtype))
    (hsigned : Section3.IsSignedIrreducibleCharacter (τ₁ η₁))
    (hconst : constantOnNonidentitySubgroup (Z.map L.subtype) (τ₁ η₁))
    (hresMap :
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η₁) =
        regularCoeff • regularCharacter (Z.map L.subtype) +
          b • Section1.principalCharacter (Z.map L.subtype))
    (hresLocal :
      Section1.subgroupRestriction Z
          (Section1.subgroupRestriction L (τ₁ η₁)) =
        regularCoeff • regularCharacter Z + b • Section1.principalCharacter Z)
    (χ₀ : X)
    (hη₁Y : η₁ ∈ Y)
    (hA : A =
      Section1.scalarProduct L (χ₀ : Section1.ClassFunction L)
        (Section1.subgroupRestriction L (τ₁ η₁)) / (dX χ₀ : ℂ))
    (hdeg0_ne : (dX χ₀ : ℂ) ≠ 0)
    (hker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction L (τ₁ η₁) - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1)
    (hfactor : Nat.card (P : Subgroup G) =
      Nat.card (Z.map L.subtype) * Z.relIndex H) :
    ∃ k : ℤ,
      Section1.scalarProduct G
        (T ((χ₀ : Section1.ClassFunction L) -
          (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁))
        (τ₁ η₁) =
          (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ) := by
  have hZH : Z ≤ H := hfamily.1
  have hW1_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hratio :
      (dX χ₀ : ℂ) =
        (Section1.degree (χ₀ : Section1.ClassFunction L) /
          (Nat.card W1 : ℂ)) * (Nat.card W1 : ℂ) := by
    calc
      (dX χ₀ : ℂ) =
          Section1.degree (χ₀ : Section1.ClassFunction L) := by
            rw [hdegX χ₀]
      _ =
          (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) * (Nat.card W1 : ℂ) := by
            field_simp [hW1_ne]
  have hsource :
      ∃ k : ℤ,
        Section1.scalarProduct L (χ₀ : Section1.ClassFunction L)
          (Section1.subgroupRestriction L (τ₁ η₁)) =
          (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ) :=
    theorem_6_8_caseA_source_coeff_multiple_of_residual_kernel_pf67_ambient
      P L0 hsemi hZH hXchar dX hdegX hbase hsigned hconst hresMap hresLocal
      χ₀ hA hdeg0_ne hratio hker z hz hfactor
  exact theorem_6_8_caseA_anchor_multiple_of_source_coeff_multiple
    h68 hSbot hsemi hfamily hτ₁ χ₀.2 hη₁Y hsource

theorem theorem_6_8_caseA_base_shift_data_of_residual_kernel_pf67_ambient
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 : Subgroup G)
    {H W1 W2 W Z : Subgroup L} [Z.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₁ : coherentExtension Y T τ₁)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    {η₁ : Section1.ClassFunction L}
    {regularCoeff b A : ℂ}
    (hbase : theorem_6_7_base_hypothesis p P L0 (Z.map L.subtype))
    (hsigned : Section3.IsSignedIrreducibleCharacter (τ₁ η₁))
    (hconst : constantOnNonidentitySubgroup (Z.map L.subtype) (τ₁ η₁))
    (hresMap :
      Section1.subgroupRestriction (Z.map L.subtype) (τ₁ η₁) =
        regularCoeff • regularCharacter (Z.map L.subtype) +
          b • Section1.principalCharacter (Z.map L.subtype))
    (hresLocal :
      Section1.subgroupRestriction Z
          (Section1.subgroupRestriction L (τ₁ η₁)) =
        regularCoeff • regularCharacter Z + b • Section1.principalCharacter Z)
    (χ₀ : X)
    (hη₁Y : η₁ ∈ Y)
    (hA : A =
      Section1.scalarProduct L (χ₀ : Section1.ClassFunction L)
        (Section1.subgroupRestriction L (τ₁ η₁)) / (dX χ₀ : ℂ))
    (hdeg0_ne : (dX χ₀ : ℂ) ≠ 0)
    (hker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction L (τ₁ η₁) - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1)
    (hfactor : Nat.card (P : Subgroup G) =
      Nat.card (Z.map L.subtype) * Z.relIndex H) :
    (∃ X₁ : Section1.ClassFunction G,
      orthogonalToTransformedFinset Y τ₁ X₁ ∧
        T ((χ₀ : Section1.ClassFunction L) -
          (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (Section1.degree (χ₀ : Section1.ClassFunction L) /
            (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∃ X₁ : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X₁ ∧
              T ((χ₀ : Section1.ClassFunction L) -
                (Section1.degree (χ₀ : Section1.ClassFunction L) /
                  (Nat.card W1 : ℂ)) • η₁) =
                X₁ - (Section1.degree (χ₀ : Section1.ClassFunction L) /
                  (Nat.card W1 : ℂ)) • (-τ₁ η₂) := by
  have hχ₀irr : Section1.IsIrreducibleCharacterOnGroup
      (χ₀ : Section1.ClassFunction L) :=
    ((hXchar (χ₀ : Section1.ClassFunction L)).1 χ₀.2).1
  have hanchor :
      ∃ k : ℤ,
        Section1.scalarProduct G
          (T ((χ₀ : Section1.ClassFunction L) -
            (Section1.degree (χ₀ : Section1.ClassFunction L) /
              (Nat.card W1 : ℂ)) • η₁))
          (τ₁ η₁) =
            (Section1.degree (χ₀ : Section1.ClassFunction L) /
              (Nat.card W1 : ℂ)) * ((k : ℤ) : ℂ) :=
    theorem_6_8_caseA_anchor_multiple_of_residual_kernel_pf67_ambient
      P L0 h68 hSbot hsemi hfamily hτ₁ hXchar dX hdegX
      hbase hsigned hconst hresMap hresLocal χ₀ hη₁Y hA hdeg0_ne hker z hz hfactor
  exact theorem_6_8_caseA_base_shift_data_of_anchor_multiple
    h68 hSbot hsemi hfamily hZcomm h52union hτ₁
    hχ₀irr χ₀.2 hη₁Y hanchor

theorem theorem_6_8_caseA_base_shift_data_of_residual_kernel_selected
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L0 : Subgroup G)
    {H W1 W2 W Z : Subgroup L} [H.Normal] [Z.Normal]
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T τ₂ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T)
    (hτ₂ : coherentExtension X T τ₂)
    (hτ₁ : coherentExtension Y T τ₁)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (dX : X → ℕ)
    (hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ))
    (hbase : theorem_6_7_base_hypothesis p P L0 (Z.map L.subtype))
    {η₁ χ₀ : Section1.ClassFunction L}
    (hsigned : Section3.IsSignedIrreducibleCharacter (τ₁ η₁))
    (hη₁Y : η₁ ∈ Y)
    (hχ₀X : χ₀ ∈ X)
    (hmul : ∀ χ : Section1.ClassFunction L, χ ∈ X →
      ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀)
    (z : Z) (hz : z ≠ 1)
    (hfactor : Nat.card (P : Subgroup G) =
      Nat.card (Z.map L.subtype) * Z.relIndex H) :
    (∃ X₁ : Section1.ClassFunction G,
      orthogonalToTransformedFinset Y τ₁ X₁ ∧
        T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
          X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
      ∃ η₂ : Section1.ClassFunction L,
        Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
          ∃ X₁ : Section1.ClassFunction G,
            orthogonalToTransformedFinset Y τ₁ X₁ ∧
              T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
                X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • (-τ₁ η₂) := by
  classical
  let χ₀x : X := ⟨χ₀, hχ₀X⟩
  let c : ℂ :=
    Section1.scalarProduct L χ₀ (Section1.subgroupRestriction L (τ₁ η₁))
  let A : ℂ := c / (dX χ₀x : ℂ)
  have hχ₀irr : Section1.IsIrreducibleCharacterOnGroup χ₀ :=
    ((hXchar χ₀).1 hχ₀X).1
  rcases theorem_6_6_positive_degree_nat_of_irreducible hχ₀irr with
    ⟨d₀, hd₀pos, hχ₀deg⟩
  have hdeg0_eq : dX χ₀x = d₀ := by
    have hcast : (dX χ₀x : ℂ) = (d₀ : ℂ) := by
      rw [← hdegX χ₀x, hχ₀deg]
    exact_mod_cast hcast
  have hdeg0_ne : (dX χ₀x : ℂ) ≠ 0 := by
    rw [hdeg0_eq]
    exact_mod_cast hd₀pos.ne'
  have hτη₁virt : Theory.Character.IsVirtualCharacter (τ₁ η₁) :=
    hτ₁.2.1 η₁ (Section5.integerSpan_of_mem Y hη₁Y)
  have hcstar : star c = c := by
    dsimp [c]
    exact theorem_6_8_source_scalarProduct_star_eq_self_of_virtual
      hχ₀irr hτη₁virt
  have hψclass :
      Section1.IsClassFunction (Section1.subgroupRestriction L (τ₁ η₁)) :=
    theorem_6_8_subgroupRestriction_isClassFunction
      (theorem_6_8_coherentExtension_mem_isClassFunction hτ₁ hη₁Y)
  have hcoeff : ∀ χ : X,
      Section1.scalarProduct L (χ : Section1.ClassFunction L)
          (Section1.subgroupRestriction L (τ₁ η₁)) =
        ((dX χ : ℂ) / (dX χ₀x : ℂ)) * c := by
    intro χ
    rcases hmul (χ : Section1.ClassFunction L) χ.2 with
      ⟨d, hχdeg⟩
    have hsource :=
      theorem_6_8_caseA_source_coeff_eq_nat_mul_base_of_degree_multiple
        h68 hSbot hfamily hZcomm h52union hτ₂ hτ₁
        χ.2 hχ₀X hη₁Y hχdeg
    have hratio : ((dX χ : ℂ) / (dX χ₀x : ℂ)) = (d : ℂ) := by
      have hdXχ : (dX χ : ℂ) = (d : ℂ) * (dX χ₀x : ℂ) := by
        calc
          (dX χ : ℂ) =
              Section1.degree (χ : Section1.ClassFunction L) := by
                rw [hdegX χ]
          _ = (d : ℂ) * Section1.degree χ₀ := hχdeg
          _ = (d : ℂ) * (dX χ₀x : ℂ) := by
                rw [hdegX χ₀x]
      rw [hdXχ]
      field_simp [hdeg0_ne]
    rw [hsource, hratio]
  have hker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction L (τ₁ η₁) - A •
        Section1.weightedFamilySum (fun χ : X => (dX χ : ℂ))
          (fun χ : X => (χ : Section1.ClassFunction L))) Z := by
    simpa [A] using
      theorem_6_8_caseA_source_residual_subgroupInKernel
        hXchar dX hψclass χ₀x hcstar hdeg0_ne hcoeff
  rcases theorem_6_8_regular_add_restrictions_of_residual_kernel_subtypeMap
      hXchar dX hdegX hker z hz with
    ⟨hconst, regularCoeff, b, hresMap, hresLocal⟩
  exact theorem_6_8_caseA_base_shift_data_of_residual_kernel_pf67_ambient
    P L0 h68 hSbot hsemi hfamily hZcomm h52union hτ₁
    hXchar dX hdegX hbase hsigned hconst hresMap hresLocal
    χ₀x hη₁Y (by rfl) hdeg0_ne hker z hz hfactor


theorem theorem_6_8_induced_indexed_degree_sum_le_intermediate_sum
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal] [Z.Normal]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S SZ X S1 : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily K ⊥ S)
    (hSZ : inducedKernelFamily K Z SZ)
    (hXeq : X = S \ SZ)
    (hXS1 : X ⊆ S1)
    (θ : ι → Section1.ClassFunction K)
    (hθirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (θ i))
    (hθnotZ : ∀ i, ¬ Section1.subgroupInKernel' (θ i) (Z.subgroupOf K))
    (hθinj : ∀ {i j : ι}, θ i = θ j → i = j)
    (dθ : ι → ℕ)
    (hdegθ : ∀ i, Section1.degree (θ i) = (dθ i : ℂ))
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ η : S1,
      Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ)) :
    (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ i : ι, (dθ i : ℝ) ^ (2 : ℕ) ≤
      ∑ η : S1,
        (((dS1 η : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (η : Section1.ClassFunction L)) := by
  classical
  have hZleK : Z ≤ K := hSZ.1
  have hθne : ∀ i, θ i ≠ Section1.principalCharacter K := by
    intro i hprincipal
    exact hθnotZ i (by intro z; simp [hprincipal, Section1.degree])
  have hθbot :
      ∀ i, Section1.subgroupInKernel' (θ i) ((⊥ : Subgroup L).subgroupOf K) := by
    intro i a
    have haL : (((a : (⊥ : Subgroup L).subgroupOf K) : K) : L) = 1 := by
      have hmem :
          (((a : (⊥ : Subgroup L).subgroupOf K) : K) : L) ∈
            (⊥ : Subgroup L) :=
        Subgroup.mem_subgroupOf.mp a.2
      simpa using hmem
    have haK : (a : K) = 1 := Subtype.ext haL
    simp [Section1.degree, haK]
  let Y : ι → Section1.ClassFunction L := fun i => Section1.inducedCF K (θ i)
  have hYdef : ∀ i : ι, Y i = Section1.inducedCF K (θ i) := by
    intro i
    rfl
  have hYS : ∀ i : ι, Y i ∈ S := by
    intro i
    exact (hSbot.2 (Y i)).mpr ⟨θ i, hθirr i, hθbot i, hθne i, rfl⟩
  have hYnotker : ∀ i : ι, ¬ Section1.subgroupInKernel' (Y i) Z := by
    intro i hIndKer
    apply hθnotZ i
    rcases hθirr i with ⟨n, ρ, _hρirr, hθeq⟩
    have hρIndKer :
        Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) Z := by
      simpa [Y, hθeq] using hIndKer
    have hρker : Section1.subgroupInKernel' ρ.character (Z.subgroupOf K) :=
      (Section1.proposition_1_6_a K Z hZleK ρ).mpr hρIndKer
    simpa [hθeq] using hρker
  have hYX : ∀ i : ι, Y i ∈ X := by
    intro i
    exact theorem_6_6_mem_Xset_of_mem_S_not_subgroupInKernel
      (K := K) (Z := Z) (show Z.Normal from inferInstance) hZleK
      hSZ hXeq (hYS i) (hYnotker i)
  let YS1 : ι → S1 := fun i => ⟨Y i, hXS1 (hYX i)⟩
  have hYS1coe : ∀ i : ι, (YS1 i : Section1.ClassFunction L) = Y i := by
    intro i
    rfl
  let term : S1 → ℝ := fun η =>
    (((dS1 η : ℝ) ^ (2 : ℕ)) / Section5.cfNormSq (η : Section1.ClassFunction L))
  have hterm_nonneg : ∀ η : S1, 0 ≤ term η := by
    intro η
    dsimp [term]
    exact div_nonneg (sq_nonneg _) (Section5.cfNormSq_nonneg _)
  have hterm_rep : ∀ i : ι, term (YS1 i) =
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ o : Section1.conjugateOrbitIndex K (θ i), (dθ i : ℝ) ^ (2 : ℕ) := by
    intro i
    rcases theorem_6_2_pf15_orbit_contribution (L := L) (K := K) (hθirr i) with
      ⟨dθ', dχ, hθdeg', hχdeg, hterm⟩
    have hdθ_eq : dθ' = dθ i := by
      have hcast : (dθ' : ℂ) = (dθ i : ℂ) := by
        rw [← hθdeg', hdegθ]
      exact_mod_cast hcast
    have hdχ_eq : dχ = dS1 (YS1 i) := by
      have hcast : (dχ : ℂ) = (dS1 (YS1 i) : ℂ) := by
        rw [← hχdeg]
        rw [← hYdef i, ← hYS1coe i]
        exact hdS1 (YS1 i)
      exact_mod_cast hcast
    change (((dS1 (YS1 i) : ℝ) ^ (2 : ℕ)) /
        Section5.cfNormSq (YS1 i : Section1.ClassFunction L)) =
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ o : Section1.conjugateOrbitIndex K (θ i), (dθ i : ℝ) ^ (2 : ℕ)
    rw [← hdχ_eq]
    rw [hYS1coe i, hYdef i]
    rw [hterm, hdθ_eq]
  have hconjS1 : ∀ i j : ι, YS1 j = YS1 i →
      ∃ o : Section1.conjugateOrbitIndex K (θ i),
        θ j = Section1.conjugateOrbitConj K (θ i) o := by
    intro i j hYS
    have hYeq : Y j = Y i := by
      have h := congrArg (fun Y : S1 => (Y : Section1.ClassFunction L)) hYS
      simpa [hYS1coe] using h
    by_contra hnone
    push Not at hnone
    have hnot : ∀ o : Section1.conjugateOrbitIndex K (θ i),
        θ j ≠ Section1.conjugateOrbitConj K (θ i) o := hnone
    rcases hθirr j with ⟨nj, ρj, hρj, hθj_eq⟩
    rcases hθirr i with ⟨ni, ρi, hρi, hθi_eq⟩
    have hnot' : ∀ o : Section1.conjugateOrbitIndex K ρi.character,
        θ j ≠ Section1.conjugateOrbitConj K ρi.character o := by
      have htmp := hnot
      rw [hθi_eq] at htmp
      exact htmp
    have horth := Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
      (G := L) (H := K) (phi := θ j) (phiRep := ρj)
      (thetaRep := ρi) (hphi := hθj_eq) (hphi_irreducible := hρj)
      (htheta_irreducible := hρi)
      (hnotConj := hnot')
    have hself : Section1.scalarProduct L (Y i) (Y i) ≠ 0 := by
      have hsp := Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        (G := L) (H := K) ρi hρi
      have hrel_ne : K.relIndex (Section1.inertiaSubgroup K ρi.character) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      rw [hYdef i, hθi_eq]
      change Section1.scalarProduct L
        (Section1.inducedCF K ρi.character)
        (Section1.inducedCF K ρi.character) ≠ 0
      rw [hsp]
      exact_mod_cast hrel_ne
    apply hself
    have horthY : Section1.scalarProduct L (Y j) (Y i) = 0 := by
      rw [hYdef j, hYdef i, hθi_eq]
      exact horth
    rw [hYeq] at horthY
    exact horthY
  let weight : ι → ℝ := fun i =>
    (K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)
  have hfiber_bound_rep : ∀ i : ι,
      (Finset.univ.filter (fun j : ι => YS1 j = YS1 i)).sum weight ≤ term (YS1 i) := by
    intro i
    let fiber : Finset ι := Finset.univ.filter (fun j : ι => YS1 j = YS1 i)
    let orbitOf : ι → Section1.conjugateOrbitIndex K (θ i) := fun j =>
      if h : YS1 j = YS1 i then Classical.choose (hconjS1 i j h)
      else Section1.conjugateOrbitFiber K (θ i) 1
    have horbit_spec : ∀ j : ι, (hj : j ∈ fiber) →
        θ j = Section1.conjugateOrbitConj K (θ i) (orbitOf j) := by
      intro j hj
      have hji : YS1 j = YS1 i := by
        simpa [fiber] using hj
      dsimp [orbitOf]
      rw [dif_pos hji]
      exact Classical.choose_spec (hconjS1 i j hji)
    have hinj : Set.InjOn orbitOf (fiber : Set ι) := by
      intro j hj k hk heq
      have hθj := horbit_spec j hj
      have hθk := horbit_spec k hk
      apply hθinj
      rw [hθj, hθk, heq]
    have hmaps : Set.MapsTo orbitOf (fiber : Set ι)
        (Finset.univ : Finset (Section1.conjugateOrbitIndex K (θ i))) := by
      intro j hj
      simp
    have hcard_le : fiber.card ≤
        Fintype.card (Section1.conjugateOrbitIndex K (θ i)) := by
      simpa using Finset.card_le_card_of_injOn orbitOf hmaps hinj
    have hdeg_eq : ∀ j ∈ fiber, dθ j = dθ i := by
      intro j hj
      have hθj := horbit_spec j hj
      have hdeg_orbit :
          Section1.degree (Section1.conjugateOrbitConj K (θ i) (orbitOf j)) =
            Section1.degree (θ i) := by
        refine Quotient.inductionOn (orbitOf j) ?_
        intro g
        unfold Section1.degree Section1.conjugateOrbitConj
        dsimp [Section1.conjugateOnNormal]
        congr 1
        ext
        simp
      have hcast : (dθ j : ℂ) = (dθ i : ℂ) := by
        rw [← hdegθ j, hθj, hdeg_orbit, hdegθ i]
      exact_mod_cast hcast
    have hfiber_sum_eq :
        fiber.sum weight =
          fiber.card * ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)) := by
      calc
        fiber.sum weight =
            fiber.sum (fun _ : ι =>
              (K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [weight, hdeg_eq j hj]
        _ = fiber.card *
            ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
    have horbit_sum_eq :
        (∑ o : Section1.conjugateOrbitIndex K (θ i), (dθ i : ℝ) ^ (2 : ℕ)) =
          Fintype.card (Section1.conjugateOrbitIndex K (θ i)) *
            (dθ i : ℝ) ^ (2 : ℕ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    change fiber.sum weight ≤ term (YS1 i)
    rw [hfiber_sum_eq, hterm_rep i, horbit_sum_eq]
    have hnonneg :
        0 ≤ (K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ) := by
      positivity
    have hcard_le_real :
        (fiber.card : ℝ) ≤
          (Fintype.card (Section1.conjugateOrbitIndex K (θ i)) : ℝ) := by
      exact_mod_cast hcard_le
    calc
      (fiber.card : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)) ≤
        (Fintype.card (Section1.conjugateOrbitIndex K (θ i)) : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dθ i : ℝ) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hcard_le_real hnonneg
      _ = (K.relIndex (⊤ : Subgroup L) : ℝ) *
          ((Fintype.card (Section1.conjugateOrbitIndex K (θ i)) : ℝ) *
            (dθ i : ℝ) ^ (2 : ℕ)) := by
          ring
  have hfiber_bound_all : ∀ Y0 : S1,
      (Finset.univ.filter (fun i : ι => YS1 i = Y0)).sum weight ≤ term Y0 := by
    intro Y0
    by_cases hY0 : ∃ i : ι, YS1 i = Y0
    · rcases hY0 with ⟨i, hi⟩
      have hsum_eq :
          (Finset.univ.filter (fun j : ι => YS1 j = Y0)).sum weight =
            (Finset.univ.filter (fun j : ι => YS1 j = YS1 i)).sum weight := by
        congr 1
        ext j
        simp [hi]
      rw [hsum_eq, ← hi]
      exact hfiber_bound_rep i
    · have hempty : Finset.univ.filter (fun j : ι => YS1 j = Y0) = ∅ := by
        ext j
        simp
        intro hji
        exact (hY0 ⟨j, hji⟩).elim
      rw [hempty]
      simpa using hterm_nonneg Y0
  have hsum_weight_le : (∑ i : ι, weight i) ≤ ∑ Y0 : S1, term Y0 := by
    rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset ι)) (g := YS1) (f := weight)]
    apply Finset.sum_le_sum
    intro Y0 _hY0
    exact hfiber_bound_all Y0
  calc
    (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ i : ι, (dθ i : ℝ) ^ (2 : ℕ) =
        ∑ i : ι, weight i := by
          simp [weight, Finset.mul_sum]
    _ ≤ ∑ Y0 : S1, term Y0 := hsum_weight_le

theorem theorem_6_8_weighted_degree_term_pos
    {L : Type u} [Group L] [Finite L]
    (η : Section1.ClassFunction L) {d : ℕ}
    (hdeg : Section1.degree η = (d : ℂ))
    (hdpos : 0 < d) :
    0 < (((d : ℝ) ^ (2 : ℕ)) / Section5.cfNormSq η) := by
  have hcf_ne : Section5.cfNormSq η ≠ 0 := by
    intro hcf0
    have hηzero : η = 0 := Section5.cfNormSq_eq_zero hcf0
    have hdeg0 : Section1.degree η = 0 := by
      simp [hηzero, Section1.degree]
    have hd0 : (d : ℂ) = 0 := by
      simpa [hdeg] using hdeg0
    have : d = 0 := by
      exact_mod_cast hd0
    omega
  have hcf_pos : 0 < Section5.cfNormSq η :=
    lt_of_le_of_ne (Section5.cfNormSq_nonneg η) (Ne.symm hcf_ne)
  have hnum_pos : 0 < ((d : ℝ) ^ (2 : ℕ)) := by
    positivity
  exact div_pos hnum_pos hcf_pos

theorem theorem_6_8_endpoint_numeric_small_bound
    {w q r n d dψ : ℕ} {sigma : ℝ}
    (hwpos : 0 < w)
    (hrpos : 0 < r)
    (hq : q = w)
    (hstrict : ((w * r * n : ℕ) : ℝ) < sigma)
    (hupper : sigma ≤ 2 * (dψ : ℝ) * (q : ℝ))
    (hdψ : dψ = q * d)
    (hdsq : d ^ (2 : ℕ) ≤ r) :
    ((r * n ^ (2 : ℕ) : ℕ) : ℝ) < ((4 * w ^ (2 : ℕ) : ℕ) : ℝ) := by
  have hmain : ((w * r * n : ℕ) : ℝ) <
      2 * ((q * d : ℕ) : ℝ) * (q : ℝ) := by
    calc
      ((w * r * n : ℕ) : ℝ) < sigma := hstrict
      _ ≤ 2 * (dψ : ℝ) * (q : ℝ) := hupper
      _ = 2 * ((q * d : ℕ) : ℝ) * (q : ℝ) := by simp [hdψ]
  have hmain' : (w : ℝ) * (r : ℝ) * (n : ℝ) <
      2 * ((w : ℝ) * (d : ℝ)) * (w : ℝ) := by
    simpa [hq, Nat.cast_mul] using hmain
  have hdsqR : (d : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hdsq
  have hwposR : (0 : ℝ) < w := by exact_mod_cast hwpos
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hdiv : (r : ℝ) * (n : ℝ) < 2 * (w : ℝ) * (d : ℝ) := by
    nlinarith
  have hleft_nonneg : 0 ≤ (r : ℝ) * (n : ℝ) := by positivity
  have hright_nonneg : 0 ≤ 2 * (w : ℝ) * (d : ℝ) := by positivity
  have hsquare_abs : |(r : ℝ) * (n : ℝ)| <
      |2 * (w : ℝ) * (d : ℝ)| := by
    rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    exact hdiv
  have hsquare : ((r : ℝ) * (n : ℝ)) ^ (2 : ℕ) <
      (2 * (w : ℝ) * (d : ℝ)) ^ (2 : ℕ) := by
    exact sq_lt_sq.mpr hsquare_abs
  have hgoalR : (r : ℝ) * (n : ℝ) ^ (2 : ℕ) <
      4 * (w : ℝ) ^ (2 : ℕ) := by
    nlinarith
  simpa [Nat.cast_mul, Nat.cast_pow] using hgoalR

theorem theorem_6_8_endpoint_caseA_arithmetic_contradiction
    {w r n : ℕ}
    (hrpos : 0 < r)
    (hsmall : ((r * n ^ (2 : ℕ) : ℕ) : ℝ) <
      ((4 * w ^ (2 : ℕ) : ℕ) : ℝ))
    (hbound : 2 * w ≤ n) : False := by
  have hrge1R : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  have hboundR : (2 * (w : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hbound
  have hsmallR : (r : ℝ) * (n : ℝ) ^ (2 : ℕ) <
      4 * (w : ℝ) ^ (2 : ℕ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hsmall
  nlinarith [sq_nonneg ((n : ℝ) - 2 * (w : ℝ))]

theorem theorem_6_8_endpoint_caseB_arithmetic_contradiction
    {w r n : ℕ}
    (hsmall : ((r * n ^ (2 : ℕ) : ℕ) : ℝ) <
      ((4 * w ^ (2 : ℕ) : ℕ) : ℝ))
    (hrbound : (2 * w + 1) ^ (2 : ℕ) ≤ r)
    (hnbound : 2 ≤ n) : False := by
  have hrboundR' : (((2 * w + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (r : ℝ) := by
    exact_mod_cast hrbound
  have hcast : ((2 * w + 1 : ℕ) : ℝ) = 2 * (w : ℝ) + 1 := by
    norm_num
  have hrboundR : (2 * (w : ℝ) + 1) ^ (2 : ℕ) ≤ (r : ℝ) := by
    simpa [hcast] using hrboundR'
  have hnboundR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnbound
  have hsmallR : (r : ℝ) * (n : ℝ) ^ (2 : ℕ) <
      4 * (w : ℝ) ^ (2 : ℕ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hsmall
  nlinarith [sq_nonneg (2 * (w : ℝ) + 1),
    sq_nonneg ((n : ℝ) - 2)]

theorem theorem_6_8_caseA_card_bound_of_dvd
    {L : Type u} [Group L] [Finite L]
    {W1 Z : Subgroup L}
    (hW1odd : Odd (Nat.card W1))
    (hZodd : Odd (Nat.card Z))
    (hZne : Z ≠ ⊥)
    (hdiv : Nat.card W1 ∣ Nat.card Z - 1) :
    2 * Nat.card W1 ≤ Nat.card Z - 1 := by
  have hZgt : 1 < Nat.card Z := by
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hne : Nat.card Z ≠ 1 := by
      intro hcard
      exact hZne (Subgroup.card_eq_one.mp hcard)
    omega
  have hbound :=
    odd_divisor_sub_one_lower_bound hW1odd hZodd hZgt hdiv
  omega

theorem theorem_6_8_caseA_card_bound_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hfrob : frobeniusWithKernel (⊤ : Subgroup L) H)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    2 * Nat.card W1 ≤ Nat.card Z - 1 := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases hfamily with ⟨hZH, _hSZ, _hXeq, _hY⟩
  rcases theorem_6_8_Z_center_normal_ne_bot_of_caseData h68' hpQ
      (Or.inl hA) with
    ⟨hZne, _hZcenter, hZnorm⟩
  have hW1odd : Odd (Nat.card W1) :=
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card W1)
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card Z)
  have hdiv : Nat.card W1 ∣ Nat.card Z - 1 :=
    theorem_6_8_frobenius_card_dvd_Z_sub_one hsemi hfrob hZH hZnorm
  exact theorem_6_8_caseA_card_bound_of_dvd hW1odd hZodd hZne hdiv

theorem theorem_6_8_caseA_c2_card_dvd_Z_sub_one
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hZnorm : Z.Normal) :
    Nat.card W1 ∣ Nat.card Z - 1 := by
  classical
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hdirect, _hWodd⟩
  rcases hA with ⟨hcenterW2, hZeq⟩
  have hZcenter : Z ≤ centerIn H := by
    rw [hZeq]
    exact inf_le_left
  have : Z.Normal := hZnorm
  have hcentZ :
      ∀ r : W1, r ≠ 1 → Section2.centralizerIn Z (r : L) = ⊥ := by
    intro r hr
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxZ : x ∈ Z := hx.1
    have hxCenter : x ∈ centerIn H := hZcenter hxZ
    have hxH : x ∈ H := hxCenter.1
    have hxcentH : x ∈ Section2.centralizerIn H (r : L) := ⟨hxH, hx.2⟩
    have hxW2 : x ∈ W2 := by
      have hcent_eq := hcentW1 r hr
      simpa [hcent_eq] using hxcentH
    have hxInf : x ∈ centerIn H ⊓ W2 := ⟨hxCenter, hxW2⟩
    have hxbot : x ∈ (⊥ : Subgroup L) := by
      simpa [hcenterW2] using hxInf
    simpa using hxbot
  exact frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
    (K := Z) (R := W1) (N := Z) le_rfl hcentZ

theorem theorem_6_8_caseA_card_bound_of_caseC2
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z) :
    2 * Nat.card W1 ≤ Nat.card Z - 1 := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases theorem_6_8_Z_center_normal_ne_bot_of_caseData h68' hpQ
      (Or.inl hA) with
    ⟨hZne, _hZcenter, hZnorm⟩
  have hW1odd : Odd (Nat.card W1) :=
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card W1)
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card Z)
  have hdiv : Nat.card W1 ∣ Nat.card Z - 1 :=
    theorem_6_8_caseA_c2_card_dvd_Z_sub_one hcase hA hZnorm
  exact theorem_6_8_caseA_card_bound_of_dvd hW1odd hZodd hZne hdiv

theorem theorem_6_8_caseA_card_bound_of_branch
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y) :
    2 * Nat.card W1 ≤ Nat.card Z - 1 := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases hbranch with hfrob | hcaseC2
  · exact theorem_6_8_caseA_card_bound_of_frobenius
      h68' hfrob hpQ hA hfamily
  · exact theorem_6_8_caseA_card_bound_of_caseC2
      h68' hcaseC2 hpQ hA

theorem theorem_6_8_caseB_Z_sub_one_lower_bound
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z) :
    2 ≤ Nat.card Z - 1 := by
  classical
  rcases hB with ⟨hW2ne, _hW2center, _hW2comm, hZeq⟩
  subst Z
  rcases hcase with ⟨⟨d⟩, _hprime, _hW2comm'⟩
  let : Fintype d.I := d.instFintypeI
  let : Fintype d.J := d.instFintypeJ
  let : DecidableEq d.I := d.instDecidableEqI
  let : DecidableEq d.J := d.instDecidableEqJ
  rcases d.fullHypothesis with
    ⟨h46, _hW2K, _h31img, _hσiso, _hσvirt, _hσclass, _hσone, _h22A,
      _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hτcyclic,
      _hτA0, _hτisoA0, _hτpunctA0, _hτvirtA0⟩
  rcases h46 with ⟨h42, _hHnorm46, _hW2H, _hHH, _hcentA, _hA⟩
  rcases h42 with
    ⟨_hsemi42, _hHall, _hcyc1, _hW1card_ne, _hcyc2, _hW2card_ne,
      _hcentW1, _hW1W, hW2W, _hdirect, hWodd⟩
  have hW2odd : Odd (Nat.card W2) :=
    Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le hW2W)
  have hW2ne1 : Nat.card W2 ≠ 1 := by
    intro hcard
    exact hW2ne (Subgroup.card_eq_one.mp hcard)
  have hW2ne2 : Nat.card W2 ≠ 2 := by
    intro hcard
    have hcardF : Fintype.card W2 = 2 := by
      simpa [Nat.card_eq_fintype_card] using hcard
    have htwoOdd : Odd 2 := by
      simpa [hcardF] using hW2odd
    rcases htwoOdd with ⟨k, hk⟩
    omega
  have hpos : 0 < Nat.card W2 := Nat.card_pos
  omega

theorem theorem_6_8_caseB_relIndex_sq_lower_bound
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hZneComm : Z ≠ ⁅H,H⁆) :
    (2 * Nat.card W1 + 1) ^ (2 : ℕ) ≤ Z.relIndex H := by
  have hfrobZ : frobeniusQuotientWithKernel H Z :=
    theorem_6_8_frobeniusQuotient_Z_of_caseB h68 hcase hB
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, _hTI, _hSbot, _hT, _hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have hsolvH : Group.IsSolvable H := by
    have : Group.IsNilpotent H := hnil
    infer_instance
  have hZcomm : Z ≤ ⁅H,H⁆ :=
    theorem_6_8_Z_le_commutator_of_caseData
      (G := G) (L := L) (H := H) (W1 := W1) (W2 := W2)
      (W := W) (Z := Z) (T := T) (Or.inr ⟨hcase, hB⟩)
  have hcommH : ⁅H,H⁆ ≤ H :=
    Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have hZltComm : Z < ⁅H,H⁆ := lt_of_le_of_ne hZcomm hZneComm
  have hcommLtH : ⁅H,H⁆ < H := by
    have hnot : ¬ H ≤ ⁅H,H⁆ :=
      theorem_6_8_not_le_commutator_of_nontrivial_nilpotent hHne hnil
    refine lt_of_le_of_ne hcommH ?_
    intro hEq
    exact hnot (by rw [hEq])
  have hcommNorm : ⁅H,H⁆.Normal := Subgroup.commutator_normal H H
  have hlower :=
    frobeniusQuotientWithKernel_intermediate_lower_bounds
      (K := H) (H1 := Z) (N := ⁅H,H⁆)
      hodd hsolvH hfrobZ hcommNorm hZcomm hcommH hZltComm hcommLtH
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hlowZ :
      2 * Nat.card W1 + 1 ≤ Z.relIndex ⁅H,H⁆ := by
    simpa [hHindex] using hlower.1
  have hlowH :
      2 * Nat.card W1 + 1 ≤ ⁅H,H⁆.relIndex H := by
    simpa [hHindex] using hlower.2
  have hmul := Nat.mul_le_mul hlowZ hlowH
  have hrel : Z.relIndex ⁅H,H⁆ * ⁅H,H⁆.relIndex H = Z.relIndex H :=
    Subgroup.relIndex_mul_relIndex Z ⁅H,H⁆ H hZcomm hcommH
  rw [hrel] at hmul
  simpa [pow_two] using hmul

theorem theorem_6_8_caseB_card_bounds
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hcase : caseC2Hypothesis L H W1 W2 W T)
    (hB : theorem_6_8_caseBData H W2 Z)
    (hZneComm : Z ≠ ⁅H,H⁆) :
    (2 * Nat.card W1 + 1) ^ (2 : ℕ) ≤ Z.relIndex H ∧
      2 ≤ Nat.card Z - 1 := by
  exact
    ⟨theorem_6_8_caseB_relIndex_sq_lower_bound h68 hcase hB hZneComm,
      theorem_6_8_caseB_Z_sub_one_lower_bound hcase hB⟩


theorem theorem_6_8_X_degree_data_of_character
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L}
    {X : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z) :
    ∃ dX : X → ℕ,
      ∀ χ : X,
        Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ) := by
  classical
  have hXdeg_exists :
      ∀ χ : X,
        ∃ dχ : ℕ,
          Section1.degree (χ : Section1.ClassFunction L) = (dχ : ℂ) := by
    intro χ
    rcases ((hXchar (χ : Section1.ClassFunction L)).mp χ.2).1 with
      ⟨dχ, ρ, _hρirr, hχeq⟩
    refine ⟨dχ, ?_⟩
    rw [hχeq, Section1.degree_representation_character]
    simp
  let dX : X → ℕ := fun χ => Classical.choose (hXdeg_exists χ)
  have hdegX : ∀ χ : X,
      Section1.degree (χ : Section1.ClassFunction L) = (dX χ : ℂ) := by
    intro χ
    exact Classical.choose_spec (hXdeg_exists χ)
  exact ⟨dX, hdegX⟩

theorem theorem_6_8_complete_nonkernel_degree_data
    {K : Type u} [Group K] [Finite K]
    {A : Subgroup K} [A.Normal] :
    ∃ X : Finset (Section1.ClassFunction K),
      (∀ θ : Section1.ClassFunction K, θ ∈ X ↔
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          ¬ Section1.subgroupInKernel' θ A) ∧
        ∃ dX : X → ℕ,
          (∀ θ : X,
            Section1.degree (θ : Section1.ClassFunction K) = (dX θ : ℂ)) ∧
            (∑ θ : X, dX θ ^ (2 : ℕ)) +
                Nat.card (K ⧸ A) = Nat.card K := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := K) with
    ⟨ι, hι, χ, hχ, _hsumχ⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let θ : ι → Section1.ClassFunction K :=
    fun i => Section1.ofConjClassFunction (χ i)
  let X : Finset (Section1.ClassFunction K) :=
    (Finset.univ.filter fun i : ι =>
      ¬ Section1.subgroupInKernel' (θ i) A).image θ
  have hθirr :
      ∀ i, Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
  have hXchar : ∀ θ0 : Section1.ClassFunction K, θ0 ∈ X ↔
      Section1.IsIrreducibleCharacterOnGroup θ0 ∧
        ¬ Section1.subgroupInKernel' θ0 A := by
    intro θ0
    constructor
    · intro hθ0
      rcases Finset.mem_image.mp hθ0 with ⟨i, hi, hiθ⟩
      have hi_not :
          ¬ Section1.subgroupInKernel' (θ i) A := by
        exact (Finset.mem_filter.mp hi).2
      constructor
      · simpa [hiθ] using hθirr i
      · intro hker
        exact hi_not (by simpa [hiθ] using hker)
    · intro hθ0
      have hθ0class : Section1.IsClassFunction θ0 := by
        rcases hθ0.1 with ⟨_n, ρ, _hρirr, hθ0eq⟩
        intro x g
        rw [hθ0eq]
        simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
      have hθ0rep :
          Theory.Character.IsIrreducibleConjCharacter
            (Section1.toConjClassFunction θ0 hθ0class) := by
        rcases hθ0.1 with ⟨n, ρ, hρirr, hθ0eq⟩
        constructor
        · refine ⟨n, ρ, ?_⟩
          ext c
          rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
          change θ0 g = ρ.character g
          rw [hθ0eq]
        · have hnorm :=
            (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
          have hto :
              Section1.toConjClassFunction θ0 hθ0class =
                (Theory.Character.characterClassFunction ρ) := by
            refine Section1.toConjClassFunction_eq_of_apply θ0 hθ0class
              (Theory.Character.characterClassFunction ρ) ?_
            intro g
            rw [hθ0eq]
            rfl
          rw [hto]
          exact hnorm
      rcases hχ.2.1 (Section1.toConjClassFunction θ0 hθ0class) hθ0rep with
        ⟨i, hi⟩
      have hiθ : θ i = θ0 := by
        dsimp [θ]
        rw [hi]
        ext g
        rfl
      refine Finset.mem_image.mpr ⟨i, ?_, hiθ⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, by simpa [hiθ] using hθ0.2⟩
  rcases theorem_6_8_X_degree_data_of_character hXchar with
    ⟨dX, hdegX⟩
  refine ⟨X, hXchar, dX, hdegX, ?_⟩
  exact theorem_6_8_X_degree_sq_sum_add_quotient_card hXchar dX hdegX

theorem theorem_6_8_nonkernel_source_lower_bound
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L} [Z.Normal]
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hXS1 : X ⊆ S1)
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ η : S1,
      Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ)) :
    ((Nat.card W1 * Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) ≤
      ∑ η : S1,
        (((dS1 η : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (η : Section1.ClassFunction L)) := by
  classical
  have : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have hZH : Z ≤ H := hfamily.1
  have : (Z.subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf (H := Z) (K := H)
      (inferInstance : Z.Normal)
  rcases theorem_6_8_complete_nonkernel_degree_data
      (K := H) (A := Z.subgroupOf H) with
    ⟨XH, hXHchar, dXH, hdegXH, hsumXH⟩
  have hlower :=
    theorem_6_8_induced_indexed_degree_sum_le_intermediate_sum
      (K := H) (Z := Z) (S := S) (SZ := SZ) (X := X) (S1 := S1)
      hSbot hfamily.2.1 hfamily.2.2.1 hXS1
      (fun θ : XH => (θ : Section1.ClassFunction H))
      (fun θ : XH => ((hXHchar (θ : Section1.ClassFunction H)).mp θ.2).1)
      (fun θ : XH => ((hXHchar (θ : Section1.ClassFunction H)).mp θ.2).2)
      (by
        intro θ η hθη
        exact Subtype.ext hθη)
      dXH hdegXH dS1 hdS1
  have hsum_nat :
      (∑ θ : XH, dXH θ ^ (2 : ℕ)) =
        Nat.card H - Nat.card (H ⧸ Z.subgroupOf H) := by
    exact Nat.eq_sub_of_add_eq hsumXH
  have hcardH :
      Nat.card H - Nat.card (H ⧸ Z.subgroupOf H) =
        Z.relIndex H * (Nat.card Z - 1) := by
    have hcardHZ : Nat.card H =
        Nat.card (H ⧸ Z.subgroupOf H) * Nat.card (Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    have hcardZ : Nat.card (Z.subgroupOf H) = Nat.card Z :=
      natCard_subgroupOf_eq Z H hZH
    have hquot : Nat.card (H ⧸ Z.subgroupOf H) = Z.relIndex H := by
      rw [← Subgroup.index_eq_card]
      rfl
    rw [hcardHZ, hcardZ, hquot]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hcast :
      (H.relIndex (⊤ : Subgroup L) : ℝ) *
          ∑ θ : XH, (dXH θ : ℝ) ^ (2 : ℕ) =
        ((Nat.card W1 * Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) := by
    have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
    calc
      (H.relIndex (⊤ : Subgroup L) : ℝ) *
          ∑ θ : XH, (dXH θ : ℝ) ^ (2 : ℕ)
          = (Nat.card W1 : ℝ) *
              ((∑ θ : XH, dXH θ ^ (2 : ℕ)) : ℝ) := by
              simp [hHindex]
      _ = (Nat.card W1 : ℝ) *
              ((Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) := by
              have hsum_real_cast :
                  (∑ θ : XH, (dXH θ : ℝ) ^ (2 : ℕ)) =
                    (((∑ θ : XH, dXH θ ^ (2 : ℕ)) : ℕ) : ℝ) := by
                norm_num [Nat.cast_sum, Nat.cast_pow]
              have hsum_nat_cast :
                  (((∑ θ : XH, dXH θ ^ (2 : ℕ)) : ℕ) : ℝ) =
                    ((Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) := by
                exact_mod_cast hsum_nat.trans hcardH
              rw [hsum_real_cast, hsum_nat_cast]
      _ = ((Nat.card W1 * Z.relIndex H *
              (Nat.card Z - 1) : ℕ) : ℝ) := by
              norm_num [Nat.cast_mul]
              ring
  rwa [← hcast]

theorem theorem_6_8_nonkernel_source_strict_lower_bound_of_extra
    {L : Type u} [Group L] [Finite L]
    {H W1 Z : Subgroup L} [Z.Normal]
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hXS1 : X ⊆ S1)
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ η : S1,
      Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ))
    (η0 : S1)
    (hη0notX : (η0 : Section1.ClassFunction L) ∉ X)
    {dη0 : ℕ}
    (hη0deg : Section1.degree (η0 : Section1.ClassFunction L) = (dη0 : ℂ))
    (hdη0pos : 0 < dη0) :
    ((Nat.card W1 * Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) <
      ∑ η : S1,
        (((dS1 η : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (η : Section1.ClassFunction L)) := by
  classical
  let S1' : Finset (Section1.ClassFunction L) :=
    S1.erase (η0 : Section1.ClassFunction L)
  have hXS1' : X ⊆ S1' := by
    intro χ hχX
    refine Finset.mem_erase.mpr ⟨?_, hXS1 hχX⟩
    intro hχη
    exact hη0notX (by simpa [← hχη] using hχX)
  let emb : S1' ↪ S1 :=
    { toFun := fun η => ⟨(η : Section1.ClassFunction L),
        (Finset.mem_erase.mp η.2).2⟩
      inj' := by
        intro η ξ hηξ
        exact Subtype.ext
          (congrArg (fun a : S1 => (a : Section1.ClassFunction L)) hηξ) }
  let dS1' : S1' → ℕ := fun η => dS1 (emb η)
  have hdS1' : ∀ η : S1',
      Section1.degree (η : Section1.ClassFunction L) = (dS1' η : ℂ) := by
    intro η
    exact hdS1 (emb η)
  have hlower :=
    theorem_6_8_nonkernel_source_lower_bound
      (S1 := S1') hSbot hsemi hfamily hXS1' dS1' hdS1'
  let term : S1 → ℝ := fun η =>
    (((dS1 η : ℝ) ^ (2 : ℕ)) /
      Section5.cfNormSq (η : Section1.ClassFunction L))
  let term' : S1' → ℝ := fun η =>
    (((dS1' η : ℝ) ^ (2 : ℕ)) /
      Section5.cfNormSq (η : Section1.ClassFunction L))
  have hterm_nonneg : ∀ η : S1, 0 ≤ term η := by
    intro η
    dsimp [term]
    exact div_nonneg (sq_nonneg _) (Section5.cfNormSq_nonneg _)
  have hterm'_eq : ∀ η : S1', term' η = term (emb η) := by
    intro η
    rfl
  have himage_sum :
      (∑ η ∈ ((Finset.univ : Finset S1').image emb), term η) =
        ∑ η : S1', term (emb η) := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact emb.injective h
  have hsubset :
      ((Finset.univ : Finset S1').image emb) ⊆
        (Finset.univ : Finset S1) := by
    intro η _hη
    simp
  have hη0notImage : η0 ∉ ((Finset.univ : Finset S1').image emb) := by
    intro hη0
    rcases Finset.mem_image.mp hη0 with ⟨η, _hη, hηeq⟩
    have hηerase :
        (η0 : Section1.ClassFunction L) ∈
          S1.erase (η0 : Section1.ClassFunction L) := by
      have hval : (η0 : Section1.ClassFunction L) =
          (η : Section1.ClassFunction L) :=
        congrArg (fun a : S1 => (a : Section1.ClassFunction L)) hηeq.symm
      have hηmem : (η : Section1.ClassFunction L) ∈
          S1.erase (η0 : Section1.ClassFunction L) := η.2
      exact hval.symm ▸ hηmem
    exact (Finset.mem_erase.mp hηerase).1 rfl
  have hη0term_pos : 0 < term η0 := by
    have hd_eq : dS1 η0 = dη0 := by
      have hcast : (dS1 η0 : ℂ) = (dη0 : ℂ) := by
        rw [← hdS1 η0, hη0deg]
      exact_mod_cast hcast
    dsimp [term]
    rw [hd_eq]
    exact theorem_6_8_weighted_degree_term_pos
      (η0 : Section1.ClassFunction L) hη0deg hdη0pos
  have himage_subset_erase :
      ((Finset.univ : Finset S1').image emb) ⊆
        ((Finset.univ : Finset S1).erase η0) := by
    intro η hη
    exact Finset.mem_erase.mpr
      ⟨by
        intro hηeq
        exact hη0notImage (by simpa [hηeq] using hη),
       by simp⟩
  have himage_le_erase :
      (∑ η ∈ ((Finset.univ : Finset S1').image emb), term η) ≤
        ∑ η ∈ ((Finset.univ : Finset S1).erase η0), term η := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset_erase
      (by intro η _hηerase _hηnot; exact hterm_nonneg η)
  have himage_lt_univ :
      (∑ η ∈ ((Finset.univ : Finset S1').image emb), term η) <
        ∑ η : S1, term η := by
    have hlt :
        (∑ η ∈ ((Finset.univ : Finset S1').image emb), term η) <
          (∑ η ∈ ((Finset.univ : Finset S1).erase η0), term η) +
            term η0 :=
      lt_of_le_of_lt himage_le_erase
        (lt_add_of_pos_right _ hη0term_pos)
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset S1)) (f := term) (a := η0) (by simp)
    rw [hsplit] at hlt
    exact hlt
  have hstrict :
      ∑ η : S1', term' η < ∑ η : S1, term η := by
    calc
      ∑ η : S1', term' η = ∑ η : S1', term (emb η) := by
        refine Finset.sum_congr rfl ?_
        intro η _hη
        exact hterm'_eq η
      _ = ∑ η ∈ ((Finset.univ : Finset S1').image emb), term η :=
        himage_sum.symm
      _ < ∑ η : S1, term η := himage_lt_univ
  exact lt_of_le_of_lt hlower hstrict

theorem theorem_6_8_nonkernel_source_strict_lower_bound_of_intermediate
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L} [Z.Normal]
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (hXS1 : X ⊆ S1)
    (hunionS1 : X ∪ Y ⊆ S1)
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ η : S1,
      Section1.degree (η : Section1.ClassFunction L) = (dS1 η : ℂ)) :
    ((Nat.card W1 * Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) <
      ∑ η : S1,
        (((dS1 η : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (η : Section1.ClassFunction L)) := by
  rcases theorem_6_8_exists_intermediate_not_X_degree_relIndex
      h68 hfamily hZcomm hunionS1 with
    ⟨η1, hηnotX, hηdeg⟩
  have hHrel_pos : 0 < H.relIndex (⊤ : Subgroup L) := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_eq_card]
    exact Nat.card_pos
  exact theorem_6_8_nonkernel_source_strict_lower_bound_of_extra
    hSbot hsemi hfamily hXS1 dS1 hdS1 η1 hηnotX hηdeg hHrel_pos

theorem theorem_6_8_endpoint_small_bound_of_obstruction_nonkernel
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hZnorm : Z.Normal)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hunionS1 : X ∪ Y ⊆ S1)
    (hS1sub : S1 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (hS1coh : coherentFamily S1 T)
    {ψ : Section1.ClassFunction L}
    (hψS : ψ ∈ S)
    (hψnotS1 : ψ ∉ S1)
    (hψnotUnion : ψ ∉ X ∪ Y)
    (hnotPair : ¬ coherentFamily
      (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
        Finset (Section1.ClassFunction L))) T) :
    (((Z.relIndex H) * (Nat.card Z - 1) ^ (2 : ℕ) : ℕ) : ℝ) <
      ((4 * (Nat.card W1) ^ (2 : ℕ) : ℕ) : ℝ) := by
  classical
  have : Z.Normal := hZnorm
  have hXS1 : X ⊆ S1 := by
    intro χ hχX
    exact hunionS1 (Finset.mem_union.mpr (Or.inl hχX))
  rcases theorem_6_8_exists_intermediate_degree_relIndex h68 hfamily hunionS1 with
    ⟨η1, hηdeg⟩
  rcases theorem_6_8_pf56_numeric_obstruction_with_degree_data
      h52 hSbot hZnorm hfamily hS1sub hS1closed hS1coh
      hψS hψnotS1 hψnotUnion hnotPair η1 hηdeg with
    ⟨dS1, hdS1, d, dψ, hdsq, _hψdeg, hdψ, hupper⟩
  have hstrict :
      ((Nat.card W1 * Z.relIndex H * (Nat.card Z - 1) : ℕ) : ℝ) <
        ∑ η : S1,
          (((dS1 η : ℝ) ^ (2 : ℕ)) /
            Section5.cfNormSq (η : Section1.ClassFunction L)) :=
    theorem_6_8_nonkernel_source_strict_lower_bound_of_intermediate
      h68 hSbot hsemi hfamily hZcomm hXS1 hunionS1 dS1 hdS1
  have hW1pos : 0 < Nat.card W1 := Nat.card_pos
  have hZrelpos : 0 < Z.relIndex H := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos
  have hHindex : H.relIndex (⊤ : Subgroup L) = Nat.card W1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hsmall :
      (((Z.relIndex H) * (Nat.card Z - 1) ^ (2 : ℕ) : ℕ) : ℝ) <
        ((4 * (Nat.card W1) ^ (2 : ℕ) : ℕ) : ℝ) :=
    theorem_6_8_endpoint_numeric_small_bound
      (w := Nat.card W1) (q := H.relIndex (⊤ : Subgroup L))
      (r := Z.relIndex H) (n := Nat.card Z - 1)
      (d := d) (dψ := dψ)
      hW1pos hZrelpos hHindex hstrict hupper hdψ hdsq
  exact hsmall

theorem theorem_6_8_endpoint_contradiction_of_obstruction_nonkernel
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hSbot : inducedKernelFamily H ⊥ S)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hcase : theorem_6_8_caseAData H W2 Z ∨
      (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z))
    (hZnorm : Z.Normal)
    (hZcomm : Z ≤ ⁅H,H⁆)
    (hZneComm : Z ≠ ⁅H,H⁆)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (hunionS1 : X ∪ Y ⊆ S1)
    (hS1sub : S1 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (hS1coh : coherentFamily S1 T)
    {ψ : Section1.ClassFunction L}
    (hψS : ψ ∈ S)
    (hψnotS1 : ψ ∉ S1)
    (hψnotUnion : ψ ∉ X ∪ Y)
    (hnotPair : ¬ coherentFamily
      (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
        Finset (Section1.ClassFunction L))) T) :
    False := by
  have hsmall :
      (((Z.relIndex H) * (Nat.card Z - 1) ^ (2 : ℕ) : ℕ) : ℝ) <
        ((4 * (Nat.card W1) ^ (2 : ℕ) : ℕ) : ℝ) :=
    theorem_6_8_endpoint_small_bound_of_obstruction_nonkernel
      h68 h52 hSbot hsemi hZnorm hZcomm hfamily
      hunionS1 hS1sub hS1closed hS1coh
      hψS hψnotS1 hψnotUnion hnotPair
  have hZrelpos : 0 < Z.relIndex H := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos
  rcases hcase with hA | hB
  · have hAbound : 2 * Nat.card W1 ≤ Nat.card Z - 1 :=
      theorem_6_8_caseA_card_bound_of_branch h68 hpQ hA hfamily
    exact theorem_6_8_endpoint_caseA_arithmetic_contradiction
      hZrelpos hsmall hAbound
  · rcases hB with ⟨hcaseC2, hBdata⟩
    rcases theorem_6_8_caseB_card_bounds h68 hcaseC2 hBdata hZneComm with
      ⟨hrelbound, hZbound⟩
    exact theorem_6_8_endpoint_caseB_arithmetic_contradiction
      hsmall hrelbound hZbound

public theorem theorem_6_8_nonabelianPQuotient_of_not_coherent
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hfrob : frobeniusQuotientWithKernel H ⁅H, H⁆)
    (hnot : ¬ coherentFamily S T) :
    ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p := by
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have h64 : hypothesis_6_4_statement H ⊥ ⁅H, H⁆ S T :=
    theorem_6_8_hypothesis_6_4_commutator_of_source_bridges h68' h52 hfrob
  exact theorem_6_5_b H ⊥ ⁅H, H⁆ S S T h64 hSbot hnot


theorem theorem_6_8_of_theorem_6_8_3_and_branch_bridges
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h52Frob :
      frobeniusWithKernel (⊤ : Subgroup L) H →
        Section5.hypothesis_5_2_statement S T)
    (hfrobQuotC2 :
      theorem_6_8_hypothesis L H W1 W2 W S T →
      caseC2Hypothesis L H W1 W2 W T →
        frobeniusQuotientWithKernel H ⁅H,H⁆)
    (h83 : ∀ {W2' Z : Subgroup L}
        {SZ X Y : Finset (Section1.ClassFunction L)},
        theorem_6_8_3_statement L H W1 W2' W Z S SZ X Y T) :
    (theorem_6_8_hypothesis L H W1 W2 W S T → coherentFamily S T) := by
  intro h68
  by_contra hnot
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hcase⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  let Z₀ : Subgroup L := centerIn H ⊓ ⁅H, H⁆
  have hZ₀H : Z₀ ≤ H := by
    exact inf_le_right.trans (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
  have hfamily₀ := theorem_6_8_familyData_of_Z hHnorm hSbot hZ₀H
  rcases hcase with hfrob | hcaseC2
  · have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
      ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, Or.inl hfrob⟩
    have h52 : Section5.hypothesis_5_2_statement S T := h52Frob hfrob
    have hfrobQuot : frobeniusQuotientWithKernel H ⁅H,H⁆ :=
      theorem_6_8_frobeniusQuotient_commutator_of_frobenius hHne hnil hfrob
    have hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p :=
      theorem_6_8_nonabelianPQuotient_of_not_coherent h68' h52 hfrobQuot hnot
    have h68bot : theorem_6_8_hypothesis L H W1 (⊥ : Subgroup L) W S T :=
      theorem_6_8_hypothesis_with_bot_W2_of_frobenius
        (L := L) (H := H) (W1 := W1) (W2 := W2) (W := W)
        (S := S) (T := T) h68' hfrob
    have hcaseData :
        theorem_6_8_caseAData H (⊥ : Subgroup L) Z₀ ∨
          (caseC2Hypothesis L H W1 (⊥ : Subgroup L) W T ∧
            theorem_6_8_caseBData H (⊥ : Subgroup L) Z₀) := by
      exact Or.inl (theorem_6_8_caseAData_bot H)
    exact hnot (h83 h68bot hpQ hcaseData hfamily₀)
  · have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
      ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, Or.inr hcaseC2⟩
    have h52 : Section5.hypothesis_5_2_statement S T :=
      theorem_6_8_hypothesis_5_2_of_caseC2 h68' hcaseC2
    have hfrobQuot : frobeniusQuotientWithKernel H ⁅H,H⁆ :=
      hfrobQuotC2 h68' hcaseC2
    have hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p :=
      theorem_6_8_nonabelianPQuotient_of_not_coherent h68' h52 hfrobQuot hnot
    rcases theorem_6_8_case_split_of_caseC2 hcaseC2 with hA | hB
    · have hcaseData :
          theorem_6_8_caseAData H W2 Z₀ ∨
            (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z₀) := by
        exact Or.inl hA
      exact hnot (h83 h68' hpQ hcaseData hfamily₀)
    · let ZB : Subgroup L := W2
      have hZBH : ZB ≤ H := by
        exact hB.2.2.1.trans (Subgroup.commutator_le_left (H₁ := H) (H₂ := H))
      have hfamilyB := theorem_6_8_familyData_of_Z hHnorm hSbot hZBH
      have hcaseData :
          theorem_6_8_caseAData H W2 ZB ∨
            (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 ZB) := by
        exact Or.inr ⟨hcaseC2, hB⟩
      exact hnot (h83 h68' hpQ hcaseData hfamilyB)

set_option maxHeartbeats 160000000 in
theorem theorem_6_8_caseA_union_coherent_of_caseData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {H W1 W2 W Z : Subgroup L}
    {S SZ X Y : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
    (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
    (hA : theorem_6_8_caseAData H W2 Z)
    (hfamily : theorem_6_8_familyData H Z S SZ X Y)
    (h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T) :
    coherentFamily (X ∪ Y) T := by
  classical
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  rcases hpQ with ⟨p, hpQp⟩
  rcases hpQp with
    ⟨hbotH, hbotnormH, hbotnorm, hHnormQ, hpprime, hQp, hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hpQp' : nonabelianPQuotient (⊥ : Subgroup L) H p :=
    ⟨hbotH, hbotnormH, hbotnorm, hHnormQ, hpprime, hQp, hnoncomm⟩
  have hpQ' : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p :=
    ⟨p, hpQp'⟩
  rcases theorem_6_8_Z_center_normal_ne_bot_of_caseData h68' hpQ'
      (Or.inl hA) with
    ⟨hZne, _hZcenter, hZnorm⟩
  have : Z.Normal := hZnorm
  have hZcomm : Z ≤ ⁅H,H⁆ :=
    theorem_6_8_Z_le_commutator_of_caseData
      (G := G) (L := L) (H := H) (W1 := W1) (W2 := W2)
      (W := W) (Z := Z) (T := T) (Or.inl hA)
  rcases theorem_6_8_theorem_6_7_base_hypothesis_ambient_card_of_caseA
      h68' hpQp' hA hfamily with
    ⟨P, hbase, hfactor⟩
  rcases theorem_6_8_Y_coherentExtension_of_familyData h68' hfamily with
    ⟨τ₁, hτ₁⟩
  rcases theorem_6_8_exists_Y_degree_relIndex h68' hfamily with
    ⟨η₁, hη₁Y, _hη₁deg⟩
  have hsigned : Section3.IsSignedIrreducibleCharacter (τ₁ η₁) :=
    theorem_6_8_coherentExtension_mem_signedIrreducible hτ₁ hη₁Y
      (theorem_6_8_Y_irreducible_of_familyData h68' hfamily η₁ hη₁Y)
  have hXdata :
      (∀ χ : Section1.ClassFunction L, χ ∈ X ↔
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            ¬ Section1.subgroupInKernel' χ Z) ∧
        coherentFamily X T := by
    rcases hbranch with hfrob | hcaseC2
    · exact theorem_6_8_caseA_X_data_of_frobenius
        h68' hfrob hpQ' hA hfamily
    · rcases hcaseC2 with ⟨⟨d⟩, hprime, hW2comm⟩
      exact theorem_6_8_caseA_X_data_of_quotient_pf45
        h68' ⟨⟨d⟩, hprime, hW2comm⟩ hpQ' hA hfamily d
  rcases hXdata with ⟨hXchar, hXcoh⟩
  rcases theorem_6_8_X_degree_data_of_character hXchar with
    ⟨dX, hdegX⟩
  rcases theorem_6_8_coherentExtension_of_coherentFamily hXcoh with
    ⟨τ₂, hτ₂⟩
  have hXnonempty : X.Nonempty := by
    rcases hXcoh with
      ⟨_hsrcX, hspanX, _τX, _hIsoX, _hvirtX, _hagreeX⟩
    rcases hspanX with ⟨φ, hφspanOn, hφne⟩
    by_contra hXempty
    have hXeq : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXempty
    subst X
    rcases hφspanOn.1 with ⟨v, hφeq⟩
    apply hφne
    rw [hφeq]
    ext g
    simp [Section1.evalCoeff]
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hZne with ⟨z, hz⟩
  have hbaseData : ∀ χ₀ : Section1.ClassFunction L, χ₀ ∈ X →
      (∀ χ : Section1.ClassFunction L, χ ∈ X →
        ∃ d : ℕ, Section1.degree χ = (d : ℂ) * Section1.degree χ₀) →
      (∃ X₁ : Section1.ClassFunction G,
        orthogonalToTransformedFinset Y τ₁ X₁ ∧
          T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
            X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • τ₁ η₁) ∨
        ∃ η₂ : Section1.ClassFunction L,
          Y.card = 2 ∧ η₂ ∈ Y ∧ η₂ ≠ η₁ ∧
            ∃ X₁ : Section1.ClassFunction G,
              orthogonalToTransformedFinset Y τ₁ X₁ ∧
                T (χ₀ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • η₁) =
                  X₁ - (Section1.degree χ₀ / (Nat.card W1 : ℂ)) • (-τ₁ η₂) := by
    intro χ₀ hχ₀X hmul
    exact theorem_6_8_caseA_base_shift_data_of_residual_kernel_selected
      P L h68' hSbot hsemi hfamily hZcomm h52union hτ₂ hτ₁
      hXchar dX hdegX hbase hsigned hη₁Y hχ₀X hmul z hz hfactor
  exact theorem_6_8_caseA_union_coherent_of_selected_base_shift_data
    hSbot hsemi hfamily hZcomm h52union hpQp' hτ₂ hτ₁
    hη₁Y hXnonempty hbaseData

-- set_option maxHeartbeats 1600000 in
theorem theorem_6_8_3
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W Z : Subgroup L)
    (S SZ X Y : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_8_3_statement L H W1 W2 W Z S SZ X Y T := by
  intro h68 hpQ hcase hfamily
  classical
  by_contra hnotS
  rcases h68 with ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have h68' : theorem_6_8_hypothesis L H W1 W2 W S T :=
    ⟨hsemi, hodd, hHne, hnil, hTI, hSbot, hT, hbranch⟩
  have hHnorm : H.Normal := theorem_6_8_left_normal_of_semidirect_top hsemi
  have : H.Normal := hHnorm
  have h52 : Section5.hypothesis_5_2_statement S T :=
    theorem_6_8_hypothesis_5_2_of_branch h68'

  have hunionSubset : X ∪ Y ⊆ S := by
    intro χ hχ
    rcases Finset.mem_union.mp hχ with hχX | hχY
    · exact theorem_6_8_familyData_X_subset_S hfamily hχX
    · exact theorem_6_8_familyData_Y_subset_S hSbot hfamily hχY
  have hunionNonempty : (X ∪ Y).Nonempty :=
    by
      rcases theorem_6_8_exists_Y_degree_relIndex h68' hfamily with
        ⟨η, hηY, _hηdeg⟩
      exact ⟨η, Finset.mem_union.mpr (Or.inr hηY)⟩
  have hunionClosed : ∀ χ : Section1.ClassFunction L, χ ∈ X ∪ Y →
      Section1.conjugateCharacter χ ∈ X ∪ Y := by
    rcases hfamily with ⟨_hZH, hSZ, hXeq, hY⟩
    intro χ hχ
    rcases Finset.mem_union.mp hχ with hχX | hχY
    · exact Finset.mem_union.mpr
        (Or.inl (theorem_6_6_diff_conjugate_closed hSbot hSZ hXeq χ hχX))
    · exact Finset.mem_union.mpr
        (Or.inr (inducedKernelFamily_conjugate_mem hY hχY))
  have h52union : Section5.hypothesis_5_2_statement (X ∪ Y) T :=
    Section5.hypothesis_5_2_statement_subset
      hunionSubset hunionNonempty hunionClosed h52

  have hcaseA_union :
      theorem_6_8_caseAData H W2 Z → coherentFamily (X ∪ Y) T := by
    intro hA
    exact theorem_6_8_caseA_union_coherent_of_caseData
      h68' hpQ hA hfamily h52union

  have hunion : coherentFamily (X ∪ Y) T := by
    rcases hcase with hA | hB
    · exact hcaseA_union hA
    · exact theorem_6_8_caseB_union_coherent_of_projection
        h52union h68' hpQ hB.1 hB.2 hfamily

  have hAU : X ∪ Y ⊆ S := hunionSubset
  have hAcl : ∀ χ : Section1.ClassFunction L, χ ∈ X ∪ Y →
      Section1.conjugateCharacter χ ∈ X ∪ Y := hunionClosed
  have hUcl : ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.conjugateCharacter χ ∈ S :=
    inducedKernelFamily_conjugate_closed hSbot

  have data := finset_closed_maximal_obstruction
      (conj := Section1.conjugateCharacter)
      (hconj := by intro χ; ext g; simp [Section1.conjugateCharacter])
      (P := fun U => coherentFamily U T)
      (A := X ∪ Y) (U := S)
      (hAU := hAU)
      (hAcl := hAcl)
      (hUcl := hUcl)
      (hPA := hunion) (hnotU := hnotS)

  rcases data with
    ⟨S1, ψ, hunionS1, hS1sub, hS1closed, hS1coh,
      hψS, hψnotS1, hnotPair⟩

  have hψnotUnion : ψ ∉ X ∪ Y := by
    intro hψUnion
    exact hψnotS1 (hunionS1 hψUnion)

  -- theorem theorem_6_8_endpoint_basic_inputs_of_not_coherent
  --   {G : Type u} [Group G] [Finite G]
  --   {L : Subgroup G}
  --   {H W1 W2 W Z : Subgroup L}
  --   {S SZ X Y : Finset (Section1.ClassFunction L)}
  --   {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
  --   (h68 : theorem_6_8_hypothesis L H W1 W2 W S T)
  --   (hpQ : ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p)
  --   (hcase : theorem_6_8_caseAData H W2 Z ∨
  --     (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z))
  --   (hfamily : theorem_6_8_familyData H Z S SZ X Y)
  --   (hunion : coherentFamily (X ∪ Y) T)
  --   (hnotS : ¬ coherentFamily S T) :
  --   Section5.hypothesis_5_2_statement S T ∧
  --     inducedKernelFamily H ⊥ S ∧
  --       Z.Normal ∧ Z ≤ ⁅H,H⁆ ∧ Z ≠ ⁅H,H⁆

  rcases theorem_6_8_endpoint_basic_inputs_of_not_coherent
      (G := G) (L := L) (H := H) (W1 := W1) (W2 := W2) (W := W) (Z := Z)
      (S := S) (SZ := SZ) (X := X) (Y := Y) (T := T)
      h68' hpQ hcase hfamily hunion hnotS with
    ⟨h52endpoint, hSbotEndpoint, hZnorm, hZcomm, hZneComm⟩

  exact theorem_6_8_endpoint_contradiction_of_obstruction_nonkernel
    h68' h52endpoint hSbotEndpoint hsemi hpQ hcase hZnorm hZcomm hZneComm
    hfamily hunionS1 hS1sub hS1closed hS1coh
    hψS hψnotS1 hψnotUnion hnotPair

public theorem theorem_6_8
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    (theorem_6_8_hypothesis L H W1 W2 W S T → coherentFamily S T) := by
  intro h68
  exact theorem_6_8_of_theorem_6_8_3_and_branch_bridges
    L H W1 W2 W S T
    (fun hfrob => theorem_6_8_hypothesis_5_2_of_frobenius h68 hfrob)
    theorem_6_8_frobeniusQuotient_commutator_of_caseC2
    (fun {W2' Z} {SZ X Y} =>
      theorem_6_8_3 L H W1 W2' W Z S SZ X Y T)
    h68

end CFSG.Section6
