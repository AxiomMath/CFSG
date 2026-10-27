module

public import CFSG.Quasithin.H13.L32AKG1468j
public import CFSG.Quasithin.EmptyFaithful.S153QPD6

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

omit [Group G] in
theorem exists_factor_of_surjective {K H N : Type*} [Group K] [Group H] [Group N] (φ : K →* H)
    (hφ : Function.Surjective φ) (ψ : K →* N) (hle : φ.ker ≤ ψ.ker) :
    ∃ θ : H →* N, (∀ k, θ (φ k) = ψ k) ∧ (Function.Surjective ψ → Function.Surjective θ) ∧
      (IsPGroup 2 ψ.ker → IsPGroup 2 θ.ker) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let θ : H →* N := (QuotientGroup.lift φ.ker ψ hle).comp e.symm.toMonoidHom
  have hθ : ∀ k, θ (φ k) = ψ k := by
    intro k
    have h1 : e.symm (φ k) = (k : K ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift φ.ker ψ hle (e.symm (φ k)) = ψ k
    rw [h1]
    rfl
  refine ⟨θ, hθ, fun hs n => ?_, fun hk z => ?_⟩
  · obtain ⟨k, rfl⟩ := hs n
    exact ⟨φ k, hθ k⟩
  · obtain ⟨h, hh⟩ := z
    obtain ⟨k, rfl⟩ := hφ h
    have hk1 : ψ k = 1 := by
      rw [← hθ]
      exact hh
    obtain ⟨j, hj⟩ := hk ⟨k, hk1⟩
    refine ⟨j, Subtype.ext ?_⟩
    have h2 : k ^ 2 ^ j = 1 := congrArg Subtype.val hj
    show (φ k) ^ 2 ^ j = 1
    rw [← map_pow, h2, map_one]

variable [Finite G] {Y R M I : Subgroup G}

structure BlkCtx (Y R M I : Subgroup G) : Prop where
  hyp : HypC23 Y R M
  comp : I ∈ cComp Y
  normal : (I.subgroupOf Y).Normal
  charTwo : CharTwo I
  quasi : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I)
  not_le : ¬ I ≤ M
  norm : R ≤ Subgroup.normalizer (I : Set G)
  quot : Nonempty (↥(oTwoUpper (I ⊓ M)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (I ⊓ M)) ≃*
    alternatingGroup (Fin 5))

theorem c27_facts (hC27 : ASC27Statement G) (c : BlkCtx Y R M I) :
    I ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (I ⊔ R)) : Set G) ∧
      I ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (I ⊔ R)) : Set G) ≤ oTwoZIn I ∧
        pCoreOf 2 I ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (I ⊔ R)) : Set G) := by
  have h1 := (hC27 Y R M I _ c.hyp c.comp c.quasi c.charTwo c.not_le c.norm rfl).1
  exact ⟨SBc17.le_normalizer_V I R, SBc17.inf_centralizer_le_oTwoZIn h1.2.1, fun x hx =>
    (h1.1 (SBc17.pCoreOf_le_pCoreOf_sup c.norm hx)).2⟩

omit [Finite G] in
theorem oTwoUpper_le_inf : oTwoUpper (I ⊓ M) ≤ M ⊓ I :=
  (oTwoUpper_le _).trans (le_of_eq (inf_comm I M))

theorem inf_pCoreOf_le {B : Subgroup G} (hBI : B ≤ I) : B ⊓ pCoreOf 2 I ≤ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le inf_le_right)
  intro x hx
  exact SBc14.mem_normalizer_inf (Subgroup.le_normalizer hx)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I (hBI hx))

theorem exists_theta {V B : Subgroup G} (hIV : I ≤ Subgroup.normalizer (V : Set G))
    (hD : I ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn I) (hBI : B ≤ I)
    (e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5)) :
    ∃ θ : ↥(autOn B V) →* alternatingGroup (Fin 5), Function.Surjective θ ∧
      IsPGroup 2 θ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := hBI.trans hIV
  let φ := SBc17.actHom hBV
  let ψ : ↥B →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ∀ b : ↥B, ψ b = 1 ↔ (b : G) ∈ pCoreOf 2 B := by
    intro b
    show e (QuotientGroup.mk b) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact He16.mk_eq_one_iff_mem_pCoreOf' b
  have hle : φ.ker ≤ ψ.ker := by
    intro k hk
    have hkc := He17.centralizer_of_actHom_eq_one hBV k hk
    obtain ⟨-, hkcomm⟩ := mem_oTwoZIn_iff_commutator.mp (hD ⟨hBI k.2, hkc⟩)
    have hcen : ψ k ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro n
      obtain ⟨b, rfl⟩ := hψs n
      have h1 : ψ (k * b * k⁻¹ * b⁻¹) = 1 := by
        rw [hψk]
        have hm : ((k * b * k⁻¹ * b⁻¹ : ↥B) : G) ∈ B ⊓ pCoreOf 2 I :=
          ⟨(k * b * k⁻¹ * b⁻¹).2, by simpa using hkcomm (b : G) (hBI b.2)⟩
        exact inf_pCoreOf_le hBI hm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [SBc17.center_alt_bot (by norm_num), Subgroup.mem_bot] at hcen
    exact hcen
  obtain ⟨θ, -, hs, hk⟩ := exists_factor_of_surjective φ (SBc17.actHom_surjective hBV) ψ hle
  refine ⟨θ, hs hψs, hk ?_⟩
  intro z
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B ⟨((z : ↥B) : G), (hψk z).mp z.2⟩
  refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥(pCoreOf 2 B) => (y : G)) hj
  simpa using this

theorem autOn_oTwoUpper_inf {V : Subgroup G} (hIV : I ≤ Subgroup.normalizer (V : Set G)) :
    autOn (oTwoUpper (I ⊓ M)) V = oTwoUpper (autOn (M ⊓ I) V) := by
  rw [inf_comm I M]
  exact autOn_oTwoUpper (inf_le_right.trans hIV)

theorem exists_five_mem {B : Subgroup G} (e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5)) :
    ∃ a ∈ B, orderOf a = 5 := by
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨a, ha⟩ := exists_orderOf_five h60 (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact ⟨a, a.2, by rw [Subgroup.orderOf_coe, ha]⟩

end CFSG.Quasithin.H13.KGBlk
