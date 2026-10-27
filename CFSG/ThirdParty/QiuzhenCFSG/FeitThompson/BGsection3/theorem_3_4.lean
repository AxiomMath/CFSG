module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_3

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement IsMulCommutative

public instance CFSG.instMulDistribMulAction_subtype_local {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] {H : Subgroup G} [IsInvariant A G H] :
    MulDistribMulAction A H where
  smul a x := ⟨a • x.1, (IsInvariant.invariant (A := A) (G := G) (H := H) a x.1).1 x.2⟩
  one_smul x := by
    ext
    change ((1 : A) • (x : G)) = x
    simp
  mul_smul a b x := by
    ext
    change ((a * b) • (x : G)) = a • (b • (x : G))
    simpa using (mul_smul a b (x : G))
  smul_mul a x y := by
    ext
    change a • ((x : G) * (y : G)) = a • (x : G) * a • (y : G)
    simp
  smul_one a := by
    ext
    change a • (1 : G) = (1 : G)
    simp

public lemma CFSG.fixedPointSubgroup_subtype_eq_local {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] :
    fixedPointSubgroup A H = (fixedPointSubgroup A G).subgroupOf H := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ fixedPointSubgroup A G
    rw [FixedPoints.mem_subgroup] at hx ⊢
    intro a
    exact congrArg Subtype.val (hx a)
  · intro hx
    change (x : G) ∈ fixedPointSubgroup A G at hx
    rw [FixedPoints.mem_subgroup] at hx
    rw [FixedPoints.mem_subgroup]
    intro a
    apply Subtype.ext
    exact hx a

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.exists_simple_submodule_nontrivial_of_not_le_ker_of_fixedSubspace_eq_bot
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule]
    (R H : Subgroup G) (hfix : ρ.fixedSubspace R = ⊥) (hH : ¬ H ≤ ρ.ker) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R = ⊥ ∧
      ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  obtain ⟨m, hm, hHmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker (ρ := ρ) H hH
  exact ⟨m, hm, fixedSubspace_ofSubmodule'_eq_bot_of_fixedSubspace_eq_bot ρ R m hfix, hHmk⟩


set_option backward.isDefEq.respectTransparency false in
theorem CFSG.elementaryAbelian_invariant_complement_of_coprime_aut_local
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p G] (σ : MulAut G) (hcop : Nat.Coprime (orderOf σ) p)
    (B : Subgroup G) (hBσ : B.map σ.toMonoidHom = B) :
    ∃ C : Subgroup G, IsCompl B C ∧ C.map σ.toMonoidHom = C := by
  let eAdd : Additive G ≃+ Additive G := MulEquiv.toAdditive (σ : G ≃* G)
  let eLin : Additive G ≃ₗ[ZMod p] Additive G :=
    eAdd.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
  let f : Module.End (ZMod p) (Additive G) := eLin.toLinearMap
  have hpowσ : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
  have hpow_apply :
      ∀ n : ℕ, ∀ x : Additive G, Additive.toMul ((f ^ n) x) = (σ ^ n) (Additive.toMul x) := by
    intro n
    induction n with
    | zero =>
        intro x
        simp [f]
    | succ n ihn =>
        intro x
        simp [pow_succ, ihn, f, eLin, eAdd]
  have hpowf : f ^ orderOf σ = 1 := by
    ext x
    apply Additive.toMul.injective
    rw [hpow_apply]
    simp [hpowσ]
  have hne : (orderOf σ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd).1 hcop.symm
  have hsep : ((Polynomial.X ^ orderOf σ - 1 : Polynomial (ZMod p))).Separable :=
    (Polynomial.X_pow_sub_one_separable_iff).2 hne
  have hsq : Squarefree (Polynomial.X ^ orderOf σ - 1 : Polynomial (ZMod p)) :=
    hsep.squarefree
  have hsemisimple : f.IsSemisimple := by
    have haeval :
        Polynomial.aeval f (Polynomial.X ^ orderOf σ - 1 : Polynomial (ZMod p)) = 0 := by
      rw [map_sub, Polynomial.aeval_X_pow]
      simpa using sub_eq_zero.mpr hpowf
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
  let φ : AddSubgroup (Additive G) ≃o Submodule (ZMod p) (Additive G) :=
    AddSubgroup.toZModSubmodule (n := p)
  let ψ : AddSubgroup (Additive G) ≃o Subgroup G := AddSubgroup.toSubgroup'
  let Sadd : AddSubgroup (Additive G) := Subgroup.toAddSubgroup B
  let S : Submodule (ZMod p) (Additive G) := φ Sadd
  have hSinv : S ∈ f.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    have hxB : Additive.toMul x ∈ B := by
      simpa [S, Sadd, φ] using hx
    have hσxBmap : σ (Additive.toMul x) ∈ B.map σ.toMonoidHom := ⟨Additive.toMul x, hxB, rfl⟩
    have hσxB : σ (Additive.toMul x) ∈ B := by
      rw [hBσ] at hσxBmap
      exact hσxBmap
    simpa [f, eLin, eAdd, S, Sadd, φ] using hσxB
  obtain ⟨Tinv, hTcompl⟩ := (Module.End.isSemisimple_iff').1 hsemisimple ⟨S, hSinv⟩
  let T : Submodule (ZMod p) (Additive G) := Tinv
  let Tadd : AddSubgroup (Additive G) := φ.symm T
  let C : Subgroup G := ψ Tadd
  have hcompl_sub : IsCompl S T :=
    ((Module.End.invtSubmodule.isCompl_iff (f := f) (p := ⟨S, hSinv⟩) (q := Tinv))).1 hTcompl
  have hcompl_add : IsCompl Sadd Tadd := by
    have : IsCompl (φ Sadd) (φ Tadd) := by
      simpa [S, T, Tadd] using hcompl_sub
    exact ((OrderIso.isCompl_iff (f := φ) (x := Sadd) (y := Tadd))).2 this
  have hcompl : IsCompl B C :=
    IsCompl.of_orderEmbedding (RelIso.toRelEmbedding Subgroup.toAddSubgroup) hcompl_add
  have hTinv : T ∈ f.invtSubmodule := Tinv.2
  have hCmap_le : C.map σ.toMonoidHom ≤ C := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyTadd : Additive.ofMul y ∈ Tadd := by
      simpa [C, ψ] using hy
    have hyT : Additive.ofMul y ∈ T := by
      change Additive.ofMul y ∈ Submodule.toAddSubgroup T at hyTadd
      exact hyTadd
    have hσyT : f (Additive.ofMul y) ∈ T := hTinv hyT
    change Additive.ofMul (σ y) ∈ Submodule.toAddSubgroup T at hσyT
    change Additive.ofMul (σ y) ∈ Tadd
    exact hσyT
  have hCcard : Nat.card (C.map σ.toMonoidHom) = Nat.card C := by
    simpa using (Subgroup.card_map_of_injective (K := C) (f := σ.toMonoidHom) σ.injective)
  have hCeq : C.map σ.toMonoidHom = C := by
    apply Subgroup.eq_of_le_of_card_ge hCmap_le
    rw [hCcard]
  exact ⟨C, hcompl, hCeq⟩

public theorem CFSG.zpowers_eq_top_of_prime_card_of_ne_one {A : Type*} [Group A] [Finite A]
    (hAprime : Nat.Prime (Nat.card A)) {a : A} (ha : a ≠ 1) :
    Subgroup.zpowers a = ⊤ := by
  have hcard_dvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card A :=
    Subgroup.card_subgroup_dvd_card (Subgroup.zpowers a)
  have hcard_ne_one : Nat.card (Subgroup.zpowers a) ≠ 1 := by
    intro hcard
    have hbot : Subgroup.zpowers a = ⊥ := (Subgroup.eq_bot_iff_card (H := Subgroup.zpowers a)).2 hcard
    have ha_bot : a ∈ (⊥ : Subgroup A) := by simpa [hbot] using (Subgroup.mem_zpowers a)
    exact ha (by simpa using ha_bot)
  have hcard_eq : Nat.card (Subgroup.zpowers a) = Nat.card A :=
    (hAprime.eq_one_or_self_of_dvd (Nat.card (Subgroup.zpowers a)) hcard_dvd).resolve_left hcard_ne_one
  exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).1 hcard_eq

theorem CFSG.fixedPointSubgroup_zpowers_eq_bot_of_elementaryAbelian_of_proper_invariant_fixed
    {K : Type*} [Group K] [Finite K] [Nontrivial K] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q K] (σ : MulAut K) (hσ_ne : σ ≠ 1)
    (hcop : Nat.Coprime (orderOf σ) q)
    (hproper :
      ∀ H : Subgroup K, H ≠ ⊤ → H.map σ.toMonoidHom = H →
        H ≤ fixedPointSubgroup (↥(Subgroup.zpowers σ)) K) :
    fixedPointSubgroup (↥(Subgroup.zpowers σ)) K = ⊥ := by
  let B : Subgroup K := fixedPointSubgroup (↥(Subgroup.zpowers σ)) K
  by_contra hB_ne_bot
  have hBσ : B.map σ.toMonoidHom = B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      have hyB' : ∀ τ : Subgroup.zpowers σ, τ • y = y := by
        simpa [B, FixedPoints.mem_subgroup] using hyB
      change ∀ τ : Subgroup.zpowers σ, τ • (σ y) = σ y
      intro τ
      have hyσ : σ y = y := by
        simpa using hyB' ⟨σ, Subgroup.mem_zpowers σ⟩
      simpa [hyσ] using hyB' τ
    · intro hx
      refine ⟨x, hx, ?_⟩
      have hxσ : σ x = x := by
        have hx' : ∀ τ : Subgroup.zpowers σ, τ • x = x := by
          simpa [B, FixedPoints.mem_subgroup] using hx
        simpa using hx' ⟨σ, Subgroup.mem_zpowers σ⟩
      simp [hxσ]
  obtain ⟨C, hBC, hCσ⟩ :=
    elementaryAbelian_invariant_complement_of_coprime_aut_local (σ := σ) hcop B hBσ
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    have hB_bot : B = ⊥ := by simpa [hC_top] using hBC.disjoint
    exact hB_ne_bot hB_bot
  have hCfix : C ≤ B := hproper C hC_ne_top hCσ
  have hC_bot : C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact (Subgroup.disjoint_def.mp hBC.disjoint) (hCfix hx) hx
  have hB_top : B = ⊤ := by simpa [B, hC_bot] using hBC.sup_eq_top
  have hσ_eq_one : σ = 1 := by
    ext x
    have hxB : x ∈ B := by simp [hB_top]
    have hxB' : ∀ τ : Subgroup.zpowers σ, τ • x = x := by
      simpa [B, FixedPoints.mem_subgroup] using hxB
    simpa using hxB' ⟨σ, Subgroup.mem_zpowers σ⟩
  exact hσ_ne hσ_eq_one

theorem CFSG.quotient_center_nontrivial_of_not_isMulCommutative {K : Type*} [Group K]
    (hcomm : ¬ IsMulCommutative K) :
    Nontrivial (K ⧸ Subgroup.center K) := by
  by_contra htriv
  have : Subsingleton (K ⧸ Subgroup.center K) := not_nontrivial_iff_subsingleton.mp htriv
  have hcenter_top : Subgroup.center K = ⊤ :=
    QuotientGroup.subgroup_eq_top_of_subsingleton (Subgroup.center K) inferInstance
  have hcomm' : IsMulCommutative K := by
    refine ⟨⟨?_⟩⟩
    intro x y
    have hxcent : x ∈ Subgroup.center K := by simp [hcenter_top]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  exact hcomm hcomm'

public theorem CFSG.isElementaryAbelian_quotient_center_of_commutator_le_center_of_exponent_eq
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q K)]
    (hcomm : commutator K ≤ Subgroup.center K) (hexp : Monoid.exponent K = q)
    [Nontrivial (K ⧸ Subgroup.center K)] :
    IsElementaryAbelian q (K ⧸ Subgroup.center K) := by
  let : Fact (IsPGroup q (K ⧸ Subgroup.center K)) :=
    ⟨(Fact.out : IsPGroup q K).to_quotient (Subgroup.center K)⟩
  have hexpQ : Monoid.exponent (K ⧸ Subgroup.center K) ∣ q := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center K) x
    have hyq : y ^ q = 1 := by
      exact
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent K ∣ q by simp [hexp])) y
    simpa using congrArg (QuotientGroup.mk' (Subgroup.center K)) hyq
  refine
    { toIsMulCommutative :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := Subgroup.center K)).mpr hcomm
      exponent_dvd_p := by
        simpa using hexpQ }

theorem CFSG.fittingSubgroup_eq_top_of_proper_characteristic_fixed
    {K A : Type*} [Group K] [Finite K] [Nontrivial K] [Group A] [Finite A] [Nontrivial A]
    [MulDistribMulAction A K] [FaithfulSMul A K]
    (hsolvK : Group.IsSolvable K) (hcop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hproper :
      ∀ H : Subgroup K, H.Characteristic → H ≠ ⊤ → H ≤ fixedPointSubgroup A K) :
    fittingSubgroup K = ⊤ := by
  by_contra hF
  let F : Subgroup K := fittingSubgroup K
  have hFchar : F.Characteristic := fittingSubgroup_characteristic
  have hFfix : F ≤ fixedPointSubgroup A K := hproper F hFchar hF
  have hfaithF : FaithfulSMul A F := faithful_on_fitting_of_coprime (G := K) (A := A) hsolvK hcop
  have htrivA : ∀ a : A, a = 1 := by
    intro a
    exact (faithfulSMul_iff (G := A) (α := F)).1 hfaithF a <| by
      intro x
      apply Subtype.ext
      exact hFfix x.2 a
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  exact ha (htrivA a)

theorem CFSG.exists_maximal_characteristic_abelian_subgroup_local
    {G : Type*} [Group G] [Finite G] :
    ∃ A : Subgroup G,
      A.Characteristic ∧
        IsMulCommutative A ∧
        ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → A ≤ B → B = A := by
  classical
  let s : Set (Subgroup G) := {A | A.Characteristic ∧ IsMulCommutative A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor <;> infer_instance
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximal hsne
  refine ⟨A, hAmax.1.1, hAmax.1.2, ?_⟩
  intro B hBchar hBcomm hAB
  exact le_antisymm (hAmax.2 ⟨hBchar, hBcomm⟩ hAB) hAB

theorem CFSG.actsTrivially_of_proper_centralizer_maximal_characteristic_abelian_local
    {K A : Type*} [Group K] [Finite K] [Nontrivial K] [Group A] [Finite A]
    [MulDistribMulAction A K] {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q K)]
    (hqodd : q ≠ 2) (hcop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hexp : Monoid.exponent K = q)
    (E : Subgroup K) (hEchar : E.Characteristic) (hEcomm : IsMulCommutative E)
    (hproper :
      ∀ H : Subgroup K, H.Characteristic → H ≠ ⊤ → H ≤ fixedPointSubgroup A K)
    (hcent_proper : Subgroup.centralizer (E : Set K) ≠ ⊤) :
    ActsTrivially (A := A) (G := K) := by
  let D : Subgroup K := Subgroup.centralizer (E : Set K)
  have hDchar : D.Characteristic := by
    let : E.Characteristic := hEchar
    dsimp [D]
    infer_instance
  have hDfix : D ≤ fixedPointSubgroup A K := hproper D hDchar hcent_proper
  have hEelem : ∃ _ : Fact (IsPGroup q ↥E), IsElementaryAbelian q ↥E := by
    refine ⟨⟨(Fact.out : IsPGroup q K).to_subgroup E⟩, ?_⟩
    refine
      { toIsMulCommutative := hEcomm
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    have hqpowK : ((x : E) : K) ^ q = 1 := by
      exact
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (show Monoid.exponent K ∣ q by
          simp [hexp])) ((x : E) : K)
    simpa using hqpowK
  refine corollary_1_12 (G := K) (A := A) hqodd E hEelem hcop ?_
  intro g hg hq a
  exact hDfix hg a


public theorem CFSG.maximal_normal_abelian_selfCentralizing_local {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (A : Subgroup G)
    (hAnorm : A.Normal) (hAcomm : IsMulCommutative A)
    (hAmax : ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set G) ≤ A := by
  classical
  let : A.Normal := hAnorm
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hA_le_C : A ≤ C :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  by_contra hCA
  have hC_ne_A : C ≠ A := by
    intro hEq
    apply hCA
    simp [C, hEq]
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let N : Subgroup (G ⧸ A) := C.map q
  have hCnorm : C.Normal := by
    simpa [C] using (inferInstance : (Subgroup.centralizer (A : Set G)).Normal)
  have hNnorm : N.Normal := by
    dsimp [N]
    infer_instance
  have hN_ne_bot : N ≠ ⊥ := by
    intro hNbot
    have hsup : A ⊔ C = A := by
      simpa [q, N, C] using congrArg (Subgroup.comap q) hNbot
    apply hCA
    rw [sup_eq_left] at hsup
    simpa [C] using hsup
  obtain ⟨M, hMnorm, hMN, hM_ne_bot, hMmin⟩ :=
    exists_minimal_normal_le (G := G ⧸ A) N hNnorm hN_ne_bot
  let : M.Normal := hMnorm
  let : IsMinimalNormal M := {
    minimal := by
      intro K _ hKM
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hMmin K inferInstance hKM hKbot)
  }
  have hQp : IsPGroup p (G ⧸ A) := (Fact.out : IsPGroup p G).to_quotient A
  let : Fact (IsPGroup p (G ⧸ A)) := ⟨hQp⟩
  let : Group.IsNilpotent (G ⧸ A) := hQp.isNilpotent
  have : Group.IsSolvable (G ⧸ A) := by infer_instance
  have : Group.IsSolvable M := by infer_instance
  have hM_centerIn :
      M ≤ centerIn (G := G ⧸ A) (fittingSubgroup (G ⧸ A)) :=
    minimalNormal_solvable_le_centerIn_fittingSubgroup (G := G ⧸ A) M
  have hfit_top : fittingSubgroup (G ⧸ A) = ⊤ :=
    fitting_eq_top_of_nilpotent (G := G ⧸ A)
  have hM_center' : M ≤ Subgroup.centralizer (Set.univ : Set (G ⧸ A)) := by
    simpa [centerIn, hfit_top] using hM_centerIn
  have hM_center : M ≤ Subgroup.center (G ⧸ A) := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro y
    exact (Subgroup.mem_centralizer_iff.mp (hM_center' hm)) y (by trivial)
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
  obtain ⟨xbar, hxbar_ne⟩ := exists_ne (1 : M)
  let K : Subgroup (G ⧸ A) := Subgroup.zpowers (xbar : G ⧸ A)
  have hK_le_M : K ≤ M := by
    refine (Subgroup.zpowers_le).2 ?_
    exact xbar.property
  have hK_le_center : K ≤ Subgroup.center (G ⧸ A) :=
    hK_le_M.trans hM_center
  have hKnorm : K.Normal := by
    refine ⟨?_⟩
    intro n hn g
    have hncent : n ∈ Subgroup.center (G ⧸ A) := hK_le_center hn
    have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hncent) g
    rw [show g * n * g⁻¹ = n by
      calc
        g * n * g⁻¹ = (n * g) * g⁻¹ := by rw [hcomm]
        _ = n := by simp [mul_assoc]]
    exact hn
  have hK_ne_bot : K ≠ ⊥ := by
    intro hKbot
    have hxbot : ((xbar : G ⧸ A) ∈ (⊥ : Subgroup (G ⧸ A))) := by
      simpa [K, hKbot] using (Subgroup.mem_zpowers (xbar : G ⧸ A))
    have hxbar_one : xbar = 1 := by
      apply Subtype.ext
      simpa using hxbot
    exact hxbar_ne hxbar_one
  have hK_eq_M : K = M := hMmin K hKnorm hK_le_M hK_ne_bot
  have hxN : (xbar : G ⧸ A) ∈ N := hMN xbar.property
  rcases hxN with ⟨x, hxC, hqx⟩
  let B : Subgroup G := A ⊔ Subgroup.zpowers x
  have hzx_cent : Subgroup.zpowers x ≤ C := (Subgroup.zpowers_le).2 hxC
  have hBcomm : IsMulCommutative B := by
    refine (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).1 ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    change u ∈ A ⊔ Subgroup.zpowers x at hu
    change v ∈ A ⊔ Subgroup.zpowers x at hv
    rcases (Subgroup.mem_sup_of_normal_left (x := u) (s := A) (t := Subgroup.zpowers x)).1 hu with
      ⟨a₁, ha₁, z₁, hz₁, rfl⟩
    rcases (Subgroup.mem_sup_of_normal_left (x := v) (s := A) (t := Subgroup.zpowers x)).1 hv with
      ⟨a₂, ha₂, z₂, hz₂, rfl⟩
    symm
    have hz₁a₂ : z₁ * a₂ = a₂ * z₁ :=
      ((Subgroup.mem_centralizer_iff.mp (hzx_cent hz₁)) a₂ ha₂).symm
    have hz₂a₁ : z₂ * a₁ = a₁ * z₂ :=
      ((Subgroup.mem_centralizer_iff.mp (hzx_cent hz₂)) a₁ ha₁).symm
    have ha₁a₂ : a₁ * a₂ = a₂ * a₁ := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := A)).comm ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
    have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Subgroup.zpowers x)).comm ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩)
    calc
      (a₁ * z₁) * (a₂ * z₂) = a₁ * a₂ * (z₁ * z₂) := by
        rw [mul_assoc, ← mul_assoc z₁ a₂ z₂, hz₁a₂]
        simp [mul_assoc]
      _ = a₂ * a₁ * (z₂ * z₁) := by rw [ha₁a₂, hz₁z₂]
      _ = a₂ * (z₂ * (a₁ * z₁)) := by
        have hinner : a₁ * (z₂ * z₁) = z₂ * (a₁ * z₁) := by
          calc
            a₁ * (z₂ * z₁) = (a₁ * z₂) * z₁ := by simp [mul_assoc]
            _ = (z₂ * a₁) * z₁ := by rw [← hz₂a₁]
            _ = z₂ * (a₁ * z₁) := by simp [mul_assoc]
        rw [mul_assoc, hinner]
      _ = (a₂ * z₂) * (a₁ * z₁) := by
        simp [mul_assoc]
  have hB_eq_comap : B = Subgroup.comap q M := by
    ext g
    constructor
    · intro hg
      change g ∈ A ⊔ Subgroup.zpowers x at hg
      rcases (Subgroup.mem_sup_of_normal_left (x := g) (s := A) (t := Subgroup.zpowers x)).1 hg with
        ⟨a, ha, z, hz, rfl⟩
      rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, rfl⟩
      change q (a * x ^ k) ∈ M
      have hxpow : q (x ^ k) ∈ M := by
        have hxpowK : q (x ^ k) ∈ K := by
          have hxpowK' : (q x) ^ k ∈ K := by
            change (q x) ^ k ∈ Subgroup.zpowers (xbar : G ⧸ A)
            rw [hqx]
            exact Subgroup.zpow_mem_zpowers (xbar : G ⧸ A) k
          simpa using hxpowK'
        simpa [hK_eq_M] using hxpowK
      have haq : q a = 1 := (QuotientGroup.eq_one_iff (N := A) a).2 ha
      simpa [map_mul, haq] using hxpow
    · intro hg
      change q g ∈ M at hg
      rw [← hK_eq_M, Subgroup.mem_zpowers_iff] at hg
      rcases hg with ⟨k, hk⟩
      have hga : g * (x ^ k)⁻¹ ∈ A := by
        have hqg : q g = q x ^ k := by
          simpa [hqx] using hk.symm
        refine (QuotientGroup.eq_one_iff (N := A) (g * (x ^ k)⁻¹)).mp ?_
        calc
          q (g * (x ^ k)⁻¹) = q g * (q (x ^ k))⁻¹ := by simp [map_mul]
          _ = (q x ^ k) * (q (x ^ k))⁻¹ := by rw [hqg]
          _ = 1 := by simp
      show g ∈ A ⊔ Subgroup.zpowers x
      exact (Subgroup.mem_sup_of_normal_left (x := g) (s := A) (t := Subgroup.zpowers x)).2
        ⟨g * (x ^ k)⁻¹, hga, x ^ k, Subgroup.zpow_mem_zpowers x k, by simp [mul_assoc]⟩
  have hBnorm : B.Normal := by
    rw [hB_eq_comap]
    infer_instance
  have hAB : A ≤ B := le_sup_left
  have hB_ne_A : B ≠ A := by
    intro hBA
    have hxB : x ∈ B := by
      change x ∈ A ⊔ Subgroup.zpowers x
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hxA : x ∈ A := by simpa [hBA] using hxB
    have hxbar_val_one : (xbar : G ⧸ A) = 1 := by
      have hqx_one : q x = 1 := (QuotientGroup.eq_one_iff (N := A) x).2 hxA
      simpa [hqx] using hqx_one
    have hxbar_one : xbar = 1 := by
      apply Subtype.ext
      simpa using hxbar_val_one
    exact hxbar_ne hxbar_one
  have hBA_eq : B = A := hAmax B hBnorm hBcomm hAB
  exact hB_ne_A hBA_eq


public theorem CFSG.classTwo_exponent_prime_of_proper_characteristic_fixed
    {K A : Type*} [Group K] [Finite K] [Nontrivial K] [Group A] [Finite A] [Nontrivial A]
    [MulDistribMulAction A K] [FaithfulSMul A K] {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q K)]
    (hqodd : q ≠ 2) (hcop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hproper :
      ∀ H : Subgroup K, H.Characteristic → H ≠ ⊤ → H ≤ fixedPointSubgroup A K) :
    commutator K ≤ Subgroup.center K ∧ Monoid.exponent K = q := by
  obtain ⟨H, hHchar, hHcomm, -, hHexp, hAfixp⟩ := theorem_1_13 (G := K) (p := q) hqodd
  by_cases hHtop : H = ⊤
  · subst hHtop
    have hcenter_top : centerIn (G := K) (⊤ : Subgroup K) = Subgroup.center K := by
      ext x
      simp [centerIn, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    refine ⟨?_, ?_⟩
    · rw [← _root_.commutator_def, hcenter_top] at hHcomm
      exact hHcomm
    · simpa using hHexp
  · have hHfix : H ≤ fixedPointSubgroup A K := hproper H hHchar hHtop
    let Afix : Subgroup (MulAut K) := fixingSubgroup (M := MulAut K) (α := K) (H : Set K)
    let φ : A →* MulAut K := MulDistribMulAction.toMulAut A K
    have hφrange_le : φ.range ≤ Afix := by
      intro σ hσ
      rcases hσ with ⟨a, rfl⟩
      exact (mem_fixingSubgroup_iff (M := MulAut K) (s := (H : Set K))).2 <| by
        intro x hx
        exact hHfix hx a
    have hφrange_sub : IsPGroup q (φ.range.subgroupOf Afix) := hAfixp.to_subgroup _
    have hφrange : IsPGroup q φ.range := by
      exact hφrange_sub.of_equiv (Subgroup.subgroupOfEquivOfLe hφrange_le)
    have hfaith :
        ∀ a : A, (∀ x : K, a • x = x) → a = 1 :=
      (faithfulSMul_iff (G := A) (α := K)).1 inferInstance
    have hφinj : Function.Injective φ := by
      intro a b hab
      have hfix : ∀ x : K, (b⁻¹ * a) • x = x := by
        intro x
        have hax : a • x = b • x := by
          simpa [φ] using congrArg (fun f : MulAut K => f x) hab
        calc
          (b⁻¹ * a) • x = b⁻¹ • (a • x) := by simp [mul_smul]
          _ = b⁻¹ • (b • x) := by rw [hax]
          _ = x := by simp
      have hba : b⁻¹ * a = 1 := hfaith (b⁻¹ * a) hfix
      calc
        a = b * (b⁻¹ * a) := by simp
        _ = b := by simp [hba]
    have hφrange_inj : Function.Injective φ.rangeRestrict := by
      intro a b hab
      exact hφinj (by simpa using congrArg Subtype.val hab)
    let e : A ≃* φ.range :=
      MulEquiv.ofBijective φ.rangeRestrict ⟨hφrange_inj, φ.rangeRestrict_surjective⟩
    have hAp : IsPGroup q A := hφrange.of_equiv e.symm
    obtain ⟨nK, hnK_pos, hcardK⟩ :=
      (IsPGroup.nontrivial_iff_card (p := q) (G := K) (hG := Fact.out)).mp inferInstance
    have hqdvdK : q ∣ Nat.card K := by
      rw [hcardK]
      exact dvd_pow_self q (Nat.ne_of_gt hnK_pos)
    have hqnotdvdA : ¬ q ∣ Nat.card A := by
      have hAqcop : Nat.Coprime (Nat.card A) q := Nat.Coprime.of_dvd_right hqdvdK hcop
      exact (Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hAqcop.symm
    obtain ⟨nA, hnA_pos, hcardA⟩ :=
      (IsPGroup.nontrivial_iff_card (p := q) (G := A) (hG := hAp)).mp inferInstance
    have hqdvdA : q ∣ Nat.card A := by
      rw [hcardA]
      exact dvd_pow_self q (Nat.ne_of_gt hnA_pos)
    exact (hqnotdvdA hqdvdA).elim

public theorem CFSG.exists_prime_isPGroup_of_nilpotent_of_proper_characteristic_fixed
    {K A : Type*} [Group K] [Finite K] [Nontrivial K] [Group A] [Finite A] [Nontrivial A]
    [MulDistribMulAction A K] [FaithfulSMul A K] (hnil : Group.IsNilpotent K)
    (hproper :
      ∀ H : Subgroup K, H.Characteristic → H ≠ ⊤ → H ≤ fixedPointSubgroup A K) :
    ∃ q : ℕ, Nat.Prime q ∧ IsPGroup q K := by
  by_contra hno
  push Not at hno
  have hSylow_fix :
      ∀ p ∈ (Nat.card K).primeFactors,
        ((default : Sylow p K) : Subgroup K) ≤ fixedPointSubgroup A K := by
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpprime⟩
    let P : Sylow p K := default
    have hP_normal : ((P : Subgroup K)).Normal := Group.IsNilpotent.sylow_normal hnil p P
    have hP_char : ((P : Subgroup K)).Characteristic := Sylow.characteristic_of_normal P hP_normal
    have hP_ne_top : ((P : Subgroup K)) ≠ ⊤ := by
      intro hPtop
      exact hno p hpprime (by
        have htop_p : IsPGroup p ↥(⊤ : Subgroup K) := by
          exact P.isPGroup'.of_equiv (MulEquiv.subgroupCongr hPtop)
        exact htop_p.of_equiv Subgroup.topEquiv)
    exact hproper (P : Subgroup K) hP_char hP_ne_top
  have hsup_le :
      (⨆ p ∈ (Nat.card K).primeFactors, ((default : Sylow p K) : Subgroup K)) ≤
        fixedPointSubgroup A K := by
    refine iSup₂_le ?_
    intro p hp
    exact hSylow_fix p hp
  have hfix_top : fixedPointSubgroup A K = ⊤ := by
    apply top_unique
    rw [← Sylow.iSup_sylow_eq_top (G := K)]
    exact hsup_le
  have htriv : ActsTrivially (A := A) (G := K) := by
    intro a k
    have hkfix : k ∈ fixedPointSubgroup A K := by simp [hfix_top]
    exact hkfix a
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  exact ha ((faithfulSMul_iff (G := A) (α := K)).1 inferInstance a (htriv a))

theorem CFSG.faithfulSMul_of_prime_order_of_not_actsTrivially {A G : Type*} [Group A] [Finite A]
    [Group G] [MulDistribMulAction A G] (hAprime : Nat.Prime (Nat.card A))
    (hntriv : ¬ ActsTrivially (A := A) (G := G)) :
    FaithfulSMul A G := by
  let C : Subgroup A := fixingSubgroupOf A G Set.univ
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    apply hntriv
    intro a g
    have haC : a ∈ C := by
      simp [C, hC_top]
    have haKer : a ∈ (MulDistribMulAction.toMulAut A G).ker := by
      simpa [C, fixingSubgroupOf_univ_eq_ker_toMulAut] using haC
    simpa [MonoidHom.mem_ker] using congrArg (fun f : MulAut G => f g) haKer
  have hcardC_dvd : Nat.card C ∣ Nat.card A := Subgroup.card_subgroup_dvd_card C
  have hcardC_eq_one : Nat.card C = 1 := by
    refine (hAprime.eq_one_or_self_of_dvd (Nat.card C) hcardC_dvd).resolve_right ?_
    intro hcardC_eq
    exact hC_ne_top ((Subgroup.card_eq_iff_eq_top (H := C)).1 hcardC_eq)
  have hC_bot : C = ⊥ := (Subgroup.eq_bot_iff_card (H := C)).2 hcardC_eq_one
  refine (faithfulSMul_iff (G := A) (α := G)).2 ?_
  intro a ha
  have haC : a ∈ C := by
    rw [show C = fixingSubgroupOf A G Set.univ by rfl]
    rw [fixingSubgroupOf_univ_eq_ker_toMulAut, MonoidHom.mem_ker]
    ext g
    exact ha g
  have ha_bot : a ∈ (⊥ : Subgroup A) := by simpa [C, hC_bot] using haC
  simpa using ha_bot


theorem CFSG.map_subtype_le_normalizer_of_normal {G : Type*} [Group G]
    (K : Subgroup G) (H : Subgroup K) [H.Normal] :
    K ≤ Subgroup.normalizer (H.map K.subtype) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨h, hhH, rfl⟩
    exact Subgroup.mem_map_of_mem K.subtype (Subgroup.Normal.conj_mem inferInstance h hhH ⟨k, hk⟩)
  · intro hx
    rcases hx with ⟨h, hhH, hhx⟩
    refine ⟨(⟨k, hk⟩)⁻¹ * h * ⟨k, hk⟩, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance h hhH ((⟨k, hk⟩ : K)⁻¹)
    · calc
        (((⟨k, hk⟩)⁻¹ * h * ⟨k, hk⟩ : K) : G) = k⁻¹ * ((h : K) : G) * k := by rfl
        _ = k⁻¹ * (k * x * k⁻¹) * k := by
          have hhx' : (h : G) = k * x * k⁻¹ := hhx
          rw [hhx']
        _ = x := by simp [mul_assoc]


universe uG uF uV

abbrev CFSG.Theorem34IndHyp {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F]
    (K : Subgroup G) : Prop :=
  ∀ {V' : Type uV} [AddCommGroup V'] [Module F V']
    {G' : Type uG} [Group G'] [Finite G'] (K' R' : Subgroup G')
    (ρ' : Representation F G' V'),
    Nat.card K' < Nat.card K →
    Group.IsSolvable G' →
    Odd (Nat.card G') →
    K'.Normal →
    K'.IsComplement' R' →
    Nat.Coprime (Nat.card K') (Nat.card R') →
    Nat.Prime (Nat.card R') →
    (ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G'))) →
    ρ'.fixedSubspace R' = ⊥ →
    ⁅R', K'⁆ ≤ ρ'.centralizerIn K'

set_option maxHeartbeats 1000000 in
theorem CFSG.theorem_3_4_quotient_step {G : Type uG} [Group G] [Finite G] {F : Type uF}
    [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) (hN_ne_bot : ρ.centralizerIn K ≠ ⊥) :
    ⁅R, K⁆ ≤ ρ.centralizerIn K := by
  let N : Subgroup G := ρ.centralizerIn K
  have hN_le_K : N ≤ K := by
    intro x hx
    exact hx.1
  have hN_le_ker : N ≤ ρ.ker := by
    intro x hx
    exact hx.2
  let : N.Normal := by
    dsimp [N, Representation.centralizerIn]
    infer_instance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let : Representation.IsTrivial (ρ.comp N.subtype) :=
    isTrivialCompSubtypeOfLeKer (ρ := ρ) (N := N) hN_le_ker
  let ρq : Representation F (G ⧸ N) V := Representation.ofQuotient ρ N
  have hcard_quot_dvd : Nat.card (G ⧸ N) ∣ Nat.card G := by
    exact ⟨Nat.card N, by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := N))⟩
  have hquot_fix :
      ρq.fixedSubspace (R.map q) = ⊥ := by
    simpa [ρq] using fixedSubspace_map_mk'_ofQuotient_eq (ρ := ρ) (N := N) (R := R) ▸ hfixR
  have hKmap_normal : (K.map q).Normal := by
    exact Subgroup.Normal.map (H := K) (f := q) hK_normal (QuotientGroup.mk'_surjective _)
  have hquot : ⁅R.map q, K.map q⁆ ≤ ρq.centralizerIn (K.map q) := by
    exact
      hind (K.map q) (R.map q) ρq
        (natCard_map_mk'_lt_of_ne_bot K N hN_le_K hN_ne_bot)
        (by infer_instance)
        (odd_of_card_dvd hodd hcard_quot_dvd)
        hKmap_normal
        (isComplement'_map_mk'_of_le_isComplement' K R N hN_le_K hKR)
        (coprime_card_map_mk'_of_le_isComplement' K R N hN_le_K hKR hcopKR)
        (prime_card_map_mk'_of_le_isComplement' K R N hN_le_K hKR hR_prime)
        (hchar_of_card_dvd (G := G) (F := F) hchar hcard_quot_dvd)
        hquot_fix
  exact
    commutator_le_centralizerIn_of_map_le_centralizerIn_ofQuotient
      (N := N) (K := K) (R := R) (ρ := ρ) hK_normal hquot

set_option maxHeartbeats 1000000 in
theorem CFSG.theorem_3_4_subgroup_step {G : Type uG} [Group G] [Finite G] {F : Type uF}
    [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (H : Subgroup G) (hH_lt : H < K) (hH_normal : H.Normal)
    (hRinv : ∀ r : R, ∀ h ∈ H, (r : G) * h * (r : G)⁻¹ ∈ H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) :
    ⁅R, H⁆ ≤ ρ.centralizerIn H := by
  let : H.Normal := hH_normal
  let S : Subgroup G := H ⊔ R
  let ρS : Representation F S V := ρ.comp S.subtype
  have hdisj : Disjoint H R := hKR.disjoint.mono_left hH_lt.1
  have hcard_sub_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hHsub_lt : Nat.card (H.subgroupOf S) < Nat.card K := by
    rw [natCard_subgroupOf_eq H S le_sup_left]
    exact natCard_lt_of_subgroup_lt hH_lt
  have hRsub_prime : Nat.Prime (Nat.card (R.subgroupOf S)) := by
    rw [natCard_subgroupOf_eq R S le_sup_right]
    exact hR_prime
  have hsub_fix : ρS.fixedSubspace (R.subgroupOf S) = ⊥ := by
    simpa [ρS] using
      (fixedSubspace_subgroupOf_eq (ρ := ρ) (S := S) (R := R) le_sup_right).trans hfixR
  set_option maxHeartbeats 800000 in
  have hsub : ⁅R.subgroupOf S, H.subgroupOf S⁆ ≤ ρS.centralizerIn (H.subgroupOf S) := by
    exact
      hind (H.subgroupOf S) (R.subgroupOf S) ρS
        hHsub_lt
        (by infer_instance)
        (odd_of_card_dvd hodd hcard_sub_dvd)
        (normal_subgroupOf_sup_of_conj_mem H R hRinv)
        (isComplement'_subgroupOf_sup_of_disjoint H R hdisj)
        (coprime_card_subgroupOf_sup_of_le H K R hH_lt.1 hcopKR)
        hRsub_prime
        (hchar_of_card_dvd (G := G) (F := F) hchar hcard_sub_dvd)
        hsub_fix
  exact
    commutator_le_centralizerIn_of_subgroupOf_eq
      (ρ := ρ) (S := S) (H := H) (R := R) le_sup_left le_sup_right hsub

theorem CFSG.proper_normal_fixed_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) (hKbot : ρ.centralizerIn K = ⊥)
    (H : Subgroup G) (hH_lt : H < K) (hH_normal : H.Normal)
    (hRinv : ∀ r : R, ∀ h ∈ H, (r : G) * h * (r : G)⁻¹ ∈ H) :
    ∀ r : R, ∀ x ∈ H, (r : G) * x * (r : G)⁻¹ = x := by
  have hsub :
      ⁅R, H⁆ ≤ ρ.centralizerIn H :=
    theorem_3_4_subgroup_step K R ρ hind H hH_lt hH_normal hRinv
      hsolvG hodd hKR hcopKR hR_prime hchar hfixR
  have hHbot : ρ.centralizerIn H = ⊥ :=
    centralizerIn_eq_bot_of_le_of_centralizerIn_eq_bot (ρ := ρ) hH_lt.1 hKbot
  have hcommH : ⁅R, H⁆ = ⊥ := by
    rw [hHbot] at hsub
    exact le_antisymm hsub bot_le
  have hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  have : Subgroup.Normalizes R H := ⟨hRnormH⟩
  have htrivH : ActsTrivially (A := ↥R) (G := ↥H) :=
    actsTrivially_subgroup_conj_of_commutator_eq_bot (K := H) (R := R) hRnormH hcommH
  intro r x hx
  let xH : H := ⟨x, hx⟩
  have hxfix : r • xH = xH := htrivH r xH
  simpa [xH, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
    congrArg Subtype.val hxfix

theorem CFSG.proper_characteristic_le_fixedPointSubgroup_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) (hKbot : ρ.centralizerIn K = ⊥)
    (H : Subgroup K) (hH_char : H.Characteristic) (hH_top : H ≠ ⊤) :
    ∀ r : R, ∀ x : K, x ∈ H → (r : G) * (x : G) * (r : G)⁻¹ = x := by
  have hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  let H' : Subgroup G := H.map K.subtype
  have hH'_le : H' ≤ K := by
    simpa [H'] using (Subgroup.map_subtype_le H)
  have hH'_normal : H'.Normal := by
    let : H.Characteristic := hH_char
    let : K.Normal := hK_normal
    simpa [H'] using (inferInstance : (H.map K.subtype).Normal)
  have hH'_ne : H' ≠ K := by
    intro hEq
    apply hH_top
    apply top_unique
    intro x hx
    have hx' : ((x : K) : G) ∈ H' := by simp [H', hEq]
    rcases hx' with ⟨y, hy, hyx⟩
    have hy_eq : y = x := by
      apply Subtype.ext
      simpa using hyx
    simpa [hy_eq] using hy
  have hH'_lt : H' < K := lt_of_le_of_ne hH'_le hH'_ne
  have hRinv : ∀ r : R, ∀ h ∈ H', (r : G) * h * (r : G)⁻¹ ∈ H' := by
    let : H.Characteristic := hH_char
    have : IsInvariant (↥R) (↥K) H := isInvariant_of_characteristic (A := ↥R) (G := ↥K) H
    intro r h hh
    rcases hh with ⟨x, hx, rfl⟩
    refine ⟨r • x, (IsInvariant.invariant (A := ↥R) (G := ↥K) (H := H) r x).1 hx, ?_⟩
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hsub :
      ⁅R, H'⁆ ≤ ρ.centralizerIn H' :=
    theorem_3_4_subgroup_step K R ρ hind H' hH'_lt hH'_normal hRinv
      hsolvG hodd hKR hcopKR hR_prime hchar hfixR
  have hH'_bot : ρ.centralizerIn H' = ⊥ :=
    centralizerIn_eq_bot_of_le_of_centralizerIn_eq_bot (ρ := ρ) hH'_le hKbot
  have hcommH' : ⁅R, H'⁆ = ⊥ := by
    rw [hH'_bot] at hsub
    exact le_antisymm hsub bot_le
  have hRnormH' : R ≤ Subgroup.normalizer H' := Subgroup.le_normalizer_of_normal (H := H')
  have : Subgroup.Normalizes R H' := ⟨hRnormH'⟩
  have htrivH' : ActsTrivially (A := ↥R) (G := ↥H') :=
    actsTrivially_subgroup_conj_of_commutator_eq_bot (K := H') (R := R) hRnormH' hcommH'
  intro r x hx
  let x' : H' := ⟨((x : K) : G), Subgroup.mem_map_of_mem K.subtype hx⟩
  have hxfix : r • x' = x' := htrivH' r x'
  simpa [x', Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH'] using
    congrArg Subtype.val hxfix

theorem CFSG.theorem_3_4_quotient_center_fixfree_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) (hKbot : ρ.centralizerIn K = ⊥)
    {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)]
    (hqdvdK : q ∣ Nat.card K)
    (hnontrivAction : ∃ a : R, ∃ x : K, (a : G) * (x : G) * (a : G)⁻¹ ≠ x)
    (hcommK : ¬ IsMulCommutative ↥K)
    (hcomm : commutator (↥K) ≤ Subgroup.center (↥K)) (hexp : Monoid.exponent (↥K) = q) :
    ∀ r : R, r ≠ 1 → elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype := by
  let : K.Normal := hK_normal
  have hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  let Z : Subgroup ↥K := Subgroup.center (↥K)
  let : Z.Normal := by infer_instance
  have hZ_top : Z ≠ ⊤ := by
    intro hZ
    apply hcommK
    refine ⟨⟨?_⟩⟩
    intro x y
    have hxcent : x ∈ Z := by simp [Z, hZ]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  have hZfix :
      Z ≤ fixedPointSubgroup (↥R) (↥K) := by
    intro z hz
    rw [FixedPoints.mem_subgroup]
    intro a
    apply Subtype.ext
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
      proper_characteristic_le_fixedPointSubgroup_local K R ρ hind hsolvG hodd hK_normal hKR
        hcopKR hR_prime hchar hfixR hKbot Z inferInstance hZ_top a z hz
  have hZinv : IsInvariant (↥R) (↥K) Z :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥K) Z
  let : MulAction.QuotientAction (↥R) Z :=
    quotientAction_of_isInvariant (A := ↥R) Z hZinv
  let Q : Type uG := ↥K ⧸ Z
  let : Group Q := QuotientGroup.Quotient.group Z
  let : MulDistribMulAction (↥R) Q :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥K) Z hZinv
  let qZ : ↥K →* Q := QuotientGroup.mk' Z
  let : Nontrivial Q := quotient_center_nontrivial_of_not_isMulCommutative hcommK
  let : IsElementaryAbelian q Q :=
    isElementaryAbelian_quotient_center_of_commutator_le_center_of_exponent_eq hcomm hexp
  intro r hr_ne
  let σ : MulAut Q := MulDistribMulAction.toMulAut (↥R) Q r
  have hσcopq : Nat.Coprime (orderOf σ) q := by
    have hσdvdR : orderOf σ ∣ Nat.card R := by
      exact (orderOf_map_dvd (MulDistribMulAction.toMulAut (↥R) Q) r).trans (orderOf_dvd_natCard r)
    have hσcopK : Nat.Coprime (orderOf σ) (Nat.card K) :=
      Nat.Coprime.of_dvd_left hσdvdR hcopKR.symm
    exact Nat.Coprime.of_dvd_right hqdvdK hσcopK
  have hσpow_top : Subgroup.zpowers r = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hR_prime hr_ne
  have hσ_ne : σ ≠ 1 := by
    intro hσ_eq
    have hquot :
        ActsTrivially (A := ↥R) (G := Q) := by
      intro a x
      have ha_zpow : a ∈ Subgroup.zpowers r := by
        simp [hσpow_top]
      rcases Subgroup.mem_zpowers_iff.mp ha_zpow with ⟨n, rfl⟩
      have hmap_zpow :
          MulDistribMulAction.toMulAut (↥R) Q (r ^ n) = σ ^ n := by
        simpa [σ] using (map_zpow (MulDistribMulAction.toMulAut (↥R) Q) r n)
      change (MulDistribMulAction.toMulAut (↥R) Q (r ^ n)) x = x
      rw [hmap_zpow, hσ_eq]
      simp
    have hcomm_le_Z : commutatorAction (A := ↥R) (G := ↥K) ≤ Z := by
      change
        Subgroup.closure {x : ↥K | ∃ a : ↥R, ∃ g : ↥K, g ∈ (⊤ : Subgroup ↥K) ∧
          x = g⁻¹ * (a • g)} ≤ Z
      refine (Subgroup.closure_le (K := Z)).2 ?_
      intro x hx
      rcases hx with ⟨a, g, -, rfl⟩
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change ((g : Q)⁻¹ * (((a • g : ↥K) : Q))) = 1
      rw [← show a • ((g : ↥K) : Q) = (((a • g : ↥K) : Q)) by
        simp]
      rw [hquot a ((g : ↥K) : Q)]
      simp
    have hcomm_le_fix :
        commutatorAction (A := ↥R) (G := ↥K) ≤ fixedPointSubgroup (↥R) (↥K) :=
      le_trans hcomm_le_Z hZfix
    have hcomm₂ : commutatorAction₂ (A := ↥R) (G := ↥K) = ⊥ := by
      apply bot_unique
      change
        Subgroup.closure
            {x : ↥K | ∃ a : ↥R, ∃ g : ↥K, g ∈ commutatorAction (A := ↥R) (G := ↥K) ∧
              x = g⁻¹ * (a • g)} ≤
          (⊥ : Subgroup ↥K)
      refine (Subgroup.closure_le (K := (⊥ : Subgroup ↥K))).2 ?_
      intro x hx
      rcases hx with ⟨a, g, hg, rfl⟩
      have hgfix : ∀ b : ↥R, b • g = g := by
        have hgmem : g ∈ fixedPointSubgroup (↥R) (↥K) := hcomm_le_fix hg
        simpa [FixedPoints.mem_subgroup] using hgmem
      simp [hgfix a]
    have hsolvK : Group.IsSolvable ↥K := by infer_instance
    have htrivK : ActsTrivially (A := ↥R) (G := ↥K) :=
      proposition_1_6_c (G := ↥K) (A := ↥R) hsolvK hcopKR.symm hcomm₂
    rcases hnontrivAction with ⟨a, x, hax⟩
    have hfix : (a : G) * (x : G) * (a : G)⁻¹ = x := by
      have hxfix : a • x = x := htrivK a x
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
        congrArg Subtype.val hxfix
    exact hax hfix
  have hproperσ :
      ∀ Hbar : Subgroup Q, Hbar ≠ ⊤ → Hbar.map σ.toMonoidHom = Hbar →
        Hbar ≤ fixedPointSubgroup (↥(Subgroup.zpowers σ)) Q := by
    intro Hbar hHbar_top hHbarσ
    let H : Subgroup ↥K := Subgroup.comap qZ Hbar
    have hH_top : H ≠ ⊤ := by
      intro hH_eq
      have hmapH :
          Subgroup.map qZ H = Hbar :=
        Subgroup.map_comap_eq_self_of_surjective (f := qZ) (QuotientGroup.mk'_surjective Z) Hbar
      have hmap_top : Subgroup.map qZ (⊤ : Subgroup ↥K) = ⊤ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := Z) x
          exact ⟨y, trivial, rfl⟩
      have hHbar_eq_top : Hbar = ⊤ := by
        calc
          Hbar = Subgroup.map qZ H := hmapH.symm
          _ = ⊤ := by simpa [hH_eq] using hmap_top
      exact hHbar_top hHbar_eq_top
    have hσ_mem : ∀ {x : Q}, x ∈ Hbar → σ x ∈ Hbar := by
      intro x hx
      have hx' : σ x ∈ Hbar.map σ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [hHbarσ] at hx'
      exact hx'
    have hσinv_mem : ∀ {x : Q}, x ∈ Hbar → σ⁻¹ x ∈ Hbar := by
      intro x hx
      have hx' : x ∈ Hbar.map σ.toMonoidHom := by
        rw [hHbarσ]
        exact hx
      rcases hx' with ⟨y, hy, hyx⟩
      have hy_eq : y = σ⁻¹ x := by
        apply σ.injective
        calc
          σ y = x := by simpa using hyx
          _ = σ (σ⁻¹ x) := by simp
      simpa [hy_eq] using hy
    have hσzpow_mem : ∀ n : ℤ, ∀ {x : Q}, x ∈ Hbar → (σ ^ n) x ∈ Hbar := by
      have hpow_mem : ∀ n : ℕ, ∀ {x : Q}, x ∈ Hbar → (σ ^ n) x ∈ Hbar := by
        intro n
        induction n with
        | zero =>
            intro x hx
            simpa
        | succ n ih =>
            intro x hx
            have hxσ : σ x ∈ Hbar := hσ_mem hx
            have hxpow : (σ ^ n) (σ x) ∈ Hbar := ih hxσ
            simpa [pow_succ] using hxpow
      have hinvpow_mem : ∀ n : ℕ, ∀ {x : Q}, x ∈ Hbar → (σ⁻¹ ^ n) x ∈ Hbar := by
        intro n
        induction n with
        | zero =>
            intro x hx
            simpa
        | succ n ih =>
            intro x hx
            have hxσ : σ⁻¹ x ∈ Hbar := hσinv_mem hx
            have hxpow : (σ⁻¹ ^ n) (σ⁻¹ x) ∈ Hbar := ih hxσ
            simpa [pow_succ] using hxpow
      intro n x hx
      cases n with
      | ofNat n =>
          simpa [zpow_ofNat] using hpow_mem n hx
      | negSucc n =>
          simpa [zpow_negSucc] using hinvpow_mem (n + 1) hx
    let H' : Subgroup G := H.map K.subtype
    have hH'_le : H' ≤ K := by
      simpa [H'] using (Subgroup.map_subtype_le H)
    have hH'_ne : H' ≠ K := by
      intro hEq
      apply hH_top
      apply top_unique
      intro x hx
      have hx' : ((x : K) : G) ∈ H' := by simp [H', hEq]
      rcases hx' with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        apply Subtype.ext
        simpa using hyx
      simpa [H, hy_eq] using hy
    have hH'_lt : H' < K := lt_of_le_of_ne hH'_le hH'_ne
    have hH_normal : H.Normal := by
      let : Hbar.Normal := by infer_instance
      dsimp [H]
      infer_instance
    have hRinv : ∀ a : R, ∀ h ∈ H', (a : G) * h * (a : G)⁻¹ ∈ H' := by
      intro a h hh
      rcases hh with ⟨x, hx, rfl⟩
      have ha_zpow : a ∈ Subgroup.zpowers r := by
        simp [hσpow_top]
      rcases Subgroup.mem_zpowers_iff.mp ha_zpow with ⟨n, rfl⟩
      let y : K := (MulDistribMulAction.toMulAut (↥R) (↥K) (r ^ n)) x
      have hybar : qZ y ∈ Hbar := by
        have hqy :
            qZ y = (σ ^ n) (qZ x) := by
          have hmap_zpow :
              MulDistribMulAction.toMulAut (↥R) Q (r ^ n) = σ ^ n := by
            simpa [σ] using (map_zpow (MulDistribMulAction.toMulAut (↥R) Q) r n)
          calc
            qZ y = ((r ^ n : R) • (qZ x)) := by
                change QuotientGroup.mk' Z (((r ^ n : R) • x : K)) = (r ^ n : R) • QuotientGroup.mk' Z x
                simp
            _ = (MulDistribMulAction.toMulAut (↥R) Q (r ^ n)) (qZ x) := rfl
            _ = (σ ^ n) (qZ x) := by rw [hmap_zpow]
        exact hqy.symm ▸ hσzpow_mem n hx
      refine ⟨y, hybar, ?_⟩
      change ((y : K) : G) = ((r ^ n : R) : G) * ((x : K) : G) * ((r ^ n : R) : G)⁻¹
      simp [y, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hH'_normal : H'.Normal := by
      let : H.Normal := hH_normal
      have hKnormH' : K ≤ Subgroup.normalizer H' := by
        simpa [H'] using map_subtype_le_normalizer_of_normal K H
      refine ⟨?_⟩
      intro x hx g
      rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨a, haR⟩⟩, hka⟩
      have hax : (a : G) * x * (a : G)⁻¹ ∈ H' := hRinv ⟨a, haR⟩ x hx
      have hkax : (k : G) * ((a : G) * x * (a : G)⁻¹) * (k : G)⁻¹ ∈ H' := by
        exact ((Subgroup.mem_normalizer_iff.mp (hKnormH' hkK)) _).1 hax
      have hconj_eq : g * x * g⁻¹ = (k : G) * ((a : G) * x * (a : G)⁻¹) * (k : G)⁻¹ := by
        have hka' : (k : G) * (a : G) = g := by simpa using hka
        calc
          g * x * g⁻¹ = ((k : G) * (a : G)) * x * (((k : G) * (a : G))⁻¹) := by rw [hka']
          _ = (k : G) * ((a : G) * x * (a : G)⁻¹) * (k : G)⁻¹ := by simp [mul_assoc]
      rw [hconj_eq]
      exact hkax
    have hfixH :
        ∀ a : R, ∀ x : K, x ∈ H → (a : G) * (x : G) * (a : G)⁻¹ = x := by
      intro a x hx
      simpa using
        proper_normal_fixed_local K R ρ hind hsolvG hodd hKR hcopKR hR_prime hchar hfixR
          hKbot H' hH'_lt hH'_normal hRinv a ((x : K) : G)
          (Subgroup.mem_map_of_mem K.subtype hx)
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := Z) x
    have hy : y ∈ H := by
      change qZ y ∈ Hbar at hx
      exact hx
    rw [FixedPoints.mem_subgroup]
    intro τ
    rcases τ.property with ⟨n, hn⟩
    have hyfix_r : ((r : R) : G) * ((y : K) : G) * ((r : R) : G)⁻¹ = y := hfixH r y hy
    have hyfixσ : σ (((y : K) : Q)) = ((y : K) : Q) := by
      have hyfix : r • y = y := by
        apply Subtype.ext
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hyfix_r
      calc
        σ (((y : K) : Q)) = (r : R) • (((y : K) : Q)) := rfl
        _ = (((r : R) • y : K) : Q) := by
              simp
        _ = ((y : K) : Q) := by simp [hyfix]
    have hyfixσpow : ∀ n : ℤ, (σ ^ n) (((y : K) : Q)) = ((y : K) : Q) := by
      intro n
      have hyfix : ((y : K) : Q) ∈ MulAction.fixedBy Q σ := by
        change σ ((y : K) : Q) = ((y : K) : Q)
        exact hyfixσ
      have hyfixpow :=
        MulAction.mem_fixedBy_zpow (α := Q) (g := σ) (a := ((y : K) : Q)) hyfix n
      change (σ ^ n) ((y : K) : Q) = ((y : K) : Q) at hyfixpow
      exact hyfixpow
    have hτ : (τ : MulAut Q) = σ ^ n := by simpa using hn.symm
    have hfixτ : (τ : MulAut Q) (((y : K) : Q)) = ((y : K) : Q) := by simpa [hτ] using hyfixσpow n
    change (τ : MulAut Q) ((y : K) : Q) = ((y : K) : Q)
    exact hfixτ
  have hfixσ :
      fixedPointSubgroup (↥(Subgroup.zpowers σ)) Q = ⊥ :=
    fixedPointSubgroup_zpowers_eq_bot_of_elementaryAbelian_of_proper_invariant_fixed
      (σ := σ) hσ_ne hσcopq hproperσ
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨hyK, hycent⟩
    have hyfixσ : σ (((⟨y, hyK⟩ : K) : Q)) = ((⟨y, hyK⟩ : K) : Q) := by
      have hycomm : (r : G) * y = y * (r : G) := by
        exact (Subgroup.mem_centralizer_singleton_iff.mp hycent).symm
      have hyconj : (r : G) * y * (r : G)⁻¹ = y := by
        calc
          (r : G) * y * (r : G)⁻¹ = (y * (r : G)) * (r : G)⁻¹ := by rw [hycomm]
          _ = y := by simp [mul_assoc]
      have hyfix : r • (⟨y, hyK⟩ : K) = ⟨y, hyK⟩ := by
        apply Subtype.ext
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hyconj
      calc
        σ (((⟨y, hyK⟩ : K) : Q)) = (r : R) • (((⟨y, hyK⟩ : K) : Q)) := rfl
        _ = (((r : R) • (⟨y, hyK⟩ : K) : K) : Q) := by
              simp
        _ = ((⟨y, hyK⟩ : K) : Q) := by simp [hyfix]
    have hyfix :
        (((⟨y, hyK⟩ : K) : Q)) ∈ fixedPointSubgroup (↥(Subgroup.zpowers σ)) Q := by
      rw [FixedPoints.mem_subgroup]
      intro τ
      rcases τ.property with ⟨n, hn⟩
      have hyσ : (((⟨y, hyK⟩ : K) : Q)) ∈ MulAction.fixedBy Q σ := by
        change σ (((⟨y, hyK⟩ : K) : Q)) = ((⟨y, hyK⟩ : K) : Q)
        exact hyfixσ
      have hyσpow :
          (((⟨y, hyK⟩ : K) : Q)) ∈ MulAction.fixedBy Q (σ ^ n) :=
        MulAction.mem_fixedBy_zpow (α := Q) (g := σ) (a := (((⟨y, hyK⟩ : K) : Q))) hyσ n
      have hτ : (τ : MulAut Q) = σ ^ n := by simpa using hn.symm
      have hfixτ : (τ : MulAut Q) (((⟨y, hyK⟩ : K) : Q)) = ((⟨y, hyK⟩ : K) : Q) := by
        change (σ ^ n) (((⟨y, hyK⟩ : K) : Q)) = ((⟨y, hyK⟩ : K) : Q) at hyσpow
        simpa [hτ] using hyσpow
      change (τ : MulAut Q) (((⟨y, hyK⟩ : K) : Q)) = ((⟨y, hyK⟩ : K) : Q)
      exact hfixτ
    have hybot : (((⟨y, hyK⟩ : K) : Q)) ∈ (⊥ : Subgroup Q) := by simpa [hfixσ] using hyfix
    change QuotientGroup.mk' Z (⟨y, hyK⟩ : K) = 1 at hybot
    exact ⟨⟨y, hyK⟩, (QuotientGroup.eq_one_iff (N := Z) (⟨y, hyK⟩ : K)).1 hybot, rfl⟩
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hzsmul : r • z = z := (hZfix hz) r
    have hzfix : (r : G) * ((z : K) : G) * (r : G)⁻¹ = z := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
        congrArg Subtype.val hzsmul
    have hzcomm : (r : G) * ((z : K) : G) = ((z : K) : G) * (r : G) := by
      simpa [mul_assoc] using congrArg (fun t : G => t * (r : G)) hzfix
    exact hzcomm.symm


public theorem CFSG.subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
    {G : Type*} [Group G] [Finite G] (H R X : Subgroup G) [X.Normal]
    (hRnormH : R ≤ Subgroup.normalizer H) (hsolvH : Group.IsSolvable ↥H)
    (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hXinv : ∀ r : R, ∀ x ∈ X, (r : G) * x * (r : G)⁻¹ ∈ X) :
    subgroupCentralizerIn (H.map (QuotientGroup.mk' X)) (R.map (QuotientGroup.mk' X)) =
      (subgroupCentralizerIn H R).map (QuotientGroup.mk' X) := by
  let qG : G →* G ⧸ X := QuotientGroup.mk' X
  let Xsub : Subgroup ↥H := X.subgroupOf H
  have : Xsub.Normal := by
    exact Subgroup.Normal.subgroupOf (H := X) (K := H) (inferInstance : X.Normal)
  have : Subgroup.Normalizes R H := ⟨hRnormH⟩
  have hXsub_inv : IsInvariant (↥R) (↥H) Xsub := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hxX : (x : G) ∈ X := by
        simpa [Xsub, Subgroup.mem_subgroupOf] using hx
      have hsmulX : (((a • x : H) : G)) ∈ X := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
          hXinv a x hxX
      simpa [Xsub, Subgroup.mem_subgroupOf] using hsmulX
    · intro hx
      have hxX : (((a • x : H) : G)) ∈ X := by
        simpa [Xsub, Subgroup.mem_subgroupOf] using hx
      have hx' :
          ((((a : R) : G)⁻¹ * (((a : R) • x : H) : G) * (((a : R) : G)⁻¹)⁻¹) ∈ X) := by
        simpa using
          (inferInstance : X.Normal).conj_mem
            ((((a : R) • x : H) : G)) hxX (((a : R) : G)⁻¹)
      simpa [Xsub, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH, mul_assoc] using hx'
  let : IsInvariant (↥R) (↥H) Xsub := hXsub_inv
  let : MulAction.QuotientAction (↥R) Xsub :=
    quotientAction_of_isInvariant (A := ↥R) (G := ↥H) Xsub hXsub_inv
  let : MulDistribMulAction (↥R) (↥H ⧸ Xsub) :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥H) Xsub hXsub_inv
  let e : (↥H ⧸ Xsub) ≃* H.map qG := quotientSubgroupRangeEquiv H X
  have hfixedH :
      fixedPointSubgroup (↥R) (↥H) = (subgroupCentralizerIn H R).subgroupOf H := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H R hRnormH
  have hfixed_quot :
      fixedPointSubgroup (↥R) (↥H ⧸ Xsub) =
        ((subgroupCentralizerIn H R).subgroupOf H).map (QuotientGroup.mk' Xsub) := by
    calc
      fixedPointSubgroup (↥R) (↥H ⧸ Xsub) =
          (fixedPointSubgroup (↥R) (↥H)).map (QuotientGroup.mk' Xsub) := by
            simpa [Xsub] using
              proposition_1_5_d (G := ↥H) (A := ↥R) hsolvH hcopHR.symm (π := ∅) Xsub hXsub_inv
      _ = ((subgroupCentralizerIn H R).subgroupOf H).map (QuotientGroup.mk' Xsub) := by
            rw [hfixedH]
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyH, hyC⟩
    change y ∈ H.map qG at hyH
    rw [Subgroup.mem_map] at hyH
    rcases hyH with ⟨h, hhH, hhy⟩
    let hH : H := ⟨h, hhH⟩
    let hbar : ↥H ⧸ Xsub := QuotientGroup.mk' Xsub hH
    have hhbar_fix :
        hbar ∈ fixedPointSubgroup (↥R) (↥H ⧸ Xsub) := by
      rw [FixedPoints.mem_subgroup]
      intro a
      apply e.injective
      apply Subtype.ext
      calc
        (((e (a • hbar) : H.map qG) : G ⧸ X)) = qG (((a : R) • hH : H) : G) := by
          rw [show a • hbar = QuotientGroup.mk' Xsub ((a : R) • hH) by
                simp [hbar]]
          simpa [e, qG, hH, Xsub] using
            quotientSubgroupRangeEquiv_apply_mk H X (((a : R) • hH : H))
        _ = qG ((hH : H) : G) := by
          have hy_comm : qG (a : G) * y = y * qG (a : G) :=
            Subgroup.mem_centralizer_iff.mp hyC (qG (a : G))
              (by exact ⟨a, a.2, rfl⟩)
          calc
            qG (((a : R) • hH : H) : G) = qG ((a : G) * h * (a : G)⁻¹) := by
              simp [hH, qG, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
            _ = qG (a : G) * qG h * (qG (a : G))⁻¹ := by simp [qG, map_mul, mul_assoc]
            _ = qG (a : G) * y * (qG (a : G))⁻¹ := by simp [hhy]
            _ = y := by rw [hy_comm]; simp [mul_assoc]
            _ = qG ((hH : H) : G) := by simp [hH, hhy]
        _ = (((e hbar : H.map qG) : G ⧸ X)) := by
          symm
          simpa [e, qG, hH, hbar, Xsub] using quotientSubgroupRangeEquiv_apply_mk H X hH
    have hhbar_map :
        hbar ∈ ((subgroupCentralizerIn H R).subgroupOf H).map (QuotientGroup.mk' Xsub) := by
      simpa [hfixed_quot] using hhbar_fix
    rcases hhbar_map with ⟨z, hz, hzhbar⟩
    have hy_eq : y = QuotientGroup.mk' X (z : G) := by
      calc
        (y : G ⧸ X) = qG h := hhy.symm
        _ = (((e hbar : H.map qG) : G ⧸ X)) := by
              symm
              simpa [e, qG, hH, hbar, Xsub] using quotientSubgroupRangeEquiv_apply_mk H X hH
        _ = (((e (QuotientGroup.mk' Xsub z) : H.map qG) : G ⧸ X)) := by simp [e, hzhbar]
        _ = QuotientGroup.mk' X (z : G) := by
              simpa [e, qG, Xsub] using quotientSubgroupRangeEquiv_apply_mk H X z
    exact ⟨(z : G), by simpa [Subgroup.mem_subgroupOf] using hz, by simpa [qG] using hy_eq.symm⟩
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    change QuotientGroup.mk' X z ∈ Subgroup.centralizer (R.map qG : Set (G ⧸ X))
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨r, hrR, rfl⟩
    have hcomm : (r : G) * z = z * (r : G) :=
      Subgroup.mem_centralizer_iff.mp hz.2 (r : G) hrR
    simpa [qG, map_mul] using congrArg qG hcomm

theorem CFSG.elementCentralizerIn_map_mk'_eq_map_center_of_solvable_coprime
    {G : Type*} [Group G] [Finite G] (K R N : Subgroup G) [N.Normal]
    (hRK : R ≤ Subgroup.normalizer K) (hsolvK : Group.IsSolvable ↥K)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hcent_r :
      ∀ r : R, r ≠ 1 →
        elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype)
    {r : R} (hr_ne : r ≠ 1) :
    elementCentralizerIn (K.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N (r : G)) =
      ((Subgroup.center (↥K)).map K.subtype).map (QuotientGroup.mk' N) := by
  let qG : G →* G ⧸ N := QuotientGroup.mk' N
  let Nsub : Subgroup ↥K := N.subgroupOf K
  have : Nsub.Normal := by
    exact Subgroup.Normal.subgroupOf (H := N) (K := K) (inferInstance : N.Normal)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  have hcop_zpow : Nat.Coprime (Nat.card (Subgroup.zpowers r)) (Nat.card K) := by
    have hzpow_dvd : Nat.card (Subgroup.zpowers r) ∣ Nat.card R :=
      Subgroup.card_subgroup_dvd_card (Subgroup.zpowers r)
    exact (Nat.Coprime.of_dvd_right hzpow_dvd hcopKR).symm
  have hNsub_inv : IsInvariant (↥(Subgroup.zpowers r)) (↥K) Nsub := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hxN : (x : G) ∈ N := by
        simpa [Nsub, Subgroup.mem_subgroupOf] using hx
      have hsmulN :
          ((((a : Subgroup.zpowers r) : R) • x : K) : G) ∈ N := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
          (inferInstance : N.Normal).conj_mem (x : G) hxN (((a : Subgroup.zpowers r) : R) : G)
      change ((((a : Subgroup.zpowers r) : R) • x : K) : G) ∈ N
      exact hsmulN
    · intro hx
      have hxN : ((((a : Subgroup.zpowers r) : R) • x : K) : G) ∈ N := by
        change ((((a : Subgroup.zpowers r) : R) • x : K) : G) ∈ N at hx
        exact hx
      have hx' :
          ((((a : Subgroup.zpowers r) : R) : G)⁻¹ *
              ((((a : Subgroup.zpowers r) : R) • x : K) : G) *
              ((((a : Subgroup.zpowers r) : R) : G)⁻¹)⁻¹) ∈ N := by
        simpa using
          (inferInstance : N.Normal).conj_mem
            ((((a : Subgroup.zpowers r) : R) • x : K) : G) hxN ((((a : Subgroup.zpowers r) : R) : G)⁻¹)
      simpa [Nsub, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK, mul_assoc] using hx'
  let : IsInvariant (↥(Subgroup.zpowers r)) (↥K) Nsub := hNsub_inv
  let : MulAction.QuotientAction (↥(Subgroup.zpowers r)) Nsub :=
    quotientAction_of_isInvariant (A := ↥(Subgroup.zpowers r)) (G := ↥K) Nsub hNsub_inv
  let : MulDistribMulAction (↥(Subgroup.zpowers r)) (↥K ⧸ Nsub) :=
    quotientMulDistribMulAction (A := ↥(Subgroup.zpowers r)) (G := ↥K) Nsub hNsub_inv
  let e : (↥K ⧸ Nsub) ≃* K.map qG := quotientSubgroupRangeEquiv K N
  have hfixedK :
      fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K) = Subgroup.center (↥K) := by
    calc
      fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K) =
          (elementCentralizerIn K (r : G)).subgroupOf K := by
            simpa using
              fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn K R hRK r
      _ = (((Subgroup.center (↥K)).map K.subtype)).subgroupOf K := by rw [hcent_r r hr_ne]
      _ = Subgroup.center (↥K) := by
            ext x
            simp [Subgroup.mem_subgroupOf]
  have hfixed_quot :
      fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K ⧸ Nsub) =
        (Subgroup.center (↥K)).map (QuotientGroup.mk' Nsub) := by
    calc
      fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K ⧸ Nsub) =
          (fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K)).map (QuotientGroup.mk' Nsub) := by
            simpa [Nsub] using
              proposition_1_5_d (G := ↥K) (A := ↥(Subgroup.zpowers r)) hsolvK hcop_zpow
                (π := ∅) Nsub hNsub_inv
      _ = (Subgroup.center (↥K)).map (QuotientGroup.mk' Nsub) := by rw [hfixedK]
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyK, hyC⟩
    change y ∈ K.map qG at hyK
    rw [Subgroup.mem_map] at hyK
    rcases hyK with ⟨k, hkK, hky⟩
    let kK : K := ⟨k, hkK⟩
    let kbar : ↥K ⧸ Nsub := QuotientGroup.mk' Nsub kK
    have hqG_fix :
        qG (((r : R) • kK : K) : G) = qG ((kK : K) : G) := by
      have hy_comm : y * QuotientGroup.mk' N (r : G) = QuotientGroup.mk' N (r : G) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      calc
        qG (((r : R) • kK : K) : G) = qG (r * k * r⁻¹) := by
          simp [kK, qG, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = qG r * qG k * (qG r)⁻¹ := by simp [qG, mul_assoc]
        _ = (QuotientGroup.mk' N (r : G)) * y * (QuotientGroup.mk' N (r : G))⁻¹ := by
              simp [hky, qG]
        _ = y := by
              rw [← hy_comm]
              simp [mul_assoc]
        _ = qG ((kK : K) : G) := by simp [kK, hky]
    have hkbar_fix_r :
        (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) • kbar = kbar := by
      apply e.injective
      apply Subtype.ext
      calc
        (((e ((⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) • kbar) : K.map qG) : G ⧸ N)) =
            qG (((r : R) • kK : K) : G) := by
              rw [show (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) • kbar =
                  QuotientGroup.mk' Nsub (((r : R) • kK : K)) by
                    simp [kbar]]
              simpa [e, qG, kK, Nsub] using
                quotientSubgroupRangeEquiv_apply_mk K N (((r : R) • kK : K))
        _ = qG ((kK : K) : G) := hqG_fix
        _ = (((e kbar : K.map qG) : G ⧸ N)) := by
              symm
              simpa [e, qG, kK, kbar, Nsub] using quotientSubgroupRangeEquiv_apply_mk K N kK
    have hkbar_fix :
        kbar ∈ fixedPointSubgroup (↥(Subgroup.zpowers r)) (↥K ⧸ Nsub) := by
      rw [FixedPoints.mem_subgroup]
      intro a
      have ha_mem :
          a ∈ Subgroup.zpowers (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) := by
        rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
          apply Subtype.ext
          simpa using hn⟩
      exact
        smul_eq_self_of_mem_zpowers (y := (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r))
          ha_mem hkbar_fix_r
    have hkbar_map :
        kbar ∈ (Subgroup.center (↥K)).map (QuotientGroup.mk' Nsub) := by
      simpa [hfixed_quot] using hkbar_fix
    rcases hkbar_map with ⟨z, hz, hzkbar⟩
    have hy_eq : y = QuotientGroup.mk' N (z : G) := by
      calc
        (y : G ⧸ N) = qG k := hky.symm
        _ = (((e kbar : K.map qG) : G ⧸ N)) := by
              symm
              simpa [e, qG, kK, kbar, Nsub] using quotientSubgroupRangeEquiv_apply_mk K N kK
        _ = (((e (QuotientGroup.mk' Nsub z) : K.map qG) : G ⧸ N)) := by simp [e, hzkbar]
        _ = QuotientGroup.mk' N (z : G) := by
              simpa [e, qG, Nsub] using quotientSubgroupRangeEquiv_apply_mk K N z
    exact ⟨(z : G), ⟨z, hz, rfl⟩, by simpa [qG] using hy_eq.symm⟩
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨z0, hz0, rfl⟩
    refine ⟨⟨z0, z0.property, rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hzcent : ((z0 : K) : G) ∈ elementCentralizerIn K (r : G) := by
      simpa [hcent_r r hr_ne] using show ((z0 : K) : G) ∈ (Subgroup.center (↥K)).map K.subtype by
        exact ⟨z0, hz0, rfl⟩
    have hcomm : ((z0 : K) : G) * (r : G) = (r : G) * ((z0 : K) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hzcent.2
    simpa [qG, map_mul] using congrArg qG hcomm


theorem CFSG.injective_comp_mulEquiv_toMonoidHom_iff
    {G H : Type*} [Group G] [Group H] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F H V) (e : G ≃* H) :
    Function.Injective (ρ.comp e.toMonoidHom) ↔ Function.Injective ρ := by
  constructor
  · intro hρ x y hxy
    rcases e.surjective x with ⟨x', rfl⟩
    rcases e.surjective y with ⟨y', rfl⟩
    exact congrArg e (hρ (by simpa using hxy))
  · intro hρ x y hxy
    exact e.injective (hρ (by simpa using hxy))

theorem CFSG.fixedSubspace_eq_bot_iff_fixedVectors_eq_zero
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G) :
    ρ.fixedSubspace H = ⊥ ↔ {v : V | ∀ h : H, ρ h v = v} = {0} := by
  constructor
  · intro hbot
    ext v
    constructor
    · intro hv
      have hv' : v ∈ ρ.fixedSubspace H := by
        simpa [Representation.fixedSubspace, Representation.mem_invariants] using hv
      have hv0 : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv'
      simpa using hv0
    · intro hv0 h
      have hv : v = 0 := by simpa using hv0
      simp [hv]
  · intro hfix
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' : ∀ h : H, ρ h v = v := by
      simpa [Representation.fixedSubspace, Representation.mem_invariants] using hv
    have hv0 : v ∈ ({0} : Set V) := by
      rw [← hfix]
      exact hv'
    simpa using hv0

theorem CFSG.nontrivial_of_not_le_ker_local
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (K : Subgroup G)
    (hK_nontrivial : ¬ K ≤ ρ.ker) :
    Nontrivial V := by
  classical
  by_contra hV
  let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hK_le_ker : K ≤ ρ.ker := by
    intro x hx
    change ρ x = 1
    ext v
    exact Subsingleton.elim _ _
  exact hK_nontrivial hK_le_ker

theorem CFSG.representation_eq_one_of_mul_eq_one_of_coprime_components_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)]
    (ρ : Representation F G V) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hqdvdK : q ∣ Nat.card K) (hexp : Monoid.exponent (↥K) = q)
    {k : K} {r : R} (hkr : ρ ((k : G) * (r : G)) = 1) :
    ρ (k : G) = 1 ∧ ρ (r : G) = 1 := by
  have hk_eq_inv : ρ (k : G) = ρ ((r : G)⁻¹) := by
    have hmul : ρ (k : G) * ρ (r : G) = 1 := by
      simpa [map_mul] using hkr
    calc
      ρ (k : G) = ρ (k : G) * 1 := by simp
      _ = ρ (k : G) * ρ ((r : G) * (r : G)⁻¹) := by
        rw [show (1 : V →ₗ[F] V) = ρ ((r : G) * (r : G)⁻¹) by simp]
      _ = (ρ (k : G) * ρ (r : G)) * ρ ((r : G)⁻¹) := by rw [map_mul]; simp [mul_assoc]
      _ = ρ ((r : G)⁻¹) := by simp [hmul]
  have hqcopR : Nat.Coprime q (Nat.card R) := Nat.Coprime.of_dvd_left hqdvdK hcopKR
  have hρk_order_dvd_q : orderOf (ρ (k : G)) ∣ q := by
    exact
      (orderOf_map_dvd (ρ.comp K.subtype) k).trans <|
        (Monoid.order_dvd_exponent k).trans (by simp [hexp])
  have hρk_order_dvd_R : orderOf (ρ (k : G)) ∣ Nat.card R := by
    calc
      orderOf (ρ (k : G)) = orderOf (ρ ((r : G)⁻¹)) := by simp [hk_eq_inv]
      _ ∣ orderOf ((r : G)⁻¹) := orderOf_map_dvd ρ ((r : G)⁻¹)
      _ = orderOf (r : G) := orderOf_inv _
      _ ∣ orderOf r := orderOf_map_dvd R.subtype r
      _ ∣ Nat.card R := orderOf_dvd_natCard r
  have hρk_order_one : orderOf (ρ (k : G)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hqcopR hρk_order_dvd_q hρk_order_dvd_R
  have hρk_one : ρ (k : G) = 1 := (orderOf_eq_one_iff.mp hρk_order_one)
  have hρr_one : ρ (r : G) = 1 := by
    have hmul : ρ (k : G) * ρ (r : G) = 1 := by simpa [map_mul] using hkr
    simpa [hρk_one] using hmul
  exact ⟨hρk_one, hρr_one⟩

theorem CFSG.eq_one_of_mem_ker_complement_prime_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V) (hR_prime : Nat.Prime (Nat.card R))
    (hfixR : ρ.fixedSubspace R = ⊥) (hK_nontrivial : ¬ K ≤ ρ.ker)
    {r : R} (hrker : ρ (r : G) = 1) :
    r = 1 := by
  let : Nontrivial V := nontrivial_of_not_le_ker_local ρ K hK_nontrivial
  by_contra hr_ne
  let : Fact (Nat.Prime (Nat.card R)) := ⟨hR_prime⟩
  have hr_top : Subgroup.zpowers r = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hR_prime hr_ne
  have htop_fix : ρ.fixedSubspace R = ⊤ := by
    apply top_unique
    intro v hv
    change ∀ a : R, ρ a v = v
    intro a
    have ha_mem : a ∈ Submonoid.powers r :=
      mem_powers_of_prime_card (G := ↥R) (p := Nat.card R) rfl hr_ne (g' := a)
    rcases (Submonoid.mem_powers_iff a r).mp ha_mem with ⟨n, hn⟩
    have hrpow : ρ ((a : R) : G) = 1 := by
      calc
        ρ ((a : R) : G) = ρ ((((r : R) ^ n : R) : R) : G) := by simp [hn]
        _ = (ρ (r : G)) ^ n := by simp [map_pow]
        _ = 1 := by simp [hrker]
    simpa using congrArg (fun e : V →ₗ[F] V => e v) hrpow
  exact top_ne_bot (htop_fix.symm.trans hfixR)

theorem CFSG.ker_le_of_isComplement'_prime_fixedSubspace_eq_bot
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)]
    (ρ : Representation F G V) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R)) (hfixR : ρ.fixedSubspace R = ⊥)
    (hK_nontrivial : ¬ K ≤ ρ.ker) (hqdvdK : q ∣ Nat.card K)
    (hexp : Monoid.exponent (↥K) = q) :
    ρ.ker ≤ K := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hkr⟩
  let kK : K := ⟨k, hkK⟩
  let rR : R := ⟨r, hrR⟩
  have hρkr : ρ (((kK : K) : G) * ((rR : R) : G)) = 1 := by
    simpa [kK, rR, hkr] using hg
  have hρr : ρ (rR : G) = 1 :=
    (representation_eq_one_of_mul_eq_one_of_coprime_components_local
      K R ρ hcopKR hqdvdK hexp hρkr).2
  have hr_eq_one : rR = 1 :=
    eq_one_of_mem_ker_complement_prime_local K R ρ hR_prime hfixR hK_nontrivial hρr
  have hr_eq_one' : (r : G) = 1 := congrArg Subtype.val hr_eq_one
  have hg_eq_k : g = k := by
    calc
      g = (k : G) * (r : G) := hkr.symm
      _ = k := by simp [hr_eq_one']
  exact hg_eq_k ▸ hkK

theorem CFSG.natCard_map_ker_eq_prime_of_central_exponent_prime_irreducible_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hirr : Representation.IsIrreducible ρ) (Z : Subgroup G) (hZ_central : Z ≤ Subgroup.center G)
    {q : ℕ} [Fact q.Prime] (hZpow : ∀ z : Z, (z : G) ^ q = 1) (hZ_nontrivial : ¬ Z ≤ ρ.ker) :
    Nat.card (Z.map (QuotientGroup.mk' ρ.ker)) = q := by
  let mkKer : G →* G ⧸ ρ.ker := QuotientGroup.mk' ρ.ker
  let ρq : Representation F (G ⧸ ρ.ker) V := Theory.Representation.kerRepresentation ρ
  have : Representation.IsIrreducible ρq :=
    (Theory.Representation.kerRepresentation_irreducible_iff ρ).2 hirr
  have : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ hirr
  have hZmap_central : Z.map mkKer ≤ Subgroup.center (G ⧸ ρ.ker) := by
    intro z hz
    rcases hz with ⟨z0, hz0, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro gq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := ρ.ker) gq
    have hz0_cent : (z0 : G) ∈ Subgroup.center G := hZ_central hz0
    simpa [mkKer, map_mul] using congrArg mkKer ((Subgroup.mem_center_iff.mp hz0_cent) g)
  have hZmap_ne_bot : Z.map mkKer ≠ ⊥ := by
    intro hZmap_bot
    apply hZ_nontrivial
    intro z hzZ
    have hzq_mem : mkKer z ∈ Z.map mkKer := ⟨z, hzZ, rfl⟩
    have hzq_eq_one : mkKer z = 1 := by
      have hzq_bot : mkKer z ∈ (⊥ : Subgroup (G ⧸ ρ.ker)) := by
        rw [← hZmap_bot]
        exact hzq_mem
      simpa using hzq_bot
    exact (QuotientGroup.eq_one_iff (N := ρ.ker) z).mp hzq_eq_one
  have hcenter_cyclic : IsCyclic (Subgroup.center (G ⧸ ρ.ker)) :=
    center_cyclic_of_representation_faithful_irreducible ρq
      (Theory.Representation.kerRepresentation_faithful ρ)
  let : IsCyclic (Subgroup.center (G ⧸ ρ.ker)) := hcenter_cyclic
  have hZmap_cyclic : IsCyclic (Z.map mkKer) := Subgroup.isCyclic_of_le hZmap_central
  let : IsCyclic (Z.map mkKer) := hZmap_cyclic
  have hexpZmap : Monoid.exponent ↥(Z.map mkKer) ∣ q := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro zq
    rcases zq.property with ⟨z, hzZ, hzq⟩
    apply Subtype.ext
    calc
      ((zq : Z.map mkKer) : G ⧸ ρ.ker) ^ q = (mkKer z) ^ q := by rw [hzq.symm]
      _ = mkKer (z ^ q) := by simp [mkKer]
      _ = 1 := by simpa [mkKer] using congrArg mkKer (hZpow ⟨z, hzZ⟩)
  have hcard_dvd_q : Nat.card (Z.map mkKer) ∣ q := by
    rw [← IsCyclic.exponent_eq_card (α := ↥(Z.map mkKer))]
    simpa using hexpZmap
  have hcard_ne_one : Nat.card (Z.map mkKer) ≠ 1 := by
    intro hcard_eq_one
    exact hZmap_ne_bot ((Subgroup.eq_bot_iff_card (H := Z.map mkKer)).2 hcard_eq_one)
  rcases (Nat.dvd_prime Fact.out).mp hcard_dvd_q with hcard_eq_one | hcard_eq_q
  · exact False.elim (hcard_ne_one hcard_eq_one)
  · exact hcard_eq_q

theorem CFSG.center_map_le_center_of_isComplement'_commute
    {G : Type uG} [Group G] (K R : Subgroup G) (hKR : K.IsComplement' R)
    (hcomm :
      ∀ r : R, ∀ z : Subgroup.center (↥K), (r : G) * (z : G) = (z : G) * (r : G)) :
    (Subgroup.center (↥K)).map K.subtype ≤ Subgroup.center G := by
  intro z hz
  rcases hz with ⟨z0, hz0, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hkr⟩
  have hkz0 :
      (k : G) * ((z0 : K) : G) = ((z0 : K) : G) * (k : G) := by
    simpa using congrArg K.subtype ((Subgroup.mem_center_iff.mp hz0) ⟨k, hkK⟩)
  have hrz0 :
      (r : G) * ((z0 : K) : G) = ((z0 : K) : G) * (r : G) :=
    hcomm ⟨r, hrR⟩ ⟨z0, hz0⟩
  calc
    g * ((z0 : K) : G) = ((k : G) * (r : G)) * ((z0 : K) : G) := by rw [← hkr]
    _ = (k : G) * ((r : G) * ((z0 : K) : G)) := by simp [mul_assoc]
    _ = (k : G) * (((z0 : K) : G) * (r : G)) := by rw [hrz0]
    _ = ((k : G) * ((z0 : K) : G)) * (r : G) := by simp [mul_assoc]
    _ = (((z0 : K) : G) * (k : G)) * (r : G) := by rw [hkz0]
    _ = ((z0 : K) : G) * ((k : G) * (r : G)) := by simp [mul_assoc]
    _ = ((z0 : K) : G) * g := by rw [← hkr]

theorem CFSG.natCard_eq_prime_of_central_exponent_prime_faithful_irreducible_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hirr : Representation.IsIrreducible ρ) (hfaithful : Function.Injective ρ)
    (Z : Subgroup G) (hZ_central : Z ≤ Subgroup.center G)
    {q : ℕ} [Fact q.Prime] (hZpow : ∀ z : Z, (z : G) ^ q = 1) (hZ_nontrivial : ¬ Z ≤ ρ.ker) :
    Nat.card Z = q := by
  have hker_eq_bot : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).2 hfaithful
  have hmk_inj : Function.Injective (QuotientGroup.mk' ρ.ker) := by
    rw [← (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' ρ.ker))]
    simp [QuotientGroup.ker_mk', hker_eq_bot]
  have hcard_map :
      Nat.card (Z.map (QuotientGroup.mk' ρ.ker)) = q :=
    natCard_map_ker_eq_prime_of_central_exponent_prime_irreducible_local
      (ρ := ρ) hirr Z hZ_central hZpow hZ_nontrivial
  have hcard_Zmap :
      Nat.card (Z.map (QuotientGroup.mk' ρ.ker)) = Nat.card Z := by
    simpa using
      (Subgroup.card_map_of_injective (K := Z) (f := QuotientGroup.mk' ρ.ker) hmk_inj)
  exact hcard_Zmap.symm.trans hcard_map

theorem CFSG.isExtraspecial_of_commutator_le_center_of_exponent_eq_of_faithful_irreducible_local
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] (K : Subgroup G) (ρ : Representation F G V)
    (hirr : Representation.IsIrreducible ρ) (hfaithful : Function.Injective ρ)
    {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)] (hcommK : ¬ IsMulCommutative ↥K)
    (hcomm : commutator (↥K) ≤ Subgroup.center (↥K)) (hexp : Monoid.exponent (↥K) = q)
    (hZ_central : (Subgroup.center (↥K)).map K.subtype ≤ Subgroup.center G) :
    IsExtraspecial q ↥K := by
  let Z : Subgroup G := (Subgroup.center (↥K)).map K.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_eq_bot
    subst hK_eq_bot
    exact hcommK inferInstance
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  have hcenter_ne_bot : (Subgroup.center (↥K)) ≠ ⊥ := by
    let : Nontrivial (Subgroup.center (↥K)) :=
      IsPGroup.center_nontrivial (p := q) (G := ↥K) (hG := Fact.out)
    intro hcenter_bot
    obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center (↥K))
    have hz_eq_one : ((z : Subgroup.center (↥K)) : ↥K) = 1 := by
      simpa [hcenter_bot] using z.2
    exact hz_ne (Subtype.ext hz_eq_one)
  have hZ_nontrivial : ¬ Z ≤ ρ.ker := by
    intro hZ_le_ker
    have hZ_eq_bot : Z = ⊥ := by
      exact le_bot_iff.mp (le_trans hZ_le_ker (by simpa using (MonoidHom.ker_eq_bot_iff ρ).2 hfaithful))
    apply hcenter_ne_bot
    exact
      (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (↥K))
        (f := K.subtype) K.subtype_injective).mp (by simpa [Z] using hZ_eq_bot)
  have hZpow : ∀ z : Z, (z : G) ^ q = 1 := by
    intro z
    rcases z.property with ⟨z0, hz0, hz_eq⟩
    have hz0q : (z0 : ↥K) ^ q = 1 := by
      exact
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥K) ∣ q by simp [hexp])) z0
    calc
      (z : G) ^ q = (K.subtype z0) ^ q := by rw [← hz_eq]
      _ = 1 := by simpa using congrArg K.subtype hz0q
  have hcard_Z : Nat.card Z = q :=
    natCard_eq_prime_of_central_exponent_prime_faithful_irreducible_local
      (ρ := ρ) hirr hfaithful Z hZ_central hZpow hZ_nontrivial
  have hcard_center : Nat.card (Subgroup.center (↥K)) = q := by
    calc
      Nat.card (Subgroup.center (↥K)) = Nat.card Z := by
        symm
        simpa [Z] using
          (Subgroup.card_map_of_injective (K := Subgroup.center (↥K))
            (f := K.subtype) K.subtype_injective)
      _ = q := hcard_Z
  let : Nontrivial (↥K ⧸ Subgroup.center (↥K)) :=
    quotient_center_nontrivial_of_not_isMulCommutative hcommK
  refine
    { center_order_p := hcard_center
      quotient_elementary_abelian :=
        isElementaryAbelian_quotient_center_of_commutator_le_center_of_exponent_eq hcomm hexp
      quotient_nontrivial := quotient_center_nontrivial_of_not_isMulCommutative hcommK }

private theorem CFSG.center_le_of_normal_ne_bot_of_commutator_le_center_of_prime_center_local
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    (hcomm : commutator K ≤ Subgroup.center K)
    (hcenter : Nat.card (Subgroup.center K) = q)
    {N : Subgroup K} [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    Subgroup.center K ≤ N := by
  by_cases hN_center : N ≤ Subgroup.center K
  · exact
      center_le_of_le_center_ne_bot_of_prime_center_local hcenter hN_center hN_ne_bot
  · let C : Subgroup K := ⁅N, (⊤ : Subgroup K)⁆
    have hC_le_N : C ≤ N := by
      exact Subgroup.commutator_le_left (H₁ := N) (H₂ := (⊤ : Subgroup K))
    have hC_le_center : C ≤ Subgroup.center K := by
      exact (Subgroup.commutator_mono (show N ≤ (⊤ : Subgroup K) by exact le_top) le_rfl).trans
        hcomm
    have hC_ne_bot : C ≠ ⊥ := by
      intro hC_eq_bot
      have hN_le_center : N ≤ Subgroup.center K := by
        have hN_le_centralizer : N ≤ Subgroup.centralizer ((⊤ : Subgroup K) : Set K) := by
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hC_eq_bot
        simpa [Subgroup.centralizer_univ] using hN_le_centralizer
      exact hN_center hN_le_center
    exact
      le_trans
        (center_le_of_le_center_ne_bot_of_prime_center_local hcenter hC_le_center hC_ne_bot)
        hC_le_N

private lemma CFSG.commutatorElement_mem_center_of_commutator_le_center_local
    {G : Type*} [Group G] (hcomm : commutator G ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  exact
    hcomm <|
      Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
        (show x ∈ (⊤ : Subgroup G) by trivial) (show y ∈ (⊤ : Subgroup G) by trivial)

lemma CFSG.commutatorElement_eq_one_of_mem_center_right_local
    {G : Type*} [Group G] {x z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz x)

lemma CFSG.commutatorElement_eq_one_of_mem_center_left_local
    {G : Type*} [Group G] {x z : G} (hz : z ∈ Subgroup.center G) :
    ⁅z, x⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hz x).symm)

lemma CFSG.commutatorElement_mul_left_of_commutator_le_center_local
    {K : Type*} [Group K] (hcomm : commutator K ≤ Subgroup.center K) (x y z : K) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz_cent : ⁅y, z⁆ ∈ Subgroup.center K :=
    commutatorElement_mem_center_of_commutator_le_center_local hcomm y z
  have hleft :
      x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    calc
      x * ⁅y, z⁆ * x⁻¹ = (⁅y, z⁆ * x) * x⁻¹ := by
        rw [(Subgroup.mem_center_iff.mp hyz_cent x).symm]
      _ = ⁅y, z⁆ := by simp [mul_assoc]
  have hEq : ⁅x * y, z⁆ * ⁅z, x⁆ = ⁅y, z⁆ := by
    calc
      ⁅x * y, z⁆ * ⁅z, x⁆ = x * ⁅y, z⁆ * x⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      _ = ⁅y, z⁆ := hleft
  have hyz_comm : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    ((Subgroup.mem_center_iff.mp hyz_cent) ⁅x, z⁆).symm
  have hzx_one : ⁅z, x⁆ * ⁅x, z⁆ = 1 := by
    simpa [commutatorElement_inv] using (mul_inv_cancel (⁅z, x⁆))
  calc
    ⁅x * y, z⁆ = ⁅x * y, z⁆ * 1 := by simp
    _ = ⁅x * y, z⁆ * (⁅z, x⁆ * ⁅x, z⁆) := by rw [hzx_one]
    _ = (⁅x * y, z⁆ * ⁅z, x⁆) * ⁅x, z⁆ := by simp [mul_assoc]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hEq]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyz_comm

lemma CFSG.commutatorElement_mul_right_of_commutator_le_center_local
    {K : Type*} [Group K] (hcomm : commutator K ≤ Subgroup.center K) (x y z : K) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hxz_cent : ⁅x, z⁆ ∈ Subgroup.center K :=
    commutatorElement_mem_center_of_commutator_le_center_local hcomm x z
  have hright :
      y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    calc
      y * ⁅x, z⁆ * y⁻¹ = (⁅x, z⁆ * y) * y⁻¹ := by
        rw [(Subgroup.mem_center_iff.mp hxz_cent y).symm]
      _ = ⁅x, z⁆ := by simp [mul_assoc]
  have hEq : ⁅y, x⁆ * ⁅x, y * z⁆ = ⁅x, z⁆ := by
    calc
      ⁅y, x⁆ * ⁅x, y * z⁆ = y * ⁅x, z⁆ * y⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      _ = ⁅x, z⁆ := hright
  have hxyx_one : ⁅x, y⁆ * ⁅y, x⁆ = 1 := by
    simpa [commutatorElement_inv] using (mul_inv_cancel (⁅x, y⁆))
  calc
    ⁅x, y * z⁆ = 1 * ⁅x, y * z⁆ := by simp
    _ = (⁅x, y⁆ * ⁅y, x⁆) * ⁅x, y * z⁆ := by rw [hxyx_one]
    _ = ⁅x, y⁆ * (⁅y, x⁆ * ⁅x, y * z⁆) := by simp [mul_assoc]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hEq]

lemma CFSG.commutatorElement_mul_center_right_left_invariant_local
    {K : Type*} [Group K] (hcomm : commutator K ≤ Subgroup.center K)
    {x y z : K} (hz : z ∈ Subgroup.center K) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_of_commutator_le_center_local hcomm x z y,
    commutatorElement_eq_one_of_mem_center_left_local hz, mul_one]

lemma CFSG.commutatorElement_mul_center_right_right_invariant_local
    {K : Type*} [Group K] (hcomm : commutator K ≤ Subgroup.center K)
    {x y z : K} (hz : z ∈ Subgroup.center K) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_of_commutator_le_center_local hcomm x y z,
    commutatorElement_eq_one_of_mem_center_right_local hz, mul_one]

theorem CFSG.natCard_eq_prime_pow_succ_of_isExtraspecial_local
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K] {n : ℕ}
    (hcardQ : Nat.card (K ⧸ Subgroup.center K) = q ^ n) :
    Nat.card K = q ^ (n + 1) := by
  calc
    Nat.card K = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) := by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Subgroup.center K)
    _ = q ^ n * q := by
      rw [hcardQ, IsExtraspecial.center_order_p q K]
    _ = q ^ (n + 1) := by
      rw [pow_succ', Nat.mul_comm]


public noncomputable def CFSG.centerAddEquivZMod_local
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K] :
    Additive (Subgroup.center K) ≃+ ZMod q := by
  let : CommGroup (Subgroup.center K) := IsMulCommutative.instCommGroup
  exact
    addEquivOfPrimeCardEq
      (G := Additive (Subgroup.center K)) (G' := ZMod q)
      ((Nat.card_congr Additive.toMul).trans (IsExtraspecial.center_order_p q K))
      (by simp [Nat.card_eq_fintype_card, ZMod.card])

noncomputable def CFSG.extraspecialCenterPairingRaw
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K] :
    K → K → ZMod q := fun x y =>
  centerAddEquivZMod_local (q := q) (K := K)
    (Additive.ofMul
      ⟨⁅x, y⁆,
        commutatorElement_mem_center_of_commutator_le_center_local
          (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) x y⟩)

theorem CFSG.extraspecialCenterPairingRaw_mul_center_left
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {x y z : K} (hz : z ∈ Subgroup.center K) :
    extraspecialCenterPairingRaw (q := q) (K := K) (x * z) y =
      extraspecialCenterPairingRaw (q := q) (K := K) x y := by
  simp [extraspecialCenterPairingRaw,
    commutatorElement_mul_center_right_left_invariant_local
      (K := K) (hcomm := commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) hz]

theorem CFSG.extraspecialCenterPairingRaw_mul_center_right
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {x y z : K} (hz : z ∈ Subgroup.center K) :
    extraspecialCenterPairingRaw (q := q) (K := K) x (y * z) =
      extraspecialCenterPairingRaw (q := q) (K := K) x y := by
  simp [extraspecialCenterPairingRaw,
    commutatorElement_mul_center_right_right_invariant_local
      (K := K) (hcomm := commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) hz]

theorem CFSG.extraspecialCenterPairingRaw_mul_left
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    (x y z : K) :
    extraspecialCenterPairingRaw (q := q) (K := K) (x * y) z =
      extraspecialCenterPairingRaw (q := q) (K := K) x z +
        extraspecialCenterPairingRaw (q := q) (K := K) y z := by
  let e := centerAddEquivZMod_local (q := q) (K := K)
  change e _ = e _ + e _
  rw [← e.map_add]
  congr 1
  ext
  simp [commutatorElement_mul_left_of_commutator_le_center_local
      (commutator_le_center_of_isExtraspecial_local (q := q) (K := K))]

theorem CFSG.extraspecialCenterPairingRaw_mul_right
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    (x y z : K) :
    extraspecialCenterPairingRaw (q := q) (K := K) x (y * z) =
      extraspecialCenterPairingRaw (q := q) (K := K) x y +
        extraspecialCenterPairingRaw (q := q) (K := K) x z := by
  let e := centerAddEquivZMod_local (q := q) (K := K)
  change e _ = e _ + e _
  rw [← e.map_add]
  congr 1
  ext
  simp [commutatorElement_mul_right_of_commutator_le_center_local
      (commutator_le_center_of_isExtraspecial_local (q := q) (K := K))]

noncomputable def CFSG.extraspecialCenterPairing
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K] :
    Additive (K ⧸ Subgroup.center K) → Additive (K ⧸ Subgroup.center K) → ZMod q :=
  fun a b =>
    Quotient.liftOn₂ (Additive.toMul a) (Additive.toMul b)
      (fun x y => extraspecialCenterPairingRaw (q := q) (K := K) x y)
      (by
        intro x₁ y₁ x₂ y₂ hx hy
        have hxq : (x₁ : K ⧸ Subgroup.center K) = x₂ := Quotient.sound hx
        have hyq : (y₁ : K ⧸ Subgroup.center K) = y₂ := Quotient.sound hy
        have hxmem : x₁⁻¹ * x₂ ∈ Subgroup.center K := QuotientGroup.eq.mp hxq
        have hymem : y₁⁻¹ * y₂ ∈ Subgroup.center K := QuotientGroup.eq.mp hyq
        calc
          extraspecialCenterPairingRaw (q := q) (K := K) x₁ y₁ =
              extraspecialCenterPairingRaw (q := q) (K := K) (x₁ * (x₁⁻¹ * x₂)) y₁ := by
                symm
                exact extraspecialCenterPairingRaw_mul_center_left
                  (q := q) (K := K) (x := x₁) (y := y₁) (z := x₁⁻¹ * x₂) hxmem
          _ = extraspecialCenterPairingRaw (q := q) (K := K) x₂ y₁ := by simp
          _ = extraspecialCenterPairingRaw (q := q) (K := K) x₂ (y₁ * (y₁⁻¹ * y₂)) := by
                symm
                exact extraspecialCenterPairingRaw_mul_center_right
                  (q := q) (K := K) (x := x₂) (y := y₁) (z := y₁⁻¹ * y₂) hymem
          _ = extraspecialCenterPairingRaw (q := q) (K := K) x₂ y₂ := by simp)


theorem CFSG.odd_ne_prime_pow_add_one_local {h q n : ℕ} [Fact q.Prime] (hh : Odd h)
    (hq_ne_two : q ≠ 2) :
    h ≠ q ^ n + 1 := by
  intro hEq
  rcases hh with ⟨a, ha⟩
  have hqpow_odd : Odd (q ^ n) := (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime q) hq_ne_two).pow
  rcases hqpow_odd with ⟨b, hb⟩
  rw [hEq, hb] at ha
  omega

theorem CFSG.even_finrank_of_isAlt_nondegenerate_local
    {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) (hNondeg : B.Nondegenerate) :
    Even (Module.finrank K V) := by
  by_contra hEven
  have hOdd : Odd (Module.finrank K V) := Nat.not_even_iff_odd.mp hEven
  let b := Module.finBasis K V
  let A := LinearMap.BilinForm.toMatrix b B
  have hA_transpose : A.transpose = -A := by
    ext i j
    simp [A, hAlt.neg_eq (b i) (b j)]
  have hdet_ne_zero : Matrix.det A ≠ 0 :=
    Matrix.Nondegenerate.det_ne_zero (LinearMap.BilinForm.Nondegenerate.toMatrix hNondeg b)
  have hdet_eq : Matrix.det A = -Matrix.det A := by
    calc
      Matrix.det A = Matrix.det A.transpose := by rw [Matrix.det_transpose]
      _ = Matrix.det (-A) := by rw [hA_transpose]
      _ = (-1 : K) ^ Fintype.card (Fin (Module.finrank K V)) * Matrix.det A := by
        rw [Matrix.det_neg]
      _ = -Matrix.det A := by
        simp [hOdd.neg_one_pow]
  have htwo : (2 : K) * Matrix.det A = 0 := by
    have hsum := congrArg (fun x : K => x + Matrix.det A) hdet_eq
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hsum
  exact hdet_ne_zero ((mul_eq_zero.mp htwo).resolve_left two_ne_zero)

theorem CFSG.exists_natCard_eq_prime_pow_two_mul_add_one_of_isExtraspecial_local
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    (hq_odd : Odd q) :
    ∃ n : ℕ, Nat.card K = q ^ (2 * n + 1) := by
  let Qmul := K ⧸ Subgroup.center K
  let : IsElementaryAbelian q Qmul := IsExtraspecial.quotient_elementary_abelian q K
  let : IsMulCommutative Qmul := (inferInstance : IsElementaryAbelian q Qmul).toIsMulCommutative
  let : CommGroup Qmul := IsMulCommutative.instCommGroup
  let Q := Additive Qmul
  let : AddCommGroup Q := Additive.addCommGroup
  -- letI : Module (ZMod q) Q := IsElementaryAbelian.isVectorSpace q Qmul
  let : Finite Q := inferInstance
  let : FiniteDimensional (ZMod q) Q := Module.Finite.of_finite
  have hq_ne_two : q ≠ 2 := by
    intro hq_two
    have : ¬ Odd 2 := by decide
    exact this (hq_two ▸ hq_odd)
  let : Invertible (2 : ZMod q) :=
    invertibleOfCharPNotDvd (K := ZMod q) (p := q) (t := 2) (by
      intro hq_dvd_two
      have hq_le_two := Nat.le_of_dvd (by decide : 0 < 2) hq_dvd_two
      have hq_ge_two := (Fact.out : Nat.Prime q).two_le
      omega)
  have hpair_zero_right :
      ∀ x : Q, extraspecialCenterPairing (q := q) (K := K) x 0 = 0 := by
    intro x
    rw [← ofMul_toMul x]
    refine Quotient.inductionOn (Additive.toMul x) ?_
    intro x
    have hraw : extraspecialCenterPairingRaw (q := q) (K := K) x (1 : K) = 0 := by
      simp [extraspecialCenterPairingRaw]
    change extraspecialCenterPairingRaw (q := q) (K := K) x 1 = 0
    exact hraw
  have hpair_add_right :
      ∀ x y₁ y₂ : Q,
        extraspecialCenterPairing (q := q) (K := K) x (y₁ + y₂) =
          extraspecialCenterPairing (q := q) (K := K) x y₁ +
            extraspecialCenterPairing (q := q) (K := K) x y₂ := by
    intro x y₁ y₂
    rw [← ofMul_toMul x, ← ofMul_toMul y₁, ← ofMul_toMul y₂]
    refine Quotient.inductionOn₃ (Additive.toMul x) (Additive.toMul y₁) (Additive.toMul y₂) ?_
    intro x y₁ y₂
    change extraspecialCenterPairingRaw (q := q) (K := K) x (y₁ * y₂) =
      extraspecialCenterPairingRaw (q := q) (K := K) x y₁ +
        extraspecialCenterPairingRaw (q := q) (K := K) x y₂
    exact extraspecialCenterPairingRaw_mul_right (q := q) (K := K) x y₁ y₂
  have hpair_zero_left :
      ∀ y : Q, extraspecialCenterPairing (q := q) (K := K) 0 y = 0 := by
    intro y
    rw [← ofMul_toMul y]
    refine Quotient.inductionOn (Additive.toMul y) ?_
    intro y
    have hraw : extraspecialCenterPairingRaw (q := q) (K := K) (1 : K) y = 0 := by
      simp [extraspecialCenterPairingRaw]
    change extraspecialCenterPairingRaw (q := q) (K := K) 1 y = 0
    exact hraw
  have hpair_add_left :
      ∀ x₁ x₂ y : Q,
        extraspecialCenterPairing (q := q) (K := K) (x₁ + x₂) y =
          extraspecialCenterPairing (q := q) (K := K) x₁ y +
            extraspecialCenterPairing (q := q) (K := K) x₂ y := by
    intro x₁ x₂ y
    rw [← ofMul_toMul x₁, ← ofMul_toMul x₂, ← ofMul_toMul y]
    refine Quotient.inductionOn₃ (Additive.toMul x₁) (Additive.toMul x₂) (Additive.toMul y) ?_
    intro x₁ x₂ y
    change extraspecialCenterPairingRaw (q := q) (K := K) (x₁ * x₂) y =
      extraspecialCenterPairingRaw (q := q) (K := K) x₁ y +
        extraspecialCenterPairingRaw (q := q) (K := K) x₂ y
    exact extraspecialCenterPairingRaw_mul_left (q := q) (K := K) x₁ x₂ y
  let pairingAdd : Q →+ AddMonoidHom Q (ZMod q) :=
    { toFun := fun x =>
        { toFun := fun y => extraspecialCenterPairing (q := q) (K := K) x y
          map_zero' := hpair_zero_right x
          map_add' := hpair_add_right x }
      map_zero' := by
        apply AddMonoidHom.ext
        intro y
        exact hpair_zero_left y
      map_add' := by
        intro x₁ x₂
        apply AddMonoidHom.ext
        intro y
        exact hpair_add_left x₁ x₂ y }
  let B : LinearMap.BilinForm (ZMod q) Q :=
    { toFun := fun x => (pairingAdd x).toZModLinearMap q
      map_add' := by
        intro x₁ x₂
        ext y
        simp
      map_smul' := by
        intro c x
        ext y
        simpa using DFunLike.congr_fun (ZMod.map_smul pairingAdd c x) y }
  have hB_mk (x y : K) :
      B (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
        extraspecialCenterPairingRaw (q := q) (K := K) x y := by
    rfl
  have hAlt : B.IsAlt := by
    intro x
    rw [← ofMul_toMul x]
    refine Quotient.inductionOn (Additive.toMul x) ?_
    intro x
    change B (Additive.ofMul (QuotientGroup.mk x))
      (Additive.ofMul (QuotientGroup.mk x)) = 0
    rw [hB_mk]
    simp [extraspecialCenterPairingRaw]
  have hSep : B.SeparatingLeft := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial]
    intro x hx
    rw [← ofMul_toMul x] at hx ⊢
    revert hx
    refine Quotient.inductionOn (Additive.toMul x) ?_
    intro x hx
    change B (Additive.ofMul (QuotientGroup.mk x)) = 0 at hx
    have hcent : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy :
          B (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) = 0 := by
        simpa using DFunLike.congr_fun hx (Additive.ofMul (QuotientGroup.mk y))
      rw [hB_mk] at hy
      have hy' :
          (Additive.ofMul
            ⟨⁅x, y⁆,
              commutatorElement_mem_center_of_commutator_le_center_local
                (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) x y⟩ :
            Additive (Subgroup.center K)) = 0 := by
        apply (centerAddEquivZMod_local (q := q) (K := K)).injective
        simpa [extraspecialCenterPairingRaw] using hy
      have hxy : ⁅x, y⁆ = 1 := by
        simpa using congrArg Additive.toMul hy'
      exact (commutatorElement_eq_one_iff_mul_comm.mp hxy).symm
    have hqone : (QuotientGroup.mk x : Qmul) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center K) x).2 hcent
    change (QuotientGroup.mk x : Qmul) = 1
    exact hqone
  have hNondeg : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hSep
  have hEven : Even (Module.finrank (ZMod q) Q) :=
    even_finrank_of_isAlt_nondegenerate_local (K := ZMod q) (V := Q) B hAlt hNondeg
  have hcardQ :
      Nat.card Qmul = q ^ Module.finrank (ZMod q) Q := by
    calc
      Nat.card Qmul = Nat.card Q :=
        (Nat.card_congr (Additive.toMul : Q ≃ Qmul)).symm
      _ = q ^ Module.finrank (ZMod q) Q := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using
          (Module.natCard_eq_pow_finrank (K := ZMod q) (V := Q))
  have hcardK :
      Nat.card K = q ^ (Module.finrank (ZMod q) Q + 1) := by
    simpa [Q] using natCard_eq_prime_pow_succ_of_isExtraspecial_local (q := q) (K := K) hcardQ
  rcases hEven with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hcardK, hn]
  congr 1
  omega

theorem CFSG.theorem_3_4_extraspecial_faithful_center_fixedpoints_of_isExtraspecial_card
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hodd : Odd (Nat.card G)) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    {q : ℕ} [Fact q.Prime] (hfixR : ρ.fixedSubspace R = ⊥)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hcent_r :
      ∀ r : R, r ≠ 1 →
        elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype)
    (hirr : Representation.IsIrreducible ρ) (hfaithful : Function.Injective ρ)
    [IsExtraspecial q ↥K] {n : ℕ} (hcardK : Nat.card K = q ^ (2 * n + 1)) :
    False := by
  let hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  let φ : R →* MulAut K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))
  let e : K ⋊[φ] R ≃* G := SemidirectProduct.mulEquivSubgroup hKR
  let σ : Representation F (K ⋊[φ] R) V := ρ.comp e.toMonoidHom
  have : Representation.IsIrreducible σ := by
    exact
      (Theory.Representation.RepEquiv.irreducible_iff_group_iso (ρ := σ) (σ := ρ) e
        (by intro g v; rfl)).2 hirr
  have : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ hirr
  have hσfaithful : Function.Injective σ :=
    (injective_comp_mulEquiv_toMonoidHom_iff ρ e).2 hfaithful
  have hq_dvdK : q ∣ Nat.card K := by
    rw [hcardK]
    exact dvd_pow_self q (by positivity)
  have hq_odd : Odd q := by
    exact odd_of_card_dvd hodd (dvd_trans hq_dvdK (Subgroup.card_subgroup_dvd_card K))
  have hq_ne_two : q ≠ 2 := by
    intro hq_two
    have : ¬ Odd 2 := by decide
    exact this (hq_two ▸ hq_odd)
  have hR_odd : Odd (Nat.card R) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card R)
  let : Fact (Nat.Prime (Nat.card R)) := ⟨hR_prime⟩
  have : IsCyclic ↥R := isCyclic_of_prime_card (p := Nat.card R) rfl
  have hcentralizer :
      ∀ x : R, x ≠ 1 → {p : K | φ x p = p} = Subgroup.center (↥K) := by
    intro x hx
    ext y
    constructor
    · intro hy
      have hycent : (y : G) ∈ elementCentralizerIn K (x : G) := by
        refine ⟨y.property, ?_⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
          simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK]
            using congrArg Subtype.val hy
        have hmul := congrArg (fun t : G => t * (x : G)) hyconj
        simpa [mul_assoc] using hmul.symm
      have hyZ : (y : G) ∈ (Subgroup.center (↥K)).map K.subtype := by
        simpa [hcent_r x hx] using hycent
      rcases hyZ with ⟨z, hz, hz_eq⟩
      have hzy : z = y := K.subtype_injective hz_eq
      simpa [hzy] using hz
    · intro hy
      apply Subtype.ext
      have hycent : (y : G) ∈ elementCentralizerIn K (x : G) := by
        simpa [hcent_r x hx] using show (y : G) ∈ (Subgroup.center (↥K)).map K.subtype by
          exact ⟨y, hy, rfl⟩
      have hmul : (y : G) * (x : G) = (x : G) * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hycent.2
      have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
        calc
          (x : G) * (y : G) * (x : G)⁻¹ = ((y : G) * (x : G)) * (x : G)⁻¹ := by
            rw [hmul.symm]
          _ = y := by simp [mul_assoc]
      simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hyconj
  have hcardSD :
      Nat.card (K ⋊[φ] R) = Nat.card K * Nat.card R := by
    simp [φ]
  have hcard_prod :
      Nat.card R * q ^ (2 * n + 1) = Nat.card G := by
    calc
      Nat.card R * q ^ (2 * n + 1) = Nat.card R * Nat.card K := by rw [hcardK]
      _ = Nat.card (K ⋊[φ] R) := by
        rw [hcardSD, Nat.mul_comm]
      _ = Nat.card G := Nat.card_congr e.toEquiv
  have hc :
      ¬ ringChar F ∣ Nat.card R * q ^ (2 * n + 1) := by
    rcases hchar with hchar0 | ⟨hchar_prime, hchar_coprime⟩
    · rw [hchar0]
      intro hdiv
      have hzero : Nat.card G = 0 := by
        rw [← hcard_prod]
        simpa using hdiv
      exact Nat.ne_of_gt Nat.card_pos hzero
    · intro hdiv
      have hdivG : ringChar F ∣ Nat.card G := by
        simpa [hcard_prod] using hdiv
      exact (hchar_prime.coprime_iff_not_dvd.mp hchar_coprime) hdivG
  have hhne : Nat.card R ≠ q ^ n + 1 :=
    odd_ne_prime_pow_add_one_local (h := Nat.card R) hR_odd hq_ne_two
  have hfixed_nonzero :
      {v | ∀ h : R, σ ⟨1, h⟩ v = v} ≠ ({0} : Set V) :=
    theorem_2_5_b (p := q) (n := n) (P := ↥K) hcardK (h := Nat.card R) (H := ↥R) rfl
      (Nat.Coprime.symm (Nat.Coprime.of_dvd_left hq_dvdK hcopKR)) (φ := φ) hcentralizer hc hhne
      (ρ := σ) hσfaithful
  have hfixed_eq :
      {v | ∀ h : R, σ ⟨1, h⟩ v = v} = {v : V | ∀ h : R, ρ h v = v} := by
    have he_inr : ∀ h : R, e (SemidirectProduct.inr h) = (h : G) := by
      intro h
      simp [e, SemidirectProduct.mulEquivSubgroup, SemidirectProduct.monoidHomSubgroup]
    ext v
    constructor
    · intro hv h
      simpa [σ, he_inr h] using hv h
    · intro hv h
      simpa [σ, he_inr h] using hv h
  have hfix_zero : {v : V | ∀ h : R, ρ h v = v} = ({0} : Set V) :=
    (fixedSubspace_eq_bot_iff_fixedVectors_eq_zero ρ R).mp hfixR
  exact hfixed_nonzero (hfixed_eq.trans hfix_zero)

theorem CFSG.theorem_3_4_extraspecial_faithful_center_fixedpoints
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)] (hfixR : ρ.fixedSubspace R = ⊥)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hcommK : ¬ IsMulCommutative ↥K)
    (hcomm : commutator (↥K) ≤ Subgroup.center (↥K)) (hexp : Monoid.exponent (↥K) = q)
    (hcent_r :
      ∀ r : R, r ≠ 1 →
        elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype)
    (hirr : Representation.IsIrreducible ρ)
    (hcomm_nontrivial : ¬ (commutator (↥K)).map K.subtype ≤ ρ.ker) :
    False := by
  let _ := hodd
  let _ := hcent_r
  let C : Subgroup G := (commutator (↥K)).map K.subtype
  have hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  have hC_le_K : C ≤ K := by
    intro c hc
    rcases hc with ⟨x, hx, rfl⟩
    exact x.property
  have hK_nontrivial : ¬ K ≤ ρ.ker := by
    intro hK_le_ker
    exact hcomm_nontrivial (le_trans hC_le_K hK_le_ker)
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_eq_bot
    exact hK_nontrivial (hK_eq_bot ▸ bot_le)
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  have hqdvdK : q ∣ Nat.card K := by
    obtain ⟨nK, hnK_pos, hcardKq⟩ :=
      (IsPGroup.nontrivial_iff_card (p := q) (G := ↥K) (hG := Fact.out)).mp inferInstance
    rw [hcardKq]
    exact dvd_pow_self q (Nat.ne_of_gt hnK_pos)
  have hker_le_K : ρ.ker ≤ K :=
    ker_le_of_isComplement'_prime_fixedSubspace_eq_bot
      K R ρ hKR hcopKR hR_prime hfixR hK_nontrivial hqdvdK hexp
  have hcommRZ :
      ∀ r : R, ∀ z : Subgroup.center (↥K), (r : G) * (z : G) = (z : G) * (r : G) := by
    intro r z
    by_cases hr : r = 1
    · subst hr
      simp
    · have hzmem : (z : G) ∈ elementCentralizerIn K (r : G) := by
        rw [hcent_r r hr]
        exact ⟨z, z.property, rfl⟩
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzmem.2).symm
  have hZ_central : (Subgroup.center (↥K)).map K.subtype ≤ Subgroup.center G :=
    center_map_le_center_of_isComplement'_commute K R hKR hcommRZ
  let _ := hchar_of_card_dvd (G := G) (F := F) hchar (Subgroup.card_subgroup_dvd_card K)
  let _ := hker_le_K
  let _ := hZ_central
  let _ := hcommK
  let _ := hirr
  by_cases hker_bot : ρ.ker = ⊥
  · have hfaithful : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker_bot
    have hK_extraspecial : IsExtraspecial q ↥K :=
      isExtraspecial_of_commutator_le_center_of_exponent_eq_of_faithful_irreducible_local
        K ρ hirr hfaithful hcommK hcomm hexp hZ_central
    let : IsExtraspecial q ↥K := hK_extraspecial
    have hq_odd : Odd q := by
      exact odd_of_card_dvd hodd (dvd_trans hqdvdK (Subgroup.card_subgroup_dvd_card K))
    obtain ⟨n, hcardK⟩ :=
      exists_natCard_eq_prime_pow_two_mul_add_one_of_isExtraspecial_local (q := q) (K := ↥K)
        hq_odd
    exact
      theorem_3_4_extraspecial_faithful_center_fixedpoints_of_isExtraspecial_card K R ρ hodd
        hK_normal hKR hcopKR hR_prime hfixR hchar hcent_r hirr hfaithful hcardK
  · have hker_ne_bot : ρ.ker ≠ ⊥ := hker_bot
    let qG : G →* G ⧸ ρ.ker := QuotientGroup.mk' ρ.ker
    let Kq : Subgroup (G ⧸ ρ.ker) := K.map qG
    let Rq : Subgroup (G ⧸ ρ.ker) := R.map qG
    let Zq : Subgroup (G ⧸ ρ.ker) := ((Subgroup.center (↥K)).map K.subtype).map qG
    let ρq : Representation F (G ⧸ ρ.ker) V := Theory.Representation.kerRepresentation ρ
    have hρq :
        Representation.IsIrreducible ρq ∧
          Function.Injective ρq ∧
          ρq.fixedSubspace Rq = ⊥ ∧
          ¬ C.map qG ≤ ρq.ker :=
      quotient_representation_data_of_irreducible_not_le_ker_local ρ R C hirr hfixR
        hcomm_nontrivial
    have hρq_ker : ρq.ker = ⊥ := ker_of_kerRepresentation_eq_bot (ρ := ρ)
    have hCq_ne_bot : C.map qG ≠ ⊥ := by
      intro hCq_bot
      exact hρq.2.2.2 (hCq_bot ▸ bot_le)
    have hCq_le_Kq : C.map qG ≤ Kq := by
      exact Subgroup.map_mono hC_le_K
    have hKq_ne_bot : Kq ≠ ⊥ := by
      intro hKq_bot
      exact hCq_ne_bot (le_bot_iff.mp (hKq_bot ▸ hCq_le_Kq))
    let : Nontrivial ↥Kq := Kq.nontrivial_iff_ne_bot.mpr hKq_ne_bot
    have hcommKq : ¬ IsMulCommutative ↥Kq :=
      not_isMulCommutative_map_mk'_of_commutator_map_ne_bot K ρ.ker hCq_ne_bot
    have hKq_exp : Monoid.exponent (↥Kq) = q :=
      exponent_map_mk'_eq_prime_of_exponent_eq_prime_of_ne_bot (q := q) K ρ.ker hexp hKq_ne_bot
    have : Fact (IsPGroup q ↥Kq) := ⟨IsPGroup.map (p := q) (H := K) Fact.out qG⟩
    have hKq_normal : Kq.Normal := by
      exact Subgroup.Normal.map (H := K) (f := qG) hK_normal (QuotientGroup.mk'_surjective _)
    have hKRq : Kq.IsComplement' Rq :=
      isComplement'_map_mk'_of_le_isComplement' K R ρ.ker hker_le_K hKR
    have hcopKqRq : Nat.Coprime (Nat.card Kq) (Nat.card Rq) :=
      coprime_card_map_mk'_of_le_isComplement' K R ρ.ker hker_le_K hKR hcopKR
    have hRq_prime : Nat.Prime (Nat.card Rq) :=
      prime_card_map_mk'_of_le_isComplement' K R ρ.ker hker_le_K hKR hR_prime
    have hRq_ne_bot : Rq ≠ ⊥ := by
      intro hRq_bot
      exact hRq_prime.ne_one ((Subgroup.eq_bot_iff_card (H := Rq)).1 hRq_bot)
    let : Nontrivial ↥Rq := Rq.nontrivial_iff_ne_bot.mpr hRq_ne_bot
    have hodd_qG : Odd (Nat.card (G ⧸ ρ.ker)) := by
      exact odd_of_card_dvd hodd (Subgroup.card_quotient_dvd_card (s := ρ.ker))
    have hchar_qG :
        ringChar F = 0 ∨
          (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card (G ⧸ ρ.ker))) := by
      exact hchar_of_card_dvd (G := G) (F := F) hchar (Subgroup.card_quotient_dvd_card (s := ρ.ker))
    have hC_le_Z : C ≤ (Subgroup.center (↥K)).map K.subtype := by
      simpa [C] using Subgroup.map_mono (f := K.subtype) hcomm
    have hZq_ne_bot : Zq ≠ ⊥ := by
      intro hZq_bot
      have hZ_le_ker : (Subgroup.center (↥K)).map K.subtype ≤ ρ.ker := by
        intro z hzZ
        have hzq_mem : qG z ∈ Zq := ⟨z, hzZ, rfl⟩
        have hzq_bot : qG z ∈ (⊥ : Subgroup (G ⧸ ρ.ker)) := by
          simpa [Zq, hZq_bot] using hzq_mem
        exact (QuotientGroup.eq_one_iff (N := ρ.ker) z).mp (by simpa [qG] using hzq_bot)
      exact hcomm_nontrivial (le_trans hC_le_Z hZ_le_ker)
    have hZq_central : Zq ≤ Subgroup.center (G ⧸ ρ.ker) := by
      intro z hz
      rcases hz with ⟨z0, hz0, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro gq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := ρ.ker) gq
      have hz0_cent : z0 ∈ Subgroup.center G := hZ_central hz0
      simpa [qG, map_mul] using congrArg qG ((Subgroup.mem_center_iff.mp hz0_cent) g)
    have hZq_pow : ∀ z : Zq, (z : G ⧸ ρ.ker) ^ q = 1 := by
      intro z
      rcases z.property with ⟨z0, hz0, hzq⟩
      rcases hz0 with ⟨z1, hz1, rfl⟩
      have hz1q : (z1 : ↥K) ^ q = 1 := by
        exact
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (show Monoid.exponent (↥K) ∣ q by simp [hexp])) z1
      have hz1qG : (z1 : G) ^ q = 1 := by
        simpa using congrArg K.subtype hz1q
      calc
        (z : G ⧸ ρ.ker) ^ q = (qG (K.subtype z1)) ^ q := by
          simpa using congrArg (fun t : G ⧸ ρ.ker => t ^ q) hzq.symm
        _ = qG ((z1 : G) ^ q) := by simp [qG]
        _ = 1 := by simpa [qG] using congrArg qG hz1qG
    have hZq_nontrivial : ¬ Zq ≤ ρq.ker := by
      intro hZq_ker
      exact hZq_ne_bot (le_bot_iff.mp (hρq_ker ▸ hZq_ker))
    have hZq_card : Nat.card Zq = q :=
      natCard_eq_prime_of_central_exponent_prime_faithful_irreducible_local
        (ρ := ρq) hρq.1 hρq.2.1 Zq hZq_central hZq_pow hZq_nontrivial
    have hZq_le_Kq : Zq ≤ Kq := by
      intro z hzZq
      rcases hzZq with ⟨z0, hz0, rfl⟩
      rcases hz0 with ⟨z1, hz1, rfl⟩
      exact ⟨z1, z1.property, rfl⟩
    have hZq_le_centerKq : Zq ≤ (Subgroup.center (↥Kq)).map Kq.subtype := by
      intro z hzZq
      rcases hzZq with ⟨z0, hz0, rfl⟩
      rcases hz0 with ⟨z1, hz1, rfl⟩
      let zKq : Kq := ⟨qG (K.subtype z1), ⟨z1, z1.property, rfl⟩⟩
      refine ⟨zKq, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr ?_
      intro y
      rcases y.property with ⟨y0, hy0, hyq⟩
      have hzy : y0 * (K.subtype z1 : G) = (K.subtype z1 : G) * y0 := by
        simpa using congrArg K.subtype ((Subgroup.mem_center_iff.mp hz1) ⟨y0, hy0⟩)
      apply Subtype.ext
      calc
        (((y * zKq : Kq)) : G ⧸ ρ.ker) = qG y0 * qG (K.subtype z1) := by
          simp [zKq, hyq]
        _ = qG (y0 * (K.subtype z1 : G)) := by simp [qG]
        _ = qG ((K.subtype z1 : G) * y0) := by rw [hzy]
        _ = qG (K.subtype z1) * qG y0 := by simp [qG]
        _ = (((zKq * y : Kq)) : G ⧸ ρ.ker) := by
          simp [zKq, hyq]
    have hCq_le_Zq : C.map qG ≤ Zq := by
      simpa [Zq] using Subgroup.map_mono (f := qG) hC_le_Z
    have hCq_card : Nat.card (C.map qG) = q := by
      have hCq_card_dvd : Nat.card (C.map qG) ∣ Nat.card Zq :=
        Subgroup.card_dvd_of_le hCq_le_Zq
      rw [hZq_card] at hCq_card_dvd
      have hCq_card_ne_one : Nat.card (C.map qG) ≠ 1 := by
        intro hCq_card_one
        exact hCq_ne_bot ((Subgroup.eq_bot_iff_card (H := C.map qG)).2 hCq_card_one)
      rcases (Nat.dvd_prime Fact.out).1 hCq_card_dvd with hCq_card_one | hCq_card_q
      · exact False.elim (hCq_card_ne_one hCq_card_one)
      · exact hCq_card_q
    have hCq_eq_Zq : C.map qG = Zq := by
      apply Subgroup.eq_of_le_of_card_ge hCq_le_Zq
      rw [hZq_card, hCq_card]
    have hCq_commutator : C.map qG = ⁅Kq, Kq⁆ := by
      simpa [C, Kq] using
        (show ((commutator (↥K)).map K.subtype).map qG = ⁅K.map qG, K.map qG⁆ by
          rw [Subgroup.map_subtype_commutator, Subgroup.map_commutator])
    have hcommKq_map :
        (commutator (↥Kq)).map Kq.subtype = C.map qG := by
      rw [Subgroup.map_subtype_commutator]
      exact hCq_commutator.symm
    have hcommKq_map_le_center :
        (commutator (↥Kq)).map Kq.subtype ≤ (Subgroup.center (↥Kq)).map Kq.subtype := by
      intro x hx
      rw [hcommKq_map] at hx
      have hxC : x ∈ C.map qG := hx
      rw [hCq_eq_Zq] at hxC
      exact hZq_le_centerKq hxC
    have hcommKq_center : commutator (↥Kq) ≤ Subgroup.center (↥Kq) := by
      intro x hx
      have hxmap : (x : G ⧸ ρ.ker) ∈ (commutator (↥Kq)).map Kq.subtype := by
        exact ⟨x, hx, rfl⟩
      have hxcent_map : (x : G ⧸ ρ.ker) ∈ (Subgroup.center (↥Kq)).map Kq.subtype :=
        hcommKq_map_le_center hxmap
      rcases hxcent_map with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Kq.subtype_injective hyx
      simpa [hy_eq] using hy
    have hcent_rq_raw :
        ∀ rq : Rq, rq ≠ 1 → elementCentralizerIn Kq (rq : G ⧸ ρ.ker) = Zq := by
      have hsolvK : Group.IsSolvable ↥K := by
        let : Group.IsNilpotent ↥K :=
          IsPGroup.isNilpotent (p := q) (G := ↥K) (h := (Fact.out : IsPGroup q ↥K))
        infer_instance
      intro rq hrq_ne
      rcases rq.property with ⟨r, hrR, hrq⟩
      let rR : R := ⟨r, hrR⟩
      have hrR_ne : rR ≠ 1 := by
        intro hrR_eq
        apply hrq_ne
        apply Subtype.ext
        calc
          (rq : G ⧸ ρ.ker) = qG r := hrq.symm
          _ = 1 := by
            have hr_eq_one : (r : G) = 1 := congrArg Subtype.val hrR_eq
            simp [qG, hr_eq_one]
      rw [← hrq]
      simpa [Kq, Zq, qG, rR] using
        elementCentralizerIn_map_mk'_eq_map_center_of_solvable_coprime
          K R ρ.ker hRK hsolvK hcopKR hcent_r
          (r := rR) hrR_ne
    have hKq_lt_K : Nat.card Kq < Nat.card K :=
      natCard_map_mk'_lt_of_ne_bot K ρ.ker hker_le_K hker_ne_bot
    have hindq : Theorem34IndHyp.{uG, uF, uV} (F := F) Kq := by
      intro V' _ _ G' _ _ K' R' ρ' hK'_lt hsolvG' hoddG' hK'_normal hK'R' hcopK'R'
        hR'_prime hcharG' hfixR'
      exact
        hind (G' := G') K' R' ρ' (lt_trans hK'_lt hKq_lt_K) hsolvG' hoddG' hK'_normal hK'R'
          hcopK'R' hR'_prime hcharG' hfixR'
    have : Group.IsSolvable G := hsolvG
    have hsolv_qG : Group.IsSolvable (G ⧸ ρ.ker) := by
      infer_instance
    have hKqbot : ρq.centralizerIn Kq = ⊥ := by
      simp [Representation.centralizerIn, hρq_ker]
    have hZKq_top : Subgroup.center (↥Kq) ≠ ⊤ := by
      intro hZKq_top
      let : IsMulCommutative ↥Kq := by
        refine ⟨⟨?_⟩⟩
        intro x y
        have hxcent : x ∈ Subgroup.center (↥Kq) := by simp [hZKq_top]
        exact (Subgroup.mem_center_iff.mp hxcent y).symm
      exact hcommKq inferInstance
    have hRKq : Rq ≤ Subgroup.normalizer Kq := Subgroup.le_normalizer_of_normal (H := Kq)
    have : Subgroup.Normalizes Rq Kq := ⟨hRKq⟩
    have hZfix_q : Subgroup.center (↥Kq) ≤ fixedPointSubgroup (↥Rq) (↥Kq) := by
      intro z hz
      rw [FixedPoints.mem_subgroup]
      intro rq
      apply Subtype.ext
      exact
        proper_characteristic_le_fixedPointSubgroup_local Kq Rq ρq hindq hsolv_qG hodd_qG
          hKq_normal hKRq hcopKqRq hRq_prime hchar_qG hρq.2.2.1 hKqbot
          (Subgroup.center (↥Kq)) inferInstance hZKq_top rq z hz
    have hcommRqZKq :
        ∀ rq : Rq, ∀ z : Subgroup.center (↥Kq),
          (rq : G ⧸ ρ.ker) * (z : G ⧸ ρ.ker) = (z : G ⧸ ρ.ker) * (rq : G ⧸ ρ.ker) := by
      have : Subgroup.Normalizes Rq Kq := ⟨hRKq⟩
      intro rq z
      have hzfix : rq • (z : Kq) = z := by
        exact
          (FixedPoints.mem_subgroup (M := ↥Rq) (a := (z : Kq))).mp (hZfix_q z.property) rq
      have hzconj : (rq : G ⧸ ρ.ker) * (z : G ⧸ ρ.ker) * (rq : G ⧸ ρ.ker)⁻¹ = z := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRKq] using
          congrArg Subtype.val hzfix
      have := congrArg (fun t : G ⧸ ρ.ker => t * (rq : G ⧸ ρ.ker)) hzconj
      simpa [mul_assoc] using this
    have hZKq_central :
        (Subgroup.center (↥Kq)).map Kq.subtype ≤ Subgroup.center (G ⧸ ρ.ker) :=
      center_map_le_center_of_isComplement'_commute Kq Rq hKRq hcommRqZKq
    have hKq_extraspecial : IsExtraspecial q ↥Kq :=
      isExtraspecial_of_commutator_le_center_of_exponent_eq_of_faithful_irreducible_local
        Kq ρq hρq.1 hρq.2.1 hcommKq hcommKq_center hKq_exp hZKq_central
    let : IsExtraspecial q ↥Kq := hKq_extraspecial
    have hqdvdKq : q ∣ Nat.card Kq := by
      obtain ⟨nKq, hnKq_pos, hcardKqq⟩ :=
        (IsPGroup.nontrivial_iff_card (p := q) (G := ↥Kq) (hG := Fact.out)).mp inferInstance
      rw [hcardKqq]
      exact dvd_pow_self q (Nat.ne_of_gt hnKq_pos)
    have hq_odd : Odd q := by
      exact odd_of_card_dvd hodd_qG (dvd_trans hqdvdKq (Subgroup.card_subgroup_dvd_card Kq))
    have hcenterKq_card : Nat.card ((Subgroup.center (↥Kq)).map Kq.subtype) = q := by
      calc
        Nat.card ((Subgroup.center (↥Kq)).map Kq.subtype) = Nat.card (Subgroup.center (↥Kq)) := by
          simpa using
            (Subgroup.card_map_of_injective (K := Subgroup.center (↥Kq))
              (f := Kq.subtype) Kq.subtype_injective)
        _ = q := IsExtraspecial.center_order_p q ↥Kq
    have hZq_eq_centerKq : Zq = (Subgroup.center (↥Kq)).map Kq.subtype := by
      apply Subgroup.eq_of_le_of_card_ge hZq_le_centerKq
      rw [hcenterKq_card, hZq_card]
    have hcent_rq :
        ∀ rq : Rq, rq ≠ 1 →
          elementCentralizerIn Kq (rq : G ⧸ ρ.ker) = (Subgroup.center (↥Kq)).map Kq.subtype := by
      intro rq hrq_ne
      rw [hcent_rq_raw rq hrq_ne, hZq_eq_centerKq]
    obtain ⟨n, hcardKq⟩ :=
      exists_natCard_eq_prime_pow_two_mul_add_one_of_isExtraspecial_local (q := q) (K := ↥Kq)
        hq_odd
    exact
      theorem_3_4_extraspecial_faithful_center_fixedpoints_of_isExtraspecial_card Kq Rq ρq
        hodd_qG hKq_normal hKRq hcopKqRq hRq_prime hρq.2.2.1 hchar_qG hcent_rq hρq.1 hρq.2.1
        hcardKq

set_option backward.isDefEq.respectTransparency false in
theorem CFSG.theorem_3_4_theorem_2_5_replacement {G : Type uG} [Group G] [Finite G]
    {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)]
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hKbot : ρ.centralizerIn K = ⊥) (hcommK : ¬ IsMulCommutative ↥K)
    (hcomm : commutator (↥K) ≤ Subgroup.center (↥K)) (hexp : Monoid.exponent (↥K) = q)
    (hZfix : Subgroup.center (↥K) ≤ fixedPointSubgroup (↥R) (↥K))
    (hcent_r :
      ∀ r : R, r ≠ 1 →
        elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype) :
    ρ.fixedSubspace R ≠ ⊥ := by
  intro hfixR
  let C : Subgroup G := (commutator (↥K)).map K.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_eq_bot
    subst hK_eq_bot
    exact hcommK inferInstance
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  have hcomm_ne_bot : commutator (↥K) ≠ ⊥ := by
    intro hcomm_bot
    apply hcommK
    have hcenter_top : Subgroup.center (↥K) = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (G := ↥K)).mp hcomm_bot
    refine ⟨⟨?_⟩⟩
    intro x y
    have hxcent : x ∈ Subgroup.center (↥K) := by simp [hcenter_top]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  have hC_ne_bot : C ≠ ⊥ := by
    intro hC_bot
    apply hcomm_ne_bot
    exact
      (Subgroup.map_eq_bot_iff_of_injective (H := commutator (↥K))
        (f := K.subtype) K.subtype_injective).mp (by simpa [C] using hC_bot)
  have hC_le_K : C ≤ K := by
    intro c hc
    rcases hc with ⟨x, hx, rfl⟩
    exact x.property
  have hC_nontrivial : ¬ C ≤ ρ.ker := by
    intro hC_le_ker
    have hCbot : Representation.centralizerIn ρ C = ⊥ :=
      centralizerIn_eq_bot_of_le_of_centralizerIn_eq_bot (ρ := ρ) hC_le_K hKbot
    have hC_eq_bot : C = ⊥ := by
      simpa [Representation.centralizerIn, inf_eq_left.mpr hC_le_ker] using hCbot
    exact hC_ne_bot hC_eq_bot
  let : IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := ρ) hchar
  obtain ⟨m, hm_simple, hm_fix, hm_C_nontrivial⟩ :=
    exists_simple_submodule_nontrivial_of_not_le_ker_of_fixedSubspace_eq_bot
      (ρ := ρ) (R := R) (H := C) hfixR hC_nontrivial
  let ρm := (Subrepresentation.ofSubmodule' m).toRepresentation
  have hirr : Representation.IsIrreducible ρm :=
    irreducible_of_ofSubmodule'_simple (ρ := ρ) hm_simple
  exact
    theorem_3_4_extraspecial_faithful_center_fixedpoints K R ρm hind hsolvG hodd hK_normal hKR
      hcopKR hR_prime hm_fix hchar hcommK hcomm hexp hcent_r hirr hm_C_nontrivial

theorem CFSG.theorem_3_4_extraspecial_endpoint {G : Type uG} [Group G] [Finite G]
    {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥K)] (hfixR : ρ.fixedSubspace R = ⊥)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hKbot : ρ.centralizerIn K = ⊥) (hcommK : ¬ IsMulCommutative ↥K)
    (hcomm : commutator (↥K) ≤ Subgroup.center (↥K)) (hexp : Monoid.exponent (↥K) = q)
    (hZfix : Subgroup.center (↥K) ≤ fixedPointSubgroup (↥R) (↥K))
    (hcent_r :
      ∀ r : R, r ≠ 1 →
        elementCentralizerIn K (r : G) = (Subgroup.center (↥K)).map K.subtype) :
    False := by
  exact
    theorem_3_4_theorem_2_5_replacement K R ρ hind hsolvG hodd hK_normal hKR hcopKR hR_prime
      hchar hKbot hcommK hcomm hexp hZfix hcent_r hfixR

theorem CFSG.theorem_3_4_faithful_endpoint {G : Type uG} [Group G] [Finite G] {F : Type uF}
    [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) (hKbot : ρ.centralizerIn K = ⊥) :
    ⁅R, K⁆ ≤ ρ.centralizerIn K := by
  have hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  by_cases htriv : ActsTrivially (A := ↥R) (G := ↥K)
  · have hcomm : ⁅R, K⁆ = ⊥ :=
      commutator_eq_bot_of_actsTrivially_subgroup_conj (K := K) (R := R) hRK htriv
    simpa [hKbot] using hcomm.le
  · have hK_ne_bot : K ≠ ⊥ := by
      intro hK_eq_bot
      apply htriv
      intro r k
      have hk_eq_one : ((k : K) : G) = 1 := by simpa [hK_eq_bot] using k.2
      apply Subtype.ext
      simp [hk_eq_one, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hR_ne_bot : R ≠ ⊥ := by
      intro hR_eq_bot
      exact hR_prime.ne_one ((Subgroup.eq_bot_iff_card (H := R)).1 hR_eq_bot)
    let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
    let : Nontrivial ↥R := R.nontrivial_iff_ne_bot.mpr hR_ne_bot
    have hfaith : FaithfulSMul (↥R) (↥K) :=
      faithfulSMul_of_prime_order_of_not_actsTrivially (A := ↥R) (G := ↥K) hR_prime htriv
    have hproper :
        ∀ H : Subgroup K, H.Characteristic → H ≠ ⊤ → H ≤ fixedPointSubgroup (↥R) (↥K) := by
      intro H hH_char hH_top x hx
      rw [FixedPoints.mem_subgroup]
      intro r
      apply Subtype.ext
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using
        proper_characteristic_le_fixedPointSubgroup_local K R ρ hind hsolvG hodd hK_normal hKR
          hcopKR hR_prime hchar hfixR hKbot H hH_char hH_top r x hx
    have hsolvK : Group.IsSolvable ↥K := by infer_instance
    have hfit_top : fittingSubgroup (↥K) = ⊤ :=
      fittingSubgroup_eq_top_of_proper_characteristic_fixed (K := ↥K) (A := ↥R) hsolvK
        hcopKR.symm hproper
    have hnilK : Group.IsNilpotent ↥K := by
      have : Group.IsNilpotent (fittingSubgroup (↥K)) := by infer_instance
      let e : (fittingSubgroup (↥K)) ≃* (↥K) :=
        (MulEquiv.subgroupCongr hfit_top).trans (Subgroup.topEquiv : (⊤ : Subgroup (↥K)) ≃* (↥K))
      exact Group.nilpotent_of_mulEquiv (G := fittingSubgroup (↥K)) (G' := ↥K) e
    obtain ⟨q, hq_prime, hq_pgroup⟩ :=
      exists_prime_isPGroup_of_nilpotent_of_proper_characteristic_fixed
        (K := ↥K) (A := ↥R) hnilK hproper
    have : Fact q.Prime := ⟨hq_prime⟩
    have : Fact (IsPGroup q ↥K) := ⟨hq_pgroup⟩
    have hKcard_dvd : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
    have hoddK : Odd (Nat.card K) := odd_of_card_dvd hodd hKcard_dvd
    have hqdvdK : q ∣ Nat.card K := by
      obtain ⟨nK, hnK_pos, hcardKq⟩ :=
        (IsPGroup.nontrivial_iff_card (p := q) (G := ↥K) (hG := hq_pgroup)).mp inferInstance
      rw [hcardKq]
      exact dvd_pow_self q (Nat.ne_of_gt hnK_pos)
    have hqodd : q ≠ 2 := Odd.ne_two_of_dvd_nat hoddK hqdvdK
    have hclassTwo_exp :
        commutator (↥K) ≤ Subgroup.center (↥K) ∧ Monoid.exponent (↥K) = q :=
      classTwo_exponent_prime_of_proper_characteristic_fixed (K := ↥K) (A := ↥R) hqodd
        hcopKR.symm hproper
    obtain ⟨hcommK_center, hexpK⟩ := hclassTwo_exp
    by_cases hcommK : IsMulCommutative ↥K
    · let : IsElementaryAbelian q ↥K :=
        { toIsMulCommutative := hcommK
          exponent_dvd_p := by
            simp [hexpK] }
      have hfixfree_of_ne_one :
          ∀ r : R, r ≠ 1 →
            fixedPointSubgroup
              (↥(Subgroup.zpowers (MulDistribMulAction.toMulAut (↥R) (↥K) r))) (↥K) = ⊥ := by
        intro r hr_ne
        let σ : MulAut ↥K := MulDistribMulAction.toMulAut (↥R) (↥K) r
        have hσ_ne : σ ≠ 1 := by
          intro hσ
          apply hr_ne
          apply (faithfulSMul_iff (G := ↥R) (α := ↥K)).1 hfaith r
          intro x
          have hxfix : σ x = x := by simp [σ, hσ]
          simpa [σ] using hxfix
        have hσdvdR : orderOf σ ∣ Nat.card R := by
          exact
            (orderOf_map_dvd (MulDistribMulAction.toMulAut (↥R) (↥K)) r).trans
              (orderOf_dvd_natCard r)
        have hσcopK : Nat.Coprime (orderOf σ) (Nat.card K) :=
          Nat.Coprime.of_dvd_left hσdvdR hcopKR.symm
        have hσcopq : Nat.Coprime (orderOf σ) q :=
          Nat.Coprime.of_dvd_right hqdvdK hσcopK
        have hσpow_top : Subgroup.zpowers r = ⊤ :=
          zpowers_eq_top_of_prime_card_of_ne_one hR_prime hr_ne
        have hproperσ :
            ∀ H : Subgroup K, H ≠ ⊤ → H.map σ.toMonoidHom = H →
              H ≤ fixedPointSubgroup (↥(Subgroup.zpowers σ)) (↥K) := by
          intro H hH_top hHσ
          let : IsMulCommutative ↥K := hcommK
          have hσ_mem : ∀ {x : K}, x ∈ H → σ x ∈ H := by
            intro x hx
            have hx' : σ x ∈ H.map σ.toMonoidHom := ⟨x, hx, rfl⟩
            rw [hHσ] at hx'
            exact hx'
          have hσinv_mem : ∀ {x : K}, x ∈ H → σ⁻¹ x ∈ H := by
            intro x hx
            have hx' : x ∈ H.map σ.toMonoidHom := by
              rw [hHσ]
              exact hx
            rcases hx' with ⟨y, hy, hyx⟩
            have hy_eq : y = σ⁻¹ x := by
              apply σ.injective
              calc
                σ y = x := by simpa using hyx
                _ = σ (σ⁻¹ x) := by simp
            simpa [hy_eq] using hy
          have hσzpow_mem : ∀ n : ℤ, ∀ {x : K}, x ∈ H → (σ ^ n) x ∈ H := by
            have hpow_mem : ∀ n : ℕ, ∀ {x : K}, x ∈ H → (σ ^ n) x ∈ H := by
              intro n
              induction n with
              | zero =>
                  intro x hx
                  simpa
              | succ n ih =>
                  intro x hx
                  have hxσ : σ x ∈ H := hσ_mem hx
                  have hxpow : (σ ^ n) (σ x) ∈ H := ih hxσ
                  simpa [pow_succ] using hxpow
            have hinvpow_mem : ∀ n : ℕ, ∀ {x : K}, x ∈ H → (σ⁻¹ ^ n) x ∈ H := by
              intro n
              induction n with
              | zero =>
                  intro x hx
                  simpa
              | succ n ih =>
                  intro x hx
                  have hxσ : σ⁻¹ x ∈ H := hσinv_mem hx
                  have hxpow : (σ⁻¹ ^ n) (σ⁻¹ x) ∈ H := ih hxσ
                  simpa [pow_succ] using hxpow
            intro n x hx
            cases n with
            | ofNat n =>
                simpa [zpow_ofNat] using hpow_mem n hx
            | negSucc n =>
                simpa [zpow_negSucc] using hinvpow_mem (n + 1) hx
          let H' : Subgroup G := H.map K.subtype
          have hH'_le : H' ≤ K := by
            simpa [H'] using (Subgroup.map_subtype_le H)
          have hH'_ne : H' ≠ K := by
            intro hEq
            apply hH_top
            apply top_unique
            intro x hx
            have hx' : ((x : K) : G) ∈ H' := by simp [H', hEq]
            rcases hx' with ⟨y, hy, hyx⟩
            have hy_eq : y = x := by
              apply Subtype.ext
              simpa using hyx
            simpa [hy_eq] using hy
          have hH'_lt : H' < K := lt_of_le_of_ne hH'_le hH'_ne
          have hRinv : ∀ a : R, ∀ h ∈ H', (a : G) * h * (a : G)⁻¹ ∈ H' := by
            intro a h hh
            rcases hh with ⟨x, hx, rfl⟩
            have ha_zpow : a ∈ Subgroup.zpowers r := by
              simp [hσpow_top]
            rcases Subgroup.mem_zpowers_iff.mp ha_zpow with ⟨n, rfl⟩
            let y : K := (MulDistribMulAction.toMulAut (↥R) (↥K) (r ^ n)) x
            have hy_eq : y = (σ ^ n) x := by
              have hmap_zpow :
                  MulDistribMulAction.toMulAut (↥R) (↥K) (r ^ n) = σ ^ n := by
                simpa [σ] using
                  (map_zpow (MulDistribMulAction.toMulAut (↥R) (↥K)) r n)
              change ((MulDistribMulAction.toMulAut (↥R) (↥K) (r ^ n)) x) = (σ ^ n) x
              rw [hmap_zpow]
            refine ⟨y, hy_eq.symm ▸ hσzpow_mem n hx, ?_⟩
            change ((y : K) : G) = ((r ^ n : R) : G) * ((x : K) : G) * ((r ^ n : R) : G)⁻¹
            simp [y, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          have hH'_normal : H'.Normal := by
            refine ⟨?_⟩
            intro x hx g
            rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨a, haR⟩⟩, hka⟩
            have hax : (a : G) * x * (a : G)⁻¹ ∈ H' := hRinv ⟨a, haR⟩ x hx
            have haxK : (a : G) * x * (a : G)⁻¹ ∈ K := hH'_le hax
            have hk_comm :
                (k : G) * ((a : G) * x * (a : G)⁻¹) =
                  ((a : G) * x * (a : G)⁻¹) * (k : G) := by
              exact congrArg Subtype.val
                ((IsMulCommutative.is_comm (M := K)).comm ⟨k, hkK⟩
                  ⟨(a : G) * x * (a : G)⁻¹, haxK⟩)
            have hconj_eq : g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹ := by
              have hka' : (k : G) * (a : G) = g := by simpa using hka
              calc
                g * x * g⁻¹ = ((k : G) * (a : G)) * x * (((k : G) * (a : G))⁻¹) := by
                  rw [hka']
                _ = (k : G) * ((a : G) * x * (a : G)⁻¹) * (k : G)⁻¹ := by
                  simp [mul_assoc]
                _ = ((a : G) * x * (a : G)⁻¹) * ((k : G) * (k : G)⁻¹) := by
                  rw [hk_comm]
                  simp [mul_assoc]
                _ = (a : G) * x * (a : G)⁻¹ := by simp [mul_assoc]
            rw [hconj_eq]
            exact hax
          have hfixH :
              ∀ a : R, ∀ x : K, x ∈ H → (a : G) * (x : G) * (a : G)⁻¹ = x := by
            intro a x hx
            simpa using
              proper_normal_fixed_local K R ρ hind hsolvG hodd hKR hcopKR hR_prime hchar hfixR
                hKbot H' hH'_lt hH'_normal hRinv a ((x : K) : G)
                (Subgroup.mem_map_of_mem K.subtype hx)
          intro x hx
          rw [FixedPoints.mem_subgroup]
          intro τ
          rcases τ.property with ⟨n, hn⟩
          have hfix_r : ((r : R) : G) * ((x : K) : G) * ((r : R) : G)⁻¹ = x := hfixH r x hx
          have hxfixσ : σ x = x := by
            apply Subtype.ext
            simpa [σ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hfix_r
          have hxfixσpow :
              ∀ n : ℤ, (σ ^ n) x = x := by
            intro n
            have hxfix : x ∈ MulAction.fixedBy (↥K) σ := by
              simpa [MulAction.mem_fixedBy] using hxfixσ
            simpa [MulAction.mem_fixedBy] using
              (MulAction.mem_fixedBy_zpow (α := ↥K) (g := σ) (a := x) hxfix n)
          have hτ : (τ : MulAut ↥K) = σ ^ n := by simpa using hn.symm
          have hfixτ : (τ : MulAut ↥K) x = x := by simpa [hτ] using hxfixσpow n
          change (τ : MulAut ↥K) x = x
          exact hfixτ
        exact
          fixedPointSubgroup_zpowers_eq_bot_of_elementaryAbelian_of_proper_invariant_fixed
            (σ := σ) hσ_ne hσcopq hproperσ
      have hcent : ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ := by
        intro x hx
        let σ : MulAut ↥K := MulDistribMulAction.toMulAut (↥R) (↥K) x
        have hfixσ : fixedPointSubgroup (↥(Subgroup.zpowers σ)) (↥K) = ⊥ :=
          hfixfree_of_ne_one x hx
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        rcases hy with ⟨hyK, hycent⟩
        let yK : K := ⟨y, hyK⟩
        have hyfixσ : σ yK = yK := by
          have hycomm : (x : G) * y = y * (x : G) := by
            exact (Subgroup.mem_centralizer_singleton_iff.mp hycent).symm
          have hyconj : (x : G) * y * (x : G)⁻¹ = y := by
            calc
              (x : G) * y * (x : G)⁻¹ = (y * (x : G)) * (x : G)⁻¹ := by rw [hycomm]
              _ = y := by simp [mul_assoc]
          apply Subtype.ext
          simpa [σ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hyconj
        have hyfix : yK ∈ fixedPointSubgroup (↥(Subgroup.zpowers σ)) (↥K) := by
          rw [FixedPoints.mem_subgroup]
          intro τ
          rcases τ.property with ⟨n, hn⟩
          have hyσ : yK ∈ MulAction.fixedBy (↥K) σ := by
            simpa [MulAction.mem_fixedBy] using hyfixσ
          have hyσpow : yK ∈ MulAction.fixedBy (↥K) (σ ^ n) :=
            MulAction.mem_fixedBy_zpow (α := ↥K) (g := σ) (a := yK) hyσ n
          have hτ : (τ : MulAut ↥K) = σ ^ n := by simpa using hn.symm
          have hfixτ : (τ : MulAut ↥K) yK = yK := by
            simpa [MulAction.mem_fixedBy, hτ] using hyσpow
          change (τ : MulAut ↥K) yK = yK
          exact hfixτ
        have hybot : yK ∈ (⊥ : Subgroup K) := by simpa [hfixσ] using hyfix
        have hyone : yK = 1 := by simpa using hybot
        exact congrArg Subtype.val hyone
      have hfrob : IsFrobeniusGroupWithKernelComplement K R :=
        (lemma_3_1 (K := K) (R := R) hK_ne_bot hR_ne_bot hK_normal hKR).2 hcent
      have hK_nontrivial : ¬ K ≤ ρ.ker := by
        intro hKker
        exact hK_ne_bot (by
          simpa [Representation.centralizerIn, inf_eq_left.mpr hKker] using hKbot)
      exact False.elim <|
        lemma_3_3 K R ρ hfrob (hchar_of_card_dvd (G := G) (F := F) hchar hKcard_dvd)
          hK_nontrivial hfixR
    · have hnontrivAction : ∃ a : R, ∃ x : K, (a : G) * (x : G) * (a : G)⁻¹ ≠ x := by
        by_contra hcontra
        push Not at hcontra
        apply htriv
        intro a x
        apply Subtype.ext
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hcontra a x
      obtain ⟨E, hEchar, hEcomm, hEmax⟩ :=
        exists_maximal_characteristic_abelian_subgroup_local (G := ↥K)
      by_cases hcentE : Subgroup.centralizer (E : Set ↥K) = ⊤
      · let Z : Subgroup ↥K := Subgroup.center (↥K)
        have hE_le_Z : E ≤ Z := by
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro y
          have hycent : y ∈ Subgroup.centralizer (E : Set ↥K) := by
            simp [hcentE]
          exact ((Subgroup.mem_centralizer_iff.mp hycent) x hx).symm
        have hZ_eq_E : Z = E := hEmax Z inferInstance inferInstance hE_le_Z
        have hZfix :
            Z ≤ fixedPointSubgroup (↥R) (↥K) := by
          have hZ_top : Z ≠ ⊤ := by
            intro hZ
            apply hcommK
            refine ⟨⟨?_⟩⟩
            intro x y
            have hxcent : x ∈ Z := by simp [Z, hZ]
            exact (Subgroup.mem_center_iff.mp hxcent y).symm
          exact hproper Z inferInstance hZ_top
        have hcent_r :
            ∀ r : R, r ≠ 1 →
              elementCentralizerIn K (r : G) = (Z.map K.subtype) := by
          simpa [Z] using
            theorem_3_4_quotient_center_fixfree_local K R ρ hind hsolvG hodd hK_normal hKR
              hcopKR hR_prime hchar hfixR hKbot hqdvdK hnontrivAction hcommK hcommK_center
              hexpK
        have hE_eq_Z : E = Z := hZ_eq_E.symm
        let _ := hE_eq_Z
        exact False.elim <|
          theorem_3_4_extraspecial_endpoint K R ρ hind hsolvG hodd hK_normal hKR hcopKR hR_prime
            hfixR hchar hKbot hcommK hcommK_center hexpK hZfix hcent_r
      · have htrivK : ActsTrivially (A := ↥R) (G := ↥K) :=
          actsTrivially_of_proper_centralizer_maximal_characteristic_abelian_local
            (K := ↥K) (A := ↥R) hqodd hcopKR.symm hexpK E hEchar hEcomm hproper hcentE
        exact False.elim (htriv htrivK)

theorem CFSG.theorem_3_4_by_card {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V] :
    ∀ (G : Type uG) [Group G] [Finite G] (K R : Subgroup G) (ρ : Representation F G V),
      Group.IsSolvable G →
      Odd (Nat.card G) →
      K.Normal →
      K.IsComplement' R →
      Nat.Coprime (Nat.card K) (Nat.card R) →
      Nat.Prime (Nat.card R) →
      (ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) →
      ρ.fixedSubspace R = ⊥ →
      ⁅R, K⁆ ≤ ρ.centralizerIn K := by
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type uV) [AddCommGroup W] [Module F W]
      (G : Type uG) [Group G] [Finite G] (K R : Subgroup G) (ρ : Representation F G W),
      Nat.card K = n →
      Group.IsSolvable G →
      Odd (Nat.card G) →
      K.Normal →
      K.IsComplement' R →
      Nat.Coprime (Nat.card K) (Nat.card R) →
      Nat.Prime (Nat.card R) →
      (ringChar F = 0 ∨
        (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) →
      ρ.fixedSubspace R = ⊥ →
      ⁅R, K⁆ ≤ ρ.centralizerIn K
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih W _ _ G _ _ K R ρ hcard hsolvG hodd hK_normal hKR hcopKR hR_prime hchar hfixR
    have hind : Theorem34IndHyp.{uG, uF, uV} (F := F) K := by
      intro W' _ _ G' _ _ K' R' ρ' hlt hsolvG' hodd' hK'_normal hK'R' hcopK'R' hR'_prime
        hchar' hfixR'
      have hlt' : Nat.card K' < n := by simpa [hcard] using hlt
      exact
        ih (Nat.card K') hlt' W' G' K' R' ρ' rfl hsolvG' hodd' hK'_normal hK'R'
          hcopK'R' hR'_prime hchar' hfixR'
    by_cases hKbot : ρ.centralizerIn K = ⊥
    · exact
        theorem_3_4_faithful_endpoint K R ρ hind hsolvG hodd hK_normal hKR hcopKR hR_prime
          hchar hfixR hKbot
    · exact
        theorem_3_4_quotient_step K R ρ hind hsolvG hodd hK_normal hKR hcopKR hR_prime hchar
          hfixR hKbot
  intro G _ _ K R ρ hsolvG hodd hK_normal hKR hcopKR hR_prime hchar hfixR
  exact hP (Nat.card K) V G K R ρ rfl hsolvG hodd hK_normal hKR hcopKR hR_prime hchar hfixR

public theorem CFSG.theorem_3_4 {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F]
    {V : Type uV}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : ρ.fixedSubspace R = ⊥) :
    ⁅R, K⁆ ≤ ρ.centralizerIn K := by
  exact theorem_3_4_by_card G K R ρ hsolvG hodd hK_normal hKR hcopKR hR_prime hchar hfixR

public theorem CFSG.exists_inner_of_fix_center_and_quotient_of_isExtraspecial_local
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    (α : MulAut K)
    (hαZ : ∀ z : Subgroup.center K, α z = z)
    (hαQ : ∀ x : K, (QuotientGroup.mk (α x) : K ⧸ Subgroup.center K) = QuotientGroup.mk x) :
    ∃ s : K, ∀ x : K, α x = s * x * s⁻¹ := by
  let Qmul := K ⧸ Subgroup.center K
  let : IsElementaryAbelian q Qmul := IsExtraspecial.quotient_elementary_abelian q K
  let : IsMulCommutative Qmul := (inferInstance : IsElementaryAbelian q Qmul).toIsMulCommutative
  let : CommGroup Qmul := IsMulCommutative.instCommGroup
  let Q := Additive Qmul
  let : AddCommGroup Q := Additive.addCommGroup
  let : Module (ZMod q) Q := inferInstance
  let : Finite Q := inferInstance
  let : FiniteDimensional (ZMod q) Q := Module.Finite.of_finite
  let cRaw : K → ZMod q := fun x =>
    centerAddEquivZMod_local (q := q) (K := K)
      (Additive.ofMul
        ⟨x⁻¹ * α x, QuotientGroup.eq.mp (hαQ x).symm⟩)
  have hcRaw_mul_center :
      ∀ x z : K, z ∈ Subgroup.center K → cRaw (x * z) = cRaw x := by
    intro x z hz
    have hxZ : x⁻¹ * α x ∈ Subgroup.center K := QuotientGroup.eq.mp (hαQ x).symm
    have hzfix : α z = z := hαZ ⟨z, hz⟩
    let e := centerAddEquivZMod_local (q := q) (K := K)
    change e _ = e _
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    calc
      (x * z)⁻¹ * α (x * z)
          = z⁻¹ * x⁻¹ * (α x * α z) := by
              simp [map_mul, mul_assoc]
      _ = z⁻¹ * (x⁻¹ * α x) * z := by
              simp [hzfix, mul_assoc]
      _ = (x⁻¹ * α x) * z⁻¹ * z := by
              rw [((Subgroup.mem_center_iff.mp hxZ) z⁻¹).symm, mul_assoc]
      _ = x⁻¹ * α x := by simp
  have hcRaw_mul :
      ∀ x y : K, cRaw (x * y) = cRaw x + cRaw y := by
    intro x y
    have hxZ : x⁻¹ * α x ∈ Subgroup.center K := QuotientGroup.eq.mp (hαQ x).symm
    have hyZ : y⁻¹ * α y ∈ Subgroup.center K := QuotientGroup.eq.mp (hαQ y).symm
    let e := centerAddEquivZMod_local (q := q) (K := K)
    change e _ = e _ + e _
    rw [← e.map_add]
    congr 1
    ext
    calc
      (x * y)⁻¹ * α (x * y)
          = y⁻¹ * x⁻¹ * (α x * α y) := by
              simp [map_mul, mul_assoc]
      _ = y⁻¹ * (x⁻¹ * α x) * α y := by
              simp [mul_assoc]
      _ = (x⁻¹ * α x) * y⁻¹ * α y := by
              calc
                y⁻¹ * (x⁻¹ * α x) * α y = ((y⁻¹ * (x⁻¹ * α x)) * α y) := by
                    simp [mul_assoc]
                _ = (((x⁻¹ * α x) * y⁻¹) * α y) := by
                    rw [((Subgroup.mem_center_iff.mp hxZ) y⁻¹).symm]
                _ = (x⁻¹ * α x) * y⁻¹ * α y := by
                    simp [mul_assoc]
      _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by
              simp [mul_assoc]
      _ = (x⁻¹ * α x) * (y⁻¹ * α y) := rfl
  let c : Q →+ ZMod q :=
    { toFun := fun a =>
        Quotient.liftOn (Additive.toMul a) cRaw (by
          intro x y hxy
          have hxyq : (x : K ⧸ Subgroup.center K) = y := Quotient.sound hxy
          have hz : x⁻¹ * y ∈ Subgroup.center K := QuotientGroup.eq.mp hxyq
          calc
            cRaw x = cRaw (x * (x⁻¹ * y)) := by
              symm
              exact hcRaw_mul_center x (x⁻¹ * y) hz
            _ = cRaw y := by simp)
      map_zero' := by
        change cRaw 1 = 0
        simp [cRaw]
      map_add' := by
        intro a b
        rw [← ofMul_toMul a, ← ofMul_toMul b]
        refine Quotient.inductionOn₂ (Additive.toMul a) (Additive.toMul b) ?_
        intro x y
        change cRaw (x * y) = cRaw x + cRaw y
        exact hcRaw_mul x y }
  let f : Module.Dual (ZMod q) Q := c.toZModLinearMap q
  have hpair_zero_right :
      ∀ x : Q, extraspecialCenterPairing (q := q) (K := K) x 0 = 0 := by
    intro x
    rw [← ofMul_toMul x]
    refine Quotient.inductionOn (Additive.toMul x) ?_
    intro x
    have hraw : extraspecialCenterPairingRaw (q := q) (K := K) x (1 : K) = 0 := by
      simp [extraspecialCenterPairingRaw]
    change extraspecialCenterPairingRaw (q := q) (K := K) x 1 = 0
    exact hraw
  have hpair_add_right :
      ∀ x y₁ y₂ : Q,
        extraspecialCenterPairing (q := q) (K := K) x (y₁ + y₂) =
          extraspecialCenterPairing (q := q) (K := K) x y₁ +
            extraspecialCenterPairing (q := q) (K := K) x y₂ := by
    intro x y₁ y₂
    rw [← ofMul_toMul x, ← ofMul_toMul y₁, ← ofMul_toMul y₂]
    refine Quotient.inductionOn₃ (Additive.toMul x) (Additive.toMul y₁) (Additive.toMul y₂) ?_
    intro x y₁ y₂
    change extraspecialCenterPairingRaw (q := q) (K := K) x (y₁ * y₂) =
      extraspecialCenterPairingRaw (q := q) (K := K) x y₁ +
        extraspecialCenterPairingRaw (q := q) (K := K) x y₂
    exact extraspecialCenterPairingRaw_mul_right (q := q) (K := K) x y₁ y₂
  have hpair_zero_left :
      ∀ y : Q, extraspecialCenterPairing (q := q) (K := K) 0 y = 0 := by
    intro y
    rw [← ofMul_toMul y]
    refine Quotient.inductionOn (Additive.toMul y) ?_
    intro y
    have hraw : extraspecialCenterPairingRaw (q := q) (K := K) (1 : K) y = 0 := by
      simp [extraspecialCenterPairingRaw]
    change extraspecialCenterPairingRaw (q := q) (K := K) 1 y = 0
    exact hraw
  have hpair_add_left :
      ∀ x₁ x₂ y : Q,
        extraspecialCenterPairing (q := q) (K := K) (x₁ + x₂) y =
          extraspecialCenterPairing (q := q) (K := K) x₁ y +
            extraspecialCenterPairing (q := q) (K := K) x₂ y := by
    intro x₁ x₂ y
    rw [← ofMul_toMul x₁, ← ofMul_toMul x₂, ← ofMul_toMul y]
    refine Quotient.inductionOn₃ (Additive.toMul x₁) (Additive.toMul x₂) (Additive.toMul y) ?_
    intro x₁ x₂ y
    change extraspecialCenterPairingRaw (q := q) (K := K) (x₁ * x₂) y =
      extraspecialCenterPairingRaw (q := q) (K := K) x₁ y +
        extraspecialCenterPairingRaw (q := q) (K := K) x₂ y
    exact extraspecialCenterPairingRaw_mul_left (q := q) (K := K) x₁ x₂ y
  let pairingAdd : Q →+ AddMonoidHom Q (ZMod q) :=
    { toFun := fun x =>
        { toFun := fun y => extraspecialCenterPairing (q := q) (K := K) x y
          map_zero' := hpair_zero_right x
          map_add' := hpair_add_right x }
      map_zero' := by
        apply AddMonoidHom.ext
        intro y
        exact hpair_zero_left y
      map_add' := by
        intro x₁ x₂
        apply AddMonoidHom.ext
        intro y
        exact hpair_add_left x₁ x₂ y }
  let B : LinearMap.BilinForm (ZMod q) Q :=
    { toFun := fun x => (pairingAdd x).toZModLinearMap q
      map_add' := by
        intro x₁ x₂
        ext y
        simp
      map_smul' := by
        intro c x
        ext y
        simpa using DFunLike.congr_fun (ZMod.map_smul pairingAdd c x) y }
  have hB_mk (x y : K) :
      B (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
        extraspecialCenterPairingRaw (q := q) (K := K) x y := by
    rfl
  have hSep : B.SeparatingLeft := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial]
    intro x hx
    rw [← ofMul_toMul x] at hx ⊢
    revert hx
    refine Quotient.inductionOn (Additive.toMul x) ?_
    intro x hx
    change B (Additive.ofMul (QuotientGroup.mk x)) = 0 at hx
    have hcent : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy :
          B (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) = 0 := by
        simpa using DFunLike.congr_fun hx (Additive.ofMul (QuotientGroup.mk y))
      rw [hB_mk] at hy
      have hy' :
          (Additive.ofMul
            ⟨⁅x, y⁆,
              commutatorElement_mem_center_of_commutator_le_center_local
                (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) x y⟩ :
            Additive (Subgroup.center K)) = 0 := by
        apply (centerAddEquivZMod_local (q := q) (K := K)).injective
        simpa [extraspecialCenterPairingRaw] using hy
      have hxy : ⁅x, y⁆ = 1 := by
        simpa using congrArg Additive.toMul hy'
      exact (commutatorElement_eq_one_iff_mul_comm.mp hxy).symm
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center K) x).2 hcent
  have hNondeg : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hSep
  let sbar : Q := (B.toDual hNondeg).symm f
  obtain ⟨s, hsbar⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center K) (Additive.toMul sbar)
  refine ⟨s, ?_⟩
  intro x
  have hsbar_eq : sbar = Additive.ofMul (QuotientGroup.mk s) := by
    apply Additive.toMul.injective
    simpa using hsbar.symm
  have hdual :
      B sbar (Additive.ofMul (QuotientGroup.mk x)) =
        f (Additive.ofMul (QuotientGroup.mk x)) :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hNondeg) f (Additive.ofMul (QuotientGroup.mk x))
  have hcomm_eq :
      (Additive.ofMul
        ⟨x⁻¹ * α x, QuotientGroup.eq.mp (hαQ x).symm⟩ :
          Additive (Subgroup.center K)) =
        Additive.ofMul
          ⟨⁅s, x⁆,
            commutatorElement_mem_center_of_commutator_le_center_local
              (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) s x⟩ := by
    apply (centerAddEquivZMod_local (q := q) (K := K)).injective
    simpa [f, c, cRaw, hsbar_eq, hB_mk, extraspecialCenterPairingRaw] using hdual.symm
  have hdelta : x⁻¹ * α x = ⁅s, x⁆ := by
    simpa using congrArg Additive.toMul hcomm_eq
  have hsx_center : ⁅s, x⁆ ∈ Subgroup.center K :=
    commutatorElement_mem_center_of_commutator_le_center_local
      (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) s x
  calc
    α x = x * (x⁻¹ * α x) := by group
    _ = x * ⁅s, x⁆ := by rw [hdelta]
    _ = ⁅s, x⁆ * x := by rw [((Subgroup.mem_center_iff.mp hsx_center) x).symm]
    _ = s * x * s⁻¹ := by simp [commutatorElement_def, mul_assoc]
