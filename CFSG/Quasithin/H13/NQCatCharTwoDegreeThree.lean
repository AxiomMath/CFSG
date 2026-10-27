module

public import CFSG.Quasithin.H13.NQCatUnitaryThree
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Quasithin
open scoped Matrix

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (Q ⧸ center Q) := (QuotientGroup.mk'_surjective (center Q)).subsingleton
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable Q

theorem isQuasisimple_quotient_pCore_of_ker {L G' : Type*} [Group L] [Group G'] [Finite L]
    (ρ : L →* G') (hker : IsPGroup 2 ρ.ker) (hJ : CFSG.IsQuasisimple ρ.range) :
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : (CFSG.pCore 2 L).Normal := CFSG.pCore_normal
  have hOp : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hkerO : ρ.ker ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, hker⟩
  have hρs : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have : Finite ρ.range := Finite.of_surjective _ hρs
  have hO'n : ((CFSG.pCore 2 L).map ρ.rangeRestrict).Normal := hOn.map _ hρs
  have hO'p : IsPGroup 2 ((CFSG.pCore 2 L).map ρ.rangeRestrict) := hOp.map _
  have hO'c : (CFSG.pCore 2 L).map ρ.rangeRestrict ≤ center ρ.range := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hO'n with htop | hc
    · exfalso
      apply not_isSolvable_of_isQuasisimple hJ
      have h2 : IsPGroup 2 (⊤ : Subgroup ρ.range) := htop ▸ hO'p
      have h3 : IsPGroup 2 ρ.range := h2.of_equiv Subgroup.topEquiv
      have := h3.isNilpotent
      infer_instance
    · exact hc
  have hquot := (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hJ hO'c).1
  let φ : L →* ρ.range ⧸ (CFSG.pCore 2 L).map ρ.rangeRestrict :=
    (QuotientGroup.mk' _).comp ρ.rangeRestrict
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hρs
  have hφker : φ.ker = CFSG.pCore 2 L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : ρ y = ρ x := congrArg Subtype.val hyx
      have h1 : y⁻¹ * x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx', inv_mul_cancel]
      have h2 := mul_mem hy (hkerO h1)
      rwa [mul_inv_cancel_left] at h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  have e : L ⧸ CFSG.pCore 2 L ≃* ρ.range ⧸ (CFSG.pCore 2 L).map ρ.rangeRestrict :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hquot

theorem isQuasisimple_quotient_pCore_of_mulEquiv {B L : Type*} [Group B] [Group L] (e : B ≃* L)
    (h : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    CFSG.IsQuasisimple (B ⧸ CFSG.pCore 2 B) := by
  have : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  have : (CFSG.pCore 2 L).Normal := CFSG.pCore_normal
  have e' : B ⧸ CFSG.pCore 2 B ≃* L ⧸ CFSG.pCore 2 L :=
    QuotientGroup.congr _ _ e (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e)
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e').2 h

theorem mul_self_eq_one_of_flag {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] {W : Submodule k V} {g : LinearMap.GeneralLinearGroup k V}
    (h1 : ∀ v, (g : V →ₗ[k] V) v - v ∈ W) (h2 : ∀ w ∈ W, (g : V →ₗ[k] V) w = w) :
    g * g = 1 := by
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  rw [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
  have hv : (g : V →ₗ[k] V) v = v + ((g : V →ₗ[k] V) v - v) := by abel
  calc (g : V →ₗ[k] V) ((g : V →ₗ[k] V) v) = (g : V →ₗ[k] V) (v + ((g : V →ₗ[k] V) v - v)) := by
        rw [← hv]
    _ = (g : V →ₗ[k] V) v + ((g : V →ₗ[k] V) v - v) := by rw [map_add, h2 _ (h1 v)]
    _ = v + (((g : V →ₗ[k] V) v - v) + ((g : V →ₗ[k] V) v - v)) := by abel
    _ = v := by rw [← two_smul k, CharTwo.two_eq_zero, zero_smul, add_zero]

theorem isPGroup_two_of_mul_self {G : Type*} [Group G] {K : Subgroup G}
    (h : ∀ x ∈ K, x * x = 1) : IsPGroup 2 K := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]; exact h x x.2)⟩

theorem quasisimple_quotient_of_two_dim_rep {k : Type*} [Field k] [Finite k] [CharP k 2]
    {M : Type*} [Group M] [Finite M] {Q : Type*} [AddCommGroup Q] [Module k Q]
    [FiniteDimensional k Q] (hQ : finrank k Q = 2) (ρ : M →* LinearMap.GeneralLinearGroup k Q)
    (hker : IsPGroup 2 ρ.ker) (hM : (⊤ : Subgroup M) ∈ cComp (⊤ : Subgroup M)) :
    CFSG.IsQuasisimple (M ⧸ CFSG.pCore 2 M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (LinearMap.GeneralLinearGroup k Q) := LocDbl.finite_GL
  have hsolv : Group.IsSolvable ρ.ker := by
    have := hker.isNilpotent
    infer_instance
  have hJ := LocDbl.map_mem_cComp_of_ker ρ hsolv hM
  rw [← MonoidHom.range_eq_map] at hJ
  have hq := (LocDbl.cComp_quasisimple_and_subsingleton_of_finrank_two (p := 2) hQ
    ρ.range).1 ρ.range hJ
  exact isQuasisimple_quotient_pCore_of_ker ρ hker hq

theorem flag_conclusions {k V : Type*} [Field k] [Finite k] [CharP k 2] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (hV : finrank k V = 3)
    {L : Subgroup (LinearMap.GeneralLinearGroup k V)} (hLperf : ⁅L, L⁆ = L)
    {W : Submodule k V} (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hLW : ∀ g ∈ L, ∀ w ∈ W, (g : V →ₗ[k] V) w ∈ W) :
    (∀ x ∈ L, ∀ c : k, (x : V →ₗ[k] V) = c • LinearMap.id → x = 1) ∧
      (L ∈ cComp L → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (LinearMap.GeneralLinearGroup k V) := LocDbl.finite_GL
  have hd1 : 1 ≤ finrank k W := Submodule.one_le_finrank_iff.mpr hW0
  have hd2 : finrank k W < 3 := hV ▸ Submodule.finrank_lt hWtop
  have hbot : ∀ g ∈ L, ∀ a ∈ (⊥ : Submodule k V), (g : V →ₗ[k] V) a ∈ (⊥ : Submodule k V) :=
    fun g _ a ha => by
      rw [Submodule.mem_bot] at ha ⊢
      rw [ha, map_zero]
  have hcomp : L ∈ cComp L → (⊤ : Subgroup ↥L) ∈ cComp (⊤ : Subgroup ↥L) := fun hL => by
    have h := subgroupOf_mem_cComp hL
    rwa [Subgroup.subgroupOf_self] at h
  rcases (by omega : finrank k W = 1 ∨ finrank k W = 2) with h1 | h2
  ·
    have htrivW : ∀ g ∈ L, ∀ w ∈ W, (g : V →ₗ[k] V) w = w := by
      intro g hg w hw
      have := LocDbl.sub_mem_of_finrank_succ hLperf (bot_le : (⊥ : Submodule k V) ≤ W)
        (by rw [finrank_bot, h1]) hLW hbot hg hw
      rwa [Submodule.mem_bot, sub_eq_zero] at this
    refine ⟨fun x hx c hc => ?_, fun hL => ?_⟩
    · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      have h := htrivW x hx w hw
      rw [hc, LinearMap.smul_apply, LinearMap.id_apply] at h
      have hc1 : c = 1 := by
        have h' : (c - 1) • w = 0 := by rw [sub_smul, one_smul, h, sub_self]
        rcases smul_eq_zero.mp h' with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hw0
      apply Units.ext
      rw [hc, hc1, one_smul, Units.val_one]
      rfl
    · set ρ := (CFSG.LinearAlgebra.SteinbergBQ.segRep L (A := W) (B := ⊤)
        (fun _ _ _ _ => Submodule.mem_top) hLW).toHomUnits with hρ
      have hQ : finrank k (↥(⊤ : Submodule k V) ⧸ W.comap (⊤ : Submodule k V).subtype) = 2 := by
        have h := Submodule.finrank_quotient_add_finrank (W.comap (⊤ : Submodule k V).subtype)
        rw [(Submodule.comapSubtypeEquivOfLe (le_top : W ≤ ⊤)).finrank_eq, finrank_top, hV,
          h1] at h
        omega
      refine quasisimple_quotient_of_two_dim_rep hQ ρ
        (isPGroup_two_of_mul_self fun x hx => ?_) (hcomp hL)
      have hx' : CFSG.LinearAlgebra.SteinbergBQ.segRep L (A := W) (B := ⊤)
          (fun _ _ _ _ => Submodule.mem_top) hLW x = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
        rwa [hρ, MonoidHom.coe_toHomUnits, Units.val_one] at this
      have hsub : ∀ v, ((x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v - v ∈ W := by
        intro v
        have := LinearMap.congr_fun hx' (Submodule.Quotient.mk ⟨v, Submodule.mem_top⟩)
        rw [CFSG.LinearAlgebra.SteinbergBQ.segRep_mk, Module.End.one_apply,
          Submodule.Quotient.eq] at this
        exact this
      have hsq := mul_self_eq_one_of_flag hsub (htrivW x x.2)
      exact Subtype.ext hsq
  ·
    have htrivQ : ∀ g ∈ L, ∀ v, (g : V →ₗ[k] V) v - v ∈ W := fun g hg v =>
      LocDbl.sub_mem_of_finrank_succ hLperf (le_top : W ≤ ⊤) (by rw [finrank_top, hV, h2])
        (fun _ _ _ _ => Submodule.mem_top) hLW hg Submodule.mem_top
    refine ⟨fun x hx c hc => ?_, fun hL => ?_⟩
    · obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
        by_contra hall
        exact hWtop (eq_top_iff.mpr fun v _ => by
          by_contra hv
          exact hall ⟨v, hv⟩)
      have h := htrivQ x hx v
      rw [hc, LinearMap.smul_apply, LinearMap.id_apply] at h
      have hc1 : c = 1 := by
        by_contra hne
        apply hv
        have h' : (c - 1) • v ∈ W := by rwa [sub_smul, one_smul]
        have h'' := W.smul_mem (c - 1)⁻¹ h'
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at h''
      apply Units.ext
      rw [hc, hc1, one_smul, Units.val_one]
      rfl
    · set ρ := (CFSG.LinearAlgebra.SteinbergBQ.segRep L (A := ⊥) (B := W) hLW hbot).toHomUnits
        with hρ
      have hQ : finrank k (↥W ⧸ (⊥ : Submodule k V).comap W.subtype) = 2 := by
        have h := Submodule.finrank_quotient_add_finrank ((⊥ : Submodule k V).comap W.subtype)
        rw [(Submodule.comapSubtypeEquivOfLe (bot_le : (⊥ : Submodule k V) ≤ W)).finrank_eq,
          finrank_bot, h2] at h
        omega
      refine quasisimple_quotient_of_two_dim_rep hQ ρ
        (isPGroup_two_of_mul_self fun x hx => ?_) (hcomp hL)
      have hx' : CFSG.LinearAlgebra.SteinbergBQ.segRep L (A := ⊥) (B := W) hLW hbot x = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
        rwa [hρ, MonoidHom.coe_toHomUnits, Units.val_one] at this
      have hfix : ∀ w ∈ W, ((x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w = w := by
        intro w hw
        have := LinearMap.congr_fun hx' (Submodule.Quotient.mk ⟨w, hw⟩)
        rw [CFSG.LinearAlgebra.SteinbergBQ.segRep_mk, Module.End.one_apply,
          Submodule.Quotient.eq] at this
        have h0 : ((x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w - w ∈
            (⊥ : Submodule k V) := this
        rwa [Submodule.mem_bot, sub_eq_zero] at h0
      have hsq := mul_self_eq_one_of_flag (htrivQ x x.2) hfix
      exact Subtype.ext hsq

theorem commutator_pCore_eq_bot_of_scalar_quotient {k : Type*} [Field k] [Finite k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {Γ : Subgroup (GL (Fin 3) k)} (D : Subgroup Γ) [D.Normal]
    (hD : ∀ d ∈ D, ∃ c : kˣ, (d : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B] (β : B →* Γ ⧸ D)
    (hβ : Function.Injective β) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    ⁅(⊤ : Subgroup B), CFSG.pCore ℓ B⁆ = ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hB' : ⁅β.range, β.range⁆ = β.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hNB : (CFSG.pCore ℓ B).map β ≤ β.range := by
    rw [MonoidHom.range_eq_map]
    exact map_mono le_top
  have : (CFSG.pCore ℓ B).Normal := CFSG.pCore_normal
  have hNn := map_subgroupOf_range_normal β (CFSG.pCore ℓ B)
  have hNp : IsPGroup ℓ ((CFSG.pCore ℓ B).map β) := CFSG.pCore_isPGroup.map β
  have hc := degree_three_scalar_quotient_normal_coprime_prime_subgroup_central D hD hB' hNB hNn
    hℓ hℓp hNp
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : (⟨β y, ⟨y, rfl⟩⟩ : β.range) ∈ center β.range :=
    hc (mem_subgroupOf.mpr ⟨y, hy, rfl⟩)
  have h1 := Subgroup.mem_center_iff.mp hy' ⟨β b, ⟨b, rfl⟩⟩
  apply hβ
  rw [map_mul, map_mul]
  exact (congrArg Subtype.val h1).symm

theorem char_two_degree_three_scalar_quotient_Ccomponents_quasisimple_two_core_quotient
    {k : Type*} [Field k] [Finite k] [CharP k 2] {Γ : Subgroup (GL (Fin 3) k)}
    (D : Subgroup Γ) [D.Normal]
    (hD : ∀ d ∈ D, ∃ c : kˣ, (d : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    {G : Type*} [Group G] [Finite G] {B : Subgroup G} (hB : B ∈ cComp B)
    (β : ↥B →* Γ ⧸ D) (hβ : Function.Injective β) :
    CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GL (Fin 3) k) := Finite.of_injective _ Units.val_injective
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hBperf
  by_cases hq : CFSG.IsQuasisimple ↥B
  ·
    have hOn : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hOn with htop | hc
    · exfalso
      apply not_isSolvable_of_mem_cComp hB
      have h2 : IsPGroup 2 (⊤ : Subgroup ↥B) := htop ▸ CFSG.pCore_isPGroup
      have h3 : IsPGroup 2 ↥B := h2.of_equiv Subgroup.topEquiv
      have := h3.isNilpotent
      infer_instance
    · exact (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hq hc).1
  have hO2 : CFSG.pCore 2 ↥B ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, -, -, hcomm⟩ := LocDbl.nonquasisimple_Fitting_of_mem_cComp hB hq
    apply hcomm
    refine LocDbl.commutator_fitting_eq_bot_of_pCore fun ℓ hℓ => ?_
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      rw [hbot, Subgroup.commutator_bot_right]
    · exact commutator_pCore_eq_bot_of_scalar_quotient (p := 2) D hD β hβ hℓ hℓ2
  set π : Γ →* Γ ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hDc : D ≤ center Γ := by
    intro d hd
    obtain ⟨c, hc⟩ := hD d hd
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL (Fin 3) k)).symm
  have hker : π.ker ≤ center Γ := by rw [hπ, QuotientGroup.ker_mk']; exact hDc
  have hN₂p : IsPGroup 2 ((CFSG.pCore 2 ↥B).map β) := CFSG.pCore_isPGroup.map β
  obtain ⟨P₀, hchar, hPN⟩ := exists_normal_sylow_of_central_kernel π hπs hker hN₂p
  set Q : Subgroup Γ := (P₀ : Subgroup (((CFSG.pCore 2 ↥B).map β).comap π)).map
    (((CFSG.pCore 2 ↥B).map β).comap π).subtype with hQdef
  let θ : Γ →* LinearMap.GeneralLinearGroup k (Fin 3 → k) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) k ≃* _).toMonoidHom.comp Γ.subtype
  have hθ : Function.Injective θ :=
    Matrix.GeneralLinearGroup.toLin.injective.comp Γ.subtype_injective
  have hV3 : finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  have : Finite (LinearMap.GeneralLinearGroup k (Fin 3 → k)) := LocDbl.finite_GL
  have hQp : IsPGroup 2 (Q.map θ) := (P₀.isPGroup'.map _).map θ
  have hQne : Q.map θ ≠ ⊥ := by
    have hN₂ne : (CFSG.pCore 2 ↥B).map β ≠ ⊥ := fun h =>
      hO2 ((Subgroup.map_eq_bot_iff_of_injective _ hβ).mp h)
    obtain ⟨n, hn, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN₂ne |> fun ⟨n, hn⟩ =>
      (⟨n, n.2, fun h => hn (Subtype.ext h)⟩ : ∃ n ∈ (CFSG.pCore 2 ↥B).map β, n ≠ 1)
    obtain ⟨q, hq, hqn⟩ := hPN n hn
    intro hbot
    have hθq : θ q ∈ Q.map θ := ⟨q, ⟨q, hq, rfl⟩, rfl⟩
    rw [hbot, mem_bot] at hθq
    apply hn1
    rw [← hqn, hθ (hθq.trans (map_one θ).symm), map_one]
  have hB' : ⁅β.range, β.range⁆ = β.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  set L₀ : Subgroup Γ := (CFSG.perfectResidual (β.range.comap π)).map
    (β.range.comap π).subtype with hL₀def
  have hL₀B : L₀.map π = β.range := map_perfectResidual_comap_eq π hπs hB'
  have hL₀perf : ⁅L₀, L₀⁆ = L₀ := by
    have h1 : Group.IsPerfect (CFSG.perfectResidual (β.range.comap π)) :=
      (CFSG.perfect_residual_characterization (G := β.range.comap π)).2.2.1
    rw [Subgroup.isPerfect_iff] at h1
    rw [hL₀def, ← Subgroup.map_commutator, h1]
  have : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  have hNn := map_subgroupOf_range_normal β (CFSG.pCore 2 ↥B)
  have hNB : (CFSG.pCore 2 ↥B).map β ≤ β.range := by
    rw [MonoidHom.range_eq_map]
    exact map_mono le_top
  have hrangeN : β.range ≤ normalizer (((CFSG.pCore 2 ↥B).map β : Subgroup (Γ ⧸ D)) :
      Set (Γ ⧸ D)) := (normal_subgroupOf_iff_le_normalizer hNB).mp hNn
  have hL₀Q : L₀ ≤ normalizer (Q : Set Γ) :=
    (map_subtype_le _).trans (((comap_mono hrangeN).trans (le_normalizer_comap π)).trans
      (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))
  have hLperf : ⁅L₀.map θ, L₀.map θ⁆ = L₀.map θ := by rw [← Subgroup.map_commutator, hL₀perf]
  have hLQ : L₀.map θ ≤ normalizer ((Q.map θ : Subgroup _) : Set _) :=
    (map_mono hL₀Q).trans (le_normalizer_map θ)
  have hW0 : LocDbl.fixedSpace (Q.map θ) ≠ ⊥ :=
    LocDbl.exists_fixed_ne_zero (p := 2) (by rw [hV3]; norm_num) hQp
  have hWtop : LocDbl.fixedSpace (Q.map θ) ≠ ⊤ := LocDbl.fixedSpace_ne_top hQne
  have hLW : ∀ g ∈ L₀.map θ, ∀ w ∈ LocDbl.fixedSpace (Q.map θ),
      (g : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) w ∈ LocDbl.fixedSpace (Q.map θ) :=
    fun g hg w hw => LocDbl.fixedSpace_invariant (hLQ hg) hw
  obtain ⟨hscalar, hquot⟩ := flag_conclusions hV3 hLperf hW0 hWtop hLW
  have hinj : Function.Injective (π.comp L₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxD : (x : Γ) ∈ D := by
      rwa [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    obtain ⟨c, hc⟩ := hD _ hxD
    have hθx : ((θ x : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
        (Fin 3 → k) →ₗ[k] (Fin 3 → k)) = (c : k) • LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      have h1 : ((θ x : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
          (Fin 3 → k) →ₗ[k] (Fin 3 → k)) v =
          (((x : Γ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v := rfl
      rw [h1, hc]
      ext i
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct, Matrix.scalar_apply,
        Matrix.diagonal_apply]
    have h1 := hscalar (θ x) ⟨x, x.2, rfl⟩ (c : k) hθx
    exact Subtype.ext (hθ (h1.trans (map_one θ).symm))
  have hrange : (π.comp L₀.subtype).range = β.range := by
    rw [MonoidHom.range_comp, range_subtype, hL₀B]
  let e : ↥B ≃* ↥(L₀.map θ) :=
    (MonoidHom.ofInjective hβ).trans (((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr hrange)).symm.trans (L₀.equivMapOfInjective θ hθ))
  have hLcomp : L₀.map θ ∈ cComp (L₀.map θ) := by
    have h1 : (⊤ : Subgroup ↥B) ∈ cComp (⊤ : Subgroup ↥B) := by
      have h := subgroupOf_mem_cComp hB
      rwa [Subgroup.subgroupOf_self] at h
    have h2 := cComp_map_mulEquiv e h1
    rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
    have h3 := map_subtype_mem_cComp h2
    rwa [← MonoidHom.range_eq_map, range_subtype] at h3
  exact isQuasisimple_quotient_pCore_of_mulEquiv e (hquot hLcomp)

end CFSG.Quasithin.H13.NQCat
