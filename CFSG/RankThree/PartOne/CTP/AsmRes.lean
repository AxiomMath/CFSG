module

public import CFSG.RankThree.PartOne.CTP.AsmDefs
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartOne.S12K.FixedLayer
public import CFSG.RankThree.PartOne.CTP.ModelFacts

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.LocalCores
open CFSG.RankThree.PartOne.EmbeddingTransport
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_residual_inf {p : ℕ} {a : G} {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p a) {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer ({a} : Set G)) :
    ((inSubgroup perfectResidual (I ⊓ H)).subgroupOf H).IsSubnormal := by
  have hsn := isSubnormal_of_mem_thetaComponentsAt hI
  have h1 := hsn.comap (Subgroup.inclusion hH)
  have hY : ((I ⊓ H).subgroupOf H).IsSubnormal := by
    convert h1 using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
      Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  set Y := I ⊓ H with hYdef
  set X := inSubgroup perfectResidual Y with hXdef
  have hXY : X ≤ Y := Subgroup.map_subtype_le _
  have hXn : (X.subgroupOf Y).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_inSubgroup_perfectResidual g.2 hx⟩
  exact S12K.isSubnormal_subgroupOf_of_normal hXY hXn hY

theorem eq_of_components_common {H X X' J : Subgroup G} (hX : X ≤ H) (hX' : X' ≤ H)
    (hXq : CFSG.IsQuasisimple ↥X) (hX'q : CFSG.IsQuasisimple ↥X')
    (hXs : (X.subgroupOf H).IsSubnormal) (hX's : (X'.subgroupOf H).IsSubnormal)
    (hJX : J ≤ X) (hJX' : J ≤ X') (hJ : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) : X = X' := by
  have hc1 : CFSG.IsComponent (X.subgroupOf H) :=
    ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hX).symm hXq, hXs⟩
  have hc2 : CFSG.IsComponent (X'.subgroupOf H) :=
    ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hX').symm hX'q, hX's⟩
  rcases distinct_components_commute hc1 hc2 with h | h
  · have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hX'] at this
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hJ
    have hc : ⁅(⟨x, hX (hJX hx)⟩ : H), (⟨y, hX' (hJX' hy)⟩ : H)⁆ ∈
        ⁅X.subgroupOf H, X'.subgroupOf H⁆ :=
      Subgroup.commutator_mem_commutator (hJX hx) (hJX' hy)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hxy (congrArg Subtype.val hc)

omit [Finite G] in
theorem centralizer_zpowers_eq (b : G) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h b (Subgroup.mem_zpowers b)).symm
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute b x from h.symm) k).eq

omit [Finite G] in
theorem pairLayer_eq_residual {I BK Jab R : Subgroup G} {b : G}
    (hI : I ≤ Subgroup.centralizer ({b} : Set G))
    (hR : R = (BK ⊓ Subgroup.centralizer (Jab : Set G)) ⊔ Subgroup.zpowers b) :
    pairLayer I BK Jab = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer (R : Set G)) := by
  unfold pairLayer
  congr 1
  rw [hR, centralizer_sup, centralizer_zpowers_eq]
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, hx2⟩
    exact ⟨hx, hx2, hI hx⟩
  · rintro ⟨hx, hx2, -⟩
    exact ⟨hx, hx2⟩

omit [Finite G] in
theorem three_ne_e3 (x : Fin 3) : (3 : Fin 5) ≠ e3 x := fun h => by
  have := congrArg Fin.val h
  simp [e3] at this
  omega

omit [Finite G] in
theorem four_ne_e3 (x : Fin 3) : (4 : Fin 5) ≠ e3 x := fun h => by
  have := congrArg Fin.val h
  simp [e3] at this
  omega

omit [Finite G] in
theorem e3_ne {x y : Fin 3} (h : x ≠ y) : e3 x ≠ e3 y := fun h' => by
  apply h
  have := congrArg Fin.val h'
  simp [e3] at this
  exact Fin.ext this

section Asm

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G}

structure Asm (c : G) (F : LFam L B f₀ b K) (I : Subgroup G) : Prop where
  hI : I ∈ thetaComponentsAt 5 b
  cfg : ∀ σ, IConfig c f₀ (Isg F I σ) (Ksg F σ) (BKsg F σ) (Jsg F σ)
  facts : ∀ σ, IFacts c f₀ (Isg F I σ) (Ksg F σ) (BKsg F σ) (Jsg F σ)
  h5norm : ∀ (σ : Equiv.Perm (Fin 5)) (x : G), x * bsg F σ = bsg F σ * x →
    (∃ k : ℕ, orderOf x = 5 ^ k) → x ∈ Subgroup.normalizer (Isg F I σ : Set G)

variable {c : G} {F : LFam L B f₀ b K} {I : Subgroup G}

theorem Asm.Isg_le_cent (A : Asm c F I) (σ : Equiv.Perm (Fin 5)) :
    Isg F I σ ≤ Subgroup.centralizer ({bsg F σ} : Set G) :=
  (mem_thetaComponentsAt_iff.mp (Isg_mem_theta F I A.hI σ)).1

omit [Finite G] in
theorem R_eq (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) (hxy : x ≠ y) :
    B ⊓ Subgroup.centralizer (F.J (σ (e3 x)) (σ (e3 y)) : Set G) =
      (BKsg F σ ⊓ Subgroup.centralizer (Jsg F σ x y : Set G)) ⊔ Subgroup.zpowers (bsg F σ) := by
  have h := congrArg (conjBy (F.W σ)) (F.hyper_eq x y hxy)
  rw [conjBy_B_inf_centralizer_J, conjBy_sup, conjBy_inf, conjBy_centralizer,
    conjBy_zpowers] at h
  exact h

theorem Asm.Msg_eq_residual (A : Asm c F I) (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) (hxy : x ≠ y) :
    Msg F I σ x y = inSubgroup perfectResidual (Isg F I σ ⊓ Subgroup.centralizer
      ((B ⊓ Subgroup.centralizer (F.J (σ (e3 x)) (σ (e3 y)) : Set G) : Subgroup G) : Set G)) :=
  pairLayer_eq_residual (A.Isg_le_cent σ) (R_eq σ x y hxy)

omit [Finite G] in
theorem bsg_mem_R (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) (hxy : x ≠ y) :
    bsg F σ ∈ B ⊓ Subgroup.centralizer (F.J (σ (e3 x)) (σ (e3 y)) : Set G) := by
  refine ⟨(bsg_mem F σ).1, ?_⟩
  have hle := F.disj (σ 3) (σ 4) (σ (e3 x)) (σ (e3 y)) (σ.injective.ne (by decide))
    (σ.injective.ne (e3_ne hxy)) (σ.injective.ne (three_ne_e3 x))
    (σ.injective.ne (three_ne_e3 y)) (σ.injective.ne (four_ne_e3 x))
    (σ.injective.ne (four_ne_e3 y))
  exact hle (bsg_mem F σ).2

theorem Asm.Msg_eq_of_pair (A : Asm c F I) {σ τ : Equiv.Perm (Fin 5)} {x y x' y' : Fin 3}
    (hxy : x ≠ y) (hxy' : x' ≠ y') (h1 : σ (e3 x) = τ (e3 x')) (h2 : σ (e3 y) = τ (e3 y')) :
    Msg F I σ x y = Msg F I τ x' y' := by
  set R : Subgroup G := B ⊓ Subgroup.centralizer (F.J (σ (e3 x)) (σ (e3 y)) : Set G) with hR
  set H : Subgroup G := Subgroup.centralizer (R : Set G) with hH
  have hRτ : B ⊓ Subgroup.centralizer (F.J (τ (e3 x')) (τ (e3 y')) : Set G) = R := by
    rw [← h1, ← h2]
  have hX := A.Msg_eq_residual σ x y hxy
  have hX' := A.Msg_eq_residual τ x' y' hxy'
  rw [hRτ] at hX'
  have hXH : Msg F I σ x y ≤ H := by
    rw [hX]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hXH' : Msg F I τ x' y' ≤ H := by
    rw [hX']
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hbσ : bsg F σ ∈ R := bsg_mem_R σ x y hxy
  have hbτ : bsg F τ ∈ R := by
    rw [← hRτ]
    exact bsg_mem_R τ x' y' hxy'
  have hHσ : H ≤ Subgroup.centralizer ({bsg F σ} : Set G) :=
    Subgroup.centralizer_le (by simpa using hbσ)
  have hHτ : H ≤ Subgroup.centralizer ({bsg F τ} : Set G) :=
    Subgroup.centralizer_le (by simpa using hbτ)
  have hsn : ((Msg F I σ x y).subgroupOf H).IsSubnormal := by
    rw [hX]
    exact isSubnormal_residual_inf (Isg_mem_theta F I A.hI σ) hHσ
  have hsn' : ((Msg F I τ x' y').subgroupOf H).IsSubnormal := by
    rw [hX']
    exact isSubnormal_residual_inf (Isg_mem_theta F I A.hI τ) hHτ
  have hJ : F.J (σ (e3 x)) (σ (e3 y)) ≤ Msg F I σ x y :=
    (Jsg_eq F σ x y).symm.le.trans ((A.facts σ).J_le_M x y hxy)
  have hJ' : F.J (σ (e3 x)) (σ (e3 y)) ≤ Msg F I τ x' y' := by
    have e : F.J (σ (e3 x)) (σ (e3 y)) = Jsg F τ x' y' := by rw [Jsg_eq, h1, h2]
    exact e.le.trans ((A.facts τ).J_le_M x' y' hxy')
  have hnc := psl2_model_exists_noncomm (F.J_model (σ (e3 x)) (σ (e3 y))
    (σ.injective.ne (e3_ne hxy)))
  exact eq_of_components_common hXH hXH' ((A.facts σ).M_quasi x y hxy)
    ((A.facts τ).M_quasi x' y' hxy') hsn hsn' hJ hJ' hnc

end Asm

end CFSG.RankThree.PartOne.CTP
