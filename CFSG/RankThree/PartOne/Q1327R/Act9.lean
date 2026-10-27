module

public import CFSG.RankThree.PartOne.Q1327R.Aut9
public import CFSG.RankThree.PartOne.Q1327R.Frame9

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KFU
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Theta

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def psuEquiv (n : ℕ) :
    unitaryPSU h n ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

@[expose] noncomputable def Theta (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1) :
    unitarySU 2 f K 4 ≃* P4 h :=
  have hbot : unitaryScalars h 4 = ⊥ :=
    Subgroup.card_eq_one.mp ((card_unitaryScalars h (by norm_num)).trans hgcd)
  ((QuotientGroup.quotientBot (G := unitarySU 2 f K 4)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans (psuEquiv h 4)

theorem Theta_apply (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1) (t : unitarySU 2 f K 4)
    (hm : (t : GL (Fin 4) K) ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    Theta h hgcd t = (QuotientGroup.mk (⟨(t : GL (Fin 4) K), hm⟩ : gramSU h
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : P4 h) := by
  rfl

theorem fld_Theta_of_fixed (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1) (σ : K ≃+* K)
    (t : unitarySU 2 f K 4) (ht : glAut σ (t : GL (Fin 4) K) = (t : GL (Fin 4) K)) :
    fld h σ (Theta h hgcd t) = Theta h hgcd t := by
  have hm : (t : GL (Fin 4) K) ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    (SetLike.ext_iff.mp (unitarySU_eq_gramSU h 4) _).mp t.2
  rw [Theta_apply h hgcd t hm]
  unfold fld
  rw [primeFormFieldHom, MonoidHom.coe_mk, OneHom.coe_mk, primeFormFieldAut_mk]
  congr 1
  exact Subtype.ext ht

end Theta

theorem mem_centralizer_of_conj_eq {G : Type} [Group G] {X : Subgroup G} {g : G}
    (h : ∀ y ∈ X, g * y * g⁻¹ = y) : g ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h4 := h y hy
  calc y * g = (g * y * g⁻¹) * g := by rw [h4]
    _ = g * y := by group

namespace U4Frame

variable {G : Type} [Group G] {p f : ℕ} {K : Type} [Field K] {X E : Subgroup G}
  (C : U4Frame p f K X E) (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1)

@[expose] noncomputable def eP : X ≃* P4 C.hU := C.ψ.symm.trans (Theta C.hU hgcd)

@[expose] noncomputable def Phi : ↥(Subgroup.normalizer (X : Set G)) →* MulAut (P4 C.hU) :=
  (MulAut.congr (C.eP hgcd)).toMonoidHom.comp X.normalizerMonoidHom

theorem eP_psi (t : unitarySU 2 f K 4) : C.eP hgcd (C.ψ t) = Theta C.hU hgcd t := by
  simp [eP]

theorem coe_symm_Phi (n : ↥(Subgroup.normalizer (X : Set G))) (y : X) :
    (((C.eP hgcd).symm (C.Phi hgcd n (C.eP hgcd y)) : X) : G) = n * y * (n : G)⁻¹ := by
  simp [Phi, MulAut.congr_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem Phi_eq_one_iff (n : ↥(Subgroup.normalizer (X : Set G))) :
    C.Phi hgcd n = 1 ↔ ∀ y ∈ X, (n : G) * y * (n : G)⁻¹ = y := by
  constructor
  · intro h1 y hy
    have := C.coe_symm_Phi hgcd n ⟨y, hy⟩
    rw [h1] at this
    simpa using this.symm
  · intro h1
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := (C.eP hgcd).surjective q
    apply (C.eP hgcd).symm.injective
    apply Subtype.ext
    rw [C.coe_symm_Phi hgcd n y, MulAut.one_apply]
    simpa using h1 y y.2

theorem Phi_of_mem_X (y₀ : X) (hy₀ : (y₀ : G) ∈ Subgroup.normalizer (X : Set G)) :
    C.Phi hgcd ⟨y₀, hy₀⟩ = MulAut.conj (C.eP hgcd y₀) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨y, rfl⟩ := (C.eP hgcd).surjective q
  apply (C.eP hgcd).symm.injective
  apply Subtype.ext
  rw [C.coe_symm_Phi hgcd ⟨y₀, hy₀⟩ y]
  simp [MulAut.conj_apply]

theorem mem_sup_of_Phi_mem_inner (n : ↥(Subgroup.normalizer (X : Set G)))
    (hn : C.Phi hgcd n ∈ inner (P4 C.hU)) :
    (n : G) ∈ X ⊔ Subgroup.centralizer (X : Set G) := by
  obtain ⟨q, hq⟩ := hn
  obtain ⟨y₀, rfl⟩ := (C.eP hgcd).surjective q
  have hy₀N : (y₀ : G) ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer y₀.2
  have h1 : C.Phi hgcd n = C.Phi hgcd ⟨y₀, hy₀N⟩ := by
    rw [C.Phi_of_mem_X hgcd y₀ hy₀N]
    exact hq.symm
  have h2 : C.Phi hgcd (n * ⟨y₀, hy₀N⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (C.Phi_eq_one_iff hgcd _).mp h2
  have hc : (n : G) * (y₀ : G)⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    refine mem_centralizer_of_conj_eq fun y hy => ?_
    have := h3 y hy
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have : (n : G) = ((n : G) * (y₀ : G)⁻¹) * (y₀ : G) := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hc y₀.2

theorem centralizes_of_Phi_fld (hp : p.Prime) (u : ↥(Subgroup.normalizer (X : Set G)))
    {σ : K ≃+* K} (hσ : σ ^ p = 1) (hu : C.Phi hgcd u = fld C.hU σ) {e : G} (he : e ∈ E) :
    (u : G) * e * (u : G)⁻¹ = e := by
  obtain ⟨t, ht, rfl⟩ := C.exists_decomp he
  obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp ht
  have hglt : glAut σ ((t : unitarySU 2 f K 4) : GL (Fin 4) K) = (t : GL (Fin 4) K) := by
    rw [← hd]
    apply Units.ext
    rw [coe_glAut, diagU_val, Matrix.diagonal_map (map_zero σ)]
    congr 1
    funext i
    exact ringEquiv_fixes_rootsOfUnity hp hσ (by
      have := congrArg (fun z : Kˣ => (z : K)) (hd1 i)
      simpa using this)
  have hfix := fld_Theta_of_fixed C.hU hgcd σ t hglt
  have hψ : C.eP hgcd (C.ψ t) = Theta C.hU hgcd t := C.eP_psi hgcd t
  have h1 := C.coe_symm_Phi hgcd u (C.ψ t)
  rw [hu, hψ, hfix, ← hψ, MulEquiv.symm_apply_apply] at h1
  exact h1.symm

end U4Frame

end CFSG.RankThree.PartOne.Q1327R
