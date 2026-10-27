module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DSix
public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CRank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open Module
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem inf_QB_eq_of_le_sup95 (hc : Ctx M Q Z B) {B' : Subgroup G} (hc' : Ctx M Q Z B')
    (hle : B' ≤ Z ⊔ B) {Y : Subgroup G} (hYQ : Y ≤ Q) :
    Y ⊓ QB B' = Y ⊓ QB B := by
  obtain ⟨p, hp, rfl⟩ := hc.exists_conj_of_le_ZB hc' hle
  rw [QB_conj]
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  ext v
  simp only [Subgroup.mem_inf, mem_conjSubgroup]
  constructor
  · rintro ⟨hvY, hv⟩
    refine ⟨hvY, ?_⟩
    have hcomm : ⁅p⁻¹, v⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hp) (hYQ hvY)
    have hζ : p⁻¹ * v * p * v⁻¹ ∈ Z := by simpa [commutatorElement_def] using hcomm
    have e : v = (p⁻¹ * v * p * v⁻¹)⁻¹ * (p⁻¹ * v * p) := by group
    rw [e]
    exact (QB B).mul_mem ((QB B).inv_mem (hZQB hζ)) hv
  · rintro ⟨hvY, hv⟩
    refine ⟨hvY, ?_⟩
    have hcomm : ⁅p⁻¹, v⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hp) (hYQ hvY)
    have hζ : p⁻¹ * v * p * v⁻¹ ∈ Z := by simpa [commutatorElement_def] using hcomm
    have e : p⁻¹ * v * p = (p⁻¹ * v * p * v⁻¹) * v := by group
    rw [e]
    exact (QB B).mul_mem (hZQB hζ) hv

theorem polar_mulVec_of_mem95 {K : Type} [Field K] {g : GL (Fin 2 ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 2 K)) (a b : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 2 K) ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a)
        ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b) = polar (quadPlus 2 K) a b := by
  have hQ : ∀ v, quadPlus 2 K ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      quadPlus 2 K v := by
    intro v
    have := statedOmega_isometry95 hg v
    rwa [← coe_quadPlus 2 K] at this
  have h1 := QuadraticMap.map_add (quadPlus 2 K)
    ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a)
    ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b)
  rw [← Matrix.mulVec_add, hQ, hQ, hQ] at h1
  have h2 := QuadraticMap.map_add (quadPlus 2 K) a b
  linear_combination h2 - h1

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.mem_QB_conj_iff (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t) :
    v ∈ QB (conjSubgroup ρ B) ↔
      polar (quadPlus 2 K) ((C.φ ⟨ρ, hρ⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u)
        (secVec C.ψ ⟨v, hv⟩) = 0 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hρi : ρ⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hρ
  have hv' : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρi) v).mp hv
    simpa using this
  rw [QB_conj, mem_conjSubgroup]
  have hvec : secVec C.ψ ⟨ρ⁻¹ * v * ρ, hv'⟩ =
      (C.φ ⟨ρ⁻¹, hρi⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨v, hv⟩ :=
    C.hψ ⟨ρ⁻¹, hρi⟩ ⟨v, hv⟩ ⟨ρ⁻¹ * v * ρ, hv'⟩ (by simp)
  have hΩ : C.φ ⟨ρ, hρ⟩ ∈ StatedOmega (StatedQuadPlus 2 K) := C.hφ ▸ ⟨_, rfl⟩
  have hinv : (C.φ ⟨ρ⁻¹, hρi⟩ : GL (Fin 2 ⊕ Fin 2) K) = (C.φ ⟨ρ, hρ⟩)⁻¹ := by
    rw [← map_inv]; rfl
  have hpol : polar (quadPlus 2 K) C.u
      ((C.φ ⟨ρ⁻¹, hρi⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨v, hv⟩) =
      polar (quadPlus 2 K)
        ((C.φ ⟨ρ, hρ⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u)
        (secVec C.ψ ⟨v, hv⟩) := by
    have := polar_mulVec_of_mem95 hΩ C.u
      ((C.φ ⟨ρ⁻¹, hρi⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨v, hv⟩)
    rw [← this]
    congr 1
    rw [Matrix.mulVec_mulVec, hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [← hpol, ← hvec]
  constructor
  · intro h
    have h1 : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t ⊓ QB B := ⟨hv', h⟩
    exact ((C.hW (secVec C.ψ ⟨ρ⁻¹ * v * ρ, hv'⟩)).mp ⟨⟨ρ⁻¹ * v * ρ, hv'⟩, h1, rfl⟩)
  · intro h
    obtain ⟨w, hwVQ, hwv⟩ := (C.hW _).mpr h
    have hzw : (w : G)⁻¹ * (ρ⁻¹ * v * ρ) ∈ Z := by
      have h1 : secVec C.ψ (w⁻¹ * ⟨ρ⁻¹ * v * ρ, hv'⟩) = 0 := by
        rw [secVec_mul, secVec_inv, hwv]
        abel
      exact (secVec_eq_zero_iff C.ψ _).mp h1
    have e1 : ρ⁻¹ * v * ρ = (w : G) * ((w : G)⁻¹ * (ρ⁻¹ * v * ρ)) := by group
    rw [e1]
    exact (QB B).mul_mem (Subgroup.mem_inf.mp hwVQ).2 (hZQB hzw)

theorem card_polar_orth_two95 {u₁ u₂ : Fin 2 ⊕ Fin 2 → K} (h₁ : u₁ ≠ 0)
    (hind : ∀ a : K, u₂ ≠ a • u₁) :
    Nat.card {y : Fin 2 ⊕ Fin 2 → K // polar (quadPlus 2 K) u₁ y = 0 ∧
      polar (quadPlus 2 K) u₂ y = 0} = Nat.card K ^ 2 := by
  classical
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  set Sp : Submodule K (Fin 2 ⊕ Fin 2 → K) := Submodule.span K {u₁, u₂} with hSp
  have hli : LinearIndependent K ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht0 : t = 0 := by
      by_contra ht
      apply hind (-(s / t))
      have : t • u₂ = -(s • u₁) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      calc u₂ = t⁻¹ • (t • u₂) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (-(s • u₁)) := by rw [this]
        _ = (-(s / t)) • u₁ := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    subst ht0
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right h₁, rfl⟩
  have hSpdim : finrank K Sp = 2 := by
    have h := finrank_span_eq_card hli
    have hrange : Set.range ![u₁, u₂] = {u₁, u₂} := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
      exact or_comm
    rw [hrange] at h
    simpa [hSp] using h
  have hdim : finrank K ↥(LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 2 K)) Sp) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQnd, hSpdim, Module.finrank_fintype_fun_eq_card]
    simp
  have hcard : Nat.card ↥(LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 2 K)) Sp) =
      Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdim]
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · rintro ⟨hy₁, hy₂⟩ x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    show (polarBilin (quadPlus 2 K)) (a • u₁ + b • u₂) y = 0
    rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply]
    simp [QuadraticMap.polarBilin_apply_apply, hy₁, hy₂]
  · intro h
    refine ⟨?_, ?_⟩
    · have := h u₁ (Submodule.subset_span (by simp))
      simpa [LinearMap.BilinForm.isOrtho_def, QuadraticMap.polarBilin_apply_apply] using this
    · have := h u₂ (Submodule.subset_span (by simp))
      simpa [LinearMap.BilinForm.isOrtho_def, QuadraticMap.polarBilin_apply_apply] using this

theorem Coord95.card_inf_two_points (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {ρ₁ ρ₂ : G}
    (hρ₁ : ρ₁ ∈ Rt M (LB M Q B) t) (hρ₂ : ρ₂ ∈ Rt M (LB M Q B) t)
    (hind : ∀ a : K, (C.φ ⟨ρ₂, hρ₂⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u ≠
      a • ((C.φ ⟨ρ₁, hρ₁⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u)) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup ρ₁ B) ⊓ QB (conjSubgroup ρ₂ B)) =
      Nat.card Z ^ 3 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  set V := Vt M (LB M Q B) B Z t with hVdef
  set u₁ : Fin 2 ⊕ Fin 2 → K :=
    (C.φ ⟨ρ₁, hρ₁⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u with hu₁
  set u₂ : Fin 2 ⊕ Fin 2 → K :=
    (C.φ ⟨ρ₂, hρ₂⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u with hu₂
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    apply C.hu0
    have := congrArg (fun y => ((C.φ ⟨ρ₁, hρ₁⟩)⁻¹ : GL (Fin 2 ⊕ Fin 2) K).val *ᵥ y) h0
    simp only [hu₁, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  set Y : Subgroup G := V ⊓ QB (conjSubgroup ρ₁ B) ⊓ QB (conjSubgroup ρ₂ B) with hYdef
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZY : Z ≤ Y := by
    refine le_inf (le_inf hZV ?_) ?_
    · exact (hc.conj_of_mem (hc.Rt_le_M t hρ₁)).Z_le_QB.1
    · exact (hc.conj_of_mem (hc.Rt_le_M t hρ₂)).Z_le_QB.1
  have hYV : Y ≤ V := inf_le_left.trans inf_le_left
  let g : ↥Y →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    (C.ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf V))).comp (Subgroup.inclusion hYV)
  have hg : ∀ y : ↥Y, g y = Multiplicative.ofAdd (secVec C.ψ ⟨y, hYV y.2⟩) := fun y => rfl
  have hkerg : g.ker = Z.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, hg, ofAdd_eq_one, secVec_eq_zero_iff, Subgroup.mem_subgroupOf]
  have hkerCard : Nat.card g.ker = Nat.card Z := by
    rw [hkerg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  have hrange : (g.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) =
      Multiplicative.ofAdd '' {y : Fin 2 ⊕ Fin 2 → K | polar (quadPlus 2 K) u₁ y = 0 ∧
        polar (quadPlus 2 K) u₂ y = 0} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨secVec C.ψ ⟨y, hYV y.2⟩, ⟨?_, ?_⟩, rfl⟩
      · exact (C.mem_QB_conj_iff hs hρ₁ (hYV y.2)).mp y.2.1.2
      · exact (C.mem_QB_conj_iff hs hρ₂ (hYV y.2)).mp y.2.2
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      obtain ⟨v, hv⟩ := exists_secVec_eq C.ψ s
      have hvY : (v : G) ∈ Y := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨v.2, ?_⟩, ?_⟩
        · exact (C.mem_QB_conj_iff hs hρ₁ v.2).mpr (by rw [hv]; exact h1)
        · exact (C.mem_QB_conj_iff hs hρ₂ v.2).mpr (by rw [hv]; exact h2)
      refine ⟨⟨v, hvY⟩, ?_⟩
      rw [hg]
      show Multiplicative.ofAdd (secVec C.ψ v) = _
      rw [hv]
  have hrangeCard : Nat.card g.range = Nat.card K ^ 2 := by
    calc Nat.card g.range
        = Nat.card (g.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) := rfl
      _ = Nat.card (Multiplicative.ofAdd '' {y : Fin 2 ⊕ Fin 2 → K |
          polar (quadPlus 2 K) u₁ y = 0 ∧ polar (quadPlus 2 K) u₂ y = 0}) := by rw [hrange]
      _ = Nat.card {y : Fin 2 ⊕ Fin 2 → K |
          polar (quadPlus 2 K) u₁ y = 0 ∧ polar (quadPlus 2 K) u₂ y = 0} :=
        Nat.card_image_of_injective Multiplicative.ofAdd.injective _
      _ = Nat.card K ^ 2 := card_polar_orth_two95 hu₁0 hind
  have hmul := Subgroup.card_ker_mul_card_range g
  rw [hkerCard, hrangeCard, C.hK] at hmul
  rw [← hmul]
  ring

end Count

theorem le_sup_of_common_pi95 {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {X X' : Subgroup G}
    (hX : Ctx M Q Z X) (hX' : Ctx M Q Z X') {a a' : G} (ha : a ∈ X) (ha' : a' ∈ X')
    (hpi : M₀.π a = M₀.π a') (hne : M₀.π a ≠ 0) : X' ≤ Z ⊔ X := by
  classical
  obtain ⟨b, hb0, -, hB, -, -⟩ := hX.dictB h
  obtain ⟨b', hb'0, -, hB', -, -⟩ := hX'.dictB h
  have h1 : M₀.π a ∈ M₀.img X := M₀.pi_mem_img ha (hX.le ha)
  have h2 : M₀.π a' ∈ M₀.img X' := M₀.pi_mem_img ha' (hX'.le ha')
  obtain ⟨s, hs⟩ := (hB _).mp h1
  obtain ⟨s', hs'⟩ := (hB' _).mp h2
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hne (by rw [hs, zero_smul])
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    exact hne (by rw [hpi, hs', zero_smul])
  have hbb : b' = (s' ⁻¹ * s) • b := by
    have : s' • b' = s • b := by rw [← hs', ← hs, hpi]
    calc b' = s'⁻¹ • (s' • b') := by rw [smul_smul, inv_mul_cancel₀ hs'0, one_smul]
      _ = s'⁻¹ • (s • b) := by rw [this]
      _ = (s'⁻¹ * s) • b := by rw [smul_smul]
  intro x' hx'
  have hx'Q : x' ∈ Q := hX'.le hx'
  have h3 : M₀.π x' ∈ M₀.img X' := M₀.pi_mem_img hx' hx'Q
  obtain ⟨r, hr⟩ := (hB' _).mp h3
  have h4 : M₀.π x' ∈ M₀.img (X ⊔ Z) := by
    obtain ⟨x, hxX, hxQ, hx⟩ := (hB ((r * (s'⁻¹ * s)) • b)).mpr ⟨r * (s'⁻¹ * s), rfl⟩
    refine ⟨x, Subgroup.mem_sup_left hxX, hxQ, ?_⟩
    rw [hx, hr, hbb, smul_smul]
  have := (M₀.mem_img_iff (le_sup_right : Z ≤ X ⊔ Z) hx'Q).mp h4
  rwa [sup_comm] at this

section Final

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.conj_le_sup_of_eigen95 (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) {a : K}
    (ha : (C.φ ⟨ρ, hρ⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u = a • C.u) :
    conjSubgroup ρ B ≤ Z ⊔ B := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  intro v hv
  have hb : ρ⁻¹ * v * ρ ∈ B := mem_conjSubgroup.mp hv
  have hbV : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
  have hvV : v ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) (ρ⁻¹ * v * ρ)).mp hbV
    simpa [mul_assoc] using this
  obtain ⟨c', hc'⟩ := (C.hBiff (secVec C.ψ ⟨ρ⁻¹ * v * ρ, hbV⟩)).mp ⟨⟨ρ⁻¹ * v * ρ, hbV⟩, hb, rfl⟩
  have h1 : secVec C.ψ ⟨v, hvV⟩ =
      (C.φ ⟨ρ, hρ⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        secVec C.ψ ⟨ρ⁻¹ * v * ρ, hbV⟩ :=
    C.hψ ⟨ρ, hρ⟩ ⟨ρ⁻¹ * v * ρ, hbV⟩ ⟨v, hvV⟩ (by simp [mul_assoc])
  rw [hc', Matrix.mulVec_smul, ha, smul_smul] at h1
  obtain ⟨b₂, hb₂B, hb₂⟩ := (C.hBiff ((c' * a) • C.u)).mpr ⟨c' * a, rfl⟩
  have h2 : (v : G) * (b₂ : G)⁻¹ ∈ Z := by
    have := (secVec_eq_iff C.ψ ⟨v, hvV⟩ b₂).mp (h1.trans hb₂.symm)
    exact this
  have e : v = ((v : G) * (b₂ : G)⁻¹) * (b₂ : G) := by group
  rw [e]
  exact (Z ⊔ B).mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right hb₂B)

theorem Coord95.card_conj_inf95 (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {K' : Type} [Field K']
    [Finite K'] {γ : G → K'} {M₀ : Tim79.QuadModel Q Z K' γ} (h : GlobalModelData M Q Z γ M₀)
    {z c : G} (hzM : z ∈ M) (hzBZ : z ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G))
    (hcR : c ∈ Rt M (LB M Q B) t)
    (hcN : c ∉ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G))
    (hCV : ∀ a ∈ conjSubgroup c B,
      a ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t))
    (h54 : ∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      ∃ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t), ∃ b ∈ B, u * (ρ * b * ρ⁻¹)⁻¹ ∈ Z) :
    Nat.card ↥(conjSubgroup z (Vt M (LB M Q B) B Z t) ⊓ QB B ⊓ QB (conjSubgroup c B)) =
      Nat.card Z ^ 3 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  set V := Vt M (LB M Q B) B Z t with hVdef
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  have hzi : z⁻¹ ∈ M := M.inv_mem hzM
  have hzBZi : z⁻¹ ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)).inv_mem hzBZ
  have hZc : ∀ g ∈ M, conjSubgroup g Z = Z := fun g hg => hc.conj_Z_eq hg
  have hBZc : ∀ g ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G),
      conjSubgroup g (B ⊔ Z) = B ⊔ Z := fun g hg => conjSubgroup_eq_self_iff.mpr hg
  have hcmono : ∀ (g : G) {H H' : Subgroup G}, H ≤ H' → conjSubgroup g H ≤ conjSubgroup g H' :=
    fun g H H' hle => Subgroup.map_mono hle
  have hCtxc : Ctx M Q Z (conjSubgroup c B) := hc.conj_of_mem hcM
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  obtain ⟨b₀, hb₀B, hb₀Q, hb₀π⟩ := (M₀.mem_img).mp ((hB b).mpr ⟨1, (one_smul K' b).symm⟩)
  set a₀ : G := c * b₀ * c⁻¹ with ha₀
  have ha₀C : a₀ ∈ conjSubgroup c B := conj_mem95 c hb₀B
  have ha₀Q : a₀ ∈ Q := hVQ (hCV a₀ ha₀C).1
  obtain ⟨ρ, hρ, b'', hb'', hZ'⟩ := h54 a₀ (hCV a₀ ha₀C)
  have hρ₁ : z⁻¹ * ρ * z ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp hρ
  have hρM : ρ ∈ M := by
    have h1 : z * (z⁻¹ * ρ * z) * z⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hzM (hc.Rt_le_M t hρ₁)) hzi
    simpa [mul_assoc] using h1
  have hCtxρ : Ctx M Q Z (conjSubgroup ρ B) := hc.conj_of_mem hρM
  set w : G := ρ * b'' * ρ⁻¹ with hw
  have hwB : w ∈ conjSubgroup ρ B := conj_mem95 ρ hb''
  have hwQ : w ∈ Q := (hc.conj_mem_Q_of_mem_M hρM).1 b'' (hc.le hb'')
  have hwM : w ∈ M := M.mul_mem (M.mul_mem hρM (hc.hyp.Q_normal.1 (hc.le hb''))) (M.inv_mem hρM)
  have hpi : M₀.π w = M₀.π a₀ := by
    refine (M₀.pi_eq_iff hwQ ha₀Q).mpr ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hwM)) _).mp hZ'
    have e : w⁻¹ * a₀ = w⁻¹ * (a₀ * w⁻¹) * w⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hne : M₀.π w ≠ 0 := by
    rw [hpi]
    intro h0
    have h1 : a₀ ∈ Z := (M₀.π_ker a₀ ha₀Q).mp h0
    have h2 : b₀ ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hcM)) a₀).mp h1
      have e : c⁻¹ * a₀ * c⁻¹⁻¹ = b₀ := by rw [ha₀]; group
      rwa [e] at this
    have h3 : b₀ ∈ Z ⊓ B := ⟨h2, hb₀B⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
    apply hb0
    rw [← hb₀π, h3]
    exact M₀.pi_one
  have hCle : conjSubgroup c B ≤ Z ⊔ conjSubgroup ρ B :=
    le_sup_of_common_pi95 h hCtxρ hCtxc hwB ha₀C hpi hne
  set ρ₁ : G := z⁻¹ * ρ * z with hρ₁def
  set B₂ : Subgroup G := conjSubgroup z⁻¹ B with hB₂
  set C₂ : Subgroup G := conjSubgroup z⁻¹ (conjSubgroup c B) with hC₂
  have hρ₁M : ρ₁ ∈ M := hc.Rt_le_M t hρ₁
  have hB₂le : B₂ ≤ Z ⊔ B := by
    have h1 : conjSubgroup z⁻¹ B ≤ conjSubgroup z⁻¹ (B ⊔ Z) := hcmono z⁻¹ le_sup_left
    rw [hBZc z⁻¹ hzBZi] at h1
    rwa [sup_comm] at h1
  have hC₂le : C₂ ≤ Z ⊔ conjSubgroup ρ₁ B := by
    have h1 : conjSubgroup z⁻¹ (conjSubgroup c B) ≤ conjSubgroup z⁻¹ (Z ⊔ conjSubgroup ρ B) :=
      hcmono z⁻¹ hCle
    rw [conjSubgroup_sup95, hZc z⁻¹ hzi] at h1
    have h2 : conjSubgroup z⁻¹ (conjSubgroup ρ B) = conjSubgroup ρ₁ B₂ := by
      rw [← conjSubgroup_mul, hB₂, ← conjSubgroup_mul]
      congr 1
      rw [hρ₁def]
      group
    have h3 : conjSubgroup ρ₁ B₂ ≤ Z ⊔ conjSubgroup ρ₁ B := by
      have h4 := hcmono ρ₁ hB₂le
      rw [conjSubgroup_sup95, hZc ρ₁ hρ₁M] at h4
      exact h4
    rw [h2] at h1
    exact h1.trans (sup_le le_sup_left h3)
  have hCtxB₂ : Ctx M Q Z B₂ := hc.conj_of_mem hzi
  have hCtxC₂ : Ctx M Q Z C₂ := hCtxc.conj_of_mem hzi
  have hCtxρ₁ : Ctx M Q Z (conjSubgroup ρ₁ B) := hc.conj_of_mem hρ₁M
  have hA : V ⊓ QB B₂ = V ⊓ QB B := inf_QB_eq_of_le_sup95 hc hCtxB₂ hB₂le hVQ
  have hCC : V ⊓ QB C₂ = V ⊓ QB (conjSubgroup ρ₁ B) :=
    inf_QB_eq_of_le_sup95 hCtxρ₁ hCtxC₂ hC₂le hVQ
  have hconj : conjSubgroup z⁻¹ (conjSubgroup z V ⊓ QB B ⊓ QB (conjSubgroup c B)) =
      V ⊓ QB B₂ ⊓ QB C₂ := by
    rw [conjSubgroup_inf, conjSubgroup_inf, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one, ← QB_conj, ← QB_conj]
  have hcard : Nat.card ↥(conjSubgroup z V ⊓ QB B ⊓ QB (conjSubgroup c B)) =
      Nat.card ↥(V ⊓ QB B₂ ⊓ QB C₂) := by
    rw [← hconj, card_conjSubgroup]
  have hfinal : V ⊓ QB B₂ ⊓ QB C₂ = V ⊓ QB (conjSubgroup 1 B) ⊓ QB (conjSubgroup ρ₁ B) := by
    ext v
    have e1 := SetLike.ext_iff.mp hA v
    have e2 := SetLike.ext_iff.mp hCC v
    simp only [Subgroup.mem_inf] at e1 e2 ⊢
    rw [conjSubgroup_one]
    tauto
  have h1R : (1 : G) ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).one_mem
  have hind : ∀ a : K,
      (C.φ ⟨ρ₁, hρ₁⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u ≠
        a • ((C.φ ⟨1, h1R⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u) := by
    intro a ha
    have hφ1 : C.φ ⟨1, h1R⟩ = 1 := by
      have : (⟨1, h1R⟩ : ↥(Rt M (LB M Q B) t)) = 1 := rfl
      rw [this, map_one]
    rw [hφ1] at ha
    simp only [Units.val_one, Matrix.one_mulVec] at ha
    have hle : conjSubgroup ρ₁ B ≤ Z ⊔ B := C.conj_le_sup_of_eigen95 hs hρ₁ ha
    have hC₂B : C₂ ≤ Z ⊔ B := by
      refine hC₂le.trans (sup_le le_sup_left (hle.trans ?_))
      exact le_rfl
    have hCg : conjSubgroup c B ≤ Z ⊔ B := by
      have h1 : conjSubgroup z C₂ ≤ conjSubgroup z (Z ⊔ B) := hcmono z hC₂B
      have h2 : conjSubgroup z C₂ = conjSubgroup c B := by
        rw [hC₂, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
      rw [h2, sup_comm, hBZc z hzBZ] at h1
      rwa [sup_comm] at h1
    obtain ⟨p, hp, hpe⟩ := hc.exists_conj_of_le_ZB hCtxc hCg
    apply hcN
    have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
    rw [← conjSubgroup_eq_self_iff, conjSubgroup_sup95, hZc c hcM, ← hpe]
    calc conjSubgroup p B ⊔ Z = conjSubgroup p B ⊔ conjSubgroup p Z := by rw [hZc p hpM]
      _ = conjSubgroup p (B ⊔ Z) := (conjSubgroup_sup95 p B Z).symm
      _ = B ⊔ Z := hc.conj_sup_Z_of_mem_Q hp
  have hcount := C.card_inf_two_points hs h1R hρ₁ hind
  rw [hcard, hfinal]
  exact hcount

end Final

end HS9

end CFSG.RankThree.GF2n.Stroth80
