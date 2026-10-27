module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


@[expose] def StatedOmegaPlusFourPerfectStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 4 ≤ Nat.card K →
    ⁅StatedOmega (StatedQuadPlus 4 K), StatedOmega (StatedQuadPlus 4 K)⁆ =
      StatedOmega (StatedQuadPlus 4 K)

@[expose] def QuadraticPlusTypeStatement : Prop :=
  ∀ (H : Type) [Group H] (K : Type) [Field K] [Finite K] (QF V : Subgroup H) (γ : H → K)
    (M₀ : Tim79.QuadModel QF V K γ) (Γ : Subgroup (M₀.E ≃ₗ[K] M₀.E)),
    CharP K 2 → Module.finrank K M₀.E = 8 →
    Γ ≤ TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm →
    Nonempty (Γ ≃* StatedOmega (StatedQuadPlus 4 K)) →
    ∃ e : M₀.E ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K), ∀ v, quadPlus 4 K (e v) = M₀.Qf v

@[expose] def Sec714ModelStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 12 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
    ∃ (γ : Mbar M Q → K) (M₀ : Tim79.QuadModel (bar M Q (hc.CN t)) (bar M Q Z0) K γ)
      (ψ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (M₀.E ≃ₗ[K] M₀.E)),
      Tim79.GammaReg (bar M Q (hc.CN t)) (bar M Q Z0) γ ∧ CharP K 2 ∧
      Module.finrank K M₀.E = 8 ∧
      (∀ g : ↥(bar M Q (Rt M (LB M Q B) t)), ∀ x ∈ bar M Q (hc.CN t),
        M₀.π ((g : Mbar M Q) * x * (g : Mbar M Q)⁻¹) = ψ g (M₀.π x)) ∧
      (∀ g : ↥(bar M Q (Rt M (LB M Q B) t)), ∀ v, M₀.Qf (ψ g v) = M₀.Qf v) ∧
      (∀ g : ↥(bar M Q (Rt M (LB M Q B) t)), ψ g = 1 ↔ (g : Mbar M Q) ∈ bar M Q (hc.CN t))

section Transport

variable {K : Type} [Field K]

@[expose] def stroth714ConjEquiv {E F : Type} [AddCommGroup E] [Module K E] [AddCommGroup F]
    [Module K F] (e : E ≃ₗ[K] F) : (E ≃ₗ[K] E) ≃* (F ≃ₗ[K] F) where
  toFun T := e.symm.trans (T.trans e)
  invFun T := e.trans (T.trans e.symm)
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp
  map_mul' T S := by ext x; simp [mul_assoc]

theorem map_orthogonalGroup_stroth714Conj {E F : Type} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (Q : QuadraticForm K E) (Q' : QuadraticForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ v, Q' (e v) = Q v) :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map (stroth714ConjEquiv e).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := by
  ext A
  constructor
  · rintro ⟨T, hT, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    have hTv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hT (e.symm v)
    change Q' (e (T (e.symm v))) = Q' v
    rw [he, hTv, ← he (e.symm v)]
    simp
  · intro hA
    refine ⟨(stroth714ConjEquiv e).symm A, ?_, by simp⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    have hAv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hA (e v)
    change Q (e.symm (A (e v))) = Q v
    rw [← he (e.symm (A (e v))), LinearEquiv.apply_symm_apply, hAv, he]

theorem natCard_statedOmega_eq_omega (n : ℕ) (Q₀ : (Fin n ⊕ Fin n → K) → K)
    (h : ⇑(quadPlus n K) = Q₀) :
    Nat.card ↥(StatedOmega Q₀) = Nat.card ↥(⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆) := by
  rw [statedOmega_eq_comap h]
  have key : Subgroup.comap (toLinEquiv (Fin n ⊕ Fin n) K).toMonoidHom
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆ =
      Subgroup.map (toLinEquiv (Fin n ⊕ Fin n) K).symm.toMonoidHom
        ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆ := by
    ext x
    constructor
    · intro hx
      exact ⟨(toLinEquiv (Fin n ⊕ Fin n) K) x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [key]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem commutator_eq_of_mulEquiv {A B : Type} [Group A] [Group B] (S : Subgroup A)
    (T : Subgroup B) (f : ↥S ≃* ↥T) (hT : ⁅T, T⁆ = T) : ⁅S, S⁆ = S := by
  have hmapT : Subgroup.map T.subtype (⊤ : Subgroup ↥T) = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapS : Subgroup.map S.subtype (⊤ : Subgroup ↥S) = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapf : Subgroup.map f.toMonoidHom (⊤ : Subgroup ↥S) = ⊤ := by simp
  have hTtop : ⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := T.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hmapT]
    exact hT
  have hStop : ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := f.toMonoidHom) (MulEquiv.injective f)
    rw [Subgroup.map_commutator, hmapf, hTtop]
  have h := congrArg (Subgroup.map S.subtype) hStop
  rw [Subgroup.map_commutator, hmapS] at h
  exact h

theorem finite_linEquiv_self {V : Type} [AddCommGroup V] [Module K V] [Finite V] [Finite K] :
    Finite (V ≃ₗ[K] V) :=
  Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V))
    (fun a b h => LinearEquiv.ext fun x => congrFun h x)

end Transport

theorem exists_hyperbolic_of_iso {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
    (Q : E → K) (e : E ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (he : ∀ v, quadPlus 4 K (e v) = Q v) :
    ∃ S₁ S₂ : Submodule K E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, Q x = 0) ∧ ∀ x ∈ S₂, Q x = 0 := by
  refine ⟨LinearMap.ker (LinearMap.funLeft K K (Sum.inr : Fin 4 → Fin 4 ⊕ Fin 4) ∘ₗ
      e.toLinearMap), LinearMap.ker (LinearMap.funLeft K K (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 4) ∘ₗ
      e.toLinearMap), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 : e x ∘ Sum.inr = 0 := hx1
    have h2 : e x ∘ Sum.inl = 0 := hx2
    apply e.injective
    rw [map_zero]
    funext s
    rcases s with i | i
    · exact congrFun h2 i
    · exact congrFun h1 i
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hdec : e x = Sum.elim (fun i => e x (Sum.inl i)) (fun _ => 0) +
        Sum.elim (fun _ => 0) (fun i => e x (Sum.inr i)) := by
      funext s
      rcases s with i | i <;> simp
    refine Submodule.mem_sup.mpr ⟨e.symm (Sum.elim (fun i => e x (Sum.inl i)) (fun _ => 0)),
      ?_, e.symm (Sum.elim (fun _ => 0) (fun i => e x (Sum.inr i))), ?_, ?_⟩
    · show (LinearMap.funLeft K K (Sum.inr : Fin 4 → Fin 4 ⊕ Fin 4) ∘ₗ e.toLinearMap)
        (e.symm _) = 0
      funext i
      simp
    · show (LinearMap.funLeft K K (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 4) ∘ₗ e.toLinearMap)
        (e.symm _) = 0
      funext i
      simp
    · rw [← map_add, ← hdec]
      simp
  · intro x hx
    have h : e x ∘ Sum.inr = 0 := hx
    rw [← he x, quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [this]
  · intro x hx
    have h : e x ∘ Sum.inl = 0 := hx
    rw [← he x, quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [this]

theorem inducesOmega_of_range {H : Type} [Group H] {P Z : Subgroup H} {K : Type} [Field K]
    [Finite K] {γ : H → K} (M₀ : Tim79.QuadModel P Z K γ) (X : Subgroup H)
    (ψ : ↥X →* (M₀.E ≃ₗ[K] M₀.E))
    (hcomp : ∀ g : ↥X, ∀ x ∈ P, M₀.π ((g : H) * x * (g : H)⁻¹) = ψ g (M₀.π x))
    (hiso : ∀ g : ↥X, ∀ v, M₀.Qf (ψ g v) = M₀.Qf v)
    (hchar : CharP K 2) (hfin : Module.finrank K M₀.E = 8)
    (hperf : ⁅StatedOmega (StatedQuadPlus 4 K), StatedOmega (StatedQuadPlus 4 K)⁆ =
      StatedOmega (StatedQuadPlus 4 K))
    (hPlus : QuadraticPlusTypeStatement)
    (hγ : Nonempty (ψ.range ≃* StatedOmega (StatedQuadPlus 4 K))) :
    InducesOmega M₀ X := by
  classical
  have hΓO : ψ.range ≤ TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm := by
    rintro _ ⟨g, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => hiso g v
  obtain ⟨e, he⟩ := hPlus H K P Z γ M₀ ψ.range hchar hfin hΓO hγ
  have hOc := map_orthogonalGroup_stroth714Conj M₀.toQuadraticForm (quadPlus 4 K) e
    (fun v => he v)
  set c := stroth714ConjEquiv e with hc_def
  have hOmega : (Satz5.omegaOf M₀).map c.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
    rw [Satz5.omegaOf, Subgroup.map_commutator, hOc]
  have hperfΓ : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    obtain ⟨f⟩ := hγ
    exact commutator_eq_of_mulEquiv _ _ f hperf
  set Γ' := ψ.range.map c.toMonoidHom with hΓ'
  have hΓ'O : Γ' ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
    rw [← hOc]; exact Subgroup.map_mono hΓO
  have hΓ'perf : ⁅Γ', Γ'⁆ = Γ' := by
    rw [hΓ', ← Subgroup.map_commutator, hperfΓ]
  have hle : Γ' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
    rw [← hΓ'perf]; exact Subgroup.commutator_mono hΓ'O hΓ'O
  obtain ⟨φ0⟩ := hγ
  have hcardΓ : Nat.card ↥Γ' = Nat.card ↥(StatedOmega (StatedQuadPlus 4 K)) := by
    rw [hΓ', Subgroup.card_map_of_injective c.injective]
    exact Nat.card_congr φ0.toEquiv
  have hcardO := natCard_statedOmega_eq_omega 4 (StatedQuadPlus 4 K) (coe_quadPlus 4 K)
  haveI : Finite ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := finite_linEquiv_self
  have heq : Γ' = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [← hcardO, hcardΓ])
  intro T hT
  have hcT : c T ∈ Γ' := by
    rw [heq, ← hOmega]
    exact Subgroup.mem_map_of_mem _ hT
  obtain ⟨g, hg, hgT⟩ := Subgroup.mem_map.mp hcT
  obtain ⟨x0, hx0⟩ := MonoidHom.mem_range.mp hg
  have hgT' : g = T := c.injective hgT
  refine ⟨(x0 : H), x0.2, fun x hx => ?_⟩
  rw [hcomp x0 x hx, hx0, hgT']

theorem false_of_range_model {H : Type} [Group H] {P Z X : Subgroup H} {K : Type} [Field K]
    [Finite K] {γ : H → K} (M₀ : Tim79.QuadModel P Z K γ) (R : Tim79.GammaReg P Z γ)
    (hchar : CharP K 2) (hfin : Module.finrank K M₀.E = 8) (hK : 2 < Nat.card K)
    (hnorm : ∀ g ∈ X, ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hcent : ∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z)
    (ψ : ↥X →* (M₀.E ≃ₗ[K] M₀.E))
    (hcomp : ∀ g : ↥X, ∀ x ∈ P, M₀.π ((g : H) * x * (g : H)⁻¹) = ψ g (M₀.π x))
    (hiso : ∀ g : ↥X, ∀ v, M₀.Qf (ψ g v) = M₀.Qf v)
    (hker : ∀ g : ↥X, ψ g = 1 → (g : H) ∈ P)
    (hperf : ⁅StatedOmega (StatedQuadPlus 4 K), StatedOmega (StatedQuadPlus 4 K)⁆ =
      StatedOmega (StatedQuadPlus 4 K))
    (hPlus : QuadraticPlusTypeStatement)
    (hγ : Nonempty (ψ.range ≃* StatedOmega (StatedQuadPlus 4 K))) : False := by
  classical
  haveI := hchar
  have hΓO : ψ.range ≤ TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm := by
    rintro _ ⟨g, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => hiso g v
  obtain ⟨e, he⟩ := hPlus H K P Z γ M₀ ψ.range hchar hfin hΓO hγ
  obtain ⟨S₁, S₂, hS, h1, h2⟩ := exists_hyperbolic_of_iso M₀.Qf e he
  have hΩ := inducesOmega_of_range M₀ X ψ hcomp hiso hchar hfin hperf hPlus hγ
  refine beisiegel_satz5 M₀ R hK ⟨S₁, S₂, hS, h1, h2⟩ (by omega) hnorm hcent ?_ hΩ
  intro g hg hπ
  have hgX : ψ ⟨g, hg⟩ = 1 := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨x, hxP, rfl⟩ := M₀.π_surj v
    show ψ ⟨g, hg⟩ (M₀.π x) = M₀.π x
    rw [← hcomp ⟨g, hg⟩ x hxP]
    exact hπ x hxP
  exact ⟨g, hker ⟨g, hg⟩ hgX, fun x _ => rfl⟩

theorem step714NotTwelve_of_model (hModel : Sec714ModelStatement)
    (hPerf : StatedOmegaPlusFourPerfectStatement) (hPlus : QuadraticPlusTypeStatement) :
    Step714NotTwelveStatement := by
  intro G _ _ M Q Z B hc n t hs hn4 hn12
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (hc.Q_le_Rt ht)
  have hQCN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  have hRM : Rt M (LB M Q B) t ≤ M := Rt_le_M (Ctx.LB_le_M hc) t
  have hn4' := hn4
  obtain ⟨K, hKf, hKfin, hcard, φ, hrange, hkerφ, -⟩ := hn4'
  obtain ⟨γ, M₀, ψ, hR, hchar, hdim, hcomp, hiso, hker'⟩ :=
    hModel G M Q Z B hc n t hs hn4 hn12 Z0 hZ0 K hcard
  have hCNn : ∀ g ∈ Rt M (LB M Q B) t, ∀ c ∈ hc.CN t, g * c * g⁻¹ ∈ hc.CN t := by
    have hN : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
      rw [← hkerφ]; exact φ.normal_ker
    intro g hg c hcN
    have h := hN.conj_mem ⟨c, hCNR hcN⟩ (Subgroup.mem_subgroupOf.mpr hcN) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hnorm : ∀ g ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ bar M Q (hc.CN t),
      g * x * g⁻¹ ∈ bar M Q (hc.CN t) := by
    intro g hg x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have e : QuotientGroup.mk' (Q.subgroupOf M) r * QuotientGroup.mk' (Q.subgroupOf M) y *
        (QuotientGroup.mk' (Q.subgroupOf M) r)⁻¹ =
          QuotientGroup.mk' (Q.subgroupOf M) (r * y * r⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, mk_mem_bar_iff_sec4 hQCN]
    have hr' : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    have hy' : (y : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hy
    simpa using hCNn _ hr' _ hy'
  have hcent : ∀ g ∈ bar M Q (Rt M (LB M Q B) t), ∀ z ∈ bar M Q Z0, g * z * g⁻¹ = z := by
    intro g hg z hz
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyZ : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hy
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    have hc1 : ⁅(y : G), (r : G)⁆ ∈ Q := hZ0.comm_mem hyZ hrR
    have hc2 : ⁅(r : G), (y : G)⁆ ∈ Q := by
      have h := Q.inv_mem hc1
      rwa [commutatorElement_inv] at h
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⁅r, y⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hc2
    rw [← mul_inv_eq_one]
    have e : QuotientGroup.mk' (Q.subgroupOf M) r * QuotientGroup.mk' (Q.subgroupOf M) y *
        (QuotientGroup.mk' (Q.subgroupOf M) r)⁻¹ * (QuotientGroup.mk' (Q.subgroupOf M) y)⁻¹ =
          QuotientGroup.mk' (Q.subgroupOf M) ⁅r, y⁆ := by
      simp [commutatorElement_def, map_mul, map_inv]
    rw [e, h1]
  let θ0 : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hθ0 : ∀ r : ↥(Rt M (LB M Q B) t), θ0 r ∈ bar M Q (Rt M (LB M Q B) t) := by
    intro r
    exact Subgroup.mem_map.mpr ⟨⟨r, hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let θ : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := θ0.codRestrict _ hθ0
  have hθsurj : Function.Surjective θ := by
    intro g
    obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp g.2
    exact ⟨⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩, Subtype.ext hrg⟩
  have key : ∀ r : ↥(Rt M (LB M Q B) t), ψ (θ r) = 1 ↔ (r : G) ∈ hc.CN t := by
    intro r
    rw [hker' (θ r)]
    exact mk_mem_bar_iff_sec4 hQCN (⟨(r : G), hRM r.2⟩ : M)
  let ψθ := ψ.comp θ
  have hker_eq : ψθ.ker = φ.ker := by
    ext r
    rw [MonoidHom.mem_ker, hkerφ, Subgroup.mem_subgroupOf]
    exact key r
  have hrange_eq : ψθ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨θ r, rfl⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨r, hr⟩ := hθsurj g
      exact ⟨r, by simp [ψθ, hr]⟩
  have hγ : Nonempty (ψ.range ≃* StatedOmega (StatedQuadPlus 4 K)) := by
    have e1 := QuotientGroup.quotientKerEquivRange ψθ
    have e2 := QuotientGroup.quotientKerEquivRange φ
    have e3 := QuotientGroup.quotientMulEquivOfEq hker_eq
    exact ⟨((MulEquiv.subgroupCongr hrange_eq).symm.trans (e1.symm.trans (e3.trans e2))).trans
      (MulEquiv.subgroupCongr hrange)⟩
  have hK : 2 < Nat.card K := by
    rw [hcard]
    have := hc.hyp.q4
    omega
  have hperf := hPerf K (by rw [hcard]; exact hc.hyp.q4)
  exact false_of_range_model M₀ hR hchar hdim hK hnorm hcent ψ hcomp hiso
    (fun g hg => (hker' g).mp hg) hperf hPlus hγ

end CFSG.RankThree.GF2n.Stroth80
