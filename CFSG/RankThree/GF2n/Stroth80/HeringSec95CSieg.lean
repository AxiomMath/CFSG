module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COrth
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open Module

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {Γ : Type*} [Group Γ]

structure Siegel (B : LinearMap.BilinForm K E) (Qf : E → K) (α : Γ →* (E ≃ₗ[K] E))
    (U : Submodule K E) (b₀ : E) : Prop where
  iso : ∀ g e, Qf (α g e) = Qf e
  invol : ∀ g e, α g (α g e) = e
  sing : ∀ u ∈ U, Qf u = 0
  perp : ∀ e, (∀ u ∈ U, B u e = 0) → e ∈ U
  mem : b₀ ∈ U
  ne : b₀ ≠ 0
  fix : ∀ g, α g b₀ = b₀
  act : ∀ g, ∀ u ∈ U, ∃ c : K, α g u = u + c • b₀

section Basic

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {α : Γ →* (E ≃ₗ[K] E)}
  {U : Submodule K E} {b₀ : E} (hQ : IsQuadSpace B Qf) (hS : Siegel B Qf α U b₀)
include hQ hS

theorem Siegel.selfadj (g : Γ) (e e' : E) : B (α g e) e' = B e (α g e') := by
  have h := hQ.B_iso (α g) (hS.iso g) e (α g e')
  rw [hS.invol g e'] at h
  exact h

theorem Siegel.isotropic {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U) : B u u' = 0 := by
  have h1 := hQ.Qf_add u u'
  rw [hS.sing _ (U.add_mem hu hu'), hS.sing u hu, hS.sing u' hu'] at h1
  linear_combination -h1

theorem Siegel.form_symm (g : Γ) (e e' : E) :
    B e (α g e' - e') = B (α g e - e) e' := by
  rw [map_sub, ← hS.selfadj hQ g e e', LinearMap.map_sub₂]

theorem Siegel.sub_mem_U (g : Γ) {e : E} (he : B b₀ e = 0) : α g e - e ∈ U := by
  apply hS.perp
  intro u hu
  obtain ⟨c, hc⟩ := hS.act g u hu
  have h1 : B u (α g e) = B (α g u) e := (hS.selfadj hQ g u e).symm
  rw [map_sub, h1, hc, LinearMap.map_add₂, LinearMap.map_smul₂, he]
  simp

theorem Siegel.form_alt (g : Γ) {e : E} (he : B b₀ e = 0) : B e (α g e - e) = 0 := by
  have h := hQ.Qf_add e (α g e - e)
  rw [add_sub_cancel, hS.iso g e, hS.sing _ (hS.sub_mem_U hQ g he)] at h
  linear_combination -h

theorem Siegel.form_mul (g h : Γ) {e e' : E} (he : B b₀ e = 0) (he' : B b₀ e' = 0) :
    B e (α (g * h) e' - e') = B e (α g e' - e') + B e (α h e' - e') := by
  have e1 : α (g * h) e' - e' = (α g e' - e') + (α h e' - e') +
      (α g (α h e' - e') - (α h e' - e')) := by
    rw [map_mul]
    simp only [LinearEquiv.mul_apply, map_sub]
    abel
  have h1 : B e (α g (α h e' - e') - (α h e' - e')) = 0 := by
    rw [hS.form_symm hQ g e _]
    exact hS.isotropic hQ (hS.sub_mem_U hQ g he) (hS.sub_mem_U hQ h he')
  rw [e1, map_add, map_add, h1, add_zero]

end Basic

section TwoMod

theorem exists_pair_span {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (h : finrank K V ≤ 2) : ∃ x y : V, ∀ v : V, ∃ a b : K, v = a • x + b • y := by
  rcases (by omega : finrank K V = 0 ∨ finrank K V = 1 ∨ finrank K V = 2) with h0 | h1 | h2
  · refine ⟨0, 0, fun v => ⟨0, 0, ?_⟩⟩
    have : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  · let bs := Module.finBasisOfFinrankEq K V h1
    refine ⟨bs 0, 0, fun v => ⟨bs.repr v 0, 0, ?_⟩⟩
    have := bs.sum_repr v
    rw [Fin.sum_univ_one] at this
    rw [zero_smul, add_zero]
    exact this.symm
  · let bs := Module.finBasisOfFinrankEq K V h2
    refine ⟨bs 0, bs 1, fun v => ⟨bs.repr v 0, bs.repr v 1, ?_⟩⟩
    have := bs.sum_repr v
    rw [Fin.sum_univ_two] at this
    exact this.symm

theorem exists_two_mod {P S : Submodule K E} (hSP : S ≤ P)
    (hdim : finrank K P ≤ finrank K S + 2) :
    ∃ e₁ ∈ P, ∃ e₂ ∈ P, ∀ p ∈ P, ∃ a b : K, p - a • e₁ - b • e₂ ∈ S := by
  classical
  let S' : Submodule K P := S.comap P.subtype
  have hS'dim : finrank K S' = finrank K S :=
    (Submodule.comapSubtypeEquivOfLe hSP).finrank_eq
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S'
  have hTdim : finrank K T ≤ 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hT
    omega
  obtain ⟨x, y, hxy⟩ := exists_pair_span (K := K) hTdim
  refine ⟨((x : P) : E), (x : P).2, ((y : P) : E), (y : P).2, fun p hp => ?_⟩
  have hp' : (⟨p, hp⟩ : P) ∈ S' ⊔ T := by
    rw [hT.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hp'
  obtain ⟨a, b, hab⟩ := hxy ⟨t, ht⟩
  refine ⟨a, b, ?_⟩
  have h1 : ((s : P) : E) + ((t : P) : E) = p := congrArg (fun z : P => (z : E)) hst
  have h2 : ((t : P) : E) = a • ((x : P) : E) + b • ((y : P) : E) := by
    have := congrArg (fun z : T => ((z : P) : E)) hab
    simpa using this
  have h3 : p - a • ((x : P) : E) - b • ((y : P) : E) = ((s : P) : E) := by
    rw [← h1, h2]
    abel
  rw [h3]
  exact hs

end TwoMod

section Pigeon

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {α : Γ →* (E ≃ₗ[K] E)}
  {U : Submodule K E} {b₀ : E} (hQ : IsQuadSpace B Qf) (hS : Siegel B Qf α U b₀)

omit hQ hS in
theorem mem_perp_iff {e : E} :
    e ∈ B.orthogonal (Submodule.span K {b₀}) ↔ B b₀ e = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact h b₀ (Submodule.mem_span_singleton_self b₀)
  · intro h y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    show B (c • b₀) e = 0
    rw [LinearMap.map_smul₂, h, smul_zero]

include hQ hS

theorem Siegel.act_perp_of_form_zero (g : Γ)
    (hg : ∀ e e', B b₀ e = 0 → B b₀ e' = 0 → B e (α g e' - e') = 0) {e' : E}
    (he' : B b₀ e' = 0) : ∃ c : K, α g e' = e' + c • b₀ := by
  have hrefl : B.IsRefl := LinearMap.BilinForm.IsAlt.isRefl hQ.alt
  have hmem : α g e' - e' ∈ B.orthogonal (B.orthogonal (Submodule.span K {b₀})) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hg y e' ((mem_perp_iff (B := B) (b₀ := b₀)).mp hy) he'
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ.nondegenerate hrefl] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, by rw [hc]; abel⟩

theorem exists_kernel_subgroup [Finite K] (G₂ : Subgroup Γ) (S : Submodule K E)
    (hSP : ∀ s ∈ S, B b₀ s = 0)
    (hdim : finrank K (B.orthogonal (Submodule.span K {b₀})) ≤ finrank K S + 2)
    (hS0 : ∀ g ∈ G₂, ∀ s ∈ S, ∀ e, B b₀ e = 0 → B s (α g e - e) = 0) :
    ∃ C : Subgroup Γ, C ≤ G₂ ∧ C.relIndex G₂ ≤ Nat.card K ∧
      ∀ g ∈ C, ∀ e e', B b₀ e = 0 → B b₀ e' = 0 → B e (α g e' - e') = 0 := by
  classical
  have hSP' : S ≤ B.orthogonal (Submodule.span K {b₀}) := fun s hs =>
    (mem_perp_iff (B := B) (b₀ := b₀)).mpr (hSP s hs)
  obtain ⟨e₁, he₁, e₂, he₂, hdec⟩ := exists_two_mod hSP' hdim
  have he₁0 : B b₀ e₁ = 0 := (mem_perp_iff (B := B) (b₀ := b₀)).mp he₁
  have he₂0 : B b₀ e₂ = 0 := (mem_perp_iff (B := B) (b₀ := b₀)).mp he₂
  let c : G₂ → K := fun g => B e₁ (α (g : Γ) e₂ - e₂)
  have hc : ∀ g g' : G₂, c (g * g') = c g + c g' := fun g g' =>
    hS.form_mul hQ (g : Γ) (g' : Γ) he₁0 he₂0
  have hc1 : c 1 = 0 := by simp [c]
  let f : G₂ →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd (c g)
      map_one' := by simp [hc1]
      map_mul' := fun g g' => by simp [hc] }
  refine ⟨f.ker.map G₂.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact g.2
  · have hsub : (f.ker.map G₂.subtype).subgroupOf G₂ = f.ker := by
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective f.ker
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker f]
    haveI : Finite (Multiplicative K) := inferInstanceAs (Finite K)
    calc Nat.card f.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group _
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
  · rintro _ ⟨g, hg, rfl⟩ e e' he he'
    have hcg : c g = 0 := by
      have hf : f g = 1 ↔ c g = 0 := by
        show Multiplicative.ofAdd (c g) = 1 ↔ _
        exact ofAdd_eq_one
      exact hf.mp hg
    set γ : Γ := (g : Γ) with hγ
    have hgmem : γ ∈ G₂ := g.2
    let Φ : E →ₗ[K] E →ₗ[K] K := B.compl₂ ((α γ).toLinearMap - LinearMap.id)
    have hΦ : ∀ x y, Φ x y = B x (α γ y - y) := fun x y => by simp [Φ]
    have h11 : Φ e₁ e₁ = 0 := by rw [hΦ]; exact hS.form_alt hQ γ he₁0
    have h22 : Φ e₂ e₂ = 0 := by rw [hΦ]; exact hS.form_alt hQ γ he₂0
    have h12 : Φ e₁ e₂ = 0 := by rw [hΦ]; exact hcg
    have h21 : Φ e₂ e₁ = 0 := by
      rw [hΦ, hS.form_symm hQ γ e₂ e₁, hQ.B_neg e₁ (α γ e₂ - e₂)]
      have : B e₁ (α γ e₂ - e₂) = 0 := hcg
      rw [this, neg_zero]
    have hSl : ∀ s ∈ S, ∀ y, B b₀ y = 0 → Φ s y = 0 := fun s hs y hy => by
      rw [hΦ]; exact hS0 γ hgmem s hs y hy
    have hSr : ∀ y, B b₀ y = 0 → ∀ x ∈ S, Φ y x = 0 := fun y hy x hx => by
      rw [hΦ, hS.form_symm hQ γ y x, hQ.B_neg x (α γ y - y), hS0 γ hgmem x hx y hy, neg_zero]
    have key : ∀ (a b a' b' : K) (s s' : E), s ∈ S → s' ∈ S →
        Φ (a • e₁ + b • e₂ + s) (a' • e₁ + b' • e₂ + s') = 0 := by
      intro a b a' b' s s' hs hs'
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [h11, h12, h21, h22, hSr e₁ he₁0 s' hs', hSr e₂ he₂0 s' hs', hSl s hs e₁ he₁0,
        hSl s hs e₂ he₂0, hSl s hs s' (hSP s' hs')]
      ring
    obtain ⟨a, b, hs⟩ := hdec e ((mem_perp_iff (B := B) (b₀ := b₀)).mpr he)
    obtain ⟨a', b', hs'⟩ := hdec e' ((mem_perp_iff (B := B) (b₀ := b₀)).mpr he')
    have hx : e = a • e₁ + b • e₂ + (e - a • e₁ - b • e₂) := by abel
    have hx' : e' = a' • e₁ + b' • e₂ + (e' - a' • e₁ - b' • e₂) := by abel
    show B e (α γ e' - e') = 0
    rw [← hΦ]
    calc Φ e e' = Φ (a • e₁ + b • e₂ + (e - a • e₁ - b • e₂))
          (a' • e₁ + b' • e₂ + (e' - a' • e₁ - b' • e₂)) := by rw [← hx, ← hx']
      _ = 0 := key a b a' b' _ _ hs hs'

end Pigeon

section Fix

def fixSpace (α : Γ →* (E ≃ₗ[K] E)) (H : Subgroup Γ) : Submodule K E where
  carrier := {e | ∀ g ∈ H, α g e = e}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun c e he g hg => by rw [map_smul, he g hg]

theorem mem_fixSpace {α : Γ →* (E ≃ₗ[K] E)} {H : Subgroup Γ} {e : E} :
    e ∈ fixSpace α H ↔ ∀ g ∈ H, α g e = e := Iff.rfl

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {α : Γ →* (E ≃ₗ[K] E)}
  {U : Submodule K E} {b₀ : E} (hQ : IsQuadSpace B Qf) (hS : Siegel B Qf α U b₀)
include hQ hS

theorem Siegel.exists_dual : ∃ a₀ : E, B b₀ a₀ = 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∀ y, B b₀ y = 0 := by
    intro y
    by_contra hy
    apply hcon ((B b₀ y)⁻¹ • y)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  exact hS.ne (hQ.nondeg b₀ h1)

theorem Siegel.sub_mul (g h : Γ) {u : E} (hu : u ∈ U) :
    α (g * h) u - u = (α g u - u) + (α h u - u) := by
  obtain ⟨c, hc⟩ := hS.act h u hu
  rw [map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [hc, map_add, map_smul, hS.fix g]
  abel

theorem Siegel.sub_eq_smul (g : Γ) {u : E} (hu : u ∈ U) {a₀ : E} (ha₀ : B b₀ a₀ = 1) :
    α g u - u = B (α g u - u) a₀ • b₀ := by
  obtain ⟨c, hc⟩ := hS.act g u hu
  have : α g u - u = c • b₀ := by rw [hc]; abel
  rw [this, LinearMap.map_smul₂, ha₀, smul_eq_mul, mul_one]

theorem Siegel.finrank_fix_le [Finite K] (Γ₁ : Subgroup Γ) (m : ℕ)
    (hfaith : ∀ g ∈ Γ₁, (∀ u ∈ U, α g u = u) → ∀ e, α g e = e)
    (hcard : Nat.card K ^ m ≤ α.ker.relIndex Γ₁) :
    m + finrank K ↥(U ⊓ fixSpace α Γ₁) ≤ finrank K U := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.exists_dual hQ
  let C' : Submodule K E := U ⊓ fixSpace α Γ₁
  have hC'U : C' ≤ U := inf_le_left
  let C'' : Submodule K U := C'.comap U.subtype
  have hC''dim : finrank K C'' = finrank K C' :=
    (Submodule.comapSubtypeEquivOfLe hC'U).finrank_eq
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl C''
  have hsum : finrank K C'' + finrank K D = finrank K U :=
    Submodule.finrank_add_eq_of_isCompl hD
  let lam : Γ → (D →ₗ[K] K) := fun g =>
    ((B.flip a₀).comp ((α g).toLinearMap - LinearMap.id)).comp (U.subtype.comp D.subtype)
  have hlam : ∀ g (d : D), lam g d = B (α g ((d : U) : E) - ((d : U) : E)) a₀ := fun g d => by
    simp [lam]
  have hlam_mul : ∀ g h, lam (g * h) = lam g + lam h := by
    intro g h
    ext d
    rw [LinearMap.add_apply, hlam, hlam, hlam,
      hS.sub_mul hQ g h (d : U).2, LinearMap.map_add₂]
  have hlam_one : lam 1 = 0 := by
    ext d
    rw [hlam]
    simp
  let Λ : Γ₁ →* Multiplicative (Module.Dual K D) :=
    { toFun := fun g => Multiplicative.ofAdd (lam (g : Γ))
      map_one' := by simp [hlam_one]
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (lam ((g : Γ) * (h : Γ))) = _
        rw [hlam_mul]
        rfl }
  have hker : Λ.ker ≤ α.ker.subgroupOf Γ₁ := by
    intro g hg
    have hg0 : lam (g : Γ) = 0 := by
      have : Λ g = 1 := hg
      exact ofAdd_eq_one.mp this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    refine LinearEquiv.ext fun e => ?_
    refine hfaith (g : Γ) g.2 (fun u hu => ?_) e
    have hu' : (⟨u, hu⟩ : U) ∈ C'' ⊔ D := by rw [hD.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hu'
    have h1 : ((c : U) : E) + ((d : U) : E) = u := congrArg (fun z : U => (z : E)) hcd
    have hc1 : α (g : Γ) ((c : U) : E) = ((c : U) : E) := hc.2 (g : Γ) g.2
    have hd1 : α (g : Γ) ((d : U) : E) = ((d : U) : E) := by
      have h2 : B (α (g : Γ) ((d : U) : E) - ((d : U) : E)) a₀ = 0 := by
        have := LinearMap.congr_fun hg0 ⟨d, hd⟩
        rw [hlam] at this
        exact this
      have h3 := hS.sub_eq_smul hQ (g : Γ) (d : U).2 ha₀
      rw [h2, zero_smul] at h3
      exact sub_eq_zero.mp h3
    rw [← h1, map_add, hc1, hd1]
  have hfin : Finite (Module.Dual K D) := Module.finite_of_finite K
  haveI : Finite (Multiplicative (Module.Dual K D)) := hfin
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hle : α.ker.relIndex Γ₁ ≤ Nat.card K ^ finrank K D := by
    have h1 : (α.ker.subgroupOf Γ₁).index ∣ Λ.ker.index := Subgroup.index_dvd_of_le hker
    have h2 : Λ.ker.index = Nat.card Λ.range := Subgroup.index_ker Λ
    have h3 : Nat.card Λ.range ≤ Nat.card (Multiplicative (Module.Dual K D)) :=
      Subgroup.card_le_card_group _
    have h4 : Nat.card (Multiplicative (Module.Dual K D)) = Nat.card K ^ finrank K D := by
      rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := K),
        Subspace.dual_finrank_eq]
    have h5 : Λ.ker.index ≠ 0 := by
      rw [h2]
      exact Nat.card_pos.ne'
    have h6 : (α.ker.subgroupOf Γ₁).index ≤ Λ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h1
    rw [Subgroup.relIndex]
    omega
  have hCC : finrank K ↥(U ⊓ fixSpace α Γ₁) = finrank K C'' := hC''dim.symm
  have hm : m ≤ finrank K D := (Nat.pow_le_pow_iff_right hq).mp (hcard.trans hle)
  omega

theorem Siegel.exists_rank_two [Finite K] (Γ₁ G₂ : Subgroup Γ)
    (hCU : finrank K ↥(U ⊓ fixSpace α Γ₁) ≤ 3)
    (hfix : ∀ g ∈ G₂, ∀ e, ∀ y ∈ Γ₁, α y (α g e - e) = α g e - e)
    (hcard : ∀ C : Subgroup Γ, C ≤ G₂ → (∀ g ∈ C, α g = 1) → Nat.card K < C.relIndex G₂) :
    ∃ g ∈ G₂, α g ≠ 1 ∧ ∀ e, B b₀ e = 0 → ∃ c : K, α g e = e + c • b₀ := by
  classical
  let C' : Submodule K E := U ⊓ fixSpace α Γ₁
  let S : Submodule K E := B.orthogonal C'
  have hb₀C : b₀ ∈ C' := ⟨hS.mem, fun g _ => hS.fix g⟩
  have hSP : ∀ s ∈ S, B b₀ s = 0 := fun s hs =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hs) b₀ hb₀C
  have hdimS : finrank K S = finrank K E - finrank K C' :=
    LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate C'
  have hC'le : finrank K C' ≤ finrank K E := Submodule.finrank_le C'
  have hdimP : finrank K (B.orthogonal (Submodule.span K {b₀})) = finrank K E - 1 := by
    have := LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate (Submodule.span K {b₀})
    rw [finrank_span_singleton hS.ne] at this
    exact this
  have hCU' : finrank K C' ≤ 3 := hCU
  have hdim : finrank K (B.orthogonal (Submodule.span K {b₀})) ≤ finrank K S + 2 := by omega
  have hS0 : ∀ g ∈ G₂, ∀ s ∈ S, ∀ e, B b₀ e = 0 → B s (α g e - e) = 0 := by
    intro g hg s hs e he
    have hmem : α g e - e ∈ C' := ⟨hS.sub_mem_U hQ g he, fun y hy => hfix g hg e y hy⟩
    have h1 : B (α g e - e) s = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hs) _ hmem
    rw [hQ.B_neg (α g e - e) s, h1, neg_zero]
  obtain ⟨C, hCG, hCidx, hCform⟩ := exists_kernel_subgroup hQ hS G₂ S hSP hdim hS0
  have hex : ∃ g ∈ C, α g ≠ 1 := by
    by_contra h
    push Not at h
    have := hcard C hCG h
    omega
  obtain ⟨g, hg, hne⟩ := hex
  exact ⟨g, hCG hg, hne, fun e he => hS.act_perp_of_form_zero hQ g (hCform g hg) he⟩

end Fix

end CFSG.RankThree.GF2n.Stroth80.HS9
