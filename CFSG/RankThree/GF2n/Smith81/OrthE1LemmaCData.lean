module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open Module

section QSpaceLemmas

variable {K : Type} [Field K] (S : QSpace K)

theorem QSpace.B_comm [CharP K 2] (e f : S.E) : S.B e f = S.B f e := by
  have h := S.alt (e + f)
  simp only [map_add, LinearMap.add_apply, S.alt, zero_add, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

theorem QSpace.B_isometry {g : S.E ≃ₗ[K] S.E} (hg : g ∈ S.O) (e f : S.E) :
    S.B (g e) (g f) = S.B e f := by
  have h1 := S.Qf_add (g e) (g f)
  have h2 := S.Qf_add e f
  have hg' : ∀ e, S.Qf (g e) = S.Qf e := hg
  rw [← map_add, hg', hg', hg'] at h1
  exact add_left_cancel (h1.symm.trans h2)

theorem QSpace.B_zero_of_ts {V : Submodule K S.E} (hV : S.IsTS V) {v w : S.E} (hv : v ∈ V)
    (hw : w ∈ V) : S.B v w = 0 := by
  have h := S.Qf_add v w
  rw [hV _ (V.add_mem hv hw), hV v hv, hV w hw] at h
  simpa using h.symm

theorem QSpace.mem_Cent_iff (X : Set (S.E ≃ₗ[K] S.E)) (g : S.E ≃ₗ[K] S.E) :
    g ∈ S.Cent X ↔ g ∈ S.O ∧ ∀ x ∈ X, ∀ e, x (g e) = g (x e) := by
  unfold QSpace.Cent
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => forall₂_congr fun x hx => ?_
  constructor
  · intro h e
    exact LinearEquiv.congr_fun h e
  · intro h
    ext e
    exact h e

end QSpaceLemmas

structure LCData {K : Type} [Field K] (S : QSpace K) (V : Submodule K S.E)
    (Xg : Subgroup (S.E ≃ₗ[K] S.E)) where
  O_le : Xg ≤ S.O
  ts : S.IsTS V
  perp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V
  dimV : Module.finrank K V = 4
  dimE : Module.finrank K S.E = 8
  act : ↥Xg → V →ₗ[K] V
  act_coe : ∀ (g : ↥Xg) (v : V), ((act g v : V) : S.E) = (g : S.E ≃ₗ[K] S.E) v
  pf : V →ₗ[K] V →ₗ[K] K
  pf_nondeg : ∀ v, (∀ w, pf v w = 0) → v = 0
  pf_alt : ∀ v, pf v v = 0
  pf_inv : ∀ (g : ↥Xg) (v w : V), pf (act g v) (act g w) = pf v w
  schur : ∀ a : V →ₗ[K] V, (∀ (g : ↥Xg) (v : V), a (act g v) = act g (a v)) →
    ∃ c : K, ∀ v, a v = c • v

namespace LCData

variable {K : Type} [Field K] {S : QSpace K} {V : Submodule K S.E}
  {Xg : Subgroup (S.E ≃ₗ[K] S.E)} (D : LCData S V Xg)

theorem act_inv_act (g : ↥Xg) (v : V) : D.act g⁻¹ (D.act g v) = v := by
  apply Subtype.ext
  rw [D.act_coe, D.act_coe]
  simp

theorem act_act_inv (g : ↥Xg) (v : V) : D.act g (D.act g⁻¹ v) = v := by
  simpa using D.act_inv_act g⁻¹ v

theorem pf_injective : Function.Injective D.pf := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  exact D.pf_nondeg v fun w => by rw [hv]; rfl

@[expose] noncomputable def pfEquiv : V ≃ₗ[K] Module.Dual K V :=
  LinearEquiv.ofBijective D.pf ⟨D.pf_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := K) (V := V)).symm).mp D.pf_injective⟩

@[expose] noncomputable def β0 : S.E →ₗ[K] V :=
  (D.pfEquiv.symm : Module.Dual K V →ₗ[K] V) ∘ₗ (S.B.compl₂ V.subtype)

@[expose] noncomputable def β : S.E →ₗ[K] S.E := V.subtype ∘ₗ D.β0

theorem β_apply (e : S.E) : D.β e = ((D.β0 e : V) : S.E) := rfl

theorem pf_β0 (e : S.E) (w : V) : D.pf (D.β0 e) w = S.B e w := by
  have h : D.pf (D.β0 e) = S.B.compl₂ V.subtype e :=
    D.pfEquiv.apply_symm_apply (S.B.compl₂ V.subtype e)
  rw [h]
  rfl

theorem β0_eq_zero_iff (e : S.E) : D.β0 e = 0 ↔ e ∈ V := by
  constructor
  · intro h
    apply D.perp
    intro v hv
    have := D.pf_β0 e ⟨v, hv⟩
    rw [h] at this
    simpa using this.symm
  · intro he
    apply D.pf_nondeg
    intro w
    rw [D.pf_β0]
    exact S.B_zero_of_ts D.ts he w.2

theorem β_mem (e : S.E) : D.β e ∈ V := (D.β0 e).2

theorem β_kills {v : S.E} (hv : v ∈ V) : D.β v = 0 := by
  rw [β_apply, (D.β0_eq_zero_iff v).2 hv]
  rfl

theorem mem_of_β_eq_zero {e : S.E} (h : D.β e = 0) : e ∈ V :=
  (D.β0_eq_zero_iff e).1 (Subtype.ext h)

theorem β_alt (e : S.E) : S.B e (D.β e) = 0 := by
  have := D.pf_β0 e (D.β0 e)
  rw [D.pf_alt] at this
  exact this.symm

theorem β_β (e : S.E) : D.β (D.β e) = 0 := D.β_kills (D.β_mem e)

theorem betaProps : BetaProps S V D.β where
  range := D.β_mem
  ker := fun _ h => D.mem_of_β_eq_zero h
  kills := fun _ hv => D.β_kills hv
  alt := D.β_alt

theorem β0_act (g : ↥Xg) (e : S.E) :
    D.β0 ((g : S.E ≃ₗ[K] S.E) e) = D.act g (D.β0 e) := by
  have hg : (g : S.E ≃ₗ[K] S.E) ∈ S.O := D.O_le g.2
  rw [← sub_eq_zero]
  apply D.pf_nondeg
  intro w
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero, D.pf_β0]
  have h1 : D.pf (D.act g (D.β0 e)) w = D.pf (D.β0 e) (D.act g⁻¹ w) := by
    conv_lhs => rw [← D.act_act_inv g w]
    exact D.pf_inv g _ _
  rw [h1, D.pf_β0, D.act_coe]
  have h2 := S.B_isometry hg e (((g⁻¹ : ↥Xg) : S.E ≃ₗ[K] S.E) w)
  have h3 : (g : S.E ≃ₗ[K] S.E) ((((g⁻¹ : ↥Xg) : S.E ≃ₗ[K] S.E)) (w : S.E)) = w := by simp
  rw [h3] at h2
  exact h2

theorem β_act (g : ↥Xg) (e : S.E) : D.β ((g : S.E ≃ₗ[K] S.E) e) = (g : S.E ≃ₗ[K] S.E) (D.β e) := by
  rw [β_apply, β_apply, D.β0_act, D.act_coe]

theorem ker_β0 : LinearMap.ker D.β0 = V := by
  ext e
  rw [LinearMap.mem_ker, D.β0_eq_zero_iff]

theorem β0_surjective : Function.Surjective D.β0 := by
  have h := LinearMap.finrank_range_add_finrank_ker D.β0
  rw [D.ker_β0, D.dimE, D.dimV] at h
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [D.dimV]
  omega

theorem schur_β (φ : S.E →ₗ[K] S.E) (hcomm : ∀ (g : ↥Xg) e, φ ((g : S.E ≃ₗ[K] S.E) e) =
    (g : S.E ≃ₗ[K] S.E) (φ e)) (hr : ∀ e, φ e ∈ V) (hk : ∀ v ∈ V, φ v = 0) :
    ∃ c : K, ∀ e, φ e = c • D.β e := by
  obtain ⟨s, hs⟩ := D.β0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr D.β0_surjective)
  have hs' : ∀ u, D.β0 (s u) = u := fun u => by simpa using LinearMap.congr_fun hs u
  let ψ : V →ₗ[K] V := (φ.codRestrict V hr) ∘ₗ s
  obtain ⟨c, hc⟩ := D.schur ψ (by
    intro g v
    apply Subtype.ext
    have hd : s (D.act g v) - (g : S.E ≃ₗ[K] S.E) (s v) ∈ V := by
      rw [← D.β0_eq_zero_iff, map_sub, hs', D.β0_act, hs', sub_self]
    have h1 := hk _ hd
    rw [map_sub, sub_eq_zero] at h1
    simp only [ψ, LinearMap.comp_apply, LinearMap.codRestrict_apply, D.act_coe]
    rw [h1, hcomm])
  refine ⟨c, fun e => ?_⟩
  have h1 : e - s (D.β0 e) ∈ V := by
    rw [← D.β0_eq_zero_iff, map_sub, hs', sub_self]
  have h2 : φ e = φ (s (D.β0 e)) := by
    have := hk _ h1
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h2]
  have h3 := congrArg Subtype.val (hc (D.β0 e))
  simpa [ψ, β_apply] using h3

theorem Qf_add_smul_β (c : K) (e : S.E) : S.Qf (e + c • D.β e) = S.Qf e := by
  rw [S.Qf_add, D.ts _ (V.smul_mem c (D.β_mem e)), map_smul, D.β_alt]
  simp

end LCData

end CFSG.RankThree.GF2n.Smith81.Smith23E1
