module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Rho
public import CFSG.Quasithin.EmptyFaithful.S14612GB0
public import CFSG.Quasithin.EmptyFaithful.S146zHTrans
public import CFSG.Quasithin.EmptyFaithful.S146zHCls

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open CFSG.Quasithin.S1417
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem rhoH_eq_one_of_comm_le (hcls : ClassAutShapeStmt) (h35 : Lemma1435)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {x : G} (hxH : x ∈ H) {Z' : Subgroup G} (hZ'U : Z' ≤ conjClosure (VZ T M) H)
    (hZ'2 : Nat.card Z' ≤ 2)
    (hcomm : ∀ u ∈ conjClosure (VZ T M) H, x * u * x⁻¹ * u⁻¹ ∈ Z') :
    rhoH h98.toHypF91 ⟨x, hxH⟩ = 1 := by
  classical
  by_contra hne
  obtain ⟨hsplit, hinf, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  let ψ : ↥Z' →* UMod h98.toHypF91 :=
    { toFun := fun z => clsU h98.toHypF91 (hZ'U z.2)
      map_one' := clsU_one h98.toHypF91
      map_mul' := fun a b => (clsU_mul h98.toHypF91 (hZ'U a.2) (hZ'U b.2)).symm }
  have hcomm' : ∀ w : UMod h98.toHypF91, commHom (rhoH h98.toHypF91 ⟨x, hxH⟩) w ∈ ψ.range := by
    intro w
    obtain ⟨u', hu', rfl⟩ := exists_clsU h98.toHypF91 w
    have hcU : x * u' * x⁻¹ * u'⁻¹ ∈ conjClosure (VZ T M) H := hZ'U (hcomm u' hu')
    refine ⟨⟨x * u' * x⁻¹ * u'⁻¹, hcomm u' hu'⟩, ?_⟩
    show clsU h98.toHypF91 hcU = _
    rw [commHom_apply, rhoH_clsU, clsU_inv,
      clsU_mul h98.toHypF91 (conj_mem_UH hxH hu') ((conjClosure (VZ T M) H).inv_mem hu')]
  have hle : commV (Subgroup.zpowers (rhoH h98.toHypF91 ⟨x, hxH⟩)) ≤ ψ.range := by
    rw [commV_zpowers_eq_map]
    rintro _ ⟨w, -, rfl⟩
    exact hcomm' w
  have hcardle : Nat.card ↥(commV (Subgroup.zpowers (rhoH h98.toHypF91 ⟨x, hxH⟩))) ≤ 2 :=
    (Subgroup.card_le_of_le hle).trans
      ((Nat.card_le_card_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective).trans hZ'2)
  have hrk := two_le_rk_commV_rho hsplit hinf hstr hne
  have hpow := card_eq_two_pow (V := UMod h98.toHypF91) IntMod.sq_eq_one
    (commV (Subgroup.zpowers (rhoH h98.toHypF91 ⟨x, hxH⟩)))
  have h4 : 2 ^ 2 ≤ Nat.card ↥(commV (Subgroup.zpowers (rhoH h98.toHypF91 ⟨x, hxH⟩))) := by
    rw [hpow]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  omega

theorem false_of_tvData (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) {g : G} (tv : TvData T M H g) :
    False := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hZgU : ∀ a ∈ conjSub g⁻¹ (conjClosure (VZ T M) H), ∀ b ∈ conjClosure (VZ T M) H,
      ⁅a, b⁆ ∈ conjClosure (VZ T M) H := fun a ha b hb => by
    have hab : a * b * a⁻¹ ∈ conjClosure (VZ T M) H := conj_mem_UH (tv.le_H ha) hb
    rw [commutatorElement_def]
    exact (conjClosure (VZ T M) H).mul_mem hab ((conjClosure (VZ T M) H).inv_mem hb)
  have hZg_le : conjSub g⁻¹ (quasithinOmegaOneCenter T) ≤ conjClosure (VZ T M) H := by
    rw [← tv.comm]
    exact Subgroup.commutator_le.mpr hZgU
  have hZg_ne : conjSub g⁻¹ (quasithinOmegaOneCenter T) ≠ ⊥ := fun e => by
    have := tv.card
    rw [e, Subgroup.card_bot] at this
    omega
  obtain ⟨x, hx, u, hu, hxu⟩ : ∃ x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H),
      ∃ u ∈ conjClosure (VZ T M) H, ⁅x, u⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hZg_ne
    rw [← tv.comm]
    exact eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun a ha b hb => by
      simpa using hall a ha b hb)
  have hxH : x ∈ H := tv.le_H hx
  have hcZ : ∀ u' ∈ conjClosure (VZ T M) H,
      x * u' * x⁻¹ * u'⁻¹ ∈ conjSub g⁻¹ (quasithinOmegaOneCenter T) := fun u' hu' => by
    rw [← tv.comm]
    exact Subgroup.commutator_mem_commutator hx hu'
  have hρ : rhoH h98.toHypF91 ⟨x, hxH⟩ = 1 :=
    rhoH_eq_one_of_comm_le hcls h35 S hred hshape h98 hxH hZg_le (by rw [tv.card]) hcZ
  have h4 : x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T :=
    (rhoH_clsU_eq_iff h98.toHypF91 ⟨x, hxH⟩ hu).mp (by rw [hρ]; rfl)
  have h5 : x * u * x⁻¹ * u⁻¹ ∈ conjSub g⁻¹ (quasithinOmegaOneCenter T) ⊓
      quasithinOmegaOneCenter T := ⟨hcZ u hu, h4⟩
  rw [tv.inf, Subgroup.mem_bot] at h5
  exact hxu (by rw [commutatorElement_def]; exact h5)

theorem Dγ_lt_Uγ_of_shape (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) :
    F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) < F8.Uγ (VZ T M) H (g : G) := by
  by_contra hn
  have hle : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) ≤
      F8.Uγ (VZ T M) H (g : G) := centralizerMod_le_left _ _ _
  have hge : F8.Uγ (VZ T M) H (g : G) ≤
      F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) := by
    by_contra hn'
    exact hn (lt_of_le_not_ge hle hn')
  exact false_of_tvData hcls h35 S hred hshape (S.tvData hred.isHTM hs (le_antisymm hge hle))

end CFSG.Quasithin
