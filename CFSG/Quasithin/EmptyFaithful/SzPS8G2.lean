module

public import CFSG.Quasithin.EmptyFaithful.SzPS8U33Core
public import CFSG.Quasithin.EmptyFaithful.SzPS8G2Data
public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs
public import CFSG.Quasithin.H13.L32NKGSp6Cert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
  CFSG.Quasithin.H13.U3 CFSG.Quasithin.SzPS8.G2U Matrix

namespace SzPS8

section Rep

@[expose] def g2uGL (i : Fin 5) : GL (Fin 6) (ZMod 2) :=
  ⟨colMat (g2uc i), colMat (g2uci i), by rw [← colMat_mul6, (g2uc_mul_inv i).1, colMat_id6],
    by rw [← colMat_mul6, (g2uc_mul_inv i).2, colMat_id6]⟩

theorem coe_prod_g2uGL (w : List (Fin 5 × Bool)) :
    (((w.map fun l => cond l.2 (g2uGL l.1) (g2uGL l.1)⁻¹).prod : GL (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      colMat ((w.map fun l => cond l.2 (g2uc l.1) (g2uci l.1)).foldr mul6 id6) := by
  induction w with
  | nil => simp [colMat_id6]
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, List.map_cons, List.foldr_cons,
      colMat_mul6]
    congr 1
    cases l.2 <;> rfl

@[expose] noncomputable def g2uRep : U33G →* GL (Fin 6) (ZMod 2) :=
  PresentedGroup.toGroup (f := g2uGL) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    apply Units.ext
    rw [coe_prod_g2uGL, Units.val_one, g2uc_relators w hw, colMat_id6])

theorem g2uRep_gen (i : Fin 5) : g2uRep (u33GenPG i) = g2uGL i := by
  simp only [u33GenPG, Fin.is_lt, ↓reduceDIte, Fin.eta, g2uRep, PresentedGroup.toGroup.of]

theorem g2uRep_injective :
    Function.Injective g2uRep := by
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g2uRep.ker with h | h
  · exact h
  · exfalso
    have h1 : g2uRep (u33GenPG 0) = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
    have h2 : colMat (g2uc 0) = colMat id6 := by
      rw [colMat_id6]
      have := g2uRep_gen 0
      rw [show (u33GenPG ((0 : Fin 5) : ℕ)) = u33GenPG 0 from rfl, h1] at this
      exact (congrArg Units.val this).symm
    exact g2uc_zero_ne (colMat_injective (by decide +kernel) (by decide +kernel) h2)

end Rep

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem OvgSymp.false_of_g22
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}
    (S : OvgSymp B Γ T0 v) (hd : Module.finrank (ZMod 2) V = 6) (hc : Nat.card Γ = 12096) :
    False := by
  classical
  obtain ⟨b, hb⟩ := H13.KGCert.kgSp6Order12096 V B S.alt S.nondegenerate hd Γ S.isometry hc
  let Θ : (V ≃ₗ[ZMod 2] V) ≃* GL (Fin 6) (ZMod 2) :=
    MulEquiv.ofBijective (H13.KGSp6.phi b) ⟨H13.KGSp6.phi_injective b, H13.KGSp6.phi_surjective b⟩
  set ρ : U33G →* (V ≃ₗ[ZMod 2] V) := Θ.symm.toMonoidHom.comp g2uRep with hρ
  have hρinj : Function.Injective ρ := Θ.symm.injective.comp g2uRep_injective
  have hgen : ∀ i : Fin 5, ρ (u33GenPG i) ∈ Γ := by
    intro i
    have hmem : colMat (g2uc i) ∈ H13.KGCert.g22Mats := by
      have := H13.KGCert.decodeC_evalWord_mem (g2uw i)
      rw [g2uc_words] at this
      exact this
    obtain ⟨γ, hγ, hγe⟩ := (hb _).mp hmem
    have h1 : Θ γ = g2uGL i := by
      apply Units.ext
      rw [show Θ γ = H13.KGSp6.phi b γ from rfl, H13.KGSp6.coe_phi, hγe]
      rfl
    have h2 : ρ (u33GenPG i) = γ := by
      simp only [hρ, MonoidHom.comp_apply, g2uRep_gen]
      exact (MulEquiv.symm_apply_eq Θ).mpr h1.symm
    rw [h2]
    exact hγ
  have hall : ∀ g, ρ g ∈ Γ := by
    have hle : (⊤ : Subgroup U33G) ≤ Γ.comap ρ := by
      rw [← u33Data.gen]
      refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | rfl | rfl | rfl | rfl)
      exacts [hgen 0, hgen 1, hgen 2, hgen 3, hgen 4]
    exact fun g => hle (Subgroup.mem_top g)
  have hKΓ : ρ.range ≤ Γ := by
    rintro _ ⟨g, rfl⟩
    exact hall g
  have hKcard : Nat.card ρ.range = 6048 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact card_u33Pres
  have hKnorm : (ρ.range.subgroupOf Γ).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h1 := Subgroup.card_mul_index (ρ.range.subgroupOf Γ)
    have h2 : Nat.card ↥(ρ.range.subgroupOf Γ) = 6048 := by
      rw [← hKcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKΓ).toEquiv
    rw [h2, hc] at h1
    omega
  refine S.toOvgSetting.false_of_u33 ρ hρinj hKΓ (fun γ hγ k hk => ?_) ⟨1, by rw [hc]; norm_num⟩
  exact hKnorm.conj_mem ⟨k, hKΓ hk⟩ hk ⟨γ, hγ⟩

theorem excl6_of_ovg
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) : Lemma14315Excl6 := by
  intro G _ _ T M hyp hnot hU D hc
  obtain ⟨v, S⟩ := exists_ovgSymp h11 h113 h35 hyp hnot hU D
  exact (S.false_of_g22 hc.1 hc.2).elim

end Main

end SzPS8

end CFSG.Quasithin
