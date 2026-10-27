module

public import CFSG.Milestones.ASVolI.F45.G2dSix
public import CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin

theorem burnsideF46_g2d_D2_perm : ∀ i : Fin 32,
    u33D u33GenP 2 * u33Tel u33GenP i * (u33D u33GenP 2 * u33Tel u33GenP i) ≠ 1 := by
  decide +kernel

theorem burnsideF46_g2d_invol_B
    {u : U33G} (hu : u ∈ u33Data.B) (hu2 : u * u = 1) :
    u ∈ u33Data.T := by
  obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff u).1 hu
  rcases hj with rfl | rfl
  · rw [u33Data.D_zero, mul_one]
    exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
  · exfalso
    obtain ⟨k, hk⟩ := u33Data.exists_Tel_mul i₂ i₁
    have e : u33Data.D u33Data.jb * u33Data.Tel k * (u33Data.D u33Data.jb * u33Data.Tel k) = 1 := by
      rw [hk]
      have h : u33Data.D u33Data.jb * (u33Data.Tel i₂ * u33Data.Tel i₁) *
          (u33Data.D u33Data.jb * (u33Data.Tel i₂ * u33Data.Tel i₁)) =
          (u33Data.Tel i₁)⁻¹ * ((u33Data.Tel i₁ * u33Data.D u33Data.jb * u33Data.Tel i₂) *
            (u33Data.Tel i₁ * u33Data.D u33Data.jb * u33Data.Tel i₂)) * u33Data.Tel i₁ := by
        group
      rw [h, hu2]
      group
    have e' : u33D u33GenPG (u33Data.jb : ℕ) * u33Tel u33GenPG k *
        (u33D u33GenPG (u33Data.jb : ℕ) * u33Tel u33GenPG k) = 1 := e
    have hjb : (u33Data.jb : ℕ) = 2 := rfl
    rw [hjb] at e'
    apply burnsideF46_g2d_D2_perm k
    have := congrArg u33PresHom e'
    simpa only [map_mul, map_one, u33Tel_hom, u33D_hom] using this

open CFSG.ASVolI.ChF in
theorem burnsideF46_g2d_exists_theta
    {E : Type} [Group E] {M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .G2d 2 1 (⊤ : Subgroup E) M₁ M₂) :
    ∃ θ : U33G ≃* E, M₁ = u33Data.B.map θ.toMonoidHom := by
  obtain ⟨K, fK, finK, hcard, marking, h1, -⟩ := burnsideF4gG2Two_chart_G2d hyp
  letI := fK
  haveI := finK
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  have h2eq : (2 : K) = 0 := two_eq_zero_of_card_two hcard
  have hk2 := eq_zero_or_eq_one_of_card_two hcard
  have hψi := burnsideF4gG2TwoInv_psi_injective hcard marking
  have hψs := burnsideF4gG2TwoInv_psi_surjective hcard marking rfl
  let θ : U33G ≃* E := MulEquiv.ofBijective (burnsideF4gG2TwoInv_psi hcard marking) ⟨hψi, hψs⟩
  have hM1 : M₁ = ((G2Native.pointParabolic K).comap (g2HomC h2eq)).map
      (burnsideF4gG2TwoInv_psi hcard marking) := by
    rw [← burnsideF4gG2TwoInv_psi_map hcard marking, ← h1]
    exact (Subgroup.map_subgroupOf_eq_of_le le_top).symm
  obtain ⟨g₀, hg₀⟩ := burnsideF4gG2TwoInv_Pg_conj hcard h2eq hk2
  refine ⟨(MulAut.conj g₀).symm.trans θ, ?_⟩
  rw [hM1, ← hg₀, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  show burnsideF4gG2TwoInv_psi hcard marking x = θ ((MulAut.conj g₀).symm (MulAut.conj g₀ x))
  rw [MulEquiv.symm_apply_apply]
  rfl

open CFSG.ASVolI.ChF in
theorem burnsideF46_g2d_invol_mem
    {E : Type} [Group E] {M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .G2d 2 1 (⊤ : Subgroup E) M₁ M₂)
    {h : E} (hh : h ∈ M₁) (hh2 : h * h = 1) : h ∈ M₂ := by
  haveI := hyp.finite
  obtain ⟨θ, hθ⟩ := burnsideF46_g2d_exists_theta hyp
  set S : Set E := {g | g ∈ M₁ ∧ g * g = 1} with hS
  have hSle : Subgroup.closure S ≤ M₁ := (Subgroup.closure_le _).2 fun g hg => hg.1
  have hST : Subgroup.closure S ≤ u33Data.T.map θ.toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hg1 : θ.symm g ∈ u33Data.B := by
      have hgm : g ∈ u33Data.B.map θ.toMonoidHom := hθ ▸ hg.1
      rwa [Subgroup.mem_map_equiv] at hgm
    have hg2 : θ.symm g * θ.symm g = 1 := by rw [← map_mul, hg.2, map_one]
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
    exact burnsideF46_g2d_invol_B hg1 hg2
  have hp : IsPGroup 2 (Subgroup.closure S) := (u33_syl.1.map θ.toMonoidHom).to_le hST
  have hnorm : M₁ ≤ Subgroup.normalizer (Subgroup.closure S : Set E) := by
    intro g hg
    apply mem_normalizer_closure_of
    · rintro u ⟨hu1, hu2⟩
      refine ⟨M₁.mul_mem (M₁.mul_mem hg hu1) (M₁.inv_mem hg), ?_⟩
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    · rintro u ⟨hu1, hu2⟩
      refine ⟨M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hg) hu1) hg, ?_⟩
      calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [hu2]; group
  have hcore : Subgroup.closure S ≤ pCoreOf 2 M₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSle hnorm hp
  obtain ⟨K, fK, finK, hK, π, h1, h2⟩ := burnsideF45_g2d_chart hyp
  letI := fK
  have hP := burnsideF45_g2d_isLie hK π h1 h2
  have hQ := (burnsideF4b_pCoreOf_le Nat.prime_two hP).1
  rw [top_inf_eq] at hQ
  exact hQ (hcore (Subgroup.subset_closure ⟨hh, hh2⟩))

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7
  CFSG.ASVolI.ChF in
theorem burnsideF46_g2d_invol_fix
    {E : Type} [Group E] {M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .G2d 2 1 (⊤ : Subgroup E) M₁ M₂)
    {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (hc : c.IsFaithful) {g : c.G0}
    (hg : g ∈ stv c c.xv) (hg2 : g * g = 1) {w : c.Γ} (hw : c.graph.Adj c.xv w) : g • w = w := by
  obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 c hg
  have ha2 : a * a = 1 := f1_injective c hc (by rw [map_mul, hg2, map_one])
  obtain ⟨k, hk1, hk2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show c.lv ∈ CosetGeom.nbrs c.xv from CosetGeom.adj_γ₀_γ₁) hw
  rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at hk1
  obtain ⟨b, hb⟩ := hk1
  have hkb : k = f1 (c := c) b := Subtype.ext hb.symm
  set t : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := b⁻¹ * a * b with ht
  have hconj : t * t = 1 := by
    calc t * t = b⁻¹ * (a * a) * b := by rw [ht]; group
      _ = 1 := by rw [ha2]; group
  have hE : ((show ↥M₁ from t) : E) * ((show ↥M₁ from t) : E) = 1 := congrArg Subtype.val hconj
  have hmem : ((show ↥M₁ from t) : E) ∈ M₂ :=
    burnsideF46_g2d_invol_mem hyp (show ↥M₁ from t).2 hE
  have hrange : t ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
    rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range = (M₁ ⊓ M₂).subgroupOf M₁ from
      Subgroup.inclusion_range (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
    exact Subgroup.mem_subgroupOf.mpr ⟨(show ↥M₁ from t).2, hmem⟩
  have hfix : f1 (c := c) t • c.lv = c.lv :=
    MulAction.mem_stabilizer_iff.mp (burnsideF4b_f1_mem_stv_lv c hrange)
  rw [← hk2, hkb]
  have e : f1 (c := c) a * f1 (c := c) b = f1 (c := c) b * f1 (c := c) t := by
    rw [ht, map_mul, map_mul, map_inv]
    group
  rw [← mul_smul, e, mul_smul, hfix]

end CFSG.ASVolI
