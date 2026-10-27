module

public import CFSG.Milestones.ASVolI.F4N.Cor

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_f1_smul_lv_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (b : α.G1) :
    f1 (c := c) b • c.lv = c.lv ↔ b ∈ α.α1.range := by
  constructor
  · intro h
    have h1 : ((f1 (c := c) b : c.G0) : Y) ∈ c.φ2.range :=
      (burnsideF4b_mem_stv_lv c _).mp (MulAction.mem_stabilizer_iff.mpr h)
    have h2 : c.φ1 b ∈ c.φ1.range ⊓ c.φ2.range := ⟨⟨b, rfl⟩, h1⟩
    rw [c.inter] at h2
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, hc.1 (by rw [c.comm1]; exact hd)⟩
  · intro hb
    exact MulAction.mem_stabilizer_iff.mp (burnsideF4b_f1_mem_stv_lv c hb)

theorem burnsideF4n_stv_lv_eq_range {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) : stv c c.lv = (f2 (c := c)).range :=
  le_antisymm (stv_lv_le_range_f2 c) (by
    rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a))

theorem burnsideF4n_f1_alpha1 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (d : α.G12) : f1 (c := c) (α.α1 d) = f2 (c := c) (α.α2 d) := by
  apply Subtype.ext
  show c.φ1 (α.α1 d) = c.φ2 (α.α2 d)
  rw [c.comm1, c.comm2]

theorem burnsideF4n_mem_of_normalizer_borel {D : Type} [Group D] [Finite D] {p : ℕ}
    (hp : p.Prime) {B P₁ P₂ : Subgroup D} (h : IsLieParabolics p (⊤ : Subgroup D) B P₁ P₂)
    {e : D} (he : e ∈ Subgroup.normalizer (B : Set D)) : e ∈ B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨S, ⟨-, hSp, hSidx⟩, hB⟩, -⟩ := h
  have hidx : ¬ p ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSidx
  let T : Sylow p D := hSp.toSylow hidx
  have hNB : Subgroup.normalizer ((T : Subgroup D) : Set D) = B := by
    rw [hB, top_inf_eq]
    rfl
  have hNN := Sylow.normalizer_normalizer T
  rw [← Sylow.coe_coe] at hNN
  rw [← hNB] at he ⊢
  rwa [hNN] at he

theorem burnsideF4n_selfNorm {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hN : ∀ e : E, e ∈ Subgroup.normalizer ((M₁ ⊓ M₂ : Subgroup E) : Set E) → e ∈ M₁ ⊓ M₂)
    (a₀ b₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)
    (hR : ∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      a₀⁻¹ * a * a₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range ↔
        b₀⁻¹ * a * b₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range) :
    b₀⁻¹ * a₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
  let ι1 : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 →* E := M₁.subtype
  have hι1 : Function.Injective ι1 := M₁.subtype_injective
  have hmem : ∀ r : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      r ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range ↔ ι1 r ∈ M₁ ⊓ M₂ := by
    intro r
    constructor
    · rintro ⟨d, rfl⟩
      exact d.2
    · intro hr
      exact ⟨⟨ι1 r, hr⟩, hι1 rfl⟩
  have hn1 : ∀ r : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      r ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range →
        (b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
    intro r hr
    have h1 := (hR (a₀ * r * a₀⁻¹)).mp (by rwa [show a₀⁻¹ * (a₀ * r * a₀⁻¹) * a₀ = r by group])
    rwa [show b₀⁻¹ * (a₀ * r * a₀⁻¹) * b₀ = (b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹ by group] at h1
  have hn2 : ∀ r : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      (b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range →
        r ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
    intro r hr
    have h1 := (hR (b₀ * ((b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹) * b₀⁻¹)).mpr (by
      rwa [show b₀⁻¹ * (b₀ * ((b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹) * b₀⁻¹) * b₀ =
        (b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹ by group])
    rwa [show a₀⁻¹ * (b₀ * ((b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹) * b₀⁻¹) * a₀ = r by group] at h1
  have hnM : ι1 (b₀⁻¹ * a₀) ∈ M₁ := (b₀⁻¹ * a₀ : ↥M₁).2
  refine (hmem _).mpr (hN _ (Subgroup.mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩))
  · let r : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := (⟨e, he.1⟩ : ↥M₁)
    have h1 := (hmem _).mp (hn1 r ((hmem r).mpr he))
    rwa [map_mul, map_mul, map_inv] at h1
  · have heM : e ∈ M₁ := by
      have h1 : (ι1 (b₀⁻¹ * a₀))⁻¹ * (ι1 (b₀⁻¹ * a₀) * e * (ι1 (b₀⁻¹ * a₀))⁻¹) *
          ι1 (b₀⁻¹ * a₀) ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hnM) he.1) hnM
      rwa [show (ι1 (b₀⁻¹ * a₀))⁻¹ * (ι1 (b₀⁻¹ * a₀) * e * (ι1 (b₀⁻¹ * a₀))⁻¹) *
          ι1 (b₀⁻¹ * a₀) = e by group] at h1
    let r : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := (⟨e, heM⟩ : ↥M₁)
    have h1 : (b₀⁻¹ * a₀) * r * (b₀⁻¹ * a₀)⁻¹ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
      refine (hmem _).mpr ?_
      rw [map_mul, map_mul, map_inv]
      exact he
    exact (hmem r).mp (hn2 r h1)

theorem burnsideF4n_fix_xv {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : c.Facts46 m) (hm : 2 < m) {cc : c.Γ} (hcc : cc ∈ CosetGeom.nbrs c.xv)
    (hccl : cc ≠ c.lv) {h : c.G0} (h1 : h • c.lv = c.lv) (h2 : h • cc = cc) :
    h • c.xv = c.xv := by
  let w : c.graph.Walk c.lv cc :=
    SimpleGraph.Walk.cons (CosetGeom.adj_γ₀_γ₁.symm)
      (SimpleGraph.Walk.cons (hcc : c.graph.Adj c.xv cc) SimpleGraph.Walk.nil)
  let q : GPath c.graph 2 := GPath.ofWalk w
  have hq0 : q 0 = c.lv := rfl
  have hq1 : q 1 = c.xv := rfl
  have hq2 : q 2 = cc := rfl
  have hqn : q ∈ GPath.nbPaths c.graph c.lv 2 := by
    refine ⟨hq0, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hq0, hq2]
    exact fun e => hccl e.symm
  obtain ⟨hd, huniq⟩ := F.uniq 2 hm c.lv q hqn
  have hgeo : (h • q).IsGeodesic := by
    show c.graph.dist ((h • q) 0) ((h • q) 2) = 2
    rw [GPath.smul_apply, GPath.smul_apply, hq0, hq2, h1, h2, ← hq2]
    exact hd
  have heq := huniq (h • q) (by rw [GPath.smul_apply, hq0, h1])
    (by rw [GPath.smul_apply, hq2, h2]) hgeo
  have h3 : (h • q) 1 = q 1 := by rw [heq]
  rwa [GPath.smul_apply, hq1] at h3

theorem burnsideF4n_exists_conj_equiv {α : RankTwoAmalgam.{0}} {Y Y' : Type} [Group Y] [Group Y']
    (β : α.Completion Y) (ρ : α.Completion Y') (hβ : β.IsFaithful) (hρ : ρ.IsFaithful)
    (a₀ : α.G1) :
    ∃ ρ₃ : ↥(stv β (f1 (c := β) a₀ • β.lv)) ≃* ↥(stv ρ (f1 (c := ρ) a₀ • ρ.lv)),
      ∀ (x : ↥(stv β (f1 (c := β) a₀ • β.lv))) (k : α.G2),
        f2 (c := β) k = (f1 (c := β) a₀)⁻¹ * (x : β.G0) * f1 (c := β) a₀ →
        ((ρ₃ x : ↥(stv ρ (f1 (c := ρ) a₀ • ρ.lv))) : ρ.G0) =
          f1 (c := ρ) a₀ * f2 (c := ρ) k * (f1 (c := ρ) a₀)⁻¹ := by
  let eβ : α.G2 ≃* ↥(stv β β.lv) := (MonoidHom.ofInjective (f2_injective β hβ)).trans
    (MulEquiv.subgroupCongr (burnsideF4n_stv_lv_eq_range β).symm)
  let eρ : α.G2 ≃* ↥(stv ρ ρ.lv) := (MonoidHom.ofInjective (f2_injective ρ hρ)).trans
    (MulEquiv.subgroupCongr (burnsideF4n_stv_lv_eq_range ρ).symm)
  have heβ : ∀ k, ((eβ k : ↥(stv β β.lv)) : β.G0) = f2 (c := β) k := fun k => by
    show ((MonoidHom.ofInjective (f2_injective β hβ) k : ↥(f2 (c := β)).range) : β.G0) = _
    rw [MonoidHom.ofInjective_apply]
  have heρ : ∀ k, ((eρ k : ↥(stv ρ ρ.lv)) : ρ.G0) = f2 (c := ρ) k := fun k => by
    show ((MonoidHom.ofInjective (f2_injective ρ hρ) k : ↥(f2 (c := ρ)).range) : ρ.G0) = _
    rw [MonoidHom.ofInjective_apply]
  let e₁ : ↥(stv β β.lv) ≃* ↥(stv β (f1 (c := β) a₀ • β.lv)) :=
    MulAction.stabilizerEquivStabilizer (G := β.G0) (a := β.lv) rfl
  let e₄ : ↥(stv ρ ρ.lv) ≃* ↥(stv ρ (f1 (c := ρ) a₀ • ρ.lv)) :=
    MulAction.stabilizerEquivStabilizer (G := ρ.G0) (a := ρ.lv) rfl
  refine ⟨e₁.symm.trans (eβ.symm.trans (eρ.trans e₄)), fun x k hk => ?_⟩
  have h1 : e₁.symm x = eβ k := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MulAction.stabilizerEquivStabilizer_apply, MulAut.conj_apply, heβ, hk]
    group
  show ((e₄ (eρ (eβ.symm (e₁.symm x))) : ↥(stv ρ (f1 (c := ρ) a₀ • ρ.lv))) : ρ.G0) = _
  rw [h1, MulEquiv.symm_apply_apply, MulAction.stabilizerEquivStabilizer_apply,
    MulAut.conj_apply, heρ]

theorem burnside_as_F_4_21_of
    (h46 : F_4_6) : F_4_21 := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ Y _ β hβ _hs Y' _ ρ hρ cc hcc hccl cc' hcc' hccl' hstab
  haveI : Finite E := hyp.finite
  subst hGp
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  have hP := burnsideF4n_parabolics_at hyp
  rw [top_inf_eq, top_inf_eq, top_inf_eq] at hP
  have F := burnsideF4n_facts46_at h46 hyp β hβ
  have hm : 2 < κ.m := by rcases hκ with rfl | rfl <;> decide
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁ : β.graph.Adj β.xv β.lv) (hcc : β.graph.Adj β.xv cc)
  obtain ⟨a₀, rfl⟩ := stv_xv_le_range_f1 β (MulAction.mem_stabilizer_iff.mpr hg1)
  obtain ⟨g', hg1', hg2'⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁ : ρ.graph.Adj ρ.xv ρ.lv) (hcc' : ρ.graph.Adj ρ.xv cc')
  obtain ⟨b₀, rfl⟩ := stv_xv_le_range_f1 ρ (MulAction.mem_stabilizer_iff.mpr hg1')
  subst hg2
  subst hg2'
  have key : ∀ {Z : Type} [Group Z] (c : Cpl M₁ M₂ Z), c.IsFaithful →
      ∀ a₁ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      f1 (c := c) a ∈ stv c (f1 (c := c) a₁ • c.lv) ↔
        a₁⁻¹ * a * a₁ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := by
    intro Z _ c hc a₁ a
    rw [← burnsideF4n_f1_smul_lv_iff c hc, MulAction.mem_stabilizer_iff, map_mul, map_mul,
      map_inv, mul_smul, mul_smul, inv_smul_eq_iff]
  have hR : ∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      a₀⁻¹ * a * a₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range ↔
        b₀⁻¹ * a * b₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range := fun a =>
    (key β hβ a₀ a).symm.trans ((hstab a).trans (key ρ hρ b₀ a))
  have hnR : b₀⁻¹ * a₀ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range :=
    burnsideF4n_selfNorm (fun e he => burnsideF4n_mem_of_normalizer_borel hp hP he) a₀ b₀ hR
  have hcc'eq : f1 (c := ρ) b₀ • ρ.lv = f1 (c := ρ) a₀ • ρ.lv := by
    have h1 := (burnsideF4n_f1_smul_lv_iff ρ hρ _).mpr hnR
    rw [show a₀ = b₀ * (b₀⁻¹ * a₀) by group, map_mul, mul_smul, h1]
  rw [hcc'eq] at hstab ⊢
  obtain ⟨ρ₃, hρ₃⟩ := burnsideF4n_exists_conj_equiv β ρ hβ hρ a₀
  have hagree1 : ∀ (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) (h : f1 (c := β) a ∈ stv β (f1 (c := β) a₀ • β.lv)),
      ((ρ₃ ⟨f1 (c := β) a, h⟩ : ↥(stv ρ (f1 (c := ρ) a₀ • ρ.lv))) : ρ.G0) = f1 (c := ρ) a := by
    intro a h
    obtain ⟨d, hd⟩ := (key β hβ a₀ a).mp h
    have hk : f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 d) =
        (f1 (c := β) a₀)⁻¹ * f1 (c := β) a * f1 (c := β) a₀ := by
      rw [← burnsideF4n_f1_alpha1, hd, map_mul, map_mul, map_inv]
    rw [hρ₃ _ _ hk, ← burnsideF4n_f1_alpha1, hd, map_mul, map_mul, map_inv]
    group
  refine ⟨ρ₃, hagree1, fun a h => ?_⟩
  have hx : f2 (c := β) a • β.xv = β.xv :=
    burnsideF4n_fix_xv F hm hcc hccl (f2_smul_lv a) (MulAction.mem_stabilizer_iff.mp h)
  obtain ⟨a', ha'⟩ := stv_xv_le_range_f1 β (MulAction.mem_stabilizer_iff.mpr hx)
  have hY : β.φ1 a' = β.φ2 a := congrArg Subtype.val ha'
  have hint : β.φ1 a' ∈ β.φ1.range ⊓ β.φ2.range := ⟨⟨a', rfl⟩, ⟨a, hY.symm⟩⟩
  rw [β.inter] at hint
  obtain ⟨d, hd⟩ := hint
  have hd1 : (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d = a' := hβ.1 (by rw [β.comm1]; exact hd)
  have hd2 : (RankTwoAmalgam.ofSubgroups M₁ M₂).α2 d = a :=
    hβ.2.2 (by rw [β.comm2]; exact hd.trans hY)
  have h' : f1 (c := β) a' ∈ stv β (f1 (c := β) a₀ • β.lv) := by rw [ha']; exact h
  have hsub : (⟨f2 (c := β) a, h⟩ : ↥(stv β (f1 (c := β) a₀ • β.lv))) = ⟨f1 (c := β) a', h'⟩ :=
    Subtype.ext ha'.symm
  rw [hsub, hagree1 a' h', ← hd1, ← hd2, burnsideF4n_f1_alpha1]

end CFSG.ASVolI
