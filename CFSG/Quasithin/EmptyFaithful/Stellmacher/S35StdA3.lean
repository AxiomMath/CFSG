module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35StdA2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
@[expose] def actHom {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ)
    {g : G} (hg : g ∈ stab l) : ↥(Ysub l) →* ↥(Ysub l) where
  toFun y := ⟨g * y * g⁻¹, InY.conj hψ hg y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    show g * (x * y : G) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
    group)

omit [Finite G] in
theorem act_sq {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ) {g : G}
    (hg : g ∈ stab l) (h : ψ ⟨g, hg⟩ * ψ ⟨g, hg⟩ = 1) {z : G} (hz : InY l z) :
    g * (g * z * g⁻¹) * g⁻¹ = z := by
  have hgg : g * g ∈ stab l := Subgroup.mul_mem _ hg hg
  have hψ' : ψ ⟨g * g, hgg⟩ = ψ ⟨(1 : G), Subgroup.one_mem _⟩ := by
    rw [show (⟨g * g, hgg⟩ : ↥(stab l)) = ⟨g, hg⟩ * ⟨g, hg⟩ from rfl, map_mul, h]
    exact (map_one ψ).symm
  calc g * (g * z * g⁻¹) * g⁻¹ = (g * g) * z * (g * g)⁻¹ := by group
    _ = 1 * z * 1⁻¹ := conj_eq_of_psi hψ hgg (Subgroup.one_mem _) hψ' hz
    _ = z := by simp

theorem fpf_rel (hS : Sit H M S) {l β : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ) {a b : G}
    (ha : a ∈ stab l ⊓ stab β) (hb : b ∈ stab l)
    (h1 : ψ ⟨a, ha.1⟩ * ψ ⟨a, ha.1⟩ = 1) (h2 : ψ ⟨b, hb⟩ * ψ ⟨b, hb⟩ = 1)
    (h1' : ψ ⟨a, ha.1⟩ ≠ 1) (h2' : ψ ⟨b, hb⟩ ≠ 1) (h12 : ψ ⟨a, ha.1⟩ ≠ ψ ⟨b, hb⟩)
    {u : G} (hu : InY l u) :
    u * (a * (b * u * b⁻¹) * a⁻¹) * (b * (a * u * a⁻¹) * b⁻¹) = 1 := by
  have hc : a * b ∈ stab l := Subgroup.mul_mem _ ha.1 hb
  have hcc : (a * b) * (a * b) ∈ stab l := Subgroup.mul_mem _ hc hc
  have hrel := perm3_two_involutions _ _ h1 h2 h1' h2' h12
  have hm : ψ ⟨a * b, hc⟩ = ψ ⟨a, ha.1⟩ * ψ ⟨b, hb⟩ := map_mul ψ ⟨a, ha.1⟩ ⟨b, hb⟩
  have hba : b * a ∈ stab l := Subgroup.mul_mem _ hb ha.1
  have hmba : ψ ⟨b * a, hba⟩ = ψ ⟨b, hb⟩ * ψ ⟨a, ha.1⟩ := map_mul ψ ⟨b, hb⟩ ⟨a, ha.1⟩
  have hmcc : ψ ⟨(a * b) * (a * b), hcc⟩ = ψ ⟨a * b, hc⟩ * ψ ⟨a * b, hc⟩ :=
    map_mul ψ ⟨a * b, hc⟩ ⟨a * b, hc⟩
  have hbaeq : ψ ⟨b * a, hba⟩ = ψ ⟨(a * b) * (a * b), hcc⟩ := by
    rw [hmba, hmcc, hm]; exact hrel.2
  have hccc : (a * b) * (a * b) * (a * b) ∈ stab l := Subgroup.mul_mem _ hcc hc
  have hmccc : ψ ⟨(a * b) * (a * b) * (a * b), hccc⟩ = ψ ⟨(1 : G), Subgroup.one_mem _⟩ := by
    rw [show (⟨(a * b) * (a * b) * (a * b), hccc⟩ : ↥(stab l)) =
      ⟨(a * b) * (a * b), hcc⟩ * ⟨a * b, hc⟩ from rfl, map_mul, hmcc, hm]
    exact hrel.1.trans (map_one ψ).symm
  set u₁ := a * (b * u * b⁻¹) * a⁻¹ with hu₁
  set u₂ := b * (a * u * a⁻¹) * b⁻¹ with hu₂
  have hu₁' : u₁ = (a * b) * u * (a * b)⁻¹ := by rw [hu₁]; group
  have hu₂' : u₂ = ((a * b) * (a * b)) * u * ((a * b) * (a * b))⁻¹ := by
    rw [hu₂, conj_eq_of_psi hψ hcc hba hbaeq.symm hu]
    · group
  have hY₁ : InY l u₁ := by rw [hu₁']; exact hu.conj hψ hc
  have hY₂ : InY l u₂ := by rw [hu₂']; exact hu.conj hψ hcc
  have hw : InY l (u * u₁ * u₂) := (hu.mul hY₁).mul hY₂
  have hfix : (a * b) * (u * u₁ * u₂) * (a * b)⁻¹ = u * u₁ * u₂ := by
    have e1 : (a * b) * u₁ * (a * b)⁻¹ = u₂ := by
      rw [hu₁', hu₂']; group
    have e2 : (a * b) * u₂ * (a * b)⁻¹ = u := by
      rw [hu₂']
      calc (a * b) * (((a * b) * (a * b)) * u * ((a * b) * (a * b))⁻¹) * (a * b)⁻¹
          = ((a * b) * (a * b) * (a * b)) * u * ((a * b) * (a * b) * (a * b))⁻¹ := by group
        _ = 1 * u * 1⁻¹ := conj_eq_of_psi hψ hccc (Subgroup.one_mem _) hmccc hu
        _ = u := by simp
    calc (a * b) * (u * u₁ * u₂) * (a * b)⁻¹
        = ((a * b) * u * (a * b)⁻¹) * ((a * b) * u₁ * (a * b)⁻¹) * ((a * b) * u₂ * (a * b)⁻¹) := by
          group
      _ = u₁ * u₂ * u := by rw [e1, e2, ← hu₁']
      _ = u * u₁ * u₂ := by
        exact ((hY₁.mul hY₂).comm hu).trans (mul_assoc u u₁ u₂).symm
  exact fixed_trivial hS hl hβ hψ ha hb h1 h2 h1' h2' h12 hw hfix

theorem fixed_mem_Zv (hS : Sit H M S) {l μ : Geo H M} (hl : vtype l = true)
    (hμ : μ ∈ nbrs l) {a p : G} (ha : a ∈ stab l ⊓ stab μ) (haQ : a ∉ Qv l) (hp : InY l p)
    (hfix : a * p * a⁻¹ = p) : p ∈ Zv l := by
  have hA := hS.glob.amalg
  have hT2 := (sylow_stab_inf_left hA hμ).2.1
  have hZ : ¬ Subgroup.zpowers a ≤ Qv l := fun h => haQ (h (Subgroup.mem_zpowers a))
  have hK := exists_mul_of_isPGroup_of_vtype_true hA hl hT2 inf_le_left
    (Subgroup.zpowers_le.mpr ha) hZ
  have hpa : Commute p a := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hcomm : ∀ x ∈ stab l ⊓ stab μ, p * x = x * p := by
    intro x hx
    obtain ⟨a', ha', q, hq, rfl⟩ := hK x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    exact ((hpa.zpow_right k).mul_right (show Commute p q from hp.2.2 q hq)).eq
  have hmem : p ∈ quasithinOmegaOneCenter (stab l ⊓ stab μ) :=
    Subgroup.subset_closure ⟨⟨Qv_le_edge hA hμ hp.1,
      Subgroup.mem_centralizer_iff.mpr fun x hx => (hcomm x hx).symm⟩, hp.2.1⟩
  exact (omegaOneCenter_le_Zv hA hμ).2.1 hmem

theorem omegaZ_le (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    ∀ x ∈ Qv l, x ^ 2 = 1 → (∀ y ∈ Qv l, x * y = y * x) → x ∈ Zv l := by
  intro x hx hx2 hxc
  have hA := hS.glob.amalg
  obtain ⟨ψ, hs, hψ⟩ := exists_quotHom_true hA hl
  obtain ⟨β, δ, δ', hn, hβδ, -, -⟩ := nbrs_S3 hS hl
  have hβ : β ∈ nbrs l := by rw [hn]; simp
  have hδ : δ ∈ nbrs l := by rw [hn]; simp
  obtain ⟨a, ha, haQ⟩ := exists_edge_not_Qv hS hβ hs hψ
  obtain ⟨b, hb, hbQ⟩ := exists_edge_not_Qv hS hδ hs hψ
  have hsq : ∀ {μ : Geo H M}, μ ∈ nbrs l → ∀ {g : G} (hg : g ∈ stab l ⊓ stab μ),
      ψ ⟨g, hg.1⟩ * ψ ⟨g, hg.1⟩ = 1 := by
    intro μ hμ g hg
    obtain ⟨k, hk⟩ := (sylow_stab_inf_left hA hμ).2.1 ⟨g, hg⟩
    have h1 : (⟨g, hg.1⟩ : ↥(stab l)) ^ (2 ^ k) = 1 := Subtype.ext (by
      simpa using congrArg Subtype.val hk)
    exact perm3_sq_of_pow (k := k) (by rw [← map_pow, h1, map_one])
  have hne1 : ∀ {g : G} (hg : g ∈ stab l), g ∉ Qv l → ψ ⟨g, hg⟩ ≠ 1 :=
    fun hg hgQ h => hgQ ((hψ _).mp h)
  have h12 : ψ ⟨a, ha.1⟩ ≠ ψ ⟨b, hb.1⟩ := by
    intro h
    have hmem : a⁻¹ * b ∈ stab l := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha.1) hb.1
    have hq : a⁻¹ * b ∈ Qv l := by
      refine (hψ ⟨a⁻¹ * b, hmem⟩).mp ?_
      have : (⟨a⁻¹ * b, hmem⟩ : ↥(stab l)) = ⟨a, ha.1⟩⁻¹ * ⟨b, hb.1⟩ := rfl
      rw [this, map_mul, map_inv, h, inv_mul_cancel]
    have hbT : b ∈ stab β ⊓ stab l ⊓ stab δ := by
      refine ⟨⟨?_, hb.1⟩, hb.2⟩
      have : b = a * (a⁻¹ * b) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha.2 (Qv_le_edge hA hβ hq).2
    rw [stab_inf_arc hS (vtype_nbr_S3 hl hβ) (mem_nbrs_symm.mp hβ) (mem_nbrs_symm.mp hδ)
      (Ne.symm hβδ)] at hbT
    exact hbQ hbT
  have h1 := hsq hβ ha
  have h2 := hsq hδ hb
  have h1' := hne1 ha.1 haQ
  have h2' := hne1 hb.1 hbQ
  let A := actHom hψ ha.1
  let B := actHom hψ hb.1
  have hcm : ∀ z w : ↥(Ysub (G := G) l), z * w = w * z :=
    fun z w => Subtype.ext (InY.comm z.2 w.2)
  have hAA : ∀ z, A (A z) = z := fun z => Subtype.ext (act_sq hψ ha.1 h1 z.2)
  have hBB : ∀ z, B (B z) = z := fun z => Subtype.ext (act_sq hψ hb.1 h2 z.2)
  have hc : ∀ z : ↥(Ysub (G := G) l), z * A (B z) * B (A z) = 1 := fun z =>
    Subtype.ext (fpf_rel hS hl hβ hψ ha hb.1 h1 h2 h1' h2' h12 z.2)
  have key := decomp hcm (fun z => Subtype.ext z.2.sq_eq) A B hc
    (⟨x, InY.mem_of_central hx hx2 hxc⟩ : ↥(Ysub (G := G) l))
  set y : ↥(Ysub (G := G) l) := ⟨x, InY.mem_of_central hx hx2 hxc⟩ with hy
  have hx' : x = ((y * B y) * A (y * B y) : ↥(Ysub (G := G) l)) *
      ((y * A y) * B (y * A y) : ↥(Ysub (G := G) l)) := congrArg Subtype.val key.symm
  rw [hx']
  refine Subgroup.mul_mem _ ?_ ?_
  · refine fixed_mem_Zv hS hl hβ ha haQ (Subtype.prop _) ?_
    have : A ((y * B y) * A (y * B y)) = (y * B y) * A (y * B y) := by
      rw [map_mul, hAA, hcm]
    exact congrArg Subtype.val this
  · refine fixed_mem_Zv hS hl hδ hb hbQ (Subtype.prop _) ?_
    have : B ((y * A y) * B (y * A y)) = (y * A y) * B (y * A y) := by
      rw [map_mul, hBB, hcm]
    exact congrArg Subtype.val this

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin
