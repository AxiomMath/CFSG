module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Timmesfeld.Bridge.Asc72Basic
import CFSG.Timmesfeld.CorollaryBOpp
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Fischer

theorem exists_mulEquiv_of_commGraphIso {G₁ G₂ : Type} [Group G₁] [Group G₂] {D₁ : Set G₁}
    {D₂ : Set G₂} (h₁ : Asc72.Setup G₁ D₁) (h₂ : Asc72.Setup G₂ D₂)
    (hZ₁ : Subgroup.center G₁ = ⊥) (hZ₂ : Subgroup.center G₂ = ⊥)
    (β : commGraph D₁ ≃g commGraph D₂)
    (haxis : ∀ u : D₂, ∀ σ : commGraph D₂ ≃g commGraph D₂,
      (∀ v : D₂, Commute (v : G₂) u → σ v = v) →
      (∀ v : D₂, σ v = v) ∨ ∀ v : D₂, (σ v : G₂) = (u : G₂) * v * u) :
    ∃ φ : G₁ ≃* G₂, ∀ u : D₁, φ u = β u := by
  classical
  let ρ₁ : G₁ →* Equiv.Perm D₁ :=
    { toFun := fun g =>
        { toFun := fun x => ⟨g * x * g⁻¹, h₁.conj_mem g x.2⟩
          invFun := fun x => ⟨g⁻¹ * x * g, by simpa using h₁.conj_mem g⁻¹ x.2⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g h => Equiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  let ρ₂ : G₂ →* Equiv.Perm D₂ :=
    { toFun := fun g =>
        { toFun := fun x => ⟨g * x * g⁻¹, h₂.conj_mem g x.2⟩
          invFun := fun x => ⟨g⁻¹ * x * g, by simpa using h₂.conj_mem g⁻¹ x.2⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g h => Equiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  have hρ₁apply : ∀ (g : G₁) (x : D₁), ((ρ₁ g x : D₁) : G₁) = g * x * g⁻¹ :=
    fun _ _ => rfl
  have hρ₂apply : ∀ (g : G₂) (x : D₂), ((ρ₂ g x : D₂) : G₂) = g * x * g⁻¹ :=
    fun _ _ => rfl
  have hρ₁inj : Function.Injective ρ₁ := by
    intro g h hgh
    have hcomm : ∀ x ∈ D₁, Commute (h⁻¹ * g) x := by
      intro x hx
      show (h⁻¹ * g) * x = x * (h⁻¹ * g)
      have hx' : g * x * g⁻¹ = h * x * h⁻¹ := by
        have h2 := congrArg (fun z : D₁ => (z : G₁))
          (congrArg (fun p : Equiv.Perm D₁ => p ⟨x, hx⟩) hgh)
        simpa only [hρ₁apply] using h2
      calc (h⁻¹ * g) * x = h⁻¹ * (g * x * g⁻¹) * g := by group
        _ = h⁻¹ * (h * x * h⁻¹) * g := by rw [hx']
        _ = x * (h⁻¹ * g) := by group
    have hcenter : h⁻¹ * g ∈ Subgroup.center G₁ :=
      CFSG.Timmesfeld.CorB.mem_center_of_forall_commute h₁.gen hcomm
    rw [hZ₁, Subgroup.mem_bot] at hcenter
    calc g = h * (h⁻¹ * g) := by group
      _ = h := by rw [hcenter, mul_one]
  have hρ₂inj : Function.Injective ρ₂ := by
    intro g h hgh
    have hcomm : ∀ x ∈ D₂, Commute (h⁻¹ * g) x := by
      intro x hx
      show (h⁻¹ * g) * x = x * (h⁻¹ * g)
      have hx' : g * x * g⁻¹ = h * x * h⁻¹ := by
        have h2 := congrArg (fun z : D₂ => (z : G₂))
          (congrArg (fun p : Equiv.Perm D₂ => p ⟨x, hx⟩) hgh)
        simpa only [hρ₂apply] using h2
      calc (h⁻¹ * g) * x = h⁻¹ * (g * x * g⁻¹) * g := by group
        _ = h⁻¹ * (h * x * h⁻¹) * g := by rw [hx']
        _ = x * (h⁻¹ * g) := by group
    have hcenter : h⁻¹ * g ∈ Subgroup.center G₂ :=
      CFSG.Timmesfeld.CorB.mem_center_of_forall_commute h₂.gen hcomm
    rw [hZ₂, Subgroup.mem_bot] at hcenter
    calc g = h * (h⁻¹ * g) := by group
      _ = h := by rw [hcenter, mul_one]
  let ce : D₁ → commGraph D₁ ≃g commGraph D₁ := fun e =>
    { toEquiv := ρ₁ e
      map_rel_iff' := by
        intro a b
        rw [commGraph_adj_iff, commGraph_adj_iff]
        constructor
        · rintro ⟨hne, hc⟩
          refine ⟨?_, ?_⟩
          · intro hab
            exact hne (by rw [hρ₁apply e a, hρ₁apply e b, hab])
          · have hc' : (e : G₁) * (a : G₁) * (e : G₁)⁻¹ *
                ((e : G₁) * (b : G₁) * (e : G₁)⁻¹) =
                (e : G₁) * (b : G₁) * (e : G₁)⁻¹ *
                  ((e : G₁) * (a : G₁) * (e : G₁)⁻¹) := by
              simpa only [hρ₁apply] using hc
            exact (conj_commute_iff (e : G₁) (a : G₁) (b : G₁)).1 hc'
        · rintro ⟨hne, hc⟩
          refine ⟨?_, ?_⟩
          · intro hab
            exact hne (by
              have h : (ρ₁ e a : D₁) = ρ₁ e b := Subtype.ext hab
              exact congrArg Subtype.val ((ρ₁ e).injective h))
          · have hc' : (e : G₁) * (a : G₁) * (e : G₁)⁻¹ *
                ((e : G₁) * (b : G₁) * (e : G₁)⁻¹) =
                (e : G₁) * (b : G₁) * (e : G₁)⁻¹ *
                  ((e : G₁) * (a : G₁) * (e : G₁)⁻¹) :=
              (conj_commute_iff (e : G₁) (a : G₁) (b : G₁)).2 hc
            simpa only [hρ₁apply] using hc' }
  have key : ∀ u : D₁, ∀ x : D₁,
      (β (ρ₁ u x) : G₂) = (β u : G₂) * (β x : G₂) * (β u : G₂) := by
    intro u x
    let cu : commGraph D₁ ≃g commGraph D₁ := ce u
    let σ : commGraph D₂ ≃g commGraph D₂ := β.symm.trans (cu.trans β)
    have hσx : ∀ z : D₁, σ (β z) = β (cu z) := by
      intro z
      show (β.symm.trans (cu.trans β)) (β z) = β (cu z)
      rw [RelIso.trans_apply, RelIso.trans_apply, RelIso.symm_apply_apply]
    have hσfix : ∀ v : D₂, Commute (v : G₂) (β u) → σ v = v := by
      intro v hv
      obtain ⟨z, rfl⟩ := β.surjective v
      have hzu : Commute (z : G₁) (u : G₁) := by
        rcases commGraph_eq_or_adj hv.eq with h | h
        · have hz_eq : z = u := β.injective h
          rw [hz_eq]
        · exact (commGraph_adj.1 (β.map_adj_iff.1 h)).2
      have huzu : (u : G₁) * (z : G₁) * (u : G₁) = (z : G₁) := by
        calc (u : G₁) * (z : G₁) * (u : G₁) =
              (u : G₁) * ((z : G₁) * (u : G₁)) := by rw [mul_assoc]
          _ = (u : G₁) * ((u : G₁) * (z : G₁)) := by rw [hzu.eq]
          _ = ((u : G₁) * (u : G₁)) * (z : G₁) := by rw [← mul_assoc]
          _ = (z : G₁) := by rw [h₁.oddT.mul_self_eq_one u.2, one_mul]
      have hcuz : cu z = z := by
        apply Subtype.ext
        change ((ρ₁ u z : D₁) : G₁) = (z : G₁)
        rw [hρ₁apply u z, h₁.oddT.inv_eq u.2]
        exact huzu
      rw [hσx z, hcuz]
    have hσne : ¬ (∀ v : D₂, σ v = v) := by
      intro hσid
      have hcommu : ∀ z : D₁, Commute (u : G₁) (z : G₁) := by
        intro z
        have hcuz : cu z = z := by
          apply β.injective
          have h := hσid (β z)
          rw [hσx z] at h
          exact h
        have hconj : (u : G₁) * (z : G₁) * (u : G₁)⁻¹ = (z : G₁) := by
          have h := congrArg Subtype.val hcuz
          change ((ρ₁ u z : D₁) : G₁) = (z : G₁) at h
          rwa [hρ₁apply u z] at h
        rw [Commute]
        calc (u : G₁) * (z : G₁) =
              (u : G₁) * (z : G₁) * (u : G₁)⁻¹ * (u : G₁) := by group
          _ = (z : G₁) * (u : G₁) := by rw [hconj]
      have hcenter : (u : G₁) ∈ Subgroup.center G₁ :=
        CFSG.Timmesfeld.CorB.mem_center_of_forall_commute h₁.gen
          (fun z hz => hcommu ⟨z, hz⟩)
      rw [hZ₁, Subgroup.mem_bot] at hcenter
      exact h₁.oddT.ne_one u.2 hcenter
    rcases haxis (β u) σ hσfix with h | h
    · exact absurd h hσne
    · have hx := h (β x)
      have hleft : (σ (β x) : G₂) = (β (ρ₁ u x) : G₂) := by
        rw [hσx x]
        rfl
      rw [hleft] at hx
      exact hx
  have hc : ∀ u : D₁, Equiv.permCongrHom β.toEquiv (ρ₁ u) = ρ₂ (β u) := by
    intro u
    ext v
    obtain ⟨x, rfl⟩ := β.surjective v
    change (β.toEquiv.permCongr (ρ₁ u)) (β x) = ((ρ₂ (β u)) (β x) : G₂)
    rw [Equiv.permCongr_apply]
    change (β.toEquiv (ρ₁ u (β.toEquiv.symm (β.toEquiv x))) : G₂) =
      ((ρ₂ (β u)) (β x) : G₂)
    rw [Equiv.symm_apply_apply]
    change (β (ρ₁ u x) : G₂) = ((ρ₂ (β u)) (β x) : G₂)
    rw [key u x]
    change (β u : G₂) * (β x : G₂) * (β u : G₂) = ((ρ₂ (β u)) (β x) : G₂)
    change (β u : G₂) * (β x : G₂) * (β u : G₂) =
      (β u : G₂) * (β x : G₂) * ((β u : G₂))⁻¹
    rw [h₂.oddT.inv_eq (β u).2]
  have hrangeρ₁ : ρ₁.range = Subgroup.closure (Set.range fun e : D₁ => ρ₁ e) := by
    rw [MonoidHom.range_eq_map, ← h₁.gen, MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  have hrangeρ₂ : ρ₂.range = Subgroup.closure (Set.range fun e : D₂ => ρ₂ e) := by
    rw [MonoidHom.range_eq_map, ← h₂.gen, MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  let c : Equiv.Perm D₁ ≃* Equiv.Perm D₂ := Equiv.permCongrHom β.toEquiv
  have hrange : ρ₁.range.map c.toMonoidHom = ρ₂.range := by
    rw [hrangeρ₁, hrangeρ₂, MonoidHom.map_closure]
    congr 1
    ext τ
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨β u, (hc u).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := β.surjective v
      exact ⟨ρ₁ u, ⟨u, rfl⟩, hc u⟩
  let e₁ : G₁ ≃* ρ₁.range := MonoidHom.ofInjective (f := ρ₁) hρ₁inj
  let e₂ : G₂ ≃* ρ₂.range := MonoidHom.ofInjective (f := ρ₂) hρ₂inj
  let eR : ρ₁.range ≃* ρ₂.range :=
    (ρ₁.range.equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr hrange)
  let φ : G₁ ≃* G₂ := (e₁.trans eR).trans e₂.symm
  have hφ : ∀ u : D₁, φ u = β u := by
    intro u
    apply hρ₂inj
    have h1 : (e₂ (φ u) : Equiv.Perm D₂) = ρ₂ (φ u) := rfl
    have h2 : e₂ (φ u) = eR (e₁ u) := by simp [φ]
    rw [← h1, h2]
    exact hc u
  exact ⟨φ, hφ⟩

end CFSG.OddTranspositions.PartThree
