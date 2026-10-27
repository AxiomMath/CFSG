module

public import CFSG.Quasithin.AppendixH.H12.TransModule

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

private theorem exists_conj_map_eq_of_sylow {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (P Q : Sylow p H) :
    ∃ g : H, (Q : Subgroup H) = (P : Subgroup H).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl⟩

private theorem subgroupOf_map_conj {Γ : Type*} [Group Γ] {H P : Subgroup Γ} {g : ↥H}
    (hP : P ≤ H) :
    (P.subgroupOf H).map ((H.subtype).comp (MulAut.conj g).toMonoidHom) =
      P.map (MulAut.conj (g : Γ)).toMonoidHom := by
  have hcomp : (H.subtype).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Γ)).toMonoidHom.comp H.subtype := by
    ext a
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP]

theorem exists_conj_of_isSylowIn {Γ : Type*} [Group Γ] {p : ℕ} [Fact p.Prime] {H P Q : Subgroup Γ}
    [Finite ↥H] (hP : IsSylowIn p P H) (hQ : IsSylowIn p Q H) :
    ∃ c ∈ H, Q = P.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_sylow (p := p) hP.toSylow hQ.toSylow
  refine ⟨g, g.2, ?_⟩
  have hg' := congrArg (Subgroup.map H.subtype) hg
  rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow, Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hQ.le] at hg'
  rw [hg', subgroupOf_map_conj hP.le]

namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

@[expose] def conj (c : ↥L') : Trans L' L ρ' ρ where
  φ := (MulAut.conj c).trans τ.φ
  β := (ρ' (c : Γ)).trans τ.β
  compat g v := by
    simp only [MulEquiv.trans_apply]
    rw [τ.compat ((MulAut.conj c) g) (ρ' (c : Γ) v)]
    congr 1
    simp [MulAut.conj_apply, map_mul]

@[simp] private theorem conj_φ_apply (c : ↥L') (g : ↥L') :
    (τ.conj c).φ g = τ.φ ((MulAut.conj c) g) := rfl

@[simp] private theorem conj_β_apply (c : ↥L') (v : V') :
    (τ.conj c).β v = τ.β (ρ' (c : Γ) v) := rfl

@[simp] private theorem conj_β_symm_apply (c : ↥L') (x : V) :
    ((τ.conj c).β).symm x = (ρ' (c : Γ))⁻¹ (τ.β.symm x) := by
  apply ((τ.conj c).β).injective
  rw [MulEquiv.apply_symm_apply, conj_β_apply]
  simp

theorem toG_conj (c : ↥L') (X : Subgroup Γ) :
    (τ.conj c).toG X = τ.toG (X.map (MulAut.conj (c : Γ)).toMonoidHom) := by
  ext g
  rw [mem_toG, mem_toG]
  constructor
  · rintro ⟨h, hL, hh, hφ⟩
    refine ⟨(MulAut.conj (c : Γ)) h, L'.mul_mem (L'.mul_mem c.2 hL) (L'.inv_mem c.2),
      ⟨h, hh, rfl⟩, ?_⟩
    rw [← hφ, conj_φ_apply]
    congr 1
  · rintro ⟨h', hL', ⟨h, hh, rfl⟩, hφ⟩
    have hhL : h ∈ L' := by
      have hmem : (c : Γ)⁻¹ * ((MulAut.conj (c : Γ)) h) * (c : Γ) ∈ L' :=
        L'.mul_mem (L'.mul_mem (L'.inv_mem c.2) hL') c.2
      simpa [MulAut.conj_apply, mul_assoc] using hmem
    refine ⟨h, hhL, hh, ?_⟩
    rw [← hφ, conj_φ_apply]
    congr 1

theorem iota_conj {K : Type*} [Field K] (ι : K →+* AddMonoid.End (Additive V')) (c : ↥L')
    (hc : ∀ (a : K) (v : V'), ρ' (c : Γ) (kSmul ι a v) = kSmul ι a (ρ' (c : Γ) v)) :
    (τ.conj c).iota ι = τ.iota ι := by
  refine RingHom.ext fun a => AddMonoidHom.ext fun x => ?_
  apply Additive.toMul.injective
  show kSmul ((τ.conj c).iota ι) a (Additive.toMul x) =
    kSmul (τ.iota ι) a (Additive.toMul x)
  set u : V := Additive.toMul x
  set v : V' := (ρ' (c : Γ))⁻¹ (τ.β.symm u)
  have hβv : ((τ.conj c).β) v = u := by
    rw [conj_β_apply]
    simp [v]
  have h1 : kSmul ((τ.conj c).iota ι) a u = ((τ.conj c).β) (kSmul ι a v) := by
    rw [← hβv, kSmul_iota]
  have h2 : ((τ.conj c).β) (kSmul ι a v) = kSmul (τ.iota ι) a u := by
    rw [conj_β_apply, hc a v, show ρ' (c : Γ) v = τ.β.symm u from by simp [v]]
    rw [← kSmul_iota τ ι a (τ.β.symm u), MulEquiv.apply_symm_apply]
  rw [h1, h2]

theorem form_conj {K : Type*} (f : V' → V' → K) (c : ↥L')
    (hc : ∀ u v : V', f (ρ' (c : Γ) u) (ρ' (c : Γ) v) = f u v) :
    (τ.conj c).form f = τ.form f := by
  funext u v
  simp only [Trans.form, conj_β_symm_apply]
  rw [← hc ((ρ' (c : Γ))⁻¹ (τ.β.symm u)) ((ρ' (c : Γ))⁻¹ (τ.β.symm v))]
  simp

theorem exists_conj_toG_eq {p : ℕ} [Fact p.Prime] [Finite ↥L'] {T₀ : Subgroup Γ}
    (hT₀ : IsSylowIn p T₀ L') {T : Subgroup G} (hT : IsSylowIn p T L) :
    ∃ c : ↥L', (τ.conj c).toG T₀ = T := by
  have hsyl : IsSylowIn p (τ.fromG T) L' := by
    rw [isSylowIn_toG τ (τ.fromG_le T) le_rfl, τ.toG_fromG hT.le, τ.toG_top]
    exact hT
  obtain ⟨c, hcL', hceq⟩ := exists_conj_of_isSylowIn hT₀ hsyl
  refine ⟨⟨c, hcL'⟩, ?_⟩
  rw [toG_conj, ← hceq, τ.toG_fromG hT.le]

end Trans

end CFSG.Quasithin.AppendixH.H12