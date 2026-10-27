module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section QuasiEquiv

@[expose] def burnsideF4n_triple {α : RankTwoAmalgam.{0}} (a₁ : α.G1 ≃* α.G1)
    (a₁₂ : α.G12 ≃* α.G12) (a₂ : α.G2 ≃* α.G2) : ∀ d, α.toAmalgam.X d ≃* α.toAmalgam.X d
  | .one => a₁
  | .two => a₂
  | .onetwo => a₁₂

@[expose] def burnsideF4n_amalgIso {α : RankTwoAmalgam.{0}} (a₁ : α.G1 ≃* α.G1)
    (a₁₂ : α.G12 ≃* α.G12) (a₂ : α.G2 ≃* α.G2) (h1 : ∀ g, α.α1 (a₁₂ g) = a₁ (α.α1 g))
    (h2 : ∀ g, α.α2 (a₁₂ g) = a₂ (α.α2 g)) : Amalgam.Iso α.toAmalgam α.toAmalgam where
  toEquiv := burnsideF4n_triple a₁ a₁₂ a₂
  comm {d e} h x := by
    cases d <;> cases e
    all_goals first | rfl | exact h.elim | exact h1 x | exact h2 x

theorem burnsideF4n_exists_aut {X Y Z : Type} [Group X] [Group Y] [Group Z] (φ : Y ≃* Z)
    (f : X →* Y) (g : X →* Z) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : f.range.map φ.toMonoidHom = g.range) : ∃ a : X ≃* X, ∀ x, g (a x) = φ (f x) := by
  refine ⟨(MonoidHom.ofInjective hf).trans
    ((f.range.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      ((MulEquiv.subgroupCongr hfg).trans (MonoidHom.ofInjective hg).symm)), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← MonoidHom.ofInjective_apply hg, MulEquiv.apply_symm_apply]
  rfl

theorem burnsideF4n_quasiEquiv_of_map {α : RankTwoAmalgam.{0}} {Y Z : Type} [Group Y] [Group Z]
    (μ : α.Completion Y) (ν : α.Completion Z) (hμ : μ.IsFaithful) (hν : ν.IsFaithful)
    (φ : Y ≃* Z) (h1 : μ.φ1.range.map φ.toMonoidHom = ν.φ1.range)
    (h2 : μ.φ2.range.map φ.toMonoidHom = ν.φ2.range) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion ν.toCompletion := by
  have h12 : μ.φ12.range.map φ.toMonoidHom = ν.φ12.range := by
    rw [← μ.inter, ← ν.inter, Subgroup.map_inf_eq _ _ _ φ.injective, h1, h2]
  obtain ⟨a₁, ha₁⟩ := burnsideF4n_exists_aut φ μ.φ1 ν.φ1 hμ.1 hν.1 h1
  obtain ⟨a₁₂, ha₁₂⟩ := burnsideF4n_exists_aut φ μ.φ12 ν.φ12 hμ.2.1 hν.2.1 h12
  obtain ⟨a₂, ha₂⟩ := burnsideF4n_exists_aut φ μ.φ2 ν.φ2 hμ.2.2 hν.2.2 h2
  have c1 : ∀ g, α.α1 (a₁₂ g) = a₁ (α.α1 g) := fun g =>
    hν.1 (by rw [ν.comm1, ha₁₂, ha₁, μ.comm1])
  have c2 : ∀ g, α.α2 (a₁₂ g) = a₂ (α.α2 g) := fun g =>
    hν.2.2 (by rw [ν.comm2, ha₁₂, ha₂, μ.comm2])
  refine ⟨φ, burnsideF4n_amalgIso a₁ a₁₂ a₂ c1 c2, fun d x => ?_⟩
  cases d
  · exact (ha₁ x).symm
  · exact (ha₂ x).symm
  · exact (ha₁₂ x).symm

end QuasiEquiv

section Rigid

theorem burnsideF4n_mem_range_incl1 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (z : ↥(M₁ ⊔ M₂)) : z ∈ (incl M₁ M₂).φ1.range ↔ (z : E) ∈ M₁ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact (a : ↥M₁).2
  · intro h
    exact ⟨(⟨z, h⟩ : ↥M₁), Subtype.ext rfl⟩

theorem burnsideF4n_mem_range_incl2 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (z : ↥(M₁ ⊔ M₂)) : z ∈ (incl M₁ M₂).φ2.range ↔ (z : E) ∈ M₂ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact (a : ↥M₂).2
  · intro h
    exact ⟨(⟨z, h⟩ : ↥M₂), Subtype.ext rfl⟩

theorem burnsideF4n_rigid_of_overgroups {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    {M₁ M₂ : Subgroup E} (hgen : M₁ ⊔ M₂ = ⊤) {S₀ : Subgroup E} (hSp : IsPGroup p S₀)
    (hSi : ¬ p ∣ S₀.index) (hB : M₁ ⊓ M₂ = Subgroup.normalizer (S₀ : Set E))
    (hH1 : ∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₁) → X = M₁)
    (hH2 : ∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₂) → X = M₂)
    {Y : Type} [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful) (e : E ≃* Y) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion (incl M₁ M₂).toCompletion := by
  classical
  let ι₁₂ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 →* E := (M₁ ⊓ M₂).subtype
  let ψ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 →* E := e.symm.toMonoidHom.comp μ.φ12
  have hψ : Function.Injective ψ := e.symm.injective.comp hμ.2.1
  have hS₀B : S₀ ≤ M₁ ⊓ M₂ := hB ▸ Subgroup.le_normalizer
  let S₀' : Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := S₀.comap ι₁₂
  let S₁ : Subgroup E := S₀'.map ψ
  have hcard₁ : Nat.card S₁ = Nat.card S₀ := by
    rw [Subgroup.card_map_of_injective hψ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀B).toEquiv
  obtain ⟨n, hn⟩ := hSp.exists_card_eq
  have hS₁p : IsPGroup p S₁ := IsPGroup.of_card (n := n) (by rw [hcard₁, hn])
  have hidx : S₁.index = S₀.index := by
    have h1 := Subgroup.card_mul_index S₁
    have h2 := Subgroup.card_mul_index S₀
    rw [hcard₁] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hS₁i : ¬ p ∣ S₁.index := hidx ▸ hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E (hSp.toSylow hSi) (hS₁p.toSylow hS₁i)
  have hconj : ∀ x, x ∈ S₁ ↔ ∃ s ∈ S₀, g * s * g⁻¹ = x := by
    intro x
    have hS₁eq : S₁ = ((g • hSp.toSylow hSi : Sylow p E) : Subgroup E) := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [hS₁eq, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.mem_smul_pointwise_iff_exists]
    simp only [MulAut.smul_def, MulAut.conj_apply]
  have hnorm : ∀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12, ∀ s ∈ S₁,
      ψ b * s * (ψ b)⁻¹ ∈ S₁ := by
    intro b s hs
    obtain ⟨c, hc, rfl⟩ := hs
    refine ⟨b * c * b⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hb : ι₁₂ b ∈ Subgroup.normalizer (S₀ : Set E) := hB ▸ (b : ↥(M₁ ⊓ M₂)).2
    show ι₁₂ (b * c * b⁻¹) ∈ S₀
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hb _).mp hc
  have hconjL : ∀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12, g⁻¹ * ψ b * g ∈ M₁ ⊓ M₂ := by
    have fwd : ∀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12, ∀ h ∈ S₀,
        (g⁻¹ * ψ b * g) * h * (g⁻¹ * ψ b * g)⁻¹ ∈ S₀ := by
      intro b h hh
      have h1 : g * h * g⁻¹ ∈ S₁ := (hconj _).mpr ⟨h, hh, rfl⟩
      obtain ⟨s, hs, hseq⟩ := (hconj _).mp (hnorm b _ h1)
      have e1 : (g⁻¹ * ψ b * g) * h * (g⁻¹ * ψ b * g)⁻¹ = s := by
        calc (g⁻¹ * ψ b * g) * h * (g⁻¹ * ψ b * g)⁻¹
            = g⁻¹ * (ψ b * (g * h * g⁻¹) * (ψ b)⁻¹) * g := by group
          _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [hseq]
          _ = s := by group
      rw [e1]
      exact hs
    intro b
    rw [hB, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fwd b h, fun hh => ?_⟩
    have h2 := fwd b⁻¹ _ hh
    have e2 : (g⁻¹ * ψ b⁻¹ * g) * ((g⁻¹ * ψ b * g) * h * (g⁻¹ * ψ b * g)⁻¹) *
        (g⁻¹ * ψ b⁻¹ * g)⁻¹ = h := by
      rw [map_inv]
      group
    rwa [e2] at h2
  let ψ' : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 →* E := (MulAut.conj g⁻¹).toMonoidHom.comp ψ
  have hψ' : Function.Injective ψ' := (MulAut.conj g⁻¹).injective.comp hψ
  have hψ'v : ∀ b, ψ' b = g⁻¹ * ψ b * g := fun b => by
    show g⁻¹ * ψ b * g⁻¹⁻¹ = _
    rw [inv_inv]
  have hrange : ψ'.range = M₁ ⊓ M₂ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨b, rfl⟩
      rw [hψ'v]
      exact hconjL b
    · rw [Nat.card_congr (MonoidHom.ofInjective hψ').toEquiv.symm]
      exact le_rfl
  have hpre : ∀ x ∈ M₁ ⊓ M₂, ∃ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12,
      ψ b = g * x * g⁻¹ := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨b, hb⟩ := hx
    refine ⟨b, ?_⟩
    rw [← hb, hψ'v]
    group
  let e' : E ≃* Y := (MulAut.conj g).trans e
  have he' : ∀ x, e' x = e (g * x * g⁻¹) := fun x => rfl
  have hK12 : ∀ x ∈ M₁ ⊓ M₂, e' x ∈ μ.φ12.range := by
    intro x hx
    obtain ⟨b, hb⟩ := hpre x hx
    refine ⟨b, ?_⟩
    rw [he', ← hb]
    show μ.φ12 b = e (e.symm (μ.φ12 b))
    rw [MulEquiv.apply_symm_apply]
  have h12le1 : μ.φ12.range ≤ μ.φ1.range := μ.inter ▸ inf_le_left
  have h12le2 : μ.φ12.range ≤ μ.φ2.range := μ.inter ▸ inf_le_right
  have hL1 : μ.φ1.range.comap e'.toMonoidHom = M₁ := by
    refine hH1 _ (fun x hx => h12le1 (hK12 x hx)) ⟨?_⟩
    exact ((μ.φ1.range.comap e'.toMonoidHom).equivMapOfInjective e'.toMonoidHom e'.injective).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e'.surjective _)).trans
        (MonoidHom.ofInjective hμ.1).symm)
  have hL2 : μ.φ2.range.comap e'.toMonoidHom = M₂ := by
    refine hH2 _ (fun x hx => h12le2 (hK12 x hx)) ⟨?_⟩
    exact ((μ.φ2.range.comap e'.toMonoidHom).equivMapOfInjective e'.toMonoidHom e'.injective).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e'.surjective _)).trans
        (MonoidHom.ofInjective hμ.2.2).symm)
  let φ : Y ≃* ↥(M₁ ⊔ M₂) :=
    e'.symm.trans ((Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr hgen.symm))
  have hφsymm : ∀ z : ↥(M₁ ⊔ M₂), φ.symm z = e' (z : E) := fun z => rfl
  have hm1 : ∀ x : E, e' x ∈ μ.φ1.range ↔ x ∈ M₁ := fun x => SetLike.ext_iff.mp hL1 x
  have hm2 : ∀ x : E, e' x ∈ μ.φ2.range ↔ x ∈ M₂ := fun x => SetLike.ext_iff.mp hL2 x
  refine burnsideF4n_quasiEquiv_of_map μ (incl M₁ M₂) hμ (incl_faithful M₁ M₂) φ ?_ ?_
  · ext z
    rw [Subgroup.mem_map_equiv, hφsymm, burnsideF4n_mem_range_incl1]
    exact hm1 _
  · ext z
    rw [Subgroup.mem_map_equiv, hφsymm, burnsideF4n_mem_range_incl2]
    exact hm2 _

end Rigid

end CFSG.ASVolI
