module

public import CFSG.Quasithin.Background.HA7Mod

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open scoped Matrix

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

noncomputable abbrev pairA7 : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2))) :=
  pairImg (Γ α) (θ α).toMonoidHom

noncomputable abbrev pairNormA7 : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2))) :=
  pairNorm (Γ α) (θ α).toMonoidHom

omit α in
theorem exists_matAut_two (a : MulAut (StdMod (Fin 4) (ZMod 2))) :
    ∃ A : GL (Fin 4) (ZMod 2), a = matAut A := by
  refine exists_matAut_of_mem_linSub fun c v => ?_
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 c with rfl | rfl
  · rw [zero_smul, toAddMap_zero, RingEquiv.refl_apply, zero_smul]
  · rw [one_smul, RingEquiv.refl_apply, one_smul]

theorem hAut (β : MulAut (Γ α)) : ∃ (A : GL (Fin 4) (ZMod 2)) (σ : ZMod 2 ≃+* ZMod 2),
    (∀ γ, (((β γ : Γ α) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ *
        ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) ∨
    ∀ γ, (((β γ : Γ α) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((((θ α).toMonoidHom γ : Γ α) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ *
        ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M.map (RingEquiv.refl (ZMod 2)) = M :=
    fun M => by ext; rfl
  obtain ⟨A, hA | hA⟩ := exists_aut α β
  · refine ⟨A, RingEquiv.refl _, Or.inl fun γ => ?_⟩
    rw [hA γ, hmap]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  · refine ⟨A, RingEquiv.refl _, Or.inr fun γ => ?_⟩
    rw [hA γ, hmap]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, MulEquiv.coe_toMonoidHom]

theorem exists_natural {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {V₁ : Subgroup V}
    {π : ↥(alternatingGroup (Fin 7)) →* ↥H}
    (hπ : (FFModel.a7Four α).RealizesVia H V₁ ⊥ π) :
    ∃ e₁ : ↥V₁ ≃* StdMod (Fin 4) (ZMod 2), ∀ (σ : ↥(alternatingGroup (Fin 7))) (u : ↥V₁)
      (hu : ((π σ : ↥H) : MulAut V) (u : V) ∈ V₁), e₁ ⟨_, hu⟩ = matAut (rep α σ) (e₁ u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q := QuotientGroup.lift ((FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec)
    (FFModel.a7Four α).sec.subtype fun x hx => Subgroup.mem_bot.mp hx
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro y hy
      induction y using QuotientGroup.induction_on with
      | H m =>
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_bot.mpr hy
    · intro w
      exact ⟨QuotientGroup.mk ⟨w, Subgroup.mem_top w⟩, rfl⟩
  let e₁ : ↥V₁ ≃* StdMod (Fin 4) (ZMod 2) :=
    (MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans (MulEquiv.ofBijective q hq)
  refine ⟨e₁, fun σ u hu => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hm' : (FFModel.a7Four α).act σ m.1 ∈ (FFModel.a7Four α).sec := Subgroup.mem_top _
  have h1 := hβe σ u m hu hm' hm.symm
  have h2 : q (QuotientGroup.mk ⟨(FFModel.a7Four α).act σ m.1, hm'⟩) =
      matAut (rep α σ) (q (QuotientGroup.mk m)) := rfl
  have h3 := congrArg (fun z => matAut (rep α σ) (q z)) hm
  exact ((congrArg q h1).trans h2).trans h3

theorem exists_model {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : A7Four H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    ∃ (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
      (e : V ≃* PairMod (Fin 4) (ZMod 2)), M.map (congrHom e) ≤ pairNormA7 α := by
  obtain ⟨α, π, hπ⟩ := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_natural α hπ
  set π' : ↥(Γ α) →* ↥H := π.comp (ψ α).symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp (ψ α).symm.surjective
  have he₁' : ∀ (γ : ↥(Γ α)) (u : ↥V₁) (hu : ((π' γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL (Fin 4) (ZMod 2)) (e₁ u) := by
    intro γ u hu
    have h := he₁ ((ψ α).symm γ) u hu
    have e : rep α ((ψ α).symm γ) = (γ : GL (Fin 4) (ZMod 2)) := by
      rw [← coe_ψ, MulEquiv.apply_symm_apply]
    rw [← e]
    exact h
  obtain ⟨e, he⟩ := PairG.exists_pair_model (θ α).toMonoidHom π' hπ's hU e₁ he₁' (hAut α) hφ
    hinf hsup hniso
  exact ⟨α, e, PairG.map_le_pairNorm (θ α).toMonoidHom e he hMN⟩

theorem θ_surjective : Function.Surjective (θ α).toMonoidHom := (θ α).surjective

omit α in
theorem mem_normalizer_of_matAut {Γ' : Subgroup (GL (Fin 4) (ZMod 2))}
    {A : GL (Fin 4) (ZMod 2)} (h : ∀ γ ∈ Γ', ∃ δ ∈ Γ', A * γ * A⁻¹ = δ)
    (h' : ∀ γ ∈ Γ', ∃ δ ∈ Γ', A⁻¹ * γ * A = δ) :
    A ∈ Subgroup.normalizer (Γ' : Set (GL (Fin 4) (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro γ
  constructor
  · intro hγ
    obtain ⟨δ, hδ, e⟩ := h γ hγ
    rw [e]
    exact hδ
  · intro hγ
    obtain ⟨δ, hδ, e⟩ := h' _ hγ
    have : γ = δ := by rw [← e]; group
    rw [this]
    exact hδ

theorem not_isoMod :
    ¬ Pair.IsoMod (pairA7 α) (V₁ (Fin 4) (ZMod 2)) (V₂ (Fin 4) (ZMod 2)) := by
  rintro ⟨e, he⟩
  have hmem : ∀ x : StdMod (Fin 4) (ZMod 2),
      ((x, 1) : PairMod (Fin 4) (ZMod 2)) ∈ V₁ (Fin 4) (ZMod 2) := fun x => mem_V₁.mpr rfl
  have hmem₂ : ∀ y : StdMod (Fin 4) (ZMod 2),
      ((1, y) : PairMod (Fin 4) (ZMod 2)) ∈ V₂ (Fin 4) (ZMod 2) := fun y => mem_V₂.mpr rfl
  let i₁ : ↥(V₁ (Fin 4) (ZMod 2)) ≃* StdMod (Fin 4) (ZMod 2) :=
    { toFun := fun w => (w : PairMod (Fin 4) (ZMod 2)).1
      invFun := fun x => ⟨(x, 1), hmem x⟩
      left_inv := fun w => Subtype.ext (Prod.ext rfl (mem_V₁.mp w.2).symm)
      right_inv := fun x => rfl
      map_mul' := fun w w' => rfl }
  let i₂ : ↥(V₂ (Fin 4) (ZMod 2)) ≃* StdMod (Fin 4) (ZMod 2) :=
    { toFun := fun w => (w : PairMod (Fin 4) (ZMod 2)).2
      invFun := fun y => ⟨(1, y), hmem₂ y⟩
      left_inv := fun w => Subtype.ext (Prod.ext (mem_V₂.mp w.2).symm rfl)
      right_inv := fun y => rfl
      map_mul' := fun w w' => rfl }
  let t : MulAut (StdMod (Fin 4) (ZMod 2)) := (i₁.symm.trans e).trans i₂
  have ht : ∀ x, t x = ((e ⟨(x, 1), hmem x⟩ : V₂ (Fin 4) (ZMod 2)) :
      PairMod (Fin 4) (ZMod 2)).2 := fun x => rfl
  have hint : ∀ γ : Γ α, ∀ x, t (natAut (Γ α) γ x) = natAut (Γ α) (θ α γ) (t x) := by
    intro γ x
    have hl := pairHom_mem_pairImg (Γ α) (θ α).toMonoidHom γ
    have hlx : pairHom (Γ α) (θ α).toMonoidHom γ ((x, 1) : PairMod (Fin 4) (ZMod 2)) =
        (natAut (Γ α) γ x, 1) := by
      rw [pairHom_apply, pairAut_apply, map_one]
    have hlv : pairHom (Γ α) (θ α).toMonoidHom γ ((x, 1) : PairMod (Fin 4) (ZMod 2)) ∈
        V₁ (Fin 4) (ZMod 2) := mem_V₁.mpr (by rw [hlx])
    have h1 := he _ hl ⟨(x, 1), hmem x⟩ hlv
    have h2 : (⟨pairHom (Γ α) (θ α).toMonoidHom γ (x, 1), hlv⟩ : V₁ (Fin 4) (ZMod 2)) =
        ⟨(natAut (Γ α) γ x, 1), hmem _⟩ := Subtype.ext hlx
    have h3 := congrArg (fun z : PairMod (Fin 4) (ZMod 2) => z.2) h1
    calc t (natAut (Γ α) γ x)
        = ((e ⟨(natAut (Γ α) γ x, 1), hmem _⟩ : V₂ (Fin 4) (ZMod 2)) :
            PairMod (Fin 4) (ZMod 2)).2 := rfl
      _ = ((e ⟨pairHom (Γ α) (θ α).toMonoidHom γ (x, 1), hlv⟩ : V₂ (Fin 4) (ZMod 2)) :
            PairMod (Fin 4) (ZMod 2)).2 :=
          congrArg (fun w => ((e w : V₂ (Fin 4) (ZMod 2)) : PairMod (Fin 4) (ZMod 2)).2) h2.symm
      _ = (pairHom (Γ α) (θ α).toMonoidHom γ ((e ⟨(x, 1), hmem x⟩ : V₂ (Fin 4) (ZMod 2)) :
            PairMod (Fin 4) (ZMod 2))).2 := h3
      _ = natAut (Γ α) (θ α γ) (t x) := rfl
  obtain ⟨T, hT⟩ := exists_matAut_two t
  have hTt : ∀ x, matAut T x = t x := fun x => by rw [← hT]
  have hconj : ∀ γ : Γ α, T * (γ : GL (Fin 4) (ZMod 2)) * T⁻¹ = ((θ α γ : Γ α) :
      GL (Fin 4) (ZMod 2)) := by
    intro γ
    apply matHom_injective
    refine MulEquiv.ext fun x => ?_
    rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply, matHom_apply]
    change matAut T (natAut (Γ α) γ ((matAut T)⁻¹ x)) = natAut (Γ α) (θ α γ) x
    obtain ⟨y, rfl⟩ := (matAut T).surjective x
    rw [MulAut.inv_apply_self, hTt, hint, ← hTt]
  have hTN : T ∈ Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) := by
    refine mem_normalizer_of_matAut (fun γ hγ => ⟨_, (θ α ⟨γ, hγ⟩).2, hconj ⟨γ, hγ⟩⟩)
      fun γ hγ => ?_
    obtain ⟨δ, hδ⟩ := (θ α).surjective ⟨γ, hγ⟩
    refine ⟨δ, δ.2, ?_⟩
    have h1 := hconj δ
    rw [hδ] at h1
    have h2 : T * (δ : GL (Fin 4) (ZMod 2)) * T⁻¹ = γ := h1
    rw [← h2]
    group
  rw [normalizer_eq] at hTN
  obtain ⟨g, hg⟩ := (ψ α).surjective ⟨T, hTN⟩
  have hθg : ∀ σ : alternatingGroup (Fin 7),
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) s σ = g * σ * g⁻¹ := by
    intro σ
    apply (ψ α).injective
    rw [← θ_apply]
    apply Subtype.ext
    rw [← hconj, map_mul, map_mul, map_inv, hg]
    rfl
  have hsg : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s) =
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) (g : Perm (Fin 7)) := by
    refine MulEquiv.ext fun σ => Subtype.ext ?_
    rw [hθg, MulAut.conjNormal_apply]
    rfl
  have hs := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).1 hsg
  have h1 := sign_s
  rw [hs, Equiv.Perm.mem_alternatingGroup.mp g.2] at h1
  exact absurd h1 (by decide)

theorem mem_pairA7_of_map
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α)
    (h1 : (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2)) :
    x ∈ pairA7 α := by
  obtain ⟨a, b, rfl⟩ := PairG.exists_pairAut (isNatIrr α) (θ_surjective α) (not_isoMod α) hx h1
  obtain ⟨A, rfl⟩ := exists_matAut_two a
  have hconj : ∀ γ : Γ α, ∃ δ : Γ α, matAut A * natAut (Γ α) γ * (matAut A)⁻¹ =
      natAut (Γ α) δ ∧ b * natAut (Γ α) (θ α γ) * b⁻¹ = natAut (Γ α) (θ α δ) :=
    fun γ => exists_conj hx γ
  have hAconj : ∀ γ : Γ α, ∃ δ : Γ α, A * (γ : GL (Fin 4) (ZMod 2)) * A⁻¹ = δ := by
    intro γ
    obtain ⟨δ, h, -⟩ := hconj γ
    refine ⟨δ, matHom_injective ?_⟩
    rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply]
    exact h
  have hx' : pairAut (matAut A)⁻¹ b⁻¹ ∈ pairNormA7 α := by
    rw [← pairAut_inv]
    exact Subgroup.inv_mem _ hx
  have hAconj' : ∀ γ : Γ α, ∃ δ : Γ α, A⁻¹ * (γ : GL (Fin 4) (ZMod 2)) * A = δ := by
    intro γ
    obtain ⟨δ, h, -⟩ := exists_conj hx' γ
    refine ⟨δ, matHom_injective ?_⟩
    rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply]
    rw [inv_inv] at h
    exact h
  have hAN : A ∈ Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) :=
    mem_normalizer_of_matAut (fun γ hγ => by
      obtain ⟨δ, hδ⟩ := hAconj ⟨γ, hγ⟩
      exact ⟨δ, δ.2, hδ⟩) fun γ hγ => by
      obtain ⟨δ, hδ⟩ := hAconj' ⟨γ, hγ⟩
      exact ⟨δ, δ.2, hδ⟩
  rw [normalizer_eq] at hAN
  set γ₀ : Γ α := ⟨A, hAN⟩ with hγ₀
  have hc : ∀ γ : Γ α, (natAut (Γ α) (θ α γ₀))⁻¹ * b * natAut (Γ α) γ =
      natAut (Γ α) γ * ((natAut (Γ α) (θ α γ₀))⁻¹ * b) := by
    intro γ
    obtain ⟨γ', rfl⟩ := (θ α).surjective γ
    obtain ⟨δ, h, h'⟩ := hconj γ'
    have hδ : δ = γ₀ * γ' * γ₀⁻¹ := by
      apply natAut_injective (Γ α)
      rw [← h, map_mul, map_mul, map_inv]
      rfl
    rw [hδ, map_mul, map_mul, map_inv] at h'
    rw [map_mul, map_mul, map_inv] at h'
    calc (natAut (Γ α) (θ α γ₀))⁻¹ * b * natAut (Γ α) (θ α γ')
        = (natAut (Γ α) (θ α γ₀))⁻¹ * (b * natAut (Γ α) (θ α γ') * b⁻¹) * b := by group
      _ = (natAut (Γ α) (θ α γ₀))⁻¹ * (natAut (Γ α) (θ α γ₀) * natAut (Γ α) (θ α γ') *
          (natAut (Γ α) (θ α γ₀))⁻¹) * b := by rw [h']
      _ = natAut (Γ α) (θ α γ') * ((natAut (Γ α) (θ α γ₀))⁻¹ * b) := by group
  obtain ⟨C, hC⟩ := exists_matAut_two ((natAut (Γ α) (θ α γ₀))⁻¹ * b)
  have hCcent : C ∈ Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro γ hγ
    apply matHom_injective
    rw [map_mul, map_mul, matHom_apply, matHom_apply, ← hC]
    exact (hc ⟨γ, hγ⟩).symm
  rw [centralizer_eq_bot, Subgroup.mem_bot] at hCcent
  have hb : b = natAut (Γ α) (θ α γ₀) := by
    have h1 : (natAut (Γ α) (θ α γ₀))⁻¹ * b = 1 := by
      rw [hC, hCcent]
      exact map_one (matHom (ι := Fin 4) (K := ZMod 2))
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  refine ⟨γ₀, ?_⟩
  rw [pairHom_apply, hb]
  rfl

end A7

end H

end CFSG.Quasithin
