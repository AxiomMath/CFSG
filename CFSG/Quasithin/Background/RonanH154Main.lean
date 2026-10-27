module

public import CFSG.Quasithin.Background.RonanH154Std
public import CFSG.Quasithin.Background.RonanH154Tconj
public import CFSG.Quasithin.Background.RonanH163Main

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem exists_iso_of_conj
    {a b : Fin 24} {Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    {c : P24} (hc : c ∈ AutPerm) (hca : c a = 0) (hcb : c b = 1)
    (hcΓ : conjSubg c Γ = mog22plus)
    (hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ φ : ↥Γ →* ↥mog22plus, (∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) ∧
      ∃ e : V ≃* W10, ∀ (g : ↥Γ) (v : V), e (ρ g v) = Rc (φ g) (e v) := by
  set τ : P24 := c⁻¹ with hτdef
  have hτ : τ ∈ AutPerm := AutPerm.inv_mem hc
  have hτ0 : τ 0 = a := by rw [hτdef, Equiv.Perm.inv_eq_iff_eq, hca]
  have hτ1 : τ 1 = b := by rw [hτdef, Equiv.Perm.inv_eq_iff_eq, hcb]
  have hn : ∀ m, m ∈ G6.coreMod 24 ↔ G6.permAct 24 τ⁻¹ m ∈ G6.coreMod 24 :=
    (preserves_iff_of_mem hτ).1
  have hC := (preserves_iff_of_mem hτ).2
  have hτ0' : τ⁻¹ a = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ b = 1 := by rw [← hτ1]; simp
  have hd : ∀ m, m ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) ↔
      G6.permAct 24 τ⁻¹ m ∈ golayC ⊔ Subgroup.zpowers (pairVec 0 1) := by
    intro m
    refine (mem_sup_zpowers_iff' (pairVec_sq a b) m).trans
      (Iff.trans ?_ (mem_sup_zpowers_iff' (pairVec_sq 0 1) _).symm)
    rw [hC m, hC (m * pairVec a b), map_mul, permAct_pairVec, hτ0', hτ1']
  have hΓ' : ∀ σ ∈ Γ, Preserves (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)) σ := by
    intro σ hσ
    have hσ' : c * σ * c⁻¹ ∈ mog22plus := by
      rw [← hcΓ, mem_conjSubg_iff]
      have e : c⁻¹ * (c * σ * c⁻¹) * c = σ := by group
      rw [e]
      exact hσ
    have e : ∀ m, G6.permAct 24 τ⁻¹ (G6.permAct 24 σ m) =
        G6.permAct 24 (c * σ * c⁻¹) (G6.permAct 24 τ⁻¹ m) := by
      intro m
      rw [hτdef, inv_inv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
        permAct_inv_apply_permAct]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [hn, e]
      exact (preserves_cocode22 hσ').1 _ ((hn m).1 hm)
    · rw [hd, e]
      exact (preserves_cocode22 hσ').2 _ ((hd m).1 hm)
  obtain ⟨e, he⟩ := (cocode22Coords.conj τ hn hd).exists_equiv hΓ' hreal
  obtain ⟨φ, hφ⟩ := exists_conjHom c hcΓ
  refine ⟨φ, hφ, e, fun g v => ?_⟩
  have h1 := he g v
  have h2 : (cocode22Coords.conj τ hn hd).rho Γ hΓ' g (e v) =
      cocode22Coords.rhoHom (c * (g : P24) * c⁻¹) (e v) := by
    show (cocode22Coords.conj τ hn hd).rhoHom (g : P24) (e v) = _
    rw [SecCoords.conj_rhoHom, hτdef, inv_inv]
  have h3 : Rc (φ g) (e v) = cocode22Coords.rhoHom (c * (g : P24) * c⁻¹) (e v) := by
    show cocode22Coords.rhoHom ((φ g : ↥mog22plus) : P24) (e v) = _
    rw [hφ]
  exact (h1.trans h2).trans h3.symm

theorem exists_std_iso_cocode
    {a b : Fin 24} (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) (hΓ : Γ = M2ab a b)
    (hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ c : P24, c ∈ AutPerm ∧ c a = 0 ∧ c b = 1 ∧ c • O = Ostd ∧ c • S = Sstd ∧ c • B = Bstd ∧
      ∃ (hcΓ : conjSubg c Γ = mog22plus) (φ : ↥Γ →* ↥mog22plus),
        (∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) ∧
        ∃ e : V ≃* W10, ∀ (g : ↥Γ) (v : V), e (ρ g v) = Rc (φ g) (e v) := by
  obtain ⟨c, hc, hca, hcb, hcO, hcS, hcB, hcΓ⟩ :=
    normal_form_plus hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ hSyl
  obtain ⟨φ, hφ, e, he'⟩ := exists_iso_of_conj hc hca hcb hcΓ hreal
  exact ⟨c, hc, hca, hcb, hcO, hcS, hcB, hcΓ, φ, hφ, e, he'⟩

theorem main154 {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ)
    (hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Γ = M2ab a b → Concl154 ρ a b (S.erase B) := by
  intro hΓ
  obtain ⟨c, hc, hca, hcb, -, hcS, hcB, hcΓ, φ, hφ, e, he'⟩ :=
    exists_std_iso_cocode hab hO haO hbO hS hBS haB hbB hTO hTS hL hSyl hΓ hreal
  have hQ : c • S.erase B = Qstd := by
    rw [smul_erase_finset_finset, hcS, hcB, Sstd_erase]
  have key := Concl154_of_transport c hc hcΓ ρ Rc φ hφ e he' a b (S.erase B)
  rw [hca, hcb, hQ] at key
  exact key std154

end CFSG.Quasithin.RonanH154
