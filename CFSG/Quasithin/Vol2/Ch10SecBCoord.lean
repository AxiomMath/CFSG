module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10SecBL32K
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] noncomputable def quotO2Equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ CFSG.pCore 2 A) ≃* (B ⧸ CFSG.pCore 2 B) :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

theorem quotO2Equiv_mk {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    quotO2Equiv e (a : A ⧸ CFSG.pCore 2 A) = ((e a : B) : B ⧸ CFSG.pCore 2 B) := rfl

variable {G : Type} [Group G]

@[expose] noncomputable def conjEquiv (K : Subgroup G) (g : G) : ↥K ≃* ↥(CFSG.conjugate K g) :=
  K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem conjEquiv_coe (K : Subgroup G) (g : G) (k : ↥K) :
    ((conjEquiv K g k : ↥(CFSG.conjugate K g)) : G) = g⁻¹ * k * g := by
  show (MulAut.conj g⁻¹) (k : G) = _
  simp

theorem isSylowTwoOf_map_of_surjective {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) (hρ : Function.Surjective ρ) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ⊤ := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨le_top, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ⊤ =
      ((S.subgroupOf H).map ρ).comap (⊤ : Subgroup K).subtype := rfl
  rw [show (((S.subgroupOf H).map ρ).subgroupOf ⊤).index = ((S.subgroupOf H).map ρ).index from
    Subgroup.relIndex_top_right _]
  exact fun hd => hS.2.2 (hd.trans (Subgroup.index_map_dvd _ hρ))

theorem isSylowTwoOf_U3 : IsSylowTwoOf L32.U3 ⊤ := by
  have hcard : Nat.card L32.U3 = 8 := by
    rw [Nat.card_eq_fintype_card, ← L32.card_U]
    exact Fintype.card_subtype (· ∈ L32.U3)
  have hΓ : Nat.card L32.Γ = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), ?_⟩
  rw [show (L32.U3.subgroupOf ⊤).index = L32.U3.index from Subgroup.relIndex_top_right _]
  have h := L32.U3.card_mul_index
  rw [hcard, hΓ] at h
  have hidx : L32.U3.index = 21 := by omega
  rw [hidx]
  decide

theorem exists_equiv_map_eq_U3 {Q : Type} [Group Q] [Finite Q] (e : Q ≃* L32.Γ)
    {D : Subgroup Q} (hD : IsSylowTwoOf D ⊤) : ∃ ψ : Q ≃* L32.Γ, D.map ψ.toMonoidHom = L32.U3 := by
  have hD' : IsSylowTwoOf (D.map e.toMonoidHom) ⊤ := by
    have h := isSylowTwoOf_map_of_surjective hD (e.toMonoidHom.comp (⊤ : Subgroup Q).subtype)
      (fun y => ⟨⟨e.symm y, trivial⟩, by simp⟩)
    have heq : (D.subgroupOf ⊤).map (e.toMonoidHom.comp (⊤ : Subgroup Q).subtype) =
        D.map e.toMonoidHom := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_top_eq]
    rwa [heq] at h
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_U3 hD'
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_⟩
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have := (hg (e d)).mp ⟨d, hd, rfl⟩
    exact this
  · intro hx
    have h1 : g * x * g⁻¹ ∈ D.map e.toMonoidHom := (hg _).mpr (by simpa [mul_assoc] using hx)
    obtain ⟨d, hd, hde⟩ := h1
    refine ⟨d, hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom] at hde
    rw [hde]
    group

end CFSG.Quasithin.Vol2.Ch10.SecB
