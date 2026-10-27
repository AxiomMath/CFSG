module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalGeo
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalComm
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_phi_P2 (F : Frame L1 L2 S D X) :
    ∃ φ : ↥(P2 L1 L2 S) →* Alt5, Function.Surjective φ ∧
      ∀ p : ↥(P2 L1 L2 S), φ p = 1 ↔ (p : G) ∈ Q2 L1 L2 S := by
  obtain ⟨φL, hφs, hφk⟩ := F.exists_phi
  have : ((Q2 L1 L2 S).subgroupOf (P2 L1 L2 S)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (P2_le_normalizer_Q2 L1 L2 S)
  set N := (Q2 L1 L2 S).subgroupOf (P2 L1 L2 S) with hN
  let θ : ↥L2 →* ↥(P2 L1 L2 S) ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion (le_sup_left : L2 ≤ P2 L1 L2 S))
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨l, hl, q, hq, hpq⟩ := exists_mul_P2 F p.2
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk' N) _ = _
    rw [QuotientGroup.mk'_apply]
    show ((⟨l, _⟩ : ↥(P2 L1 L2 S)) : ↥(P2 L1 L2 S) ⧸ N) = _
    rw [QuotientGroup.eq]
    show (⟨l, _⟩ : ↥(P2 L1 L2 S))⁻¹ * p ∈ N
    show ((⟨l, _⟩ : ↥(P2 L1 L2 S)) : G)⁻¹ * (p : G) ∈ Q2 L1 L2 S
    simp only [hpq]
    simpa using hq
  have hθk : ∀ l : ↥L2, θ l = 1 ↔ φL l = 1 := by
    intro l
    rw [hφk l]
    show (QuotientGroup.mk' N) _ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show (l : G) ∈ Q2 L1 L2 S ↔ _
    constructor
    · intro h
      exact Frame.inf_Q2_le ⟨l.2, h⟩
    · intro h
      exact F.pCore_L2_le_Q2 h
  have hker : θ.ker = φL.ker := by
    ext l
    exact hθk l
  let e1 := QuotientGroup.quotientKerEquivOfSurjective θ hθs
  let e2 := QuotientGroup.quotientKerEquivOfSurjective φL hφs
  let e3 : (↥L2 ⧸ θ.ker) ≃* (↥L2 ⧸ φL.ker) := QuotientGroup.quotientMulEquivOfEq hker
  let e : (↥(P2 L1 L2 S) ⧸ N) ≃* Alt5 := e1.symm.trans (e3.trans e2)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N), e.surjective.comp
    (QuotientGroup.mk'_surjective N), fun p => ?_⟩
  show e (QuotientGroup.mk' N p) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

theorem exists_phi_stab (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) :
    ∃ φ : ↥(stab δ) →* Alt5, Function.Surjective φ ∧ φ.ker = (Qv δ).subgroupOf (stab δ) := by
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨φ0, hφ0s, hφ0k⟩ := exists_phi_P2 F
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hδ
  let c : ↥(stab (g • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))) →*
      ↥(P2 L1 L2 S) :=
    { toFun := fun x => ⟨(g : G)⁻¹ * x * g, (mem_stab_smul_γ₁ h₂ g).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hQ : Qv (g • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) =
      conjSub (g : G) (Q2 L1 L2 S) := by
    rw [Qv_smul]
    unfold Qv
    rw [stab_γ₁ h₂]
  refine ⟨φ0.comp c, hφ0s.comp ?_, ?_⟩
  · intro p
    refine ⟨⟨(g : G) * p * (g : G)⁻¹, (mem_stab_smul_γ₁ h₂ g).mpr (by
      have e : (g : G)⁻¹ * ((g : G) * p * (g : G)⁻¹) * g = p := by group
      rw [e]; exact p.2)⟩, ?_⟩
    ext
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]
    group
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hQ, mem_conjSub]
    exact hφ0k (c x)

end CFSG.Quasithin.Kleidman.F204
