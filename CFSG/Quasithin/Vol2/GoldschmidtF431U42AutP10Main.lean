module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Iso
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Rho
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cj
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Good

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique U42F431
open scoped MatrixGroups

section Std

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem iota_toG (c : AutCtx G M₁ M₂ z) (ι : Ah ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) (b : Bh) :
    (ι (b : Ah) : G) = c.iso.toG b := by
  rw [← c.iso.toG1_inclusion b]
  exact h1 (Subgroup.inclusion Bh_le_P1h b)

theorem aOf_eq_map (c : AutCtx G M₁ M₂ z) (ι : Ah ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) :
    aOf M₂ (c.iso.toG fhB) = A2h.map ((M₁ ⊔ M₂).subtype.comp ι.toMonoidHom) := by
  rw [aOf_M2 c.iso]
  ext x
  rw [AutIso.mem_imgG, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, iota_toG c ι h1 b⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, That_le_Bh (A2h_le_That ha)⟩, ha, (iota_toG c ι h1 _).symm⟩

end Std

theorem u42AutIdent_of_rho (hrho : U42AutRho) :
    U42AutIdent := by
  intro G _ _ M₁ M₂ z c T hT f hfT hgood R hR hTR hconf h54 h55 h56
  obtain ⟨g, hgB, -, hTg, hfg⟩ := exists_norm c hT hfT hgood
  have hF : (c.conj hgB).iso.toG fhB = f := by
    rw [hfg]
    exact AutIso.toG_conjIso c.iso hgB fhB
  have hT' : (c.conj hgB).iso.imgG That = T := by
    rw [hTg]
    exact AutIso.imgG_conjIso c.iso hgB That
  obtain ⟨hcF, hcF0, ι, hι1, hι2⟩ := h55
  have hgM : g ∈ M₁ ⊔ M₂ := Subgroup.mem_sup_left hgB.1
  set c' := c.conj hgB with hc'
  let ι' : Ah ≃* ↥(M₁ ⊔ M₂) := ι.trans (MulAut.conj (⟨g, hgM⟩ : ↥(M₁ ⊔ M₂)))
  have hι1' : ∀ x : P1h, (ι' (x : Ah) : G) = (c'.iso.phi1 x : G) := by
    intro x
    show g * (ι (x : Ah) : G) * g⁻¹ = g * (c.iso.phi1 x : G) * g⁻¹
    rw [hι1]
  have hι2' : ∀ x : P2h, (ι' (x : Ah) : G) = (c'.iso.phi2 x : G) := by
    intro x
    show g * (ι (x : Ah) : G) * g⁻¹ = g * (c.iso.phi2 x : G) * g⁻¹
    rw [hι2]
  subst hF hT'
  obtain ⟨ρ, hρM, hρ2, hρe⟩ := hrho G M₁ M₂ z c' R hR hTR hconf h54 ⟨hcF, hcF0, ι', hι1', hι2'⟩
    ι' hι1' hι2'
  set F := c'.iso.toG fhB with hFdef
  let ιG : Ah →* G := (M₁ ⊔ M₂).subtype.comp ι'.toMonoidHom
  have hinj : Function.Injective ιG := Subtype.val_injective.comp ι'.injective
  have hFι : ιG fhatA = F := iota_toG c' ι' hι1' fhB
  have hrange : ιG.range = M₁ ⊔ M₂ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (ι' a).2
    · intro hx
      exact ⟨ι'.symm ⟨x, hx⟩, by simp [ιG]⟩
  let d : RhoData G :=
    { ι := ιG
      ρ := ρ
      inj := hinj
      not_mem := by rw [hrange]; exact hρM
      sq := by rw [hFι]; exact hρ2
      conj := by
        intro a ha
        rw [hFι]
        exact hρe a ha }
  have hA : d.A = aOf M₂ F := (aOf_eq_map c' ι' hι1').symm
  have hH : Nat.card d.H = 576 := by
    have := h54.2.2.2.2.2.1
    change Nat.card ↥(Subgroup.normalizer (d.A : Set G)) = 576
    rw [hA]
    exact this
  have hG : d.ι.range ⊔ d.H = ⊤ := by
    show ιG.range ⊔ Subgroup.normalizer (d.A : Set G) = ⊤
    rw [hrange, hA]
    exact h56
  obtain ⟨e⟩ := d.nonempty_mulEquiv hH hG ⟨z, c.z1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.Quasithin.H13.lieModel_of_mulEquiv_psl_zmod
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩ e

end CFSG.Quasithin.H13.F431.U42Aut
