module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7B
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Rad

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

theorem cent_eq_t0_check : ∀ l ∈ Thl, comp l l = idL → l ≠ idL → l ≠ xL →
    64 ≤ (Thl.filter fun m => comp m l == comp l m).length →
      ∀ m ∈ Thl, (comp m l = comp l m ↔ comp m (Tl.getD 20 []) = comp (Tl.getD 20 []) m) := by
  decide +kernel

theorem cent_eq_t0 {t : Ah}
    (ht : t ∈ That) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htx : t ≠ xA)
    (hcard : 64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({t} : Set Ah))) :
    That ⊓ Subgroup.centralizer ({t} : Set Ah) =
      That ⊓ Subgroup.centralizer ({t0A} : Set Ah) := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff t).1 ht
  have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
    have : (t : P45) * (t : P45) = 1 := congrArg Subtype.val ht2
    rw [this]
    exact repL_one 45)
  have hl1 : l ≠ idL := fun h => ht1 (Subtype.ext (eq_of_repL hrep (h ▸ repL_one 45)))
  have hlx : l ≠ xL := fun h => htx (Subtype.ext (eq_of_repL hrep (h ▸ (repL_x : RepL xL _))))
  have hlen := (hcard.trans (card_cent_le_k hrep (le_refl
    (Thl.filter fun m => comp m l == comp l m).length)))
  have hch := cent_eq_t0_check l hl hl2 hl1 hlx hlen
  ext a
  constructor
  · rintro ⟨haT, hac⟩
    obtain ⟨la, hla, hrepa⟩ := (mem_That_iff a).1 haT
    refine ⟨haT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_comp_comm (v := t0A) repL_t0A hrepa
      ((hch la hla).1 (comp_comm_of_comm hrep hrepa
        (Subgroup.mem_centralizer_singleton_iff.1 hac)))
  · rintro ⟨haT, hac⟩
    obtain ⟨la, hla, hrepa⟩ := (mem_That_iff a).1 haT
    refine ⟨haT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_comp_comm hrep hrepa
      ((hch la hla).2 (comp_comm_of_comm (v := t0A) repL_t0A hrepa
        (Subgroup.mem_centralizer_singleton_iff.1 hac)))

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] noncomputable def imgGEquiv (iso : AutIso M₁ M₂) {K : Subgroup Ah} (hK : K ≤ Bh) :
    ↥K ≃* ↥(iso.imgG K) :=
  (Subgroup.subgroupOfEquivOfLe hK).symm.trans
    (Subgroup.equivMapOfInjective _ iso.toGHom iso.toG_injective)

theorem R_equiv
    (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (h4 : NotExtremalStmt) (h5 : U42AutFusionZ)
    {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R) :
    Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4) := by
  have hcard := card_R c h2 h4 h5 hR hTR
  have hTG : IsSylowTwoOf (c.iso.imgG That) ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  obtain ⟨S, hS, hRS⟩ := B6.exists_isSylowTwoOf_ge hR.2.1 (le_top : R ≤ ⊤)
  obtain ⟨g, -, hSg⟩ := B6.isSylowTwoOf_exists_conj hTG hS
  have hFc : ∀ b ∈ cenOf (c.iso.toG fhB), b * c.iso.toG fhB = c.iso.toG fhB * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 hb
  have hFR : c.iso.toG fhB ∈ R := mem_of_central_of_isSylowTwoOf hR
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) hFc (F_sq c.iso)
  have hRT : ∀ x ∈ R, g⁻¹ * x * g ∈ c.iso.imgG That := fun x hx =>
    B6.mem_conjSub.1 (hSg ▸ hRS hx)
  obtain ⟨t', ht'T, ht'g⟩ := c.iso.mem_imgG.1 (hRT _ hFR)
  have ht'2 : t' * t' = 1 := by
    apply c.iso.toG_injective
    rw [AutIso.toG_mul, ht'g, c.iso.toG_one]
    calc g⁻¹ * c.iso.toG fhB * g * (g⁻¹ * c.iso.toG fhB * g)
        = g⁻¹ * (c.iso.toG fhB * c.iso.toG fhB) * g := by group
      _ = 1 := by rw [F_sq c.iso]; group
  have ht'1 : (t' : Ah) ≠ 1 := by
    intro h1
    apply F_ne_one c.iso
    have h3 := congrArg c.iso.toG (Subtype.ext h1 : t' = 1)
    rw [ht'g, c.iso.toG_one] at h3
    calc c.iso.toG fhB = g * (g⁻¹ * c.iso.toG fhB * g) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have ht'x : (t' : Ah) ≠ xA := by
    intro h1
    apply F_notConj c h5
    have h3 := congrArg c.iso.toG (Subtype.ext h1 : t' = xB)
    rw [ht'g, c.iso.toG_xB c.z2 c.z1 c.zc] at h3
    exact isConj_iff.2 ⟨g⁻¹, by
      calc g⁻¹ * c.iso.toG fhB * g⁻¹⁻¹ = g⁻¹ * c.iso.toG fhB * g := by group
        _ = z := h3⟩
  have hK : That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah) ≤ Bh := inf_le_left.trans That_le_Bh
  have hle : B6.conjSub g⁻¹ R ≤ c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g) := by
    intro x hx
    have hx' : g⁻¹⁻¹ * x * g⁻¹ ∈ R := B6.mem_conjSub.1 hx
    refine ⟨?_, ?_⟩
    · have := hRT _ hx'
      simpa [mul_assoc] using this
    · show x ∈ Subgroup.centralizer ({g⁻¹ * c.iso.toG fhB * g} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hFc _ (hR.1 hx')
      calc x * (g⁻¹ * c.iso.toG fhB * g)
          = g⁻¹ * (g * x * g⁻¹ * c.iso.toG fhB) * g := by group
        _ = g⁻¹ * (c.iso.toG fhB * (g * x * g⁻¹)) * g := by
          simpa using congrArg (g⁻¹ * · * g) h1
        _ = g⁻¹ * c.iso.toG fhB * g * x := by group
  have e := c.iso.imgG_inf_cen t'
  rw [ht'g] at e
  have hcardT : Nat.card ↥(c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g)) =
      Nat.card ↥(That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah)) := by
    rw [← e, c.iso.card_imgG hK]
  have hge : 64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah)) := by
    have h64 : Nat.card ↥(B6.conjSub g⁻¹ R) = 64 := by
      rw [conjSub_card, hcard]
      norm_num
    rw [← hcardT]
    have := Subgroup.card_le_of_le hle
    omega
  have hle64 := card_cent_le_64 ht'T (congrArg (fun x : Bh => (x : Ah)) ht'2) ht'1 ht'x
  have hEq : B6.conjSub g⁻¹ R = c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g) :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardT, conjSub_card, hcard]
      exact hle64.trans (by norm_num))
  have hcent := cent_eq_t0 ht'T (congrArg (fun x : Bh => (x : Ah)) ht'2) ht'1 ht'x hge
  obtain ⟨e3⟩ := cent_t0_equiv
  let e1 : ↥R ≃* ↥(B6.conjSub g⁻¹ R) := (MulAut.conj g⁻¹).subgroupMap R
  refine ⟨e1.trans ((MulEquiv.subgroupCongr hEq).trans ((MulEquiv.subgroupCongr e.symm).trans
    ((imgGEquiv c.iso hK).symm.trans ((MulEquiv.subgroupCongr hcent).trans e3))))⟩

end CFSG.Quasithin.H13.F431.U42Aut
