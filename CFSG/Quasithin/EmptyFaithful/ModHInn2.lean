module

public import CFSG.Quasithin.EmptyFaithful.ModHInn
public import CFSG.Quasithin.EmptyFaithful.ModHOut2
public import CFSG.Quasithin.EmptyFaithful.ModHOut1

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem ker_rho0_isPGroup (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hIeq : I = L ⊔ Sgp153 T V₁) :
    IsPGroup 2 (rho0 hN hcen).ker := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hcen2 : IsPGroup 2 (Subgroup.center ↥L) := SBd11.isPGroup_center_of_center_eq hZ
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
  have hS02 : IsPGroup 2 ↥(Sgp153 T V₁ ⊓ innerPart hN) :=
    hS2.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  exact ker_isPGroup (L := L) (I := innerPart hN) (S := Sgp153 T V₁ ⊓ innerPart hN)
    (le_innerPart hN hLI) ((innerPart_le hN).trans hN) (innerPart_eq_sup hN hLI hIeq hSI) hS02
    inf_le_right hcen2 (rho0 hN hcen) (rho0_mk hN hcen hLI)

omit [Finite G] in
theorem isPGroup_subgroupOf {S K : Subgroup G} (hS : IsPGroup 2 ↥S) : IsPGroup 2 ↥(S.subgroupOf K) := by
  intro x
  obtain ⟨k, hk⟩ := hS ⟨x.1.1, x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥S => ((z : ↥S) : G)) hk
  simpa using this

theorem isSylowTwoOf_img_S0 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) :
    IsSylowTwoOf (img (rho0 hN hcen) (Sgp153 T V₁)) ⊤ := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
  have hP2 : IsPGroup 2 ↥(img (rho0 hN hcen) (Sgp153 T V₁)) := by
    have h1 : IsPGroup 2 ↥((Sgp153 T V₁).subgroupOf (innerPart hN)) := isPGroup_subgroupOf hS2
    exact h1.of_surjective ((rho0 hN hcen).subgroupMap ((Sgp153 T V₁).subgroupOf (innerPart hN)))
      ((rho0 hN hcen).subgroupMap_surjective _)
  refine isSylowTwoOf_of_le_top (quotSylow_of_ctx c hN) ?_ hP2
  intro q hq
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
  refine mem_img.2 ⟨l, le_innerPart hN hLI l.2, (Subgroup.mem_subgroupOf.1 hl).1, ?_⟩
  rw [rho0_mk hN hcen hLI l]
  rfl

theorem solvable_nine_img_Yp0 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hLI : L ≤ I) (hYL : Yp ≤ L)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hker : IsPGroup 2 (rho0 hN hcen).ker) :
    Group.IsSolvable ↥(img (rho0 hN hcen) Yp) ∧ 9 ∣ Nat.card ↥(img (rho0 hN hcen) Yp) := by
  have hYI : Yp ≤ innerPart hN := hYL.trans (le_innerPart hN hLI)
  obtain ⟨b, k, hk2, -, hcard⟩ := SBd11.card_form_of_struct c.facts11.struct_Yp
  have hsolvY : Group.IsSolvable ↥Yp := isSolvable_of_struct c.facts11.struct_Yp
  let ψ : ↥Yp →* ↥L ⧸ Subgroup.center ↥L := (rho0 hN hcen).comp (Subgroup.inclusion hYI)
  have hrange : ψ.range = img (rho0 hN hcen) Yp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_img.2 ⟨y.1, hYI y.2, y.2, rfl⟩
    · intro hx
      obtain ⟨a, ha, haY, rfl⟩ := mem_img.1 hx
      exact ⟨⟨a, haY⟩, rfl⟩
  have hK2 : IsPGroup 2 ψ.ker := by
    intro z
    obtain ⟨m, hm⟩ := hker ⟨Subgroup.inclusion hYI z.1, z.2⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun w : ↥(rho0 hN hcen).ker => ((w : ↥(innerPart hN)) : G)) hm
    simpa using this
  have hsolv : Group.IsSolvable ↥(img (rho0 hN hcen) Yp) := by
    rw [← hrange]
    exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hprod := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 hK2
  have h3k : 3 ^ k ∣ Nat.card ψ.range := by
    have h1 : 3 ^ k ∣ Nat.card ψ.ker * Nat.card ψ.range := by
      rw [hprod, hcard]
      exact Dvd.intro_left _ rfl
    have hcop : Nat.Coprime (3 ^ k) (Nat.card ψ.ker) := by
      rw [hi]
      exact Nat.Coprime.pow k i (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h1
  have h9 : 9 ∣ Nat.card ψ.range := (pow_dvd_pow 3 hk2).trans h3k
  exact ⟨hsolv, by rw [← hrange]; exact h9⟩

omit [Finite G] in
theorem img_map_actQ (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) {A : Subgroup G} (s : ↥I)
    (hs : ∀ x : G, x ∈ A ↔ (s : G) * x * (s : G)⁻¹ ∈ A) :
    (img (rho0 hN hcen) A).map (actQ hN s).toMonoidHom = img (rho0 hN hcen) A := by
  ext q
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨q0, hq0, rfl⟩
    obtain ⟨a, ha, haA, rfl⟩ := mem_img.1 hq0
    have hsa : (s : G) * a * (s : G)⁻¹ ∈ innerPart hN := innerPart_conj_mem hN s.2 ha
    refine mem_img.2 ⟨(s : G) * a * (s : G)⁻¹, hsa, (hs a).1 haA, ?_⟩
    exact rho0_conj hN hcen s ⟨a, ha⟩
  · intro hq
    obtain ⟨a', ha', haA', rfl⟩ := mem_img.1 hq
    have ha : (s : G)⁻¹ * a' * (s : G) ∈ innerPart hN := by
      have := innerPart_conj_mem hN (I.inv_mem s.2) ha'
      simpa using this
    refine ⟨rho0 hN hcen ⟨(s : G)⁻¹ * a' * (s : G), ha⟩, mem_img.2 ⟨_, ha, ?_, rfl⟩, ?_⟩
    · rw [hs]
      simpa [mul_assoc] using haA'
    · have := rho0_conj hN hcen s ⟨(s : G)⁻¹ * a' * (s : G), ha⟩
      have h2 : (s : G) * ((s : G)⁻¹ * a' * (s : G)) * (s : G)⁻¹ = a' := by group
      simp only [h2] at this
      exact this.symm

end CFSG.Quasithin.ModH
