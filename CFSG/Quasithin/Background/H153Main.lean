module

public import CFSG.Quasithin.Background.H153Defs
import CFSG.Quasithin.Background.H153Std2
import CFSG.Quasithin.Background.H153Conj
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H CFSG.Quasithin.H156

private theorem exists_equiv_core' {numer denom : Subgroup (G6.PermMod 24)} {W : Type*}
    [CommGroup W] {V : Type*} [CommGroup V] (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (π : ↥Γ → MulAut V) (β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer)
    (hβs : ∀ q, ∃ u, β u = q) (hβ1 : ∀ v : V, β ⟨v, Subgroup.mem_top v⟩ = 1 → v = 1)
    (hβa : ∀ (γ : ↥Γ) (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m →
      β ⟨π γ v, Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨G6.permAct 24 γ m, (hΓ γ γ.2).1 m m.2⟩) :
    ∃ e : V ≃* W, (∀ (γ : ↥Γ) (v : V), e (π γ v) = c.rho Γ hΓ γ (e v)) ∧
      ∀ (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m → e v = c.κ m := by
  let κs : ↥numer →* W := c.κ.comp numer.subtype
  have hle : denom.subgroupOf numer ≤ κs.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    exact (c.ker_iff m m.2).2 (Subgroup.mem_subgroupOf.1 hm)
  let κb : ↥numer ⧸ denom.subgroupOf numer →* W := QuotientGroup.lift _ κs hle
  have hκb : ∀ m : ↥numer, κb (QuotientGroup.mk m) = c.κ m := fun _ => rfl
  let e₀ : V →* W := κb.comp (β.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom)
  have he₀ : ∀ v, e₀ v = κb (β ⟨v, Subgroup.mem_top v⟩) := fun _ => rfl
  have hinj : Function.Injective e₀ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [he₀] at hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
    rw [← hm, hκb] at hv
    have hmd : (m : G6.PermMod 24) ∈ denom := (c.ker_iff m m.2).1 hv
    have hm1 : (QuotientGroup.mk m : ↥numer ⧸ denom.subgroupOf numer) = 1 :=
      (QuotientGroup.eq_one_iff m).2 (Subgroup.mem_subgroupOf.2 hmd)
    exact hβ1 v (hm.symm.trans hm1)
  have hsurj : Function.Surjective e₀ := by
    intro w
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨c.lift w, c.lift_mem w⟩)
    refine ⟨(u : V), ?_⟩
    rw [he₀]
    have : (⟨(u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u := rfl
    rw [this, hu, hκb]
    exact c.κ_lift w
  have hbij : Function.Bijective e₀ := ⟨hinj, hsurj⟩
  refine ⟨MulEquiv.ofBijective e₀ hbij, fun γ v => ?_, fun v m hm => ?_⟩
  · rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
    rw [he₀, he₀, hβa γ v m hm.symm, hκb, ← hm, hκb]
    exact c.κ_permAct_rho Γ hΓ γ m.2
  · rw [MulEquiv.ofBijective_apply, he₀, hm, hκb]

private theorem congrHom_twist_rho' {V : Type} [CommGroup V] (ρ : ↥AutPerm →* MulAut V)
    (e : V ≃* W11)
    (hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v))
    (g γ : ↥AutPerm) :
    congrHom (twistEquiv e rhoM24 g⁻¹) (ρ γ) = rho11 AutPerm le_rfl (g⁻¹ * γ * g) := by
  refine MulEquiv.ext fun w => ?_
  have h1 : (rhoM24 g⁻¹).symm w = rhoM24 g w := by
    rw [MulEquiv.symm_apply_eq, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have h3 : ∀ x : W11, congrHom e (ρ γ) x = rho11 AutPerm le_rfl γ x := fun x =>
    (congrHom_apply e (ρ γ) x).trans ((hcompat γ _).trans (congrArg _ (e.apply_symm_apply x)))
  have h4 : rho11 AutPerm le_rfl (g⁻¹ * γ * g) = rhoM24 g⁻¹ * rhoM24 γ * rhoM24 g := by
    rw [map_mul, map_mul]
  refine (congrHom_twist_apply e rhoM24 g⁻¹ (ρ γ) w).trans ?_
  rw [h1, h3, h4]
  exact ((MulAut.mul_apply W11 (rhoM24 g⁻¹ * rhoM24 γ) (rhoM24 g) w).trans
    (MulAut.mul_apply W11 (rhoM24 g⁻¹) (rhoM24 γ) (rhoM24 g w))).symm

private theorem mem_map_cj_iff {c : S24} {A : Subgroup S24} {x : S24} :
    x ∈ A.map (cjS c).toMonoidHom ↔ c⁻¹ * x * c ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : c⁻¹ * (cjS c).toMonoidHom a * c = a := by
      show c⁻¹ * (c * a * c⁻¹) * c = a
      group
    rw [this]
    exact ha
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    show c * (c⁻¹ * x * c) * c⁻¹ = x
    group

private theorem rho11_inv_apply (g : ↥AutPerm) (w : W11) :
    rhoM24 g⁻¹ (rhoM24 g w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem isDualOfConj_conj' {V : Type*} [CommGroup V] (ρ ρ' : ↥M24g →* MulAut V)
    (c : ↥M24g) (hρ' : ρ' = ρ.comp (MulAut.conj c).toMonoidHom) {G K : Subgroup S24}
    {A B : Subgroup V} (h : IsDualOfConj' ρ' G A B K) :
    IsDualOfConj' ρ (G.map (cjS (c : S24)).toMonoidHom) A B
      (K.map (cjS (c : S24)).toMonoidHom) := by
  subst hρ'
  exact isDualOfConj_conj ρ c h

theorem h153_main
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (cfg : Cfg14 a b O Tr S B T₀) {V : Type} [CommGroup V]
    (ρ : ↥M24g →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (hreal : RealizesBy (mathModel false 24 a b M24g) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ V₇ : Subgroup V, Chain153' a b β ρ S V₇ ∧
      FullTranspCenter' (rImg ρ (MY M24g S)) (rImg ρ (KY M24g S)) V₇
        (fixV (rImg ρ (KY M24g S))) ∧
      xiSub (rImg ρ (KY M24g S)) = ⊤ ∧
      (∀ x : V, x ∈ V₇ ↔ ∀ g ∈ rImg ρ (KY M24g S), g x * x⁻¹ ∈ fixV (rImg ρ (KY M24g S))) := by
  have hreal' : RealizesBy (FFModel.golaySec M24g (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
      ρ.rangeRestrict β := hreal
  obtain ⟨-, -, -, -, -, -, -, hβs, hβ1, hβa⟩ := hreal'
  obtain ⟨e, he, hκ⟩ := exists_equiv_core' cocodeCoords (fun _ hσ => preserves_cocode hσ)
    (fun γ => ρ γ) β hβs (fun v hv => Subgroup.mem_bot.1 ((hβ1 _).1 hv))
    (fun γ v m hm => hβa γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hm)
  have hκ' : ∀ (v : V) (m : ↥(mathModel false 24 a b M24g).sec),
      β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m →
        e v = cocodeCoords.κ ((show ↥(G6.coreMod 24) from m) : G6.PermMod 24) :=
    hκ
  have hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v) :=
    fun γ v => he γ v
  obtain ⟨h, hh, hSh⟩ := sextet_normal_form cfg.sextet
  obtain ⟨c, hch⟩ : ∃ c : ↥M24g, (c : S24) = h := ⟨⟨h, hh⟩, rfl⟩
  have hMY : MY M24g S = (MY M24g S0).map (cjS (c : S24)).toMonoidHom := by
    rw [hch, hSh]
    exact MY_conj hh
  have hKY : KY M24g S = (KY M24g S0).map (cjS (c : S24)).toMonoidHom := by
    rw [hch, hSh]
    exact KY_conj hh
  obtain ⟨eg, hegdef⟩ : ∃ eg : V ≃* W11, eg = twistEquiv e rhoM24 c⁻¹ := ⟨_, rfl⟩
  have hcg : ∀ γ : ↥M24g, congrHom eg (ρ γ) = rho11 AutPerm le_rfl (c⁻¹ * γ * c) := fun γ => by
    rw [hegdef]
    exact congrHom_twist_rho' ρ e hcompat c γ
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ↥M24g →* MulAut V, ρ' = ρ.comp (MulAut.conj c).toMonoidHom :=
    ⟨_, rfl⟩
  have hρ'app : ∀ γ : ↥M24g, ρ' γ = ρ (c * γ * c⁻¹) := fun γ => by
    rw [hρ']
    exact rho_comp_conj_apply ρ c γ
  have hc' : ∀ (γ : ↥M24g) (v : V), eg (ρ' γ v) = rho11 AutPerm le_rfl γ (eg v) := by
    intro γ v
    have h1 : eg (ρ' γ v) = congrHom eg (ρ (c * γ * c⁻¹)) (eg v) := by
      rw [hρ'app]
      exact (congrHom_apply_eg eg (ρ (c * γ * c⁻¹)) v).symm
    refine h1.trans ?_
    have h3 : c⁻¹ * (c * γ * c⁻¹) * c = γ := by group
    exact congrArg (fun φ : MulAut W11 => φ (eg v))
      ((hcg (c * γ * c⁻¹)).trans (congrArg (rho11 AutPerm le_rfl) h3))
  obtain ⟨V₇, z, hez, hfix, hconc⟩ := h153_std ρ' eg hc'
  have hRM : rImg ρ ((MY M24g S0).map (cjS (c : S24)).toMonoidHom) = rImg ρ' (MY M24g S0) := by
    rw [hρ']
    exact (rImg_comp_conj ρ c _).symm
  have hRK : rImg ρ ((KY M24g S0).map (cjS (c : S24)).toMonoidHom) = rImg ρ' (KY M24g S0) := by
    rw [hρ']
    exact (rImg_comp_conj ρ c _).symm
  obtain ⟨hc1, hc2, hc4, hc5, hc6, hc7, ⟨N, hN1, hN2, hN3, hN4⟩, hc9, hc10, hc11⟩ := hconc
  refine ⟨V₇, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hMY, hKY, hRM, hRK]
    exact hc1
  · rw [hKY, hRK]
    exact hc2
  ·
    intro B' hB'
    rw [hKY, hRK]
    refine ⟨z, ?_, hfix⟩
    rw [hSh] at hB'
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_smul_finset.1 hB'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB₀
    have hmem : eY (h • colF j) ∈ (mathModel false 24 a b M24g).sec := by
      show eY (h • colF j) ∈ G6.coreMod 24
      rw [eY_smul]
      exact (preserves_cocode hh).1 _ (eY_colF_mem_coreMod j)
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨eY (h • colF j), hmem⟩)
    have hκu : e (u : V) = cocodeCoords.κ (eY (h • colF j)) :=
      hκ' (u : V) ⟨eY (h • colF j), hmem⟩ hu
    have hκ2 : cocodeCoords.κ (eY (h • colF j)) = rho11 AutPerm le_rfl c z0 := by
      rw [eY_smul, ← hch]
      have := SecCoords.κ_permAct_rho cocodeCoords M24g (fun _ hσ => preserves_cocode hσ) c
        (eY_colF_mem_coreMod j)
      rw [kappa_colF] at this
      exact this
    have heg : eg (u : V) = z0 := by
      rw [hegdef]
      show rhoM24 c⁻¹ (e (u : V)) = z0
      rw [hκu, hκ2]
      exact rho11_inv_apply c z0
    have hueq : (u : V) = z := eg.injective (heg.trans hez.symm)
    refine ⟨hmem, ?_⟩
    have hu' : β ⟨(u : V), Subgroup.mem_top _⟩ = QuotientGroup.mk ⟨eY (h • colF j), hmem⟩ := hu
    rw [hueq] at hu'
    exact hu'
  · rw [hMY, hKY, hRM, hRK]
    exact hc4
  · rw [hMY, hRM]
    exact hc5
  · exact hc6
  · rw [hMY, hKY, hRK]
    exact isDualOfConj_conj' ρ ρ' c hρ' hc7
  · rw [hMY, hRM]
    refine ⟨N.map (cjS (c : S24)).toMonoidHom, isO23_map _ hN1, exists_pi_map _ hN2, ?_, hN4⟩
    ·
      intro g hg
      have hg' : (c : S24)⁻¹ * (g : S24) * (c : S24) ∈ MY M24g S0 := mem_map_cj_iff.1 hg
      have hgA : (c : S24)⁻¹ * (g : S24) * (c : S24) ∈ M24g :=
        M24g.mul_mem (M24g.mul_mem (M24g.inv_mem c.2) g.2) c.2
      have hρ : ρ' (⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hgA⟩ : ↥M24g) = ρ g := by
        rw [hρ'app]
        congr 1
        apply Subtype.ext
        show (c : S24) * ((c : S24)⁻¹ * (g : S24) * (c : S24)) * (c : S24)⁻¹ = g
        group
      have h1 := hN3 ⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hgA⟩ hg'
      rw [hρ] at h1
      rw [h1, mem_map_cj_iff]
  · rw [hMY, hKY, hRM, hRK]
    exact hc9
  · rw [hKY, hRK]
    exact hc10
  · rw [hKY, hRK]
    exact hc11

end CFSG.Quasithin.H153
