module

import CFSG.Quasithin.Background.H156Std
import CFSG.Quasithin.Background.H156Tr
import CFSG.Quasithin.Background.H158UHB
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.Background.H158TNF
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.Sporadic.Schreier.J4SSylowBase
import CFSG.Quasithin.Background.H156Tri

public section

open scoped Matrix Pointwise

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.ASVolI.ChH CFSG.Quasithin.H

@[expose] def Chain156' {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (Tr : Finset (Finset (Fin 24))) (V₉ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) ⊥ (fixV (rImg ρ (KY Γ Tr))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Tr))) = 3 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) (fixV (rImg ρ (KY Γ Tr))) V₉ ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) V₉ ⊤ ∧
  V₉ = CFSG.Quasithin.commV (rImg ρ (perfectCore (MY Γ Tr))) ∧
  V₉ = CFSG.Quasithin.commV (rImg ρ (KY Γ Tr)) ∧ rkIdx V₉ = 2 ∧
  InducesOn (rImg ρ (MY Γ Tr)) (fixV (rImg ρ (KY Γ Tr))) ⊥ (Multiplicative (Fin 3 → ZMod 2))
    (natSub 3 (ZMod 2) ⊤) ∧
  InducesOn (rImg ρ (MY Γ Tr)) ⊤ V₉ (Multiplicative (Fin 2 → ZMod 2)) (natSub 2 (ZMod 2) ⊤) ∧
  InducesOn (rImg ρ (MY Γ Tr)) V₉ (fixV (rImg ρ (KY Γ Tr)))
    (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) (Subgroup.closure tensorSet32)

@[expose] def TensorFactors156' {V : Type*} [CommGroup V] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (Tr : Finset (Finset (Fin 24))) (V₉ : Subgroup V) : Prop :=
  ∃ (quotientAction : ↥(MY Γ Tr) →* (GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2)))
    (tensorIdentification : ↥V₉ →* Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))),
    Function.Surjective quotientAction ∧
    quotientAction.ker = (KY Γ Tr).subgroupOf (MY Γ Tr) ∧
    Function.Surjective tensorIdentification ∧
    tensorIdentification.ker = (fixV (rImg ρ (KY Γ Tr))).subgroupOf V₉ ∧
    ∀ (acting : ↥Γ) (hacting : (acting : S24) ∈ MY Γ Tr)
      (original transported : ↥V₉), (transported : V) = ρ acting (original : V) →
        Multiplicative.toAdd (tensorIdentification transported) =
          ((quotientAction ⟨(acting : S24), hacting⟩).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            Multiplicative.toAdd (tensorIdentification original) *
            ((quotientAction ⟨(acting : S24), hacting⟩).2 : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ

private theorem AutPerm_map_conj {h : Equiv.Perm (Fin 24)} (hh : h ∈ AutPerm) :
    AutPerm.map (MulAut.conj h).toMonoidHom = AutPerm := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact AutPerm.mul_mem (AutPerm.mul_mem hh hy) (AutPerm.inv_mem hh)
  · intro hx
    refine ⟨h⁻¹ * x * h, AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hh) hx) hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem MY_conj
    {h : Equiv.Perm (Fin 24)}
    (hh : h ∈ AutPerm) : MY M24g (h • labTrio) = stabUTP.map (MulAut.conj h).toMonoidHom := by
  have e1 : MY M24g (h • labTrio) =
      AutPerm ⊓ (MulAction.stabilizer S24 labTrio).map (MulAut.conj h).toMonoidHom := by
    unfold MY
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rfl
  rw [e1, stabUTP_eq, Subgroup.map_inf _ _ _ (MulAut.conj h).injective, AutPerm_map_conj hh]

private theorem KY_conj
    {h : Equiv.Perm (Fin 24)}
    (hh : h ∈ AutPerm) : KY M24g (h • labTrio) = Kperm.map (MulAut.conj h).toMonoidHom := by
  unfold KY
  rw [MY_conj hh, pCoreOf_map_of_injective 2 _ (MulAut.conj h).injective, pCoreOf_stabUTP]

private theorem perfectCore_conj
    {h : Equiv.Perm (Fin 24)}
    (hh : h ∈ AutPerm) :
    perfectCore (MY M24g (h • labTrio)) = trQ.map (MulAut.conj h).toMonoidHom := by
  rw [MY_conj hh, ← map_perfectCore, perfectCore_stabUTP']

private theorem rImg_conj_map {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (g : ↥M24g)
    (eg : V ≃* W11) (hcg : ∀ γ : ↥M24g, congrHom eg (ρ γ) = rhoM24 (g⁻¹ * γ * g))
    {A : Subgroup S24} (hA : A ≤ AutPerm) :
    (rImg ρ (A.map (MulAut.conj (g : S24)).toMonoidHom)).map (congrHom eg) = img11 A := by
  ext φ
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨a, haA, hay⟩ := Subgroup.mem_subgroupOf.1 hy
    have hya : (g : S24)⁻¹ * (y : S24) * (g : S24) = a := by
      rw [← hay]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨⟨a, hA haA⟩, Subgroup.mem_subgroupOf.2 haA, ?_⟩
    rw [hcg y]
    exact congrArg rhoM24 (Subtype.ext hya.symm)
  · rintro ⟨x, hx, rfl⟩
    have hxA : (x : S24) ∈ A := Subgroup.mem_subgroupOf.1 hx
    let x' : ↥M24g := ⟨(x : S24), x.2⟩
    refine ⟨ρ (g * x' * g⁻¹), ⟨g * x' * g⁻¹, ?_, rfl⟩, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨x, hxA, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rfl
    · rw [hcg]
      refine congrArg rhoM24 (Subtype.ext ?_)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
      rfl

private theorem UT_lt_V9 : UT < V9 :=
  lt_of_le_of_ne UT_le_V9 fun h => by
    have := card_UT
    rw [h, card_V9] at this
    omega

private theorem V9_lt_top : V9 < ⊤ :=
  lt_of_le_of_ne le_top fun h => by
    have h1 := card_V9
    rw [h, Subgroup.card_top, Nat.card_eq_fintype_card, card_Wn] at h1
    omega

theorem h156_main
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (cfg : Cfg14 a b O Tr S B T₀) {V : Type} [CommGroup V]
    (ρ : ↥M24g →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (hreal : RealizesBy (mathModel false 24 a b M24g) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ V₉ : Subgroup V, Chain156' ρ Tr V₉ ∧ TensorFactors156' ρ Tr V₉ := by
  have hreal' : RealizesBy (FFModel.golaySec M24g (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
      ρ.rangeRestrict β := hreal
  obtain ⟨e, he⟩ := SecCoords.exists_equiv cocodeCoords (fun _ hσ => preserves_cocode hσ) hreal'
  have hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v) :=
    fun γ v => he γ v
  have hinj : Function.Injective ρ := rho_injective ρ e hcompat
  obtain ⟨hTrcard, hTroct, hTrdisj, hTrcov⟩ := cfg.trio
  obtain ⟨h, hh, hTrh⟩ := trio_normal_form T₀ cfg.sylow Tr hTrcard
    (fun O' hO' => (hTroct O' hO').1) hTrdisj hTrcov cfg.stab_Tr
  obtain ⟨g, hgdef⟩ : ∃ g : ↥M24g, g = ⟨h, hh⟩ := ⟨_, rfl⟩
  have hgh : (g : S24) = h := by rw [hgdef]
  obtain ⟨eg, heg⟩ : ∃ eg : V ≃* W11, eg = twistEquiv e rhoM24 g⁻¹ := ⟨_, rfl⟩
  have hcg : ∀ γ : ↥M24g, congrHom eg (ρ γ) = rhoM24 (g⁻¹ * γ * g) := by
    intro γ
    rw [heg]
    exact congrHom_twist_rho ρ e hcompat g γ
  have hMY : MY M24g Tr = stabUTP.map (MulAut.conj (g : S24)).toMonoidHom := by
    rw [hgh, hTrh]; exact MY_conj hh
  have hKY : KY M24g Tr = Kperm.map (MulAut.conj (g : S24)).toMonoidHom := by
    rw [hgh, hTrh]; exact KY_conj hh
  have hPC : perfectCore (MY M24g Tr) = trQ.map (MulAut.conj (g : S24)).toMonoidHom := by
    rw [hgh, hTrh]; exact perfectCore_conj hh
  have hG : (rImg ρ (MY M24g Tr)).map (congrHom eg) = img11 stabUTP := by
    rw [hMY]; exact rImg_conj_map ρ g eg hcg stabUTP_le_autPerm
  have hK : (rImg ρ (KY M24g Tr)).map (congrHom eg) = img11 Kperm := by
    rw [hKY]; exact rImg_conj_map ρ g eg hcg Kperm_le_aut
  have hP : (rImg ρ (perfectCore (MY M24g Tr))).map (congrHom eg) = img11 trQ := by
    rw [hPC]; exact rImg_conj_map ρ g eg hcg trQ_le
  have hV3 : (fixV (rImg ρ (KY M24g Tr))).map eg.toMonoidHom = UT :=
    ((fixV_map_congrHom eg _).symm.trans (congrArg fixV hK)).trans
      ((congrArg fixV img11_Kperm).trans fixV_ktCent)
  have hV9 : (CFSG.Quasithin.commV (rImg ρ (KY M24g Tr))).map eg.toMonoidHom = V9 :=
    ((commV_map_congrHom eg _).symm.trans (congrArg CFSG.Quasithin.commV hK)).trans
      commV_img11_Kperm
  have hVP : (CFSG.Quasithin.commV (rImg ρ (perfectCore (MY M24g Tr)))).map eg.toMonoidHom = V9 :=
    ((commV_map_congrHom eg _).symm.trans (congrArg CFSG.Quasithin.commV hP)).trans
      commV_img11_trQ
  set V₃ := fixV (rImg ρ (KY M24g Tr)) with hV₃
  set V₉ := CFSG.Quasithin.commV (rImg ρ (KY M24g Tr)) with hV₉
  set G := rImg ρ (MY M24g Tr) with hGdef
  have hc3 : Nat.card ↥V₃ = 8 :=
    (Subgroup.card_map_of_injective (f := eg.toMonoidHom) eg.injective (K := V₃)).symm.trans
      ((congrArg (fun K : Subgroup W11 => Nat.card ↥K) hV3).trans card_UT)
  have hlt3 : (⊥ : Subgroup V) < V₃ := by
    refine lt_of_le_of_ne bot_le fun hh => ?_
    have h1 : Nat.card ↥V₃ = 1 := by
      rw [← hh]
      simp
    omega
  have hlt39 : V₃ < V₉ :=
    (Subgroup.map_lt_map_iff_of_injective (f := eg.toMonoidHom) eg.injective).1
      (by rw [hV3, hV9]; exact UT_lt_V9)
  have hlt9 : V₉ < ⊤ :=
    (Subgroup.map_lt_map_iff_of_injective (f := eg.toMonoidHom) eg.injective).1
      (by rw [hV9, Subgroup.map_top_of_surjective eg.toMonoidHom eg.surjective]; exact V9_lt_top)
  have hI3 : InducesOn G V₃ ⊥ (Multiplicative (Fin 3 → ZMod 2)) (natSub 3 (ZMod 2) ⊤) :=
    inducesOn_of_map' eg hG hV3 (Subgroup.map_bot eg.toMonoidHom) std_ind3
  have hI2 : InducesOn G ⊤ V₉ (Multiplicative (Fin 2 → ZMod 2)) (natSub 2 (ZMod 2) ⊤) :=
    inducesOn_of_map' eg hG (Subgroup.map_top_of_surjective eg.toMonoidHom eg.surjective) hV9
      std_ind2
  have hIT : InducesOn G V₉ V₃ (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2)))
      (Subgroup.closure tensorSet32) :=
    inducesOn_of_map' eg hG hV9 hV3 std_indT
  have c1 : IsChiefFactorUnder (actsOnModule G) ⊥ V₃ := chief_of_inducesOn hI3 hlt3 irred3
  have c2 : rk ↥V₃ = 3 := rk_eq_of_natCard 3 (hc3.trans (by norm_num))
  have c3 : IsChiefFactorUnder (actsOnModule G) V₃ V₉ := chief_of_inducesOn hIT hlt39 irrT
  have c4 : IsChiefFactorUnder (actsOnModule G) V₉ ⊤ := chief_of_inducesOn hI2 hlt9 irred2
  have c5 : V₉ = CFSG.Quasithin.commV (rImg ρ (perfectCore (MY M24g Tr))) := by
    apply Subgroup.map_injective (f := eg.toMonoidHom) eg.injective
    exact hV9.trans hVP.symm
  have c7 : rkIdx V₉ = 2 := by
    show padicValNat 2 V₉.index = 2
    rw [← Subgroup.index_map_equiv V₉ eg]
    exact (congrArg (fun K : Subgroup W11 => padicValNat 2 K.index) hV9).trans rkIdx_V9
  have hchain : Chain156' ρ Tr V₉ := ⟨c1, c2, c3, c4, c5, rfl, c7, hI3, hI2, hIT⟩
  refine ⟨V₉, hchain, ?_⟩
  have hMYle : MY M24g Tr ≤ M24g := fun σ hσ => hσ.1
  have hψmem : ∀ σ : ↥(MY M24g Tr),
      congrHom eg (ρ (Subgroup.inclusion hMYle σ)) ∈ img11 stabUTP := by
    intro σ
    rw [← hG]
    exact ⟨ρ (Subgroup.inclusion hMYle σ),
      ⟨Subgroup.inclusion hMYle σ, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩, rfl⟩
  let ψ : ↥(MY M24g Tr) →* ↥(img11 stabUTP) :=
    ((congrHom eg).comp (ρ.comp (Subgroup.inclusion hMYle))).codRestrict (img11 stabUTP) hψmem
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    rw [← hG] at hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
    exact ⟨⟨(z : S24), Subgroup.mem_subgroupOf.1 hz⟩, rfl⟩
  let qa : ↥(MY M24g Tr) →* GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) :=
    ((invTGL 3).prodMap (MonoidHom.id _)).comp (Psi.comp ψ)
  have hqa_surj : Function.Surjective qa := by
    intro p
    obtain ⟨y, hy⟩ := Psi_surjective (invTGL 3 p.1, p.2)
    obtain ⟨σ, rfl⟩ := hψsurj y
    refine ⟨σ, ?_⟩
    show (invTGL 3 (Psi (ψ σ)).1, (Psi (ψ σ)).2) = p
    rw [hy]
    exact Prod.ext (invTGL_invTGL p.1) rfl
  have hqa_ker : qa.ker = (KY M24g Tr).subgroupOf (MY M24g Tr) := by
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have key : qa σ = 1 ↔ Psi (ψ σ) = 1 := by
      constructor
      · intro hq
        have h1 : invTGL 3 (Psi (ψ σ)).1 = 1 := congrArg Prod.fst hq
        have h2 := congrArg Prod.snd hq
        refine Prod.ext ?_ h2
        have h3 := congrArg (invTGL 3) h1
        rwa [invTGL_invTGL, map_one] at h3
      · intro hq
        show (invTGL 3 (Psi (ψ σ)).1, (Psi (ψ σ)).2) = 1
        rw [hq]
        exact Prod.ext (map_one _) rfl
    have h1 : Psi (ψ σ) = 1 ↔ ((ψ σ : ↥(img11 stabUTP)) : MulAut W11) ∈ img11 Kperm := by
      rw [← MonoidHom.mem_ker, Psi_ker, Subgroup.mem_subgroupOf, ← img11_Kperm]
    have h2 : ((ψ σ : ↥(img11 stabUTP)) : MulAut W11) ∈ img11 Kperm ↔
        ρ (Subgroup.inclusion hMYle σ) ∈ rImg ρ (KY M24g Tr) := by
      rw [← hK]
      exact Subgroup.mem_map_iff_mem (congrHom_injective eg)
    have h3 : ρ (Subgroup.inclusion hMYle σ) ∈ rImg ρ (KY M24g Tr) ↔ (σ : S24) ∈ KY M24g Tr :=
      (Subgroup.mem_map_iff_mem hinj).trans Subgroup.mem_subgroupOf
    exact key.trans (h1.trans (h2.trans h3))
  let tI : ↥V₉ →* Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2)) :=
    beta6.comp (eg.toMonoidHom.comp V₉.subtype)
  have hmemV9 : ∀ u : ↥V₉, eg (u : V) ∈ V9 := by
    intro u
    have := Subgroup.mem_map_of_mem eg.toMonoidHom u.2
    rwa [hV9] at this
  have htI_surj : Function.Surjective tI := by
    intro X
    obtain ⟨x, hx, hX⟩ := beta6_surj_V9 X
    rw [← hV9] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨⟨u, hu⟩, hX⟩
  have htI_ker : tI.ker = V₃.subgroupOf V₉ := by
    refine Subgroup.ext fun u => ?_
    have h1 : beta6 (eg (u : V)) = 1 ↔ eg (u : V) ∈ UT := beta6_ker_V9 (hmemV9 u)
    have h2 : eg (u : V) ∈ UT ↔ (u : V) ∈ V₃ := by
      rw [← hV3]
      exact Subgroup.mem_map_iff_mem (f := eg.toMonoidHom) eg.injective
    exact h1.trans h2
  refine ⟨qa, tI, hqa_surj, hqa_ker, htI_surj, htI_ker, ?_⟩
  intro acting hacting original transported htr
  let σ : ↥(MY M24g Tr) := ⟨(acting : S24), hacting⟩
  have hx := (Psi_spec (ψ σ)).2.2 (eg (original : V)) (hmemV9 original)
  have hψval : ((ψ σ : ↥(img11 stabUTP)) : MulAut W11) = congrHom eg (ρ acting) := rfl
  have hψ : ((ψ σ : ↥(img11 stabUTP)) : MulAut W11) (eg (original : V)) = eg (transported : V) :=
    (congrArg (fun φ : MulAut W11 => φ (eg (original : V))) hψval).trans
      ((congrHom_apply_eg eg (ρ acting) (original : V)).trans (congrArg eg htr.symm))
  rw [hψ] at hx
  exact congrArg Multiplicative.toAdd hx

end CFSG.Quasithin.H156
