module

public import CFSG.Quasithin.Background.H156Ind2

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.ASVolI.ChH

theorem img11_mono {A B : Subgroup (Equiv.Perm (Fin 24))} (h : A ≤ B) : img11 A ≤ img11 B :=
  Subgroup.map_mono fun x hx => h hx

theorem card_GL3 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem card_GL2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

section Cnt


theorem H_le_good' : img11 stabUTP ≤ GoodSub := H_le_good

@[expose] noncomputable def Psi :
    ↥(img11 stabUTP) →* GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) :=
  Psi0.comp (Subgroup.inclusion H_le_good')

theorem Psi_apply (g : ↥(img11 stabUTP)) : Psi g = Psi0 (Subgroup.inclusion H_le_good' g) := rfl

theorem Psi_spec (g : ↥(img11 stabUTP)) : PsiSpec g.1 (Psi g).1 (Psi g).2 := by
  rw [Psi_apply]
  exact Psi0_spec (Subgroup.inclusion H_le_good' g)

theorem Psi_eq {g : ↥(img11 stabUTP)} {a : GL (Fin 3) (ZMod 2)} {c : GL (Fin 2) (ZMod 2)}
    (h : PsiSpec g.1 a c) : Psi g = (a, c) := by
  rw [Psi_apply]
  exact Psi0_eq (g := Subgroup.inclusion H_le_good' g) h

theorem H_stab_UT {g : MulAut W11} (hg : g ∈ img11 stabUTP) : g ∈ stabSub UT :=
  (H_le_good hg).1

theorem H_stab_V9 {g : MulAut W11} (hg : g ∈ img11 stabUTP) : g ∈ stabSub V9 :=
  (H_le_good hg).2.1

theorem card_H : Nat.card ↥(img11 stabUTP) = 64512 := by
  obtain ⟨hcS, -, -⟩ := CFSG.Quasithin.H158U.stab_facts
  rw [card_img11 stabUTP_le_autPerm, hcS]

theorem trQ_img_le_H : img11 trQ ≤ img11 stabUTP := img11_mono trQ_le_stabUTP

theorem gT3_mem_H : gT3 ∈ img11 stabUTP := by
  rw [img11_stabUTP]
  exact Subgroup.subset_closure (by simp [genSet])

theorem gT2_mem_H : gT2 ∈ img11 stabUTP := by
  rw [img11_stabUTP]
  exact Subgroup.subset_closure (by simp [genSet])

@[expose] noncomputable def Psi2 : ↥(img11 stabUTP) →* GL (Fin 2) (ZMod 2) :=
  (MonoidHom.snd _ _).comp Psi

theorem Psi2_apply (g : ↥(img11 stabUTP)) : Psi2 g = (Psi g).2 := rfl

theorem Psi_gT3 : Psi ⟨gT3, gT3_mem_H⟩ = (aT3, cT3) := Psi_eq psiSpec_gT3

theorem Psi_gT2 : Psi ⟨gT2, gT2_mem_H⟩ = (aT2, cT2) := Psi_eq psiSpec_gT2

theorem Psi2_surjective : Function.Surjective Psi2 := by
  have h3 : Psi2 ⟨gT3, gT3_mem_H⟩ = cT3 := by rw [Psi2_apply, Psi_gT3]
  have h2 : Psi2 ⟨gT2, gT2_mem_H⟩ = cT2 := by rw [Psi2_apply, Psi_gT2]
  have hc : ∀ c : GL (Fin 2) (ZMod 2), c = 1 ∨ c = cT3 ∨ c = cT3 * cT3 ∨ c = cT2 ∨
      c = cT3 * cT2 ∨ c = cT3 * cT3 * cT2 := by decide +kernel
  intro c
  rcases hc c with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨_, h3⟩
  · exact ⟨⟨gT3, gT3_mem_H⟩ * ⟨gT3, gT3_mem_H⟩, by rw [map_mul, h3]⟩
  · exact ⟨_, h2⟩
  · exact ⟨⟨gT3, gT3_mem_H⟩ * ⟨gT2, gT2_mem_H⟩, by rw [map_mul, h3, h2]⟩
  · exact ⟨⟨gT3, gT3_mem_H⟩ * ⟨gT3, gT3_mem_H⟩ * ⟨gT2, gT2_mem_H⟩, by
      rw [map_mul, map_mul, h3, h2]⟩

theorem Psi2_eq_one_iff (g : ↥(img11 stabUTP)) : Psi2 g = 1 ↔ g.1 ∈ Ntriv := by
  have hs := (Psi_spec g).2.1
  constructor
  · intro h x
    have h1 : (Psi g).2 = 1 := h
    rw [hs x, h1]
    exact natHom_one_apply 2 _
  · intro h
    apply natHom_injective 2
    refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := beta2_surjective w
    exact (hs x).symm.trans ((h x).trans (natHom_one_apply 2 _).symm)

theorem H_inf_Ntriv : img11 stabUTP ⊓ Ntriv = img11 trQ := by
  obtain ⟨-, -, hQ10⟩ := CFSG.Quasithin.H158U.stab_facts
  have hker : Psi2.ker = (img11 stabUTP ⊓ Ntriv).subgroupOf (img11 stabUTP) := by
    ext g
    rw [MonoidHom.mem_ker, Psi2_eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_ker_mul_card_range Psi2
  rw [MonoidHom.range_eq_top_of_surjective _ Psi2_surjective, Subgroup.card_top, card_GL2,
    card_H, hker] at h1
  have hc : Nat.card ↥(img11 stabUTP ⊓ Ntriv) = 10752 := by
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : img11 stabUTP ⊓ Ntriv ≤ img11 stabUTP)).toEquiv
    omega
  have hle : img11 trQ ≤ img11 stabUTP ⊓ Ntriv := le_inf trQ_img_le_H img11_trQ_le_Ntriv
  have hQc : Nat.card ↥(img11 trQ) = 10752 := (card_img11 trQ_le).trans hQ10
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem fix_of_inj {V A : Type*} [CommGroup V] [CommGroup A] (β : V →* A) (U : Subgroup V)
    (hinj : ∀ u ∈ U, β u = 1 → u = 1) {g : MulAut V} (hg : g ∈ stabSub U)
    (h : ∀ u ∈ U, β (g u) = β u) : g ∈ centSub U := by
  intro u hu
  have hgu : g u ∈ U := (mem_stabSub.1 hg u).2 hu
  have h1 : β (g u * u⁻¹) = 1 := by
    rw [map_mul, h u hu, ← map_mul, mul_inv_cancel, map_one]
  have h2 : g u * u⁻¹ = 1 := hinj _ (U.mul_mem hgu (U.inv_mem hu)) h1
  exact mul_inv_eq_one.1 h2

theorem natHom_eq_one_of {n : ℕ} (β : W11 →* Wn n) (U : Subgroup W11)
    (hsurj : ∀ w : Wn n, ∃ u ∈ U, β u = w) {g : MulAut W11} {a : GL (Fin n) (ZMod 2)}
    (hs : ∀ u ∈ U, β (g u) = natHom n (ZMod 2) a (β u)) (hfix : g ∈ centSub U) : a = 1 := by
  apply natHom_injective n
  refine MulEquiv.ext fun w => ?_
  obtain ⟨u, hu, rfl⟩ := hsurj w
  have e : g u = u := hfix u hu
  exact (hs u hu).symm.trans ((congrArg β e).trans (natHom_one_apply n _).symm)

theorem Psi_ker : Psi.ker = (img11 trQ ⊓ centSub UT).subgroupOf (img11 stabUTP) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hs := Psi_spec g
  constructor
  · intro h
    have ha : (Psi g).1 = 1 := congrArg Prod.fst h
    have hc : (Psi g).2 = 1 := congrArg Prod.snd h
    have hcent : (g.1 : MulAut W11) ∈ centSub UT := by
      refine fix_of_inj beta3 UT (fun u hu => beta3_inj_UT hu) (H_stab_UT g.2) (fun u hu => ?_)
      exact (hs.1 u hu).trans ((congrArg (fun a => natHom 3 (ZMod 2) a (beta3 u)) ha).trans
        (natHom_one_apply 3 _))
    have hN : g.1 ∈ Ntriv := (Psi2_eq_one_iff g).1 hc
    have hmem : (g.1 : MulAut W11) ∈ img11 stabUTP ⊓ Ntriv := ⟨g.2, hN⟩
    rw [H_inf_Ntriv] at hmem
    exact ⟨hmem, hcent⟩
  · rintro ⟨hQ, hcent⟩
    have hN : (g.1 : MulAut W11) ∈ Ntriv := img11_trQ_le_Ntriv hQ
    have ha : (Psi g).1 = 1 := natHom_eq_one_of beta3 UT beta3_surj_UT hs.1 hcent
    exact Prod.ext ha ((Psi2_eq_one_iff g).2 hN)

theorem Psi_surjective : Function.Surjective Psi := by
  obtain ⟨-, -, hQ10⟩ := CFSG.Quasithin.H158U.stab_facts
  have h1 := Subgroup.card_ker_mul_card_range Psi
  have hle : img11 trQ ⊓ centSub UT ≤ img11 stabUTP := inf_le_left.trans trQ_img_le_H
  have hk : Nat.card ↥Psi.ker = 64 := by
    rw [Psi_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_ktCent
  rw [card_H, hk] at h1
  have hr : Nat.card ↥Psi.range = 1008 := by omega
  have hcard : Nat.card (GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2)) = 1008 := by
    rw [Nat.card_prod, card_GL3, card_GL2]
  have := Subgroup.eq_top_of_card_eq Psi.range (hr.trans hcard.symm)
  exact MonoidHom.range_eq_top.1 this

end Cnt

end CFSG.Quasithin.H156
