module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section NAct

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s828NAct (U K : Subgroup G) (hKN : K ≤ Subgroup.normalizer (U : Set G)) :
    ↥K →* MulAut ↥U :=
  (conjAct U).comp (Subgroup.inclusion hKN)

theorem s828NAct_apply {U K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (U : Set G)) (k : ↥K)
    (u : ↥U) : ((s828NAct U K hKN k u : ↥U) : G) = (k : G) * (u : G) * (k : G)⁻¹ :=
  CFSG.QuasithinUnique.Setup.coe_conjAct_apply (Subgroup.inclusion hKN k) u

theorem s828NAct_eq_one_iff {U K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (U : Set G))
    (k : ↥K) : s828NAct U K hKN k = 1 ↔ (k : G) ∈ Subgroup.centralizer (U : Set G) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : G)) h1
    simp only [s828NAct_apply, MulAut.one_apply] at h2
    calc u * (k : G) = (k : G) * u * (k : G)⁻¹ * (k : G) := by rw [h2]
      _ = (k : G) * u := by group
  · intro hk
    ext u
    rw [s828NAct_apply, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hk (u : G) u.2
    rw [← h, mul_inv_cancel_right]

theorem s828N_card_ker {U K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card (s828NAct U K hKN).ker = Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) := by
  have hker : (s828NAct U K hKN).ker = (Subgroup.centralizer (U : Set G)).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, s828NAct_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [hker]
  exact Nat.card_congr
    { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem s828N_card_mulAut_sixteen {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) :
    Nat.card (MulAut W) = 20160 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq
    (n := 4) (by rw [hW]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)]
  decide

theorem s828N_card_alt6 {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    (hH : AlternatingNatural H ⊤ ⊥ 6) : Nat.card ↥H = 360 := by
  have hne : H ≠ ⊥ := ne_bot_of_alternatingNatural_828 (Or.inr rfl) hH
  obtain ⟨π₀, hsurj₀, -⟩ := hH
  obtain ⟨π, hsurj⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥H, Function.Surjective π :=
    ⟨π₀, hsurj₀⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hker : π.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨g, hg⟩ := hsurj ⟨x, hx⟩
      have hgk : g ∈ π.ker := by
        rw [h]
        exact Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hgk
      have hx1 : (⟨x, hx⟩ : ↥H) = 1 := by
        rw [← hg, hgk]
      exact congrArg Subtype.val hx1
  have hbij : Function.Bijective π := ⟨(MonoidHom.ker_eq_bot_iff π).mp hker, hsurj⟩
  have hcard : Nat.card ↥H = Nat.card ↥(alternatingGroup (Fin 6)) :=
    (Nat.card_congr (Equiv.ofBijective π hbij)).symm
  rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem s828N_dvd_range {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k)
    (hX6 : AlternatingNatural
      (autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
        (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) ⊤ ⊥ 6)
    {K : Subgroup G} (hLUK : ch82LU L (ch82U (fsuV T I) h) ≤ K)
    (hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :
    360 ∣ Nat.card ↥(s828NAct (ch82U (fsuV T I) h) K hKN).range := by
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hLUU : ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 c.hAN
  let eW : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≃* ↥(ch82U (fsuV T I) h) :=
    (MulEquiv.subgroupCongr hfix).trans (Subgroup.subgroupOfEquivOfLe hUV)
  have heW : ∀ w, ((eW w : ↥(ch82U (fsuV T I) h)) : G) = ((w : ↥(fsuV T I)) : G) :=
    fun w => rfl
  have heWs : ∀ u : ↥(ch82U (fsuV T I) h),
      (((eW.symm u : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (u : G) := fun u => rfl
  let ψU : ↥(ch82LU L (ch82U (fsuV T I) h)) →* MulAut ↥(ch82U (fsuV T I) h) :=
    s828NAct (ch82U (fsuV T I) h) (ch82LU L (ch82U (fsuV T I) h)) hLUU
  let ψ : ↥(ch82LU L (ch82U (fsuV T I) h)) →*
      MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) :=
    (MulAut.congr eW.symm).toMonoidHom.comp ψU
  have hψ : ∀ (x : ↥(ch82LU L (ch82U (fsuV T I) h)))
      (w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))),
      (((ψ x w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (x : G) * ((w : ↥(fsuV T I)) : G) * (x : G)⁻¹ := by
    intro x w
    show (((eW.symm (ψU x (eW w)) :
      ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) = _
    rw [heWs, s828NAct_apply, heW]
  have hXY : autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≤ ψ.range := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbLU : (b : G) ∈ ch82LU L (ch82U (fsuV T I) h) := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨(b : G), hbLU⟩, ?_⟩
    ext w
    rw [hψ, resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
  have h360 : 360 ∣ Nat.card ↥ψ.range := by
    have h1 := Subgroup.card_dvd_of_le hXY
    rwa [s828N_card_alt6 hX6] at h1
  have hrange : ψ.range = ψU.range.map (MulAut.congr eW.symm).toMonoidHom := by
    rw [MonoidHom.range_comp]
  have hcardψ : Nat.card ↥ψ.range = Nat.card ↥ψU.range := by
    rw [hrange]
    exact Subgroup.card_map_of_injective (MulAut.congr eW.symm).injective
  have hle : ψU.range ≤ (s828NAct (ch82U (fsuV T I) h) K hKN).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨(x : G), hLUK x.2⟩, rfl⟩
  rw [hcardψ] at h360
  exact h360.trans (Subgroup.card_dvd_of_le hle)

end NAct

end CFSG.Quasithin.H13
