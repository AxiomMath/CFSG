module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Norm
public import CFSG.RankThree.GF2n.Stroth80.Sec108Phi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Sec108Data.phi_mem_Vsp_of_normalizer (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) {e : AM.M₀.E}
    (he : e ∈ AM.Vsp hc t) : AM.φ ⟨d, hd⟩ e ∈ AM.Vsp hc t := by
  obtain ⟨v, hvV, hvQ, rfl⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp he)
  rw [← AM.φ_π ⟨d, hd⟩ v hvQ]
  have hV := D.conj_Vt_of_mem_normalizer_root hd.1 hdY
  exact mem_imgSub.mpr (AM.M₀.pi_mem_img
    ((Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hV) v).mp hvV)
    (conj_mem_Q hc.hyp hd.1 hvQ))

theorem Sec108Data.exists_phi_nu (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {d : G} (hd : d ∈ H0 M Z) (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) :
    ∃ c : AM.Kˣ, ∀ e, AM.φ ⟨d, hd⟩ (D.nu AM e) = (c : AM.K) • D.nu AM (AM.φ ⟨d, hd⟩ e) := by
  obtain ⟨y, hy, w, hw, hyw⟩ := D.exists_root_mul
    ((Subgroup.mem_normalizer_iff.mp hdY t).mp (Subgroup.mem_sup_left D.sit.mem))
  obtain ⟨c, hcy⟩ := D.root_eq AM hy
  have hyH : y ∈ H0 M Z := hc.LB_le_H0 (D.root_le_LB hy)
  have hwH : w ∈ H0 M Z := hc.Q_le_H0 hw
  have hconj : ∀ e, AM.φ ⟨d, hd⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨y, hyH⟩ (AM.φ ⟨d, hd⟩ e) := by
    intro e
    have h1 : (⟨d, hd⟩ : ↥(H0 M Z)) * ⟨t, D.t_mem_H0⟩ = ⟨y, hyH⟩ * ⟨w, hwH⟩ * ⟨d, hd⟩ :=
      Subtype.ext (by
        show d * t = y * w * d
        rw [hyw]
        group)
    have hw1 : AM.φ ⟨w, hwH⟩ = 1 := (AM.φ_ker _).mpr hw
    have h2 := congrArg (fun g : ↥(H0 M Z) => AM.φ g e) h1
    simpa only [map_mul, LinearEquiv.mul_apply, hw1, LinearEquiv.coe_one, id_eq] using h2
  have hφy : ∀ e, AM.φ ⟨y, hyH⟩ e = e + c • D.nu AM e := fun e => by
    have h := LinearMap.congr_fun hcy e
    simpa using h
  have key : ∀ e, AM.φ ⟨d, hd⟩ (D.nu AM e) = c • D.nu AM (AM.φ ⟨d, hd⟩ e) := by
    intro e
    rw [D.nu_apply AM e, map_sub, hconj, hφy]
    abel
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine D.nu_ne_zero AM (LinearMap.ext fun e => ?_)
    have h := key e
    rw [zero_smul] at h
    rw [LinearMap.zero_apply]
    exact (AM.φ ⟨d, hd⟩).map_eq_zero_iff.mp h
  exact ⟨Units.mk0 c hc0, key⟩

private noncomputable abbrev incl :
    ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) →* ↥(H0 M Z) :=
  Subgroup.inclusion inf_le_left

noncomputable def Sec108Data.nuMul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) : AM.Kˣ :=
  (D.exists_phi_nu AM d.2.1 d.2.2).choose

theorem Sec108Data.nuMul_spec (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (e : AM.M₀.E) :
    AM.φ ⟨d, d.2.1⟩ (D.nu AM e) = (D.nuMul AM d : AM.K) • D.nu AM (AM.φ ⟨d, d.2.1⟩ e) :=
  (D.exists_phi_nu AM d.2.1 d.2.2).choose_spec e

theorem Sec108Data.eq_of_smul_nu (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {c c' : AM.K} (h : ∀ e, c • D.nu AM e = c' • D.nu AM e) : c = c' := by
  obtain ⟨e₀, he₀⟩ : ∃ e₀, D.nu AM e₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact D.nu_ne_zero AM (LinearMap.ext h')
  exact smul_left_injective AM.K he₀ (h e₀)

private theorem nuMul_mul (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d d' : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    D.nuMul AM (d * d') = D.nuMul AM d * D.nuMul AM d' := by
  have hmul : AM.φ ⟨((d * d' : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
      G), (d * d').2.1⟩ = AM.φ ⟨d, d.2.1⟩ * AM.φ ⟨d', d'.2.1⟩ := by
    rw [← map_mul]
    rfl
  apply Units.ext
  refine D.eq_of_smul_nu AM fun x => ?_
  obtain ⟨e, rfl⟩ := (AM.φ ⟨((d * d' : ↥(H0 M Z ⊓ Subgroup.normalizer
    ((Y ⊔ Q : Subgroup G) : Set G))) : G), (d * d').2.1⟩).surjective x
  rw [← D.nuMul_spec, hmul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, D.nuMul_spec AM d',
    map_smul, D.nuMul_spec AM d, smul_smul, Units.val_mul, mul_comm (D.nuMul AM d' : AM.K)]

private theorem matV_incl_mul (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d d' : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    D.matV AM (incl (d * d')) = D.matV AM (incl d) * D.matV AM (incl d') := by
  rw [map_mul]
  exact D.matV_mul AM fun e he => D.phi_mem_Vsp_of_normalizer AM d'.2.1 d'.2.2 he

noncomputable def Sec108Data.oddChar (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) →* AM.Kˣ × AM.Kˣ where
  toFun d := (⟨(D.matV AM ⟨d, d.2.1⟩).det, (D.matV AM ⟨(d⁻¹ : ↥(H0 M Z ⊓
      Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))), (d⁻¹).2.1⟩).det,
      by
        change (D.matV AM (incl d)).det * (D.matV AM (incl d⁻¹)).det = 1
        rw [← det_mul, ← matV_incl_mul, mul_inv_cancel, map_one, D.matV_one, det_one],
      by
        change (D.matV AM (incl d⁻¹)).det * (D.matV AM (incl d)).det = 1
        rw [← det_mul, ← matV_incl_mul, inv_mul_cancel, map_one, D.matV_one, det_one]⟩,
    D.nuMul AM d)
  map_one' := by
    refine Prod.ext (Units.ext ?_) ?_
    · show (D.matV AM (incl 1)).det = 1
      rw [map_one, D.matV_one, det_one]
    · have h := nuMul_mul D AM 1 1
      rw [mul_one] at h
      exact (mul_eq_left.mp h.symm)
  map_mul' d d' := by
    refine Prod.ext (Units.ext ?_) (nuMul_mul D AM d d')
    show (D.matV AM (incl (d * d'))).det =
      (D.matV AM (incl d)).det * (D.matV AM (incl d')).det
    rw [matV_incl_mul, det_mul]

theorem Sec108Data.oddChar_fst (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    ((D.oddChar AM d).1 : AM.K) = (D.matV AM ⟨d, d.2.1⟩).det := by
  simp only [Sec108Data.oddChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk]

theorem Sec108Data.oddChar_snd (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (e : AM.M₀.E) :
    AM.φ ⟨d, d.2.1⟩ (D.nu AM e) = ((D.oddChar AM d).2 : AM.K) • D.nu AM (AM.φ ⟨d, d.2.1⟩ e) :=
  D.nuMul_spec AM d e

theorem Sec108Data.oddChar_snd_eq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    (D.oddChar AM d).2 = D.nuMul AM d := by
  simp only [Sec108Data.oddChar, MonoidHom.coe_mk, OneHom.coe_mk]

theorem Sec108Data.oddChar_eq_one_of_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (hdQ : (d : G) ∈ Q) :
    D.oddChar AM d = 1 := by
  have h1 : AM.φ ⟨d, d.2.1⟩ = 1 := (AM.φ_ker _).mpr hdQ
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, d.2.1⟩ e = e := fun e _ => by
    rw [h1, LinearEquiv.coe_one, id_eq]
  have hpres : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, d.2.1⟩ e ∈ AM.Vsp hc t := fun e he => by
    rw [hfix e he]
    exact he
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · rw [D.oddChar_fst, (D.matV_eq_one_iff AM hpres).mpr hfix, det_one]
    rfl
  · obtain ⟨e₀, he₀⟩ : ∃ e₀, D.nu AM e₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact D.nu_ne_zero AM (LinearMap.ext h)
    have h := D.oddChar_snd AM d e₀
    rw [h1, LinearEquiv.coe_one, id_eq, id_eq] at h
    have h' : ((D.oddChar AM d).2 : AM.K) • D.nu AM e₀ = (1 : AM.K) • D.nu AM e₀ := by
      rw [one_smul]
      exact h.symm
    rw [smul_left_injective AM.K he₀ h']
    rfl

theorem Sec108Data.odd_card_units_prod (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Odd (Nat.card (AM.Kˣ × AM.Kˣ)) := by
  obtain ⟨n, -, hn, -⟩ := hc.hyp.cp
  have hK : Nat.card AM.K = 2 ^ n := by rw [AM.glob.card, hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hc.hyp.q4
    rw [hn, pow_zero] at this
    omega
  have hodd : Odd (Nat.card AM.Kˣ) := by
    rw [Nat.card_units, hK]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' hn0).mpr even_two) odd_one
  rw [Nat.card_prod]
  exact hodd.mul hodd

end CFSG.RankThree.GF2n.Stroth80
