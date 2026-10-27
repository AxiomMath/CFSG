module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace TensorModel

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {TM : TensorModel M Q Z B}

@[expose] def centPreimage (H : StrothHyp M Q Z) (S : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ H0 M Z ∧ ∀ x ∈ S, ⁅h, x⁆ ∈ Q}
  mul_mem' := by
    rintro u v ⟨huH, hu⟩ ⟨hvH, hv⟩
    refine ⟨(H0 M Z).mul_mem huH hvH, fun x hx => ?_⟩
    have e : ⁅u * v, x⁆ = (u * ⁅v, x⁆ * u⁻¹) * ⁅u, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 huH.1) _).mp
      (hv x hx)) (hu x hx)
  one_mem' := ⟨(H0 M Z).one_mem, fun x _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro u ⟨huH, hu⟩
    refine ⟨(H0 M Z).inv_mem huH, fun x hx => ?_⟩
    have e : ⁅u⁻¹, x⁆ = u⁻¹ * ⁅u, x⁆⁻¹ * u := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (M.inv_mem huH.1)) _).mp
      (Q.inv_mem (hu x hx))
    simpa using h1

theorem centPreimage_conj_mem (H : StrothHyp M Q Z) {m : G} (hm : m ∈ M) {h : G}
    (hh : h ∈ centPreimage H (Lgen M (LB M Q B))) :
    m * h * m⁻¹ ∈ centPreimage H (Lgen M (LB M Q B)) := by
  refine ⟨⟨M.mul_mem (M.mul_mem hm hh.1.1) (M.inv_mem hm), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : m⁻¹ * z * m ∈ Z := by
      simpa using (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 (M.inv_mem hm)) z).mp hz
    have hcomm := (Subgroup.mem_centralizer_iff.mp hh.1.2) (m⁻¹ * z * m) hz'
    calc z * (m * h * m⁻¹) = m * ((m⁻¹ * z * m) * h) * m⁻¹ := by group
      _ = m * (h * (m⁻¹ * z * m)) * m⁻¹ := by rw [← hcomm]
      _ = m * h * (m⁻¹ * z * m) * m⁻¹ := by group
      _ = (m * h * m⁻¹) * z := by group
  · intro x hx
    have hx' : m⁻¹ * x * m ∈ Lgen M (LB M Q B) := by
      have h := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B)
        (M.inv_mem hm)) x).mp hx
      simpa using h
    have e : ⁅m * h * m⁻¹, x⁆ = m * ⁅h, m⁻¹ * x * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hm) _).mp (hh.2 (m⁻¹ * x * m) hx')

theorem centPreimage_normal (H : StrothHyp M Q Z) :
    M ≤ Subgroup.normalizer ((centPreimage H (Lgen M (LB M Q B)) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => centPreimage_conj_mem H hm hh, fun hh => ?_⟩
  have hconj := centPreimage_conj_mem H (M.inv_mem hm) hh
  have e : m⁻¹ * (m * h * m⁻¹) * (m⁻¹)⁻¹ = h := by group
  rwa [e] at hconj

theorem Q_le_centPreimage (hc : Ctx M Q Z B) :
    Q ≤ centPreimage hc.hyp (Lgen M (LB M Q B)) := by
  intro q hq
  refine ⟨⟨hc.hyp.Q_normal.1 hq, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzC : z ∈ Subgroup.centralizer (Q : Set G) := by
      have h1 : z ∈ cen Q := hc.hyp.hZ ▸ hz
      rw [cen_eq] at h1
      exact h1.2
    exact ((Subgroup.mem_centralizer_iff.mp hzC) q hq).symm
  · intro x hx
    have hxM : x ∈ M := (Lgen_le_H0 hc hx).1
    have e : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hxM) q⁻¹).mp
      (Q.inv_mem hq))

theorem card_comap_Gamma :
    Nat.card ↥(TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F)) =
      Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) := by
  let toGL : Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F :=
    Matrix.SpecialLinearGroup.toGL
  have hmap : (TM.Gamma.comap toGL).map toGL = TM.Gamma ⊓ StatedSL 2 TM.F := by
    rw [Subgroup.map_comap_eq, ← StatedAPI.statedSL_eq_range_toGL, inf_comm]
  calc Nat.card ↥(TM.Gamma.comap toGL)
      = Nat.card ↥((TM.Gamma.comap toGL).map toGL) :=
        (Subgroup.card_map_of_injective (f := toGL)
          Matrix.SpecialLinearGroup.toGL_injective).symm
    _ = Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) := by rw [hmap]

theorem centDvdN_two_of_card_dvd (hc : Ctx M Q Z B)
    (h : Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) ∣ 2 * (Nat.card TM.F - 1)) :
    CentDvdN 2 M Q Z (Lgen M (LB M Q B)) := by
  let C₀ : Subgroup G := centPreimage hc.hyp (Lgen M (LB M Q B))
  have hQC : Q ≤ C₀ := Q_le_centPreimage hc
  have hCH : C₀ ≤ H0 M Z := fun x hx => hx.1
  have hC : ∀ x, x ∈ C₀ ↔ x ∈ H0 M Z ∧ ∀ y ∈ Lgen M (LB M Q B), ⁅x, y⁆ ∈ Q :=
    fun _ => Iff.rfl
  have hcardC := card_eq_mul_card_Gamma_inf_SL (TM := TM) hc hQC hCH hC
  refine ⟨C₀, hQC, hCH, hC, ?_⟩
  rw [hcardC, ← TM.card_F]
  exact Nat.mul_dvd_mul_left _ h

theorem inSubgroup_pCore_centPreimage_le (hc : Ctx M Q Z B) :
    inSubgroup (CFSG.pCore 2) (centPreimage hc.hyp (Lgen M (LB M Q B))) ≤ Q := by
  let C₀ : Subgroup G := centPreimage hc.hyp (Lgen M (LB M Q B))
  have hC₀M : C₀ ≤ M := fun x hx => hx.1.1
  have hcore2 : IsPGroup 2 (inSubgroup (CFSG.pCore 2) C₀) :=
    IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥C₀)) C₀.subtype
  have hcore_norm : M ≤
      Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) C₀ : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_map_subtype_of_characteristic
      (centPreimage_normal hc.hyp hm) (CFSG.pCore 2 ↥C₀)
  have hleM : inSubgroup (CFSG.pCore 2) C₀ ≤ M := (Subgroup.map_subtype_le _).trans hC₀M
  have hN : (inSubgroup (CFSG.pCore 2) C₀).subgroupOf M ≤ CFSG.pCore 2 M := by
    refine le_sSup ⟨Subgroup.normal_subgroupOf_of_le_normalizer hcore_norm, ?_⟩
    exact hcore2.comap_subtype
  calc inSubgroup (CFSG.pCore 2) C₀
      = ((inSubgroup (CFSG.pCore 2) C₀).subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hleM).symm
    _ ≤ (CFSG.pCore 2 M).map M.subtype := Subgroup.map_mono hN
    _ = Q := by rw [hc.hyp.hQ]; rfl

private theorem normalizer_map_toGL {C₀ : Subgroup G} {ψ : ↥C₀ →* GL (Fin 2) TM.F}
    (hrange : ψ.range = TM.Gamma ⊓ StatedSL 2 TM.F)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F)}
    (hN : TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F) ≤
      Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F))) :
    ψ.range ≤ Subgroup.normalizer ((P.map (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F)) :
        Set (GL (Fin 2) TM.F)) := by
  let toGL : Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F :=
    Matrix.SpecialLinearGroup.toGL
  let Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F) := TM.Gamma.comap toGL
  change Γ₁ ≤ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F)) at hN
  let Pbar : Subgroup (GL (Fin 2) TM.F) := P.map toGL
  have hPbarnorm : ψ.range ≤ Subgroup.normalizer (Pbar : Set (GL (Fin 2) TM.F)) := by
    rintro _ ⟨c, rfl⟩
    have hmem : ψ c ∈ TM.Gamma ⊓ StatedSL 2 TM.F := by
      rw [← hrange]
      exact ⟨c, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : Matrix.SpecialLinearGroup (Fin 2) TM.F, toGL p = ψ c := by
      rw [StatedAPI.statedSL_eq_range_toGL] at hmem
      exact hmem.2
    have hpΓ : p ∈ Γ₁ := by
      change toGL p ∈ TM.Gamma
      rw [hp]
      exact hmem.1
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      refine ⟨p * x * p⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hN hpΓ) x).mp hxP
      · rw [map_mul, map_mul, map_inv, hp]
    · rintro ⟨x, hxP, hx⟩
      refine ⟨p⁻¹ * x * p, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN hpΓ)) x).mp hxP
        simpa using this
      · rw [map_mul, map_mul, map_inv, hp, hx]
        group
  simpa [Pbar] using hPbarnorm

private theorem exists_normal_two_comap {C₀ : Subgroup G} {ψ : ↥C₀ →* GL (Fin 2) TM.F}
    (hker : ψ.ker = Q.subgroupOf C₀) (hrange : ψ.range = TM.Gamma ⊓ StatedSL 2 TM.F)
    (hQ2 : IsPGroup 2 Q)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F)}
    (hP : P ≤ TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F))
    (hN : TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F) ≤
      Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F)))
    (h2 : IsPGroup 2 P) :
    ∃ Pbar : Subgroup (GL (Fin 2) TM.F), ∃ Ptilde : Subgroup ↥C₀,
      Pbar = P.map (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F) ∧
        Ptilde.Normal ∧ IsPGroup 2 Ptilde ∧ Ptilde.map ψ = Pbar := by
  let toGL : Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F :=
    Matrix.SpecialLinearGroup.toGL
  let Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F) := TM.Gamma.comap toGL
  change P ≤ Γ₁ at hP
  let Pbar : Subgroup (GL (Fin 2) TM.F) := P.map toGL
  have hPbarΓ : Pbar ≤ TM.Gamma := by
    rintro _ ⟨p, hp, rfl⟩
    exact hP hp
  have hPbarSL : Pbar ≤ StatedSL 2 TM.F := by
    rintro _ ⟨p, -, rfl⟩
    rw [StatedAPI.statedSL_eq_range_toGL]
    exact ⟨p, rfl⟩
  have hPbarrange : Pbar ≤ ψ.range := by
    rw [hrange]
    exact le_inf hPbarΓ hPbarSL
  have hPbar2 : IsPGroup 2 Pbar := h2.map toGL
  let Ptilde : Subgroup ↥C₀ := Pbar.comap ψ
  have hPtildemap : Ptilde.map ψ = Pbar := Subgroup.map_comap_eq_self hPbarrange
  have hPbarnorm : ψ.range ≤ Subgroup.normalizer (Pbar : Set (GL (Fin 2) TM.F)) :=
    normalizer_map_toGL (TM := TM) hrange hN
  have hPtildenormal : Ptilde.Normal := by
    refine Subgroup.Normal.mk fun x hx c => ?_
    rw [Subgroup.mem_comap] at hx ⊢
    have hψ : ψ (c * x * c⁻¹) = ψ c * ψ x * (ψ c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hψ]
    exact (Subgroup.mem_normalizer_iff.mp (hPbarnorm ⟨c, rfl⟩) (ψ x)).mp hx
  let N : Subgroup Ptilde := (Q.subgroupOf C₀).subgroupOf Ptilde
  have hN2 : IsPGroup 2 N := (hQ2.comap_subtype).comap_subtype
  have hNnorm : N.Normal := by
    haveI : (Q.subgroupOf C₀).Normal := by
      rw [← hker]
      infer_instance
    exact inferInstance
  have hPtilde2 : IsPGroup 2 Ptilde := by
    have hNker : (ψ.domRestrict Ptilde).ker = N := by
      rw [MonoidHom.ker_domRestrict, hker]
    have hNrange : (ψ.domRestrict Ptilde).range = Pbar := by
      rw [MonoidHom.domRestrict_range, hPtildemap]
    have hquot2 : IsPGroup 2 (Ptilde ⧸ N) := by
      have hIso : Ptilde ⧸ N ≃* Pbar :=
        (QuotientGroup.quotientMulEquivOfEq hNker.symm).trans
          ((QuotientGroup.quotientKerEquivRange (ψ.domRestrict Ptilde)).trans
            (MulEquiv.subgroupCongr hNrange))
      exact hPbar2.of_equiv hIso.symm
    haveI : N.Normal := hNnorm
    exact IsPGroup.of_subgroup_of_quotient hN2 hquot2
  exact ⟨Pbar, Ptilde, rfl, hPtildenormal, hPtilde2, hPtildemap⟩

theorem eq_bot_of_isPGroup_two (hc : Ctx M Q Z B)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F)}
    (hP : P ≤ TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F))
    (hN : TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F) ≤
      Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F)))
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  let toGL : Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F :=
    Matrix.SpecialLinearGroup.toGL
  let C₀ : Subgroup G := centPreimage hc.hyp (Lgen M (LB M Q B))
  have hCH : C₀ ≤ H0 M Z := fun x hx => hx.1
  have hC : ∀ x, x ∈ C₀ ↔ x ∈ H0 M Z ∧ ∀ y ∈ Lgen M (LB M Q B), ⁅x, y⁆ ∈ Q :=
    fun _ => Iff.rfl
  obtain ⟨ψ, hker, hrange⟩ := exists_hom_Gamma_inf_SL (TM := TM) hc hCH hC
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  obtain ⟨Pbar, Ptilde, hPbar, hPtildenormal, hPtilde2, hPtildemap⟩ :=
    exists_normal_two_comap (TM := TM) hker hrange hQ2 hP hN h2
  have hPtildecore : Ptilde ≤ CFSG.pCore 2 ↥C₀ := by
    unfold CFSG.pCore
    exact le_sSup ⟨hPtildenormal, hPtilde2⟩
  have hPtildeker : Ptilde ≤ ψ.ker := by
    rw [hker]
    intro x hx
    exact inSubgroup_pCore_centPreimage_le hc
      (Subgroup.mem_map.mpr ⟨x, hPtildecore hx, rfl⟩)
  have hPbarbot : Pbar = ⊥ := by
    rw [← hPtildemap]
    exact (Subgroup.map_eq_bot_iff Ptilde).mpr hPtildeker
  have hmapbot : P.map toGL = ⊥ := by rw [← hPbar]; exact hPbarbot
  exact (Subgroup.map_eq_bot_iff_of_injective P (f := toGL)
    Matrix.SpecialLinearGroup.toGL_injective).mp hmapbot

end TensorModel

end CFSG.RankThree.GF2n.Smith81
