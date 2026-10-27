module

public import CFSG.Quasithin.MS93.S37Bad
public import CFSG.Quasithin.MS93.S37ALR

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F] [CharP F 2]

theorem qe_mem_Q₁ (x s : F) : qe x 0 s ∈ Q₁ F := fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [qe_mulVec]
  simp [h0, h1]

theorem qe_transv_mulVec_f₂ {w : V4 F} (hw : w ∈ ln₀ F) :
    mat (qe (w (.inl 0)) 0 0 * transv (e₂ F) (w (.inl 1))) *ᵥ f₂ F - f₂ F = w := by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hw
  rw [mat_mul_mulVec, transv_mulVec, qe_mulVec, form_e₂]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₂, h0, h1]

end Sp

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem comm_Qt_Ut (θ : MulAut ↥(T1 M T L)) {x y : G} (hx : x ∈ Qt M θ)
    (hy : y ∈ Ut M T L θ) : x * y = y * x := by
  obtain ⟨a, haT, ha, rfl⟩ := mem_tImage.1 hx
  obtain ⟨b, hbT, hb, rfl⟩ := mem_tImage.1 hy
  have hc : b * a = a * b := Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le
    (Uq_le_Z0q C.h.L_le) (C.h.pCoreOf_le_centralizer_Z0q ha)) b hb
  have h2 : (⟨a, haT⟩ : ↥(T1 M T L)) * ⟨b, hbT⟩ = ⟨b, hbT⟩ * ⟨a, haT⟩ := Subtype.ext hc.symm
  have h3 := congrArg (fun x => ((θ x : ↥(T1 M T L)) : G)) h2
  simpa only [map_mul, Subgroup.coe_mul] using h3

theorem comm_of_mem_Dq_Ut (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (θ : MulAut ↥(T1 M T L)) (hDQt : Dq M L ≤ Qt M θ) {x : G} (hxD : x ∈ Dq M L)
    (hxU : x ∈ Ut M T L θ) {t : G} (ht : t ∈ T1 M T L) : t * x = x * t := by
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_T1 ht
  obtain ⟨u, hu, hd⟩ := hQUD q hq
  have h1 : Commute l x := Subgroup.mem_centralizer_iff.1 hxD.2 l hl.2
  have h2 : Commute u x := Subgroup.mem_centralizer_iff.1 hxD.2 u (Uq_le_L C.h hu)
  have h3 : Commute (u⁻¹ * q) x := C.comm_Qt_Ut θ (hDQt hd) hxU
  have h := (h1.mul_left h2).mul_left h3
  have e : l * q = l * u * (u⁻¹ * q) := by group
  rw [e]
  exact h

theorem co_mem_fixSp {u : G} (hu : u ∈ Uq M T L) (hc : ∀ t ∈ T1 M T L, t * u = u * t) :
    C.N.co ⟨u, hu⟩ ∈ fixSp C.T0bar := by
  refine mem_fixSp.2 fun g hg => ?_
  obtain ⟨t, rfl⟩ := hg
  rw [C.rho1_apply]
  refine (C.co_conj ⟨t, T1_le_sup t.2⟩ (u := ⟨u, hu⟩) (v := ⟨u, hu⟩) ?_).symm
  show u = t * u * (t : G)⁻¹
  rw [hc t t.2, mul_inv_cancel_right]

theorem tImage_mem_Uq (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : C.T0bar = Q₁ F) (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ)
    (hθ' : C.IsGood θ⁻¹) {u : G} (hu : u ∈ Uq M T L) (hco : C.N.co ⟨u, hu⟩ ∈ ln₀ F) :
    ((θ ⟨u, C.Uq_le_T1 hu⟩ : ↥(T1 M T L)) : G) ∈ Uq M T L := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  set w := C.N.co ⟨u, hu⟩ with hw
  have hgT : qe (w (.inl 0)) 0 0 * transv (e₂ F) (w (.inl 1)) ∈ C.T0bar := by
    rw [hT]
    exact (Q₁ F).mul_mem (qe_mem_Q₁ _ _) (transv_e₂_mem_Q₁ _)
  obtain ⟨t, ht, x, hx, hgtx⟩ := C.exists_rho_eq_mul θ⁻¹ hgT
  have htT : t ∈ T1 M T L := T_inf_L_le_T1 ht
  have hxX : C.rho1 (θ⁻¹ ⟨x, C.pCore_le_T1 hx⟩) ∈ X₂ F := by
    rw [← hθ'.rhoIm_Qt, C.rho1_apply]
    exact (C.mem_rhoIm).2 ⟨_, _, mem_tImage.2 ⟨x, C.pCore_le_T1 hx, hx, rfl⟩, rfl⟩
  have hxf : mat (C.rho1 (θ⁻¹ ⟨x, C.pCore_le_T1 hx⟩)) *ᵥ f₂ F = f₂ F :=
    (mem_fixer.1 hxX) _ (mem_perp_pt₀.2 (by simp [f₂]))
  set s := θ⁻¹ ⟨t, htT⟩ with hs
  have hsf : mat (C.rho1 s) *ᵥ f₂ F - f₂ F = w := by
    have h := qe_transv_mulVec_f₂ (mem_ln₀.2 (mem_ln₀.1 hco))
    rw [hgtx, mat_mul_mulVec, hxf] at h
    exact h
  obtain ⟨v, hv⟩ := C.N.co_surj (f₂ F)
  have hvT : (v : G) ∈ T1 M T L := C.Uq_le_T1 v.2
  have hsM : (s : G) ∈ M := C.sup_le_M (T1_le_sup s.2)
  have hcU : ⁅(s : G), (v : G)⁆ ∈ Uq M T L := by
    rw [commutatorElement_def]
    exact (Uq M T L).mul_mem ((Subgroup.mem_normalizer_iff.1 (C.hMU hsM) _).1 v.2)
      ((Uq M T L).inv_mem v.2)
  have hco' : C.N.co ⟨_, hcU⟩ = w := by
    rw [C.co_comm hsM v.2 hcU, show C.act hsM = C.act (C.sup_le_M (T1_le_sup s.2)) from rfl,
      C.rho_spec ⟨(s : G), T1_le_sup s.2⟩, ← C.rho1_apply]
    rw [show (⟨(v : G), v.2⟩ : ↥(Uq M T L)) = v from rfl, hv]
    exact hsf
  have ha : ((⟨_, hcU⟩ : ↥(Uq M T L))⁻¹ * ⟨u, hu⟩ : ↥(Uq M T L)) ∈
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    rw [Subgroup.mem_subgroupOf]
    exact (C.N.co_eq_co_iff _ _).1 (hco'.trans hw)
  set a : G := ⁅(s : G), (v : G)⁆⁻¹ * u with hadef
  have haA : a ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := ha
  have haT : a ∈ T1 M T L := C.Uq_le_T1 haA.1
  have hsplit : (⟨u, C.Uq_le_T1 hu⟩ : ↥(T1 M T L)) = ⁅s, ⟨v, hvT⟩⁆ * ⟨a, haT⟩ :=
    Subtype.ext (by
      show u = ⁅(s : G), (v : G)⁆ * (⁅(s : G), (v : G)⁆⁻¹ * u)
      group)
  have hθs : θ s = ⟨t, htT⟩ := by rw [hs, MulAut.apply_inv_self]
  have hθu : ((θ ⟨u, C.Uq_le_T1 hu⟩ : ↥(T1 M T L)) : G) =
      ⁅t, ((θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G)⁆ * ((θ ⟨a, haT⟩ : ↥(T1 M T L)) : G) := by
    rw [hsplit, map_mul, map_commutatorElement, hθs]
    rfl
  rw [hθu]
  refine (Uq M T L).mul_mem ?_ ?_
  ·
    have hvQ : ((θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M := by
      have hvp : C.N.co ⟨(v : G), v.2⟩ ∈ perp (pt₀ F) := by
        rw [show (⟨(v : G), v.2⟩ : ↥(Uq M T L)) = v from rfl, hv]
        exact mem_perp_pt₀.2 (by simp [f₂])
      have hvU : (v : G) ∈ C.Usub (perp (pt₀ F)) := (C.mem_Usub).2 ⟨v.2, hvp⟩
      obtain ⟨y, hyT, hyQ, hye⟩ := mem_tImage.1 (C.Usub_perp_le_Qt θ⁻¹ hθ'.rhoIm_Ut hvU)
      have e : (⟨v, hvT⟩ : ↥(T1 M T L)) = θ⁻¹ ⟨y, hyT⟩ := Subtype.ext hye.symm
      rw [e, MulAut.apply_inv_self]
      exact hyQ
    obtain ⟨u', hu', hd⟩ := hQUD _ hvQ
    obtain ⟨d, hdD, hde⟩ : ∃ d ∈ Dq M L, ((θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G) = u' * d :=
      ⟨_, hd, by group⟩
    rw [hde]
    have htd : t * d = d * t := Subgroup.mem_centralizer_iff.1 hdD.2 t ht.2
    have hdt : d * t⁻¹ = t⁻¹ * d := by
      calc d * t⁻¹ = t⁻¹ * (t * d) * t⁻¹ := by group
        _ = t⁻¹ * (d * t) * t⁻¹ := by rw [htd]
        _ = t⁻¹ * d := by group
    have e : ⁅t, u' * d⁆ = t * u' * t⁻¹ * u'⁻¹ := by
      calc ⁅t, u' * d⁆ = t * u' * (d * t⁻¹) * d⁻¹ * u'⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = t * u' * t⁻¹ * u'⁻¹ := by
            rw [hdt]
            group
    rw [e]
    exact (Uq M T L).mul_mem ((Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.L_le ht.2)) _).1 hu')
      ((Uq M T L).inv_mem hu')
  ·
    have hR : a ∈ Rt M T L θ⁻¹ := C.A_le_Rt hq θ⁻¹ hθ'.rhoIm_Ut haA
    have hR' : ((θ ⟨a, haT⟩ : ↥(T1 M T L)) : G) ∈ Rt M T L θ := by
      rw [← C.tImage_Rt θ]
      exact mem_tImage.2 ⟨a, haT, hR, rfl⟩
    exact C.Usub_le _ (C.Rt_le_Usub θ hθ.rhoIm_Ut hR')

theorem mem_A_of_mem_Dq_Ut (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : C.T0bar = Q₁ F) (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ)
    (hθ' : C.IsGood θ⁻¹) {x : G} (hxD : x ∈ Dq M L) (hxU : x ∈ Ut M T L θ) :
    x ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  obtain ⟨u, huT, hu, rfl⟩ := mem_tImage.1 hxU
  have hc : ∀ t ∈ T1 M T L, t * u = u * t := by
    intro t ht
    have h1 := C.comm_of_mem_Dq_Ut hQUD θ hθ.Dq_le hxD hxU (θ ⟨t, ht⟩).2
    have h2 : θ (⟨t, ht⟩ * ⟨u, huT⟩) = θ (⟨u, huT⟩ * ⟨t, ht⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    exact congrArg Subtype.val (θ.injective h2)
  have hco := C.co_mem_fixSp hu hc
  rw [hT, fixSp_Q₁] at hco
  exact ⟨C.tImage_mem_Uq hQUD hT hq θ hθ hθ' hu hco, hxD.2⟩

theorem co_mem_pt₀_of_mem_Dt_Q₁ (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : C.T0bar = Q₁ F) (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ)
    (hθ' : C.IsGood θ⁻¹) {d : G} (hd : d ∈ Uq M T L) (hdD : d ∈ Dt M L θ⁻¹) :
    C.N.co ⟨d, hd⟩ ∈ pt₀ F := by
  obtain ⟨d₀, hd₀T, hd₀, hd₀e⟩ := mem_tImage.1 hdD
  have hdT : d ∈ T1 M T L := C.Uq_le_T1 hd
  have e : (⟨d, hdT⟩ : ↥(T1 M T L)) = θ⁻¹ ⟨d₀, hd₀T⟩ := Subtype.ext hd₀e.symm
  have hd₀U : d₀ ∈ Ut M T L θ := by
    refine mem_tImage.2 ⟨d, hdT, hd, ?_⟩
    rw [e, MulAut.apply_inv_self]
  have hA := C.mem_A_of_mem_Dq_Ut hQUD hT hq θ hθ hθ' hd₀ hd₀U
  have hR : d ∈ Rt M T L θ⁻¹ := by
    have h := C.tImage_Rt θ⁻¹
    rw [inv_inv] at h
    rw [← h]
    exact mem_tImage.2 ⟨d₀, hd₀T, C.A_le_Rt hq θ hθ.rhoIm_Ut hA, hd₀e⟩
  obtain ⟨hd', hco⟩ := (C.mem_Usub).1 (C.Rt_le_Usub θ⁻¹ hθ'.rhoIm_Ut hR)
  exact hco

theorem false_of_isGood_Q₁ (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : C.T0bar = Q₁ F) (hq : 8 ≤ Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ)
    (hθ' : C.IsGood θ⁻¹) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hq2 : 2 < Nat.card F := by omega
  have key := C.rho1_inv_mem_X₂ hQUD hq θ hθ hθ'
    (fun d hd hdD => C.co_mem_pt₀_of_mem_Dt_Q₁ hQUD hT hq2 θ hθ hθ' hd hdD)
  have hmem : qe (1 : F) 0 0 ∈ C.T0bar := by
    rw [hT]
    exact qe_mem_Q₁ 1 0
  obtain ⟨t, ht⟩ := hmem
  refine C.false_of_rho1_inv_mem_X₂ θ key (t := t) (by rw [ht]; exact qe_mem_Q₂ _ _ _) ?_
  rw [ht]
  exact qe_one_not_mem_X₂

end Cfg

end CFSG.Quasithin.MS93.S37
