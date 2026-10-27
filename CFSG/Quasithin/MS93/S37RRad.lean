module

public import CFSG.Quasithin.MS93.S37RCom

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Quasithin.MS93.S37 CFSG.Quasithin.MS93.S37L
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]

namespace Dat

variable {C : Cfg M T L F} (D : Dat C)

omit [Fintype F] in
theorem eq_elim_of_mem_ln₀ {v : V4 F} (hv : v ∈ ln₀ F) :
    v = Sum.elim (fun i => v (.inl i)) 0 := by
  rw [mem_ln₀] at hv
  funext i
  rcases i with i | i
  · rfl
  · fin_cases i
    · exact hv.1
    · exact hv.2

variable [CharP F 2]

theorem co_comm_z (x y : Fin 2 → F) (h : ⁅D.z y, D.u x⁆ ∈ Uq M T L) :
    C.N.co ⟨⁅D.z y, D.u x⁆, h⟩ = Sum.elim (mv (D.Φ y) x) 0 := by
  have e : (⟨⁅D.z y, D.u x⁆, h⟩ : ↥(Uq M T L)) = ⟨D.Ψ (iota (lc (D.Φ y) x)), D.hU _⟩ :=
    Subtype.ext (D.comm_z x y)
  rw [e, D.hβ]
  rfl

theorem mem_Ut_of_mem_R₀ {v : G} (hv : v ∈ C.Usub (ln₀ F)) : v ∈ Ut M T L D.θ := by
  obtain ⟨hvU, hco⟩ := (C.mem_Usub).1 hv
  obtain ⟨x₁, -, -, hg₁, -⟩ := D.exists_good_pair
  obtain ⟨y, hy⟩ := hg₁ (fun i => C.N.co ⟨v, hvU⟩ (.inl i))
  have hc := C.comm_mem_inf C.pCore_le_T1 T1_le_T D.θ (D.z_mem_Ut y) (D.u_mem x₁)
  have hA : (⟨v, hvU⟩⁻¹ * ⟨⁅D.z y, D.u x₁⁆, hc.1⟩ : ↥(Uq M T L)) ∈
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    rw [Subgroup.mem_subgroupOf]
    refine (C.N.co_eq_co_iff _ _).1 ?_
    rw [D.co_comm_z, hy]
    exact eq_elim_of_mem_ln₀ hco
  have hAR := C.A_le_Rt_of_caseII D.hT D.hq D.θ D.hcrit D.hII hA
  have hAU := (C.Rt_le_inf D.θ hAR).2
  have e : v = ⁅D.z y, D.u x₁⁆ * (v⁻¹ * ⁅D.z y, D.u x₁⁆)⁻¹ := by group
  rw [e]
  exact (Ut M T L D.θ).mul_mem hc.2 ((Ut M T L D.θ).inv_mem hAU)

omit [CharP F 2] in
theorem R₀_le_T1 : C.Usub (ln₀ F) ≤ T1 M T L := (C.Usub_le _).trans C.Uq_le_T1

theorem tImage_R₀ : tImage D.θ (C.Usub (ln₀ F)) = C.Usub (ln₀ F) := by
  have hle : C.Usub (ln₀ F) ≤ tImage D.θ (C.Usub (ln₀ F)) := by
    intro v hv
    obtain ⟨w, hwT, hwU, hwv⟩ := mem_tImage.1 (D.mem_Ut_of_mem_R₀ hv)
    have hvQ : v ∈ pCoreOf 2 M := C.Uq_le_pCore ((C.Usub_le _) hv)
    have hwQ : w ∈ Qt M D.θ⁻¹ := by
      refine mem_tImage.2 ⟨v, R₀_le_T1 hv, hvQ, ?_⟩
      rw [show (⟨v, R₀_le_T1 hv⟩ : ↥(T1 M T L)) = D.θ ⟨w, hwT⟩ from Subtype.ext hwv.symm]
      simp
    have hco := (mem_Qt_iff C D.θ⁻¹ D.fixSp_E' hwU).1 hwQ
    exact mem_tImage.2 ⟨w, hwT, (C.mem_Usub).2 ⟨hwU, hco⟩, hwv⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_tImage D.θ R₀_le_T1]

theorem tImage_inv_R₀ : tImage D.θ⁻¹ (C.Usub (ln₀ F)) = C.Usub (ln₀ F) :=
  tImage_inv_eq R₀_le_T1 D.tImage_R₀

theorem tImage_A_le :
    tImage D.θ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ C.Usub (ln₀ F) := by
  rw [← D.tImage_R₀]
  exact tImage_mono' D.θ (C.A_le_Usub _)

theorem mem_R₀_of_mem_Ut {v : G} (hv : v ∈ Ut M T L D.θ) (hvQ : v ∈ pCoreOf 2 M) :
    v ∈ C.Usub (ln₀ F) := by
  obtain ⟨w, hwT, hwU, hwv⟩ := mem_tImage.1 hv
  have hwQ : w ∈ Qt M D.θ⁻¹ := by
    refine mem_tImage.2 ⟨v, C.pCore_le_T1 hvQ, hvQ, ?_⟩
    rw [show (⟨v, C.pCore_le_T1 hvQ⟩ : ↥(T1 M T L)) = D.θ ⟨w, hwT⟩ from Subtype.ext hwv.symm]
    simp
  rw [← D.tImage_R₀]
  exact mem_tImage.2 ⟨w, hwT, (C.mem_Usub).2 ⟨hwU, (mem_Qt_iff C D.θ⁻¹ D.fixSp_E' hwU).1 hwQ⟩,
    hwv⟩

theorem mem_R₀_of_mem_Ut_inv {v : G} (hv : v ∈ Ut M T L D.θ⁻¹) (hvQ : v ∈ pCoreOf 2 M) :
    v ∈ C.Usub (ln₀ F) := by
  obtain ⟨w, hwT, hwU, hwv⟩ := mem_tImage.1 hv
  have hwQ : w ∈ Qt M D.θ := by
    refine mem_tImage.2 ⟨v, C.pCore_le_T1 hvQ, hvQ, ?_⟩
    rw [show (⟨v, C.pCore_le_T1 hvQ⟩ : ↥(T1 M T L)) = D.θ⁻¹ ⟨w, hwT⟩ from Subtype.ext hwv.symm]
    simp
  rw [← D.tImage_inv_R₀]
  exact mem_tImage.2 ⟨w, hwT, (C.mem_Usub).2 ⟨hwU, (mem_Qt_iff C D.θ D.fixSp_E hwU).1 hwQ⟩,
    hwv⟩

theorem comm_z_mem_R₀ (y : Fin 2 → F) {x : G} (hx : x ∈ pCoreOf 2 M) :
    ⁅D.z y, x⁆ ∈ C.Usub (ln₀ F) := by
  refine D.mem_R₀_of_mem_Ut ?_ ?_
  · rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine (Ut M T L D.θ).mul_mem (D.z_mem_Ut y) ?_
    rw [← mul_assoc]
    exact C.conj_mem_Ut T1_le_T D.θ (C.pCore_le_T1 hx) ((Ut M T L D.θ).inv_mem (D.z_mem_Ut y))
  · rw [commutatorElement_def]
    refine (pCoreOf 2 M).mul_mem ?_ ((pCoreOf 2 M).inv_mem hx)
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M
      (C.h.le (T1_le_T (D.z_mem_T1 y)))) x).1 hx

theorem co_comm_z_pCore (y : Fin 2 → F) {x : G} (hx : x ∈ pCoreOf 2 M) {B : F}
    (hB : ∀ g, C.coc hx g = S5.cform B 0 g) :
    C.N.co ⟨⁅D.z y, x⁆, (C.Usub_le _) (D.comm_z_mem_R₀ y hx)⟩ = Sum.elim (B • sd (D.Φ y)) 0 := by
  obtain ⟨v, hv, hco, hD⟩ := C.exists_comm_eq hx (T1_le_sup (D.z_mem_T1 y))
  have hc : ⁅D.z y, x⁆ ∈ Uq M T L := (C.Usub_le _) (D.comm_z_mem_R₀ y hx)
  have hA : ((⟨v, hv⟩ : ↥(Uq M T L))⁻¹ * ⟨⁅D.z y, x⁆, hc⟩ : ↥(Uq M T L)) ∈
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(Uq M T L).mul_mem ((Uq M T L).inv_mem hv) hc, hD.2⟩
  rw [← (C.N.co_eq_co_iff _ _).2 hA, hco, hB]
  obtain ⟨Cm, hCm, hg⟩ := S5.exists_tau_of_mem_Q₁ (D.rho_mem_Q₁ (D.z_mem_T1 y))
  rw [Φ, hg]
  have h0 := S5.cform_tau_inl0 B 0 hCm
  have h1 := S5.cform_tau_inl1 B 0 hCm
  have h2 := S5.cform_tau_inr B 0 hCm
  funext i
  rcases i with i | i
  · fin_cases i
    · simp [h0, sd, S5.q1Coord, tau_entry]
    · simp [h1, sd, S5.q1Coord, tau_entry]
  · simp [h2]

theorem co_comm_u_T1 (y : Fin 2 → F) {t : G} (ht : t ∈ T1 M T L) (h : ⁅D.u y, t⁆ ∈ Uq M T L) :
    C.N.co ⟨⁅D.u y, t⁆, h⟩ =
      Sum.elim (mv (S5.q1Coord (C.rho ⟨t, T1_le_sup ht⟩)) y) 0 := by
  have e : ⁅D.u y, t⁆ = D.Ψ (iota (lc (S5.q1Coord (C.rho ⟨t, T1_le_sup ht⟩)) y))⁻¹ := by
    rw [map_inv, ← D.comm_u ht, commutatorElement_inv]
  have e' : (⟨⁅D.u y, t⁆, h⟩ : ↥(Uq M T L)) =
      ⟨D.Ψ (iota (lc (S5.q1Coord (C.rho ⟨t, T1_le_sup ht⟩)) y))⁻¹, D.hU _⟩ := Subtype.ext e
  rw [e', D.hβ, toAdd_inv]
  funext i
  rcases i with i | i <;> simp [iota, lc, CharTwo.neg_eq]

theorem comm_D_mem_A {d : G} (hd : d ∈ Dq M L) {t : G} (ht : t ∈ Ut M T L D.θ⁻¹) :
    ⁅d, t⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  have htT : t ∈ T1 M T L := tImage_le _ _ ht
  have hdT : d ∈ T1 M T L := C.pCore_le_T1 hd.1
  have hDn : t ∈ Subgroup.normalizer (Dq M L : Set G) :=
    le_normalizer_Dq C.h.le_normalizer (C.h.le (T1_le_T htT))
  have hD : ⁅d, t⁆ ∈ Dq M L := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine (Dq M L).mul_mem hd ?_
    rw [← mul_assoc]
    exact (Subgroup.mem_normalizer_iff.1 hDn _).1 ((Dq M L).inv_mem hd)
  have hU : ⁅d, t⁆ ∈ Ut M T L D.θ⁻¹ := by
    rw [commutatorElement_def]
    exact (Ut M T L D.θ⁻¹).mul_mem (C.conj_mem_Ut T1_le_T D.θ⁻¹ hdT ht)
      ((Ut M T L D.θ⁻¹).inv_mem ht)
  exact ⟨(C.Usub_le _) (D.mem_R₀_of_mem_Ut_inv hU hD.1), hD.2⟩

theorem tImage_D_le_of
    (hA : tImage D.θ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤
      Uq M T L ⊓ Subgroup.centralizer (L : Set G))
    {d : G} (hd : d ∈ Dq M L) :
    ((D.θ ⟨d, C.pCore_le_T1 hd.1⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M := by
  set e := D.θ ⟨d, C.pCore_le_T1 hd.1⟩ with he
  rw [← C.inf_centralizer_Uq C.pCore_le_T1 T1_le_T]
  refine ⟨e.2, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  set w := D.θ⁻¹ ⟨v, C.Uq_le_T1 hv⟩ with hw
  have hwU : (w : G) ∈ Ut M T L D.θ⁻¹ := mem_tImage.2 ⟨v, C.Uq_le_T1 hv, hv, rfl⟩
  have hcA := D.comm_D_mem_A hd hwU
  have hθ : ((D.θ ⟨⁅d, (w : G)⁆, (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem
      (C.pCore_le_T1 hd.1) w.2) ((T1 M T L).inv_mem (C.pCore_le_T1 hd.1)))
      ((T1 M T L).inv_mem w.2)⟩ : ↥(T1 M T L)) : G) = ⁅(e : G), v⁆ := by
    have e1 : (⟨⁅d, (w : G)⁆, (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem
        (C.pCore_le_T1 hd.1) w.2) ((T1 M T L).inv_mem (C.pCore_le_T1 hd.1)))
        ((T1 M T L).inv_mem w.2)⟩ : ↥(T1 M T L)) =
        ⁅(⟨d, C.pCore_le_T1 hd.1⟩ : ↥(T1 M T L)), w⁆ := rfl
    rw [e1, map_commutatorElement, hw, MulAut.apply_inv_self]
    rfl
  have hmem : ⁅(e : G), v⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← hθ]
    exact hA (mem_tImage.2 ⟨_, _, hcA, rfl⟩)
  have h1 := eq_one_of_comm_mem_A C (T1_le_sup e.2) hv hmem
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

omit [CharP F 2] in
theorem rhoIm_eq_of (hQ : ∀ x ∈ pCoreOf 2 M, ∃ v ∈ Uq M T L, v⁻¹ * x ∈ Dq M L)
    (hD : ∀ (d : G) (hd : d ∈ Dq M L),
      ((D.θ ⟨d, C.pCore_le_T1 hd.1⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M) :
    C.rhoIm (Qt M D.θ) = C.rhoIm (Ut M T L D.θ) := by
  refine le_antisymm (fun g hg => ?_) (rhoIm_mono C (tImage_mono' D.θ C.Uq_le_pCore))
  obtain ⟨t, htK, ht, rfl⟩ := (C.mem_rhoIm).1 hg
  obtain ⟨x, hxT, hxQ, rfl⟩ := mem_tImage.1 ht
  obtain ⟨v, hv, hvd⟩ := hQ x hxQ
  have hvT : v ∈ T1 M T L := C.Uq_le_T1 hv
  have hdT : v⁻¹ * x ∈ T1 M T L := (T1 M T L).mul_mem ((T1 M T L).inv_mem hvT) hxT
  have e : (⟨x, hxT⟩ : ↥(T1 M T L)) = ⟨v, hvT⟩ * ⟨v⁻¹ * x, hdT⟩ :=
    Subtype.ext (by simp)
  have hθv : ((D.θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G) ∈ Ut M T L D.θ :=
    mem_tImage.2 ⟨v, hvT, hv, rfl⟩
  have hθd := hD _ hvd
  refine (C.mem_rhoIm).2 ⟨_, T1_le_sup (D.θ ⟨v, hvT⟩).2, hθv, ?_⟩
  have hab : ((D.θ ⟨x, hxT⟩ : ↥(T1 M T L)) : G) =
      ((D.θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G) * ((D.θ ⟨v⁻¹ * x, hdT⟩ : ↥(T1 M T L)) : G) := by
    rw [e, map_mul]
    rfl
  have hmul : ((D.θ ⟨v, hvT⟩ : ↥(T1 M T L)) : G) * ((D.θ ⟨v⁻¹ * x, hdT⟩ : ↥(T1 M T L)) : G) ∈
      L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem (T1_le_sup (D.θ ⟨v, hvT⟩).2) (Subgroup.mem_sup_right hθd)
  have hρ : C.rho ⟨_, htK⟩ = C.rho ⟨_, hmul⟩ := by
    congr 1
    exact Subtype.ext hab
  rw [hρ, C.rho_mul_eq (T1_le_sup (D.θ ⟨v, hvT⟩).2) (Subgroup.mem_sup_right hθd),
    (C.rho_eq_one_iff ⟨_, Subgroup.mem_sup_right hθd⟩).2 hθd, mul_one]

end Dat

theorem exists_normal_coc (C : Cfg M T L F) [CharP F 2] {x : G} (hx : x ∈ pCoreOf 2 M) :
    ∃ v ∈ Uq M T L, ∃ (B : F) (hx' : v⁻¹ * x ∈ pCoreOf 2 M), ∀ g, C.coc hx' g = S5.cform B 0 g := by
  obtain ⟨B, m, hBm⟩ := C.exists_cform hx
  obtain ⟨u, hu⟩ := C.N.co_surj m
  have huQ : (u : G)⁻¹ ∈ pCoreOf 2 M := (pCoreOf 2 M).inv_mem (C.Uq_le_pCore u.2)
  refine ⟨u, u.2, B, (pCoreOf 2 M).mul_mem huQ hx, fun g => ?_⟩
  rw [C.coc_mul_left huQ hx, C.coc_of_mem_Uq ((Uq M T L).inv_mem u.2) huQ, hBm]
  have e : C.N.co ⟨(u : G)⁻¹, (Uq M T L).inv_mem u.2⟩ = -m := by
    rw [← hu, ← C.N.co_inv]
    rfl
  rw [e]
  simp only [S5.cform, Matrix.mulVec_neg, Matrix.mulVec_zero, sub_zero]
  abel

end CFSG.Quasithin.MS93.S37R
