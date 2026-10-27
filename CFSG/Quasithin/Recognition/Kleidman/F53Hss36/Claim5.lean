module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim3
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.S5Facts
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim1Core
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim5Aux
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim2

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem mem_sup_exists_mul_of_normalizes {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have key : ∀ a ∈ A, ∀ b ∈ B, a⁻¹ * b * a ∈ B := fun a ha b hb => by
    have := (Subgroup.mem_normalizer_iff.mp (hA (A.inv_mem ha)) b).mp hb
    simpa using this
  let S : Subgroup G :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * b * a') * b', B.mul_mem (key a' ha' b hb) hb', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, ?_⟩
        · have := key a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
          simpa using this
        · group }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hy

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem comm_inf_eq_bot_of_not_Zv_le (hZ : ¬ Zv α' ≤ Vn β) :
    ⁅Vn β ⊓ Qv α', Vn α'⁆ = ⊥ := by
  obtain ⟨hzmem, hz1, hzonly⟩ := C.zgen_spec' C.vtype_alpha'
  have hZinf : Zv α' ⊓ Vn β = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases hzonly x hx1 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      apply hZ
      intro z hz
      rcases hzonly z hz with h' | h'
      · rw [h']; exact one_mem _
      · rw [h', ← h]; exact hx2
  rw [eq_bot_iff]
  have a1 : ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ Zv α' := by
    calc ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ ⁅Qv α', Vn α'⁆ := Subgroup.commutator_mono inf_le_right le_rfl
      _ = ⁅Vn α', Qv α'⁆ := Subgroup.commutator_comm _ _
      _ = Zv α' := C.comm_Vn_Qv_eq C.vtype_alpha'
  have a2 : ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ Vn β :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans C.comm_Vn_Vn_le
  exact (le_inf a1 a2).trans hZinf.le

theorem Zv_le_Vn_of_relIndex_two (h2 : (Qv α').relIndex (Vn β) = 2) : Zv α' ≤ Vn β := by
  by_contra hZ
  exact C.relIndex_ne_two_of_comm_eq_bot (C.comm_inf_eq_bot_of_not_Zv_le hZ) h2

theorem exists_theta_alt {δ δ' : Geo H M} (hδ : vtype δ = false)
    (hd : CosetGeom.dist δ δ' + 1 = bMin H M) (h4 : (Qv δ).relIndex (Vn δ') = 4) :
    ∃ θ : ↥(stab δ) →* Equiv.Perm (Fin 5), Function.Surjective θ ∧
      θ.ker = (Qv δ).subgroupOf (stab δ) ∧
      Nat.card (((Vn δ').subgroupOf (stab δ)).map θ) = 4 ∧
      ((Vn δ').subgroupOf (stab δ)).map θ ≤ alternatingGroup (Fin 5) := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hδ
  obtain ⟨-, hAK, -, hq0⟩ := hss114_d C.hA C.hb3 hd
  have hVδs : Vn δ ≤ stab δ :=
    (C.Vn_le_Qv_self hδ).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self δ)
  have hLX : F53B3.Cv δ ≤ Vn δ := inf_le_left
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) δ
  have hXN : ⁅Vn δ, Vn δ'⁆ ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) :=
    (commutator_le_of_le' hVδs hAK).trans hstabN
  have hAN : Vn δ' ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) := hAK.trans hstabN
  have hquadC : ⁅commSec (Vn δ') (F53B3.Cv δ) (Vn δ), Vn δ'⁆ ≤ F53B3.Cv δ :=
    commutator_sup_le_of hXN hAN (by rw [hq0]; exact bot_le)
  have hq := (hsd.quadratic_iff hLX hAK).mp hquadC
  have hcard : Nat.card (((Vn δ').subgroupOf (stab δ)).map θ) = 4 := by
    rw [C.card_map_theta hθk hAK]; exact h4
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ ((Vn δ').subgroupOf (stab δ)).map θ, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : ((Vn δ').subgroupOf (stab δ)).map θ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [hbot] at hcard
    simp at hcard
  exact ⟨θ, hθs, hθk, hcard, (quadratic_four_nat hcard hq haA ha1).1⟩

theorem relIndex_eq_two_of_Zv_le (hZ : Zv α' ≤ Vn β) : (Qv α').relIndex (Vn β) = 2 := by
  by_contra hne
  have hrel := C.relIndex_Qv_Vn_eq
  have h4 : (Qv α').relIndex (Vn β) = 4 := by omega
  have hd' : CosetGeom.dist α' β + 1 = bMin H M := by
    rw [CosetGeom.dist_comm]; exact C.hc.dist_eq'
  obtain ⟨θ, hθs, hθk, hcard, hAalt⟩ := C.exists_theta_alt C.vtype_alpha' hd' h4
  set P := critPathOf C.hc with hP
  have hW2 : Wnn β ≤ stab α' := by
    refine (C.claim2 P hZ).trans ?_
    have hb := C.hb5
    have := P.isGeodesic.mem_nbrs_succ (i := bMin H M - 1) (by omega)
    rw [show bMin H M - 1 + 1 = bMin H M by omega, P.p_b] at this
    exact Qv_le_stab_of_mem_nbrs C.hA this
  set A := ((Vn β).subgroupOf (stab α')).map θ with hA
  have hAab : IsElemAbelian 2 A :=
    isElemAbelian_map_subgroupOf (isElemAbelian_Vn C.hA C.hb3 β) θ
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [hbot] at hcard
    simp at hcard
  obtain ⟨b, hbA, hbn⟩ : ∃ b ∈ A, b ∉ Subgroup.zpowers a := by
    by_contra hno
    push Not at hno
    have hle : A ≤ Subgroup.zpowers a := hno
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hcard] at h1
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hAab.2 a haA)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
  have hab : a ≠ b := fun h => hbn (h ▸ Subgroup.mem_zpowers a)
  have ha2 : a * a = 1 := by simpa [pow_two] using hAab.2 a haA
  have hb2 : b * b = 1 := by simpa [pow_two] using hAab.2 b hbA
  have hcab : a * b = b * a := by
    have := CFSG.Quasithin.F53B3.N37.elemAbelian_comm (E := A) hAab haA hbA
    exact this
  have hsa : Equiv.Perm.sign a = 1 := Equiv.Perm.mem_alternatingGroup.mp (hAalt haA)
  have hsb : Equiv.Perm.sign b = 1 := Equiv.Perm.mem_alternatingGroup.mp (hAalt hbA)
  have hVs : Vn β ≤ stab α' := C.Vn_beta_le_stab
  refine C.claim3 (fun w hw => ?_)
  have hws : w ∈ stab α' := hW2 hw
  have hcentr : ∀ c ∈ A, θ ⟨w, hws⟩ * c = c * θ ⟨w, hws⟩ := by
    rintro c ⟨v, hv, rfl⟩
    have hvV : (v : G) ∈ Vn β := Subgroup.mem_subgroupOf.mp hv
    have hcomm : w * (v : G) = (v : G) * w := by
      have := Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hw) _ hvV
      exact this.symm
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hmemA : θ ⟨w, hws⟩ ∈ A := by
    rcases CFSG.Quasithin.Kleidman.F53Hss36.centralizer_T_type ha2 hb2 ha1 hb1 hab hcab hsa hsb
      (hcentr a haA) (hcentr b hbA) with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact haA
    · rw [h]; exact hbA
    · rw [h]; exact mul_mem haA hbA
  obtain ⟨v, hv, hvw⟩ := hmemA
  have hker : v⁻¹ * ⟨w, hws⟩ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvw]; simp
  rw [hθk, Subgroup.mem_subgroupOf] at hker
  have hvV : (v : G) ∈ Vn β := Subgroup.mem_subgroupOf.mp hv
  have : (v : G) * ((v : G)⁻¹ * w) = w := by simp
  rw [← this]
  exact mul_mem (Subgroup.mem_sup_left hvV) (Subgroup.mem_sup_right hker)

theorem relIndex_Qv_le_four_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hle : E ≤ stab α') : (Qv α').relIndex E ≤ 4 := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData C.vtype_alpha'
  have h1 := C.card_map_theta hθk hle
  have hab := isElemAbelian_map_subgroupOf hE θ
  rw [← h1]
  rcases card_cases_of_elemAbelian_perm hab with h | h | h <;> omega


theorem Wnn_le_stab_alpha'_of_Zv_le (hZ : Zv α' ≤ Vn β) : Wnn β ≤ stab α' := by
  set P := critPathOf C.hc with hP
  refine (C.claim2 P hZ).trans ?_
  have hb := C.hb5
  have := P.isGeodesic.mem_nbrs_succ (i := bMin H M - 1) (by omega)
  rw [show bMin H M - 1 + 1 = bMin H M by omega, P.p_b] at this
  exact Qv_le_stab_of_mem_nbrs C.hA this

theorem exists_x_not_comm (hZ : Zv α' ≤ Vn β) :
    ∃ μ ∈ nbrs β, ∃ x ∈ Vn α' ⊓ Qv β, ∃ z ∈ Zv μ, x * z ≠ z * x := by
  have rel2 := C.relIndex_eq_two_of_Zv_le hZ
  have rel2' : (Qv β).relIndex (Vn α') = 2 := C.relIndex_Qv_Vn_eq.1.trans rel2
  obtain ⟨μ', C'⟩ := C.exists_mirror
  have hne : ⁅Vn α' ⊓ Qv β, Vn β⁆ ≠ ⊥ := fun h => C'.relIndex_ne_two_of_comm_eq_bot h rel2'
  by_contra hno
  push Not at hno
  apply hne
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx v hv
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have hcent : Vn β ≤ Subgroup.centralizer ({x} : Set G) := by
    refine iSup₂_le fun μ hμ z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hno μ hμ g hx z hz
  exact (Subgroup.mem_centralizer_iff.mp (hcent hv) x rfl)

theorem relIndex_Wn_inf_le_two (hZ : Zv α' ≤ Vn β) {μ : Geo H M} (hμ : μ ∈ nbrs β) :
    (Wn μ ⊓ (Vn β ⊔ Qv α')).relIndex (Wn μ) ≤ 2 := by
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have hWst : Wn μ ≤ stab α' := (Wn_le_Wnn hμ).trans (C.Wnn_le_stab_alpha'_of_Zv_le hZ)
  have hWab := C.isElemAbelian_Wn hvμ
  have h4 := C.relIndex_Qv_le_four_of_elemAbelian hWab hWst
  have hVW : Vn β ≤ Wn μ := Vn_le_Wn (mem_nbrs_comm hμ)
  set X := Wn μ ⊓ Qv α' with hX
  set W0 := Wn μ ⊓ (Vn β ⊔ Qv α') with hW0
  have hXW0 : X ≤ W0 := inf_le_inf_left _ le_sup_right
  have hW0W : W0 ≤ Wn μ := inf_le_left
  have hVW0 : Vn β ≤ W0 := le_inf hVW le_sup_left
  have h1 : X.relIndex W0 * W0.relIndex (Wn μ) = X.relIndex (Wn μ) :=
    Subgroup.relIndex_mul_relIndex _ _ _ hXW0 hW0W
  have h2 : X.relIndex (Wn μ) = (Qv α').relIndex (Wn μ) := by
    rw [hX, inf_comm, Subgroup.inf_relIndex_right]
  have h3 : X.relIndex (Vn β) = 2 := by
    rw [← C.relIndex_eq_two_of_Zv_le hZ]
    unfold Subgroup.relIndex
    congr 1
    ext v
    simp only [Subgroup.mem_subgroupOf, hX, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hVW v.2, h⟩⟩
  have h5 : X.relIndex (Vn β) ≤ X.relIndex W0 :=
    Subgroup.relIndex_le_of_le_right hVW0 (relIndex_ne_zero' _ _)
  have : 2 * W0.relIndex (Wn μ) ≤ 4 := by
    calc 2 * W0.relIndex (Wn μ) ≤ X.relIndex W0 * W0.relIndex (Wn μ) :=
          Nat.mul_le_mul_right _ (h3 ▸ h5)
      _ = _ := h1
      _ ≤ 4 := h2 ▸ h4
  omega

theorem comm_mem_Zv_sup (hZ : Zv α' ≤ Vn β) {μ : Geo H M} (hμ : μ ∈ nbrs β) {x w : G}
    (hx : x ∈ Vn α' ⊓ Qv β) (hw : w ∈ Wn μ ⊓ (Vn β ⊔ Qv α')) : ⁅w, x⁆ ∈ Zv μ ⊔ Zv α' := by
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have hWab := C.isElemAbelian_Wn hvμ
  have hVW : Vn β ≤ Wn μ := Vn_le_Wn (mem_nbrs_comm hμ)
  have hN : Vn β ≤ Subgroup.normalizer (Qv α' : Set G) :=
    C.Vn_beta_le_stab.trans (le_normalizer_pCoreOf 2 (stab α'))
  obtain ⟨v, hv, q, hq, rfl⟩ := mem_sup_exists_mul_of_normalizes hN hw.2
  have hvx : ⁅v, x⁆ ∈ Zv β := by
    rw [← C.comm_Vn_Qv_eq C.vtype_beta]
    exact Subgroup.commutator_mem_commutator hv hx.2
  have hqx : ⁅q, x⁆ ∈ Zv α' := by
    rw [← C.comm_Vn_Qv_eq C.vtype_alpha', Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hq hx.1
  have h1 : ⁅v * q, x⁆ = v * ⁅q, x⁆ * v⁻¹ * ⁅v, x⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : v * ⁅q, x⁆ = ⁅q, x⁆ * v :=
    elemAbelian_comm hWab (hVW hv) (hVW (hZ hqx))
  rw [h1, h2]
  have h3 : ⁅q, x⁆ * v * v⁻¹ * ⁅v, x⁆ = ⁅q, x⁆ * ⁅v, x⁆ := by group
  rw [h3]
  exact mul_mem (Subgroup.mem_sup_right hqx)
    (Subgroup.mem_sup_left (C.Zv_le_Zv_of_mem_nbrs (vtype_true_of_mem_nbrs_false hμ C.vtype_beta)
      (mem_nbrs_comm hμ) hvx))

theorem exists_arc_index_le_four (hZ : Zv α' ≤ Vn β) :
    ∃ μ ∈ nbrs β, ∃ μ1 ∈ nbrs μ, μ1 ≠ β ∧ (Iv μ).relIndex (Vn μ1) ≤ 4 := by
  obtain ⟨μ, hμ, x, hx, z, hz, hxz⟩ := C.exists_x_not_comm hZ
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have hμβ : β ∈ nbrs μ := mem_nbrs_comm hμ
  have hxst : x ∈ stab μ := Qv_le_stab_of_mem_nbrs C.hA hμ hx.2
  have hxQμ : x ∉ Qv μ := by
    intro h
    rw [← centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hvμ)] at h
    exact hxz (Subgroup.mem_centralizer_iff.mp h.2 z hz).symm
  obtain ⟨μ1, hμ1, hμ1β⟩ := exists_mem_nbrs_ne C.hA μ hμβ
  obtain ⟨μ2, hμ2, hμ2β, hμ2μ1⟩ := exists_third_mem_nbrs C.hA hvμ (Ne.symm hμ1β)
  refine ⟨μ, hμ, μ1, hμ1, hμ1β, ?_⟩
  set g : ↥(H ⊔ M) := ⟨x, stab_le μ hxst⟩ with hg
  have hsw : g • μ1 = μ2 :=
    C.smul_eq_third hvμ hμβ hμ1 hμ2 (Ne.symm hμ1β) (Ne.symm hμ2β) (Ne.symm hμ2μ1)
      (show (g : G) ∈ Qv β from hx.2) hxQμ
  have hVW : Vn β ≤ Wn μ := Vn_le_Wn hμβ
  have hWab := C.isElemAbelian_Wn hvμ
  obtain ⟨K, hK, hKi⟩ := exists_comm_kernel_relIndex_le_four hWab (stab_le_normalizer_Wn μ hxst)
    (C.relIndex_Wn_inf_le_two hZ hμ) ((Zv_le_Vn_of_mem_nbrs hμ).trans hVW) (hZ.trans hVW)
    (C.card_Zv_false C.vtype_alpha').le (fun w hw => C.comm_mem_Zv_sup hZ hμ hx hw)
    (Vn_le_Wn hμ1)
  have hKI : K ≤ Iv μ := by
    intro v hv
    obtain ⟨hvV, hvx⟩ := (hK v).mp hv
    have hZV : Zv μ ≤ Vn μ1 := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hμ1)
    have hu1 : x * v * x⁻¹ ∈ Vn μ1 := by
      have h1 : x * v⁻¹ * x⁻¹ = v⁻¹ * ⁅v, x⁆ := by
        simp only [commutatorElement_def]; group
      have h2 : x * v⁻¹ * x⁻¹ ∈ Vn μ1 := by
        rw [h1]; exact mul_mem ((Vn μ1).inv_mem hvV) (hZV hvx)
      have := (Vn μ1).inv_mem h2
      simpa [mul_assoc] using this
    have hu2 : x * v * x⁻¹ ∈ Vn μ2 := by
      rw [← hsw, Vn_smul, mem_conjSub]
      simpa [hg, mul_assoc] using hvV
    have hu : x * v * x⁻¹ ∈ Iv μ := by
      rw [← C.Vn_inf_Vn_eq_Iv hvμ hμ1 hμ2 (Ne.symm hμ2μ1).symm.symm]
      exact ⟨hu1, hu2⟩
    have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Iv μ (inv_mem hxst)) _).mp hu
    simpa [mul_assoc] using this
  exact (Subgroup.relIndex_le_of_le_left hKI (relIndex_ne_zero' _ _)).trans hKi

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
