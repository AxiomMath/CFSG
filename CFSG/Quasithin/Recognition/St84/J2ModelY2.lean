module

public import CFSG.Quasithin.Recognition.St84.J2YPair
public import CFSG.Quasithin.Recognition.St84.SemidirectRec
public import CFSG.Quasithin.Recognition.St84.HeisF4Rigid
public import Certificates.Certificate733001
public import CFSG.Certificates.Kernel.SporSch.TblSound
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2

public section

namespace CFSG.Quasithin.F112R.St84.J2Model

open CFSG.Fischer
open CFSG.Quasithin.F112R.St84.Heis
open CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

noncomputable def E1 : Equiv.Perm (Fin 315) := tp 315 (e1T ())

noncomputable def E2 : Equiv.Perm (Fin 315) := tp 315 (e2T ())

noncomputable def F1 : Equiv.Perm (Fin 315) := tp 315 (f1T ())

noncomputable def F2 : Equiv.Perm (Fin 315) := tp 315 (f2T ())

noncomputable def bm : Equiv.Perm (Fin 315) := tp 315 (bmT ())

noncomputable def tm : Equiv.Perm (Fin 315) := tp 315 (tmT ())

noncomputable def rm : Equiv.Perm (Fin 315) := tp 315 (rmT ())

noncomputable def Em (a : F4) : Equiv.Perm (Fin 315) :=
  E1 ^ (a.code.val % 2) * E2 ^ (a.code.val / 2)

noncomputable def Fm (b : F4) : Equiv.Perm (Fin 315) :=
  F1 ^ (b.code.val % 2) * F2 ^ (b.code.val / 2)

noncomputable def κ (q : Q1M) : Equiv.Perm (Fin 315) :=
  Em q.a * Fm q.b * ⁅E1, Fm (q.c + q.a * q.b)⁆

theorem rep_e1T (h : b0OK = true) : Rep 315 (e1T ()) E1 := rep_tp (e1T_permOK h)

theorem rep_e2T (h : b0OK = true) : Rep 315 (e2T ()) E2 := rep_tp (e2T_permOK h)

theorem rep_f1T (h : b0OK = true) : Rep 315 (f1T ()) F1 := rep_tp (f1T_permOK h)

theorem rep_f2T (h : b0OK = true) : Rep 315 (f2T ()) F2 := rep_tp (f2T_permOK h)

theorem rep_bmT (h : b0OK = true) : Rep 315 (bmT ()) bm := rep_tp (bmT_permOK h)

theorem rep_tmT (h : b0OK = true) : Rep 315 (tmT ()) tm := rep_tp (tmT_permOK h)

theorem rep_rmT (h : b0OK = true) : Rep 315 (rmT ()) rm := rep_tp (rmT_permOK h)

theorem rep_EmT (h : b0OK = true) (a : F4) : Rep 315 (EmT a) (Em a) :=
  Rep.compT (Rep.powT (n := 315) (by norm_num) (rep_e1T h) _)
    (Rep.powT (n := 315) (by norm_num) (rep_e2T h) _)

theorem rep_FmT (h : b0OK = true) (b : F4) : Rep 315 (FmT b) (Fm b) :=
  Rep.compT (Rep.powT (n := 315) (by norm_num) (rep_f1T h) _)
    (Rep.powT (n := 315) (by norm_num) (rep_f2T h) _)

theorem rep_commFT (h : b0OK = true) (b : F4) :
    Rep 315 (commFT b) ⁅E1, Fm b⁆ := by
  rw [commutatorElement_def]
  have hE := rep_e1T h
  have hF := rep_FmT h b
  exact Rep.compT (Rep.compT (Rep.compT hE hF) (CFSG.KS.Tbl.invT_rep (by norm_num) hE))
    (CFSG.KS.Tbl.invT_rep (by norm_num) hF)

theorem rep_κT (h : b0OK = true) (q : Q1M) : Rep 315 (κT q) (κ q) :=
  Rep.compT (Rep.compT (rep_EmT h q.a) (rep_FmT h q.b))
    (rep_commFT h (q.c + q.a * q.b))

noncomputable def κHom : Q1M →* Equiv.Perm (Fin 315) where
  toFun := κ
  map_one' := by
    have h : (1 : Q1M) = ⟨0, 0, 0⟩ := rfl
    rw [h]
    simp [κ, Em, Fm, commutatorElement_def, code_zero]
  map_mul' := by
    intro x y
    have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
    have hb1 : b1OK = true := Certificates.certificate733001.2.2.2.2.1
    exact (tblEq_iff_eq (rep_κT hb0 (x * y))
      (Rep.compT (rep_κT hb0 x) (rep_κT hb0 y))).mp (κT_mul hb1 x y)

theorem κHom_injective : Function.Injective κHom := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb1 : b1OK = true := Certificates.certificate733001.2.2.2.2.1
  have key : ∀ z : Q1M, κHom z = 1 → z = 1 := by
    intro z hz
    by_contra hne
    have h2 : tblEq 315 (κT z) (idT 315) = true :=
      (tblEq_iff_eq (rep_κT hb0 z) (Rep.idT (n := 315) (by norm_num))).mpr hz
    rw [κT_ne_one hb1 hne] at h2
    exact Bool.false_ne_true h2
  intro x y hxy
  have h1 : x * y⁻¹ = 1 := key _ (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
  rwa [mul_inv_eq_one] at h1

theorem code_one : ((1 : F4).code : ℕ) = 1 := rfl

theorem code_zero : ((0 : F4).code : ℕ) = 0 := rfl

theorem code_ω : (F4.ω.code : ℕ) = 2 := rfl

theorem Em_zero : Em 0 = 1 := by
  unfold Em
  rw [code_zero]
  norm_num

theorem Fm_zero : Fm 0 = 1 := by
  unfold Fm
  rw [code_zero]
  norm_num

theorem Em_one : Em 1 = E1 := by
  unfold Em
  rw [code_one]
  norm_num

theorem Em_ω : Em F4.ω = E2 := by
  unfold Em
  rw [code_ω]
  norm_num

theorem Fm_one : Fm 1 = F1 := by
  unfold Fm
  rw [code_one]
  norm_num

theorem Fm_ω : Fm F4.ω = F2 := by
  unfold Fm
  rw [code_ω]
  norm_num

theorem κHom_e1 : κHom e1 = E1 := by
  have h : κ e1 = E1 := by
    unfold κ
    rw [show e1.a = (1 : F4) from rfl, show e1.b = (0 : F4) from rfl,
      show e1.c = (0 : F4) from rfl, show (0 : F4) + (1 : F4) * 0 = 0 from by norm_num,
      Em_one, Fm_zero, commutatorElement_def]
    simp
  exact h

theorem κHom_e2 : κHom e2 = E2 := by
  have h : κ e2 = E2 := by
    unfold κ
    rw [show e2.a = F4.ω from rfl, show e2.b = (0 : F4) from rfl,
      show e2.c = (0 : F4) from rfl, show (0 : F4) + F4.ω * 0 = 0 from by norm_num,
      Em_ω, Fm_zero, commutatorElement_def]
    simp
  exact h

theorem κHom_f1 : κHom f1 = F1 := by
  have h : κ f1 = F1 := by
    unfold κ
    rw [show f1.a = (0 : F4) from rfl, show f1.b = (1 : F4) from rfl,
      show f1.c = (0 : F4) from rfl, show (0 : F4) + (0 : F4) * 1 = 0 from by norm_num,
      Em_zero, Fm_one, commutatorElement_def]
    simp [Fm_zero]
  exact h

theorem κHom_f2 : κHom f2 = F2 := by
  have h : κ f2 = F2 := by
    unfold κ
    rw [show f2.a = (0 : F4) from rfl, show f2.b = F4.ω from rfl,
      show f2.c = (0 : F4) from rfl, show (0 : F4) + (0 : F4) * F4.ω = 0 from by norm_num,
      Em_zero, Fm_ω, commutatorElement_def]
    simp [Fm_zero]
  exact h

theorem conj_of_conjGenOK {cT : Table}
    {c : Equiv.Perm (Fin 315)} {α : MulAut Q1M}
    (hc : Rep 315 cT c) (hci : Rep 315 (invT 315 cT) c⁻¹)
    (hall : conjGenOK cT α = true) (q : Q1M) :
    c * κHom q * c⁻¹ = κHom (α q) := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  let φ : Q1M →* Equiv.Perm (Fin 315) := (MulAut.conj c).toMonoidHom.comp κHom
  let ψ : Q1M →* Equiv.Perm (Fin 315) := κHom.comp α.toMonoidHom
  have hφ : ∀ x, φ x = c * κHom x * c⁻¹ := fun x => MulAut.conj_apply c (κHom x)
  have hψ : ∀ x, ψ x = κHom (α x) := fun _ => rfl
  have hφψ : φ = ψ := by
    refine Heis.hom_ext ?_ ?_ ?_ ?_
    · simp only [hφ, hψ]
      exact (tblEq_iff_eq (rep_conjT hc hci (rep_κT hb0 e1)) (rep_κT hb0 (α e1))).mp
        (conjGenOK_spec hall (by simp [gensQ1M]))
    · simp only [hφ, hψ]
      exact (tblEq_iff_eq (rep_conjT hc hci (rep_κT hb0 e2)) (rep_κT hb0 (α e2))).mp
        (conjGenOK_spec hall (by simp [gensQ1M]))
    · simp only [hφ, hψ]
      exact (tblEq_iff_eq (rep_conjT hc hci (rep_κT hb0 f1)) (rep_κT hb0 (α f1))).mp
        (conjGenOK_spec hall (by simp [gensQ1M]))
    · simp only [hφ, hψ]
      exact (tblEq_iff_eq (rep_conjT hc hci (rep_κT hb0 f2)) (rep_κT hb0 (α f2))).mp
        (conjGenOK_spec hall (by simp [gensQ1M]))
  have hq := congrArg (fun f : Q1M →* Equiv.Perm (Fin 315) => f q) hφψ
  simpa only [hφ, hψ] using hq

theorem bm_conj (q : Q1M) :
    bm * κHom q * bm⁻¹ = κHom (βM q) := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb2 : b2OK = true := Certificates.certificate733001.2.2.2.2.2.1
  exact conj_of_conjGenOK (rep_bmT hb0)
    (CFSG.KS.Tbl.invT_rep (by norm_num) (rep_bmT hb0)) (b2OK_bm hb2) q

theorem rm_conj (q : Q1M) :
    rm * κHom q * rm⁻¹ = κHom (ρM q) := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb2 : b2OK = true := Certificates.certificate733001.2.2.2.2.2.1
  exact conj_of_conjGenOK (rep_rmT hb0)
    (CFSG.KS.Tbl.invT_rep (by norm_num) (rep_rmT hb0)) (b2OK_rm hb2) q

theorem tm_conj (q : Q1M) :
    tm * κHom q * tm⁻¹ = κHom (τM q) := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb2 : b2OK = true := Certificates.certificate733001.2.2.2.2.2.1
  exact conj_of_conjGenOK (rep_tmT hb0)
    (CFSG.KS.Tbl.invT_rep (by norm_num) (rep_tmT hb0)) (b2OK_tm hb2) q

theorem bm_pow_three : bm ^ 3 = 1 := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb3 : b3OK = true := Certificates.certificate733001.2.2.2.2.2.2.1
  exact (tblEq_iff_eq (Rep.powT (n := 315) (by norm_num) (rep_bmT hb0) 3)
    (Rep.idT (n := 315) (by norm_num))).mp (bm_cube hb3)

theorem tm_pow_two : tm ^ 2 = 1 := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb3 : b3OK = true := Certificates.certificate733001.2.2.2.2.2.2.1
  exact (tblEq_iff_eq (Rep.powT (n := 315) (by norm_num) (rep_tmT hb0) 2)
    (Rep.idT (n := 315) (by norm_num))).mp (tm_square hb3)

theorem tm_mul_bm : tm * bm = bm * tm := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hb3 : b3OK = true := Certificates.certificate733001.2.2.2.2.2.2.1
  exact (tblEq_iff_eq (Rep.compT (rep_tmT hb0) (rep_bmT hb0))
    (Rep.compT (rep_bmT hb0) (rep_tmT hb0))).mp (tm_bm_commute hb3)

noncomputable def Q1m : Subgroup (Equiv.Perm (Fin 315)) :=
  κHom.range

noncomputable def T0m : Subgroup (Equiv.Perm (Fin 315)) :=
  genOf 315 [e1T, e2T, f1T, f2T, tmT]

theorem tm_mem_T0m : tm ∈ T0m := by
  unfold T0m
  exact tp_mem_genOf (n := 315) (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)

noncomputable def Am : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 [rmT, bmT, tmT]

noncomputable def X2m : Subgroup (Equiv.Perm (Fin 315)) :=
  genOf 315 [e1T, e2T, f1T, f2T, rmT, bmT, tmT]

theorem permOK_T0m_list :
    ∀ g ∈ [e1T, e2T, f1T, f2T, tmT], permOK 315 g = true := by
  intro g hg
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact e1T_permOK hb0
  · exact e2T_permOK hb0
  · exact f1T_permOK hb0
  · exact f2T_permOK hb0
  · exact tmT_permOK hb0

theorem permOK_Am_list :
    ∀ g ∈ [rmT, bmT, tmT], permOK 315 g = true := by
  intro g hg
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact rmT_permOK hb0
  · exact bmT_permOK hb0
  · exact tmT_permOK hb0

theorem permOK_X2m_list :
    ∀ g ∈ [e1T, e2T, f1T, f2T, rmT, bmT, tmT], permOK 315 g = true := by
  intro g hg
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e1T_permOK hb0
  · exact e2T_permOK hb0
  · exact f1T_permOK hb0
  · exact f2T_permOK hb0
  · exact rmT_permOK hb0
  · exact bmT_permOK hb0
  · exact tmT_permOK hb0

theorem card_Q1m : Nat.card Q1m = 64 := by
  unfold Q1m
  rw [← Nat.card_congr (MonoidHom.ofInjective κHom_injective).toEquiv]
  exact card_Q1M

theorem E1_mem_Q1m : E1 ∈ Q1m := by
  unfold Q1m
  exact ⟨e1, κHom_e1⟩

theorem E2_mem_Q1m : E2 ∈ Q1m := by
  unfold Q1m
  exact ⟨e2, κHom_e2⟩

theorem F1_mem_Q1m : F1 ∈ Q1m := by
  unfold Q1m
  exact ⟨f1, κHom_f1⟩

theorem F2_mem_Q1m : F2 ∈ Q1m := by
  unfold Q1m
  exact ⟨f2, κHom_f2⟩

theorem Q1m_eq_closure :
    Q1m = Subgroup.closure ({E1, E2, F1, F2} : Set (Equiv.Perm (Fin 315))) := by
  have himg : κHom '' ({e1, e2, f1, f2} : Set Q1M) = ({E1, E2, F1, F2} : Set _) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl | rfl
      · exact Or.inl (by rw [κHom_e1])
      · exact Or.inr (Or.inl (by rw [κHom_e2]))
      · exact Or.inr (Or.inr (Or.inl (by rw [κHom_f1])))
      · exact Or.inr (Or.inr (Or.inr (by rw [κHom_f2])))
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨e1, Or.inl rfl, by rw [κHom_e1]⟩
      · exact ⟨e2, Or.inr (Or.inl rfl), by rw [κHom_e2]⟩
      · exact ⟨f1, Or.inr (Or.inr (Or.inl rfl)), by rw [κHom_f1]⟩
      · exact ⟨f2, Or.inr (Or.inr (Or.inr rfl)), by rw [κHom_f2]⟩
  unfold Q1m
  rw [MonoidHom.range_eq_map, ← closure_gens, MonoidHom.map_closure, himg]

theorem Q1m_le_T0m : Q1m ≤ T0m := by
  rw [Q1m_eq_closure, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact tp_mem_genOf (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)
  · exact tp_mem_genOf (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)
  · exact tp_mem_genOf (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)
  · exact tp_mem_genOf (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)

theorem permOK_j2C2Gens :
    ∀ g ∈ j2C2Gens, permOK 315 g = true := by
  have h := j2_QOK
  simp only [j2QOK, Bool.and_eq_true, beq_iff_eq] at h
  exact List.all_eq_true.mp h.1.1.1.2

theorem T0m_le_C2 :
    T0m ≤ genOf 315 j2C2Gens := by
  unfold T0m
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · exact tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
      (e1T_permOK Certificates.certificate733001.2.2.2.1)
  · exact tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
      (e2T_permOK Certificates.certificate733001.2.2.2.1)
  · exact tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
      (f1T_permOK Certificates.certificate733001.2.2.2.1)
  · exact tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
      (f2T_permOK Certificates.certificate733001.2.2.2.1)
  · exact tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
      (tmT_permOK Certificates.certificate733001.2.2.2.1)

theorem bm_mem_C2 :
    bm ∈ genOf 315 j2C2Gens :=
  tp_wordTbl_mem (by norm_num) permOK_j2C2Gens (by decide)
    (bmT_permOK Certificates.certificate733001.2.2.2.1)

theorem card_T0m : Nat.card T0m = 128 := by
  obtain ⟨h, -⟩ := enumOK_spec (n := 315) (cap := 200) (m := 128)
    (gs := [e1T, e2T, f1T, f2T, tmT]) (by norm_num) permOK_T0m_list
    (enumOK_T0m Certificates.certificate733001.2.2.2.2.2.2.2.1)
  exact h

theorem card_Am : Nat.card Am = 18 := by
  obtain ⟨h, -⟩ := enumOK_spec (n := 315) (cap := 100) (m := 18)
    (gs := [rmT, bmT, tmT]) (by norm_num) permOK_Am_list
    (enumOK_Am Certificates.certificate733001.2.2.2.2.2.2.2.1)
  exact h

theorem card_X2m : Nat.card X2m = 1152 := by
  obtain ⟨h, -⟩ := enumOK_spec (n := 315) (cap := 3000) (m := 1152)
    (gs := [e1T, e2T, f1T, f2T, rmT, bmT, tmT]) (by norm_num) permOK_X2m_list
    (enumOK_X2m Certificates.certificate733001.2.2.2.2.2.2.2.1)
  exact h

theorem tm_not_mem_Q1m : tm ∉ Q1m := by
  intro htm
  have hT : T0m ≤ Q1m := by
    unfold T0m
    rw [genOf, Subgroup.closure_le]
    rintro _ ⟨T, hT, rfl⟩
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl
    · exact E1_mem_Q1m
    · exact E2_mem_Q1m
    · exact F1_mem_Q1m
    · exact F2_mem_Q1m
    · exact htm
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hT) (Subgroup.inclusion_injective hT)
  rw [card_T0m, card_Q1m] at hc
  omega

theorem bm_mem_normalizer_T0m :
    bm ∈ Subgroup.normalizer (T0m : Set (Equiv.Perm (Fin 315))) := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hβ1 : bm * E1 * bm⁻¹ ∈ T0m := by
    have h := bm_conj e1
    rw [κHom_e1] at h
    rw [h]
    exact Q1m_le_T0m (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hβ2 : bm * E2 * bm⁻¹ ∈ T0m := by
    have h := bm_conj e2
    rw [κHom_e2] at h
    rw [h]
    exact Q1m_le_T0m (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hβ3 : bm * F1 * bm⁻¹ ∈ T0m := by
    have h := bm_conj f1
    rw [κHom_f1] at h
    rw [h]
    exact Q1m_le_T0m (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hβ4 : bm * F2 * bm⁻¹ ∈ T0m := by
    have h := bm_conj f2
    rw [κHom_f2] at h
    rw [h]
    exact Q1m_le_T0m (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hβ5 : bm * tm * bm⁻¹ ∈ T0m := by
    have h : bm * tm * bm⁻¹ = tm := by
      rw [← tm_mul_bm]
      group
    rw [h]
    exact tp_mem_genOf (gs := [e1T, e2T, f1T, f2T, tmT]) (by simp)
  have hmap : T0m.map (MulAut.conj bm).toMonoidHom ≤ T0m := by
    unfold T0m
    rw [genOf, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨T, hT, rfl⟩ := hx
    change bm * tp 315 T * bm⁻¹ ∈ T0m
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl
    · exact hβ1
    · exact hβ2
    · exact hβ3
    · exact hβ4
    · exact hβ5
  have heq : T0m.map (MulAut.conj bm).toMonoidHom = T0m :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj bm).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

noncomputable def χQ : ↥Q1m ≃* Q1M :=
  (MonoidHom.ofInjective κHom_injective).symm

theorem κHom_χQ (x : ↥Q1m) :
    κHom (χQ x) = (x : Equiv.Perm (Fin 315)) :=
  congrArg Subtype.val ((MonoidHom.ofInjective κHom_injective).apply_symm_apply x)

theorem actsAs_bm : ActsAs χQ bm βM := by
  intro x y hy
  refine κHom_injective ?_
  rw [κHom_χQ, ← bm_conj (χQ x), κHom_χQ]
  exact hy

theorem actsAs_rm : ActsAs χQ rm ρM := by
  intro x y hy
  refine κHom_injective ?_
  rw [κHom_χQ, ← rm_conj (χQ x), κHom_χQ]
  exact hy

theorem actsAs_tm : ActsAs χQ tm τM := by
  intro x y hy
  refine κHom_injective ?_
  rw [κHom_χQ, ← tm_conj (χQ x), κHom_χQ]
  exact hy

theorem Q1m_le_X2m : Q1m ≤ X2m := by
  rw [Q1m_eq_closure, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨e1T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨e2T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨f1T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨f2T, by simp, rfl⟩

theorem Am_le_X2m : Am ≤ X2m := by
  unfold Am X2m
  rw [genOf, genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨rmT, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨bmT, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨tmT, by simp, rfl⟩

theorem bm_mem_normalizer_Q1m :
    bm ∈ Subgroup.normalizer (Q1m : Set (Equiv.Perm (Fin 315))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj bm).injective])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hy
  rw [← hq]
  change bm * κHom q * bm⁻¹ ∈ Q1m
  rw [bm_conj q]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem rm_mem_normalizer_Q1m :
    rm ∈ Subgroup.normalizer (Q1m : Set (Equiv.Perm (Fin 315))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj rm).injective])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hy
  rw [← hq]
  change rm * κHom q * rm⁻¹ ∈ Q1m
  rw [rm_conj q]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem tm_mem_normalizer_Q1m :
    tm ∈ Subgroup.normalizer (Q1m : Set (Equiv.Perm (Fin 315))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj tm).injective])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hy
  rw [← hq]
  change tm * κHom q * tm⁻¹ ∈ Q1m
  rw [tm_conj q]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem X2m_le_normalizer_Q1m :
    X2m ≤ Subgroup.normalizer (Q1m : Set (Equiv.Perm (Fin 315))) := by
  unfold X2m
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.le_normalizer E1_mem_Q1m
  · exact Subgroup.le_normalizer E2_mem_Q1m
  · exact Subgroup.le_normalizer F1_mem_Q1m
  · exact Subgroup.le_normalizer F2_mem_Q1m
  · exact rm_mem_normalizer_Q1m
  · exact bm_mem_normalizer_Q1m
  · exact tm_mem_normalizer_Q1m

theorem C2_le_j2P :
    genOf 315 j2C2Gens ≤ j2P := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hr := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hC2 : genOf 315 j2C2Gens =
      j2P ⊓ Subgroup.centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315))) := by
    have h := hr.2.2.2.1
    dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h
  rw [hC2]
  exact inf_le_left

theorem X2m_le_j2P :
    X2m ≤ j2P := by
  have hb0 : b0OK = true := Certificates.certificate733001.2.2.2.1
  have hC2 := C2_le_j2P
  have hrm : rm ∈ j2P :=
    (j2_groupData.sift (rmT ()) rm (rep_rmT hb0)).mp
      (sift_rmT Certificates.certificate733001.2.2.2.2.2.2.2.2)
  unfold X2m
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hC2 (T0m_le_C2 (Q1m_le_T0m E1_mem_Q1m))
  · exact hC2 (T0m_le_C2 (Q1m_le_T0m E2_mem_Q1m))
  · exact hC2 (T0m_le_C2 (Q1m_le_T0m F1_mem_Q1m))
  · exact hC2 (T0m_le_C2 (Q1m_le_T0m F2_mem_Q1m))
  · exact hrm
  · exact hC2 bm_mem_C2
  · exact hC2 (T0m_le_C2 tm_mem_T0m)

theorem T0m_le_X2m : T0m ≤ X2m := by
  unfold T0m X2m
  rw [genOf, genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨e1T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨e2T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨f1T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨f2T, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨tmT, by simp, rfl⟩

@[expose] noncomputable def actA : ↥Am →* MulAut Q1M :=
  (parAct X2m_le_normalizer_Q1m χQ).comp (Subgroup.inclusion Am_le_X2m)

theorem rm_mem_Am : rm ∈ Am := by
  unfold Am
  rw [genOf]
  exact Subgroup.subset_closure ⟨rmT, by simp, rfl⟩

theorem bm_mem_Am : bm ∈ Am := by
  unfold Am
  rw [genOf]
  exact Subgroup.subset_closure ⟨bmT, by simp, rfl⟩

theorem tm_mem_Am : tm ∈ Am := by
  unfold Am
  rw [genOf]
  exact Subgroup.subset_closure ⟨tmT, by simp, rfl⟩

theorem actA_rm : actA ⟨rm, rm_mem_Am⟩ = ρM := by
  show parAct X2m_le_normalizer_Q1m χQ ⟨rm, Am_le_X2m rm_mem_Am⟩ = ρM
  exact parAct_eq_of_actsAs (Am_le_X2m rm_mem_Am) actsAs_rm

theorem actA_bm : actA ⟨bm, bm_mem_Am⟩ = βM := by
  show parAct X2m_le_normalizer_Q1m χQ ⟨bm, Am_le_X2m bm_mem_Am⟩ = βM
  exact parAct_eq_of_actsAs (Am_le_X2m bm_mem_Am) actsAs_bm

theorem actA_tm : actA ⟨tm, tm_mem_Am⟩ = τM := by
  show parAct X2m_le_normalizer_Q1m χQ ⟨tm, Am_le_X2m tm_mem_Am⟩ = τM
  exact parAct_eq_of_actsAs (Am_le_X2m tm_mem_Am) actsAs_tm

theorem nonempty_X2m_equiv :
    Nonempty (↥X2m ≃* Q1M ⋊[AJ.subtype] ↥AJ) := by
  have hAP : Am ≤ X2m := Am_le_X2m
  have hQP : Q1m ≤ X2m := Q1m_le_X2m
  have hPQ : X2m ≤ Subgroup.normalizer (Q1m : Set (Equiv.Perm (Fin 315))) :=
    X2m_le_normalizer_Q1m
  have hρ : ρM ∈ actA.range := by
    rw [← actA_rm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hβ : βM ∈ actA.range := by
    rw [← actA_bm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hτ : τM ∈ actA.range := by
    rw [← actA_tm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hAJle : AJ ≤ actA.range := by
    intro x hx
    rw [mem_AJ_iff, mem_ajList] at hx
    obtain ⟨i, j, k, rfl⟩ := hx
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hρ _) (Subgroup.pow_mem _ hβ _))
      (Subgroup.pow_mem _ hτ _)
  have hcardrange : Nat.card actA.range = 18 := by
    have h1 : Nat.card actA.range ≤ Nat.card ↥Am :=
      Nat.card_le_card_of_surjective
        (fun a : ↥Am => (⟨actA a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ : ↥actA.range))
        (fun b => by
          obtain ⟨a, ha⟩ := b.2
          exact ⟨a, Subtype.ext ha⟩)
    rw [card_Am] at h1
    have h2 : 18 ≤ Nat.card actA.range := by
      rw [← card_AJ]
      exact Nat.card_le_card_of_injective (Subgroup.inclusion hAJle)
        (Subgroup.inclusion_injective hAJle)
    omega
  have hrange : actA.range = AJ := by
    rw [eq_comm]
    exact Subgroup.eq_of_le_of_card_ge hAJle (by rw [card_AJ, hcardrange])
  have hinj : Function.Injective actA := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥Am) actA.ker
    have hq : Nat.card (↥Am ⧸ actA.ker) = Nat.card actA.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange actA).toEquiv
    rw [hq, hrange, card_AJ, card_Am] at hcard
    have hker : Nat.card actA.ker = 1 := by omega
    refine (MonoidHom.ker_eq_bot_iff actA).mp ?_
    rw [Subgroup.eq_bot_iff_card]
    exact hker
  have hAQ : Am ⊓ Q1m = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haAm, haQ⟩ := Subgroup.mem_inf.mp ha
    have h1 : actA ⟨a, haAm⟩ = MulAut.conj (χQ ⟨a, haQ⟩) := by
      show parAct X2m_le_normalizer_Q1m χQ ⟨a, hAP haAm⟩ = MulAut.conj (χQ ⟨a, haQ⟩)
      exact parAct_of_mem (Q := Q1m) (χ := χQ) haQ (hAP haAm)
    have h2 : actA ⟨a, haAm⟩ ∈ AJ := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h3 : MulAut.conj (χQ ⟨a, haQ⟩) ∈ AJ' := AJ_le_AJ' (h1 ▸ h2)
    have h4 : MulAut.conj (χQ ⟨a, haQ⟩) = 1 := conj_eq_one_of_mem_AJ' h3
    have h5 : actA ⟨a, haAm⟩ = 1 := by rw [h1, h4]
    have h5' : actA ⟨a, haAm⟩ = actA 1 := by rw [h5, map_one]
    have h6 : (⟨a, haAm⟩ : ↥Am) = 1 := hinj h5'
    simpa using congrArg Subtype.val h6
  have hcard : Nat.card Q1m * Nat.card Am = Nat.card X2m := by
    rw [card_Q1m, card_Am, card_X2m]
  let e : ↥Am ≃* ↥AJ := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ a : ↥Am, (e a : MulAut Q1M) = parAct hPQ χQ (Subgroup.inclusion hAP a) :=
    fun a => rfl
  exact nonempty_mulEquiv_semidirect hQP hPQ hAP hAQ hcard χQ e he

section Y2

open CFSG.Quasithin.A312J2 CFSG.QuasithinUnique

theorem T0m_le_j2P :
    T0m ≤ j2P :=
  le_trans T0m_le_C2 C2_le_j2P

theorem sylow_T0m_subgroupOf :
    IsSylowTwoOf (T0m.subgroupOf j2P) ⊤ := by
  have hJ2 : Nat.card ↥j2P = 604800 := card_j2P
  have hT0le : T0m ≤ j2P := T0m_le_j2P
  have hcT : Nat.card (T0m.subgroupOf j2P) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT0le).toEquiv]
    exact card_T0m
  refine ⟨le_top, IsPGroup.of_card (p := 2) (n := 7) (by rw [hcT]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index (T0m.subgroupOf j2P)
  rw [hcT, hJ2] at h1
  have h2 : (T0m.subgroupOf j2P).index = 4725 := by omega
  show ¬ 2 ∣ (T0m.subgroupOf j2P).relIndex ⊤
  rw [Subgroup.relIndex_top_right, h2]
  norm_num

theorem card_subgroupOf_X2m :
    Nat.card (X2m.subgroupOf j2P) = 1152 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe X2m_le_j2P).toEquiv]
  exact card_X2m

theorem card_Y2_J :
    Nat.card (j2CtxA.Y 2) = 1152 := by
  have h := j2A_card (j := 2) (by norm_num)
  simpa using h

theorem nonempty_X2m_equiv_Y2 :
    Nonempty (↥X2m ≃* ↥(j2CtxA.Y 2)) := by
  have hT0le : T0m.subgroupOf j2P ≤ X2m.subgroupOf j2P :=
    Subgroup.subgroupOf_mono j2P T0m_le_X2m
  let Z : Subgroup ↥j2P := X2m.subgroupOf j2P
  have hZcard : Nat.card Z = 1152 := card_subgroupOf_X2m
  let ψ : ↥j2P ≃* ↥CFSG.Sporadic.J2.J :=
    (CFSG.Sporadic.Bridge.J2.nativeEquiv.symm.trans CFSG.Sporadic.Schreier.j2PermEquiv).symm
  obtain ⟨e⟩ := @CFSG.Quasithin.F112R.nonempty_equiv_of_overgroup ↥j2P
    ↥CFSG.Sporadic.J2.J inferInstance inferInstance inferInstance inferInstance ψ
    (T0m.subgroupOf j2P) sylow_T0m_subgroupOf j2CtxA.S j2A_sylow Z hT0le (j2CtxA.Y 2)
    (fun W hSW hc => by
      refine J2Y.eq_of_card (j := 2) (Or.inl rfl) hSW ?_
      rw [hc, hZcard, card_Y2_J])
  exact ⟨(Subgroup.subgroupOfEquivOfLe X2m_le_j2P).symm.trans e⟩

theorem nonempty_Y2_equiv :
    Nonempty (↥(j2CtxA.Y 2) ≃* Q1M ⋊[AJ.subtype] ↥AJ) := by
  obtain ⟨e1⟩ := nonempty_X2m_equiv_Y2
  obtain ⟨e2⟩ := nonempty_X2m_equiv
  exact ⟨e1.symm.trans e2⟩

end Y2

section HeisChart

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G}

private noncomputable abbrev chartC2 : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 j2C2Gens

private theorem chartQ1m_le_C2 : Q1m ≤ chartC2 :=
  le_trans Q1m_le_T0m T0m_le_C2

private noncomputable abbrev chartD2 (Φ : ↥L2 ≃* ↥chartC2) : Subgroup ↥L2 :=
  (Q1m.subgroupOf chartC2).comap (Φ : ↥L2 →* ↥chartC2)

private noncomputable abbrev chartD (Φ : ↥L2 ≃* ↥chartC2) : Subgroup G :=
  (chartD2 Φ).map L2.subtype

private theorem chartD2_map (Φ : ↥L2 ≃* ↥chartC2) :
    (chartD2 Φ).map (Φ : ↥L2 →* ↥chartC2) = Q1m.subgroupOf chartC2 := by
  rw [chartD2]
  exact Subgroup.map_comap_eq_self_of_surjective Φ.surjective _

private theorem chartD_symm_coe (Φ : ↥L2 ≃* ↥chartC2) (x : ↥(chartD Φ)) :
    (((Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm x :
      ↥L2) : G) = (x : G) := by
  have h := congrArg Subtype.val
    ((Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).apply_symm_apply x)
  exact h

private noncomputable def chartζ (Φ : ↥L2 ≃* ↥chartC2) : ↥(chartD Φ) ≃* Q1M :=
  (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm.trans
    ((MulEquiv.subgroupMap Φ (chartD2 Φ)).trans
      ((MulEquiv.subgroupCongr (chartD2_map Φ)).trans
        ((Subgroup.subgroupOfEquivOfLe chartQ1m_le_C2).trans χQ)))

private theorem chartζ_apply_coe (Φ : ↥L2 ≃* ↥chartC2) (x : ↥(chartD Φ)) :
    κHom (chartζ Φ x) =
      (Φ ((Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm x) :
        Equiv.Perm (Fin 315)) := by
  have hζ : chartζ Φ x =
      ((Subgroup.subgroupOfEquivOfLe chartQ1m_le_C2).trans χQ)
        ((MulEquiv.subgroupCongr (chartD2_map Φ))
          ((MulEquiv.subgroupMap Φ (chartD2 Φ))
            ((Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm x))) :=
    rfl
  rw [hζ, MulEquiv.trans_apply, κHom_χQ]
  rfl

private theorem mem_chartD_iff (Φ : ↥L2 ≃* ↥chartC2) {x : ↥L2} :
    (x : G) ∈ chartD Φ ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ Q1m := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hy' : (Φ y : Equiv.Perm (Fin 315)) ∈ Q1m := by
      rw [chartD2, Subgroup.mem_comap] at hy
      exact Subgroup.mem_subgroupOf.mp hy
    have hyx : y = x := L2.subtype_injective (by simpa using hxy)
    simpa [hyx] using hy'
  · intro hx
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [chartD2, Subgroup.mem_comap]
    exact Subgroup.mem_subgroupOf.mpr hx

private theorem chartD_le_L2 (Φ : ↥L2 ≃* ↥chartC2) : chartD Φ ≤ L2 := by
  rintro g ⟨x, -, rfl⟩
  exact x.2

private theorem chartD_le_S (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m) :
    chartD Φ ≤ S := by
  rintro g ⟨x, hx, rfl⟩
  change Φ x ∈ Q1m.subgroupOf chartC2 at hx
  exact (hΦS x).mpr (Q1m_le_T0m (Subgroup.mem_subgroupOf.mp hx))

private theorem chartD_le_S2 (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m) :
    chartD Φ ≤ S ⊓ L2 :=
  le_inf (chartD_le_S Φ hΦS) (chartD_le_L2 Φ)

private theorem chartD_card (Φ : ↥L2 ≃* ↥chartC2) : Nat.card (chartD Φ) = 64 := by
  rw [chartD, Subgroup.card_map_of_injective L2.subtype_injective]
  have h1 : Nat.card (chartD2 Φ) = Nat.card ↥((chartD2 Φ).map (Φ : ↥L2 →* ↥chartC2)) :=
    Nat.card_congr (MulEquiv.subgroupMap Φ (chartD2 Φ)).toEquiv
  rw [chartD2_map] at h1
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe chartQ1m_le_C2).toEquiv]
  exact card_Q1m

private noncomputable def chartβ (Φ : ↥L2 ≃* ↥chartC2) : ↥L2 :=
  Φ.symm ⟨bm, bm_mem_C2⟩

private theorem chartβ_apply (Φ : ↥L2 ≃* ↥chartC2) :
    (Φ (chartβ Φ) : Equiv.Perm (Fin 315)) = bm := by
  have h : Φ (chartβ Φ) = ⟨bm, bm_mem_C2⟩ := Φ.apply_symm_apply _
  exact congrArg (fun z : ↥chartC2 => (z : Equiv.Perm (Fin 315))) h

private noncomputable def chartτ (Φ : ↥L2 ≃* ↥chartC2) : ↥L2 :=
  Φ.symm ⟨tm, T0m_le_C2 tm_mem_T0m⟩

private theorem chartτ_apply (Φ : ↥L2 ≃* ↥chartC2) :
    (Φ (chartτ Φ) : Equiv.Perm (Fin 315)) = tm := by
  have h : Φ (chartτ Φ) = ⟨tm, T0m_le_C2 tm_mem_T0m⟩ := Φ.apply_symm_apply _
  exact congrArg (fun z : ↥chartC2 => (z : Equiv.Perm (Fin 315))) h

private theorem chart_Phi_conj (Φ : ↥L2 ≃* ↥chartC2) {γ x : ↥L2}
    {b : Equiv.Perm (Fin 315)} (hγ : (Φ γ : Equiv.Perm (Fin 315)) = b) :
    (Φ (γ * x * γ⁻¹) : Equiv.Perm (Fin 315)) =
      b * (Φ x : Equiv.Perm (Fin 315)) * b⁻¹ := by
  simp [map_mul, map_inv, hγ]

private theorem chart_normalizes_S2_of_mem (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    {γ : ↥L2} {b : Equiv.Perm (Fin 315)}
    (hγ : (Φ γ : Equiv.Perm (Fin 315)) = b)
    (hb : b ∈ Subgroup.normalizer (T0m : Set (Equiv.Perm (Fin 315)))) :
    (γ : G) ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    have hzL2 : z ∈ L2 := hz.2
    let zL : ↥L2 := ⟨z, hzL2⟩
    have hzT : (Φ zL : Equiv.Perm (Fin 315)) ∈ T0m := (hΦS zL).mp hz.1
    have hbconj : b * (Φ zL : Equiv.Perm (Fin 315)) * b⁻¹ ∈ T0m :=
      (Subgroup.mem_normalizer_iff.mp hb _).mp hzT
    have hΦconj : (Φ (γ * zL * γ⁻¹) : Equiv.Perm (Fin 315)) =
        b * (Φ zL : Equiv.Perm (Fin 315)) * b⁻¹ :=
      chart_Phi_conj Φ hγ
    constructor
    · change (((γ * zL * γ⁻¹ : ↥L2) : G) ∈ S)
      exact (hΦS (γ * zL * γ⁻¹)).mpr (by rw [hΦconj]; exact hbconj)
    · exact L2.mul_mem (L2.mul_mem γ.2 hzL2) (L2.inv_mem γ.2)
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj (γ : G) : G →* G))
      (MulAut.conj (γ : G)).injective]

private theorem chartβ_mem_normalizer_S2 (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m) :
    (chartβ Φ : G) ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
  chart_normalizes_S2_of_mem Φ hΦS (chartβ_apply Φ) bm_mem_normalizer_T0m

private theorem chartβ_mem_borel (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m) :
    (chartβ Φ : G) ∈ borelOf L2 S :=
  ⟨(chartβ Φ).2, chartβ_mem_normalizer_S2 Φ hΦS⟩

private theorem chartβ_pow_three (Φ : ↥L2 ≃* ↥chartC2) : (chartβ Φ : G) ^ 3 = 1 := by
  have hΦβ : Φ (chartβ Φ) = ⟨bm, bm_mem_C2⟩ := Φ.apply_symm_apply _
  have h3 : (chartβ Φ) ^ 3 = 1 := by
    apply Φ.injective
    rw [map_pow, hΦβ, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, bm_pow_three]
  simpa using congrArg Subtype.val h3

private theorem chartβ_mem_normalizer_D (Φ : ↥L2 ≃* ↥chartC2) :
    (chartβ Φ : G) ∈ Subgroup.normalizer ((chartD Φ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨xL, hxL, rfl⟩ := Subgroup.mem_map.mp hx
    have hxQ : (Φ xL : Equiv.Perm (Fin 315)) ∈ Q1m := by
      change Φ xL ∈ Q1m.subgroupOf chartC2 at hxL
      exact Subgroup.mem_subgroupOf.mp hxL
    have hconjQ : bm * (Φ xL : Equiv.Perm (Fin 315)) * bm⁻¹ ∈ Q1m :=
      (Subgroup.mem_normalizer_iff.mp bm_mem_normalizer_Q1m _).mp hxQ
    have hΦconj : (Φ (chartβ Φ * xL * (chartβ Φ)⁻¹) : Equiv.Perm (Fin 315)) =
        bm * (Φ xL : Equiv.Perm (Fin 315)) * bm⁻¹ :=
      chart_Phi_conj Φ (chartβ_apply Φ)
    change (((chartβ Φ * xL * (chartβ Φ)⁻¹ : ↥L2) : G) ∈ chartD Φ)
    exact (mem_chartD_iff Φ).mpr (by rw [hΦconj]; exact hconjQ)
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj (chartβ Φ : G) : G →* G))
      (MulAut.conj (chartβ Φ : G)).injective]

private theorem chartζ_actsAs_beta (Φ : ↥L2 ≃* ↥chartC2) :
    ActsAs (chartζ Φ) (chartβ Φ : G) βM := by
  intro x y hy
  let xL := (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm x
  let yL := (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm y
  have hxL : (xL : G) = (x : G) := chartD_symm_coe Φ x
  have hyL : (yL : G) = (y : G) := chartD_symm_coe Φ y
  have hxy : yL = chartβ Φ * xL * (chartβ Φ)⁻¹ := by
    apply L2.subtype_injective
    calc (yL : G) = (y : G) := hyL
      _ = (chartβ Φ : G) * (x : G) * (chartβ Φ : G)⁻¹ := hy
      _ = (chartβ Φ : G) * (xL : G) * (chartβ Φ : G)⁻¹ := by rw [hxL]
      _ = ((chartβ Φ * xL * (chartβ Φ)⁻¹ : ↥L2) : G) := rfl
  apply κHom_injective
  rw [chartζ_apply_coe Φ y, ← bm_conj (chartζ Φ x), chartζ_apply_coe Φ x]
  rw [← chart_Phi_conj (x := xL) Φ (chartβ_apply Φ), ← hxy]

private theorem chartζ_actsAs_tau (Φ : ↥L2 ≃* ↥chartC2) :
    ActsAs (chartζ Φ) (chartτ Φ : G) τM := by
  intro x y hy
  let xL := (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm x
  let yL := (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm y
  have hxL : (xL : G) = (x : G) := chartD_symm_coe Φ x
  have hyL : (yL : G) = (y : G) := chartD_symm_coe Φ y
  have hxy : yL = chartτ Φ * xL * (chartτ Φ)⁻¹ := by
    apply L2.subtype_injective
    calc (yL : G) = (y : G) := hyL
      _ = (chartτ Φ : G) * (x : G) * (chartτ Φ : G)⁻¹ := hy
      _ = (chartτ Φ : G) * (xL : G) * (chartτ Φ : G)⁻¹ := by rw [hxL]
      _ = ((chartτ Φ * xL * (chartτ Φ)⁻¹ : ↥L2) : G) := rfl
  apply κHom_injective
  rw [chartζ_apply_coe Φ y, ← tm_conj (chartζ Φ x), chartζ_apply_coe Φ x]
  rw [← chart_Phi_conj (x := xL) Φ (chartτ_apply Φ), ← hxy]

private theorem chartτ_mem_S2 (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m) :
    (chartτ Φ : G) ∈ S ⊓ L2 := by
  refine ⟨?_, (chartτ Φ).2⟩
  exact (hΦS (chartτ Φ)).mpr (by rw [chartτ_apply]; exact tm_mem_T0m)

private theorem map_beta_chartImage (Φ : ↥L2 ≃* ↥chartC2) {A : Subgroup G}
    (hAD : A ≤ chartD Φ)
    (hA : (chartβ Φ : G) ∈ Subgroup.normalizer (A : Set G)) :
    (((A.subgroupOf (chartD Φ)).map (chartζ Φ : ↥(chartD Φ) →* Q1M)).map βM.toMonoidHom) =
      (A.subgroupOf (chartD Φ)).map (chartζ Φ).toMonoidHom := by
  let H : Subgroup ↥(chartD Φ) := A.subgroupOf (chartD Φ)
  let W : Subgroup Q1M := H.map (chartζ Φ : ↥(chartD Φ) →* Q1M)
  have hle : W.map βM.toMonoidHom ≤ W := by
    rintro q ⟨w, hw, rfl⟩
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hw
    have hdA : (d : G) ∈ A := Subgroup.mem_subgroupOf.mp hd
    have hconjA : (chartβ Φ : G) * (d : G) * (chartβ Φ : G)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hA (d : G)).mp hdA
    have hconjD : (chartβ Φ : G) * (d : G) * (chartβ Φ : G)⁻¹ ∈ chartD Φ :=
      hAD hconjA
    let e : ↥(chartD Φ) :=
      ⟨(chartβ Φ : G) * (d : G) * (chartβ Φ : G)⁻¹, hconjD⟩
    have heH : e ∈ H := Subgroup.mem_subgroupOf.mpr hconjA
    exact Subgroup.mem_map.mpr ⟨e, heH, chartζ_actsAs_beta Φ d e rfl⟩
  have hcard : Nat.card (W.map βM.toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective (f := (βM : Q1M →* Q1M)) βM.injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

private theorem false_of_relIndex_two (Φ : ↥L2 ≃* ↥chartC2) {A : Subgroup G}
    (hAD : A ≤ chartD Φ)
    (hA : (chartβ Φ : G) ∈ Subgroup.normalizer (A : Set G))
    (hidx2 : A.relIndex (chartD Φ) = 2) : False := by
  have hWindex : ((A.subgroupOf (chartD Φ)).map (chartζ Φ : ↥(chartD Φ) →* Q1M)).index = 2 := by
    rw [Subgroup.index_map_equiv]
    exact hidx2
  have hWbeta : ((A.subgroupOf (chartD Φ)).map (chartζ Φ : ↥(chartD Φ) →* Q1M)).map
        βM.toMonoidHom =
      (A.subgroupOf (chartD Φ)).map (chartζ Φ : ↥(chartD Φ) →* Q1M) :=
    map_beta_chartImage Φ hAD hA
  exact not_index_two hWindex hWbeta

private theorem chartβ_mem_normalizer_K (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    (chartβ Φ : G) ∈ Subgroup.normalizer ((S ⊓ L2 ⊓ L1 : Subgroup G) : Set G) := by
  have h1 : (chartβ Φ : G) ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    chartβ_mem_normalizer_S2 Φ hΦS
  have h2 : (chartβ Φ : G) ∈ Subgroup.normalizer (L1 : Set G) :=
    hN (chartβ_mem_borel Φ hΦS)
  exact Subgroup.inf_normalizer_le_normalizer_inf (H := S ⊓ L2) (K := L1) ⟨h1, h2⟩

private theorem chartβ_mem_normalizer_Q1 (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    (chartβ Φ : G) ∈ Subgroup.normalizer ((pCoreOf 2 L1 : Subgroup G) : Set G) :=
  (normalizer_le_normalizer_pCoreOf (r := 2) L1) (hN (chartβ_mem_borel Φ hΦS))

private theorem chartD_le_K (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    chartD Φ ≤ S ⊓ L2 ⊓ L1 := by
  let K : Subgroup G := S ⊓ L2 ⊓ L1
  have hrelK : K.relIndex (chartD Φ) ≤ 2 := by
    have hne : K.relIndex (S ⊓ L2) ≠ 0 := by
      have hdvd : K.relIndex (S ⊓ L2) ∣ Nat.card ↥(S ⊓ L2) :=
        Subgroup.relIndex_dvd_card (H := K) (K := S ⊓ L2)
      have hpos : 0 < Nat.card ↥(S ⊓ L2) := Nat.card_pos
      exact (Nat.pos_of_dvd_of_pos hdvd hpos).ne'
    calc K.relIndex (chartD Φ) ≤ K.relIndex (S ⊓ L2) :=
          Subgroup.relIndex_le_of_le_right (chartD_le_S2 Φ hΦS) hne
      _ ≤ 2 := hidx
  have hrelA : (chartD Φ ⊓ K).relIndex (chartD Φ) ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact hrelK
  have hposA : 0 < (chartD Φ ⊓ K).relIndex (chartD Φ) := by
    have hdvd : (chartD Φ ⊓ K).relIndex (chartD Φ) ∣ Nat.card ↥(chartD Φ) :=
      Subgroup.relIndex_dvd_card (H := chartD Φ ⊓ K) (K := chartD Φ)
    have hpos : 0 < Nat.card ↥(chartD Φ) := by rw [chartD_card]; norm_num
    exact Nat.pos_of_dvd_of_pos hdvd hpos
  have hne2 : (chartD Φ ⊓ K).relIndex (chartD Φ) ≠ 2 := by
    intro h2
    have hNA : (chartβ Φ : G) ∈ Subgroup.normalizer
        ((chartD Φ ⊓ K : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := chartD Φ) (K := S ⊓ L2 ⊓ L1)
        ⟨chartβ_mem_normalizer_D Φ, chartβ_mem_normalizer_K Φ hΦS hN⟩
    exact false_of_relIndex_two Φ inf_le_left hNA h2
  have hone : (chartD Φ ⊓ K).relIndex (chartD Φ) = 1 := by omega
  exact le_trans (Subgroup.relIndex_eq_one.mp hone) inf_le_right

private theorem chartD_eq_pCore (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hQ1 : Nat.card (pCoreOf 2 L1) = 2 ^ 6) (hQS : pCoreOf 2 L1 ≤ S ⊓ L1)
    (hS1 : Nat.card ↥(S ⊓ L1) = 2 ^ 7)
    (hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    chartD Φ = pCoreOf 2 L1 := by
  have hDK : chartD Φ ≤ S ⊓ L2 ⊓ L1 := chartD_le_K Φ hΦS hidx hN
  have hDS1 : chartD Φ ≤ S ⊓ L1 :=
    le_inf (le_trans hDK (show S ⊓ L2 ⊓ L1 ≤ S from le_trans inf_le_left inf_le_left))
      (le_trans hDK (show S ⊓ L2 ⊓ L1 ≤ L1 from inf_le_right))
  have hQ1card : Nat.card (pCoreOf 2 L1) = 64 := by rw [hQ1]; norm_num
  have hrelS1 : (pCoreOf 2 L1).relIndex (S ⊓ L1) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 L1) (K := S ⊓ L1)
    have hinf : pCoreOf 2 L1 ⊓ (S ⊓ L1) = pCoreOf 2 L1 := inf_eq_left.mpr hQS
    rw [hinf, hQ1card, hS1] at h
    omega
  have hle2 : (pCoreOf 2 L1).relIndex (chartD Φ) ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := pCoreOf 2 L1)
      (K := chartD Φ) (L := S ⊓ L1) hDS1 (by rw [hrelS1]; norm_num)
    omega
  have hpos : 0 < (pCoreOf 2 L1).relIndex (chartD Φ) := by
    have hdvd := Subgroup.relIndex_dvd_card (H := pCoreOf 2 L1) (K := chartD Φ)
    have hposD : 0 < Nat.card ↥(chartD Φ) := by rw [chartD_card]; norm_num
    exact Nat.pos_of_dvd_of_pos hdvd hposD
  have hne2 : (pCoreOf 2 L1).relIndex (chartD Φ) ≠ 2 := by
    intro h2
    have hNA : (chartβ Φ : G) ∈ Subgroup.normalizer
        ((pCoreOf 2 L1 ⊓ chartD Φ : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 L1) (K := chartD Φ)
        ⟨chartβ_mem_normalizer_Q1 Φ hΦS hN, chartβ_mem_normalizer_D Φ⟩
    have h2' : (pCoreOf 2 L1 ⊓ chartD Φ).relIndex (chartD Φ) = 2 := by
      rw [Subgroup.inf_relIndex_right]
      exact h2
    exact false_of_relIndex_two Φ inf_le_right hNA h2'
  have hone : (pCoreOf 2 L1).relIndex (chartD Φ) = 1 := by omega
  have hle : chartD Φ ≤ pCoreOf 2 L1 := Subgroup.relIndex_eq_one.mp hone
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [chartD_card, hQ1]
  norm_num

private theorem index_Q1m_subgroupOf_T0m : (Q1m.subgroupOf T0m).index = 2 := by
  change Q1m.relIndex T0m = 2
  have h := Subgroup.relIndex_mul_card (H := Q1m) (K := T0m)
  have hinf : Q1m ⊓ T0m = Q1m := inf_eq_left.mpr Q1m_le_T0m
  rw [hinf, card_Q1m, card_T0m] at h
  omega

private theorem τM_ne_one : τM ≠ 1 := by
  intro h
  have h1 : τM e1 = f1 := by decide +kernel
  have h2 : τM e1 = e1 := by rw [h]; rfl
  exact (by decide : f1 ≠ e1) (h1.symm.trans h2)

private theorem exists_q_mul_tm_of_notMem (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    {x : G} (hxS2 : x ∈ S ⊓ L2)
    (hxQ : (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) ∉ Q1m) :
    ∃ q : Q1M, (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) = κHom q * tm := by
  let xL : ↥L2 := ⟨x, hxS2.2⟩
  change (Φ xL : Equiv.Perm (Fin 315)) ∉ Q1m at hxQ
  have hxT : (Φ xL : Equiv.Perm (Fin 315)) ∈ T0m := (hΦS xL).mp hxS2.1
  let a : ↥T0m := ⟨(Φ xL : Equiv.Perm (Fin 315)), hxT⟩
  let b : ↥T0m := ⟨tm, tm_mem_T0m⟩
  have hbQ : b ∉ Q1m.subgroupOf T0m := by
    intro h
    exact tm_not_mem_Q1m (Subgroup.mem_subgroupOf.mp h)
  have haQ : a ∉ Q1m.subgroupOf T0m := by
    intro h
    exact hxQ (by simpa [a] using Subgroup.mem_subgroupOf.mp h)
  have hab : a * b ∈ Q1m.subgroupOf T0m :=
    (Subgroup.mul_mem_iff_of_index_two (H := Q1m.subgroupOf T0m) index_Q1m_subgroupOf_T0m).mpr
      (iff_of_false haQ hbQ)
  let q : Q1M := χQ ⟨((a * b : ↥T0m) : Equiv.Perm (Fin 315)),
    Subgroup.mem_subgroupOf.mp hab⟩
  have hΦx : (Φ xL : Equiv.Perm (Fin 315)) = κHom q * tm := by
    have ha_eq : a = (a * b) * b⁻¹ := by group
    have hbval : (b : Equiv.Perm (Fin 315)) = tm := rfl
    have htminv : tm⁻¹ = tm := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_two] using tm_pow_two
    have hstep : (a : Equiv.Perm (Fin 315)) =
        ((a * b : ↥T0m) : Equiv.Perm (Fin 315)) * (b : Equiv.Perm (Fin 315))⁻¹ := by
      calc (a : Equiv.Perm (Fin 315)) =
          (((a * b) * b⁻¹ : ↥T0m) : Equiv.Perm (Fin 315)) :=
            congrArg (fun z : ↥T0m => (z : Equiv.Perm (Fin 315))) ha_eq
        _ = ((a * b : ↥T0m) : Equiv.Perm (Fin 315)) * (b : Equiv.Perm (Fin 315))⁻¹ := by
            conv_lhs => rw [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (Φ xL : Equiv.Perm (Fin 315)) = (a : Equiv.Perm (Fin 315)) := rfl
      _ = ((a * b : ↥T0m) : Equiv.Perm (Fin 315)) * (b : Equiv.Perm (Fin 315))⁻¹ := hstep
      _ = ((a * b : ↥T0m) : Equiv.Perm (Fin 315)) * tm := by rw [hbval, htminv]
      _ = κHom q * tm := by rw [κHom_χQ]
  exact ⟨q, hΦx⟩

private theorem central_action_of_mul_tm (Φ : ↥L2 ≃* ↥chartC2)
    (hDQ : chartD Φ = pCoreOf 2 L1)
    {x : G} (hxS2 : x ∈ S ⊓ L2)
    (hxcent : x ∈ Subgroup.centralizer (pCoreOf 2 L1 : Set G))
    {q : Q1M} (hΦx : (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) = κHom q * tm) :
    ∀ p : Q1M, (κHom q * tm) * κHom p * (κHom q * tm)⁻¹ = κHom p := by
  let xL : ↥L2 := ⟨x, hxS2.2⟩
  change (Φ xL : Equiv.Perm (Fin 315)) = κHom q * tm at hΦx
  intro p
  let dD : ↥(chartD Φ) := (chartζ Φ).symm p
  have hζd : chartζ Φ dD = p := (chartζ Φ).apply_symm_apply p
  let dL : ↥L2 :=
    (Subgroup.equivMapOfInjective (chartD2 Φ) L2.subtype L2.subtype_injective).symm dD
  have hdLval : (dL : G) = (dD : G) := chartD_symm_coe Φ dD
  have hdval : (Φ dL : Equiv.Perm (Fin 315)) = κHom p := by
    rw [← chartζ_apply_coe Φ dD, hζd]
  let dp : ↥(pCoreOf 2 L1) := ⟨(dD : G), hDQ ▸ dD.2⟩
  have hdpval : (dp : G) = (dL : G) := hdLval.symm
  have hcomm : x * (dL : G) = (dL : G) * x := by
    have h := (Subgroup.mem_centralizer_iff.mp hxcent) (dp : G) dp.2
    rw [hdpval] at h
    exact h.symm
  have hcommL : xL * dL = dL * xL := by
    apply L2.subtype_injective
    show (xL : G) * (dL : G) = (dL : G) * (xL : G)
    exact hcomm
  have hconjL : xL * dL * xL⁻¹ = dL := by
    rw [hcommL]
    group
  have hΦconj : (Φ xL : Equiv.Perm (Fin 315)) * (Φ dL : Equiv.Perm (Fin 315)) *
      (Φ xL : Equiv.Perm (Fin 315))⁻¹ = (Φ dL : Equiv.Perm (Fin 315)) := by
    have h := congrArg (fun z : ↥L2 => Φ z) hconjL
    simpa [map_mul, map_inv] using
      congrArg (fun z : ↥chartC2 => (z : Equiv.Perm (Fin 315))) h
  rw [← hΦx, ← hdval]
  exact hΦconj

private theorem exists_q_mul_tm (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hDQ : chartD Φ = pCoreOf 2 L1)
    {x : G} (hxS2 : x ∈ S ⊓ L2)
    (hxcent : x ∈ Subgroup.centralizer (pCoreOf 2 L1 : Set G))
    (hxQ : (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) ∉ Q1m) :
    ∃ q : Q1M, (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) = κHom q * tm ∧
      ∀ p : Q1M, (κHom q * tm) * κHom p * (κHom q * tm)⁻¹ = κHom p := by
  obtain ⟨q, hΦx⟩ := exists_q_mul_tm_of_notMem Φ hΦS hxS2 hxQ
  exact ⟨q, hΦx, central_action_of_mul_tm Φ hDQ hxS2 hxcent hΦx⟩

private theorem false_of_central_q_mul_tm {q : Q1M}
    (hcentral : ∀ p : Q1M, (κHom q * tm) * κHom p * (κHom q * tm)⁻¹ = κHom p) : False := by
  have hτ : τM = MulAut.conj q⁻¹ := by
    refine MulEquiv.ext fun p => ?_
    have h1 : κHom q * κHom (τM p) * (κHom q)⁻¹ = κHom p := by
      calc κHom q * κHom (τM p) * (κHom q)⁻¹
          = κHom q * (tm * κHom p * tm⁻¹) * (κHom q)⁻¹ := by rw [tm_conj p]
        _ = (κHom q * tm) * κHom p * (κHom q * tm)⁻¹ := by group
        _ = κHom p := hcentral p
    have h2 : q * τM p * q⁻¹ = p := by
      apply κHom_injective
      rw [map_mul, map_mul, map_inv, h1]
    calc τM p = q⁻¹ * (q * τM p * q⁻¹) * q := by group
      _ = q⁻¹ * p * q := by rw [h2]
      _ = MulAut.conj q⁻¹ p := by rw [MulAut.conj_apply, inv_inv]
  have hτmem : MulAut.conj q⁻¹ ∈ AJ' := by
    rw [← hτ]
    exact AJ_le_AJ' τM_mem_AJ
  have hone : MulAut.conj q⁻¹ = 1 := conj_eq_one_of_mem_AJ' hτmem
  exact τM_ne_one (hτ.trans hone)

private theorem centralizer_mem_Q1m (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hDQ : chartD Φ = pCoreOf 2 L1)
    {x : G} (hxS2 : x ∈ S ⊓ L2)
    (hxcent : x ∈ Subgroup.centralizer (pCoreOf 2 L1 : Set G)) :
    (Φ ⟨x, hxS2.2⟩ : Equiv.Perm (Fin 315)) ∈ Q1m := by
  by_contra hxQ
  obtain ⟨q, -, hcentral⟩ := exists_q_mul_tm Φ hΦS hDQ hxS2 hxcent hxQ
  exact false_of_central_q_mul_tm hcentral

private theorem centralizer_le_chartD (Φ : ↥L2 ≃* ↥chartC2)
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hQ1 : Nat.card (pCoreOf 2 L1) = 2 ^ 6) (hQS : pCoreOf 2 L1 ≤ S ⊓ L1)
    (hS1 : Nat.card ↥(S ⊓ L1) = 2 ^ 7)
    (hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    S ⊓ L2 ⊓ Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ chartD Φ := by
  have hDQ : chartD Φ = pCoreOf 2 L1 := chartD_eq_pCore Φ hΦS hQ1 hQS hS1 hidx hN
  intro x hx
  obtain ⟨hxS2, hxcent⟩ := Subgroup.mem_inf.mp hx
  exact (mem_chartD_iff Φ).mpr (centralizer_mem_Q1m Φ hΦS hDQ hxS2 hxcent)

theorem exists_heisChart (Φ : ↥L2 ≃* ↥(genOf 315 j2C2Gens))
    (hΦS : ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ T0m)
    (hQ1 : Nat.card (pCoreOf 2 L1) = 2 ^ 6) (hQS : pCoreOf 2 L1 ≤ S ⊓ L1)
    (hS1 : Nat.card ↥(S ⊓ L1) = 2 ^ 7)
    (hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2)
    (hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)) :
    ∃ χ : ↥(pCoreOf 2 L1) ≃* Q1M, pCoreOf 2 L1 ≤ S ⊓ L2 ∧
      (∃ β ∈ borelOf L2 S, β ^ 3 = 1 ∧ ActsAs χ β βM) ∧
      (∃ t ∈ S ⊓ L2, ActsAs χ t τM) ∧
      S ⊓ L2 ⊓ Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ pCoreOf 2 L1 := by
  have hDQ : chartD Φ = pCoreOf 2 L1 := chartD_eq_pCore Φ hΦS hQ1 hQS hS1 hidx hN
  let eDQ : ↥(pCoreOf 2 L1) ≃* ↥(chartD Φ) := (MulEquiv.subgroupCongr hDQ).symm
  let χ : ↥(pCoreOf 2 L1) ≃* Q1M := eDQ.trans (chartζ Φ)
  have hχ_apply : ∀ x : ↥(pCoreOf 2 L1), χ x = chartζ Φ (eDQ x) := fun _ => rfl
  have heDQ_apply : ∀ x : ↥(pCoreOf 2 L1), (eDQ x : G) = (x : G) :=
    fun x => MulEquiv.subgroupCongr_symm_apply hDQ x
  have hχβ : ActsAs χ (chartβ Φ : G) βM := by
    intro x y hy
    have hy' : (eDQ y : G) =
        (chartβ Φ : G) * (eDQ x : G) * (chartβ Φ : G)⁻¹ := by
      rw [heDQ_apply y, heDQ_apply x]
      exact hy
    calc χ y = chartζ Φ (eDQ y) := hχ_apply y
      _ = βM (chartζ Φ (eDQ x)) := chartζ_actsAs_beta Φ (eDQ x) (eDQ y) hy'
      _ = βM (χ x) := by rw [hχ_apply x]
  have hχt : ActsAs χ (chartτ Φ : G) τM := by
    intro x y hy
    have hy' : (eDQ y : G) =
        (chartτ Φ : G) * (eDQ x : G) * (chartτ Φ : G)⁻¹ := by
      rw [heDQ_apply y, heDQ_apply x]
      exact hy
    calc χ y = chartζ Φ (eDQ y) := hχ_apply y
      _ = τM (chartζ Φ (eDQ x)) := chartζ_actsAs_tau Φ (eDQ x) (eDQ y) hy'
      _ = τM (χ x) := by rw [hχ_apply x]
  refine ⟨χ, ?_, ⟨(chartβ Φ : G), chartβ_mem_borel Φ hΦS, chartβ_pow_three Φ, hχβ⟩,
    ⟨(chartτ Φ : G), chartτ_mem_S2 Φ hΦS, hχt⟩, ?_⟩
  · intro x hx
    have hx' : x ∈ chartD Φ := by rwa [← hDQ] at hx
    exact chartD_le_S2 Φ hΦS hx'
  · intro x hx
    have hx' : x ∈ chartD Φ := centralizer_le_chartD Φ hΦS hQ1 hQS hS1 hidx hN hx
    rwa [hDQ] at hx'

end HeisChart

end CFSG.Quasithin.F112R.St84.J2Model
