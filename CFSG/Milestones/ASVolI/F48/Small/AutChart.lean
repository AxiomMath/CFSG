module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartWords
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Base
public import CFSG.Milestones.ASVolI.F48.Small.AutChartCore
public import CFSG.Milestones.ASVolI.F48.Small.U42
public import Certificates.Certificate7544
public import Certificates.Certificate7545
public import CFSG.Milestones.ASVolI.F48.Small.AutBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Lat

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S image_lineSet lineSet_eq_of_sameSet
  sameSet_of_lineSet_eq Xs_eq x45_mem y45_mem P1 P2 nonempty_mulEquiv_Y lieModel_Y
  isSimpleGroup_of_lieModel_PSU_four_two repL_wordP wordP)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 f45)

theorem burnsideF48s_autc_fix0_of {l : List ℕ} {σ : P45} (h : RepL l σ) (h0 : l.getD 0 0 = 0) :
    σ 0 = 0 :=
  Fin.ext ((h.2 0).symm.trans h0)

theorem burnsideF48s_autc_not_fix0_of {l : List ℕ} {σ : P45} (h : RepL l σ)
    (h0 : l.getD 0 0 ≠ 0) : σ 0 ≠ 0 := fun e =>
  h0 ((h.2 0).trans (congrArg Fin.val e))

theorem burnsideF48s_autc_line_of {l : List ℕ} {σ : P45} (h : RepL l σ)
    (hs : sameSet (imgSet l L0) L0 = true) : σ '' L0S = L0S := by
  rw [L0S, image_lineSet h (by decide), lineSet_eq_of_sameSet hs]

theorem burnsideF48s_autc_not_line_of {l : List ℕ} {σ : P45} (h : RepL l σ)
    (hs : sameSet (imgSet l L0) L0 = false) : σ '' L0S ≠ L0S := by
  intro e
  rw [L0S, image_lineSet h (by decide)] at e
  exact Bool.false_ne_true (hs.symm.trans (sameSet_of_lineSet_eq e))

theorem burnsideF48s_autc_sign_gAP (k : ℕ) :
    Equiv.Perm.sign (gAP k) = if k % 4 = 3 then -1 else 1 := by
  have hx : Equiv.Perm.sign CFSG.Quasithin.H13.F431.U42.x45 = 1 :=
    sign_of_mem_Xs (Xs_eq ▸ x45_mem)
  have hy : Equiv.Perm.sign CFSG.Quasithin.H13.F431.U42.y45 = 1 :=
    sign_of_mem_Xs (Xs_eq ▸ y45_mem)
  have hf : Equiv.Perm.sign f45 = -1 := by decide +kernel
  unfold gAP
  split_ifs with h0 h1 h2 h3 h4 h5 <;> first | omega | simp_all

theorem burnsideF48s_autc_sign_wordAP (w : List ℕ) :
    Equiv.Perm.sign (wordAP w) = (-1) ^ (w.countP fun k => k % 4 = 3) := by
  induction w with
  | nil => simp [wordAP]
  | cons k w ih =>
    have e : wordAP (k :: w) = gAP k * wordAP w := by simp [wordAP]
    rw [e, map_mul, ih, burnsideF48s_autc_sign_gAP, List.countP_cons]
    by_cases h : k % 4 = 3
    · simp [h, pow_succ, mul_comm]
    · simp [h]

theorem burnsideF48s_autc_not_mem_Yh (w : List ℕ)
    (hw : (w.countP fun k => k % 4 = 3) % 2 = 1) : (⟨wordAP w, wordAP_mem w⟩ : Ah) ∉ Yh := by
  rw [← signA_eq_neg_one_iff, signA_apply]
  show Equiv.Perm.sign (wordAP w) = -1
  rw [burnsideF48s_autc_sign_wordAP]
  exact Odd.neg_one_pow (Nat.odd_iff.2 hw)

theorem burnsideF48s_autc_le_normalizer_inf (H : Subgroup Ah) :
    H ≤ Subgroup.normalizer ((Yh ⊓ H : Subgroup Ah) : Set Ah) := by
  intro h hh
  have hY := Yh_normal
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨hY.conj_mem x hx1 h, H.mul_mem (H.mul_mem hh hx2) (H.inv_mem hh)⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · have := hY.conj_mem _ hx1 h⁻¹
      simpa [mul_assoc] using this
    · have := H.mul_mem (H.mul_mem (H.inv_mem hh) hx2) hh
      simpa [mul_assoc] using this

theorem burnsideF48s_autc_mem_normalizer_closure {G : Type*} [Group G] {S : Set G} {t : G}
    (ht : t * t = 1) (hS : ∀ s ∈ S, t * s * t⁻¹ ∈ Subgroup.closure S) :
    t ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  have hmap : (Subgroup.closure S).map (MulAut.conj t).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hS s hs
  have key : ∀ x ∈ Subgroup.closure S, t * x * t⁻¹ ∈ Subgroup.closure S := fun x hx =>
    hmap (Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key x, fun hx => ?_⟩
  have h2 := key _ hx
  rw [htinv, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul,
    mul_one] at h2
  exact h2

section U42


theorem burnsideF48s_autc_u42_repL (k : Fin 5) :
    RepL ((burnsideF48s_autc_u42gl ()).getD k []) ((burnsideF48s_u42eG k : Ah) : P45) :=
  burnsideF48s_autc_repL_gl burnsideF48s_u42eXY k

theorem burnsideF48s_autc_u42_repLi (k : Fin 5) :
    RepL ((burnsideF48s_autc_u42gli ()).getD k []) (((burnsideF48s_u42eG k)⁻¹ : Ah) : P45) := by
  rw [Subgroup.coe_inv]
  exact burnsideF48s_autc_repL_gli burnsideF48s_u42eXY k

theorem burnsideF48s_autc_u42_mem_spec :
    (∀ k ∈ [0, 1, 2, 4], ((burnsideF48s_autc_u42gl ()).getD k []).getD 0 0 = 0) ∧
      ((burnsideF48s_autc_u42gl ()).getD 3 []).getD 0 0 ≠ 0 ∧
      (∀ k ∈ [0, 1, 3, 4],
        sameSet (imgSet ((burnsideF48s_autc_u42gl ()).getD k []) L0) L0 = true) ∧
      sameSet (imgSet ((burnsideF48s_autc_u42gl ()).getD 2 []) L0) L0 = false := by
  have h := Certificates.certificate7544.1
  simp only [burnsideF48s_autc_u42_checkMem, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem burnsideF48s_autc_u42_P1h :
    burnsideF48s_u42eG 0 ∈ P1h ∧ burnsideF48s_u42eG 1 ∈ P1h ∧ burnsideF48s_u42eG 2 ∈ P1h ∧
      burnsideF48s_u42eG 4 ∈ P1h ∧ burnsideF48s_u42eG 3 ∉ P1h := by
  obtain ⟨h1, h2, -, -⟩ := burnsideF48s_autc_u42_mem_spec
  have fix : ∀ k : Fin 5, ((burnsideF48s_autc_u42gl ()).getD k []).getD 0 0 = 0 →
      burnsideF48s_u42eG k ∈ P1h := fun k hk =>
    (mem_P1h_iff _).2 (burnsideF48s_autc_fix0_of (burnsideF48s_autc_u42_repL k) hk)
  exact ⟨fix 0 (h1 0 (by simp)), fix 1 (h1 1 (by simp)), fix 2 (h1 2 (by simp)),
    fix 4 (h1 4 (by simp)), fun h => burnsideF48s_autc_not_fix0_of (burnsideF48s_autc_u42_repL 3)
      h2 ((mem_P1h_iff _).1 h)⟩

theorem burnsideF48s_autc_u42_P2h :
    burnsideF48s_u42eG 0 ∈ P2h ∧ burnsideF48s_u42eG 1 ∈ P2h ∧ burnsideF48s_u42eG 3 ∈ P2h ∧
      burnsideF48s_u42eG 4 ∈ P2h ∧ burnsideF48s_u42eG 2 ∉ P2h := by
  obtain ⟨-, -, h3, h4⟩ := burnsideF48s_autc_u42_mem_spec
  have line : ∀ k : Fin 5,
      sameSet (imgSet ((burnsideF48s_autc_u42gl ()).getD k []) L0) L0 = true →
      burnsideF48s_u42eG k ∈ P2h := fun k hk =>
    (mem_P2h_iff _).2 (burnsideF48s_autc_line_of (burnsideF48s_autc_u42_repL k) hk)
  exact ⟨line 0 (h3 0 (by simp)), line 1 (h3 1 (by simp)), line 3 (h3 3 (by simp)),
    line 4 (h3 4 (by simp)), fun h => burnsideF48s_autc_not_line_of (burnsideF48s_autc_u42_repL 2)
      h4 ((mem_P2h_iff _).1 h)⟩

theorem burnsideF48s_autc_u42_card_B : Nat.card ↥burnsideF48s_u42eB = 384 := by
  rw [burnsideF48s_u42eB, burnsideF48s_autc_set3 burnsideF48s_u42eG 0 1 4]
  exact burnsideF48s_autc_card_closure burnsideF48s_autc_u42_repL burnsideF48s_autc_u42_repLi
    Certificates.certificate7544.2


theorem burnsideF48s_autc_u42_B_eq : burnsideF48s_u42eB = Bh := by
  obtain ⟨a1, b1, -, f1, -⟩ := burnsideF48s_autc_u42_P1h
  obtain ⟨a2, b2, -, f2, -⟩ := burnsideF48s_autc_u42_P2h
  have hle : burnsideF48s_u42eB ≤ Bh := by
    rw [burnsideF48s_u42eB, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨a1, a2⟩
    · exact ⟨b1, b2⟩
    · exact ⟨f1, f2⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [card_Bh, burnsideF48s_autc_u42_card_B]))

theorem burnsideF48s_autc_u42_B_le :
    burnsideF48s_u42eB ≤ burnsideF48s_u42eP1 ∧ burnsideF48s_u42eB ≤ burnsideF48s_u42eP2 := by
  constructor
  · rw [burnsideF48s_u42eB, burnsideF48s_u42eP1]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)
  · rw [burnsideF48s_u42eB, burnsideF48s_u42eP2]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)

theorem burnsideF48s_autc_u42_P1_eq : burnsideF48s_u42eP1 = P1h := by
  obtain ⟨a1, b1, p1, f1, q1⟩ := burnsideF48s_autc_u42_P1h
  obtain ⟨-, -, -, -, p2⟩ := burnsideF48s_autc_u42_P2h
  have hle : burnsideF48s_u42eP1 ≤ P1h := by
    rw [burnsideF48s_u42eP1, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact a1
    · exact b1
    · exact p1
    · exact f1
  have hB : Bh ≤ burnsideF48s_u42eP1 := burnsideF48s_autc_u42_B_eq ▸ burnsideF48s_autc_u42_B_le.1
  have hp : burnsideF48s_u42eG 2 ∈ burnsideF48s_u42eP1 := Subgroup.subset_closure (by simp)
  rcases lattice_Bh hB with h | h | h | h
  · exact absurd (Bh_le_P2h (h ▸ hp)) p2
  · exact h
  · exact absurd (h ▸ hp) p2
  · exact absurd (hle (by rw [h]; exact Subgroup.mem_top _)) q1

theorem burnsideF48s_autc_u42_P2_eq : burnsideF48s_u42eP2 = P2h := by
  obtain ⟨-, -, -, -, q1⟩ := burnsideF48s_autc_u42_P1h
  obtain ⟨a2, b2, q2, f2, p2⟩ := burnsideF48s_autc_u42_P2h
  have hle : burnsideF48s_u42eP2 ≤ P2h := by
    rw [burnsideF48s_u42eP2, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact a2
    · exact b2
    · exact q2
    · exact f2
  have hB : Bh ≤ burnsideF48s_u42eP2 := burnsideF48s_autc_u42_B_eq ▸ burnsideF48s_autc_u42_B_le.2
  have hq : burnsideF48s_u42eG 3 ∈ burnsideF48s_u42eP2 := Subgroup.subset_closure (by simp)
  rcases lattice_Bh hB with h | h | h | h
  · exact absurd (Bh_le_P1h (h ▸ hq)) q1
  · exact absurd (h ▸ hq) q1
  · exact h
  · exact absurd (hle (by rw [h]; exact Subgroup.mem_top _)) p2

theorem burnsideF48s_autc_u42_inf :
    burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 = burnsideF48s_u42eB := by
  rw [burnsideF48s_autc_u42_P1_eq, burnsideF48s_autc_u42_P2_eq, burnsideF48s_autc_u42_B_eq]

theorem burnsideF48s_autc_u42_normalizer_P1 :
    Subgroup.normalizer ((P1.map incl : Subgroup Ah) : Set Ah) = burnsideF48s_u42eP1 := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_lieModel_PSU_four_two lieModel_Y
  have hmap : P1.map incl = Yh ⊓ P1h := by
    rw [← comap_P1h, Subgroup.map_comap_eq, ← Yh_eq_range]
  rw [burnsideF48s_autc_u42_P1_eq]
  refine burnsideF48s_autc_normalizer_eq
    (burnsideF48s_autc_self_of_lie burnsideF48s_u42_isLieParabolics (Or.inl rfl)) ?_ ?_
    fhatA_mem_P1h fhatA_not_mem_Yh
  · rw [hmap]
    exact inf_le_right
  · rw [hmap]
    exact burnsideF48s_autc_le_normalizer_inf P1h

theorem burnsideF48s_autc_u42_normalizer_P2 :
    Subgroup.normalizer ((P2.map incl : Subgroup Ah) : Set Ah) = burnsideF48s_u42eP2 := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_lieModel_PSU_four_two lieModel_Y
  have hmap : P2.map incl = Yh ⊓ P2h := by
    rw [← comap_P2h, Subgroup.map_comap_eq, ← Yh_eq_range]
  rw [burnsideF48s_autc_u42_P2_eq]
  refine burnsideF48s_autc_normalizer_eq
    (burnsideF48s_autc_self_of_lie burnsideF48s_u42_isLieParabolics (Or.inr rfl)) ?_ ?_
    fhatA_mem_P2h fhatA_not_mem_Yh
  · rw [hmap]
    exact inf_le_right
  · rw [hmap]
    exact burnsideF48s_autc_le_normalizer_inf P2h

end U42

section U42Chart


theorem burnsideF48s_autc_u42_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U4 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    ∃ θ : Ah ≃* E, M₁ ⊓ M₂ = burnsideF48s_u42eB.map θ.toMonoidHom ∧
      ((M₁ = burnsideF48s_u42eP1.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_u42eP2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48s_u42eP2.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_u42eP1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := nonempty_mulEquiv_Y (burnsideF48_lieModel_U4 hyp.model)
  exact burnsideF48s_autc_chart_of burnsideF48s_u42_isLieParabolics
    burnsideF48s_autc_u42_normalizer_P1 burnsideF48s_autc_u42_normalizer_P2
    burnsideF48s_autc_u42_inf (ε₀.trans (MulEquiv.subgroupCongr Xs_eq)) hyp.centralizer_trivial
    hyp.split hP hGp

end U42Chart

section Sp43


theorem burnsideF48s_autc_sp43_repL (k : Fin 5) :
    RepL ((burnsideF48s_autc_sp43gl ()).getD k []) ((burnsideF48s_sp43eG k : Ah) : P45) :=
  burnsideF48s_autc_repL_gl burnsideF48s_sp43eXY k

theorem burnsideF48s_autc_sp43_repLi (k : Fin 5) :
    RepL ((burnsideF48s_autc_sp43gli ()).getD k []) (((burnsideF48s_sp43eG k)⁻¹ : Ah) : P45) := by
  rw [Subgroup.coe_inv]
  exact burnsideF48s_autc_repL_gli burnsideF48s_sp43eXY k

theorem burnsideF48s_autc_sp43_rel_spec :
    (∀ i ∈ List.range 4,
        (burnsideF48s_autc_sp43gl ()).getD i [] = evalW (burnsideF48s_sp43XY.getD i [])) ∧
      compL ((burnsideF48s_autc_sp43gl ()).getD 4 []) ((burnsideF48s_autc_sp43gl ()).getD 4 []) =
        List.range 45 ∧
      ∀ i ∈ List.range 4, compL (compL ((burnsideF48s_autc_sp43gl ()).getD 4 [])
          ((burnsideF48s_autc_sp43gl ()).getD i [])) ((burnsideF48s_autc_sp43gli ()).getD 4 []) =
        burnsideF48s_autc_evL (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ())
          (burnsideF48s_autc_sp43RelW.getD i []) := by
  have h := Certificates.certificate7545.1
  simp only [burnsideF48s_autc_sp43_checkRel, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem burnsideF48s_autc_sp43_coe (i : Fin 4) :
    ((burnsideF48s_sp43eG i.castSucc : Ah) : P45) = ((burnsideF48s_sp43G i : Y) : P45) := by
  refine eq_of_repL (burnsideF48s_autc_sp43_repL i.castSucc) ?_
  have e := burnsideF48s_autc_sp43_rel_spec.1 i (List.mem_range.2 i.2)
  rw [Fin.coe_castSucc, e]
  exact repL_wordP _

theorem burnsideF48s_autc_sp43_G_eq :
    burnsideF48s_sp43eG 0 = incl (burnsideF48s_sp43G 0) ∧
      burnsideF48s_sp43eG 1 = incl (burnsideF48s_sp43G 1) ∧
      burnsideF48s_sp43eG 2 = incl (burnsideF48s_sp43G 2) ∧
      burnsideF48s_sp43eG 3 = incl (burnsideF48s_sp43G 3) :=
  ⟨Subtype.ext ((burnsideF48s_autc_sp43_coe 0).trans (coe_incl _).symm),
    Subtype.ext ((burnsideF48s_autc_sp43_coe 1).trans (coe_incl _).symm),
    Subtype.ext ((burnsideF48s_autc_sp43_coe 2).trans (coe_incl _).symm),
    Subtype.ext ((burnsideF48s_autc_sp43_coe 3).trans (coe_incl _).symm)⟩

theorem burnsideF48s_autc_sp43_f_sq : burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG 4 = 1 := by
  apply Subtype.ext
  have h := repL_mul (burnsideF48s_autc_sp43_repL 4) (burnsideF48s_autc_sp43_repL 4)
  have e : compL ((burnsideF48s_autc_sp43gl ()).getD ((4 : Fin 5) : ℕ) [])
      ((burnsideF48s_autc_sp43gl ()).getD ((4 : Fin 5) : ℕ) []) = List.range 45 :=
    burnsideF48s_autc_sp43_rel_spec.2.1
  rw [e] at h
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  exact eq_of_repL h (repL_one 45)

theorem burnsideF48s_autc_sp43_conj (i : ℕ) (hi : i < 4) :
    burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG ⟨i, by omega⟩ * (burnsideF48s_sp43eG 4)⁻¹ =
      burnsideF48s_autc_ev burnsideF48s_sp43eG (burnsideF48s_autc_sp43RelW.getD i []) := by
  apply Subtype.ext
  refine eq_of_repL ?_ (burnsideF48s_autc_repL_ev _ _ _ burnsideF48s_autc_sp43_repL
    burnsideF48s_autc_sp43_repLi _)
  have e := burnsideF48s_autc_sp43_rel_spec.2.2 i (List.mem_range.2 hi)
  have e' : compL (compL ((burnsideF48s_autc_sp43gl ()).getD ((4 : Fin 5) : ℕ) [])
      ((burnsideF48s_autc_sp43gl ()).getD ((⟨i, by omega⟩ : Fin 5) : ℕ) []))
      ((burnsideF48s_autc_sp43gli ()).getD ((4 : Fin 5) : ℕ) []) =
      burnsideF48s_autc_evL (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ())
        (burnsideF48s_autc_sp43RelW.getD i []) := e
  rw [← e', Subgroup.coe_mul, Subgroup.coe_mul]
  exact repL_mul (repL_mul (burnsideF48s_autc_sp43_repL 4)
    (burnsideF48s_autc_sp43_repL ⟨i, by omega⟩)) (burnsideF48s_autc_sp43_repLi 4)

theorem burnsideF48s_autc_sp43_conj_eq :
    burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG 0 * (burnsideF48s_sp43eG 4)⁻¹ =
        (burnsideF48s_sp43eG 0)⁻¹ ∧
      burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG 1 * (burnsideF48s_sp43eG 4)⁻¹ =
        (burnsideF48s_sp43eG 0)⁻¹ * (burnsideF48s_sp43eG 1)⁻¹ * burnsideF48s_sp43eG 0 ∧
      burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG 2 * (burnsideF48s_sp43eG 4)⁻¹ =
        burnsideF48s_sp43eG 2 ∧
      burnsideF48s_sp43eG 4 * burnsideF48s_sp43eG 3 * (burnsideF48s_sp43eG 4)⁻¹ =
        (burnsideF48s_sp43eG 0)⁻¹ * (burnsideF48s_sp43eG 3)⁻¹ * burnsideF48s_sp43eG 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := burnsideF48s_autc_sp43_conj 0 (by norm_num)
    simpa [burnsideF48s_autc_sp43RelW, burnsideF48s_autc_ev] using this
  · have := burnsideF48s_autc_sp43_conj 1 (by norm_num)
    simpa [burnsideF48s_autc_sp43RelW, burnsideF48s_autc_ev, mul_assoc] using this
  · have := burnsideF48s_autc_sp43_conj 2 (by norm_num)
    simpa [burnsideF48s_autc_sp43RelW, burnsideF48s_autc_ev] using this
  · have := burnsideF48s_autc_sp43_conj 3 (by norm_num)
    simpa [burnsideF48s_autc_sp43RelW, burnsideF48s_autc_ev, mul_assoc] using this

theorem burnsideF48s_autc_sp43_sub_spec :
    burnsideF48s_autc_groupB (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ())
        [0, 1, 4] (burnsideF48s_autc_sp43BW ()) 324 = true ∧
      burnsideF48s_autc_groupB (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ())
        [0, 1, 2, 4] (burnsideF48s_autc_sp43P1W ()) 1296 = true ∧
      burnsideF48s_autc_groupB (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ())
        [0, 1, 3, 4] (burnsideF48s_autc_sp43P2W ()) 1296 = true := by
  have h := Certificates.certificate7545.2.1
  simp only [burnsideF48s_autc_sp43_checkSub, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem burnsideF48s_autc_sp43_card_B : Nat.card ↥burnsideF48s_sp43eB = 324 := by
  rw [burnsideF48s_sp43eB, burnsideF48s_autc_set3 burnsideF48s_sp43eG 0 1 4]
  exact burnsideF48s_autc_card_closure burnsideF48s_autc_sp43_repL burnsideF48s_autc_sp43_repLi
    burnsideF48s_autc_sp43_sub_spec.1

theorem burnsideF48s_autc_sp43_inf :
    burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2 = burnsideF48s_sp43eB := by
  obtain ⟨hB, hP1, hP2⟩ := burnsideF48s_autc_sp43_sub_spec
  have hinf := Certificates.certificate7545.2.2
  simp only [burnsideF48s_autc_sp43_checkInf, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_true_eq, decide_eq_false_iff_not] at hinf
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · rintro z ⟨hz1, hz2⟩
    rw [burnsideF48s_sp43eP1, burnsideF48s_autc_set4 burnsideF48s_sp43eG 0 1 2 4] at hz1
    rw [burnsideF48s_sp43eP2, burnsideF48s_autc_set4 burnsideF48s_sp43eG 0 1 3 4] at hz2
    rw [burnsideF48s_sp43eB, burnsideF48s_autc_set3 burnsideF48s_sp43eG 0 1 4]
    obtain ⟨w, hw, rfl⟩ :=
      (burnsideF48s_autc_mem_closure_iff burnsideF48s_autc_sp43_repL burnsideF48s_autc_sp43_repLi
        hP1 _).1 hz1
    have hr := burnsideF48s_autc_repL_ev _ _ _ burnsideF48s_autc_sp43_repL
      burnsideF48s_autc_sp43_repLi w
    have h2 := burnsideF48s_autc_mem_of_mem_closure burnsideF48s_autc_sp43_repL
      burnsideF48s_autc_sp43_repLi hP2 hr hz2
    rcases hinf _ (List.mem_map_of_mem hw) with h | h
    · exact absurd h2 h
    · exact burnsideF48s_autc_mem_closure_of_mem burnsideF48s_autc_sp43_repL
        burnsideF48s_autc_sp43_repLi hB hr h
  · rw [burnsideF48s_sp43eB, burnsideF48s_sp43eP1]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)
  · rw [burnsideF48s_sp43eB, burnsideF48s_sp43eP2]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)


theorem burnsideF48s_autc_sp43_f_not_mem_Yh : burnsideF48s_sp43eG 4 ∉ Yh :=
  burnsideF48s_autc_not_mem_Yh _ (by decide)

theorem burnsideF48s_autc_sp43_normalizer_P1
    (hYP : ChF.IsLieParabolics 3 (⊤ : Subgroup Y) burnsideF48s_sp43B burnsideF48s_sp43P1
      burnsideF48s_sp43P2) :
    Subgroup.normalizer ((burnsideF48s_sp43P1.map incl : Subgroup Ah) : Set Ah) =
      burnsideF48s_sp43eP1 := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_lieModel_PSU_four_two lieModel_Y
  obtain ⟨ha, hb, hp, -⟩ := burnsideF48s_autc_sp43_G_eq
  obtain ⟨c0, c1, c2, -⟩ := burnsideF48s_autc_sp43_conj_eq
  have hmap : burnsideF48s_sp43P1.map incl =
      Subgroup.closure {burnsideF48s_sp43eG 0, burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 2} := by
    rw [burnsideF48s_sp43P1, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, ← ha, ← hb, ← hp]
  have hf : burnsideF48s_sp43eG 4 ∈ Subgroup.normalizer ((burnsideF48s_sp43P1.map incl :
      Subgroup Ah) : Set Ah) := by
    rw [hmap]
    refine burnsideF48s_autc_mem_normalizer_closure burnsideF48s_autc_sp43_f_sq ?_
    rintro s (rfl | rfl | rfl)
    · rw [c0]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [c1]
      refine Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) (Subgroup.inv_mem _ ?_)) ?_ <;>
        exact Subgroup.subset_closure (by simp)
    · rw [c2]
      exact Subgroup.subset_closure (by simp)
  have hf1 : burnsideF48s_sp43eG 4 ∈ burnsideF48s_sp43eP1 := Subgroup.subset_closure (by simp)
  refine burnsideF48s_autc_normalizer_eq (burnsideF48s_autc_self_of_lie hYP (Or.inl rfl)) ?_ ?_
    hf1 burnsideF48s_autc_sp43_f_not_mem_Yh
  · rw [hmap, burnsideF48s_sp43eP1]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)
  · rw [burnsideF48s_sp43eP1, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact hf

theorem burnsideF48s_autc_sp43_normalizer_P2
    (hYP : ChF.IsLieParabolics 3 (⊤ : Subgroup Y) burnsideF48s_sp43B burnsideF48s_sp43P1
      burnsideF48s_sp43P2) :
    Subgroup.normalizer ((burnsideF48s_sp43P2.map incl : Subgroup Ah) : Set Ah) =
      burnsideF48s_sp43eP2 := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_lieModel_PSU_four_two lieModel_Y
  obtain ⟨ha, hb, -, hq⟩ := burnsideF48s_autc_sp43_G_eq
  obtain ⟨c0, c1, -, c3⟩ := burnsideF48s_autc_sp43_conj_eq
  have hmap : burnsideF48s_sp43P2.map incl =
      Subgroup.closure {burnsideF48s_sp43eG 0, burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 3} := by
    rw [burnsideF48s_sp43P2, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, ← ha, ← hb, ← hq]
  have hf : burnsideF48s_sp43eG 4 ∈ Subgroup.normalizer ((burnsideF48s_sp43P2.map incl :
      Subgroup Ah) : Set Ah) := by
    rw [hmap]
    refine burnsideF48s_autc_mem_normalizer_closure burnsideF48s_autc_sp43_f_sq ?_
    rintro s (rfl | rfl | rfl)
    · rw [c0]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [c1]
      refine Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) (Subgroup.inv_mem _ ?_)) ?_ <;>
        exact Subgroup.subset_closure (by simp)
    · rw [c3]
      refine Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) (Subgroup.inv_mem _ ?_)) ?_ <;>
        exact Subgroup.subset_closure (by simp)
  have hf2 : burnsideF48s_sp43eG 4 ∈ burnsideF48s_sp43eP2 := Subgroup.subset_closure (by simp)
  refine burnsideF48s_autc_normalizer_eq (burnsideF48s_autc_self_of_lie hYP (Or.inr rfl)) ?_ ?_
    hf2 burnsideF48s_autc_sp43_f_not_mem_Yh
  · rw [hmap, burnsideF48s_sp43eP2]
    exact Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp)
  · rw [burnsideF48s_sp43eP2, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact Subgroup.le_normalizer (by rw [hmap]; exact Subgroup.subset_closure (by simp))
    · exact hf

end Sp43

theorem burnsideF48s_autc_sp43_equiv {H : Type} [Group H]
    (h : ChF.IsGenLie H .Sp4 3 1) : Nonempty (H ≃* ↥QP45.originalSubgroup) := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card, pow_one]
  let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  exact ⟨(e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ))).trans
    CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP⟩

section Sp43Chart


theorem burnsideF48s_autc_sp43_chart
    (hYP : ChF.IsLieParabolics 3 (⊤ : Subgroup Y) burnsideF48s_sp43B burnsideF48s_sp43P1
      burnsideF48s_sp43P2)
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .Sp4 3 1 Gp M₁ M₂)
    (hGp : Gp ≠ ⊤) :
    ∃ θ : Ah ≃* E, M₁ ⊓ M₂ = burnsideF48s_sp43eB.map θ.toMonoidHom ∧
      ((M₁ = burnsideF48s_sp43eP1.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_sp43eP2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48s_sp43eP2.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_sp43eP1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨e⟩ := burnsideF48s_autc_sp43_equiv hyp.model
  exact burnsideF48s_autc_chart_of hYP (burnsideF48s_autc_sp43_normalizer_P1 hYP)
    (burnsideF48s_autc_sp43_normalizer_P2 hYP) burnsideF48s_autc_sp43_inf e
    hyp.centralizer_trivial hyp.split hP hGp

end Sp43Chart

end CFSG.ASVolI
