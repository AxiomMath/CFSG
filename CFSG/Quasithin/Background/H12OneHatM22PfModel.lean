
module

public import CFSG.Quasithin.Background.H12OneHatM22PfModelBase

public import Certificates.Certificate7209

public section

namespace CFSG.Quasithin.H.Mathieu.H12Cert

open CFSG.Quasithin.H13.MatNCert

theorem zB_fix :
    ∀ v ∈ List.range 4096, mvN z12 v ≠ v ∨ v = 0 :=
  Certificates.certificate7209.1

theorem eq_zero_of_zU_fix {v : Fin 12 → ZMod 2}
    (hv : ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v = v) :
    v = 0 := by
  rw [← vecN_codeN v, zU_val, decN_mulVec z12_facts.1] at hv
  have hc := codeN_lt v
  have h1 : mvN z12 (codeN v) = codeN v := vecN_inj (mvN_lt validN_z12.2 _) hc hv
  rcases zB_fix (codeN v) (List.mem_range.mpr hc) with h | h
  · exact absurd h1 h
  · rw [← vecN_codeN v, h, vecN_zero]

theorem orbB_spec :
    orbL.head? = some (v0, []) ∧ orbL.length = 693 ∧ (orbL.map Prod.fst).Nodup ∧
      ∀ uw ∈ orbL, mvN (tW uw.2) v0 = uw.1 :=
  Certificates.certificate7209.2.1

theorem v0_mem : (v0, ([] : List ℕ)) ∈ orbL :=
  List.mem_of_mem_head? (by rw [orbB_spec.1]; rfl)

theorem orbL_lt {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    uw.1 < 2 ^ 12 := by
  rw [← orbB_spec.2.2.2 uw huw]
  exact mvN_lt (validN_evalW gG validN_gG _).2 _

theorem orbL_ext {uw uw' : ℕ × List ℕ} (huw : uw ∈ orbL)
    (huw' : uw' ∈ orbL) (h : uw.1 = uw'.1) : uw = uw' :=
  List.inj_on_of_nodup_map orbB_spec.2.2.1 huw huw' h

theorem schB_spec :
    ∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s ∈ S0, mulN (tW uw'.2) (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) =
        mulN g (tW uw.2) :=
  Certificates.certificate7209.2.2.1

theorem card_S0 : Nat.card S0 = 1920 :=
  Certificates.certificate7209.2.2.2.1.1

theorem S0_fix {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    (s : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0 := by
  rw [mulVec_vecN, Certificates.certificate7209.2.2.2.1.2 s hs]

theorem tU_mulVec {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    ((tU uw.2 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [tU_val, decN_mulVec (length_evalW gG _), orbB_spec.2.2.2 uw huw]

theorem decomp {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ G) :
    ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s := by
  refine G_induction (p := fun x => ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s)
    ⟨_, v0_mem, 1, one_mem _, by simp [tU]⟩ ?_ hx
  rintro i hi y ⟨uw, huw, s, hs, rfl⟩
  obtain ⟨uw', huw', -, σU, hσU, hσeq⟩ := schB_spec uw huw _ (getD_mem_gG hi)
  refine ⟨uw', huw', σU * s, S0.mul_mem hσU hs, ?_⟩
  have key : gU i * tU uw.2 = tU uw'.2 * σU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, gU_val, tU_val, tU_val,
      ← decN_colsN (σU : Matrix (Fin 12) (Fin 12) (ZMod 2)),
      ← decN_mulN (validN_getD validN_gG i).1 (length_evalW gG _),
      ← decN_mulN (length_evalW gG _) (validN_colsN _).1, hσeq]
  rw [← mul_assoc, key, mul_assoc]

theorem mulVec_decomp {uw : ℕ × List ℕ} (huw : uw ∈ orbL)
    {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    ((tU uw.2 * s : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, S0_fix hs, tU_mulVec huw]

theorem card_G : Nat.card G = 1330560 := by
  let f : {uw // uw ∈ orbL} × S0 → G := fun p =>
    ⟨tU p.1.1.2 * p.2, G.mul_mem (tU_mem _) (S0_le p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h1 : tU p.1.1.2 * p.2 = tU q.1.1.2 * q.2 := congrArg Subtype.val h
      have h2 := mulVec_decomp p.1.2 p.2.2
      rw [h1, mulVec_decomp q.1.2 q.2.2] at h2
      have hpq : p.1 = q.1 := Subtype.ext (orbL_ext p.1.2 q.1.2
        (vecN_inj (orbL_lt p.1.2) (orbL_lt q.1.2) h2.symm))
      rw [hpq] at h1
      exact Prod.ext hpq (Subtype.ext (mul_left_cancel h1))
    · obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
      exact ⟨(⟨uw, huw⟩, ⟨s, hs⟩), rfl⟩
  have hnd : orbL.Nodup := List.Nodup.of_map _ orbB_spec.2.2.1
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, card_S0,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := orbL) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, orbB_spec.2.1]

theorem tG_S0 :
    ∀ g ∈ tG, ∃ s ∈ S0, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = g :=
  Certificates.certificate7209.2.2.2.2.1.2.1

theorem tG_validN : ∀ g ∈ tG, ValidN 12 g := fun g hg =>
  let ⟨_, _, hs⟩ := tG_S0 g hg; hs ▸ validN_colsN _

theorem tG_unit : ∀ g ∈ tG, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := tG_S0 g hg; ⟨u, by rw [← hu, decN_colsN]⟩

theorem card_T0 : Nat.card T0 = 128 :=
  Certificates.certificate7209.2.2.2.2.1.1

theorem T0_le_S0 : T0 ≤ S0 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨s, hs, hs'⟩ := tG_S0 _ hu
  have : u = s := eq_of_colsN_eq hs'.symm
  exact this ▸ hs

theorem T0_le_G : T0 ≤ G := T0_le_S0.trans S0_le

theorem fix_T0_iff (v : Fin 12 → ZMod 2) :
    (∀ t ∈ T0, ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v = v) ↔
      v ∈ F0v := by
  constructor
  · intro hv
    have hc := codeN_lt v
    rcases Certificates.certificate7209.2.2.2.2.1.2.2 (codeN v) (List.mem_range.mpr hc)
      with h | h
    · exfalso
      have hall : (tG.all fun g => mvN g (codeN v) == codeN v) = true := by
        rw [List.all_eq_true]
        intro g hg
        obtain ⟨u, hu'⟩ := tG_unit g hg
        have hvg := tG_validN g hg
        have h1 := hv u (mem_genSubN_of_mem tG_validN hg hu')
        rw [← vecN_codeN v, hu', decN_mulVec hvg.1] at h1
        rw [beq_iff_eq]
        exact vecN_inj (mvN_lt hvg.2 _) hc h1
      rw [hall] at h
      exact absurd h (by decide)
    · exact ⟨_, h, (vecN_codeN v).symm⟩
  · intro hv t ht
    have htG : t ∈ G := T0_le_G ht
    have hfix : ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 = w0 :=
      S0_fix (T0_le_S0 ht)
    have hcomm : ∀ x : Fin 12 → ZMod 2,
        ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec x) =
        ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec x) := by
      intro x
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        zU_comm htG]
    rcases (mem_F0v_iff v).mp hv with rfl | rfl | rfl | rfl
    · exact Matrix.mulVec_zero _
    · exact hfix
    · rw [hcomm, hfix]
    · rw [hcomm, hcomm, hfix]

theorem T0_le_lineStab : T0 ≤ lineStab := fun t ht =>
  ⟨zU_comm (T0_le_G ht), by rw [S0_fix (T0_le_S0 ht)]; exact w0_mem_F0v⟩

theorem le_card_T0_sup :
    384 ≤ Nat.card ↥(T0 ⊔ Subgroup.zpowers zU) := by
  have h1 : 128 ∣ Nat.card ↥(T0 ⊔ Subgroup.zpowers zU) :=
    card_T0 ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : 3 ∣ Nat.card ↥(T0 ⊔ Subgroup.zpowers zU) := by
    rw [← orderOf_zU, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_right
  exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2)

theorem ovB_spec :
    (∀ uw ∈ orbL, uw.1 ∈ f0 ∨ uw.1 ∈ UC ∨
      ∃ t₁ ∈ T0, ∃ t₂ ∈ T0,
        lineNe uw.1 (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe uw.1 (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1)
          (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true) ∧
    (∀ r ∈ rP, (∃ s ∈ S0, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1) ∧
      mulN r.1 r.2 = one12) ∧
    (∀ s ∈ S0, ∃ r ∈ rP, ∃ t ∈ T0,
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN r.2 (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ∧
    (∀ u ∈ UC, ∃ w : List ℕ, mvN (tW w) v0 = u ∧ ∀ r ∈ rP,
      (∃ w' : List ℕ, evalW 12 rG w' = mulN (tW w) r.1) ∨
      ∃ c₁ c₂ c₃ : ℕ, (∀ c ∈ [c₁, c₂, c₃], c ≠ 0 ∧ lineNe v0 c = true ∧
          ∃ w' : List ℕ, mvN (evalW 12 (tG ++ [z12, mulN (tW w) r.1]) w') v0 = c) ∧
        lineNe c₁ c₂ = true ∧ lineNe c₁ c₃ = true ∧ lineNe c₂ c₃ = true) ∧
    Nat.card (genSubN 12 rG) = 1152 ∧ mvN y0 v0 ∉ f0 :=
  Certificates.certificate7209.2.2.2.2.2

theorem rG_unit : ∀ g ∈ rG, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tG_unit g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨zU, zU_val⟩
    · exact ⟨y0U, tU_val y0W⟩

theorem card_R0 : Nat.card R0 = 1152 :=
  ovB_spec.2.2.2.2.1

theorem validN_rG : ∀ g ∈ rG, ValidN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tG_validN g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact validN_z12
    · exact validN_evalW gG validN_gG y0W

theorem zU_mem_R0 : zU ∈ R0 :=
  mem_genSubN_of_mem validN_rG (by simp [rG]) zU_val

theorem y0U_mem_R0 : y0U ∈ R0 :=
  mem_genSubN_of_mem validN_rG (by simp [rG, y0]) (tU_val y0W)

theorem R0_le_G : R0 ≤ G := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  have hu' : colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ rG := hu
  rcases List.mem_append.mp hu' with h | h
  · obtain ⟨v, hv⟩ := tG_unit _ h
    have huv : u = v := eq_of_colsN_eq (by rw [hv, colsN_decN (tG_validN _ h)])
    exact huv ▸ T0_le_G (mem_genSubN_of_mem tG_validN h hv)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · have : u = zU := eq_of_colsN_eq (by rw [h, zU_val, colsN_decN validN_z12])
      exact this ▸ zU_mem
    · have : u = y0U := eq_of_colsN_eq (by
        rw [h, y0U, tU_val, colsN_decN (validN_evalW gG validN_gG y0W)]; rfl)
      exact this ▸ tU_mem y0W

theorem y0U_not_mem :
    ((y0U : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∉ F0v := by
  rintro ⟨c, hc, hcv⟩
  rw [y0U, tU_val, decN_mulVec (length_evalW gG _)] at hcv
  have := vecN_inj (mvN_lt (validN_evalW gG validN_gG y0W).2 _) (f0_lt c hc) hcv
  exact ovB_spec.2.2.2.2.2 (this ▸ hc)

theorem index_le_three {R : Subgroup (GL (Fin 12) (ZMod 2))}
    (hT : T0 ≤ R) (hz : zU ∈ R) (hcard : Nat.card R = 1152) :
    ((R ⊓ lineStab).subgroupOf R).index ≤ 3 := by
  have hK : T0 ⊔ Subgroup.zpowers zU ≤ R ⊓ lineStab :=
    le_inf (sup_le hT ((Subgroup.zpowers_le).mpr hz))
      (sup_le T0_le_lineStab ((Subgroup.zpowers_le).mpr zU_mem_lineStab))
  have hc : 384 ≤ Nat.card ↥(R ⊓ lineStab) :=
    le_card_T0_sup.trans (Subgroup.card_le_of_le hK)
  have h := Subgroup.relIndex_mul_card (R ⊓ lineStab) R
  have hinf : R ⊓ lineStab ⊓ R = R ⊓ lineStab := by
    rw [inf_comm (R ⊓ lineStab) R, ← inf_assoc, inf_idem]
  rw [hinf, hcard] at h
  unfold Subgroup.relIndex at h
  by_contra hlt
  have : 4 * 384 ≤ ((R ⊓ lineStab).subgroupOf R).index * Nat.card ↥(R ⊓ lineStab) :=
    Nat.mul_le_mul (by omega) hc
  omega

theorem card_eq_of_le {H R : Subgroup (GL (Fin 12) (ZMod 2))}
    (hHR : H ≤ R) (hcard : Nat.card R = 1152) (hT : T0 ≤ H) (hz : zU ∈ H) :
    Nat.card H = 384 ∨ Nat.card H = 1152 := by
  have h1 : 128 ∣ Nat.card H := card_T0 ▸ Subgroup.card_dvd_of_le hT
  have h2 : 3 ∣ Nat.card H := by
    rw [← orderOf_zU, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hz)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  have hdvd : Nat.card H ∣ 1152 := hcard ▸ Subgroup.card_dvd_of_le hHR
  rw [hk, show (1152 : ℕ) = 384 * 3 by norm_num] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
    with rfl | rfl
  · exact Or.inl (by rw [hk])
  · exact Or.inr (by rw [hk])

theorem mem_S0_of_fix {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ G)
    (hxv : ((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 = w0) :
    x ∈ S0 := by
  obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
  have h := mulVec_decomp huw hs
  rw [hxv] at h
  have h1 : uw.1 = v0 := vecN_inj (orbL_lt huw) (by decide) h.symm
  rw [orbL_ext huw v0_mem h1]
  simpa [tU] using hs

theorem eq_R0_of {R : Subgroup (GL (Fin 12) (ZMod 2))}
    (hRG : R ≤ G) (hT : T0 ≤ R) (hz : zU ∈ R) (hcard : Nat.card R = 1152)
    {y : GL (Fin 12) (ZMod 2)} (hyR : y ∈ R)
    (hy : ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∉ F0v) :
    R = R0 := by
  have hidx := index_le_three hT hz hcard
  obtain ⟨uw, huw, s, hs, rfl⟩ := decomp (hRG hyR)
  have hyv := mulVec_decomp huw hs
  have hu12 := orbL_lt huw
  have hu0 : uw.1 ∉ f0 := fun h => hy (by rw [hyv]; exact ⟨_, h, rfl⟩)
  have hv12 : v0 < 2 ^ 12 := by decide
  have hf0 : f0 = [0, 5, 10, 15] := z12_facts.2.2.2.2.2
  have hne0 : ∀ b, b ∉ f0 → b ≠ 0 := fun b hb h => hb (by rw [h, hf0]; simp)
  have hlv0 : ∀ b, b ∉ f0 → lineNe v0 b = true := by
    intro b hb
    rw [hf0] at hb
    have h10 : mvN z12 v0 = 10 := by decide +kernel
    have h15 : mvN z12 10 = 15 := by decide +kernel
    simp only [lineNe, h10, h15, Bool.and_eq_true, bne_iff_ne, ne_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    exact ⟨⟨fun h => hb.2.1 (h.trans rfl), hb.2.2.1⟩, hb.2.2.2⟩
  have hUC : uw.1 ∈ UC := by
    rcases ovB_spec.1 uw huw with h | h | ⟨q₁, hq₁, q₂, hq₂, h1, h2, h12⟩
    · exact absurd h hu0
    · exact h
    · exfalso
      set t₁ := colsN (q₁ : Matrix (Fin 12) (Fin 12) (ZMod 2)) with ht₁def
      set t₂ := colsN (q₂ : Matrix (Fin 12) (Fin 12) (ZMod 2)) with ht₂def
      have hq₁' : (q₁ : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 t₁ := (decN_colsN _).symm
      have hq₂' : (q₂ : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 t₂ := (decN_colsN _).symm
      have hv₁ : ValidN 12 t₁ := validN_colsN _
      have hv₂ : ValidN 12 t₂ := validN_colsN _
      have hqv : ∀ {q : GL (Fin 12) (ZMod 2)} {t : List ℕ}, ValidN 12 t →
          (q : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 t →
          ((q * (tU uw.2 * s) : GL (Fin 12) (ZMod 2)) :
            Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 = vecN 12 (mvN t uw.1) := by
        intro q t ht hq
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, hq, decN_mulVec ht.1]
      have hnf : ∀ {q : GL (Fin 12) (ZMod 2)} {t : List ℕ}, q ∈ T0 → ValidN 12 t →
          (q : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 t → mvN t uw.1 ∉ f0 := by
        intro q t hqT ht hq hf
        apply hy
        have hq' : (q⁻¹ : GL (Fin 12) (ZMod 2)) ∈ lineStab := T0_le_lineStab (T0.inv_mem hqT)
        have h3 : ((q⁻¹ * (q * (tU uw.2 * s)) : GL (Fin 12) (ZMod 2)) :
            Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∈ F0v := by
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hqv ht hq]
          exact mapsTo_F0v hq'.1 hq'.2 ⟨_, hf, rfl⟩
        simpa using h3
      have hn₁ := hnf hq₁ hv₁ hq₁'
      have hn₂ := hnf hq₂ hv₂ hq₂'
      let m : Fin 4 → ↥R := ![1, ⟨_, hyR⟩, ⟨q₁ * _, R.mul_mem (hT hq₁) hyR⟩,
        ⟨q₂ * _, R.mul_mem (hT hq₂) hyR⟩]
      let c : Fin 4 → ℕ := ![v0, uw.1, mvN t₁ uw.1, mvN t₂ uw.1]
      have hc : ∀ i, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          w0 = vecN 12 (c i) := by
        intro i
        fin_cases i
        · simp [m, c]
        · exact hyv
        · exact hqv hv₁ hq₁'
        · exact hqv hv₂ hq₂'
      have hc12 : ∀ i, c i < 2 ^ 12 := by
        intro i
        fin_cases i
        · exact hv12
        · exact hu12
        · exact mvN_lt hv₁.2 _
        · exact mvN_lt hv₂.2 _
      have hc0 : ∀ i, c i ≠ 0 := by
        intro i
        fin_cases i
        · simp [c, v0]
        · exact hne0 _ hu0
        · exact hne0 _ hn₁
        · exact hne0 _ hn₂
      have hne : ∀ i j, i < j → lineNe (c i) (c j) = true := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij
        · exact hlv0 _ hu0
        · exact hlv0 _ hn₁
        · exact hlv0 _ hn₂
        · exact h1
        · exact h2
        · exact h12
      have hlt : ∀ i j, i < j →
          ((m i : GL (Fin 12) (ZMod 2))⁻¹ * m j) ∉ lineStab := fun i j hij =>
        inv_mul_not_mem_of_lineNe (hRG (m i).2) (hc12 i) (hc12 j) (hc0 j) (hc i) (hc j)
          (hne i j hij)
      have hdist : ∀ i j, ((m i : GL (Fin 12) (ZMod 2))⁻¹ * m j) ∈ lineStab → i = j := by
        intro i j hij
        by_contra hne'
        rcases lt_or_gt_of_ne hne' with h | h
        · exact hlt i j h hij
        · apply hlt j i h
          have := lineStab.inv_mem hij
          rwa [mul_inv_rev, inv_inv] at this
      have := four_le_index m hdist
      omega
  obtain ⟨w, hw, hwr⟩ := ovB_spec.2.2.2.1 uw.1 hUC
  have hwv : ((tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      vecN 12 uw.1 := by
    rw [tU_val, decN_mulVec (length_evalW gG _), hw]
  have hxS : (tU w)⁻¹ * (tU uw.2 * s) ∈ S0 := by
    refine mem_S0_of_fix (G.mul_mem (G.inv_mem (tU_mem w)) (hRG hyR)) ?_
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, ← hwv, Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨r, hr, tq, htq, hrT⟩ := ovB_spec.2.2.1 _ hxS
  obtain ⟨⟨rU, hrU, hrU''⟩, hrr⟩ := ovB_spec.2.1 r hr
  obtain ⟨hvr1, hvr2⟩ := validN_rP r hr
  have hrU' : (rU : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 r.1 := by
    rw [← hrU'', decN_colsN]
  have hrinv : ((rU⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 r.2 := by
    have h1 : (rU : Matrix (Fin 12) (Fin 12) (ZMod 2)) * decN 12 r.2 = 1 := by
      rw [hrU', ← decN_mulN hvr1.1 hvr2.1, hrr, decN_oneN]
    calc ((rU⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
        = ((rU⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
            ((rU : Matrix (Fin 12) (Fin 12) (ZMod 2)) * decN 12 r.2) := by
          rw [h1, Matrix.mul_one]
      _ = decN 12 r.2 := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hrs : rU⁻¹ * ((tU w)⁻¹ * (tU uw.2 * s)) ∈ T0 := by
    have : rU⁻¹ * ((tU w)⁻¹ * (tU uw.2 * s)) = tq := eq_of_colsN_eq (by
      rw [hrT, Units.val_mul, colsN_mul, hrinv, colsN_decN hvr2])
    rw [this]
    exact htq
  set y' := tU w * rU with hy'def
  have hy'R : y' ∈ R := by
    have : y' = (tU uw.2 * s) * (rU⁻¹ * ((tU w)⁻¹ * (tU uw.2 * s)))⁻¹ := by rw [hy'def]; group
    rw [this]
    exact R.mul_mem hyR (R.inv_mem (hT hrs))
  have hy'v : ((y' : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      vecN 12 uw.1 := by
    rw [hy'def, Units.val_mul, ← Matrix.mulVec_mulVec, S0_fix hrU, hwv]
  have hy'cols : colsN (y' : Matrix (Fin 12) (Fin 12) (ZMod 2)) = mulN (tW w) r.1 := by
    rw [hy'def, Units.val_mul, colsN_mul, tU_val, hrU', colsN_decN (validN_evalW gG validN_gG _),
      colsN_decN hvr1]
  have hy'ls : y' ∉ lineStab := fun h => hu0 (by
    obtain ⟨c, hc, hcv⟩ := h.2
    rw [hy'v] at hcv
    rwa [vecN_inj hu12 (f0_lt c hc) hcv])
  rcases hwr r hr with ⟨w', hw'⟩ | ⟨c₁, c₂, c₃, hcs, h12, h13, h23⟩
  · have hy'R0 : y' ∈ R0 := by
      obtain ⟨u, hu, hu'⟩ := exists_evalW rG validN_rG rG_unit w'
      have : u = y' := eq_of_colsN_eq (by rw [hu', colsN_decN (validN_evalW rG validN_rG w'), hw',
        hy'cols])
      exact this ▸ hu
    have hTH : T0 ≤ R ⊓ R0 := le_inf hT T0_le_R0
    rcases card_eq_of_le inf_le_left hcard hTH ⟨hz, zU_mem_R0⟩ with h384 | h1152
    · exfalso
      have hle : T0 ⊔ Subgroup.zpowers zU ≤ R ⊓ R0 :=
        sup_le hTH ((Subgroup.zpowers_le).mpr ⟨hz, zU_mem_R0⟩)
      have heq : T0 ⊔ Subgroup.zpowers zU = R ⊓ R0 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h384]; exact le_card_T0_sup)
      have hy'mem : y' ∈ T0 ⊔ Subgroup.zpowers zU := heq ▸ ⟨hy'R, hy'R0⟩
      exact hy'ls (sup_le T0_le_lineStab ((Subgroup.zpowers_le).mpr zU_mem_lineStab) hy'mem)
    · have h1 : R ⊓ R0 = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, h1152])
      have h2 : R ⊓ R0 = R0 := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [card_R0, h1152])
      exact h1.symm.trans h2
  · exfalso
    set gens := tG ++ [z12, mulN (tW w) r.1] with hgens
    have hvalid : ∀ g ∈ gens, ValidN 12 g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact tG_validN g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact validN_z12
        · exact validN_mulN (validN_evalW gG validN_gG _) hvr1
    have hunit : ∀ g ∈ gens, ∃ u : GL (Fin 12) (ZMod 2),
        (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact tG_unit g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact ⟨zU, zU_val⟩
        · exact ⟨y', by rw [← hy'cols, decN_colsN]⟩
    have hle : genSubN 12 gens ≤ R := by
      refine (Subgroup.closure_le _).mpr fun u hu => ?_
      have hu' : colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ gens := hu
      rcases List.mem_append.mp hu' with h | h
      · obtain ⟨v, hv⟩ := tG_unit _ h
        have huv : u = v :=
          eq_of_colsN_eq (by rw [hv, colsN_decN (tG_validN _ h)])
        exact huv ▸ hT (mem_genSubN_of_mem tG_validN h hv)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · have : u = zU := eq_of_colsN_eq (by rw [h, zU_val, colsN_decN validN_z12])
          exact this ▸ hz
        · have : u = y' := eq_of_colsN_eq (by rw [h, hy'cols])
          exact this ▸ hy'R
    have hm : ∀ c ∈ [c₁, c₂, c₃], ∃ m : ↥R,
        ((m : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 = vecN 12 c ∧
          c < 2 ^ 12 ∧ c ≠ 0 ∧ lineNe v0 c = true := by
      intro c hc
      obtain ⟨hc0, hcv, w'', hw''⟩ := hcs c hc
      obtain ⟨u, hu, hu'⟩ := exists_evalW gens hvalid hunit w''
      refine ⟨⟨u, hle hu⟩, ?_, ?_, hc0, hcv⟩
      · rw [hu', decN_mulVec (length_evalW gens _), hw'']
      · rw [← hw'']
        exact mvN_lt (validN_evalW gens hvalid _).2 _
    obtain ⟨m₁, hm₁, hb₁, h0₁, hl₁⟩ := hm c₁ (by simp)
    obtain ⟨m₂, hm₂, hb₂, h0₂, hl₂⟩ := hm c₂ (by simp)
    obtain ⟨m₃, hm₃, hb₃, h0₃, hl₃⟩ := hm c₃ (by simp)
    refine not_four_lines hRG hidx ![1, m₁, m₂, m₃] ![v0, c₁, c₂, c₃] (fun i => ?_) (fun i => ?_)
      (fun i => ?_) (fun i j hij => ?_)
    · fin_cases i
      · simp
      · exact hm₁
      · exact hm₂
      · exact hm₃
    · fin_cases i
      · exact hv12
      · exact hb₁
      · exact hb₂
      · exact hb₃
    · fin_cases i
      · simp [v0]
      · exact h0₁
      · exact h0₂
      · exact h0₃
    · fin_cases i <;> fin_cases j <;> simp at hij
      · exact hl₁
      · exact hl₂
      · exact hl₃
      · exact h12
      · exact h13
      · exact h23

end CFSG.Quasithin.H.Mathieu.H12Cert
