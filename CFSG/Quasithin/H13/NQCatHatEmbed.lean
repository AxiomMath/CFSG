module

public import Certificates.Certificate7121
public import CFSG.Quasithin.Vol2.Ch3Sec3HatNorm
public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixGenerators
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine

public section

namespace CFSG.Quasithin.H13.HatE

open Subgroup CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

theorem mact_zero (m : List ℕ) : mact m 0 = 0 := by
  simp [mact, mactN]

theorem injC_mcode (x : MulAut W6) : injC (mcode ⇑x) = true := by
  rw [injC, List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  rw [bne_iff_ne, ne_eq]
  intro h
  have h1 := HatN.mact_inj x (by omega) (by norm_num) (h.trans (mact_zero _).symm)
  omega

theorem mcode_pow (x : MulAut W6) (n : ℕ) : mcode ⇑(x ^ n) = powC (mcode ⇑x) n := by
  induction n with
  | zero => rw [pow_zero, mcode_one]; rfl
  | succ n ih => rw [pow_succ', mcode_mul, ih]; rfl

theorem mcode_eq_hc {x : MulAut W6} (hx : x * hom = hom * x) :
    mcode ⇑x = hc (mact (mcode ⇑x) 1) (mact (mcode ⇑x) 4) (mact (mcode ⇑x) 16) := by
  have key : ∀ c < 64, mact (mcode ⇑x) (mact omc c) = mact omc (mact (mcode ⇑x) c) := by
    intro c hc
    rw [← mcode_hom, ← HatN.mact_mul _ _ hc, ← HatN.mact_mul _ _ hc, hx]
  have e2 : mact (mcode ⇑x) 2 = mact omc (mact (mcode ⇑x) 1) := by
    rw [← key 1 (by norm_num), show mact omc 1 = 2 by decide +kernel]
  have e8 : mact (mcode ⇑x) 8 = mact omc (mact (mcode ⇑x) 4) := by
    rw [← key 4 (by norm_num), show mact omc 4 = 8 by decide +kernel]
  have e32 : mact (mcode ⇑x) 32 = mact omc (mact (mcode ⇑x) 16) := by
    rw [← key 16 (by norm_num), show mact omc 16 = 32 by decide +kernel]
  refine (HatN.mcode_eq x).trans ?_
  rw [e2, e8, e32]
  rfl

theorem invPair_symm {m m' : List ℕ} (h : InvPair m m') : InvPair m' m :=
  ⟨fun c hc => (h.1 c hc).symm, h.2.2, h.2.1⟩

@[expose] def pAut {m m' : List ℕ} (h : InvPair m m') : MulAut W6 :=
  caut m m' h.1 h.2.1 h.2.2

theorem pAut_inv {m m' : List ℕ} (h : InvPair m m') : (pAut h)⁻¹ = pAut (invPair_symm h) :=
  MulEquiv.ext fun _ => rfl

theorem mcode_pAut {m m' : List ℕ} (h : InvPair m m') (hl : m.length = 6) :
    mcode ⇑(pAut h) = m :=
  mcode_caut _ _ _ _ _ hl

theorem of_pairB {m m' : List ℕ} (h : pairB m m' = true) :
    InvPair m m' ∧ m.length = 6 ∧ m'.length = 6 := by
  unfold pairB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨of_decide_eq_true h.1.1, h.1.2, h.2⟩

theorem hom_pow_three : hom ^ 3 = 1 :=
  mcode_injective (by rw [mcode_pow, mcode_hom, mcode_one]; decide +kernel)

theorem inZ_of_mem {y : MulAut W6} (hy : y ∈ zpowers hom) : inZ (mcode ⇑y) = true := by
  have hfin : IsOfFinOrder hom := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hom_pow_three⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hy)
  rw [pow_eq_pow_mod n hom_pow_three]
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 3)
  · rw [pow_zero, mcode_one]; decide +kernel
  · rw [pow_one, mcode_hom]; decide +kernel
  · rw [pow_two, mcode_mul, mcode_hom]; decide +kernel

theorem invHyp_mcode {x : MulAut W6} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) :
    invHyp (mcode ⇑x) = true := by
  simp only [invHyp, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨injC_mcode x, by rw [← mcode_mul, ← pow_two, h2, mcode_one]⟩, code_ne_idc h1⟩

@[expose] def hA0 : MulAut W6 := welt [0, 1, 1, 1, 0, 0, 1, 0]

theorem mcode_hA0 : mcode ⇑hA0 = a0c := by
  change mcode ⇑(welt [0, 1, 1, 1, 0, 0, 1, 0]) = a0c
  rw [mcode_welt]
  decide +kernel

theorem genHyp_mcode {x : MulAut W6} (h4 : x ^ 4 = 1) (h5 : (hA0 * x) ^ 5 ∈ zpowers hom)
    (h5' : (hA0 * (x * x)) ^ 5 ∈ zpowers hom) : genHyp (mcode ⇑x) = true := by
  simp only [genHyp, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨injC_mcode x, ?_⟩, ?_⟩, ?_⟩
  · rw [← mcode_pow, h4, mcode_one]
  · rw [← mcode_hA0, ← mcode_mul, ← mcode_pow]
    exact inZ_of_mem h5
  · rw [← mcode_hA0, ← mcode_mul, ← mcode_mul, ← mcode_pow]
    exact inZ_of_mem h5'

theorem g0List_spec :
    idc ∈ g0List ∧ g0List.length = 1080 ∧ ∀ m ∈ g0List, mmul g1c m ∈ g0List ∧
      mmul g2c m ∈ g0List ∧ mmul g1i m ∈ g0List ∧ mmul g2i m ∈ g0List := by
  have h := Certificates.certificate7121.1
  simp only [g0OK, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun m hm => ⟨(h.2 m hm).1.1.1, (h.2 m hm).1.1.2, (h.2 m hm).1.2,
    (h.2 m hm).2⟩⟩

theorem conjTab_spec {e : List ℕ × List ℕ × List ℕ}
    (he : e ∈ conjTab) :
    pairB e.1 e.2.1 = true ∧ wval e.2.2 = mmul e.2.1 (mmul a0c e.1) ∧ ∀ i ∈ e.2.2, i < 2 := by
  have h := Certificates.certificate7121.2.1
  simp only [conjOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h e he
  exact ⟨h1, h2, h3⟩

theorem invTab_spec {c0 c2 c4 : ℕ} (h0 : c0 < 64) (h2 : c2 < 64)
    (h4 : c4 < 64) (h : invHyp (hc c0 c2 c4) = true) :
    ∃ e ∈ invTab, pairB e.2.1 e.2.2 = true ∧ mmul e.2.1 omc = mmul omc e.2.1 ∧
      mmul e.2.1 (mmul a0c e.2.2) = hc c0 c2 c4 := by
  have hall := Certificates.certificate7121.2.2.1
  simp only [allCodes, List.all_eq_true, List.mem_range] at hall
  have h1 := hall c0 h0 c2 h2 c4 h4
  rw [h, Bool.not_true, Bool.false_or, invOK, List.any_eq_true] at h1
  obtain ⟨e, he, h3⟩ := h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨e, he, h3.1.1.2, h3.1.2, h3.2⟩

theorem genTab_spec {c0 c2 c4 : ℕ} (h0 : c0 < 64) (h2 : c2 < 64)
    (h4 : c4 < 64) (h : genHyp (hc c0 c2 c4) = true) :
    ∃ w : List ℕ, ∃ c ∈ conjTab, wval w = mmul c.2.1 (mmul (hc c0 c2 c4) c.1) ∧
      ∀ i ∈ w, i < 2 := by
  have hall := Certificates.certificate7121.2.2.2
  simp only [allCodes, List.all_eq_true, List.mem_range] at hall
  have h1 := hall c0 h0 c2 h2 c4 h4
  rw [h, Bool.not_true, Bool.false_or, genOK, List.any_eq_true] at h1
  obtain ⟨e, -, h3⟩ := h1
  rw [Bool.and_eq_true] at h3
  obtain ⟨-, h5⟩ := h3
  revert h5
  cases hj : conjTab[e.2.1]? with
  | none => intro h5; simp at h5
  | some c =>
    intro h5
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h5
    exact ⟨e.2.2, c, List.mem_of_getElem? hj, h5.1, h5.2⟩

theorem exists_conj_mem_Gam0 {A B : MulAut W6}
    (hA : A * hom = hom * A) (hB : B * hom = hom * B) (hA2 : A ^ 2 = 1) (hA1 : A ≠ 1)
    (hB4 : B ^ 4 = 1) (hAB : (A * B) ^ 5 ∈ zpowers hom)
    (hAB2 : (A * B ^ 2) ^ 5 ∈ zpowers hom) :
    ∃ g : MulAut W6, g * A * g⁻¹ ∈ Gam0 ∧ g * B * g⁻¹ ∈ Gam0 := by
  obtain ⟨e, -, hpair, hcomm, hconj⟩ := invTab_spec (HatN.mact_lt' A 1) (HatN.mact_lt' A 4)
    (HatN.mact_lt' A 16) (by rw [← mcode_eq_hc hA]; exact invHyp_mcode hA2 hA1)
  rw [← mcode_eq_hc hA] at hconj
  obtain ⟨hP, hl1, hl2⟩ := of_pairB hpair
  obtain ⟨C, hCdef⟩ : ∃ C, C = pAut hP := ⟨_, rfl⟩
  have hC : mcode ⇑C = e.2.1 := by rw [hCdef]; exact mcode_pAut hP hl1
  have hCi : mcode ⇑C⁻¹ = e.2.2 := by rw [hCdef, pAut_inv]; exact mcode_pAut _ hl2
  have hCom : C * hom = hom * C :=
    mcode_injective (by rw [mcode_mul, mcode_mul, hC, mcode_hom, hcomm])
  have hCA : C * (hA0 * C⁻¹) = A :=
    mcode_injective (by rw [mcode_mul, mcode_mul, hC, hCi, mcode_hA0, hconj])
  set φ : MulAut W6 ≃* MulAut W6 := MulAut.conj C⁻¹ with hφdef
  have hφ : ∀ y, φ y = C⁻¹ * y * C := fun y => by rw [hφdef, MulAut.conj_apply, inv_inv]
  have hφω : φ hom = hom := by
    rw [hφ, mul_assoc, ← hCom, inv_mul_cancel_left]
  have hφZ : ∀ y ∈ zpowers hom, φ y ∈ zpowers hom := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [map_zpow, hφω]
    exact zpow_mem (mem_zpowers _) k
  have hφA : φ A = hA0 := by
    rw [hφ, ← hCA]
    group
  obtain ⟨B1, hB1def⟩ : ∃ B1, B1 = φ B := ⟨_, rfl⟩
  have hB1 : B1 * hom = hom * B1 := by
    rw [hB1def, ← hφω, ← map_mul, ← map_mul, hB]
  have hB1g : genHyp (mcode ⇑B1) = true := by
    refine genHyp_mcode ?_ ?_ ?_
    · rw [hB1def, ← map_pow, hB4, map_one]
    · rw [hB1def, ← hφA, ← map_mul, ← map_pow]
      exact hφZ _ hAB
    · rw [hB1def, ← hφA, ← map_mul, ← map_mul, ← map_pow, ← pow_two]
      exact hφZ _ hAB2
  obtain ⟨w, c, hc, hw, hw2⟩ := genTab_spec (HatN.mact_lt' B1 1) (HatN.mact_lt' B1 4)
    (HatN.mact_lt' B1 16) (by rw [← mcode_eq_hc hB1]; exact hB1g)
  rw [← mcode_eq_hc hB1] at hw
  obtain ⟨hpc, hwc, hwc2⟩ := conjTab_spec hc
  obtain ⟨hPc, hlc1, hlc2⟩ := of_pairB hpc
  obtain ⟨D, hDdef⟩ : ∃ D, D = pAut hPc := ⟨_, rfl⟩
  have hD : mcode ⇑D = c.1 := by rw [hDdef]; exact mcode_pAut hPc hlc1
  have hDi : mcode ⇑D⁻¹ = c.2.1 := by rw [hDdef, pAut_inv]; exact mcode_pAut _ hlc2
  have hDB : D⁻¹ * (B1 * D) = welt w :=
    mcode_injective (by rw [mcode_mul, mcode_mul, hD, hDi, mcode_welt, hw])
  have hDA : D⁻¹ * (hA0 * D) = welt c.2.2 :=
    mcode_injective (by rw [mcode_mul, mcode_mul, hD, hDi, mcode_welt, hwc, mcode_hA0])
  refine ⟨D⁻¹ * C⁻¹, ?_, ?_⟩
  · have h1 : D⁻¹ * C⁻¹ * A * (D⁻¹ * C⁻¹)⁻¹ = D⁻¹ * (C⁻¹ * A * C * D) := by group
    rw [h1, ← hφ, hφA, hDA]
    exact welt_mem_Gam0 _ hwc2
  · have h1 : D⁻¹ * C⁻¹ * B * (D⁻¹ * C⁻¹)⁻¹ = D⁻¹ * (C⁻¹ * B * C * D) := by group
    rw [h1, ← hφ, ← hB1def, hDB]
    exact welt_mem_Gam0 _ hw2

theorem mcode_hg1_inv : mcode ⇑hg1⁻¹ = g1i := by
  rw [show hg1 = pAut pair_g1 from rfl, pAut_inv]
  exact mcode_pAut _ rfl

theorem mcode_hg2_inv : mcode ⇑hg2⁻¹ = g2i := by
  rw [show hg2 = pAut pair_g2 from rfl, pAut_inv]
  exact mcode_pAut _ rfl

theorem mcode_mem_g0List {x : MulAut W6} (hx : x ∈ Gam0) :
    mcode ⇑x ∈ g0List := by
  obtain ⟨h1, -, hcl⟩ := g0List_spec
  refine Subgroup.closure_induction_left (p := fun (x : MulAut W6) _ => mcode ⇑x ∈ g0List)
    ?_ ?_ ?_ hx
  · rw [mcode_one]
    exact h1
  · intro x hx y _ ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [mcode_mul, mcode_hg1]
      exact (hcl _ ih).1
    · rw [mcode_mul, mcode_hg2]
      exact (hcl _ ih).2.1
  · intro x hx y _ ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [mcode_mul, mcode_hg1_inv]
      exact (hcl _ ih).2.2.1
    · rw [mcode_mul, mcode_hg2_inv]
      exact (hcl _ ih).2.2.2

theorem finite_card_Gam0_le :
    Finite Gam0 ∧ Nat.card Gam0 ≤ 1080 := by
  classical
  let f : Gam0 → ↥g0List.toFinset := fun x =>
    ⟨mcode ⇑(x : MulAut W6), List.mem_toFinset.mpr (mcode_mem_g0List x.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (mcode_injective (congrArg Subtype.val hxy))
  refine ⟨Finite.of_injective f hf, ?_⟩
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥g0List.toFinset), Fintype.card_coe] at h1
  exact h1.trans ((List.toFinset_card_le _).trans g0List_spec.2.1.le)

theorem card_Gam0 : Nat.card Gam0 = 1080 := by
  obtain ⟨hfin, hle⟩ := finite_card_Gam0_le
  refine le_antisymm hle ?_
  have h1 := le_card_orbit (H := Gam0) le_rfl
  have hPG : PG0 ≤ Gam0 := by
    rw [← inf_P0_eq]
    exact inf_le_left
  have hPP : PG0 ≤ P0 := by
    rw [← inf_P0_eq]
    exact inf_le_right
  let f : PG0 → MulAction.stabilizer (↥Gam0) w0 := fun x =>
    ⟨⟨x, hPG x.2⟩, P0_le_stab0 (hPP x.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (congrArg (fun s : MulAction.stabilizer (↥Gam0) w0 =>
      ((s : ↥Gam0) : MulAut W6)) hxy)
  have h2 := Nat.card_le_card_of_injective f hf
  rw [card_PG0] at h2
  have h3 := (MulAction.stabilizer (↥Gam0) w0).index_mul_card
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h3
  calc 1080 = 45 * 24 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h1 h2
    _ = Nat.card Gam0 := h3

@[expose] def sa : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 2 3 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def sb : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 5,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem std_rel : sa ^ 2 = 1 ∧ sa ≠ 1 ∧ sb ^ 4 = 1 ∧ (sa * sb) ^ 5 = 1 ∧
    (sa * sb ^ 2) ^ 5 = 1 ∧ sa ^ 3 = sa ∧ sb ^ 9 = sb := by
  decide +kernel

theorem std_words :
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.x =
      [sa, sb, sa, sb, sa, sb, sb, sb, sa, sb, sb].prod ∧
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.y =
      [sb, sb, sb, sa, sb, sb, sa, sb, sa, sb].prod := by
  decide +kernel

theorem closure_std : closure ({sa, sb} : Set (alternatingGroup (Fin 6))) = ⊤ := by
  have hw : ∀ l : List (alternatingGroup (Fin 6)), (∀ g ∈ l, g = sa ∨ g = sb) →
      l.prod ∈ closure ({sa, sb} : Set (alternatingGroup (Fin 6))) := fun l hl =>
    Subgroup.list_prod_mem _ fun g hg => subset_closure (hl g hg)
  rw [eq_top_iff,
    ← CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.generating_pair,
    closure_le]
  rintro _ (rfl | rfl)
  · rw [std_words.1]
    exact hw _ (by simp)
  · rw [std_words.2]
    exact hw _ (by simp)

theorem exists_std_gens {X : Type} [Group X] (hX : IsHat X ↥(alternatingGroup (Fin 6))) :
    ∃ a b : X, a ^ 2 = 1 ∧ a ≠ 1 ∧ b ^ 4 = 1 ∧ (a * b) ^ 5 ∈ center X ∧
      (a * b ^ 2) ^ 5 ∈ center X ∧ closure {a, b} = ⊤ := by
  obtain ⟨hq, hZ3, ⟨θ⟩⟩ := hX
  set π : X →* alternatingGroup (Fin 6) := θ.toMonoidHom.comp (QuotientGroup.mk' (center X))
    with hπ
  have hker : ∀ x, π x = 1 ↔ x ∈ center X := fun x => by
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hZ : ∀ z ∈ center X, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥(center X)) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  obtain ⟨a, ha⟩ := hsurj sa
  obtain ⟨b, hb⟩ := hsurj sb
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := std_rel
  have ha2 : a ^ 2 ∈ center X := (hker _).mp (by rw [map_pow, ha, r1])
  have hb4 : b ^ 4 ∈ center X := (hker _).mp (by rw [map_pow, hb, r3])
  refine ⟨a ^ 3, b ^ 9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hZ _ ha2]
  · intro h
    apply r2
    rw [← r6, ← ha, ← map_pow, h, map_one]
  · rw [← pow_mul, show 9 * 4 = 4 * 3 * 3 from rfl, pow_mul, pow_mul, hZ _ hb4, one_pow]
  · exact (hker _).mp (by simp only [map_pow, map_mul, ha, hb, r6, r7, r4])
  · exact (hker _).mp (by simp only [map_pow, map_mul, ha, hb, r6, r7, r5])
  · refine CFSG.QuasithinUnique.Setup.X1.eq_top_of_sup_center_eq_top hq.1
      (eq_top_iff.mpr fun x _ => ?_)
    have hmap : (closure {a ^ 3, b ^ 9}).map π = ⊤ := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [map_pow, ha, hb, r6, r7]
      exact closure_std
    have hx : π x ∈ (closure {a ^ 3, b ^ 9}).map π := by
      rw [hmap]
      exact mem_top _
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have hc : h⁻¹ * x ∈ center X := (hker _).mp (by rw [map_mul, map_inv, hhx, inv_mul_cancel])
    have h1 := mul_mem_sup hh hc
    rwa [mul_inv_cancel_left] at h1

theorem card_W6 : Nat.card W6 = 2 ^ 6 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem sq_W6 (w : W6) : w * w = 1 := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply, h2]

theorem sq2_W6 (w : W6) : w ^ 2 = 1 := by
  rw [pow_two]
  exact sq_W6 w

theorem hom_fpf (w : W6) (hw : hom w = w) : w = 1 := by
  obtain ⟨c, hc, rfl⟩ : ∃ c < 64, Multiplicative.ofAdd (dec c) = w :=
    ⟨enc (Multiplicative.toAdd w), enc_lt _, by rw [dec_enc]; rfl⟩
  have h1 : mact omc c = c := by
    have h := congrArg (fun v => enc (Multiplicative.toAdd v)) hw
    rwa [enc_apply hom c hc, mcode_hom, toAdd_ofAdd, enc_dec c hc] at h
  have h0 : ∀ c < 64, mact omc c = c → c = 0 := by decide +kernel
  rw [h0 c hc h1, dec_zero, ofAdd_zero]

theorem exists_coord_equiv {V : Type} [CommGroup V] [Finite V] (hsq2 : ∀ v : V, v ^ 2 = 1)
    (hV : Nat.card V = 2 ^ 6) {z : MulAut V} (h3 : z ^ 3 = 1) (hfp : ∀ v, z v = v → v = 1) :
    ∃ E : Multiplicative (Fin 3 → CFSG.CharacterTheory.SteinbergBY.FieldFour) ≃* V,
      ∀ c, E (Multiplicative.ofAdd (CFSG.CharacterTheory.SteinbergBY.FieldFour.ω •
        Multiplicative.toAdd c)) = z (E c) := by
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hsq2 v
  have hzz : ∀ v, z (z v) = v * z v := fun v =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hu⟩ := HatA6.exists_coord hsq hV h3 hfp
  exact ⟨HatA6.coordEquiv hu, fun c => HatA6.coordHom_ω hsq hzz u c⟩

theorem exists_equiv_conj_hom {V : Type} [CommGroup V] [Finite V] (hsq2 : ∀ v : V, v ^ 2 = 1)
    (hV : Nat.card V = 2 ^ 6) {z : MulAut V} (h3 : z ^ 3 = 1) (hfp : ∀ v, z v = v → v = 1) :
    ∃ e : V ≃* W6, ∀ v, e (z v) = hom (e v) := by
  obtain ⟨E, hE⟩ := exists_coord_equiv hsq2 hV h3 hfp
  obtain ⟨EW, hEW⟩ := exists_coord_equiv (V := W6) (fun w => sq2_W6 w) card_W6 (z := hom)
    hom_pow_three hom_fpf
  refine ⟨E.symm.trans EW, fun v => ?_⟩
  obtain ⟨c, rfl⟩ := E.surjective v
  have h2 : EW (Multiplicative.ofAdd (CFSG.CharacterTheory.SteinbergBY.FieldFour.ω •
      Multiplicative.toAdd c)) = hom (EW c) := hEW c
  calc (E.symm.trans EW) (z (E c)) = EW (E.symm (z (E c))) := rfl
    _ = EW (Multiplicative.ofAdd (CFSG.CharacterTheory.SteinbergBY.FieldFour.ω •
        Multiplicative.toAdd c)) := by rw [← hE, MulEquiv.symm_apply_apply]
    _ = hom (EW c) := h2
    _ = hom ((E.symm.trans EW) (E c)) := by rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem hatA6Embed_holds : HatA6Embed := by
  intro V _ _ hsq2 hV K hK
  obtain ⟨hq, hZ3, ⟨θ⟩⟩ := hK
  have hK1080 : Nat.card K = 1080 := (HatA6.quasisimple_card hq.1 hZ3 θ).2
  obtain ⟨zK, hcen, h3, hfp⟩ := HatA6.exists_center_fpf hsq2 hV hq.1 hZ3 θ
  obtain ⟨e₀, he₀⟩ := exists_equiv_conj_hom hsq2 hV h3 hfp
  set ψ : MulAut V →* MulAut W6 := CFSG.Quasithin.H.congrHom e₀ with hψ
  have hψz : ψ zK = hom := MulEquiv.ext fun w => by
    have h := he₀ (e₀.symm w)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hψinj : Function.Injective ψ := CFSG.Quasithin.H.congrHom_injective e₀
  obtain ⟨a, b, ha2, ha1, hb4, hab, hab2, hgen⟩ := exists_std_gens ⟨hq, hZ3, ⟨θ⟩⟩
  have hZ : ∀ x ∈ center ↥K, ψ (x : MulAut V) ∈ zpowers hom := by
    intro x hx
    rw [hcen] at hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [Subgroup.coe_zpow, map_zpow, hψz]
    exact zpow_mem (mem_zpowers _) k
  have hcomm : ∀ x : ↥K, ψ x * hom = hom * ψ x := by
    intro x
    have h1 : x * zK = zK * x :=
      mem_center_iff.mp (hcen ▸ mem_zpowers zK : zK ∈ center ↥K) x
    have h2 : (x : MulAut V) * zK = zK * x := congrArg Subtype.val h1
    rw [← hψz, ← map_mul, ← map_mul, h2]
  obtain ⟨g, hga, hgb⟩ := exists_conj_mem_Gam0 (hcomm a) (hcomm b)
    (by rw [← map_pow, ← Subgroup.coe_pow, ha2, Subgroup.coe_one, map_one])
    (fun h => ha1 (Subtype.ext (hψinj (h.trans (map_one ψ).symm))))
    (by rw [← map_pow, ← Subgroup.coe_pow, hb4, Subgroup.coe_one, map_one])
    (by
      have h1 : (ψ a * ψ b) ^ 5 = ψ ↑((a * b) ^ 5) := by
        simp only [Subgroup.coe_pow, Subgroup.coe_mul, map_pow, map_mul]
      rw [h1]
      exact hZ _ hab)
    (by
      have h1 : (ψ a * ψ b ^ 2) ^ 5 = ψ ↑((a * b ^ 2) ^ 5) := by
        simp only [Subgroup.coe_pow, Subgroup.coe_mul, map_pow, map_mul]
      rw [h1]
      exact hZ _ hab2)
  have hKgen : K = closure {(a : MulAut V), (b : MulAut V)} := by
    have h1 := congrArg (Subgroup.map K.subtype) hgen
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, range_subtype] at h1
    exact h1.symm
  have hle : (K.map ψ).map (MulAut.conj g).toMonoidHom ≤ Gam0 := by
    rw [hKgen, MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair,
      closure_le]
    rintro _ (rfl | rfl)
    · exact hga
    · exact hgb
  have hcard : Nat.card ((K.map ψ).map (MulAut.conj g).toMonoidHom) = 1080 := by
    rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      card_map_of_injective hψinj, hK1080]
  have : Finite Gam0 := finite_card_Gam0_le.1
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_Gam0, hcard]))
  refine ⟨e₀.trans g, ?_⟩
  rw [← heq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ψ x, ⟨x, hx, rfl⟩, MulEquiv.ext fun w => rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, MulEquiv.ext fun w => rfl⟩

end CFSG.Quasithin.H13.HatE
