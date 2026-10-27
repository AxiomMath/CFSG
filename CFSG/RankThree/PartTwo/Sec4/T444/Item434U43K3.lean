module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Class
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Pair
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Out
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGen
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (NoSignalizer)

attribute [local irreducible] sAt

theorem NoSignalizer.mono {X : Type*} [Group X] {P' P : Subgroup X} (h : P' ≤ P)
    (hP' : NoSignalizer P') : NoSignalizer P := fun Y hY hPY =>
  hP' Y hY ((Subgroup.map_mono h).trans hPY)

theorem mul_conj_mul_inv_aut {X : Type*} [Group X] (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext u
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem noSignalizer_of_inner' {X : Type*} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {B : Subgroup X}
    (hin : ∀ W : Subgroup X, ¬ 3 ∣ Nat.card W → B ≤ Subgroup.normalizer (W : Set X) → W = ⊥)
    (hout : ∀ α : MulAut X, (∀ f ∈ B, α f = f) → α ∈ (MulAut.conj : X →* MulAut X).range) :
    NoSignalizer B := by
  intro Y hY3 hBY
  set ι := (MulAut.conj : X →* MulAut X) with hι
  have hinj : Function.Injective ι := Item434Kit.conj_injective_of_center_eq_bot hZ
  set W := Y.comap ι with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    apply hY3
    have h1 : Nat.card (W.map ι) = Nat.card W := Subgroup.card_map_of_injective hinj
    have h2 : W.map ι ≤ Y := Subgroup.map_comap_le _ _
    exact (h1 ▸ h3).trans (Subgroup.card_dvd_of_le h2)
  have hBW : B ≤ Subgroup.normalizer (W : Set X) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hfN : ι f ∈ Subgroup.normalizer (Y : Set (MulAut X)) := hBY ⟨f, hf, rfl⟩
    simp only [hW, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hfN (ι w)
  have hW1 : W = ⊥ := hin W hW3 hBW
  have hYinn : ∀ g : X, ι g ∈ Y → g = 1 := fun g hg => by
    have : g ∈ W := hg
    rw [hW1] at this
    exact Subgroup.mem_bot.mp this
  rw [eq_bot_iff]
  intro α hα
  have hfix : ∀ f ∈ B, α f = f := by
    intro f hf
    have hfN : ι f ∈ Subgroup.normalizer (Y : Set (MulAut X)) := hBY ⟨f, hf, rfl⟩
    have hc : ι f * α * (ι f)⁻¹ * α⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hfN α).mp hα) (Y.inv_mem hα)
    have heq : ι f * α * (ι f)⁻¹ * α⁻¹ = ι (f * (α f)⁻¹) := by
      have h1 : α * (ι f)⁻¹ * α⁻¹ = (ι (α f))⁻¹ := by
        rw [← map_inv ι f, hι, mul_conj_mul_inv_aut, map_inv α, map_inv]
      calc ι f * α * (ι f)⁻¹ * α⁻¹ = ι f * (α * (ι f)⁻¹ * α⁻¹) := by group
        _ = ι (f * (α f)⁻¹) := by rw [h1, map_mul, map_inv]
    rw [heq] at hc
    have h1 := hYinn _ hc
    rw [mul_inv_eq_one] at h1
    exact h1.symm
  obtain ⟨g, rfl⟩ := hout α hfix
  rw [Subgroup.mem_bot, hYinn g hα, map_one]

theorem eq_one_of_pGroup_coprime {X : Type*} [Group X] [Finite X] {C W : Subgroup X}
    (hC : IsPGroup 3 C) (hW : ¬ 3 ∣ Nat.card W) {x : X} (hxW : x ∈ W) (hxC : x ∈ C) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hC ⟨x, hxC⟩
  have hx : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hxW
  have hcop : Nat.Coprime (3 ^ k) (Nat.card W) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)

theorem hin_of_triple (hsyl : uSylCheck = true) (hcls : uClassCheck = true) {z a b : SUg}
    (haS : a ∈ sylS) (hbS : b ∈ sylS) (hcomm : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hkind : ∀ x ∈ Subgroup.closure ({a, b} : Set SUg), x ≠ 1 →
      ∃ p < 729, kindAt p = 3 ∧ x = sAt p)
    {W : Subgroup UX} (hW3 : ¬ 3 ∣ Nat.card W)
    (hN : (Subgroup.closure ({z, a, b} : Set SUg)).map piU ≤ Subgroup.normalizer (W : Set UX)) :
    W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({a, b} : Set SUg) with hE
  have hEe : IsElemAbelian 3 E := by
    refine Item434SporE81.isElemAbelian_closure_of_comm ?_ ?_
    · rintro x (rfl | rfl) y (rfl | rfl)
      · exact Commute.refl _
      · exact hcomm
      · exact hcomm.symm
      · exact Commute.refl _
    · rintro x (rfl | rfl)
      · exact ha3
      · exact hb3
  have hEle : E ≤ sylS := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haS
    · exact hbS
  have hE9 : Nat.card E = 9 := Asc83Table.card_closure_pair_eq_nine ha3 hb3 hcomm ha1 hba
  have hBe : IsElemAbelian 3 (E.map piU) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hEe
  have hB9 : 3 ^ 2 ≤ Nat.card (E.map piU) := by
    rw [card_map_piU_of_le hsyl hEle, hE9]
    norm_num
  have hEP : E ≤ Subgroup.closure ({z, a, b} : Set SUg) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have hBN : E.map piU ≤ Subgroup.normalizer (W : Set UX) :=
    (Subgroup.map_mono hEP).trans hN
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBe hB9 hBN hcop ?_
  rintro _ ⟨y, hy, rfl⟩ hv1 x ⟨hxW, hxC⟩
  have hy1 : y ≠ 1 := fun h => hv1 (by rw [h, map_one])
  obtain ⟨p, hp, h3, rfl⟩ := hkind y hy hy1
  exact Subgroup.mem_bot.mpr
    (eq_one_of_pGroup_coprime (isPGroup_centralizer_kind3 hsyl hcls hp h3) hW3 hxW hxC)

theorem lt_of_kindAt_eq_three (hk : uKindCheck = true) {p : ℕ} (h3 : kindAt p = 3) : p < 729 := by
  simp only [uKindCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  by_contra hlt
  have : kindAt p = 0 := by
    unfold kindAt uKindArr
    simp [Array.getD_eq_getD_getElem?, hk.1.1.1, hlt]
  omega

theorem sAt_ne_of_code_ne (hsyl : uSylCheck = true) {s t : ℕ} (hs : s < 729) (ht : t < 729)
    (h : uAt s ≠ uAt t) : sAt s ≠ sAt t := fun e =>
  h (dec4_injective (canon4_uAt hsyl hs) (canon4_uAt hsyl ht)
    (by rw [← toMat_sAt hsyl hs, ← toMat_sAt hsyl ht, e]))

theorem bad_facts (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hbad : uBadCheck = true) {k : ℕ} (hk : k < 12) {pa pb : ℕ}
    (hpa : (badTriple k).getD 1 0 = pa) (hpb : (badTriple k).getD 2 0 = pb) :
    pa < 729 ∧ pb < 729 ∧ sAt pa ∈ sylS ∧ sAt pb ∈ sylS ∧ sAt pa * sAt pb = sAt pb * sAt pa ∧
      sAt pa ^ 3 = 1 ∧ sAt pb ^ 3 = 1 ∧ sAt pa ≠ 1 ∧ sAt pb ∉ Subgroup.zpowers (sAt pa) ∧
      (∀ x ∈ Subgroup.closure ({sAt pa, sAt pb} : Set SUg), x ≠ 1 →
        ∃ p < 729, kindAt p = 3 ∧ x = sAt p) := by
  obtain ⟨-, hk', -, -, -⟩ := uClassCheck_parts hcls
  have hpa_lt : pa < 729 := hpa ▸ badTriple_lt hbad hk 1
  have hpb_lt : pb < 729 := hpb ▸ badTriple_lt hbad hk 2
  obtain ⟨-, -, -, hcomm, hca, hcb, hne, hnm, hkinds, -, -, -, -⟩ :=
    badOK_spec (badOK_of_check hbad hk)
  have hA : badA k = uAt pa := by rw [badA, hpa]
  have hB : badB k = uAt pb := by rw [badB, hpb]
  rw [hA] at hca hne
  rw [hB] at hcb
  rw [hA, hB] at hcomm hnm hkinds
  have ha3 : sAt pa ^ 3 = 1 := pow_three_of_cube4 hsyl hpa_lt hca
  have hb3 : sAt pb ^ 3 = 1 := pow_three_of_cube4 hsyl hpb_lt hcb
  have hab : sAt pa * sAt pb = sAt pb * sAt pa := commute_of_commutes4 hsyl hpa_lt hpb_lt hcomm
  have hb1 : sAt pb ≠ 1 := ne_one_of_code_ne hsyl hpb_lt fun e => hnm (by simp [e])
  refine ⟨hpa_lt, hpb_lt, sAt_mem hsyl hpa_lt, sAt_mem hsyl hpb_lt, hab, ha3, hb3,
    ne_one_of_code_ne hsyl hpa_lt hne, ?_, ?_⟩
  · refine Asc83Table.not_mem_zpowers_of_ne ha3 hb1 ?_ ?_
    · exact sAt_ne_of_code_ne hsyl hpb_lt hpa_lt fun e => hnm (by simp [e])
    · intro e
      apply hnm
      have : uAt pb = sq4 (uAt pa) := by
        apply dec4_injective (canon4_uAt hsyl hpb_lt) (by unfold sq4; exact canon4_mul4 _ _)
        rw [← toMat_sAt hsyl hpb_lt, e, sq4, dec4_mul4, ← toMat_sAt hsyl hpa_lt, pow_two, map_mul]
      simp [this]
  · intro x hx hx1
    obtain ⟨c, hc, hcx⟩ := mem_e9Elems (toMat_sAt hsyl hpa_lt) (toMat_sAt hsyl hpb_lt) ha3 hb3
      hab hx
    have hc' := hkinds c hc
    rcases hc' with h1 | h3
    · exact absurd (toMat_injective (by rw [← hcx, h1, dec4_one4, map_one])) hx1
    · have hp : posOf c < 729 := lt_of_kindAt_eq_three hk' h3
      refine ⟨posOf c, hp, h3, toMat_injective ?_⟩
      rw [toMat_sAt hsyl hp, posOf_spec hp, hcx]

theorem noSignalizer_of_good (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hZ : Subgroup.center UX = ⊥) {pa pb : ℕ} {zc' ac bc Qc Tc Tic : List ℕ} {u : Fin 4 → F9}
    (hfacts : pa < 729 ∧ pb < 729 ∧ sAt pa ∈ sylS ∧ sAt pb ∈ sylS ∧
      sAt pa * sAt pb = sAt pb * sAt pa ∧ sAt pa ^ 3 = 1 ∧ sAt pb ^ 3 = 1 ∧ sAt pa ≠ 1 ∧
      sAt pb ∉ Subgroup.zpowers (sAt pa) ∧
      (∀ x ∈ Subgroup.closure ({sAt pa, sAt pb} : Set SUg), x ≠ 1 →
        ∃ p < 729, kindAt p = 3 ∧ x = sAt p))
    (hz : uAt uZ = zc') (ha : uAt pa = ac) (hb : uAt pb = bc)
    (hg : OutGood (dec4 zc') (dec4 ac) (dec4 bc) (dec4 Qc) (dec4 Tc) (dec4 Tic) u) :
    NoSignalizer ((Subgroup.closure ({sAt uZ, sAt pa, sAt pb} : Set SUg)).map piU) := by
  obtain ⟨hpa, hpb, haS, hbS, hcomm, ha3, hb3, ha1, hba, hkind⟩ := hfacts
  obtain ⟨-, hk, -, -, hzc⟩ := uClassCheck_parts hcls
  obtain ⟨hzlt, -, hz3, -⟩ := uZ_spec hsyl hzc
  refine noSignalizer_of_inner' hZ ?_ ?_
  · intro W hW3 hN
    exact hin_of_triple hsyl hcls haS hbS hcomm ha3 hb3 ha1 hba hkind hW3 hN
  · intro α hα
    have hmem : ∀ y ∈ ({sAt uZ, sAt pa, sAt pb} : Set SUg), α (piU y) = piU y := fun y hy =>
      hα _ (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure hy))
    exact inner_of_fix_triple (toMat_sAt hsyl hzlt |>.trans (congrArg dec4 hz))
      (toMat_sAt hsyl hpa |>.trans (congrArg dec4 ha))
      (toMat_sAt hsyl hpb |>.trans (congrArg dec4 hb)) hz3 ha3 hb3 hg α
      (hmem _ (by simp)) (hmem _ (by simp)) (hmem _ (by simp))

@[expose] def zLit : List ℕ := [4, 6, 8, 8, 3, 4, 7, 7, 5, 4, 5, 2, 5, 4, 2, 5]

@[expose] def a1Lit : List ℕ := [1, 2, 6, 6, 1, 2, 3, 3, 2, 2, 6, 3, 2, 2, 3, 6]

@[expose] def b1Lit : List ℕ := [7, 4, 1, 4, 8, 6, 1, 0, 5, 8, 2, 4, 2, 7, 1, 0]

@[expose] def a2Lit : List ℕ := [8, 7, 6, 8, 5, 6, 3, 0, 7, 4, 1, 5, 6, 7, 2, 0]

theorem uLits : uAt uZ = zLit ∧ uAt 68 = a1Lit ∧ uAt 167 = b1Lit ∧ uAt 19 = a2Lit := by
  decide +kernel

@[expose] def uSoc : Fin 4 → F9 := fun i => uncodeF ([1, 3, 5, 5].getD i 0)

theorem outGood1 : OutGood (dec4 zLit) (dec4 a1Lit) (dec4 b1Lit)
    (dec4 [4, 7, 3, 3, 4, 2, 8, 0, 2, 3, 8, 0, 3, 6, 6, 0])
    (dec4 [5, 3, 1, 0, 3, 7, 6, 0, 1, 6, 5, 0, 0, 0, 0, 1])
    (dec4 [4, 3, 2, 0, 3, 8, 6, 0, 2, 6, 4, 0, 0, 0, 0, 2]) uSoc := by
  decide +kernel

theorem outGood2 : OutGood (dec4 zLit) (dec4 a2Lit) (dec4 a1Lit)
    (dec4 [4, 7, 3, 3, 6, 2, 7, 0, 8, 6, 5, 0, 3, 5, 1, 0])
    (dec4 [4, 6, 6, 0, 6, 8, 2, 0, 6, 2, 8, 0, 0, 0, 0, 1])
    (dec4 [5, 6, 6, 0, 6, 7, 1, 0, 6, 1, 7, 0, 0, 0, 0, 2]) uSoc := by
  decide +kernel

theorem repIdx_eq : ∀ k < 12, repIdx (badClass k) = 0 ∨ repIdx (badClass k) = 3 := by decide

theorem noSignalizer_rep (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hbad : uBadCheck = true) (hZ : Subgroup.center UX = ⊥) {r : ℕ} (hr : r = 0 ∨ r = 3) :
    NoSignalizer ((Subgroup.closure ({sAt uZ, sAt ((badTriple r).getD 1 0),
      sAt ((badTriple r).getD 2 0)} : Set SUg)).map piU) := by
  have hu := uLits
  rcases hr with rfl | rfl
  · have e1 : (badTriple 0).getD 1 0 = 68 := by decide
    have e2 : (badTriple 0).getD 2 0 = 167 := by decide
    rw [e1, e2]
    exact noSignalizer_of_good hsyl hcls hZ (bad_facts hsyl hcls hbad (by norm_num) e1 e2)
      hu.1 hu.2.1 hu.2.2.1 outGood1
  · have e1 : (badTriple 3).getD 1 0 = 19 := by decide
    have e2 : (badTriple 3).getD 2 0 = 68 := by decide
    rw [e1, e2]
    exact noSignalizer_of_good hsyl hcls hZ (bad_facts hsyl hcls hbad (by norm_num) e1 e2)
      hu.1 hu.2.2.2 hu.2.1 outGood2

theorem map_piU_map_conj (H : Subgroup SUg) (g : SUg) :
    (H.map (MulAut.conj g).toMonoidHom).map piU =
      (H.map piU).map (MulAut.conj (piU g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem sq_mul_sq_eq {z : SUg} (hz3 : z ^ 3 = 1) : z * z * (z * z) = z :=
  calc z * z * (z * z) = z * (z * z) * z := by simp only [mul_assoc]
    _ = z ^ 3 * z := by rw [pow_three]
    _ = z := by rw [hz3, one_mul]

theorem closure_sq_eq {z a b : SUg} (hz3 : z ^ 3 = 1) :
    Subgroup.closure ({z * z, a, b} : Set SUg) = Subgroup.closure ({z, a, b} : Set SUg) := by
  have hzz := sq_mul_sq_eq hz3
  have h1 : z * z ∈ Subgroup.closure ({z * z, a, b} : Set SUg) :=
    Subgroup.subset_closure (by simp)
  have h2 : z ∈ Subgroup.closure ({z * z, a, b} : Set SUg) := by
    have := Subgroup.mul_mem _ h1 h1
    rwa [hzz] at this
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact h2
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact Subgroup.subset_closure (by simp)

theorem map_conj_closure_triple (g z a b : SUg) :
    (Subgroup.closure ({z, a, b} : Set SUg)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * z * g⁻¹, g * a * g⁻¹, g * b * g⁻¹} : Set SUg) := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem noSignalizer_bad (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hbad : uBadCheck = true) (hZ : Subgroup.center UX = ⊥) {k : ℕ} (hk : k < 12) :
    NoSignalizer ((Subgroup.closure ({sAt uZ, sAt ((badTriple k).getD 1 0),
      sAt ((badTriple k).getD 2 0)} : Set SUg)).map piU) := by
  obtain ⟨-, -, -, -, hzc⟩ := uClassCheck_parts hcls
  obtain ⟨hzlt, -, hz3, -⟩ := uZ_spec hsyl hzc
  obtain ⟨-, hk', -, -, -⟩ := uClassCheck_parts hcls
  obtain ⟨-, -, hr12, -, -, -, -, -, -, hw, hca, hcb, hcz⟩ :=
    badOK_spec (badOK_of_check hbad hk)
  have hw' : ∀ l ∈ badWord k, l < 4 := hw
  have hNr := noSignalizer_rep hsyl hcls hbad hZ (repIdx_eq k hk)
  set r := repIdx (badClass k) with hr
  set g : SUg := wordElem (badWord k) with hg
  have hpa := badTriple_lt hbad hk 1
  have hpb := badTriple_lt hbad hk 2
  have hpar := badTriple_lt hbad hr12 1
  have hpbr := badTriple_lt hbad hr12 2
  have hcA : g * sAt ((badTriple k).getD 1 0) * g⁻¹ = sAt ((badTriple r).getD 1 0) := by
    apply toMat_injective
    rw [toMat_conj_word hw' (toMat_sAt hsyl hpa), toMat_sAt hsyl hpar]
    exact congrArg dec4 hca
  have hcB : g * sAt ((badTriple k).getD 2 0) * g⁻¹ = sAt ((badTriple r).getD 2 0) := by
    apply toMat_injective
    rw [toMat_conj_word hw' (toMat_sAt hsyl hpb), toMat_sAt hsyl hpbr]
    exact congrArg dec4 hcb
  have hcZ : g * sAt uZ * g⁻¹ = sAt uZ ∨ g * sAt uZ * g⁻¹ = sAt uZ * sAt uZ := by
    rcases hcz with h | h
    · left
      apply toMat_injective
      rw [toMat_conj_word hw' (toMat_sAt hsyl hzlt)]
      exact congrArg dec4 h |>.trans (toMat_sAt hsyl hzlt).symm
    · right
      apply toMat_injective
      rw [toMat_conj_word hw' (toMat_sAt hsyl hzlt), map_mul, toMat_sAt hsyl hzlt]
      exact (congrArg dec4 h).trans (by rw [zc2, sq4, dec4_mul4]; rfl)
  have hPr : (Subgroup.closure ({sAt uZ, sAt ((badTriple k).getD 1 0),
      sAt ((badTriple k).getD 2 0)} : Set SUg)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({sAt uZ, sAt ((badTriple r).getD 1 0),
        sAt ((badTriple r).getD 2 0)} : Set SUg) := by
    rw [map_conj_closure_triple, hcA, hcB]
    rcases hcZ with h | h
    · rw [h]
    · rw [h]
      exact closure_sq_eq hz3
  have hX := hNr.map_conj (piU g)⁻¹
  have hPX : (Subgroup.map piU (Subgroup.closure ({sAt uZ, sAt ((badTriple r).getD 1 0),
      sAt ((badTriple r).getD 2 0)} : Set SUg))).map (MulAut.conj (piU g)⁻¹).toMonoidHom =
      (Subgroup.closure ({sAt uZ, sAt ((badTriple k).getD 1 0),
        sAt ((badTriple k).getD 2 0)} : Set SUg)).map piU := by
    rw [← hPr, map_piU_map_conj]
    have := Item434AltPerm.map_conj_map_conj_inv
      ((Subgroup.closure ({sAt uZ, sAt ((badTriple k).getD 1 0),
        sAt ((badTriple k).getD 2 0)} : Set SUg)).map piU) (piU g)⁻¹
    rwa [inv_inv] at this
  rwa [hPX] at hX

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
