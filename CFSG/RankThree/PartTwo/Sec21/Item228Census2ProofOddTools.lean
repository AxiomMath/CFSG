module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofTools
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverGroup

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def NoL2Config228 (D : Type) [Group D] : Prop :=
  ∀ (N Kb : Subgroup D) (m : ℕ), N.Normal → Kb ≤ N → Nonempty (Kb ≃* projSL 2 (GaloisField 2 m)) →
    0 < m → Even m → (Kb = N ∨ StatedClassicalModel N .PSU 3 2 2) → False

namespace Item228Census2Proof

theorem isSimpleGroup_of_mulEquiv_projSL_two {X : Type*} [Group X] {m : ℕ} (hm : 0 < m)
    (he : Even m) (e : X ≃* projSL 2 (GaloisField 2 m)) : IsSimpleGroup X := by
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) :=
    isSimpleGroup_projSL_two (by obtain ⟨r, hr⟩ := he; omega)
  exact e.isSimpleGroup

theorem conj_mem_inSubgroup_perfectResidual {S : Type*} [Group S] {H : Subgroup S} {c d : S}
    (hc : c ∈ H) (hd : d ∈ inSubgroup perfectResidual H) :
    c * d * c⁻¹ ∈ inSubgroup perfectResidual H := by
  obtain ⟨x, hx, rfl⟩ := hd
  have hn : (perfectResidual H).Normal := inferInstance
  exact ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, hn.conj_mem x hx _, rfl⟩

theorem noL2Normal228_of_noL2Config {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (h : ∀ y : S, orderOf y = 3 →
      NoL2Config228 (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set S)))) :
    NoL2Normal228 S := by
  intro y N Kb m hyZ hy3 hcomm hnorm hKbN ⟨eK⟩ hm he hU
  have hy3' : y ^ 3 = 1 := by rwa [hZ, Subgroup.mem_bot] at hy3
  have hy1 : y ≠ 1 := fun h1 => hyZ (h1 ▸ Subgroup.one_mem _)
  set C := Subgroup.centralizer ({y} : Set S) with hCdef
  set D := inSubgroup perfectResidual C with hDdef
  have hKbD : Kb ≤ D := le_perfectResidual_centralizer hcomm hKbN eK hm he
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hmemC : ∀ g : S, g ∈ C ↔ g * y = y * g := fun g => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have hNC : N ≤ C := fun k hk => (hmemC k).mpr (hcomm k hk).symm
  have hNs : IsSimpleGroup N := by
    rcases hU with rfl | hU
    · exact isSimpleGroup_of_mulEquiv_projSL_two hm he eK
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hU).2
  have hKb1 : Kb ≠ ⊥ := by
    have : IsSimpleGroup Kb := isSimpleGroup_of_mulEquiv_projSL_two hm he eK
    intro hb
    obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial : Nontrivial Kb)
    apply hab
    have ha : (a : S) ∈ (⊥ : Subgroup S) := hb ▸ a.2
    have hb' : (b : S) ∈ (⊥ : Subgroup S) := hb ▸ b.2
    rw [Subgroup.mem_bot] at ha hb'
    exact Subtype.ext (ha.trans hb'.symm)
  have hND : N ≤ D := by
    have hnormal : (D.subgroupOf N).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using conj_mem_inSubgroup_perfectResidual (hNC g.2) hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.subgroupOf N) with hb | ht
    · exfalso
      apply hKb1
      rw [eq_bot_iff]
      intro k hk
      have : (⟨k, hKbN hk⟩ : N) ∈ D.subgroupOf N := Subgroup.mem_subgroupOf.mpr (hKbD hk)
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : N) ∈ D.subgroupOf N := ht ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  refine h y (orderOf_eq_prime hy3' hy1) (N.subgroupOf D) (Kb.subgroupOf D) m ?_ ?_
    ⟨(Subgroup.subgroupOfEquivOfLe hKbD).trans eK⟩ hm he ?_
  · refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hnorm g ((hmemC g).mp (hDC g.2)) x hx
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hKbN hx
  · rcases hU with rfl | hU
    · exact Or.inl rfl
    · exact Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hND) hU)

theorem noL2Config228_of_mulEquiv {D D' : Type} [Group D] [Group D'] (e : D ≃* D')
    (h : NoL2Config228 D') : NoL2Config228 D := by
  intro N Kb m hN hKbN ⟨eK⟩ hm he hU
  refine h (N.map e.toMonoidHom) (Kb.map e.toMonoidHom) m ?_ (Subgroup.map_mono hKbN)
    ⟨(Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩ hm he ?_
  · exact hN.map _ e.surjective
  · rcases hU with rfl | hU
    · exact Or.inl rfl
    · exact Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        (N.equivMapOfInjective e.toMonoidHom e.injective).symm hU)

theorem eq_neg_one_of_sq_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) : A = -1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have hsq : ∀ i j, ((A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)) i j =
      (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) F =>
      (B : Matrix (Fin 2) (Fin 2) F) i j) hA
    simpa [sq] using this
  have e00 := hsq 0 0
  have e01 := hsq 0 1
  have e10 := hsq 1 0
  have e11 := hsq 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  have htr : a + d ≠ 0 := by
    intro htr
    have hd : d = -a := by linear_combination htr
    apply h2
    linear_combination -e00 - hdet + a * htr
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hb, hc] at hdet e00 e11
  have hda : d = a := by
    have h1 : a * (a - d) = 0 := by linear_combination e00 - hdet
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h] at hdet
      simp at hdet
    · linear_combination -h
  have ha : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases ha with ha | ha
  · exfalso
    apply hA1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ha, hb, hc, hda] at *
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ha, hb, hc, hda] at *

theorem noL2Config228_SL2 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    NoL2Config228 (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro N Kb m _ _ ⟨eK⟩ hm he _
  have hm2 : 2 ≤ m := by obtain ⟨r, hr⟩ := he; omega
  obtain ⟨E, -, hE, hE4⟩ := Commute33Steps.exists_fourGroup_of_mulEquiv_projSL hm2 eK
  have hne : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE4
    omega
  obtain ⟨⟨a, haE⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from h)
    rw [hE4, Nat.card_zpowers, orderOf_eq_prime (hE.2 a haE) ha1] at hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hba' : b ≠ a := fun h => hba (h ▸ Subgroup.mem_zpowers a)
  exact hba' ((eq_neg_one_of_sq_eq_one h2 b (hE.2 b hbE) hb1).trans
    (eq_neg_one_of_sq_eq_one h2 a (hE.2 a haE) ha1).symm)

theorem noL2Config228_of_simple {D : Type} [Group D] [Finite D] [IsSimpleGroup D]
    (h1 : ∀ m : ℕ, 0 < m → Even m → Nat.card D ≠ Nat.card (projSL 2 (GaloisField 2 m)))
    (h2 : Nat.card D ≠ 62400) : NoL2Config228 D := by
  intro N Kb m hN hKbN ⟨eK⟩ hm he hU
  have hKs : IsSimpleGroup Kb := isSimpleGroup_of_mulEquiv_projSL_two hm he eK
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · exfalso
      obtain ⟨⟨a, ha⟩, ⟨b, hb'⟩, hab⟩ := (IsSimpleGroup.toNontrivial : Nontrivial Kb)
      apply hab
      have ha' : a ∈ (⊥ : Subgroup D) := hb ▸ hKbN ha
      have hb'' : b ∈ (⊥ : Subgroup D) := hb ▸ hKbN hb'
      rw [Subgroup.mem_bot] at ha' hb''
      exact Subtype.ext (ha'.trans hb''.symm)
    · exact ht
  have hcard : Nat.card N = Nat.card D := by rw [hNtop, Subgroup.card_top]
  rcases hU with rfl | hU
  · exact h1 m hm he (hcard.symm.trans (Nat.card_congr eK.toEquiv))
  · exact h2 (hcard.symm.trans (Item22Res4Proof.card_of_statedU34 hU))

theorem noL2Config228_of_quasisimple {D : Type} [Group D] [Finite D] (hperf : Group.IsPerfect D)
    (hs : IsSimpleGroup (D ⧸ Subgroup.center D)) (hZ : Subgroup.center D ≠ ⊥) :
    NoL2Config228 D := by
  intro N Kb m hN hKbN ⟨eK⟩ hm he hU
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_mulEquiv_projSL eK
  rcases CFSG.QuasithinUnique.Ch1.HSCover.normal_le_center_or_eq_top' hperf hs N with hc | ht
  · apply hab
    have ha := hc (hKbN a.2)
    exact Subtype.ext (Subgroup.mem_center_iff.mp ha b).symm
  · have hNs : IsSimpleGroup N := by
      rcases hU with rfl | hU
      · exact isSimpleGroup_of_mulEquiv_projSL_two hm he eK
      · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hU).2
    have eND : N ≃* D := (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
    have hDs : IsSimpleGroup D := eND.symm.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with hb | ht'
    · exact hZ hb
    · apply hab
      have ha : (a : D) ∈ Subgroup.center D := ht' ▸ Subgroup.mem_top _
      exact Subtype.ext (Subgroup.mem_center_iff.mp ha b).symm

end Item228Census2Proof

end CFSG.RankThree.PartTwo.Sec21
