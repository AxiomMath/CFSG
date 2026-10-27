module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuPerf
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuCases
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.A312Ru

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native.A312L

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem modO2_of_hom_iso {T B : Subgroup Γ} (hB : B ∈ lFamily T) {H : Type} [Group H] [Finite H]
    (ρ : ↥(B ⊔ T) →* H) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = CFSG.pCore 2 ↥(B ⊔ T)) (A : Subgroup H) [A.Normal] [IsSimpleGroup A]
    (hAnab : ∃ a b : A, a * b ≠ b * a) (hHA : IsPGroup 2 (H ⧸ A))
    (hq : ∀ (N : Subgroup ↥(B ⊔ T)) [N.Normal], IsPGroup 2 (↥(B ⊔ T) ⧸ N) →
      Nat.card (↥(B ⊔ T) ⧸ N) ≤ Nat.card (H ⧸ A)) :
    Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* A) ∧
      Nonempty (↥(CFSG.pCore 2 ↥B) ≃* ↥(CFSG.pCore 2 ↥(B ⊔ T))) := by
  classical
  obtain ⟨f, hfs, -, hfker2, hPR, hcard, ⟨e⟩⟩ := perfectCore_quot ρ hρ hker A hAnab hHA hq
  have hRmap : (perfectCore (⊤ : Subgroup ↥(B ⊔ T))).map (B ⊔ T).subtype =
      perfectCore (B ⊔ T) := by
    have h := map_perfectCore (B ⊔ T).subtype (⊤ : Subgroup ↥(B ⊔ T))
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  let eR : ↥(perfectCore (⊤ : Subgroup ↥(B ⊔ T))) ≃* ↥(perfectCore (B ⊔ T)) :=
    ((perfectCore (⊤ : Subgroup ↥(B ⊔ T))).equivMapOfInjective _
      (B ⊔ T).subtype_injective).trans (MulEquiv.subgroupCongr hRmap)
  let f' : ↥(perfectCore (B ⊔ T)) →* A := f.comp eR.symm.toMonoidHom
  have hf's : Function.Surjective f' := by
    intro a
    obtain ⟨r, hr⟩ := hfs a
    exact ⟨eR r, by simp [f', hr]⟩
  have hsolv : Group.IsSolvable f'.ker := by
    have h2 : IsPGroup 2 f'.ker := by
      intro x
      obtain ⟨k, hk⟩ := hfker2 ⟨eR.symm x, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := congrArg (fun z : f.ker => eR ((z : ↥(perfectCore (⊤ : Subgroup ↥(B ⊔ T)))))) hk
      simpa using h1
    have : Group.IsNilpotent f'.ker := h2.isNilpotent
    infer_instance
  have hBeq : B = perfectCore (B ⊔ T) := lFamily_eq_perfectCore hB hAnab f' hf's hsolv
  let eB : ↥B ≃* ↥(perfectCore (⊤ : Subgroup ↥(B ⊔ T))) :=
    (MulEquiv.subgroupCongr hBeq).trans eR.symm
  have hOcore : CFSG.pCore 2 ↥(perfectCore (⊤ : Subgroup ↥(B ⊔ T))) =
      (CFSG.pCore 2 ↥(B ⊔ T)).subgroupOf (perfectCore ⊤) := by
    have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥(B ⊔ T)) := CFSG.pCore_isPGroup
    have hP2R : IsPGroup 2 ((CFSG.pCore 2 ↥(B ⊔ T)).subgroupOf (perfectCore ⊤)) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPR).symm
    have hle : (CFSG.pCore 2 ↥(B ⊔ T)).subgroupOf (perfectCore ⊤) ≤
        CFSG.pCore 2 ↥(perfectCore (⊤ : Subgroup ↥(B ⊔ T))) :=
      le_sSup ⟨inferInstance, hP2R⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv]
  refine ⟨⟨(A312.modO2Equiv eB).trans e⟩, ⟨?_⟩⟩
  exact ((Subgroup.equivMapOfInjective _ eB.toMonoidHom eB.injective).trans
    (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 2 eB))).trans
    ((MulEquiv.subgroupCongr hOcore).trans (Subgroup.subgroupOfEquivOfLe hPR))

theorem modO2_psl32_gen {T B Y Y₃ : Subgroup Γ} {e k : ℕ} (hB : B ∈ lFamily T) (hY : B ⊔ T = Y)
    (hek : e = k + 3) (hle : Y₃ ≤ Y) (hcard : Nat.card ↥Y = 2 ^ e * 3 * 7)
    (hcard₃ : Nat.card Y₃ = 2 ^ e * 3) (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ k)
    (hq : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 1) :
    IsPSL 3 2 1 (ModO2 B) ∧ Nonempty (↥(CFSG.pCore 2 ↥B) ≃* ↥(CFSG.pCore 2 ↥Y)) := by
  classical
  subst hY
  have hns := not_isSolvable_join hB
  have hY₃ : Nat.card (Y₃.subgroupOf (B ⊔ T)) = 2 ^ e * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]; exact hcard₃
  obtain ⟨ρ0, hker, htr⟩ := exists_hom_perm (Y := ↥(B ⊔ T)) hns (Y' := Y₃.subgroupOf (B ⊔ T))
    (e := e) (p := 7) (by norm_num) (by norm_num) hcard hY₃
  have hcardG : Nat.card ρ0.range = 168 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ0.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ0).toEquiv, hker, hcard, hP] at h1
    have h2 : (2 : ℕ) ^ e = 2 ^ k * 8 := by rw [hek, pow_add]; norm_num
    rw [h2] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : Nat.card ρ0.range * 2 ^ k = 168 * 2 ^ k := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hGns : ¬ Group.IsSolvable ρ0.range := fun hGs => by
    apply hns
    have h2 : IsPGroup 2 ρ0.ker := by rw [hker]; exact CFSG.pCore_isPGroup
    have : Group.IsNilpotent ρ0.ker := h2.isNilpotent
    exact Group.isSolvable_of_ker_le_range ρ0.ker.subtype ρ0.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hsimple : IsSimpleGroup ρ0.range := isSimpleGroup_of_card_168 hcardG hGns
  let ρ : ↥(B ⊔ T) →* ρ0.range := ρ0.rangeRestrict
  have hρs : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective ρ0
  have hρker : ρ.ker = CFSG.pCore 2 ↥(B ⊔ T) := by
    rw [← hker]; exact MonoidHom.ker_rangeRestrict ρ0
  have hsimpleA : IsSimpleGroup (⊤ : Subgroup ρ0.range) :=
    (Subgroup.topEquiv : (⊤ : Subgroup ρ0.range) ≃* ρ0.range).isSimpleGroup
  have hcardA : Nat.card (⊤ : Subgroup ρ0.range) = 168 := by
    rw [Subgroup.card_top, hcardG]
  have hAnab : ∃ a b : (⊤ : Subgroup ρ0.range), a * b ≠ b * a :=
    nonabelian_of_simple (by rw [hcardA]; norm_num)
  have hidx : Nat.card (ρ0.range ⧸ (⊤ : Subgroup ρ0.range)) = 1 := Subgroup.index_top
  have hHA : IsPGroup 2 (ρ0.range ⧸ (⊤ : Subgroup ρ0.range)) :=
    IsPGroup.of_card (n := 0) (by rw [hidx]; norm_num)
  obtain ⟨⟨e'⟩, hiso⟩ := modO2_of_hom_iso hB ρ hρs hρker (⊤ : Subgroup ρ0.range) hAnab hHA
    (by rw [hidx]; exact hq)
  have hmodel : IsPSL 3 2 1 ρ0.range :=
    isPSL_three_two_of_perm_seven hcardG ρ0.range.subtype (Subgroup.subtype_injective _)
      (fun i j => by
        obtain ⟨y, hy⟩ := htr i j
        exact ⟨⟨ρ0 y, y, rfl⟩, hy⟩)
  exact ⟨IsPSL.of_mulEquiv (Subgroup.topEquiv.symm.trans e'.symm) hmodel, hiso⟩

end CFSG.Quasithin.A312Ru
