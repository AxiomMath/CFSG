module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211CGrp
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.Quasithin.Background.HZCode22B
public import CFSG.Quasithin.Background.HZCoc24C

public section

namespace CFSG.Quasithin.H13.L8211CRow

open CFSG.Quasithin.H13.L8211C

noncomputable def imgEquiv22 :
    ↥(CFSG.Quasithin.H.Code22.imgC CFSG.Quasithin.H.Code22.L22) ≃*
      ↥CFSG.Quasithin.H.Code22.L22 := by
  unfold CFSG.Quasithin.H.Code22.imgC
  exact (Subgroup.equivMapOfInjective _ _
      CFSG.Quasithin.H.ModelType.rhoC10_mog22_injective).symm.trans
    (Subgroup.subgroupOfEquivOfLe CFSG.Quasithin.H.Code22.L22_le)

noncomputable def imgEquiv24 :
    ↥(CFSG.Quasithin.H.Mathieu.img11 CFSG.Quasithin.H.Coc24.Lz) ≃*
      ↥CFSG.Quasithin.H.Coc24.Lz := by
  unfold CFSG.Quasithin.H.Mathieu.img11
  exact (Subgroup.equivMapOfInjective _ _
      (CFSG.Quasithin.H.Mathieu.rho11_injective CFSG.Monster.Code.AutPerm le_rfl)).symm.trans
    (Subgroup.subgroupOfEquivOfLe CFSG.Quasithin.H.Coc24.Lz_le)

theorem isQS_of_perfect_surj_alt6 {G : Type} [Group G] {P : Subgroup G}
    (hPp : ⁅P, P⁆ = P) (f : ↥P →* ↥(alternatingGroup (Fin 6)))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] : IsQS ↥P := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact isQS_of_surjective f hf (perfect_top_subgroup hPp) (isQS_of_isSimpleGroup _)

theorem isSolvable_of_normal_pgroup_index_three {N : Type} [Group N] [Finite N]
    (O : Subgroup N) [O.Normal] (hO : IsPGroup 2 ↥O) (hcard : Nat.card N = 3 * Nat.card O) :
    Group.IsSolvable N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpos : 0 < Nat.card O := Nat.card_pos
  have hq : Nat.card (N ⧸ O) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup O
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos h.symm
  have hQ : IsPGroup 3 (N ⧸ O) := IsPGroup.iff_card.mpr ⟨1, by rw [hq]; norm_num⟩
  haveI : Group.IsNilpotent (N ⧸ O) := hQ.isNilpotent
  haveI : Group.IsNilpotent ↥O := hO.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient O

theorem isSolvable_colLz_ker :
    Group.IsSolvable ↥CFSG.Quasithin.H.Coc24.colLz.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : CFSG.Quasithin.H.Coc24.colLz.range = alternatingGroup (Fin 6) :=
    CFSG.Quasithin.H.Coc24.range_colLz.trans CFSG.Quasithin.H.Coc24.A6c_eq
  have hON : CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz ≤ CFSG.Quasithin.H.Coc24.colLz.ker :=
    CFSG.Quasithin.H.Code22.pCore_le_ker_of_range_eq _ hrange
  have hNcard : Nat.card ↥CFSG.Quasithin.H.Coc24.colLz.ker = 192 :=
    CFSG.Quasithin.H.Coc24.card_ker_colLz
  have hO64 : Nat.card ↥(CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz) = 64 := by
    have h1 : Nat.card ↥(CFSG.Open.pCoreOf 2 CFSG.Quasithin.H.Coc24.Lz) = 64 := by
      rw [CFSG.Quasithin.H.Coc24.pCoreOf_Lz, CFSG.Quasithin.H.Coc24.card_KSp]
    unfold CFSG.Open.pCoreOf at h1
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
  haveI hOn' : (CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz).Normal :=
    CFSG.LieType.BorelTits.pCore_normal 2
  have hOp : IsPGroup 2 ↥(CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz) :=
    CFSG.LieType.BorelTits.pCore_isPGroup 2
  haveI hOn : ((CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz).subgroupOf
      CFSG.Quasithin.H.Coc24.colLz.ker).Normal :=
    Subgroup.Normal.subgroupOf hOn' _
  have hOcard : Nat.card ↥((CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz).subgroupOf
      CFSG.Quasithin.H.Coc24.colLz.ker) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv, hO64]
  have hOp' : IsPGroup 2 ↥((CFSG.pCore 2 ↥CFSG.Quasithin.H.Coc24.Lz).subgroupOf
      CFSG.Quasithin.H.Coc24.colLz.ker) := by
    refine IsPGroup.iff_card.mpr ⟨6, ?_⟩
    rw [hOcard]
    norm_num
  exact isSolvable_of_normal_pgroup_index_three _ hOp' (by rw [hNcard, hOcard])

theorem isQS_parz22 {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (h : CFSG.Quasithin.MathieuCode22 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    (hS : CFSG.Quasithin.H13.IsSylowVec82 H z) :
    Nontrivial ↥(CFSG.Quasithin.H13.parz82 H z) ∧ IsQS ↥(CFSG.Quasithin.H13.parz82 H z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut V) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z
  obtain ⟨S, hSH, hS', hzS⟩ := hS
  obtain ⟨e, he, hez⟩ := CFSG.Quasithin.H.Code22.exists_equiv_z0 h hz1 hSH hS' hzS
  have h1 : (CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e) =
      CFSG.Quasithin.H.Code22.imgC CFSG.Quasithin.H.Code22.L22 := by
    rw [← CFSG.Quasithin.H.Code22.parZ_std, ← he, ← hez]
    exact CFSG.Quasithin.H.ZTrans.parZ_map e H z
  let e1 : ↥(CFSG.Quasithin.H13.parz82 H z) ≃*
      ↥((CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e)) :=
    Subgroup.equivMapOfInjective _ _ (CFSG.Quasithin.H.congrHom_injective e)
  let e2 : ↥((CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e)) ≃*
      ↥(CFSG.Quasithin.H.Code22.imgC CFSG.Quasithin.H.Code22.L22) :=
    MulEquiv.subgroupCongr h1
  let β : ↥(CFSG.Quasithin.H13.parz82 H z) ≃* ↥CFSG.Quasithin.H.Code22.L22 :=
    e1.trans (e2.trans imgEquiv22)
  have hA : ∀ x : ↥CFSG.Quasithin.H.Code22.L22,
      CFSG.Quasithin.H.Code22.hexL22 x ∈ alternatingGroup (Fin 6) := by
    intro x
    rw [← CFSG.Quasithin.H.Coc24.A6c_eq, ← CFSG.Quasithin.H.Code22.range_hexL22]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let f0 : ↥(CFSG.Quasithin.H13.parz82 H z) →* Equiv.Perm (Fin 6) :=
    CFSG.Quasithin.H.Code22.hexL22.comp β.toMonoidHom
  let f : ↥(CFSG.Quasithin.H13.parz82 H z) →* ↥(alternatingGroup (Fin 6)) :=
    f0.codRestrict (alternatingGroup (Fin 6)) (fun p => hA (β p))
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ CFSG.Quasithin.H.Code22.hexL22.range := by
      rw [CFSG.Quasithin.H.Code22.range_hexL22, CFSG.Quasithin.H.Coc24.A6c_eq]
      exact hy
    obtain ⟨x, hx⟩ := hy'
    obtain ⟨p, rfl⟩ := β.surjective x
    exact ⟨p, Subtype.ext hx⟩
  have hK : IsPGroup 2 ↥CFSG.Quasithin.H.Code22.hexL22.ker := by
    refine IsPGroup.iff_card.mpr ⟨4, ?_⟩
    rw [CFSG.Quasithin.H.Code22.card_ker_hexL22]
    norm_num
  have hφ : ∀ x : ↥f.ker, β x.1 ∈ CFSG.Quasithin.H.Code22.hexL22.ker := by
    intro x
    have hx : f x.1 = 1 := MonoidHom.mem_ker.mp x.2
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  let φ : ↥f.ker →* ↥CFSG.Quasithin.H.Code22.hexL22.ker :=
    (β.toMonoidHom.comp f.ker.subtype).codRestrict _ hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h2 : β a.1 = β b.1 := congrArg Subtype.val hab
    exact Subtype.ext (β.injective h2)
  have hker : IsPGroup 2 ↥f.ker := hK.of_injective φ hφinj
  haveI : Group.IsNilpotent ↥f.ker := hker.isNilpotent
  have hperf : ⁅CFSG.Quasithin.H13.parz82 H z, CFSG.Quasithin.H13.parz82 H z⁆ =
      CFSG.Quasithin.H13.parz82 H z :=
    CFSG.Quasithin.perfectCore_perfect _
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨hf.nontrivial, isQS_of_perfect_surj_alt6 hperf f hf⟩

theorem isQS_parz24 {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (h : CFSG.Quasithin.MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    (hS : CFSG.Quasithin.H13.IsSylowVec82 H z) :
    Nontrivial ↥(CFSG.Quasithin.H13.parz82 H z) ∧ IsQS ↥(CFSG.Quasithin.H13.parz82 H z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut V) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z
  obtain ⟨S, hSH, hS', hzS⟩ := hS
  obtain ⟨e, he, hez⟩ := CFSG.Quasithin.H.Coc24.exists_equiv_z0 h hz1 hSH hS' hzS
  have h1 : (CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e) =
      CFSG.Quasithin.H.Mathieu.img11 CFSG.Quasithin.H.Coc24.Lz := by
    rw [← CFSG.Quasithin.H.Coc24.parZ_std, ← he, ← hez]
    exact CFSG.Quasithin.H.ZTrans.parZ_map e H z
  let e1 : ↥(CFSG.Quasithin.H13.parz82 H z) ≃*
      ↥((CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e)) :=
    Subgroup.equivMapOfInjective _ _ (CFSG.Quasithin.H.congrHom_injective e)
  let e2 : ↥((CFSG.Quasithin.H13.parz82 H z).map (CFSG.Quasithin.H.congrHom e)) ≃*
      ↥(CFSG.Quasithin.H.Mathieu.img11 CFSG.Quasithin.H.Coc24.Lz) :=
    MulEquiv.subgroupCongr h1
  let β : ↥(CFSG.Quasithin.H13.parz82 H z) ≃* ↥CFSG.Quasithin.H.Coc24.Lz :=
    e1.trans (e2.trans imgEquiv24)
  have hA : ∀ x : ↥CFSG.Quasithin.H.Coc24.Lz,
      CFSG.Quasithin.H.Coc24.colLz x ∈ alternatingGroup (Fin 6) := by
    intro x
    rw [← CFSG.Quasithin.H.Coc24.A6c_eq, ← CFSG.Quasithin.H.Coc24.range_colLz]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let f0 : ↥(CFSG.Quasithin.H13.parz82 H z) →* Equiv.Perm (Fin 6) :=
    CFSG.Quasithin.H.Coc24.colLz.comp β.toMonoidHom
  let f : ↥(CFSG.Quasithin.H13.parz82 H z) →* ↥(alternatingGroup (Fin 6)) :=
    f0.codRestrict (alternatingGroup (Fin 6)) (fun p => hA (β p))
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ CFSG.Quasithin.H.Coc24.colLz.range := by
      rw [CFSG.Quasithin.H.Coc24.range_colLz, CFSG.Quasithin.H.Coc24.A6c_eq]
      exact hy
    obtain ⟨x, hx⟩ := hy'
    obtain ⟨p, rfl⟩ := β.surjective x
    exact ⟨p, Subtype.ext hx⟩
  haveI : Group.IsSolvable ↥CFSG.Quasithin.H.Coc24.colLz.ker := isSolvable_colLz_ker
  have hφ : ∀ x : ↥f.ker, β x.1 ∈ CFSG.Quasithin.H.Coc24.colLz.ker := by
    intro x
    have hx : f x.1 = 1 := MonoidHom.mem_ker.mp x.2
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  let φ : ↥f.ker →* ↥CFSG.Quasithin.H.Coc24.colLz.ker :=
    (β.toMonoidHom.comp f.ker.subtype).codRestrict _ hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h2 : β a.1 = β b.1 := congrArg Subtype.val hab
    exact Subtype.ext (β.injective h2)
  haveI : Group.IsSolvable ↥f.ker := Group.isSolvable_of_isSolvable_injective hφinj
  have hperf : ⁅CFSG.Quasithin.H13.parz82 H z, CFSG.Quasithin.H13.parz82 H z⁆ =
      CFSG.Quasithin.H13.parz82 H z :=
    CFSG.Quasithin.perfectCore_perfect _
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨hf.nontrivial, isQS_of_perfect_surj_alt6 hperf f hf⟩

end CFSG.Quasithin.H13.L8211CRow
