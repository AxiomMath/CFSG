module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxGen

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

section Cyclic

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem isCyclic_quotient_of_cyclicMod {A C : Subgroup G} (hA : IsMulCommutative A) (hCA : C ≤ A)
    (h : CyclicMod A C) : IsCyclic (A ⧸ C.subgroupOf A) := by
  obtain ⟨a, ha, hle⟩ := h
  refine ⟨⟨QuotientGroup.mk ⟨a, ha⟩, fun x => ?_⟩⟩
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hcomm : ∀ c ∈ C, ∀ l ∈ Subgroup.zpowers a, Commute c l := fun c hc l hl =>
    Sec6Gen.commute_of_mem_comm hA (hCA hc) ((Subgroup.zpowers_le.mpr ha) hl)
  obtain ⟨c, hc, l, hl, hcl⟩ := (mem_sup_iff_of_commute hcomm).mp (hle hy)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hai : a ^ i ∈ A := zpow_mem ha i
  have : ((⟨a, ha⟩ : A) ^ i)⁻¹ * ⟨y, hy⟩ = ⟨c, hCA hc⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [← hcl]
    have hc' := Sec6Gen.commute_of_mem_comm hA (hCA hc) hai
    rw [hc'.eq]
    group
  rw [this]
  exact hc


theorem exists_card_sq_between {p : ℕ} (hp : p.Prime) {A C F : Subgroup G}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) (hCA : C ≤ A) (hFC : F ≤ C)
    (hF : Nat.card F = p) (hcyc : CyclicMod A C) :
    ∃ B : Subgroup G, B ≤ C ∧ F ≤ B ∧ Nat.card B = p ^ 2 := by
  have := Fact.mk hp
  have : IsMulCommutative A := hA.1
  have hcyc' := isCyclic_quotient_of_cyclicMod hA.1 hCA hcyc
  have hdvd : p ^ (1 + 1) ∣ Nat.card C := by
    rcases (CFSG.SignalizerFunctorTheorem.McBride.isCyclic_quotient_iff_of_isElemAbelian hp hA
      hCA).mp hcyc' with h | ⟨-, h⟩
    · rw [h, hAc]
      exact pow_dvd_pow p (by norm_num)
    · rw [hAc] at h
      have h' : p * Nat.card C = p * p ^ 2 := by rw [← pow_succ']; exact h.symm
      rw [Nat.eq_of_mul_eq_mul_left hp.pos h']
  have hH : Nat.card ↥(F.subgroupOf C) = p ^ 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hF, pow_one]
  obtain ⟨K, hK, hFK⟩ := Sylow.exists_subgroup_card_pow_succ (G := ↥C) (p := p) (n := 1) hdvd hH
  refine ⟨K.map C.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hFC]
    exact Subgroup.map_mono hFK
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hK]


end Cyclic

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_rSetN_two_ge_of_one
    (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ rSetN p A θ 1) : ∃ B ∈ rSetN p A θ 2, F ≤ B := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hFr, hFcard⟩ := hF
  have hFcard' : Nat.card F = p := by simpa using hFcard
  obtain ⟨hF1, hFA, -⟩ := h.mem_rSet_iff.mp hFr
  obtain ⟨hHm, P, hP⟩ := hFr.2.2
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hZ, hZ₂s, hcyc⟩ :=
    exists_solvable_pair hθ h.bot_mem_dset (X₁ := P.1) (X₂ := P.2) hP.1
  have hZm₁ : Z₁ ∈ mhat p A θ := hZ.1.1
  have hZm₂ : Z₂ ∈ mhat p A θ := hZ.1.2.1
  have hAZ₁ : A ≤ Subgroup.normalizer (Z₁ : Set G) := hZm₁.1.1
  have hAZ₂ : A ≤ Subgroup.normalizer (Z₂ : Set G) := hZm₂.1.1
  have hZ₁H : Z₁ ≤ thetaOf θ F := hZ₁.trans hP.2
  have hFC : F ≤ secCenIn A Z₁ Z₂ := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      exact one_mem _
    refine Subgroup.mem_inf.mpr ⟨hFA hf, hAZ₂ (hFA hf), hAZ₁ (hFA hf), fun y hy => ?_⟩
    have hyθ : y ∈ θ f := thetaOf_le_apply hf hf1 (hZ₁H hy)
    have hyc : y ∈ Subgroup.centralizer {f} := hθ.isFunctor.le_centralizer f (hFA hf) hf1 hyθ
    have : f * y = y * f := (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact one_mem _
  obtain ⟨B, hBC, hFB, hBc⟩ := exists_card_sq_between hθ.prime hθ.elemAbelian
    (by rw [h.hyp.card]) (inf_le_left : secCenIn A Z₁ Z₂ ≤ A) hFC hFcard' hcyc
  have hBA : B ≤ A := hBC.trans inf_le_left
  have hB1 : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hBc
    exact (Nat.one_lt_pow (by norm_num) hθ.prime.one_lt : 1 < p ^ 2).ne hBc
  refine ⟨B, h.mem_rSetN_iff.mpr ⟨hB1, hBA, fun hsolB => ?_, hBc⟩, hFB⟩
  have hZ₁ns : ¬ Group.IsSolvable ↥Z₁ := by
    intro hs
    have hPYX := h.mem_pairsYX_bot hZ.1 (X := thetaOf θ F) hZ₁H
    have hiP : (Z₁, Z₂) ∈ iPairs A (thetaOf θ F) := by
      have : (Z₁, Z₂) ∈ iPairsY A (thetaOf θ F) ⊥ := by
        rw [← pairsYX_eq_iPairsY hθ hHm]
        exact hPYX
      exact this.1
    obtain ⟨n, hn⟩ := hs.solvable
    exact Thm33a.not_isSolvableSection_of_mem_iPairs hiP ⟨n, (le_of_eq hn).trans bot_le⟩
  have hCzH : Z₁ ⊓ Subgroup.centralizer (B : Set G) ≤ thetaOf θ B := by
    refine le_thetaOf_iff.mpr fun b hb hb1 => ?_
    exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))).trans
      (hZm₁.1.2.2.1 b (hBA hb) hb1)
  have hBelem : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hθ.elemAbelian hBA
  have hfact := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p
    hθ.prime B Z₁ (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B hBelem)
    (hBA.trans hAZ₁) hZm₁.1.2.1
  have hcomm : ⁅Z₁, B⁆ ≤ Z₂ := by
    refine Subgroup.commutator_le.mpr fun z hz b hb => ?_
    have h1 : ⁅b, z⁆ ∈ Z₂ := (Subgroup.mem_inf.mp (hBC hb)).2.2.2 z hz
    rw [← commutatorElement_inv]
    exact inv_mem h1
  have hZ₂N : Z₁ ≤ Subgroup.normalizer (Z₂ : Set G) := le_sup_left.trans
    (le_sup_left.trans hZ.1.2.2.1.1.2)
  have hCzsol : Group.IsSolvable ↥(Z₁ ⊓ Subgroup.centralizer (B : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hCzH) (by
      have := hsolB
      exact Subgroup.inclusion_injective hCzH)
  have hZ₂adm : Admits (Z₁ ⊓ Subgroup.centralizer (B : Set G)) Z₂ := inf_le_left.trans hZ₂N
  have hsolsup : Group.IsSolvable ↥(Z₂ ⊔ Z₁ ⊓ Subgroup.centralizer (B : Set G)) :=
    AssocSup.isSolvable_sup hZ₂adm hCzsol hZ₂s
  have hle : Z₁ ≤ Z₂ ⊔ Z₁ ⊓ Subgroup.centralizer (B : Set G) := by
    calc Z₁ = ⁅Z₁, B⁆ ⊔ Z₁ ⊓ Subgroup.centralizer (B : Set G) := hfact.symm
      _ ≤ _ := sup_le_sup_right hcomm _
  have := hsolsup
  exact hZ₁ns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))


theorem exists_rSetN_two_ge
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    ∃ B₂ ∈ rSetN p A θ 2, B ≤ B₂ := by
  rcases h.card_of_mem_rSet hB with hc | hc
  · exact h.exists_rSetN_two_ge_of_one ⟨hB, hc.trans (pow_one p).symm⟩
  · exact ⟨B, ⟨hB, hc⟩, le_rfl⟩

theorem rSetN_two_nonempty_aux
    (h : Counterexample p A θ) : (rSetN p A θ 2).Nonempty := by
  obtain ⟨a, ha, ha1, hns⟩ := h.exists_not_solvable
  obtain ⟨B, hB, -⟩ := h.exists_rSetN_two_ge_of_one
    ((h.zpowers_mem_rSetN_one_iff).mpr ⟨ha, ha1, hns⟩)
  exact ⟨B, hB⟩

omit [Finite G] in
theorem card_eq_mul_relIndex {A H : Subgroup G} (hHA : H ≤ A) :
    Nat.card A = Nat.card H * H.relIndex A := by
  rw [← Subgroup.card_mul_index (H.subgroupOf A),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv]
  rfl

omit [Finite G] in
theorem inf_ne_bot_of_card_sq {A H K : Subgroup G} (hAc : Nat.card A = p ^ 3) (hH : H ≤ A)
    (hK : K ≤ A) (hHc : Nat.card H = p ^ 2) (hKc : Nat.card K = p ^ 2) (hp : p.Prime) :
    H ⊓ K ≠ ⊥ := by
  have hp0 : 0 < p := hp.pos
  have e1 := card_eq_mul_relIndex hH
  have e2 := card_eq_mul_relIndex hK
  have e3 := card_eq_mul_relIndex (inf_le_left.trans hH : H ⊓ K ≤ A)
  have h1 : H.relIndex A = p := by
    rw [hAc, hHc] at e1
    have : p ^ 2 * p = p ^ 2 * H.relIndex A := by rw [← pow_succ]; exact e1
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) this).symm
  have h2 : K.relIndex A = p := by
    rw [hAc, hKc] at e2
    have : p ^ 2 * p = p ^ 2 * K.relIndex A := by rw [← pow_succ]; exact e2
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) this).symm
  have hle := Subgroup.relIndex_inf_le (H := H) (K := K) (L := A)
  rw [h1, h2] at hle
  intro hbot
  rw [hbot] at hle e3
  rw [Subgroup.card_bot, hAc, one_mul] at e3
  have : p ^ 3 ≤ p * p := by rw [e3]; exact hle
  have hp2 : 2 ≤ p := hp.two_le
  nlinarith

theorem inf_kOf_eq_of_le
    (h : Counterexample p A θ) {E F : Subgroup G} (hE : E ∈ rSet p A θ)
    (hF : F ∈ rSet p A θ) (hEF : E ≤ F) :
    dsub A θ ⊓ kOf (thetaOf θ E) = dsub A θ ⊓ kOf (thetaOf θ F) := by
  have hθ := h.hyp.nearFunctor
  have hEm := (h.mem_rSet_iff.mp hE)
  have hFm := (h.mem_rSet_iff.mp hF)
  have hXE : thetaOf θ E ∈ cset p A θ ⊥ := hE.2.2
  have hXF : thetaOf θ F ∈ cset p A θ ⊥ := hF.2.2
  have hKFE : kOf (thetaOf θ F) ≤ kOf (thetaOf θ E) := by
    have h1 : kOf (thetaOf θ F) ≤ perfRes (thetaOf θ E) :=
      Nonsolvable.le_perfectResidual_map_of_isPerfect (h.isPerfect_kOf hXF)
        ((kOf_le _).trans (thetaOf_anti hEF))
    exact h1.trans (h.perfRes_eq_kOf hXE).le
  by_cases hEeq : E = F
  · rw [hEeq]
  refine le_antisymm (le_inf inf_le_left ?_) (inf_le_inf_left _ hKFE)
  have hcard : Nat.card E = p ∧ Nat.card F = p ^ 2 := by
    rcases h.card_of_mem_rSet hE with hc | hc <;> rcases h.card_of_mem_rSet hF with hc' | hc'
    · exact absurd (Subgroup.eq_of_le_of_card_ge hEF (by rw [hc, hc'])) hEeq
    · exact ⟨hc, hc'⟩
    · exfalso
      have := Subgroup.card_le_of_le hEF
      rw [hc, hc'] at this
      have h1 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hθ.prime.one_lt (by norm_num)
      rw [pow_one] at h1
      omega
    · exact absurd (Subgroup.eq_of_le_of_card_ge hEF (by rw [hc, hc'])) hEeq
  have hEA : E ∈ signalizerFunctorEk p 1 A := ⟨hEm.2.1, by rw [hcard.1, pow_one]⟩
  obtain ⟨a, ha, ha1, hza⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one hθ.prime hEA
  have hnle : ¬ F ≤ E := fun hle => hEeq (le_antisymm hEF hle)
  obtain ⟨b, hbF, hbE⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hbA : b ∈ A := hFm.2.1 hbF
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem _)
  have hbna : b ∉ Subgroup.zpowers a := hza ▸ hbE
  have hza1 := zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian ha ha1
  have hzb1 := zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian hbA hb1
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hθ.prime (by rw [hzb1.2, pow_one])
      (fun hle => hbna (hle (Subgroup.mem_zpowers b)))
  have hsup : Subgroup.zpowers a ⊔ Subgroup.zpowers b ∈ signalizerFunctorEk p 2 A := by
    simpa using CFSG.SignalizerFunctorTheorem.sup_mem_Ek_succ hθ.elemAbelian hza1 hzb1 hdisj
  have hFeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = F :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hza ▸ hEF) (Subgroup.zpowers_le.mpr hbF))
      (by rw [hcard.2, hsup.2])
  have hHE : thetaOf θ E = θ a := by rw [← hza]; exact hθ.isFunctor.thetaOf_zpowers ha ha1
  have key := kOf_apply_inf_centralizer_le hθ ha ha1 hbA hb1
  rw [hFeq] at key
  intro x hx
  refine key ⟨?_, ?_⟩
  · rw [← hHE]
    exact hx.2
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
      (dsub_le_centralizer hθ hx.1)

theorem inf_kOf_eq_of_mem_rSet
    (h : Counterexample p A θ) {B B' : Subgroup G}
    (hB : B ∈ rSet p A θ) (hB' : B' ∈ rSet p A θ) :
    dsub A θ ⊓ kOf (thetaOf θ B) = dsub A θ ⊓ kOf (thetaOf θ B') := by
  obtain ⟨B₂, hB₂, hBB₂⟩ := h.exists_rSetN_two_ge hB
  obtain ⟨B₂', hB₂', hB'B₂'⟩ := h.exists_rSetN_two_ge hB'
  have hC : B₂ ⊓ B₂' ≠ ⊥ := by
    obtain ⟨-, hBA, -, hc⟩ := h.mem_rSetN_iff.mp hB₂
    obtain ⟨-, hBA', -, hc'⟩ := h.mem_rSetN_iff.mp hB₂'
    exact inf_ne_bot_of_card_sq h.hyp.card hBA hBA' hc hc' h.hyp.prime
  have hCr : B₂ ⊓ B₂' ∈ rSet p A θ := h.rSet_mono hB₂.1 inf_le_left hC
  calc dsub A θ ⊓ kOf (thetaOf θ B) = dsub A θ ⊓ kOf (thetaOf θ B₂) :=
        h.inf_kOf_eq_of_le hB hB₂.1 hBB₂
    _ = dsub A θ ⊓ kOf (thetaOf θ (B₂ ⊓ B₂')) := (h.inf_kOf_eq_of_le hCr hB₂.1 inf_le_left).symm
    _ = dsub A θ ⊓ kOf (thetaOf θ B₂') := h.inf_kOf_eq_of_le hCr hB₂'.1 inf_le_right
    _ = dsub A θ ⊓ kOf (thetaOf θ B') := (h.inf_kOf_eq_of_le hB' hB₂'.1 hB'B₂').symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
