module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxK
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Glauberman
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type*} [Group Γ]

theorem isPGroup_zpowers {p : ℕ} {b : Γ} (hbp : b ^ p = 1) :
    IsPGroup p (Subgroup.zpowers b) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  have : (g : Γ) ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  simpa using this

theorem centralizer_zpowers_eq (b : Γ) :
    Subgroup.centralizer (Subgroup.zpowers b : Set Γ) = Subgroup.centralizer {b} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem zpowers_eq_of_mem_zpowers [Finite Γ] {p : ℕ} (hp : p.Prime) {b a : Γ} (hbp : b ^ p = 1)
    (hb1 : b ≠ 1) (ha : a ∈ Subgroup.zpowers b) (ha1 : a ≠ 1) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : orderOf b = p := orderOf_eq_prime hbp hb1
  have hap : a ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  have ha' : orderOf a = p := orderOf_eq_prime hap ha1
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · exact Subgroup.zpowers_le.mpr ha
  · rw [Nat.card_zpowers, Nat.card_zpowers, ha', hb]

theorem zpowers_inf_normalizer_eq_bot [Finite Γ] {p : ℕ} (hp : p.Prime) {b : Γ}
    {J : Subgroup Γ}
    (hbp : b ^ p = 1) (hbJ : b ∉ Subgroup.normalizer (J : Set Γ)) :
    Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ := by
  have hb1 : b ≠ 1 := fun h => hbJ (h ▸ one_mem _)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
  by_contra ha1
  obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
  refine hbJ ?_
  have heq := zpowers_eq_of_mem_zpowers hp hbp hb1 haA ha1
  have h2 : Subgroup.zpowers a ≤ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.mpr haN
  exact h2 (by rw [heq]; exact Subgroup.mem_zpowers b)

theorem map_conj_map_conj (J : Subgroup Γ) (a c : Γ) :
    (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      J.map (MulAut.conj (a * c)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem conj_mem_orbitClosure {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) {x : Γ}
    (hx : x ∈ orbitClosure J A) : a * x * a⁻¹ ∈ orbitClosure J A := by
  have h : orbitClosure J A ≤ (orbitClosure J A).comap (MulAut.conj a).toMonoidHom := by
    refine orbitClosure_le fun c hc => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem ha hc)
  exact h hx

theorem mem_normalizer_orbitClosure {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_orbitClosure ha, fun hx => ?_⟩
  have := conj_mem_orbitClosure (inv_mem ha) hx
  rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at this

section Finite

variable [Finite Γ] {p : ℕ} {Z : Subgroup Γ} {b : Γ}

theorem orbitClosure_le_kOf {A J : Subgroup Γ} (hsol : sol Z = ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set Γ)) (hJ : J ∈ lcal Z) : orbitClosure J A ≤ kOf Z :=
  orbitClosure_le fun _ ha => (isDirectProduct_lcal_kOf hsol).le (map_conj_mem_lcal hJ (hAZ ha))

theorem kOf_le_normalizer_orbitClosure {A J : Subgroup Γ} (hsol : sol Z = ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set Γ)) (hJ : J ∈ lcal Z) :
    kOf Z ≤ Subgroup.normalizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  unfold orbitClosure
  refine le_normalizer_iSup _ fun a => le_normalizer_iSup _ fun ha => ?_
  exact (isDirectProduct_lcal_kOf hsol).le_normalizer (map_conj_mem_lcal hJ (hAZ ha))

theorem inf_centralizer_eq_iSup_of_finite {ι : Type*} [Finite ι] (hp : p.Prime) {A K : Subgroup Γ}
    (hA : IsPGroup p A) (hK : Nat.Coprime p (Nat.card K)) (K' : ι → Subgroup Γ)
    (hinv : ∀ i, A ≤ Subgroup.normalizer (K' i : Set Γ))
    (hperm : ∀ i j, (K' i : Set Γ) * K' j = K' j * K' i) (hgen : ⨆ i, K' i = K) :
    K ⊓ Subgroup.centralizer (A : Set Γ) = ⨆ i, K' i ⊓ Subgroup.centralizer (A : Set Γ) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have h := centralizer_eq_iSup_centralizer hp hA hK (fun i : Fin n => K' (e.symm i))
    (fun i => hinv _) (fun i j => hperm _ _) (by rw [Equiv.iSup_comp e.symm]; exact hgen)
  rw [h]
  exact Equiv.iSup_comp e.symm (g := fun i => K' i ⊓ Subgroup.centralizer (A : Set Γ))

theorem kOf_inf_centralizer_le_iSup_smear (hp : p.Prime) (hsol : sol Z = ⊥)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hbp : b ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card Z)) :
    kOf Z ⊓ Subgroup.centralizer {b} ≤ ⨆ J ∈ lcal Z, smear J (Subgroup.zpowers b) := by
  set A := Subgroup.zpowers b with hA
  have hAZ : A ≤ Subgroup.normalizer (Z : Set Γ) := Subgroup.zpowers_le.mpr hbZ
  have hdp := isDirectProduct_lcal_kOf hsol
  have hKcop : Nat.Coprime p (Nat.card (kOf Z)) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le Z))
  let K' : ↥(lcal Z) → Subgroup Γ := fun J => orbitClosure J.1 A
  have hinv : ∀ J, A ≤ Subgroup.normalizer (K' J : Set Γ) := fun J a ha =>
    mem_normalizer_orbitClosure ha
  have hperm : ∀ i j, (K' i : Set Γ) * K' j = K' j * K' i := by
    intro i j
    have hi := kOf_le_normalizer_orbitClosure (A := A) hsol hAZ i.2
    have hj := kOf_le_normalizer_orbitClosure (A := A) hsol hAZ j.2
    have hiK : K' i ≤ kOf Z := orbitClosure_le_kOf hsol hAZ i.2
    have hjK : K' j ≤ kOf Z := orbitClosure_le_kOf hsol hAZ j.2
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (K' i) (K' j) (hjK.trans hi),
      ← Subgroup.coe_mul_of_right_le_normalizer_left (K' j) (K' i) (hiK.trans hj), sup_comm]
  have hgen : (⨆ J : ↥(lcal Z), K' J) = kOf Z := by
    refine le_antisymm (iSup_le fun J => orbitClosure_le_kOf hsol hAZ J.2) ?_
    rw [← hdp.sSup_eq]
    exact sSup_le fun J hJ => (le_orbitClosure J A).trans
      (le_iSup (fun J : ↥(lcal Z) => K' J) ⟨J, hJ⟩)
  have h := inf_centralizer_eq_iSup_of_finite hp (isPGroup_zpowers hbp) hKcop K' hinv hperm hgen
  rw [centralizer_zpowers_eq] at h
  rw [h]
  refine iSup_le fun J => le_iSup₂_of_le J.1 J.2 ?_
  show orbitClosure J.1 A ⊓ Subgroup.centralizer {b} ≤ smear J.1 A
  rw [smear, hA, centralizer_zpowers_eq]

theorem smear_le_inf_centralizer {J : Subgroup Γ} (hsol : sol Z = ⊥)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hJ : J ∈ lcal Z) :
    smear J (Subgroup.zpowers b) ≤ Z ⊓ Subgroup.centralizer {b} := by
  refine le_inf ?_ ?_
  · exact (smear_le_orbitClosure J _).trans
      ((orbitClosure_le_kOf hsol (Subgroup.zpowers_le.mpr hbZ) hJ).trans (kOf_le Z))
  · rw [← centralizer_zpowers_eq]
    exact smear_le_centralizer J _

theorem isSubnormal_smear {J : Subgroup Γ} (hsol : sol Z = ⊥)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hJ : J ∈ lcal Z) :
    ((smear J (Subgroup.zpowers b)).subgroupOf (Z ⊓ Subgroup.centralizer {b})).IsSubnormal := by
  set A := Subgroup.zpowers b with hA
  have hAZ : A ≤ Subgroup.normalizer (Z : Set Γ) := Subgroup.zpowers_le.mpr hbZ
  have hUT : smear J A ≤ kOf Z ⊓ Subgroup.centralizer {b} := by
    refine le_inf ((smear_le_orbitClosure J A).trans (orbitClosure_le_kOf hsol hAZ hJ)) ?_
    rw [← centralizer_zpowers_eq]
    exact smear_le_centralizer J A
  have hTC : kOf Z ⊓ Subgroup.centralizer {b} ≤ Z ⊓ Subgroup.centralizer {b} :=
    inf_le_inf_right _ (kOf_le Z)
  refine Thm52Aux.isSubnormal_subgroupOf_of_normal_chain hUT hTC ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff hUT]
    intro h k hh hk
    obtain ⟨hkK, hkc⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hhL, hhc⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (kOf_le_normalizer_orbitClosure hsol hAZ hJ hkK)
        h).mp hhL
    · rw [hA, centralizer_zpowers_eq] at hhc ⊢
      exact mul_mem (mul_mem hkc hhc) (inv_mem hkc)
  · rw [Subgroup.normal_subgroupOf_iff hTC]
    intro h k hh hk
    obtain ⟨hhK, hhc⟩ := Subgroup.mem_inf.mp hh
    obtain ⟨hkZ, hkc⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hkc hhc) (inv_mem hkc)⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf Z hkZ) h).mp hhK

theorem nonempty_mulEquiv_smear (hp : p.Prime)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hbp : b ^ p = 1) {J : Subgroup Γ}
    (hJ : J ∈ lcal Z) (hbJ : b ∉ Subgroup.normalizer (J : Set Γ)) :
    Nonempty (↥(smear J (Subgroup.zpowers b)) ≃* ↥J) := by
  set A := Subgroup.zpowers b with hA
  have hAZ : A ≤ Subgroup.normalizer (Z : Set Γ) := Subgroup.zpowers_le.mpr hbZ
  let S : Set (Subgroup Γ) := {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}
  have hL : IsDirectProduct S (orbitClosure J A) := isDirectProduct_orbit hAZ hJ
  have hAS : ∀ a ∈ A, ∀ K ∈ S, K.map (MulAut.conj a).toMonoidHom ∈ S := by
    rintro a ha _ ⟨a', ha', rfl⟩
    refine ⟨a * a', mul_mem ha ha', ?_⟩
    rw [map_conj_map_conj]
  have hJS : J ∈ S := ⟨1, one_mem A, by ext x; simp⟩
  have htrans : ∀ K ∈ S, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom := fun K hK => hK
  let ψ : ↥(smear J A) →* ↥J :=
    (hL.coord hJS).comp (Subgroup.inclusion (smear_le_orbitClosure J A))
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : Γ) ∈ sSup (S \ {J}) := (hL.coord_eq_one_iff hJS _).mp hy
    have h2 : (y : Γ) ∈ orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓ sSup (S \ {J}) :=
      Subgroup.mem_inf.mpr ⟨y.2, h1⟩
    rw [inf_centralizer_inf_sSup_eq_bot_of_transitive hL hAS hJS htrans, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective ψ := by
    intro j
    have hN : A ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ :=
      zpowers_inf_normalizer_eq_bot hp hbp hbJ
    have hj : (j : Γ) ∈ projIn S J (orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ)) := by
      rw [projIn_centralizer_eq hL hAS hJS, hN]
      refine Subgroup.mem_inf.mpr ⟨j.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh]
      simp
    obtain ⟨y, hy, hyj⟩ := (hL.mem_projIn_iff hJS).mp hj
    exact ⟨⟨y, hy⟩, Subtype.ext hyj⟩
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

theorem smear_le_kOf_inf_centralizer (hp : p.Prime) (hsol : sol Z = ⊥)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hbp : b ^ p = 1)
    (hfix : ∀ J ∈ lcal Z, b ∈ Subgroup.normalizer (J : Set Γ) → ¬ J ≤ Subgroup.centralizer {b} →
      Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b}))
    {J : Subgroup Γ} (hJ : J ∈ lcal Z) :
    smear J (Subgroup.zpowers b) ≤ kOf (Z ⊓ Subgroup.centralizer {b}) := by
  set A := Subgroup.zpowers b with hA
  have hsub := isSubnormal_smear hsol hbZ hJ
  have hUC := smear_le_inf_centralizer hsol hbZ hJ
  obtain ⟨hJZ, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  by_cases hbJ : b ∈ Subgroup.normalizer (J : Set Γ)
  · have hAJ : A ≤ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.mpr hbJ
    have hL : orbitClosure J A = J := by
      refine le_antisymm (orbitClosure_le fun a ha => ?_) (le_orbitClosure J A)
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAJ ha)).le
    have hU : smear J A = J ⊓ Subgroup.centralizer {b} := by
      rw [smear, hL, hA, centralizer_zpowers_eq]
    by_cases hc : J ≤ Subgroup.centralizer {b}
    · have hU' : smear J A = J := by rw [hU]; exact inf_eq_left.mpr hc
      rw [hU'] at hsub hUC ⊢
      exact le_kOf_of_mem_lcal (mem_lcal_iff.mpr ⟨hUC, hsub, hs, hnc⟩)
    · rw [hU] at hsub hUC ⊢
      exact le_kOf_of_isSubnormal_of_isSolvable hUC hsub (hfix J hJ hbJ hc)
  · obtain ⟨e⟩ := nonempty_mulEquiv_smear hp hbZ hbp hJ hbJ
    have hUs : IsSimpleGroup ↥(smear J A) := e.isSimpleGroup
    have hUnc : ¬ IsMulCommutative ↥(smear J A) := fun hc => hnc ((isMulCommutative_congr e).mp hc)
    exact le_kOf_of_mem_lcal (mem_lcal_iff.mpr ⟨hUC, hsub, hUs, hUnc⟩)

theorem kOf_inf_centralizer_le_kOf_inf_centralizer (hp : p.Prime) (hsol : sol Z = ⊥)
    (hbZ : b ∈ Subgroup.normalizer (Z : Set Γ)) (hbp : b ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card Z))
    (hfix : ∀ J ∈ lcal Z, b ∈ Subgroup.normalizer (J : Set Γ) → ¬ J ≤ Subgroup.centralizer {b} →
      Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b})) :
    kOf Z ⊓ Subgroup.centralizer {b} ≤ kOf (Z ⊓ Subgroup.centralizer {b}) :=
  (kOf_inf_centralizer_le_iSup_smear hp hsol hbZ hbp hcop).trans
    (iSup₂_le fun _ hJ => smear_le_kOf_inf_centralizer hp hsol hbZ hbp hfix hJ)

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux
