module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.Diagonal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.FixedPoint
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.HypA

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511

variable {Γ : Type*} [Group Γ]

abbrev Lgen (A G : Subgroup Γ) : Subgroup Γ :=
  ⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer ({a} : Set Γ))

theorem kOf_le_Lgen {A G : Subgroup Γ} {a : Γ} (ha : a ∈ A) (ha1 : a ≠ 1) :
    kOf (G ⊓ Subgroup.centralizer ({a} : Set Γ)) ≤ Lgen A G :=
  le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)

theorem commutator_mul_mul_eq {x y u v : Γ} (huy : Commute u y) (huv : Commute u v)
    (hvx : Commute v x) :
    x * u * (y * v) * (x * u)⁻¹ * (y * v)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc x * u * (y * v) * (x * u)⁻¹ * (y * v)⁻¹
      = x * (u * y) * v * u⁻¹ * x⁻¹ * v⁻¹ * y⁻¹ := by group
    _ = x * (y * u) * v * u⁻¹ * x⁻¹ * v⁻¹ * y⁻¹ := by rw [huy.eq]
    _ = x * y * (u * v) * u⁻¹ * x⁻¹ * v⁻¹ * y⁻¹ := by group
    _ = x * y * (v * u) * u⁻¹ * x⁻¹ * v⁻¹ * y⁻¹ := by rw [huv.eq]
    _ = x * y * v * x⁻¹ * v⁻¹ * y⁻¹ := by group
    _ = x * y * (v * x⁻¹) * v⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * v) * v⁻¹ * y⁻¹ := by rw [hvx.inv_right.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem le_of_normal_step {J L : Subgroup Γ} (hJs : IsSimpleGroup J)
    (hdiag : ∀ j ∈ J, ∃ l : Γ, (∀ x ∈ J, Commute x l) ∧ j * l ∈ L) (hne : L ⊓ J ≠ ⊥) :
    J ≤ L := by
  have hnorm : ((L ⊓ J).subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, hl, hgl⟩ := hdiag g g.2
    obtain ⟨hnL, hnJ⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
    have hcomm : l * (n : Γ) = (n : Γ) * l := (hl n n.2).eq.symm
    have h1 : (g : Γ) * n * (g : Γ)⁻¹ = ((g : Γ) * l) * n * ((g : Γ) * l)⁻¹ := by
      calc (g : Γ) * n * (g : Γ)⁻¹ = (g : Γ) * (n * l) * l⁻¹ * (g : Γ)⁻¹ := by group
        _ = (g : Γ) * (l * n) * l⁻¹ * (g : Γ)⁻¹ := by rw [hcomm]
        _ = ((g : Γ) * l) * n * ((g : Γ) * l)⁻¹ := by group
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · change (g : Γ) * n * (g : Γ)⁻¹ ∈ L
      rw [h1]
      exact mul_mem (mul_mem hgl hnL) (inv_mem hgl)
    · exact mul_mem (mul_mem g.2 hnJ) (inv_mem g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ J).subgroupOf J) with h | h
  · exfalso
    refine hne ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_)
    obtain ⟨hxL, hxJ⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxJ⟩ : J) ∈ (L ⊓ J).subgroupOf J := hx
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro x hx
    have hmem : (⟨x, hx⟩ : J) ∈ (L ⊓ J).subgroupOf J := by rw [h]; trivial
    exact (Subgroup.mem_inf.mp hmem).1

variable [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem le_Lgen_of_centralizes (hJ : J ∈ lcal G) {a : Γ} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hc : J ≤ Subgroup.centralizer ({a} : Set Γ)) : J ≤ Lgen A G :=
  (le_kOf_of_mem_lcal (mem_lcal_of_le hJ (le_inf (lcal_le hJ) hc) inf_le_left)).trans
    (kOf_le_Lgen haA ha1)

theorem le_Lgen_of_free (hp : p.Prime) (hA : IsElemAbelian p A)
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hmove : ∀ x ∈ A, x ≠ 1 → x ∉ Subgroup.normalizer (J : Set Γ)) {a b : Γ} (haA : a ∈ A)
    (hbA : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hind : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) : J ≤ Lgen A G := by
  have hap : a ^ p = 1 := hA.2 a haA
  have hbp : b ^ p = 1 := hA.2 b hbA
  have haG := hAG haA
  have hbG := hAG hbA
  have haJ := hmove a haA ha1
  have hbJ := hmove b hbA hb1
  obtain ⟨-, -, hJs', hJnc⟩ := mem_lcal_iff.mp hJ
  have hJs : IsSimpleGroup J := hJs'
  have hLa : smear J (Subgroup.zpowers a) ≤ Lgen A G :=
    (smear_le_kOf hp haG hap ha1 hsol hJ haJ).trans (kOf_le_Lgen haA ha1)
  have hLb : smear J (Subgroup.zpowers b) ≤ Lgen A G :=
    (smear_le_kOf hp hbG hbp hb1 hsol hJ hbJ).trans (kOf_le_Lgen hbA hb1)
  have hQa := isDirectProduct_orbitSet haG hJ
  have hQb := isDirectProduct_orbitSet hbG hJ
  have hJa := self_mem_orbitSet (Subgroup.zpowers a) J
  have hJb := self_mem_orbitSet (Subgroup.zpowers b) J
  have hK := isDirectProduct_lcal_kOf hsol
  have hSa : orbitSet (Subgroup.zpowers a) J ⊆ lcal G :=
    orbitSet_subset_lcal (Subgroup.zpowers_le.mpr haG) hJ
  have hSb : orbitSet (Subgroup.zpowers b) J ⊆ lcal G :=
    orbitSet_subset_lcal (Subgroup.zpowers_le.mpr hbG) hJ
  have hc3 : ∀ x ∈ sSup (orbitSet (Subgroup.zpowers a) J \ {J}),
      ∀ y ∈ sSup (orbitSet (Subgroup.zpowers b) J \ {J}), Commute x y := by
    refine commute_of_forall_commute_sSup fun K₁ hK₁ K₂ hK₂ x hx y hy => ?_
    have hne : K₁ ≠ K₂ := by
      obtain ⟨⟨u, hu, rfl⟩, hK₁J⟩ := hK₁
      obtain ⟨⟨w, hw, rfl⟩, -⟩ := hK₂
      intro heq
      have huA : u ∈ A := (Subgroup.zpowers_le.mpr haA) hu
      have hwA : w ∈ A := (Subgroup.zpowers_le.mpr hbA) hw
      have h1 : u⁻¹ * w = 1 := by
        by_contra h
        exact hmove _ (mul_mem (inv_mem huA) hwA) h (map_conj_eq_iff.mp heq)
      have huw : u = w := inv_mul_eq_one.mp h1
      have hu1 : u = 1 := by
        have : u ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := Subgroup.mem_inf.mpr ⟨hu, huw ▸ hw⟩
        rw [hind] at this
        exact Subgroup.mem_bot.mp this
      exact hK₁J (by rw [Set.mem_singleton_iff, hu1]; exact map_conj_one' J)
    exact hK.commute K₁ (hSa hK₁.1) K₂ (hSb hK₂.1) hne x hx y hy
  obtain ⟨j, hj, k, hk, hjk⟩ : ∃ j ∈ J, ∃ k ∈ J, j * k ≠ k * j := by
    by_contra hcon
    push Not at hcon
    exact hJnc (isMulCommutative_iff.mpr fun x y => Subtype.ext (hcon x x.2 y y.2))
  obtain ⟨la, hla, hja⟩ := exists_diag_lift hp haG hap ha1 hJ haJ hj
  obtain ⟨lb, hlb, hkb⟩ := exists_diag_lift hp hbG hbp hb1 hJ hbJ hk
  have hcomm := commutator_mul_mul_eq (x := j) (y := k) (u := la) (v := lb)
    (hQa.commute_sSup_diff hJa k hk la hla).symm (hc3 la hla lb hlb)
    (hQb.commute_sSup_diff hJb j hj lb hlb).symm
  have hdaL := hLa hja
  have hdbL := hLb hkb
  have hcL : j * k * j⁻¹ * k⁻¹ ∈ Lgen A G := by
    rw [← hcomm]
    exact mul_mem (mul_mem (mul_mem hdaL hdbL) (inv_mem hdaL)) (inv_mem hdbL)
  have hcJ : j * k * j⁻¹ * k⁻¹ ∈ J := mul_mem (mul_mem (mul_mem hj hk) (inv_mem hj)) (inv_mem hk)
  have hc1 : j * k * j⁻¹ * k⁻¹ ≠ 1 := by
    intro h
    have h2 : j * k * j⁻¹ = k := mul_inv_eq_one.mp h
    exact hjk (mul_inv_eq_iff_eq_mul.mp h2)
  refine le_of_normal_step hJs (fun j' hj' => ?_)
    (Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, Subgroup.mem_inf.mpr ⟨hcL, hcJ⟩⟩,
      fun h => hc1 (congrArg Subtype.val h)⟩)
  obtain ⟨l', hl', hj'l⟩ := exists_diag_lift hp haG hap ha1 hJ haJ hj'
  exact ⟨l', fun x hx => hQa.commute_sSup_diff hJa x hx l' hl', hLa hj'l⟩

theorem le_Lgen_of_fixed (hp : p.Prime) (hA : IsElemAbelian p A)
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hB : signalizerMcBrideHypothesisB p G)
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) {a₁ e : Γ} (ha₁A : a₁ ∈ A) (ha₁1 : a₁ ≠ 1)
    (ha₁N : a₁ ∈ Subgroup.normalizer (J : Set Γ))
    (ha₁C : ¬ J ≤ Subgroup.centralizer ({a₁} : Set Γ)) (heA : e ∈ A) (he1 : e ≠ 1)
    (heN : e ∉ Subgroup.normalizer (J : Set Γ)) : J ≤ Lgen A G := by
  have hep : e ^ p = 1 := hA.2 e heA
  have ha₁p : a₁ ^ p = 1 := hA.2 a₁ ha₁A
  obtain ⟨-, -, hJs', -⟩ := mem_lcal_iff.mp hJ
  have hJs : IsSimpleGroup J := hJs'
  have hLe : smear J (Subgroup.zpowers e) ≤ Lgen A G :=
    (smear_le_kOf hp (hAG heA) hep he1 hsol hJ heN).trans (kOf_le_Lgen heA he1)
  have hQe := isDirectProduct_orbitSet (hAG heA) hJ
  have hJe := self_mem_orbitSet (Subgroup.zpowers e) J
  have hfix : J ⊓ Subgroup.centralizer ({a₁} : Set Γ) ≠ ⊥ := by
    let f : MulAut ↥J := J.normalizerMonoidHom ⟨a₁, ha₁N⟩
    have hfc : ∀ t : J, ((f t : J) : Γ) = a₁ * t * a₁⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨a₁, ha₁N⟩
    have hf1 : f ≠ 1 := by
      intro h1
      refine ha₁C fun t ht => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : t = a₁ * t * a₁⁻¹ := by simpa [h1] using hfc ⟨t, ht⟩
      calc t * a₁ = a₁ * t * a₁⁻¹ * a₁ := by rw [← h2]
        _ = a₁ * t := by group
    have hfp : f ^ p = 1 := by
      rw [← map_pow]
      have : (⟨a₁, ha₁N⟩ : Subgroup.normalizer (J : Set Γ)) ^ p = 1 :=
        Subtype.ext (by simpa using ha₁p)
      rw [this, map_one]
    have hf : orderOf f = p := by
      have := Fact.mk hp
      exact orderOf_eq_prime hfp hf1
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (signalizerFixedSubgroup_ne_bot (signalizerMcBrideHypothesisA_of_mem_lcal hB hJ) hf)
    have hxf : f (x : J) = (x : J) := x.2
    have hxc : ((x : J) : Γ) ∈ Subgroup.centralizer ({a₁} : Set Γ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : a₁ * ((x : J) : Γ) * a₁⁻¹ = ((x : J) : Γ) := by
        rw [← hfc, hxf]
      calc ((x : J) : Γ) * a₁ = a₁ * ((x : J) : Γ) * a₁⁻¹ * a₁ := by rw [h2]
        _ = a₁ * ((x : J) : Γ) := by group
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨((x : J) : Γ), Subgroup.mem_inf.mpr
      ⟨(x : J).2, hxc⟩⟩, fun h => hx1 ?_⟩
    have h' : ((x : J) : Γ) = 1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hK := isDirectProduct_lcal_kOf hsol
  have hJK : J ≤ kOf G := hK.le hJ
  have hJn : (J.subgroupOf (kOf G)).Normal := by
    have : J ∈ simpleComponents (kOf G) := (simpleComponents_kOf hsol).symm ▸ hJ
    exact this.2.1
  have hsub := isSubnormal_inf_centralizer hJK (kOf_le G) hJn (normal_kOf_subgroupOf G)
    ({a₁} : Set Γ)
  have hle : kOf (J ⊓ Subgroup.centralizer ({a₁} : Set Γ)) ≤ Lgen A G :=
    (kOf_le_kOf_of_isSubnormal (inf_le_inf_right _ (lcal_le hJ)) hsub).trans
      (kOf_le_Lgen ha₁A ha₁1)
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (kOf_ne_bot hfix)
  have hyJ : (y : Γ) ∈ J :=
    (inf_le_left : J ⊓ Subgroup.centralizer ({a₁} : Set Γ) ≤ J) (kOf_le _ y.2)
  refine le_of_normal_step hJs (fun j' hj' => ?_)
    (Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(y : Γ), Subgroup.mem_inf.mpr ⟨hle y.2, hyJ⟩⟩,
      fun h => hy1 (Subtype.ext (by simpa using congrArg Subtype.val h))⟩)
  obtain ⟨l', hl', hj'l⟩ := exists_diag_lift hp (hAG heA) hep he1 hJ heN hj'
  exact ⟨l', fun x hx => hQe.commute_sSup_diff hJe x hx l' hl', hLe hj'l⟩

theorem le_Lgen_of_mem_lcal
    (hp : p.Prime) (hA : IsElemAbelian p A) (hrank : p ^ 2 ≤ Nat.card A)
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hB : signalizerMcBrideHypothesisB p G)
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) : J ≤ Lgen A G := by
  by_cases h1 : ∃ a ∈ A, a ≠ 1 ∧ J ≤ Subgroup.centralizer ({a} : Set Γ)
  · obtain ⟨a, haA, ha1, hc⟩ := h1
    exact le_Lgen_of_centralizes hJ haA ha1 hc
  push Not at h1
  by_cases h2 : ∃ a₁ ∈ A, a₁ ≠ 1 ∧ a₁ ∈ Subgroup.normalizer (J : Set Γ)
  · obtain ⟨a₁, ha₁A, ha₁1, ha₁N⟩ := h2
    obtain ⟨e, heA, heN⟩ : ∃ e ∈ A, e ∉ Subgroup.normalizer (J : Set Γ) := by
      by_contra hcon
      push Not at hcon
      have hAN : A ≤ Subgroup.normalizer (J : Set Γ) := hcon
      have hdvd := card_range_conj_dvd hp hA hB hJ le_rfl hAN
      let ρ : ↥A →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
      have hinj : Function.Injective ρ := by
        rw [injective_iff_map_eq_one]
        intro x hx
        by_contra hx1
        have hx1' : (x : Γ) ≠ 1 := fun h => hx1 (Subtype.ext h)
        refine h1 x x.2 hx1' fun t ht => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h3 : ((ρ x ⟨t, ht⟩ : J) : Γ) = (x : Γ) * t * (x : Γ)⁻¹ :=
          Subgroup.normalizerMonoidHom_apply_apply_coe J (Subgroup.inclusion hAN x) ⟨t, ht⟩
        have h2 : ((ρ x ⟨t, ht⟩ : J) : Γ) = t := by rw [hx]; rfl
        rw [h2] at h3
        calc t * (x : Γ) = (x : Γ) * t * (x : Γ)⁻¹ * (x : Γ) := by rw [← h3]
          _ = (x : Γ) * t := by group
      have hcard : Nat.card A = Nat.card ρ.range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      have hle : Nat.card ρ.range ≤ p := Nat.le_of_dvd hp.pos hdvd
      have h4 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    have he1 : e ≠ 1 := fun h => heN (h ▸ one_mem _)
    exact le_Lgen_of_fixed hp hA hAG hB hsol hJ ha₁A ha₁1 ha₁N (h1 a₁ ha₁A ha₁1) heA he1 heN
  · push Not at h2
    obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hA1 : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
      rw [hA1, Subgroup.card_bot] at hrank
      nlinarith [hp.two_le]
    have hap : a ^ p = 1 := hA.2 a haA
    obtain ⟨b, hbA, hb⟩ : ∃ b ∈ A, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push Not at hcon
      have hAle : A ≤ Subgroup.zpowers a := hcon
      have hord : orderOf a = p := by
        have := Fact.mk hp
        exact orderOf_eq_prime hap ha1
      have := Subgroup.card_le_of_le hAle
      rw [Nat.card_zpowers, hord] at this
      nlinarith [hp.two_le]
    have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
    exact le_Lgen_of_free hp hA hAG hsol hJ h2 haA hbA ha1 hb1
      (zpowers_inf_zpowers_eq_bot hp (hA.2 b hbA) hb1 hb)

theorem kOf_le_Lgen_of_sol_eq_bot
    (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hB : signalizerMcBrideHypothesisB p G) (hsol : sol G = ⊥) : kOf G ≤ Lgen A G := by
  rw [← (isDirectProduct_lcal_kOf hsol).sSup_eq]
  exact sSup_le fun J hJ => le_Lgen_of_mem_lcal hp hA hrank hAG hB hsol hJ

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511
