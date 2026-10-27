module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.RankThree.S4Free.StellmacherHosts
public import CFSG.LocalAnalysis.UniquenessCase.UCInspBasic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree.S4Free CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UCK (SzOrder3Aut)

private def restrictAut {Q : Type*} [Group Q] (σ : MulAut Q) {J : Subgroup Q}
    (h : ∀ x, x ∈ J ↔ σ x ∈ J) : MulAut ↥J where
  toFun j := ⟨σ (j : Q), (h j).mp j.2⟩
  invFun j := ⟨σ.symm (j : Q), (h _).mpr (by simpa using j.2)⟩
  left_inv j := Subtype.ext (σ.symm_apply_apply j)
  right_inv j := Subtype.ext (σ.apply_symm_apply j)
  map_mul' a b := Subtype.ext (map_mul σ (a : Q) (b : Q))

private def quotCenterAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun τ := QuotientGroup.congr _ _ τ
    ((Subgroup.characteristic_iff_map_eq (H := Subgroup.center X)).mp inferInstance τ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

private theorem exists_odd_prime_dvd_card {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ Nat.card X := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => by
    by_contra hd2
    exact hcon d hd hd2 hdvd
  haveI : Group.IsNilpotent X := (IsPGroup.of_card hpow).isNilpotent
  obtain ⟨a, b, hab⟩ := hna
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 inferInstance a b)

private theorem isSylowOf_top_iff {X : Type*} [Group X] [Finite X] {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Subgroup X} : IsSylowOf ℓ P ⊤ ↔ IsPGroup ℓ P ∧ ¬ ℓ ∣ P.index := by
  rw [isSylowOf_iff, Subgroup.relIndex_top_right]
  simp only [le_top, true_and]

private theorem isSylowOf_top_map_mk {Q : Type*} [Group Q] [Finite Q] {J T : Subgroup Q}
    (N : Subgroup ↥J) [N.Normal] {ℓ : ℕ} [Fact ℓ.Prime] (hT : IsSylowOf ℓ T J) :
    IsSylowOf ℓ ((T.subgroupOf J).map (QuotientGroup.mk' N)) ⊤ := by
  obtain ⟨-, hTp, hTi⟩ := isSylowOf_iff.mp hT
  rw [isSylowOf_top_iff]
  exact ⟨(hTp.comap_subtype).map _, fun hdvd =>
    hTi (hdvd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective N)))⟩

private theorem mulAut_eq_one_of_central {X : Type*} [Group X] [hX : Group.IsPerfect X]
    (τ : MulAut X) (h : ∀ x : X, x⁻¹ * τ x ∈ Subgroup.center X) : τ = 1 := by
  let φ : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * τ x, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hz := Subgroup.mem_center_iff.mp (h x) y⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (τ x * τ y) = y⁻¹ * (x⁻¹ * τ x) * τ y := by group
          _ = (x⁻¹ * τ x) * y⁻¹ * τ y := by rw [hz]
          _ = x⁻¹ * τ x * (y⁻¹ * τ y) := by group }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hX.commutator_eq_top]
    exact Abelianization.commutator_subset_ker φ
  ext x
  have h1 : φ x = 1 := MonoidHom.mem_ker.mp (by rw [hker]; trivial)
  exact (inv_mul_eq_one.mp (congrArg Subtype.val h1)).symm

variable {Q : Type} [Group Q] [Finite Q]

private theorem map_component_eq {σ : MulAut Q}
    (hfix : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
      ∃ P : Subgroup Q, IsSylowOf ℓ P (layer Q) ∧ ∀ x ∈ P, σ x = x)
    {J : Subgroup Q} (hJ : IsComponent J) : J.map σ.toMonoidHom = J := by
  by_contra hne
  have hJ' : IsComponent (J.map σ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv σ hJ
  have hcomm : ⁅J, J.map σ.toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hJ hJ' with h | h
    · exact absurd h.symm hne
    · exact h
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
  obtain ⟨ℓ, hℓ, hℓ2, hℓd⟩ := exists_odd_prime_dvd_card (X := ↥J ⧸ Subgroup.center ↥J) hJ.1.2.2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨S, hS, hSfix⟩ := hfix ℓ hℓ hℓ2
  have hT : IsSylowOf ℓ (S ⊓ J) J :=
    hS.inf_of_le_normalizer (CFSG.LocalCores.components_normal_in_layer hJ).1
      (CFSG.LocalCores.layer_le_normalizer hJ)
  obtain ⟨t, htT, htZ⟩ : ∃ t ∈ (S ⊓ J).subgroupOf J, t ∉ Subgroup.center ↥J := by
    by_contra hcon
    push Not at hcon
    have hbot : ((S ⊓ J).subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hcon
    have h := (isSylowOf_top_iff.mp (isSylowOf_top_map_mk (Subgroup.center ↥J) hT)).2
    rw [hbot, Subgroup.index_bot] at h
    exact h hℓd
  apply htZ
  rw [Subgroup.mem_center_iff]
  intro g
  have htS : (t : Q) ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp htT)).1
  have htJ' : (t : Q) ∈ J.map σ.toMonoidHom := ⟨t, t.2, hSfix _ htS⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm g.2) (t : Q) htJ').symm

theorem fixed_of_isComponent (hSz : SzSections Q) (hSz3 : SzOrder3Aut) {σ : MulAut Q}
    (hσ : σ ^ 3 = 1)
    (hfix : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
      ∃ P : Subgroup Q, IsSylowOf ℓ P (layer Q) ∧ ∀ x ∈ P, σ x = x)
    {J : Subgroup Q} (hJ : IsComponent J) : ∀ x ∈ J, σ x = x := by
  have hmap := map_component_eq hfix hJ
  have hstab : ∀ x, x ∈ J ↔ σ x ∈ J := by
    intro x
    have h : σ x ∈ J.map σ.toMonoidHom ↔ x ∈ J := by
      simpa using (Subgroup.mem_map_equiv (f := σ) (K := J) (x := σ x))
    rw [hmap] at h
    exact h.symm
  let τ : MulAut ↥J := restrictAut σ hstab
  have hpow : ∀ (n : ℕ) (j : ↥J), (((τ ^ n) j : ↥J) : Q) = (σ ^ n) (j : Q) := by
    intro n
    induction n with
    | zero => intro j; rfl
    | succ n ih =>
      intro j
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
      exact (ih (τ j))
  have hτ3 : τ ^ 3 = 1 := by
    refine MulEquiv.ext fun j => Subtype.ext ?_
    rw [hpow 3 j, hσ]
    rfl
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
  have hτbar : quotCenterAut ↥J τ = 1 := by
    by_contra hne
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (quotCenterAut ↥J τ) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hτ3, map_one]) hne
    obtain ⟨a, ha, K, _, _, hK, ⟨e⟩⟩ := hSz J (Subgroup.center ↥J) hJ.1.2.1 hJ.1.2.2
    have hmodel : CFSG.Blueprint.SuzukiModel (↥J ⧸ Subgroup.center ↥J) 2 (2 * a + 1) :=
      ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e⟩⟩
    obtain ⟨ℓ₁, _, hℓ₁, -, -, hℓ₁2, -, hmov⟩ := hSz3 _ _ hmodel _ hord
    haveI : Fact ℓ₁.Prime := ⟨hℓ₁⟩
    obtain ⟨S, hS, hSfix⟩ := hfix ℓ₁ hℓ₁ hℓ₁2
    have hT : IsSylowOf ℓ₁ (S ⊓ J) J :=
      hS.inf_of_le_normalizer (CFSG.LocalCores.components_normal_in_layer hJ).1
        (CFSG.LocalCores.layer_le_normalizer hJ)
    obtain ⟨x, hx, hxne⟩ :=
      hmov _ (Or.inl (isSylowOf_top_map_mk (Subgroup.center ↥J) hT))
    apply hxne
    obtain ⟨y, hy, rfl⟩ := hx
    have hyS : (y : Q) ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
    have hτy : τ y = y := Subtype.ext (hSfix _ hyS)
    change QuotientGroup.mk' (Subgroup.center ↥J) (τ y) = _
    rw [hτy]
  have hcen : ∀ j : ↥J, j⁻¹ * τ j ∈ Subgroup.center ↥J := by
    intro j
    have h : (QuotientGroup.mk (τ j) : ↥J ⧸ Subgroup.center ↥J) = QuotientGroup.mk j := by
      have := congrArg (fun f => f (QuotientGroup.mk j)) hτbar
      exact this
    exact QuotientGroup.eq.mp h.symm
  haveI : Group.IsPerfect ↥J := hJ.1.1
  have hτ1 : τ = 1 := mulAut_eq_one_of_central τ hcen
  intro x hx
  have := congrArg (fun f : MulAut ↥J => ((f ⟨x, hx⟩ : ↥J) : Q)) hτ1
  exact this

theorem mulAut_fixes_layer_of_szSections (hSz : SzSections Q) (hSz3 : SzOrder3Aut)
    {σ : MulAut Q} (hσ : σ ^ 3 = 1)
    (hfix : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
      ∃ P : Subgroup Q, IsSylowOf ℓ P (layer Q) ∧ ∀ x ∈ P, σ x = x) :
    ∀ x ∈ layer Q, σ x = x := by
  have hle : layer Q ≤ σ.toMonoidHom.eqLocus (MonoidHom.id Q) := by
    rw [layer.eq_sSup]
    exact sSup_le fun J hJ x hx => fixed_of_isComponent hSz hSz3 hσ hfix hJ x hx
  exact fun x hx => hle hx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
