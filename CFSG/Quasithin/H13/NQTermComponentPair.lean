module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open scoped Pointwise commutatorElement

theorem isQuasisimple_of_isSimpleGroup_of_nonabelian {D : Type*} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : CFSG.IsQuasisimple D := by
  have hZ : center D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcomm : commutator D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator D :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  refine ⟨⟨hcomm⟩, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

variable {H : Type*} [Group H]

theorem isComponent_conjugate {K : Subgroup H} (hK : CFSG.IsComponent K) (g : H) :
    CFSG.IsComponent (CFSG.conjugate K g) := by
  have hsurj : Function.Surjective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).surjective
  refine ⟨?_, hK.2.map hsurj⟩
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (K.equivMapOfInjective _ (MulAut.conj g⁻¹).injective)).mp hK.1

theorem exists_isElementaryAbelian_card_pRank {p : ℕ} (hp : 1 < p) (G : Type*) [Group G]
    [Finite G] : ∃ E : Subgroup G, CFSG.IsElementaryAbelian p E ∧
      Nat.card E = p ^ CFSG.pRank p G := by
  have hbot : ∀ a : (⊥ : Subgroup G), a = 1 := fun a => Subtype.ext (Subgroup.mem_bot.mp a.2)
  have : IsMulCommutative (⊥ : Subgroup G) := ⟨⟨fun a b => by rw [hbot a, hbot b]⟩⟩
  have hne : ({r : ℕ | ∃ A : Subgroup G, CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ r}).Nonempty :=
    ⟨0, ⊥, ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by rw [hbot a, one_pow]⟩,
      by rw [Subgroup.card_bot, pow_zero]⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup G, CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ r} := by
    refine ⟨Nat.card G, ?_⟩
    rintro r ⟨A, -, hA⟩
    calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
      _ = Nat.card A := hA.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group A
  exact Nat.sSup_mem hne hbdd

theorem SQTK_conjugate_component_pair_thin_central_quotient
    {H : Type} [Group H] [Finite H]
    (hH : CFSG.SectionRank.IsSQTKCat H) {J : Subgroup H} (hJ : CFSG.IsComponent J) {h : H}
    (hh : CFSG.conjugate J h ≠ J) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (J ⧸ center J) ≤ 1 := by
  intro r hr hr2
  classical
  have : Fact r.Prime := ⟨hr⟩
  set J₂ := CFSG.conjugate J h with hJ₂def
  have hJ₂ : CFSG.IsComponent J₂ := isComponent_conjugate hJ h
  have hcomm : ⁅J, J₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ hJ₂).resolve_left (Ne.symm hh)
  have hc : ∀ a ∈ J, ∀ b ∈ J₂, a * b = b * a := fun a ha b hb => by
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set K := J ⊔ J₂ with hK
  have hJK : J ≤ K := le_sup_left
  have hJ₂K : J₂ ≤ K := le_sup_right
  have hcent : ∀ z : H, (∀ a ∈ J, a * z = z * a) → (∀ b ∈ J₂, b * z = z * b) →
      ∀ k ∈ K, k * z = z * k := by
    intro z h1 h2 k hk
    have hle : K ≤ Subgroup.centralizer ({z} : Set H) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (h1 a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (h2 b hb).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hk)) z rfl).symm
  set π := QuotientGroup.mk' (center K) with hπ
  have hcenter : ∀ k : K, k ∈ center K ↔ ∀ k' : K, k' * k = k * k' := fun k =>
    Subgroup.mem_center_iff
  have hZ₁ : center J ≤ (π.comp (Subgroup.inclusion hJK)).ker := by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hcenter]
    intro k'
    apply Subtype.ext
    exact hcent (a : H) (fun x hx => congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp ha) ⟨x, hx⟩))
      (fun b hb => (hc (a : H) a.2 b hb).symm) k' k'.2
  have hZ₂ : center J₂ ≤ (π.comp (Subgroup.inclusion hJ₂K)).ker := by
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hcenter]
    intro k'
    apply Subtype.ext
    exact hcent (b : H) (fun a ha => hc a ha (b : H) b.2)
      (fun x hx => congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb) ⟨x, hx⟩)) k' k'.2
  set α₁ : J ⧸ center J →* K ⧸ center K := QuotientGroup.lift _ _ hZ₁ with hα₁
  set α₂ : J₂ ⧸ center J₂ →* K ⧸ center K := QuotientGroup.lift _ _ hZ₂ with hα₂
  have hα₁mk : ∀ a : J, α₁ (a : J ⧸ center J) = π (Subgroup.inclusion hJK a) := fun _ => rfl
  have hα₂mk : ∀ b : J₂, α₂ (b : J₂ ⧸ center J₂) = π (Subgroup.inclusion hJ₂K b) := fun _ => rfl
  have hαc : ∀ x y, Commute (α₁ x) (α₂ y) := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Commute, SemiconjBy, hα₁mk, hα₂mk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc (a : H) a.2 (b : H) b.2)
  set Θ := α₁.noncommCoprod α₂ hαc with hΘ
  have hΘapp : ∀ a : J, ∀ b : J₂, Θ ((a : J ⧸ center J), (b : J₂ ⧸ center J₂)) =
      π (⟨(a : H) * b, mul_mem (hJK a.2) (hJ₂K b.2)⟩ : K) := by
    intro a b
    rw [hΘ, MonoidHom.noncommCoprod_apply, hα₁mk, hα₂mk, ← map_mul]
    rfl
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hΘapp, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcenter] at hxy
    have hab : ∀ k ∈ K, k * ((a : H) * b) = ((a : H) * b) * k := fun k hk =>
      congrArg Subtype.val (hxy ⟨k, hk⟩)
    have ha : a ∈ center J := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have h1 := hab (x : H) (hJK x.2)
      have h2 : (x : H) * b = b * x := hc (x : H) x.2 (b : H) b.2
      change (x : H) * a = a * x
      have h3 : (x : H) * a * b = a * x * b := by
        calc (x : H) * a * b = (x : H) * ((a : H) * b) := by group
          _ = ((a : H) * b) * x := h1
          _ = a * (x * b) := by rw [mul_assoc, ← h2]
          _ = a * x * b := by group
      exact mul_right_cancel h3
    have hb : b ∈ center J₂ := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := hab (y : H) (hJ₂K y.2)
      have h2 : (a : H) * y = y * a := hc (a : H) a.2 (y : H) y.2
      change (y : H) * b = b * y
      have h3 : (a : H) * (y * b) = a * (b * y) := by
        calc (a : H) * (y * b) = (a * y) * b := by group
          _ = (y * a) * b := by rw [h2]
          _ = (y : H) * ((a : H) * b) := by group
          _ = ((a : H) * b) * y := h1
          _ = a * (b * y) := by group
      exact mul_left_cancel h3
    rw [Prod.mk_eq_one, (QuotientGroup.eq_one_iff a).mpr ha, (QuotientGroup.eq_one_iff b).mpr hb]
    exact ⟨rfl, rfl⟩
  have hJN : J ≤ normalizer (J₂ : Set H) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hΘsurj : Function.Surjective Θ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) q
    have hk : (k : H) ∈ (J : Set H) * (J₂ : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J J₂ hJN]
      exact k.2
    obtain ⟨a, ha, b, hb, hab⟩ := hk
    have hab' : a * b = (k : H) := hab
    refine ⟨(((⟨a, ha⟩ : J) : J ⧸ center J), ((⟨b, hb⟩ : J₂) : J₂ ⧸ center J₂)), ?_⟩
    rw [hΘapp]
    congr 1
    exact Subtype.ext hab'
  have hsimple₁ : IsSimpleGroup (J ⧸ center J) := hJ.1.2.1
  have hsimple₂ : IsSimpleGroup (J₂ ⧸ center J₂) := hJ₂.1.2.1
  have hcompα : ∀ {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : ∃ a b : Q, a * b ≠ b * a)
      (α : Q →* K ⧸ center K) (hα : Function.Injective α)
      (hn : ∀ g : K ⧸ center K, ∀ x : Q, ∃ y : Q, g * α x * g⁻¹ = α y),
      CFSG.IsComponent α.range := by
    intro Q _ _ hQ α hα hn
    refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (MonoidHom.ofInjective hα)).mp (isQuasisimple_of_isSimpleGroup_of_nonabelian hQ), ?_⟩
    refine Subgroup.Normal.isSubnormal ⟨fun n hn' g => ?_⟩
    obtain ⟨x, rfl⟩ := hn'
    obtain ⟨y, hy⟩ := hn g x
    exact ⟨y, hy.symm⟩
  have hα₁inj : Function.Injective α₁ := fun x y hxy => by
    have h1 : Θ (x, 1) = Θ (y, 1) := by
      simp [hΘ, hxy]
    exact congrArg Prod.fst (hΘinj h1)
  have hα₂inj : Function.Injective α₂ := fun x y hxy => by
    have h1 : Θ (1, x) = Θ (1, y) := by
      simp [hΘ, hxy]
    exact congrArg Prod.snd (hΘinj h1)
  have hn₁ : ∀ g : K ⧸ center K, ∀ x, ∃ y, g * α₁ x * g⁻¹ = α₁ y := by
    intro g x
    obtain ⟨⟨u, v⟩, rfl⟩ := hΘsurj g
    refine ⟨u * x * u⁻¹, ?_⟩
    rw [hΘ, MonoidHom.noncommCoprod_apply, map_mul, map_mul, map_inv]
    have h1 := (hαc x v).eq
    have h2 := (hαc u⁻¹ v).eq
    rw [map_inv] at h2
    calc α₁ u * α₂ v * α₁ x * (α₁ u * α₂ v)⁻¹
        = α₁ u * (α₂ v * α₁ x) * (α₂ v)⁻¹ * (α₁ u)⁻¹ := by group
      _ = α₁ u * α₁ x * (α₁ u)⁻¹ := by rw [← h1]; group
  have hn₂ : ∀ g : K ⧸ center K, ∀ y, ∃ z, g * α₂ y * g⁻¹ = α₂ z := by
    intro g y
    obtain ⟨⟨u, v⟩, rfl⟩ := hΘsurj g
    refine ⟨v * y * v⁻¹, ?_⟩
    rw [hΘ, MonoidHom.noncommCoprod_apply, map_mul, map_mul, map_inv]
    have h1 := (hαc u (v * y)).eq
    have h2 := (hαc u v).eq
    calc α₁ u * α₂ v * α₂ y * (α₁ u * α₂ v)⁻¹
        = α₁ u * (α₂ v * α₂ y) * (α₂ v)⁻¹ * (α₁ u)⁻¹ := by group
      _ = (α₂ v * α₂ y) * α₁ u * (α₂ v)⁻¹ * (α₁ u)⁻¹ := by
          rw [← map_mul α₂ v y, h1]
      _ = α₂ v * α₂ y * (α₂ v)⁻¹ := by
          have h3 : α₁ u * (α₂ v)⁻¹ = (α₂ v)⁻¹ * α₁ u := by
            rw [← map_inv, (hαc u v⁻¹).eq]
          rw [mul_assoc (α₂ v * α₂ y) (α₁ u), h3]
          group
  have hM₁ := hcompα hJ.1.2.2 α₁ hα₁inj hn₁
  have hM₂ := hcompα hJ₂.1.2.2 α₂ hα₂inj hn₂
  have hle₁ : α₁.range ≤ CFSG.layer (K ⧸ center K) := le_sSup hM₁
  have hle₂ : α₂.range ≤ CFSG.layer (K ⧸ center K) := le_sSup hM₂
  have hlayer : CFSG.layer (K ⧸ center K) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨⟨u, v⟩, rfl⟩ := hΘsurj g
    rw [hΘ, MonoidHom.noncommCoprod_apply]
    exact mul_mem (hle₁ ⟨u, rfl⟩) (hle₂ ⟨v, rfl⟩)
  have hSQT : IsStronglyQuasithin (K ⧸ center K) :=
    CFSG.SectionRank.sqtk_semisimple_section_rank_of_catalog
      CFSG.SectionRank.oddKernelCentralization CFSG.SectionRank.catalogStepHyp hH K (center K)
      hlayer
  by_contra hlt
  push Not at hlt
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_isElementaryAbelian_card_pRank hr.one_lt (J ⧸ center J)
  let e : J ≃* J₂ := J.equivMapOfInjective _ (MulAut.conj h⁻¹).injective
  let eZ : (J ⧸ center J) ≃* (J₂ ⧸ center J₂) :=
    QuotientGroup.congr (center J) (center J₂) e (Subgroup.map_center_eq e)
  set E₂ := E₁.map eZ.toMonoidHom with hE₂
  have hE₂c : Nat.card E₂ = r ^ CFSG.pRank r (J ⧸ center J) := by
    rw [hE₂, Subgroup.card_map_of_injective (f := eZ.toMonoidHom) eZ.injective, hE₁c]
  have hE₂e : CFSG.IsElementaryAbelian r E₂ := by
    rw [hE₂]
    exact CFSG.IsElementaryAbelian.map _
  set F := E₁.prod E₂ with hF
  have hFc : Nat.card F = r ^ (CFSG.pRank r (J ⧸ center J) + CFSG.pRank r (J ⧸ center J)) := by
    rw [hF, Nat.card_congr (Subgroup.prodEquiv E₁ E₂).toEquiv, Nat.card_prod, hE₁c, hE₂c,
      pow_add]
  have : IsMulCommutative F := ⟨⟨fun x y => Subtype.ext (Prod.ext
    (congrArg Subtype.val (hE₁.toIsMulCommutative.is_comm.comm ⟨_, (Subgroup.mem_prod.mp x.2).1⟩
      ⟨_, (Subgroup.mem_prod.mp y.2).1⟩))
    (congrArg Subtype.val (hE₂e.toIsMulCommutative.is_comm.comm ⟨_, (Subgroup.mem_prod.mp x.2).2⟩
      ⟨_, (Subgroup.mem_prod.mp y.2).2⟩)))⟩⟩
  have hFe : CFSG.IsElementaryAbelian r F := by
    refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (Prod.ext ?_ ?_)⟩
    · rw [Subgroup.coe_pow, Prod.pow_fst, Subgroup.coe_one, Prod.fst_one]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ (Subgroup.mem_prod.mp x.2).1
    · rw [Subgroup.coe_pow, Prod.pow_snd, Subgroup.coe_one, Prod.snd_one]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ (Subgroup.mem_prod.mp x.2).2
  have h1 := CFSG.LieType.SteinbergBR.le_pRank_of_card hr.one_lt F hFe hFc
  have h2 := CFSG.RankThree.OddKernel.pRank_le_of_injective hr.one_lt Θ hΘinj
  have h3 := hSQT r hr hr2
  omega

end CFSG.Quasithin.H13.NQTerm
