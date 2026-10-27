module

public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.BalTools

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec15
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev thetaRho (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) →* MulAut (J ⧸ aschbacherSolvableCore 3 J) :=
  (thetaQuotMulAut J).comp J.normalizerMonoidHom

theorem commutator_mem_theta_of_ne_in {M J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ thetaComponentsIn M) (h₂ : J₂ ∈ thetaComponentsIn M) (hne : J₁ ≠ J₂)
    {x y : G} (hx : x ∈ J₁) (hy : y ∈ J₂) :
    x * y * x⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) M := by
  obtain ⟨J₁', hJ₁', rfl⟩ := h₁
  obtain ⟨J₂', hJ₂', rfl⟩ := h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := M) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 M) with hπ
  have hne' : J₁' ≠ J₂' := fun h => hne (h ▸ rfl)
  have hJne : J₁'.map π ≠ J₂'.map π := fun h => hne' (hbij.injOn hJ₁' hJ₂' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hJ₁')
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hJ₂')).resolve_left hJne
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : π y' * π x' = π x' * π y' :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
      (Subgroup.mem_map_of_mem π hy')
  have h2 : π (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem le_normalizer_of_ne_in {M J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ thetaComponentsIn M) (h₂ : J₂ ∈ thetaComponentsIn M) (hne : J₁ ≠ J₂) :
    J₁ ≤ Subgroup.normalizer (J₂ : Set G) := by
  obtain ⟨J₁', hJ₁', rfl⟩ := h₁
  obtain ⟨J₂', hJ₂', rfl⟩ := h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := M) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 M) with hπ
  have hne' : J₁' ≠ J₂' := fun h => hne (h ▸ rfl)
  have hJne : J₁'.map π ≠ J₂'.map π := fun h => hne' (hbij.injOn hJ₁' hJ₂' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hJ₁')
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hJ₂')).resolve_left hJne
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rintro _ ⟨x', hx', rfl⟩
  have hJx := map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj x') hJ₂'
  have himg : (J₂'.map (MulAut.conj x').toMonoidHom).map π = J₂'.map π := by
    rw [Subgroup.map_map]
    ext z
    constructor
    · rintro ⟨y', hy', rfl⟩
      have h1 : π y' * π x' = π x' * π y' :=
        Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
          (Subgroup.mem_map_of_mem π hy')
      refine ⟨y', hy', ?_⟩
      change π y' = π (x' * y' * x'⁻¹)
      rw [map_mul, map_mul, map_inv, ← h1]
      group
    · rintro ⟨y', hy', rfl⟩
      have h1 : π y' * π x' = π x' * π y' :=
        Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
          (Subgroup.mem_map_of_mem π hy')
      refine ⟨y', hy', ?_⟩
      change π (x' * y' * x'⁻¹) = π y'
      rw [map_mul, map_mul, map_inv, ← h1]
      group
  have heq := hbij.injOn hJx hJ₂' himg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc (J₂'.map M.subtype).map (MulAut.conj (x' : G)).toMonoidHom
      = (J₂'.map (MulAut.conj x').toMonoidHom).map M.subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
    _ = J₂'.map M.subtype := by rw [heq]

theorem le_thetaQuotCentralizer_of_ne_in {M J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ thetaComponentsIn M) (h₂ : J₂ ∈ thetaComponentsIn M) (hne : J₁ ≠ J₂) :
    J₁ ≤ thetaQuotCentralizer J₂ := by
  intro x hx
  have hxN := le_normalizer_of_ne_in h₁ h₂ hne hx
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
  rw [theta_eq_inf_of_mem_thetaComponentsIn h₂]
  refine ⟨J₂.mul_mem (J₂.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl), ?_⟩
  have hc := commutator_mem_theta_of_ne_in h₁ h₂ hne hx hl
  have hlM : l ∈ M := le_of_mem_thetaComponentsIn h₂ hl
  have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta M (M.inv_mem hlM)) _).mp hc
  have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
  rwa [e] at h1

theorem thetaRho_of_mem {J : Subgroup G} {j : G} (hj : j ∈ J) :
    thetaRho J ⟨j, Subgroup.le_normalizer hj⟩ =
      MulAut.conj ((⟨j, hj⟩ : J) : J ⧸ aschbacherSolvableCore 3 J) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    change (((J.normalizerMonoidHom ⟨j, Subgroup.le_normalizer hj⟩ z : J) :
        J ⧸ aschbacherSolvableCore 3 J)) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem exists_mem_inv_mul_mem_thetaQuotCentralizer {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hin : thetaRho J ⟨g, hg⟩ ∈ inner (J ⧸ aschbacherSolvableCore 3 J)) :
    ∃ j ∈ J, j⁻¹ * g ∈ thetaQuotCentralizer J := by
  obtain ⟨s, hs⟩ := hin
  obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective s
  have hjN : (j' : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer j'.2
  have hjN' : (j' : G)⁻¹ * g ∈ Subgroup.normalizer (J : Set G) := mul_mem (inv_mem hjN) hg
  refine ⟨j', j'.2, ⟨⟨_, hjN'⟩, ?_, rfl⟩⟩
  change thetaRho J ⟨_, hjN'⟩ = 1
  have hsplit : (⟨(j' : G)⁻¹ * g, hjN'⟩ : Subgroup.normalizer (J : Set G)) =
      (⟨j', hjN⟩ : Subgroup.normalizer (J : Set G))⁻¹ * ⟨g, hg⟩ := rfl
  rw [hsplit, map_mul, map_inv, ← hs, thetaRho_of_mem j'.2]
  exact inv_mul_cancel _

theorem outer_comm {S : Type*} [Group S]
    (hout : commutator (MulAut S) ≤ (MulAut.conj : S →* MulAut S).range) (x y : Outer S) :
    x * y = y * x := by
  have hc : ∀ a b : MulAut S ⧸ inner S, a * b = b * a := fun a b => by
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hab : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [hab]
        exact hout (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
          (Subgroup.mem_top _))
  exact hc x y

theorem thetaRho_commutator_mem_inner {M A J : Subgroup G} (hM3 : ¬ 3 ∣ Nat.card M)
    (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hAJ : ∀ J' ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (J' : Set G))
    (hJ : J ∈ thetaComponentsIn M)
    (hout : commutator (MulAut (J ⧸ aschbacherSolvableCore 3 J)) ≤
      (MulAut.conj : (J ⧸ aschbacherSolvableCore 3 J) →* _).range)
    {y α : G} (hy : y ∈ M) (hα : α ∈ A) (hα3 : α ^ 3 = 1) :
    ∃ hN : ⁅y, α⁆ ∈ Subgroup.normalizer (J : Set G),
      thetaRho J ⟨⁅y, α⁆, hN⟩ ∈ inner (J ⧸ aschbacherSolvableCore 3 J) := by
  set S := J ⧸ aschbacherSolvableCore 3 J
  have hyN : y⁻¹ ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer (M.inv_mem hy)
  have hJ' := Proof1423.map_conj_mem_thetaComponentsIn1423 hyN hJ
  have hαJ' : α ∈ Subgroup.normalizer
      ((J.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G) : Set G) := hAJ _ hJ' hα
  have huN : y * α * y⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change J.map (MulAut.conj (y * α * y⁻¹)).toMonoidHom = J
    have h1 : (J.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj α).toMonoidHom =
        J.map (MulAut.conj y⁻¹).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.mp hαJ'
    have hcomp : (MulAut.conj (y * α * y⁻¹)).toMonoidHom = ((MulAut.conj y).toMonoidHom.comp
        (MulAut.conj α).toMonoidHom).comp (MulAut.conj y⁻¹).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, h1,
      Proof1423.map_conj_map_conj_inv]
  have hvN : α⁻¹ ∈ Subgroup.normalizer (J : Set G) := inv_mem (hAJ J hJ hα)
  have hgN : ⁅y, α⁆ ∈ Subgroup.normalizer (J : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem huN hvN
  refine ⟨hgN, ?_⟩
  set φ := (QuotientGroup.mk' (inner S)).comp (thetaRho J) with hφ
  have hsplit : (⟨⁅y, α⁆, hgN⟩ : Subgroup.normalizer (J : Set G)) =
      ⟨y * α * y⁻¹, huN⟩ * ⟨α⁻¹, hvN⟩ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  have hu3 : (⟨y * α * y⁻¹, huN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, hα3]
    group
  have hv3 : (⟨α⁻¹, hvN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, inv_pow, hα3, inv_one]
  have hφ3 : φ ⟨⁅y, α⁆, hgN⟩ ^ 3 = 1 := by
    have hc : Commute (φ ⟨y * α * y⁻¹, huN⟩) (φ ⟨α⁻¹, hvN⟩) := outer_comm hout _ _
    rw [hsplit, map_mul, hc.mul_pow, ← map_pow, ← map_pow, hu3, hv3, map_one, one_mul]
  have hgM : ⁅y, α⁆ ∈ M := by
    rw [commutatorElement_def]
    have : α * y⁻¹ * α⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hAM hα) _).mp (M.inv_mem hy)
    simpa [mul_assoc] using M.mul_mem hy this
  have hgM' : (⟨⁅y, α⁆, hgN⟩ : Subgroup.normalizer (J : Set G)) ^ Nat.card M = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have := pow_card_eq_one' (G := M) (x := ⟨⁅y, α⁆, hgM⟩)
    exact congrArg Subtype.val this
  have hφM : φ ⟨⁅y, α⁆, hgN⟩ ^ Nat.card M = 1 := by rw [← map_pow, hgM', map_one]
  have hcop : Nat.Coprime 3 (Nat.card M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3
  have hφ1 : φ ⟨⁅y, α⁆, hgN⟩ = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hφ3
    have h2 := orderOf_dvd_of_pow_eq_one hφM
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hφ1
  exact hφ1

theorem inf_iInf_thetaQuotCentralizer_le_theta {M : Subgroup G} (hM3 : ¬ 3 ∣ Nat.card M) :
    M ⊓ (⨅ J ∈ thetaComponentsIn M, thetaQuotCentralizer J) ≤
      inSubgroup (aschbacherSolvableCore 3) M := by
  set C := M ⊓ (⨅ J ∈ thetaComponentsIn M, thetaQuotCentralizer J) with hC
  have hcent : ∀ J ∈ thetaComponentsIn M, C ≤ thetaQuotCentralizer J := fun J hJ =>
    inf_le_right.trans (iInf₂_le J hJ)
  have hsol := Proof1423.isSolvable_normalClosureSub_of_forall hM3 hcent
  set N := Sec15.normalClosureSub M C with hN
  have hNM : N ≤ M := Subgroup.map_subtype_le _
  have hCN : C ≤ N := by
    intro x hx
    exact ⟨⟨x, hx.1⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    have h : N.subgroupOf M = Subgroup.normalClosure ((C.subgroupOf M : Subgroup M) : Set M) := by
      rw [hN, Sec15.normalClosureSub, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hn : (N.subgroupOf M).Normal := h ▸ Subgroup.normalClosure_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hn
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 => hM3 (h3.trans (Subgroup.card_dvd_of_le hNM))
  exact hCN.trans (le_theta_of_normal hNM hMN hsol hN3)

theorem mem_sup_theta_of_forall_inner {M : Subgroup G} (hM3 : ¬ 3 ∣ Nat.card M) {g : G}
    (hgM : g ∈ M)
    (hg : ∀ J ∈ thetaComponentsIn M, ∃ hN : g ∈ Subgroup.normalizer (J : Set G),
      thetaRho J ⟨g, hN⟩ ∈ inner (J ⧸ aschbacherSolvableCore 3 J)) :
    g ∈ (⨆ J ∈ thetaComponentsIn M, J) ⊔ inSubgroup (aschbacherSolvableCore 3) M := by
  classical
  have key : ∀ S : Finset (Subgroup G), (∀ J ∈ S, J ∈ thetaComponentsIn M) →
      ∃ e ∈ (⨆ J ∈ S, J), ∀ J ∈ S, e⁻¹ * g ∈ thetaQuotCentralizer J := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_mem _, fun J hJ => absurd hJ (Finset.notMem_empty J)⟩
    | insert J₀ S hJ₀ ih =>
      intro hS
      obtain ⟨e, he, heS⟩ := ih fun J hJ => hS J (Finset.mem_insert_of_mem hJ)
      have hJ₀M := hS J₀ (Finset.mem_insert_self J₀ S)
      have heC : e ∈ thetaQuotCentralizer J₀ := by
        refine (iSup₂_le fun J hJ => ?_ : (⨆ J ∈ S, J) ≤ thetaQuotCentralizer J₀) he
        exact le_thetaQuotCentralizer_of_ne_in (hS J (Finset.mem_insert_of_mem hJ)) hJ₀M
          (fun h => hJ₀ (h ▸ hJ))
      obtain ⟨hgN, hgin⟩ := hg J₀ hJ₀M
      have heN : e ∈ Subgroup.normalizer (J₀ : Set G) :=
        thetaQuotCentralizer_le_normalizer J₀ heC
      have hegN : e⁻¹ * g ∈ Subgroup.normalizer (J₀ : Set G) := mul_mem (inv_mem heN) hgN
      have hρe : thetaRho J₀ ⟨e, heN⟩ = 1 := by
        obtain ⟨e', he', hee'⟩ := heC
        have : e' = ⟨e, heN⟩ := Subtype.ext hee'
        rw [← this]
        exact he'
      have hegin : thetaRho J₀ ⟨e⁻¹ * g, hegN⟩ ∈ inner (J₀ ⧸ aschbacherSolvableCore 3 J₀) := by
        have hsplit : (⟨e⁻¹ * g, hegN⟩ : Subgroup.normalizer (J₀ : Set G)) =
            (⟨e, heN⟩ : Subgroup.normalizer (J₀ : Set G))⁻¹ * ⟨g, hgN⟩ := rfl
        rw [hsplit, map_mul, map_inv, hρe, inv_one, one_mul]
        exact hgin
      obtain ⟨j, hj, hjC⟩ := exists_mem_inv_mul_mem_thetaQuotCentralizer hegN hegin
      refine ⟨e * j, ?_, fun J hJ => ?_⟩
      · refine mul_mem ((iSup₂_le fun J hJ => ?_ : (⨆ J ∈ S, J) ≤ ⨆ J ∈ insert J₀ S, J) he) ?_
        · exact le_iSup₂_of_le (f := fun J (_ : J ∈ insert J₀ S) => J) J
            (Finset.mem_insert_of_mem hJ) le_rfl
        · exact (le_iSup₂_of_le (f := fun J (_ : J ∈ insert J₀ S) => J) J₀
            (Finset.mem_insert_self J₀ S) le_rfl) hj
      · have e1 : (e * j)⁻¹ * g = j⁻¹ * (e⁻¹ * g) := by group
        rw [e1]
        rcases Finset.mem_insert.mp hJ with rfl | hJS
        · exact hjC
        · have hjJ : j ∈ thetaQuotCentralizer J :=
            le_thetaQuotCentralizer_of_ne_in hJ₀M (hS J (Finset.mem_insert_of_mem hJS))
              (fun h => hJ₀ (h ▸ hJS)) hj
          exact mul_mem (inv_mem hjJ) (heS J hJS)
  have hfin : (thetaComponentsIn M).Finite := Set.toFinite _
  obtain ⟨e, he, heC⟩ := key hfin.toFinset fun J hJ => (Set.Finite.mem_toFinset hfin).mp hJ
  have heM : e ∈ M := by
    refine (iSup₂_le fun J hJ => ?_ : (⨆ J ∈ hfin.toFinset, J) ≤ M) he
    exact le_of_mem_thetaComponentsIn ((Set.Finite.mem_toFinset hfin).mp hJ)
  have hθ : e⁻¹ * g ∈ inSubgroup (aschbacherSolvableCore 3) M := by
    refine inf_iInf_thetaQuotCentralizer_le_theta hM3
      (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem heM) hgM, ?_⟩)
    rw [Subgroup.mem_iInf]
    intro J
    rw [Subgroup.mem_iInf]
    intro hJ
    exact heC J ((Set.Finite.mem_toFinset hfin).mpr hJ)
  have heE : e ∈ ⨆ J ∈ thetaComponentsIn M, J := by
    refine (iSup₂_le fun J hJ => ?_ : (⨆ J ∈ hfin.toFinset, J) ≤ _) he
    exact le_iSup₂_of_le (f := fun J (_ : J ∈ thetaComponentsIn M) => J) J
      ((Set.Finite.mem_toFinset hfin).mp hJ) le_rfl
  have e1 : g = e * (e⁻¹ * g) := by group
  rw [e1]
  exact mul_mem (le_sup_left (a := ⨆ J ∈ thetaComponentsIn M, J) heE)
    (le_sup_right (b := inSubgroup (aschbacherSolvableCore 3) M) hθ)

theorem commutator_le_sup_theta {M A : Subgroup G} (hM3 : ¬ 3 ∣ Nat.card M)
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hA3 : ∀ α ∈ A, α ^ 3 = 1)
    (hAJ : ∀ J ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (J : Set G))
    (hout : ∀ J ∈ thetaComponentsIn M, commutator (MulAut (J ⧸ aschbacherSolvableCore 3 J)) ≤
      (MulAut.conj : (J ⧸ aschbacherSolvableCore 3 J) →* _).range) :
    ⁅M, A⁆ ≤ (⨆ J ∈ thetaComponentsIn M, J) ⊔ inSubgroup (aschbacherSolvableCore 3) M := by
  rw [Subgroup.commutator_le]
  intro y hy α hα
  have hgM : ⁅y, α⁆ ∈ M := by
    rw [commutatorElement_def]
    have : α * y⁻¹ * α⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hAM hα) _).mp (M.inv_mem hy)
    simpa [mul_assoc] using M.mul_mem hy this
  exact mem_sup_theta_of_forall_inner hM3 hgM fun J hJ =>
    thetaRho_commutator_mem_inner hM3 hAM hAJ hJ (hout J hJ) hy hα (hA3 α hα)

end CFSG.RankThree.PartTwo.Sec14.BalTools
