module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem close16_opp_le (p : ℕ) (X : Subgroup G) : Opp p X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

theorem close16_opp_idem (p : ℕ) (X : Subgroup G) : Opp p (Opp p X) = Opp p X := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun _ hx => hx.1
  · refine Subgroup.closure_mono ?_
    rintro x ⟨hxL, hk⟩
    exact ⟨Subgroup.subset_closure ⟨hxL, hk⟩, hk⟩

theorem close16_mem_normalizer_opp (p : ℕ) {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((Opp p X : Subgroup G) : Set G) := by
  have hg' := mem_normalizer_iff.mp hg
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, k, hk⟩, rfl⟩
    refine ⟨(hg' x).mp hxL, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  · rintro ⟨hyL, k, hk⟩
    have hx : g⁻¹ * y * g ∈ X := by
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      exact (hg' _).mpr (by rw [e]; exact hyL)
    refine ⟨g⁻¹ * y * g, ⟨hx, k, ?_⟩, ?_⟩
    · rw [← hk]
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
      simpa [MulAut.conj_apply] using this
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem close16_opp_normal (p : ℕ) (X : Subgroup G) : ((Opp p X).subgroupOf X).Normal :=
  Subgroup.normal_subgroupOf_iff_le_normalizer (close16_opp_le p X) |>.2
    fun _ hx => close16_mem_normalizer_opp p (Subgroup.le_normalizer hx)

structure Close16Quot3 (Z : Subgroup G) (Λ : Type) [Group Λ] (Ψ : ↥Z →* Λ) : Prop where
  surjective : Function.Surjective Ψ
  simple : IsSimpleGroup Λ
  nonabelian : ¬ IsMulCommutative Λ
  three_dvd : 3 ∣ Nat.card Λ
  ker_two : IsPGroup 2 ↥Ψ.ker

theorem Close16Quot3.opp_surjective {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : ((Opp 3 Z).subgroupOf Z).map Ψ = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite Λ := Finite.of_surjective (Ψ : ↥Z → Λ) h.surjective
  have htop : (⊤ : Subgroup ↥Z).map Z.subtype = Z := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmap : CFSG.RankThree.PartOne.pElementSubgroup 3 Z =
      (CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup ↥Z)).map Z.subtype := by
    rw [s13_pElementSubgroup_map (p := 3) (by norm_num) Z.subtype ⊤, htop]
  have hsub : (Opp 3 Z).subgroupOf Z =
      CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup ↥Z) := by
    change (CFSG.RankThree.PartOne.pElementSubgroup 3 Z).subgroupOf Z =
      CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup ↥Z)
    rw [hmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Z.subtype_injective]
  have hmap2 : ((Opp 3 Z).subgroupOf Z).map Ψ =
      CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ) := by
    rw [hsub, s13_pElementSubgroup_map (p := 3) (by norm_num) Ψ ⊤,
      Subgroup.map_top_of_surjective _ h.surjective]
  have hPtop : CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ) = ⊤ := by
    haveI := h.simple
    have hnorm : (CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ)).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      ext g
      exact ⟨fun _ => Subgroup.mem_top g, fun _ =>
        close16_mem_normalizer_opp (G := Λ) 3 (X := ⊤)
          (Subgroup.le_normalizer (Subgroup.mem_top g))⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h.three_dvd
    have hxP : x ∈ CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ) :=
      Subgroup.subset_closure ⟨Subgroup.mem_top x, ⟨1, by rw [pow_one, hx]⟩⟩
    have hne : CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ) ≠ ⊥ := by
      intro hbot
      have hx1 : x = 1 := by
        have : x ∈ (⊥ : Subgroup Λ) := hbot ▸ hxP
        simpa using this
      rw [hx1] at hx
      simp at hx
    haveI hPn : (CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ)).Normal := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (CFSG.RankThree.PartOne.pElementSubgroup 3 (⊤ : Subgroup Λ)) with hb | ht
    · exact absurd hb hne
    · exact ht
  rw [hmap2, hPtop]

theorem Close16Quot3.opp_ne_bot {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : Opp 3 Z ≠ ⊥ := by
  haveI := h.simple
  intro h0
  have h1 := h.opp_surjective
  rw [h0, Subgroup.bot_subgroupOf, Subgroup.map_bot] at h1
  exact bot_ne_top h1

private theorem close16_isPerfect_of_surjective_ker_isPGroup
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hB : Group.IsPerfect B)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hpker : IsPGroup p f.ker)
    (hqgen : Subgroup.closure {a : A | ∃ k, orderOf a = q ^ k} = ⊤) :
    Group.IsPerfect A := by
  rw [Group.isPerfect_def]
  let D : Subgroup A := _root_.commutator A
  haveI hDnormal : D.Normal := by
    change (_root_.commutator A).Normal
    infer_instance
  have hDmap : D.map f = ⊤ := by
    change (_root_.commutator A).map f = ⊤
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf,
      ← _root_.commutator_def]
    exact hB.commutator_eq_top
  have hle : Subgroup.closure {a : A | ∃ k, orderOf a = q ^ k} ≤ D := by
    refine (Subgroup.closure_le D).2 ?_
    intro a ha
    obtain ⟨k, hk⟩ := ha
    have hfa : f a ∈ D.map f := by rw [hDmap]; exact Subgroup.mem_top (f a)
    obtain ⟨c, hcD, hc⟩ := Subgroup.mem_map.mp hfa
    have hdker : c⁻¹ * a ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).mp hpker ⟨c⁻¹ * a, hdker⟩
    rw [Subgroup.orderOf_mk] at hn
    have hquot : (QuotientGroup.mk' D) a = (QuotientGroup.mk' D) (c⁻¹ * a) := by
      have haeq : a = c * (c⁻¹ * a) := by group
      conv_lhs => rw [haeq]
      rw [map_mul,
        show (QuotientGroup.mk' D) c = 1 from (QuotientGroup.eq_one_iff c).mpr hcD, one_mul]
    have h1 : orderOf ((QuotientGroup.mk' D) a) ∣ q ^ k := by
      rw [← hk]
      exact orderOf_map_dvd (QuotientGroup.mk' D) a
    have h2 : orderOf ((QuotientGroup.mk' D) a) ∣ p ^ n := by
      rw [hquot]
      exact hn ▸ orderOf_map_dvd (QuotientGroup.mk' D) (c⁻¹ * a)
    have hcop : Nat.Coprime (q ^ k) (p ^ n) :=
      Nat.Coprime.pow k n
        ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hpq.symm)
    have hone : orderOf ((QuotientGroup.mk' D) a) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff a).mp (by
      simpa using orderOf_eq_one_iff.mp hone)
  have hDtop : D = ⊤ := top_le_iff.mp (hqgen ▸ hle)
  exact hDtop

theorem Close16Quot3.opp_perfect {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : ⁅Opp 3 Z, Opp 3 Z⁆ = Opp 3 Z := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite Λ := Finite.of_surjective (Ψ : ↥Z → Λ) h.surjective
  haveI := h.simple
  let ι : ↥(Opp 3 Z) →* ↥Z := Subgroup.inclusion (close16_opp_le 3 Z)
  let Ψ' : ↥(Opp 3 Z) →* Λ := Ψ.comp ι
  have hιrange : ι.range = (Opp 3 Z).subgroupOf Z :=
    Subgroup.inclusion_range (close16_opp_le 3 Z)
  have hΨ'surj : Function.Surjective Ψ' := by
    rw [← MonoidHom.range_eq_top]
    change (Ψ.comp ι).range = ⊤
    rw [MonoidHom.range_comp, hιrange, h.opp_surjective]
  have hpker : IsPGroup 2 Ψ'.ker := by
    have hk : Ψ'.ker = Ψ.ker.comap ι := by
      change (Ψ.comp ι).ker = Ψ.ker.comap ι
      exact (MonoidHom.comap_ker Ψ ι).symm
    rw [hk]
    exact h.ker_two.comap_of_injective ι (Subgroup.inclusion_injective (close16_opp_le 3 Z))
  have hqgen : Subgroup.closure {a : ↥(Opp 3 Z) | ∃ k, orderOf a = 3 ^ k} = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have hset : (Opp 3 Z).subtype '' {a : ↥(Opp 3 Z) | ∃ k, orderOf a = 3 ^ k} =
        {y : G | y ∈ Opp 3 Z ∧ ∃ k, orderOf y = 3 ^ k} := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨k, hk⟩ := ha
        exact ⟨a.2, k, (Subgroup.orderOf_coe a).trans hk⟩
      · rintro ⟨hy, k, hk⟩
        exact ⟨⟨y, hy⟩, ⟨k, (Subgroup.orderOf_mk y hy).trans hk⟩, rfl⟩
    rw [hset]
    exact close16_opp_idem 3 Z
  have hperf : Group.IsPerfect ↥(Opp 3 Z) :=
    close16_isPerfect_of_surjective_ker_isPGroup Ψ' hΨ'surj
      (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative h.nonabelian)
      (p := 2) (q := 3) (by norm_num) hpker hqgen
  exact (Subgroup.isPerfect_iff (H := Opp 3 Z)).mp hperf

theorem Close16Quot3.opp_index {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : ∃ k : ℕ, ((Opp 3 Z).subgroupOf Z).index = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Finite Λ := Finite.of_surjective (Ψ : ↥Z → Λ) h.surjective
  haveI : ((Opp 3 Z).subgroupOf Z).Normal := close16_opp_normal 3 Z
  let φ : ↥Ψ.ker →* (↥Z ⧸ (Opp 3 Z).subgroupOf Z) :=
    (QuotientGroup.mk' ((Opp 3 Z).subgroupOf Z)).comp Ψ.ker.subtype
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ((Opp 3 Z).subgroupOf Z) q
    have hg : Ψ g ∈ ((Opp 3 Z).subgroupOf Z).map Ψ := by
      rw [h.opp_surjective]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxΨ⟩ := Subgroup.mem_map.mp hg
    refine ⟨⟨g * x⁻¹, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hxΨ, mul_inv_cancel]
    · change (QuotientGroup.mk' ((Opp 3 Z).subgroupOf Z)) (g * x⁻¹) =
        (QuotientGroup.mk' ((Opp 3 Z).subgroupOf Z)) g
      rw [map_mul, map_inv,
        show (QuotientGroup.mk' ((Opp 3 Z).subgroupOf Z)) x = 1 from
          (QuotientGroup.eq_one_iff x).mpr hx, inv_one, mul_one]
  have hQ : IsPGroup 2 (↥Z ⧸ (Opp 3 Z).subgroupOf Z) :=
    h.ker_two.of_surjective φ hφsurj
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
  exact ⟨k, by simpa [Subgroup.index] using hk⟩

theorem Close16Quot3.opp_bar2 {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : Nonempty (Bar2 (Opp 3 Z) ≃* Λ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite Λ := Finite.of_surjective (Ψ : ↥Z → Λ) h.surjective
  haveI := h.simple
  let ι : ↥(Opp 3 Z) →* ↥Z := Subgroup.inclusion (close16_opp_le 3 Z)
  let Ψ' : ↥(Opp 3 Z) →* Λ := Ψ.comp ι
  have hιrange : ι.range = (Opp 3 Z).subgroupOf Z :=
    Subgroup.inclusion_range (close16_opp_le 3 Z)
  have hΨ'surj : Function.Surjective Ψ' := by
    rw [← MonoidHom.range_eq_top]
    change (Ψ.comp ι).range = ⊤
    rw [MonoidHom.range_comp, hιrange, h.opp_surjective]
  have hpker' : IsPGroup 2 Ψ'.ker := by
    have hk : Ψ'.ker = Ψ.ker.comap ι := by
      change (Ψ.comp ι).ker = Ψ.ker.comap ι
      exact (MonoidHom.comap_ker Ψ ι).symm
    rw [hk]
    exact h.ker_two.comap_of_injective ι (Subgroup.inclusion_injective (close16_opp_le 3 Z))
  have hker : CFSG.pCore 2 ↥(Opp 3 Z) = Ψ'.ker := by
    refine le_antisymm ?_ ?_
    · rw [← Subgroup.map_eq_bot_iff (f := Ψ')]
      haveI hPn : (CFSG.pCore 2 ↥(Opp 3 Z)).Normal := inferInstance
      have hmapnorm : ((CFSG.pCore 2 ↥(Opp 3 Z)).map Ψ').Normal :=
        hPn.map Ψ' hΨ'surj
      have hmap2 : IsPGroup 2 ((CFSG.pCore 2 ↥(Opp 3 Z)).map Ψ') :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Z))).map Ψ'
      haveI : ((CFSG.pCore 2 ↥(Opp 3 Z)).map Ψ').Normal := hmapnorm
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((CFSG.pCore 2 ↥(Opp 3 Z)).map Ψ') with hbot | htop
      · exact hbot
      · exfalso
        rw [htop] at hmap2
        have h2Λ : IsPGroup 2 Λ := hmap2.of_equiv Subgroup.topEquiv
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2Λ
        have h32 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; exact h.three_dvd
        exact (by norm_num : ¬ (3 : ℕ) ∣ 2) ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow h32)
    · exact le_sSup ⟨inferInstance, hpker'⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective Ψ' hΨ'surj)⟩

theorem Close16Quot3.pCore_ne_bot {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) (hne : Ψ.ker ≠ ⊥) : pCoreOf 2 Z ≠ ⊥ := by
  intro h0
  apply hne
  have hker : Ψ.ker ≤ CFSG.pCore 2 ↥Z := le_sSup ⟨inferInstance, h.ker_two⟩
  have hpc : CFSG.pCore 2 ↥Z = ⊥ := by
    have : (CFSG.pCore 2 ↥Z).map Z.subtype = ⊥ := h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective).1 this
  rw [hpc] at hker
  exact le_bot_iff.1 hker

theorem Close16Quot3.card_eq {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : Nat.card ↥Z = Nat.card ↥Ψ.ker * Nat.card Λ := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Ψ h.surjective).toEquiv, mul_comm]

private theorem close16_quasisimple_of_equiv {X Λ : Type} [Group X] [Group Λ] [IsSimpleGroup Λ]
    (hΛ : ¬ IsMulCommutative Λ) (e : X ≃* Λ) : CFSG.Open.IsQuasisimple X := by
  haveI : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hX : ¬ IsMulCommutative X := by
    intro hc
    apply hΛ
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, mul_comm x y]
  have hcen : Subgroup.center X = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hX
  have hperf : Group.IsPerfect X := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hX
  refine ⟨Group.isPerfect_def.1 hperf, ?_⟩
  have e2 : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e2

theorem Close16Quot3.opp_quasisimple {Z : Subgroup G} {Λ : Type} [Group Λ] {Ψ : ↥Z →* Λ}
    (h : Close16Quot3 Z Λ Ψ) : CFSG.Open.IsQuasisimple (Bar2 (Opp 3 Z)) := by
  haveI := h.simple
  obtain ⟨e⟩ := h.opp_bar2
  exact close16_quasisimple_of_equiv h.nonabelian e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
