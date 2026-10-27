module

public import CFSG.RankThree.OddKernel.ComponentRanks
public import CFSG.RankThree.Coprime.HighTwoRankOddKernel
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PerfectCover.MinimalCover
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreFrobenius

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

universe u v

section Generic

theorem exists_component_ne_ne {X : Type*} [Group X] [Finite X]
    (h3 : 3 ≤ Nat.card (ComponentIndex X)) (J₁ J₂ : Subgroup X) :
    ∃ J : Subgroup X, IsComponent J ∧ J₁ ≠ J ∧ J₂ ≠ J := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective fun J : ComponentIndex X => decide (J.1 = J₁) := by
    intro J J' h
    by_cases hJ : J.1 = J₁
    · have hJ' : J'.1 = J₁ := by simpa [hJ] using h.symm
      exact Subtype.ext (hJ.trans hJ'.symm)
    · have hJ' : J'.1 ≠ J₁ := by simpa [hJ] using h.symm
      exact Subtype.ext ((hcon J.1 J.2 (Ne.symm hJ)).symm.trans (hcon J'.1 J'.2 (Ne.symm hJ')))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

end Generic

section Dichotomy

theorem eq_or_le_center_of_transitive {T : Type*} [Group T] [Finite T] (S : Subgroup T)
    [S.Normal] (hES : layer S = ⊤)
    (hA : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ t : T, L₁.map (MulAut.conjNormal t).toMonoidHom = L₂)
    (N : Subgroup T) [hN : N.Normal] (hNS : N ≤ S) :
    N = S ∨ N ≤ (center S).map S.subtype := by
  classical
  have hN'n : (N.subgroupOf S).Normal := hN.subgroupOf S
  have hinv : ∀ (t : T) (L : Subgroup S), L ≤ N.subgroupOf S →
      L.map (MulAut.conjNormal t).toMonoidHom ≤ N.subgroupOf S := by
    rintro t L hL _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
    exact hN.conj_mem _ (Subgroup.mem_subgroupOf.mp (hL hs)) t
  by_cases hex : ∃ L : Subgroup S, IsComponent L ∧ L ≤ N.subgroupOf S
  · left
    obtain ⟨L₀, hL₀, hL₀N⟩ := hex
    have htop : N.subgroupOf S = ⊤ := by
      rw [eq_top_iff, ← hES]
      refine sSup_le fun L hL => ?_
      obtain ⟨t, ht⟩ := hA L₀ L hL₀ hL
      rw [← ht]
      exact hinv t L₀ hL₀N
    refine le_antisymm hNS fun s hs => ?_
    have h : (⟨s, hs⟩ : S) ∈ N.subgroupOf S := htop ▸ mem_top _
    exact Subgroup.mem_subgroupOf.mp h
  · right
    push Not at hex
    have hcen : (⊤ : Subgroup S) ≤ centralizer (N.subgroupOf S : Set S) := by
      rw [← hES]
      refine sSup_le fun L hL => ?_
      rcases component_normal_subgroup hL hN'n with h | h
      · exact absurd h (hex L hL)
      · exact commutator_eq_bot_iff_le_centralizer.mp h
    intro n hn
    refine ⟨⟨n, hNS hn⟩, mem_center_iff.mpr fun g => ?_, rfl⟩
    exact (mem_centralizer_iff.mp (hcen (mem_top g)) ⟨n, hNS hn⟩
      (Subgroup.mem_subgroupOf.mpr hn)).symm

end Dichotomy

section Sixteen

theorem exists_four_group_of_isComponent {S : Type*} [Group S] [Finite S] (hES : layer S = ⊤)
    (hZS : Odd (Nat.card (center S))) {L : Subgroup S} (hL : IsComponent L) :
    Odd (Nat.card (center L)) ∧ ∃ W : Subgroup S, W ≤ L ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ (∀ x ∈ W, x ^ 2 = 1) ∧ Nat.card W = 4 := by
  have hZL : Odd (Nat.card (center L)) := by
    have h := inf_center_eq_of_layer_eq_top hES hL
    have h1 : Nat.card (center L) = Nat.card (L ⊓ center S : Subgroup S) := by
      rw [h, card_map_of_injective L.subtype_injective]
    rw [h1]
    exact Odd.of_dvd_nat hZS (card_dvd_of_le inf_le_right)
  refine ⟨hZL, ?_⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  obtain ⟨W₀, hW₀c, hW₀2, hW₀4⟩ := exists_four_group_of_isSimpleGroup hL.1.2.2
  have hodd : Odd (Nat.card (QuotientGroup.mk' (center L)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hZL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW₀p : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW₀4]; norm_num)
  obtain ⟨W₁, -, hW₁, hinj⟩ := exists_two_subgroup_map_eq (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) hodd W₀ hW₀p
  obtain ⟨hc, h2, hcard⟩ := props_of_injective_map _ hinj hW₁ hW₀c hW₀2
  refine ⟨W₁.map L.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hc x hx y hy)
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (h2 x hx)
  · rw [card_map_of_injective L.subtype_injective, hcard, hW₀4]

theorem exists_elementary_sixteen_of_components {S : Type*} [Group S] [Finite S]
    (hES : layer S = ⊤) (hZS : Odd (Nat.card (center S))) {L₁ L₂ : Subgroup S}
    (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) (hne : L₁ ≠ L₂) :
    ∃ V : Subgroup S, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 16 := by
  obtain ⟨hZ₁, W₁, hW₁L, hW₁c, hW₁2, hW₁4⟩ := exists_four_group_of_isComponent hES hZS h₁
  obtain ⟨-, W₂, hW₂L, hW₂c, hW₂2, hW₂4⟩ := exists_four_group_of_isComponent hES hZS h₂
  have h12 := le_centralizer_of_components h₁ h₂ hne
  refine exists_elementary_sixteen hW₁c hW₂c hW₁2 hW₂2 hW₁4 hW₂4
    (fun x hx y hy => (mem_centralizer_iff.mp (h12 (hW₁L hx)) y (hW₂L hy)).symm) ?_
  rw [eq_bot_iff]
  rintro x ⟨hx₁, hx₂⟩
  have hxZ : (⟨x, hW₁L hx₁⟩ : L₁) ∈ center L₁ := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp (h12 g.2) x (hW₂L hx₂)).symm
  have h1 := CFSG.Wreathed.ConfinedOddCore.eq_one_of_sq_eq_one hZ₁ hxZ (Subtype.ext (hW₁2 x hx₁))
  rw [mem_bot]
  exact congrArg Subtype.val h1

theorem exists_elementary_sixteen_lift {G H : Type*} [Group G] [Group H] [Finite G]
    (π : G →* H) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {E : Subgroup H}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hE16 : Nat.card E = 16) :
    ∃ V : Subgroup G, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
      Nat.card V = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hE16]; norm_num)
  obtain ⟨V, -, hV, hinj⟩ := exists_two_subgroup_map_eq π hπ hker E hEp
  obtain ⟨hc, h2, hcard⟩ := props_of_injective_map π hinj hV hEc hE2
  exact ⟨V, hc, h2, hcard.trans hE16⟩

end Sixteen

section Centralization

theorem le_of_isPerfect_of_map_le {Γ T : Type*} [Group Γ] [Group T] [Finite Γ] (ρ : Γ →* T)
    {K K₀ : Subgroup Γ} [hK₀n : K₀.Normal] (hK : Group.IsPerfect K) (hK₀K : K₀ ≤ K)
    (hmap : K.map ρ ≤ K₀.map ρ) (hsolv : Group.IsSolvable (K ⊓ ρ.ker : Subgroup Γ)) :
    K ≤ K₀ := by
  classical
  have hMn : (K₀.subgroupOf K).Normal := hK₀n.subgroupOf K
  let f : (K ⊓ ρ.ker : Subgroup Γ) →* K ⧸ K₀.subgroupOf K :=
    (QuotientGroup.mk' (K₀.subgroupOf K)).comp (Subgroup.inclusion inf_le_left)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (K₀.subgroupOf K) y
    obtain ⟨k₀, hk₀, hkk⟩ := hmap ⟨k, k.2, rfl⟩
    have hc : k₀⁻¹ * (k : Γ) ∈ (K ⊓ ρ.ker : Subgroup Γ) :=
      Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hK₀K hk₀)) k.2, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkk, inv_mul_cancel]⟩
    refine ⟨⟨_, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 : (((Subgroup.inclusion inf_le_left ⟨_, hc⟩ : K)⁻¹ * k : K) : Γ) =
        (k : Γ)⁻¹ * k₀ * (k : Γ)⁻¹⁻¹ := by
      simp [mul_assoc]
    rw [h1]
    exact hK₀n.conj_mem k₀ hk₀ (k : Γ)⁻¹
  have : Group.IsSolvable (K ⧸ K₀.subgroupOf K) := Group.isSolvable_of_surjective hf
  have : Group.IsPerfect K := hK
  intro k hk
  have h1 : QuotientGroup.mk' (K₀.subgroupOf K) ⟨k, hk⟩ = 1 := by
    rcases subsingleton_or_nontrivial (K ⧸ K₀.subgroupOf K) with h | h
    · exact Subsingleton.elim _ _
    · exact absurd ‹Group.IsSolvable (K ⧸ K₀.subgroupOf K)›
        (Group.IsPerfect.not_isSolvable (K ⧸ K₀.subgroupOf K))
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem le_centralizer_of_le_centralizer_fixing {Γ : Type*} [Group Γ] [Finite Γ] {q : ℕ}
    [Fact q.Prime] {K : Subgroup Γ} (hK : Group.IsPerfect K) (R : Subgroup Γ) [R.Normal]
    {D : Subgroup R} (hDfix : IsPGroup q (fixingSubgroup (MulAut R) (D : Set R)))
    (hKD : K ≤ centralizer ((D.map R.subtype : Subgroup Γ) : Set Γ)) :
    K ≤ centralizer (R : Set Γ) := by
  have : Group.IsPerfect K := hK
  let g : K →* MulAut R := (MulAut.conjNormal (H := R)).comp K.subtype
  have hrange : g.range ≤ fixingSubgroup (MulAut R) (D : Set R) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    change (k : Γ) * (d : Γ) * (k : Γ)⁻¹ = d
    have h1 := mem_centralizer_iff.mp (hKD k.2) (d : Γ) ⟨d, hd, rfl⟩
    rw [← h1, mul_inv_cancel_right]
  have hgp : IsPGroup q g.range := hDfix.to_le hrange
  have hgs : Group.IsSolvable g.range := by
    have := hgp.isNilpotent
    infer_instance
  intro x hx
  rw [mem_centralizer_iff]
  intro r hr
  have h1 := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : Γ))
    (CFSG.RankThree.Coprime.eq_one_of_isSolvable_range g hgs ⟨x, hx⟩)
  simp only [g, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h1
  change x * r * x⁻¹ = r at h1
  calc r * x = x * r * x⁻¹ * x := by rw [h1]
    _ = x * r := by group

variable {Γ : Type u} {T : Type v} [Group Γ] [Group T] [Finite Γ] [Finite T]

theorem perfectResidual_le_centralizer_of_normal_pGroup (ρ : Γ →* T)
    (hρ : Function.Surjective ρ) (hCsolv : Group.IsSolvable ρ.ker)
    (hCodd : Odd (Nat.card ρ.ker)) (S : Subgroup T) [S.Normal] (hES : layer S = ⊤)
    (hZS : IsPGroup 3 (center S))
    (hA : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ t : T, L₁.map (MulAut.conjNormal t).toMonoidHom = L₂)
    (h2 : 2 ≤ Nat.card (ComponentIndex S)) (hKS : (perfectResidual Γ).map ρ = S) {q : ℕ}
    [hq : Fact q.Prime] (hq3 : 3 < q) (hloc : localRank q Γ ≤ 2) (R : Subgroup Γ) [R.Normal]
    (hR : IsPGroup q R) :
    perfectResidual Γ ≤ centralizer (R : Set Γ) := by
  classical
  have hKperf : Group.IsPerfect (perfectResidual Γ) :=
    (perfect_residual_characterization (G := Γ)).2.2.1
  have hq2 : q ≠ 2 := by omega
  rcases subsingleton_or_nontrivial R with hRs | hRnt
  · intro x _
    rw [mem_centralizer_iff]
    intro r hr
    have : r = 1 := congrArg Subtype.val (Subsingleton.elim (⟨r, hr⟩ : R) 1)
    rw [this, one_mul, mul_one]
  obtain ⟨D, hDchar, hD1, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hR
  have : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD1
  have hD'n : (D.map R.subtype).Normal := inferInstance
  have hK₀n : (perfectResidual Γ ⊓ centralizer ((D.map R.subtype : Subgroup Γ) : Set Γ)).Normal :=
    inferInstance
  have hNn : ((perfectResidual Γ ⊓
      centralizer ((D.map R.subtype : Subgroup Γ) : Set Γ)).map ρ).Normal := hK₀n.map ρ hρ
  have hNS : (perfectResidual Γ ⊓
      centralizer ((D.map R.subtype : Subgroup Γ) : Set Γ)).map ρ ≤ S :=
    hKS ▸ map_mono inf_le_left
  rcases eq_or_le_center_of_transitive S hES hA _ hNS with hN | hN
  · have hsolv : Group.IsSolvable (perfectResidual Γ ⊓ ρ.ker : Subgroup Γ) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
    have hKK₀ := le_of_isPerfect_of_map_le ρ hKperf inf_le_left (by rw [hKS, hN]) hsolv
    exact le_centralizer_of_le_centralizer_fixing hKperf R hDfix (hKK₀.trans inf_le_right)
  · exfalso
    have hZodd : Odd (Nat.card (center S)) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := hZS.exists_card_eq
      rw [hk]
      exact Odd.pow (by decide)
    have h1 : 1 < Nat.card (ComponentIndex S) := by omega
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨L₁, L₂, hne⟩ := exists_pair_ne (ComponentIndex S)
    obtain ⟨E, hEc, hE2, hE16⟩ := exists_elementary_sixteen_of_components hES hZodd L₁.2 L₂.2
      fun h => hne (Subtype.ext h)
    have hmemS : ∀ k : perfectResidual Γ, ρ k ∈ S := fun k => hKS ▸ ⟨k, k.2, rfl⟩
    let π : perfectResidual Γ →* S := (ρ.comp (perfectResidual Γ).subtype).codRestrict S hmemS
    have hπ : Function.Surjective π := by
      intro s
      have hs : (s : T) ∈ (perfectResidual Γ).map ρ := hKS ▸ s.2
      obtain ⟨k, hk, hks⟩ := hs
      exact ⟨⟨k, hk⟩, Subtype.ext hks⟩
    have hπker : Odd (Nat.card π.ker) := by
      have h := MonoidHom.ker_codRestrict (ρ.comp (perfectResidual Γ).subtype) S hmemS
      change Odd (Nat.card ((ρ.comp (perfectResidual Γ).subtype).codRestrict S hmemS).ker)
      rw [h]
      exact Odd.of_dvd_nat hCodd (CFSG.RankThree.PerfectCover.card_ker_comp_subtype_dvd ρ _)
    obtain ⟨V₀, hV₀c, hV₀2, hV₀16⟩ := exists_elementary_sixteen_lift π hπ hπker hEc hE2 hE16
    have hVK : V₀.map (perfectResidual Γ).subtype ≤ perfectResidual Γ := map_subtype_le V₀
    have hVc : ∀ x ∈ V₀.map (perfectResidual Γ).subtype,
        ∀ y ∈ V₀.map (perfectResidual Γ).subtype, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hV₀c x hx y hy)
    have hV2 : ∀ x ∈ V₀.map (perfectResidual Γ).subtype, x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hV₀2 x hx)
    have hV16 : Nat.card (V₀.map (perfectResidual Γ).subtype) = 16 := by
      rw [card_map_of_injective (perfectResidual Γ).subtype_injective, hV₀16]
    have hexp : Monoid.exponent D = q := exponent_eq_of_forall_pow_eq_one hq.out fun x =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, hDexp x x.2, OneMemClass.coe_one])
    have hclass : D.lowerCentralSeries 2 = ⊥ := by
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
        Subgroup.lowerCentralSeries_zero, commutator_eq_bot_iff_le_centralizer]
      exact (commutator_mono le_rfl le_top).trans (hDcomm.trans inf_le_right)
    have hfix : ∀ t : Γ, orderOf t = 2 →
        pRank q (D.map R.subtype ⊓ centralizer {t} : Subgroup Γ) ≤ 2 := fun t ht =>
      ((pRank_le_of_injective hq.out.one_lt (Subgroup.inclusion inf_le_right)
        (Subgroup.inclusion_injective _)).trans
          (pRank_centralizer_le_localRank hq.out.one_lt ht)).trans hloc
    refine false_of_elementary_sixteen hq2 hR hexp hclass hfix _ hVc hV2 hV16
      fun a ha hcent => ?_
    have haK₀ : a ∈ perfectResidual Γ ⊓ centralizer ((D.map R.subtype : Subgroup Γ) : Set Γ) := by
      refine Subgroup.mem_inf.mpr ⟨hVK ha, ?_⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      have h := hcent d hd
      calc ((d : R) : Γ) * a = a * d * a⁻¹ * a := by rw [h]
        _ = a * d := by group
    have hρa : ρ a ∈ (center S).map S.subtype := hN ⟨a, haK₀, rfl⟩
    have ha2 : a ^ 2 = 1 := hV2 a ha
    have hρa1 : ρ a = 1 := by
      obtain ⟨z, hz, hza⟩ := hρa
      have hz2 : z ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        change (S.subtype z) ^ 2 = 1
        rw [hza, ← map_pow, ha2, map_one])
      have h3 : ¬ 3 ∣ Nat.card (zpowers z) := by
        rw [Nat.card_zpowers]
        intro h
        have := Nat.le_of_dvd (by norm_num) (h.trans (orderOf_dvd_of_pow_eq_one hz2))
        omega
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [← hza, CFSG.RankThree.PerfectCover.eq_one_of_mem_of_isPGroup_of_not_dvd hZS h3 hz
        (mem_zpowers z), map_one]
    exact CFSG.Wreathed.ConfinedOddCore.eq_one_of_sq_eq_one hCodd (show a ∈ ρ.ker from hρa1) ha2

theorem commutator_perfectResidual_ker_eq_bot (ρ : Γ →* T) (hρ : Function.Surjective ρ)
    (hCnil : Group.IsNilpotent ρ.ker) (hCodd : Odd (Nat.card ρ.ker))
    (hC3 : ¬ 3 ∣ Nat.card ρ.ker) (hloc : ∀ q : ℕ, q.Prime → 3 < q → localRank q Γ ≤ 2)
    (S : Subgroup T) [S.Normal] (hES : layer S = ⊤) (hZS : IsPGroup 3 (center S))
    (hA : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ t : T, L₁.map (MulAut.conjNormal t).toMonoidHom = L₂)
    (h2 : 2 ≤ Nat.card (ComponentIndex S)) (hKS : (perfectResidual Γ).map ρ = S) :
    ⁅perfectResidual Γ, ρ.ker⁆ = ⊥ := by
  have hCsolv : Group.IsSolvable ρ.ker := by
    have := hCnil
    infer_instance
  have hC : ρ.ker = (⨆ p ∈ (Nat.card ρ.ker).primeFactors,
      ((default : Sylow p ρ.ker) : Subgroup ρ.ker)).map ρ.ker.subtype := by
    rw [Sylow.iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer, hC, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun p hp => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr hpdvd)
  have hp3' : p ≠ 3 := by
    rintro rfl
    exact hC3 hpdvd
  have hp3 : 3 < p := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have : (CFSG.pCore p Γ).Normal := CFSG.pCore_normal
  have hcore := perfectResidual_le_centralizer_of_normal_pGroup ρ hρ hCsolv hCodd S hES hZS hA h2
    hKS hp3 (hloc p (Nat.prime_of_mem_primeFactors hp) hp3) (CFSG.pCore p Γ) CFSG.pCore_isPGroup
  exact (Sylow.map_le_pCore inferInstance hCnil p default).trans (le_centralizer_iff.mp hcore)

end Centralization

section CentralCover

variable {X Y : Type*} [Group X] [Group Y]

theorem not_le_center_of_isQuasisimple {J : Subgroup X} (hJ : IsQuasisimple J) :
    ¬ J ≤ center X := by
  intro hJZ
  obtain ⟨-, -, a, b, hab⟩ := hJ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h : a * b = b * a := Subtype.ext (mem_center_iff.mp (hJZ a.2) b).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isComponent_map_of_ker_le_center (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center X) {J : Subgroup X} (hJ : IsComponent J) : IsComponent (J.map π) :=
  ⟨isQuasisimple_map hJ.1 π fun h => not_le_center_of_isQuasisimple hJ.1 (h.trans hker),
    hJ.2.map hπ⟩

theorem eq_of_map_eq_of_isComponent [Finite X] (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center X) {J J' : Subgroup X} (hJ : IsComponent J) (hJ' : IsComponent J')
    (h : J.map π = J'.map π) : J = J' := by
  by_contra hne
  have hc : ⁅J, J'⁆ = ⊥ := (distinct_components_commute hJ hJ').resolve_left hne
  have hL := isComponent_map_of_ker_le_center π hπ hker hJ
  have hc' : ⁅J.map π, J'.map π⁆ = ⊥ := by rw [← Subgroup.map_commutator, hc, Subgroup.map_bot]
  rw [← h, Subgroup.isPerfect_iff.mp hL.1.1] at hc'
  have := isQuasisimple_nontrivial hL.1
  exact ((nontrivial_iff_ne_bot _).mp this) hc'

theorem isComponent_commutator_comap (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center X) {L : Subgroup Y} (hL : IsQuasisimple L) (hLn : L.Normal) :
    IsComponent ⁅L.comap π, L.comap π⁆ ∧ ⁅L.comap π, L.comap π⁆.map π = L := by
  set H := L.comap π with hH
  let πH : H →* L := (π.comp H.subtype).codRestrict L fun h => h.2
  have hπH : Function.Surjective πH := by
    intro l
    obtain ⟨x, hx⟩ := hπ l
    exact ⟨⟨x, show π x ∈ L by rw [hx]; exact l.2⟩, Subtype.ext hx⟩
  have hπHker : πH.ker ≤ center H := by
    intro h hh
    have hh' : (h : X) ∈ π.ker := by
      rw [MonoidHom.mem_ker] at hh ⊢
      exact congrArg Subtype.val hh
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hker hh') g)
  have hq := quasisimple_central_extension_derived_of_surjective πH hπH hπHker hL
  obtain ⟨-, -, hsurj⟩ := central_extension_derived_of_surjective πH hπH hπHker hL.1
  have hJ : (commutator H).map H.subtype = ⁅H, H⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hHn : H.Normal := hLn.comap π
  refine ⟨⟨?_, (Subgroup.commutator_normal H H).isSubnormal⟩, ?_⟩
  · rw [← hJ]
    exact isQuasisimple_of_mulEquiv ((commutator H).equivMapOfInjective _ H.subtype_injective) hq
  · refine le_antisymm ?_ fun l hl => ?_
    · rw [← hJ, Subgroup.map_map]
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    · obtain ⟨c, hc⟩ := hsurj ⟨l, hl⟩
      rw [← hJ]
      exact ⟨((c : H) : X), ⟨(c : H), c.2, rfl⟩, congrArg Subtype.val hc⟩

theorem layer_eq_top_of_central_cover [Finite X] [Finite Y] (hX : Group.IsPerfect X)
    (π : X →* Y) (hπ : Function.Surjective π) (hker : π.ker ≤ center X) (hY : layer Y = ⊤) :
    layer X = ⊤ := by
  have hmap : (layer X).map π = ⊤ := by
    rw [eq_top_iff, ← hY]
    refine sSup_le fun L hL => ?_
    obtain ⟨hJ, hJL⟩ := isComponent_commutator_comap π hπ hker hL.1
      (component_normal_of_layer_eq_top hY hL)
    rw [← hJL]
    exact map_mono (component_le_layer hJ)
  have hsup : layer X ⊔ center X = ⊤ := by
    have h := comap_map_eq π (layer X)
    rw [hmap, comap_top] at h
    exact eq_top_iff.mpr (h.le.trans (sup_le_sup_left hker _))
  exact (perfect_central_supplement hX).1 _ hsup

theorem exists_map_eq_of_transitive [Finite X] {I : Type*} (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) (φ : I → MulAut X) (ψ : I → MulAut Y)
    (hφψ : ∀ i x, π (φ i x) = ψ i (π x))
    (htrans : ∀ L₁ L₂ : Subgroup Y, IsComponent L₁ → IsComponent L₂ →
      ∃ i, L₁.map (ψ i).toMonoidHom = L₂)
    {J J' : Subgroup X} (hJ : IsComponent J) (hJ' : IsComponent J') :
    ∃ i, J.map (φ i).toMonoidHom = J' := by
  obtain ⟨i, hi⟩ := htrans _ _ (isComponent_map_of_ker_le_center π hπ hker hJ)
    (isComponent_map_of_ker_le_center π hπ hker hJ')
  refine ⟨i, eq_of_map_eq_of_isComponent π hπ hker (isComponent_map_mulEquiv (φ i) hJ) hJ' ?_⟩
  have hcomp : π.comp (φ i).toMonoidHom = (ψ i).toMonoidHom.comp π :=
    MonoidHom.ext fun x => hφψ i x
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hi]

theorem exists_component_dvd_card_center [Finite X] (hE : layer X = ⊤) {q : ℕ} (hq : q.Prime)
    (hqZ : q ∣ Nat.card (center X)) :
    ∃ J : Subgroup X, IsComponent J ∧ q ∣ Nat.card (center J) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center X) q hqZ
  obtain ⟨x, hx⟩ := exists_layerMul_eq (show (z : X) ∈ layer X from hE ▸ mem_top _)
  have hzc : layerMul X x ∈ centralizer (layer X : Set X) := by
    rw [hx, hE, coe_top, centralizer_univ]
    exact z.2
  have hxc := (layerMul_mem_centralizer_iff x).mp hzc
  have hzm : (z : X) ^ (∏ J : ComponentIndex X, Nat.card (center J.1)) = 1 := by
    rw [← hx, ← map_pow]
    convert map_one (layerMul X)
    funext J
    obtain ⟨k, hk⟩ : Nat.card (center J.1) ∣ ∏ J : ComponentIndex X, Nat.card (center J.1) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ J)
    have h1 : (⟨x J, hxc J⟩ : center J.1) ^ Nat.card (center J.1) = 1 := pow_card_eq_one'
    have h2 : x J ^ Nat.card (center J.1) = 1 := congrArg Subtype.val h1
    rw [Pi.pow_apply, hk, pow_mul, h2, one_pow, Pi.one_apply]
  have hqm : q ∣ ∏ J : ComponentIndex X, Nat.card (center J.1) := by
    rw [← hz, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hzm
  obtain ⟨J, -, hJ⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqm
  exact ⟨J.1, J.2, hJ⟩

end CentralCover

section RankContradiction

variable {X : Type*} [Group X] [Finite X]

theorem not_dvd_card_center_of_three_components {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hrank : ∀ u : X, orderOf u = 2 → pRank q (centralizer {u} : Subgroup X) ≤ 2)
    {J₁ J₂ J₃ : Subgroup X} (h₁ : IsComponent J₁) (h₂ : IsComponent J₂) (h₃ : IsComponent J₃)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) (hcard : Nat.card J₂ = Nat.card J₁) :
    ¬ q ∣ Nat.card (center J₁) := by
  intro hqZ
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := J₃) 2
    (even_iff_two_dvd.mp (even_card_of_isQuasisimple h₃.1))
  have hu' : orderOf (u : X) = 2 := (Subgroup.orderOf_coe u).trans hu
  have hJc : ∀ J : Subgroup X, IsComponent J → J ≠ J₃ → J ≤ centralizer {(u : X)} :=
    fun J hJ hne => (le_centralizer_of_components hJ h₃ hne).trans
      (centralizer_le (Set.singleton_subset_iff.mpr u.2))
  have hrankJ : ∀ J : Subgroup X, J ≤ centralizer {(u : X)} → pRank q J ≤ 2 := fun J hJ =>
    (pRank_le_of_injective hq.one_lt (Subgroup.inclusion hJ)
      (Subgroup.inclusion_injective hJ)).trans (hrank u hu')
  have : Group.IsPerfect J₂ := h₂.1.1
  have : Group.IsPerfect J₁ := h₁.1.1
  have hZ₂ : pRank q (center J₂) ≤ 1 :=
    (perfect_rank_two_large_prime_center hq hq3 (hrankJ J₂ (hJc J₂ h₂ h23))).2
  have hqJ₂ : q ∣ Nat.card J₂ := hcard ▸ hqZ.trans (card_subgroup_dvd_card (center J₁))
  obtain ⟨x, hxq, hxZ⟩ := (perfect_cyclic_center_odd_elements hq2 hqJ₂).1 hZ₂
  obtain ⟨B₀, hB₀, hB₀card⟩ := exists_elemAbelian_sq_of_dvd_card_center hq2 hqZ
  have hB : CFSG.Open.IsElemAbelian q (B₀.map J₁.subtype) := isElemAbelian_map hB₀ _
  have hBcard : Nat.card (B₀.map J₁.subtype) = q ^ 2 := by
    rw [card_map_of_injective J₁.subtype_injective, hB₀card]
  have hBJ₁ : B₀.map J₁.subtype ≤ J₁ := map_subtype_le _
  have hJ₁J₂ := le_centralizer_of_components h₁ h₂ h12
  have hbc : ∀ e ∈ B₀.map J₁.subtype, Commute e (x : X) := fun e he =>
    (mem_centralizer_iff.mp (hJ₁J₂ (hBJ₁ he)) x x.2).symm
  have hbq : (x : X) ^ q = 1 := by
    rw [← hxq, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  have hbB : (x : X) ∉ B₀.map J₁.subtype := by
    intro hxB
    apply hxZ
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp (hJ₁J₂ (hBJ₁ hxB)) g g.2)
  have h3 := succ_le_pRank_of_commute hq hB hBcard hbc hbq hbB
    (hBJ₁.trans (hJc J₁ h₁ h13)) (hJc J₂ h₂ h23 x.2)
  have h2 := hrank u hu'
  rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup] at h2
  omega

theorem ker_eq_bot_of_transitive_central_cover {Y I : Type*} [Group Y] [Finite Y]
    (hX : Group.IsPerfect X) (π : X →* Y) (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hodd : Odd (Nat.card π.ker)) (h3 : ¬ 3 ∣ Nat.card π.ker) (hY : layer Y = ⊤)
    (hd : 3 ≤ Nat.card (ComponentIndex Y)) (φ : I → MulAut X) (ψ : I → MulAut Y)
    (hφψ : ∀ i x, π (φ i x) = ψ i (π x))
    (htrans : ∀ L₁ L₂ : Subgroup Y, IsComponent L₁ → IsComponent L₂ →
      ∃ i, L₁.map (ψ i).toMonoidHom = L₂)
    (hrank : ∀ q : ℕ, q.Prime → 3 < q → ∀ u : X, orderOf u = 2 →
      pRank q (centralizer {u} : Subgroup X) ≤ 2) :
    π.ker = ⊥ := by
  classical
  by_contra hne
  have hcard1 : Nat.card π.ker ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard1
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqdvd)
  have hq3' : q ≠ 3 := by
    rintro rfl
    exact h3 hqdvd
  have hq3 : 3 < q := by
    have := hq.two_le
    omega
  have hEX : layer X = ⊤ := layer_eq_top_of_central_cover hX π hπ hker hY
  obtain ⟨J₁, hJ₁, hqJ₁⟩ := exists_component_dvd_card_center hEX hq
    (hqdvd.trans (card_dvd_of_le hker))
  have hlift : ∀ L : ComponentIndex Y, IsComponent ⁅L.1.comap π, L.1.comap π⁆ ∧
      ⁅L.1.comap π, L.1.comap π⁆.map π = L.1 := fun L =>
    isComponent_commutator_comap π hπ hker L.2.1 (component_normal_of_layer_eq_top hY L.2)
  have h3X : 3 ≤ Nat.card (ComponentIndex X) := by
    let f : ComponentIndex Y → ComponentIndex X := fun L => ⟨_, (hlift L).1⟩
    have hf : Function.Injective f := by
      intro L L' h
      apply Subtype.ext
      rw [← (hlift L).2, ← (hlift L').2]
      exact congrArg (fun J : ComponentIndex X => J.1.map π) h
    exact hd.trans (Nat.card_le_card_of_injective f hf)
  obtain ⟨J₂, hJ₂, h12⟩ := exists_other_component (by omega) hJ₁
  obtain ⟨J₃, hJ₃, h13, h23⟩ := exists_component_ne_ne h3X J₁ J₂
  have hcard : Nat.card J₂ = Nat.card J₁ := by
    obtain ⟨i, hi⟩ := exists_map_eq_of_transitive π hπ hker φ ψ hφψ htrans hJ₁ hJ₂
    rw [← hi, card_map_of_injective (φ i).injective]
  exact not_dvd_card_center_of_three_components hq hq3 (hrank q hq hq3) hJ₁ hJ₂ hJ₃ h12 h13 h23
    hcard hqJ₁

end RankContradiction

section MinimalCover

variable {Γ : Type u} {T : Type v} [Group Γ] [Group T] [Finite Γ] [Finite T]

theorem ker_eq_bot_of_minimal_cover (ρ : Γ →* T) (hρ : Function.Surjective ρ)
    (hmin : ∀ Y : Subgroup Γ, Y.map ρ = ⊤ → Y = ⊤) (S : Subgroup T) [S.Normal]
    (hTS : IsPGroup 3 (T ⧸ S)) (K : Subgroup Γ) [K.Normal] (hKS : K.map ρ = S)
    (hKC : K ⊓ ρ.ker = ⊥) (hC3 : ¬ 3 ∣ Nat.card ρ.ker) : ρ.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Γ) := inferInstance
  have hST : S ⊔ (P : Subgroup Γ).map ρ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hρ, ← Subgroup.index_eq_one]
    obtain ⟨k, hk⟩ := hTS.exists_card_eq
    have h1 : (S ⊔ (P.mapSurjective hρ : Subgroup T)).index ∣ 3 ^ k :=
      (Subgroup.index_dvd_of_le le_sup_left).trans hk.dvd
    have h2 : (S ⊔ (P.mapSurjective hρ : Subgroup T)).index ∣
        ((P.mapSurjective hρ : Sylow 3 T) : Subgroup T).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have hcop : Nat.Coprime 3 (S ⊔ (P.mapSurjective hρ : Subgroup T)).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
        (P.mapSurjective hρ).not_dvd_index (h.trans h2)
    exact Nat.eq_one_of_dvd_one ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸ Nat.dvd_gcd h1 dvd_rfl)
  have hKP : K ⊔ (P : Subgroup Γ) = ⊤ := hmin _ (by rw [Subgroup.map_sup, hKS, hST])
  rw [eq_bot_iff]
  intro c hc
  have hcK : c ∈ K := by
    have hmap : (⊤ : Subgroup Γ).map (QuotientGroup.mk' K) =
        (P : Subgroup Γ).map (QuotientGroup.mk' K) := by
      rw [← hKP, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    obtain ⟨p, hp, hpc⟩ : QuotientGroup.mk' K c ∈ (P : Subgroup Γ).map (QuotientGroup.mk' K) :=
      hmap ▸ ⟨c, mem_top c, rfl⟩
    have h1 : orderOf (QuotientGroup.mk' K c) ∣ Nat.card ρ.ker :=
      (orderOf_map_dvd _ c).trans (Subgroup.orderOf_dvd_natCard _ hc)
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have h2 : orderOf (QuotientGroup.mk' K c) ∣ 3 ^ n := by
      rw [← hpc, ← hn]
      exact (orderOf_map_dvd _ p).trans (Subgroup.orderOf_dvd_natCard _ hp)
    have hcop : Nat.Coprime (3 ^ n) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3)
    have h3 : orderOf (QuotientGroup.mk' K c) = 1 :=
      Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  have h : c ∈ K ⊓ ρ.ker := Subgroup.mem_inf.mpr ⟨hcK, hc⟩
  rwa [hKC] at h

end MinimalCover

section Product

variable {G ι : Type*} [Group G] [Fintype ι] {H : ι → Subgroup G}

theorem noncommPiCoprod_eq_list_prod
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (x : ∀ i, H i)
    {l : List ι} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Subgroup.noncommPiCoprod hcomm x = (l.map fun i => (x i : G)).prod := by
  classical
  have hc : (l.toFinset : Set ι).Pairwise (Function.onFun Commute fun i => (x i : G)) :=
    fun i _ j _ h => hcomm h _ _ (x i).2 (x j).2
  rw [← Finset.noncommProd_toFinset l _ hc hl, Subgroup.noncommPiCoprod_apply]
  exact Finset.noncommProd_congr (by ext i; simp [hall]) (fun _ _ => rfl) _

theorem noncommPiCoprod_mem_center_of_eq_one [DecidableEq ι]
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) {x : ∀ i, H i}
    (hx : Subgroup.noncommPiCoprod hcomm x = 1) (i : ι) : x i ∈ center (H i) := by
  have hxy : x = Pi.mulSingle i (x i) * Function.update x i 1 := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
  have hyc : Subgroup.noncommPiCoprod hcomm (Function.update x i 1) ∈
      centralizer (H i : Set G) := by
    rw [Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
    by_cases h : j = i
    · subst h
      simp
    · rw [Function.update_of_ne h, mem_centralizer_iff]
      intro g hg
      exact (hcomm (Ne.symm h) g (x j) hg (x j).2).eq
  have h1 := congrArg (Subgroup.noncommPiCoprod hcomm) hxy
  rw [map_mul, Subgroup.noncommPiCoprod_mulSingle, hx] at h1
  have h2 : (x i : G) = (Subgroup.noncommPiCoprod hcomm (Function.update x i 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  have h3 := mem_centralizer_iff.mp (inv_mem hyc) g g.2
  rw [← h2] at h3
  exact h3

end Product

section ComponentProduct

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem central_cover_component_product (hX : Group.IsPerfect X) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) (hY : layer Y = ⊤)
    (H : ComponentIndex Y → Subgroup X) (hH : ∀ L, H L = L.1.comap π) :
    (∀ L : ComponentIndex Y, IsComponent ⁅H L, H L⁆ ∧ ⁅H L, H L⁆.map π = L.1) ∧
      ⨆ L : ComponentIndex Y, ⁅H L, H L⁆ = ⊤ ∧
      ∃ μ : (∀ L : ComponentIndex Y, ↥⁅H L, H L⁆) →* X,
        (∀ (L : ComponentIndex Y) (k : ↥⁅H L, H L⁆), μ (Pi.mulSingle L k) = k) ∧
        (∀ (x : ∀ L : ComponentIndex Y, ↥⁅H L, H L⁆) (l : List (ComponentIndex Y)), l.Nodup →
          (∀ L, L ∈ l) → μ x = (l.map fun L => (x L : X)).prod) ∧
        Function.Surjective μ ∧
        ∀ x, x ∈ μ.ker ↔ (∀ L, x L ∈ center ↥⁅H L, H L⁆) ∧ μ x = 1 := by
  have hcomp : ∀ L : ComponentIndex Y, IsComponent ⁅H L, H L⁆ ∧ ⁅H L, H L⁆.map π = L.1 := by
    intro L
    rw [hH L]
    exact isComponent_commutator_comap π hπ hker L.2.1 (component_normal_of_layer_eq_top hY L.2)
  have hsup : ⨆ L : ComponentIndex Y, ⁅H L, H L⁆ = ⊤ := by
    have hmap : (⨆ L : ComponentIndex Y, ⁅H L, H L⁆).map π = ⊤ := by
      rw [Subgroup.map_iSup, eq_top_iff, ← hY]
      exact sSup_le fun L hL => le_iSup_of_le ⟨L, hL⟩ (hcomp ⟨L, hL⟩).2.ge
    have h := comap_map_eq π (⨆ L : ComponentIndex Y, ⁅H L, H L⁆)
    rw [hmap, comap_top] at h
    exact (perfect_central_supplement hX).1 _
      (eq_top_iff.mpr (h.le.trans (sup_le_sup_left hker _)))
  have hcomm : Pairwise fun L L' : ComponentIndex Y =>
      ∀ x y : X, x ∈ ⁅H L, H L⁆ → y ∈ ⁅H L', H L'⁆ → Commute x y := by
    intro L L' hne x y hx hy
    have hne' : ⁅H L, H L⁆ ≠ ⁅H L', H L'⁆ := by
      intro h
      apply hne
      apply Subtype.ext
      rw [← (hcomp L).2, ← (hcomp L').2, h]
    have hc := le_centralizer_of_components (hcomp L).1 (hcomp L').1 hne'
    exact (mem_centralizer_iff.mp (hc hx) y hy).symm
  let μ : (∀ L : ComponentIndex Y, ↥⁅H L, H L⁆) →* X := Subgroup.noncommPiCoprod hcomm
  refine ⟨hcomp, hsup, μ, fun L k => ?_, fun x l hl hall => ?_, ?_, fun x => ?_⟩
  · exact Subgroup.noncommPiCoprod_mulSingle (H := fun L => ⁅H L, H L⁆) (hcomm := hcomm) L k
  · exact noncommPiCoprod_eq_list_prod hcomm x hl hall
  · rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range, hsup]
  · rw [MonoidHom.mem_ker]
    exact ⟨fun h => ⟨noncommPiCoprod_mem_center_of_eq_one hcomm h, h⟩, fun h => h.2⟩

end ComponentProduct

section Main

theorem perfectResidual_map_eq_of_semisimple {Γ T : Type*} [Group Γ] [Group T] [Finite Γ]
    [Finite T] (ρ : Γ →* T) (hρ : Function.Surjective ρ) (S : Subgroup T) [S.Normal]
    (hES : layer S = ⊤) (hTS : IsPGroup 3 (T ⧸ S)) : (perfectResidual Γ).map ρ = S := by
  have h1 : (perfectResidual Γ).map ρ = perfectResidual T :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ρ hρ
  rw [h1]
  have hSperf : Group.IsPerfect S := by
    have h : Group.IsPerfect (layer S) := layer_isPerfect
    rw [hES] at h
    exact Group.IsPerfect.top_iff.mp h
  have hsolv : Group.IsSolvable (T ⧸ S) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := hTS.isNilpotent
    infer_instance
  exact le_antisymm (((perfect_residual_characterization (G := T)).2.2.2.2.1 S).mp hsolv)
    ((perfect_residual_transport (G := T) (MonoidHom.id T)).2.2 S hSperf)

variable {Γ : Type u} {T : Type v} [Group Γ] [Group T] [Finite Γ] [Finite T]

theorem odd_three_complement_transitive_semisimple_minimal_cover_trivial_kernel (ρ : Γ →* T)
    (hρ : Function.Surjective ρ) (hmin : ∀ Y : Subgroup Γ, Y ≠ ⊤ → Y.map ρ ≠ ⊤)
    (hCnil : Group.IsNilpotent ρ.ker) (hCodd : Odd (Nat.card ρ.ker))
    (hC3 : Nat.Coprime (Nat.card ρ.ker) 3)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → localRank q Γ ≤ 2) (S : Subgroup T) [S.Normal]
    (hES : layer S = ⊤) (hTS : IsPGroup 3 (T ⧸ S)) (hZS : IsPGroup 3 (center S))
    (hd : 3 ≤ Nat.card (ComponentIndex S)) (A : Subgroup Γ)
    (hA : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ a ∈ A, L₁.map (MulAut.conjNormal (ρ a)).toMonoidHom = L₂) :
    let K := perfectResidual Γ
    let H : ComponentIndex S → Subgroup K := fun L =>
      (L.1.map S.subtype).comap (ρ.comp K.subtype)
    K.map ρ = S ∧ ⁅K, ρ.ker⁆ = ⊥ ∧ K ⊓ ρ.ker = ⊥ ∧ ρ.ker = ⊥ ∧
      (∃ e : Γ ≃* T, ∀ g, e g = ρ g) ∧ (∃ e : K ≃* S, ∀ k : K, (e k : T) = ρ k) ∧
      (∀ L : ComponentIndex S, IsComponent ⁅H L, H L⁆ ∧
        ⁅H L, H L⁆.map (ρ.comp K.subtype) = L.1.map S.subtype) ∧
      ⨆ L : ComponentIndex S, ⁅H L, H L⁆ = ⊤ ∧
      ∃ μ : (∀ L : ComponentIndex S, ↥⁅H L, H L⁆) →* K,
        (∀ (L : ComponentIndex S) (k : ↥⁅H L, H L⁆), μ (Pi.mulSingle L k) = k) ∧
        (∀ (x : ∀ L : ComponentIndex S, ↥⁅H L, H L⁆) (l : List (ComponentIndex S)), l.Nodup →
          (∀ L, L ∈ l) → μ x = (l.map fun L => (x L : K)).prod) ∧
        Function.Surjective μ ∧
        ∀ x, x ∈ μ.ker ↔ (∀ L, x L ∈ center ↥⁅H L, H L⁆) ∧ μ x = 1 := by
  intro K H
  have hmin' : ∀ Y : Subgroup Γ, Y.map ρ = ⊤ → Y = ⊤ := fun Y hY => by
    by_contra h
    exact hmin Y h hY
  have hC3' : ¬ 3 ∣ Nat.card ρ.ker :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hC3.symm
  have hA' : ∀ L₁ L₂ : Subgroup S, IsComponent L₁ → IsComponent L₂ →
      ∃ t : T, L₁.map (MulAut.conjNormal t).toMonoidHom = L₂ := fun L₁ L₂ h₁ h₂ => by
    obtain ⟨a, -, h⟩ := hA L₁ L₂ h₁ h₂
    exact ⟨ρ a, h⟩
  have hKperf : Group.IsPerfect K := (perfect_residual_characterization (G := Γ)).2.2.1
  have hKS : K.map ρ = S := perfectResidual_map_eq_of_semisimple ρ hρ S hES hTS
  have hKC : ⁅K, ρ.ker⁆ = ⊥ := commutator_perfectResidual_ker_eq_bot ρ hρ hCnil hCodd hC3' hloc
    S hES hZS hA' (by omega) hKS
  have hmemS : ∀ k : K, ρ k ∈ S := fun k => hKS ▸ ⟨k, k.2, rfl⟩
  let π : K →* S := (ρ.comp K.subtype).codRestrict S hmemS
  have hπapp : ∀ k : K, ((π k : S) : T) = ρ k := fun _ => rfl
  have hπ : Function.Surjective π := by
    intro s
    have hs : (s : T) ∈ K.map ρ := hKS ▸ s.2
    obtain ⟨k, hk, hks⟩ := hs
    exact ⟨⟨k, hk⟩, Subtype.ext hks⟩
  have hπker : ∀ k : K, k ∈ π.ker ↔ (k : Γ) ∈ ρ.ker := fun k => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hπapp, ← OneMemClass.coe_one S,
      Subtype.ext_iff]
  have hπcard : Nat.card π.ker ∣ Nat.card ρ.ker := by
    have h := MonoidHom.ker_codRestrict (ρ.comp K.subtype) S hmemS
    change Nat.card ((ρ.comp K.subtype).codRestrict S hmemS).ker ∣ _
    rw [h]
    exact CFSG.RankThree.PerfectCover.card_ker_comp_subtype_dvd ρ K
  have hπZ : π.ker ≤ center K := by
    intro k hk
    have hkC : (k : Γ) ∈ ρ.ker := (hπker k).mp hk
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have h := commutator_eq_bot_iff_le_centralizer.mp hKC g.2
    exact (mem_centralizer_iff.mp h (k : Γ) hkC).symm
  have hrankK : ∀ q : ℕ, q.Prime → 3 < q → ∀ u : K, orderOf u = 2 →
      pRank q (centralizer {u} : Subgroup K) ≤ 2 := by
    intro q hq hq3 u hu
    have hu' : orderOf (u : Γ) = 2 := (Subgroup.orderOf_coe u).trans hu
    have hmem : ∀ c : (centralizer {u} : Subgroup K),
        ((c : K) : Γ) ∈ (centralizer {(u : Γ)} : Subgroup Γ) := by
      intro c
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2)
    let f := (K.subtype.comp (centralizer {u} : Subgroup K).subtype).codRestrict _ hmem
    have hf : Function.Injective f := fun a b h => by
      have h' : ((f a : Γ)) = (f b : Γ) := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    exact ((pRank_le_of_injective hq.one_lt f hf).trans
      (pRank_centralizer_le_localRank hq.one_lt hu')).trans (hloc q hq hq3)
  have hφψ : ∀ (a : A) (k : K),
      π (MulAut.conjNormal (a : Γ) k) = MulAut.conjNormal (ρ a) (π k) := by
    intro a k
    apply Subtype.ext
    rw [hπapp, MulAut.conjNormal_apply, MulAut.conjNormal_apply, hπapp, map_mul, map_mul, map_inv]
  have hπbot : π.ker = ⊥ := ker_eq_bot_of_transitive_central_cover hKperf π hπ hπZ
    (Odd.of_dvd_nat hCodd hπcard) (fun h => hC3' (h.trans hπcard)) hES hd
    (fun a : A => MulAut.conjNormal (a : Γ)) (fun a : A => MulAut.conjNormal (ρ a)) hφψ
    (fun L₁ L₂ h₁ h₂ => by
      obtain ⟨a, ha, h⟩ := hA L₁ L₂ h₁ h₂
      exact ⟨⟨a, ha⟩, h⟩) hrankK
  have hKC0 : K ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h : (⟨g, hg.1⟩ : K) ∈ π.ker := (hπker _).mpr hg.2
    rw [hπbot, mem_bot] at h
    exact (mem_bot).mpr (congrArg Subtype.val h)
  have hC : ρ.ker = ⊥ := ker_eq_bot_of_minimal_cover ρ hρ hmin' S hTS K hKS hKC0 hC3'
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπbot
  have hH : ∀ L : ComponentIndex S, H L = L.1.comap π := by
    intro L
    have hcomp : ρ.comp K.subtype = S.subtype.comp π := MonoidHom.ext fun _ => rfl
    change (L.1.map S.subtype).comap (ρ.comp K.subtype) = _
    rw [hcomp, ← Subgroup.comap_comap, Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  obtain ⟨hcomp, hsup, hμ⟩ := central_cover_component_product hKperf π hπ hπZ hES H hH
  refine ⟨hKS, hKC, hKC0, hC, ⟨MulEquiv.ofBijective ρ ⟨(MonoidHom.ker_eq_bot_iff ρ).mp hC, hρ⟩,
    fun _ => rfl⟩, ⟨MulEquiv.ofBijective π ⟨hπinj, hπ⟩, fun _ => rfl⟩, fun L => ⟨(hcomp L).1, ?_⟩,
    hsup, hμ⟩
  have hcomp' : ρ.comp K.subtype = S.subtype.comp π := MonoidHom.ext fun _ => rfl
  rw [hcomp', ← Subgroup.map_map, (hcomp L).2]

end Main

end CFSG.RankThree.OddKernel
