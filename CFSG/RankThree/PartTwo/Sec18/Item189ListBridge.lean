module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListBasic
public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectI
public import CFSG.RankThree.PartTwo.Sec18.Item189KType
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
public import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Bridge

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem c_mem_sk189 (M H : Subgroup G) (c : G) : c ∈ sk189 M H c :=
  (le_sup_right : normalClosureIn M c ≤ sk189 M H c)
    (Subgroup.subset_closure ⟨1, M.one_mem, by group⟩)

noncomputable def cAlpha189 (M H : Subgroup G) (c : G) : SKAlpha189 M H c :=
  alpha189 M H c ⟨c, c_mem_sk189 M H c⟩

theorem gammaInv_sAlpha189 (h : Sec18H G A M H c) :
    GammaInv189 (Sec4.autThetaQuot A (sk189 M H c)) (sAlpha189 M H c) := by
  intro γ hγ t ht
  obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hγ
  obtain ⟨x, hx, rfl⟩ := ht
  have hx' : x ∈ (s189 M H).subgroupOf (sk189 M H c) := hx
  refine ⟨(sk189 M H c).normalizerMonoidHom ⟨a, haN⟩ x, ?_, rfl⟩
  show _ ∈ (s189 M H).subgroupOf (sk189 M H c)
  rw [Subgroup.mem_subgroupOf, Sec4.normalizerMonoidHom_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_s189 h haA) (x : G)).mp
    (Subgroup.mem_subgroupOf.mp hx')

theorem sAlpha189_maximal (h186 : Item186H) (h : Sec18H G A M H c) (h7 : Hyp187 A M H c)
    {T : Subgroup (SKAlpha189 M H c)} (hT : IsPGroup 2 T) (hST : sAlpha189 M H c ≤ T)
    (hinv : GammaInv189 (Sec4.autThetaQuot A (sk189 M H c)) T) : T = sAlpha189 M H c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set T' : Subgroup ↥(sk189 M H c) := T.comap (alpha189 M H c) with hT'
  set Tt : Subgroup G := T'.map (sk189 M H c).subtype with hTt
  have hkey : ∀ a ∈ A, ∀ g ∈ Tt, a * g * a⁻¹ ∈ Tt := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer ((sk189 M H c : Subgroup G) : Set G) :=
      le_normalizer_sk189 h ha
    have hγ : Sec4.thetaQuotMulAut ↥(sk189 M H c) ((sk189 M H c).normalizerMonoidHom ⟨a, haN⟩) ∈
        Sec4.autThetaQuot A (sk189 M H c) := Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨(sk189 M H c).normalizerMonoidHom ⟨a, haN⟩ k, hinv _ hγ _ hk,
      Sec4.normalizerMonoidHom_apply_coe haN k⟩
  have hAT : A ≤ Subgroup.normalizer (Tt : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hkey a ha g, fun hg => ?_⟩
    have := hkey a⁻¹ (A.inv_mem ha) _ hg
    simpa [mul_assoc] using this
  have hT3 : ¬ 3 ∣ Nat.card Tt := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp z.2
    have hk3 : orderOf k = 3 := by
      rw [← Subgroup.orderOf_coe k]
      change orderOf ((sk189 M H c).subtype k) = 3
      rw [hkz, Subgroup.orderOf_coe, hz]
    have hαk : alpha189 M H c k ∈ T := hk
    have hord : orderOf (alpha189 M H c k) = 1 := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨_, hαk⟩
      rw [Subgroup.orderOf_mk] at hj
      have h1 : orderOf (alpha189 M H c k) ∣ orderOf k := orderOf_map_dvd (alpha189 M H c) k
      rw [hk3] at h1
      rw [hj] at h1 ⊢
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
      · exact h2
      · exfalso
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simp at h2
        · have : 2 ∣ 2 ^ j := dvd_pow_self 2 hjpos.ne'
          rw [h2] at this
          omega
    have hk1 : alpha189 M H c k = 1 := orderOf_eq_one_iff.mp hord
    have hkθ : k ∈ aschbacherSolvableCore 3 ↥(sk189 M H c) := (QuotientGroup.eq_one_iff k).mp hk1
    have hmem : (k : G) ∈ theta189 M H c := ⟨k, hkθ, rfl⟩
    have h3dvd : orderOf (k : G) ∣ Nat.card (theta189 M H c) := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_coe, hk3] at h3dvd
    exact not_three_dvd_card_theta189 M H c h3dvd
  have hST' : s189 M H ≤ Tt := by
    intro s hs
    have hsSK : s ∈ sk189 M H c := (le_sup_left : s189 M H ≤ sk189 M H c) hs
    exact ⟨⟨s, hsSK⟩, hST ⟨⟨s, hsSK⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, rfl⟩
  obtain ⟨T₂, hT₂, hST₂, hAT₂⟩ := exists_isSylowOf_le_of_coprime189 (p := 3) (q := 2)
    hA.isPGroup hAT hT3 hST' (isPGroup_s189 M H) (le_normalizer_s189 h)
  have hT₂S : T₂ = s189 M H :=
    (mem_maxInvariantPiSubgroups_iff.mp (s189_mem_maxInvariant h186 h h7)).2 T₂
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT₂.isPGroup, hAT₂⟩) hST₂
  rw [hT₂S] at hT₂
  have hodd : ¬ 2 ∣ (s189 M H).relIndex Tt := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT₂).2.2
  have hS' : ((s189 M H).subgroupOf (sk189 M H c)).map (sk189 M H c).subtype = s189 M H :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hrel : (s189 M H).relIndex Tt =
      ((s189 M H).subgroupOf (sk189 M H c)).relIndex T' := by
    conv_lhs => rw [← hS']
    exact Subgroup.relIndex_map_map_of_injective _ _ (sk189 M H c).subtype_injective
  have hcomap : ((sAlpha189 M H c).comap (alpha189 M H c)).relIndex T' =
      (sAlpha189 M H c).relIndex T := by
    rw [Subgroup.relIndex_comap (H := sAlpha189 M H c) (alpha189 M H c) T']
    congr 1
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) T
  have hdvd : (sAlpha189 M H c).relIndex T ∣ (s189 M H).relIndex Tt := by
    rw [hrel, ← hcomap]
    have hle : ((s189 M H).subgroupOf (sk189 M H c)) ≤ (sAlpha189 M H c).comap (alpha189 M H c) :=
      fun s hs => Subgroup.mem_map_of_mem _ hs
    exact Subgroup.relIndex_dvd_of_le_left T' hle
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (sAlpha189 M H c).relIndex T = 2 ^ n := by
    have := hT.index ((sAlpha189 M H c).subgroupOf T)
    exact this
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans (hn ▸ hdvd))
  rw [hn0, pow_zero] at hn
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hn) hST

theorem autThetaQuot_comm189 (h : Sec18H G A M H c) {γ δ : MulAut (SKAlpha189 M H c)}
    (hγ : γ ∈ Sec4.autThetaQuot A (sk189 M H c)) (hδ : δ ∈ Sec4.autThetaQuot A (sk189 M H c)) :
    γ * δ = δ * γ :=
  Sec13.autThetaQuot_commute (E := A) (L := sk189 M H c)
    (fun x hx y hy => congrArg Subtype.val
      ((isE27_of_mem_partTwoE h.mem_partTwoE).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hγ hδ

theorem autThetaQuot_pow_three189 (h : Sec18H G A M H c) {γ : MulAut (SKAlpha189 M H c)}
    (hγ : γ ∈ Sec4.autThetaQuot A (sk189 M H c)) : γ ^ 3 = 1 :=
  Sec13.autThetaQuot_pow_three (E := A) (L := sk189 M H c)
    (isE27_of_mem_partTwoE h.mem_partTwoE).1.2 hγ

theorem conj_cAlpha189_mem (h : Sec18H G A M H c) :
    MulAut.conj (cAlpha189 M H c) ∈ Sec4.autThetaQuot A (sk189 M H c) := by
  have hcA : c ∈ A := mem_of_sec18H189 h
  have hN : c ∈ Subgroup.normalizer (sk189 M H c : Set G) := le_normalizer_sk189 h hcA
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨c, hN, hcA, ?_⟩
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    have e : (sk189 M H c).normalizerMonoidHom ⟨c, hN⟩ g =
        (⟨c, c_mem_sk189 M H c⟩ : ↥(sk189 M H c)) * g *
          (⟨c, c_mem_sk189 M H c⟩ : ↥(sk189 M H c))⁻¹ := Subtype.ext rfl
    show alpha189 M H c ((sk189 M H c).normalizerMonoidHom ⟨c, hN⟩ g) = _
    rw [e, map_mul, map_mul, map_inv, MulAut.conj_apply]
    rfl

theorem cAlpha189_mem_kAlpha (h : Sec18H G A M H c) : cAlpha189 M H c ∈ kAlpha189 M H c :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Sec20.self_mem_normalClosureIn M c))

theorem orderOf_cAlpha189 (h : Sec18H G A M H c) (hc1 : c ≠ 1) :
    orderOf (cAlpha189 M H c) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 := pow_three_of_sec18H189 h
  have hcSK : c ∈ sk189 M H c := c_mem_sk189 M H c
  have hcb3 : cAlpha189 M H c ^ 3 = 1 := by
    rw [cAlpha189, ← map_pow]
    have : (⟨c, hcSK⟩ : ↥(sk189 M H c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hcb1 : cAlpha189 M H c ≠ 1 := by
    intro h1
    rw [cAlpha189, alpha189, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := orderOf_dvd_natCard
      (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c))
    rw [hord] at hdvd
    exact (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
      Nat.prime_three).2.2.1 hdvd
  exact orderOf_eq_prime hcb3 hcb1

theorem listData189_of_setting (h186 : Item186H) (hset : Setting189 G A M H c) :
    ListData189 (kAlpha189 M H c) (sAlpha189 M H c) (Sec4.autThetaQuot A (sk189 M H c))
      (cAlpha189 M H c) := by
  have h := hset.toSec18H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := kAlpha189_normal M H c
  set ψ := kThetaEquiv189 M H c with hψ
  have hsimpleθ := ktype_simple hset.mem_thetaComponentsIn hset.pRank_eq
  have hQθ := quasisimple_of_mem_thetaComponentsIn hset.mem_thetaComponentsIn
  have hsimple : IsSimpleGroup ↥(kAlpha189 M H c) := ψ.symm.isSimpleGroup
  have hperfθ : Group.IsPerfect
      (↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c)) := hQθ.1
  have hperf : Group.IsPerfect ↥(kAlpha189 M H c) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hZ : Subgroup.center ↥(kAlpha189 M H c) = ⊥ :=
    center_eq_bot_of_isSimpleGroup189 hperf.commutator_eq_top
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hset.pRank_eq
  exact
    { normal := kAlpha189_normal M H c
      simple := hsimple
      sup_eq := kAlpha189_sup_sAlpha189 M H c
      centralizer_eq := centralizer_eq_bot_of_sup189 (kAlpha189_sup_sAlpha189 M H c)
        (isPGroup_sAlpha189 M H c) (aschbacherSolvableCore_sKAlpha189 M H c) hZ
      isPGroup := isPGroup_sAlpha189 M H c
      ne_bot := hset.sAlpha_ne
      inv := gammaInv_sAlpha189 h
      maximal := fun T hT hST hinv => sAlpha189_maximal h186 h hset.hyp187 hT hST hinv
      comm := fun γ hγ δ hδ => autThetaQuot_comm189 h hγ hδ
      pow_three := fun γ hγ => autThetaQuot_pow_three189 h hγ
      mem := cAlpha189_mem_kAlpha h
      orderOf_eq := orderOf_cAlpha189 h hc1
      conj_mem := conj_cAlpha189_mem h }

end Bridge

@[expose] def List189L3Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f → p ^ f % 3 = 2 →
      Nonempty (↥(kAlpha189 M H c) ≃* projSL 3 (GaloisField p f)) → f = 1

@[expose] def List189U3Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f → p ^ f % 3 = 1 →
      Nonempty (↥(kAlpha189 M H c) ≃* projSU 3 p f) → f = 1

theorem step189List_of_families (h186 : Item186H) (hL2e : List189L2Even) (hL3e : List189L3Even)
    (hU3e : List189U3Even) (hL2o : List189L2Odd) (hL3o : List189L3Odd) (hU3o : List189U3Odd)
    (hJ1 : List189J1) : Step189List := by
  intro G _ _ A M H c hset
  have hdata := listData189_of_setting h186 hset
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := kThetaEquiv189 M H c with hψ
  have hperf : Group.IsPerfect ↥(kAlpha189 M H c) := hdata.isPerfect
  suffices hab : AbsList189 (kAlpha189 M H c) (sAlpha189 M H c) by
    rcases hab with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases hset.rankOne with ⟨p, f, hp, hp3, hf, ⟨e⟩⟩ | ⟨p, f, hp, hf, hq, ⟨e⟩⟩ |
      ⟨p, f, hp, hf, hq, ⟨e⟩⟩ | hJ
  · by_cases hp2 : p = 2
    · subst hp2
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1 : f = 1 := by omega
        subst hf1
        exact not_nonempty_equiv_projSL_two_one189 ⟨ψ.symm.trans e⟩
      exact hL2e _ _ _ _ _ f hdata hf2 ⟨ψ.symm.trans e⟩
    · exact hL2o _ _ _ _ _ p f hdata hp2 hp3 hf ⟨ψ.symm.trans e⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact hL3e _ _ _ _ _ f hdata (odd_of_two_pow_mod_three189 hq) ⟨ψ.symm.trans e⟩
    · obtain rfl : f = 1 := hL3o G A M H c hset p f hp2 hf hq ⟨ψ.symm.trans e⟩
      rw [pow_one] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, by omega,
        Or.inl ⟨hq, ⟨ψ.symm.trans e⟩⟩⟩))))
  · by_cases hp2 : p = 2
    · subst hp2
      have hfe := even_of_two_pow_mod_three189 hq
      have hf2 : 2 ≤ f := by
        obtain ⟨k, rfl⟩ := hfe
        omega
      exact hU3e _ _ _ _ _ f hdata hfe hf2 ⟨ψ.symm.trans e⟩
    · obtain rfl : f = 1 := hU3o G A M H c hset p f hp2 hf hq ⟨ψ.symm.trans e⟩
      rw [pow_one] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, by
        have := hp.out.two_le
        omega, Or.inr ⟨hq, ⟨ψ.symm.trans e⟩⟩⟩))))
  · obtain ⟨e⟩ := hJ
    exact hJ1 _ _ _ _ _ hdata ⟨ψ.symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec18
