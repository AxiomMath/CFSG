module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSub

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

theorem nineThree_A_le_S (h9 : Hyp9 V T) (hA : IsGConj V A) (hAT : A ≤ T)
    (htau : E1.tauOf (normalizer (V : Set G)) T A ≤ S) : A ≤ S := by
  have hAab : IsMulCommutative ↥A := by
    obtain ⟨g, hg⟩ := hA
    rw [hg]
    exact (E3.isElemAbelian_conjSubgroup h9.hyp7.1 g).1
  intro a ha
  refine htau (E1.mem_tauOf.mpr ⟨hAT ha, ?_, ?_⟩)
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (V : Set G))
      (h9.sylow.le (hAT ha))
  · intro a' ha'
    have h1 : ⁅a, a'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    rw [h1]
    exact Subgroup.one_mem _

theorem nineThree_centralizer_le_S (h9 : Hyp9 V T)
    (htau : E1.tauOf (normalizer (V : Set G)) T A ≤ S) :
    T ⊓ centralizer (A : Set G) ≤ S := by
  intro t ht
  refine htau (E1.mem_tauOf.mpr ⟨ht.1, ?_, ?_⟩)
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (V : Set G))
      (h9.sylow.le ht.1)
  · intro a ha
    have h1 : ⁅t, a⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_centralizer_iff.mp ht.2) a ha).symm
    rw [h1]
    exact Subgroup.one_mem _

theorem TwoPTwo.commutator_mem_pCoreOf (h : TwoPTwo K S X p) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) {r y : G}
    (hr : r ∈ pCoreOf 2 (S ⊔ Y)) (hy : y ∈ Y) : ⁅y, r⁆ ∈ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K₀ := S ⊔ Y
  let R₀ := pCoreOf 2 K₀
  let L := pCoreOf 2 K ⊔ Y
  have hSL : S ≤ normalizer (L : Set G) := h.le_normalizer_sup hYX hY
  have hYL : Y ≤ L := le_sup_right
  have hK₀L : K₀ ≤ normalizer (L : Set G) := sup_le hSL (hYL.trans Subgroup.le_normalizer)
  have hrK₀ : r ∈ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀ hr
  have hyK₀ : y ∈ K₀ := Subgroup.mem_sup_right hy
  have hR₀N : K₀ ≤ normalizer (R₀ : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have h1 : ⁅y, r⁆ ∈ R₀ := by
    have h2 : y * r * y⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp (hR₀N hyK₀) r).mp hr
    exact R₀.mul_mem h2 (R₀.inv_mem hr)
  have h3 : ⁅y, r⁆ ∈ L := by
    have h4 : r * y⁻¹ * r⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hK₀L hrK₀) y⁻¹).mp (L.inv_mem (hYL hy))
    have h5 : ⁅y, r⁆ = y * (r * y⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h5]
    exact L.mul_mem (hYL hy) h4
  have hLXR : L ≤ pCoreOf 2 K ⊔ X := sup_le_sup_left hYX _
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀ ⟨⁅y, r⁆, h1⟩
  exact h.mem_pCoreOf_of_mem_sup (hLXR h3) (n := n) (by simpa using congrArg Subtype.val hn)

private theorem nineThree_inf_center_ne_bot {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent T := hT.isNilpotent
  haveI : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem nineThree_witness (h9 : Hyp9 V T)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ∃ b ∈ E3.cClos V 1 T, b ≠ 1 ∧
      ∀ Y ∈ calP V, Y ≤ centralizer ({b} : Set G) → Y = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h9.hyp7.1
  have hVT : V ≤ T := h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp
  have hVW : V ≤ E3.wClos V 1 T := E3.le_wClos_of_mQuot_le_self h9.hyp7.1 hVT le_rfl
    (k := 1) (by rw [E3.mQuot_self]; norm_num) (by have := h9.rk_gt; omega)
  obtain ⟨h, hhN, hhM⟩ := SetLike.not_le_iff_exists.1 h1
  have hW1h : conjSubgroup (E3.wClos V 1 T) h = E3.wClos V 1 T :=
    (conjSubgroup_eq_iff_mem_normalizer).2 hhN
  have hVhW1 : conjSubgroup V h ≤ E3.wClos V 1 T := by
    have h1' : conjSubgroup V h ≤ conjSubgroup (E3.wClos V 1 T) h :=
      E3.conjSubgroup_mono_left h hVW
    rwa [hW1h] at h1'
  have hVhM : conjSubgroup V h ≤ normalizer (V : Set G) :=
    hVhW1.trans ((E3.wClos_le 1 T).trans h9.sylow.le)
  have hW1two : IsPGroup 2 (E3.wClos V 1 T) := h9.sylow.isPGroup.to_le (E3.wClos_le 1 T)
  have hW1norm : E3.wClos V 1 T ≤ normalizer (V : Set G) :=
    (E3.wClos_le 1 T).trans h9.sylow.le
  have hVne : V ≠ ⊥ := by
    intro hVbot
    have h2 := h9.hyp7.2.1
    rw [hVbot, Subgroup.card_bot] at h2
    omega
  have hb0ne : V ⊓ (E3.wClos V 1 T ⊓ centralizer (E3.wClos V 1 T : Set G)) ≠ ⊥ :=
    nineThree_inf_center_ne_bot hW1two hVW hW1norm hVne
  obtain ⟨⟨b₀, hb₀mem⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb0ne
  have hb₀V : b₀ ∈ V := (Subgroup.mem_inf.1 hb₀mem).1
  have hb₀C : b₀ ∈ centralizer (E3.wClos V 1 T : Set G) := (Subgroup.mem_inf.1 hb₀mem).2.2
  have hb₀1' : b₀ ≠ 1 := fun hb => hb₀1 (Subtype.ext hb)
  set b : G := h⁻¹ * b₀ * h with hbdef
  have hbVh : b ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rw [hbdef]
    rw [show h * (h⁻¹ * b₀ * h) * h⁻¹ = b₀ by group]
    exact hb₀V
  have hb1 : b ≠ 1 := by
    intro hb
    apply hb₀1'
    have h1' : b₀ = h * b * h⁻¹ := by rw [hbdef]; group
    rw [hb] at h1'
    simpa using h1'
  have hbW : b ∈ E3.wClos V 1 T := hVhW1 hbVh
  have hbT : b ∈ T := E3.wClos_le 1 T hbW
  have hbC : b ∈ centralizer (E3.wClos V 1 T : Set G) := by
    have h1' : b ∈ conjSubgroup (centralizer (E3.wClos V 1 T : Set G)) h := by
      rw [mem_conjSubgroup_iff]
      rw [hbdef]
      rw [show h * (h⁻¹ * b₀ * h) * h⁻¹ = b₀ by group]
      exact hb₀C
    rwa [E3.conjSubgroup_centralizer, hW1h] at h1'
  refine ⟨b, ⟨hbT, hbC⟩, hb1, ?_⟩
  intro Y hY hYb
  rcases hY with ⟨q, hq, hq2, hYp, hYM, hYG, hYtriv⟩
  have hYN : Y ≤ normalizer (conjSubgroup V h : Set G) :=
    hYb.trans (centralizer_le_normalizer_conj h9.hyp7.2.2 h hbVh hb1)
  have hYMh : Y ≤ conjSubgroup (normalizer (V : Set G)) h := by
    rw [E3.conjSubgroup_normalizer]
    exact hYN
  have htriv := hYtriv h hhM hVhM
  rw [← inf_eq_left.2 hYMh]
  exact htriv

theorem nineThree_cClos_le (h9 : Hyp9 V T) (hA : IsGConj V A) (hAT : A ≤ T) (hST : S ≤ T)
    (htau : E1.tauOf (normalizer (V : Set G)) T A ≤ S) :
    E3.cClos V 1 T ≤ E3.cClos V 1 S := by
  obtain ⟨g, rfl⟩ := hA
  have hAW : conjSubgroup V g ≤ E3.wClos V 1 T := by
    refine E3.le_wClos_of_mQuot_le h9.hyp7.1 g hAT le_rfl ?_ ?_
    · rw [E3.mQuot_self]
      norm_num
    · have := h9.rk_gt
      omega
  intro b hb
  have hbT : b ∈ T := hb.1
  have hbC : b ∈ centralizer (E3.wClos V 1 T : Set G) := hb.2
  have hbA : b ∈ centralizer (conjSubgroup V g : Set G) :=
    Subgroup.centralizer_le (fun x hx => hAW hx) hbC
  have hbS : b ∈ S := nineThree_centralizer_le_S h9 htau ⟨hbT, hbA⟩
  refine ⟨hbS, ?_⟩
  exact Subgroup.centralizer_le (fun x hx => E3.wClos_mono hST hx) hbC

theorem Nine3Seed.not_le_pCoreOf (h : Nine3Seed V T A K S X p) {Y : Subgroup G}
    (hY : Nine3Fam K S X A Y) : ¬ A ≤ pCoreOf 2 (S ⊔ Y) := by
  intro hA
  apply hY.2.2
  intro y hy
  have hyK : y ∈ K := h.two.sylowP.le (hY.1 hy)
  refine E1.mem_tauOf.mpr ⟨hyK, ?_, ?_⟩
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hyK
  · intro a ha
    exact h.two.commutator_mem_pCoreOf hY.1 hY.2.1 (hA ha) hy

theorem Nine3Seed.notW (h : Nine3Seed V T A K S X p) {Y : Subgroup G}
    (hY : Nine3Fam K S X A Y) : ¬ S ⊔ Y ≤ normalizer (E3.wClos V 0 S : Set G) := by
  intro hN
  have hAS : A ≤ S := nineThree_A_le_S h.h9 h.conj h.leT h.tau
  obtain ⟨g, hg⟩ := h.conj
  have hAW : A ≤ E3.wClos V 0 S := by
    refine E3.le_wClos ⟨hAS, g, hg.le, ?_⟩
    rw [hg, E3.mQuot_self]
  have hW2 : IsPGroup 2 (E3.wClos V 0 S) :=
    h.two.sylowTwo.isPGroup.to_le (E3.wClos_le 0 S)
  have hWK₀ : E3.wClos V 0 S ≤ S ⊔ Y := (E3.wClos_le 0 S).trans le_sup_left
  have hW : E3.wClos V 0 S ≤ pCoreOf 2 (S ⊔ Y) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWK₀ hN hW2
  exact h.not_le_pCoreOf hY (hAW.trans hW)

theorem nineThree_le_twoResidual {H Y : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : IsPGroup p Y) (hYH : Y ≤ H) : Y ≤ twoResidual H := by
  intro x hx
  rw [mem_twoResidual_iff]
  intro N hNH hHN hpow
  obtain ⟨k, hk⟩ := hpow x (hYH hx)
  obtain ⟨a, ha⟩ := hY ⟨x, hx⟩
  have hxorder : orderOf x ∣ p ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    have h := congrArg Subtype.val ha
    simpa using h
  have hcop : (2 ^ k).Coprime (orderOf x) := by
    have hp2' : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have h1' : (2 ^ k).Coprime (p ^ a) := (hp2'.pow_left k).pow_right a
    exact h1'.coprime_dvd_right hxorder
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact N.pow_mem hk j

theorem Nine3Seed.notC (h : Nine3Seed V T A K S X p) {Y : Subgroup G}
    (hY : Nine3Fam K S X A Y)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ⁅twoResidual (S ⊔ Y), E3.cClos V 1 S⁆ ≠ ⊥ := by
  intro hcomm
  obtain ⟨b, hbC, hb1, hbY⟩ := nineThree_witness h.h9 h1
  have hbS : b ∈ E3.cClos V 1 S := nineThree_cClos_le h.h9 h.conj h.leT h.leS h.tau hbC
  have hY1 : Y ≠ ⊥ := by
    rintro rfl
    exact hY.2.2 bot_le
  have hYp : IsPGroup p Y := h.two.sylowP.isPGroup.to_le hY.1
  have hres : Y ≤ twoResidual (S ⊔ Y) := nineThree_le_twoResidual h.two.prime h.two.odd hYp
    le_sup_right
  have hleC : twoResidual (S ⊔ Y) ≤ centralizer (E3.cClos V 1 S : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  have hYb : Y ≤ centralizer ({b} : Set G) := by
    intro y hy
    have hyc : y ∈ centralizer (E3.cClos V 1 S : Set G) := hleC (hres hy)
    rw [Subgroup.mem_centralizer_iff] at hyc ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hyc b hbS
  exact hY1 (hbY Y (calP_mono h.mem hY.1) hYb)

theorem Nine3Seed.hyp (h : Nine3Seed V T A K S X p) {Y : Subgroup G} (hY : Nine3Fam K S X A Y)
    (hmin : ∀ Y' : Subgroup G, Nine3Fam K S X A Y' → Y' ≤ Y → Y' = Y)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    Nine2Hyp V (S ⊔ Y) S Y p := by
  exact ⟨⟨⟨h.two.of_sup hY.1 hY.2.1, h.irred hY hmin⟩,
      (sup_le h.two.sylowTwo.le (hY.1.trans h.two.sylowP.le)).trans h.le⟩,
    calP_mono h.mem hY.1, h.notW hY, h.notC hY h1⟩

end CFSG.LocalAnalysis.WeakClosure81
