module

public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem perm_fin_mul_comm : ∀ r : ℕ, r ≤ 2 → ∀ a b : Equiv.Perm (Fin r), a * b = b * a := by
  intro r hr
  interval_cases r <;> decide

section Product

variable {Γ : Type*} [Group Γ]

theorem eq_bot_or_eq_of_isSimpleGroup {A B : Subgroup Γ} (hAB : A ≤ B) (hB : IsSimpleGroup B)
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) : A = ⊥ ∨ A = B := by
  have hQ : (A.subgroupOf B).Normal := ⟨fun x hx g => mem_subgroupOf.mpr (by
    simpa using hn g g.2 x (mem_subgroupOf.mp hx))⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf B) with h | h
  · left
    rw [subgroupOf_eq_bot] at h
    exact eq_bot_iff.mpr fun a ha => mem_bot.mpr (Subgroup.disjoint_def.mp h ha (hAB ha))
  · right
    exact le_antisymm hAB (subgroupOf_eq_top.mp h)

structure IsSimpleProduct {r : ℕ} (V : Subgroup Γ) (S : Fin r → Subgroup Γ) : Prop where
  le : ∀ i, S i ≤ V
  simple : ∀ i, IsSimpleGroup (S i)
  nonabelian : ∀ i, ∃ a b : S i, a * b ≠ b * a
  normal : ∀ i, ∀ v ∈ V, ∀ s ∈ S i, v * s * v⁻¹ ∈ S i
  commute : ∀ i j, i ≠ j → ∀ s ∈ S i, ∀ t ∈ S j, s * t = t * s
  iSup_eq : ⨆ i, S i = V
  eq_one : ∀ z ∈ V, (∀ i, ∀ s ∈ S i, z * s = s * z) → z = 1

theorem isSimpleProduct_of_mulEquiv {r : ℕ} {V : Subgroup Γ} {S : Fin r → Subgroup Γ}
    (hSV : ∀ i, S i ≤ V) (hSs : ∀ i, IsSimpleGroup (S i))
    (hSnab : ∀ i, ∃ a b : S i, a * b ≠ b * a) (hSn : ∀ i, ((S i).subgroupOf V).Normal)
    (e : ((i : Fin r) → S i) ≃* V)
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : Γ) = x i) :
    IsSimpleProduct V S := by
  classical
  have hsingle : ∀ i (s : S i), (e (Pi.mulSingle i s) : Γ) = s := fun i s => by
    rw [he i _ fun j hj => Pi.mulSingle_eq_of_ne (M := fun j : Fin r => (S j : Type _)) hj s,
      Pi.mulSingle_eq_same]
  refine ⟨hSV, hSs, hSnab, ?_, ?_, ?_, ?_⟩
  · intro i v hv s hs
    have := (hSn i).conj_mem ⟨s, hSV i hs⟩ (mem_subgroupOf.mpr hs) ⟨v, hv⟩
    simpa using mem_subgroupOf.mp this
  · intro i j hij s hs t ht
    have h1 := (Pi.mulSingle_commute (f := fun j : Fin r => (S j : Type _)) hij
      (⟨s, hs⟩ : S i) (⟨t, ht⟩ : S j)).eq
    have h2 := congrArg (fun x => (e x : Γ)) h1
    simpa only [map_mul, Subgroup.coe_mul, hsingle] using h2
  · refine le_antisymm (iSup_le hSV) fun v hv => ?_
    set x := e.symm ⟨v, hv⟩ with hx
    have hmem : x ∈ (⨆ i, S i).comap (V.subtype.comp e.toMonoidHom) :=
      Subgroup.pi_mem_of_mulSingle_mem x fun i => by
        rw [mem_comap]
        change (e (Pi.mulSingle i (x i)) : Γ) ∈ ⨆ i, S i
        rw [hsingle]
        exact mem_iSup_of_mem i (x i).2
    rw [mem_comap] at hmem
    simpa [hx] using hmem
  · intro z hzV hz
    set x := e.symm ⟨z, hzV⟩ with hx
    have hex : (e x : Γ) = z := by rw [hx, MulEquiv.apply_symm_apply]
    have hxi : ∀ i, x i = 1 := by
      intro i
      have hcent : ∀ s : S i, x i * s = s * x i := by
        intro s
        have h1 : e x * e (Pi.mulSingle i s) = e (Pi.mulSingle i s) * e x := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, hsingle, hex]
          exact hz i s s.2
        rw [← map_mul, ← map_mul] at h1
        have h2 := congrFun (e.injective h1) i
        simpa using h2
      have := hSs i
      by_contra hne
      obtain ⟨a, b, hab⟩ := hSnab i
      have hZ : center (S i) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (S i)) with h | h
        · exfalso
          apply hne
          have hmem : x i ∈ center (S i) := mem_center_iff.mpr fun g => (hcent g).symm
          rw [h] at hmem
          exact hmem
        · exact h
      exact hab (mem_center_iff.mp (hZ ▸ mem_top b) a)
    have hx1 : x = 1 := funext hxi
    rw [← hex, hx1, map_one, Subgroup.coe_one]

namespace IsSimpleProduct

variable {r : ℕ} {V : Subgroup Γ} {S : Fin r → Subgroup Γ}

theorem injective (h : IsSimpleProduct V S) : Function.Injective S := by
  intro i j hij
  by_contra hne
  obtain ⟨a, b, hab⟩ := h.nonabelian i
  apply hab
  apply Subtype.ext
  have hb : (b : Γ) ∈ S j := hij ▸ b.2
  exact h.commute i j hne a a.2 b hb

theorem exists_eq_of_normal (h : IsSimpleProduct V S) {K : Subgroup Γ} (hKV : K ≤ V)
    (hKn : ∀ v ∈ V, ∀ k ∈ K, v * k * v⁻¹ ∈ K) (hK : IsSimpleGroup K) : ∃ j, K = S j := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ j, ∀ k ∈ K, ∀ s ∈ S j, k * s = s * k := by
    intro j k hk s hs
    have hc : k * s * k⁻¹ * s⁻¹ ∈ K ⊓ S j := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : s * k⁻¹ * s⁻¹ ∈ K := hKn s (h.le j hs) k⁻¹ (inv_mem hk)
        have h2 : k * s * k⁻¹ * s⁻¹ = k * (s * k⁻¹ * s⁻¹) := by group
        rw [h2]
        exact mul_mem hk h1
      · exact mul_mem (h.normal j k (hKV hk) s hs) (inv_mem hs)
    have hbot : K ⊓ S j = ⊥ := by
      rcases eq_bot_or_eq_of_isSimpleGroup inf_le_right (h.simple j)
          (fun b hb a ha => ⟨hKn b (h.le j hb) a ha.1, h.normal j b (h.le j hb) a ha.2⟩) with
        h1 | h1
      · exact h1
      · exfalso
        have hSK : S j ≤ K := h1 ▸ inf_le_left
        rcases eq_bot_or_eq_of_isSimpleGroup hSK hK
            (fun b hb a ha => h.normal j b (hKV hb) a ha) with h2 | h2
        · have := h.simple j
          obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne (S j)
          rw [h2] at ha hb
          exact hab (Subtype.ext ((mem_bot.mp ha).trans (mem_bot.mp hb).symm))
        · exact hne j h2.symm
    rw [hbot, mem_bot] at hc
    have h3 : k * s * k⁻¹ * s⁻¹ * s * k = k * s := by group
    rw [hc, one_mul] at h3
    exact h3.symm
  have := hK
  have hK1 : ∀ k ∈ K, k = 1 := fun k hk => h.eq_one k (hKV hk) fun j s hs => hcomm j k hk s hs
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne K
  exact hab (Subtype.ext ((hK1 a ha).trans (hK1 b hb).symm))

theorem exists_map_conj_eq (h : IsSimpleProduct V S) (hVn : V.Normal) (g : Γ) (i : Fin r) :
    ∃ j, (S i).map (MulAut.conj g).toMonoidHom = S j := by
  refine h.exists_eq_of_normal ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact hVn.conj_mem s (h.le i hs) g
  · rintro v hv _ ⟨s, hs, rfl⟩
    have hv' : g⁻¹ * v * g ∈ V := by simpa using hVn.conj_mem v hv g⁻¹
    refine ⟨(g⁻¹ * v * g) * s * (g⁻¹ * v * g)⁻¹, h.normal i _ hv' s hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have := h.simple i
    exact ((S i).equivMapOfInjective _ (MulAut.conj g).injective).symm.isSimpleGroup

noncomputable def permIdx (h : IsSimpleProduct V S) (hVn : V.Normal) (g : Γ) (i : Fin r) :
    Fin r :=
  (h.exists_map_conj_eq hVn g i).choose

theorem map_conj_eq_permIdx (h : IsSimpleProduct V S) (hVn : V.Normal) (g : Γ) (i : Fin r) :
    (S i).map (MulAut.conj g).toMonoidHom = S (h.permIdx hVn g i) :=
  (h.exists_map_conj_eq hVn g i).choose_spec

theorem permIdx_one (h : IsSimpleProduct V S) (hVn : V.Normal) (i : Fin r) :
    h.permIdx hVn 1 i = i := by
  apply h.injective
  rw [← h.map_conj_eq_permIdx hVn 1 i, map_one]
  exact Subgroup.map_id _

theorem permIdx_mul (h : IsSimpleProduct V S) (hVn : V.Normal) (g g' : Γ) (i : Fin r) :
    h.permIdx hVn (g * g') i = h.permIdx hVn g (h.permIdx hVn g' i) := by
  apply h.injective
  rw [← h.map_conj_eq_permIdx hVn, ← h.map_conj_eq_permIdx hVn, ← h.map_conj_eq_permIdx hVn,
    Subgroup.map_map, map_mul]
  rfl

@[instance_reducible] noncomputable def mulActionFactors (h : IsSimpleProduct V S)
    (hVn : V.Normal) : MulAction Γ (Fin r) where
  smul g i := h.permIdx hVn g i
  one_smul i := h.permIdx_one hVn i
  mul_smul g g' i := h.permIdx_mul hVn g g' i

theorem map_conj_eq_of_isPerfect (h : IsSimpleProduct V S) (hVn : V.Normal) (hr : r ≤ 2)
    {D : Type*} [Group D] (hD : Group.IsPerfect D) (φ : D →* Γ) (d : D) (i : Fin r) :
    (S i).map (MulAut.conj (φ d)).toMonoidHom = S i := by
  let _ := h.mulActionFactors hVn
  have : IsMulCommutative (Equiv.Perm (Fin r)) := ⟨⟨perm_fin_mul_comm r hr⟩⟩
  have h1 := Sec6.BThreeCensus.map_eq_one_of_isPerfect hD
    ((MulAction.toPermHom Γ (Fin r)).comp φ) d
  have h2 : h.permIdx hVn (φ d) i = i := by
    have := congrArg (fun σ : Equiv.Perm (Fin r) => σ i) h1
    exact this
  rw [h.map_conj_eq_permIdx hVn, h2]

end IsSimpleProduct

end Product

section Suzuki

variable {Γ : Type} [Group Γ]

theorem IsSimpleProduct.commute_of_pow_three_pow {r : ℕ} {V : Subgroup Γ} {S : Fin r → Subgroup Γ}
    (h : IsSimpleProduct V S) (hSz : ∀ i, ∃ q f : ℕ, SuzukiModel (S i) q f) {D : Type*} [Group D]
    (hD : Group.IsPerfect D) (φ : D →* Γ)
    (hφ : ∀ d i, (S i).map (MulAut.conj (φ d)).toMonoidHom = S i) {d : D} {k : ℕ}
    (hd : d ^ 3 ^ k = 1) : ∀ v ∈ V, φ d * v = v * φ d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi : ∀ i, ∀ s ∈ S i, φ d * s = s * φ d := by
    intro i s hs
    obtain ⟨q, f, hSzi⟩ := hSz i
    have hN : ∀ d' : D, φ d' ∈ normalizer (S i : Set Γ) := fun d' =>
      mem_normalizer_iff_map_conj_eq.mpr (hφ d' i)
    set ρ : D →* MulAut (S i) := (S i).normalizerMonoidHom.comp (φ.codRestrict _ hN) with hρ
    have hρin : ρ d ∈ inner (S i) := by
      have h1 := KFacts.KP7.map_commutator_le_inner hSzi ρ (⊤ : Subgroup D) (⊤ : Subgroup D)
      have h2 : ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ = (⊤ : Subgroup D) := by
        rw [← commutator_def]
        exact hD.commutator_eq_top
      rw [h2] at h1
      exact h1 ⟨d, mem_top d, rfl⟩
    have hP : IsPGroup 3 (zpowers (ρ d)) := by
      have h1 : (ρ d) ^ 3 ^ k = 1 := by rw [← map_pow, hd, map_one]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have h3 := KFacts.KP7.inf_inner_eq_bot hSzi hP
    have h4 : ρ d ∈ zpowers (ρ d) ⊓ inner (S i) := ⟨mem_zpowers _, hρin⟩
    rw [h3, mem_bot] at h4
    have h5 := congrArg (fun σ : MulAut (S i) => ((σ ⟨s, hs⟩ : S i) : Γ)) h4
    have h6 : φ d * s * (φ d)⁻¹ = s := by
      simpa [hρ] using h5
    calc φ d * s = φ d * s * (φ d)⁻¹ * φ d := by group
      _ = s * φ d := by rw [h6]
  intro v hv
  rw [← h.iSup_eq] at hv
  have hle : ⨆ i, S i ≤ centralizer ({φ d} : Set Γ) :=
    iSup_le fun i s hs => mem_centralizer_singleton_iff.mpr (hi i s hs).symm
  exact (mem_centralizer_singleton_iff.mp (hle hv)).symm

theorem le_pRank_five {r : ℕ} {S : Fin r → Type} [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hSz : ∀ i, ∃ q f : ℕ, SuzukiModel (S i) q f) :
    r ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ((i : Fin r) → S i)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy : ∀ i, ∃ y : S i, orderOf y = 5 := fun i => by
    obtain ⟨q, f, hi⟩ := hSz i
    exact exists_prime_orderOf_dvd_card' 5 (KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hi)
  choose y hy using hy
  let f : ((i : Fin r) → zpowers (y i)) →* ((i : Fin r) → S i) :=
    { toFun := fun x i => (x i : S i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f ?_
    (le_top : f.range ≤ ⊤)
  · intro a b
    funext i
    apply Subtype.ext
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (a i).2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (b i).2
    change ((a i : S i)) * (b i : S i) = (b i : S i) * (a i : S i)
    rw [← hm, ← hn]
    exact zpow_mul_comm _ _ _
  · intro a
    funext i
    have h1 := pow_card_eq_one' (G := zpowers (y i)) (x := a i)
    rw [Nat.card_zpowers, hy i] at h1
    exact h1
  · rw [Nat.card_pi]
    simp only [Nat.card_zpowers, hy, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    funext i
    exact Subtype.ext (congrFun hab i)

end Suzuki

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
