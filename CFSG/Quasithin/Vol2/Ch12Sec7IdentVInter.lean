module

public import CFSG.Quasithin.Vol2.Ch12Sec7IdentMain

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin Subgroup
open scoped IsMulCommutative

theorem vInter_core {A : Type*} [Group A] [Finite A] (σ : A ≃* A) (Zs Ys : Set A)
    (hZ : ∀ a ∈ Zs, σ a ∈ Zs) (hY : ∀ a ∈ Ys, σ a ∈ Ys) (h1Y : (1 : A) ∉ Ys)
    (hcov : ∀ a : A, a ≠ 1 → a ∈ Zs ∨ a ∈ Ys) (hYc : Ys.ncard ≤ 18)
    (W : Subgroup A) (hW : Nat.card W = 16) (z : A) (hzZ : z ∈ Zs) (hzW : z ∈ W)
    (hσz : σ z ≠ z) : ∃ w ∈ Zs, w ∈ W ∧ w ≠ z := by
  by_contra H
  push Not at H
  have hWc : (W : Set A).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hW
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hσz (map_one σ)
  have hσzW : σ z ∉ W := fun h => hσz (H _ (hZ z hzZ) h)
  have hpair : ({1, z} : Set A).ncard = 2 := Set.ncard_pair (Ne.symm hz1)
  have hpairW : ({1, z} : Set A) ⊆ (W : Set A) := by
    rintro x (rfl | rfl)
    · exact W.one_mem
    · exact hzW
  have hX14 : 14 ≤ ((W : Set A) ∩ Ys).ncard := by
    have hsub : (W : Set A) \ {1, z} ⊆ (W : Set A) ∩ Ys := by
      rintro w ⟨hwW, hwn⟩
      have hw1 : w ≠ 1 := fun h => hwn (Or.inl h)
      have hwz : w ≠ z := fun h => hwn (Or.inr h)
      refine ⟨hwW, ?_⟩
      rcases hcov w hw1 with hwZ | hwY
      · exact absurd (H w hwZ hwW) hwz
      · exact hwY
    have h14 := Set.ncard_sdiff_add_ncard_of_subset hpairW
    have h14' : ((W : Set A) \ {1, z}).ncard = 14 := by omega
    rw [← h14']
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  set S : Subgroup A := W ⊓ Subgroup.comap σ.toMonoidHom W with hSdef
  have hSW : S ≤ W := inf_le_left
  have hzS : z ∉ S := fun h => hσzW (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 h).2)
  have hSne : Nat.card S ≠ 16 := by
    intro h
    have hSeq : S = W := Subgroup.eq_of_le_of_card_ge hSW (by rw [h, hW])
    exact hzS (hSeq ▸ hzW)
  have hSle : Nat.card S ≤ 8 := by
    have hdvd : Nat.card S ∣ 16 := hW ▸ Subgroup.card_dvd_of_le hSW
    obtain ⟨k, hk⟩ := hdvd
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · omega
      · omega
    · nlinarith
  have hXS : (((W : Set A) ∩ Ys) ∩ (S : Set A)).ncard ≤ 7 := by
    have hsub : ((W : Set A) ∩ Ys) ∩ (S : Set A) ⊆ (S : Set A) \ {1} := by
      rintro a ⟨⟨-, haY⟩, haS⟩
      refine ⟨haS, fun h1 => h1Y ?_⟩
      rw [Set.mem_singleton_iff] at h1
      rw [← h1]
      exact haY
    have h1S : (1 : A) ∈ (S : Set A) := S.one_mem
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_sdiff_singleton_of_mem h1S] at h2
    have h3 : (S : Set A).ncard = Nat.card S := rfl
    omega
  have hint : (σ '' ((W : Set A) ∩ Ys)) ∩ (W : Set A) =
      σ '' (((W : Set A) ∩ Ys) ∩ (S : Set A)) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hyW⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      exact Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_comap.2 hyW⟩
    · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hxS).2)⟩
  have hcard2 : ((σ '' ((W : Set A) ∩ Ys)) ∩ (W : Set A)).ncard ≤ 7 := by
    rw [hint, Set.ncard_image_of_injective _ σ.injective]
    exact hXS
  have hYσ : (σ '' ((W : Set A) ∩ Ys)).ncard = ((W : Set A) ∩ Ys).ncard :=
    Set.ncard_image_of_injective _ σ.injective
  have hYsub : σ '' ((W : Set A) ∩ Ys) ⊆ Ys := by
    rintro _ ⟨x, hx, rfl⟩
    exact hY x hx.2
  have hdiff1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (σ '' ((W : Set A) ∩ Ys)) (W : Set A)
  have hdiff2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard Ys (W : Set A)
  have hsubdiff : σ '' ((W : Set A) ∩ Ys) \ (W : Set A) ⊆ Ys \ (W : Set A) :=
    Set.diff_subset_diff_left hYsub
  have hle := Set.ncard_le_ncard hsubdiff (Set.toFinite _)
  have hYW : (Ys ∩ (W : Set A)).ncard = ((W : Set A) ∩ Ys).ncard := by
    rw [Set.inter_comm]
  omega

theorem vInter1277_of (h1222 : Stmt12_2_2) : VInter1277 := by
  intro G _ _ T L V h z hzV t htV hz45 ht18 hcov W hWV hzW hW16
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  haveI := hcomm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  obtain ⟨zA, hzA⟩ : ∃ a : ↥V, (a : G) = z := ⟨⟨z, hzV⟩, rfl⟩
  obtain ⟨tA, htA⟩ : ∃ a : ↥V, (a : G) = t := ⟨⟨t, htV⟩, rfl⟩
  have hmem : ∀ a b : ↥V, b ∈ Orbit.orbitIn (autOn L V) a ↔ ∃ l ∈ L, l * (a : G) * l⁻¹ = b :=
    fun a b => S127.mem_orbitIn_autOn_iff hLV a b
  have hZc : (Orbit.orbitIn (autOn L V) zA).ncard = 45 := by
    rw [← Nat.card_coe_set_eq, S127.card_orbitIn_autOn hLV zA, hzA]
    exact hz45
  have hYc : (Orbit.orbitIn (autOn L V) tA).ncard = 18 := by
    rw [← Nat.card_coe_set_eq, S127.card_orbitIn_autOn hLV tA, htA]
    exact ht18
  have ht1 : tA ≠ 1 := by
    intro h1
    apply S127.ne_one_of_relIndex ht18 (by norm_num : (18 : ℕ) ≠ 1)
    rw [← htA, h1]
    rfl
  have hinv : ∀ (x a : ↥V) (g : MulAut ↥V), g ∈ autOn L V →
      a ∈ Orbit.orbitIn (autOn L V) x → g a ∈ Orbit.orbitIn (autOn L V) x := by
    rintro x a g hg ⟨k, hk, rfl⟩
    exact ⟨g * k, (autOn L V).mul_mem hg hk, rfl⟩
  have h1notin : ∀ x : ↥V, x ≠ 1 → (1 : ↥V) ∉ Orbit.orbitIn (autOn L V) x := by
    rintro x hx ⟨k, -, hk⟩
    exact hx (by simpa using hk)
  have hcov' : ∀ a : ↥V, a ≠ 1 →
      a ∈ Orbit.orbitIn (autOn L V) zA ∨ a ∈ Orbit.orbitIn (autOn L V) tA := by
    intro a ha
    have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    rcases hcov (a : G) a.2 ha' with ⟨l, hl, hlz⟩ | ⟨l, hl, hlt⟩
    · left
      rw [hmem]
      refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
      rw [hzA, ← hlz]
      group
    · right
      rw [hmem]
      refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
      rw [htA, ← hlt]
      group
  obtain ⟨g, hg, hgz⟩ : ∃ g ∈ autOn L V, g zA ≠ zA := by
    by_contra hno
    push Not at hno
    have hsub : Orbit.orbitIn (autOn L V) zA ⊆ {zA} := by
      rintro b ⟨k, hk, rfl⟩
      exact Set.mem_singleton_iff.2 (hno k hk)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hZc, Set.ncard_singleton] at this
    omega
  have hzA_mem : zA ∈ Orbit.orbitIn (autOn L V) zA := ⟨1, (autOn L V).one_mem, rfl⟩
  have hW' : Nat.card (W.subgroupOf V) = 16 := by
    rw [← hW16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv
  have hzW' : zA ∈ W.subgroupOf V := by
    rw [Subgroup.mem_subgroupOf, hzA]
    exact hzW
  obtain ⟨w, hwZ, hwW, hwz⟩ := vInter_core g (Orbit.orbitIn (autOn L V) zA)
    (Orbit.orbitIn (autOn L V) tA) (fun a ha => hinv zA a g hg ha)
    (fun a ha => hinv tA a g hg ha) (h1notin tA ht1) hcov' hYc.le (W.subgroupOf V) hW' zA
    hzA_mem hzW' hgz
  obtain ⟨l, hl, hlw⟩ := (hmem zA w).1 hwZ
  have hconj : l⁻¹⁻¹ * z * l⁻¹ = (w : G) := by
    rw [inv_inv, ← hzA]
    exact hlw
  refine ⟨l⁻¹, L.inv_mem hl, ?_, ?_⟩
  · rw [hconj]
    exact Subgroup.mem_subgroupOf.1 hwW
  · rw [hconj]
    intro h
    exact hwz (Subtype.ext (by rw [hzA]; exact h))

end CFSG.Quasithin.H13.I1277

namespace CFSG.Quasithin.H13.I1277

theorem ident1277_of_struct' (h1222 : Stmt12_2_2) (hS : Struct1277) : Ident1277 :=
  ident1277_of_struct h1222 hS (vInter1277_of h1222)

end CFSG.Quasithin.H13.I1277
