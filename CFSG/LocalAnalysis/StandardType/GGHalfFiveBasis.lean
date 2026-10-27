module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBElt
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem closure_eq_top_of_le_closure {G : Type*} [Group G] {Γ : Subgroup G} {X : Set G}
    (hX : X ⊆ Γ) (h : Γ ≤ Subgroup.closure X) :
    Subgroup.closure {s : ↥Γ | (s : G) ∈ X} = ⊤ := by
  have hmap : (Subgroup.closure {s : ↥Γ | (s : G) ∈ X}).map Γ.subtype = Subgroup.closure X := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, hX hx⟩, hx, rfl⟩
  rw [eq_top_iff]
  rintro γ -
  have : (γ : G) ∈ (Subgroup.closure {s : ↥Γ | (s : G) ∈ X}).map Γ.subtype := by
    rw [hmap]
    exact h γ.2
  obtain ⟨c, hc, hcγ⟩ := Subgroup.mem_map.mp this
  exact (Subtype.ext hcγ : c = γ) ▸ hc

private theorem zmod3_three_dvd_of_ofAdd_zpow_eq_one {a : ℤ}
    (h : (Multiplicative.ofAdd (1 : ZMod 3)) ^ a = 1) : (3 : ℤ) ∣ a := by
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow, toAdd_ofAdd, toAdd_one] at h2
  rw [zsmul_eq_mul, mul_one] at h2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h2

private theorem halfTorus5_indep {a b c : ℤ}
    (h : (omegaBlock 5 ⟨0, by omega⟩) ^ a * (omegaBlock 5 ⟨2, by omega⟩) ^ b *
        (omegaBlock 5 ⟨4, by omega⟩) ^ c = 1) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c := by
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord 5
  let u : Fin 3 → (Fin 3 → Multiplicative (ZMod 3)) :=
    fun j => Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))
  have h0 : ((Φ (u 0) : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) =
      omegaBlock 5 ⟨0, by omega⟩ := by
    have := hΦ (0 : Fin 3)
    simpa [u] using this
  have h1 : ((Φ (u 1) : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) =
      omegaBlock 5 ⟨2, by omega⟩ := by
    have := hΦ (1 : Fin 3)
    simpa [u] using this
  have h2 : ((Φ (u 2) : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) =
      omegaBlock 5 ⟨4, by omega⟩ := by
    have := hΦ (2 : Fin 3)
    simpa [u] using this
  have hU : u 0 ^ a * u 1 ^ b * u 2 ^ c = 1 := by
    apply Φ.injective
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, Subgroup.coe_zpow,
      Subgroup.coe_one, h0, h1, h2]
    exact h
  have hb1 : (1 : Multiplicative (ZMod 3)) ^ b = 1 := one_zpow b
  have hc1 : (1 : Multiplicative (ZMod 3)) ^ c = 1 := one_zpow c
  have ha1 : (1 : Multiplicative (ZMod 3)) ^ a = 1 := one_zpow a
  refine ⟨?_, ?_, ?_⟩
  · apply zmod3_three_dvd_of_ofAdd_zpow_eq_one
    have hthis := congrFun hU (0 : Fin 3)
    simp only [u, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (by decide : (0:Fin 3) ≠ 1),
      Pi.mulSingle_eq_of_ne (by decide : (0:Fin 3) ≠ 2)] at hthis
    rw [hb1, hc1, mul_one, mul_one] at hthis
    exact hthis
  · apply zmod3_three_dvd_of_ofAdd_zpow_eq_one
    have hthis := congrFun hU (1 : Fin 3)
    simp only [u, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (by decide : (1:Fin 3) ≠ 0),
      Pi.mulSingle_eq_of_ne (by decide : (1:Fin 3) ≠ 2)] at hthis
    rw [ha1, hc1, one_mul, mul_one] at hthis
    exact hthis
  · apply zmod3_three_dvd_of_ofAdd_zpow_eq_one
    have hthis := congrFun hU (2 : Fin 3)
    simp only [u, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (by decide : (2:Fin 3) ≠ 0),
      Pi.mulSingle_eq_of_ne (by decide : (2:Fin 3) ≠ 1)] at hthis
    rw [ha1, hb1, one_mul, one_mul] at hthis
    exact hthis

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem exists_bsBasis : ∃ e : Fin 4 → ↥Bs,
    (e 0 : G) = vElt φ₁ ∧ (e 1 : G) = uElt φ₂ ∧ (e 2 : G) = φ₁ (omegaBlock 5 4) ∧
    (e 3 : G) = wElt φ₂ ∧ (∀ i j, e i * e j = e j * e i) ∧ (∀ i, e i ^ 3 = 1) ∧
    Subgroup.closure (Set.range e) = ⊤ ∧
    ∀ a b c d : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c * e 3 ^ d = 1 →
      (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d := by
  have hu2mem : φ₁ (omegaBlock 5 4) ∈ Bs :=
    h.torusL_le (Subgroup.mem_map.mpr
      ⟨omegaBlock 5 4, Subgroup.subset_closure ⟨(4 : Fin 5), by norm_num, rfl⟩, rfl⟩)
  let e : Fin 4 → ↥Bs := ![
    ⟨vElt φ₁, h.vElt_mem⟩,
    ⟨uElt φ₂, h.uElt_mem⟩,
    ⟨φ₁ (omegaBlock 5 4), hu2mem⟩,
    ⟨wElt φ₂, h.wElt_mem⟩]
  have he0 : (e 0 : G) = vElt φ₁ := rfl
  have he1 : (e 1 : G) = uElt φ₂ := rfl
  have he2 : (e 2 : G) = φ₁ (omegaBlock 5 4) := rfl
  have he3 : (e 3 : G) = wElt φ₂ := rfl
  refine ⟨e, he0, he1, he2, he3, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact Subtype.ext (h.basic.1 (e i : G) (e i).2 (e j : G) (e j).2)
  · intro i
    exact Subtype.ext (h.basic.2.1 (e i : G) (e i).2)
  · let efun : Fin 4 → G := fun i => (e i : G)
    have hXsub : Set.range efun ⊆ Bs := by
      rintro g ⟨i, rfl⟩
      exact (e i).2
    have hgen : Bs ≤ Subgroup.closure (Set.range efun) := by
      refine le_trans h.bs_le_closure ?_
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with hg | hg
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with hgx | hgv | hgu
        · rw [hgx]
          have hxle : Subgroup.zpowers x ≤ Subgroup.closure (Set.range efun) := by
            rw [zpowers_x h]
            exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨3, he3⟩)
          exact hxle (Subgroup.mem_zpowers x)
        · rw [hgv]; exact Subgroup.subset_closure ⟨0, he0⟩
        · rw [hgu]; exact Subgroup.subset_closure ⟨1, he1⟩
      · simp only [zSet, Set.mem_setOf_eq] at hg
        obtain ⟨k, hk2, hk4, rfl⟩ := hg
        refine Subgroup.subset_closure ⟨2, ?_⟩
        change (e 2 : G) = φ₁ (omegaBlock 5 k)
        rw [he2]
        have hkval : k.val = 4 := by
          obtain ⟨c, hc⟩ := (Nat.dvd_iff_mod_eq_zero).mpr hk2
          omega
        rw [show k = (4 : Fin 5) from Fin.ext hkval]
    have hclosure : Subgroup.closure {s : ↥Bs | (s : G) ∈ Set.range efun} = ⊤ :=
      closure_eq_top_of_le_closure hXsub hgen
    have hset : {s : ↥Bs | (s : G) ∈ Set.range efun} = Set.range e := by
      ext s
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rwa [hset] at hclosure
  · intro a b c d hpow
    have hpowG : vElt φ₁ ^ a * uElt φ₂ ^ b * (φ₁ (omegaBlock 5 4)) ^ c * wElt φ₂ ^ d = 1 := by
      have hh := congrArg (Subtype.val) hpow
      simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one, he0, he1, he2, he3]
        using hh
    have hv : vElt φ₁ ∈ (halfTorus 5).map φ₁ :=
      Subgroup.mem_map.mpr ⟨omegaBlock 5 ⟨0, by omega⟩,
        Subgroup.subset_closure ⟨⟨0, by omega⟩, by simp, rfl⟩, rfl⟩
    have hu1 : uElt φ₂ ∈ (halfTorus 5).map φ₁ := by
      refine Subgroup.mem_map.mpr ⟨omegaBlock 5 (2 : Fin 5), ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨(2 : Fin 5), by norm_num, rfl⟩
      · rw [uElt_eq h]; norm_num
    have hu2 : φ₁ (omegaBlock 5 4) ∈ (halfTorus 5).map φ₁ :=
      Subgroup.mem_map.mpr ⟨omegaBlock 5 4,
        Subgroup.subset_closure ⟨(4 : Fin 5), by norm_num, rfl⟩, rfl⟩
    have hbase_mem : vElt φ₁ ^ a * uElt φ₂ ^ b * (φ₁ (omegaBlock 5 4)) ^ c ∈
        (halfTorus 5).map φ₁ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hv a) (Subgroup.zpow_mem _ hu1 b))
        (Subgroup.zpow_mem _ hu2 c)
    have hmem1 : wElt φ₂ ^ d ∈ Subgroup.zpowers x := by
      have hw : wElt φ₂ ∈ Subgroup.zpowers x := by
        rw [zpowers_x h]; exact Subgroup.mem_zpowers _
      exact Subgroup.zpow_mem _ hw d
    have hw_eq : wElt φ₂ ^ d =
        (vElt φ₁ ^ a * uElt φ₂ ^ b * (φ₁ (omegaBlock 5 4)) ^ c)⁻¹ := by
      have h1 : vElt φ₁ ^ a * uElt φ₂ ^ b * (φ₁ (omegaBlock 5 4)) ^ c =
          (wElt φ₂ ^ d)⁻¹ := eq_inv_of_mul_eq_one_left hpowG
      have h2 : (vElt φ₁ ^ a * uElt φ₂ ^ b * (φ₁ (omegaBlock 5 4)) ^ c)⁻¹ = wElt φ₂ ^ d := by
        rw [h1, inv_inv]
      exact h2.symm
    have hmem2 : wElt φ₂ ^ d ∈ (halfTorus 5).map φ₁ := by
      rw [hw_eq]
      exact Subgroup.inv_mem _ hbase_mem
    have hwd1 : wElt φ₂ ^ d = 1 := by
      have hdisj := (bs_eq_sup h).2
      rw [Subgroup.disjoint_def] at hdisj
      exact hdisj hmem1 hmem2
    have hdvd : (3 : ℤ) ∣ d := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have hw3 : wElt φ₂ ^ 3 = 1 := h.basic.2.1 _ h.wElt_mem
      have hwne : wElt φ₂ ≠ 1 := by
        intro hh
        apply omegaBlock_ne_one 5 ⟨4, by omega⟩
        apply h.coords.inj₂
        rw [show wElt φ₂ = φ₂ (omegaBlock 5 ⟨4, by omega⟩) from rfl] at hh
        rw [hh, map_one]
      have hord : orderOf (wElt φ₂) = 3 := orderOf_eq_prime hw3 hwne
      have h3 := orderOf_dvd_iff_zpow_eq_one.mpr hwd1
      rwa [hord] at h3
    have htriple : (vElt φ₁ ^ a * uElt φ₂ ^ b) * (φ₁ (omegaBlock 5 4)) ^ c = 1 := by
      have hh := hpowG
      rw [hwd1, mul_one] at hh
      exact hh
    have hω : (omegaBlock 5 ⟨0, by omega⟩) ^ a * (omegaBlock 5 ⟨2, by omega⟩) ^ b *
        (omegaBlock 5 ⟨4, by omega⟩) ^ c = 1 := by
      apply h.coords.inj₁
      rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_one]
      have htu : φ₁ (omegaBlock 5 ⟨2, by omega⟩) = uElt φ₂ := by
        rw [uElt_eq h]
      rw [show φ₁ (omegaBlock 5 ⟨0, by omega⟩) = vElt φ₁ from rfl, htu,
        show omegaBlock 5 ⟨4, by omega⟩ = omegaBlock 5 4 from by norm_num]
      exact htriple
    obtain ⟨h3a, h3b, h3c⟩ := halfTorus5_indep hω
    exact ⟨h3a, h3b, h3c, hdvd⟩

end GGHalfCtx

end CFSG.StandardType

end
