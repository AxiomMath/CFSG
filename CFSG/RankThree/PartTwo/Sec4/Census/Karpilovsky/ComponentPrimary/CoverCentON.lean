module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Alt6Count
public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.Native.ONTripleK0
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TripleCoverON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.Blueprint Subgroup
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21

section Embedding


theorem exists_alt6_embedding_range {X : Type*} [Group X] (φ : GM →* X) (hker : φ.ker = zpowers zG) :
    ∃ ι : alternatingGroup (Fin 6) →* X, Function.Injective ι ∧
      (∀ g, ι g ∈ centralizer ({φ (xG 0)} : Set X)) ∧ ι.range = K0G.map φ := by
  let ψ : K0G →* alternatingGroup (Fin 6) :=
    actK.codRestrict (alternatingGroup (Fin 6)) (fun k => by
      rw [← range_actK]; exact ⟨k, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro g
    have : (g : Equiv.Perm (Fin 6)) ∈ actK.range := by rw [range_actK]; exact g.2
    obtain ⟨k, hk⟩ := this
    exact ⟨k, Subtype.ext hk⟩
  have hψker : ∀ k, ψ k = 1 ↔ actK k = 1 := fun k => by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  let φK : K0G →* X := φ.comp K0G.subtype
  have hz : ∀ n : ℤ, actK ((⟨zG, zG_mem_K0⟩ : K0G) ^ n) = 1 := by
    intro n
    rw [map_zpow, actK_z, one_zpow]
  have hle : ψ.ker ≤ φK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hψker] at hk
    have hk' : k ∈ actK.ker := hk
    rw [ker_actK] at hk'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
    rw [MonoidHom.mem_ker]
    have h : zG ^ n ∈ φ.ker := by
      rw [hker]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zG) n
    rw [MonoidHom.mem_ker] at h
    simpa [φK] using h
  have hle' : φK.ker ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hk' : (k : GM) ∈ φ.ker := hk
    rw [hker] at hk'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk'
    have : k = (⟨zG, zG_mem_K0⟩ : K0G) ^ n := Subtype.ext (by simpa using hn.symm)
    rw [MonoidHom.mem_ker, hψker, this]
    exact hz n
  let ι := (MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ)
    (Function.rightInverse_surjInv hψ)) ⟨φK, hle⟩
  have hι : ∀ k, ι (ψ k) = φ (k : GM) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φK, hle⟩ k
  refine ⟨ι, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨k, rfl⟩ := hψ a
    rw [hι] at ha
    have : k ∈ φK.ker := ha
    exact hle' this
  · intro a
    obtain ⟨k, rfl⟩ := hψ a
    rw [hι, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    have hc := K0G_le_centralizer k.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc]
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨k, rfl⟩ := hψ a
      exact ⟨(k : GM), k.2, (hι k).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ψ ⟨y, hy⟩, hι ⟨y, hy⟩⟩

theorem alt6_data_of_cover {G : Type} [Group G] (φ : GM →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker = zpowers zG) :
    ∃ E : Subgroup G, Nonempty (↥E ≃* alternatingGroup (Fin 6)) ∧
      E ≤ centralizer ({φ (xG 0)} : Set G) ∧
      ∀ c ∈ centralizer ({φ (xG 0)} : Set G), ∀ e ∈ E,
        c * e * c⁻¹ ∈ zpowers (φ (xG 0)) ⊔ E := by
  obtain ⟨ι, hι, -, hrange⟩ := exists_alt6_embedding_range φ hker
  set E : Subgroup G := K0G.map φ with hE
  let eE : ↥E ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hι).symm
  have hEC : E ≤ centralizer ({φ (xG 0)} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    have hc := mem_centralizer_singleton_iff.1 (K0G_le_centralizer hk)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]
  refine ⟨E, ⟨eE⟩, hEC, ?_⟩
  intro c hc e he
  obtain ⟨ct, rfl⟩ := hφ c
  obtain ⟨k, hk, rfl⟩ := he
  have hc' : φ ct * φ (xG 0) = φ (xG 0) * φ ct := mem_centralizer_singleton_iff.1 hc
  have hk0 : k * xG 0 = xG 0 * k := mem_centralizer_singleton_iff.1 (K0G_le_centralizer hk)
  have hmem : (xG 0)⁻¹ * (ct⁻¹ * xG 0 * ct) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have h : (φ ct)⁻¹ * φ (xG 0) * φ ct = φ (xG 0) := by
      rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h, inv_mul_cancel]
  rw [hker] at hmem
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
  have hy : ct⁻¹ * xG 0 * ct = xG 0 * zG ^ n := by
    rw [hn]; group
  have hkz : k * zG ^ n = zG ^ n * k := ((Commute.zpow_left (zG_central k) n) : Commute (zG ^ n) k).eq.symm
  have hky : k * (ct⁻¹ * xG 0 * ct) = (ct⁻¹ * xG 0 * ct) * k := by
    rw [hy, ← mul_assoc, hk0, mul_assoc, hkz, ← mul_assoc]
  have hcomm : xG 0 * (ct * k * ct⁻¹) = (ct * k * ct⁻¹) * xG 0 := by
    have h1 : xG 0 = ct * (ct⁻¹ * xG 0 * ct) * ct⁻¹ := by group
    calc xG 0 * (ct * k * ct⁻¹) = ct * ((ct⁻¹ * xG 0 * ct) * k) * ct⁻¹ := by group
      _ = ct * (k * (ct⁻¹ * xG 0 * ct)) * ct⁻¹ := by rw [hky]
      _ = (ct * k * ct⁻¹) * xG 0 := by group
  have hin : ct * k * ct⁻¹ ∈ centralizer ({xG 0} : Set GM) := mem_centralizer_singleton_iff.2 hcomm.symm
  rw [(centralizer_x0_eq).1] at hin
  have himg := Subgroup.mem_map_of_mem φ hin
  rw [Subgroup.map_sup, MonoidHom.map_zpowers] at himg
  simpa [map_mul, map_inv] using himg

theorem not_hasType424_centralizer_of_cover {G : Type} [Group G] [Finite G] (φ : GM →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker = zpowers zG)
    (hcard : Nat.card (centralizer ({φ (xG 0)} : Set G)) = 3240) :
    ¬ Sec11.KS11Lie2Proof.HasType424 ↥(centralizer ({φ (xG 0)} : Set G)) := by
  obtain ⟨E, ⟨eE⟩, hEC, hmove⟩ := alt6_data_of_cover φ hφ hker
  exact not_hasType424_of_alt6_index_nine _ E eE hEC hcard hmove

theorem alt6_normal_of_cover {G : Type} [Group G] (φ : GM →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker = zpowers zG)
    (hcard : Nat.card (centralizer ({φ (xG 0)} : Set G)) = 3240) :
    ∃ E : Subgroup ↥(centralizer ({φ (xG 0)} : Set G)), E.Normal ∧
      Nonempty (↥E ≃* alternatingGroup (Fin 6)) ∧ Nat.card (↥(centralizer ({φ (xG 0)} : Set G)) ⧸ E) = 9 := by
  obtain ⟨E, ⟨eE⟩, hEC, hmove⟩ := alt6_data_of_cover φ hφ hker
  obtain ⟨hn, hq⟩ := alt6_normal_index_nine _ E eE hEC hcard hmove
  exact ⟨E.subgroupOf _, hn, ⟨(Subgroup.subgroupOfEquivOfLe hEC).trans eE⟩, hq⟩

end Embedding


theorem on_cover_data :
    ∃ φ : GM →* NativeSporadic.Carrier .ONan, Function.Surjective φ ∧ φ.ker = zpowers zG ∧
      (∀ x : NativeSporadic.Carrier .ONan, orderOf x = 3 →
        ∃ g : NativeSporadic.Carrier .ONan, x = g * φ (xG 0) * g⁻¹) ∧
      Nat.card (centralizer ({φ (xG 0)} : Set (NativeSporadic.Carrier .ONan))) = 3240 := by
  obtain ⟨φ, hφ, hker⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.exists_hom_ON
  set x₁ : (NativeSporadic.Carrier .ONan) := φ (xG 0) with hx₁
  have hx₁3 : orderOf x₁ = 3 := by
    have h3 : x₁ ^ 3 = 1 := by
      rw [hx₁, ← map_pow]
      have : xG 0 ^ 3 = 1 := by
        have h := pow_orderOf_eq_one (xG 0)
        rwa [orderOf_xG0] at h
      rw [this, map_one]
    have h1 : x₁ ≠ 1 := by
      intro h
      have hmem : xG 0 ∈ φ.ker := h
      rw [hker] at hmem
      have hK : xG 0 ∈ K0G := zpowers_le.mpr zG_mem_K0 hmem
      have : xG 0 ∈ zpowers (xG 0) ⊓ K0G := ⟨Subgroup.mem_zpowers _, hK⟩
      rw [zpowers_inf_K0, Subgroup.mem_bot] at this
      have h3 := orderOf_xG0
      rw [this, orderOf_one] at h3
      omega
    exact orderOf_eq_prime h3 h1
  refine ⟨φ, hφ, hker, fun x hx => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := onThree_fusion hx₁3 hx
    exact ⟨k, hk.symm⟩
  · obtain ⟨k, hk⟩ := onThree_fusion hx₁3 orderOf_onThreeElt
    have := (CFSG.AGLEmbeddingD2.Wilson.Census228Spor.card_conj_data k x₁ x₁).2
    rw [hk] at this
    exact this.symm.trans card_centralizer_onThreeElt

theorem noType424At3_ON :
    Coordinator.CoverCent.NoType424At3 (NativeSporadic.Carrier .ONan) := by
  have : Finite (NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  obtain ⟨φ, hφ, hker, hconj, hcard⟩ := on_cover_data
  exact noType424At3_of_conj_class _ hconj
    (not_hasType424_centralizer_of_cover φ hφ hker hcard)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
