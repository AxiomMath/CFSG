module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem fs81Sp_inf_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKz : Subgroup.center K = ⊥) :
    K ⊓ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxK : x ∈ K := hx.1
  have hxCent : x ∈ Subgroup.centralizer (K : Set G) := hx.2.2
  have hxCenter : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm := Subgroup.mem_centralizer_iff.mp hxCent (y : K) y.2
    apply Subtype.ext
    simpa using hcomm
  have hxone : (⟨x, hxK⟩ : K) = 1 := by
    have hmem : (⟨x, hxK⟩ : K) ∈ (⊥ : Subgroup K) := by
      rw [← hKz]
      exact hxCenter
    simpa using hmem
  exact congrArg Subtype.val hxone

theorem fs81Sp_comm {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G} :
    ∀ k ∈ K, ∀ d ∈ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)),
      k * d = d * k := by
  intro k hk d hd
  have hdCent : d ∈ Subgroup.centralizer (K : Set G) := hd.2
  exact Subgroup.mem_centralizer_iff.mp hdCent k hk

theorem fs81Sp_mem_sup_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hyA | hyB
    · exact ⟨y, hyA, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hyB, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y z hy hz ihy ihz =>
    rcases ihy with ⟨a1, ha1, b1, hb1, rfl⟩
    rcases ihz with ⟨a2, ha2, b2, hb2, rfl⟩
    have hcomm_b1_a2 : b1 * a2 = a2 * b1 := (hcomm a2 ha2 b1 hb1).symm
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    calc
      a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
      _ = a1 * (a2 * b1) * b2 := by rw [hcomm_b1_a2]
      _ = a1 * a2 * (b1 * b2) := by group
  | inv y hy ihy =>
    rcases ihy with ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc
      (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        rw [← inv_inj]
        simpa [mul_inv_rev] using hcomm a ha b hb

theorem fs81Sp_phi_apply_mem_K {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hC_le_norm : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (k : K) :
    K.normalizerMonoidHom (Subgroup.inclusion hC_le_norm (Subgroup.inclusion hKC k)) =
      MulAut.conj k := by
  ext x
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]

theorem fs81Sp_no_three_index {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hOut : ¬ 3 ∣ Nat.card (Outer K)) :
    ¬ 3 ∣ ((K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))).subgroupOf
      (Subgroup.centralizer ({b₀} : Set G))).index := by
  let C := Subgroup.centralizer ({b₀} : Set G)
  let D := C ⊓ Subgroup.centralizer (K : Set G)
  have hC_le_norm : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact hKn
  let φ : C →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hC_le_norm)
  let ψ : C →* Outer K := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).comp φ
  have hφk : ∀ k : K, φ (Subgroup.inclusion hKC k) = MulAut.conj k := by
    intro k
    exact fs81Sp_phi_apply_mem_K hKC hC_le_norm k
  have hker_phi : φ.ker = D.subgroupOf C := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hmem : (Subgroup.inclusion hC_le_norm x) ∈ K.normalizerMonoidHom.ker := by
        simpa [φ] using hx
      rw [Subgroup.normalizerMonoidHom_ker] at hmem
      rw [Subgroup.mem_subgroupOf] at hmem
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, hmem⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hxCent : (x : G) ∈ Subgroup.centralizer (K : Set G) := hx.2
      rw [MonoidHom.mem_ker]
      have hmem : (Subgroup.inclusion hC_le_norm x) ∈ K.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        rw [Subgroup.mem_subgroupOf]
        exact hxCent
      simpa [φ] using hmem
  have hker_psi : ψ.ker = (K ⊔ D).subgroupOf C := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx_inner : φ x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K := by
        have h1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) (φ x) = 1 := by
          simpa [ψ] using hx
        exact (QuotientGroup.eq_one_iff (φ x)).mp h1
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hx_inner
      have hφk_eq : φ (Subgroup.inclusion hKC k) = φ x := by
        rw [hφk k]
        exact hk
      have hmem_ker : x * (Subgroup.inclusion hKC k)⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_inv, hφk_eq]
        simp
      have hdD : x * (Subgroup.inclusion hKC k)⁻¹ ∈ D.subgroupOf C := by
        rw [← hker_phi]
        exact hmem_ker
      have hikK : (Subgroup.inclusion hKC k : G) ∈ K := by
        simpa using k.2
      have hikK_C : Subgroup.inclusion hKC k ∈ K.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        exact hikK
      have hx_eq : x = (x * (Subgroup.inclusion hKC k)⁻¹) * (Subgroup.inclusion hKC k) := by
        group
      rw [hx_eq]
      have hmul : (x * (Subgroup.inclusion hKC k)⁻¹) * (Subgroup.inclusion hKC k) ∈
          D.subgroupOf C ⊔ K.subgroupOf C := by
        exact Subgroup.mul_mem_sup hdD hikK_C
      rw [← Subgroup.subgroupOf_sup inf_le_left hKC] at hmul
      rw [sup_comm] at hmul
      exact hmul
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨a, ha, b, hb, hx_eq⟩ := fs81Sp_mem_sup_of_commute (fs81Sp_comm) hx
      rw [MonoidHom.mem_ker]
      have hx_inner : φ x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K := by
        have hx_eq_C : x = Subgroup.inclusion hKC ⟨a, ha⟩ * ⟨b, hb.1⟩ := by
          apply Subtype.ext
          simpa [Subgroup.inclusion] using hx_eq
        have hbD : ⟨b, hb.1⟩ ∈ D.subgroupOf C := by
          rw [Subgroup.mem_subgroupOf]
          exact hb
        have hφb : φ ⟨b, hb.1⟩ = 1 := by
          have : ⟨b, hb.1⟩ ∈ φ.ker := by
            rw [hker_phi]
            exact hbD
          simpa using this
        have hφx : φ x = MulAut.conj ⟨a, ha⟩ := by
          rw [hx_eq_C, map_mul, hφb, mul_one]
          exact hφk ⟨a, ha⟩
        rw [hφx]
        exact ⟨⟨a, ha⟩, rfl⟩
      change QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) (φ x) = 1
      exact (QuotientGroup.eq_one_iff (φ x)).mpr hx_inner
  have hcard_dvd : Nat.card (C ⧸ ψ.ker) ∣ Nat.card (Outer K) := by
    have h1 : Nat.card (C ⧸ ψ.ker) = Nat.card ψ.range := by
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hindex_eq : Nat.card (C ⧸ ψ.ker) = ((K ⊔ D).subgroupOf C).index := by
    rw [hker_psi]
    exact (Subgroup.index_eq_card (H := (K ⊔ D).subgroupOf C)).symm
  intro h3
  apply hOut
  exact dvd_trans h3 (hindex_eq ▸ hcard_dvd)

theorem fs81Sp_exists_sylow_le_of_not_dvd_index {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hS : ¬ p ∣ S.index) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ S := by
  let PS : Sylow p S := Classical.choice Sylow.nonempty
  let Pmap : Subgroup G := (PS : Subgroup S).map S.subtype
  have hPmap_p : IsPGroup p (↥Pmap) := by
    exact IsPGroup.map (p := p) (H := (PS : Subgroup S)) PS.isPGroup' S.subtype
  have hPmap_not_dvd : ¬ p ∣ Pmap.index := by
    have hPS_not_dvd : ¬ p ∣ (PS : Subgroup S).index := PS.not_dvd_index
    rw [show Pmap = (PS : Subgroup S).map S.subtype by rfl]
    rw [Subgroup.index_map_subtype (H := S) (K := (PS : Subgroup S))]
    exact Nat.Prime.not_dvd_mul (Fact.out : Nat.Prime p) hPS_not_dvd hS
  refine ⟨hPmap_p.toSylow hPmap_not_dvd, ?_⟩
  simpa [Pmap] using (Subgroup.map_subtype_le (H := S) (K := (PS : Subgroup S)))

theorem fs81Sp_sylow_le_normal {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S : Subgroup G} [hS_normal : S.Normal]
    (hS : ¬ p ∣ S.index) (P : Sylow p G) :
    (P : Subgroup G) ≤ S := by
  obtain ⟨Q, hQ_le⟩ := fs81Sp_exists_sylow_le_of_not_dvd_index (p := p) hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmap : (Q : Subgroup G).map (MulAut.conj g).toMonoidHom =
      ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hg, ← hmap]
  rintro _ ⟨q, hq, rfl⟩
  exact hS_normal.conj_mem q (hQ_le hq) g

end CFSG.StandardType.FrameRoute
