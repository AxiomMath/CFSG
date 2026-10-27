module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf
public import CFSG.Quasithin.Recognition.F112Crit.BenderRigidDefs
public import CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs γ₀ γ₁)

@[expose] def RigidAt {G₀ G₁ G₂ : Subgroup G} (μ δ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) :
    Prop :=
  ∃ δ' ∈ nbrs μ, δ' ≠ δ ∧ ∀ c ∈ stab μ ⊓ stab δ ⊓ stab δ',
    (∃ k : ℕ, c ^ 2 ^ k ∈ ballStab 1 μ) →
    (∀ d ∈ L ⊓ stab δ ⊓ stab δ', c * d * c⁻¹ * d⁻¹ ∈ ballStab 1 μ) → c ∈ ballStab 1 μ

structure RigidLocal {G₀ G₁ G₂ : Subgroup G} (μ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) :
    Prop where
  rigid : ∀ δ ∈ nbrs μ, RigidAt μ δ L

theorem RigidAt.smul {G₀ G₁ G₂ : Subgroup G} {μ δ : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (h : RigidAt μ δ L) (g : ↥G₀) : RigidAt (g • μ) (g • δ) (conjSub (g : G) L) := by
  obtain ⟨δ', hδ', hne, hrig⟩ := h
  refine ⟨g • δ', (CosetGeom.smul_adj g).mpr hδ', fun h' => hne (smul_left_cancel g h'), ?_⟩
  intro c hc hk hcd
  rw [CosetGeom.stab_smul, CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf,
    ← conjSub_inf, mem_conjSub] at hc
  rw [CosetGeom.ballStab_smul, mem_conjSub]
  refine hrig _ hc ?_ ?_
  · obtain ⟨k, hk⟩ := hk
    refine ⟨k, ?_⟩
    rw [CosetGeom.ballStab_smul, mem_conjSub] at hk
    have e : ((g : G)⁻¹ * c * g) ^ 2 ^ k = (g : G)⁻¹ * c ^ 2 ^ k * g := by
      have := map_pow (MulAut.conj (g : G)⁻¹) c (2 ^ k)
      simpa [MulAut.conj_apply] using this.symm
    rw [e]
    exact hk
  · intro d hd
    have h1 := hcd ((g : G) * d * (g : G)⁻¹) (by
      rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, ← conjSub_inf, mem_conjSub]
      simpa [mul_assoc] using hd)
    rw [CosetGeom.ballStab_smul, mem_conjSub] at h1
    convert h1 using 1
    group

namespace RigidLocalOf

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem smul_γ₁_mem_nbrs (hs : Setting L₁ L₂ S Z) {y : ↥(L₁ ⊔ L₂ ⊔ S)} (hy : (y : G) ∈ L₂) :
    y • ν₁ ∈ nbrs ν₀ := by
  have hy0 : y • ν₀ = ν₀ := CosetGeom.smul_eq_of_mem_stab (by
    rw [BenderLocalOf.stab_γ₀_eq hs]
    exact Subgroup.mem_sup_left hy)
  have h := (CosetGeom.smul_adj y).mpr (CosetGeom.adj_γ₀_γ₁ (G₀ := L₁ ⊔ L₂ ⊔ S)
    (G₁ := P₂ L₁ L₂ S) (G₂ := P₁ L₁ L₂ S))
  rwa [hy0] at h

theorem conj_mem_P₁_of_mem_ballStab (hs : Setting L₁ L₂ S Z) {e y : G}
    (he : e ∈ ballStab 1 ν₀) (hy : y ∈ L₂) : y⁻¹ * e * y ∈ P₁ L₁ L₂ S := by
  have hyΛ : y ∈ L₁ ⊔ L₂ ⊔ S := hs.toCritAmalgam.amalgam.le₁ (Subgroup.mem_sup_left hy)
  have hnb : (graph (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)).Adj ν₀
      ((⟨y, hyΛ⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁) := smul_γ₁_mem_nbrs hs hy
  have h1 := CosetGeom.mem_ballStab.mp he _ (CosetGeom.dist_eq_one_iff_adj.mpr hnb).le
  rwa [CosetGeom.stab_smul, mem_conjSub, BenderLocalOf.stab_γ₁_eq hs] at h1

theorem mem_ballStab_of_forall (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) {c : G} (hc : c ∈ stab ν₀)
    (h : ∀ y ∈ oddGen L₂, y⁻¹ * c * y ∈ P₁ L₁ L₂ S) : c ∈ ballStab 1 ν₀ := by
  refine CosetGeom.mem_ballStab.mpr fun ε hε => ?_
  rcases (CosetGeom.dist_le_one_iff hs.toCritAmalgam.amalgam.gen).mp hε with rfl | hadj
  · exact hc
  · obtain ⟨g, hg, rfl⟩ := BenderLocalOf.exists_smul_γ₁_eq hK hs hadj
    rw [CosetGeom.stab_smul, mem_conjSub, BenderLocalOf.stab_γ₁_eq hs]
    exact h _ hg

theorem mk_mem_normalizer_iff (hs : Setting L₁ L₂ S Z) {P : Sylow 2 (oTwoQuot ↥L₂)}
    (hP : (P : Subgroup (oTwoQuot ↥L₂)) =
      ((S ⊓ L₂).subgroupOf L₂).map (QuotientGroup.mk' (pCore 2 ↥L₂))) (z : ↥L₂) :
    QuotientGroup.mk' (pCore 2 ↥L₂) z ∈
        Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥L₂)) : Set (oTwoQuot ↥L₂)) ↔
      (z : G) ∈ P₁ L₁ L₂ S := by
  rw [← Subgroup.mem_comap, BenderLocalOf.comap_normalizer_oTwoQuot
    (BenderLocalOf.isSylowTwoOf_inf hs) hP, Subgroup.mem_subgroupOf,
    BenderLocalOf.mem_P₁_iff hs z.2]

theorem rigidAt_γ₁ (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    (hR : IsRigidQuot (oTwoQuot ↥L₂)) : RigidAt ν₀ ν₁ (oddGen L₂) := by
  have hA := hs.toCritAmalgam.amalgam
  have hN := BenderLocalOf.P₂_le_normalizer hs
  obtain ⟨P, hP⟩ := BenderLocalOf.exists_sylow_oTwoQuot (BenderLocalOf.isSylowTwoOf_inf hs)
  have hmem := mk_mem_normalizer_iff hs hP
  obtain ⟨xb, hxb, hrig⟩ := hR.rigid P
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) xb
  have hxΛ : (x : G) ∈ L₁ ⊔ L₂ ⊔ S := hA.le₁ (Subgroup.mem_sup_left x.2)
  have hstab' : stab ((⟨x, hxΛ⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁) = conjSub (x : G) (P₁ L₁ L₂ S) := by
    rw [CosetGeom.stab_smul, BenderLocalOf.stab_γ₁_eq hs]
  refine ⟨(⟨x, hxΛ⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁, smul_γ₁_mem_nbrs hs x.2,
    fun h => hxb ((hmem x).mpr ?_), ?_⟩
  · have := CosetGeom.mem_stab_of_smul_eq h
    rwa [BenderLocalOf.stab_γ₁_eq hs] at this
  intro c hc hk hcd
  obtain ⟨hc01, hc2⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hc0, hc1⟩ := Subgroup.mem_inf.mp hc01
  rw [BenderLocalOf.stab_γ₀_eq hs] at hc0
  rw [BenderLocalOf.stab_γ₁_eq hs] at hc1
  rw [hstab', mem_conjSub] at hc2
  have hconj : ∀ (m : G) (hm : m ∈ P₂ L₁ L₂ S) (y : ↥L₂),
      CFSG.GroupTheory.conjModPCore 2 L₂ (P₂ L₁ L₂ S) hN ⟨m, hm⟩
          (QuotientGroup.mk' (pCore 2 ↥L₂) y) =
        QuotientGroup.mk' (pCore 2 ↥L₂) ⟨m * y * m⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hN hm) (y : G)).mp y.2⟩ := fun m hm y =>
    CFSG.GroupTheory.conjModPCore_mk 2 L₂ (P₂ L₁ L₂ S) hN ⟨m, hm⟩ y
  have hcls : ∀ (y z : ↥L₂), (QuotientGroup.mk' (pCore 2 ↥L₂) y)⁻¹ *
      QuotientGroup.mk' (pCore 2 ↥L₂) z * QuotientGroup.mk' (pCore 2 ↥L₂) y ∈
        Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥L₂)) : Set (oTwoQuot ↥L₂)) ↔
      (y : G)⁻¹ * z * y ∈ P₁ L₁ L₂ S := fun y z => by
    rw [← map_inv, ← map_mul, ← map_mul, hmem]
    rfl
  set σ := CFSG.GroupTheory.conjModPCore 2 L₂ (P₂ L₁ L₂ S) hN ⟨c, hc0⟩ with hσ
  have hfix := hrig σ ?_ ?_ ?_
  ·
    refine mem_ballStab_of_forall hs hK (by rw [BenderLocalOf.stab_γ₀_eq hs]; exact hc0)
      fun y hy => ?_
    have h1 := hfix (QuotientGroup.mk' (pCore 2 ↥L₂) ⟨y, MS93.oddGen_le L₂ hy⟩)
    rw [hσ, hconj, ← map_inv, ← map_mul, hmem] at h1
    have h2 : y⁻¹ * (c * y * c⁻¹) * c ∈ P₁ L₁ L₂ S := mul_mem h1 hc1
    simpa [mul_assoc] using h2
  ·
    obtain ⟨k, hk⟩ := hk
    refine ⟨k, fun yb => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) yb
    have hpow : σ ^ 2 ^ k =
        CFSG.GroupTheory.conjModPCore 2 L₂ (P₂ L₁ L₂ S) hN ⟨c ^ 2 ^ k, pow_mem hc0 _⟩ := by
      rw [hσ, ← map_pow]
      exact congrArg _ (Subtype.ext (SubgroupClass.coe_pow _ _))
    rw [hpow, hconj, ← map_inv, ← map_mul, hmem]
    have h1 := conj_mem_P₁_of_mem_ballStab hs hk y.2
    have h2 : (c ^ 2 ^ k)⁻¹ ∈ P₁ L₁ L₂ S := inv_mem (pow_mem hc1 _)
    have h3 : (y : G)⁻¹ * (c ^ 2 ^ k * y * (c ^ 2 ^ k)⁻¹) ∈ P₁ L₁ L₂ S := by
      have := mul_mem h1 h2
      simpa [mul_assoc] using this
    exact h3
  ·
    intro mb hmb
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) mb
    rw [hσ, hconj, hmem]
    exact mul_mem (mul_mem hc1 ((hmem m).mp hmb)) (inv_mem hc1)
  ·
    intro db hdb hdbx yb
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) db
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) yb
    have hd1 : (d : G) ∈ P₁ L₁ L₂ S := (hmem d).mp hdb
    have hd2 : (x : G)⁻¹ * d * x ∈ P₁ L₁ L₂ S := (hcls x d).mp hdbx
    obtain ⟨a, ha, o, ho, hao⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
      ((MS93.oddGen_le L₂).trans (le_normalizer_pCoreOf 2 L₂))).mp
        (BenderLocalOf.le_oddGen_sup_pCoreOf hK d.2)
    have hoP : o ∈ P₁ L₁ L₂ S :=
      BenderLocalOf.bigB_le_P₁ (BenderLocalOf.pCoreOf_le_bigB hs ho)
    have ha1 : a ∈ P₁ L₁ L₂ S := by
      have e : a = (d : G) * o⁻¹ := by rw [hao]; group
      rw [e]
      exact mul_mem hd1 (inv_mem hoP)
    have ha2 : (x : G)⁻¹ * a * x ∈ P₁ L₁ L₂ S := by
      have ho' : (x : G)⁻¹ * o⁻¹ * x ∈ P₁ L₁ L₂ S := by
        refine BenderLocalOf.bigB_le_P₁ (BenderLocalOf.pCoreOf_le_bigB hs ?_)
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 L₂ (L₂.inv_mem x.2)) o⁻¹).mp (inv_mem ho)
        simpa using this
      have e : (x : G)⁻¹ * a * x = ((x : G)⁻¹ * d * x) * ((x : G)⁻¹ * o⁻¹ * x) := by
        rw [hao]; group
      rw [e]
      exact mul_mem hd2 ho'
    have hca := hcd a (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨ha, by rw [BenderLocalOf.stab_γ₁_eq hs]; exact ha1⟩, by rw [hstab', mem_conjSub]; exact ha2⟩)
    have haL : a ∈ L₂ := MS93.oddGen_le L₂ ha
    have hda : QuotientGroup.mk' (pCore 2 ↥L₂) d =
        QuotientGroup.mk' (pCore 2 ↥L₂) (⟨a, haL⟩ : ↥L₂) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine (F1.mem_pCore_iff_coe _).mpr ?_
      have e : (((d⁻¹ * ⟨a, haL⟩ : ↥L₂)) : G) = o⁻¹ := by
        show (d : G)⁻¹ * a = o⁻¹
        rw [hao]; group
      rw [e]
      exact inv_mem ho
    have hcaL : c * a * c⁻¹ ∈ L₂ := (Subgroup.mem_normalizer_iff.mp (hN hc0) a).mp haL
    rw [hda, hσ, hconj c hc0]
    have e : QuotientGroup.mk' (pCore 2 ↥L₂) (⟨c * a * c⁻¹, hcaL⟩ : ↥L₂) *
        (QuotientGroup.mk' (pCore 2 ↥L₂) ⟨a, haL⟩)⁻¹ =
        QuotientGroup.mk' (pCore 2 ↥L₂) ⟨c * a * c⁻¹ * a⁻¹, mul_mem hcaL (inv_mem haL)⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hcls]
    exact conj_mem_P₁_of_mem_ballStab hs hca y.2

end RigidLocalOf

namespace Setting

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

theorem rigidLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    (hR : IsRigidQuot (oTwoQuot ↥L₂)) :
    RigidLocal (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) (oddGen L₂) where
  rigid := by
    intro δ hδ
    obtain ⟨g, hg, rfl⟩ := BenderLocalOf.exists_smul_γ₁_eq hK hs hδ
    have h := (RigidLocalOf.rigidAt_γ₁ hs hK hR).smul g
    have h0 : g • γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) =
        γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) := by
      refine CosetGeom.smul_eq_of_mem_stab ?_
      rw [BenderLocalOf.stab_γ₀_eq hs]
      exact Subgroup.mem_sup_left (MS93.oddGen_le L₂ hg)
    have hL : conjSub (g : G) (oddGen L₂) = oddGen L₂ :=
      F1.conjSub_eq_of_mem_normalizer (MS93.le_normalizer_oddGen L₂ (MS93.oddGen_le L₂ hg))
    rw [h0, hL] at h
    exact h

end Setting

end CFSG.Quasithin.F112Crit

end
