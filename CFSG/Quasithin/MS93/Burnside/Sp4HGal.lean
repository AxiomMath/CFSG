module

import CFSG.Quasithin.MS93.S33SpCoord
import CFSG.Quasithin.MS93.S34EAB
public import CFSG.Quasithin.MS93.S34FFlat
public import CFSG.Quasithin.MS93.S34FPar

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem burnsideSp4H_ringHom_eq {F : Type} [Field F] [Finite F] [CharP F 2] {σ τ : F →+* F}
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (hσ1 : ∃ x, σ x ≠ x)
    (hτ1 : ∃ x, τ x ≠ x) : ∀ x, σ x = τ x := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomm : ∀ (ρ : F →+* F) (r : ZMod 2),
      ρ (algebraMap (ZMod 2) F r) = algebraMap (ZMod 2) F r := fun ρ r =>
    DFunLike.congr_fun
      (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)) r
  let toAlg : (F →+* F) → (F →ₐ[ZMod 2] F) := fun ρ => { ρ with commutes' := hcomm ρ }
  have hbij : ∀ ρ : F →+* F, Function.Bijective (toAlg ρ) := fun ρ =>
    Finite.injective_iff_bijective.mp ρ.injective
  let e : (F →+* F) → (F ≃ₐ[ZMod 2] F) := fun ρ => AlgEquiv.ofBijective (toAlg ρ) (hbij ρ)
  have he : ∀ ρ x, e ρ x = ρ x := fun _ _ => rfl
  have hsq : ∀ ρ : F →+* F, (∀ x, ρ (ρ x) = x) → e ρ ^ 2 = 1 := fun ρ hρ => by
    ext x
    rw [pow_two, AlgEquiv.mul_apply, he, he, hρ, AlgEquiv.one_apply]
  have hne : ∀ ρ : F →+* F, (∃ x, ρ x ≠ x) → e ρ ≠ 1 := fun ρ ⟨x, hx⟩ h1 => hx (by
    have := congrArg (fun φ : F ≃ₐ[ZMod 2] F => φ x) h1
    simpa [he] using this)
  haveI : Finite (F ≃ₐ[ZMod 2] F) :=
    Finite.of_injective (fun φ : F ≃ₐ[ZMod 2] F => (φ : F → F)) fun a b hab =>
      AlgEquiv.ext (congrFun hab)
  haveI : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  by_contra hστ
  push Not at hστ
  obtain ⟨x₀, hx₀⟩ := hστ
  have hστ' : e σ ≠ e τ := fun h => hx₀ (by
    have := congrArg (fun φ : F ≃ₐ[ZMod 2] F => φ x₀) h
    simpa [he] using this)
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod 2] F) (n := 2) (by norm_num)
  have hsub : ({1, e σ, e τ} : Finset (F ≃ₐ[ZMod 2] F)) ⊆
      Finset.univ.filter (fun a : F ≃ₐ[ZMod 2] F => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hsq σ hσ
    · exact hsq τ hτ
  have h3 : ({1, e σ, e τ} : Finset (F ≃ₐ[ZMod 2] F)).card = 3 := by
    have h1σ : (1 : F ≃ₐ[ZMod 2] F) ≠ e σ := (hne σ hσ1).symm
    have h1τ : (1 : F ≃ₐ[ZMod 2] F) ≠ e τ := (hne τ hτ1).symm
    rw [Finset.card_insert_of_notMem (by simp [h1σ, h1τ]), Finset.card_pair hστ']
  have h4 := Finset.card_le_card hsub
  omega

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4H_mul_mem_sup (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) {t t' : G}
    (ht : t ∈ T) (ht' : t' ∈ T) (ht2 : t ^ 2 = 1) (ht'2 : t' ^ 2 = 1)
    (htL : t ∉ L ⊔ pCoreOf 2 M) (ht'L : t' ∉ L ⊔ pCoreOf 2 M) : t * t' ∈ L ⊔ pCoreOf 2 M := by
  obtain ⟨m, F, _, _, a, -, hcard, ha, hLV, -, β, hβ, hβker, hβα⟩ := hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  have hsemi : ∀ y ∈ T, ∃ f : MSP.V4 F →+ MSP.V4 F, IsCoordAct β y f ∧
      ∃ σ : F →+* F, ∀ (c : F) (v : MSP.V4 F), f (c • v) = σ c • f v := by
    intro y hy
    obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker (hTV hy) (hTZ hy)
    obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem (hTV hy)) (hTZ (inv_mem hy))
    obtain ⟨σ, hσ⟩ := S33.exists_semilinear_sp ha hLV hβ (S33.isCoordAct_of_natSp hβα)
      (hTV hy) (h.le_normalizer (h.le hy)) hf hf'
    exact ⟨f, hf, σ, hσ⟩
  have hlin : ∀ y ∈ T, ∀ f : MSP.V4 F →+ MSP.V4 F, IsCoordAct β y f →
      (∀ (c : F) (v : MSP.V4 F), f (c • v) = c • f v) → y ∈ L ⊔ pCoreOf 2 M := by
    intro y hy f hf hl
    obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker (hTV hy) (hTZ hy) hf hl
    exact S34D.mem_sup_of_isCoordAct_sp h hcard' ha hβ hβker hβα hy hγ
  obtain ⟨v₀, hv₀⟩ : ∃ v : MSP.V4 F, v ≠ 0 :=
    ⟨fun _ => 1, fun h0 => one_ne_zero (congrFun h0 (Sum.inl 0))⟩
  have hinvol : ∀ y ∈ T, y ^ 2 = 1 → ∀ f : MSP.V4 F →+ MSP.V4 F, IsCoordAct β y f →
      ∀ σ : F →+* F, (∀ (c : F) (v : MSP.V4 F), f (c • v) = σ c • f v) →
        ∀ c, σ (σ c) = c := by
    intro y hy hy2 f hf σ hσ c
    have h1 : IsCoordAct β (y * y) (f ∘ f) := hf.mul (hTV hy) hf
    rw [← pow_two, hy2] at h1
    have h2 := IsCoordAct.unique hβ (one_mem _) h1 isCoordAct_one
    have h3 : f (f (c • v₀)) = c • v₀ := congrFun h2 (c • v₀)
    have h4 : f (f v₀) = v₀ := congrFun h2 v₀
    rw [hσ, hσ, h4] at h3
    have h5 : (σ (σ c) - c) • v₀ = 0 := by rw [sub_smul, h3, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv₀)
  have hnontriv : ∀ y ∈ T, y ∉ L ⊔ pCoreOf 2 M → ∀ f : MSP.V4 F →+ MSP.V4 F,
      IsCoordAct β y f → ∀ σ : F →+* F, (∀ (c : F) (v : MSP.V4 F), f (c • v) = σ c • f v) →
        ∃ c, σ c ≠ c := by
    intro y hy hyL f hf σ hσ
    by_contra hall
    push Not at hall
    exact hyL (hlin y hy f hf fun c v => by rw [hσ, hall])
  obtain ⟨f, hf, σ, hσ⟩ := hsemi t ht
  obtain ⟨f', hf', σ', hσ'⟩ := hsemi t' ht'
  have hσσ' := burnsideSp4H_ringHom_eq (hinvol t ht ht2 f hf σ hσ)
    (hinvol t' ht' ht'2 f' hf' σ' hσ')
    (hnontriv t ht htL f hf σ hσ) (hnontriv t' ht' ht'L f' hf' σ' hσ')
  have hσ'2 := hinvol t' ht' ht'2 f' hf' σ' hσ'
  refine hlin (t * t') (T.mul_mem ht ht') (f.comp f') ((hf.mul (hTV ht') hf').congr fun x => rfl)
    fun c v => ?_
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hσ', hσ, hσσ', hσ'2]

theorem burnsideSp4H_mul_mem_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {γ δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδγ : (puAmalgam h.le).treeGraph.Adj δ γ)
    {x y : (puAmalgam h.le).Universal} (hx : x ∈ Qv _ γ) (hy : y ∈ Qv _ γ)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hxF : x ∉ S34F.flat h δ) (hyF : y ∉ S34F.flat h δ) :
    x * y ∈ S34F.flat h δ := by
  obtain ⟨g, hgα, hgβ⟩ := exists_smul_edge_of_isMVtx (puAmalgam h.le) (PU.isMVtx_baseA _)
    (adj_baseA_baseB _) hδ hδγ
  rw [← hgβ, qv_smul] at hx hy
  rw [← hgα, S34F.flat, puTrans_smul h.le (S34F.flat_subgroupOf_normal h)] at hxF hyF ⊢
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [puAmalgam.qv_baseB, imM_of_le h.le le_rfl] at hx' hy'
  obtain ⟨t, -, rfl⟩ := hx'
  obtain ⟨t', -, rfl⟩ := hy'
  have hbase : ∀ s : ↥T, (MulAut.conj g).toMonoidHom (puAmalgam.ofT h.le s) ∈
      (puTrans h.le (L ⊔ pCoreOf 2 M) (baseA _)).map (MulAut.conj g).toMonoidHom ↔
        (s : G) ∈ L ⊔ pCoreOf 2 M := by
    intro s
    rw [Subgroup.mem_map_iff_mem (MulAut.conj g).injective,
      puTrans_baseA h.le (S34F.flat_subgroupOf_normal h), S34E.ofT_mem_imM_iff h]
  have hsq : ∀ s : ↥T, ((MulAut.conj g).toMonoidHom (puAmalgam.ofT h.le s)) ^ 2 = 1 →
      (s : G) ^ 2 = 1 := by
    intro s hs
    rw [← map_pow, ← map_pow] at hs
    have h1 := (MulAut.conj g).injective (hs.trans (map_one _).symm)
    have h2 : puAmalgam.ofT h.le (s ^ 2) = puAmalgam.ofT h.le 1 := by rw [h1, map_one]
    have h3 := congrArg Subtype.val
      (((puAmalgam h.le).ofB_injective.comp SemidirectProduct.inl_injective) h2)
    simpa using h3
  rw [← map_mul, ← map_mul, hbase]
  rw [hbase] at hxF hyF
  exact burnsideSp4H_mul_mem_sup h hU t.2 t'.2 (hsq t hx2) (hsq t' hy2) hxF hyF

end CFSG.Quasithin.MS93.S4L
