module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Core
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Main
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNc

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

theorem nk_s9main_final (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {G : Type} [Group G] [Finite G] {Λ W₀ W₁ Lu H T V K : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (SW : SectionModule Λ W₀ W₁ W)
    (hcfg : TransvConfig (SW.img Lu) (SW.img (conjClosure V H)) (SW.img T) (SW.img V)
      (SW.sub (V ⊓ W₁)))
    (hKne : SW.img K ≠ ⊥)
    (hLuΛ : Lu ≤ Λ) (hKΛ : K ≤ Λ) (hVΛ : V ≤ Λ) (hTΛ : T ≤ Λ)
    (hKG : K ≤ conjClosure V H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hVT : V ≤ T)
    {v : G} (hv : v ∈ V) (hvgen : K ≤ Subgroup.closure {x | ∃ k ∈ K, x = k * v * k⁻¹})
    {τ : G} (hτ : τ ∈ T)
    {Ks : Type} [Group Ks] (hs : IsSimpleGroup Ks) (hna : ∃ a b : Ks, a * b ≠ b * a)
    (hKs3 : IsPSL 3 2 1 Ks)
    (ψ : ↥K →* Ks) (hψ : Function.Surjective ψ) (J : Subgroup G)
    (hJ : ∀ z : ↥K, ψ z = 1 ↔ (z : G) ∈ J)
    (hker : ∀ N : Subgroup ↥K, N.Normal → N ≠ ⊤ → N ≤ ψ.ker)
    (hout : ∀ k ∈ K, ∃ x ∈ K, τ * x * τ⁻¹ * (k * x * k⁻¹)⁻¹ ∉ K ⊓ J)
    (hKperf : commutator ↥K = ⊤)
    (hQ : ∃ Q : Subgroup G, Q ≤ K ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q, ∀ x ∈ K, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, v * q * v⁻¹ ∈ Q) ∧
      (∃ k₀ ∈ K, ∀ x ∈ K, ∃ q ∈ Q, v * x * v⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z ∈ K, z ∈ J → ∀ x ∈ K, ∃ q ∈ Q, z * x * z⁻¹ = q * x)) : False := by
  classical
  let eK : ↥(K.subgroupOf Λ) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKΛ
  let ρK : ↥(K.subgroupOf Λ) →* ↥(SW.img K) :=
    MonoidHom.codRestrict (SW.ρ.comp (K.subgroupOf Λ).subtype) (SW.img K)
      (fun x => (SW.mem_img).mpr ⟨x.1, Subgroup.mem_subgroupOf.mp x.2, rfl⟩)
  have hρK : Function.Surjective ρK := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mpr hy⟩, rfl⟩
  let ψΛ : ↥(K.subgroupOf Λ) →* Ks := ψ.comp eK.toMonoidHom
  have hψΛ : Function.Surjective ψΛ := hψ.comp eK.surjective
  have hkerρ : ρK.ker ≤ ψΛ.ker := by
    intro x hx
    haveI : (ρK.ker.map eK.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ eK.surjective
    have hne : ρK.ker.map eK.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hKne
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
      have hmem : eK ⟨y, Subgroup.mem_subgroupOf.mpr hy⟩ ∈ ρK.ker.map eK.toMonoidHom := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨z, hz, hez⟩ := Subgroup.mem_map.mp hmem
      have hz' : z = ⟨y, Subgroup.mem_subgroupOf.mpr hy⟩ := eK.injective hez
      rw [hz'] at hz
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hz))
    have hmem : eK x ∈ ρK.ker.map eK.toMonoidHom := Subgroup.mem_map_of_mem eK.toMonoidHom hx
    have h1 := hker _ inferInstance hne hmem
    exact h1
  let σ : ↥(SW.img K) →* Ks :=
    (QuotientGroup.lift ρK.ker ψΛ hkerρ).comp
      (QuotientGroup.quotientKerEquivOfSurjective ρK hρK).symm.toMonoidHom
  have hσρ : ∀ x : ↥(K.subgroupOf Λ), σ (ρK x) = ψΛ x := by
    intro x
    have h2 : (QuotientGroup.quotientKerEquivOfSurjective ρK hρK).symm (ρK x) =
        (x : ↥(K.subgroupOf Λ) ⧸ ρK.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ρK.ker ψΛ hkerρ
        ((QuotientGroup.quotientKerEquivOfSurjective ρK hρK).symm (ρK x)) = ψΛ x
    rw [h2]
    rfl
  have hσsurj : Function.Surjective σ := by
    intro g
    obtain ⟨x, hx⟩ := hψΛ g
    exact ⟨ρK x, by rw [hσρ]; exact hx⟩
  have hkerσ : ∀ M' : Subgroup ↥(SW.img K), M'.Normal → M' ≠ ⊤ → M' ≤ σ.ker := by
    intro M' hM' hne' m hm
    rw [MonoidHom.mem_ker]
    obtain ⟨x, rfl⟩ := hρK m
    rw [hσρ]
    have hN' : (M'.comap ρK).Normal := Subgroup.Normal.comap hM' ρK
    have hneN : M'.comap ρK ≠ ⊤ := by
      intro htop
      apply hne'
      rw [eq_top_iff]
      intro g _
      obtain ⟨z, rfl⟩ := hρK g
      have hz : z ∈ M'.comap ρK := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hz
    haveI : ((M'.comap ρK).map eK.toMonoidHom).Normal :=
      Subgroup.Normal.map hN' _ eK.surjective
    have hneM : (M'.comap ρK).map eK.toMonoidHom ≠ ⊤ := by
      intro htop2
      apply hneN
      rw [eq_top_iff]
      intro z _
      have hz : eK z ∈ (M'.comap ρK).map eK.toMonoidHom := by
        rw [htop2]
        exact Subgroup.mem_top _
      obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hz
      have : w = z := eK.injective hwe
      rw [← this]
      exact hw
    have h1 := hker _ inferInstance hneM (Subgroup.mem_map_of_mem eK.toMonoidHom hm)
    exact h1
  have hS : ∀ x ∈ {x : G | ∃ k ∈ K, x = k * v * k⁻¹}, x ∈ Λ := by
    rintro x ⟨k, hk, rfl⟩
    exact Λ.mul_mem (Λ.mul_mem (hKΛ hk) (hVΛ hv)) (Λ.inv_mem (hKΛ hk))
  let vW : W ≃ₗ[ZMod 2] W := SW.ρ ⟨v, hVΛ hv⟩
  have hvW : vW ∈ SW.img V := (SW.mem_img).mpr ⟨⟨v, hVΛ hv⟩, hv, rfl⟩
  let τW : W ≃ₗ[ZMod 2] W := SW.ρ ⟨τ, hTΛ hτ⟩
  have hτW : τW ∈ SW.img T := (SW.mem_img).mpr ⟨⟨τ, hTΛ hτ⟩, hτ, rfl⟩
  have hτKmem : ∀ z ∈ K, τ * z * τ⁻¹ ∈ K := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTK hτ) z).mp hz
  have hvKmem : ∀ z ∈ K, v * z * v⁻¹ ∈ K := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTK (hVT hv)) z).mp hz
  have hconj : ∀ (g : G) (hg : g ∈ Λ), (∀ z ∈ K, g * z * g⁻¹ ∈ K) →
      ∀ g' ∈ SW.img K, SW.ρ ⟨g, hg⟩ * g' * (SW.ρ ⟨g, hg⟩)⁻¹ ∈ SW.img K := by
    intro g hg hgK g' hg'
    obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg'
    refine (SW.mem_img).mpr ⟨⟨g * (y : G) * g⁻¹,
      Λ.mul_mem (Λ.mul_mem hg y.2) (Λ.inv_mem hg)⟩, hgK _ hy, ?_⟩
    rw [show (⟨g * (y : G) * g⁻¹, Λ.mul_mem (Λ.mul_mem hg y.2) (Λ.inv_mem hg)⟩ : ↥Λ) =
      ⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
  have hvK : ∀ g ∈ SW.img K, vW * g * vW⁻¹ ∈ SW.img K :=
    hconj v (hVΛ hv) hvKmem
  have hτK : ∀ g ∈ SW.img K, τW * g * τW⁻¹ ∈ SW.img K :=
    hconj τ (hTΛ hτ) hτKmem
  have hK₀v : SW.img K ≤ Subgroup.closure {x | ∃ k ∈ SW.img K, x = k * vW * k⁻¹} := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
    obtain ⟨hyΛ, hmem⟩ := s9main_closure_image SW.ρ _ hS (y : G) (hvgen hy)
    have hsub : {m : W ≃ₗ[ZMod 2] W | ∃ x ∈ {x : G | ∃ k ∈ K, x = k * v * k⁻¹},
        ∃ hx : x ∈ Λ, m = SW.ρ ⟨x, hx⟩} ⊆
        {x | ∃ k ∈ SW.img K, x = k * vW * k⁻¹} := by
      rintro m ⟨x, ⟨k, hk, rfl⟩, hx, rfl⟩
      refine ⟨SW.ρ ⟨k, hKΛ hk⟩, (SW.mem_img).mpr ⟨⟨k, hKΛ hk⟩, hk, rfl⟩, ?_⟩
      rw [show (⟨k * v * k⁻¹, hx⟩ : ↥Λ) = ⟨k, hKΛ hk⟩ * ⟨v, hVΛ hv⟩ * ⟨k, hKΛ hk⟩⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    exact Subgroup.closure_mono hsub hmem
  have hv1 : vW ≠ 1 := by
    intro h1
    apply hKne
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
    obtain ⟨hyΛ, hmem⟩ := s9main_closure_image SW.ρ _ hS (y : G) (hvgen hy)
    have hbot : Subgroup.closure {m : W ≃ₗ[ZMod 2] W | ∃ x ∈ {x : G | ∃ k ∈ K, x = k * v * k⁻¹},
        ∃ hx : x ∈ Λ, m = SW.ρ ⟨x, hx⟩} ≤ ⊥ := by
      rw [Subgroup.closure_le]
      rintro m ⟨x, ⟨k, hk, rfl⟩, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      rw [show (⟨k * v * k⁻¹, hx⟩ : ↥Λ) = ⟨k, hKΛ hk⟩ * ⟨v, hVΛ hv⟩ * ⟨k, hKΛ hk⟩⁻¹ from rfl,
        map_mul, map_mul, map_inv]
      have h1' : SW.ρ ⟨v, hVΛ hv⟩ = 1 := h1
      rw [h1']
      simp
    exact Subgroup.mem_bot.mpr (hbot hmem)
  have hout' : ∀ g : ↥(SW.img K), ∃ x : ↥(SW.img K), ∃ z : ↥(SW.img K),
      (z : W ≃ₗ[ZMod 2] W) = τW * x * τW⁻¹ ∧ σ z ≠ σ (g * x * g⁻¹) := by
    rintro ⟨g, hg⟩
    obtain ⟨yy, hy, rfl⟩ := (SW.mem_img).mp hg
    obtain ⟨x, hxK, hx⟩ := hout (yy : G) hy
    have hxΛ : x ∈ Λ := hKΛ hxK
    have hτxK : τ * x * τ⁻¹ ∈ K := hτKmem x hxK
    let xΛ : ↥(K.subgroupOf Λ) := ⟨⟨x, hxΛ⟩, Subgroup.mem_subgroupOf.mpr hxK⟩
    let zΛ : ↥(K.subgroupOf Λ) := ⟨⟨τ * x * τ⁻¹, Λ.mul_mem (Λ.mul_mem (hTΛ hτ) hxΛ)
      (Λ.inv_mem (hTΛ hτ))⟩, Subgroup.mem_subgroupOf.mpr hτxK⟩
    let yΛ : ↥(K.subgroupOf Λ) := ⟨⟨(yy : G), yy.2⟩, Subgroup.mem_subgroupOf.mpr hy⟩
    refine ⟨ρK xΛ, ρK zΛ, ?_, ?_⟩
    · have e1 : (⟨τ * x * τ⁻¹, Λ.mul_mem (Λ.mul_mem (hTΛ hτ) hxΛ)
          (Λ.inv_mem (hTΛ hτ))⟩ : ↥Λ) = ⟨τ, hTΛ hτ⟩ * ⟨x, hxΛ⟩ * ⟨τ, hTΛ hτ⟩⁻¹ := rfl
      show SW.ρ ⟨τ * x * τ⁻¹, _⟩ = τW * SW.ρ ⟨x, hxΛ⟩ * τW⁻¹
      rw [e1, map_mul, map_mul, map_inv]
    · have hgyy : (⟨SW.ρ yy, (SW.mem_img).mpr ⟨yy, hy, rfl⟩⟩ : ↥(SW.img K)) = ρK yΛ := rfl
      rw [hgyy]
      have e2 : ρK yΛ * ρK xΛ * (ρK yΛ)⁻¹ = ρK (yΛ * xΛ * yΛ⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e2, hσρ, hσρ]
      intro heq
      set z' : ↥K := eK (zΛ * (yΛ * xΛ * yΛ⁻¹)⁻¹) with hz'
      have hψz' : ψ z' = 1 := by
        have : ψΛ (zΛ * (yΛ * xΛ * yΛ⁻¹)⁻¹) = 1 := by
          rw [map_mul, map_inv, heq, mul_inv_cancel]
        exact this
      have hJz : (z' : G) ∈ J := (hJ z').mp hψz'
      apply hx
      have e3 : (z' : G) = τ * x * τ⁻¹ * ((yy : G) * x * (yy : G)⁻¹)⁻¹ := by
        simp [hz', zΛ, yΛ, xΛ, eK, mul_assoc]
      rw [← e3]
      exact Subgroup.mem_inf.mpr ⟨z'.2, hJz⟩
  have hK₀G : SW.img K ≤ SW.img (conjClosure V H) := SW.img_mono hKG
  have hK₀perf : commutator ↥(SW.img K) = ⊤ := by
    have hf : Function.Surjective (ρK.comp eK.symm.toMonoidHom) :=
      hρK.comp eK.symm.surjective
    have key : (commutator ↥K).map (ρK.comp eK.symm.toMonoidHom) = commutator ↥(SW.img K) := by
      rw [commutator_def K, commutator_def (SW.img K), Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hf]
    rw [← key, hKperf]
    exact Subgroup.map_top_of_surjective _ hf
  have hQW : ∃ Q₀ : Subgroup (W ≃ₗ[ZMod 2] W), Q₀ ≤ SW.img K ∧
      (∀ q ∈ Q₀, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧ (∀ q ∈ Q₀, ∀ x ∈ SW.img K, x * q * x⁻¹ ∈ Q₀) ∧
      (∀ q ∈ Q₀, vW * q * vW⁻¹ ∈ Q₀) ∧
      (∃ k₀ ∈ SW.img K, ∀ x ∈ SW.img K, ∃ q ∈ Q₀, vW * x * vW⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥(SW.img K), σ z = 1 → ∀ x ∈ SW.img K, ∃ q ∈ Q₀,
        (z : W ≃ₗ[ZMod 2] W) * x * (z : W ≃ₗ[ZMod 2] W)⁻¹ = q * x) := by
    obtain ⟨Q, hQK, hQ2, hQKn, hQv, ⟨k₀, hk₀, hvin⟩, hcen⟩ := hQ
    refine ⟨SW.img Q, SW.img_mono hQK, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
      obtain ⟨m, hm⟩ := hQ2 (y : G) hy
      refine ⟨m, ?_⟩
      have : y ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
      rw [← map_pow, this, map_one]
    · intro g hg x hx
      obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
      obtain ⟨z, hz, rfl⟩ := (SW.mem_img).mp hx
      refine (SW.mem_img).mpr ⟨z * y * z⁻¹, ?_, by simp [map_mul, map_inv]⟩
      have := hQKn (y : G) hy (z : G) hz
      simpa using this
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
      refine (SW.mem_img).mpr ⟨⟨v, hVΛ hv⟩ * y * ⟨v, hVΛ hv⟩⁻¹, ?_, by simp [map_mul, map_inv, vW]⟩
      have := hQv (y : G) hy
      simpa using this
    · refine ⟨SW.ρ ⟨k₀, hKΛ hk₀⟩, (SW.mem_img).mpr ⟨⟨k₀, hKΛ hk₀⟩, hk₀, rfl⟩, ?_⟩
      intro x hx
      obtain ⟨z, hz, rfl⟩ := (SW.mem_img).mp hx
      obtain ⟨q, hq, hqe⟩ := hvin (z : G) hz
      have hqΛ : q ∈ Λ := hKΛ (hQK hq)
      refine ⟨SW.ρ ⟨q, hqΛ⟩, (SW.mem_img).mpr ⟨⟨q, hqΛ⟩, hq, rfl⟩, ?_⟩
      have e : (⟨v, hVΛ hv⟩ : ↥Λ) * z * ⟨v, hVΛ hv⟩⁻¹ =
          ⟨q, hqΛ⟩ * (⟨k₀, hKΛ hk₀⟩ * z * ⟨k₀, hKΛ hk₀⟩⁻¹) := Subtype.ext (by simpa using hqe)
      have := congrArg SW.ρ e
      simpa [map_mul, map_inv, vW] using this
    · intro z hz x hx
      obtain ⟨z₀, rfl⟩ := hρK z
      obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hx
      rw [hσρ] at hz
      have hψz : ψ (eK z₀) = 1 := hz
      have hzJ : ((eK z₀ : ↥K) : G) ∈ J := (hJ _).mp hψz
      obtain ⟨q, hq, hqe⟩ := hcen (eK z₀ : ↥K) (eK z₀).2 hzJ (y : G) hy
      have hqΛ : q ∈ Λ := hKΛ (hQK hq)
      refine ⟨SW.ρ ⟨q, hqΛ⟩, (SW.mem_img).mpr ⟨⟨q, hqΛ⟩, hq, rfl⟩, ?_⟩
      have e : (z₀ : ↥Λ) * y * (z₀ : ↥Λ)⁻¹ = ⟨q, hqΛ⟩ * y := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hqe
      have := congrArg SW.ρ e
      have hρ : ((ρK z₀ : ↥(SW.img K)) : W ≃ₗ[ZMod 2] W) = SW.ρ (z₀ : ↥Λ) := rfl
      rw [hρ]
      simpa [map_mul, map_inv] using this
  exact nk_s9_mod_core hSch hSL3 hConj hcfg hK₀G vW hvW hv1 hK₀v hvK τW hτW hτK hs hna hKs3 σ
    hσsurj hkerσ hout' hK₀perf hQW



end CFSG.Quasithin.H13.L829NK
