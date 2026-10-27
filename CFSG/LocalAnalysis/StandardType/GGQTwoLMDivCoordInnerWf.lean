module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerQuot
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

private theorem qTwoLMDivCoordInner_wf_conj_mem {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (n : ↥L)
    (hnBs : (n : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hw
    have hnb : (n : G) * (b : G) * (n : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hnBs b).mp b.2
    refine MonoidHom.mem_range.mpr ⟨⟨(n : G) * (b : G) * (n : G)⁻¹, hnb⟩, ?_⟩
    rw [← hb]
    exact ggGamma_conj L hN n b hnb
  · intro hw
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hw
    have hnb : ((n⁻¹ : ↥L) : G) * (b : G) * (((n⁻¹ : ↥L) : G))⁻¹ ∈ Bs := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnBs) b).mp b.2
    refine MonoidHom.mem_range.mpr
      ⟨⟨((n⁻¹ : ↥L) : G) * (b : G) * (((n⁻¹ : ↥L) : G))⁻¹, hnb⟩, ?_⟩
    rw [ggGamma_conj L hN n⁻¹ b hnb,
      show MulAut.conj (n⁻¹ : ↥L) = (MulAut.conj n)⁻¹ from
        map_inv (MulAut.conj : ↥L →* MulAut ↥L) n]
    rw [hb]
    group

private theorem qTwoLMDivCoordInner_wf_conjAut_eq {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (h3 : 3 ∣ m)
    (τ : ↥(sumZero m 3) →* ↥L) (hmem : ∀ f, ((τ f : ↥L) : G) ∈ Bs)
    (θ : QTwoHm m h3 ≃* ↥(ggGamma L hN).range)
    (hθ : ∀ f, ((θ (QuotientGroup.mk f) : ↥(ggGamma L hN).range) : MulAut ↥L) =
      ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩)
    (ρ : Equiv.Perm (Fin m) →* MulAut (QTwoHm m h3))
    (hρ : ∀ σ f, ρ σ (QuotientGroup.mk f) = QuotientGroup.mk (permAutV σ f))
    (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)))
    (π : Equiv.Perm (Fin m))
    (hπ : ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV π f) : ↥L) : G)) :
    ggConjAut (ggGamma L hN).range hn = MulAut.congr θ (ρ π) := by
  have hconj : ∀ f, MulAut.conj n * ((θ (QuotientGroup.mk f) : ↥(ggGamma L hN).range) :
        MulAut ↥L) * (MulAut.conj n)⁻¹ =
      ((θ (QuotientGroup.mk (permAutV π f)) : ↥(ggGamma L hN).range) : MulAut ↥L) := by
    intro f
    rw [hθ f, hθ (permAutV π f)]
    have hnb : (n : G) * (⟨((τ f : ↥L) : G), hmem f⟩ : ↥Bs) * (n : G)⁻¹ ∈ Bs := by
      change (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ ∈ Bs
      rw [hπ f]
      exact hmem (permAutV π f)
    rw [← ggGamma_conj L hN n ⟨((τ f : ↥L) : G), hmem f⟩ hnb]
    exact congrArg (ggGamma L hN) (Subtype.ext (hπ f))
  apply MulEquiv.ext
  intro a
  obtain ⟨v, rfl⟩ := θ.surjective a
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers (qTwoOneVec m h3)) v
  rw [← hf, QuotientGroup.mk'_apply]
  apply Subtype.ext
  rw [ggConjAut_apply, hconj f, MulAut.congr_apply]
  simp [hρ]

theorem qTwoLMDivCoordInner_wtheta {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (h3 : 3 ∣ m)
    (τ : ↥(sumZero m 3) →* ↥L) (hmem : ∀ f, ((τ f : ↥L) : G) ∈ Bs)
    (hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t)
    (hsplit : ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k)
    (hker : ∀ f, ((τ f : ↥L) : G) ∈ Subgroup.zpowers x ↔ f ∈ Subgroup.zpowers (qTwoOneVec m h3)) :
    ∃ θ : QTwoHm m h3 ≃* ↥(ggGamma L hN).range, ∀ f,
      ((θ (QuotientGroup.mk f) : ↥(ggGamma L hN).range) : MulAut ↥L) =
        ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩ := by
  let ψ : ↥(sumZero m 3) →* ↥Bs :=
    { toFun := fun f => ⟨((τ f : ↥L) : G), hmem f⟩
      map_one' := Subtype.ext (by simpa using congrArg Subtype.val (map_one τ))
      map_mul' := fun f g => Subtype.ext (by
        show ((τ (f * g) : ↥L) : G) = ((τ f : ↥L) : G) * ((τ g : ↥L) : G)
        rw [map_mul, Subgroup.coe_mul]) }
  let φ : ↥(sumZero m 3) →* ↥(ggGamma L hN).range :=
    (MonoidHom.rangeRestrict (ggGamma L hN)).comp ψ
  have hφ_apply : ∀ f, ((φ f : ↥(ggGamma L hN).range) : MulAut ↥L) =
      ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩ := fun f => rfl
  have hφ_one_iff : ∀ f, φ f = 1 ↔ ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩ = 1 := by
    intro f
    constructor
    · intro h
      simpa [hφ_apply f] using
        congrArg (fun y : ↥(ggGamma L hN).range => (y : MulAut ↥L)) h
    · intro h
      exact Subtype.ext (by simpa [hφ_apply f] using h)
  have hxBs : x ∈ Bs := by
    have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [qTwoLMPrimeC_ker hG hBs]
      exact Subgroup.mem_zpowers x
    exact hx.1
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [qTwoLMPrimeC_ker hG hBs]
      exact Subgroup.mem_zpowers x
    exact hx.2
  have hxgam : ggGamma L hN ⟨x, hxBs⟩ = 1 := (ggGamma_eq_one_iff L hN _).mpr hxcent
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp w.2
    obtain ⟨t, htBs, k, hbk⟩ := hsplit b b.2
    obtain ⟨f, hf⟩ := hrange t htBs
    have hb_eq : b = ⟨((τ f : ↥L) : G), hmem f⟩ * ⟨x, hxBs⟩ ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [hbk, hf]
    have hgam : ggGamma L hN b = ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩ := by
      rw [hb_eq, map_mul, map_pow, hxgam, one_pow, mul_one]
    refine ⟨f, Subtype.ext ?_⟩
    rw [hφ_apply f, ← hb]
    exact hgam.symm
  have hmember : ∀ f, φ f = 1 ↔ ((τ f : ↥L) : G) ∈ Subgroup.zpowers x := by
    intro f
    rw [hφ_one_iff f, ggGamma_eq_one_iff L hN ⟨((τ f : ↥L) : G), hmem f⟩]
    constructor
    · intro hc
      have h2 : ((τ f : ↥L) : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hmem f, hc⟩
      rwa [qTwoLMPrimeC_ker hG hBs] at h2
    · intro hx
      have h2 : ((τ f : ↥L) : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [qTwoLMPrimeC_ker hG hBs]
        exact hx
      exact h2.2
  have hker_eq : φ.ker = Subgroup.zpowers (qTwoOneVec m h3) := by
    ext f
    rw [MonoidHom.mem_ker]
    exact (hmember f).trans (hker f)
  obtain ⟨θ, hθ⟩ := qTwoLMDivCoordInner_quot h3 φ hsurj hker_eq
  exact ⟨θ, fun f => by rw [hθ f, hφ_apply f]⟩

theorem qTwoLMDivCoordInner_wfields {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (h3 : 3 ∣ m)
    (τ : ↥(sumZero m 3) →* ↥L) (hmem : ∀ f, ((τ f : ↥L) : G) ∈ Bs)
    (θ : QTwoHm m h3 ≃* ↥(ggGamma L hN).range)
    (hθ : ∀ f, ((θ (QuotientGroup.mk f) : ↥(ggGamma L hN).range) : MulAut ↥L) =
      ggGamma L hN ⟨((τ f : ↥L) : G), hmem f⟩)
    (ρ : Equiv.Perm (Fin m) →* MulAut (QTwoHm m h3))
    (hρ : ∀ σ f, ρ σ (QuotientGroup.mk f) = QuotientGroup.mk (permAutV σ f))
    (hwn : ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      (n : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hcl1 : ∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ π' : Equiv.Perm (Fin m), ∀ f,
        (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV π' f) : ↥L) : G))
    (hcl2 : ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV σ f) : ↥L) : G)) :
    (∀ (n : ↥L) (hn : MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
      ∃ π' : Equiv.Perm (Fin m), ggConjAut (ggGamma L hN).range hn = MulAut.congr θ (ρ π')) ∧
    ∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
      ggConjAut (ggGamma L hN).range hn = MulAut.congr θ (ρ σ) := by
  constructor
  · intro n hn
    obtain ⟨π', hπ'⟩ := hcl1 n (hwn n hn)
    exact ⟨π', qTwoLMDivCoordInner_wf_conjAut_eq hN h3 τ hmem θ hθ ρ hρ n hn π' hπ'⟩
  · intro σ
    obtain ⟨n, hnBs, hnτ⟩ := hcl2 σ
    have hn : MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) :=
      qTwoLMDivCoordInner_wf_conj_mem hN n hnBs
    exact ⟨n, hn, qTwoLMDivCoordInner_wf_conjAut_eq hN h3 τ hmem θ hθ ρ hρ n hn σ hnτ⟩

end CFSG.StandardType.QTwo

end
