module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCModel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMPrimeC_assemble {Bs L : Subgroup G} {x : G} {m : ℕ} {R : Type} [Group R]
    (eL : ↥L ≃* R) (hxBs : x ∈ Bs) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k)
    (τ : ↥(sumZero m 3) →* R) (hτinj : Function.Injective τ)
    (hτrange : τ.range = qTwoLMPrimeC_imgT Bs L eL)
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAutV σ f))
    (hnorm : ∀ g : R, (∀ e ∈ qTwoLMPrimeC_imgT Bs L eL, g * e * g⁻¹ ∈ qTwoLMPrimeC_imgT Bs L eL) →
      ∃ π : Equiv.Perm (Fin m), ∀ f, g * τ f * g⁻¹ = τ (permAutV π f)) :
    ∃ ΘT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L),
      (∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
        ∃ π : Equiv.Perm (Fin m), ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 π v) : ↥(Bs ⊓ L)) : G)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
        (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 σ v) : ↥(Bs ⊓ L)) : G)) := by
  have hEdef : qTwoLMPrimeC_imgT Bs L eL =
      ((Bs ⊓ L).subgroupOf L).map eL.toMonoidHom := rfl
  have hmemb : ∀ f : ↥(sumZero m 3), (eL.symm (τ f) : G) ∈ Bs ⊓ L := by
    intro f
    have hf : τ f ∈ qTwoLMPrimeC_imgT Bs L eL := by
      rw [← hτrange]
      exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
    rw [hEdef] at hf
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hf
    have ha' : (a : G) ∈ Bs ⊓ L := Subgroup.mem_subgroupOf.mp ha
    have hval : (eL.symm (τ f) : G) = (a : G) := by
      have hvalL : eL.symm (τ f) = a := by
        rw [← hae]
        exact eL.symm_apply_apply a
      exact congrArg (fun z : ↥L => (z : G)) hvalL
    rw [hval]
    exact ha'
  let ψfun : ↥(sumZero m 3) → ↥(Bs ⊓ L) :=
    fun f => ⟨(eL.symm (τ f) : G), hmemb f⟩
  have hψ_one : ψfun 1 = 1 := by
    apply Subtype.ext
    simp [ψfun]
  have hψ_mul : ∀ f g, ψfun (f * g) = ψfun f * ψfun g := by
    intro f g
    apply Subtype.ext
    simp only [ψfun, map_mul, Subgroup.coe_mul]
  let ψ : ↥(sumZero m 3) →* ↥(Bs ⊓ L) :=
    { toFun := ψfun, map_one' := hψ_one, map_mul' := hψ_mul }
  have hψinj : Function.Injective ψ := by
    intro f g hfg
    have h2 : (eL.symm (τ f) : G) = (eL.symm (τ g) : G) := by
      have h3 := congrArg (fun z : ↥(Bs ⊓ L) => (z : G)) hfg
      change ((ψ f : ↥(Bs ⊓ L)) : G) = ((ψ g : ↥(Bs ⊓ L)) : G)
      exact h3
    have h1 : eL.symm (τ f) = eL.symm (τ g) := Subtype.ext h2
    apply hτinj
    have h4 := congrArg eL h1
    simpa only [MulEquiv.apply_symm_apply] using h4
  have hψsurj : Function.Surjective ψ := by
    intro t
    have ht : eL ⟨(t : G), t.2.2⟩ ∈ ((Bs ⊓ L).subgroupOf L).map eL.toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨⟨(t : G), t.2.2⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr t.2
    have ht' : eL ⟨(t : G), t.2.2⟩ ∈ qTwoLMPrimeC_imgT Bs L eL := by
      rw [hEdef]
      exact ht
    rw [← hτrange] at ht'
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp ht'
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change (eL.symm (τ f) : G) = (t : G)
    have h3 : eL.symm (τ f) = (⟨(t : G), t.2.2⟩ : ↥L) := by
      rw [hf, MulEquiv.symm_apply_apply]
    rw [h3]
  let ΘT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hΘval : ∀ f, ((ΘT f : ↥(Bs ⊓ L)) : G) = (eL.symm (τ f) : G) := by
    intro f
    rfl
  have hkey : ∀ (σ : Equiv.Perm (Fin m)) (w : R) (n : ↥L), eL n = w →
      (∀ f, w * τ f * w⁻¹ = τ (permAutV σ f)) →
      ∀ f, (n : G) * ((ΘT f : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
        ((ΘT (permAutV σ f) : ↥(Bs ⊓ L)) : G) := by
    intro σ w n hn hw f
    have h1 : ∀ g : ↥(sumZero m 3),
        eL (⟨((ΘT g : ↥(Bs ⊓ L)) : G), (ΘT g).2.2⟩ : ↥L) = τ g := by
      intro g
      have hg : (⟨((ΘT g : ↥(Bs ⊓ L)) : G), (ΘT g).2.2⟩ : ↥L) = eL.symm (τ g) :=
        Subtype.ext (hΘval g)
      rw [hg, MulEquiv.apply_symm_apply]
    have heq : eL (n * (⟨((ΘT f : ↥(Bs ⊓ L)) : G), (ΘT f).2.2⟩ : ↥L) * n⁻¹) =
        eL (⟨((ΘT (permAutV σ f) : ↥(Bs ⊓ L)) : G),
          (ΘT (permAutV σ f)).2.2⟩ : ↥L) := by
      rw [map_mul, map_mul, map_inv, hn, h1 f, hw f, h1 (permAutV σ f)]
    have := congrArg (fun z : ↥L => (z : G)) (eL.injective heq)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  refine ⟨ΘT, ?_, ?_⟩
  · intro n hnBs
    have hgE : ∀ e ∈ qTwoLMPrimeC_imgT Bs L eL,
        (eL n) * e * (eL n)⁻¹ ∈ qTwoLMPrimeC_imgT Bs L eL := by
      intro e he
      rw [hEdef] at he ⊢
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp he
      have ha' : (a : G) ∈ Bs ⊓ L := Subgroup.mem_subgroupOf.mp ha
      have hmemB : ((n * a * n⁻¹ : ↥L) : G) ∈ Bs ⊓ L := by
        change (n : G) * (a : G) * (n : G)⁻¹ ∈ Bs ⊓ L
        exact ⟨(Subgroup.mem_set_normalizer_iff.mp hnBs (a : G)).mp ha'.1,
          L.mul_mem (L.mul_mem n.2 ha'.2) (L.inv_mem n.2)⟩
      refine Subgroup.mem_map.mpr ⟨n * a * n⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hmemB
      · rw [map_mul, map_mul, map_inv, hae]
        simp only [MulEquiv.coe_toMonoidHom]
    obtain ⟨π, hπ⟩ := hnorm (eL n) hgE
    refine ⟨π, ?_⟩
    intro v
    rw [permAutVHom_apply]
    exact hkey π (eL n) n rfl hπ v
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    let n : ↥L := eL.symm w
    have hn : eL n = w := MulEquiv.apply_symm_apply eL w
    have hconj : ∀ f : ↥(sumZero m 3),
        (n : G) * ((ΘT f : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
          ((ΘT (permAutV σ f) : ↥(Bs ⊓ L)) : G) := hkey σ w n hn hw
    have hconj_inv : ∀ f : ↥(sumZero m 3),
        (n : G)⁻¹ * ((ΘT f : ↥(Bs ⊓ L)) : G) * (n : G) =
          ((ΘT (permAutV σ⁻¹ f) : ↥(Bs ⊓ L)) : G) := by
      intro f
      have hcomp : (permAutV σ : MulAut ↥(sumZero m 3))
          ((permAutV σ⁻¹ : MulAut ↥(sumZero m 3)) f) = f := by
        have hmul : (permAutV σ * permAutV σ⁻¹ : MulAut ↥(sumZero m 3)) = 1 := by
          rw [← permAutV_mul, mul_inv_cancel, permAutV_one]
        have h := congrArg (fun φ : MulAut ↥(sumZero m 3) => φ f) hmul
        simpa only [MulAut.mul_apply, MulAut.one_apply] using h
      have hc := hconj (permAutV σ⁻¹ f)
      rw [hcomp] at hc
      calc (n : G)⁻¹ * ((ΘT f : ↥(Bs ⊓ L)) : G) * (n : G)
          = (n : G)⁻¹ * ((n : G) * ((ΘT (permAutV σ⁻¹ f) : ↥(Bs ⊓ L)) : G) *
              (n : G)⁻¹) * (n : G) := by rw [hc]
        _ = ((ΘT (permAutV σ⁻¹ f) : ↥(Bs ⊓ L)) : G) := by group
    have hnT : ∀ t : ↥(Bs ⊓ L), (n : G) * (t : G) * (n : G)⁻¹ ∈ Bs ⊓ L := by
      intro t
      obtain ⟨f, hf⟩ := ΘT.surjective t
      rw [← hf, hconj f]
      exact (ΘT (permAutV σ f)).2
    have hnTinv : ∀ t : ↥(Bs ⊓ L), (n : G)⁻¹ * (t : G) * (n : G) ∈ Bs ⊓ L := by
      intro t
      obtain ⟨f, hf⟩ := ΘT.surjective t
      rw [← hf, hconj_inv f]
      exact (ΘT (permAutV σ⁻¹ f)).2
    have hxcent : (n : G) * x = x * (n : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx n.2)
    have hxn : (n : G) * x * (n : G)⁻¹ = x := by
      rw [hxcent, mul_assoc, mul_inv_cancel, mul_one]
    have hxk : ∀ k : ℕ, (n : G) * x ^ k * (n : G)⁻¹ = x ^ k := by
      intro k
      rw [← conj_pow (i := k) (a := (n : G)) (b := x), hxn]
    have hxk_inv : ∀ k : ℕ, (n : G)⁻¹ * x ^ k * (n : G) = x ^ k := by
      intro k
      calc (n : G)⁻¹ * x ^ k * (n : G)
          = (n : G)⁻¹ * ((n : G) * x ^ k * (n : G)⁻¹) * (n : G) := by rw [hxk k]
        _ = x ^ k := by group
    have hnormn : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro b
      constructor
      · intro hb
        obtain ⟨t, ht, k, hbk⟩ := hsplit b hb
        have h1 : (n : G) * t * (n : G)⁻¹ ∈ Bs := (hnT ⟨t, ht⟩).1
        rw [hbk]
        have hcalc : (n : G) * (t * x ^ k) * (n : G)⁻¹ =
            ((n : G) * t * (n : G)⁻¹) * x ^ k := by
          calc (n : G) * (t * x ^ k) * (n : G)⁻¹
              = ((n : G) * t * (n : G)⁻¹) * ((n : G) * x ^ k * (n : G)⁻¹) := by group
            _ = ((n : G) * t * (n : G)⁻¹) * x ^ k := by rw [hxk k]
        rw [hcalc]
        exact Bs.mul_mem h1 (Bs.pow_mem hxBs k)
      · intro hb
        obtain ⟨t, ht, k, hbk⟩ := hsplit ((n : G) * b * (n : G)⁻¹) hb
        have h1 : (n : G)⁻¹ * t * (n : G) ∈ Bs := (hnTinv ⟨t, ht⟩).1
        have hbt : b = ((n : G)⁻¹ * t * (n : G)) * x ^ k := by
          calc b = (n : G)⁻¹ * ((n : G) * b * (n : G)⁻¹) * (n : G) := by group
            _ = (n : G)⁻¹ * (t * x ^ k) * (n : G) := by rw [hbk]
            _ = ((n : G)⁻¹ * t * (n : G)) * ((n : G)⁻¹ * x ^ k * (n : G)) := by group
            _ = ((n : G)⁻¹ * t * (n : G)) * x ^ k := by rw [hxk_inv k]
        rw [hbt]
        exact Bs.mul_mem h1 (Bs.pow_mem hxBs k)
    refine ⟨n, hnormn, ?_⟩
    intro v
    rw [permAutVHom_apply]
    exact hconj v

end CFSG.StandardType.QTwo

end
