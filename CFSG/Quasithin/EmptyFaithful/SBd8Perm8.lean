module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.SBd8Abs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section Perm8

theorem center_alt8_eq_bot : Subgroup.center ↥(alternatingGroup (Fin 8)) = ⊥ := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    CFSG.QuasithinUnique.Bridge.alt_isSimple (by norm_num)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Bridge.alt_exists_noncomm (m := 8) (by norm_num)
    have : a ∈ Subgroup.center ↥(alternatingGroup (Fin 8)) := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

variable {Γ : Type} [Group Γ] [Finite Γ] {X J S₀ K : Subgroup Γ}

theorem conjAct_injective_of_pCore_eq_bot (d : Insp28Data X J S₀ K) (hZ : Subgroup.center ↥X = ⊥) :
    Function.Injective ((conjAct X).comp (Subgroup.inclusion d.J_norm)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  set ρ : ↥J →* MulAut ↥X := (conjAct X).comp (Subgroup.inclusion d.J_norm) with hρ
  have hXJ : X ≤ J := d.J_eq ▸ le_sup_left
  have hS₀J : S₀ ≤ J := d.syl.1
  set C : Subgroup ↥J := ρ.ker with hC
  set C' : Subgroup Γ := C.map J.subtype with hC'
  have hC'J : C' ≤ J := by rintro _ ⟨c, -, rfl⟩; exact c.2
  have hnorm : J ≤ Subgroup.normalizer (C' : Set Γ) := by
    intro g hg
    have h1 : Subgroup.normalizer (C : Set ↥J) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.2 inferInstance
    have h2 := Subgroup.le_normalizer_map (H := C) J.subtype
    rw [h1] at h2
    exact h2 ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩
  have hp : IsPGroup 2 ↥C' := by
    intro c
    obtain ⟨c₀, hc₀, hcc₀⟩ := c.2
    have hXJ' : (X.subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).2 d.J_norm
    have hjoin : X.subgroupOf J ⊔ S₀.subgroupOf J = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hXJ hS₀J, ← d.J_eq, Subgroup.subgroupOf_self]
    have hSp : IsPGroup 2 ↥(S₀.subgroupOf J) :=
      d.syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀J).symm
    have hc₀top : c₀ ∈ X.subgroupOf J ⊔ S₀.subgroupOf J := by
      rw [hjoin]; exact Subgroup.mem_top c₀
    obtain ⟨nh, hnh, sh, hsh, hc₀eq⟩ := mem_sup_of_le_normalizer (N := X.subgroupOf J)
      (H := S₀.subgroupOf J)
      (fun g _ => Subgroup.normalizer_eq_top_iff.2 hXJ' ▸ Subgroup.mem_top g) hc₀top
    obtain ⟨a, ha⟩ := hSp ⟨sh, hsh⟩
    have hsha : sh ^ 2 ^ a = 1 := congrArg Subtype.val ha
    obtain ⟨n', hn', hpow⟩ := pow_mul_mem_of_normal (N := X.subgroupOf J) (s := sh) hnh (2 ^ a)
    rw [← hc₀eq, hsha, mul_one] at hpow
    have hρ1 : ρ (c₀ ^ 2 ^ a) = 1 := by rw [map_pow, hc₀]; exact one_pow _
    rw [hpow] at hρ1
    have hn'X : (n' : Γ) ∈ X := hn'
    have hcent : (⟨(n' : Γ), hn'X⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun f : MulAut ↥X => ((f x : ↥X) : Γ)) hρ1
      simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
      have h2 : ((conjAct X (Subgroup.inclusion d.J_norm n') x : ↥X) : Γ) =
          (n' : Γ) * x * (n' : Γ)⁻¹ := conj_coe_apply X _ x
      rw [h2] at h1
      apply Subtype.ext
      show (x : Γ) * n' = n' * x
      have : (x : Γ) * n' = ((n' : Γ) * x * (n' : Γ)⁻¹) * n' := by rw [h1]
      rw [this]; group
    rw [hZ, Subgroup.mem_bot] at hcent
    have hn'1 : n' = 1 := Subtype.ext (by simpa using congrArg Subtype.val hcent)
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have h3 : c₀ ^ 2 ^ a = 1 := by rw [hpow, hn'1]
    have h4 : ((c : Γ)) = (c₀ : Γ) := hcc₀.symm
    show ((c : Γ)) ^ 2 ^ a = 1
    rw [h4, ← Subgroup.coe_pow, h3]
    rfl
  have hle : C' ≤ pCoreOf 2 J := le_pCoreOf_of_le_normalizer 2 hC'J hnorm hp
  rw [d.red] at hle
  intro j hj
  have hjC : (j : Γ) ∈ C' := ⟨j, hj, rfl⟩
  have := hle hjC
  rw [Subgroup.mem_bot] at this ⊢
  exact Subtype.ext this

open CFSG.GroupTheory.AutAlternating in
theorem nonempty_perm8_of_alt8 (d : Insp28Data X J S₀ K) (h8 : IsAlt 8 ↥X) {α : MulAut ↥X}
    (hα : α ∈ autOn S₀ X) (hnon : ∀ x : ↥X, α ≠ MulAut.conj x) :
    Nonempty (↥J ≃* Equiv.Perm (Fin 8)) := by
  obtain ⟨e⟩ := h8
  have hXJ : X ≤ J := d.J_eq ▸ le_sup_left
  have hS₀J : S₀ ≤ J := d.syl.1
  set ρ : ↥J →* MulAut ↥X := (conjAct X).comp (Subgroup.inclusion d.J_norm) with hρ
  have hZ : Subgroup.center ↥X = ⊥ := by
    apply Subgroup.map_injective (f := (e : ↥X →* ↥(alternatingGroup (Fin 8)))) e.injective
    rw [Subgroup.map_center_eq e, center_alt8_eq_bot, Subgroup.map_bot]
  have hρinj : Function.Injective ρ := conjAct_injective_of_pCore_eq_bot d hZ
  have hb := aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num)
  set c : Equiv.Perm (Fin 8) →* MulAut ↥(alternatingGroup (Fin 8)) := MulAut.conjNormal with hc
  set ψ : ↥J →* MulAut ↥(alternatingGroup (Fin 8)) := (MulAut.congr e).toMonoidHom.comp ρ with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective.comp hρinj
  have hρconj : ∀ x : ↥X, ρ ⟨(x : Γ), hXJ x.2⟩ = MulAut.conj x := by
    intro x
    ext y
    have h1 : ((ρ ⟨(x : Γ), hXJ x.2⟩ y : ↥X) : Γ) = (x : Γ) * y * (x : Γ)⁻¹ :=
      conj_coe_apply X _ y
    rw [h1]
    simp [MulAut.conj_apply]
  have hcongr : ∀ x : ↥X, MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hcconj : ∀ (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ alternatingGroup (Fin 8)),
      c σ = MulAut.conj (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 8))) := by
    intro σ hσ
    ext y
    rw [hc, MulAut.conjNormal_apply]
    simp [MulAut.conj_apply]
  have hψsurj : Function.Surjective ψ := by
    intro β
    obtain ⟨π, rfl⟩ := hb.2 β
    set R : Subgroup (Equiv.Perm (Fin 8)) := ψ.range.comap c with hR
    have hA8R : alternatingGroup (Fin 8) ≤ R := by
      intro σ hσ
      refine ⟨⟨((e.symm ⟨σ, hσ⟩ : ↥X) : Γ), hXJ (e.symm ⟨σ, hσ⟩).2⟩, ?_⟩
      show MulAut.congr e (ρ _) = c σ
      rw [hρconj, hcongr, hcconj σ hσ]
      simp
    obtain ⟨s, hs, hsS, hsα⟩ := mem_autOn_iff_exists.1 hα
    obtain ⟨π₀, hπ₀⟩ := hb.2 (MulAut.congr e α)
    have hπ₀R : π₀ ∈ R := by
      refine ⟨⟨s, hS₀J hsS⟩, ?_⟩
      show MulAut.congr e (ρ _) = c π₀
      rw [hπ₀]
      congr 1
    have hπ₀A : π₀ ∉ alternatingGroup (Fin 8) := by
      intro hπ
      apply hnon (e.symm ⟨π₀, hπ⟩)
      apply (MulAut.congr e).injective
      rw [hcongr, hπ₀.symm.trans (hcconj π₀ hπ)]
      simp
    have hRtop : R = ⊤ := by
      have h1 : R.index ∣ (alternatingGroup (Fin 8)).index := Subgroup.index_dvd_of_le hA8R
      rw [alternatingGroup.index_eq_two] at h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact Subgroup.index_eq_one.1 h
      · exfalso
        have hc1 := Subgroup.card_mul_index R
        have hc2 := Subgroup.card_mul_index (alternatingGroup (Fin 8))
        rw [h] at hc1
        rw [alternatingGroup.index_eq_two] at hc2
        have hRA : R = alternatingGroup (Fin 8) :=
          (Subgroup.eq_of_le_of_card_ge hA8R (by omega)).symm
        exact hπ₀A (hRA ▸ hπ₀R)
    have : π ∈ R := by rw [hRtop]; exact Subgroup.mem_top π
    exact this
  exact ⟨(MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (MulEquiv.ofBijective c hb).symm⟩

end Perm8

end SBd8

end CFSG.Quasithin
