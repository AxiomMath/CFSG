module

public import CFSG.Quasithin.Background.G10FifteenNondegF
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.G10FifteenIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def restrictOnR' (H : Subgroup (GLV V)) (I I' : Submodule (ZMod 2) V)
    (hI : Invariant H I) :
    ↥(centralizerOn H I') →* ↥(restrictRange H I hI) :=
  (restrictHom H I hI).rangeRestrict.comp (Subgroup.inclusion (fun _ hr => hr.1))

theorem restrictOnR'_injective {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hc : IsCompl I I') :
    Function.Injective (restrictOnR' H I I' hI) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1 : ∀ u ∈ I, (t : GLV V) u = u := by
    intro u hu
    have := congrArg (fun e : ↥(restrictRange H I hI) =>
      (((e : GLV ↥I) ⟨u, hu⟩ : ↥I) : V)) ht
    exact this
  apply Subtype.ext
  exact eq_one_of_centralizes_compl hc h1 t.2.2

theorem restrictOnR'_surjective {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
    (hI : Invariant H I)
    (hsplit : ∀ h ∈ H, ∃ r ∈ centralizerOn H I, ∃ r' ∈ centralizerOn H I', h = r * r') :
    Function.Surjective (restrictOnR' H I I' hI) := by
  rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩⟩
  obtain ⟨r, hr, r', hr', rfl⟩ := hsplit h hh
  refine ⟨⟨r', hr'⟩, ?_⟩
  apply Subtype.ext
  have h1 : restrictHom H I hI ⟨r, hr.1⟩ = 1 := by
    rw [restrictHom_eq_one_iff]
    exact hr.2
  show restrictHom H I hI ⟨r', hr'.1⟩ = restrictHom H I hI ⟨r * r', hh⟩
  have : (⟨r * r', hh⟩ : ↥H) = ⟨r, hr.1⟩ * ⟨r', hr'.1⟩ := rfl
  rw [this, map_mul, h1, one_mul]

@[expose] noncomputable def R'Equiv {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hc : IsCompl I I')
    (hsplit : ∀ h ∈ H, ∃ r ∈ centralizerOn H I, ∃ r' ∈ centralizerOn H I', h = r * r') :
    ↥(centralizerOn H I') ≃* ↥(restrictRange H I hI) :=
  MulEquiv.ofBijective (restrictOnR' H I I' hI)
    ⟨restrictOnR'_injective hI hc, restrictOnR'_surjective hI hsplit⟩

theorem map_conj_centralizerOn {H : Subgroup (GLV V)} {x : GLV V} (hx2 : x * x = 1)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) {U : Submodule (ZMod 2) V} :
    (centralizerOn H (conjSub x U)).map (MulAut.conj x).toMonoidHom = centralizerOn H U := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
  have hconj : ∀ g : GLV V, x * (x * g * x⁻¹) * x⁻¹ = g := fun g => by
    calc x * (x * g * x⁻¹) * x⁻¹ = (x * x) * g * (x⁻¹ * x⁻¹) := by group
      _ = g := by rw [hx2, hxx']; simp
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := centralizerOn_conj hxH (U := conjSub x U) t ht
    rwa [conjSub_conjSub_of_sq hx2] at this
  · intro hg
    have h1 := centralizerOn_conj hxH (U := U) g hg
    refine ⟨x * g * x⁻¹, h1, ?_⟩
    show x * (x * g * x⁻¹) * x⁻¹ = g
    exact hconj g

theorem commSpace_centralizerOn_conj {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
    (hI : IsIrr H I) (hI' : Invariant H I') (hc : IsCompl I I')
    (hne : ∃ r ∈ centralizerOn H I', r ≠ 1) :
    commSpace (centralizerOn H I') ⊤ = I := by
  have hle : commSpace (centralizerOn H I') ⊤ ≤ I := by
    rw [commSpace, Submodule.span_le]
    rintro _ ⟨r, hr, v, -, rfl⟩
    have hv : v ∈ I ⊔ I' := by
      rw [codisjoint_iff.1 hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have h1 : r (a + b) - (a + b) = r a - a := by
      rw [map_add, hr.2 b hb]
      abel
    show r (a + b) - (a + b) ∈ I
    rw [h1]
    exact I.sub_mem (hI.1 r hr.1 a ha) ha
  have hinv : Invariant H (commSpace (centralizerOn H I') ⊤) :=
    invariant_commSpace (fun k' hk' k hk => centralizerOn_normal hI' k' hk' k hk) (invariant_top _)
  rcases hI.eq_bot_or_eq hinv hle with h0 | h1
  · exfalso
    obtain ⟨r, hr, hr1⟩ := hne
    apply hr1
    ext v
    have hmem : r v - v ∈ commSpace (centralizerOn H I') ⊤ :=
      sub_mem_commSpace hr Submodule.mem_top
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  · exact h1

theorem fixedSpace_centralizerOn_conj {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
    (hI : IsIrr H I) (hI' : Invariant H I') (hc : IsCompl I I')
    (hne : ∃ r ∈ centralizerOn H I', r ≠ 1)
    (hnoI : ∀ r ∈ centralizerOn H I', (∀ u ∈ I, r u = u) → r = 1) :
    fixedSpace (centralizerOn H I') = I' := by
  have hn : ∀ γ ∈ H, ∀ r ∈ centralizerOn H I', γ * r * γ⁻¹ ∈ centralizerOn H I' :=
    fun γ hγ r hr => centralizerOn_normal hI' γ hγ r hr
  refine le_antisymm ?_ ?_
  · intro v hv
    have hv' : v ∈ I ⊔ I' := by
      rw [codisjoint_iff.1 hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv'
    have hCinv : Invariant H (fixedSpace (centralizerOn H I') ⊓ I) :=
      (invariant_fixedSpace hn).inf hI.1
    have haC : a ∈ fixedSpace (centralizerOn H I') ⊓ I := by
      refine ⟨fun r hr => ?_, ha⟩
      have h1 := hv r hr
      rw [map_add, hr.2 b hb] at h1
      exact add_right_cancel h1
    rcases hI.eq_bot_or_eq hCinv inf_le_right with h0 | h1
    · rw [h0, Submodule.mem_bot] at haC
      rw [haC, zero_add]
      exact hb
    · exfalso
      obtain ⟨r, hr, hr1⟩ := hne
      apply hr1
      refine hnoI r hr fun u hu => ?_
      have : u ∈ fixedSpace (centralizerOn H I') ⊓ I := by rw [h1]; exact hu
      exact this.1 r hr
  · intro u hu r hr
    exact hr.2 u hu

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem component_eq_of_le_simple {R' : Subgroup (GLV V)} (hR'Γ : R' ≤ Γ)
    (hsimp : IsSimpleGroup ↥R') (hL : L ≤ R') : L = R' := by
  have hsub : IsSubnormal (R' ⊓ L) R' :=
    CFSG.Quasithin.B113.isSubnormal_inf_of_le hyp.component.2.1 hR'Γ
  rw [inf_eq_right.2 hL] at hsub
  have hN : (L.subgroupOf R').IsSubnormal := CFSG.Quasithin.B113.subgroupOf_isSubnormal hsub
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hN with h | h
  · exfalso
    obtain ⟨l, hl, hl1⟩ := hyp.exists_ne_one_mem_L
    have : (⟨l, hL hl⟩ : ↥R') ∈ L.subgroupOf R' := hl
    rw [h, Subgroup.mem_bot] at this
    exact hl1 (congrArg Subtype.val this)
  · refine le_antisymm hL fun r hr => ?_
    have : (⟨r, hr⟩ : ↥R') ∈ L.subgroupOf R' := by rw [h]; trivial
    exact this

theorem III_of_nondeg (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hSQT : SectionSQTInput)
    (h1212 : G1212Stmt) (hSimple : InspectSimple) (hOuter : InspectOuter)
    (hSylow : InspectSylow) (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hnd : NondegOn B I)
    (hL : L ≤ centralizerOn (normalClosure Γ L) (conjSub x I)) :
    ¬ Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧ NondegOn B I ∧
      ¬ FaithfulOn (normalClosure Γ L) I ∧ Module.finrank (ZMod 2) V = 8 ∧
      ∃ x ∈ X, conjSub x I ≠ I ∧
        normalClosure Γ L = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
        Nat.card X = 8 ∧ X = (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x ∧
        I = commSpace L ⊤ ∧ IsA5Module L I ∧ conjSub x I = fixedSpace L := by
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hI' : IrrPlus (normalClosure Γ L) (conjSub x I) := hyp.irrPlus_conj hI hx
  have hinv' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hn : ¬ HIso (normalClosure Γ L) I (conjSub x I) := fun h => hne (hfix x hx h)
  have hc := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
  obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
  have hFT := hyp.fullTransvections hI hfix hx hne hi hv
  have horth := hyp.conj_le_orthogonal h10 h11 h12 hI hfix hx hne hnd
  have hnle := hyp.not_le_perp_of_nondeg hi.1 hi0 hv hnd horth
  obtain ⟨hsplit, h4, hY4, hXH, φ, ψ, hφψ⟩ := hyp.split_structure hq hSQT h1212 hSimple hOuter
    hSylow h10 h11 h12 hI hfix hx hne hc hi hi0 hFT hnd hnle
  obtain ⟨f, hD, hsimpK, hqK⟩ := hyp.nondeg_data hq hSQT h1212 hSimple hI hi hi0 hFT hnd hnle
  have hsimpR' : IsSimpleGroup ↥(centralizerOn (normalClosure Γ L) (conjSub x I)) :=
    (R'Equiv hI.1 hc hsplit).isSimpleGroup
  have hLeq : L = centralizerOn (normalClosure Γ L) (conjSub x I) :=
    hyp.component_eq_of_le_simple (fun r hr => hyp.H_le hr.1) hsimpR' hL
  obtain ⟨l₀, hl₀L, hl₀1⟩ := hyp.exists_ne_one_mem_L
  have hLne : ∃ r ∈ centralizerOn (normalClosure Γ L) (conjSub x I), r ≠ 1 :=
    ⟨l₀, hL hl₀L, hl₀1⟩
  have hnoI : ∀ r ∈ centralizerOn (normalClosure Γ L) (conjSub x I), (∀ u ∈ I, r u = u) →
      r = 1 := fun r hr hu => eq_one_of_centralizes_compl hc hu hr.2
  have hmapL : L.map (MulAut.conj x).toMonoidHom = centralizerOn (normalClosure Γ L) I := by
    have h1 := map_conj_centralizerOn hx2 hxH (U := I)
    refine le_antisymm ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      exact h1.le ⟨l, hL hl, rfl⟩
    · intro r hr
      rw [← h1] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      exact ⟨t, hLeq.symm.le ht, rfl⟩
  refine ⟨fun h => hn (h I (conjSub x I) hI hI'), selfDual_of_nondegOn hyp.toG101Hyp.isRefl
    hyp.H_isometry hnd, hnd, ?_, ?_, x, hx, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hf
    have hr : x * l₀ * x⁻¹ ∈ centralizerOn (normalClosure Γ L) I := by
      have := hmapL.le ⟨l₀, hl₀L, rfl⟩
      exact this
    have h1 : x * l₀ * x⁻¹ = 1 := faithfulOn_iff.1 hf _ hr.1 hr.2
    apply hl₀1
    calc l₀ = x⁻¹ * (x * l₀ * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  ·
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_conjSub] at h1
    omega
  ·
    rw [hmapL]
    refine le_antisymm (fun h hh => ?_) (sup_le (le_normalClosure Γ L) (fun r hr => hr.1))
    obtain ⟨r, hr, r', hr', rfl⟩ := hsplit h hh
    have hcomm := hyp.centralizers_comm hI.1 hx hc hr hr'
    rw [hcomm]
    exact Subgroup.mul_mem_sup (hLeq.symm.le hr') hr
  ·
    have hYX : stabilizerOf X I ≤ X := fun y hy => hy.1
    have hmul := Subgroup.relIndex_mul_card (stabilizerOf X I) X
    rw [inf_eq_left.2 hYX, hyp.relIndex_stabilizerOf_eq_two hI hfix hx hne, hY4] at hmul
    omega
  ·
    rw [hXH]
    refine le_antisymm (fun g hg => ?_) (sup_le (fun y hy => hy.1)
      ((Subgroup.zpowers_le).2 hx))
    rcases hyp.permutes hI hfix hx hne g hg with h1 | h1
    · exact Subgroup.mem_sup_left ⟨hg, h1⟩
    · have hy : x⁻¹ * g ∈ stabilizerOf X I := by
        refine ⟨X.mul_mem (X.inv_mem hx) hg, ?_⟩
        rw [conjSub_mul, h1, conjSub_inv_conjSub]
      have : g = x * (x⁻¹ * g) := by group
      rw [this, sup_comm]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) hy
  ·
    rw [hLeq]
    exact (commSpace_centralizerOn_conj hirr hinv' hc hLne).symm
  ·
    refine ⟨(MulEquiv.subgroupCongr hLeq).trans ((R'Equiv hI.1 hc hsplit).trans φ), ψ, ?_⟩
    intro γ v w hw
    exact hφψ _ v w (Subtype.ext hw)
  ·
    rw [hLeq]
    exact (fixedSpace_centralizerOn_conj hirr hinv' hc hLne hnoI).symm

end G108Hyp

end G11

end CFSG.Quasithin
