module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSection
public import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped MatrixGroups

section SumSec

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def secLift (W₁ W₂ : Submodule (ZMod 2) V) (U : Submodule (ZMod 2) (SecMod W₁ W₂)) :
    Submodule (ZMod 2) V :=
  (U.comap (Submodule.mkQ (W₂.comap W₁.subtype))).map W₁.subtype

theorem mem_secLift {W₁ W₂ : Submodule (ZMod 2) V} {U : Submodule (ZMod 2) (SecMod W₁ W₂)}
    {v : V} :
    v ∈ secLift W₁ W₂ U ↔
      ∃ h : v ∈ W₁, (Submodule.Quotient.mk (⟨v, h⟩ : ↥W₁) : SecMod W₁ W₂) ∈ U := by
  rw [secLift, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [Submodule.mem_comap, Submodule.mkQ_apply] at hx
    simpa using hx
  · rintro ⟨h, hh⟩
    exact ⟨⟨v, h⟩, by rwa [Submodule.mem_comap, Submodule.mkQ_apply], rfl⟩

theorem secLift_le (W₁ W₂ : Submodule (ZMod 2) V) (U : Submodule (ZMod 2) (SecMod W₁ W₂)) :
    secLift W₁ W₂ U ≤ W₁ := by
  simpa [secLift] using
    Submodule.map_subtype_le W₁ (U.comap (Submodule.mkQ (W₂.comap W₁.subtype)))

theorem le_secLift {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁)
    (U : Submodule (ZMod 2) (SecMod W₁ W₂)) : W₂ ≤ secLift W₁ W₂ U := by
  intro v hv
  rw [mem_secLift]
  refine ⟨hW hv, ?_⟩
  have h0 : (Submodule.Quotient.mk (⟨v, hW hv⟩ : ↥W₁) : SecMod W₁ W₂) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hv
  rw [h0]
  exact Submodule.zero_mem U

theorem secLift_invariant (ρ : G →* LGL 2 V) {W₁ W₂ : Submodule (ZMod 2) V}
    (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂)
    {U : Submodule (ZMod 2) (SecMod W₁ W₂)}
    (hU : ∀ g : G, ∀ u ∈ U, sectionRep ρ W₁ W₂ h₁ h₂ g u ∈ U) :
    ∀ g : G, ∀ v ∈ secLift W₁ W₂ U, ρ g v ∈ secLift W₁ W₂ U := by
  intro g v hv
  obtain ⟨hv₁, hvU⟩ := mem_secLift.mp hv
  rw [mem_secLift]
  refine ⟨h₁ g v hv₁, ?_⟩
  have hmem := hU g (Submodule.Quotient.mk (⟨v, hv₁⟩ : ↥W₁)) hvU
  rwa [sectionRep_mk] at hmem

private theorem b12_TwelveSumSec_mk_mem_iff (W₁ W₂ : Submodule (ZMod 2) V)
    (U : Submodule (ZMod 2) (SecMod W₁ W₂)) (x : ↥W₁) :
    (Submodule.Quotient.mk x : SecMod W₁ W₂) ∈ U ↔ (x : V) ∈ secLift W₁ W₂ U := by
  rw [mem_secLift]
  constructor
  · intro hx
    exact ⟨x.2, by simpa using hx⟩
  · rintro ⟨h, hh⟩
    simpa using hh

private theorem b12_TwelveSumSec_secLift_injective (W₁ W₂ : Submodule (ZMod 2) V) :
    Function.Injective (secLift W₁ W₂) := by
  intro U U' h
  ext u
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) u
  rw [b12_TwelveSumSec_mk_mem_iff, b12_TwelveSumSec_mk_mem_iff, h]

private theorem b12_TwelveSumSec_secLift_mono (W₁ W₂ : Submodule (ZMod 2) V)
    (U U' : Submodule (ZMod 2) (SecMod W₁ W₂)) (h : U ≤ U') :
    secLift W₁ W₂ U ≤ secLift W₁ W₂ U' := by
  intro v hv
  obtain ⟨hv₁, hvU⟩ := mem_secLift.mp hv
  exact mem_secLift.mpr ⟨hv₁, h hvU⟩

private theorem b12_TwelveSumSec_secLift_bot {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁) :
    secLift W₁ W₂ ⊥ = W₂ := by
  ext v
  rw [mem_secLift]
  constructor
  · rintro ⟨h, hh⟩
    rw [Submodule.mem_bot] at hh
    have h2 := (Submodule.Quotient.mk_eq_zero (W₂.comap W₁.subtype)).mp hh
    rwa [Submodule.mem_comap, Submodule.subtype_apply] at h2
  · intro hv
    exact ⟨hW hv, by
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply]
      exact hv⟩

private theorem b12_TwelveSumSec_secLift_top (W₁ W₂ : Submodule (ZMod 2) V) :
    secLift W₁ W₂ ⊤ = W₁ := by
  ext v
  rw [mem_secLift]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro hv
    exact ⟨hv, Submodule.mem_top⟩

private theorem b12_TwelveSumSec_secLift_inf (W₁ W₂ : Submodule (ZMod 2) V)
    (U U' : Submodule (ZMod 2) (SecMod W₁ W₂)) :
    secLift W₁ W₂ (U ⊓ U') = secLift W₁ W₂ U ⊓ secLift W₁ W₂ U' := by
  ext v
  rw [mem_secLift, Submodule.mem_inf, mem_secLift, mem_secLift]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh.1⟩, ⟨h, hh.2⟩⟩
  · rintro ⟨⟨h, hh⟩, ⟨h', hh'⟩⟩
    refine ⟨h, Submodule.mem_inf.mpr ⟨hh, ?_⟩⟩
    simpa using hh'

private theorem b12_TwelveSumSec_secLift_sup {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁)
    (U U' : Submodule (ZMod 2) (SecMod W₁ W₂)) :
    secLift W₁ W₂ (U ⊔ U') = secLift W₁ W₂ U ⊔ secLift W₁ W₂ U' := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hv₁, hvU⟩ := mem_secLift.mp hv
    obtain ⟨u, huU, u', hu'U', huusum⟩ := Submodule.mem_sup.mp hvU
    obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) u
    obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) u'
    have hsum : (Submodule.Quotient.mk (x₁ + x₂) : SecMod W₁ W₂) =
        Submodule.Quotient.mk (⟨v, hv₁⟩ : ↥W₁) := by
      rw [Submodule.Quotient.mk_add (W₂.comap W₁.subtype), huusum]
    have hw : v - ((x₁ : V) + (x₂ : V)) ∈ W₂ := by
      have h2 : (⟨v, hv₁⟩ : ↥W₁) - (x₁ + x₂) ∈ W₂.comap W₁.subtype :=
        (Submodule.Quotient.eq (W₂.comap W₁.subtype)).mp hsum.symm
      simpa [Submodule.mem_comap, Submodule.subtype_apply] using h2
    have hx₁ : (x₁ : V) ∈ secLift W₁ W₂ U :=
      (b12_TwelveSumSec_mk_mem_iff W₁ W₂ U x₁).mp huU
    have hx₂ : (x₂ : V) ∈ secLift W₁ W₂ U' :=
      (b12_TwelveSumSec_mk_mem_iff W₁ W₂ U' x₂).mp hu'U'
    have hw' : v - ((x₁ : V) + (x₂ : V)) ∈ secLift W₁ W₂ U := le_secLift hW U hw
    have hv_eq : v = (v - ((x₁ : V) + (x₂ : V)) + (x₁ : V)) + (x₂ : V) := by abel
    rw [hv_eq]
    exact Submodule.add_mem_sup ((secLift W₁ W₂ U).add_mem hw' hx₁) hx₂
  · exact sup_le (b12_TwelveSumSec_secLift_mono W₁ W₂ U (U ⊔ U') le_sup_left)
      (b12_TwelveSumSec_secLift_mono W₁ W₂ U' (U ⊔ U') le_sup_right)

private theorem b12_TwelveSumSec_secLift_finset_sup {W₁ W₂ : Submodule (ZMod 2) V}
    (hW : W₂ ≤ W₁) (s : Finset (Submodule (ZMod 2) (SecMod W₁ W₂))) :
    secLift W₁ W₂ (s.sup id) = (s.image (secLift W₁ W₂)).sup id ⊔ W₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.image_empty, Finset.sup_empty,
        b12_TwelveSumSec_secLift_bot hW, bot_sup_eq]
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.image_insert, Finset.sup_insert,
        b12_TwelveSumSec_secLift_sup hW, ih, sup_assoc]
      rfl

theorem isSumNatSection_of_family (ρ : G →* LGL 2 V) (N : Subgroup G) {n : ℕ}
    {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) (s : Finset (Submodule (ZMod 2) (SecMod W₁ W₂)))
    (hsup : s.sup id = ⊤) (hind : ∀ U ∈ s, U ⊓ (s.erase U).sup id = ⊥)
    (hnat : ∀ U ∈ s, IsNatSection ρ N (secLift W₁ W₂ U) W₂ n) :
    IsSumNatSection ρ N W₁ W₂ n := by
  classical
  refine ⟨s.image (secLift W₁ W₂), ?_, ?_, ?_⟩
  · intro U' hU'
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hU'
    exact ⟨le_secLift hW U, secLift_le W₁ W₂ U, hnat U hU⟩
  · rw [← b12_TwelveSumSec_secLift_finset_sup hW s, hsup,
      b12_TwelveSumSec_secLift_top W₁ W₂]
  · intro U' hU'
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hU'
    rw [← Finset.image_erase (f := secLift W₁ W₂)
        (b12_TwelveSumSec_secLift_injective W₁ W₂) s U,
      ← b12_TwelveSumSec_secLift_finset_sup hW (s.erase U),
      ← b12_TwelveSumSec_secLift_inf W₁ W₂ U ((s.erase U).sup id),
      hind U hU, b12_TwelveSumSec_secLift_bot hW]

theorem isNatSL2Section_secLift (ρ : G →* LGL 2 V) (N : Subgroup G) {n : ℕ}
    {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) {U : Submodule (ZMod 2) (SecMod W₁ W₂)}
    (hnat : IsNatSL2Section (sectionRep ρ W₁ W₂ h₁ h₂) N U ⊥ n) :
    IsNatSL2Section ρ N (secLift W₁ W₂ U) W₂ n := by
  obtain ⟨-, hUinv, -, K, hK, hKfin, φ, ψ, hcard, hφs, hker, hψs, hψ0, hψeq⟩ := hnat
  have hmem : ∀ v : ↥(secLift W₁ W₂ U),
      (Submodule.Quotient.mk (⟨(v : V), secLift_le W₁ W₂ U v.2⟩ : ↥W₁) :
        SecMod W₁ W₂) ∈ U := by
    intro v
    obtain ⟨h, hh⟩ := mem_secLift.mp v.2
    have heq : (⟨(v : V), h⟩ : ↥W₁) = ⟨(v : V), secLift_le W₁ W₂ U v.2⟩ := Subtype.ext rfl
    rwa [heq] at hh
  let f : ↥(secLift W₁ W₂ U) →+ ↥U :=
    { toFun := fun v =>
        ⟨Submodule.Quotient.mk (⟨(v : V), secLift_le W₁ W₂ U v.2⟩ : ↥W₁), hmem v⟩
      map_zero' := by
        apply Subtype.ext
        simpa using Submodule.Quotient.mk_zero (W₂.comap W₁.subtype)
      map_add' := fun a b => by
        apply Subtype.ext
        conv_rhs => rw [Submodule.coe_add]
        rw [← Submodule.Quotient.mk_add (W₂.comap W₁.subtype)]
        congr 1 }
  refine ⟨le_secLift hW U, secLift_invariant ρ h₁ h₂ hUinv, h₂, K, hK, hKfin, φ, ψ.comp f,
    hcard, hφs, hker, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hψs y
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) (u : SecMod W₁ W₂)
    have hxmem : (x : V) ∈ secLift W₁ W₂ U := by
      rw [mem_secLift]
      refine ⟨x.2, ?_⟩
      rw [show (⟨(x : V), x.2⟩ : ↥W₁) = x from Subtype.ext rfl, hx]
      exact u.2
    refine ⟨⟨(x : V), hxmem⟩, ?_⟩
    have hfeq : f ⟨(x : V), hxmem⟩ = u := by
      apply Subtype.ext
      show (Submodule.Quotient.mk (⟨(x : V), secLift_le W₁ W₂ U hxmem⟩ : ↥W₁) :
        SecMod W₁ W₂) = (u : SecMod W₁ W₂)
      rw [← hx]
    rw [AddMonoidHom.comp_apply, hfeq, hu]
  · intro v
    rw [AddMonoidHom.comp_apply, hψ0 (f v), Submodule.mem_bot]
    show (Submodule.Quotient.mk (⟨(v : V), secLift_le W₁ W₂ U v.2⟩ : ↥W₁) :
      SecMod W₁ W₂) = 0 ↔ (v : V) ∈ W₂
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  · intro g w hw
    have key := hψeq g (f w) (hUinv g (f w) (f w).2)
    rw [AddMonoidHom.comp_apply]
    simpa [f, sectionRep_mk] using key

theorem isSumNatSection_of_fpf_psl (hNat : NatSumL2Input) [Finite G] {n : ℕ}
    (hG : CFSG.Quasithin.IsPSL 2 2 n G) (ρ : G →* LGL 2 V) {W₁ W₂ : Submodule (ZMod 2) V}
    (hW : W₂ ≤ W₁) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂)
    {x : G} (hx : orderOf x = 3) (hfpf : fixMod W₂ (ρ x) ⊓ W₁ ≤ W₂) :
    IsSumNatSection ρ ⊥ W₁ W₂ n := by
  have hPSL : CFSG.Quasithin.IsPSL 2 2 n G := hG
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := hG
  have hn1 : 1 ≤ n := hadm.2.1
  have hn : 1 < n := by
    by_contra hlt
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact hadm.2.2.2.1 (by simp)
  haveI : Finite (SecMod W₁ W₂) :=
    Finite.of_surjective (Submodule.mkQ (W₂.comap W₁.subtype))
      (Submodule.mkQ_surjective (W₂.comap W₁.subtype))
  let τ := sectionRep ρ W₁ W₂ h₁ h₂
  have hD : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hx]
  have hfix : ∀ w : SecMod W₁ W₂,
      (∀ d ∈ Subgroup.zpowers x, τ d w = w) → w = 0 := by
    intro w hw
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) w
    have hτ : sectionRep ρ W₁ W₂ h₁ h₂ x
        (Submodule.Quotient.mk (⟨(y : V), y.2⟩ : ↥W₁)) =
        Submodule.Quotient.mk (⟨(y : V), y.2⟩ : ↥W₁) :=
      hw x (Subgroup.mem_zpowers x)
    rw [sectionRep_mk] at hτ
    have hy : ρ x (y : V) - (y : V) ∈ W₂ := by
      have h2 : (⟨ρ x (y : V), h₁ x (y : V) y.2⟩ : ↥W₁) -
          (⟨(y : V), y.2⟩ : ↥W₁) ∈ W₂.comap W₁.subtype :=
        (Submodule.Quotient.eq (W₂.comap W₁.subtype)).mp hτ
      simpa [Submodule.mem_comap, Submodule.subtype_apply] using h2
    have hyW₂ : (y : V) ∈ W₂ := hfpf ⟨(mem_fixMod).mpr hy, y.2⟩
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hyW₂
  obtain ⟨s, hinv, hsup, hind, hs⟩ :=
    hNat n hn G hPSL (SecMod W₁ W₂) τ ⟨Subgroup.zpowers x, hD, hfix⟩
  refine isSumNatSection_of_family ρ ⊥ hW h₁ h₂ s hsup hind ?_
  intro U hU
  have hnatU : IsNatSL2Section (sectionRep ρ W₁ W₂ h₁ h₂) ⊥ U ⊥ n := by
    obtain ⟨K', hK', hKfin', φ, ψ, hcard', hψeq⟩ := hs U hU
    refine ⟨bot_le, hinv U hU, ?_, K', hK', hKfin', φ.toMonoidHom, ψ.toAddMonoidHom,
      hcard', φ.surjective, ?_, ψ.surjective, ?_, ?_⟩
    · intro g w hw
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]
    · ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      exact map_eq_one_iff φ φ.injective
    · intro w
      rw [Submodule.mem_bot]
      constructor
      · intro h
        exact Subtype.ext_iff.mp ((map_eq_zero_iff ψ ψ.injective).mp h)
      · intro h
        exact (map_eq_zero_iff ψ ψ.injective).mpr (Subtype.ext_iff.mpr h)
    · exact hψeq
  exact Or.inl (isNatSL2Section_secLift ρ ⊥ hW h₁ h₂ (U := U) hnatU)

end SumSec

end CFSG.LocalAnalysis.WeakClosure81
