module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

namespace Item2119End4Proof

theorem isCyclic_of_isPGroup_three_SL2 {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) (hS : IsPGroup 3 S) :
    IsCyclic S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpp : p.Prime := Fact.out
  by_cases hp5 : p = 5
  · subst hp5
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
      rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    have hdvd : 3 ^ k ∣ 120 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card S
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := h9.trans hdvd
      norm_num at this
    refine isCyclic_of_card_dvd_prime (p := 3) ?_
    rw [hk]
    interval_cases k <;> norm_num
  · have hp7 : 7 ≤ p := by
      by_contra hlt
      interval_cases p <;> first | exact absurd rfl hp5 | exact absurd hpp (by norm_num)
    set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) with hZ
    set π := QuotientGroup.mk' Z with hπ
    have hinj : Function.Injective (π.comp S.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hs
      obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
      rw [Fintype.card_fin] at hr
      have hsval : (((s : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p))) = Matrix.scalar (Fin 2) r := hrs.symm
      have hs2 : (s : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, hsval, ← map_pow, hr, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      obtain ⟨k, hk⟩ := hS s
      have hs3 : (s : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ^ 3 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hcop : Nat.Coprime (2 : ℕ) (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      have h1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hs2)
        (orderOf_dvd_of_pow_eq_one hs3)
      rw [orderOf_eq_one_iff] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    have hSπ : IsPGroup 3 (S.map π) := hS.map π
    obtain ⟨R, hR⟩ := hSπ.exists_le_sylow
    have hRc : IsCyclic (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) :=
      GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (ZMod p) (p := p) (f := 1)
        (by rw [Nat.card_zmod, pow_one]) (by rw [Nat.card_zmod]; exact hp7) 3 (by norm_num)
        (by rw [Nat.card_zmod]; exact (Nat.coprime_primes Nat.prime_three hpp).mpr (by omega)) R
    have hSc : IsCyclic (S.map π) := Subgroup.isCyclic_of_le hR
    have hrange : (π.comp S.subtype).range = S.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact isCyclic_of_injective ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp
      (MonoidHom.ofInjective hinj).toMonoidHom)
      ((MulEquiv.subgroupCongr hrange).injective.comp (MonoidHom.ofInjective hinj).injective)

theorem exists_mulAut_toGL_aux {p : ℕ} [Fact p.Prime] {H : Type*} [CommGroup H] [Finite H]
    [Module (ZMod p) (Additive H)] (hcard : Nat.card H = p ^ 2) :
    ∃ ρ : MulAut H →* GL (Fin 2) (ZMod p), Function.Injective ρ := by
  have hfin : Module.finrank (ZMod p) (Additive H) = 2 := by
    have h := FiniteField.pow_finrank_eq_natCard p (Additive H)
    have h2 : Nat.card (Additive H) = p ^ 2 := hcard
    rw [h2] at h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  have : Finite (Additive H) := inferInstanceAs (Finite H)
  have : Module.Finite (ZMod p) (Additive H) := Module.Finite.of_finite
  let b : Module.Basis (Fin 2) (ZMod p) (Additive H) :=
    Module.finBasisOfFinrankEq (ZMod p) (Additive H) hfin
  let lin : MulAut H →* (Additive H ≃ₗ[ZMod p] Additive H) :=
    { toFun := fun σ => (MulEquiv.toAdditive σ).toLinearEquiv
        (fun c x => ZMod.map_smul (MulEquiv.toAdditive σ).toAddMonoidHom c x)
      map_one' := by
        ext x
        rfl
      map_mul' := fun σ τ => by
        ext x
        rfl }
  let ρ : MulAut H →* GL (Fin 2) (ZMod p) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
        (Additive H)).symm.toMonoidHom.comp lin)
  refine ⟨ρ, fun σ τ h => ?_⟩
  have h1 : lin σ = lin τ := by
    have h2 := congrArg (fun g => LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
      (Additive H) (Matrix.GeneralLinearGroup.toLin' b g)) h
    simpa [ρ] using h2
  ext x
  have h3 := congrArg (fun f : Additive H ≃ₗ[ZMod p] Additive H => Additive.toMul (f
    (Additive.ofMul x))) h1
  exact h3

theorem exists_mulAut_toGL {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    (hcomm : ∀ x y : H, x * y = y * x) (hexp : ∀ x : H, x ^ p = 1)
    (hcard : Nat.card H = p ^ 2) :
    ∃ ρ : MulAut H →* GL (Fin 2) (ZMod p), Function.Injective ρ :=
  @exists_mulAut_toGL_aux p _ H { (inferInstance : Group H) with mul_comm := hcomm } _
    (@AddCommGroup.zmodModule p (Additive H)
      (@Additive.addCommGroup H { (inferInstance : Group H) with mul_comm := hcomm })
      (fun x => by
        change Additive.ofMul ((Additive.toMul x) ^ p) = 0
        rw [hexp]
        rfl)) hcard

theorem isCyclic_of_le_commutator_GL {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (V : Subgroup (GL (Fin 2) (ZMod p))) (hV3 : IsPGroup 3 V)
    (hV : V ≤ commutator (GL (Fin 2) (ZMod p))) : IsCyclic V := by
  have hdet : V ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker :=
    hV.trans (Abelianization.commutator_subset_ker _)
  set ι := (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)) with hι
  have hιinj : Function.Injective ι := Matrix.SpecialLinearGroup.toGL_injective
  have hrange : ι.range = (Matrix.GeneralLinearGroup.det :
      GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker := Matrix.SpecialLinearGroup.range_toGL_eq_ker_det
  set V' := V.comap ι with hV'
  have hmap : V'.map ι = V := by
    rw [hV', Subgroup.map_comap_eq, hrange, inf_of_le_right hdet]
  have hV'3 : IsPGroup 3 V' := by
    have e : V' ≃* V'.map ι := V'.equivMapOfInjective ι hιinj
    rw [hmap] at e
    exact hV3.of_equiv e.symm
  have hV'c := isCyclic_of_isPGroup_three_SL2 hp3 V' hV'3
  have e : V' ≃* V'.map ι := V'.equivMapOfInjective ι hιinj
  rw [hmap] at e
  exact isCyclic_of_injective e.symm.toMonoidHom e.symm.injective

theorem isCyclic_of_le_commutator_starOf {G : Type} [Group G] [Finite G] {A P W₀ : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hP : IsElemAbelian p P) (hP2 : Nat.card P = p ^ 2)
    (hWA : W₀ ≤ Subgroup.normalizer (A : Set G)) (hWP : W₀ ≤ Subgroup.normalizer (P : Set G))
    (hWC : W₀ ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G))
    (T : Subgroup (MulAut A)) (hT3 : IsPGroup 3 T)
    (hT : T ≤ ⁅starOf A W₀, starOf A W₀⁆) : IsCyclic T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ₀ : W₀ →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hWA) with hφ₀
  set ψ₀ : W₀ →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hWP) with hψ₀
  have hstar : starOf A W₀ = φ₀.range := by
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hWA x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  rw [hstar, ← map_commutator_eq] at hT
  have hker : ψ₀.ker ≤ φ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxP : (x : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : G)) hx
      have h2 : (x : G) * y * (x : G)⁻¹ = y := h1
      calc y * x = (x : G) * y * (x : G)⁻¹ * x := by rw [h2]
        _ = x * y := by group
    have hxA := hWC ⟨x.2, hxP⟩
    ext a
    have hax : (a : G) * x = x * a := (Subgroup.mem_centralizer_iff.mp hxA) a a.2
    change (x : G) * a * (x : G)⁻¹ = a
    rw [← hax]
    group
  set K := commutator W₀ ⊓ T.comap φ₀ with hK
  set f : K →* T := (φ₀.comp K.subtype).codRestrict T (fun k => k.2.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk, hkt⟩ := hT ht
    exact ⟨⟨k, hk, show φ₀ k ∈ T by rw [hkt]; exact ht⟩, Subtype.ext hkt⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hST : (S : Subgroup K).map f = ⊤ := by
    have h := ((S.mapSurjective hfs).is_maximal' (hT3.to_subgroup ⊤) le_top).symm
    rwa [Sylow.coe_mapSurjective] at h
  obtain ⟨ρ, hρ⟩ := exists_mulAut_toGL (H := P) (p := p)
    (fun x y => hP.1.is_comm.comm x y) (fun x => Subtype.ext (by simpa using hP.2 x x.2)) hP2
  set g : S →* GL (Fin 2) (ZMod p) := ρ.comp (ψ₀.comp (K.subtype.comp (S : Subgroup K).subtype))
    with hg
  have hgcomm : g.range ≤ commutator (GL (Fin 2) (ZMod p)) := by
    rintro _ ⟨s, rfl⟩
    have hs : ((s : K) : W₀) ∈ commutator W₀ := (s : K).2.1
    have h1 : ψ₀ ((s : K) : W₀) ∈ commutator (MulAut P) := by
      have := Subgroup.mem_map_of_mem ψ₀ hs
      rw [map_commutator_eq] at this
      exact Subgroup.commutator_mono le_top le_top this
    have h2 := Subgroup.mem_map_of_mem ρ h1
    rw [map_commutator_eq] at h2
    exact Subgroup.commutator_mono le_top le_top h2
  have hg3 : IsPGroup 3 g.range := by
    rw [MonoidHom.range_eq_map]
    exact (S.isPGroup'.to_subgroup ⊤).map g
  have hgc := isCyclic_of_le_commutator_GL hp3 g.range hg3 hgcomm
  have hgker : g.ker ≤ (f.comp (S : Subgroup K).subtype).ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : ψ₀ ((s : K) : W₀) = 1 := hρ (by rw [map_one]; exact hs)
    have h2 := hker (MonoidHom.mem_ker.mpr h1)
    apply Subtype.ext
    exact h2
  have hcS : IsCyclic (S ⧸ g.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange g).toMonoidHom
      (QuotientGroup.quotientKerEquivRange g).injective
  set lift := QuotientGroup.lift g.ker (f.comp (S : Subgroup K).subtype) hgker with hlift
  have hlifts : Function.Surjective lift := by
    intro t
    have ht : t ∈ (S : Subgroup K).map f := by rw [hST]; exact Subgroup.mem_top t
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨((⟨s, hs⟩ : S) : S ⧸ g.ker), rfl⟩
  exact isCyclic_of_surjective lift hlifts

end Item2119End4Proof

end CFSG.RankThree.PartTwo.Sec21
