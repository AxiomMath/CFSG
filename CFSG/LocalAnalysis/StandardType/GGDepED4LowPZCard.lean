module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nPC_conjEnd_gensV {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (gensV : Set (V ≃ₗ[ZMod 3] V))
    (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) :
    l05nDA_conjEnd (p := 3) (N := 7) θ '' gensV = gens := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hg₁ g hg
    rw [l05nDA_conjEnd_apply, l05nDA_conj_coe]
    have : θ.toLinearMap ∘ₗ (g : V →ₗ[ZMod 3] V) ∘ₗ θ.symm.toLinearMap = y := by
      rw [hyeq]; apply LinearMap.ext; intro w; simp [LinearMap.comp_apply]
    rw [this]
    exact hy
  · intro hy
    obtain ⟨g, hg, hgeq⟩ := hg₂ y hy
    refine ⟨g, hg, ?_⟩
    rw [l05nDA_conjEnd_apply, l05nDA_conj_coe]
    have : θ.toLinearMap ∘ₗ (g : V →ₗ[ZMod 3] V) ∘ₗ θ.symm.toLinearMap = y := by
      rw [hgeq]; apply LinearMap.ext; intro w; simp [LinearMap.comp_apply]
    exact this

private lemma l05nPC_conjEnd_gensJV {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (gensJV : Set (V ≃ₗ[ZMod 3] V))
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin 6 // GGDepED4In i},
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap) :
    l05nDA_conjEnd (p := 3) (N := 7) θ '' gensJV =
      (fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) '' Set.univ := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := hJ₁ g hg
    refine ⟨i, Set.mem_univ _, ?_⟩
    rw [l05nDA_conjEnd_apply, l05nDA_conj_coe, hi]
    apply LinearMap.ext; intro w; simp [LinearMap.comp_apply, ggDepELrefl]
  · rintro ⟨i, -, rfl⟩
    obtain ⟨g, hg, hgeq⟩ := hJ₂ i
    refine ⟨g, hg, ?_⟩
    rw [l05nDA_conjEnd_apply, l05nDA_conj_coe, hgeq]
    apply LinearMap.ext; intro w; simp [LinearMap.comp_apply, ggDepELrefl]

private lemma l05nPC_mem_A_iff {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {A : Subgroup (MulAut ↥Bs)}
    (gensV : Set (V ≃ₗ[ZMod 3] V)) (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gensV)
    (hgen : l05nDA_conjEnd (p := 3) (N := 7) θ '' gensV = gens) (t : MulAut ↥Bs) :
    t ∈ A ↔ l05nDA_PhiEnd (p := 3) (N := 7) ι θ t ∈ Submonoid.closure gens := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hcl : l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensV) =
      ↑(Submonoid.closure gens) :=
    (l05nDA_closure_image (l05nDA_conjEnd (p := 3) (N := 7) θ) gensV).trans (by rw [hgen])
  constructor
  · intro ht
    have h1 : ggLin (p := 3) ι t ∈ ↑(Subgroup.closure gensV) := by
      rw [← hA]; exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have h2 : l05nDA_PhiEnd (p := 3) (N := 7) ι θ t ∈
        l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensV) :=
      ⟨ggLin (p := 3) ι t, h1, rfl⟩
    rwa [hcl] at h2
  · intro hs
    have h2 : l05nDA_PhiEnd (p := 3) (N := 7) ι θ t ∈
        l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensV) := by
      rwa [hcl]
    obtain ⟨u, hu, hueq⟩ := h2
    have hut : ggLin (p := 3) ι t = u := by
      apply l05nDA_conj_injective (p := 3) (N := 7) θ
      apply LinearEquiv.toLinearMap_injective
      show l05nDA_conjEnd (p := 3) (N := 7) θ (ggLin (p := 3) ι t) =
        l05nDA_conjEnd (p := 3) (N := 7) θ u
      rw [hueq, l05nDA_PhiEnd_apply]
    have hu' : ggLin (p := 3) ι t ∈ ↑(Subgroup.closure gensV) := by rwa [← hut] at hu
    have hmem : ggLin (p := 3) ι t ∈ A.map (ggLin (p := 3) ι) := by rwa [hA]
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
    rwa [ggLin_injective (p := 3) ι hxeq] at hx

private lemma l05nPC_fix_image {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {A : Subgroup (MulAut ↥Bs)}
    (gensV : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gensV)
    (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (z : ↥Bs) :
    l05nDA_PhiEnd (p := 3) (N := 7) ι θ '' ggPZFixRefl 3 A z =
      ggDepELPZFixRefl gens (θ (ι (Additive.ofMul z))) := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hgen : l05nDA_conjEnd (p := 3) (N := 7) θ '' gensV = gens :=
    l05nPC_conjEnd_gensV θ gensV gens hg₁ hg₂
  have hmem := l05nPC_mem_A_iff ι θ gensV gens hA hgen
  have hcl : l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensV) =
      ↑(Submonoid.closure gens) :=
    (l05nDA_closure_image (l05nDA_conjEnd (p := 3) (N := 7) θ) gensV).trans (by rw [hgen])
  ext s
  constructor
  · rintro ⟨t, ⟨htA, htref, htz⟩, rfl⟩
    exact ⟨(hmem t).mp htA,
      (l05nDA_reflection_iff (p := 3) (N := 7) (by norm_num) ι θ t).mp htref,
      (l05nDA_PhiEnd_fix (p := 3) (N := 7) ι θ t z).mpr htz⟩
  · rintro ⟨hs, hsref, hsz⟩
    have hs' : s ∈ l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensV) := by
      rwa [hcl]
    obtain ⟨u, hu, hueq⟩ := hs'
    have huA : u ∈ ggLin (p := 3) ι '' A := by
      rw [← hA] at hu
      exact hu
    obtain ⟨t, htA, htu⟩ := huA
    have hst : l05nDA_PhiEnd (p := 3) (N := 7) ι θ t = s := by
      rw [l05nDA_PhiEnd_apply, htu, hueq]
    refine ⟨t, ⟨htA, ?_, ?_⟩, hst⟩
    · have h : GGTWIsRefl (l05nDA_PhiEnd (p := 3) (N := 7) ι θ t) := by
        rw [hst]; exact hsref
      exact (l05nDA_reflection_iff (p := 3) (N := 7) (by norm_num) ι θ t).mpr h
    · have h : l05nDA_PhiEnd (p := 3) (N := 7) ι θ t (θ (ι (Additive.ofMul z))) =
          θ (ι (Additive.ofMul z)) := by
        rw [hst]; exact hsz
      exact (l05nDA_PhiEnd_fix (p := 3) (N := 7) ι θ t z).mp h

private lemma l05nPC_orbit_image {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {AJ A : Subgroup (MulAut ↥Bs)}
    (gensV gensJV : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gensV)
    (hAJ : AJ.map (ggLin (p := 3) ι) = Subgroup.closure gensJV)
    (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin 6 // GGDepED4In i},
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (z : ↥Bs) :
    l05nDA_PhiEnd (p := 3) (N := 7) ι θ '' ggPZOrbit 3 AJ A z =
      ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))) := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hgenJ : l05nDA_conjEnd (p := 3) (N := 7) θ '' gensJV =
      (fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) '' Set.univ :=
    l05nPC_conjEnd_gensJV θ gensJV hJ₁ hJ₂
  have hfix := l05nPC_fix_image ι θ gensV hA gens hg₁ hg₂ z
  have hclJ : l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensJV) =
      ↑(Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} =>
        ggDepELrefl i.1) '' Set.univ)) :=
    (l05nDA_closure_image (l05nDA_conjEnd (p := 3) (N := 7) θ) gensJV).trans (by rw [hgenJ])
  have hbase : ∀ g ∈ Subgroup.closure (ggPZFixRefl 3 A z),
      l05nDA_PhiEnd (p := 3) (N := 7) ι θ g ∈
        Submonoid.closure (ggDepELPZFixRefl gens (θ (ι (Additive.ofMul z)))) := by
    intro g hg
    have h2 : l05nDA_PhiEnd (p := 3) (N := 7) ι θ g ∈
        l05nDA_PhiEnd (p := 3) (N := 7) ι θ '' ↑(Subgroup.closure (ggPZFixRefl 3 A z)) :=
      ⟨g, hg, rfl⟩
    rwa [l05nDA_closure_image (l05nDA_PhiEnd (p := 3) (N := 7) ι θ) (ggPZFixRefl 3 A z),
      hfix] at h2
  have hJmem : ∀ r ∈ AJ, GGIsReflection 3 r →
      l05nDA_PhiEnd (p := 3) (N := 7) ι θ r ∈
        Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} =>
          ggDepELrefl i.1) '' Set.univ) := by
    intro r hrAJ _
    have hrin : ggLin (p := 3) ι r ∈ ↑(Subgroup.closure gensJV) := by
      rw [← hAJ]; exact Subgroup.mem_map.mpr ⟨r, hrAJ, rfl⟩
    have h2 : l05nDA_conjEnd (p := 3) (N := 7) θ (ggLin (p := 3) ι r) ∈
        l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensJV) := ⟨_, hrin, rfl⟩
    rwa [hclJ] at h2
  ext s
  constructor
  · rintro ⟨t, ⟨r, hrAJ, hrref, g, hg, rfl⟩, rfl⟩
    refine ⟨l05nDA_PhiEnd (p := 3) (N := 7) ι θ r,
      ⟨hJmem r hrAJ hrref,
        (l05nDA_reflection_iff (p := 3) (N := 7) (by norm_num) ι θ r).mp hrref⟩,
      l05nDA_PhiEnd (p := 3) (N := 7) ι θ g, hbase g hg,
      l05nDA_PhiEnd (p := 3) (N := 7) ι θ g⁻¹, hbase g⁻¹ (Subgroup.inv_mem _ hg), ?_, ?_⟩
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [map_mul, map_mul]
  · rintro ⟨r, ⟨hrclos, hrref⟩, g, hg, g', hg', hgg', rfl⟩
    have hrclos' : r ∈ l05nDA_conjEnd (p := 3) (N := 7) θ '' ↑(Subgroup.closure gensJV) := by
      rwa [hclJ]
    obtain ⟨u, hu, hur⟩ := hrclos'
    have huAJ : u ∈ ggLin (p := 3) ι '' AJ := by
      rw [← hAJ] at hu
      exact hu
    obtain ⟨r0, hr0AJ, hr0u⟩ := huAJ
    have hg'' : g ∈ l05nDA_PhiEnd (p := 3) (N := 7) ι θ ''
        ↑(Subgroup.closure (ggPZFixRefl 3 A z)) := by
      rwa [l05nDA_closure_image (l05nDA_PhiEnd (p := 3) (N := 7) ι θ) (ggPZFixRefl 3 A z),
        hfix]
    obtain ⟨g0, hg0, hg0g⟩ := hg''
    have hgg'' : g' ∈ l05nDA_PhiEnd (p := 3) (N := 7) ι θ ''
        ↑(Subgroup.closure (ggPZFixRefl 3 A z)) := by
      rwa [l05nDA_closure_image (l05nDA_PhiEnd (p := 3) (N := 7) ι θ) (ggPZFixRefl 3 A z),
        hfix]
    obtain ⟨g0', hg0', hg0'g'⟩ := hgg''
    have hgg0 : l05nDA_PhiEnd (p := 3) (N := 7) ι θ (g0 * g0') = 1 := by
      rw [map_mul, hg0g, hg0'g', hgg']
    have hgg0' : g0 * g0' = 1 :=
      l05nDA_PhiEnd_injective (p := 3) (N := 7) ι θ (by rw [hgg0, map_one])
    have hr0r : l05nDA_PhiEnd (p := 3) (N := 7) ι θ r0 = r := by
      rw [l05nDA_PhiEnd_apply, hr0u, hur]
    have hrref0 : GGIsReflection 3 r0 :=
      (l05nDA_reflection_iff (p := 3) (N := 7) (by norm_num) ι θ r0).mpr
        (by rw [hr0r]; exact hrref)
    refine ⟨g0 * r0 * g0⁻¹, ⟨r0, hr0AJ, hrref0, g0, hg0, rfl⟩, ?_⟩
    rw [show g0⁻¹ = g0' from (eq_inv_of_mul_eq_one_right hgg0').symm]
    rw [map_mul, map_mul, hg0g, hr0r, hg0'g']

theorem ggDepELPZ_card_centre {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {AJ A : Subgroup (MulAut ↥Bs)}
    (gensV gensJV : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gensV)
    (hAJ : AJ.map (ggLin (p := 3) ι) = Subgroup.closure gensJV)
    (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin 6 // GGDepED4In i},
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (z : ↥Bs) :
    Nat.card ↥(Subgroup.closure (ggPZOrbit 3 AJ A z)) =
        Nat.card ↥(Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))))) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.closure (ggPZOrbit 3 AJ A z))) =
        ggDepELCentreCard
          (Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))))) := by
  have hcl : l05nDA_PhiEnd (p := 3) (N := 7) ι θ ''
      ↑(Subgroup.closure (ggPZOrbit 3 AJ A z)) =
      ↑(Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))))) := by
    rw [l05nDA_closure_image (l05nDA_PhiEnd (p := 3) (N := 7) ι θ) (ggPZOrbit 3 AJ A z)]
    rw [l05nPC_orbit_image ι θ gensV gensJV hA hAJ gens hg₁ hg₂ hJ₁ hJ₂ z]
  have hfmem : ∀ x : ↥(Subgroup.closure (ggPZOrbit 3 AJ A z)),
      l05nDA_PhiEnd (p := 3) (N := 7) ι θ x ∈
        Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z)))) := by
    intro x
    have hx : l05nDA_PhiEnd (p := 3) (N := 7) ι θ x ∈
        l05nDA_PhiEnd (p := 3) (N := 7) ι θ '' ↑(Subgroup.closure (ggPZOrbit 3 AJ A z)) :=
      ⟨x, x.2, rfl⟩
    rwa [hcl] at hx
  let F : ↥(Subgroup.closure (ggPZOrbit 3 AJ A z)) →
      ↥(Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))))) :=
    fun x => ⟨l05nDA_PhiEnd (p := 3) (N := 7) ι θ x, hfmem x⟩
  have F_mul : ∀ a b, F (a * b) = F a * F b := by
    intro a b
    exact Subtype.ext (map_mul (l05nDA_PhiEnd (p := 3) (N := 7) ι θ)
      (a : MulAut ↥Bs) (b : MulAut ↥Bs))
  have F_inj : Function.Injective F := by
    intro a b hab
    exact Subtype.ext (l05nDA_PhiEnd_injective (p := 3) (N := 7) ι θ (Subtype.ext_iff.mp hab))
  have F_surj : Function.Surjective F := by
    intro y
    have hy : (y : Module.End (ZMod 3) (GGDepAE 3 6)) ∈
        l05nDA_PhiEnd (p := 3) (N := 7) ι θ '' ↑(Subgroup.closure (ggPZOrbit 3 AJ A z)) := by
      rw [hcl]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  constructor
  · exact Nat.card_congr (Equiv.ofBijective F ⟨F_inj, F_surj⟩)
  · have e1 : ↥(Subgroup.center ↥(Subgroup.closure (ggPZOrbit 3 AJ A z))) ≃
        {w : ↥(Subgroup.closure (ggPZOrbit 3 AJ A z)) // ∀ g, g * w = w * g} :=
      { toFun := fun z => ⟨z.1, Subgroup.mem_center_iff.mp z.2⟩
        invFun := fun z => ⟨z.1, Subgroup.mem_center_iff.mpr z.2⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
    let Zf : {w : ↥(Subgroup.closure (ggPZOrbit 3 AJ A z)) // ∀ g, g * w = w * g} →
        {w : ↥(Submonoid.closure (ggDepELPZOrbit gens (θ (ι (Additive.ofMul z))))) //
          ∀ h, w * h = h * w} :=
      fun z => ⟨F z.1, fun h => by
        obtain ⟨g, rfl⟩ := F_surj h
        rw [← F_mul, ← F_mul, z.2 g]⟩
    have hZ : Function.Bijective Zf := by
      constructor
      · intro z z' h
        exact Subtype.ext (F_inj (Subtype.ext_iff.mp h))
      · intro w
        obtain ⟨g, hg⟩ := F_surj w.1
        refine ⟨⟨g, fun a => ?_⟩, Subtype.ext hg⟩
        apply F_inj
        rw [F_mul, F_mul, hg]
        exact (w.2 (F a)).symm
    exact (Nat.card_congr e1).trans (Nat.card_congr (Equiv.ofBijective Zf hZ))

end CFSG.StandardType

end
