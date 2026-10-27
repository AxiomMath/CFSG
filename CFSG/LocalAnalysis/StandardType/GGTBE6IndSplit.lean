module

public import CFSG.LocalAnalysis.StandardType.GGTBE6Witness
public import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcSplit

public noncomputable section

namespace CFSG.StandardType.TBE6Ind

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.StandardType.GGTBE6Cover


theorem exists_aligned_adjoint {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) (ψ : L →* RecipeGroup .E6 K)
    (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p 6 (RecipeGroup .E6 K) (RecipeID .E6 K) L ψ A) :
    ∃ (ψa : L →* adjointGroup .E6 K), Function.Surjective ψa ∧
      ψa.ker ≤ Subgroup.center L ∧
      ∃ Λ : adjointGroup .E6 K →* MulAut L,
        Function.Injective Λ ∧
        (∀ x : L, Λ (ψa x) = MulAut.conj x) ∧
        (∀ g l, ψa (Λ g l) = g * ψa l * g⁻¹) ∧
        (torusPow .E6 K p).map Λ = A := by
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, -, hsc⟩ := hTB
  obtain ⟨Λ₀, hΛeq, hΛinj, hΛmap, hAΛ, hE, hcard, -⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E6 K)
      (ggOutdiagPrime_E6 hp hp3) (ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3)
      ψ hψ hker hperf hA hAI hsc
  let E := A.comap Λ₀
  let ε := recipeEquiv .E6 K
  have hEa : IsElemAbelian p (E.map ε.toMonoidHom) := TableB.isElemAbelian_map hE _
  have hEra : p ^ Tag.E6.rank ≤ Nat.card (E.map ε.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ε.injective, hcard]
    exact hr
  obtain ⟨g, hg⟩ := ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq _ hEa hEra
  let η : RecipeGroup .E6 K ≃* adjointGroup .E6 K := ε.trans (MulAut.conj g)
  have hEg : E.map η.toMonoidHom = torusPow .E6 K p := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hEA : E.map Λ₀ = A := by
    change (A.comap Λ₀).map Λ₀ = A
    have hle : A ≤ Λ₀.range := fun a ha => hAΛ a ha
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  let ψa : L →* adjointGroup .E6 K := η.toMonoidHom.comp ψ
  have hψa : Function.Surjective ψa := η.surjective.comp hψ
  have hka : ψa.ker ≤ Subgroup.center L := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact η.injective (hx.trans (map_one η).symm)
  let Λ : adjointGroup .E6 K →* MulAut L := Λ₀.comp η.symm.toMonoidHom
  have hΛn : ∀ x : L, Λ (ψa x) = MulAut.conj x := by
    intro x
    change Λ₀ (η.symm (η (ψ x))) = MulAut.conj x
    rw [η.symm_apply_apply]
    exact hΛeq rfl
  refine ⟨ψa, hψa, hka, Λ, hΛinj.comp η.symm.injective, hΛn, ?_, ?_⟩
  · intro x l
    change η (ψ (Λ₀ (η.symm x) l)) = x * η (ψ l) * x⁻¹
    rw [hΛmap, map_mul, map_mul, map_inv, η.apply_symm_apply]
  · rw [← hEg, Subgroup.map_map]
    have hcomp : Λ.comp η.toMonoidHom = Λ₀ := by
      apply MonoidHom.ext
      intro x
      change Λ₀ (η.symm (η x)) = Λ₀ x
      rw [η.symm_apply_apply]
    rw [hcomp, hEA]

theorem exists_marked {K L : Type} [Field K] [Finite K] [Group L]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) (A : Subgroup (MulAut L))
    (Λ : adjointGroup .E6 K →* MulAut L) (hΛ : Function.Injective Λ)
    (hA : (torusPow .E6 K p).map Λ = A) :
    ∃ hnA : ∀ i : Fin 6, Λ (CFSG.LieType.Chevalley.weylElement .E6 K i) ∈
        Subgroup.normalizer (A : Set (MulAut L)),
      ∃ eA : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer Λ.range A),
        ∀ i, (eA (CoxeterMatrix.E₆.simple i) : MulAut ↥A) = ggConjAut A (hnA i) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hdet := isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  let E := torusPow .E6 K p
  let ι := CFSG.RankThree.CentralCover.chevTorus .E6 ζ hζ
  have hι : Function.Injective ι :=
    CFSG.RankThree.CentralCover.chevTorus_injective hζo hζ hdet
  have hrange : ι.range = E :=
    range_chevTorus_eq_torusPow hζo hζ hdet (card_torusPow_E6 hp hp3 hpq)
  let n : Fin 6 → adjointGroup .E6 K := CFSG.LieType.Chevalley.weylElement .E6 K
  have hn : ∀ (i : Fin 6) (x : Fin 6 → ZMod p),
      n i * ι (Multiplicative.ofAdd x) * (n i)⁻¹ =
        ι (Multiplicative.ofAdd (torusAct .E6 p (simple .E6 i) x)) := by
    intro i x
    have h := CFSG.RankThree.CentralCover.weylElt_conj_chevTorus (τ := .E6) ζ hζ i x
    rw [← torusRefl_eq_torusAct (p := p) NoOffExc.cartan_symm_E6 i x]
    have hc : CFSG.RankThree.CentralCover.cartanFunctional .E6 p i x =
        ∑ j, (Tag.E6.cartan j i : ZMod p) * x j :=
      CFSG.RankThree.CentralCover.cartanFunctional_apply (τ := .E6) (p := p) i x
    simpa only [n, ι, CFSG.LieType.Chevalley.weylElement, torusRefl, hc] using h
  have hN : ∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E6 K)),
      ∃ v : WeylGroup .E6, ∀ x : Fin 6 → ZMod p,
        g * ι (Multiplicative.ofAdd x) * g⁻¹ =
          ι (Multiplicative.ofAdd (torusAct .E6 p v x)) := by
    intro g hg
    obtain ⟨u, hu, hgu⟩ := ExcWeylGen.exists_mem_closure_reflections_of_normalizes ζ hζ hrange
      (Subgroup.mem_normalizer_iff.mp hg)
    have huR : u ∈ (ExcWeylOuter.torusMulAut .E6 p).range := by
      rw [ExcWeylOuter.range_torusMulAut NoOffExc.cartan_symm_E6]
      exact hu
    obtain ⟨v, rfl⟩ := huR
    refine ⟨v, ?_⟩
    intro x
    exact hgu (Multiplicative.ofAdd x)
  obtain ⟨hnE, -, eW, heW⟩ := exists_markedWeyl_ggAutomizer (hp.odd_of_ne_two hp2)
    E ι hι hrange n hn hN
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_map E Λ hΛ hA n hnE eW heW
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) =
      CoxeterMatrix.E₆ := by
    refine coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) ?_
    rw [show Tag.E6.cartan = CartanMatrix.E 6 from cartanE_eq 6]
    exact ggIntCartan_E₆
  obtain ⟨ew, hew⟩ := HdRo7SU.Small.hdRo7SmAAux_groupEquiv_of_eq
    (M := (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
    (M' := CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6)) hmat.symm
  refine ⟨hnA, ew.trans eA, fun i => ?_⟩
  exact (congrArg (fun w : WeylGroup .E6 => (eA w : MulAut ↥A)) (hew i)).trans (heA i)

theorem torData_aligned {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) (ψ : L →* adjointGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) (A : Subgroup (MulAut L)) (hAe : IsElemAbelian p A)
    (Λ : adjointGroup .E6 K →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛn : ∀ l : L, Λ (ψ l) = MulAut.conj l)
    (hΛmap : ∀ g l, ψ (Λ g l) = g * ψ l * g⁻¹)
    (hA : (torusPow .E6 K p).map Λ = A) :
    ∃ w : GGTorusTorWit (Nat.card K - 1) 6 L A, w.Holds CartanMatrix.E₆ CoxeterMatrix.E₆ ∧
      ∀ k, ψ (w.n k) = CFSG.LieType.Chevalley.weylElement .E6 K k := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hZ : ψ.ker = Subgroup.center L := BstarDesc.ker_eq_center hψ hker
    (center_adjointGroup_eq_bot (τ := .E6) (K := K))
  let ρ : MulAut L →* MulAut (adjointGroup .E6 K) := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := BstarDesc.descAut_apply hψ hZ
  have hρi : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hρΛ : ∀ g, ρ (Λ g) = MulAut.conj g := by
    intro g
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hρ, hΛmap]
    rfl
  obtain ⟨φ, δ, hφs, hφ, -, hδi, hδ, hδfix, -, hδn⟩ :=
    exists_cover_and_diagonal_lift K L ψ hψ hker hperf
  let e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)) := by
    have he : Kˣ ≃* Multiplicative (ZMod (Nat.card Kˣ)) :=
      (zmodCyclicMulEquiv inferInstance).symm
    rwa [Nat.card_units] at he
  have hρδ : ∀ b, ρ (δ b) = rootDiagAutHom .E6 K b := by
    intro b
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hρ, hδ]
    rfl
  have hτδ : ∀ τ b, ρ τ = rootDiagAutHom .E6 K b → τ = δ b := by
    intro τ b hb
    apply hρi
    rw [hb, hρδ]
  have hfullp : ∀ b : Fin Tag.E6.rank → Kˣ, (∀ i, b i ^ p = 1) →
      rootDiagUnit .E6 b ∈ torusGroup .E6 K :=
    fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have hAT : A ≤ TBE6.torus ρ := by
    intro a ha
    rw [← hA] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg.1
    refine ⟨b, ?_⟩
    rw [hρΛ]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change rootDiagUnit .E6 b * (x : ModGL .E6 K) * (rootDiagUnit .E6 b)⁻¹ =
      (g : ModGL .E6 K) * (x : ModGL .E6 K) * (g : ModGL .E6 K)⁻¹
    rw [hb]
  have hroot : ∀ i : Fin Tag.E6.rank, ∃ a ∈ A, TBE6.root ρ e i a ≠ 1 := by
    intro i
    obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
    have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
    let b : Fin Tag.E6.rank → Kˣ := fun _ => ζ
    have hb : ∀ j, b j ^ p = 1 := fun _ => hζ
    let g : adjointGroup .E6 K := ⟨rootDiagUnit .E6 b,
      CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (hfullp b hb)⟩
    have hg : g ∈ torusPow .E6 K p := by
      refine ⟨hfullp b hb, Subtype.ext ?_⟩
      change rootDiagUnit .E6 b ^ p = 1
      rw [rootDiagUnit_pow, show b ^ p = 1 from funext hb, rootDiagUnit_one]
    have hga : Λ g ∈ A := hA ▸ Subgroup.mem_map_of_mem Λ hg
    have hρg : ρ (Λ g) = rootDiagAutHom .E6 K b := by
      rw [hρΛ]
      rfl
    refine ⟨Λ g, hga, ?_⟩
    rw [TBE6.root_apply ρ e i hρg]
    change e ζ ≠ 1
    intro he
    have hζ1 : ζ = 1 := e.injective (he.trans (map_one e).symm)
    rw [hζ1, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hcent : ∀ l : L, (∀ a ∈ A, MulAut.conj l * a = a * MulAut.conj l) →
      l ∈ (φ.comp (minTorus e6Data_valid K)).range := by
    intro l hl
    have hlT : (ψ l : ModGL .E6 K) ∈ torusGroup .E6 K := by
      have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
      rw [← adjointGroup_inf_centralizer_torusPow_of_ne_two hp hp2 hpk hfullp]
      refine ⟨(ψ l).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have hxC : x ∈ adjointGroup .E6 K :=
        CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hx.1
      let g : adjointGroup .E6 K := ⟨x, hxC⟩
      have hg : g ∈ torusPow .E6 K p := ⟨hx.1, Subtype.ext hx.2⟩
      have ha : Λ g ∈ A := hA ▸ Subgroup.mem_map_of_mem Λ hg
      have hc := congrArg ρ (hl (Λ g) ha)
      rw [map_mul, map_mul, E6ThreeModel.rho_conj hψ hρ, hρΛ] at hc
      have heq : ψ l * g = g * ψ l := by
        apply (CFSG.mulAutConj_injective_of_center_eq_bot
          (center_adjointGroup_eq_bot (τ := .E6) (K := K)))
        simpa only [map_mul] using hc
      exact congrArg Subtype.val heq.symm
    exact TBE6.mem_coroot_torus_of_map_mem_torus ψ φ hφ hφs e hlT
  have hrange : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨l, rfl⟩ := hψ g
      exact ⟨l, (hΛn l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨ψ l, hΛn l⟩
  let n : Fin Tag.E6.rank → L := fun i => φ (e6Data_valid.nm K i)
  have hnmap : ∀ i, Λ (CFSG.LieType.Chevalley.weylElement .E6 K i) = MulAut.conj (n i) := by
    intro i
    rw [← hΛn (n i)]
    congr 1
    change CFSG.LieType.Chevalley.weylElement .E6 K i = ψ (φ (e6Data_valid.nm K i))
    rw [hφ]
    apply Subtype.ext
    change weylElt .E6 K i 1 = (e6Isogeny K (e6Data_valid.nm K i) : ModGL .E6 K)
    rw [← show e6Data_valid.nt K i 1 = e6Data_valid.nm K i by
      rw [e6Data_valid.nt_eq_hm_mul, e6Data_valid.hm_one, one_mul]]
    exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_nt_eq i 1).symm
  obtain ⟨hnA, eA, heA⟩ := exists_marked hp hp2 hp3 hpq A Λ hΛ hA
  have hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L)) := by
    intro i
    have hi := hnA i
    rw [hnmap i] at hi
    exact hi
  have hfix : ∀ τ ∈ TBE6.torus ρ, ∀ i s,
      τ (φ (e6Data_valid.hm K i s)) = φ (e6Data_valid.hm K i s) := by
    intro τ hτ i s
    obtain ⟨b, hb⟩ := hτ
    rw [hτδ τ b hb.symm]
    exact hδfix b i s
  have hmove : ∀ τ ∈ TBE6.torus ρ, ∀ i,
      n i * (τ (n i))⁻¹ = (TBE6.coroot e φ i (TBE6.root ρ e i τ))⁻¹ := by
    intro τ hτ i
    obtain ⟨b, hb⟩ := hτ
    rw [hτδ τ b hb.symm]
    change φ (e6Data_valid.nm K i) * (δ b (φ (e6Data_valid.nm K i)))⁻¹ = _
    rw [hδn, TBE6.root_apply ρ e i (hρδ b)]
    change φ (e6Data_valid.nm K i) *
      (φ (e6Data_valid.hm K i (b i)) * φ (e6Data_valid.nm K i))⁻¹ =
      (φ (e6Data_valid.hm K i (e.symm (e (b i)))))⁻¹
    rw [e.symm_apply_apply]
    group
  have hfour : GGTDHoldsFour (TBE6.witness ρ e φ n hn) CoxeterMatrix.E₆ := by
    have heq : ∀ i, (eA (CoxeterMatrix.E₆.simple i) : MulAut ↥A) = ggConjAut A (hn i) := by
      intro i
      apply (heA i).trans
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      simp only [ggConjAut_apply, hnmap i]
    let eA' : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer (MulAut.conj : L →* MulAut L).range A) :=
      eA.trans (MulEquiv.subgroupCongr (congrArg (fun I => ggAutomizer I A) hrange))
    have heq' : ∀ i, (eA' (CoxeterMatrix.E₆.simple i) : MulAut ↥A) = ggConjAut A (hn i) := by
      intro i
      change (eA (CoxeterMatrix.E₆.simple i) : MulAut ↥A) = ggConjAut A (hn i)
      exact heq i
    refine ⟨?_, eA', heq'⟩
    let f : CoxeterMatrix.E₆.Group →* MulAut ↥A :=
      (ggAutomizer (MulAut.conj : L →* MulAut L).range A).subtype.comp eA'.toMonoidHom
    have hf : f.range = ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩; exact (eA' v).2
      · intro hx
        obtain ⟨v, hv⟩ := eA'.surjective ⟨x, hx⟩
        exact ⟨v, congrArg Subtype.val hv⟩
    rw [← hf, MonoidHom.range_eq_map, ← CoxeterMatrix.E₆.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (heq' i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨CoxeterMatrix.E₆.simple i, ⟨i, rfl⟩, heq' i⟩
  refine ⟨TBE6.witness ρ e φ n hn, ggTDHolds_of_parts
    (TBE6.holdsOne ρ e φ n hn ψ hψ hρ hρi hφ hAT hfix)
    (TBE6.holdsTwo ρ e φ n hn hρi hroot hfix hmove)
    (TBE6.holdsThree ρ e φ n hn ψ hψ hρ hφ hφs
      (fun a ha b hb => TableB.IsElemAbelian.comm hAe ha hb) hcent hfix) hfour, fun k => ?_⟩
  apply hΛ
  change Λ (ψ (n k)) = _
  rw [hnmap k, hΛn]

theorem ggTorusTorW_recipe_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusTorW p 6 (Nat.card K - 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
      (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨ψa, hψa, hka, Λ, hΛ, hΛn, hΛmap, hA⟩ :=
    exists_aligned_adjoint hp hp2 hp3 hpq ψ A hTB
  obtain ⟨w, hw, -⟩ := torData_aligned hp hp2 hp3 hpq ψa hψa hka hTB.2.2.1 A hTB.2.2.2.1
    Λ hΛ hΛn hΛmap hA
  exact ⟨w, hw⟩

theorem ggTBTorE6Ind_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6)
    (hpm : p ∣ ggTorM lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW p (6 - ggTorEnn p lab) (ggTorM lab) 6
        (CartanMatrix.E 6) CoxeterMatrix.E₆ R I := by
  obtain ⟨t, l, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag hf hpm ⊢
  subst htag
  have hpq : p ∣ 2 ^ f - 1 := by simpa [ggTorM] using hpm
  have hpq' : ¬ p ∣ 2 ^ f + 1 := by
    intro hd
    have heven : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hd hpq
    have hq : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by decide)
    have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [hsub] at heven
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp heven |>.resolve_left hp.ne_one)
  have hEnn : ggTorEnn p ⟨.E6, l, f⟩ = 0 := by simp [ggTorEnn, hpq']
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  rw [hEnn, Nat.sub_zero]
  have hm : ggTorM ⟨.E6, l, f⟩ = Nat.card K - 1 := by simp [ggTorM, hK]
  rw [hm]
  exact ggTorusTorW_recipe_E6 hp hp2 hp3 (by rw [hK]; exact hpq)

theorem ggTBTorE6Ind_of_twist (h : GGTBTorE6IndTwist) : GGTBTorE6Ind := by
  intro p hp hp2 hp3 lab hlab ht hm
  rcases ht with ht | ht
  · exact ggTBTorE6Ind_split hp hp2 hp3 hlab ht hm
  · exact h p hp hp2 hp3 lab hlab ht hm

end CFSG.StandardType.TBE6Ind
