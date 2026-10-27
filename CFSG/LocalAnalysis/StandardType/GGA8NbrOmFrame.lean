module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmTorusMoves
public import CFSG.LocalAnalysis.StandardType.GGA8NbrGlueB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCompBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.RankThree.PartOne.S11d.OrthModels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal
open CFSG.LieType.Universal

namespace A8Coord

private lemma om3_eq_one_of_mem_centralizer_of_center_eq_bot {G : Type*} [Group G]
    {X : Subgroup G} (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private theorem om3_exists_nat_pow {G : Type*} [Group G] {x : G} (hord : orderOf x = 7)
    {c : G} (hc : c ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = c := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  refine ⟨(n % 7).toNat, ?_⟩
  rw [← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num : (7 : ℤ) ≠ 0))]
  have h1 : x ^ (n % (7 : ℤ)) = x ^ n := by
    have h := zpow_mod_orderOf x n
    rwa [hord] at h
  rw [h1, hn]

private theorem om3_pow_val_add {M : Type*} [Monoid M] {x : M} (hx : x ^ 7 = 1)
    (a b : ZMod 7) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx]

private lemma om3_conj_apply {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (w e : V ≃ₗ[K] V) (x : V) : (w⁻¹ * e * w) x = w⁻¹ (e (w x)) := by
  rw [mul_assoc, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

private theorem om3_frameConj {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {w : V ≃ₗ[K] V}
    (hw : w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V))) :
    ∃ F' : SevOm.Frame Q p A r,
      (∀ s : Multiplicative (Fin r → ZMod p), F'.ι s = w⁻¹ * F.ι s * w) ∧
      (∀ i, F'.U i = (F.U i).map ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)) := by
  classical
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q hw.1
  have hwN : w ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)) := hw.2
  have hwNinv : w⁻¹ ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)) := Subgroup.inv_mem _ hwN
  have hwOinv : w⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hwO
  have hpol : ∀ u v : V,
      QuadraticMap.polar Q (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u) (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) v) =
        QuadraticMap.polar Q u v :=
    fun u v => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hwOinv u v
  have hpolw : ∀ u v : V,
      QuadraticMap.polar Q ((w : V →ₗ[K] V) u) ((w : V →ₗ[K] V) v) =
        QuadraticMap.polar Q u v :=
    fun u v => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hwO u v
  refine ⟨{
    ι := { toFun := fun s => w⁻¹ * F.ι s * w
           map_one' := by simp
           map_mul' := fun s t => by
             rw [map_mul]
             group }
    U := fun i => (F.U i).map ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)
    inj := ?_
    range := ?_
    ne_bot := ?_
    nondeg := ?_
    orth := ?_
    mapsTo := ?_
    triv := ?_
    fpf := ?_
    fix := ?_ }, (fun s => rfl), (fun i => rfl)⟩
  · intro s t hst
    apply F.inj
    have hst' : w⁻¹ * F.ι s * w = w⁻¹ * F.ι t * w := hst
    calc F.ι s = w * (w⁻¹ * F.ι s * w) * w⁻¹ := by group
      _ = w * (w⁻¹ * F.ι t * w) * w⁻¹ := by rw [hst']
      _ = F.ι t := by group
  · ext g
    constructor
    · rintro ⟨s, rfl⟩
      simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hwNinv (F.ι s)).mp (F.mem s)
    · intro hg
      have hwg : w * g * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwN g).mp hg
      obtain ⟨s, hs⟩ := F.exists_eq hwg
      refine ⟨s, ?_⟩
      change w⁻¹ * F.ι s * w = g
      rw [hs]
      group
  · intro i hbot
    apply F.ne_bot i
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hu' : ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u ∈ (F.U i).map ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) :=
      ⟨u, hu, rfl⟩
    rw [hbot] at hu'
    have h2 : ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u = 0 := by simpa using hu'
    exact (w⁻¹).injective (by simpa using h2)
  · intro i u hu h
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    have h0 : u₀ = 0 := F.nondeg i u₀ hu₀ fun v hv => by
      have h1 := h (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) v) ⟨v, hv, rfl⟩
      rwa [hpol v u₀] at h1
    rw [h0, map_zero]
  · intro i j hij u hu v hv
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
    rw [hpol u₀ v₀]
    exact F.orth i j hij u₀ hu₀ v₀ hv₀
  · intro s j u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    refine ⟨F.ι s u₀, F.mapsTo s j u₀ hu₀, ?_⟩
    show (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) (F.ι s u₀)) =
      (w⁻¹ * F.ι s * w) (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀)
    rw [om3_conj_apply]
    rw [show w (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀) = u₀ from
      LinearEquiv.apply_symm_apply w u₀]
    rfl
  · intro s j hj u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    show (w⁻¹ * F.ι s * w) (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀) =
      ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀
    rw [om3_conj_apply]
    rw [show w (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀) = u₀ from
      LinearEquiv.apply_symm_apply w u₀]
    rw [F.triv s j hj u₀ hu₀]
    rfl
  · intro s j hj u hu h1
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    have h2 : F.ι s u₀ = u₀ := by
      change (w⁻¹ * F.ι s * w) (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀) =
        ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀ at h1
      rw [om3_conj_apply] at h1
      rw [show w (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u₀) = u₀ from
        LinearEquiv.apply_symm_apply w u₀] at h1
      exact (w⁻¹).injective (by simpa using h1)
    rw [F.fpf s j hj u₀ hu₀ h2, map_zero]
  · intro s v
    change (w⁻¹ * F.ι s * w) v = v ↔
      ∀ j, toAdd s j ≠ 0 → ∀ u ∈ (F.U j).map ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V),
        QuadraticMap.polar Q u v = 0
    rw [om3_conj_apply]
    constructor
    · intro hv
      have h1 : F.ι s (w v) = w v := by
        have := congrArg w hv
        simpa using this
      intro j hj u' hu'
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hu'
      have h2 := (F.fix s (w v)).mp h1 j hj u hu
      have h3 : QuadraticMap.polar Q (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u) v =
          QuadraticMap.polar Q u (w v) := by
        have hh := hpol u (w v)
        rwa [show ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) (w v) = v from
          LinearEquiv.symm_apply_apply w v] at hh
      rw [h3, h2]
    · intro hv
      have h1 : F.ι s (w v) = w v := (F.fix s (w v)).mpr fun j hj u hu => by
        have h2 := hv j hj (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u) ⟨u, hu, rfl⟩
        have h3 : QuadraticMap.polar Q (((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) u) v =
            QuadraticMap.polar Q u (w v) := by
          have hh := hpol u (w v)
          rwa [show ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) (w v) = v from
            LinearEquiv.symm_apply_apply w v] at hh
        rwa [h3] at h2
      rw [h1]
      exact LinearEquiv.symm_apply_apply w v

private theorem om3_frameMoves_conj {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {O : Subgroup (ZMod p)ˣ}
    (hmoves : CoordOm.FrameMovesAll F O) {w : V ≃ₗ[K] V}
    (hw : w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)))
    {F' : SevOm.Frame Q p A r}
    (hF'ι : ∀ s : Multiplicative (Fin r → ZMod p), F'.ι s = w⁻¹ * F.ι s * w) :
    CoordOm.FrameMovesAll F' O := by
  intro π η hη
  obtain ⟨w', hw', hws'⟩ := hmoves π η hη
  refine ⟨w⁻¹ * w' * w, ⟨?_, ?_⟩, fun s => ?_⟩
  · exact (orthDerived Q).mul_mem ((orthDerived Q).mul_mem ((orthDerived Q).inv_mem hw.1) hw'.1)
      hw.1
  · exact (Subgroup.normalizer (A : Set (V ≃ₗ[K] V))).mul_mem
      ((Subgroup.normalizer (A : Set (V ≃ₗ[K] V))).mul_mem
        ((Subgroup.normalizer (A : Set (V ≃ₗ[K] V))).inv_mem hw.2) hw'.2) hw.2
  · rw [hF'ι, hF'ι]
    calc (w⁻¹ * w' * w)⁻¹ * (w⁻¹ * F.ι (ofAdd s) * w) * (w⁻¹ * w' * w)
        = w⁻¹ * (w'⁻¹ * F.ι (ofAdd s) * w') * w := by group
      _ = w⁻¹ * F.ι (ofAdd fun i => (η i : ZMod p) * s (π i)) * w := by rw [hws']

private theorem om3_frameAligned_conj {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hal : CoordOm.FrameAligned F ζ) {w : V ≃ₗ[K] V}
    {F' : SevOm.Frame Q p A r}
    (hF'ι : ∀ s : Multiplicative (Fin r → ZMod p), F'.ι s = w⁻¹ * F.ι s * w)
    (hF'U : ∀ i, F'.U i = (F.U i).map ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)) :
    CoordOm.FrameAligned F' ζ := by
  intro i
  obtain ⟨u, hu, hu0, huζ⟩ := hal i
  refine ⟨w⁻¹ u, ?_, ?_, ?_⟩
  · rw [hF'U i]; exact ⟨u, hu, rfl⟩
  · intro h
    exact hu0 ((w⁻¹).injective (by simpa using h))
  · rw [hF'ι, om3_conj_apply]
    rw [show w ((w⁻¹ : V ≃ₗ[K] V) u) = u from LinearEquiv.apply_symm_apply w u]
    rw [huζ]
    exact map_smul ((w⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) (ζ : K) u

theorem ggA8Nbr_omFrame {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J)
    (hin : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹)
    (φ : ↥omΩ →* G) (hinj : Function.Injective φ) (hrange : φ.range = L) :
    (∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L, ∃ k : ℕ, b = e * x ^ k) ∧
    ∀ e₀ ∈ Bs ⊓ L, ∃ (F : SevOm.Frame omQ 7 (omA φ Bs) 3) (ζ : (GaloisField 2 3)ˣ)
        (β : Fin 3 → ZMod 7),
      (∀ g ∈ omΩ, g ^ 7 = 1 → (∀ c ∈ omA φ Bs, g * c = c * g) → g ∈ omA φ Bs) ∧
      orderOf ζ = 7 ∧ (∀ i, Module.finrank (GaloisField 2 3) (F.U i) = 2) ∧
      CoordOm.FrameAligned F ζ ∧ CoordOm.FrameMovesAll F (CoordSp.signs 7) ∧
      CoordSp.SpAligned β ∧
      φ ⟨F.ι (ofAdd β), omA_le φ Bs (F.mem _)⟩ = e₀ ∧
      ∃ ιB : Additive ↥Bs ≃+ (Fin 4 → ZMod 7),
        ιB (Additive.ofMul ⟨x, hcfg.tableB_facts.2.2.1⟩) = Pi.single 0 1 ∧
        (∀ t : Fin 3 → ZMod 7,
          ∃ hb : φ ⟨F.ι (ofAdd t), omA_le φ Bs (F.mem _)⟩ ∈ Bs,
            ιB (Additive.ofMul ⟨φ ⟨F.ι (ofAdd t), omA_le φ Bs (F.mem _)⟩, hb⟩) =
              (Fin.cons 0 t : Fin 4 → ZMod 7)) ∧
        ∀ (π : Equiv.Perm (Fin 3)) (η : Fin 3 → (ZMod 7)ˣ), (∀ i, η i ∈ CoordSp.signs 7) →
          ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
            ιB (Additive.ofMul (ψ b)) =
              (Fin.cons (ιB (Additive.ofMul b) 0)
                (fun i : Fin 3 => (η i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) :
                Fin 4 → ZMod 7) := by
  classical
  have hBs_ea : IsElemAbelian 7 Bs := hcfg.tableB_facts.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hBs_ge : 7 ^ 4 ≤ Nat.card Bs := hcfg.tableB_facts.2.2.2.2
  have hordx : orderOf x = 7 := hcfg.orderOf_x
  have hx7 : x ^ 7 = 1 := by rw [← hordx]; exact pow_orderOf_eq_one x
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLx hy) x (by simp)).symm
  have hZOm : Subgroup.center ↥omΩ = ⊥ := by
    have h := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2 (le_refl 4)
      (minusCoeffs_irr 2 3)
    exact CFSG.RankThree.PartOne.center_orthDerived_eq_bot h.1 h.2
  have hZL : Subgroup.center L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzL : (z : G) ∈ L := z.2
    have hzG : (z : G) ∈ φ.range := by rw [hrange]; exact hzL
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hzG
    have haZ : a ∈ Subgroup.center ↥omΩ := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply hinj
      rw [map_mul, map_mul]
      have hcomm := Subgroup.mem_center_iff.mp hz
        (⟨φ b, by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩ : L)
      have h2 : φ b * (z : G) = (z : G) * φ b := congrArg Subtype.val hcomm
      rw [← ha] at h2
      first | exact h2 | exact h2.symm
    rw [hZOm, Subgroup.mem_bot] at haZ
    apply Subtype.ext
    rw [← ha, haZ, map_one]
    rfl
  have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨g, hg, hgk⟩ := hin b hb
      rw [hgk t ht]
      exact L.mul_mem (L.mul_mem hg ht) (L.inv_mem hg)
    · intro ht
      obtain ⟨g, hg, hgk⟩ := hin b⁻¹ (Bs.inv_mem hb)
      have h2 : b⁻¹ * (b * t * b⁻¹) * b ∈ L := by
        have h3 := hgk (b * t * b⁻¹) ht
        rw [inv_inv] at h3
        rw [h3]
        exact L.mul_mem (L.mul_mem hg ht) (L.inv_mem hg)
      rwa [show b⁻¹ * (b * t * b⁻¹) * b = t by group] at h2
  have hsplit0 : ∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L,
      ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = e * c :=
    ggBstar_split_of_inner hcfg.2.1 hZL hnorm hin
  have hcard_split : Nat.card Bs =
      Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    card_ggBstar_split hcfg.2.1 hZL hnorm hin
  have hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 7 :=
    hcfg.card_bstar_inf_centralizer_L
  have hE_ge : 7 ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
    have h : 7 ^ 3 * 7 ≤ Nat.card ↥(Bs ⊓ L) * 7 := by
      calc 7 ^ 3 * 7 = 7 ^ 4 := by norm_num
        _ ≤ Nat.card Bs := hBs_ge
        _ = Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
              hcard_split
        _ = Nat.card ↥(Bs ⊓ L) * 7 := by rw [hcardC]
    exact Nat.le_of_mul_le_mul_right h (by norm_num)
  have hsplit : ∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L, ∃ k : ℕ, b = e * x ^ k := by
    intro b hb
    obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b hb
    have hcz : c ∈ Subgroup.zpowers x := by
      rw [← hcfg.bstar_inf_centralizer_L]; exact hc
    obtain ⟨k, hk⟩ := om3_exists_nat_pow hordx hcz
    exact ⟨e, he, k, by rw [hbc, hk]⟩
  refine ⟨hsplit, ?_⟩
  intro e₀ he₀
  have hAΩ : omA φ Bs ≤ omΩ := omA_le φ Bs
  have hφA_mem : ∀ (a : OmV ≃ₗ[GaloisField 2 3] OmV) (ha : a ∈ omA φ Bs),
      φ ⟨a, hAΩ ha⟩ ∈ Bs := by
    intro a ha
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp ha
    have hyB : φ y ∈ Bs := Subgroup.mem_comap.mp hy
    have h1 : φ ⟨a, hAΩ ha⟩ = φ y := by
      congr 1
      exact Subtype.ext hyeq.symm
    rw [h1]; exact hyB
  have hmaxA : ∀ g ∈ omΩ, g ^ 7 = 1 → (∀ c ∈ omA φ Bs, g * c = c * g) →
      g ∈ omA φ Bs := by
    intro g hgΩ hg7 hgc
    have hgL : φ ⟨g, hgΩ⟩ ∈ L := by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨⟨g, hgΩ⟩, rfl⟩
    have hgcommC : φ ⟨g, hgΩ⟩ ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, k, hbk⟩ := hsplit b hb
      have heL : e ∈ L := (Subgroup.mem_inf.mp he).2
      have heB : e ∈ Bs := (Subgroup.mem_inf.mp he).1
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact heL)
      have haA : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs := by
        refine ⟨a, ?_, rfl⟩
        exact Subgroup.mem_comap.mpr (by rw [ha]; exact heB)
      have hcomm_ga : g * (a : OmV ≃ₗ[GaloisField 2 3] OmV) =
          (a : OmV ≃ₗ[GaloisField 2 3] OmV) * g := hgc a haA
      have hcommGe : φ ⟨g, hgΩ⟩ * e = e * φ ⟨g, hgΩ⟩ := by
        have h1 : (⟨g, hgΩ⟩ : ↥omΩ) * a = a * ⟨g, hgΩ⟩ := Subtype.ext hcomm_ga
        have h2 := congrArg φ h1
        rw [map_mul, map_mul] at h2
        rw [ha] at h2
        exact h2
      have hcommGx : φ ⟨g, hgΩ⟩ * x = x * φ ⟨g, hgΩ⟩ :=
        Subgroup.mem_centralizer_iff.mp hxcent (φ ⟨g, hgΩ⟩) hgL
      rw [hbk]
      calc (e * x ^ k) * φ ⟨g, hgΩ⟩
          = e * (x ^ k * φ ⟨g, hgΩ⟩) := by group
        _ = e * (φ ⟨g, hgΩ⟩ * x ^ k) := by
              rw [(show Commute (φ ⟨g, hgΩ⟩) x from hcommGx).pow_right k]
        _ = (e * φ ⟨g, hgΩ⟩) * x ^ k := by group
        _ = (φ ⟨g, hgΩ⟩ * e) * x ^ k := by rw [hcommGe]
        _ = φ ⟨g, hgΩ⟩ * (e * x ^ k) := by group
    have hgp : (φ ⟨g, hgΩ⟩) ^ 7 = 1 := by
      have hg7' : (⟨g, hgΩ⟩ : ↥omΩ) ^ 7 = 1 := Subtype.ext (by simpa using hg7)
      rw [← map_pow, hg7', map_one]
    exact ⟨⟨g, hgΩ⟩, hcfg.2.1.2.2.2 (φ ⟨g, hgΩ⟩) hgcommC hgp, rfl⟩
  have hp : ∀ a ∈ omA φ Bs, a ^ 7 = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    have hyB : φ y ∈ Bs := Subgroup.mem_comap.mp hy
    have h1 : φ (y ^ 7) = φ 1 := by rw [map_pow, hBs_ea.2 (φ y) hyB, map_one]
    have h2 := hinj h1
    simpa using congrArg (fun z : ↥omΩ => (z : OmV ≃ₗ[GaloisField 2 3] OmV)) h2
  have hcomm : ∀ a ∈ omA φ Bs, ∀ b ∈ omA φ Bs, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hb
    have hyB : φ y ∈ Bs := Subgroup.mem_comap.mp hy
    have hzB : φ z ∈ Bs := Subgroup.mem_comap.mp hz
    have h1 : φ y * φ z = φ z * φ y := IsElemAbelian.comm hBs_ea hyB hzB
    have h2 : φ (y * z) = φ (z * y) := by rw [map_mul, map_mul, h1]
    have h3 : y * z = z * y := hinj h2
    simpa using congrArg (fun w : ↥omΩ => (w : OmV ≃ₗ[GaloisField 2 3] OmV)) h3
  obtain ⟨F, ζ, hζo, hdim, hal, hmoves⟩ := omFrame_exists hAΩ hp hcomm hmaxA
  have he₀L : e₀ ∈ L := (Subgroup.mem_inf.mp he₀).2
  have he₀B : e₀ ∈ Bs := (Subgroup.mem_inf.mp he₀).1
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact he₀L)
  have haA : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs := by
    refine ⟨a, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr (by rw [ha]; exact he₀B)
  obtain ⟨s₀, hs₀⟩ := F.exists_eq haA
  let β₀ : Fin 3 → ZMod 7 := Multiplicative.toAdd s₀
  have hβ₀ : F.ι (ofAdd β₀) = (a : OmV ≃ₗ[GaloisField 2 3] OmV) := hs₀
  have hφβ₀ : φ ⟨F.ι (ofAdd β₀), omA_le φ Bs (F.mem _)⟩ = e₀ := by
    have h1 : (⟨F.ι (ofAdd β₀), omA_le φ Bs (F.mem _)⟩ : ↥omΩ) = a := Subtype.ext hβ₀
    rw [h1]; exact ha
  let η : Fin 3 → (ZMod 7)ˣ := CoordSp.alignSign β₀
  have hηmem : ∀ i, η i ∈ CoordSp.signs 7 := fun i => CoordSp.alignSign_mem β₀ i
  obtain ⟨w, hw, hws⟩ := hmoves (Equiv.refl (Fin 3)) η hηmem
  have hws' : ∀ s : Fin 3 → ZMod 7,
      w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun i => (η i : ZMod 7) * s i) := by
    intro s
    simpa using hws s
  obtain ⟨F', hF'ι, hF'U⟩ := om3_frameConj F hw
  let β : Fin 3 → ZMod 7 := fun i => (η i : ZMod 7) * β₀ i
  have hβal : CoordSp.SpAligned β := by
    change CoordSp.SpAligned fun i => (CoordSp.alignSign β₀ i : ZMod 7) * β₀ i
    exact CoordSp.spAligned_align (n := 3) (p := 7) (by norm_num) β₀
  have hF'β : F'.ι (ofAdd β) = F.ι (ofAdd β₀) := by
    rw [hF'ι, hws' β]
    congr 1
    apply Multiplicative.ofAdd.injective
    funext i
    change (η i : ZMod 7) * β i = β₀ i
    rw [show β i = (η i : ZMod 7) * β₀ i from rfl, ← mul_assoc, ← Units.val_mul]
    rw [show η i * η i = 1 from CoordSp.alignSign_mul_self β₀ i, Units.val_one, one_mul]
  have hdim' : ∀ i, Module.finrank (GaloisField 2 3) (F'.U i) = 2 := by
    intro i
    rw [hF'U i, LinearEquiv.finrank_map_eq]
    exact hdim i
  have hal' : CoordOm.FrameAligned F' ζ := om3_frameAligned_conj F hal hF'ι hF'U
  have hmo' : CoordOm.FrameMovesAll F' (CoordSp.signs 7) :=
    om3_frameMoves_conj F hmoves hw hF'ι
  have hφβ : φ ⟨F'.ι (ofAdd β), omA_le φ Bs (F'.mem _)⟩ = e₀ := by
    have h1 : (⟨F'.ι (ofAdd β), omA_le φ Bs (F'.mem _)⟩ : ↥omΩ) =
        ⟨F.ι (ofAdd β₀), omA_le φ Bs (F.mem _)⟩ := Subtype.ext hF'β
    rw [h1]; exact hφβ₀
  let ιT : (Fin 3 → ZMod 7) → G := fun t => φ ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩
  have hιT_mem_L : ∀ t, ιT t ∈ L := by
    intro t
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hιT_mem : ∀ t, ιT t ∈ Bs := fun t => hφA_mem _ (F'.mem _)
  have hιT_zero : ιT 0 = 1 := by
    change φ ⟨F'.ι (ofAdd (0 : Fin 3 → ZMod 7)), hAΩ (F'.mem _)⟩ = 1
    have h0 : (⟨F'.ι (ofAdd (0 : Fin 3 → ZMod 7)), hAΩ (F'.mem _)⟩ : ↥omΩ) = 1 := by
      apply Subtype.ext
      change F'.ι (ofAdd (0 : Fin 3 → ZMod 7)) = 1
      rw [show ofAdd (0 : Fin 3 → ZMod 7) = 1 from rfl]
      exact map_one F'.ι
    rw [h0]
    exact map_one φ
  have hιT_add : ∀ a b : Fin 3 → ZMod 7, ιT (a + b) = ιT a * ιT b := by
    intro a b
    change φ ⟨F'.ι (ofAdd (a + b)), hAΩ (F'.mem _)⟩ =
      φ ⟨F'.ι (ofAdd a), hAΩ (F'.mem _)⟩ * φ ⟨F'.ι (ofAdd b), hAΩ (F'.mem _)⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show F'.ι (ofAdd (a + b)) = F'.ι (ofAdd a) * F'.ι (ofAdd b)
    rw [show ofAdd (a + b) = ofAdd a * ofAdd b from rfl, map_mul]
  have hιT_inj : Function.Injective ιT := by
    intro a b hab
    have h1 : (⟨F'.ι (ofAdd a), hAΩ (F'.mem _)⟩ : ↥omΩ) =
        ⟨F'.ι (ofAdd b), hAΩ (F'.mem _)⟩ := hinj hab
    have h2 : F'.ι (ofAdd a) = F'.ι (ofAdd b) := congrArg Subtype.val h1
    exact Multiplicative.ofAdd.injective (F'.inj h2)
  have hιT_range : (Set.range ιT : Set G) = (Bs ⊓ L : Subgroup G) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨hιT_mem t, hιT_mem_L t⟩
    · intro hy
      obtain ⟨hyB, hyL⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hyL)
      have haA : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs := by
        refine ⟨a, ?_, rfl⟩
        exact Subgroup.mem_comap.mpr (by rw [ha]; exact hyB)
      obtain ⟨s, hs⟩ := F'.exists_eq haA
      refine ⟨Multiplicative.toAdd s, ?_⟩
      change φ ⟨F'.ι s, hAΩ (F'.mem _)⟩ = y
      have h1 : (⟨F'.ι s, hAΩ (F'.mem _)⟩ : ↥omΩ) = a := Subtype.ext hs
      rw [h1]
      exact ha
  have hbot_xL : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyx, hyL⟩ := Subgroup.mem_inf.mp hy
    exact om3_eq_one_of_mem_centralizer_of_center_eq_bot hZL hyL
      ((Subgroup.zpowers_le.mpr hxcent) hyx)
  let ΦFun : (Fin 4 → ZMod 7) → ↥Bs := fun v =>
    ⟨x ^ (v 0).val * ιT (Fin.tail v), Bs.mul_mem (Bs.pow_mem hxBs _) (hιT_mem _)⟩
  have hΦFun_zero : ΦFun 0 = 1 := by
    apply Subtype.ext
    simp only [ΦFun, Pi.zero_apply, ZMod.val_zero, pow_zero, one_mul]
    have htail : Fin.tail (0 : Fin 4 → ZMod 7) = 0 := by funext i; rfl
    rw [htail, hιT_zero]
    rfl
  have hΦFun_add : ∀ v w : Fin 4 → ZMod 7, ΦFun (v + w) = ΦFun v * ΦFun w := by
    intro v w
    apply Subtype.ext
    simp only [ΦFun, Subgroup.coe_mul]
    have hpv : x ^ ((v + w) 0).val = x ^ (v 0).val * x ^ (w 0).val := by
      rw [show (v + w) 0 = v 0 + w 0 from rfl]
      exact om3_pow_val_add hx7 (v 0) (w 0)
    have htv : Fin.tail (v + w) = Fin.tail v + Fin.tail w := by funext i; rfl
    rw [hpv, htv, hιT_add]
    have hcommvw : Commute (x ^ (w 0).val) (ιT (Fin.tail v)) :=
      (show Commute (ιT (Fin.tail v)) x from
        Subgroup.mem_centralizer_iff.mp hxcent (ιT (Fin.tail v)) (hιT_mem_L _)).symm.pow_left _
    calc x ^ (v 0).val * x ^ (w 0).val * (ιT (Fin.tail v) * ιT (Fin.tail w))
        = x ^ (v 0).val * (x ^ (w 0).val * ιT (Fin.tail v)) * ιT (Fin.tail w) := by group
      _ = x ^ (v 0).val * (ιT (Fin.tail v) * x ^ (w 0).val) * ιT (Fin.tail w) := by
            rw [hcommvw.eq]
      _ = x ^ (v 0).val * ιT (Fin.tail v) * (x ^ (w 0).val * ιT (Fin.tail w)) := by group
  let Φ : (Fin 4 → ZMod 7) →+ Additive ↥Bs :=
    { toFun := fun v => Additive.ofMul (ΦFun v)
      map_zero' := by
        change Additive.ofMul (ΦFun 0) = (0 : Additive ↥Bs)
        rw [hΦFun_zero]; rfl
      map_add' := fun v w => by
        change Additive.ofMul (ΦFun (v + w)) =
          Additive.ofMul (ΦFun v) + Additive.ofMul (ΦFun w)
        rw [hΦFun_add]; rfl }
  have hsurjΦ : Function.Surjective Φ := by
    intro b
    let b' : ↥Bs := Additive.toMul b
    obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b' b'.2
    have he_range : e ∈ Set.range ιT := by rw [hιT_range]; exact he
    obtain ⟨t, ht⟩ := he_range
    have hc' : c ∈ Subgroup.zpowers x := by
      rw [← hcfg.bstar_inf_centralizer_L]; exact hc
    obtain ⟨k, hk⟩ := om3_exists_nat_pow hordx hc'
    refine ⟨Fin.cons (k : ZMod 7) t, ?_⟩
    change ΦFun (Fin.cons (k : ZMod 7) t) = b'
    apply Subtype.ext
    simp only [ΦFun, Fin.cons_zero, Fin.tail_cons]
    have hkmod : x ^ (k % 7) = x ^ k := by
      conv_rhs => rw [← Nat.mod_add_div k 7]
      rw [pow_add, pow_mul, hx7, one_pow, mul_one]
    have hkval : x ^ ((k : ZMod 7)).val = c := by
      rw [ZMod.val_natCast, hkmod, hk]
    have heL : e ∈ L := (Subgroup.mem_inf.mp he).2
    calc x ^ ((k : ZMod 7)).val * ιT t
        = c * e := by rw [hkval, ht]
      _ = e * c := (Subgroup.mem_centralizer_iff.mp hc.2 e heL).symm
      _ = b' := hbc.symm
  have hinjΦ : Function.Injective Φ := by
    intro v w hvw
    have hzero : Φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : ΦFun (v - w) = 1 := by
      have h := congrArg Additive.toMul hzero
      simpa [Φ] using h
    have hcoe : x ^ ((v - w) 0).val * ιT (Fin.tail (v - w)) = 1 := by
      have h := congrArg (fun z : ↥Bs => (z : G)) h1
      simpa [ΦFun] using h
    have hxL : x ^ ((v - w) 0).val ∈ L := by
      have h1' : x ^ ((v - w) 0).val = (ιT (Fin.tail (v - w)))⁻¹ :=
        eq_inv_of_mul_eq_one_left hcoe
      rw [h1']
      exact L.inv_mem (hιT_mem_L _)
    have hxz : x ^ ((v - w) 0).val ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr
        ⟨(((v - w) 0).val : ℤ), by rw [zpow_natCast]⟩
    have hx1 : x ^ ((v - w) 0).val = 1 := by
      have hmem : x ^ ((v - w) 0).val ∈ Subgroup.zpowers x ⊓ L :=
        Subgroup.mem_inf.mpr ⟨hxz, hxL⟩
      rw [hbot_xL, Subgroup.mem_bot] at hmem
      exact hmem
    have hval : ((v - w) 0).val = 0 := by
      have hdvd : 7 ∣ ((v - w) 0).val := by
        have := orderOf_dvd_of_pow_eq_one hx1
        rwa [hordx] at this
      have hlt := ZMod.val_lt ((v - w) 0)
      omega
    have h0 : (v - w) 0 = 0 := (ZMod.val_eq_zero _).mp hval
    have htail1 : ιT (Fin.tail (v - w)) = 1 := by
      rw [hx1, one_mul] at hcoe
      exact hcoe
    have htail0 : Fin.tail (v - w) = 0 :=
      hιT_inj (by rw [htail1, hιT_zero])
    have hsub0 : v - w = 0 := by
      have h := Fin.cons_self_tail (v - w)
      rw [h0, htail0] at h
      have h00 : (Fin.cons 0 0 : Fin 4 → ZMod 7) = 0 := by funext i; fin_cases i <;> rfl
      rw [h00] at h
      exact h.symm
    exact sub_eq_zero.mp hsub0
  let Φe : (Fin 4 → ZMod 7) ≃+ Additive ↥Bs :=
    AddEquiv.ofBijective Φ ⟨hinjΦ, hsurjΦ⟩
  let ιB : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) := Φe.symm
  have hιB_PhiFun : ∀ v : Fin 4 → ZMod 7, ιB (Additive.ofMul (ΦFun v)) = v := by
    intro v
    change Φe.symm (Φ v) = v
    exact Φe.symm_apply_apply v
  have hιB_x : ιB (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 0 1 := by
    have hsingle : Φ (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) =
        Additive.ofMul ⟨x, hxBs⟩ := by
      change ΦFun (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) = ⟨x, hxBs⟩
      apply Subtype.ext
      have htail : Fin.tail (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) = 0 := by
        funext i
        rw [Fin.tail]
        exact Pi.single_eq_of_ne (by simp) 1
      haveI : Fact (1 < 7) := ⟨by norm_num⟩
      simp only [ΦFun, Pi.single_eq_same, htail, hιT_zero, ZMod.val_one]
      rw [pow_one, mul_one]
    exact (Φe.symm_apply_eq).mpr hsingle.symm
  have hιB_t : ∀ t : Fin 3 → ZMod 7,
      ∃ hb : φ ⟨F'.ι (ofAdd t), omA_le φ Bs (F'.mem _)⟩ ∈ Bs,
        ιB (Additive.ofMul ⟨φ ⟨F'.ι (ofAdd t), omA_le φ Bs (F'.mem _)⟩, hb⟩) =
          (Fin.cons 0 t : Fin 4 → ZMod 7) := by
    intro t
    refine ⟨hιT_mem t, ?_⟩
    have hsingle_t : Φ (Fin.cons 0 t) = Additive.ofMul ⟨ιT t, hιT_mem t⟩ := by
      change ΦFun (Fin.cons 0 t) = ⟨ιT t, hιT_mem t⟩
      apply Subtype.ext
      simp only [ΦFun, Fin.cons_zero, Fin.tail_cons, ZMod.val_zero, pow_zero, one_mul]
    change ιB (Additive.ofMul ⟨ιT t, hιT_mem t⟩) = Fin.cons 0 t
    exact (Φe.symm_apply_eq).mpr hsingle_t.symm
  have hmovesFinal : ∀ (π : Equiv.Perm (Fin 3)) (η' : Fin 3 → (ZMod 7)ˣ),
      (∀ i, η' i ∈ CoordSp.signs 7) →
      ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
        ιB (Additive.ofMul (ψ b)) =
          (Fin.cons (ιB (Additive.ofMul b) 0)
            (fun i : Fin 3 => (η' i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) :
            Fin 4 → ZMod 7) := by
    intro π η' hη'
    obtain ⟨w, hw, hws⟩ := hmo' π η' hη'
    have hwΩ : w ∈ omΩ := hw.1
    let wG : G := φ ⟨w, hwΩ⟩
    have hwL : wG ∈ L := by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨⟨w, hwΩ⟩, rfl⟩
    have hmem : ∀ e ∈ (Bs ⊓ L : Subgroup G), wG * e * wG⁻¹ ∈ (Bs ⊓ L : Subgroup G) := by
      intro e he
      have he' : e ∈ Set.range ιT := by rw [hιT_range]; exact he
      obtain ⟨t, rfl⟩ := he'
      have hwtA : w * F'.ι (ofAdd t) * w⁻¹ ∈ omA φ Bs :=
        (Subgroup.mem_normalizer_iff.mp hw.2 (F'.ι (ofAdd t))).mp (F'.mem _)
      have hprod : (⟨w * F'.ι (ofAdd t) * w⁻¹, hAΩ hwtA⟩ : ↥omΩ) =
          ⟨w, hwΩ⟩ * ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * ⟨w, hwΩ⟩⁻¹ := Subtype.ext rfl
      have h1 : wG * ιT t * wG⁻¹ = φ ⟨w * F'.ι (ofAdd t) * w⁻¹, hAΩ hwtA⟩ := by
        rw [hprod]
        change φ ⟨w, hwΩ⟩ * φ ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * (φ ⟨w, hwΩ⟩)⁻¹ =
          φ (⟨w, hwΩ⟩ * ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * ⟨w, hwΩ⟩⁻¹)
        simp only [map_mul, map_inv]
      rw [h1]
      exact Subgroup.mem_inf.mpr
        ⟨hφA_mem _ hwtA, h1 ▸ L.mul_mem (L.mul_mem hwL (hιT_mem_L t)) (L.inv_mem hwL)⟩
    have hmem_inv : ∀ e ∈ (Bs ⊓ L : Subgroup G), wG⁻¹ * e * wG ∈ (Bs ⊓ L : Subgroup G) := by
      intro e he
      have he' : e ∈ Set.range ιT := by rw [hιT_range]; exact he
      obtain ⟨t, rfl⟩ := he'
      have hwtA : w⁻¹ * F'.ι (ofAdd t) * w ∈ omA φ Bs := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw.2)
          (F'.ι (ofAdd t))).mp (F'.mem _)
        simpa [inv_inv] using h
      have hprod : (⟨w⁻¹ * F'.ι (ofAdd t) * w, hAΩ hwtA⟩ : ↥omΩ) =
          ⟨w, hwΩ⟩⁻¹ * ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * ⟨w, hwΩ⟩ := Subtype.ext rfl
      have h1 : wG⁻¹ * ιT t * wG = φ ⟨w⁻¹ * F'.ι (ofAdd t) * w, hAΩ hwtA⟩ := by
        rw [hprod]
        change (φ ⟨w, hwΩ⟩)⁻¹ * φ ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * φ ⟨w, hwΩ⟩ =
          φ (⟨w, hwΩ⟩⁻¹ * ⟨F'.ι (ofAdd t), hAΩ (F'.mem _)⟩ * ⟨w, hwΩ⟩)
        simp only [map_mul, map_inv]
      rw [h1]
      exact Subgroup.mem_inf.mpr
        ⟨hφA_mem _ hwtA, h1 ▸ L.mul_mem (L.mul_mem (L.inv_mem hwL) (hιT_mem_L t)) hwL⟩
    have hwE : wG ∈ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      exact ⟨hmem e, fun he => by
        have h2 := hmem_inv (wG * e * wG⁻¹) he
        rwa [show wG⁻¹ * (wG * e * wG⁻¹) * wG = e by group] at h2⟩
    have hcomm_xw : wG * x = x * wG := Subgroup.mem_centralizer_iff.mp hxcent wG hwL
    have hwx : wG * x * wG⁻¹ = x := by rw [hcomm_xw]; group
    have hwNx : wG ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := om3_exists_nat_pow hordx hy
        have h2 : wG * x ^ k * wG⁻¹ = x ^ k := by
          rw [(show Commute wG x from hcomm_xw).pow_right k]
          group
        rw [← hk, h2]
        exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by rw [zpow_natCast]⟩
      · intro hy
        obtain ⟨k, hk⟩ := om3_exists_nat_pow hordx hy
        have h2 : wG⁻¹ * x ^ k * wG = x ^ k := by
          rw [(show Commute wG x from hcomm_xw).inv_left.pow_right k]
          group
        have hyk : y = x ^ k := by
          calc y = wG⁻¹ * (wG * y * wG⁻¹) * wG := by group
            _ = wG⁻¹ * x ^ k * wG := by rw [← hk]
            _ = x ^ k := h2
        rw [hyk]
        exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by rw [zpow_natCast]⟩
    have hBs_eq : Bs = (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
      apply le_antisymm
      · intro b hb
        obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b hb
        have hc' : c ∈ Subgroup.zpowers x := by
          rw [← hcfg.bstar_inf_centralizer_L]; exact hc
        rw [hbc]
        exact ((Bs ⊓ L) ⊔ Subgroup.zpowers x).mul_mem
          (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hc')
      · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxBs)
    have hwN : wG ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [hBs_eq]
      exact Subgroup.inf_normalizer_le_normalizer_sup (Bs ⊓ L) (Subgroup.zpowers x)
        ⟨hwE, hwNx⟩
    have hwN' : wG⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hwN
    refine ⟨ggConjAut Bs hwN', ggConjAut_mem_ggAutomizer (H := L) (L.inv_mem hwL) hwN',
      fun b => ?_⟩
    set v : Fin 4 → ZMod 7 := ιB (Additive.ofMul b) with hv
    have hvPhi : Φ (ιB (Additive.ofMul b)) = Additive.ofMul b :=
      Φe.apply_symm_apply (Additive.ofMul b)
    have hb_eq : ΦFun v = b := hvPhi
    have hws_v : wG⁻¹ * ιT (Fin.tail v) * wG =
        ιT (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i)) := by
      have h0 := hws (Fin.tail v)
      have h1 : (⟨w, hwΩ⟩ : ↥omΩ)⁻¹ * ⟨F'.ι (ofAdd (Fin.tail v)), hAΩ (F'.mem _)⟩ *
            ⟨w, hwΩ⟩ =
          ⟨F'.ι (ofAdd fun i => (η' i : ZMod 7) * (Fin.tail v) (π i)), hAΩ (F'.mem _)⟩ :=
        Subtype.ext h0
      have h2 := congrArg φ h1
      simp only [map_mul, map_inv] at h2
      simpa [wG, ιT] using h2
    have hact : ggConjAut Bs hwN' (ΦFun v) =
        ΦFun (Fin.cons (v 0) (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i))) := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      simp only [ΦFun, Subgroup.coe_mk, inv_inv]
      rw [Fin.cons_zero, Fin.tail_cons]
      have hwxpow : wG⁻¹ * x ^ (v 0).val * wG = x ^ (v 0).val := by
        have hc : Commute (x ^ (v 0).val) wG :=
          (show Commute x wG from hcomm_xw.symm).pow_left (v 0).val
        calc wG⁻¹ * x ^ (v 0).val * wG = wG⁻¹ * (x ^ (v 0).val * wG) := by group
          _ = wG⁻¹ * (wG * x ^ (v 0).val) := by rw [hc.eq]
          _ = x ^ (v 0).val := by group
      calc wG⁻¹ * (x ^ (v 0).val * ιT (Fin.tail v)) * wG
          = (wG⁻¹ * x ^ (v 0).val * wG) * (wG⁻¹ * ιT (Fin.tail v) * wG) := by group
        _ = x ^ (v 0).val * ιT (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i)) := by
              rw [hwxpow, hws_v]
    have hφb : ggConjAut Bs hwN' b =
        ΦFun (Fin.cons (v 0) (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i))) := by
      rw [← hb_eq]
      exact hact
    calc ιB (Additive.ofMul (ggConjAut Bs hwN' b))
        = ιB (Additive.ofMul (ΦFun (Fin.cons (v 0)
            (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i))))) := by rw [hφb]
      _ = Fin.cons (v 0) (fun i : Fin 3 => (η' i : ZMod 7) * (Fin.tail v) (π i)) :=
            hιB_PhiFun _
      _ = Fin.cons (ιB (Additive.ofMul b) 0)
            (fun i : Fin 3 => (η' i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) := by
            rw [hv]
            funext j
            fin_cases j <;> simp [Fin.tail]
  exact ⟨F', ζ, β, hmaxA, hζo, hdim', hal', hmo', hβal, hφβ, ιB, hιB_x, hιB_t, hmovesFinal⟩

end A8Coord

end CFSG.StandardType

end
