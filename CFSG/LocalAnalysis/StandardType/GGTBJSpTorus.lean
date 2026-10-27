module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpCore
public import CFSG.LocalAnalysis.StandardType.GGTBJSpModel
public import CFSG.LocalAnalysis.StandardType.GGTBJLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly TableBSymp CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial

private theorem ggTBJ_card_fin_zmod (p m : ℕ) :
    Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m := by
  rw [← Nat.card_congr (MulEquiv.piMultiplicative (fun _ : Fin m => ZMod p)).toEquiv,
    CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod]

private theorem ggTBJ_map_conj_centralizer {G : Type*} [Group G] (g a : G) :
    (Subgroup.centralizer ({g * a * g⁻¹} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
      = Subgroup.centralizer ({a} : Set G) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change (MulAut.conj g⁻¹) y * a = a * (MulAut.conj g⁻¹) y
    rw [MulAut.conj_apply]
    calc g⁻¹ * y * g⁻¹⁻¹ * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hy]
      _ = a * (g⁻¹ * y * g⁻¹⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hx]
        _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
    · change (MulAut.conj g⁻¹) (g * x * g⁻¹) = x
      rw [MulAut.conj_apply]
      group

private theorem ggTBJ_map_centralizer_singleton_mulEquiv {M M' : Type*} [Group M] [Group M']
    (φ : M ≃* M') (t : M) :
    (Subgroup.centralizer ({t} : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ t} : Set M') := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change φ y * φ t = φ t * φ y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.mpr ⟨φ.symm x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
    · simp

theorem ggTBJ_sp_component_model {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L']
    [Finite L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1) (x : LargeEvenProj (LargeEvenSpGroup K m))
      (σ : (Fin m → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A)
      (e : LargeEvenSpGroup K m ≃* LargeEvenProj (LargeEvenSpGroup K m))
      (J₀ : Subgroup (LargeEvenSpGroup K m)),
      orderOf ζ = p ∧ (∀ f, ψ₀ (σ f) = x * spTorus hζ f * x⁻¹) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ f, e (spTorusSp hζ f) = spTorus hζ f) ∧
      J₀.map e.toMonoidHom = (J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom ∧
      CFSG.Assembly.IsComponentOf J₀ (Subgroup.centralizer
        ({spTorusSp hζ (Θ.symm ⟨y, hy⟩)} : Set (LargeEvenSpGroup K m))) ∧
      p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f} ≤ p ^ m := by
  classical
  obtain ⟨ζ, hζ, x, σ, Θ, hζo, hψσ, hΘ, hWeyl⟩ := ggTBJ_sp_stdModel hp hp2 hpq ψ₀ A hA
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f₀ : Fin m → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := MulEquiv.apply_symm_apply Θ _
  have hy_eq : y = MulAut.conj (σ f₀) := by
    have h := hΘ f₀
    rw [hΘf₀] at h
    exact h
  have hfix : fixSubgroup y = Subgroup.centralizer ({σ f₀} : Set L') := by
    rw [hy_eq]; exact ggTBJ_fixSubgroup_conj (σ f₀)
  have hJcent : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')) := by
    rw [hfix] at hJ
    exact hJ
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (σ f₀))) := by
    rw [ggTBJ_fixSubgroup_conj]
    exact hJcent
  have hJgg : CFSG.Assembly.IsComponentOf J (ggFix (MulAut.conj (σ f₀))) :=
    (isComponentOf_iff_open).mpr hJ'
  have hc : ∀ l : L', MulAut.conj (ψ₀ (σ f₀)) (ψ₀ l) = ψ₀ (MulAut.conj (σ f₀) l) := by
    intro l
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hSfix : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (fixSubgroup (MulAut.conj (ψ₀ (σ f₀)))) :=
    USixTwo.isComponentOf_map_fix hA.1 hA.2.1 hc hJgg
  have hScent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (Subgroup.centralizer ({ψ₀ (σ f₀)} : Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
    have h := hSfix
    rw [ggTBJ_fixSubgroup_conj] at h
    exact h
  let e : LargeEvenSpGroup K m ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m)) (by
      rw [show LargeEvenProjMk (LargeEvenSpGroup K m) = SymplecticFlag.proj m K from rfl]
      exact UnitaryHigher.proj_bijective_of_charTwo)
  let S' : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
    (J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom
  let J₀ : Subgroup (LargeEvenSpGroup K m) := S'.comap e.toMonoidHom
  have hmap : J₀.map e.toMonoidHom = S' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective S'
  have hSx : CFSG.Assembly.IsComponentOf S'
      (Subgroup.centralizer ({spTorus hζ f₀} : Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
    have hcent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
        (Subgroup.centralizer ({x * spTorus hζ f₀ * x⁻¹} :
          Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
      rwa [hψσ f₀] at hScent
    have h := isComponentOf_map_of_injective (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective hcent
    rw [ggTBJ_map_conj_centralizer x (spTorus hζ f₀)] at h
    exact h
  have hJ₀ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spTorusSp hζ f₀} : Set (LargeEvenSpGroup K m))) := by
    apply (isComponentOf_map_iff e.injective).mp
    change CFSG.Assembly.IsComponentOf (J₀.map e.toMonoidHom)
      ((Subgroup.centralizer ({spTorusSp hζ f₀} : Set (LargeEvenSpGroup K m))).map
        e.toMonoidHom)
    rw [hmap, ggTBJ_map_centralizer_singleton_mulEquiv e (spTorusSp hζ f₀)]
    exact hSx
  let B : Subgroup (MulAut L') := A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')
  have hcardB : Nat.card ↥B = Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} := by
    refine Nat.card_congr ?_
    let toF : ↥B → {f : Fin m → Multiplicative (ZMod p) //
        ∀ j ∈ J, σ f * j = j * σ f} := fun b =>
      let f : Fin m → Multiplicative (ZMod p) :=
        Θ.symm ⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩
      ⟨f, by
        intro j hj
        have hbj : (b : MulAut L') j = j := by
          have h := MulAction.mem_stabilizer_iff.mp
            (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
          simpa [MulAut.smul_def] using h
        have hbf : (b : MulAut L') = MulAut.conj (σ f) := by
          have hfA : Θ f = (⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
            MulEquiv.apply_symm_apply Θ _
          rw [← hΘ f]
          exact (congrArg Subtype.val hfA).symm
        rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
        exact hbj⟩
    let toG : {f : Fin m → Multiplicative (ZMod p) // ∀ j ∈ J, σ f * j = j * σ f} → ↥B :=
      fun c => ⟨((Θ c.1 : ↥A) : MulAut L'), by
        refine Subgroup.mem_inf.mpr ⟨(Θ c.1).2, ?_⟩
        rw [Subgroup.mem_iInf]
        intro j
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hΘ, MulAut.conj_apply]
        have hcomm := c.2 j j.2
        rw [hcomm]
        group⟩
    refine ⟨toF, toG, ?_, ?_⟩
    · intro b
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.apply_symm_apply]
    · intro c
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.symm_apply_eq]
  have hcardA : Nat.card ↥A = p ^ m := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact ggTBJ_card_fin_zmod p m
  have hcount' : p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ m := by
    rw [← hcardB, ← hcardA]
    exact hcount
  have hiff : ∀ f : Fin m → Multiplicative (ZMod p),
      (∀ j ∈ J, σ f * j = j * σ f) ↔
        (∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f) := by
    intro f
    have hJperf : ⁅J, J⁆ = J := by
      rw [← Subgroup.map_subtype_commutator, hJgg.2.2.1, Subgroup.map_top,
        Subgroup.range_subtype]
    have step1 : (∀ j ∈ J, σ f * j = j * σ f) ↔
        ∀ s ∈ J.map ψ₀, ψ₀ (σ f) * s = s * ψ₀ (σ f) := by
      constructor
      · intro h s hs
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hs
        rw [← map_mul, ← map_mul, h j hj]
      · intro h j hj
        have hker : ∀ t ∈ J, MulAut.conj (σ f) t * t⁻¹ ∈ ψ₀.ker := by
          intro t ht
          rw [MonoidHom.mem_ker]
          have htS : ψ₀ t ∈ J.map ψ₀ := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
          have hcomm : ψ₀ t * ψ₀ (σ f) = ψ₀ (σ f) * ψ₀ t := (h (ψ₀ t) htS).symm
          rw [MulAut.conj_apply]
          rw [map_mul, map_inv, map_mul, map_mul, map_inv]
          calc ψ₀ (σ f) * ψ₀ t * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹
              = ψ₀ t * ψ₀ (σ f) * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹ := by rw [← hcomm]
            _ = 1 := by group
        have hfixj := USixTwo.fix_of_perfect hA.2.1 hJperf hker j hj
        rw [MulAut.conj_apply] at hfixj
        exact mul_inv_eq_iff_eq_mul.mp hfixj
    have step2 : (∀ s ∈ J.map ψ₀, ψ₀ (σ f) * s = s * ψ₀ (σ f)) ↔
        ∀ t ∈ S', spTorus hζ f * t = t * spTorus hζ f := by
      constructor
      · intro h t ht
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
        have hconj := h s hs
        rw [hψσ f] at hconj
        change spTorus hζ f * (MulAut.conj x⁻¹) s =
          (MulAut.conj x⁻¹) s * spTorus hζ f
        rw [MulAut.conj_apply]
        calc spTorus hζ f * (x⁻¹ * s * x⁻¹⁻¹)
            = x⁻¹ * ((x * spTorus hζ f * x⁻¹) * s) * x := by group
          _ = x⁻¹ * (s * (x * spTorus hζ f * x⁻¹)) * x := by rw [hconj]
          _ = x⁻¹ * s * x⁻¹⁻¹ * spTorus hζ f := by group
      · intro h s hs
        have hs' : (MulAut.conj x⁻¹).toMonoidHom s ∈ S' :=
          Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
        have hconj := h _ hs'
        rw [hψσ f]
        change x * spTorus hζ f * x⁻¹ * s = s * (x * spTorus hζ f * x⁻¹)
        have hconj' : spTorus hζ f * (MulAut.conj x⁻¹) s =
            (MulAut.conj x⁻¹) s * spTorus hζ f := hconj
        rw [MulAut.conj_apply] at hconj'
        calc x * spTorus hζ f * x⁻¹ * s
            = x * (spTorus hζ f * (x⁻¹ * s * x⁻¹⁻¹)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * s * x⁻¹⁻¹) * spTorus hζ f) * x⁻¹ := by rw [hconj']
          _ = s * (x * spTorus hζ f * x⁻¹) := by group
    have step3 : (∀ t ∈ S', spTorus hζ f * t = t * spTorus hζ f) ↔
        ∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f := by
      have heD : e.toMonoidHom (spTorusSp hζ f) = spTorus hζ f := rfl
      constructor
      · intro h j₀ hj₀
        have ht : e.toMonoidHom j₀ ∈ S' := by
          rw [← hmap]
          exact Subgroup.mem_map.mpr ⟨j₀, hj₀, rfl⟩
        have hconj := h (e.toMonoidHom j₀) ht
        refine e.injective ?_
        calc e.toMonoidHom (spTorusSp hζ f * j₀)
            = e.toMonoidHom (spTorusSp hζ f) * e.toMonoidHom j₀ :=
              map_mul e.toMonoidHom _ _
          _ = spTorus hζ f * e.toMonoidHom j₀ := by rw [heD]
          _ = e.toMonoidHom j₀ * spTorus hζ f := hconj
          _ = e.toMonoidHom j₀ * e.toMonoidHom (spTorusSp hζ f) := by rw [heD]
          _ = e.toMonoidHom (j₀ * spTorusSp hζ f) :=
              (map_mul e.toMonoidHom _ _).symm
      · intro h t ht
        have ht' : t ∈ J₀.map e.toMonoidHom := by rw [hmap]; exact ht
        obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp ht'
        rw [← heD, ← map_mul, ← map_mul, h j₀ hj₀]
    exact step1.trans (step2.trans step3)
  have hPQ : Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} =
      Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have hcount_core : p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f} ≤ p ^ m := by
    rw [← hPQ]
    exact hcount'
  refine ⟨ζ, hζ, x, σ, Θ, e, J₀, hζo, hψσ, hΘ, hWeyl, ?_, hmap, hJ₀, hcount_core⟩
  intro f
  rfl

theorem ggTBJ_sp_inner_model {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L']
    [Finite L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1)
      (ν : LargeEvenSpGroup K m →* MulAut L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A)
      (J₀ : Subgroup (LargeEvenSpGroup K m)),
      orderOf ζ = p ∧ Function.Injective ν ∧
      ν.range = (MulAut.conj : L' →* MulAut L').range ∧
      (∀ f, ν (spTorusSp hζ f) = (Θ f : MulAut L')) ∧
      (spTorusSp (m := m) hζ).range.map ν = A ∧
      J₀.map ν = J.map (MulAut.conj : L' →* MulAut L') ∧
      CFSG.Assembly.IsComponentOf J₀ (Subgroup.centralizer
        ({spTorusSp hζ (Θ.symm ⟨y, hy⟩)} : Set (LargeEvenSpGroup K m))) ∧
      (p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f} ≤ p ^ m) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  obtain ⟨ζ, hζ, x, σ, Θ, e, J₀, hζo, hψσ, hΘ, hWeyl, hproj, hmap, hJ₀, hcount_core⟩ :=
    ggTBJ_sp_component_model hp hp2 hpq ψ₀ A hA y hy hJ hcount
  let Λ : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut L' :=
    ReflInner.liftConj ψ₀ hA.1 hA.2.1
  have hΛeq {z : LargeEvenProj (LargeEvenSpGroup K m)} {n : L'}
      (hn : ψ₀ n = z) : Λ z = MulAut.conj n := ReflInner.liftConj_eq hA.1 hA.2.1 hn
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hA.1 hA.2.1
    (center_spProj_eq_bot (K := K) (m := m))
  let ν : LargeEvenSpGroup K m →* MulAut L' :=
    Λ.comp ((MulAut.conj x).toMonoidHom.comp e.toMonoidHom)
  have hνval (g : LargeEvenSpGroup K m) : ν g = Λ (x * e g * x⁻¹) := rfl
  have hνinj : Function.Injective ν := hΛinj.comp ((MulAut.conj x).injective.comp e.injective)
  have hνlift (n : L') : ν (e.symm (x⁻¹ * ψ₀ n * x)) = MulAut.conj n := by
    rw [hνval, e.apply_symm_apply]
    have h : x * (x⁻¹ * ψ₀ n * x) * x⁻¹ = ψ₀ n := by group
    rw [h]
    exact hΛeq rfl
  have hνrange : ν.range = (MulAut.conj : L' →* MulAut L').range := by
    apply le_antisymm
    · rintro a ⟨g, rfl⟩
      obtain ⟨n, hn⟩ := hA.1 (x * e g * x⁻¹)
      exact ⟨n, (hΛeq hn).symm⟩
    · rintro a ⟨n, rfl⟩
      exact ⟨e.symm (x⁻¹ * ψ₀ n * x), hνlift n⟩
  have hνtorus : ∀ f, ν (spTorusSp hζ f) = (Θ f : MulAut L') := by
    intro f
    rw [hνval, hproj f]
    exact (hΛeq (hψσ f)).trans (hΘ f).symm
  have hAmap : (spTorusSp (m := m) hζ).range.map ν = A := by
    ext a
    constructor
    · rintro ⟨g, ⟨f, rfl⟩, rfl⟩
      rw [hνtorus]
      exact (Θ f).2
    · intro ha
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      exact ⟨spTorusSp hζ f, ⟨f, rfl⟩, (hνtorus f).trans (congrArg Subtype.val hf)⟩
  have hJmap : J₀.map ν = J.map (MulAut.conj : L' →* MulAut L') := by
    apply le_antisymm
    · rintro a ⟨g, hg, rfl⟩
      have heg : e g ∈ (J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom := by
        rw [← hmap]
        exact ⟨g, hg, rfl⟩
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp heg
      obtain ⟨j, hj, hju⟩ := Subgroup.mem_map.mp hu
      have hψj : ψ₀ j = x * e g * x⁻¹ := by
        rw [hju, ← hue]
        change u = x * (MulAut.conj x⁻¹) u * x⁻¹
        rw [MulAut.conj_apply]
        group
      exact ⟨j, hj, (hΛeq hψj).symm⟩
    · rintro a ⟨j, hj, rfl⟩
      let g : LargeEvenSpGroup K m := e.symm (x⁻¹ * ψ₀ j * x)
      have heg : e g ∈ J₀.map e.toMonoidHom := by
        rw [hmap]
        refine ⟨ψ₀ j, ⟨j, hj, rfl⟩, ?_⟩
        simp [g, MulAut.conj_apply]
      have hg : g ∈ J₀ := (Subgroup.mem_map_iff_mem e.injective).mp heg
      exact ⟨g, hg, hνlift j⟩
  exact ⟨ζ, hζ, ν, Θ, J₀, hζo, hνinj, hνrange, hνtorus, hAmap, hJmap,
    hJ₀, hcount_core, hWeyl⟩

theorem ggTBJ_sp_torusJNoncomm {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L']
    [Finite L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  obtain ⟨ζ, hζ, x, σ, Θ, e, J₀, hζo, hψσ, hΘ, hWeyl, hproj, hmap, hJ₀, hcount_core⟩ :=
    ggTBJ_sp_component_model hp hp2 hpq ψ₀ A hA y hy hJ hcount
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f₀ : Fin m → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  let S' : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
    (J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom
  have hmapS : J₀.map e.toMonoidHom = S' := hmap
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      haveI : Nontrivial K := ⟨0, 1, zero_ne_one⟩
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpos : 0 < Nat.card K - 1 := by omega
    have hle := Nat.le_of_dvd hpos hpq
    omega
  obtain ⟨n₁, n₂, s₁, s₂, hn₁, hn₂, hform₁, hform₂, hs₁, hs₂, hfix₁, hfix₂, hne⟩ :=
    ggTBJ_sp_core hp hp2 hK4 hζo hζ f₀ hJ₀ hcount_core
  have hmem₁ : e n₁ ∈ S' := by
    rw [← hmapS]
    exact Subgroup.mem_map.mpr ⟨n₁, hn₁, rfl⟩
  obtain ⟨u₁, hu₁, hu₁eq⟩ := Subgroup.mem_map.mp hmem₁
  obtain ⟨l₁, hl₁J, hl₁eq⟩ := Subgroup.mem_map.mp hu₁
  have hψl₁ : ψ₀ l₁ = x * e n₁ * x⁻¹ := by
    rw [hl₁eq, ← hu₁eq]
    change u₁ = x * (MulAut.conj x⁻¹) u₁ * x⁻¹
    rw [MulAut.conj_apply]
    group
  have hmem₂ : e n₂ ∈ S' := by
    rw [← hmapS]
    exact Subgroup.mem_map.mpr ⟨n₂, hn₂, rfl⟩
  obtain ⟨u₂, hu₂, hu₂eq⟩ := Subgroup.mem_map.mp hmem₂
  obtain ⟨l₂, hl₂J, hl₂eq⟩ := Subgroup.mem_map.mp hu₂
  have hψl₂ : ψ₀ l₂ = x * e n₂ * x⁻¹ := by
    rw [hl₂eq, ← hu₂eq]
    change u₂ = x * (MulAut.conj x⁻¹) u₂ * x⁻¹
    rw [MulAut.conj_apply]
    group
  have hψform₁ : ∀ f, ψ₀ l₁ * ψ₀ (σ f) * (ψ₀ l₁)⁻¹ = ψ₀ (σ (s₁ f)) := by
    intro f
    rw [hψl₁, hψσ f, hψσ (s₁ f)]
    have heq := congrArg e (hform₁ f)
    rw [map_mul, map_mul, map_inv] at heq
    rw [hproj f,
      hproj (s₁ f)] at heq
    calc x * e n₁ * x⁻¹ * (x * spTorus hζ f * x⁻¹) * (x * e n₁ * x⁻¹)⁻¹
        = x * (e n₁ * spTorus hζ f * (e n₁)⁻¹) * x⁻¹ := by group
      _ = x * spTorus hζ (s₁ f) * x⁻¹ := by rw [heq]
  have hψform₂ : ∀ f, ψ₀ l₂ * ψ₀ (σ f) * (ψ₀ l₂)⁻¹ = ψ₀ (σ (s₂ f)) := by
    intro f
    rw [hψl₂, hψσ f, hψσ (s₂ f)]
    have heq := congrArg e (hform₂ f)
    rw [map_mul, map_mul, map_inv] at heq
    rw [hproj f,
      hproj (s₂ f)] at heq
    calc x * e n₂ * x⁻¹ * (x * spTorus hζ f * x⁻¹) * (x * e n₂ * x⁻¹)⁻¹
        = x * (e n₂ * spTorus hζ f * (e n₂)⁻¹) * x⁻¹ := by group
      _ = x * spTorus hζ (s₂ f) * x⁻¹ := by rw [heq]
  obtain ⟨hn₁', heq₁⟩ :=
    exists_ggConjAut_eq_congr
      (R := LargeEvenProj (LargeEvenSpGroup K m)) hA.2.1
      (A := A) (σ := σ) Θ hΘ (n := l₁) (s := s₁) hψform₁
  obtain ⟨hn₂', heq₂⟩ :=
    exists_ggConjAut_eq_congr
      (R := LargeEvenProj (LargeEvenSpGroup K m)) hA.2.1
      (A := A) (σ := σ) Θ hΘ (n := l₂) (s := s₂) hψform₂
  have hcardV : Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m :=
    ggTBJ_card_fin_zmod p m
  have hfixV₁ : Nat.card {f : Fin m → Multiplicative (ZMod p) // s₁ f = f} * p =
      Nat.card (Fin m → Multiplicative (ZMod p)) := by
    rw [hcardV]; exact hfix₁
  have hfixV₂ : Nat.card {f : Fin m → Multiplicative (ZMod p) // s₂ f = f} * p =
      Nat.card (Fin m → Multiplicative (ZMod p)) := by
    rw [hcardV]; exact hfix₂
  have hrefl₁ : GGIsReflection p (MulAut.congr Θ s₁) :=
    ⟨by rw [← map_pow, hs₁, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₁) hfixV₁).2⟩
  have hrefl₂ : GGIsReflection p (MulAut.congr Θ s₂) :=
    ⟨by rw [← map_pow, hs₂, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₂) hfixV₂).2⟩
  have hrefl₁' : GGIsReflection p (ggConjAut A hn₁') := by rw [heq₁]; exact hrefl₁
  have hrefl₂' : GGIsReflection p (ggConjAut A hn₂') := by rw [heq₂]; exact hrefl₂
  have hne' : MulAut.congr Θ s₁ * MulAut.congr Θ s₂ ≠
      MulAut.congr Θ s₂ * MulAut.congr Θ s₁ := by
    intro h
    apply hne
    apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul]
    exact h
  have hconjne : ggConjAut A hn₁' * ggConjAut A hn₂' ≠
      ggConjAut A hn₂' * ggConjAut A hn₁' := by
    rw [heq₁, heq₂]
    exact hne'
  exact ⟨l₁, l₂, hn₁', hn₂', hl₁J, hl₂J, hWeyl l₁ hn₁', hWeyl l₂ hn₂',
    hrefl₁', hrefl₂', hconjne⟩

end CFSG.StandardType

end
