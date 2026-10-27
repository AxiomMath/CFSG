module

public import CFSG.Quasithin.Background.HMult
public import CFSG.Quasithin.Background.HSL3Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open CFSG.Quasithin.H.SL3Pair
open scoped Matrix Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_coords_of_sumOfNatVia {W : Type} [CommGroup W] [Finite W] [Finite K]
    (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut W)} {k : ℕ} {π : ↥Γ →* ↥H}
    (h : SumOfNatVia (FFModel.nat Γ) H ⊤ ⊥ k π) :
    ∃ (I : Fin k → Subgroup W) (e : W ≃* StdMod (Fin k × ι) K),
      (∀ i, (FFModel.nat Γ).RealizesVia H (I i) ⊥ π) ∧
      (∀ (γ : ↥Γ) (w : W),
        e (((π γ : ↥H) : MulAut W) w) = matAut (diagGL k (γ : GL ι K)) (e w)) ∧
      ∀ (i : Fin k) (w : W),
        w ∈ I i ↔ ∀ (j : Fin k), j ≠ i → ∀ (x : ι),
          Multiplicative.toAdd (e w) (j, x) = 0 := by
  obtain ⟨I, -, hind, hsup, hreal⟩ := h
  classical
  let eI : ∀ i : Fin k, ↥(I i) ≃* StdMod ι K :=
    fun i => Classical.choose (exists_mulEquiv_of_realizesVia_sub Γ (hreal i))
  have heI : ∀ (i : Fin k) (γ : ↥Γ) (u : ↥(I i))
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I i),
      eI i ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ = natAct Γ γ (eI i u) :=
    fun i => Classical.choose_spec (exists_mulEquiv_of_realizesVia_sub Γ (hreal i))
  have hcomm : Pairwise fun i j : Fin k =>
      ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => mul_comm x y
  let ψ : (∀ i : Fin k, ↥(I i)) →* W := Subgroup.noncommPiCoprod (H := I) hcomm
  have hindI : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
    simpa using hind i
  have hinj : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindI
  have hsupI : (⨆ i : Fin k, I i) = ⊤ := by simpa using hsup
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range, hsupI]
  let Ψ : (∀ i : Fin k, ↥(I i)) ≃* W := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hψapply : ∀ u : ∀ i : Fin k, ↥(I i), ψ u = ∏ i, ((u i : ↥(I i)) : W) := by
    intro u
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hψsingle : ∀ (i : Fin k) (x : ↥(I i)), ψ (Pi.mulSingle i x) = (x : W) :=
    fun i x => Subgroup.noncommPiCoprod_mulSingle i x
  have hψact : ∀ (h : ↥H) (u : ∀ i : Fin k, ↥(I i)),
      ψ (fun i => (⟨(h : MulAut W) (u i),
        (hreal i).2.2.2.1 h (u i) (u i).2⟩ : ↥(I i))) = (h : MulAut W) (ψ u) := by
    intro h u
    rw [hψapply, hψapply, map_prod]
  let Φhom : (∀ i : Fin k, ↥(I i)) →* StdMod (Fin k × ι) K :=
    { toFun := fun u => Multiplicative.ofAdd fun p =>
        Multiplicative.toAdd (eI p.1 (u p.1)) p.2
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext p
        simp
      map_mul' := by
        intro u v
        apply Multiplicative.toAdd.injective
        funext p
        simp only [Pi.mul_apply, toAdd_ofAdd, Pi.add_apply, map_mul, toAdd_mul] }
  have hΦinj : Function.Injective Φhom := by
    intro u v huv
    funext i
    apply (eI i).injective
    apply Multiplicative.toAdd.injective
    funext x
    have h := congrFun (congrArg Multiplicative.toAdd huv) (i, x)
    dsimp only [Φhom] at h ⊢
    exact h
  have hΦsurj : Function.Surjective Φhom := by
    intro v
    refine ⟨fun i => (eI i).symm
      (Multiplicative.ofAdd fun x => Multiplicative.toAdd v (i, x)), ?_⟩
    apply Multiplicative.toAdd.injective
    funext p
    show Multiplicative.toAdd (eI p.1 ((eI p.1).symm
      (Multiplicative.ofAdd fun x => Multiplicative.toAdd v (p.1, x)))) p.2 =
      Multiplicative.toAdd v p
    rw [MulEquiv.apply_symm_apply]
    rfl
  let Φ : (∀ i : Fin k, ↥(I i)) ≃* StdMod (Fin k × ι) K :=
    MulEquiv.ofBijective Φhom ⟨hΦinj, hΦsurj⟩
  have hΦcoord : ∀ (u : ∀ i : Fin k, ↥(I i)) (j : Fin k) (x : ι),
      Multiplicative.toAdd (Φ u) (j, x) = Multiplicative.toAdd (eI j (u j)) x :=
    fun u j x => rfl
  let e : W ≃* StdMod (Fin k × ι) K := Ψ.symm.trans Φ
  have he : ∀ w : W, e w = Φ (Ψ.symm w) := fun w => rfl
  have hΨsymm : ∀ (h : ↥H) (w : W),
      Ψ.symm ((h : MulAut W) w) =
        (fun i => (⟨(h : MulAut W) ((Ψ.symm w) i),
          (hreal i).2.2.2.1 h ((Ψ.symm w) i) ((Ψ.symm w) i).2⟩ : ↥(I i))) := by
    intro h w
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply]
    change (h : MulAut W) w = ψ (fun i => (⟨(h : MulAut W) ((Ψ.symm w) i),
      (hreal i).2.2.2.1 h ((Ψ.symm w) i) ((Ψ.symm w) i).2⟩ : ↥(I i)))
    rw [hψact]
    congr 1
    change w = Ψ (Ψ.symm w)
    rw [MulEquiv.apply_symm_apply]
  refine ⟨I, e, hreal, ?_, ?_⟩
  · intro γ w
    apply Multiplicative.toAdd.injective
    funext p
    obtain ⟨j, x⟩ := p
    have hL : Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) (j, x) =
        Multiplicative.toAdd (eI j ⟨((π γ : ↥H) : MulAut W) ((Ψ.symm w) j),
          (hreal j).2.2.2.1 (π γ) ((Ψ.symm w) j) ((Ψ.symm w) j).2⟩) x := by
      rw [he, hΨsymm, hΦcoord]
    have hR : Multiplicative.toAdd (matAut (diagGL k (γ : GL ι K)) (e w)) (j, x) =
        Multiplicative.toAdd (natAct Γ γ (eI j ((Ψ.symm w) j))) x := by
      change (toAddMap (matAut (diagGL k (γ : GL ι K)))
        (Multiplicative.toAdd (e w))) (j, x) = _
      rw [toAddMap_matAut, diagGL_mulVec]
      simp only [he, hΦcoord, natAct, toAdd_ofAdd]
    calc Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) (j, x)
        = Multiplicative.toAdd (eI j ⟨((π γ : ↥H) : MulAut W) ((Ψ.symm w) j),
            (hreal j).2.2.2.1 (π γ) ((Ψ.symm w) j) ((Ψ.symm w) j).2⟩) x := hL
      _ = Multiplicative.toAdd (natAct Γ γ (eI j ((Ψ.symm w) j))) x := by
        rw [heI]
      _ = Multiplicative.toAdd (matAut (diagGL k (γ : GL ι K)) (e w)) (j, x) := hR.symm
  · intro i w
    constructor
    · intro hw
      have hw' : Ψ.symm w = Pi.mulSingle (M := fun j : Fin k => ↥(I j)) i (⟨w, hw⟩ : ↥(I i)) := by
        apply Ψ.injective
        rw [MulEquiv.apply_symm_apply]
        change w = ψ (Pi.mulSingle (M := fun j : Fin k => ↥(I j)) i (⟨w, hw⟩ : ↥(I i)))
        rw [hψsingle]
      intro j hj x
      rw [he, hΦcoord, hw']
      simp [Pi.mulSingle_eq_of_ne hj]
    · intro h
      have hzero : ∀ j, j ≠ i → Ψ.symm w j = 1 := by
        intro j hj
        apply (eI j).injective
        apply Multiplicative.toAdd.injective
        funext x
        have hh := h j hj x
        rw [he, hΦcoord] at hh
        simpa [hh]
      have hw' : Ψ.symm w = Pi.mulSingle (M := fun j : Fin k => ↥(I j)) i (Ψ.symm w i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Pi.mulSingle_eq_same]
        · rw [hzero j hj]
          exact (Pi.mulSingle_eq_of_ne (M := fun j : Fin k => ↥(I j)) hj _).symm
      rw [← Ψ.apply_symm_apply w, hw']
      change ψ (Pi.mulSingle (M := fun j : Fin k => ↥(I j)) i (Ψ.symm w i)) ∈ I i
      rw [hψsingle]
      exact (Ψ.symm w i).2

theorem map_congrHom_eq_natImage_diag {W : Type} [CommGroup W] (Γ : Subgroup (GL ι K))
    {H : Subgroup (MulAut W)} {k : ℕ} {π : ↥Γ →* ↥H} (hπ : Function.Surjective π)
    (e : W ≃* StdMod (Fin k × ι) K)
    (he : ∀ (γ : ↥Γ) (w : W),
      e (((π γ : ↥H) : MulAut W) w) = matAut (diagGL k (γ : GL ι K)) (e w)) :
    H.map (congrHom e) = natImage (diagSub k Γ) := by
  have hγ : ∀ γ : ↥Γ, congrHom e ((π γ : ↥H) : MulAut W) =
      matAut (diagGL k (γ : GL ι K)) := by
    intro γ
    ext x
    rw [congrHom_apply, he, MulEquiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγx⟩ := hπ ⟨x, hx⟩
    have hxγ : ((π γ : ↥H) : MulAut W) = x := congrArg Subtype.val hγx
    refine ⟨⟨diagGL k (γ : GL ι K), Subgroup.mem_map_of_mem (diagGL k) γ.2⟩, ?_⟩
    change matAut (diagGL k (γ : GL ι K)) = congrHom e x
    rw [← hxγ, hγ]
  · rintro ⟨δ, rfl⟩
    obtain ⟨γ, hγmem, hγδ⟩ := Subgroup.mem_map.mp δ.2
    let γ' : ↥Γ := ⟨γ, hγmem⟩
    refine ⟨((π γ' : ↥H) : MulAut W), (π γ').2, ?_⟩
    have hδ : (δ : GL (Fin k × ι) K) = diagGL k γ := hγδ.symm
    calc congrHom e ((π γ' : ↥H) : MulAut W) = matAut (diagGL k (γ' : GL ι K)) := hγ γ'
      _ = matAut (δ : GL (Fin k × ι) K) := by rw [hδ]
      _ = natAut (diagSub k Γ) δ := rfl

theorem realizesVia_of_isoMod {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H} {U V : Subgroup W}
    (hU : D.RealizesVia H U ⊥ π) (hUV : Pair.IsoMod H U V) :
    D.RealizesVia H V ⊥ π := by
  obtain ⟨hπ, -, hker, hHU, -, hsec, hDker, β, hβs, hβk, hβe⟩ := hU
  obtain ⟨e, he⟩ := hUV
  have hHV : ∀ h : ↥H, ∀ v ∈ V, (h : MulAut W) v ∈ V := by
    intro h v hv
    obtain ⟨w, hw⟩ := e.surjective (⟨v, hv⟩ : ↥V)
    have hwU : (h : MulAut W) (w : ↥U) ∈ U := hHU h (w : ↥U) w.2
    have hv' : ((h : MulAut W) v) =
        (e ⟨(h : MulAut W) (w : ↥U), hwU⟩ : W) := by
      rw [← congrArg (fun z : ↥V => (h : MulAut W) (z : W)) hw]
      exact (he h h.2 w hwU).symm
    rw [hv']
    exact (e ⟨(h : MulAut W) (w : ↥U), hwU⟩).2
  let β' : ↥V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp e.symm.toMonoidHom
  have hβ'v : ∀ v : ↥V, β' v = β (e.symm v) := fun v => rfl
  have hβ's : Function.Surjective β' := by
    intro x
    obtain ⟨u, hu⟩ := hβs x
    exact ⟨e u, by rw [hβ'v, MulEquiv.symm_apply_apply]; exact hu⟩
  have hβ'k : ∀ v : ↥V, β' v = 1 ↔ (v : W) ∈ (⊥ : Subgroup W) := by
    intro v
    rw [hβ'v, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : e.symm v = 1 := Subtype.ext h
      simpa using congrArg e h1
    · intro h
      have hv1 : v = 1 := Subtype.ext h
      rw [hv1, map_one]
      rfl
  have hβ'e : ∀ (γ : D.Gam) (v : ↥V) (m : ↥D.sec)
      (hv : ((π γ : ↥H) : MulAut W) (v : W) ∈ V)
      (hm : D.act γ (m : D.Amb) ∈ D.sec),
      β' v = QuotientGroup.mk m →
        β' ⟨((π γ : ↥H) : MulAut W) (v : W), hv⟩ =
          QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := by
    intro γ v m hv hm hβv
    have hβv' : β (e.symm v) = QuotientGroup.mk m := hβv
    have hwU : ((π γ : ↥H) : MulAut W) ((e.symm v : ↥U) : W) ∈ U :=
      hHU (π γ) ((e.symm v : ↥U)) (e.symm v).2
    have hstep : e.symm ⟨((π γ : ↥H) : MulAut W) (v : W), hv⟩ =
        ⟨((π γ : ↥H) : MulAut W) ((e.symm v : ↥U) : W), hwU⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      have h1 := he (π γ) (π γ).2 (e.symm v) hwU
      simpa using h1.symm
    have hβ'step : β' ⟨((π γ : ↥H) : MulAut W) (v : W), hv⟩ =
        β ⟨((π γ : ↥H) : MulAut W) ((e.symm v : ↥U) : W), hwU⟩ := by
      rw [hβ'v, hstep]
    rw [hβ'step]
    exact hβe γ (e.symm v) m hwU hm hβv'
  refine ⟨hπ, bot_le, hker, hHV, ?_, hsec, hDker, β', hβ's, hβ'k, hβ'e⟩
  intro h z hz
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz, map_one]

theorem sumOfNatVia_of_isoMod {W : Type} [CommGroup W] {D : FFModel}
    {X : Subgroup (MulAut W)} {k : ℕ} {I : Fin k → Subgroup W}
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ ⊥)
    (hsup : (⊥ ⊔ ⨆ i, I i) = ⊤) (i₀ : Fin k) {π : D.Gam →* ↥X}
    (h₀ : D.RealizesVia X (I i₀) ⊥ π) (hiso : ∀ i, Pair.IsoMod X (I i₀) (I i)) :
    SumOfNatVia D X ⊤ ⊥ k π := by
  refine ⟨I, fun _ => bot_le, hind, hsup, fun i => ?_⟩
  by_cases hi : i = i₀
  · subst hi
    exact h₀
  · exact realizesVia_of_isoMod h₀ (hiso i)

theorem exists_sumOfNatVia_of_sumOfNatIsoMod_sp4 {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {n : ℕ}
    (h : SumOfNatIsoMod (fun H U Z => NatSpn H U Z 4 n) X ⊤ ⊥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSp 2 K) →* ↥X),
      Nat.card K = 2 ^ n ∧ SumOfNatVia (FFModel.nat (StatedSp 2 K)) X ⊤ ⊥ 2 π := by
  obtain ⟨I, hZ, hind, hsup, hN, hiso⟩ := h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, hreal⟩ := hN 0
  obtain ⟨π, hπ⟩ := hreal
  exact ⟨K, hKfield, hKfinite, π, hKcard,
    sumOfNatVia_of_isoMod hind hsup 0 hπ (fun i => hiso 0 i)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
