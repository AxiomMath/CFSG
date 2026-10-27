module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H CFSG.Quasithin.H.Mult CFSG.Quasithin.H.SL3Pair
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Matrix Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem s16h_e3_coords_of_sumOfNatVia_sub {W : Type} [CommGroup W] [Finite W] [Finite K]
    (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut W)} {k : ℕ} {π : ↥Γ →* ↥H}
    {U : Subgroup W} (h : SumOfNatVia (FFModel.nat Γ) H U ⊥ k π) :
    ∃ e : ↥U ≃* StdMod (Fin k × ι) K,
      ∀ (γ : ↥Γ) (w : W) (hw : w ∈ U) (hw' : ((π γ : ↥H) : MulAut W) w ∈ U),
        e ⟨((π γ : ↥H) : MulAut W) w, hw'⟩ =
          matAut (diagGL k (γ : GL ι K)) (e ⟨w, hw⟩) := by
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
  have hsupI : (⨆ i : Fin k, I i) = U := by simpa using hsup
  have hrange : ψ.range = U := by
    rw [Subgroup.noncommPiCoprod_range, hsupI]
  have hmem : ∀ x : ∀ i : Fin k, ↥(I i), ψ x ∈ U := fun x => by
    rw [← hrange]
    exact ⟨x, rfl⟩
  let ψU : (∀ i : Fin k, ↥(I i)) →* ↥U := ψ.codRestrict U hmem
  have hψUinj : Function.Injective ψU := fun a b hab => hinj (Subtype.ext_iff.mp hab)
  have hψUsurj : Function.Surjective ψU := by
    intro u
    have hu : (u : W) ∈ ψ.range := by rw [hrange]; exact u.2
    obtain ⟨x, hx⟩ := hu
    exact ⟨x, Subtype.ext hx⟩
  let Ψ : (∀ i : Fin k, ↥(I i)) ≃* ↥U := MulEquiv.ofBijective ψU ⟨hψUinj, hψUsurj⟩
  have hψapply : ∀ u : ∀ i : Fin k, ↥(I i), ψ u = ∏ i, ((u i : ↥(I i)) : W) := by
    intro u
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
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
  let e : ↥U ≃* StdMod (Fin k × ι) K := Ψ.symm.trans Φ
  have he : ∀ w : ↥U, e w = Φ (Ψ.symm w) := fun w => rfl
  have hΨsymm : ∀ (h : ↥H) (w : ↥U) (hw' : (h : MulAut W) (w : W) ∈ U),
      Ψ.symm ⟨(h : MulAut W) (w : W), hw'⟩ =
        (fun i => (⟨(h : MulAut W) ((Ψ.symm w) i),
          (hreal i).2.2.2.1 h ((Ψ.symm w) i) ((Ψ.symm w) i).2⟩ : ↥(I i))) := by
    intro h w hw'
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change (h : MulAut W) (w : W) = ψ (fun i => (⟨(h : MulAut W) ((Ψ.symm w) i),
      (hreal i).2.2.2.1 h ((Ψ.symm w) i) ((Ψ.symm w) i).2⟩ : ↥(I i)))
    rw [hψact]
    congr 1
    exact (congrArg Subtype.val (MulEquiv.apply_symm_apply Ψ w)).symm
  refine ⟨e, ?_⟩
  intro γ w hw hw'
  apply Multiplicative.toAdd.injective
  funext p
  obtain ⟨j, x⟩ := p
  have hL : Multiplicative.toAdd (e ⟨((π γ : ↥H) : MulAut W) w, hw'⟩) (j, x) =
      Multiplicative.toAdd (eI j ⟨((π γ : ↥H) : MulAut W) ((Ψ.symm ⟨w, hw⟩) j),
        (hreal j).2.2.2.1 (π γ) ((Ψ.symm ⟨w, hw⟩) j) ((Ψ.symm ⟨w, hw⟩) j).2⟩) x := by
    rw [he, hΨsymm (π γ) ⟨w, hw⟩ hw', hΦcoord]
  have hR : Multiplicative.toAdd (matAut (diagGL k (γ : GL ι K)) (e ⟨w, hw⟩)) (j, x) =
      Multiplicative.toAdd (natAct Γ γ (eI j ((Ψ.symm ⟨w, hw⟩) j))) x := by
    change (toAddMap (matAut (diagGL k (γ : GL ι K)))
      (Multiplicative.toAdd (e ⟨w, hw⟩))) (j, x) = _
    rw [toAddMap_matAut, diagGL_mulVec]
    simp only [he, hΦcoord, natAct, toAdd_ofAdd]
  calc Multiplicative.toAdd (e ⟨((π γ : ↥H) : MulAut W) w, hw'⟩) (j, x)
      = Multiplicative.toAdd (eI j ⟨((π γ : ↥H) : MulAut W) ((Ψ.symm ⟨w, hw⟩) j),
          (hreal j).2.2.2.1 (π γ) ((Ψ.symm ⟨w, hw⟩) j) ((Ψ.symm ⟨w, hw⟩) j).2⟩) x := hL
    _ = Multiplicative.toAdd (natAct Γ γ (eI j ((Ψ.symm ⟨w, hw⟩) j))) x := by rw [heI]
    _ = Multiplicative.toAdd (matAut (diagGL k (γ : GL ι K)) (e ⟨w, hw⟩)) (j, x) := hR.symm

private noncomputable def s16h_e3_matEquiv (k : ℕ) (K : Type) [Field K] :
    StdMod (Fin k × ι) K ≃* Multiplicative (Matrix ι (Fin k) K) where
  toFun v := Multiplicative.ofAdd (Matrix.of fun i p => Multiplicative.toAdd v (p, i))
  invFun M := Multiplicative.ofAdd fun q => Multiplicative.toAdd M q.2 q.1
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext q
    obtain ⟨p, i⟩ := q
    rfl
  right_inv M := by
    apply Multiplicative.toAdd.injective
    funext i p
    rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i p
    rfl

private theorem s16h_e3_matEquiv_matAut (k : ℕ) (γ : GL ι K) (v : StdMod (Fin k × ι) K) :
    s16h_e3_matEquiv (K := K) k (matAut (diagGL k γ) v) =
      Multiplicative.ofAdd ((γ : Matrix ι ι K) *
        Multiplicative.toAdd (s16h_e3_matEquiv (K := K) k v)) := by
  apply Multiplicative.toAdd.injective
  funext i p
  rw [toAdd_ofAdd]
  have h1 : Multiplicative.toAdd (s16h_e3_matEquiv (K := K) k
        (matAut (diagGL k γ) v)) i p =
      ((γ : Matrix ι ι K) *ᵥ fun j => Multiplicative.toAdd v (p, j)) i := by
    change (Matrix.of (fun i p => Multiplicative.toAdd (matAut (diagGL k γ) v) (p, i))) i p = _
    rw [Matrix.of_apply]
    change (toAddMap (matAut (diagGL k γ)) (Multiplicative.toAdd v)) (p, i) = _
    rw [toAddMap_matAut, diagGL_mulVec]
  have h2 : ((γ : Matrix ι ι K) *
        Multiplicative.toAdd (s16h_e3_matEquiv (K := K) k v)) i p =
      ((γ : Matrix ι ι K) *ᵥ fun j => Multiplicative.toAdd v (p, j)) i := by
    rw [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Multiplicative.toAdd (s16h_e3_matEquiv (K := K) k v) j p =
      Multiplicative.toAdd v (p, j) from rfl]
  rw [h1, h2]

theorem s16h_e3_l3_coord_of_iso {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hL : IsL3 ↥L 1) {I : Fin 3 → Subgroup W}
    (hI : ∀ i, BinaryNaturalSL L (I i) ⊥ 3 1)
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥)
    (hsup : (⊥ ⊔ ⨆ i, I i) = U) (i₀ : Fin 3) (hiso : ∀ i, H.Pair.IsoMod L (I i₀) (I i)) :
    ∃ (ρ : ↥L ≃* GL (Fin 3) (ZMod 2))
      (ψ : ↥U ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))),
      ∀ (l : ↥L) (u : W) (hu : u ∈ U) (hlu : (l : MulAut W) u ∈ U),
        ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
          ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)) := by
  classical
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod (hI i₀)
  have hreal : ∀ i : Fin 3,
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L (I i) ⊥ π :=
    fun i => realizesVia_of_isoMod hπ (hiso i)
  have hsum : SumOfNatVia (FFModel.nat (StatedSL 3 (ZMod 2))) L U ⊥ 3 π :=
    ⟨I, fun _ => bot_le, hind, hsup, hreal⟩
  obtain ⟨e, he⟩ :=
    s16h_e3_coords_of_sumOfNatVia_sub (K := ZMod 2) (StatedSL 3 (ZMod 2)) hsum
  have hcardDom : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
    CFSG.Open.StatedAPI.card_statedSL_three_zmod_two
  have hcardCod : Nat.card ↥L = 168 := card_eq_of_isL3 hL
  have hbij : Function.Bijective π :=
    (Nat.bijective_iff_surjective_and_card π).mpr ⟨hπ.1, by rw [hcardDom, hcardCod]⟩
  let eπ : ↥(StatedSL 3 (ZMod 2)) ≃* ↥L := MulEquiv.ofBijective π hbij
  have hTop : StatedSL 3 (ZMod 2) = ⊤ :=
    le_antisymm le_top (fun x _ => FFC.mem_statedSL_zmod x)
  let ιe : GL (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop).symm
  have hιe : ∀ δ : GL (Fin 3) (ZMod 2),
      ((ιe δ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) = δ := fun _ => rfl
  let ρ : ↥L ≃* GL (Fin 3) (ZMod 2) := eπ.symm.trans ιe.symm
  let ψ : ↥U ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    e.trans (s16h_e3_matEquiv (K := ZMod 2) 3)
  refine ⟨ρ, ψ, ?_⟩
  intro l u hu hlu
  let γ : ↥(StatedSL 3 (ZMod 2)) := eπ.symm l
  have hπγ : π γ = l := by
    change eπ (eπ.symm l) = l
    rw [MulEquiv.apply_symm_apply]
  have hγcoe : (γ : GL (Fin 3) (ZMod 2)) = (ρ l : GL (Fin 3) (ZMod 2)) := by
    have hρl : (ρ l : GL (Fin 3) (ZMod 2)) = ιe.symm γ := rfl
    rw [hρl]
    exact (hιe (ιe.symm γ)).symm
  have hsubW : ((π γ : ↥L) : MulAut W) u = (l : MulAut W) u :=
    congrArg (fun x : ↥L => ((x : MulAut W) u)) hπγ
  have hw' : ((π γ : ↥L) : MulAut W) u ∈ U := by rw [hsubW]; exact hlu
  have hsub : (⟨((π γ : ↥L) : MulAut W) u, hw'⟩ : ↥U) = ⟨(l : MulAut W) u, hlu⟩ :=
    Subtype.ext hsubW
  have he' : e ⟨(l : MulAut W) u, hlu⟩ =
      matAut (diagGL 3 (γ : GL (Fin 3) (ZMod 2))) (e ⟨u, hu⟩) := by
    rw [← hsub]
    exact he γ u hu hw'
  dsimp only [ψ]
  change (s16h_e3_matEquiv (K := ZMod 2) 3) (e ⟨(l : MulAut W) u, hlu⟩) =
    Multiplicative.ofAdd ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Multiplicative.toAdd ((s16h_e3_matEquiv (K := ZMod 2) 3) (e ⟨u, hu⟩)))
  rw [he', s16h_e3_matEquiv_matAut, hγcoe]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
