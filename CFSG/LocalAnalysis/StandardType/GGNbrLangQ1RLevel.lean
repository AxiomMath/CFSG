module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Transfer
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

open scoped commutatorElement

@[expose] def Q1RToralTransfer
    (Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop)
    (S : ℕ → LargeEvenLabel → Prop)
    (Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) → Toral R A →
      ∀ u : MulAut R, u ∈ A → orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        CFSG.StandardType.LargeEvenMarking J (fun labJ _ _ IJ _ θJ =>
          Rel p lab labJ ∧ (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ IJ))

private theorem l02qt1_commutatorElement_mul_center_left {X : Type*} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (a b : X) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz_all : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hzinv_all : ∀ g : X, z⁻¹ * g = g * z⁻¹ :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  simp only [mul_assoc]
  rw [hz_all, hzinv_all]
  group

private theorem l02qt1_commutatorElement_mul_center_right {X : Type*} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (a b : X) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz_all : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hzinv_all : ∀ g : X, z⁻¹ * g = g * z⁻¹ :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  simp only [mul_assoc]
  rw [hz_all, hzinv_all]
  group

private theorem l02qt1_commutatorElement_mul_right_center {X : Type*} [Group X] {x y z : X}
    (hy : ⁅x, y⁆ ∈ Subgroup.center X) (hz : ⁅x, z⁆ ∈ Subgroup.center X) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have h2 : x * z * x⁻¹ = ⁅x, z⁆ * z := by rw [commutatorElement_def]; group
  have h3 : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [Subgroup.mem_center_iff.mp hz y]
    group
  calc
    ⁅x, y * z⁆ = (x * y * x⁻¹) * (x * z * x⁻¹) * (z⁻¹ * y⁻¹) := by
      rw [commutatorElement_def, mul_inv_rev]; group
    _ = (⁅x, y⁆ * y) * (⁅x, z⁆ * z) * (z⁻¹ * y⁻¹) := by rw [h1, h2]
    _ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [h3]

private theorem l02qt1_commutator_sup_center {X : Type*} [Group X] {J Z : Subgroup X}
    (hZ : Z ≤ Subgroup.center X) (hJJ : ⁅J, J⁆ = J) :
    ⁅J ⊔ Z, J ⊔ Z⁆ = J := by
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨j', hj', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    rw [l02qt1_commutatorElement_mul_center_left (hZ hz) j (j' * z'),
      l02qt1_commutatorElement_mul_center_right (hZ hz') j j']
    exact hJJ ▸ Subgroup.commutator_mem_commutator hj hj'
  · calc J = ⁅J, J⁆ := hJJ.symm
      _ ≤ ⁅J ⊔ Z, J ⊔ Z⁆ :=
        Subgroup.commutator_mono (show J ≤ J ⊔ Z from le_sup_left)
          (show J ≤ J ⊔ Z from le_sup_left)


private theorem l02qt1_exists_quotientCentralEquiv
    {J J₀ : Type*} [Group J] [Group J₀]
    (ψ : J →* J₀) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center J) (hperf : commutator J = ⊤) :
    ∃ e : J ⧸ Subgroup.center J ≃* J₀ ⧸ Subgroup.center J₀,
      ∀ x : J, e (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := by
  have hle : Subgroup.center J ≤
      ((QuotientGroup.mk' (Subgroup.center J₀)).comp ψ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (ψ x : J₀ ⧸ Subgroup.center J₀) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.map_center_le_center (f := ψ) hψ (Subgroup.mem_map_of_mem ψ hx)
  let F : J ⧸ Subgroup.center J →* J₀ ⧸ Subgroup.center J₀ :=
    QuotientGroup.lift (Subgroup.center J)
      ((QuotientGroup.mk' (Subgroup.center J₀)).comp ψ) hle
  have hFmk : ∀ x : J, F (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := by
    intro x
    rw [QuotientGroup.lift_mk]
    rfl
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J₀) y
    obtain ⟨x, rfl⟩ := hψ y'
    exact ⟨QuotientGroup.mk x, hFmk x⟩
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      intro hx
      rw [hFmk x] at hx
      rw [QuotientGroup.eq_one_iff] at hx
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_center_iff]
      intro y
      have hmem : ∀ z : J, ⁅x, z⁆ ∈ Subgroup.center J := by
        intro z
        apply hker
        rw [MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hx (ψ z)).symm
      let f : J →* Subgroup.center J :=
        { toFun := fun z => ⟨⁅x, z⁆, hmem z⟩
          map_one' := by
            apply Subtype.ext
            simp [commutatorElement_one_right]
          map_mul' := fun z w => by
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            exact l02qt1_commutatorElement_mul_right_center (hmem z) (hmem w) }
      have hfcomm : commutator J ≤ f.ker :=
        Subgroup.commutator_le.2 fun a _ b _ => by
          rw [MonoidHom.mem_ker, map_commutatorElement,
            commutatorElement_eq_one_iff_mul_comm]
          apply Subtype.ext
          simpa using (Subgroup.mem_center_iff.mp (f a).2 (f b)).symm
      have hftriv : f.ker = ⊤ := le_antisymm le_top (hperf ▸ hfcomm)
      have hf1 : f y = 1 := MonoidHom.mem_ker.mp (by rw [hftriv]; trivial)
      have hy1 : ⁅x, y⁆ = 1 := by
        have h := congrArg (fun t : Subgroup.center J => (t : J)) hf1
        simpa [f] using h
      exact (commutatorElement_eq_one_iff_mul_comm (g₁ := y) (g₂ := x)).mp (by
        have h := congrArg Inv.inv hy1
        rwa [commutatorElement_inv, inv_one] at h)
  have hFbij : Function.Bijective F := ⟨hFinj, hFsurj⟩
  refine ⟨MulEquiv.ofBijective F hFbij, ?_⟩
  intro x
  rw [MulEquiv.ofBijective_apply]
  exact hFmk x

theorem q1ToralActionTransfer_of_rToral
    {Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop}
    {S : ℕ → LargeEvenLabel → Prop} {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : Q1RToralTransfer Toral S Rel) : Q1ToralActionTransfer Toral S Rel := by
  intro p hp hp2 lab hΛ hS Q hQ
  refine largeEvenRawDatum_mono ?_ (h p hp hp2 lab hΛ hS Q hQ)
  rintro R _ I F ⟨hq, hPR⟩
  refine ⟨hq, ?_⟩
  rintro X _ _ hX θ A hA hInn hTor u hu hou J hJ
  let π : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  let A' : Subgroup (MulAut R) := A.map (ggInducedAut θ)
  let β : MulAut R := ggInducedAut θ u
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_le : π.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : X ⧸ Subgroup.center X) = 1 := by
      apply θ.injective
      simpa [π] using hx
    rwa [QuotientGroup.eq_one_iff] at h1
  have hcomm_all : ∀ (b : MulAut X) (x : X),
      π (b.toMonoidHom x) = ggInducedAut θ b (π x) := by
    intro b x
    simpa [π] using (ggInducedAut_apply θ b x).symm
  have hA' : IsElemAbelian p A' := hA.map (ggInducedAut θ)
  have hInn' : ∀ a ∈ A', a ∈ I := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact hInn a₀ ha₀
  have hTor' : Toral R A' := hTor
  have hβ : β ∈ A' := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hβp : orderOf β = p := by
    have hinj : Function.Injective (ggInducedAut θ) := ggInducedAut_injective_of_perfect hX θ
    have h1 : orderOf (ggInducedAut θ u) = orderOf u :=
      orderOf_injective (ggInducedAut θ) hinj u
    change orderOf (ggInducedAut θ u) = p
    rw [h1, hou]
  have hJ' : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJ
  obtain ⟨hJ₀, -⟩ := CFSG.StandardType.S2MathAs51600.centralFixedComponentTransfer_holds
    π hπ hker_le u β (fun x => hcomm_all u x) J hJ'
  have hJ₀open : CFSG.Open.IsComponentOf (J.map π) (ggAutFixedSubgroup β) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hJ₀
  have hmark₀ := hPR A' hA' hInn' hTor' β hβ hβp (J.map π) hJ₀open
  obtain ⟨hJ₀perf, labJ, hΛJ, hraw₀⟩ := hmark₀
  have hJcomm : commutator ↥J = ⊤ := hJ.2.2.1
  let ψ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective J
  have hψker : ψ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : X) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : ((ψ x : ↥(J.map π)) : R) = 1 := by
        simpa using congrArg Subtype.val hx
      simpa [ψ, MonoidHom.subgroupMap_apply_coe] using h2
    have hxc : (x : X) ∈ Subgroup.center X := hker_le hx1
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.mp hxc (y : X)
  obtain ⟨ι, ι_mk⟩ := l02qt1_exists_quotientCentralEquiv ψ hψ hψker hJcomm
  refine ⟨hJcomm, labJ, hΛJ, largeEvenRawDatum_mono ?_ hraw₀⟩
  rintro R' _ I' F' ⟨hsimple, hnonab, θJ, hrel, hnorm₀, hind₀⟩
  have hfix : ∀ b : MulAut R, b ∈ A' →
      Subgroup.map b.toMonoidHom (J.map π) = J.map π := by
    intro b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp hb
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hnorm₀ _ (Subgroup.mem_map.mpr ⟨a₀, ha₀, rfl⟩) y hy
    · intro y hy
      have hbinv : (ggInducedAut θ a₀)⁻¹ ∈ A' := by
        rw [← map_inv]
        exact Subgroup.mem_map.mpr ⟨a₀⁻¹, A.inv_mem ha₀, rfl⟩
      exact ⟨(ggInducedAut θ a₀)⁻¹ y, hnorm₀ _ hbinv y hy,
        MulEquiv.apply_symm_apply (ggInducedAut θ a₀) y⟩
  have hInv : ∀ a ∈ A, ∀ j : X, j ∈ J → a j ∈ J := by
    intro a ha j hj
    have hbinv : (ggInducedAut θ a)⁻¹ ∈ A' := by
      rw [← map_inv]
      exact Subgroup.mem_map.mpr ⟨a⁻¹, A.inv_mem ha, rfl⟩
    have hpre_a : Subgroup.map a.toMonoidHom (Subgroup.comap π (J.map π))
        = Subgroup.comap π (J.map π) := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        simp only [Subgroup.mem_comap] at hx ⊢
        rw [hcomm_all a x, ← hfix (ggInducedAut θ a)
          (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)]
        exact Subgroup.mem_map.mpr ⟨π x, hx, rfl⟩
      · intro x hx
        simp only [Subgroup.mem_comap] at hx
        have hz : (ggInducedAut θ a)⁻¹ (π x) ∈ J.map π := by
          rw [← hfix (ggInducedAut θ a)⁻¹ hbinv]
          exact Subgroup.mem_map.mpr ⟨π x, hx, rfl⟩
        refine ⟨a⁻¹ x, ?_, MulEquiv.apply_symm_apply a x⟩
        change π (a⁻¹.toMonoidHom x) ∈ Subgroup.map π J
        rw [hcomm_all a⁻¹ x, map_inv]
        exact hz
    have hcomm_sup : ⁅J ⊔ π.ker, J ⊔ π.ker⁆ = J := by
      haveI : Group.IsPerfect ↥J := ⟨hJcomm⟩
      exact l02qt1_commutator_sup_center hker_le (Subgroup.commutator_eq_self (H := J))
    have hstep3 : J = ⁅Subgroup.comap π (J.map π), Subgroup.comap π (J.map π)⁆ := by
      rw [Subgroup.comap_map_eq (f := π) J]
      exact hcomm_sup.symm
    have hmapJ : Subgroup.map a.toMonoidHom J = J := by
      calc Subgroup.map a.toMonoidHom J
          = Subgroup.map a.toMonoidHom
              (⁅Subgroup.comap π (J.map π), Subgroup.comap π (J.map π)⁆) :=
              congrArg (Subgroup.map a.toMonoidHom) hstep3
        _ = ⁅Subgroup.map a.toMonoidHom (Subgroup.comap π (J.map π)),
              Subgroup.map a.toMonoidHom (Subgroup.comap π (J.map π))⁆ := by
              rw [Subgroup.map_commutator]
        _ = ⁅Subgroup.comap π (J.map π), Subgroup.comap π (J.map π)⁆ := by rw [hpre_a]
        _ = J := hstep3.symm
    have : a j ∈ Subgroup.map a.toMonoidHom J :=
      Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    rwa [hmapJ] at this
  have hInd : GGAutsInduceOn A J (ι.trans θJ) I' := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hind₀ (ggInducedAut θ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    refine ⟨φ, hφI, ?_⟩
    intro j j' hj
    have hrel' : ggInducedAut θ a ((ψ j : R)) = ((ψ j' : R)) := by
      rw [MonoidHom.subgroupMap_apply_coe, MonoidHom.subgroupMap_apply_coe]
      change ggInducedAut θ a (θ ((j : X) : X ⧸ Subgroup.center X)) =
        θ ((j' : X) : X ⧸ Subgroup.center X)
      rw [ggInducedAut_apply, hj]
    have hmain := hφ (ψ j) (ψ j') hrel'
    change φ (θJ (ι ↑j)) = θJ (ι ↑j')
    rw [ι_mk j, ι_mk j']
    exact hmain
  exact ⟨hsimple, hnonab, ι.trans θJ, hrel, hInv, hInd⟩

end CFSG.StandardType

end
