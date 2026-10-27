module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPNExcKac_datum_sigma
    (hBS : GGK0ExcBS) {p n : ℕ} {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hpair : GGKacExcPair labX p)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ∃ D : GGKacDatum, GGKacValid labX p D ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) →
        ∃ o ∈ D.orbits, o.qs = true ∧ labX.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
          GGHasLabel o.lab (J' ⧸ Subgroup.center J')) ∧
      (∀ o ∈ D.orbits, o.qs = true → ∃ J' : Subgroup X,
        IsComponentOf J' (ggFixSub σ) ∧ GGHasLabel o.lab (J' ⧸ Subgroup.center J')) ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → p ∣ Nat.card J') ∧
      GGKacCompBij D X σ ∧
      ∀ o ∈ D.orbits, o.lab = ⟨.A, 1, 1⟩ → o.qs = false → ∃ t : X, t ^ p = 1 ∧
        (∀ a ∈ A, a t = t) ∧
        (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → ∀ j ∈ J', t * j = j * t) ∧
        (MulAut.conj t : MulAut X) ∉ Subgroup.zpowers σ := by
  obtain ⟨hlocCore, -, -, -, -, -, -, hmarked⟩ := hd.1
  obtain ⟨hperfX, lab', hΛlab', hraw⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso_mark : GGLabelIso lab' labX :=
    ggLabelRigidInput_holds lab' labX (X ⧸ Subgroup.center X) hΛlab' hΛX hHasLabel_lab' hhX
  have hrawX := largeEvenRawDatum_of_ggLabelIso hiso_mark hraw
  have hmain := hBS p labX hΛX hpair _ hrawX
  obtain ⟨R, _, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨-, -, htheta⟩ := hQ
  obtain ⟨θ, -, -, hInd⟩ := htheta
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hσpow : σ ^ p = 1 := hlocCore.1.2 σ hlocCore.2.1
  have hφ_apply : ∀ l : X, ggInducedAut θ σ (ψ l) = ψ (σ l) := by
    intro l
    change ggInducedAut θ σ (θ (l : X ⧸ Subgroup.center X)) =
      θ ((σ l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ σ l
  have hφ_mem : ggInducedAut θ σ ∈ I := hInd σ hlocCore.2.1
  obtain ⟨D, hDval, ha, hb, hc, -, he, hSig⟩ := hP X ψ hψ hker_le hperfX σ hσpow
    ⟨ggInducedAut θ σ, hφ_mem, hφ_apply⟩
  refine ⟨D, hDval, ha, hb, hc, he, fun o ho hlab hqs => ?_⟩
  refine hSig o ho ⟨hlab, hqs⟩ A hlocCore.2.1 hlocCore.1 fun a haA => ?_
  refine ⟨ggInducedAut θ a, hInd a haA, fun l => ?_⟩
  change ggInducedAut θ a (θ (l : X ⧸ Subgroup.center X)) =
    θ ((a l : X) : X ⧸ Subgroup.center X)
  exact ggInducedAut_apply θ a l

theorem ggTPNExcKac_datum
    (hBS : GGK0ExcBS) {p n : ℕ} {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hpair : GGKacExcPair labX p)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ∃ D : GGKacDatum, GGKacValid labX p D ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) →
        ∃ o ∈ D.orbits, o.qs = true ∧ labX.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
          GGHasLabel o.lab (J' ⧸ Subgroup.center J')) ∧
      (∀ o ∈ D.orbits, o.qs = true → ∃ J' : Subgroup X,
        IsComponentOf J' (ggFixSub σ) ∧ GGHasLabel o.lab (J' ⧸ Subgroup.center J')) ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → p ∣ Nat.card J') ∧
      GGKacCompBij D X σ := by
  obtain ⟨D, hDval, ha, hb, hc, he, -⟩ := ggTPNExcKac_datum_sigma hBS hd hΛX hpair hhX
  exact ⟨D, hDval, ha, hb, hc, he⟩

end CFSG.StandardType

end
