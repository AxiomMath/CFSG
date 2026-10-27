module

public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Pair CFSG.Open Subgroup

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem s16h_e3_inner_of_twist_stable (hQ : ∀ q : Q, q ^ 2 = 1) {L : Subgroup (MulAut Q)}
    (hL : IsPSL 3 2 1 ↥L) {V : Subgroup Q}
    (hVinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcard : Nat.card ↥V = 8)
    (hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v) {τ : MulAut Q}
    (hτ : τ ∈ normalizer (L : Set (MulAut Q)))
    (hiso : H.Pair.IsoMod L (V.map τ.toMonoidHom) V) :
    ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
  obtain ⟨ψ, hψ⟩ := hiso
  have hαmem : ∀ l ∈ L, τ * l * τ⁻¹ ∈ L := fun l hl =>
    conj_mem_of_mem_normalizer hτ hl
  have hτVinv : ∀ x ∈ L, ∀ w ∈ V.map τ.toMonoidHom, x w ∈ V.map τ.toMonoidHom := by
    intro x hx w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    have hxv : (τ⁻¹ * x * τ) v ∈ V := by
      refine hVinv (τ⁻¹ * x * τ) ?_ v hv
      exact (Subgroup.mem_normalizer_iff.mp
        ((normalizer (L : Set (MulAut Q))).inv_mem hτ) x).mp hx
    exact Subgroup.mem_map.mpr ⟨(τ⁻¹ * x * τ) v, hxv, by simp [MulAut.mul_apply]⟩
  let φ : MulAut ↥V := (MulEquiv.subgroupMap τ V).trans ψ
  have hφcoe : ∀ x : ↥V, (φ x : Q) = (ψ (MulEquiv.subgroupMap τ V x) : Q) := fun x => rfl
  have hφ : ∀ (l : ↥L) (x : ↥V),
      (φ ⟨(l : MulAut Q) (x : Q), hVinv l l.2 x x.2⟩ : Q) =
        (τ * l * τ⁻¹) ((φ x : ↥V) : Q) := by
    intro l x
    have hsub : MulEquiv.subgroupMap τ V ⟨(l : MulAut Q) (x : Q), hVinv l l.2 x x.2⟩ =
        (⟨(τ * l * τ⁻¹) ((MulEquiv.subgroupMap τ V x : Q)),
          hτVinv (τ * l * τ⁻¹) (hαmem l l.2) _ (MulEquiv.subgroupMap τ V x).2⟩ :
          ↥(V.map τ.toMonoidHom)) := by
      apply Subtype.ext
      simp only [MulEquiv.coe_subgroupMap_apply]
      simp [MulAut.mul_apply]
    rw [hφcoe, hsub, hφcoe x]
    exact hψ (τ * l * τ⁻¹) (hαmem l l.2) (MulEquiv.subgroupMap τ V x) _
  have htop := rank3_surj hQ hL hVinv hcard hnt
  obtain ⟨g, hgL, hg⟩ := mem_autSub.mp (by rw [htop]; exact Subgroup.mem_top φ)
  have hgapp : ∀ w : ↥V, (g : MulAut Q) (w : Q) = (φ w : Q) := by
    intro w
    have := congrArg (fun χ : MulAut ↥V => (((χ w : ↥V) : Q))) hg
    rw [resHom_apply] at this
    simpa using this
  have hginv : ∀ w : ↥V, (g : MulAut Q)⁻¹ (w : Q) = (φ.symm w : Q) := by
    intro w
    have h1 : (g : MulAut Q) (φ.symm w : Q) = (w : Q) := by
      rw [hgapp (φ.symm w)]
      exact congrArg Subtype.val (MulEquiv.apply_symm_apply φ w)
    calc (g : MulAut Q)⁻¹ (w : Q)
        = (g : MulAut Q)⁻¹ ((g : MulAut Q) (φ.symm w : Q)) := by rw [h1]
      _ = (φ.symm w : Q) := by simp
  have hAB : ∀ (l : ↥L), ∀ v ∈ V,
      ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹) v =
        (τ * (l : MulAut Q) * τ⁻¹) v := by
    intro l v hv
    have h2 : (l : MulAut Q) ((φ.symm ⟨v, hv⟩ : ↥V) : Q) ∈ V :=
      hVinv l l.2 _ (φ.symm ⟨v, hv⟩).2
    show (g : MulAut Q) ((l : MulAut Q) ((g : MulAut Q)⁻¹ v)) =
      (τ * (l : MulAut Q) * τ⁻¹) v
    rw [hginv ⟨v, hv⟩]
    rw [show (g : MulAut Q) ((l : MulAut Q) ((φ.symm ⟨v, hv⟩ : ↥V) : Q)) =
        (φ ⟨(l : MulAut Q) ((φ.symm ⟨v, hv⟩ : ↥V) : Q), h2⟩ : Q)
        from hgapp ⟨_, h2⟩]
    rw [hφ l (φ.symm ⟨v, hv⟩)]
    rw [MulEquiv.apply_symm_apply]
  have hBAinv : ∀ (l : ↥L), ∀ v ∈ V,
      ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v =
        (τ * (l : MulAut Q) * τ⁻¹)⁻¹ v := by
    intro l v hv
    have hAle : ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹) ∈ L :=
      L.mul_mem (L.mul_mem hgL l.2) (L.inv_mem hgL)
    have hAinvV : ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v ∈ V :=
      hVinv _ (L.inv_mem hAle) _ hv
    have h := hAB l _ hAinvV
    rw [mulAut_apply_inv_apply] at h
    have h2 : ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v =
        (τ * (l : MulAut Q) * τ⁻¹)⁻¹ v := by
      have h1 : (τ * (l : MulAut Q) * τ⁻¹)
          (((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v) = v := h.symm
      calc ((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v
          = (τ * (l : MulAut Q) * τ⁻¹)⁻¹
              ((τ * (l : MulAut Q) * τ⁻¹)
                (((g : MulAut Q) * (l : MulAut Q) * (g : MulAut Q)⁻¹)⁻¹ v)) := by simp
        _ = (τ * (l : MulAut Q) * τ⁻¹)⁻¹ v := by rw [h1]
    exact h2
  refine ⟨g, hgL, fun l hl => ?_⟩
  have hAle : ((g : MulAut Q) * l * (g : MulAut Q)⁻¹) ∈ L :=
    L.mul_mem (L.mul_mem hgL hl) (L.inv_mem hgL)
  have hBle : (τ * l * τ⁻¹) ∈ L := hαmem l hl
  have ha : (τ * l * τ⁻¹) * ((g : MulAut Q) * l * (g : MulAut Q)⁻¹)⁻¹ ∈ L :=
    L.mul_mem hBle (L.inv_mem hAle)
  have hone := rank3_inj hL hVinv hnt _ ha (fun v hv => by
    show ((τ * l * τ⁻¹) * ((g : MulAut Q) * l * (g : MulAut Q)⁻¹)⁻¹) v = v
    rw [MulAut.mul_apply, hBAinv ⟨l, hl⟩ v hv]
    simp)
  exact mul_inv_eq_one.mp hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
