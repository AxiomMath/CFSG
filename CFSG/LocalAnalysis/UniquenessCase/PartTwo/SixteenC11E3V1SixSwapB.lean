module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixSwapA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private theorem s1611e3_fixV_map (h : SixHyp M L L' κ e) {n : MulAut W} (hn : n ∈ M)
    {w : W} (hw : w ∈ fixV L) : n w ∈ fixV L := by
  rw [mem_fixV] at hw ⊢
  intro ℓ hℓ
  have hℓmem : n⁻¹ * ℓ * n ∈ L := by
    have := h.normalizes n⁻¹ (M.inv_mem hn) ℓ hℓ
    simpa using this
  have h1 : (n⁻¹ * ℓ * n) w = w := hw _ hℓmem
  calc ℓ (n w) = n ((n⁻¹ * ℓ * n) w) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = n w := by rw [h1]

theorem s1611e3_six_lift (h : SixHyp M L L' κ e) (ψ : MulAut W')
    (hψ : ∀ ℓ ∈ L', ψ * ℓ * ψ⁻¹ ∈ L') :
    ∃ m ∈ M, ∀ w : W, κ ((m : MulAut W) w) = ψ (κ w) := by
  classical
  obtain ⟨I₁, -, -, -, -, -, -, hN₁, -, -⟩ := h.sum
  have hLcard : Nat.card ↥L = 360 := by
    obtain ⟨φ⟩ := h.isAlt
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcard : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  obtain ⟨π, hπ⟩ := hN₁
  have hdvd : Nat.card ↥L' ∣ 360 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_surjective hπ.1
  have h360 : 360 ∣ Nat.card ↥L' := by
    rw [← hLcard]
    exact Subgroup.card_dvd_of_surjective h.esurj
  have hL'card : Nat.card ↥L' = 360 := Nat.dvd_antisymm hdvd h360
  have hker : Nat.card e.ker = 1 := by
    have hs := Subgroup.card_ker_mul_card_of_surjective (f := e) h.esurj
    rw [hLcard, hL'card] at hs
    have hs' : Nat.card e.ker * 360 = 1 * 360 := by rw [one_mul]; exact hs
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hs'
  have hinj : Function.Injective e :=
    (MonoidHom.ker_eq_bot_iff e).mp (Subgroup.eq_bot_of_card_eq e.ker hker)
  let eIso : ↥L' ≃* ↥L := MulEquiv.ofBijective e ⟨hinj, h.esurj⟩
  let ε'hom : ↥L' →* ↥L' :=
    { toFun := fun b => ⟨ψ * (b : MulAut W') * ψ⁻¹, hψ b b.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ψ * ((a : MulAut W') * (b : MulAut W')) * ψ⁻¹ =
          (ψ * (a : MulAut W') * ψ⁻¹) * (ψ * (b : MulAut W') * ψ⁻¹)
        group }
  have hε'inj : Function.Injective ε'hom := by
    intro a b hab
    have h : ψ * (a : MulAut W') * ψ⁻¹ = ψ * (b : MulAut W') * ψ⁻¹ :=
      congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  let ε' : MulAut ↥L' := MulEquiv.ofBijective ε'hom hε'inj.bijective_of_finite
  have hε'val : ∀ b : ↥L', ((ε' b : ↥L') : MulAut W') = ψ * (b : MulAut W') * ψ⁻¹ :=
    fun b => rfl
  let ε : MulAut ↥L := eIso.symm.trans (ε'.trans eIso)
  have hε : ∀ b : ↥L', ε (e b) = e (ε' b) := by
    intro b
    change (eIso.symm.trans (ε'.trans eIso)) (eIso b) = eIso (ε' b)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨m, hmM, hm⟩ := SixHyp.exists_conj h ε
  have hmfix : ∀ w ∈ fixV L, m w ∈ fixV L := fun w hw => s1611e3_fixV_map h hmM hw
  have hmfixi : ∀ w ∈ fixV L, m⁻¹ w ∈ fixV L :=
    fun w hw => s1611e3_fixV_map h (M.inv_mem hmM) hw
  let g₁ : W →* W' := κ.comp m.toMonoidHom
  have hker₁ : κ.ker ≤ g₁.ker := by
    intro w hw
    have hwfix : w ∈ fixV L := (SixHyp.ker_eq h) ▸ hw
    have hmw : m w ∈ fixV L := hmfix w hwfix
    show κ (m w) = 1
    exact MonoidHom.mem_ker.mp ((SixHyp.ker_eq h).symm ▸ hmw)
  let mbarHom : W' →* W' := (κ.liftOfSurjective h.surj) ⟨g₁, hker₁⟩
  have happ : ∀ w, mbarHom (κ w) = κ (m w) := fun w => by
    change ((κ.liftOfSurjective h.surj) ⟨g₁, hker₁⟩) (κ w) = g₁ w
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  let g₂ : W →* W' := κ.comp m⁻¹.toMonoidHom
  have hker₂ : κ.ker ≤ g₂.ker := by
    intro w hw
    have hwfix : w ∈ fixV L := (SixHyp.ker_eq h) ▸ hw
    have hmw : m⁻¹ w ∈ fixV L := hmfixi w hwfix
    show κ (m⁻¹ w) = 1
    exact MonoidHom.mem_ker.mp ((SixHyp.ker_eq h).symm ▸ hmw)
  let mbarInv : W' →* W' := (κ.liftOfSurjective h.surj) ⟨g₂, hker₂⟩
  have happInv : ∀ w, mbarInv (κ w) = κ (m⁻¹ w) := fun w => by
    change ((κ.liftOfSurjective h.surj) ⟨g₂, hker₂⟩) (κ w) = g₂ w
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hleft : ∀ y, mbarInv (mbarHom y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := h.surj y
    rw [happ w, happInv (m w), MulAut.inv_apply_self]
  have hright : ∀ y, mbarHom (mbarInv y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := h.surj y
    rw [happInv w, happ (m⁻¹ w), MulAut.apply_inv_self]
  have hbij : Function.Bijective mbarHom :=
    ⟨fun a b hab => by
      have hh := congrArg mbarInv hab
      rwa [hleft a, hleft b] at hh,
     fun y => ⟨mbarInv y, hright y⟩⟩
  let mbarAut : MulAut W' := MulEquiv.ofBijective mbarHom hbij
  have happAut : ∀ w, mbarAut (κ w) = κ (m w) := happ
  have hInvAut : ∀ y, mbarAut⁻¹ y = mbarInv y := by
    intro y
    exact mbarAut.injective (by
      rw [MulAut.apply_inv_self]
      exact (hright y).symm)
  have hconj : ∀ b ∈ L', mbarAut * b * mbarAut⁻¹ = ψ * b * ψ⁻¹ := by
    intro b hb
    ext y
    obtain ⟨w, rfl⟩ := h.surj y
    have h1 : m (((e ⟨b, hb⟩ : ↥L) : MulAut W) (m⁻¹ w)) =
        (((ε (e ⟨b, hb⟩) : ↥L)) : MulAut W) w := by
      have hc := congrArg (fun f : MulAut W => f w) (hm (e ⟨b, hb⟩))
      simpa only [MulAut.mul_apply] using hc
    rw [MulAut.mul_apply, MulAut.mul_apply, hInvAut (κ w), happInv w,
      ← h.equiv ⟨b, hb⟩ (m⁻¹ w),
      happAut (((e ⟨b, hb⟩ : ↥L) : MulAut W) (m⁻¹ w)), h1,
      hε ⟨b, hb⟩, h.equiv (ε' ⟨b, hb⟩) w, hε'val ⟨b, hb⟩]
  have hcent : ψ⁻¹ * mbarAut ∈ Subgroup.centralizer (L' : Set (MulAut W')) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hg : (ψ⁻¹ * mbarAut) * b * (ψ⁻¹ * mbarAut)⁻¹ = b := by
      have hc := hconj b hb
      calc (ψ⁻¹ * mbarAut) * b * (ψ⁻¹ * mbarAut)⁻¹
          = ψ⁻¹ * (mbarAut * b * mbarAut⁻¹) * ψ := by group
        _ = ψ⁻¹ * (ψ * b * ψ⁻¹) * ψ := by rw [hc]
        _ = b := by group
    calc b * (ψ⁻¹ * mbarAut) =
          ((ψ⁻¹ * mbarAut) * b * (ψ⁻¹ * mbarAut)⁻¹) * (ψ⁻¹ * mbarAut) := by rw [hg]
      _ = (ψ⁻¹ * mbarAut) * b := by group
  have hψeq : mbarAut = ψ := by
    have h1 : ψ⁻¹ * mbarAut = 1 := SixHyp.cent'_eq_one h _ hcent
    calc mbarAut = ψ * (ψ⁻¹ * mbarAut) := by group
      _ = ψ := by rw [h1, mul_one]
  exact ⟨m, hmM, fun w => (happAut w).symm.trans (by rw [hψeq])⟩

theorem s1611e3_six_swap
    (h : SixHyp M L L' κ e) {I₁ I₂ : Subgroup W'} (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (h₁ : AlternatingNatural L' I₁ ⊥ 6) (h₂ : AlternatingNatural L' I₂ ⊥ 6)
    (hne : ∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₁.map ψ.toMonoidHom ≠ I₂) :
    ∃ m ∈ M, ∀ w : W, κ w ∈ I₁ → κ ((m : MulAut W) w) ∈ I₂ := by
  obtain ⟨ψ, hψn, hψmap⟩ := s1611e3_six_swap_aut hinf hsup h₁ h₂ hne
  obtain ⟨m, hmM, hm⟩ := s1611e3_six_lift h ψ hψn
  refine ⟨m, hmM, fun w hw => ?_⟩
  rw [hm w]
  exact hψmap ▸ Subgroup.mem_map.mpr ⟨κ w, hw, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
