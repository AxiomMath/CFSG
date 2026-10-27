module

public import CFSG.RankThree.PartTwo.Sec11.WreathFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_WreathObs_comm_of_comm_eq_one {G : Type*} [Group G] {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ = 1) : x * y = y * x := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem aux_WreathObs_exists_noncentral_comm {w : W33} (hw : w.right ≠ 1) :
    ∃ b : W33, b.right = 1 ∧ b * w * b⁻¹ * w⁻¹ ∉ Subgroup.center W33 := by
  refine ⟨⟨fun x => if x = 1 then wreathT else 1, 1⟩, rfl, fun hc => ?_⟩
  obtain ⟨f, q⟩ := w
  have h := Subgroup.mem_center_iff.mp hc ⟨f, q⟩
  exact not_commute_commutator f q hw (congrArg RegularWreathProduct.left h.symm)

theorem false_of_wreath_obstruction {P : Type*} [Group P] [Finite P]
    {Q : Subgroup P} [Q.Normal] (e : P ⧸ Q ≃* W33) (R : Subgroup P) (g : P)
    (hRg : R ⊔ Subgroup.zpowers g = ⊤) (hR : R.index ≤ 3)
    (hRR : ∀ u ∈ R, ∀ v ∈ R, u * v * u⁻¹ * v⁻¹ ∈ Q)
    (Z : Subgroup P) (hZ : ∀ z ∈ Z, ∀ p : P, z * p * z⁻¹ * p⁻¹ ∈ Q)
    (hRgZ : ∀ u ∈ R, u * g * u⁻¹ * g⁻¹ ∈ Z) : False := by
  obtain ⟨piW, hpiW⟩ : ∃ f : P →* W33, f = e.toMonoidHom.comp (QuotientGroup.mk' Q) :=
    ⟨_, rfl⟩
  have hpi : Function.Surjective piW := by
    rw [hpiW]
    exact e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hpiQ : ∀ q ∈ Q, piW q = 1 := by
    intro q hq
    rw [hpiW]
    simp [QuotientGroup.eq_one_iff, hq]
  have hab : ∀ x ∈ R.map piW, ∀ y ∈ R.map piW, x * y = y * x := by
    rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    have h := hpiQ _ (hRR u hu v hv)
    simp only [map_mul, map_inv] at h
    exact aux_WreathObs_comm_of_comm_eq_one h
  have hBidx : (R.map piW).index ≤ 3 := by
    have hpos : 0 < R.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact le_trans (Nat.le_of_dvd hpos (R.index_map_dvd hpi)) hR
  have hBcard : Nat.card (R.map piW) * (R.map piW).index = 81 := by
    rw [Subgroup.card_mul_index, card_wreath]
  have h27 : 27 ≤ Nat.card (R.map piW) := by
    have := Nat.mul_le_mul (le_refl (Nat.card (R.map piW))) hBidx
    omega
  have hRright : ∀ u ∈ R, (piW u).right = 1 := fun u hu =>
    right_eq_one_of_abelian_of_card hab h27 (piW u) ⟨u, hu, rfl⟩
  have hT : wreathT ≠ 1 := by decide
  have hgright : (piW g).right ≠ 1 := by
    intro hg
    have hker : R ⊔ Subgroup.zpowers g ≤
        ((RegularWreathProduct.rightHom : W33 →* Multiplicative (ZMod 3)).comp piW).ker := by
      apply sup_le
      · intro u hu
        exact MonoidHom.mem_ker.mpr (hRright u hu)
      · rw [Subgroup.zpowers_le]
        exact MonoidHom.mem_ker.mpr hg
    rw [hRg] at hker
    obtain ⟨x, hx⟩ := hpi ⟨1, wreathT⟩
    have hx1 : (piW x).right = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))
    rw [hx] at hx1
    exact hT hx1
  have hcenZ : ∀ z ∈ Z, piW z ∈ Subgroup.center W33 := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨p, rfl⟩ := hpi y
    have h := hpiQ _ (hZ z hz p)
    simp only [map_mul, map_inv] at h
    exact (aux_WreathObs_comm_of_comm_eq_one h).symm
  have hcenB : ∀ x ∈ R.map piW, x * piW g * x⁻¹ * (piW g)⁻¹ ∈ Subgroup.center W33 := by
    rintro x ⟨u, hu, rfl⟩
    have h := hcenZ _ (hRgZ u hu)
    simpa only [map_mul, map_inv] using h
  have hBle : R.map piW ≤ (RegularWreathProduct.rightHom : W33 →* Multiplicative (ZMod 3)).ker := by
    rintro x ⟨u, hu, rfl⟩
    exact MonoidHom.mem_ker.mpr (hRright u hu)
  have hkercard : Nat.card
      (RegularWreathProduct.rightHom : W33 →* Multiplicative (ZMod 3)).ker = 27 := by
    have hsurj : Function.Surjective
        (RegularWreathProduct.rightHom : W33 →* Multiplicative (ZMod 3)) :=
      fun c => ⟨⟨1, c⟩, rfl⟩
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    rw [card_wreath] at h
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
    rw [h3] at h
    omega
  have hBeq : R.map piW = (RegularWreathProduct.rightHom : W33 →* Multiplicative (ZMod 3)).ker :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [hkercard]; exact h27)
  obtain ⟨b, hbr, hbnc⟩ := aux_WreathObs_exists_noncentral_comm hgright
  have hbB : b ∈ R.map piW := by
    rw [hBeq]
    exact MonoidHom.mem_ker.mpr hbr
  exact hbnc (hcenB b hbB)

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
