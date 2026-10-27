module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_mem_not_mem_zpowers (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a : G} (ha : a ∈ B) (ha1 : a ≠ 1) :
    ∃ b ∈ B, b ∉ Subgroup.zpowers a := by
  by_contra! hcon
  have hle : B ≤ Subgroup.zpowers a := fun b hb => hcon b hb
  have h1 := Subgroup.card_le_of_le hle
  rw [hB.2, h.card_zpowers (hB.1 ha) ha1] at h1
  have : p < p ^ 2 := by nlinarith [h.prime.one_lt]
  omega

theorem zpowers_sup_eq (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hba : b ∉ Subgroup.zpowers a) : Subgroup.zpowers a ⊔ Subgroup.zpowers b = B := by
  have hb1 : b ≠ 1 := fun hb1 => hba (hb1 ▸ one_mem _)
  have hE := h.zpowers_mem_E1 (hB.1 ha) ha1
  have hF := h.zpowers_mem_E1 (hB.1 hb) hb1
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := fun heq =>
    hba (heq ▸ Subgroup.mem_zpowers b)
  have hsup := h.sup_mem_E2_of_ne hE hF hne
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hB.2, hsup.2])

theorem thetaOf_plane_eq (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hba : b ∉ Subgroup.zpowers a) : thetaOf θ B = θ a ⊓ Subgroup.centralizer {b} := by
  have hE := h.zpowers_mem_E1 (hB.1 ha) ha1
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr (hB.1 hb)
  have h1 := h.thetaOf_line_inf_centralizer hE hFA
  rw [zpowers_sup_eq h hB ha ha1 hb hba, h.isFunctor.thetaOf_zpowers (hB.1 ha) ha1,
    centralizer_zpowers_eq_singleton] at h1
  exact h1.symm

theorem lcal_plane_eq
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hba : b ∉ Subgroup.zpowers a) :
    lcal (thetaOf θ B) = {Y | ∃ L ∈ lcal (θ a), Y = smear L (Subgroup.zpowers b)} := by
  have ha' : a ∈ A := hB.1 ha
  have hb1 : b ≠ 1 := fun hb1 => hba (hb1 ▸ one_mem _)
  have hE := h.zpowers_mem_E1 ha' ha1
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr (hB.1 hb)
  have hΩ := h.isRegFam_line_of_typeA hA hE
  rw [h.isFunctor.thetaOf_zpowers ha' ha1] at hΩ
  have hFN : Subgroup.zpowers b ⊓ Subgroup.zpowers a = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_not_le h.prime (h.card_zpowers (hB.1 hb) hb1) (fun hle => hba (hle
      (Subgroup.mem_zpowers b)))
  have hsm := hΩ.smear_family h.elemAbelian.1 hFA hFN
  have hH : θ a ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      thetaOf θ B := by
    rw [centralizer_zpowers_eq_singleton]
    exact (thetaOf_plane_eq h hB ha ha1 hb hba).symm
  rw [hH] at hsm
  have hsingle : ∀ L' ∈ lcal (θ a), lcal (smear L' (Subgroup.zpowers b)) =
      {smear L' (Subgroup.zpowers b)} := by
    intro L' hL'
    obtain ⟨e⟩ := hΩ.nonempty_mulEquiv_smear hFA hFN hL'
    obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hL'
    exact lcal_eq_singleton_self e.isSimpleGroup
      fun hc => hnc ((isMulCommutative_congr e).mp hc)
  ext J
  rw [mem_lcal_iff_of_isDirectProduct hsm.isDirectProduct]
  constructor
  · rintro ⟨Y, ⟨L', hL', rfl⟩, hJ⟩
    rw [hsingle L' hL'] at hJ
    exact ⟨L', hL', hJ⟩
  · rintro ⟨L', hL', rfl⟩
    exact ⟨smear L' (Subgroup.zpowers b), ⟨L', hL', rfl⟩, by
      rw [hsingle L' hL']
      exact Set.mem_singleton _⟩

theorem smear_mem_lcal_plane
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hba : b ∉ Subgroup.zpowers a) {L' : Subgroup G} (hL' : L' ∈ lcal (θ a)) :
    smear L' (Subgroup.zpowers b) ∈ lcal (thetaOf θ B) := by
  rw [lcal_plane_eq h hA hB ha ha1 hb hba]
  exact ⟨L', hL', rfl⟩

theorem commute_of_mem_lcal_plane
    (h : Counterexample p A θ) (hA : TypeA p A θ)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hba : b ∉ Subgroup.zpowers a) {L' : Subgroup G} (hL' : L' ∈ lcal (θ a))
    {K : Subgroup G} (hK : K ∈ lcal (thetaOf θ B)) (hne : K ≠ smear L' (Subgroup.zpowers b)) :
    ∀ x ∈ K, ∀ y ∈ L', y * x = x * y := by
  have ha' : a ∈ A := hB.1 ha
  have hb1 : b ≠ 1 := fun hb1 => hba (hb1 ▸ one_mem _)
  have hE := h.zpowers_mem_E1 ha' ha1
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr (hB.1 hb)
  have hΩ := h.isRegFam_line_of_typeA hA hE
  rw [h.isFunctor.thetaOf_zpowers ha' ha1] at hΩ
  have hF : ∀ f ∈ Subgroup.zpowers b, ∀ J ∈ lcal (θ a),
      J.map (MulAut.conj f).toMonoidHom ∈ lcal (θ a) := fun f hf J hJ =>
    hΩ.map_conj_mem f (hFA hf) J hJ
  rw [lcal_plane_eq h hA hB ha ha1 hb hba] at hK
  obtain ⟨L'', hL'', rfl⟩ := hK
  have hnot : L'' ∉ RegFam.conjOrbit L' (Subgroup.zpowers b) := by
    intro hmem
    apply hne
    have h1 : orbitClosure L'' (Subgroup.zpowers b) = orbitClosure L' (Subgroup.zpowers b) := by
      rw [RegFam.orbitClosure_eq_sSup_conjOrbit, RegFam.orbitClosure_eq_sSup_conjOrbit,
        RegFam.conjOrbit_eq_of_mem hmem]
    simp only [smear, h1]
  intro x hx y hy
  have hcomm := RegFam.commute_orbitClosure hΩ.isDirectProduct hF hL' hL'' hnot
  exact (hcomm y (le_orbitClosure L' _ hy) x (smear_le_orbitClosure L'' _ hx)).eq

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
