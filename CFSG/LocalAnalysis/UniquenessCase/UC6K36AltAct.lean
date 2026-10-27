module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltOrb
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup Equiv Equiv.Perm

namespace Alt36

section AutPerm

variable {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)

@[expose] noncomputable def autPerm : MulAut (alternatingGroup (Fin n)) ≃* Perm (Fin n) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).symm

theorem conjNormal_autPerm (α : MulAut (alternatingGroup (Fin n))) :
    MulAut.conjNormal (H := alternatingGroup (Fin n)) (autPerm hn hn6 α) = α :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).apply_symm_apply α

theorem autPerm_apply_coe (α : MulAut (alternatingGroup (Fin n))) (k : alternatingGroup (Fin n)) :
    ((α k : alternatingGroup (Fin n)) : Perm (Fin n)) = autPerm hn hn6 α * k * (autPerm hn hn6 α)⁻¹ := by
  conv_lhs => rw [← conjNormal_autPerm hn hn6 α]
  rw [MulAut.conjNormal_apply]

theorem autPerm_conj (k : alternatingGroup (Fin n)) :
    autPerm hn hn6 (MulAut.conj k) = (k : Perm (Fin n)) := by
  apply (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).injective
  change MulAut.conjNormal (H := alternatingGroup (Fin n)) (autPerm hn hn6 (MulAut.conj k)) =
    MulAut.conjNormal (H := alternatingGroup (Fin n)) (k : Perm (Fin n))
  rw [conjNormal_autPerm hn hn6]
  ext x
  rw [MulAut.conj_apply, MulAut.conjNormal_apply]
  rfl

end AutPerm

section Theta

variable {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
  (φ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))

@[expose] noncomputable def theta : G →* Perm (Fin n) :=
  (autPerm hn hn6).toMonoidHom.comp (Odd.psi L φ)

theorem psi_apply_coe (g : G) (k : alternatingGroup (Fin n)) :
    ((Odd.psi L φ g k : alternatingGroup (Fin n)) : Perm (Fin n)) =
      theta L hn hn6 φ g * k * (theta L hn hn6 φ g)⁻¹ :=
  autPerm_apply_coe hn hn6 _ k

theorem psi_fix_iff (g : G) (k : alternatingGroup (Fin n)) :
    Odd.psi L φ g k = k ↔ theta L hn hn6 φ g * k = k * theta L hn hn6 φ g := by
  rw [← Subtype.coe_inj, psi_apply_coe L hn hn6 φ]
  constructor
  · intro h
    calc theta L hn hn6 φ g * k = theta L hn hn6 φ g * k * (theta L hn hn6 φ g)⁻¹ * theta L hn hn6 φ g := by
          group
      _ = k * theta L hn hn6 φ g := by rw [h]
  · intro h
    rw [h]
    group

theorem theta_of_mem {y : G} (hy : y ∈ L) :
    theta L hn hn6 φ y = (φ (QuotientGroup.mk ⟨y, hy⟩) : Perm (Fin n)) := by
  change autPerm hn hn6 (Odd.psi L φ y) = _
  rw [Odd.psi_eq_conj L φ hy, autPerm_conj]

theorem theta_eq_one_iff (g : G) :
    theta L hn hn6 φ g = 1 ↔ ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ Odd.centerOf L := by
  constructor
  · intro h y hy
    rw [← Odd.psi_mk_eq_iff L φ g y hy, ← Subtype.coe_inj, psi_apply_coe L hn hn6 φ, h]
    simp
  · intro h
    have hpsi : Odd.psi L φ g = 1 := by
      refine MulEquiv.ext fun k => ?_
      obtain ⟨c, rfl⟩ := φ.surjective k
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective c
      rw [(Odd.psi_mk_eq_iff L φ g y hy).2 (h y hy)]
      rfl
    change autPerm hn hn6 (Odd.psi L φ g) = 1
    rw [hpsi, map_one]

end Theta

end Alt36

namespace Hyp36

open Alt36 Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem centClosure_le_mImage (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (φ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n)) :
    centClosure (E.map (theta L hn hn6 φ)) ≤ (mImage L φ M).map (alternatingGroup (Fin n)).subtype := by
  rw [centClosure, Subgroup.closure_le]
  rintro g ⟨hg, _, ⟨e, he, rfl⟩, he1, hcomm⟩
  have he1' : e ≠ 1 := by
    rintro rfl
    exact he1 (map_one _)
  have hfix : Odd.psi L φ e ⟨g, hg⟩ = ⟨g, hg⟩ := (psi_fix_iff L hn hn6 φ e ⟨g, hg⟩).2 hcomm.symm
  obtain ⟨hmem, -⟩ := h.exists_mem_of_fixed L φ he he1' hfix
  exact ⟨⟨g, hg⟩, hmem, rfl⟩

theorem le_of_alternatingGroup_le_centClosure (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal]
    (hLc : commutator ↥L = ⊤) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))
    (hA : alternatingGroup (Fin n) ≤ centClosure (E.map (theta L hn hn6 φ))) : L ≤ M := by
  refine le_of_mImage_eq_top L φ hLc (eq_top_iff.2 fun k _ => ?_)
  obtain ⟨k', hk', hkk'⟩ := h.centClosure_le_mImage L hn hn6 φ (hA k.2)
  rwa [← Subtype.ext hkk']

theorem normalizes_centralizer_qbar (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (φ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n)) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) :
    ∀ k ∈ alternatingGroup (Fin n), k * theta L hn hn6 φ e = theta L hn hn6 φ e * k →
      ∀ r ∈ (pCoreOf 2 M).map (theta L hn hn6 φ) ⊓
        Subgroup.centralizer ({theta L hn hn6 φ e} : Set (Perm (Fin n))),
      k * r * k⁻¹ ∈ (pCoreOf 2 M).map (theta L hn hn6 φ) ⊓
        Subgroup.centralizer ({theta L hn hn6 φ e} : Set (Perm (Fin n))) := by
  intro k hk hke r hr
  have hfix : Odd.psi L φ e ⟨k, hk⟩ = ⟨k, hk⟩ := (psi_fix_iff L hn hn6 φ e ⟨k, hk⟩).2 hke.symm
  obtain ⟨-, m, hm, hconj⟩ := h.exists_mem_of_fixed L φ he he1 hfix
  have hθm : theta L hn hn6 φ m = k := by
    change autPerm hn hn6 (Odd.psi L φ m) = k
    rw [← hconj, autPerm_conj]
  obtain ⟨hrQ, hrC⟩ := Subgroup.mem_inf.1 hr
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hrQ
    rw [← hθm, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.2 ⟨m * q * m⁻¹, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm.1) q).1 hq
  · rw [Subgroup.mem_centralizer_singleton_iff] at hrC ⊢
    have hk' : Commute k (theta L hn hn6 φ e) := hke
    have hr' : Commute r (theta L hn hn6 φ e) := hrC
    exact ((hk'.mul_left hr').mul_left hk'.inv_left).eq

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
