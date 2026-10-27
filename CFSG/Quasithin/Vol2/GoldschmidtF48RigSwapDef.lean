module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Transport

variable {D : Type} [Group D]

theorem isTwoLocal_map_aut (φ : MulAut D) {M : Subgroup D} (h : IsTwoLocal M) :
    IsTwoLocal (M.map φ.toMonoidHom) := by
  obtain ⟨P, hP, hPp, rfl⟩ := h
  refine ⟨P.map φ.toMonoidHom, fun hbot => hP ?_, hPp.map _, ?_⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective P
      (show Function.Injective φ.toMonoidHom from φ.injective)).1 hbot
  · exact Subgroup.map_equiv_normalizer_eq P φ

theorem map_aut_map_inv (φ : MulAut D) (M : Subgroup D) :
    (M.map φ.toMonoidHom).map φ⁻¹.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

theorem isMaximalTwoLocal_map_aut (φ : MulAut D) {M : Subgroup D} (h : IsMaximalTwoLocal M) :
    IsMaximalTwoLocal (M.map φ.toMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨isTwoLocal_map_aut φ h1, fun M' hM' hle => ?_⟩
  have h3 : IsTwoLocal (M'.map φ⁻¹.toMonoidHom) := isTwoLocal_map_aut φ⁻¹ hM'
  have h4 : M ≤ M'.map φ⁻¹.toMonoidHom := by
    intro g hg
    rw [Subgroup.mem_map]
    exact ⟨φ g, hle ⟨g, hg, rfl⟩, by simp⟩
  have h5 := h2 _ h3 h4
  have h6 : M' = (M'.map φ⁻¹.toMonoidHom).map φ.toMonoidHom := by
    simpa using (map_aut_map_inv φ⁻¹ M').symm
  rw [h6, h5]

theorem mem_autStab_iff_map (φ : MulAut D) (P : Subgroup D) :
    φ ∈ autStab P ↔ P.map φ.toMonoidHom = P := by
  constructor
  · intro h
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mp hy
    · intro hx
      refine ⟨φ⁻¹ x, ?_, by simp⟩
      exact (h (φ⁻¹ x)).mpr (by simpa using hx)
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := φ.injective hyx
      rwa [this] at hy

theorem yamPair_symm {T P Q : Subgroup D} (h : IsYAmalgamPair T P Q) : IsYAmalgamPair T Q P :=
  ⟨h.1, fun e => h.2.1 e.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem autStab_snd_of_fst {T P Q : Subgroup D} (h : IsYAmalgamPair T P Q) {φ : MulAut D}
    (hB : φ ∈ autStab (P ⊓ Q)) (h1 : φ ∈ autStab P) : φ ∈ autStab Q := by
  have hP := (h.2.2 P).mpr (Or.inl rfl)
  have hQ := (h.2.2 Q).mpr (Or.inr rfl)
  have hM : IsMaximalTwoLocal (Q.map φ.toMonoidHom) := isMaximalTwoLocal_map_aut φ hQ.1
  have hN : Subgroup.normalizer (T : Set D) ≤ Q.map φ.toMonoidHom := by
    intro x hx
    have hxB : x ∈ P ⊓ Q := ⟨hP.2 hx, hQ.2 hx⟩
    refine ⟨φ⁻¹ x, ?_, by simp⟩
    exact ((hB (φ⁻¹ x)).mpr (by simpa using hxB)).2
  rcases (h.2.2 _).mp ⟨hM, hN⟩ with e | e
  · exfalso
    have h1' := (mem_autStab_iff_map φ P).mp h1
    exact h.2.1 (Subgroup.map_injective (show Function.Injective φ.toMonoidHom from
      φ.injective) (h1'.trans e.symm))
  · exact (mem_autStab_iff_map φ Q).mpr e

end Transport

namespace LieAmalgamExt

variable {D : Type} [Group D] (A : LieAmalgamExt D)

@[expose] def swap : LieAmalgamExt D where
  Mbar := A.Mbar
  TD := A.TD
  P1 := A.P2
  P2 := A.P1
  inn_le := A.inn_le
  yam := yamPair_symm A.yam
  diag φ hφ hB := by
    rw [inf_comm] at hB
    exact autStab_snd_of_fst A.yam hB (A.diag φ hφ hB)

@[simp] theorem swap_Mbar : A.swap.Mbar = A.Mbar := rfl

@[simp] theorem swap_TD : A.swap.TD = A.TD := rfl

@[simp] theorem swap_P1 : A.swap.P1 = A.P2 := rfl

@[simp] theorem swap_P2 : A.swap.P2 = A.P1 := rfl

@[simp] theorem swap_N1 : A.swap.N1 = A.N2 := rfl

@[simp] theorem swap_N2 : A.swap.N2 = A.N1 := rfl

theorem swap_K : A.swap.K = A.K := sup_comm _ _

@[expose] def swapKEquiv : ↥A.K ≃* ↥A.swap.K := MulEquiv.subgroupCongr A.swap_K.symm

@[simp] theorem coe_swapKEquiv (k : ↥A.K) : ((A.swapKEquiv k : ↥A.swap.K) : MulAut D) = k := rfl

end LieAmalgamExt

@[expose] def swapSubIso {X Z : Type} [Group X] [Group Z] {P1 P2 : Subgroup X}
    {Q1 Q2 : Subgroup Z}
    (e : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups Q1 Q2)) :
    (RankTwoAmalgam.ofSubgroups P2 P1).Iso (RankTwoAmalgam.ofSubgroups Q2 Q1) where
  φ1 := e.φ2
  φ12 := (MulEquiv.subgroupCongr (inf_comm P2 P1)).trans
    (e.φ12.trans (MulEquiv.subgroupCongr (inf_comm Q1 Q2)))
  φ2 := e.φ1
  comm1 g := e.comm2 (MulEquiv.subgroupCongr (inf_comm P2 P1) g)
  comm2 g := e.comm1 (MulEquiv.subgroupCongr (inf_comm P2 P1) g)

namespace LieExt

variable {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}

@[expose] def swap (E : LieExt D M1 M2) : LieExt D M2 M1 :=
  { E.toLieAmalgamExt.swap with iso := swapSubIso E.iso }

@[simp] theorem swap_toLieAmalgamExt (E : LieExt D M1 M2) :
    E.swap.toLieAmalgamExt = E.toLieAmalgamExt.swap := rfl

@[simp] theorem swap_phi1 (E : LieExt D M1 M2) : E.swap.phi1 = E.phi2 := rfl

@[simp] theorem swap_phi2 (E : LieExt D M1 M2) : E.swap.phi2 = E.phi1 := rfl

end LieExt

end CFSG.Quasithin.H13.F431
