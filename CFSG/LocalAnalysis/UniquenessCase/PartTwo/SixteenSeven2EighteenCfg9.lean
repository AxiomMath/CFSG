module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Inv
public import CFSG.Quasithin.EmptyFaithful.F918C15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_cfg9_abstract (hW : ∀ w : W, w ^ 2 = 1) {X L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L (commSub (⊤ : Subgroup W) L) ⊥ 3)
    (hcls : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom} = 2)
    (horb : (conjSubs X (commSub (⊤ : Subgroup W) L)).ncard = 2)
    (hind : sSupIndep (conjSubs X (commSub (⊤ : Subgroup W) L)))
    (hsup : sSup (conjSubs X (commSub (⊤ : Subgroup W) L)) = ⊤) :
    (∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), rk ↥I = 9) ∧
      (∀ t ∈ X, ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
        I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥) ∧
      (∀ t ∈ X, t * t = 1 → ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
        I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
          3 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t))) ∧
      3 ≤ E3.mParam X := by
  obtain ⟨I₁, I₂, hne, hset⟩ := Set.ncard_eq_two.1 horb
  have hdisj : I₁ ⊓ I₂ = ⊥ :=
    disjoint_iff.mp ((sSupIndep_pair hne).mp (hset ▸ hind))
  have hsup' : I₁ ⊔ I₂ = ⊤ := by
    have h : sSup ({I₁, I₂} : Set (Subgroup W)) = ⊤ := by rw [← hset]; exact hsup
    rwa [sSup_pair] at h
  have hN : NatSum3 L (commSub (⊤ : Subgroup W) L) := s16c167_natSum3_of_sumOfNat hsum
  have hrk0 : rk ↥(commSub (⊤ : Subgroup W) L) = 9 := s16c167_rk_natSum3 hN
  have hrank : ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), rk ↥I = 9 := by
    intro I hI
    obtain ⟨φ, hφX, rfl⟩ := hI
    rw [rk_map_aut_eq]
    exact hrk0
  have hperm' : ∀ t ∈ X, ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥ := by
    intro t htX I hI
    exact s16c167_perm_of_orbit hne hdisj hset t htX I (hset ▸ hI)
  have hloc' : ∀ t ∈ X, t * t = 1 → ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
      I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
        3 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
    intro t htX ht I hI hstab
    obtain ⟨φ, hφX, rfl⟩ := hI
    have hcomm := s16c167_commSub_top_conj φ L
    rw [← hcomm] at hstab ⊢
    have hY : IsPSL 3 2 1 ↥(L.map (MulAut.conj φ).toMonoidHom) := isPSL_conjAutSub φ hL
    have hYsum : NatSum3 (L.map (MulAut.conj φ).toMonoidHom)
        (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom)) := by
      rw [hcomm]
      exact s16c167_natSum3_conj hN φ
    have hn' : (L.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        L.map (MulAut.conj φ).toMonoidHom :=
      s16c167_normalizes_of_stab hcls horb (L.map (MulAut.conj φ).toMonoidHom)
        ⟨φ, hφX, rfl⟩ t htX hstab
    exact s16c167_natSum3_involution hW hY hYsum ht hn' hstab
  have hI₁ : I₁ ∈ conjSubs X (commSub (⊤ : Subgroup W) L) := by rw [hset]; simp
  have hI₂ : I₂ ∈ conjSubs X (commSub (⊤ : Subgroup W) L) := by rw [hset]; simp
  have hn₁ : 3 ≤ rk ↥I₁ := by have := hrank I₁ hI₁; omega
  have hn₂ : 3 ≤ rk ↥I₂ := by have := hrank I₂ hI₂; omega
  have hperm : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥ := by
    intro t htX _ I hI
    exact hperm' t htX I (hset ▸ hI)
  have hloc : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
        3 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
    intro t htX ht I hI
    exact hloc' t htX ht I (hset ▸ hI)
  exact ⟨hrank, hperm', hloc',
    s16c167_le_mParam_of_blocks hW X (n := 3) hdisj hsup' hn₁ hn₂ hperm hloc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
