module

public import CFSG.Quasithin.Vol2.Ch11SecHKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem det_eq_one_of_mem_statedSL {F : Type} [Field F] {n : ℕ} {B : GL (Fin n) F}
    (hB : B ∈ StatedSL n F) : (B : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hB

theorem exists_coords {W : Type*} [CommGroup W] {F : Type} [Field F] {Hs : Subgroup (MulAut W)}
    {π : ↥(StatedSL 3 F) →* ↥Hs} (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia Hs ⊤ ⊥ π) :
    ∃ φ : W → (Fin 3 → F), (∀ a b, φ (a * b) = φ a + φ b) ∧ Function.Bijective φ ∧
      ∀ (γ : ↥(StatedSL 3 F)) (w : W),
        φ ((π γ : MulAut W) w) =
          ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ w) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.exists_natMap hπ
  refine ⟨fun w => Multiplicative.toAdd (f ⟨w, trivial⟩), fun a b => ?_, ⟨?_, ?_⟩,
    fun γ w => ?_⟩
  · show Multiplicative.toAdd (f ⟨a * b, trivial⟩) =
      Multiplicative.toAdd (f ⟨a, trivial⟩) + Multiplicative.toAdd (f ⟨b, trivial⟩)
    rw [← toAdd_mul, ← map_mul]
    rfl
  · intro a b hab
    have hf : f ⟨a, trivial⟩ = f ⟨b, trivial⟩ := hab
    have h1 : f (⟨a, trivial⟩ * (⟨b, trivial⟩ : ↥(⊤ : Subgroup W))⁻¹) = 1 := by
      rw [map_mul, map_inv, hf, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp ((hfk _).mp h1)
    exact mul_inv_eq_one.mp h2
  · intro x
    obtain ⟨⟨w, _⟩, hw⟩ := hfs (Multiplicative.ofAdd x)
    exact ⟨w, by simp [hw]⟩
  · have := hfe γ ⟨w, trivial⟩ trivial
    simp only [natAct] at this
    show Multiplicative.toAdd (f ⟨(π γ : MulAut W) w, trivial⟩) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (f ⟨w, trivial⟩))
    rw [this]
    rfl

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem conjAct_P_mem (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) (π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I)))
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π)
    {p : G} (hp : p ∈ pOf T I H h) (hpN : p ∈ Subgroup.normalizer (fsuV T I : Set G)) :
    conjAct (fsuV T I) ⟨p, hpN⟩ ∈ autOn L (fsuV T I) := by
  obtain ⟨b, hb, b', hb', rfl⟩ := (d.mem_P_iff i).mp hp
  have hbN : b ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    Subgroup.le_normalizer ((inf_le_left : bOf T I H ≤ fsuV T I) hb)
  have hb'N := d.Bh_le_normalizer_V i hb'
  have hsplit : conjAct (fsuV T I) ⟨b * b', hpN⟩ =
      conjAct (fsuV T I) ⟨b, hbN⟩ * conjAct (fsuV T I) ⟨b', hb'N⟩ := by
    rw [← map_mul]
    rfl
  have hb1 : conjAct (fsuV T I) ⟨b, hbN⟩ = 1 :=
    (conjAct_eq_one_iff _ _).mpr (d.B_le_centralizer_V hb)
  rw [hsplit, hb1, one_mul]
  have hσB : conjAct (fsuV T I) ⟨b', hb'N⟩ ∈ autOn (conjSubgroup (bOf T I H) h) (fsuV T I) :=
    ⟨⟨b', hb'N⟩, Subgroup.mem_subgroupOf.mpr hb', rfl⟩
  refine i.hKF1 F n d.c.two_le hF ↥(fsuV T I) d.sq_fsuV _ π hπ _
    (d.autOn_Bh_le_normalizer i hσB) (d.autOn_Bh_sq _ hσB) ?_
  rw [d.card_fsuV, ← card_B_subgroupOf T I H]
  refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
    (fun u : ↥((bOf T I H).subgroupOf (fsuV T I)) =>
      (⟨u.1, d.autOn_Bh_fix i _ hσB u.1 u.2⟩ :
        {w : ↥(fsuV T I) // conjAct (fsuV T I) ⟨b', hb'N⟩ w = w})) ?_)
  intro u₁ u₂ hu
  have h' : (u₁ : ↥(fsuV T I)) = u₂ :=
    congrArg (fun w : {w : ↥(fsuV T I) // conjAct (fsuV T I) ⟨b', hb'N⟩ w = w} => w.1) hu
  exact Subtype.ext h'

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
