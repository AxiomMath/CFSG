module

public import CFSG.Quasithin.H13.GoldschmidtC137Data

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem rkIdx_fixV_conjAut {W : Type*} [CommGroup W] (g : MulAut W) (Y : Subgroup (MulAut W)) :
    rkIdx (fixV (B1.conjAut g Y)) = rkIdx (fixV Y) := by
  unfold rkIdx
  rw [B1.fixV_conjAut]
  exact congrArg (padicValNat 2) (Subgroup.index_map_equiv (fixV Y) g)

theorem conjAut_one_gc {W : Type*} [CommGroup W] (Y : Subgroup (MulAut W)) :
    B1.conjAut 1 Y = Y := by
  ext x
  simp [B1.mem_conjAut]

theorem starPreIn_self {V R : Subgroup G} (hV : IsElemAbelian 2 V)
    (hRN : R ≤ normalizer (V : Set G)) : starPreIn hV R (autI hV R) = R := by
  ext g
  rw [mem_starPreIn]
  constructor
  · rintro ⟨hg, -⟩
    exact hg
  · intro hg
    exact ⟨hg, hRN hg, convI_mem_autI hV hg (hRN hg)⟩

theorem hDE_of_pieces [Finite G] {X L R V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ normalizer (V : Set G)) (hLX : L ≤ X) (hRX : R ≤ X) (hR : IsPGroup 2 R)
    (hA₂ : IsSylowTwoOf (R ⊓ centralizer (V : Set G)) ((L ⊔ R) ⊓ centralizer (V : Set G)))
    (hJR : autI hV (thompsonJ R) = autI hV R) {m : ℕ} (A₀ : Fin m → Subgroup G)
    (hA₀ : ∀ i, IsMaxElemAbelian R (A₀ i)) (c : Fin m → MulAut (IntMod V hV))
    (hc : ∀ i, c i ∈ autI hV L)
    (hgen : autI hV L ≤ autI hV R ⊔ ⨆ i, B1.conjAut (c i) (autI hV (A₀ i)))
    (hsum : rkIdx (fixV (autI hV R)) + ∑ i, rkIdx (fixV (autI hV (A₀ i))) ≤
      rkIdx (fixV (autI hV L))) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI hV L, B1.conjAut g (Y i) ≤ autI hV R) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn hV (L ⊔ R) (Y i))) ∧
      (∀ i, Y i = autI hV (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 R) ∧
      autI hV L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV L)) ∧
      ∀ A, IsFFStarOffender (autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V hV))),
          A = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI hV R) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI hV L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI hV R := by
  have hRN : R ≤ normalizer (V : Set G) := hRX.trans hXN
  have hLRN : L ⊔ R ≤ normalizer (V : Set G) := (sup_le hLX hRX).trans hXN
  have hex : ∀ i, ∃ l : G, ∃ hl : l ∈ normalizer (V : Set G), l ∈ L ∧ convI hV ⟨l, hl⟩ = c i := by
    intro i
    obtain ⟨l, hlL, hlc⟩ := (mem_autI hV).1 (hc i)
    exact ⟨l, l.2, hlL, hlc⟩
  choose ℓ hℓN hℓL hℓc using hex
  have hpieces := fun i => exists_Dpiece hV hXN hLX hRX hR hA₂ (hA₀ i) (hℓL i)
  have hS0 : IsSylowTwoOf R (starPreIn hV (L ⊔ R) (autI hV R)) := by
    have := isSylowTwoOf_starPreIn hV (le_sup_right : R ≤ L ⊔ R) hLRN hR hA₂ (le_refl (autI hV R))
    rwa [starPreIn_self hV hRN] at this
  refine ⟨m + 1, Fin.cons (autI hV R) (fun i => B1.conjAut (c i) (autI hV (A₀ i))),
    Fin.cons R (fun i => cjSub (ℓ i) (starPreIn hV R (autI hV (A₀ i)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨1, (autI hV L).one_mem, by simp only [Fin.cons_zero, conjAut_one_gc]; exact le_rfl⟩
    · refine ⟨(c i)⁻¹, Subgroup.inv_mem _ (hc i), ?_⟩
      simp only [Fin.cons_succ]
      rw [B1.conjAut_inv_conjAut]
      exact autI_mono hV (hA₀ i).1
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨hRX, by simpa using hS0⟩
    · obtain ⟨hX, hS, -, -⟩ := hpieces i
      simp only [Fin.cons_succ]
      refine ⟨hX, ?_⟩
      rwa [hℓc i] at hS
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hJR.symm
    · obtain ⟨-, -, hJ, -⟩ := hpieces i
      simp only [Fin.cons_succ]
      rwa [hℓc i] at hJ
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [Fin.cons_succ]
      exact (hpieces i).2.2.2
  · refine hgen.trans (sup_le ?_ (iSup_le fun i => ?_))
    · exact le_iSup (fun j : Fin (m + 1) => (Fin.cons (autI hV R)
        (fun i => B1.conjAut (c i) (autI hV (A₀ i))) : Fin (m + 1) → _) j) 0
    · exact le_iSup (fun j : Fin (m + 1) => (Fin.cons (autI hV R)
        (fun i => B1.conjAut (c i) (autI hV (A₀ i))) : Fin (m + 1) → _) j) i.succ
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, rkIdx_fixV_conjAut]
    exact hsum
  · intro A hA
    refine ⟨1, fun _ => A, (iSup_const).symm, fun _ => ⟨hA, 0, 1, (autI hV L).one_mem, ?_, ?_⟩⟩
    · simp only [Fin.cons_zero, conjAut_one_gc]
      exact hA.1
    · simp only [Fin.cons_zero, conjAut_one_gc]
      exact le_rfl

end CFSG.Quasithin.H13.U3.GC137
