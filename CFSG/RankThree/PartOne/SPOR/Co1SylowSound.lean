module

public import CFSG.RankThree.PartOne.SPOR.Co1SylowData
public import CFSG.RankThree.PartOne.SPOR.Co1PlanesSound
public import CFSG.Sporadic.Co1Block.Tools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2

section Sound

variable {A : Type} [Group A] (ι : A →* GL24)

@[expose] def sylowMat : A →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp ι

theorem sylowMat_apply (a : A) :
    sylowMat ι a = ((ι a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := rfl

theorem sylowMat_injective (hι : Function.Injective ι) : Function.Injective (sylowMat ι) :=
  fun _ _ h => hι (Units.ext h)

theorem gtOK_valid {G : Array (Array ℕ)} {T : GTree} (h : gtOK G T = true) :
    ∀ i < T.pts.size, validRows T.pts[i]! = true := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩, -⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  intro i hi
  have hp := hpt i (Nat.zero_le _) hi
  simp only [gtPointOK, Bool.and_eq_true] at hp
  exact hp.1

theorem co1Sylow_sound [Finite A] (hι : Function.Injective ι) {baseG : List GL24}
    (hbase : List.Forall₂ MRep co1PlaneBase baseG) (hmem : ∀ g ∈ baseG, ∃ a : A, ι a = g)
    {derivs : List (List Int)} {i₁ i₂ j : ℕ} (h : co1SylowOK derivs i₁ i₂ j = true) :
    ∃ (P : Subgroup A) (x : A), Nat.card P = 625 ∧ x ^ 5 = 1 ∧
      ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z ∈ Subgroup.zpowers x := by
  simp only [co1SylowOK, co1SylowCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_assoc] at h
  obtain ⟨hflag, h1, h2, h3, h4, h5, h6, hv1, hv2, hvj, hgt, hcard, hcen, hx5⟩ := h
  have hR := dag_rep hbase derivs hflag
  have hsurj : ∀ g ∈ dagG baseG derivs, ∃ a : A, ι a = g := fun g hg => by
    have := dagG_mem (H := ι.range) (fun g hg => by
      obtain ⟨a, ha⟩ := hmem g hg
      exact ⟨a, ha⟩) derivs g hg
    exact this
  set R := (Native.dag co1PlaneBase derivs).1 with hRdef
  have hG1 : MRep (R.getD (i₁ - 1) Native.one) (ι (eltA ι hsurj i₁)) := rep_eltA ι hR hsurj i₁
  have hG2 : MRep (R.getD (i₂ - 1) Native.one) (ι (eltA ι hsurj i₂)) := rep_eltA ι hR hsurj i₂
  have hXj : MRep (R.getD (j - 1) Native.one) (ι (eltA ι hsurj j)) := rep_eltA ι hR hsurj j
  set Gs : Array (Array ℕ) := #[R.getD (i₁ - 1) Native.one, R.getD (i₂ - 1) Native.one] with hGs
  set T := gtBFS Gs 700 with hT
  let gg : ℕ → A := fun l => if l = 0 then eltA ι hsurj i₁ else eltA ι hsurj i₂
  have hgg : ∀ l < Gs.size, sylowMat ι (gg l) = rowsMatrix 24 Gs[l]! := by
    intro l hl
    have hl' : l < 2 := by simpa [hGs] using hl
    interval_cases l
    · exact hG1.symm
    · exact hG2.symm
  have hμ := sylowMat_injective ι hι
  have hvalid := gtOK_valid hgt
  refine ⟨Subgroup.closure (gg '' {l | l < Gs.size}), eltA ι hsurj j, ?_, ?_, ?_⟩
  · exact (prodTree_card (sylowMat ι) hμ hgt gg hgg).trans hcard
  · apply hι
    rw [map_pow, map_one]
    have hp := hXj.pow 5
    rw [hx5] at hp
    exact hp.eq MRep.one
  · intro z hz hcomm
    obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq (sylowMat ι) hμ hgt gg hgg
    have hz' : z ∈ (Subgroup.closure (gg '' {l | l < Gs.size}) : Set A) := hz
    rw [heq] at hz'
    obtain ⟨i, hi, rfl⟩ := hz'
    have hi' : i < T.pts.size := hi
    have hcomm1 : ∀ l < Gs.size, Native.mul T.pts[i]! Gs[l]! = Native.mul Gs[l]! T.pts[i]! := by
      intro l hl
      have hlP : gg l ∈ Subgroup.closure (gg '' {l | l < Gs.size}) :=
        Subgroup.subset_closure ⟨l, hl, rfl⟩
      have hc := congrArg (sylowMat ι) (hcomm (gg l) hlP)
      rw [map_mul, map_mul, hgg l hl, hf i hi'] at hc
      have hGv : validRows Gs[l]! = true := by
        have hl' : l < 2 := by simpa [hGs] using hl
        interval_cases l
        · exact hv1
        · exact hv2
      rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at hc
      exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
        (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows (hvalid i hi') hGv)
        (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hGv (hvalid i hi')) hc
    have hc0 := hcomm1 0 (by simp [hGs])
    have hc1 := hcomm1 1 (by simp [hGs])
    have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hcen i (Nat.zero_le _) hi'
    simp only [co1SylowCentreOK, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.any_eq_true, List.mem_range, beq_iff_eq] at hpt
    rcases hpt with hne | ⟨k, hk, hk'⟩
    · exfalso
      rcases hne with hne | hne
      · exact (Bool.eq_false_iff.1 hne) (by rw [beq_iff_eq]; simpa [hGs] using hc0)
      · exact (Bool.eq_false_iff.1 hne) (by rw [beq_iff_eq]; simpa [hGs] using hc1)
    · have hmk : sylowMat ι (f i) = sylowMat ι (eltA ι hsurj j ^ k) := by
        rw [hf i hi', hk', sylowMat_apply, map_pow]
        exact hXj.pow k
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [zpow_natCast]; exact (hμ hmk).symm⟩

end Sound

end CFSG.RankThree.PartOne.SPOR
