module

public import CFSG.RankThree.PartOne.SPOR.Co1SylowSound
public import CFSG.RankThree.PartOne.SPOR.Co1SylowGenData

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2

section GenSound

variable {A : Type} [Group A] (ι : A →* GL24)

theorem co1SylowGen_sound [Finite A] (hι : Function.Injective ι) {baseG : List GL24}
    (hbase : List.Forall₂ MRep co1PlaneBase baseG) (hmem : ∀ g ∈ baseG, ∃ a : A, ι a = g)
    {derivs : List (List Int)} {i₁ i₂ j : ℕ} (h : co1SylowOK derivs i₁ i₂ j = true)
    (hg : co1SylowGenOK derivs i₁ i₂ = true) :
    ∃ a₁ a₂ : A, a₁ ^ 5 = 1 ∧ a₂ ^ 5 = 1 ∧
      Nat.card (Subgroup.closure ({a₁, a₂} : Set A)) = 625 := by
  simp only [co1SylowOK, co1SylowCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_assoc] at h
  obtain ⟨hflag, h1, h2, h3, h4, h5, h6, hv1, hv2, hvj, hgt, hcard, hcen, hx5⟩ := h
  simp only [co1SylowGenOK, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hg1, hg2⟩ := hg
  have hR := dag_rep hbase derivs hflag
  have hsurj : ∀ g ∈ dagG baseG derivs, ∃ a : A, ι a = g := fun g hg' => by
    have := dagG_mem (H := ι.range) (fun g hg'' => by
      obtain ⟨a, ha⟩ := hmem g hg''
      exact ⟨a, ha⟩) derivs g hg'
    exact this
  set R := (Native.dag co1PlaneBase derivs).1 with hRdef
  have hG1 : MRep (R.getD (i₁ - 1) Native.one) (ι (eltA ι hsurj i₁)) := rep_eltA ι hR hsurj i₁
  have hG2 : MRep (R.getD (i₂ - 1) Native.one) (ι (eltA ι hsurj i₂)) := rep_eltA ι hR hsurj i₂
  set Gs : Array (Array ℕ) := #[R.getD (i₁ - 1) Native.one, R.getD (i₂ - 1) Native.one] with hGs
  set T := gtBFS Gs 700 with hT
  let gg : ℕ → A := fun l => if l = 0 then eltA ι hsurj i₁ else eltA ι hsurj i₂
  have hgg : ∀ l < Gs.size, sylowMat ι (gg l) = rowsMatrix 24 Gs[l]! := by
    intro l hl
    have hl' : l < 2 := by simpa [hGs] using hl
    interval_cases l
    · exact hG1.symm
    · exact hG2.symm
  have hGssize : Gs.size = 2 := by simp [hGs]
  have hset : gg '' {l | l < Gs.size} = ({gg 0, gg 1} : Set A) := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' : l < 2 := by simpa [hGssize] using hl
      interval_cases l
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [hGssize]; norm_num, rfl⟩
      · exact ⟨1, by rw [hGssize]; norm_num, rfl⟩
  have hgg0 : gg 0 = eltA ι hsurj i₁ := by simp [gg]
  have hgg1 : gg 1 = eltA ι hsurj i₂ := by simp [gg]
  have hpow1 : (ι (eltA ι hsurj i₁)) ^ 5 = 1 := (hg1 ▸ hG1.pow 5).eq MRep.one
  have hpow2 : (ι (eltA ι hsurj i₂)) ^ 5 = 1 := (hg2 ▸ hG2.pow 5).eq MRep.one
  refine ⟨eltA ι hsurj i₁, eltA ι hsurj i₂, ?_, ?_, ?_⟩
  · apply hι
    rw [map_pow, map_one]
    exact hpow1
  · apply hι
    rw [map_pow, map_one]
    exact hpow2
  · have hcl : Subgroup.closure (gg '' {l | l < Gs.size}) =
        Subgroup.closure ({eltA ι hsurj i₁, eltA ι hsurj i₂} : Set A) := by
      rw [hset, hgg0, hgg1]
    rw [← hcl]
    exact (prodTree_card (sylowMat ι) (sylowMat_injective ι hι) hgt gg hgg).trans hcard

end GenSound

end CFSG.RankThree.PartOne.SPOR
