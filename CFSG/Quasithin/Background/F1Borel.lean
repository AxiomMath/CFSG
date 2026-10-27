module

public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def bigB (L1 L2 S : Subgroup G) : Subgroup G := borelOf L1 S ⊔ borelOf L2 S ⊔ S

structure Hyp111R (L1 L2 S : Subgroup G) : Prop where
  hyp : Hyp111 L1 L2 S
  r1 : RankOneAt L1 (S ⊓ L1)
  r2 : RankOneAt L2 (S ⊓ L2)

theorem Hyp111.symm {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) : Hyp111 L2 L1 S :=
  ⟨h.h2, h.h1, by rw [sup_comm L2 L1]; exact h.o2⟩

theorem Hyp111R.symm {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) : Hyp111R L2 L1 S :=
  ⟨h.hyp.symm, h.r2, h.r1⟩

theorem bigB_comm (L1 L2 S : Subgroup G) : bigB L2 L1 S = bigB L1 L2 S := by
  simp only [bigB, sup_comm (borelOf L2 S) (borelOf L1 S)]

namespace F1

variable [Finite G] {Li Lj L1 L2 S : Subgroup G}

omit [Finite G] in
theorem isUniqueMax_borelOf (hR : RankOneAt Li (S ⊓ Li)) : (borelOf Li S) < Li ∧ (S ⊓ Li) ≤ (borelOf Li S) ∧ ∀ M : Subgroup G, (S ⊓ Li) ≤ M → M < Li → M ≤ (borelOf Li S) :=
  
  ⟨lt_of_le_of_ne (borelOf_le Li S) hR.borel_ne, sylow_le_borelOf Li S, fun M hTM hML =>
    le_inf hML.le (hR.unique_max M hTM hML.le hML.ne)⟩

theorem borelOf_eq_normalizer (h : Hyp111R Li Lj S) :
    borelOf Lj S = Lj ⊓ Subgroup.normalizer (Li : Set G) := by
  have hi := h.hyp.h1
  have hj := h.hyp.h2
  apply le_antisymm (le_inf (borelOf_le Lj S) hi.borel_le)
  by_cases hN : Lj ⊓ Subgroup.normalizer (Li : Set G) = Lj
  · exfalso
    have hLjLi : Lj ≤ Subgroup.normalizer (Li : Set G) := inf_eq_left.mp hN
    have hG0 : Li ⊔ Lj ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 Li : Set G) :=
      sup_le (sup_le (le_normalizer_pCoreOf 2 Li)
        (le_normalizer_pCoreOf_of_le_normalizer hLjLi))
        (le_normalizer_pCoreOf_of_le_normalizer hi.normalizes)
    have hO : pCoreOf 2 Li = ⊥ := by
      have h1 := le_pCoreOf_of_le_normalizer 2
        ((pCoreOf_le 2 Li).trans (le_sup_left.trans le_sup_left)) hG0 (pCoreOf_isPGroup 2 Li)
      rw [h.hyp.o2] at h1
      exact le_bot_iff.mp h1
    set P := Li ⊔ S ⊔ borelOf Lj S with hP
    have hPnorm : P ≤ Subgroup.normalizer (Li : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer hi.normalizes) hi.borel_le
    have hLiP : Li ≤ P := le_sup_left.trans le_sup_left
    have hinf : pCoreOf 2 P ⊓ Li ≤ ⊥ := by
      have := pCoreOf_inf_le hLiP
      rwa [hO] at this
    have hcomm : ⁅Li, pCoreOf 2 P⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (commutator_le_inf_of_normalizes ?_ ?_)
        (by rw [inf_comm]; exact hinf))
      · exact hLiP.trans (le_normalizer_pCoreOf 2 P)
      · exact (pCoreOf_le 2 P).trans hPnorm
    have hcent : Li ≤ Subgroup.centralizer (pCoreOf 2 P : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hLiQ : Li ≤ pCoreOf 2 P := fun x hx => hi.charTwo ⟨hLiP hx, hcent hx⟩
    have hLi2 : IsPGroup 2 Li := (pCoreOf_isPGroup 2 P).to_le hLiQ
    obtain ⟨x, hxLi, hx⟩ := isSylowTwoOf_exists_conj_le hi.sylow (le_refl Li) hLi2
    have hsyl : Li ≤ S ⊓ Li := by
      have h2 : conjSub x⁻¹ Li ≤ S ⊓ Li := (le_conjSub_iff x).mp hx
      have h3 : conjSub x⁻¹ Li = Li :=
        conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer (Li.inv_mem hxLi))
      rwa [h3] at h2
    apply h.r1.borel_ne
    have e : S ⊓ Li = Li := le_antisymm inf_le_right hsyl
    rw [e]
    exact inf_eq_left.mpr Subgroup.le_normalizer
  · have hM : Lj ⊓ Subgroup.normalizer (Li : Set G) ≤
        Subgroup.normalizer ((S ⊓ Lj : Subgroup G) : Set G) := by
      refine h.r2.unique_max _ ?_ inf_le_left hN
      exact le_inf inf_le_right (inf_le_left.trans hi.normalizes)
    exact le_inf inf_le_left hM

theorem borelOf_le_normalizer_borelOf (h : Hyp111R Li Lj S) :
    borelOf Lj S ≤ Subgroup.normalizer ((borelOf Li S : Subgroup G) : Set G) := by
  have hi := h.hyp.h1
  have hj := h.hyp.h2
  have hBi : borelOf Li S = Li ⊓ Subgroup.normalizer (Lj : Set G) := borelOf_eq_normalizer h.symm
  set X : Subgroup G := S ⊔ borelOf Lj S with hX
  have hXLj : X ≤ Subgroup.normalizer (Lj : Set G) :=
    sup_le hj.normalizes ((borelOf_le Lj S).trans Subgroup.le_normalizer)
  have hYB : X ⊓ Li ≤ borelOf Li S := by
    rw [hBi]
    exact le_inf inf_le_right (inf_le_left.trans hXLj)
  have hSY : S ⊓ Li ≤ X ⊓ Li := inf_le_inf_right Li le_sup_left
  have key : ∀ b ∈ borelOf Lj S, conjSub b (borelOf Li S) ≤ borelOf Li S := by
    intro b hb
    have hbX : b ∈ X := Subgroup.mem_sup_right hb
    have hbLi : b ∈ Subgroup.normalizer (Li : Set G) := hi.borel_le hb
    have hcLi : conjSub b Li = Li := conjSub_eq_of_mem_normalizer hbLi
    have hbY : conjSub b (X ⊓ Li) = X ⊓ Li :=
      conjSub_eq_of_mem_normalizer (mem_normalizer_inf (Subgroup.le_normalizer hbX) hbLi)
    have hM1 : conjSub b (borelOf Li S) ≤ Li :=
      (conjSub_mono b (borelOf_le Li S)).trans hcLi.le
    have hM2 : S ⊓ Li ≤ conjSub b (borelOf Li S) :=
      calc S ⊓ Li ≤ X ⊓ Li := hSY
        _ = conjSub b (X ⊓ Li) := hbY.symm
        _ ≤ conjSub b (borelOf Li S) := conjSub_mono b hYB
    have hM3 : conjSub b (borelOf Li S) ≠ Li := by
      intro heq
      apply h.r1.borel_ne
      have : conjSub b (borelOf Li S) = conjSub b Li := heq.trans hcLi.symm
      exact (conjSub_inj b).mp this
    exact le_inf hM1 (h.r1.unique_max _ hM2 hM1 hM3)
  intro b hb
  exact mem_normalizer_of_conj_le (key b hb) (key b⁻¹ ((borelOf Lj S).inv_mem hb))

theorem borelOf_le_normalizer_sylow (h : Hyp111R Li Lj S) :
    borelOf Lj S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have := le_normalizer_pCoreOf_of_le_normalizer (borelOf_le_normalizer_borelOf h)
  rwa [pCoreOf_borelOf h.hyp.h1.sylow] at this

theorem bigB_le_normalizer_borelOf (h : Hyp111R L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer ((borelOf L1 S : Subgroup G) : Set G) ∧
      bigB L1 L2 S ≤ Subgroup.normalizer ((borelOf L2 S : Subgroup G) : Set G) :=
  ⟨sup_le (sup_le Subgroup.le_normalizer (borelOf_le_normalizer_borelOf h))
      (le_normalizer_borelOf h.hyp.h1.normalizes),
    sup_le (sup_le (borelOf_le_normalizer_borelOf h.symm) Subgroup.le_normalizer)
      (le_normalizer_borelOf h.hyp.h2.normalizes)⟩

omit [Finite G] in
theorem bigB_le_normalizer_left (h : Hyp111R L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) ∧ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
  ⟨sup_le (sup_le ((borelOf_le L1 S).trans Subgroup.le_normalizer) h.hyp.h1.borel_le)
      h.hyp.h1.normalizes,
    sup_le (sup_le h.hyp.h2.borel_le ((borelOf_le L2 S).trans Subgroup.le_normalizer))
      h.hyp.h2.normalizes⟩

theorem bigB_le_normalizer_sylow (h : Hyp111R L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) ∧
      bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
  ⟨sup_le (sup_le (borelOf_le_normalizer L1 S) (borelOf_le_normalizer_sylow h))
      (le_normalizer_inf_of_le h.hyp.h1.normalizes),
    sup_le (sup_le (borelOf_le_normalizer_sylow h.symm) (borelOf_le_normalizer L2 S))
      (le_normalizer_inf_of_le h.hyp.h2.normalizes)⟩

theorem coe_bigB (h : Hyp111R L1 L2 S) :
    (bigB L1 L2 S : Set G) = (borelOf L1 S : Set G) * (borelOf L2 S : Set G) * (S : Set G) := by
  have hB2 : borelOf L2 S ≤ Subgroup.normalizer ((borelOf L1 S : Subgroup G) : Set G) :=
    borelOf_le_normalizer_borelOf h
  have hS : S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ borelOf L2 S : Subgroup G) : Set G) :=
    le_normalizer_sup (le_normalizer_borelOf h.hyp.h1.normalizes)
      (le_normalizer_borelOf h.hyp.h2.normalizes)
  ext x
  simp only [bigB, SetLike.mem_coe, Set.mem_mul]
  rw [mem_sup_iff_exists_mul_of_normalizes hS]
  constructor
  · rintro ⟨a, ha, s, hs, rfl⟩
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hB2).mp ha
    exact ⟨b1 * b2, ⟨b1, hb1, b2, hb2, rfl⟩, s, hs, rfl⟩
  · rintro ⟨_, ⟨b1, hb1, b2, hb2, rfl⟩, s, hs, rfl⟩
    exact ⟨b1 * b2, (mem_sup_iff_exists_mul_of_normalizes hB2).mpr ⟨b1, hb1, b2, hb2, rfl⟩,
      s, hs, rfl⟩

theorem bigB_eq_inf_normalizer (h : Hyp111R Li Lj S) :
    bigB Li Lj S = (Li ⊔ S ⊔ borelOf Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have hi := h.hyp.h1
  have hXB : S ⊔ borelOf Lj S ≤ bigB Li Lj S :=
    sup_le le_sup_right (le_sup_right.trans le_sup_left)
  apply le_antisymm
  · refine le_inf ?_ (bigB_le_normalizer_sylow h).1
    exact sup_le (sup_le ((borelOf_le Li S).trans (le_sup_left.trans le_sup_left))
      (le_sup_right (a := Li ⊔ S) (b := borelOf Lj S))) (le_sup_right.trans le_sup_left)
  · intro x hx
    obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
    have hX : S ⊔ borelOf Lj S ≤ Subgroup.normalizer (Li : Set G) :=
      sup_le hi.normalizes hi.borel_le
    rw [sup_assoc, mem_sup_iff_exists_mul_of_normalizes hX] at hxP
    obtain ⟨a, ha, b, hb, rfl⟩ := hxP
    have hbB : b ∈ bigB Li Lj S := hXB hb
    have hbN : b ∈ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) :=
      (bigB_le_normalizer_sylow h).1 hbB
    have haN : a ∈ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
      have := (Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)).mul_mem hxN
        ((Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)).inv_mem hbN)
      simpa using this
    have haB : a ∈ bigB Li Lj S := (le_sup_left.trans le_sup_left : borelOf Li S ≤ bigB Li Lj S)
      ⟨ha, haN⟩
    exact (bigB Li Lj S).mul_mem haB hbB

omit [Finite G] in
theorem lt_borelOf (h : Hyp111R L1 L2 S) : borelOf L1 S < L1 :=
  lt_of_le_of_ne (borelOf_le L1 S) h.r1.borel_ne

theorem inf_bigB_eq_borelOf (h : Hyp111R L1 L2 S) : L1 ⊓ bigB L1 L2 S = borelOf L1 S := by
  apply le_antisymm
  · rintro x ⟨hxL, hxB⟩
    exact ⟨hxL, (bigB_le_normalizer_sylow h).1 hxB⟩
  · exact le_inf (borelOf_le L1 S) (le_sup_left.trans le_sup_left)

omit [Finite G] in
theorem bigB_maximal_in_parabolic (h : Hyp111R L1 L2 S) (M : Subgroup G)
    (hBM : bigB L1 L2 S ≤ M) (hMP : M ≤ L1 ⊔ bigB L1 L2 S) :
    M = bigB L1 L2 S ∨ M = L1 ⊔ bigB L1 L2 S := by
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := (bigB_le_normalizer_left h).1
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hK1 : borelOf L1 S ≤ M ⊓ L1 := le_inf (hB1B.trans hBM) (borelOf_le L1 S)
  by_cases hK : M ⊓ L1 = L1
  · right
    have hL1M : L1 ≤ M := inf_eq_right.mp hK
    exact le_antisymm hMP (sup_le hL1M hBM)
  · left
    have hKB : M ⊓ L1 ≤ borelOf L1 S := by
      refine le_inf inf_le_right (h.r1.unique_max (M ⊓ L1) ?_ inf_le_right hK)
      exact (sylow_le_borelOf L1 S).trans hK1
    refine le_antisymm ?_ hBM
    intro m hm
    obtain ⟨l, hl, b, hb, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hBL1).mp (hMP hm)
    have hlM : l ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hBM hb))
      simpa using this
    have hlB : l ∈ borelOf L1 S := hKB ⟨hlM, hl⟩
    exact (bigB L1 L2 S).mul_mem (hB1B hlB) hb

theorem parabolic_inf_parabolic (h : Hyp111R L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
  have hne : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) ≠ L1 ⊔ bigB L1 L2 S := by
    intro heq
    have h1 : L1 ⊔ bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := inf_eq_left.mp heq
    have hP2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
      sup_le Subgroup.le_normalizer (bigB_le_normalizer_left h).2
    have hL1 : L1 ≤ Subgroup.normalizer (L2 : Set G) := le_sup_left.trans (h1.trans hP2)
    have hL1B : L1 ≤ borelOf L1 S := by
      rw [borelOf_eq_normalizer h.symm]
      exact le_inf le_rfl hL1
    exact (lt_borelOf h).not_ge hL1B
  rcases bigB_maximal_in_parabolic h _ (le_inf le_sup_right le_sup_right) inf_le_left with h' | h'
  · exact h'
  · exact absurd h' hne

end F1

end CFSG.Quasithin
