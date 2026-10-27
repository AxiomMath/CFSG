module

public import CFSG.Quasithin.Background.B1MoreElevenC
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineD
public import CFSG.Quasithin.Background.B1MoreSeven

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  push Not at hab
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hab⟩⟩
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ Subgroup.center Q)
      (f := QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q) inferInstance

theorem isQuasisimple_to_open {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

section Core

variable {V : Type*} [CommGroup V] [Finite V]

theorem B1_11_core (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hF : quasithinGenFitting G = L)
    (hP : ∃ A, IsFFStarOffender G A) :
    ∃ (B : Subgroup (MulAut V)) (I : Subgroup V), IsFFStarMin G B ∧ ⁅L, B⁆ = L ∧
      I ∈ IrrPlus L (⊤ : Subgroup V) ∧ (∀ b ∈ B, ∀ w ∈ I, b w ∈ I) ∧
      IsFFModule (autSec (L ⊔ B) I (I ⊓ fixV L)) := by
  have hLG : L ≤ G := hF ▸ quasithinGenFitting_le G
  have hLperf : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  obtain ⟨A, hA⟩ := hP
  obtain ⟨B, hBmin, -⟩ := exists_isFFStarMin_below hA
  have hBoff : IsFFStarOffender G B := hBmin.1
  have hBG : B ≤ G := hBoff.1
  have hBne : B ≠ ⊥ := hBoff.2.1
  have hBel : IsElemAbelian2 B := hBoff.2.2.1
  have hBn : ∀ b ∈ B, ∀ x ∈ L, b * x * b⁻¹ ∈ L := fun b hb x hx => hLn b (hBG hb) x hx
  have hBnL : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj hBn
  have hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    have := centralizer_quasithinGenFitting_le G
    rwa [hF] at this
  have hBfaith : B ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ :=
    B1More.eq_bot_of_le_center_genFitting (G := G) hO2 (hBel.isPGroup.to_le inf_le_left)
      (by rw [hF]; exact fun y hy => hCL ⟨hBG hy.1, hy.2⟩) (by rw [hF]; exact inf_le_right)
  have hLB : ⁅L, B⁆ = L := by
    set N := ⁅L, B⁆ with hN
    have hNL : N ≤ L := by
      rw [hN, Subgroup.commutator_le]
      intro l hl b hb
      have h1 := hBn b hb l⁻¹ (L.inv_mem hl)
      have e : l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by group
      show l * b * l⁻¹ * b⁻¹ ∈ L
      rw [e]
      exact L.mul_mem hl h1
    by_contra hne
    have hnle : ¬ L ≤ N := fun h => hne (le_antisymm hNL h)
    have hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := by
      intro l hl n hn
      have hn' : n ∈ ⁅B, L⁆ := by rw [Subgroup.commutator_comm]; exact hn
      have := conj_mem_commutator (H := B) (A := L) hl hn'
      rw [Subgroup.commutator_comm] at this
      exact this
    have hcomm := B1Red.commute_of_normal_not_le hLq (N := N)
      (fun n hn l hl => L.mul_mem (L.mul_mem (hNL hn) hl) (L.inv_mem (hNL hn))) hLN hnle
    have hNc : N ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun n hn =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn l hl).symm
    have hdouble : ⁅⁅L, B⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hNc
    have h0 : ⁅L, B⁆ = ⊥ :=
      CFSG.ComponentClassification.Quasisimple.perfect_double_commutator L B hdouble
    have hBc : B ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.commutator_comm] at h0
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
    exact hBne (le_bot_iff.1 (by rw [← hBfaith]; exact le_inf le_rfl hBc))
  have hE : oTwoUpper L = L := oTwoUpper_eq_of_perfect hLperf
  have hCF : AllTwoChiefFactorsCentral L := allTwoChiefFactorsCentral_of_quasisimple hLq
  have hLne : commV L ≠ ⊥ := by
    intro h
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    apply hl
    apply Subtype.ext
    ext v
    exact h (Subgroup.mem_top v) l l.2
  obtain ⟨I, hI⟩ := exists_mem_irrPlus (Subgroup.isPerfect_iff.1 hLperf) hLne
  have hBfix : ∀ b ∈ B, ∀ w ∈ I, b w ∈ I := by
    intro b hb w hw
    have h1 := B1_5_3 hV hBmin hE hLB hCF b hb I hI
    have h2 : b w ∈ I.map b.toMonoidHom := Subgroup.mem_map_of_mem _ hw
    rwa [h1] at h2
  set Y := L ⊔ B with hYdef
  have hYG : Y ≤ G := sup_le hLG hBG
  have hLY : L ≤ Y := le_sup_left
  have hBY : B ≤ Y := le_sup_right
  have hY2 : ∀ y ∈ Y, y ^ 2 ∈ L := sq_mem_of_mem_sup hBnL hBel.2
  have hO2Y : pCoreOf 2 Y = ⊥ := by
    set N := pCoreOf 2 Y with hNdef
    have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hNY : N ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
    have hNLn : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L := fun n hn l hl => hLn n (hYG (hNY hn)) l hl
    have hLNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l hl n hn => conj_mem_pCoreOf (hLY hl) hn
    have hnle : ¬ L ≤ N := by
      intro hle
      have hnil : Group.IsNilpotent ↥L := (hN2.to_le hle).isNilpotent
      exact Group.IsPerfect.not_isNilpotent ↥L hnil
    have hcomm := commute_of_normal_not_le hLq hNLn hLNn hnle
    have hNc : N ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun n hn =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn l hl).symm
    have hNL : N ≤ L := fun n hn => hCL ⟨hYG (hNY hn), hNc hn⟩
    exact B1More.eq_bot_of_le_center_genFitting (G := G) hO2 hN2 (by rw [hF]; exact hNL)
      (by rw [hF]; exact hNc)
  have hFY : quasithinGenFitting Y = L :=
    quasithinGenFitting_eq_of_two_quot hLY (fun y hy l hl => hLn y (hYG hy) l hl) hLq hY2 hO2Y
  obtain ⟨hLinvI, hcommI, hltI, -⟩ := (mem_irrPlus_top_iff).1 hI
  have hGI : Y ≤ stabSub I :=
    sup_le (B1.le_stabSub_of_invariant hLinvI) (B1.le_stabSub_of_invariant hBfix)
  have hGU : Y ≤ stabSub (I ⊓ fixV L) :=
    sup_le (B1.le_stabSub_of_invariant (isInv_inf hLinvI (isInv_fixV L)))
      (B1.le_stabSub_of_invariant (isInv_inf hBfix (fixV_inv_of_normalizes hBn)))
  have hS : ¬ commSub I (quasithinGenFitting Y) ≤ I ⊓ fixV L := by
    rw [hFY, hcommI]
    exact not_le_of_gt hltI
  have hBoffY : IsFFStarOffender Y B := ⟨hBY, hBoff.2.1, hBoff.2.2.1, hBoff.2.2.2⟩
  have h58 := B1_5_8 hV (G := Y) (A := B) hBoffY (W := I) (U := I ⊓ fixV L) inf_le_left hGI hGU
    (by rw [hFY]; exact isQuasisimple_of_open hLq) hO2Y hS
  obtain ⟨B₀, -, hB₀⟩ := h58.2.1
  exact ⟨B, I, hBmin, hLB, hI, hBfix, isFFModule_of_offender hB₀⟩

end Core

end B1Red

end CFSG.Quasithin
