module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCMate
public import CFSG.Milestones.ASVolI.C61.PAppCAU

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Mate
open CFSG.QuasithinUnique.AppC.Mate

variable {S T M₀ : Subgroup G} {x : G} (m : Mate S T M₀ x)

variable {H L M : Subgroup G} (C : Cfg T M H S L)
include C m

theorem V_conj : conjR (conjR (blockU L) x) x = blockU L := by
  show conjSubgroup (conjSubgroup (blockU L) x) x = blockU L
  rw [conjSubgroup_conjSubgroup]
  exact C5.conjSubgroup_eq_self (C56.S_le_normalizer_blockU C.hj m.xx)

theorem V_le_S : conjR (blockU L) x ≤ S := by
  have := C5.conjSubgroup_mono C.hUS x
  rwa [C5.conjSubgroup_eq_self m.xN] at this

theorem V_le_B : conjR (blockU L) x ≤ baum S := by
  have := C5.conjSubgroup_mono C.blockU_le_baum x
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S m.xN)] at this

theorem S_le_N_V : S ≤ Subgroup.normalizer (conjR (blockU L) x : Set G) := by
  intro s hs
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  show conjSubgroup (conjSubgroup (blockU L) x) s = conjSubgroup (blockU L) x
  rw [conjSubgroup_conjSubgroup]
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← conjSubgroup_conjSubgroup,
    C5.conjSubgroup_eq_self (C56.S_le_normalizer_blockU C.hj (m.conj_mem_S hs))]

omit m in
theorem V_elem : IsElemAbelian 2 (conjR (blockU L) x) :=
  C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp C.hU).conjSubgroup x)

omit m in
theorem card_V : Nat.card ↥(conjR (blockU L) x) = 16 := by
  rw [C56.conjR_eq, C5.card_conjSubgroup, C.card_U]

theorem V_not_le_Q : ¬ conjR (blockU L) x ≤ pCoreOf 2 H :=
  C56.not_conj_le_of_mem_diff C.hcs m.hSM m.hMT m.h2 m.hx m.hxS

theorem card_symm :
    Nat.card ↥(conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G)) =
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G)) := by
  have h1 : conjSubgroup (blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G)) x =
      conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G) := by
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer]
    have : conjSubgroup (conjR (blockU L) x) x = blockU L := Mate.V_conj (m := m) C
    rw [this]
    rfl
  rw [← h1, C5.card_conjSubgroup]

theorem im_V : C.P.im (conjR (blockU L) x) = Estd := by
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (Mate.V_le_S (m := m) C).trans C.hSN
  apply fin_E
  · rw [← C.hB]
    exact C.P.im_mono (Mate.V_le_B (m := m) C)
  · intro hbot
    apply Mate.V_not_le_Q (m := m) C
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hVN hv
    have h1 : C.P.π ⟨v, hvN⟩ = 1 := by
      have : C.P.π ⟨v, hvN⟩ ∈ C.P.im (conjR (blockU L) x) := C.P.pi_mem_im hv
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have h2 := (C.P.hker ⟨v, hvN⟩).1 h1
    rw [← C.hQ]
    refine ⟨C.hSH (Mate.V_le_S (m := m) C hv), Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := h2 u hu
    calc u * v = (v * u * v⁻¹) * v := by rw [this]
      _ = v * u := by group
  · intro d hd g hg
    have hd' : d ∈ C.P.im S := by rw [C.hS]; exact hd
    obtain ⟨y, hyS, rfl⟩ := (C.P.mem_im).1 hd'
    obtain ⟨v, hv, rfl⟩ := (C.P.mem_im).1 hg
    have hmem : ((y * v * y⁻¹ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈
        conjR (blockU L) x := by
      have := (Subgroup.mem_normalizer_iff.1 (Mate.S_le_N_V (m := m) C hyS) (v : G)).1 hv
      simpa using this
    have := C.P.pi_mem_im hmem
    simpa [map_mul, map_inv] using this
  · have h1 := C.P.card_im_mul (A := conjR (blockU L) x) hVN
    have h2 := C.P.card_fix (A := conjR (blockU L) x) hVN
    have h3 := Mate.card_symm (m := m) C
    rw [card_V (x := x) C] at h1
    rw [← h2, ← h3]
    exact h1

theorem cent_U_V :
    blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) =
        blockU L ⊓ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x =
        conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G) ∧
      Nat.card ↥(blockU L ⊓ conjR (blockU L) x) = 4 := by
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (Mate.V_le_S (m := m) C).trans C.hSN
  have hcard1 : Nat.card ↥(blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G)) = 4 := by
    rw [C.P.card_fix hVN, Mate.im_V (m := m) C, card_fix_Estd]
  have hcard2 :
      Nat.card ↥(conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G)) = 4 := by
    rw [Mate.card_symm (m := m) C, hcard1]
  have h1 : blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) ≤
      blockU L ⊓ conjR (blockU L) x := by
    intro u hu
    obtain ⟨huU, huC⟩ := hu
    refine ⟨huU, ?_⟩
    set f : evenWeight 5 := Multiplicative.toAdd (C.P.β ⟨u, huU⟩) with hf
    have hfix : f ∈ FixΔ Estd := by
      rw [← Mate.im_V (m := m) C]
      intro σ hσ
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im).1 hσ
      have hc := Subgroup.mem_centralizer_iff.1 huC y hy
      have h := C.P.hcomp y ⟨u, huU⟩ ⟨u, huU⟩ (by
        show u = (y : G) * u * (y : G)⁻¹
        rw [hc]; group)
      exact h.symm
    have hfe : isEven f.1 := (mem_evenWeight_iff f.1).1 f.2
    have hfE : ∀ σ ∈ Eset, pact σ f.1 = f.1 := fun σ hσ =>
      congrArg Subtype.val (hfix σ ((mem_Estd σ).2 hσ))
    obtain ⟨t, htE, w, hwe, hw⟩ := fix_comm f.1 hfe hfE
    have htV : t ∈ C.P.im (conjR (blockU L) x) := by
      rw [Mate.im_V (m := m) C]; exact (mem_Estd t).2 htE
    obtain ⟨v, hvV, hvt⟩ := (C.P.mem_im).1 htV
    have hw' : w ∈ evenWeight 5 := (mem_evenWeight_iff w).2 hwe
    set u' : ↥(blockU L) := C.P.β.symm (Multiplicative.ofAdd ⟨w, hw'⟩) with hu'
    have hu'β : Multiplicative.toAdd (C.P.β u') = ⟨w, hw'⟩ := by simp [hu']
    have hvU' : (v : G) * (u' : G) * (v : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) v.2) u').mp u'.2
    have hcomp := C.P.hcomp v u' ⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ rfl
    have heq : (⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ : ↥(blockU L)) * u'⁻¹ = ⟨u, huU⟩ := by
      apply C.P.β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hcomp, hvt, hu'β]
      apply Subtype.ext
      funext i
      have hi := congrFun hw i
      simp only [Pi.add_apply] at hi
      show pact t w i + -(w i) = f.1 i
      rw [← hi]
      generalize pact t w i = a
      generalize w i = b
      revert a b
      decide
    have hu : u = (v : G) * (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ := by
      have := congrArg Subtype.val heq
      simpa using this.symm
    rw [hu]
    have h3 : (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ ∈ conjR (blockU L) x :=
      (Subgroup.mem_normalizer_iff.1 (Mate.S_le_N_V (m := m) C (C.hUS u'.2)) ((v : G)⁻¹)).1 (inv_mem hvV)
    have := mul_mem hvV h3
    simpa [mul_assoc] using this
  have h2 : blockU L ⊓ conjR (blockU L) x ≤
      conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G) := by
    intro u hu
    refine ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_⟩
    exact blockU_comm_blockU C.hL hu' hu.1
  have e1 := Subgroup.eq_of_le_of_card_ge h1
    (by rw [hcard1]; exact (Subgroup.card_le_of_le h2).trans hcard2.le)
  have e2 := Subgroup.eq_of_le_of_card_ge h2 (by
    rw [hcard2, ← e1, hcard1])
  refine ⟨e1, e2, ?_⟩
  rw [← e1, hcard1]

theorem V_inf_Q_le_U {e : G} (hV : e ∈ conjR (blockU L) x) (hQ : e ∈ pCoreOf 2 H) :
    e ∈ blockU L := by
  have hC : e ∈ Subgroup.centralizer (blockU L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => C.Q_comm_U hQ hu |>.symm
  have : e ∈ conjR (blockU L) x ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hV, hC⟩
  rw [← (Mate.cent_U_V (m := m) C).2.1] at this
  exact this.1

end Mate

end CFSG.QuasithinUnique.burnsideC56_P.AppC
