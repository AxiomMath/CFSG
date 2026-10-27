module

public import CFSG.Quasithin.EmptyFaithful.S153YGCfg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCFin

public section

namespace CFSG.Quasithin.YG.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppD (PiS)
open CFSG.QuasithinUnique.AppC (fin_E card_fix_Estd fix_comm FixΔ)

variable {G : Type} [Group G] [Finite G]

structure GMate (H S M₀ : Subgroup G) (x : G) : Prop where
  hSM : S ≤ M₀
  hC52 : C5.NoCommonNormal S H M₀
  h2 : S.relIndex M₀ = 2
  hx : x ∈ M₀
  hxS : x ∉ S

namespace GMate

variable {H S M₀ : Subgroup G} {x : G} (m : GMate H S M₀ x)

omit [Finite G] in
include m in
theorem xN : x ∈ Subgroup.normalizer (S : Set G) := normalizer_of_relIndex_two m.hSM m.h2 m.hx

omit [Finite G] in
include m in
theorem xx : x * x ∈ S := mul_self_mem_of_relIndex_two m.h2 m.hx m.hxS

omit [Finite G] in
include m in
theorem conj_mem_S {s : G} (hs : s ∈ S) : x * s * x⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 m.xN s).1 hs

variable {L : Subgroup G} (C : GCfg H S L)
include C m

theorem V_conj : conjR (conjR C.U x) x = C.U := by
  show conjSubgroup (conjSubgroup (C.U) x) x = C.U
  rw [conjSubgroup_conjSubgroup]
  exact C5.conjSubgroup_eq_self (C.P.hSU m.xx)

theorem V_le_S : conjR (C.U) x ≤ S := by
  have := C5.conjSubgroup_mono C.hUS x
  rwa [C5.conjSubgroup_eq_self m.xN] at this

theorem V_le_B : conjR (C.U) x ≤ baum S := by
  have := C5.conjSubgroup_mono C.U_le_baum x
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S m.xN)] at this

theorem S_le_N_V : S ≤ Subgroup.normalizer (conjR (C.U) x : Set G) := by
  intro s hs
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  show conjSubgroup (conjSubgroup (C.U) x) s = conjSubgroup (C.U) x
  rw [conjSubgroup_conjSubgroup]
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← conjSubgroup_conjSubgroup,
    C5.conjSubgroup_eq_self (C.P.hSU (m.conj_mem_S hs))]

omit m in
theorem card_V : Nat.card ↥(conjR C.U x) = 16 := by
  rw [C56.conjR_eq, C5.card_conjSubgroup, C.card_U]

theorem V_not_le_Q : ¬ conjR C.U x ≤ pCoreOf 2 H := fun h =>
  C56.not_conj_le_of_mem_diff C.hcs m.hC52 m.hSM m.h2 m.hx m.hxS
    ((C5.conjSubgroup_mono C.hU1 x).trans h)

theorem card_symm :
    Nat.card ↥(conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G)) =
      Nat.card ↥(C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G)) := by
  have h1 : conjSubgroup (C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G)) x =
      conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G) := by
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer]
    have : conjSubgroup (conjR C.U x) x = C.U := m.V_conj C
    rw [this]
    rfl
  rw [← h1, C5.card_conjSubgroup]

theorem im_V : C.P.im (conjR C.U x) = Estd := by
  have hVN : conjR (C.U) x ≤ S := (m.V_le_S C)
  apply fin_E
  · rw [← C.hB]
    exact C.P.im_mono (m.V_le_B C)
  · intro hbot
    apply m.V_not_le_Q C
    intro v hv
    have hvN : v ∈ S := hVN hv
    have h1 : C.P.π ⟨v, hvN⟩ = 1 := by
      have : C.P.π ⟨v, hvN⟩ ∈ C.P.im (conjR C.U x) := C.P.pi_mem_im hv
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have h2 := (C.P.hker ⟨v, hvN⟩).1 h1
    rw [← C.hQ]
    refine ⟨C.hSH (m.V_le_S C hv), Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := h2 u hu
    calc u * v = (v * u * v⁻¹) * v := by rw [this]
      _ = v * u := by group
  · intro d hd g hg
    have hd' : d ∈ C.P.im S := by rw [C.hS]; exact hd
    obtain ⟨y, hyS, rfl⟩ := (C.P.mem_im).1 hd'
    obtain ⟨v, hv, rfl⟩ := (C.P.mem_im).1 hg
    have hmem : ((y * v * y⁻¹ : ↥S) : G) ∈
        conjR (C.U) x := by
      have := (Subgroup.mem_normalizer_iff.1 (m.S_le_N_V C hyS) (v : G)).1 hv
      simpa using this
    have := C.P.pi_mem_im hmem
    simpa [map_mul, map_inv] using this
  · have h1 := C.P.card_im_mul (A := conjR (C.U) x) hVN
    have h2 := C.P.card_fix (A := conjR (C.U) x) hVN
    have h3 := m.card_symm C
    rw [card_V (x := x) C] at h1
    rw [← h2, ← h3]
    exact h1

theorem cent_U_V :
    C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G) =
        C.U ⊓ conjR (C.U) x ∧
      C.U ⊓ conjR (C.U) x =
        conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G) ∧
      Nat.card ↥(C.U ⊓ conjR (C.U) x) = 4 := by
  have hVN : conjR (C.U) x ≤ S := (m.V_le_S C)
  have hcard1 : Nat.card ↥(C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G)) = 4 := by
    rw [C.P.card_fix hVN, m.im_V C, card_fix_Estd]
  have hcard2 :
      Nat.card ↥(conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G)) = 4 := by
    rw [m.card_symm C, hcard1]
  have h1 : C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G) ≤
      C.U ⊓ conjR (C.U) x := by
    intro u hu
    obtain ⟨huU, huC⟩ := hu
    refine ⟨huU, ?_⟩
    set f : evenWeight 5 := Multiplicative.toAdd (C.P.β ⟨u, huU⟩) with hf
    have hfix : f ∈ FixΔ Estd := by
      rw [← m.im_V C]
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
    have htV : t ∈ C.P.im (conjR C.U x) := by
      rw [m.im_V C]; exact (mem_Estd t).2 htE
    obtain ⟨v, hvV, hvt⟩ := (C.P.mem_im).1 htV
    have hw' : w ∈ evenWeight 5 := (mem_evenWeight_iff w).2 hwe
    set u' : ↥(C.U) := C.P.β.symm (Multiplicative.ofAdd ⟨w, hw'⟩) with hu'
    have hu'β : Multiplicative.toAdd (C.P.β u') = ⟨w, hw'⟩ := by simp [hu']
    have hvU' : (v : G) * (u' : G) * (v : G)⁻¹ ∈ C.U :=
      (Subgroup.mem_normalizer_iff.mp (C.P.hSU v.2) u').mp u'.2
    have hcomp := C.P.hcomp v u' ⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ rfl
    have heq : (⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ : ↥(C.U)) * u'⁻¹ = ⟨u, huU⟩ := by
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
    have h3 : (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ ∈ conjR (C.U) x :=
      (Subgroup.mem_normalizer_iff.1 (m.S_le_N_V C (C.hUS u'.2)) ((v : G)⁻¹)).1 (inv_mem hvV)
    have := mul_mem hvV h3
    simpa [mul_assoc] using this
  have h2 : C.U ⊓ conjR (C.U) x ≤
      conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G) := by
    intro u hu
    refine ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_⟩
    exact (C5.isElemAbelian_two_iff.1 C.hU).1 _ hu' _ hu.1
  have e1 := Subgroup.eq_of_le_of_card_ge h1
    (by rw [hcard1]; exact (Subgroup.card_le_of_le h2).trans hcard2.le)
  have e2 := Subgroup.eq_of_le_of_card_ge h2 (by
    rw [hcard2, ← e1, hcard1])
  refine ⟨e1, e2, ?_⟩
  rw [← e1, hcard1]

theorem V_inf_Q_le_U {e : G} (hV : e ∈ conjR (C.U) x) (hQ : e ∈ pCoreOf 2 H) :
    e ∈ C.U := by
  have hC : e ∈ Subgroup.centralizer (C.U : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => C.Q_comm_U hQ hu |>.symm
  have : e ∈ conjR (C.U) x ⊓ Subgroup.centralizer (C.U : Set G) := ⟨hV, hC⟩
  rw [← (m.cent_U_V C).2.1] at this
  exact this.1

end GMate

end CFSG.Quasithin.YG.AppD
