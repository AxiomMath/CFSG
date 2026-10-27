module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Goursat
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation
import Certificates.Certificate272037
import Certificates.Kernel.Bounds.Family
import CFSG.Certificates.Kernel.Misc.Coset.MemWalk
import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Presentation
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Model
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Sporadic.J3
import CFSG.Certificates.CosetTableShort
import CFSG.Certificates.NativeSchreierCard
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.Open.Defs

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

theorem three_lt_natCard_of_noncomm {G : Type*} [Group G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) : 3 < Nat.card G := by
  by_contra hle
  push Not at hle
  obtain ⟨a, b, hab⟩ := h
  have hpos : 0 < Nat.card G := Nat.card_pos
  have : ∀ x y : G, x * y = y * x := by
    interval_cases hc : Nat.card G
    · intro x y
      have : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact Subsingleton.elim _ _
    · have : Fact (Nat.card G).Prime := ⟨by rw [hc]; norm_num⟩
      have := isCyclic_of_prime_card hc
      have : IsMulCommutative G := IsCyclic.isMulCommutative
      intro x y
      exact IsMulCommutative.is_comm.comm x y
    · have : Fact (Nat.card G).Prime := ⟨by rw [hc]; norm_num⟩
      have := isCyclic_of_prime_card hc
      have : IsMulCommutative G := IsCyclic.isMulCommutative
      intro x y
      exact IsMulCommutative.is_comm.comm x y
  exact hab (this a b)

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
