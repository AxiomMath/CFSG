module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Norm
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open Orbit

theorem g2WeylTwoCentral : G2WeylTwoCentral := by
  intro V _ _ H X S z hz1 hzH hH hHX hXN hS v hv1 hvz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hlen, -⟩ := orbitG2Weyl V H z hz1 hzH hH
  have h63 : Nat.card (orbitIn H v) = 63 := by
    simpa using hlen v hv1 hvz
  have hSO : ∀ s ∈ S, ∀ w ∈ orbitIn H v, (s : MulAut V) w ∈ orbitIn H v := by
    intro s hs w hw
    have h1 := g2WeylNormalizerOrbits V H hH s
      (Subgroup.mem_normalizer_iff.mp (hXN (hS.1 hs))) w
    rwa [orbitIn_eq_of_mem hw] at h1
  let _ : MulAction S (orbitIn H v) :=
    { smul := fun s w => ⟨(s : MulAut V) w, hSO s s.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun s t w => Subtype.ext rfl }
  obtain ⟨⟨u, hu⟩, hfix⟩ := hS.2.1.nonempty_fixed_point_of_prime_not_dvd_card
    (orbitIn H v) (by rw [h63]; decide)
  obtain ⟨h, hh, rfl⟩ := hu
  exact ⟨h, hHX hh, fun s hs => congrArg Subtype.val (hfix ⟨s, hs⟩)⟩

end CFSG.Quasithin.H13
