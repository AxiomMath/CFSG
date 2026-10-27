module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBA
public import CFSG.RankThree.S4Free.StellmacherSzModule
public import Certificates.Certificate113

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix CFSG.CGT.PushingUpLit.SolKNA CFSG.RankThree.GF2n.SzExplicit
  CFSG.RepresentationTheory.SzMartineau
open CFSG.RankThree.S4Free.SzNatural

@[expose] noncomputable def torusSzHom (a : ℕ) : (F a)ˣ →* ↥(Sz a) where
  toFun := torusSz a
  map_one' := torusSz_one a
  map_mul' x y := (torusSz_mul_torusSz a x y).symm

theorem torusSz_inv (a : ℕ) (x : (F a)ˣ) : (torusSz a x)⁻¹ = torusSz a x⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, torusSz_mul_torusSz, mul_inv_cancel, torusSz_one]

theorem torusSz_conj_rootSz (a : ℕ) (x : (F a)ˣ) (u w : F a) :
    torusSz a x * rootSz a u w * (torusSz a x)⁻¹ =
      rootSz a ((x : F a) * u) ((x : F a) ^ (1 + 2 ^ (a + 1)) * w) := by
  have h := torusSz_mul_rootSz a x u w
  calc torusSz a x * rootSz a u w * (torusSz a x)⁻¹
      = (rootSz a ((x : F a) * u) ((x : F a) ^ (1 + 2 ^ (a + 1)) * w) * torusSz a x) *
          (torusSz a x)⁻¹ := by rw [h]
    _ = rootSz a ((x : F a) * u) ((x : F a) ^ (1 + 2 ^ (a + 1)) * w) := by
        rw [mul_assoc, mul_inv_cancel, mul_one]

theorem torusSz_mem_normalizer (a : ℕ) (x : (F a)ˣ) :
    torusSz a x ∈ Subgroup.normalizer (rootSub a : Set ↥(Sz a)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨u, w, rfl⟩ := (mem_rootSub a).mp hh
    rw [show rootElt a u w = rootSz a u w from rfl, torusSz_conj_rootSz]
    exact (mem_rootSub a).mpr ⟨_, _, rfl⟩
  · intro hh
    have hk : torusSz a x * h * (torusSz a x)⁻¹ ∈ rootSub a := hh
    obtain ⟨u, w, hu⟩ := (mem_rootSub a).mp hk
    have hmem : torusSz a x⁻¹ * rootElt a u w * (torusSz a x⁻¹)⁻¹ ∈ rootSub a := by
      rw [show rootElt a u w = rootSz a u w from rfl, torusSz_conj_rootSz]
      exact (mem_rootSub a).mpr ⟨_, _, rfl⟩
    have heq : torusSz a x⁻¹ * rootElt a u w * (torusSz a x⁻¹)⁻¹ = h := by
      rw [hu, (torusSz_inv a x).symm]
      group
    rwa [heq] at hmem

theorem torusSzHom_range_le_normalizer (a : ℕ) :
    (torusSzHom a).range ≤ Subgroup.normalizer (rootSub a : Set ↥(Sz a)) := by
  rintro _ ⟨x, rfl⟩
  exact torusSz_mem_normalizer a x

end CFSG.LocalAnalysis.WeakClosure81

end
