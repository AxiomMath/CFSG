module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7

universe u v

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]

theorem sylow_Tf_of_center_le {T Sb N : Subgroup Mb} {f : Mb} {b : ↥N →* G}
    (hb : Function.Injective b) {M : Subgroup G} (hrange : b.range = M)
    (hcent : ∀ z ∈ centerOf (perfectCore M), orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ≤ M)
    (hTN : T ≤ N) (hf : f ∈ T)
    (hSylTf : IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ N))
    (hZsq : ∀ x ∈ centerOf (perfectCore N), x ^ 2 = 1)
    (hZS : centerOf Sb ≤ centerOf (perfectCore N))
    (hWle : spWf T f ≤ centerOf Sb)
    (hWne : ∃ x ∈ spWf T f, x ∈ centerOf (perfectCore N) ∧ x ≠ 1) :
    IsSylowTwoOf (subImg b (spTf T f)) (Subgroup.centralizer ({b ⟨f, hTN hf⟩} : Set G)) := by
  have hTfN : spTf T f ≤ N := inf_le_left.trans hTN
  have hfN : f ∈ N := hTN hf
  set fg : G := b ⟨f, hfN⟩ with hfg
  have himg : subImg b (Subgroup.centralizer ({f} : Set Mb) ⊓ N) =
      M ⊓ Subgroup.centralizer ({fg} : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hxN, ⟨hxC, -⟩, rfl⟩ := mem_subImg.mp hg
      refine ⟨hrange ▸ ⟨⟨x, hxN⟩, rfl⟩, ?_⟩
      show b ⟨x, hxN⟩ ∈ Subgroup.centralizer ({fg} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_iff_of_injective hb hfN hxN).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    · rintro ⟨hgM, hgC⟩
      obtain ⟨⟨y, hyN⟩, rfl⟩ : g ∈ b.range := hrange ▸ hgM
      refine mem_subImg.mpr ⟨y, hyN, ⟨?_, hyN⟩, rfl⟩
      show y ∈ Subgroup.centralizer ({f} : Set Mb)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_iff_of_injective hb hfN hyN).mp
        (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  have hTfSyl : IsSylowTwoOf (subImg b (spTf T f)) (M ⊓ Subgroup.centralizer ({fg} : Set G)) := by
    rw [← himg]
    exact isSylowTwoOf_subImg hb (fun x hx => ⟨hx.2, hTfN hx⟩) inf_le_right hSylTf
  obtain ⟨R, hTfR, hR⟩ := exists_isSylowTwoOf_of_le (hTfSyl.le.trans inf_le_right)
    hTfSyl.2.1
  have hWg : centerOf (subImg b (spTf T f)) ⊓ ⁅subImg b (spTf T f), subImg b (spTf T f)⁆ =
      subImg b (spWf T f) := by
    unfold spWf
    rw [subImg_inf hb, subImg_centerOf hb hTfN, subImg_commutator hTfN]
  set W1 : Subgroup G := subImg b (spWf T f ⊓ centerOf (perfectCore N)) with hW1
  have hW1p : IsPGroup 2 W1 := fun g => ⟨1, by
    obtain ⟨z', hz'N, ⟨-, hz'Z⟩, hz⟩ := mem_subImg.mp g.2
    apply Subtype.ext
    have : (g : G) ^ 2 = 1 := by
      rw [← hz]
      exact (sq_eq_one_iff_of_injective hb hz'N).mpr (hZsq z' hz'Z)
    simpa using this⟩
  have hW1ne : W1 ≠ ⊥ := by
    obtain ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ := hWne
    intro h
    have hxN : x₀ ∈ N := hTfN (by
      unfold spWf at hx₀W
      exact (mem_centerOf_iff.mp hx₀W.1).1)
    have hmem : b ⟨x₀, hxN⟩ ∈ W1 := mem_subImg_of_mem b hxN ⟨hx₀W, hx₀Z⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hx₀1 (congrArg Subtype.val (hb (hmem.trans (map_one b).symm)))
  have hnorm : ∀ n ∈ R, n ∈ Subgroup.normalizer (subImg b (spTf T f) : Set G) →
      ∀ x ∈ W1, n * x * n⁻¹ ∈ W1 := by
    intro n _ hnT x hx
    obtain ⟨x', hx'N, ⟨hx'W, hx'Z⟩, rfl⟩ := mem_subImg.mp hx
    have hu : b ⟨x', hx'N⟩ ∈ centerOf (subImg b (spTf T f)) ⊓
        ⁅subImg b (spTf T f), subImg b (spTf T f)⁆ := by
      rw [hWg]
      exact mem_subImg_of_mem b hx'N hx'W
    have hnu := conj_mem_Wg hnT hu
    rw [hWg] at hnu
    obtain ⟨y, hyN, hyW, hy⟩ := mem_subImg.mp hnu
    rw [← hy]
    exact mem_subImg_of_mem b hyN ⟨hyW, hZS (hWle hyW)⟩
  have hcent' : ∀ z ∈ W1, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ M := by
    intro z hz hz1
    obtain ⟨z', hz'N, ⟨-, hz'Z⟩, rfl⟩ := mem_subImg.mp hz
    have hz'1 : z' ≠ 1 := fun h => hz1 (by subst h; exact map_one b)
    have hz'o : orderOf z' = 2 := orderOf_eq_prime (hZsq z' hz'Z) hz'1
    exact hcent _ (map_mem_centerOf_perfectCore hb hrange hz'N hz'Z)
      ((orderOf_img hb hz'N).trans hz'o)
  have hRTf := eq_of_weakly_closed hR hTfR hTfSyl hW1p hW1ne hnorm hcent'
  rw [hRTf] at hR
  exact hR

end CFSG.Quasithin.H13.F431
