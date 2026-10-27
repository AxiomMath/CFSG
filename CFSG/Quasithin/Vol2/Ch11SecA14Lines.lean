module

public import CFSG.Quasithin.Vol2.Ch11SecA14Delta2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem subgroupOf_map_conj {V U : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    (U.map (MulAut.conj x).toMonoidHom).subgroupOf V =
      (U.subgroupOf V).map (conjV V x hx).toMonoidHom := by
  ext v
  rw [Subgroup.mem_subgroupOf, mem_map_conj, mem_map_mulAut, Subgroup.mem_subgroupOf,
    ← conjV_inv, conjV_apply_coe, inv_inv]

theorem autOn_mono {A B V : Subgroup G} (h : A ≤ B) : autOn A V ≤ autOn B V :=
  Subgroup.map_mono fun _ hx => h hx

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isSylowTwoOf_inf_lOf (h : Hyp11 G T L I n) {U : Subgroup G}
    (hU : T ≤ Subgroup.normalizer (U : Set G)) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ LOf L U) (LOf L U) :=
  B6.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer (le_normalizer_lOf h.normal hU))

theorem eq_V₂_of_between (hD : FactDeltaSp4) (hD' : FactDeltaG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₁ U₂ U₃ : Subgroup G}
    (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂) (hU₃ : IsVi T L I n 3 U₃)
    {U : Subgroup G} (h1 : U₁ ≤ U) (h3 : U ≤ U₃) (hidx : U₁.relIndex U = 2 ^ n)
    (hT : T ⊓ LOf L U₁ ≤ Subgroup.normalizer (U : Set G)) : U = U₂ := by
  have hL := L_le_normalizer_fsuV h
  have hUV : U ≤ fsuV T I := h3.trans (IsVi.le_fsuV hU₃)
  have hX : LOf L U₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := (lOf_le L U₁).trans hL
  have hR := isSylowTwoOf_autOn hX (isSylowTwoOf_inf_lOf h (IsVi.le_normalizer hU₁))
  rw [autOn_lOf hL (IsVi.le_fsuV hU₁)] at hR
  have hRP : autOn (T ⊓ LOf L U₁) (fsuV T I) ≤ autOn (T ⊓ L) (fsuV T I) :=
    autOn_mono (inf_le_inf_left T (lOf_le L U₁))
  have hRs : autOn (T ⊓ LOf L U₁) (fsuV T I) ≤ stabW (U.subgroupOf (fsuV T I)) := by
    intro g hg
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    exact (conjV_mem_stabW_iff hUV hxV).mpr (hT hx)
  have heq := (deltaFacts hD hD' h1102 h hk hU₁ hU₂ hU₃).2.1 _ hR hRP (U.subgroupOf (fsuV T I))
    (fun x hx => h1 hx) (fun x hx => h3 hx)
    (by rw [Subgroup.relIndex_subgroupOf hUV, hidx]) hRs
  rw [← Subgroup.map_subgroupOf_eq_of_le hUV, heq,
    Subgroup.map_subgroupOf_eq_of_le (IsVi.le_fsuV hU₂)]

end CFSG.Quasithin.Vol2.Ch11.SecA
