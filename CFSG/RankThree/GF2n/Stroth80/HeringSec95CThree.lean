module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CRank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open Module
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.exists_eichler_LB (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {l : G}
    (hlL : l ∈ LB M Q B) :
    ∃ w : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) C.u w = 0 ∧
      ∀ v, (C.φ ⟨l, le_Rt (M := M) (LB M Q B) hs.mem hlL⟩ :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = eichler (quadPlus 2 K) C.u w v := by
  have hmem : C.φ ⟨l, le_Rt (M := M) (LB M Q B) hs.mem hlL⟩ ∈ C.E.LomGL C.u := by
    rw [← C.hLB]
    exact Subgroup.mem_map_of_mem C.φ (Subgroup.mem_subgroupOf.mpr hlL)
  obtain ⟨-, w, hw, hEw⟩ := (Om10.mem_LomGL_iff_eichler C.E).mp hmem
  exact ⟨w, hw, hEw⟩

theorem Coord95.fix_u (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {l : G} (hlL : l ∈ LB M Q B) :
    (C.φ ⟨l, le_Rt (M := M) (LB M Q B) hs.mem hlL⟩ :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u = C.u := by
  obtain ⟨w, -, hEw⟩ := C.exists_eichler_LB hs hlL
  rw [hEw]
  exact eichler_apply_self _ _

theorem Coord95.vec_mem_span (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {l : G}
    (hlL : l ∈ LB M Q B) {y : Fin 2 ⊕ Fin 2 → K} (hy : polar (quadPlus 2 K) y C.u = 0) :
    ∃ c : K, (C.φ ⟨l, le_Rt (M := M) (LB M Q B) hs.mem hlL⟩ :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y - y = c • C.u := by
  obtain ⟨w, hw, hEw⟩ := C.exists_eichler_LB hs hlL
  refine ⟨-(polar (quadPlus 2 K) y w), ?_⟩
  rw [hEw, eichler_sub_apply' C.hQu hw, hy]
  simp

theorem Coord95.comm_mem_Z_iff (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {x : G}
    (hxL : x ∈ LB M Q B) (v : ↥(Vt M (LB M Q B) B Z t)) :
    ⁅x, (v : G)⁆ ∈ Z ↔ (C.φ ⟨x, le_Rt (M := M) (LB M Q B) hs.mem hxL⟩ :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ v = secVec C.ψ v := by
  have ht : t ∈ LB M Q B := hs.mem
  have hVRn : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  have h1 := secVec_comm C.φ C.ψ C.hψ hVRn ⟨x, le_Rt (M := M) (LB M Q B) ht hxL⟩ v
  rw [← secVec_eq_zero_iff C.ψ ⟨⁅x, (v : G)⁆, comm_mem_of_le_normalizer hVRn
    ⟨x, le_Rt (M := M) (LB M Q B) ht hxL⟩ v⟩]
  rw [h1, sub_eq_zero]

end Coord

theorem relIndex_N1_conj_le (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} {z : G} (hcen : Centre95 hc t Z0) (hzM : z ∈ M)
    (hzL : conjSubgroup z (LB M Q B) = LB M Q B) (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t)
    (hnot : ¬ conjSubgroup z (N1 hc t) ≤ N1 hc t) :
    (N1 hc t).relIndex (N1 hc t ⊔ conjSubgroup z (N1 hc t)) ≤ Nat.card Z := by
  classical
  obtain ⟨K, fK, finK, hK2, hnrm, ⟨C⟩⟩ := exists_coord95 h34 hs hr
  have ht : t ∈ LB M Q B := hs.mem
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have hconjL : ∀ g ∈ conjSubgroup z (N1 hc t), g ∈ LB M Q B := by
    intro g hg
    have h1 : g ∈ conjSubgroup z (LB M Q B) :=
      mem_conjSubgroup.mpr (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hg)).1
    rwa [hzL] at h1
  obtain ⟨x₀, hx₀z, hx₀N1⟩ : ∃ x₀ ∈ conjSubgroup z (N1 hc t), x₀ ∉ N1 hc t := by
    by_contra hcon
    push Not at hcon
    exact hnot hcon
  have hx₀L : x₀ ∈ LB M Q B := hconjL x₀ hx₀z
  have hx₀N : x₀ ∉ hc.CN t := fun hx => hx₀N1 ⟨hx₀L, hx⟩
  obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ N1 hc t, z * y₀ * z⁻¹ = x₀ :=
    ⟨z⁻¹ * x₀ * z, mem_conjSubgroup.mp hx₀z, by group⟩
  obtain ⟨w₀, hw₀, hind, hEw₀, -⟩ := C.plane_facts hs hx₀L hx₀N
  obtain ⟨hCent₀, -⟩ := C.cent_eq_inf h34 h91b hs hr hcen hzM hzN
    (Subgroup.mem_inf.mp hy₀).2 hx₀L hx₀N
  obtain ⟨y', hy'u, hy'w⟩ := exists_polar_pair hQnd C.hu0 hind
  obtain ⟨g, hg⟩ := exists_polar_eq_one hQnd C.hu0
  have hug : polar (quadPlus 2 K) C.u g = 1 := by rw [polar_comm]; exact hg
  obtain ⟨v₀, hv₀QB, hv₀⟩ := (C.hW y').mpr (by rw [polar_comm]; exact hy'u)
  have hv₀D : (v₀ : G) ∉ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) := by
    rw [← hCent₀]
    intro hmemC
    have h1 := (C.comm_mem_Z_iff hs hx₀L v₀).mp (mem_CentMod.mp hmemC).2
    rw [hv₀, hEw₀ y'] at h1
    have h := eichler_sub_apply' C.hQu hw₀ y'
    rw [h1, sub_self, hy'u, hy'w, zero_smul, zero_sub, mul_zero, add_zero, one_smul] at h
    exact C.hu0 (neg_eq_zero.mp h.symm)
  let vec : ↥(LB M Q B) → (Fin 2 ⊕ Fin 2 → K) := fun l =>
    (C.φ ⟨(l : G), le_Rt (M := M) (LB M Q B) ht l.2⟩ :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y' - y'
  have hvec1 : ∀ l : ↥(LB M Q B), ∃ c : K, vec l = c • C.u := fun l =>
    C.vec_mem_span hs l.2 hy'u
  have hvec2 : ∀ l l' : ↥(LB M Q B), vec (l * l') = vec l + vec l' := by
    intro l l'
    obtain ⟨c', hc'⟩ := hvec1 l'
    have hmul : (⟨((l * l' : ↥(LB M Q B)) : G), le_Rt (M := M) (LB M Q B) ht (l * l').2⟩ :
        ↥(Rt M (LB M Q B) t)) = ⟨(l : G), le_Rt (M := M) (LB M Q B) ht l.2⟩ *
          ⟨(l' : G), le_Rt (M := M) (LB M Q B) ht l'.2⟩ := Subtype.ext rfl
    have h3 := hc'
    simp only [vec] at h3
    have h1 : (C.φ ⟨(l' : G), le_Rt (M := M) (LB M Q B) ht l'.2⟩ :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y' = y' + c' • C.u := by
      rw [sub_eq_iff_eq_add'] at h3
      exact h3
    have h2 := C.fix_u hs l.2
    simp only [vec]
    rw [hmul, map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1,
      Matrix.mulVec_add, Matrix.mulVec_smul, h2]
    abel
  have hvec0 : vec 1 = 0 := by
    have h1 : (⟨((1 : ↥(LB M Q B)) : G), le_Rt (M := M) (LB M Q B) ht (1 : ↥(LB M Q B)).2⟩ :
        ↥(Rt M (LB M Q B) t)) = 1 := Subtype.ext rfl
    simp only [vec]
    rw [h1, map_one]
    simp
  let θ : ↥(LB M Q B) →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun l => Multiplicative.ofAdd (vec l)
      map_one' := by rw [hvec0]; rfl
      map_mul' := fun l l' => by rw [hvec2]; rfl }
  have hHL : N1 hc t ⊔ conjSubgroup z (N1 hc t) ≤ LB M Q B := sup_le inf_le_left hconjL
  let ψH : ↥(N1 hc t ⊔ conjSubgroup z (N1 hc t)) →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    θ.comp (Subgroup.inclusion hHL)
  have hvecCN : ∀ l : ↥(LB M Q B), (l : G) ∈ hc.CN t → vec l = 0 := by
    intro l hl
    have h1 : (⟨(l : G), le_Rt (M := M) (LB M Q B) ht l.2⟩ : ↥(Rt M (LB M Q B) t)) ∈ C.φ.ker := by
      rw [C.hker, Subgroup.mem_subgroupOf]
      exact hl
    rw [MonoidHom.mem_ker] at h1
    simp only [vec]
    rw [h1]
    simp
  have hnormN1 : conjSubgroup z (N1 hc t) ≤ Subgroup.normalizer (N1 hc t : Set G) := by
    intro g' hg'
    have hgL : g' ∈ LB M Q B := hconjL g' hg'
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    show g' * a * g'⁻¹ ∈ LB M Q B ⊓ hc.CN t
    exact ⟨(LB M Q B).mul_mem ((LB M Q B).mul_mem hgL (Subgroup.mem_inf.mp ha).1)
      ((LB M Q B).inv_mem hgL),
      hc.CN_conj_mem ht (le_Rt (M := M) (LB M Q B) ht hgL) (Subgroup.mem_inf.mp ha).2⟩
  have hkerH : ψH.ker = (N1 hc t).subgroupOf (N1 hc t ⊔ conjSubgroup z (N1 hc t)) := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (vec (Subgroup.inclusion hHL l)) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro hv
      obtain ⟨n₂, hn₂, n₁, hn₁, hl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormN1
        (by rw [sup_comm]; exact l.2)
      have hn₁L : n₁ ∈ LB M Q B := (Subgroup.mem_inf.mp hn₁).1
      have hn₂L : n₂ ∈ LB M Q B := hconjL n₂ hn₂
      by_cases hn₂N : n₂ ∈ hc.CN t
      · have hn₂N1 : n₂ ∈ N1 hc t := ⟨hn₂L, hn₂N⟩
        show (l : G) ∈ N1 hc t
        rw [← hl]
        exact (N1 hc t).mul_mem hn₂N1 hn₁
      · exfalso
        have hlmul : (Subgroup.inclusion hHL l : ↥(LB M Q B)) = ⟨n₂, hn₂L⟩ * ⟨n₁, hn₁L⟩ :=
          Subtype.ext hl.symm
        rw [hlmul, hvec2, hvecCN ⟨n₁, hn₁L⟩ (Subgroup.mem_inf.mp hn₁).2, add_zero] at hv
        obtain ⟨y₂, hy₂, hn₂eq⟩ : ∃ y₂ ∈ N1 hc t, z * y₂ * z⁻¹ = n₂ :=
          ⟨z⁻¹ * n₂ * z, mem_conjSubgroup.mp hn₂, by group⟩
        have hY := (C.cent_eq_inf h34 h91b hs hr hcen hzM hzN (Subgroup.mem_inf.mp hy₂).2
          (hn₂eq ▸ hn₂L) (hn₂eq ▸ hn₂N)).1
        rw [hn₂eq] at hY
        have hfix : (C.φ ⟨n₂, le_Rt (M := M) (LB M Q B) ht hn₂L⟩ :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ v₀ = secVec C.ψ v₀ := by
          rw [hv₀]
          exact sub_eq_zero.mp hv
        have hcomm := (C.comm_mem_Z_iff hs hn₂L v₀).mpr hfix
        apply hv₀D
        rw [← hY]
        exact mem_CentMod.mpr ⟨v₀.2, hcomm⟩
    · intro hl
      exact hvecCN _ (Subgroup.mem_inf.mp hl).2
  have hidx : (N1 hc t).relIndex (N1 hc t ⊔ conjSubgroup z (N1 hc t)) = Nat.card ψH.range := by
    rw [Subgroup.relIndex, ← hkerH, Subgroup.index_ker]
  have hcardrange : Nat.card ψH.range ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective
      (fun p => polar (quadPlus 2 K) (Multiplicative.toAdd p.1) g) ?_
    rintro ⟨p, l, rfl⟩ ⟨p', l', rfl⟩ h
    obtain ⟨c, hc1⟩ := hvec1 (Subgroup.inclusion hHL l)
    obtain ⟨c', hc2⟩ := hvec1 (Subgroup.inclusion hHL l')
    have e1 : Multiplicative.toAdd (ψH l) = c • C.u := hc1
    have e2 : Multiplicative.toAdd (ψH l') = c' • C.u := hc2
    have h' : polar (quadPlus 2 K) (Multiplicative.toAdd (ψH l)) g =
        polar (quadPlus 2 K) (Multiplicative.toAdd (ψH l')) g := h
    rw [e1, e2, polar_smul_left_eq, polar_smul_left_eq, hug, mul_one, mul_one] at h'
    subst h'
    exact Subtype.ext (Multiplicative.toAdd.injective (e1.trans e2.symm))
  calc (N1 hc t).relIndex (N1 hc t ⊔ conjSubgroup z (N1 hc t)) = Nat.card ψH.range := hidx
    _ ≤ Nat.card K := hcardrange
    _ = Nat.card Z := C.hK

theorem isTypeA2_of_conj95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    (hn7 : 7 ≤ n) {z : G} (hzM : z ∈ M) (hzL : conjSubgroup z (LB M Q B) = LB M Q B) {x : G}
    (hx : x ∈ conjSubgroup z (N1 hc t)) (hxN : x ∉ hc.CN t) : IsTypeA2 M Q Z B t x := by
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ N1 hc t, z * y * z⁻¹ = x :=
    ⟨z⁻¹ * x * z, mem_conjSubgroup.mp hx, by group⟩
  by_contra hnA
  have hxL : z * y * z⁻¹ ∈ LB M Q B := by
    have : z * y * z⁻¹ ∈ conjSubgroup z (LB M Q B) :=
      conj_mem95 z (Subgroup.mem_inf.mp hy).1
    rwa [hzL] at this
  have := rank95_le_six h34 h91b hs hr hzM hy hxL hxN hnA
  omega

end HS9

end CFSG.RankThree.GF2n.Stroth80
