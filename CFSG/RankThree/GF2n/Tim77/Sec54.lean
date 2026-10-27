module

public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
public import CFSG.RankThree.GF2n.Tim77.Sec3Notation
public import CFSG.RankThree.GF2n.Tim77.Sec32a
public import CFSG.RankThree.GF2n.Tim77.Assembly
public import CFSG.RankThree.GF2n.Tim77.TriangleSolvable
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld.RootInvolutions
open Subgroup

section Generic

variable {G : Type*} [Group G]

theorem sec54_sq_one {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E) :
    x * x = 1 := by
  have h := hE.2 x hx
  rwa [pow_two] at h

theorem sec54_nat_two {x y : ℕ} (h : x * y = 2) (hy : y ≠ 1) : x = 1 := by
  rcases Nat.lt_or_ge x 2 with hx | hx
  · interval_cases x <;> simp_all
  · rcases Nat.lt_or_ge y 2 with hy2 | hy2
    · interval_cases y <;> simp_all
    · nlinarith

theorem sec54_nat_two' {x y : ℕ} (h : x * y = 2) (hx : x ≠ 1) : y = 1 := by
  rw [mul_comm] at h
  exact sec54_nat_two h hx

theorem sec54_eq_of_relIndex {H K L : Subgroup G} (hHK : H ≤ K) (hKL : K ≤ L)
    (h2 : H.relIndex L = 2) (hne : K ≠ L) : K = H := by
  have e := Subgroup.relIndex_mul_relIndex _ _ _ hHK hKL
  rw [h2] at e
  have hK1 : K.relIndex L ≠ 1 := fun h1 => hne (le_antisymm hKL (Subgroup.relIndex_eq_one.mp h1))
  have hx : H.relIndex K = 1 := sec54_nat_two e hK1
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hx) hHK

theorem sec54_le_sup_of_relIndex {K H : Subgroup G} (hKH : K ≤ H) (h2 : K.relIndex H = 2)
    {g : G} (hg : g ∈ H) (hgK : g ∉ K) : H ≤ K ⊔ Subgroup.closure {g} := by
  have hgP : g ∈ K ⊔ Subgroup.closure {g} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton g))
  have hPH : K ⊔ Subgroup.closure {g} ≤ H :=
    sup_le hKH ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hg))
  have e := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left : K ≤ K ⊔ Subgroup.closure {g}) hPH
  rw [h2] at e
  have hK1 : K.relIndex (K ⊔ Subgroup.closure {g}) ≠ 1 :=
    fun h1 => hgK (Subgroup.relIndex_eq_one.mp h1 hgP)
  have hy : (K ⊔ Subgroup.closure {g}).relIndex H = 1 := sec54_nat_two' e hK1
  exact Subgroup.relIndex_eq_one.mp hy

theorem sec54_normalizes_of_ti [Finite G] {T : Subgroup G} (hT : IsTI T) {x : G}
    (hx : T ⊓ conjSubgroup x T ≠ ⊥) : x ∈ Subgroup.normalizer (T : Set G) := by
  have h := conjSubgroup_eq_of_inf_ne_bot hT (g := x) (h := 1)
    (by rw [conjSubgroup_one, inf_comm]; exact hx)
  rw [conjSubgroup_one] at h
  exact conjSubgroup_eq_self_iff.mp h

theorem sec54_conj_fix {A S : Subgroup G} {b : G} (hS : S ≤ A)
    (hb : b ∈ centralizer (A : Set G)) : conjSubgroup b S = S := by
  have hcomm : ∀ y ∈ S, b * y * b⁻¹ = y := by
    intro y hy
    have h1 : y * b = b * y := Subgroup.mem_centralizer_iff.mp hb y (hS hy)
    rw [← h1, mul_inv_cancel_right]
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have e : x = b⁻¹ * x * b := by
      calc x = b * (b⁻¹ * x * b) * b⁻¹ := by group
        _ = b⁻¹ * x * b := hcomm _ hx
    rw [e]
    exact hx
  · intro hx
    have h1 : x * b = b * x := Subgroup.mem_centralizer_iff.mp hb x (hS hx)
    have e : b⁻¹ * x * b = x := by
      calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
        _ = b⁻¹ * (b * x) := by rw [h1]
        _ = x := by group
    rw [e]
    exact hx

theorem sec54_dihedral_mem {X M : Subgroup G} [(M.subgroupOf X).Normal]
    (e : ↥X ⧸ M.subgroupOf X ≃* DihedralGroup 3) {a c : G} (ha : a ∈ X) (hc : c ∈ X)
    (ha2 : a * a = 1) (hc2 : c * c = 1) (ha' : a ∉ M) (hc' : c ∉ M) (hac' : a * c ∉ M) :
    (a * c) ^ 3 ∈ M := by
  have key : ∀ u v : DihedralGroup 3, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v →
      (u * v) ^ 3 = 1 := by decide
  let φ : ↥X →* DihedralGroup 3 := e.toMonoidHom.comp (QuotientGroup.mk' (M.subgroupOf X))
  have hφ : ∀ x : ↥X, φ x = 1 → x ∈ M.subgroupOf X := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    rw [map_one]
    exact hx
  have hsq : ∀ x : ↥X, (x : G) * x = 1 → φ x * φ x = 1 := by
    intro x hx
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext hx
  have hA2 := hsq ⟨a, ha⟩ ha2
  have hC2 := hsq ⟨c, hc⟩ hc2
  have hA1 : φ ⟨a, ha⟩ ≠ 1 := fun h => ha' (Subgroup.mem_subgroupOf.mp (hφ _ h))
  have hC1 : φ ⟨c, hc⟩ ≠ 1 := fun h => hc' (Subgroup.mem_subgroupOf.mp (hφ _ h))
  have hAC : φ ⟨a, ha⟩ ≠ φ ⟨c, hc⟩ := by
    intro h
    have h1 : φ (⟨a, ha⟩⁻¹ * ⟨c, hc⟩) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : a⁻¹ * c ∈ M := Subgroup.mem_subgroupOf.mp (hφ _ h1)
    apply hac'
    rwa [inv_eq_of_mul_eq_one_right ha2] at h2
  have hk := key _ _ hA2 hC2 hA1 hC1 hAC
  have hpow : φ ((⟨a, ha⟩ * ⟨c, hc⟩ : ↥X) ^ 3) = 1 := by
    rw [map_pow, map_mul]
    exact hk
  exact Subgroup.mem_subgroupOf.mp (hφ _ hpow)

theorem sec54_solvable_of_triangle_mod {H K : Subgroup G} (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] [IsMulCommutative K] {a b c : G}
    (hH : H ≤ K ⊔ Subgroup.closure ({a, b, c} : Set G)) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : (a * b) ^ 3 ∈ K) (hac : (a * c) ^ 3 ∈ K) (hbc : (b * c) ^ 3 ∈ K ∨ (b * c) ^ 2 ∈ K) :
    Group.IsSolvable ↥H := by
  obtain ⟨a', ha'⟩ : ∃ a' : ↥H, (a' : G) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ↥H, (b' : G) = b := ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ↥H, (c' : G) = c := ⟨⟨c, hc⟩, rfl⟩
  have hsolvK : Group.IsSolvable ↥(K.subgroupOf H) :=
    tri77_solvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH)
  have hP : K.subgroupOf H ⊔ Subgroup.closure ({a', b', c'} : Set ↥H) = ⊤ := by
    rw [eq_top_iff]
    intro h _
    have hmap : K ⊔ Subgroup.closure ({a, b, c} : Set G) ≤
        (K.subgroupOf H ⊔ Subgroup.closure ({a', b', c'} : Set ↥H)).map H.subtype := by
      refine sup_le ?_ ?_
      · intro k hk
        have hkK : (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hk
        exact Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_sup_left hkK)
      · rw [Subgroup.closure_le]
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h1 | h1 | h1 <;> rw [h1]
        · rw [← ha']
          exact Subgroup.mem_map_of_mem _
            (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        · rw [← hb']
          exact Subgroup.mem_map_of_mem _
            (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        · rw [← hc']
          exact Subgroup.mem_map_of_mem _
            (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp (hmap (hH h.2))
    have hph : p = h := Subtype.ext hpe
    rw [← hph]
    exact hp
  have hrel : ∀ x y : ↥H, (x * y) ^ 3 ∈ K.subgroupOf H →
      (QuotientGroup.mk' (K.subgroupOf H) x * QuotientGroup.mk' (K.subgroupOf H) y) ^ 3 = 1 := by
    intro x y hxy
    rw [← map_mul, ← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hxy
  have hrel2 : ∀ x y : ↥H, (x * y) ^ 2 ∈ K.subgroupOf H →
      (QuotientGroup.mk' (K.subgroupOf H) x * QuotientGroup.mk' (K.subgroupOf H) y) ^ 2 = 1 := by
    intro x y hxy
    rw [← map_mul, ← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hxy
  have hsq : ∀ x : ↥H, (x : G) * x = 1 → QuotientGroup.mk' (K.subgroupOf H) x *
      QuotientGroup.mk' (K.subgroupOf H) x = 1 := by
    intro x hx
    rw [← map_mul, ← map_one (QuotientGroup.mk' (K.subgroupOf H))]
    congr 1
    exact Subtype.ext hx
  have hQgen : Subgroup.closure
      ({QuotientGroup.mk' (K.subgroupOf H) a', QuotientGroup.mk' (K.subgroupOf H) b',
        QuotientGroup.mk' (K.subgroupOf H) c'} : Set (↥H ⧸ K.subgroupOf H)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) q
    have hh : h ∈ K.subgroupOf H ⊔ Subgroup.closure ({a', b', c'} : Set ↥H) := by
      rw [hP]; exact Subgroup.mem_top h
    obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    have hk1 : QuotientGroup.mk' (K.subgroupOf H) k = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff k).mpr hk
    have hz' := Subgroup.mem_map_of_mem (QuotientGroup.mk' (K.subgroupOf H)) hz
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton] at hz'
    rw [map_mul, hk1, one_mul]
    exact hz'
  have hQ : Group.IsSolvable (↥H ⧸ K.subgroupOf H) := by
    have hs := isSolvable_closure_of_triangle (hsq a' (by rw [ha']; exact ha2))
      (hsq b' (by rw [hb']; exact hb2)) (hsq c' (by rw [hc']; exact hc2))
      (hrel a' b' (Subgroup.mem_subgroupOf.mpr (by
        rw [Subgroup.coe_pow, Subgroup.coe_mul, ha', hb']; exact hab)))
      (hrel a' c' (Subgroup.mem_subgroupOf.mpr (by
        rw [Subgroup.coe_pow, Subgroup.coe_mul, ha', hc']; exact hac)))
      (by
        rcases hbc with h3 | h2
        · left
          exact hrel b' c' (Subgroup.mem_subgroupOf.mpr (by
            rw [Subgroup.coe_pow, Subgroup.coe_mul, hb', hc']; exact h3))
        · right
          exact hrel2 b' c' (Subgroup.mem_subgroupOf.mpr (by
            rw [Subgroup.coe_pow, Subgroup.coe_mul, hb', hc']; exact h2)))
    rw [hQgen] at hs
    exact tri77_solvable_of_mulEquiv Subgroup.topEquiv.symm
  exact Group.isSolvable_of_subgroup_quotient (K.subgroupOf H)

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec54_inf_M_A (h : Sec3Ctx A Abar S₀ B) :
    A ⊓ Section3.M A Abar = Section3.A0 A Abar :=
  h.setup.inf_M

theorem sec54_inf_M_Abar (h : Sec3Ctx A Abar S₀ B) :
    Abar ⊓ Section3.M A Abar = Section3.Abar0 A Abar := by
  have := h.setup_symm.inf_M
  rw [sup_comm] at this
  exact this

theorem sec54_M_le_S0 (h : Sec3Ctx A Abar S₀ B) : Section3.M A Abar ≤ S₀ :=
  sup_le (inf_le_left.trans h.a_le_s0) h.abar0_le_s0

theorem sec54_M_pgroup (h : Sec3Ctx A Abar S₀ B) : IsPGroup 2 ↥(Section3.M A Abar) :=
  h.isPGroup_s0.to_le (sec54_M_le_S0 h)

theorem sec54_mul_not_mem_M (h : Sec3Ctx A Abar S₀ B) {a c : G} (ha : a ∈ A)
    (ha0 : a ∉ Section3.A0 A Abar) (hc : c ∈ Abar) (hc0 : c ∉ Section3.Abar0 A Abar) :
    a * c ∉ Section3.M A Abar := by
  intro hM
  have hodd : Odd (orderOf (a * c)) := h.setup.odd_orderOf_mul ha ha0 hc hc0
  obtain ⟨k, hk⟩ := sec54_M_pgroup h ⟨a * c, hM⟩
  have hk' : (a * c) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf (a * c) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf (a * c)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Odd.coprime_two_right hodd)
  have h1 : orderOf (a * c) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hac1 : a * c = 1 := orderOf_eq_one_iff.mp h1
  have hcA : c = a⁻¹ := eq_inv_of_mul_eq_one_right hac1
  have hcA' : c ∈ A := by
    rw [hcA]
    exact A.inv_mem ha
  have hc1 : c = 1 := by
    have hmem : c ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨hcA', hc⟩
    rw [h.inf_abar_eq_bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact hc0 (hc1 ▸ Subgroup.one_mem _)

theorem sec54_not_mem_M_A (h : Sec3Ctx A Abar S₀ B) {a : G} (ha : a ∈ A)
    (ha0 : a ∉ Section3.A0 A Abar) : a ∉ Section3.M A Abar := by
  intro hM
  have hmem : a ∈ A ⊓ Section3.M A Abar := Subgroup.mem_inf.mpr ⟨ha, hM⟩
  rw [sec54_inf_M_A h] at hmem
  exact ha0 hmem

theorem sec54_not_mem_M_Abar (h : Sec3Ctx A Abar S₀ B) {c : G} (hc : c ∈ Abar)
    (hc0 : c ∉ Section3.Abar0 A Abar) : c ∉ Section3.M A Abar := by
  intro hM
  have hmem : c ∈ Abar ⊓ Section3.M A Abar := Subgroup.mem_inf.mpr ⟨hc, hM⟩
  rw [sec54_inf_M_Abar h] at hmem
  exact hc0 hmem

theorem sec54_rel_three (h53 : Tim77Sec53Statement) {A Abar' S₀' B' : Subgroup G}
    (h' : Sec3Ctx A Abar' S₀' B') (hq' : Section3.q A Abar' = 2)
    (hnot' : ¬ Sec4A0LeCenterH A Abar') {a c : G} (ha : a ∈ A)
    (ha0 : a ∉ Section3.A0 A Abar') (hc : c ∈ Abar') (hc0 : c ∉ Section3.Abar0 A Abar') :
    (a * c) ^ 3 ∈ Section3.M A Abar' := by
  have hMX : Section3.M A Abar' ≤ Section3.X A Abar' := by
    unfold Section3.M Section3.X
    exact sup_le (le_sup_of_le_left inf_le_left) (le_sup_of_le_right inf_le_left)
  haveI hMn : ((Section3.M A Abar').subgroupOf (Section3.X A Abar')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).mpr h'.setup.sup_le_normalizer_M
  obtain ⟨e⟩ := h53 G A Abar' S₀' B' h' hq' hnot'
  have hXa : a ∈ Section3.X A Abar' := Subgroup.mem_sup_left ha
  have hXc : c ∈ Section3.X A Abar' := Subgroup.mem_sup_right hc
  obtain ⟨α, hα⟩ := h'.exists_abar_eq
  have hsq_a : a * a = 1 := sec54_sq_one h'.hyp.elemAbelian ha
  have hsq_c : c * c = 1 := by
    rw [hα] at hc
    exact sec54_sq_one (isElemAbelian_conj h'.hyp.elemAbelian α) hc
  exact sec54_dihedral_mem e hXa hXc hsq_a hsq_c
    (sec54_not_mem_M_A h' ha ha0) (sec54_not_mem_M_Abar h' hc hc0)
    (sec54_mul_not_mem_M h' ha ha0 hc hc0)

theorem sec54_notation_of_choice (h : Sec3Ctx A Abar S₀ B) {Abar' : Subgroup G}
    (hc : Section3.IsChoice A Abar') :
    ∃ S₀' B' : Subgroup G, Section3.Notation A Abar' S₀' B' := by
  have hA := h.hyp.elemAbelian
  have hAbar' : IsElemAbelian 2 Abar' := by
    obtain ⟨⟨g, hg⟩, -, -⟩ := hc
    rw [hg]
    exact isElemAbelian_conj hA g
  obtain ⟨Q, hQ⟩ := notation_exists_sylow_choice hA hAbar'
  obtain ⟨B', hB1, hB2, hB3⟩ := notation_exists_B hA h.not_wc Q
  exact ⟨(Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype, B',
    { choice := hc
      sylow := notation_sylow_map_max Q
      contains := hQ
      conj := hB1
      ne := hB2
      le := hB3 }⟩

theorem sec54_ctx_conj (h : Sec3Ctx A Abar S₀ B) {b : G} (hb : b ∈ B) :
    Sec3Ctx A (conjSubgroup b Abar) (conjSubgroup b S₀) (conjSubgroup b B) := by
  have hAb : conjSubgroup b A = A := conjSubgroup_eq_of_mem_centralizer (h.b_le_centralizer hb)
  have := h.conj b
  rw [hAb] at this
  exact this

end Context

theorem sec54_of (h53 : Tim77Sec53Statement) (h43 : Tim77Sec43Statement)
    (h44 : Tim77Sec44Statement) (h35 : Tim77Sec35Statement) : Tim77Sec54Statement := by
  intro G _ _ A Abar S₀ B h hq hall
  have hnot : ¬ Sec4A0LeCenterH A Abar := hall Abar S₀ B h
  obtain ⟨b, hb, hb1, hY⟩ := sec45_of h43 h44 h35 h hq
  obtain ⟨g₀, hg₀⟩ := h.exists_abar_eq
  have hA := h.hyp.elemAbelian
  have hAel : IsElemAbelian 2 Abar := by rw [hg₀]; exact isElemAbelian_conj hA g₀
  obtain ⟨gB, hgB⟩ := h.nota.conj
  have hBel : IsElemAbelian 2 B := by rw [hgB]; exact isElemAbelian_conj hA gB
  have hbb : b * b = 1 := sec54_sq_one hBel hb
  have hbC : b ∈ centralizer (A : Set G) := h.b_le_centralizer hb
  have hAb : conjSubgroup b A = A := conjSubgroup_eq_of_mem_centralizer hbC
  have hconjb : ∀ T : Subgroup G, conjSubgroup b (conjSubgroup b T) = T := by
    intro T
    rw [← conjSubgroup_mul, hbb, conjSubgroup_one]
  have hTI : IsTI (conjSubgroup b Abar) := isTI_conjSubgroup h.setup.ti_Ab b
  have ha0A : Section3.A0 A Abar ≤ A := inf_le_left
  have hbar0A : Section3.Abar0 A Abar ≤ Abar := inf_le_left
  obtain ⟨α, hαA, hαA0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne ha0A h.a0_ne)
  obtain ⟨β, hβAbar, hβ0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hbar0A h.abar0_ne)
  obtain ⟨γ, hγdef⟩ : ∃ γ : G, γ = b * β * b⁻¹ := ⟨_, rfl⟩
  have hγAb : γ ∈ conjSubgroup b Abar := by
    rw [hγdef]; exact (mem_conjSubgroup_conj_t77 b β Abar).mpr hβAbar
  have hγ0 : γ ∉ conjSubgroup b (Section3.Abar0 A Abar) := by
    rw [hγdef]; exact fun hc => hβ0 ((mem_conjSubgroup_conj_t77 b β _).mp hc)
  have hγγ : γ * γ = 1 := sec54_sq_one (isElemAbelian_conj hAel b) hγAb
  obtain ⟨x, hxA, hx1, hxo⟩ := h44 G A Abar S₀ B h hq b hb hb1
  have hIS : Section3.IsSChoice A Abar S₀ B b := ⟨b, hb, hb1, Or.inl ⟨⟨x, hxA, hx1, hxo⟩, rfl⟩⟩
  obtain ⟨hNY, hNnorm, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B b h hIS
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = Section3.N A Abar b := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = Section3.Y A Abar b := ⟨_, rfl⟩
  have hNY' : N ≤ Y := by rw [hN, hYdef]; exact hNY
  have hNnorm' : ∀ y ∈ Y, y ∈ Subgroup.normalizer (N : Set G) := by
    rw [hN, hYdef]; exact hNnorm
  have hNab' : IsElemAbelian 2 N := by rw [hN]; exact hNab
  have hY' : ¬ Group.IsSolvable ↥Y := by rw [hYdef]; exact hY
  have hNA0 : Section3.A0 A Abar ≤ N := by rw [hN]; exact le_sup_of_le_left le_sup_left
  have hNAbar0 : Section3.Abar0 A Abar ≤ N := by
    rw [hN]; exact le_sup_of_le_left le_sup_right
  have hNconj : conjSubgroup b (Section3.Abar0 A Abar) ≤ N := by
    rw [hN]; exact le_sup_right
  have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hNab'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hMN : Section3.M A Abar ≤ N := by rw [hN]; exact le_sup_left
  have hαβ : (α * β) ^ 3 ∈ N :=
    hMN (sec54_rel_three h53 h hq hnot hαA hαA0 hβAbar hβ0)
  have hctx := sec54_ctx_conj h hb
  have hqb : Section3.q A (conjSubgroup b Abar) = 2 := by
    have := section3_q_conj A Abar b
    rw [hAb] at this
    exact this.trans hq
  have hnotb : ¬ Sec4A0LeCenterH A (conjSubgroup b Abar) := hall _ _ _ hctx
  have hA0b : Section3.A0 A (conjSubgroup b Abar) = Section3.A0 A Abar := by
    have := section3_A0_conj A Abar b
    rw [hAb, sec54_conj_fix ha0A hbC] at this
    exact this
  have hAbar0b : Section3.Abar0 A (conjSubgroup b Abar) =
      conjSubgroup b (Section3.Abar0 A Abar) := by
    have := section3_Abar0_conj A Abar b
    rw [hAb] at this
    exact this
  have hαγ : (α * γ) ^ 3 ∈ N := by
    have h3 := sec54_rel_three h53 hctx hqb hnotb hαA (by rw [hA0b]; exact hαA0) hγAb
      (by rw [hAbar0b]; exact hγ0)
    have hMb : Section3.M A (conjSubgroup b Abar) ≤ N := by
      rw [hN]
      unfold Section3.M
      rw [hA0b, hAbar0b]
      exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    exact hMb h3
  have hβγ : (β * γ) ^ 3 ∈ N ∨ (β * γ) ^ 2 ∈ N := by
    by_cases hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup b Abar, x * y = y * x
    · right
      have hββ : β * β = 1 := sec54_sq_one hAel hβAbar
      have hc : β * γ = γ * β := hcomm β hβAbar γ hγAb
      have h2 : (β * γ) ^ 2 = 1 := by
        rw [pow_two]
        calc β * γ * (β * γ) = (β * β) * (γ * γ) := by
              rw [show β * γ * (β * γ) = β * (γ * β) * γ by group, ← hc]
              group
          _ = 1 := by rw [hββ, hγγ, mul_one]
      rw [h2]
      exact Subgroup.one_mem _
    · left
      have hnb : ∀ x ∈ Section3.Abar0 A Abar,
          x ∈ Subgroup.normalizer (conjSubgroup b Abar : Set G) := by
        intro x hx
        apply sec54_normalizes_of_ti hTI
        have hsub : conjSubgroup b (Section3.Abar0 A Abar) ≤
            conjSubgroup b Abar ⊓ conjSubgroup x (conjSubgroup b Abar) := by
          intro y hy
          have hy' : y ∈ conjSubgroup b Abar := (conjSubgroup_le_conj_iff b).mpr hbar0A hy
          refine Subgroup.mem_inf.mpr ⟨hy', ?_⟩
          rw [mem_conjSubgroup]
          have hcx : x * y = y * x := hNcomm x (hNAbar0 hx) y (hNconj hy)
          have e : x⁻¹ * y * x = y := by
            calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
              _ = x⁻¹ * (x * y) := by rw [hcx]
              _ = y := by group
          rw [e]
          exact hy'
        intro hbot
        have h1 := hsub.trans (le_of_eq hbot)
        exact h.abar0_ne_bot ((conjSubgroup_eq_bot_t77 b _).mp (le_bot_iff.mp h1))
      have hsubN : Section3.Abar0 A Abar ≤ normalizerIn Abar (conjSubgroup b Abar) :=
        fun x hx => Subgroup.mem_inf.mpr ⟨hbar0A hx, hnb x hx⟩
      have hnorm_fail : ¬ (Abar ≤ Subgroup.normalizer (conjSubgroup b Abar : Set G)) := by
        intro hle
        apply hcomm
        have e1 : conjSubgroup (b * g₀) A = conjSubgroup b Abar := by
          rw [conjSubgroup_mul, ← hg₀]
        have e2 : conjSubgroup g₀ A = Abar := hg₀.symm
        have hP2 : IsPGroup 2 ↥(conjSubgroup b Abar ⊔ Abar) :=
          IsPGroup.to_sup_of_normal_left'
            (notation_isPGroup_two_of_le (isElemAbelian_conj hAel b) le_rfl)
            (notation_isPGroup_two_of_le hAel le_rfl) hle
        have hP : IsPGroup 2 ↥(conjSubgroup g₀ A ⊔ conjSubgroup (b * g₀) A) := by
          rw [e1, e2, sup_comm]
          exact hP2
        have hN' : normalizerIn (conjSubgroup g₀ A) (conjSubgroup (b * g₀) A) ≠ ⊥ := by
          rw [e1, e2]
          intro e
          apply h.abar0_ne_bot
          have h1 : Section3.Abar0 A Abar ≤ ⊥ := by
            rw [← e]
            exact hsubN
          exact le_bot_iff.mp h1
        have key := commute_of_isPGroup hA h.hyp.ti hP hN'
        rw [e1, e2] at key
        exact key
      have hK_eq : normalizerIn Abar (conjSubgroup b Abar) = Section3.Abar0 A Abar := by
        refine sec54_eq_of_relIndex hsubN inf_le_left hq ?_
        intro e
        apply hnorm_fail
        intro x hx
        have hx' : x ∈ normalizerIn Abar (conjSubgroup b Abar) := by
          rw [e]
          exact hx
        exact (Subgroup.mem_inf.mp hx').2
      have hstep1 : normalizerIn (conjSubgroup b Abar) Abar =
          conjSubgroup b (Section3.Abar0 A Abar) := by
        have e := normalizerIn_conjSubgroup_t77 b Abar (conjSubgroup b Abar)
        rw [hconjb Abar, hK_eq] at e
        exact e
      obtain ⟨Abar'', hAbar''⟩ : ∃ Abar'' : Subgroup G,
          Abar'' = conjSubgroup g₀⁻¹ (conjSubgroup b Abar) := ⟨_, rfl⟩
      have hAgA : conjSubgroup g₀⁻¹ Abar = A := by
        rw [hg₀, conjSubgroup_inv_conj_cancel]
      have hgAbar'' : conjSubgroup g₀ Abar'' = conjSubgroup b Abar := by
        rw [hAbar'', conjSubgroup_conj_inv_cancel]
      have hAbar''conj : ∃ g : G, Abar'' = conjSubgroup g A := by
        refine ⟨g₀⁻¹ * (b * g₀), ?_⟩
        rw [hAbar'', conjSubgroup_mul g₀⁻¹ (b * g₀), conjSubgroup_mul b g₀, ← hg₀]
      have hA''A : Section3.Abar0 A Abar'' =
          conjSubgroup g₀⁻¹ (conjSubgroup b (Section3.Abar0 A Abar)) := by
        have e := normalizerIn_conjSubgroup_t77 g₀⁻¹ (conjSubgroup b Abar) Abar
        rw [hAgA, hstep1] at e
        rw [hAbar'']
        exact e
      have hA0''conj : conjSubgroup g₀ (Section3.A0 A Abar'') = Section3.Abar0 A Abar := by
        have e := normalizerIn_conjSubgroup_t77 g₀ A Abar''
        rw [← hg₀, hgAbar'', hK_eq] at e
        exact e.symm
      have hAbar0''conj : conjSubgroup g₀ (Section3.Abar0 A Abar'') =
          conjSubgroup b (Section3.Abar0 A Abar) := by
        have e := normalizerIn_conjSubgroup_t77 g₀ Abar'' A
        rw [hgAbar'', ← hg₀, hstep1] at e
        exact e.symm
      have hcardA0 : Nat.card (Section3.Abar0 A Abar'') = Nat.card (Section3.Abar0 A Abar) := by
        rw [hA''A, card_conjSubgroup, card_conjSubgroup]
      have hchoice : Section3.IsChoice A Abar'' := by
        refine ⟨hAbar''conj, ⟨?_, ?_⟩, ?_⟩
        · intro e
          have e' : Section3.Abar0 A Abar'' = ⊥ := e
          rw [hA''A, conjSubgroup_eq_bot_t77, conjSubgroup_eq_bot_t77] at e'
          exact h.abar0_ne_bot e'
        · intro e
          have e' : Section3.Abar0 A Abar'' = Abar'' := e
          have h1 : Nat.card ↥(Section3.Abar0 A Abar'') = Nat.card ↥Abar'' :=
            congrArg (fun H : Subgroup G => Nat.card ↥H) e'
          rw [hcardA0, hAbar'', card_conjSubgroup, card_conjSubgroup] at h1
          have h2 := Subgroup.relIndex_mul_card (H := Section3.Abar0 A Abar) (K := Abar)
          have hq' : (Section3.Abar0 A Abar).relIndex Abar = 2 := hq
          rw [inf_of_le_left hbar0A, hq'] at h2
          have hpos : 0 < Nat.card (Section3.Abar0 A Abar) := Nat.card_pos
          omega
        · intro g' hg'
          have hc : Nat.card (normalizerIn Abar'' A) = Nat.card (Section3.Abar0 A Abar) := hcardA0
          rw [hc]
          exact h.nota.choice.2.2 g' hg'
      obtain ⟨S₀'', B'', hN''⟩ := sec54_notation_of_choice h hchoice
      have h'' : Sec3Ctx A Abar'' S₀'' B'' := ⟨h.hyp, h.not_root, h.not_wc, hN''⟩
      have hnot'' : ¬ Sec4A0LeCenterH A Abar'' := hall _ _ _ h''
      have hq'' : Section3.q A Abar'' = 2 := (section3_q_eq_of_ctx h'' h).trans hq
      have hβ'' : g₀⁻¹ * β * g₀ ∈ A := by
        have hb' := hβAbar
        rw [hg₀] at hb'
        exact mem_conjSubgroup.mp hb'
      have hβ''0 : g₀⁻¹ * β * g₀ ∉ Section3.A0 A Abar'' := by
        intro hmem
        have h1 : β ∈ conjSubgroup g₀ (Section3.A0 A Abar'') := mem_conjSubgroup.mpr hmem
        rw [hA0''conj] at h1
        exact hβ0 h1
      have hγ''mem : g₀⁻¹ * γ * g₀ ∈ Abar'' := by
        have e : g₀ * (g₀⁻¹ * γ * g₀) * g₀⁻¹ = γ := by group
        have hmem : g₀ * (g₀⁻¹ * γ * g₀) * g₀⁻¹ ∈ conjSubgroup g₀ Abar'' := by
          rw [e, hgAbar'']
          exact hγAb
        exact (mem_conjSubgroup_conj_t77 g₀ _ Abar'').mp hmem
      have hγ''0 : g₀⁻¹ * γ * g₀ ∉ Section3.Abar0 A Abar'' := by
        intro hmem
        have e : g₀ * (g₀⁻¹ * γ * g₀) * g₀⁻¹ = γ := by group
        have h1 : g₀ * (g₀⁻¹ * γ * g₀) * g₀⁻¹ ∈ conjSubgroup g₀ (Section3.Abar0 A Abar'') :=
          (mem_conjSubgroup_conj_t77 g₀ _ _).mpr hmem
        rw [e, hAbar0''conj] at h1
        exact hγ0 h1
      have hrel'' := sec54_rel_three h53 h'' hq'' hnot'' hβ'' hβ''0 hγ''mem hγ''0
      have hsubM : conjSubgroup g₀ (Section3.M A Abar'') ≤ N := by
        unfold Section3.M
        rw [conjSubgroup_sup_t77]
        refine sup_le ?_ ?_
        · rw [hA0''conj]
          exact hNAbar0
        · rw [hAbar0''conj]
          exact hNconj
      have hβγconj : β * γ =
          g₀ * ((g₀⁻¹ * β * g₀) * (g₀⁻¹ * γ * g₀)) * g₀⁻¹ := by group
      have hfinal : (β * γ) ^ 3 ∈ N := by
        have hmem := hsubM ((mem_conjSubgroup_conj_t77 g₀ _ _).mpr hrel'')
        rw [hβγconj, conj_pow]
        exact hmem
      exact hfinal
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = Subgroup.closure ({α, β, γ} : Set G) := ⟨_, rfl⟩
  have hcl_α : Subgroup.closure ({α} : Set G) ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
  have hcl_β : Subgroup.closure ({β} : Set G) ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
  have hcl_γ : Subgroup.closure ({γ} : Set G) ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
  have hidxA : (Section3.A0 A Abar).relIndex A = 2 := by
    have := h.setup.relIndex_Lb
    rw [← this]
    exact hq
  have hA_le : A ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) :=
    (sec54_le_sup_of_relIndex ha0A hidxA hαA hαA0).trans
      (sup_le (le_sup_of_le_left hNA0) hcl_α)
  have hAbar_le : Abar ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) :=
    (sec54_le_sup_of_relIndex hbar0A hq hβAbar hβ0).trans
      (sup_le (le_sup_of_le_left hNAbar0) hcl_β)
  have hconj_le : conjSubgroup b Abar ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) := by
    have hrel : (conjSubgroup b (Section3.Abar0 A Abar)).relIndex (conjSubgroup b Abar) = 2 := by
      rw [relIndex_conjSubgroup_t77]
      exact hq
    exact (sec54_le_sup_of_relIndex ((conjSubgroup_le_conj_iff b).mpr hbar0A) hrel hγAb hγ0).trans
      (sup_le (le_sup_of_le_left hNconj) hcl_γ)
  have hYgen : Y ≤ N ⊔ Subgroup.closure ({α, β, γ} : Set G) := by
    rw [hYdef]
    exact sup_le (sup_le hA_le hAbar_le) hconj_le
  have hAY : A ≤ Y := by rw [hYdef]; exact le_sup_of_le_left le_sup_left
  have hAbarY : Abar ≤ Y := by rw [hYdef]; exact le_sup_of_le_left le_sup_right
  have hconjY : conjSubgroup b Abar ≤ Y := by rw [hYdef]; exact le_sup_right
  have hsolv : Group.IsSolvable ↥Y := by
    haveI : (N.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff hNY').mpr fun k₁ k₂ hk₁ hk₂ =>
        (Subgroup.mem_normalizer_iff.mp (hNnorm' k₂ hk₂) k₁).mp hk₁
    haveI : IsMulCommutative ↥N := hNab'.1
    exact sec54_solvable_of_triangle_mod hNY' hYgen (hAY hαA) (hAbarY hβAbar) (hconjY hγAb)
      (sec54_sq_one hA hαA) (sec54_sq_one hAel hβAbar) hγγ hαβ hαγ hβγ
  exact hY' hsolv

end CFSG.RankThree.GF2n.Tim77
