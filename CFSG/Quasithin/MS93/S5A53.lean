module

public import CFSG.Quasithin.MS93.S5A54
public import CFSG.Quasithin.MS93.S5A53Sp

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mod_of_isPGroup {P Y N : Subgroup G} (hP : IsPGroup 2 P)
    (hYN : IsPGroup 2 ↥(Y ⊔ N)) (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hYnN : Y ≤ Subgroup.normalizer (N : Set G))
    (hNnY : N ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ Y ≤ N) :
    ∃ y ∈ Y, y ∉ N ∧ ∀ p ∈ P, ⁅p, y⁆ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := P ⊔ (Y ⊔ N) with hK
  have hPYN : P ≤ Subgroup.normalizer ((Y ⊔ N : Subgroup G) : Set G) := le_normalizer_sup hPY hPN
  have hK2 : IsPGroup 2 K := IsPGroup.to_sup_of_normal_right' hP hYN hPYN
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hPN (sup_le hYnN Subgroup.le_normalizer)
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le hPY (sup_le Subgroup.le_normalizer hNnY)
  have hNK : N ≤ K := le_sup_right.trans le_sup_right
  have hYK : Y ≤ K := le_sup_left.trans le_sup_right
  have hPK : P ≤ K := le_sup_left
  set N' : Subgroup ↥K := N.subgroupOf K
  have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  set Y' : Subgroup ↥K := Y.subgroupOf K
  have hY' : Y'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).2 hKY
  have hQ : IsPGroup 2 (↥K ⧸ N') := hK2.to_quotient N'
  have : Group.IsNilpotent (↥K ⧸ N') := hQ.isNilpotent
  set Y'' : Subgroup (↥K ⧸ N') := Y'.map (QuotientGroup.mk' N')
  have hY'' : Y''.Normal := hY'.map _ (QuotientGroup.mk'_surjective N')
  have hne : Y'' ≠ ⊥ := by
    intro h0
    apply hY
    intro y hy
    have hyY' : (⟨y, hYK hy⟩ : ↥K) ∈ Y' := hy
    have h1 : QuotientGroup.mk' N' ⟨y, hYK hy⟩ ∈ Y'' := ⟨_, hyY', rfl⟩
    rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨⟨y, hyK⟩, hyY, hyz⟩ := (Subgroup.mem_inf.1 z.2).1
  have hzc := (Subgroup.mem_inf.1 z.2).2
  refine ⟨y, hyY, fun hyN => hz1 ?_, fun p hp => ?_⟩
  · apply Subtype.ext
    change (z : ↥K ⧸ N') = 1
    rw [← hyz]
    exact (QuotientGroup.eq_one_iff _).2 hyN
  · have hc := Subgroup.mem_center_iff.1 hzc (QuotientGroup.mk' N' ⟨p, hPK hp⟩)
    rw [← hyz] at hc
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc
    have e : ((⟨p, hPK hp⟩ * ⟨y, hyK⟩ : ↥K)⁻¹ * (⟨y, hyK⟩ * ⟨p, hPK hp⟩) : ↥K) =
        ⟨(y * p)⁻¹ * ⁅p, y⁆⁻¹ * (y * p), K.mul_mem (K.mul_mem (K.inv_mem (K.mul_mem hyK
          (hPK hp))) (K.inv_mem (K.mul_mem (K.mul_mem (K.mul_mem (hPK hp) hyK)
          (K.inv_mem (hPK hp))) (K.inv_mem hyK)))) (K.mul_mem hyK (hPK hp))⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e] at hc
    have hc' : (y * p)⁻¹ * ⁅p, y⁆⁻¹ * (y * p) ∈ N := hc
    have hyp : y * p ∈ K := K.mul_mem hyK (hPK hp)
    have := (Subgroup.mem_normalizer_iff.1 (hKN hyp) _).1 hc'
    have e2 : y * p * ((y * p)⁻¹ * ⁅p, y⁆⁻¹ * (y * p)) * (y * p)⁻¹ = ⁅p, y⁆⁻¹ := by group
    rw [e2] at this
    simpa using N.inv_mem this

omit [Finite G] in
theorem le_centralizer_of_commutator_le {M Y L : Subgroup G} (hYM : Y ≤ M) (hLM : L ≤ M)
    (hY : M ≤ Subgroup.normalizer (Y : Set G)) (hL : M ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hYL : ⁅Y, L⁆ ≤ Subgroup.centralizer (L : Set G)) :
    Y ≤ Subgroup.centralizer (L : Set G) := by
  have h1 : ⁅⁅Y, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hYL
  have h2 := commutator_eq_commutator_commutator hYM hLM hY hL hperf
  rw [h1, Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
  exact h2

section Coord

variable {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)}

abbrev cXL (M L : Subgroup G) : Subgroup G := Xq M ⊓ Subgroup.centralizer (L : Set G)

omit [Finite G] in
theorem commute_of_mem_Xq {x y : G} (hx : x ∈ Xq M) (hy : y ∈ Xq M) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hx).2 y
    (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hy).1).symm

omit [Finite G] in
theorem commute_of_mem_pCoreOf {x y : G} (hx : x ∈ Xq M) (hy : y ∈ pCoreOf 2 M) :
    y * x = x * y :=
  Subgroup.mem_centralizer_iff.1 (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hx).2 y hy

omit [Finite G] [Fintype F] in
theorem NatVec.vec_mul (nv : NatVec M T L a) (u v : ↥(Uq M T L)) :
    nv.vec (u * v) = nv.vec u + nv.vec v := by
  simp [NatVec.vec, map_mul, toAdd_mul]

omit [Finite G] [Fintype F] in
theorem NatVec.vec_inv (nv : NatVec M T L a) (u : ↥(Uq M T L)) : nv.vec u⁻¹ = -nv.vec u := by
  simp [NatVec.vec, map_inv, toAdd_inv]

omit [Finite G] [Fintype F] in
theorem NatVec.vec_eq_zero_iff (nv : NatVec M T L a) (u : ↥(Uq M T L)) :
    nv.vec u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [NatVec.vec, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, nv.ker_iff]
  exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩

omit [Finite G] [Fintype F] in
theorem NatVec.vec_one (nv : NatVec M T L a) : nv.vec (1 : ↥(Uq M T L)) = 0 := by
  simp [NatVec.vec]

@[expose] def uCoord (nv : NatVec M T L a) (n : G) : MSP.V4 F :=
  open Classical in
  if hn : ∃ u ∈ Uq M T L, ∃ c ∈ cXL M L, u * c = n then
    nv.vec ⟨Classical.choose hn, (Classical.choose_spec hn).1⟩ else 0

omit [Finite G] [Fintype F] in
theorem uCoord_mul (nv : NatVec M T L a) {u c : G} (hu : u ∈ Uq M T L) (hc : c ∈ cXL M L) :
    uCoord nv (u * c) = nv.vec ⟨u, hu⟩ := by
  unfold uCoord
  split
  · rename_i hn
    obtain ⟨hu', c', hc', he⟩ := Classical.choose_spec hn
    have hmem : (Classical.choose hn)⁻¹ * u ∈ Subgroup.centralizer (L : Set G) := by
      have e : (Classical.choose hn)⁻¹ * u = c' * c⁻¹ := by
        calc (Classical.choose hn)⁻¹ * u = (Classical.choose hn)⁻¹ * (u * c) * c⁻¹ := by group
          _ = (Classical.choose hn)⁻¹ * (Classical.choose hn * c') * c⁻¹ := by rw [he]
          _ = c' * c⁻¹ := by group
      rw [e]
      exact (Subgroup.centralizer _).mul_mem hc'.2 ((Subgroup.centralizer _).inv_mem hc.2)
    have h0 : nv.vec ((⟨Classical.choose hn, hu'⟩ : ↥(Uq M T L))⁻¹ * ⟨u, hu⟩) = 0 :=
      (nv.vec_eq_zero_iff _).2 hmem
    rw [nv.vec_mul, nv.vec_inv] at h0
    exact neg_add_eq_zero.1 h0
  · rename_i hn
    exact absurd ⟨u, hu, c, hc, rfl⟩ hn

omit [Finite G] [Fintype F] in
theorem uCoord_one (nv : NatVec M T L a) : uCoord nv (1 : G) = 0 := by
  have := uCoord_mul nv (Uq M T L).one_mem (cXL M L).one_mem
  rw [one_mul] at this
  rw [this]
  exact nv.vec_one

end Coord

section Cocycle

variable {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)} (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)

include h in
theorem le_normalizer_cXL : M ≤ Subgroup.normalizer (cXL M L : Set G) :=
  le_normalizer_inf (le_normalizer_Xq M) (le_normalizer_centralizer h.le_normalizer)

omit [Finite G] in
theorem cXL_le : cXL M L ≤ Xq M := inf_le_left

include h in
theorem mem_Uq_sup_cXL {n : G} :
    n ∈ Uq M T L ⊔ cXL M L ↔ ∃ u ∈ Uq M T L, ∃ c ∈ cXL M L, u * c = n := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((Uq_le h.L_le).trans (le_normalizer_cXL h))]
  exact Set.mem_mul

omit [Finite G] in
theorem commutatorElement_mul_left' (m₁ m₂ x : G) :
    ⁅m₁ * m₂, x⁆ = m₁ * ⁅m₂, x⁆ * m₁⁻¹ * ⁅m₁, x⁆ := by
  simp only [commutatorElement_def]
  group

omit [Fintype F] in
include h in
theorem uCoord_comm_mul (nv : NatVec M T L a) {x : G}
    (hxM : ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L) {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M) :
    uCoord nv ⁅m₁ * m₂, x⁆ =
      uCoord nv ⁅m₁, x⁆ + MSP.mat (a ⟨m₁, hm₁⟩) *ᵥ uCoord nv ⁅m₂, x⁆ := by
  obtain ⟨u₁, hu₁, c₁, hc₁, e₁⟩ := (mem_Uq_sup_cXL h).1 (hxM m₁ hm₁)
  obtain ⟨u₂, hu₂, c₂, hc₂, e₂⟩ := (mem_Uq_sup_cXL h).1 (hxM m₂ hm₂)
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hu₂' : m₁ * u₂ * m₁⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hm₁) u₂).1 hu₂
  have hc₂' : m₁ * c₂ * m₁⁻¹ ∈ cXL M L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_cXL h hm₁) c₂).1 hc₂
  have hcomm : m₁ * c₂ * m₁⁻¹ * u₁ = u₁ * (m₁ * c₂ * m₁⁻¹) :=
    commute_of_mem_Xq (cXL_le hc₂') (h.Uq_le_Xq hu₁)
  have e : ⁅m₁ * m₂, x⁆ = (m₁ * u₂ * m₁⁻¹ * u₁) * (m₁ * c₂ * m₁⁻¹ * c₁) := by
    rw [commutatorElement_mul_left', ← e₁, ← e₂]
    calc m₁ * (u₂ * c₂) * m₁⁻¹ * (u₁ * c₁) =
        m₁ * u₂ * m₁⁻¹ * (m₁ * c₂ * m₁⁻¹ * u₁) * c₁ := by group
      _ = m₁ * u₂ * m₁⁻¹ * (u₁ * (m₁ * c₂ * m₁⁻¹)) * c₁ := by rw [hcomm]
      _ = _ := by group
  rw [e, uCoord_mul nv ((Uq M T L).mul_mem hu₂' hu₁) ((cXL M L).mul_mem hc₂' hc₁), ← e₁, ← e₂,
    uCoord_mul nv hu₁ hc₁, uCoord_mul nv hu₂ hc₂]
  have e3 : (⟨m₁ * u₂ * m₁⁻¹ * u₁, (Uq M T L).mul_mem hu₂' hu₁⟩ : ↥(Uq M T L)) =
      ⟨m₁ * u₂ * m₁⁻¹, hu₂'⟩ * ⟨u₁, hu₁⟩ := rfl
  rw [e3, nv.vec_mul, add_comm]
  congr 1
  have := nv.vec_conj ⟨m₁, hm₁⟩ ⟨u₂, hu₂⟩ hu₂'
  exact this

include hd h in
theorem eq_zero_of_fixed_aL (nv : NatVec M T L a) {w : MSP.V4 F}
    (hw : ∀ l (hl : l ∈ L), MSP.mat (a ⟨l, h.L_le hl⟩) *ᵥ w = w) : w = 0 := by
  have hlift := (sp4Lift G M T L h k F _ _ a hd).2.2
  obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd w)
  have hw' : nv.vec u = w := by rw [NatVec.vec, hu]; rfl
  rw [← hw', nv.vec_eq_zero_iff, Subgroup.mem_centralizer_iff]
  intro l hl
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hlu : l * u * l⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn (h.L_le hl)) u).1 u.2
  have h1 := nv.vec_conj ⟨l, h.L_le hl⟩ u hlu
  rw [hw', hw l hl, ← hw'] at h1
  have h2 : nv.vec (⟨l * u * l⁻¹, hlu⟩ * u⁻¹) = 0 := by
    rw [nv.vec_mul, nv.vec_inv, h1, add_neg_cancel]
  have h3 := (nv.vec_eq_zero_iff _).1 h2
  have h4 := hlift l (h.L_le hl) u u.2 h3
  calc l * (u : G) = l * u * l⁻¹ * l := by group
    _ = u * l := by rw [h4]

include hd h in
theorem uCoord_comm_kerG (nv : NatVec M T L a) {x : G} (hx : x ∈ Xq M)
    (hxM : ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L)
    {κ : G} (hκ : κ ∈ kerG a) : uCoord nv ⁅κ, x⁆ = 0 := by
  obtain ⟨hκM, hκ1⟩ := (mem_kerG a).1 hκ
  have hcomm : ⁅kerG a, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (kerG_le a) (le_normalizer_kerG a) (hd.not_le_kerG h)
  refine eq_zero_of_fixed_aL hd h nv fun l hl => ?_
  have hlM := h.L_le hl
  set n := ⁅l, κ⁆ with hn
  have hnQ : n ∈ pCoreOf 2 M := by
    have := hcomm (Subgroup.commutator_mem_commutator hκ hl)
    rw [hn, ← commutatorElement_inv]
    exact (pCoreOf 2 M).inv_mem this
  have hnM : n ∈ M := pCoreOf_le' M hnQ
  have hna : a ⟨n, hnM⟩ = 1 := ((mem_kerG a).1 (hd.pCoreOf_le_kerG h hnQ)).2
  have hn0 : uCoord nv ⁅n, x⁆ = 0 := by
    have : ⁅n, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact commute_of_mem_pCoreOf hx hnQ
    rw [this, uCoord_one]
  have e : l * κ = n * (κ * l) := by
    rw [hn]
    simp only [commutatorElement_def]
    group
  have h1 := uCoord_comm_mul h nv hxM hlM hκM
  have h2 := uCoord_comm_mul h nv hxM hnM (M.mul_mem hκM hlM)
  have h3 := uCoord_comm_mul h nv hxM hκM hlM
  rw [← e, h1, hn0, zero_add, h3, hκ1, hna] at h2
  simp only [MSP.mat_one, Matrix.one_mulVec] at h2
  rw [add_comm (uCoord nv ⁅κ, x⁆)] at h2
  exact add_left_cancel h2

end Cocycle

section SpCocycle

variable {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def preA (hd : IsSp4Data M T L k F a) (g : MSP.Sp4 F) : ↥M :=
  Classical.choose (hd.surj g)

omit [Finite G] in
theorem a_preA (hd : IsSp4Data M T L k F a) (g : MSP.Sp4 F) : a (preA hd g) = g :=
  Classical.choose_spec (hd.surj g)

@[expose] def cocSp (hd : IsSp4Data M T L k F a) (nv : NatVec M T L a) (x : G) (g : MSP.Sp4 F) :
    MSP.V4 F :=
  uCoord nv ⁅((preA hd g : ↥M) : G), x⁆

theorem cocSp_a (hd : IsSp4Data M T L k F a) (h : PUHyp M T L) (nv : NatVec M T L a) {x : G}
    (hx : x ∈ Xq M) (hxM : ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L) {m : G} (hm : m ∈ M) :
    cocSp hd nv x (a ⟨m, hm⟩) = uCoord nv ⁅m, x⁆ := by
  set p := preA hd (a ⟨m, hm⟩) with hp
  have hpa : a p = a ⟨m, hm⟩ := a_preA hd _
  have hκ : (p : G)⁻¹ * m ∈ kerG a := by
    refine (mem_kerG a).2 ⟨M.mul_mem (M.inv_mem p.2) hm, ?_⟩
    have e : (⟨(p : G)⁻¹ * m, M.mul_mem (M.inv_mem p.2) hm⟩ : ↥M) = p⁻¹ * ⟨m, hm⟩ := rfl
    rw [e, map_mul, map_inv, hpa, inv_mul_cancel]
  have h1 := uCoord_comm_mul h nv hxM p.2 (M.mul_mem (M.inv_mem p.2) hm)
  rw [mul_inv_cancel_left, uCoord_comm_kerG hd h nv hx hxM hκ, Matrix.mulVec_zero,
    add_zero] at h1
  rw [h1]
  rfl

theorem cocSp_mul (hd : IsSp4Data M T L k F a) (h : PUHyp M T L) (nv : NatVec M T L a) {x : G}
    (hx : x ∈ Xq M) (hxM : ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L) (g g' : MSP.Sp4 F) :
    cocSp hd nv x (g * g') = cocSp hd nv x g + MSP.mat g *ᵥ cocSp hd nv x g' := by
  set p := preA hd g
  set p' := preA hd g'
  have e : g * g' = a ⟨(p : G) * p', M.mul_mem p.2 p'.2⟩ := by
    have : (⟨(p : G) * p', M.mul_mem p.2 p'.2⟩ : ↥M) = p * p' := rfl
    rw [this, map_mul, a_preA, a_preA]
  rw [e, cocSp_a hd h nv hx hxM, uCoord_comm_mul h nv hxM p.2 p'.2]
  have hp : a ⟨(p : G), p.2⟩ = g := a_preA hd g
  rw [hp]
  rfl

end SpCocycle

section Conj

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

omit [Finite G] in
theorem cform_vanish_of_conj {φ : MSP.Sp4 F → MSP.V4 F}
    (hφ : ∀ g g', φ (g * g') = φ g + MSP.mat g *ᵥ φ g') {B : F} {m₀ : MSP.V4 F}
    (hform : ∀ g, φ g = cform B m₀ g) {A : Subgroup (MSP.Sp4 F)} {g₀ : MSP.Sp4 F}
    (hA : ∀ j ∈ A.map (MulAut.conj g₀).toMonoidHom, φ j = 0) :
    ∀ j ∈ A, cform B (m₀ - MSP.mat g₀⁻¹ *ᵥ φ g₀) j = 0 := by
  intro j hj
  have h0 : φ (g₀ * j * g₀⁻¹) = 0 := hA _ ⟨j, hj, rfl⟩
  have h1 : φ 1 = 0 := by
    have := hφ 1 1
    rw [one_mul, MSP.mat_one, Matrix.one_mulVec] at this
    exact left_eq_add.mp this
  have hinv : φ g₀⁻¹ = -(MSP.mat g₀⁻¹ *ᵥ φ g₀) := by
    have := hφ g₀⁻¹ g₀
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have h2 := hφ (g₀ * j) g₀⁻¹
  rw [hφ g₀ j, h0, hinv] at h2
  have key : ∀ v, MSP.mat g₀⁻¹ *ᵥ (MSP.mat (g₀ * j) *ᵥ v) = MSP.mat j *ᵥ v := fun v => by
    rw [← MSP.mat_mul_mulVec, show g₀⁻¹ * (g₀ * j) = j by group]
  have key2 : ∀ v, MSP.mat g₀⁻¹ *ᵥ (MSP.mat g₀ *ᵥ v) = v := fun v => MSP.mat_inv_mulVec g₀ v
  have h4 := congrArg (MSP.mat g₀⁻¹ *ᵥ ·) h2
  simp only [Matrix.mulVec_zero, Matrix.mulVec_add, Matrix.mulVec_neg, key, key2] at h4
  set w := MSP.mat g₀⁻¹ *ᵥ φ g₀ with hw
  have h5 : w + φ j - MSP.mat j *ᵥ w = 0 := by
    rw [sub_eq_add_neg]
    exact h4.symm
  have h3 : φ j = MSP.mat j *ᵥ w - w := by
    rw [← sub_eq_zero]
    have e : φ j - (MSP.mat j *ᵥ w - w) = w + φ j - MSP.mat j *ᵥ w := by abel
    rw [e]
    exact h5
  have h6 : cform B m₀ j = MSP.mat j *ᵥ w - w := (hform j).symm.trans h3
  have e : cform B (m₀ - w) j = cform B m₀ j - (MSP.mat j *ᵥ w - w) := by
    unfold cform
    rw [Matrix.mulVec_sub]
    abel
  rw [e, h6, sub_self]

end Conj

section Main

variable {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem le_normalizer_of_commute {N Y : Subgroup G} (h : ∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) :
    N ≤ Subgroup.normalizer (Y : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h n hn y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h n hn _ hy
    have e1 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    have e2 : n⁻¹ * (n * y * n⁻¹) * n = n * y * n⁻¹ := by
      calc n⁻¹ * (n * y * n⁻¹) * n = n⁻¹ * ((n * y * n⁻¹) * n) := by group
        _ = n⁻¹ * (n * (n * y * n⁻¹)) := by rw [← h1]
        _ = n * y * n⁻¹ := by group
    rw [e1, e2]
    exact hy

omit [Fintype F] in
theorem le_normalizer_liftT (h : PUHyp M T L)
    {A₀ : Subgroup ↥(StatedSp 2 F)} (hA : candMax (imSp a T) = {A₀}) :
    T ≤ Subgroup.normalizer (liftT T a A₀ : Set G) := by
  have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ rfl
  have hinv : ∀ r ∈ imSp a T, A₀.map (MulAut.conj r).toMonoidHom = A₀ := fun r hr => by
    have := map_conj_mem_candMax hA₀ hr
    rw [hA] at this
    exact this
  have key : ∀ t ∈ T, ∀ e ∈ liftT T a A₀, t * e * t⁻¹ ∈ liftT T a A₀ := by
    intro t ht e he
    obtain ⟨heT, heM, heA⟩ := mem_liftT.1 he
    have htM := h.le ht
    refine mem_liftT.2 ⟨T.mul_mem (T.mul_mem ht heT) (T.inv_mem ht),
      M.mul_mem (M.mul_mem htM heM) (M.inv_mem htM), ?_⟩
    have e1 : (⟨t * e * t⁻¹, M.mul_mem (M.mul_mem htM heM) (M.inv_mem htM)⟩ : ↥M) =
        ⟨t, htM⟩ * ⟨e, heM⟩ * (⟨t, htM⟩ : ↥M)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    have hr : a ⟨t, htM⟩ ∈ imSp a T := ⟨⟨t, htM⟩, ht, rfl⟩
    rw [← hinv _ hr]
    exact ⟨_, heA, rfl⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨key t ht e, fun he => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ he
  simpa [mul_assoc] using this

omit [Finite G] [Fintype F] in
theorem v4_add_self [CharP F 2] (v : MSP.V4 F) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

theorem xq_inf_centralizer_jOffM_le (h51 : S51) (h32 : S32) (hd : IsSp4Data M T L k F a)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    Xq M ⊓ Subgroup.centralizer (jOffM M T L (2 ^ k) : Set G) ≤ Uq M T L ⊔ Dq M L := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have h54 := sp4_54M h51 hd h hmin hb
  have hXL : ⁅Xq M, L⁆ ≤ Uq M T L := (h32 G M T L h).2.1
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hNn : M ≤ Subgroup.normalizer ((Uq M T L ⊔ cXL M L : Subgroup G) : Set G) :=
    le_normalizer_sup hUn (le_normalizer_cXL h)
  have hTJ : T ≤ Subgroup.normalizer (jOffM M T L (2 ^ k) : Set G) := by
    rcases h54 with ⟨A₀, l, hA, -, -, -, -, hJA⟩ | ⟨p, -, -, hJT⟩
    · rw [hJA]
      exact le_normalizer_liftT h hA
    · rw [hJT]
      exact Subgroup.le_normalizer
  by_contra hcon
  have hCD : cXL M L ≤ Dq M L := inf_le_inf_right _ (Xq_le_pCoreOf M)
  have hY : ¬ Xq M ⊓ Subgroup.centralizer (jOffM M T L (2 ^ k) : Set G) ≤
      Uq M T L ⊔ cXL M L := fun hle => hcon (hle.trans (sup_le_sup_left hCD _))
  have hNX : Uq M T L ⊔ cXL M L ≤ Xq M := sup_le h.Uq_le_Xq cXL_le
  have hYX : Xq M ⊓ Subgroup.centralizer (jOffM M T L (2 ^ k) : Set G) ≤ Xq M := inf_le_left
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := h.isPGroup.to_le h.pCore_le
  obtain ⟨x, hxY, hxN, hxT⟩ := exists_fixed_mod_of_isPGroup h.isPGroup
    (hQ2.to_le ((sup_le hYX hNX).trans (Xq_le_pCoreOf M)))
    (le_normalizer_inf (h.le.trans (le_normalizer_Xq M)) (le_normalizer_centralizer hTJ))
    (h.le.trans hNn) ((hYX.trans (Xq_le M)).trans hNn)
    (le_normalizer_of_commute fun n hn y hy => commute_of_mem_Xq (hNX hn) (hYX hy)) hY
  have hxX : x ∈ Xq M := hxY.1
  have hxJ := hxY.2
  have hxM : ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L := by
    let S : Subgroup G :=
      { carrier := {m | m ∈ M ∧ ⁅m, x⁆ ∈ Uq M T L ⊔ cXL M L}
        mul_mem' := fun {m₁ m₂} h₁ h₂ => ⟨M.mul_mem h₁.1 h₂.1, by
          rw [commutatorElement_mul_left']
          exact (Uq M T L ⊔ cXL M L).mul_mem
            ((Subgroup.mem_normalizer_iff.1 (hNn h₁.1) _).1 h₂.2) h₁.2⟩
        one_mem' := ⟨M.one_mem, by
          rw [commutatorElement_one_left]
          exact (Uq M T L ⊔ cXL M L).one_mem⟩
        inv_mem' := fun {m} hm => ⟨M.inv_mem hm.1, by
          have e : ⁅m⁻¹, x⁆ = m⁻¹ * ⁅m, x⁆⁻¹ * m⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.1 (hNn (M.inv_mem hm.1)) _).1
            ((Uq M T L ⊔ cXL M L).inv_mem hm.2)⟩ }
    have hLS : L ≤ S := fun l hl => ⟨h.L_le hl, by
      have := hXL (Subgroup.commutator_mem_commutator hxX hl)
      rw [← commutatorElement_inv]
      exact Subgroup.mem_sup_left ((Uq M T L).inv_mem this)⟩
    have hTS : T ≤ S := fun t ht => ⟨h.le ht, hxT t ht⟩
    have hMS : M ≤ S := by
      rw [h.eq_sup]
      exact sup_le hLS hTS
    exact fun m hm => (hMS hm).2
  have hφ := cocSp_mul hd h nv hxX hxM
  obtain ⟨B, m₀, hBm⟩ := exists_eq_sqf hd.card_eq hd.one_le hφ
  have hform : ∀ g, cocSp hd nv x g = cform B m₀ g := hBm
  have hvan : ∀ g ∈ imSp a (jOffM M T L (2 ^ k)), cocSp hd nv x g = 0 := by
    rintro _ ⟨j, hj, rfl⟩
    have hjM := j.2
    have e : (j : ↥M) = ⟨(j : G), hjM⟩ := rfl
    rw [e, cocSp_a hd h nv hxX hxM]
    have : ⁅(j : G), x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 hxJ _ hj
    rw [this, uCoord_one]
  have hB : B = 0 := by
    rcases h54 with ⟨A₀, l, hA, hl, -, hA₀l, hA₀card, hJA⟩ | ⟨p, hp, hTp, hJT⟩
    · have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ rfl
      have himJ : imSp a (jOffM M T L (2 ^ k)) = A₀ := by rw [hJA]; exact imSp_liftT hA₀.1.1
      obtain ⟨g₀, rfl⟩ := MSP.exists_map_ln₀_eq hl
      rw [MSP.qLine_map_eq] at hA₀l
      set J₀ := A₀.map (MulAut.conj g₀⁻¹).toMonoidHom with hJ₀
      have hA₀eq : J₀.map (MulAut.conj g₀).toMonoidHom = A₀ := by
        rw [hJ₀, Subgroup.map_map]
        have : ((MulAut.conj g₀).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom) =
            MonoidHom.id _ := by
          refine MonoidHom.ext fun y => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
            MonoidHom.id_apply]
          group
        rw [this, Subgroup.map_id]
      have hJ₀Q : J₀ ≤ MSP.Q₁ F := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := hy
        have := hA₀l hz
        rw [MSP.mem_map_conj] at this
        simpa using this
      have hvan₀ := cform_vanish_of_conj hφ hform (A := J₀) (g₀ := g₀) (by
        rw [hA₀eq, ← himJ]
        exact hvan)
      by_contra hB0
      have hcJ : Nat.card J₀ = Nat.card A₀ :=
        Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective
      have hNF := hd.nat_card_eq
      rcases Nat.lt_or_ge 1 k with hk2 | hk1
      · have hle := card_le_of_cform_Q₁ hB0 (S := (J₀ : Set (MSP.Sp4 F))) hJ₀Q hvan₀
        have hc : Nat.card (J₀ : Set (MSP.Sp4 F)) = Nat.card J₀ := rfl
        rw [hc, hcJ, hNF] at hle
        rw [hNF] at hA₀card
        have h4 : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        have : (2 ^ k) ^ 2 ≤ 2 * 2 ^ k := hA₀card.trans hle
        nlinarith
      · have hk : k = 1 := le_antisymm hk1 hd.one_le
        subst hk
        have hF2 : Fintype.card F = 2 := by rw [hd.card_eq, pow_one]
        have h4 : 4 ≤ Nat.card J₀ := by
          rw [hcJ]
          rw [hNF] at hA₀card
          simpa using hA₀card
        obtain ⟨y₁, y₂, hy₁, hy₂, -, -, -, hJ₀eq⟩ :=
          eq_xPoint_sup_of_cform hF2 hB0 hJ₀Q hvan₀ h4
        refine jOffM_ne_xPoint_sup h51 hd h hmin hb
          (p₁ := (F ∙ y₁).map (Matrix.mulVecLin (MSP.mat g₀)))
          (p₂ := (F ∙ y₂).map (Matrix.mulVecLin (MSP.mat g₀))) ?_ ?_ ?_
        · have hp := MSP.isPoint_span hy₁
          unfold MSP.IsPoint at hp ⊢
          rw [← hp]
          exact (Submodule.equivMapOfInjective _ (MSP.mulVec_mat_injective g₀) _).finrank_eq.symm
        · have hp := MSP.isPoint_span hy₂
          unfold MSP.IsPoint at hp ⊢
          rw [← hp]
          exact (Submodule.equivMapOfInjective _ (MSP.mulVec_mat_injective g₀) _).finrank_eq.symm
        · rw [himJ, ← hA₀eq, hJ₀eq, Subgroup.map_sup, MSP.xPoint_map_conj, MSP.xPoint_map_conj]
    · have himJ : imSp a (jOffM M T L (2 ^ k)) = MSP.qPoint p := by rw [hJT, hTp]
      obtain ⟨g₀, rfl⟩ := MSP.exists_map_pt₀_eq hp
      rw [MSP.qPoint_map_eq] at himJ
      have hvan₀ := cform_vanish_of_conj hφ hform (A := MSP.Q₂ F) (g₀ := g₀) (by
        rw [← himJ]
        exact hvan)
      exact eq_zero_of_cform_Q₂ hvan₀
  obtain ⟨u₀, hu₀⟩ := nv.surj (Multiplicative.ofAdd m₀)
  have hvu₀ : nv.vec u₀ = m₀ := by rw [NatVec.vec, hu₀]; rfl
  set x' := x * (u₀ : G) with hx'
  have hx'X : x' ∈ Xq M := (Xq M).mul_mem hxX (h.Uq_le_Xq u₀.2)
  have hx'C : ∀ m ∈ M, ⁅m, x'⁆ ∈ cXL M L := by
    intro m hm
    obtain ⟨u, hu, c, hc, e⟩ := (mem_Uq_sup_cXL h).1 (hxM m hm)
    have hmu₀ : m * u₀ * m⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hm) u₀).1 u₀.2
    have hcomm1 : ⁅m, (u₀ : G)⁆ = m * u₀ * m⁻¹ * (u₀ : G)⁻¹ := commutatorElement_def _ _
    have hU1 : ⁅m, (u₀ : G)⁆ ∈ Uq M T L := by
      rw [hcomm1]
      exact (Uq M T L).mul_mem hmu₀ ((Uq M T L).inv_mem u₀.2)
    have e1 : ⁅m, x'⁆ = (u * ⁅m, (u₀ : G)⁆) * c := by
      have e2 : ⁅m, x * (u₀ : G)⁆ = ⁅m, x⁆ * (x * ⁅m, (u₀ : G)⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hc1 : x * ⁅m, (u₀ : G)⁆ * x⁻¹ = ⁅m, (u₀ : G)⁆ := by
        rw [commute_of_mem_Xq hxX (h.Uq_le_Xq hU1), mul_inv_cancel_right]
      have hc2 : c * ⁅m, (u₀ : G)⁆ = ⁅m, (u₀ : G)⁆ * c :=
        commute_of_mem_Xq (cXL_le hc) (h.Uq_le_Xq hU1)
      rw [hx', e2, hc1, ← e]
      calc u * c * ⁅m, (u₀ : G)⁆ = u * (c * ⁅m, (u₀ : G)⁆) := by group
        _ = u * (⁅m, (u₀ : G)⁆ * c) := by rw [hc2]
        _ = _ := by group
    have huc : uCoord nv ⁅m, x⁆ = MSP.mat (a ⟨m, hm⟩) *ᵥ m₀ - m₀ := by
      rw [← cocSp_a hd h nv hxX hxM hm, hform]
      simp [cform, hB]
    have hv : nv.vec ⟨u * ⁅m, (u₀ : G)⁆, (Uq M T L).mul_mem hu hU1⟩ = 0 := by
      have e3 : (⟨u * ⁅m, (u₀ : G)⁆, (Uq M T L).mul_mem hu hU1⟩ : ↥(Uq M T L)) =
          ⟨u, hu⟩ * (⟨m * u₀ * m⁻¹, hmu₀⟩ * u₀⁻¹) := by
        apply Subtype.ext
        show u * ⁅m, (u₀ : G)⁆ = u * (m * u₀ * m⁻¹ * (u₀ : G)⁻¹)
        rw [hcomm1]
      rw [e3, nv.vec_mul, nv.vec_mul, nv.vec_inv, nv.vec_conj ⟨m, hm⟩ u₀ hmu₀, hvu₀]
      rw [← e, uCoord_mul nv hu hc] at huc
      rw [huc]
      rw [show MSP.mat (a ⟨m, hm⟩) *ᵥ m₀ - m₀ + (MSP.mat (a ⟨m, hm⟩) *ᵥ m₀ + -m₀) =
          (MSP.mat (a ⟨m, hm⟩) *ᵥ m₀ - m₀) + (MSP.mat (a ⟨m, hm⟩) *ᵥ m₀ - m₀) by abel]
      exact v4_add_self _
    have hCL := (nv.vec_eq_zero_iff _).1 hv
    rw [e1]
    exact (cXL M L).mul_mem ⟨h.Uq_le_Xq ((Uq M T L).mul_mem hu hU1), hCL⟩ hc
  let Y : Subgroup G :=
    { carrier := {y | y ∈ Xq M ∧ ∀ m ∈ M, ⁅m, y⁆ ∈ cXL M L}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨(Xq M).mul_mem h₁.1 h₂.1, fun m hm => by
        have e : ⁅m, y₁ * y₂⁆ = ⁅m, y₁⁆ * (y₁ * ⁅m, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hX2 := cXL_le (h₂.2 m hm)
        rw [commute_of_mem_Xq h₁.1 hX2, mul_inv_cancel_right]
        exact (cXL M L).mul_mem (h₁.2 m hm) (h₂.2 m hm)⟩
      one_mem' := ⟨(Xq M).one_mem, fun m _ => by
        rw [commutatorElement_one_right]
        exact (cXL M L).one_mem⟩
      inv_mem' := fun {y} hy => ⟨(Xq M).inv_mem hy.1, fun m hm => by
        have e : ⁅m, y⁻¹⁆ = y⁻¹ * ⁅m, y⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hX1 := cXL_le ((cXL M L).inv_mem (hy.2 m hm))
        rw [commute_of_mem_Xq ((Xq M).inv_mem hy.1) hX1, inv_mul_cancel_right]
        exact (cXL M L).inv_mem (hy.2 m hm)⟩ }
  have hYM : Y ≤ M := fun y hy => Xq_le M hy.1
  have hYn : M ≤ Subgroup.normalizer (Y : Set G) := by
    have key : ∀ g ∈ M, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
      intro g hg y hy
      refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_Xq M hg) y).1 hy.1, fun m hm => ?_⟩
      have e : ⁅m, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * m * g, y⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_cXL h hg) _).1
        (hy.2 _ (M.mul_mem (M.mul_mem (M.inv_mem hg) hm) hg))
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (M.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hYL : ⁅Y, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy l hl
    rw [← commutatorElement_inv]
    exact (Subgroup.centralizer _).inv_mem (hy.2 l (h.L_le hl)).2
  have hYC := le_centralizer_of_commutator_le hYM h.L_le hYn h.le_normalizer h.perfect hYL
  have hx'L : x' ∈ Subgroup.centralizer (L : Set G) := hYC ⟨hx'X, hx'C⟩
  apply hxN
  have e : x = (u₀ : G)⁻¹ * x' := by
    rw [hx', commute_of_mem_Xq hxX (h.Uq_le_Xq u₀.2)]
    group
  rw [e]
  exact Subgroup.mul_mem_sup ((Uq M T L).inv_mem u₀.2) ⟨hx'X, hx'L⟩

end Main

end S5

open S5 in
theorem s53_of (h51 : S51) (h32 : S32) : S53 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd
  have hJM : jOffM M T L (2 ^ k) ≤ M := iSup₂_le fun E hE => (offSetM_le _ hE).trans h.le
  have hDM : Dq M L ≤ M := inf_le_left.trans (pCoreOf_le' M)
  rw [xm_baseA_eq h, jOff_baseA h, uSub_baseA h, dSub_baseA h,
    ← imM_inf_centralizer h.le (Xq M) hJM, ← imM_sup_of_le h (Uq_le h.L_le) hDM]
  exact imM_mono h.le (xq_inf_centralizer_jOffM_le h51 h32 hd h hmin hb)

end CFSG.Quasithin.MS93

