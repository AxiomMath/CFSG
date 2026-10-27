module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

section Components

variable {G : Type*} [Group G] [Finite G]

theorem isComponent_subgroupOf_of_mem_cComp_of_isQuasisimple {M K : Subgroup G}
    (hK : K ∈ cComp M) (hq : CFSG.IsQuasisimple ↥K) : CFSG.IsComponent (K.subgroupOf M) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hK)).symm hq,
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hK))⟩

theorem cComp_eq_or_commutator_eq_bot_of_isQuasisimple {M K K' : Subgroup G}
    (hK : K ∈ cComp M) (hK' : K' ∈ cComp M) (hq : CFSG.IsQuasisimple ↥K)
    (hq' : CFSG.IsQuasisimple ↥K') : K = K' ∨ ⁅K, K'⁆ = ⊥ := by
  have hKM : K ≤ M := le_of_mem_cComp hK
  have hK'M : K' ≤ M := le_of_mem_cComp hK'
  rcases CFSG.LocalCores.distinct_components_commute
      (isComponent_subgroupOf_of_mem_cComp_of_isQuasisimple hK hq)
      (isComponent_subgroupOf_of_mem_cComp_of_isQuasisimple hK' hq') with h | h
  · left
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hKM, Subgroup.map_subgroupOf_eq_of_le hK'M] at this
  · right
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKM,
      Subgroup.map_subgroupOf_eq_of_le hK'M, Subgroup.map_bot] at this

theorem commute_of_mem_pCoreOf_of_mem_cComp {M K : Subgroup G} (hK : K ∈ cComp M)
    (hq : CFSG.IsQuasisimple ↥K) {g : G} (hg : g ∈ pCoreOf 2 M) {k : G} (hk : k ∈ K) :
    g * k = k * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ M := le_of_mem_cComp hK
  have hgM : g ∈ M := pCoreOf_le 2 M hg
  have hc := isComponent_subgroupOf_of_mem_cComp_of_isQuasisimple hK hq
  have hN : ((pCoreOf 2 M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 M)).mpr
      (le_normalizer_pCoreOf 2 M)
  rcases CFSG.LocalCores.component_subnormal_subgroup hc hN.isSubnormal with h | h
  · exfalso
    have h2 : IsPGroup 2 ↥(K.subgroupOf M) :=
      ((pCoreOf_isPGroup 2 M).of_equiv
        (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 M)).symm).to_le h
    have hK2 : IsPGroup 2 ↥K := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hKM)
    have : Group.IsNilpotent ↥K := hK2.isNilpotent
    exact not_isSolvable_of_mem_cComp hK inferInstance
  · have hmem : ⁅(⟨k, hKM hk⟩ : ↥M), (⟨g, hgM⟩ : ↥M)⁆ ∈
        ⁅K.subgroupOf M, (pCoreOf 2 M).subgroupOf M⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hk)
        (Subgroup.mem_subgroupOf.mpr hg)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm

end Components

section Module

variable {W : Type} [CommGroup W]

theorem le_centSub_of_conj {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLq : CFSG.IsQuasisimple ↥L) (hLU : L ≤ stabSub U) {a : MulAut W} (haU : a ∈ centSub U)
    (haL : a ∉ Subgroup.centralizer (L : Set (MulAut W)))
    (hdich : L.map (MulAut.conj a).toMonoidHom = L ∨ ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥) :
    L ≤ centSub U := by
  have haU' : ∀ u ∈ U, a⁻¹ u = u := fun u hu => by
    have := haU u hu
    calc a⁻¹ u = a⁻¹ (a u) := by rw [this]
      _ = u := by simp
  have key : ∀ l ∈ L, ∀ u ∈ U, (a * l * a⁻¹) u = l u := by
    intro l hl u hu
    have hlu : l u ∈ U := (hLU hl u).mpr hu
    simp only [MulAut.mul_apply]
    rw [haU' u hu, haU _ hlu]
  set K : Subgroup ↥L := (centSub U).subgroupOf L with hKdef
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hKdef, Subgroup.mem_subgroupOf, mem_centSub] at hk ⊢
    intro u hu
    have hgu : (g : MulAut W)⁻¹ u ∈ U := (hLU (L.inv_mem g.2) u).mpr hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
    rw [hk _ hgu]
    simp
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hKn with hK | hK
  · intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ K := by rw [hK]; trivial
    exact this
  · exfalso
    have hcen : ∀ c ∈ L, (∀ u ∈ U, c u = u) → ∀ x ∈ L, c * x = x * c := by
      intro c hc hcU x hx
      have hcK : (⟨c, hc⟩ : ↥L) ∈ K := hcU
      have := Subgroup.mem_center_iff.mp (hK hcK) ⟨x, hx⟩
      exact (congrArg Subtype.val this).symm
    have hLperf : ⁅L, L⁆ = L := by
      have h1 := hLq.1
      rw [Group.isPerfect_def, _root_.commutator_def] at h1
      have h2 := congrArg (Subgroup.map L.subtype) h1
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rcases hdich with hLa | hcomm
    ·
      have hconj : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl => by
        rw [← hLa]; exact ⟨l, hl, rfl⟩
      have hz : ∀ l ∈ L, ∀ x ∈ L, (l⁻¹ * (a * l * a⁻¹)) * x = x * (l⁻¹ * (a * l * a⁻¹)) := by
        intro l hl x hx
        refine hcen _ (L.mul_mem (L.inv_mem hl) (hconj l hl)) (fun u hu => ?_) x hx
        simp only [MulAut.mul_apply, MulAut.inv_apply] at key ⊢
        have h1 := key l hl u hu
        rw [h1]
        simp
      apply haL
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hLperf] at hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨p, hp, q, hq, rfl⟩ := hy
        set z := p⁻¹ * (a * p * a⁻¹) with hzdef
        set w := q⁻¹ * (a * q * a⁻¹) with hwdef
        have hap : a * p * a⁻¹ = p * z := by rw [hzdef]; group
        have haq : a * q * a⁻¹ = q * w := by rw [hwdef]; group
        have hzc := hz p hp
        have hwc := hz q hq
        have e : a * ⁅p, q⁆ * a⁻¹ = ⁅a * p * a⁻¹, a * q * a⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        have e2 : ⁅p * z, q * w⁆ = ⁅p, q⁆ := by
          have hzp : z * p = p * z := hzc p hp
          have hzq : z * q = q * z := hzc q hq
          have hwp : w * p = p * w := hwc p hp
          have hwq : w * q = q * w := hwc q hq
          have hzw : z * w = w * z := hzc w (L.mul_mem (L.inv_mem hq) (hconj q hq))
          simp only [commutatorElement_def, mul_inv_rev]
          calc p * z * (q * w) * (z⁻¹ * p⁻¹) * (w⁻¹ * q⁻¹)
              = p * q * p⁻¹ * q⁻¹ * (z * w * z⁻¹ * w⁻¹) := by
                have hzi : z⁻¹ * p⁻¹ = p⁻¹ * z⁻¹ := by
                  rw [← mul_inv_rev, ← mul_inv_rev, hzp]
                have hwi : w⁻¹ * q⁻¹ = q⁻¹ * w⁻¹ := by
                  rw [← mul_inv_rev, ← mul_inv_rev, hwq]
                have hzq' : z * q⁻¹ = q⁻¹ * z := by
                  calc z * q⁻¹ = q⁻¹ * (q * z) * q⁻¹ := by group
                    _ = q⁻¹ * (z * q) * q⁻¹ := by rw [hzq]
                    _ = q⁻¹ * z := by group
                have hwp' : w * p⁻¹ = p⁻¹ * w := by
                  calc w * p⁻¹ = p⁻¹ * (p * w) * p⁻¹ := by group
                    _ = p⁻¹ * (w * p) * p⁻¹ := by rw [hwp]
                    _ = p⁻¹ * w := by group
                have hzi' : z⁻¹ * q = q * z⁻¹ := by
                  calc z⁻¹ * q = z⁻¹ * (q * z) * z⁻¹ := by group
                    _ = z⁻¹ * (z * q) * z⁻¹ := by rw [hzq]
                    _ = q * z⁻¹ := by group
                have hwi' : w⁻¹ * p⁻¹ = p⁻¹ * w⁻¹ := by
                  rw [← mul_inv_rev, ← mul_inv_rev, hwp]
                calc p * z * (q * w) * (z⁻¹ * p⁻¹) * (w⁻¹ * q⁻¹)
                    = p * (z * q) * w * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by group
                  _ = p * (q * z) * w * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by rw [hzq]
                  _ = p * q * (z * w * z⁻¹) * (p⁻¹ * w⁻¹) * q⁻¹ := by group
                  _ = p * q * (z * w * z⁻¹) * (w⁻¹ * p⁻¹) * q⁻¹ := by rw [hwi']
                  _ = p * q * (z * w * z⁻¹ * w⁻¹) * (p⁻¹ * q⁻¹) := by group
                  _ = p * q * (p⁻¹ * q⁻¹) * (z * w * z⁻¹ * w⁻¹) := by
                    have hc4 : (z * w * z⁻¹ * w⁻¹) = 1 := by rw [hzw]; group
                    rw [hc4]; group
                  _ = p * q * p⁻¹ * q⁻¹ * (z * w * z⁻¹ * w⁻¹) := by group
            _ = p * q * p⁻¹ * q⁻¹ := by
                have hc4 : (z * w * z⁻¹ * w⁻¹) = 1 := by rw [hzw]; group
                rw [hc4, mul_one]
        have : a * ⁅p, q⁆ * a⁻¹ = ⁅p, q⁆ := by rw [e, hap, haq, e2]
        calc ⁅p, q⁆ * a = (a * ⁅p, q⁆ * a⁻¹) * a := by rw [this]
          _ = a * ⁅p, q⁆ := by group
      | one => simp
      | mul x y _ _ hx hy =>
        calc x * y * a = x * (y * a) := by group
          _ = x * (a * y) := by rw [hy]
          _ = (x * a) * y := by group
          _ = (a * x) * y := by rw [hx]
          _ = a * (x * y) := by group
      | inv x _ hx =>
        calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * a) * x⁻¹ := by rw [hx]
          _ = a * x⁻¹ := by group
    ·
      have hcommLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a⁻¹) = (a * y * a⁻¹) * x := by
        intro x hx y hy
        have hmem : ⁅x, a * y * a⁻¹⁆ ∈ ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator hx ⟨y, hy, rfl⟩
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      have habel : ∀ x ∈ L, ∀ y ∈ L, ∀ u ∈ U, x (y u) = y (x u) := by
        intro x hx y hy u hu
        have hxu : x u ∈ U := (hLU hx u).mpr hu
        have h1 : x (y u) = x ((a * y * a⁻¹) u) := by rw [key y hy u hu]
        have h2 : x ((a * y * a⁻¹) u) = (a * y * a⁻¹) (x u) := by
          have := congrArg (fun f : MulAut W => f u) (hcommLa x hx y hy)
          simpa only [MulAut.mul_apply] using this
        rw [h1, h2, key y hy _ hxu]
      have hcomm_ker : ∀ x ∈ L, ∀ y ∈ L, ∀ u ∈ U, ⁅x, y⁆ u = u := by
        intro x hx y hy u hu
        have hyu : y⁻¹ u ∈ U := (hLU (L.inv_mem hy) u).mpr hu
        have hxu : x⁻¹ (y⁻¹ u) ∈ U := (hLU (L.inv_mem hx) _).mpr hyu
        simp only [commutatorElement_def, MulAut.mul_apply]
        rw [habel x hx y hy _ hxu]
        simp
      obtain ⟨q₁, q₂, hq⟩ := hLq.2.2
      apply hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₂
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have he : (((x * y)⁻¹ * (y * x) : ↥L) : MulAut W) =
          ⁅(y : MulAut W)⁻¹, (x : MulAut W)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
        group
      have hcL : ⁅(y : MulAut W)⁻¹, (x : MulAut W)⁻¹⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem y.2) (L.inv_mem x.2))
          (L.inv_mem (L.inv_mem y.2))) (L.inv_mem (L.inv_mem x.2))
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have he' : ((g * ((x * y)⁻¹ * (y * x)) : ↥L) : MulAut W) =
          (g : MulAut W) * ⁅(y : MulAut W)⁻¹, (x : MulAut W)⁻¹⁆ := by
        rw [Subgroup.coe_mul, he]
      have he'' : (((x * y)⁻¹ * (y * x) * g : ↥L) : MulAut W) =
          ⁅(y : MulAut W)⁻¹, (x : MulAut W)⁻¹⁆ * g := by
        rw [Subgroup.coe_mul, he]
      rw [he', he'']
      exact (hcen _ hcL (hcomm_ker _ (L.inv_mem y.2) _ (L.inv_mem x.2)) (g : MulAut W) g.2).symm

end Module

end CFSG.Quasithin.H13
