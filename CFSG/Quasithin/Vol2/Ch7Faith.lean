module

public import CFSG.Quasithin.Vol2.Ch10SecDGroup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

theorem commutatorElement_mul_of_mem_center {Q : Type*} [Group Q] {z w a b : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hz hw
  simp only [commutatorElement_def, mul_inv_rev]
  calc z * a * (w * b) * (a⁻¹ * z⁻¹) * (b⁻¹ * w⁻¹)
      = z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) := by rw [← hz (a * w * b * a⁻¹)]; group
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [hw a]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hw (a * b * a⁻¹ * b⁻¹)]; group

theorem normal_le_center_or_eq_top_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ Subgroup.center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hnq, inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = (n₁⁻¹ * x) * n₁ := by
      have := (Subgroup.mem_center_iff.mp hz₁) n₁
      calc x = n₁ * (n₁⁻¹ * x) := by group
        _ = (n₁⁻¹ * x) * n₁ := this
    have hy : y = (n₂⁻¹ * y) * n₂ := by
      have := (Subgroup.mem_center_iff.mp hz₂) n₂
      calc y = n₂ * (n₂⁻¹ * y) := by group
        _ = (n₂⁻¹ * y) * n₂ := this
    rw [hx, hy, commutatorElement_mul_of_mem_center hz₁ hz₂, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

variable {G : Type} [Group G]

theorem commutatorElement_mem_of_perfect {L N : Subgroup G} {b : G} (hNL : N ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hZ : ∀ l ∈ L, ∀ m ∈ L, ⁅⁅b, l⁆, m⁆ ∈ N) : ∀ l ∈ L, ⁅b, l⁆ ∈ N := by
  have hbl : ∀ l ∈ L, ⁅b, l⁆ ∈ L := fun l hl => by
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hbL l).mp hl) (L.inv_mem hl)
  have : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set π := QuotientGroup.mk' (N.subgroupOf L) with hπ
  have hπ1 : ∀ x : L, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcen : ∀ l (hl : l ∈ L), π ⟨⁅b, l⁆, hbl l hl⟩ ∈ Subgroup.center (↥L ⧸ N.subgroupOf L) := by
    intro l hl
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) q
    have h1 : π (⁅(⟨⁅b, l⁆, hbl l hl⟩ : L), m⁆) = 1 :=
      (hπ1 _).mpr (hZ l hl m m.2)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  let S : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ⁅b, l⁆ ∈ N}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨L.mul_mem hx.1 hy.1, ?_⟩
        have e : ⁅b, x * y⁆ = ⁅b, x⁆ * (x * ⁅b, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem hx.2 ((Subgroup.mem_normalizer_iff.mp (hLN hx.1) _).mp hy.2)
      one_mem' := ⟨L.one_mem, by rw [commutatorElement_one_right]; exact N.one_mem⟩
      inv_mem' := fun {x} hx => by
        refine ⟨L.inv_mem hx.1, ?_⟩
        have e : ⁅b, x⁻¹⁆ = x⁻¹ * ⁅b, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem hx.1)) _).mp (N.inv_mem hx.2) }
  have hcomm : ∀ x ∈ L, ∀ y ∈ L, ⁅x, y⁆ ∈ S := by
    intro x hx y hy
    refine ⟨Subgroup.commutator_mem_commutator hx hy |> hperf.le, ?_⟩
    have hxy : ⁅x, y⁆ ∈ L := L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
    have e : ⁅b, ⁅x, y⁆⁆ = ⁅⁅b, x⁆ * x, ⁅b, y⁆ * y⁆ * ⁅x, y⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    have hmem : ⁅b, ⁅x, y⁆⁆ ∈ L := hbl _ hxy
    have hval : (⟨⁅b, ⁅x, y⁆⁆, hmem⟩ : L) =
        ⁅(⟨⁅b, x⁆, hbl x hx⟩ : L) * ⟨x, hx⟩, (⟨⁅b, y⁆, hbl y hy⟩ : L) * ⟨y, hy⟩⁆ *
          ⁅(⟨x, hx⟩ : L), ⟨y, hy⟩⁆⁻¹ :=
      Subtype.ext (by show ⁅b, ⁅x, y⁆⁆ = _; rw [e]; rfl)
    refine (hπ1 ⟨_, hmem⟩).mp ?_
    rw [hval, map_mul, map_inv, map_commutatorElement, map_commutatorElement, map_mul, map_mul,
      commutatorElement_mul_of_mem_center (hcen x hx) (hcen y hy), mul_inv_cancel]
  intro l hl
  have hLS : L ≤ S := by
    rw [← hperf]
    exact Subgroup.commutator_le.mpr hcomm
  exact (hLS hl).2

theorem commutatorElement_mem_pCoreOf {L V : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hLC : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ m ∈ L, ⁅x, m⁆ ∈ pCoreOf 2 L := by
  set K := (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L with hK
  have hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (Vol2.Ch10.SecD.le_normalizer_inf_centralizer hLN)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hKbar : (K.map π).Normal := Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective _)
  have hcore : ∀ y : L, y ∈ CFSG.pCore 2 ↥L → (y : G) ∈ pCoreOf 2 L := fun y hy => by
    refine ⟨y, ?_, rfl⟩
    exact hy
  rcases normal_le_center_or_eq_top_of_quasisimple hq (K.map π) with h | h
  · intro x hx m hm
    have hxK : (⟨x, hx.1⟩ : L) ∈ K := Subgroup.mem_subgroupOf.mpr hx
    have hc := h ⟨⟨x, hx.1⟩, hxK, rfl⟩
    have h1 : π ⁅(⟨x, hx.1⟩ : L), ⟨m, hm⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_center_iff.mp hc) (π ⟨m, hm⟩)).symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hcore _ h1
  · exfalso
    apply hLC
    intro l hl
    have h1 : π ⟨l, hl⟩ ∈ K.map π := h ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := h1
    have h2 : k⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
      exact hkl
    have h3 : ((k⁻¹ * ⟨l, hl⟩ : L) : G) ∈ Subgroup.centralizer (V : Set G) := hO2 (hcore _ h2)
    have hkC : (k : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_subgroupOf.mp hk).2
    have e : l = (k : G) * ((k⁻¹ * ⟨l, hl⟩ : L) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ hkC h3

theorem commutatorElement_mem_pCoreOf_of_centralizer {L V : Subgroup G} {b : G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hperf : ⁅L, L⁆ = L)
    (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hLC : ¬ L ≤ Subgroup.centralizer (V : Set G)) (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hb : ∀ l ∈ L, ⁅b, l⁆ ∈ Subgroup.centralizer (V : Set G)) :
    ∀ l ∈ L, ⁅b, l⁆ ∈ pCoreOf 2 L := by
  have hbl : ∀ l ∈ L, ⁅b, l⁆ ∈ L := fun l hl => by
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hbL l).mp hl) (L.inv_mem hl)
  refine commutatorElement_mem_of_perfect (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hbL hperf fun l hl m hm => ?_
  exact commutatorElement_mem_pCoreOf hq hLN hO2 hLC _ ⟨hbl l hl, hb l hl⟩ m hm

end CFSG.Quasithin.H13
