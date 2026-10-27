module

public import CFSG.Quasithin.Vol2.Ch1Sec3A5Inner

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)

section Map

variable {X Y : Type} [Group X] [Group Y]

@[expose] noncomputable def modO2MapEquiv (e : X ≃* Y) (B : Subgroup X) :
    ModO2 (B.map e.toMonoidHom) ≃* ModO2 B :=
  QuotientGroup.congr _ _ (e.subgroupMap B).symm (CFSG.pCore_map_iso 2 _)

theorem exists_inner_of_map (e : X ≃* Y) {B : Subgroup X} {β : MulAut X}
    (h : ∃ b ∈ B.map e.toMonoidHom, ∀ y ∈ B.map e.toMonoidHom,
      ((e.symm.trans (β.trans e)) y)⁻¹ * (b * y * b⁻¹) ∈ pCoreOf 2 (B.map e.toMonoidHom)) :
    ∃ b ∈ B, ∀ x ∈ B, (β x)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B := by
  obtain ⟨b', ⟨b, hb, rfl⟩, hb'⟩ := h
  refine ⟨b, hb, fun x hx => ?_⟩
  have h1 := hb' (e x) ⟨x, hx, rfl⟩
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv] at h1
  obtain ⟨z, hz, hze⟩ := h1
  have hz' : z = (β x)⁻¹ * (b * x * b⁻¹) := by
    apply e.injective
    rw [show e z = e.toMonoidHom z from rfl, hze]
    simp
  rwa [← hz']

end Map

section Sub

variable {Q : Type} [Group Q]

theorem mem_pCoreOf_subgroupOf_iff {K B : Subgroup Q} (hBK : B ≤ K) (x : ↥K) :
    x ∈ pCoreOf 2 (B.subgroupOf K) ↔ (x : Q) ∈ pCoreOf 2 B := by
  set φ : ↥(B.subgroupOf K) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBK with hφ
  have hmap := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 φ
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨φ y, ?_, rfl⟩
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [← hmap] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    exact hyx

@[expose] noncomputable def modO2SubgroupOfEquiv {K B : Subgroup Q} (hBK : B ≤ K) :
    ModO2 (B.subgroupOf K) ≃* ModO2 B :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hBK) (CFSG.pCore_map_iso 2 _)

theorem perfectCore_subgroupOf [Finite Q] {P K : Subgroup Q} (hPK : P ≤ K) :
    perfectCore (P.subgroupOf K) = (perfectCore P).subgroupOf K := by
  have h1 : perfectCore P = (perfectCore (P.subgroupOf K)).map K.subtype := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPK]
  rw [h1]
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm

theorem isParabolic2_subgroupOf {K P : Subgroup Q} (h : IsParabolic2 K P) :
    IsParabolic2 (⊤ : Subgroup ↥K) (P.subgroupOf K) := by
  obtain ⟨hPK, S, ⟨hSK, hS2, hSi⟩, hNS⟩ := h
  refine ⟨le_top, S.subgroupOf K, ⟨le_top, ?_, ?_⟩, ?_⟩
  · exact hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  · rwa [show ((S.subgroupOf K).subgroupOf ⊤).index = (S.subgroupOf K).index from
      Subgroup.relIndex_top_right _]
  · rintro y ⟨-, hy⟩
    rw [Subgroup.mem_subgroupOf]
    refine hNS ⟨y.2, Subgroup.mem_normalizer_iff.mpr fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨q, hSK hq⟩).mp
        (by rw [Subgroup.mem_subgroupOf]; exact hq)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · have hqK : q ∈ K := by
        have h1 : (y : Q) * q * (y : Q)⁻¹ ∈ K := hSK hq
        have h2 : q = (y : Q)⁻¹ * ((y : Q) * q * (y : Q)⁻¹) * (y : Q) := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem y.2) h1) y.2
      have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨q, hqK⟩).mpr
        (by rw [Subgroup.mem_subgroupOf]; simpa using hq)
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1

theorem conjSub_mem_subgroupOf {K B : Subgroup Q} {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q)) (hgB : g ∈ Subgroup.normalizer (B : Set Q)) :
    ∀ x ∈ B.subgroupOf K, L139A5.conjSub hgK x ∈ B.subgroupOf K := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [L139A5.conjSub_apply]
  exact (Subgroup.mem_normalizer_iff.mp hgB x).mp hx

theorem exists_inner_of_sub {K B : Subgroup Q} (hBK : B ≤ K) {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q))
    (h : ∃ b ∈ B.subgroupOf K, ∀ x ∈ B.subgroupOf K,
      (L139A5.conjSub hgK x)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 (B.subgroupOf K)) :
    ∃ b ∈ B, ∀ x ∈ B, (g * x * g⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B := by
  obtain ⟨b, hb, hbx⟩ := h
  refine ⟨b, hb, fun x hx => ?_⟩
  have h1 := hbx ⟨x, hBK hx⟩ hx
  rw [mem_pCoreOf_subgroupOf_iff hBK] at h1
  simpa using h1

theorem exists_inner_of_conj {K B : Subgroup Q} (hBK : B ≤ K) {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q)) {k : ↥K}
    (hk : L139A5.conjSub hgK = MulAut.conj k)
    (h : ∃ b ∈ B.subgroupOf K, ∀ x ∈ B.subgroupOf K,
      (k * x * k⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 (B.subgroupOf K)) :
    ∃ b ∈ B, ∀ x ∈ B, (g * x * g⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B :=
  exists_inner_of_sub hBK hgK (by rw [hk]; simpa using h)

theorem mem_normalizer_of_conj {K B : Subgroup Q} {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q)) (hgB : g ∈ Subgroup.normalizer (B : Set Q))
    {k : ↥K} (hk : L139A5.conjSub hgK = MulAut.conj k) :
    k ∈ Subgroup.normalizer ((B.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : ((k * x * k⁻¹ : ↥K) : Q) = g * x * g⁻¹ := by
    have := congrArg (fun φ : MulAut ↥K => ((φ x : ↥K) : Q)) hk
    simpa using this.symm
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, h1]
  exact Subgroup.mem_normalizer_iff.mp hgB x

end Sub

end CFSG.Quasithin.L139L42
