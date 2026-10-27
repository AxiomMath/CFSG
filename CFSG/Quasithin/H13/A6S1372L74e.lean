module

public import CFSG.Quasithin.H13.A6S1372L74b
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.A6S1372Fourteen

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6L74

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_iff {H : Subgroup G} (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem le_normalizer_map_of_normal {H : Subgroup G} {N : Subgroup ↥H} (hN : N.Normal) :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hN.conj_mem y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩⁻¹⁻¹, hN.conj_mem y hy _, ?_⟩
    have hyx' : (y : G) = h * x * h⁻¹ := hyx
    show h⁻¹ * (y : G) * h⁻¹⁻¹ = x
    rw [hyx']
    group

theorem exists_comp_or_odd_of_le {H C : Subgroup G} (hQC : pCoreOf 2 H ≤ C) (hCH : C ≤ H)
    (hHC : H ≤ Subgroup.normalizer (C : Set G)) (hCQ : ¬ C ≤ pCoreOf 2 H) :
    (∃ K ∈ cComp H, K ≤ C ∧ ¬ K ≤ pCoreOf 2 H) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ K₁ : Subgroup G, pCoreOf 2 H ≤ K₁ ∧ K₁ ≤ C ∧
        H ≤ Subgroup.normalizer (K₁ : Set G) ∧ ¬ K₁ ≤ pCoreOf 2 H ∧
        (∀ k ∈ K₁, k ^ p ∈ pCoreOf 2 H) ∧
        (∀ a ∈ K₁, ∀ b ∈ K₁, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H) ∧
        ∀ N : Subgroup G, pCoreOf 2 H ≤ N → N ≤ K₁ → H ≤ Subgroup.normalizer (N : Set G) →
          N = pCoreOf 2 H ∨ N = K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup ↥H := CFSG.pCore 2 ↥H with hP
  set π : ↥H →* ↥H ⧸ P := QuotientGroup.mk' P with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hker : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCoreOf_iff]
  have hmodC : ∀ x : ↥H, ∀ y : ↥H, (y : G) ∈ C → π y = π x → (x : G) ∈ C := by
    intro x y hy hxy
    have h1 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hQC ((hker _).1 h1)
    have e : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
    rw [e]
    exact C.mul_mem hy h2
  set Cbar : Subgroup (↥H ⧸ P) := (C.subgroupOf H).map π with hCbar
  have hCn : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
  have hCbarn : Cbar.Normal := hCn.map π hπs
  have hXC : (⊤ : Subgroup (↥H ⧸ P)) ≤ Subgroup.normalizer (Cbar : Set (↥H ⧸ P)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCbarn]
  have hO2 : ∀ R : Subgroup (↥H ⧸ P), R ≤ ⊤ →
      (⊤ : Subgroup (↥H ⧸ P)) ≤ Subgroup.normalizer (R : Set (↥H ⧸ P)) → IsPGroup 2 R →
      R = ⊥ := by
    intro R _ hR hR2
    have hRn : R.Normal :=
      ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hR (Subgroup.mem_top g)) n).mp hn⟩
    have h1 : R ≤ CFSG.Open.pCore 2 (↥H ⧸ P) := le_pCore 2 hRn hR2
    rw [pCore_two_quotient_pCore_two ↥H] at h1
    exact le_bot_iff.mp h1
  have hC1 : Cbar ≠ ⊥ := by
    intro h
    apply hCQ
    intro c hc
    have h1 : π ⟨c, hCH hc⟩ ∈ Cbar := ⟨⟨c, hCH hc⟩, hc, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (hker _).1 h1
  have hsolv : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  rcases exists_comp_or_odd le_top hXC hO2 hC1 with ⟨Kbar, hK⟩ | ⟨p, hp, hp2, Nbar, hNC, hXN, hN1,
      hNp, hmin⟩
  ·
    left
    have hKsub : IsSubnormal Kbar (⊤ : Subgroup (↥H ⧸ P)) :=
      A3.subnormal_trans hK.2.1 (A3.subnormal_of_normal le_top
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr hXC))
    have hKc : Kbar ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) :=
      A6Fourteen.mem_cComp_of_isComponentOf ⟨le_top, hKsub, hK.2.2⟩
    have hKc' : Kbar ∈ cComp ((⊤ : Subgroup ↥H).map π) := by
      rwa [Subgroup.map_top_of_surjective π hπs]
    obtain ⟨K₀, hK₀, hK₀map⟩ := LocDbl.map_surjOn_cComp π hsolv ⊤ hKc'
    have hK₀H := LocDbl.map_mem_cComp_of_ker H.subtype
      (LocDbl.isSolvable_ker_of_injective _ H.subtype_injective) hK₀
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hK₀H
    refine ⟨K₀.map H.subtype, hK₀H, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : π x ∈ Kbar := hK₀map ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hK.1 h1
      exact hmodC x y hy hyx
    · intro hle
      apply ne_bot_of_mem_cComp hKc
      rw [← hK₀map, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_bot).2 ((hker x).2 (hle ⟨x, hx, rfl⟩))
  ·
    right
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hab, hexp⟩ := minimal_isElemAbelian hN1 hXN hNp hmin
    refine ⟨p, hp, hp2, (Nbar.comap π).map H.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      refine ⟨⟨q, pCoreOf_le 2 H hq⟩, ?_, rfl⟩
      show π ⟨q, _⟩ ∈ Nbar
      rw [(hker _).2 hq]
      exact Nbar.one_mem
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hNC hx
      exact hmodC x y hy hyx
    · have hNn : Nbar.Normal :=
        ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hXN (Subgroup.mem_top g)) n).mp hn⟩
      exact le_normalizer_map_of_normal (hNn.comap π)
    · intro hle
      apply hN1
      rw [eq_bot_iff]
      intro n hn
      obtain ⟨x, rfl⟩ := hπs n
      exact (Subgroup.mem_bot).2 ((hker x).2 (hle ⟨x, hn, rfl⟩))
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : π (x ^ p) = 1 := by rw [map_pow]; exact hexp _ hx
      have := (hker _).1 h1
      simpa using this
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab _ hx _ hy]
        group
      have := (hker _).1 h1
      simpa using this
    · intro N hQN hNK hHN
      set Nb : Subgroup (↥H ⧸ P) := (N.subgroupOf H).map π with hNb
      have hNH : N ≤ H := hNK.trans (Subgroup.map_subtype_le _)
      have hNbN : Nb ≤ Nbar := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hNK hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
      have hNbn : (⊤ : Subgroup (↥H ⧸ P)) ≤ Subgroup.normalizer (Nb : Set (↥H ⧸ P)) := by
        have hn : (N.subgroupOf H).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
        rw [Subgroup.normalizer_eq_top_iff.mpr (hn.map π hπs)]
      rcases hmin Nb hNbN hNbn with h | h
      · left
        refine le_antisymm (fun x hx => ?_) hQN
        have h1 : π ⟨x, hNH hx⟩ ∈ Nb := ⟨⟨x, hNH hx⟩, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact (hker _).1 h1
      · right
        refine le_antisymm hNK ?_
        rintro _ ⟨x, hx, rfl⟩
        have h1 : π x ∈ Nb := h ▸ hx
        obtain ⟨y, hy, hyx⟩ := h1
        have h2 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
        have h3 := hQN ((hker _).1 h2)
        have e : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
        rw [Subgroup.coe_subtype, e]
        exact N.mul_mem hy h3

end A6L74

end CFSG.Quasithin.H13.A6
