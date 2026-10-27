module

public import CFSG.Quasithin.Vol2.GoldschmidtP778A5S5
public import CFSG.Quasithin.H13.NParamLiftS5

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {H T A : Subgroup G} (ψ : ↥H →* Perm (Fin 5))

theorem psi_pCore_eq_one (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (n : ↥H)
    (hn : n ∈ CFSG.Open.pCore 2 ↥H) : ψ n = 1 := by
  set N := CFSG.Open.pCore 2 ↥H with hN
  have hnorm : alternatingGroup (Fin 5) ≤ Subgroup.normalizer ((N.map ψ : Subgroup _) :
      Set (Perm (Fin 5))) := by
    intro σ hσ
    obtain ⟨p, rfl⟩ := hA5 hσ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨p * m * p⁻¹, hNn.conj_mem m hm p, by simp⟩
    · rintro ⟨m, hm, hmx⟩
      refine ⟨p⁻¹ * m * p, by simpa using hNn.conj_mem m hm p⁻¹, ?_⟩
      have : x = (ψ p)⁻¹ * (ψ p * x * (ψ p)⁻¹) * ψ p := by group
      rw [this, ← hmx]
      simp
  have hsol : Group.IsSolvable ↥(N.map ψ) := by
    have : Group.IsNilpotent ↥N := (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
    have h1 : Group.IsSolvable ↥((ψ.comp N.subtype).range) :=
      Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (ψ.comp N.subtype))
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hbot := eq_bot_of_isSolvable hnorm hsol
  have hmem : ψ n ∈ N.map ψ := ⟨n, hn, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem psi_pCoreOf_eq_one (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) {x : G}
    (hx : x ∈ pCoreOf 2 H) : ∃ hxH : x ∈ H, ψ ⟨x, hxH⟩ = 1 := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨n.2, psi_pCore_eq_one ψ hA5 n hn⟩

omit [Finite G] in
theorem ker_le_T (hker : IsPGroup 2 ψ.ker) (hT : IsSylowIn 2 T H) :
    ψ.ker.map H.subtype ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hT.le_of_normal (Subgroup.map_subtype_le _) ?_ (hker.map _)
  have : (ψ.ker.map H.subtype).subgroupOf H = ψ.ker :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective ψ.ker
  rw [this]
  exact ψ.normal_ker

@[expose] def kA : Subgroup G := (C1.comap ψ).map H.subtype

@[expose] def rA : Subgroup G := (R1.comap ψ).map H.subtype

@[expose] def zA : Subgroup G := (Z01.comap ψ).map H.subtype

omit [Finite G] in
theorem mem_preimage {D : Subgroup (Perm (Fin 5))} {x : G} :
    x ∈ (D.comap ψ).map H.subtype ↔ ∃ h : x ∈ H, ψ ⟨x, h⟩ ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

omit [Finite G] in
theorem mem_kA {x : G} : x ∈ kA ψ ↔ ∃ h : x ∈ H, ψ ⟨x, h⟩ ∈ c1list :=
  mem_preimage ψ (D := C1)

omit [Finite G] in
theorem mem_rA {x : G} : x ∈ rA ψ ↔ ∃ h : x ∈ H, ψ ⟨x, h⟩ ∈ r1list :=
  mem_preimage ψ (D := R1)

omit [Finite G] in
theorem mem_zA {x : G} : x ∈ zA ψ ↔ ∃ h : x ∈ H, ψ ⟨x, h⟩ ∈ z01list :=
  mem_preimage ψ (D := Z01)

omit [Finite G] in
theorem zA_le_rA : zA ψ ≤ rA ψ := by
  intro x hx
  obtain ⟨h, hx⟩ := (mem_zA ψ).1 hx
  exact (mem_rA ψ).2 ⟨h, z01_le_r1 _ hx⟩

omit [Finite G] in
theorem rA_le_kA : rA ψ ≤ kA ψ := by
  intro x hx
  obtain ⟨h, hx⟩ := (mem_rA ψ).1 hx
  exact (mem_kA ψ).2 ⟨h, r1_le_c1 _ hx⟩

omit [Finite G] in
theorem kA_le : kA ψ ≤ H := fun _ hx => ((mem_kA ψ).1 hx).1

omit [Finite G] in
theorem zA_isPGroup (hker : IsPGroup 2 ψ.ker) : IsPGroup 2 ↥(zA ψ) := by
  have h0 : IsPGroup 2 ↥(Z01.comap ψ) := by
    intro g
    have hg : ψ g.1 ∈ z01list := g.2
    have hsq : (ψ g.1) ^ 2 = 1 := z01_sq _ hg
    have hk : g.1 ^ 2 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hsq]
    obtain ⟨k, hk'⟩ := hker ⟨g.1 ^ 2, hk⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h2 := congrArg (fun y : ↥ψ.ker => (y : ↥H)) hk'
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [Nat.pow_succ', pow_mul]
    exact h2
  exact h0.map H.subtype

omit [Finite G] in
theorem exists_preimage_kA (hψ : ψ.range = ⊤) {w : Perm (Fin 5)} (hw : w ∈ c1list) :
    ∃ s : ↥H, (s : G) ∈ kA ψ ∧ ψ s = w := by
  have : w ∈ ψ.range := hψ ▸ Subgroup.mem_top w
  obtain ⟨s, rfl⟩ := this
  exact ⟨s, (mem_kA ψ).2 ⟨s.2, by simpa using hw⟩, rfl⟩

omit [Finite G] in
theorem zA_le_kA : zA ψ ≤ kA ψ := (zA_le_rA ψ).trans (rA_le_kA ψ)

omit [Finite G] in
theorem conj_mem_zA {s x : G} (hs : s ∈ kA ψ) (hx : x ∈ zA ψ) : s * x * s⁻¹ ∈ zA ψ := by
  obtain ⟨hsH, hsc⟩ := (mem_kA ψ).1 hs
  obtain ⟨hxH, hxz⟩ := (mem_zA ψ).1 hx
  refine (mem_zA ψ).2 ⟨H.mul_mem (H.mul_mem hsH hxH) (H.inv_mem hsH), ?_⟩
  have : ψ ⟨s * x * s⁻¹, H.mul_mem (H.mul_mem hsH hxH) (H.inv_mem hsH)⟩ =
      ψ ⟨s, hsH⟩ * ψ ⟨x, hxH⟩ * (ψ ⟨s, hsH⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [this]
  exact z01_normal _ hsc _ hxz

omit [Finite G] in
theorem kA_le_normalizer_zA : kA ψ ≤ Subgroup.normalizer (zA ψ : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_zA ψ hs hx
  · intro hx
    have := conj_mem_zA ψ ((kA ψ).inv_mem hs) hx
    simpa [mul_assoc] using this

theorem pCoreOf_kA (hψ : ψ.range = ⊤) (hker : IsPGroup 2 ψ.ker) :
    pCoreOf 2 (kA ψ) = zA ψ := by
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ kA ψ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    obtain ⟨hxH, hxc⟩ := (mem_kA ψ).1 hxS
    refine (mem_zA ψ).2 ⟨hxH, o2_c1 _ hxc fun w hw => ?_⟩
    obtain ⟨b, hb, rfl⟩ := exists_preimage_kA ψ hψ hw
    have hconj : ∀ c : ↥H, (c : G) ∈ kA ψ → (c : G) * x * (c : G)⁻¹ ∈ pCoreOf 2 (kA ψ) := by
      intro c hc
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kA ψ) hc) x).mp hx
      exact this
    have hy : x * ((b : G) * x * (b : G)⁻¹) ∈ pCoreOf 2 (kA ψ) :=
      Subgroup.mul_mem _ hx (hconj b hb)
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kA ψ) ⟨_, hy⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
    refine pow_four_of_exists_two_power _ ⟨k, ?_⟩
    have hyH : (⟨x, hxH⟩ * (b * ⟨x, hxH⟩ * b⁻¹) : ↥H) ^ 2 ^ k = 1 := Subtype.ext hk'
    have := congrArg ψ hyH
    simpa [map_mul, map_inv, map_pow] using this
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (zA_le_kA ψ)
      (kA_le_normalizer_zA ψ) (zA_isPGroup ψ hker)

end CFSG.Quasithin.E1.ThinA5
