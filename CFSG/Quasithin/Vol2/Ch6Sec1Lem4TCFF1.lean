module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.T614.FFStep

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem eq_one_of_isPGroup_of_isPerfect {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p Y) [Group.IsPerfect Y] (y : Y) : y = 1 := by
  by_contra hy
  haveI : Nontrivial Y := ⟨⟨y, 1, hy⟩⟩
  exact Group.IsPerfect.not_isNilpotent Y (IsPGroup.isNilpotent hp)

section Omega

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_omegaOneCenter (Q : Subgroup G) :
    IsElemAbelian 2 (quasithinOmegaOneCenter Q) :=
  CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf Q

theorem omegaOne_le (Q : Subgroup G) : quasithinOmegaOneCenter Q ≤ Q := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  intro z hz
  exact (Subgroup.mem_inf.mp hz.1).1

theorem le_centralizer_omegaOne (Q : Subgroup G) :
    Q ≤ Subgroup.centralizer (quasithinOmegaOneCenter Q : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  intro z hz
  exact (Subgroup.mem_inf.mp hz.1).2

theorem conj_mem_omegaOne {Q H : Subgroup G} (hQH : H ≤ Subgroup.normalizer (Q : Set G))
    {h : G} (hh : h ∈ H) {r : G} (hr : r ∈ quasithinOmegaOneCenter Q) :
    h * r * h⁻¹ ∈ quasithinOmegaOneCenter Q := by
  have hN : h ∈ Subgroup.normalizer (Q : Set G) := hQH hh
  have hgen : ∀ z ∈ {z : G | z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ∧ z ^ 2 = 1},
      h * z * h⁻¹ ∈ quasithinOmegaOneCenter Q := by
    intro z hz
    obtain ⟨hzQC, hz2⟩ := hz
    obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hzQC
    unfold quasithinOmegaOneCenter
    apply Subgroup.subset_closure
    show (h * z * h⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) ∧ (h * z * h⁻¹) ^ 2 = 1
    refine ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hN z).mp hzQ
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : h⁻¹ * q * h ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hQH (H.inv_mem hh)) q).mp hq
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hzC (h⁻¹ * q * h) hq'
      calc q * (h * z * h⁻¹) = h * ((h⁻¹ * q * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * q * h)) * h⁻¹ := by rw [hc]
        _ = h * z * h⁻¹ * q := by group
    · calc (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2]; group
  have hmap : (Subgroup.closure {z : G | z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ∧ z ^ 2 = 1}).map
      (MulAut.conj h).toMonoidHom ≤ quasithinOmegaOneCenter Q := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hgen z hz
  have := hmap ⟨r, hr, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem normalizer_le_omegaOne {Q H : Subgroup G} (hQH : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer (quasithinOmegaOneCenter Q : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact conj_mem_omegaOne hQH hh hr
  · intro hr
    have := conj_mem_omegaOne hQH (H.inv_mem hh) hr
    simpa [mul_assoc] using this

end Omega

section Step2

variable {G : Type} [Group G] [Finite G]

theorem centralizer_inf_eq_pCoreOf {K R : Subgroup G} (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hperf : Group.IsPerfect ↥K) (hsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hOC : pCoreOf 2 K ≤ Subgroup.centralizer (R : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (R : Set G)) :
    K ⊓ Subgroup.centralizer (R : Set G) = pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hperf
  set C₁ : Subgroup G := K ⊓ Subgroup.centralizer (R : Set G) with hC₁
  have hC₁n : (C₁.subgroupOf K).Normal := by
    constructor
    intro c hc g
    have hc' : (c : G) ∈ C₁ := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.mp hc'
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact K.mul_mem (K.mul_mem g.2 hcK) (K.inv_mem g.2)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hg : (g : G) ∈ Subgroup.normalizer (R : Set G) := hKR g.2
      have hr' : (g : G)⁻¹ * r * (g : G) ∈ R := by
        refine (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_
        have e : (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ = r := by group
        rw [e]
        exact hr
      have hc1 := Subgroup.mem_centralizer_iff.mp hcC _ hr'
      calc r * ((g : G) * c * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * r * (g : G)) * c) * (g : G)⁻¹ := by group
        _ = (g : G) * (c * ((g : G)⁻¹ * r * (g : G))) * (g : G)⁻¹ := by rw [hc1]
        _ = (g : G) * c * (g : G)⁻¹ * r := by group
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set M : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := (C₁.subgroupOf K).map π with hM
  have hMn : M.Normal := Subgroup.Normal.map hC₁n π (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := ↥K ⧸ CFSG.pCore 2 ↥K) M with hM0 | hM1
  · refine le_antisymm (fun c hc => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hOC)
    obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.mp hc
    have h1 : π ⟨c, hcK⟩ ∈ M :=
      Subgroup.mem_map.mpr ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcK, hcC⟩),
        rfl⟩
    rw [hM0, Subgroup.mem_bot] at h1
    have h2 : (⟨c, hcK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_map.mpr ⟨⟨c, hcK⟩, h2, rfl⟩
  · exfalso
    apply hne
    intro k hk
    have hk1 : π ⟨k, hk⟩ ∈ M := by
      rw [hM1]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hπc⟩ := Subgroup.mem_map.mp hk1
    haveI hperfQ : Group.IsPerfect (↥K ⧸ C₁.subgroupOf K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (C₁.subgroupOf K))
        (QuotientGroup.mk'_surjective _)
    have hpg : IsPGroup 2 (↥K ⧸ C₁.subgroupOf K) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H k =>
        have hk2 : π k ∈ M := by
          rw [hM1]
          exact Subgroup.mem_top _
        obtain ⟨c', hc', hπc'⟩ := Subgroup.mem_map.mp hk2
        have ho : k * c'⁻¹ ∈ CFSG.pCore 2 ↥K := by
          have h3 : π (k * c'⁻¹) = 1 := by
            rw [map_mul, map_inv, hπc', mul_inv_cancel]
          exact (QuotientGroup.eq_one_iff _).mp h3
        obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨k * c'⁻¹, ho⟩
        have hn' : (k * c'⁻¹) ^ 2 ^ n = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        refine ⟨n, ?_⟩
        have e : (QuotientGroup.mk k : ↥K ⧸ C₁.subgroupOf K) = QuotientGroup.mk (k * c'⁻¹) :=
          (QuotientGroup.eq).mpr (by simpa using (C₁.subgroupOf K).inv_mem hc')
        rw [e, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
    have hall : ∀ x : ↥K ⧸ C₁.subgroupOf K, x = 1 := fun x =>
      eq_one_of_isPGroup_of_isPerfect hpg x
    have h4 := (QuotientGroup.eq_one_iff (⟨k, hk⟩ : ↥K)).mp (hall _)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h4)).2

end Step2

end CFSG.Quasithin.H13.T614.FFStep
