module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.B3Basic

public section

namespace CFSG.Quasithin.B3

@[expose] def O2s {G : Type*} [Group G] (X : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 ↥X).map X.subtype

theorem O2s_eq {G : Type*} [Group G] [Finite G] (X T R : Subgroup G) (hTX : T ≤ X)
    (hTp : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf X).index)
    (hR : ∀ r, r ∈ R ↔ r ∈ X ∧ ∀ x ∈ X, x⁻¹ * r * x ∈ T) : O2s X = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTcard : ∃ m, Nat.card T = 2 ^ m := (IsPGroup.iff_card).1 hTp
  obtain ⟨m, hm⟩ := hTcard
  have hTY : IsPGroup 2 ↥(T.subgroupOf X) := by
    apply IsPGroup.of_card (n := m)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hm]
  let TS : Sylow 2 ↥X := hTY.toSylow hidx
  have hRT : ∀ r ∈ R, r ∈ T := by
    intro r hr
    have := ((hR r).1 hr).2 1 X.one_mem
    simpa using this
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [hR]
    refine ⟨y.2, fun x hx => ?_⟩
    obtain ⟨g, hg⟩ := exists_conj_le_sylow TS (CFSG.pCore 2 ↥X) CFSG.pCore_isPGroup
    have hz : (⟨x, hx⟩ : ↥X)⁻¹ * y * ⟨x, hx⟩ ∈ cj g (CFSG.pCore 2 ↥X) := by
      rw [mem_cj]
      have h1 := hN.conj_mem y hy ((⟨x, hx⟩ : ↥X) * g)⁻¹
      simpa [mul_assoc] using h1
    have hzT : (⟨x, hx⟩ : ↥X)⁻¹ * y * ⟨x, hx⟩ ∈ (TS : Subgroup ↥X) := hg hz
    have h2 : ((⟨x, hx⟩ : ↥X)⁻¹ * y * ⟨x, hx⟩ : ↥X).1 ∈ T := hzT
    simpa using h2
  · intro r hr
    have hrX : r ∈ X := ((hR r).1 hr).1
    have hRX : R ≤ X := fun r hr => ((hR r).1 hr).1
    refine ⟨⟨r, hrX⟩, ?_, rfl⟩
    have hKn : (R.subgroupOf X).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ R := hn
      rw [Subgroup.mem_subgroupOf, hR]
      refine ⟨(g * n * g⁻¹ : ↥X).2, fun x hx => ?_⟩
      have h1 := ((hR n).1 hn').2 ((g : G)⁻¹ * x) (X.mul_mem (X.inv_mem g.2) hx)
      simpa [mul_assoc] using h1
    have hKp : IsPGroup 2 ↥(R.subgroupOf X) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (hm ▸ Subgroup.card_dvd_of_le (fun r hr => hRT r hr) : Nat.card R ∣ 2 ^ m)
      apply IsPGroup.of_card (n := j)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, hj]
    exact Subgroup.mem_sSup_of_mem (show R.subgroupOf X ∈
      {K : Subgroup ↥X | K.Normal ∧ IsPGroup 2 ↥K} from ⟨hKn, hKp⟩)
      (show (⟨r, hrX⟩ : ↥X) ∈ R.subgroupOf X from hr)

end CFSG.Quasithin.B3
