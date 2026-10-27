module

public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftStar
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftAbs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

namespace E2.BorelLift

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem pCoreOf_le_of_sylow {T H : Subgroup Γ} (hT : IsSylowTwoOf T H) : pCoreOf 2 H ≤ T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hT.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem pCoreOf_le_kerIn {T H M : Subgroup Γ} (hT : IsSylowTwoOf T H) (hTM : T ≤ M) :
    pCoreOf 2 H ≤ kerIn M H := by
  intro x hx
  rw [mem_kerIn]
  intro b hb
  have h1 : b * x * b⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hb) x).mp hx
  exact hTM (pCoreOf_le_of_sylow hT h1)

omit [Finite Γ] in
theorem coe_mem_pCoreOf {K : Subgroup Γ} {k : ↥K} (hk : k ∈ CFSG.pCore 2 ↥K) :
    (k : Γ) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff k).mpr hk

omit [Finite Γ] in
theorem mem_pCore_of_coe {K : Subgroup Γ} {k : ↥K} (hk : (k : Γ) ∈ pCoreOf 2 K) :
    k ∈ CFSG.pCore 2 ↥K := (CFSG.mem_openPCoreOf_iff k).mp hk

theorem lift_two (hTor : E2.E22TorusCover) {H T MH K : Subgroup Γ} {n : ℕ}
    (hmin : MinParabolic H T MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hJ : ∀ x : Γ, x ∈ kerIn MH H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hn : 2 ≤ n)
    (hty : E2.IsBenderOf n ↥(E2.star MH H K) ∨ IsPSL 3 2 n ↥(E2.star MH H K) ∨
      IsPSp4 2 n ↥(E2.star MH H K))
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K))) :
    E2.E22BorelLift H T MH n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T H := hmin.isSylow
  have hTM : T ≤ MH := hmin.le
  have hMH : MH ≤ H := hmin.maximal.1.le
  set Q : Subgroup Γ := pCoreOf 2 H with hQ
  have hQT : Q ≤ T := pCoreOf_le_of_sylow hT
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hsK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hT
  have hcommJ : ∀ j ∈ K, j ∈ kerIn MH H → ∀ x ∈ K, j * x * j⁻¹ * x⁻¹ ∈ K ⊓ Q := by
    intro j hjK hjJ x hxK
    exact ⟨K.mul_mem (K.mul_mem (K.mul_mem hjK hxK) (K.inv_mem hjK)) (K.inv_mem hxK),
      ((hJ j).mp hjJ).2 x (Subgroup.mem_sup_left hxK)⟩
  have hJK : ∀ j ∈ K, j ∈ kerIn MH H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K := by
    intro j hjK hjJ x hx
    have h1 := hcommJ j hjK hjJ x hx.2
    have h2 : j * x * j⁻¹ * x⁻¹ ∈ T ⊓ K := ⟨hQT h1.2, h1.1⟩
    have := (T ⊓ K).mul_mem h2 hx
    simpa using this
  have hBeq : MH ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) :=
    inf_eq_normalizer hT hTM hK hB hJK
  have hO : CFSG.pCore 2 ↥K ≤ (starRes MH H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starRes_eq_one_iff]
    have h1 : (k : Γ) ∈ pCoreOf 2 K := coe_mem_pCoreOf hk
    exact pCoreOf_le_kerIn hT hTM
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) h1)
  have hZ : ∀ k ∈ (starRes MH H K hKH).ker, ∀ x : ↥K,
      k * x * k⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥K := by
    intro k hk x
    rw [MonoidHom.mem_ker, starRes_eq_one_iff] at hk
    apply mem_pCore_of_coe
    have h1 := hcommJ k k.2 hk x x.2
    exact Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf hKH h1
  obtain ⟨hcommK, Y, w, hYle, hYc, hYcard, hwK, hwN, hwY⟩ :=
    torus_of_cover hTor (starRes MH H K hKH) (starRes_surjective hKH) hO hZ hn hty hsK
  have hMKT : MH ≤ (MH ⊓ K) ⊔ T := by
    intro m hm
    have hmKT : m ∈ ((K ⊔ T : Subgroup Γ) : Set Γ) := hHK ▸ hMH hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hmKT
    obtain ⟨k, hk, t, ht, rfl⟩ := hmKT
    have hkM : k ∈ MH := by
      have := MH.mul_mem hm (MH.inv_mem (hTM ht))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hkM, hk⟩) (Subgroup.mem_sup_right ht)
  have hTNS : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htK := hTK ht
    constructor
    · rintro ⟨hxT, hxK⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htK x).mp hxK⟩
    · rintro ⟨hxT, hxK⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htK x).mpr hxK⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
  have hMS : MH ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) :=
    hMKT.trans (sup_le (hBeq ▸ inf_le_right) hTNS)
  have hP₂T : pCoreOf 2 K ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans hQT
  refine lift_of_borel (R₀ := K) (P₂ := pCoreOf 2 K) (Y₀ := Y) (w₀ := w) hT hTM hMH hHN hKH
    (hHK ▸ le_rfl) hMS (hBeq ▸ hcommK) (by omega) (hBeq ▸ hYle) hYc hYcard (hP₂T.trans hTM)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    ((hYle.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    (hKH hwK) (fun hwM => hwN ((hBeq ▸ ⟨hwM, hwK⟩ : w ∈ K ⊓ _).2)) ?_
  intro A hAY a ha
  have h1 := hwY a (hAY ha)
  have h2 : w * a * w⁻¹ = (w * a * w⁻¹ * a) * a⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (A.inv_mem ha))

end E2.BorelLift

end CFSG.Quasithin
