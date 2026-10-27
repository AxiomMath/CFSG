module

public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146C5

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

theorem input14624NotTwoGroup_proof : Input14624NotTwoGroup := by
  intro G _ _ T M S _hB K U₁ U₂ s u hctx hKeq hL3 _hinv hP
  classical
  obtain ⟨-, -, -, hK, -, -, hdec, hch⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  obtain ⟨hSec, -, -⟩ := S.sec8_of_decomp hK hL3 hdec
  obtain ⟨huU, hunc⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T := by
    rcases hch with ⟨-, huU, hunc, -⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
    · exact ⟨huU, hunc⟩
    · exact absurd (hKn (hTH ht)) htn
  have huZ : u ∉ quasithinOmegaOneCenter T := by
    intro hu
    apply hunc
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hu) le_rfl).trans
      (S145.commutator_le_of_le_normalizer hSec.KZ)
  have hU₁card : Nat.card U₁ = 16 := by
    have h := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) U₁
    rw [inf_eq_left.mpr hSec.le, hSec.card, S.card_Z] at h
    omega
  have h21 : 21 ∣ Nat.card K := by
    have h1 := relIndex_pCoreOf_of_kbarIsL3Two hL3
    have h2 := Subgroup.relIndex_dvd_card (pCoreOf 2 K) K
    rw [h1] at h2
    exact (by norm_num : 21 ∣ 168).trans h2
  let _ : MulAction K G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp K.subtype)
  have hsmul : ∀ (k : K) (g : G), k • g = (k : G) * g * (k : G)⁻¹ := fun k g => rfl
  have horb : MulAction.orbit K u ⊆ (U₁ : Set G) \ (quasithinOmegaOneCenter T : Set G) := by
    rintro _ ⟨k, rfl⟩
    have hk : k • u = (k : G) * u * (k : G)⁻¹ := hsmul k u
    refine ⟨?_, ?_⟩
    · show k • u ∈ U₁
      rw [hk]
      exact (Subgroup.mem_normalizer_iff.mp (hSec.KU k.2) u).mp huU
    · intro hk'
      have hk'' : (k : G) * u * (k : G)⁻¹ ∈ quasithinOmegaOneCenter T := by
        have : k • u ∈ quasithinOmegaOneCenter T := hk'
        rwa [hk] at this
      exact huZ ((Subgroup.mem_normalizer_iff.mp (hSec.KZ k.2) u).mpr hk'')
  have hZsub : (quasithinOmegaOneCenter T : Set G) ⊆ (U₁ : Set G) := hSec.le
  have hdiff : ((U₁ : Set G) \ (quasithinOmegaOneCenter T : Set G)).ncard = 14 := by
    rw [Set.ncard_sdiff hZsub (Set.toFinite _)]
    have e1 : (U₁ : Set G).ncard = 16 := by
      rw [← hU₁card]; exact (Nat.card_coe_set_eq _).symm
    have e2 : (quasithinOmegaOneCenter T : Set G).ncard = 2 := by
      rw [← S.card_Z]; exact (Nat.card_coe_set_eq _).symm
    omega
  have hle : (MulAction.orbit K u).ncard ≤ 14 := by
    rw [← hdiff]
    exact Set.ncard_le_ncard horb (Set.toFinite _)
  have hpos : 0 < (MulAction.orbit K u).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, MulAction.mem_orbit_self u⟩
  have hstab : Nat.card (MulAction.stabilizer K u) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({u} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1 : G), Subgroup.mem_inf.mpr ⟨k.1.2, ?_⟩⟩
        invFun := fun a => ⟨⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩, ?_⟩
        left_inv := fun k => rfl
        right_inv := fun a => rfl }
    · have hk := k.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg (fun x => x * (k.1 : G)) hk
      simp only [mul_assoc, inv_mul_cancel, mul_one] at this
      exact this
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp a.2).2
      show (a : G) * u * (a : G)⁻¹ = u
      rw [this]
      group
  have hindex := MulAction.index_stabilizer K u
  have hmul := Subgroup.index_mul_card (MulAction.stabilizer K u)
  rw [hindex, hstab] at hmul
  have hP2 : ∃ n, Nat.card ↥(K ⊓ Subgroup.centralizer ({u} : Set G)) = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.iff_card).mp hP
  obtain ⟨n, hn⟩ := hP2
  rw [hn] at hmul
  have h21' : 21 ∣ (MulAction.orbit K u).ncard * 2 ^ n := by
    rw [hmul]; exact h21
  have hcop : Nat.Coprime 21 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have h21'' : 21 ∣ (MulAction.orbit K u).ncard := hcop.dvd_of_dvd_mul_right h21'
  have := Nat.le_of_dvd hpos h21''
  omega

end CFSG.Quasithin
