module

public import CFSG.Quasithin.Recognition.SzR1CaseTwoGen
public import CFSG.Quasithin.Background.Harris.R1.Defs
public import CFSG.Quasithin.Recognition.SzR1Vert2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzR1

namespace FamCtx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

theorem center_le_of_odd [Fintype Ω] [DecidableEq Ω] (hodd : Odd (Fintype.card Ω))
    (hΩ : 4 ≤ Fintype.card Ω) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀) :
    ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs := by
  have hyp := C.amalgamHypV
  have hS := C.isNaturalS3
  have hZW : ∀ g ∈ L2 ⊔ S, conjSub g Zs ≤ vBeta K1 L2 S Zs := fun g hg =>
    calc conjSub g Zs ≤ conjSub g (conjClosure Zs L2) := conjSub_mono g (le_conjClosure Zs L2)
      _ = conjClosure Zs L2 := F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hg)
      _ ≤ vBeta K1 L2 S Zs := le_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
  obtain ⟨b, hb, hbZ, a, ha, haZ, T, hTN, hTW, -, u, huT, hu1, hu2, hus, hbu, a₁, ha₁, a₂, ha₂,
      hr⟩ := exists_central_involution_with_orbit
    (P := L2 ⊔ S) (S := S) (Q := pCoreOf 2 (L2 ⊔ S)) (W := vBeta K1 L2 S Zs) (Z := Zs)
    (M := C.kerM) le_sup_right C.pCore_le_S (le_normalizer_pCoreOf 2 (L2 ⊔ S))
    hyp.sylow₁.2.1
    (fun N hNP hPN hN2 => le_pCoreOf_of_le_normalizer 2 hNP hPN hN2)
    (F112J2.relIndex_L2S C.hR C.h.s3) (relIndex_pCoreOf_T hyp hS) C.vBeta_le_S
    (S_le_normalizer_vBeta K1 L2 S Zs) (le_sup_right.trans C.sup_le_normalizer_kerM)
    C.vBeta_le_kerM (F112J2.S_le_centralizer_Z C.h) C.h.card_Z
    (fun h => C.h.Z_not_norm (le_sup_left.trans h)) hZW C.hcomm.le C.commutator_kerM_vBeta_le
    (C.not_vBeta_le_pCore hΩ) (C.commutator_vBeta_inf_pCore_ne_bot hΩ hij)
    (fun s hs hfix => C.mem_kerM_of_mem_pCore hΩ hij hs hfix)
  have hy : ((SzR1.gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs := by
    by_cases huZ : u ∈ Zs
    · exact C.gprod_mem_Zs_of_central hodd hij l₀ hl₀ hall hb hbZ huZ hu1 hbu
    · exact (C.false_of_noncentral_gen hodd hΩ hij l₀ hl₀ hall ha haZ hTN hTW huT hus hu2 huZ
        ha₁ ha₂ hr).elim
  intro x hxW hxc
  rcases C.center_dichotomy hij l₀ hl₀ hall hxW hxc with ⟨b', hb'⟩ | ⟨b', hb'⟩
  · rw [hb']
    exact Zs.pow_mem (C.cm_mem i₀ j₀) b'
  · rw [hb']
    exact Zs.mul_mem (Zs.pow_mem (C.cm_mem i₀ j₀) b') hy

end FamCtx

end SzR1

@[expose] def CenterBenderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs

theorem centerBender_of_fam (hF : Background.Harris.R1.FamStmt) : CenterBenderStatement := by
  classical
  intro G _ _ K1 L2 S Zs hset ⟨n, hn, hb⟩ hna x hxW hxc
  obtain ⟨Ω, _, C, hodd, hL, hnL⟩ := hF G K1 L2 S Zs hset n hn hb hna
  have h4n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h5 : 5 ≤ Fintype.card Ω := by
    by_cases hl : IsL2Quot n (OTwoQuot K1)
    · rw [hL hl]
      omega
    · have h1 := hnL hl
      have h2 : 2 ^ n ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : Ω, i₀ ≠ j₀ :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega) |>.exists_pair_ne
  exact C.center_le_of_odd hodd (by omega) hij (Finset.univ : Finset Ω).toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.mpr (Finset.mem_univ i)) x hxW hxc

end CFSG.Quasithin
