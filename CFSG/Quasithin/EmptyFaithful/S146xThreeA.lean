module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.EmptyFaithful.S146E6
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146C5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Components

variable {G : Type} [Group G] [Finite G]

theorem cComp_ne_map_commutator_eq_bot {H L K : Subgroup G} (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (hne : L ≠ K) :
    ⁅(L.subgroupOf H).map (QuotientGroup.mk' (CFSG.solvableRadical ↥H)),
      (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.solvableRadical ↥H))⁆ = ⊥ := by
  classical
  have hHL : L ≤ H := le_of_mem_cComp hL
  have hHK : K ≤ H := le_of_mem_cComp hK
  set N : Subgroup ↥H := CFSG.solvableRadical ↥H with hN
  have hNs : Group.IsSolvable N := A3.solvableRadical_isSolvable
  have hbij := cComp_quotient_bijOn N hNs
  have hL' : L.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hL
  have hK' : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  have hLc : (L.subgroupOf H).map (QuotientGroup.mk' N) ∈
      {X : Subgroup (↥H ⧸ N) | CFSG.IsComponent X} := by
    rw [← (cComp_part_five (G := ↥H)).1]
    exact hbij.mapsTo hL'
  have hKc : (K.subgroupOf H).map (QuotientGroup.mk' N) ∈
      {X : Subgroup (↥H ⧸ N) | CFSG.IsComponent X} := by
    rw [← (cComp_part_five (G := ↥H)).1]
    exact hbij.mapsTo hK'
  have hne' : (L.subgroupOf H).map (QuotientGroup.mk' N) ≠
      (K.subgroupOf H).map (QuotientGroup.mk' N) := by
    intro h
    apply hne
    have := hbij.injOn hL' hK' h
    have hL2 := Subgroup.map_subgroupOf_eq_of_le hHL
    have hK2 := Subgroup.map_subgroupOf_eq_of_le hHK
    rw [← hL2, ← hK2, this]
  exact (CFSG.LocalCores.distinct_components_commute hLc hKc).resolve_left hne'

theorem cComp_ne_commutator_le_solvRad {H L K : Subgroup G} (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (hne : L ≠ K) : ⁅L, K⁆ ≤ solvRad H := by
  classical
  have hHL : L ≤ H := le_of_mem_cComp hL
  have hHK : K ≤ H := le_of_mem_cComp hK
  set N : Subgroup ↥H := CFSG.solvableRadical ↥H with hN
  have hcomm := cComp_ne_map_commutator_eq_bot hL hK hne
  rw [Subgroup.commutator_le]
  intro l hl k hk
  have hl' : (⟨l, hHL hl⟩ : ↥H) ∈ L.subgroupOf H := hl
  have hk' : (⟨k, hHK hk⟩ : ↥H) ∈ K.subgroupOf H := hk
  have h1 : ⁅QuotientGroup.mk' N (⟨l, hHL hl⟩ : ↥H), QuotientGroup.mk' N (⟨k, hHK hk⟩ : ↥H)⁆ ∈
      ⁅(L.subgroupOf H).map (QuotientGroup.mk' N), (K.subgroupOf H).map (QuotientGroup.mk' N)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hl') (Subgroup.mem_map_of_mem _ hk')
  rw [hcomm, Subgroup.mem_bot] at h1
  have h2 : (⁅(⟨l, hHL hl⟩ : ↥H), (⟨k, hHK hk⟩ : ↥H)⁆ : ↥H) ∈ N := by
    have h3 : (QuotientGroup.mk' N) ⁅(⟨l, hHL hl⟩ : ↥H), (⟨k, hHK hk⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp h3
  rw [solvRad_eq_map_solvableRadical]
  exact ⟨_, h2, rfl⟩

theorem cComp_eq_of_le_sup {H L K Kp : Subgroup G} (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (hKp : Kp ∈ cComp H) (hle : L ≤ K ⊔ Kp) : L = K ∨ L = Kp := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hLK, hLKp⟩ := hcon
  have hHL : L ≤ H := le_of_mem_cComp hL
  have hHK : K ≤ H := le_of_mem_cComp hK
  have hHKp : Kp ≤ H := le_of_mem_cComp hKp
  set N : Subgroup ↥H := CFSG.solvableRadical ↥H with hN
  set π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N with hπ
  have h1 := cComp_ne_map_commutator_eq_bot hL hK hLK
  have h2 := cComp_ne_map_commutator_eq_bot hL hKp hLKp
  have hKc : (K.subgroupOf H).map π ≤ Subgroup.centralizer (((L.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h1
  have hKpc : (Kp.subgroupOf H).map π ≤
      Subgroup.centralizer (((L.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h2
  have hsub : L.subgroupOf H ≤ K.subgroupOf H ⊔ Kp.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hHK hHKp]
    exact fun x hx => hle hx
  have hL'le : (L.subgroupOf H).map π ≤ (K.subgroupOf H).map π ⊔ (Kp.subgroupOf H).map π := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hsub
  have hLc : (L.subgroupOf H).map π ≤ Subgroup.centralizer (((L.subgroupOf H).map π : Subgroup _) : Set _) :=
    hL'le.trans (sup_le hKc hKpc)
  have hLL : ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLc
  have hperf : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHL]
    exact perfect_of_mem_cComp hL
  have hker : L.subgroupOf H ≤ N := by
    have h3 : (L.subgroupOf H).map π = ⊥ := by
      conv_lhs => rw [← hperf]
      rw [Subgroup.map_commutator]
      exact hLL
    have h4 := (Subgroup.map_eq_bot_iff _).mp h3
    rwa [hπ, QuotientGroup.ker_mk'] at h4
  have hLrad : L ≤ solvRad H := by
    rw [solvRad_eq_map_solvableRadical]
    intro l hl
    exact ⟨⟨l, hHL hl⟩, hker hl, rfl⟩
  have := solvRad_isSolvable H
  have hsolv : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLrad)
      (Subgroup.inclusion_injective hLrad)
  exact not_isSolvable_of_mem_cComp hL hsolv

end Components

section Decomp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem conjSub_ne_of_decomp {K U₁ : Subgroup G} {s : G} (hSec : Sec8 K Zz U₁)
    (hsimple : IsSimpleGroup (KBar K))
    (hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (hs : s ∈ T)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hout : KbarInducesOuter K s) :
    conjSub s U₁ ≠ U₁ := by
  intro heq
  have hsU : s ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq heq
  have hsZ : s ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hs)
  set X : Subgroup G := K ⊔ Subgroup.zpowers s with hX
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) :=
    sup_le hSec.KZ (Subgroup.zpowers_le.mpr hsZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) :=
    sup_le hSec.KU (Subgroup.zpowers_le.mpr hsU)
  have hsX : s ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  refine hSec.false_of_twisted hsimple hQ' h168 hsK hout (secRho hXZ hXU ⟨s, hsX⟩) ?_
  intro k
  have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
  have hk' : s * (k : G) * s⁻¹ ∈ X := X.mul_mem (X.mul_mem hsX hkX) (X.inv_mem hsX)
  have e1 : hSec.rho k = secRho hXZ hXU ⟨k, hkX⟩ :=
    secRho_congr hSec.KZ hSec.KU hXZ hXU rfl
  have e2 : hSec.rho (conjAct K ⟨s, hsK⟩ k) = secRho hXZ hXU ⟨s * (k : G) * s⁻¹, hk'⟩ :=
    secRho_congr hSec.KZ hSec.KU hXZ hXU (conjAct_apply_coe' K ⟨s, hsK⟩ k)
  rw [e1, e2]
  have e3 : (⟨s * (k : G) * s⁻¹, hk'⟩ : ↥X) = ⟨s, hsX⟩ * ⟨k, hkX⟩ * ⟨s, hsX⟩⁻¹ := Subtype.ext rfl
  rw [e3, map_mul, map_mul, map_inv]

theorem inf_U₂_le_of_decomp {K U₁ U₂ : Subgroup G} {s : G} (hSec : Sec8 K Zz U₁)
    (hsimple : IsSimpleGroup (KBar K))
    (hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (hs : s ∈ T)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hout : KbarInducesOuter K s)
    (hU₂ : U₂ = conjSub s U₁) (hZU₂ : Zz ≤ U₂) : U₁ ⊓ U₂ ≤ Zz := by
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hU₂]
    exact le_normalizer_conjSub hsK hSec.KU
  have hKD : K ≤ Subgroup.normalizer ((U₁ ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSec.KU hk, hKU₂ hk⟩
  rcases hSec.irr (U₁ ⊓ U₂) (le_inf hSec.le hZU₂) inf_le_left hKD with h | h
  · exact h.le
  · exfalso
    have hle : U₁ ≤ U₂ := inf_eq_left.mp h
    have hcard : Nat.card U₂ ≤ Nat.card U₁ := by
      rw [hU₂, natCard_conjSub_eq]
    have h12 : U₁ = U₂ := Subgroup.eq_of_le_of_card_ge hle hcard
    exact conjSub_ne_of_decomp hSec hsimple hQ' h168 hs hsK hout (hU₂.symm.trans h12.symm)

theorem Setting146.mIdx_decomp_eq_six (S : Setting146 G T M) (c19 : Conc14619 T M)
    {L U₁ U₂ : Subgroup G} {s : G} (hL : L ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two L)
    (hdec : IsDecompUK T M L U₁ U₂ s) :
    mIdx (⁅uOfL22 T M, L⁆ ⊔ Zz) Zz = 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hL hL3 hdec
  have hsimple : IsSimpleGroup (KBar L) := (c19 (mcOf T) hG).2 L hL
  have hQK : pCoreOf 2 L ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL)
  have hQ' : ∀ p ∈ pCoreOf 2 L, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz := fun p hp w hw =>
    S.comm_mem_Z hG (hU₁U hw) (hQK hp)
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
  have hout : KbarInducesOuter L s := by
    rcases hdec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
    · exact ho
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  have hinf : U₁ ⊓ U₂ ≤ Zz :=
    inf_U₂_le_of_decomp hSec hsimple hQ' h168 hdec.mem.1 hdec.mem.2 hout hdec.conj hdec.Z₂
  have hZinf : U₁ ⊓ U₂ = Zz := le_antisymm hinf (le_inf hSec.le hdec.Z₂)
  have hcomm : ∀ x ∈ U₁, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (S.abelian.is_comm.comm ⟨x, hU₁U hx⟩ ⟨y, hU₂U hy⟩)
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂ hcomm
  rw [hZinf] at hc
  have h1 := Subgroup.relIndex_mul_card Zz U₁
  rw [inf_eq_left.mpr hSec.le, hSec.card] at h1
  have h2 : Nat.card U₂ = Nat.card U₁ := by rw [hdec.conj, natCard_conjSub_eq]
  have h3 := Subgroup.relIndex_mul_card Zz (U₁ ⊔ U₂)
  rw [inf_eq_left.mpr (hSec.le.trans le_sup_left)] at h3
  have hZpos : 0 < Nat.card Zz := Nat.card_pos
  have hc' : Nat.card ↥(U₁ ⊔ U₂) = 64 * Nat.card Zz := by
    refine Nat.eq_of_mul_eq_mul_right hZpos ?_
    rw [hc, h2, ← h1]
    ring
  have hrel : (quasithinOmegaOneCenter T).relIndex (U₁ ⊔ U₂) = 64 :=
    Nat.eq_of_mul_eq_mul_right hZpos (h3.trans hc')
  rw [hdec.sup]
  unfold mIdx
  rw [hrel]
  show padicValNat 2 (2 ^ 6) = 6
  exact padicValNat.prime_pow 6

end Decomp

theorem input14624ThreeA_proof : Input14624ThreeA := by
  intro G _ _ T M S _hB K U₁ U₂ s u hctx hall hne
  classical
  obtain ⟨c19, -, -, hK, c21, -, hdec, -⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  obtain ⟨Kp, hKp, hKpK, hkz, hL3K⟩ : ∃ Kp ∈ cComp (mcOf T), Kp ≠ K ∧
      perfectCore (mcOf T) = K ⊔ Kp ∧ KbarIsL3Two K := by
    rcases c21 with ⟨hper, -⟩ | ⟨⟨t, ht, htn, hper⟩, hL3⟩ | ⟨Kp, hKp, hKpK, -, -, hper, hL3, -⟩
    · exact absurd hper.symm hne
    · exact ⟨conjSub t K, map_conj_mem_cComp hK (hTH ht),
        fun heq => htn (A38.map_conj_eq_iff.mp heq), hper, hL3⟩
    · exact ⟨Kp, hKp, hKpK, hper, hL3⟩
  have hL3Kp : KbarIsL3Two Kp := by
    rcases (hall Kp hKp).1 with ⟨hper, -⟩ | ⟨-, hL3⟩ | ⟨_, _, _, -, -, _, hL3, -⟩
    · exact absurd (eq_of_le_cComp hKp hK (le_sup_left.trans (hkz.symm.trans hper).le)) hKpK.symm
    · exact hL3
    · exact hL3
  have hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp := by
    intro L hL
    have hle : L ≤ perfectCore (mcOf T) :=
      le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
    exact cComp_eq_of_le_sup hL hK hKp (hkz ▸ hle)
  obtain ⟨U₁', U₂', s', hdec'⟩ := (hall Kp hKp).2.1
  exact ⟨Kp, hKp, hKpK, hcomps, hkz, ⟨hL3K, hL3Kp⟩,
    S.mIdx_decomp_eq_six c19 hK hL3K hdec, S.mIdx_decomp_eq_six c19 hKp hL3Kp hdec'⟩

end CFSG.Quasithin
