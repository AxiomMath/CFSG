module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Sylow
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Inspection
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

theorem oTwoUpper_sup_eq_of_isPGroup' {R Y : Subgroup G} (hR : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = oTwoUpper Y) :
    oTwoUpper (Y ⊔ R) = Y := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hY).symm
  have hx' : x ∈ ((Y ⊔ R : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY] at hx'
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hR ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hRY ht) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem centralizer_singleton_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp hx z rfl).symm

theorem centralizer_zpowers_eq (z : G) :
    Subgroup.centralizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  refine le_antisymm (Subgroup.centralizer_le (by simp)) ?_
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp hx z rfl).symm

variable [Finite G]

theorem relIndex_sup_eq_three {A P : Subgroup G} (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (h3 : (pCoreOf 2 A).relIndex A = 3) (hsyl : IsSylowTwoOf P (A ⊔ P)) :
    P.relIndex (A ⊔ P) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOP : pCoreOf 2 A ≤ P := by
    refine A4.le_of_normal_of_isSylowTwoOf hsyl
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans le_sup_left)]
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)
      (hPA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A))
  have h1 := Subgroup.relIndex_mul_card P (A ⊔ P)
  rw [inf_eq_left.mpr le_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (A ⊓ P) A
  rw [inf_eq_left.mpr inf_le_left] at h2
  have h3' := card_sup_mul_card_inf hPA
  rw [sup_comm, inf_comm] at h3'
  have hP0 : 0 < Nat.card P := Nat.card_pos
  have hAP0 : 0 < Nat.card ↥(A ⊓ P) := Nat.card_pos
  have heq : P.relIndex (A ⊔ P) = (A ⊓ P).relIndex A := by
    have h4 : P.relIndex (A ⊔ P) * (Nat.card P * Nat.card ↥(A ⊓ P)) =
        (A ⊓ P).relIndex A * (Nat.card P * Nat.card ↥(A ⊓ P)) := by
      calc P.relIndex (A ⊔ P) * (Nat.card P * Nat.card ↥(A ⊓ P))
          = (P.relIndex (A ⊔ P) * Nat.card P) * Nat.card ↥(A ⊓ P) := by ring
        _ = Nat.card ↥(A ⊔ P) * Nat.card ↥(A ⊓ P) := by rw [h1]
        _ = Nat.card A * Nat.card P := h3'.trans (mul_comm _ _)
        _ = (A ⊓ P).relIndex A * Nat.card ↥(A ⊓ P) * Nat.card P := by rw [h2]
        _ = (A ⊓ P).relIndex A * (Nat.card P * Nat.card ↥(A ⊓ P)) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hP0 hAP0) h4
  rw [heq]
  have hdvd : (A ⊓ P).relIndex A ∣ 3 :=
    h3 ▸ Subgroup.relIndex_dvd_of_le_left A (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 A) hOP)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    have hAP : A ≤ P := (Subgroup.relIndex_eq_one.mp (Subgroup.inf_relIndex_left A P ▸ h)).trans
      le_rfl
    have hA2 : IsPGroup 2 A := hsyl.2.1.to_le hAP
    have hO : pCoreOf 2 A = A := by
      refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 A) ?_
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hA2
    rw [hO, Subgroup.relIndex_self] at h3
    omega
  · exact h

theorem normalCore_eq_pCore {A : Type*} [Group A] [Finite A] {P : Subgroup A} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) : P.normalCore = Open.pCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.normalCore_normal P)
      (hP.to_le (Subgroup.normalCore_le P))
  · have hN : (Open.pCore 2 A).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rw [Subgroup.normal_le_normalCore]
    exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal (hP.toSylow hidx)

theorem nonempty_quotient_pCore_of_relIndex_eq_three {P K : Subgroup G} (hsyl : IsSylowTwoOf P K)
    (h3 : P.relIndex K = 3) (hN : ¬ K ≤ Subgroup.normalizer (P : Set G)) :
    Nonempty (↥K ⧸ Open.pCore 2 ↥K ≃* Equiv.Perm (Fin 3)) := by
  rcases CFSG.Quasithin.gold_normalCore_quotient_equiv (A := ↥K) (H := P.subgroupOf K) h3 with
    ⟨h, -⟩ | ⟨-, ⟨e⟩⟩
  · exfalso
    apply hN
    have hle := (P.subgroupOf K).normalCore_le
    have heq : (P.subgroupOf K).normalCore = P.subgroupOf K := by
      have : (P.subgroupOf K).FiniteIndex :=
        ⟨by rw [show (P.subgroupOf K).index = 3 from h3]; norm_num⟩
      have h1 := Subgroup.relIndex_mul_index hle
      rw [h, show (P.subgroupOf K).index = 3 from h3] at h1
      have h2 : (P.subgroupOf K).normalCore.relIndex (P.subgroupOf K) = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
    have hnorm : (P.subgroupOf K).Normal := heq ▸ Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsyl.1).mp hnorm
  · have hcore : (P.subgroupOf K).normalCore = Open.pCore 2 ↥K :=
      normalCore_eq_pCore (A4.isPGroup_subgroupOf_of_le hsyl.1 hsyl.2.1) hsyl.2.2
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans e⟩

end General

theorem exists_inM_centralizer {G : Type} [Group G] [Finite G] {T : Subgroup G} {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    ∃ Mz : Subgroup G, InM (Subgroup.centralizer ({z} : Set G)) Mz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hne : Subgroup.zpowers z ≠ ⊥ := fun h =>
    hz1 ((Subgroup.zpowers_eq_bot).mp h)
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge
    (⟨Subgroup.zpowers z, hne, hp, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)))
  exact ⟨M, hM, (centralizer_singleton_le_normalizer_zpowers z).trans hNM⟩

namespace Config15418

variable {G : Type} [Group G] {T : Subgroup G} (c : Config15418 G T)

@[expose] def G₁ : Subgroup G := c.Y ⊔ baum T

@[expose] def G₂ : Subgroup G := c.X₁ ⊔ baum T

@[expose] def I : Subgroup G := c.G₁ ⊔ c.G₂

theorem baum_le_G₁ : baum T ≤ c.G₁ := le_sup_right

theorem baum_le_G₂ : baum T ≤ c.G₂ := le_sup_right

theorem G₁_le_I : c.G₁ ≤ c.I := le_sup_left

theorem G₂_le_I : c.G₂ ≤ c.I := le_sup_right

theorem baum_le_I : baum T ≤ c.I := c.baum_le_G₁.trans c.G₁_le_I

theorem Y_le_I : c.Y ≤ c.I := le_sup_left.trans c.G₁_le_I

theorem X₁_le_I : c.X₁ ≤ c.I := le_sup_left.trans c.G₂_le_I

theorem baum_le_normalizer_Y : baum T ≤ Subgroup.normalizer (c.Y : Set G) :=
  inf_le_left.trans c.le_normalizer_Y

theorem baum_le_normalizer_X₁ : baum T ≤ Subgroup.normalizer (c.X₁ : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := c.dataX
  exact h

theorem le_normalizer_G₁ : T ≤ Subgroup.normalizer (c.G₁ : Set G) := fun _ hu =>
  F6.mem_normalizer_sup (c.le_normalizer_Y hu)
    ((Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)) hu)

theorem oTwoUpper_G₁ [Finite G] (hT : IsPGroup 2 T) : oTwoUpper c.G₁ = c.Y :=
  oTwoUpper_sup_eq_of_isPGroup' (hT.to_le inf_le_left) c.baum_le_normalizer_Y c.famY.eq_oTwoUpper

theorem oTwoUpper_G₂ [Finite G] (hT : IsPGroup 2 T) : oTwoUpper c.G₂ = c.X₁ :=
  oTwoUpper_sup_eq_of_isPGroup' (hT.to_le inf_le_left) c.baum_le_normalizer_X₁ c.dataX.2.1

theorem I_le_centralizer_E₀ : c.I ≤ Subgroup.centralizer (c.E₀ : Set G) := by
  have hS : baum T ≤ Subgroup.centralizer (c.E₀ : Set G) := c.baum_le_centralizer_E₀
  have hY : c.Y ≤ Subgroup.centralizer (c.E₀ : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_left.trans inf_le_right
  have hX : c.X₁ ≤ Subgroup.centralizer (c.E₀ : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right.trans inf_le_right
  exact sup_le (sup_le hY hS) (sup_le hX hS)

variable [Finite G]

section Hyp

variable (H : Hyp15418 G T)
include H

theorem isSylowTwoOf_I : IsSylowTwoOf (baum T) c.I :=
  A4.isSylowTwoOf_mono (c.isSylowTwoOf_baum H) c.baum_le_I c.I_le_centralizer_E₀

theorem isSylowTwoOf_G₁ : IsSylowTwoOf (baum T) c.G₁ :=
  A4.isSylowTwoOf_mono (c.isSylowTwoOf_I H) c.baum_le_G₁ c.G₁_le_I

theorem isSylowTwoOf_G₂ : IsSylowTwoOf (baum T) c.G₂ :=
  A4.isSylowTwoOf_mono (c.isSylowTwoOf_I H) c.baum_le_G₂ c.G₂_le_I

theorem relIndex_G₁ : (baum T).relIndex c.G₁ = 3 :=
  relIndex_sup_eq_three c.baum_le_normalizer_Y c.three (c.isSylowTwoOf_G₁ H)

theorem relIndex_G₂ : (baum T).relIndex c.G₂ = 3 :=
  relIndex_sup_eq_three c.baum_le_normalizer_X₁ c.dataX.2.2.2.1 (c.isSylowTwoOf_G₂ H)

theorem not_G₁_le_normalizer : ¬ c.G₁ ≤ Subgroup.normalizer (baum T : Set G) := fun h =>
  c.not_Y_le_M₂ H ((le_sup_left.trans h).trans (H.h16 c.M₂ c.inM₂))

theorem not_G₂_le_normalizer : ¬ c.G₂ ≤ Subgroup.normalizer (baum T : Set G) := fun h =>
  c.not_X₁_le_M₁ H ((le_sup_left.trans h).trans (H.h16 c.M₁ c.inM₁))

theorem quotient_G₁ : Nonempty (↥c.G₁ ⧸ Open.pCore 2 ↥c.G₁ ≃* Equiv.Perm (Fin 3)) :=
  nonempty_quotient_pCore_of_relIndex_eq_three (c.isSylowTwoOf_G₁ H) (c.relIndex_G₁ H)
    (c.not_G₁_le_normalizer H)

theorem quotient_G₂ : Nonempty (↥c.G₂ ⧸ Open.pCore 2 ↥c.G₂ ≃* Equiv.Perm (Fin 3)) :=
  nonempty_quotient_pCore_of_relIndex_eq_three (c.isSylowTwoOf_G₂ H) (c.relIndex_G₂ H)
    (c.not_G₂_le_normalizer H)

theorem G₁_inf_G₂ : c.G₁ ⊓ c.G₂ = baum T := by
  have hle : baum T ≤ c.G₁ ⊓ c.G₂ := le_inf c.baum_le_G₁ c.baum_le_G₂
  have htower := Subgroup.relIndex_mul_relIndex (baum T) (c.G₁ ⊓ c.G₂) c.G₁ hle inf_le_left
  rw [c.relIndex_G₁ H] at htower
  rcases (Nat.dvd_prime Nat.prime_three).mp ⟨_, htower.symm⟩ with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at htower
    have h1 : (c.G₁ ⊓ c.G₂).relIndex c.G₁ = 1 := by omega
    have hG : c.G₁ ≤ c.G₂ := (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    have hG₂ : c.G₂ ≤ c.M₂ := sup_le (c.X₁_le.trans c.le_X) (inf_le_left.trans c.T_le_M₂)
    exact c.not_Y_le_M₂ H ((le_sup_left.trans hG).trans hG₂)

theorem isGoldschmidtTripleIn : F6.IsGoldschmidtTripleIn c.I c.G₁ c.G₂ :=
  ⟨rfl, c.quotient_G₁ H, c.quotient_G₂ H, (c.G₁_inf_G₂ H) ▸ c.isSylowTwoOf_I H⟩

theorem E₁_le_pCoreOf_G₁ : c.E₁ ≤ pCoreOf 2 c.G₁ := by
  have hE₁S : c.E₁ ≤ baum T := inf_le_left.trans (eOf_le_baum T)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hE₁S.trans c.baum_le_G₁) ?_
    (H.hyp.sylow.1.to_le (hE₁S.trans inf_le_left))
  have hY : c.Y ≤ Subgroup.centralizer (c.E₁ : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right
  have hS : baum T ≤ Subgroup.centralizer (c.E₁ : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  exact (sup_le hY hS).trans (Subgroup.centralizer_le_normalizer _)

theorem pCoreOf_G₁_ne : pCoreOf 2 c.G₁ ≠ pCoreOf 2 c.G₂ := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : pCoreOf 2 c.G₁ ≠ ⊥ := by
    intro hbot
    have h := c.E₁_le_pCoreOf_G₁ H
    rw [hbot] at h
    have h4 := c.card_of_relIndex_eq_two H (show c.E₁ ≤ eOf T from inf_le_left) (c.relIndex_E₁ H)
    rw [le_bot_iff.mp h, Subgroup.card_bot] at h4
    omega
  apply hne
  refine c.eq_bot_of_le_normalizer H (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.G₁) ?_ ?_
  · refine sup_le ((le_sup_left : c.Y ≤ c.G₁).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.G₁)) ?_
    exact c.le_normalizer_G₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  · rw [heq]
    exact (le_sup_left : c.X₁ ≤ c.G₂).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.G₂)

theorem pCoreOf_I_ne_bot : pCoreOf 2 c.I ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE₀S : c.E₀ ≤ baum T := (inf_le_left.trans inf_le_left).trans (eOf_le_baum T)
  have h : c.E₀ ≤ pCoreOf 2 c.I :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hE₀S.trans c.baum_le_I)
      (c.I_le_centralizer_E₀.trans (Subgroup.centralizer_le_normalizer _))
      (H.hyp.sylow.1.to_le (hE₀S.trans inf_le_left))
  intro hbot
  exact c.E₀_ne_bot H (le_bot_iff.mp (hbot ▸ h))

theorem sqtk_I : CFSG.SectionRank.IsSQTKCat ↥c.I :=
  isSQTKCat_of_hyp H.hyp (c.pCoreOf_I_ne_bot H)

theorem I_inf_centralizer_Z :
    c.I ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = baum T := by
  apply le_antisymm
  · rw [H.h8]
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp (c.isSylowTwoOf_I H)).2.2
    exact hmax _ inf_le_left (H.hyp.sylow.1.to_le inf_le_right) (le_inf c.baum_le_I inf_le_left)
  · exact le_inf c.baum_le_I (inf_le_left.trans (le_centralizer_omegaOneCenter T))

theorem normalizer_le : c.I ⊓ Subgroup.normalizer (baum T : Set G) ≤ baum T := fun _ hg =>
  c.normalizer_inf_centralizer_le H ⟨hg.2, c.I_le_centralizer_E₀ hg.1⟩

theorem lemma115Hyp {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) {Mz : Subgroup G}
    (hMz : InM (Subgroup.centralizer ({z} : Set G)) Mz) : Lemma115Hyp c.I (baum T) Mz z := by
  have hE₀T : c.E₀ ≤ T := (inf_le_left.trans inf_le_left).trans (eOf_le T)
  have hE₀C : c.E₀ ≤ Subgroup.centralizer (c.E₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact eOf_mul_comm hb.1.1 ha.1.1
  have hTE₀ := c.T_inf_centralizer_E₀ H
  have h := (H.h17 c.E₀ (Subgroup.centralizer (c.E₀ : Set G)) c.I (c.E₀_ne_bot H) hE₀T
    (sup_le hE₀C le_rfl) (Subgroup.centralizer_le_normalizer _) (hTE₀ ▸ c.isSylowTwoOf_baum H)
    (hTE₀ ▸ c.baum_le_I) c.I_le_centralizer_E₀).1 z hz hz1 Mz hMz
  rwa [hTE₀] at h

theorem oddCoreIn_I_eq_bot : oddCoreIn c.I = ⊥ := by
  obtain ⟨⟨a, haZY⟩, ha1, -⟩ := (Nat.card_eq_two_iff'
    (1 : ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G)))).mp
    (card_Z_inf H c.famY)
  obtain ⟨⟨b, hbZX⟩, hb1, -⟩ := (Nat.card_eq_two_iff'
    (1 : ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G)))).mp
    (card_Z_inf H c.famX)
  have haZ : a ∈ quasithinOmegaOneCenter T := haZY.1
  have hbZ : b ∈ quasithinOmegaOneCenter T := hbZX.1
  have hba : b ≠ a := by
    intro h
    have hmem : a ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ⊓
        Subgroup.centralizer (c.Y : Set G) := ⟨⟨haZ, h ▸ hbZX.2⟩, haZY.2⟩
    rw [c.Z_inf_X_inf_Y H, Subgroup.mem_bot] at hmem
    exact ha1 (Subtype.ext hmem)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hab : b ≠ a := hba
  have habZ : a * b ∈ quasithinOmegaOneCenter T := (quasithinOmegaOneCenter T).mul_mem haZ hbZ
  have hab1 : a * b ≠ 1 := by
    intro h
    have ha2 : a * a = 1 := by rw [← sq]; exact (mem_quasithinOmegaOneCenter_iff.mp haZ).2.2
    apply hab
    calc b = a * a * b := by rw [ha2, one_mul]
      _ = a := by rw [mul_assoc, h, mul_one]
  obtain ⟨Ma, hMa⟩ := exists_inM_centralizer haZ ha1'
  obtain ⟨Mb, hMb⟩ := exists_inM_centralizer hbZ hb1'
  obtain ⟨Mab, hMab⟩ := exists_inM_centralizer habZ hab1
  have hinv_a := (c.lemma115Hyp H haZ ha1' hMa).inverts_oddCoreIn
  have hinv_b := (c.lemma115Hyp H hbZ hb1' hMb).inverts_oddCoreIn
  have hfix := (c.lemma115Hyp H habZ hab1 hMab).oddCoreIn_properties.2.1
  rw [eq_bot_iff, ← hfix]
  intro y hy
  refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have h1 : (a * b)⁻¹ * y * (a * b) = y := by
    calc (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
      _ = b⁻¹ * y⁻¹ * b := by rw [hinv_a y hy]
      _ = (b⁻¹ * y * b)⁻¹ := by group
      _ = y := by rw [hinv_b y hy, inv_inv]
  calc a * b * y = a * b * ((a * b)⁻¹ * y * (a * b)) := by rw [h1]
    _ = y * (a * b) := by group

theorem charTwo_centralizer {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    CharTwo (c.I ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Mz, hMz⟩ := exists_inM_centralizer hz hz1
  have h := c.lemma115Hyp H hz hz1 hMz
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hzK : Subgroup.zpowers z ≤ c.I ⊓ Mz := by
    rw [Subgroup.zpowers_le]
    exact ⟨h.z_mem_H, hMz.2 (Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx])⟩
  have hc := h.charTwo_inf.inf_centralizer hzK hp
  rw [centralizer_zpowers_eq] at hc
  have heq : c.I ⊓ Mz ⊓ Subgroup.centralizer ({z} : Set G) =
      c.I ⊓ Subgroup.centralizer ({z} : Set G) :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans hMz.2)) inf_le_right)
  rwa [heq] at hc

theorem thompson₁ : ⁅oTwoUpper c.G₁, thompsonJ (baum T)⁆ = oTwoUpper c.G₁ := by
  rw [c.oTwoUpper_G₁ H.hyp.sylow.1, thompsonJ_baum]
  exact c.famY.2

theorem thompson₂ : ⁅oTwoUpper c.G₂, thompsonJ (baum T)⁆ = oTwoUpper c.G₂ := by
  rw [c.oTwoUpper_G₂ H.hyp.sylow.1, thompsonJ_baum]
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := c.dataX
  exact h

theorem inspectionData :
    InspectionData15418 c.I c.G₁ c.G₂ (baum T) T (quasithinOmegaOneCenter T) where
  sqtk := c.sqtk_I H
  triple := c.isGoldschmidtTripleIn H
  inf_eq := c.G₁_inf_G₂ H
  pCoreOf_ne := c.pCoreOf_G₁_ne H
  oddCoreIn_eq_bot := c.oddCoreIn_I_eq_bot H
  le := (omegaOneCenter_le_eOf' T).trans (eOf_le_baum T)
  card := card_Z H
  sq_eq_one := fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  charTwo_centralizer := fun z hz hz1 => c.charTwo_centralizer H hz hz1
  centralizer_eq := c.I_inf_centralizer_Z H
  component := fun L hL z hz hz1 => by
    obtain ⟨Mz, hMz⟩ := exists_inM_centralizer hz hz1
    exact ((c.lemma115Hyp H hz hz1 hMz).component_action hL).2.1
  thompson₁ := c.thompson₁ H
  thompson₂ := c.thompson₂ H
  isPGroup := H.hyp.sylow.1
  le_T := inf_le_left
  relIndex_eq_two := c.relIndex_baum H
  le_normalizer := c.le_normalizer_G₁
  omegaOneCenter_le := le_rfl
  rank := c.exists_isElemAbelian_card H

end Hyp

end Config15418

end CFSG.Quasithin.EmptyFaithfulMultiple
