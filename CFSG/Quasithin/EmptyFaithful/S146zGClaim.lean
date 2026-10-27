module

public import CFSG.Quasithin.EmptyFaithful.S146zGSurj
public import CFSG.Quasithin.EmptyFaithful.S146zGDich
public import CFSG.Quasithin.EmptyFaithful.S146zDHSide
public import CFSG.Quasithin.EmptyFaithful.S146zEInner

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section ClaimX

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem claim_X (S : Setting146 G T M)
    {K Kp U₁ U₂ : Subgroup G} {s : G} (cK : ThreeC.CCtx T M K U₁ U₂ s)
    (hKp : Kp ∈ cComp (mcOf T)) (hkz : perfectCore (mcOf T) = K ⊔ Kp)
    (hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥)
    {L : Subgroup G} (hLH : L ≤ mcOf T) (hLp : ⁅L, L⁆ = L) (hLs : IsSimpleGroup (KBar L))
    (hL168 : (pCoreOf 2 L).relIndex L = 168) (hLnKp : ¬ L ≤ Kp)
    {b : G} (hbH : b ∈ mcOf T) (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbL : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 (mcOf T)) :
    ∀ y ∈ U₁ ⊔ U₂, b * y * b⁻¹ * y⁻¹ ∈ Zz := by
  classical
  have hK := cK.hKc
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun h hh => by
    rw [S.normalizer_Z]; exact hh
  have hZc : mcOf T ≤ Subgroup.centralizer (Zz : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two S.card_Z]; exact hHZ
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have h4 : centralizerMod Zz (mcOf T) (uOfL22 T M) = pCoreOf 2 (mcOf T) :=
    S.lemma_14_5_15_four hG
  have hQ : ∀ c ∈ pCoreOf 2 (mcOf T), ∀ u ∈ uOfL22 T M, c * u * c⁻¹ * u⁻¹ ∈ Zz := by
    intro c hc u hu
    have hc' : c ∈ centralizerMod Zz (mcOf T) (uOfL22 T M) := by rw [h4]; exact hc
    exact hc'.2.2 u hu
  have hnormKp : cCompSpan (mcOf T) ≤ Subgroup.normalizer (Kp : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hKp)).mp
      (cComp_normal_span_of_le hKp).2
  have hKKp : K ≤ Subgroup.normalizer (Kp : Set G) := (le_cCompSpan hK).trans hnormKp
  have hKpcent : Kp ≤ Subgroup.centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    rw [← cK.hsup]
    refine Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc22K
    · exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hZc (hKpH hk)) z hz).symm
  have hKpU : ∀ kp ∈ Kp, ∀ w ∈ U₁ ⊔ U₂, kp * w * kp⁻¹ = w := by
    intro kp hkp w hw
    have := Subgroup.mem_centralizer_iff.mp (hKpcent hkp) w hw
    calc kp * w * kp⁻¹ = (w * kp) * kp⁻¹ := by rw [this]
      _ = w := by group
  have hLKp : L ≤ K ⊔ Kp := by
    have := le_perfectCore_of_perfect hLH hLp
    rwa [hkz] at this
  have hdec : ∀ l ∈ L, ∃ k ∈ K, ∃ kp ∈ Kp, l = k * kp := by
    intro l hl
    have hl' : l ∈ ((K ⊔ Kp : Subgroup G) : Set G) := hLKp hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKKp] at hl'
    obtain ⟨k, hk, kp, hkp, rfl⟩ := Set.mem_mul.mp hl'
    exact ⟨k, hk, kp, hkp, rfl⟩
  have hLZ : L ≤ Subgroup.normalizer (Zz : Set G) := hLH.trans hHZ
  have hKp₁ : Kp ≤ Subgroup.centralizer (U₁ : Set G) :=
    hKpcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hPZ : K ⊔ Kp ≤ Subgroup.normalizer (Zz : Set G) := (sup_le hKH hKpH).trans hHZ
  have hPU₁ : K ⊔ Kp ≤ Subgroup.normalizer (U₁ : Set G) :=
    sup_le cK.hSec.KU fun k hk => Subgroup.centralizer_le_normalizer _ (hKp₁ hk)
  have hLU₁ : L ≤ Subgroup.normalizer (U₁ : Set G) := hLKp.trans hPU₁
  have hU₁Z := cK.hSec.norm
  have hNn : ∀ l ∈ L, ∀ n ∈ centralizerMod Zz L U₁, l * n * l⁻¹ ∈ centralizerMod Zz L U₁ := by
    intro l hl n hn
    obtain ⟨hnL, hnN, hnu⟩ := hn
    refine ⟨L.mul_mem (L.mul_mem hl hnL) (L.inv_mem hl),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLZ hl) hnN) (Subgroup.inv_mem _ (hLZ hl)),
      fun u hu => ?_⟩
    have hu' : l⁻¹ * u * l ∈ U₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hLU₁ (L.inv_mem hl)) u).mp hu
      simpa using this
    have hc := hnu _ hu'
    have e : l * n * l⁻¹ * u * (l * n * l⁻¹)⁻¹ * u⁻¹ =
        l * (n * (l⁻¹ * u * l) * n⁻¹ * (l⁻¹ * u * l)⁻¹) * l⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLZ hl) _).mp hc
  rcases perfect_normal_dichotomy hLp hLs (centralizerMod_le_left _ _ _) hNn with hN | hN
  ·
    have hsurj := ThreeC.secRho_surjective hLZ hLU₁ hU₁Z cK.hSec.isElemAbelian_tilde
      cK.hSec.card_tilde hN hL168
    have hbU : b ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU hbH
    have hbZ : b ∈ Subgroup.normalizer (Zz : Set G) := hHZ hbH
    have hbUK : b ∈ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) :=
      cK.mem_normalizer_sup hbK hbU hbZ
    have hcen : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      have hkP : k ∈ K ⊔ Kp := Subgroup.mem_sup_left hk
      obtain ⟨l, hl⟩ := hsurj (secRho hPZ hPU₁ ⟨k, hkP⟩)
      obtain ⟨k', hk', kp', hkp', hlk⟩ := hdec (l : G) l.2
      have hk'P : k' ∈ K ⊔ Kp := Subgroup.mem_sup_left hk'
      have hkp'P : kp' ∈ K ⊔ Kp := Subgroup.mem_sup_right hkp'
      have hρk' : secRho hPZ hPU₁ ⟨k', hk'P⟩ = secRho hPZ hPU₁ ⟨k, hkP⟩ := by
        have e1 : secRho hLZ hLU₁ l = secRho hPZ hPU₁ ⟨(l : G), hLKp l.2⟩ :=
          secRho_congr hLZ hLU₁ hPZ hPU₁ rfl
        have e2 : (⟨(l : G), hLKp l.2⟩ : ↥(K ⊔ Kp)) = ⟨k', hk'P⟩ * ⟨kp', hkp'P⟩ :=
          Subtype.ext hlk
        have e3 : secRho hPZ hPU₁ ⟨kp', hkp'P⟩ = 1 :=
          ThreeC.secRho_eq_one_of_comm hPZ hPU₁ hU₁Z (fun u hu => by
            show kp' * u * kp'⁻¹ * u⁻¹ ∈ Zz
            rw [hKpU kp' hkp' u (Subgroup.mem_sup_left hu)]
            simp)
        rw [← hl, e1, e2, map_mul, e3, mul_one]
      have hkk'P : k'⁻¹ * k ∈ K ⊔ Kp :=
        (K ⊔ Kp).mul_mem ((K ⊔ Kp).inv_mem hk'P) hkP
      have hρ1 : secRho hPZ hPU₁ ⟨k'⁻¹ * k, hkk'P⟩ = 1 := by
        have e : (⟨k'⁻¹ * k, hkk'P⟩ : ↥(K ⊔ Kp)) = ⟨k', hk'P⟩⁻¹ * ⟨k, hkP⟩ := Subtype.ext rfl
        rw [e, map_mul, map_inv, hρk', inv_mul_cancel]
      have hkk' : ∀ w ∈ U₁, (k'⁻¹ * k) * w * (k'⁻¹ * k)⁻¹ * w⁻¹ ∈ Zz := fun w hw =>
        commutator_mem_of_secRho_eq_one hPZ hPU₁ hU₁Z hρ1 hw
      have hkk'K : k'⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hk') hk
      have ho : k'⁻¹ * k ∈ pCoreOf 2 K :=
        cK.hSec.centralizerMod_le cK.hsimple cK.hQ' ⟨hkk'K, cK.hSec.KZ hkk'K, hkk'⟩
      obtain ⟨c, hcdef⟩ : ∃ c : G, c = b * (k' * kp') * b⁻¹ * (k' * kp')⁻¹ := ⟨_, rfl⟩
      have hcQ : c ∈ pCoreOf 2 (mcOf T) := by
        rw [hcdef, ← hlk]; exact hbL (l : G) l.2
      obtain ⟨m, hmdef⟩ : ∃ m : G, m = kp' * (b * kp'⁻¹ * b⁻¹) := ⟨_, rfl⟩
      have hae : b * k' * b⁻¹ * k'⁻¹ = c * (k' * m * k'⁻¹) := by
        rw [hcdef, hmdef]; group
      have hmw : ∀ w ∈ U₁ ⊔ U₂, m * w * m⁻¹ = w := by
        intro w hw
        have hw' : b⁻¹ * w * b ∈ U₁ ⊔ U₂ := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbUK) w).mp hw
          simpa using this
        have h1 : kp'⁻¹ * (b⁻¹ * w * b) * kp'⁻¹⁻¹ = b⁻¹ * w * b :=
          hKpU kp'⁻¹ (Kp.inv_mem hkp') _ hw'
        have e : m * w * m⁻¹ =
            kp' * (b * (kp'⁻¹ * (b⁻¹ * w * b) * kp'⁻¹⁻¹) * b⁻¹) * kp'⁻¹ := by
          rw [hmdef]; group
        rw [e, h1]
        have e2 : b * (b⁻¹ * w * b) * b⁻¹ = w := by group
        rw [e2]
        exact hKpU kp' hkp' w hw
      have hatriv : ∀ w ∈ U₁, (b * k' * b⁻¹ * k'⁻¹) * w * (b * k' * b⁻¹ * k'⁻¹)⁻¹ * w⁻¹ ∈ Zz := by
        intro w hw
        have hw' : k'⁻¹ * w * k' ∈ U₁ := by
          have := (Subgroup.mem_normalizer_iff.mp (cK.hSec.KU (K.inv_mem hk')) w).mp hw
          simpa using this
        have hmw' := hmw _ (Subgroup.mem_sup_left hw')
        have e1 : (b * k' * b⁻¹ * k'⁻¹) * w * (b * k' * b⁻¹ * k'⁻¹)⁻¹ * w⁻¹ =
            c * (k' * (m * (k'⁻¹ * w * k') * m⁻¹) * k'⁻¹) * c⁻¹ * w⁻¹ := by
          rw [hae]; group
        rw [e1, hmw']
        have e2 : c * (k' * (k'⁻¹ * w * k') * k'⁻¹) * c⁻¹ * w⁻¹ = c * w * c⁻¹ * w⁻¹ := by group
        rw [e2]
        exact hQ c hcQ w (cK.hU₁U hw)
      have haK : b * k' * b⁻¹ * k'⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.mp hbK k').mp hk') (K.inv_mem hk')
      have haO : b * k' * b⁻¹ * k'⁻¹ ∈ pCoreOf 2 K :=
        cK.hSec.centralizerMod_le cK.hsimple cK.hQ' ⟨haK, cK.hSec.KZ haK, hatriv⟩
      have hbo : b * (k'⁻¹ * k) * b⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K hbK) _).mp ho
      have hconj : k' * (b * (k'⁻¹ * k) * b⁻¹ * (k'⁻¹ * k)⁻¹) * k'⁻¹ ∈ pCoreOf 2 K := by
        refine (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk') _).mp ?_
        exact (pCoreOf 2 K).mul_mem hbo ((pCoreOf 2 K).inv_mem ho)
      have e : b * k * b⁻¹ * k⁻¹ = (b * k' * b⁻¹ * k'⁻¹) *
          (k' * (b * (k'⁻¹ * k) * b⁻¹ * (k'⁻¹ * k)⁻¹) * k'⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 K).mul_mem haO hconj
    exact cK.trivial_of_centralizes S hbK hbU hbZ hcen
  ·
    exfalso
    apply hLnKp
    have hQN : Kp ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
      hKpH.trans (le_normalizer_pCoreOf 2 (mcOf T))
    have hcore := (cComp_commutator_perfectCore hKp (pCoreOf_le 2 (mcOf T))
      (isSolvable_pCoreOf_two (mcOf T)) hQN).2
    have hpQ : ∀ l ∈ L, l ∈ Kp ⊔ pCoreOf 2 (mcOf T) := by
      intro l hl
      obtain ⟨k, hk, kp, hkp, rfl⟩ := hdec l hl
      have hkw : ∀ w ∈ U₁, k * w * k⁻¹ * w⁻¹ ∈ Zz := by
        intro w hw
        have h1 := (hN hl).2.2 w hw
        have h3 : kp * w * kp⁻¹ = w := hKpU kp hkp w (Subgroup.mem_sup_left hw)
        have e : (k * kp) * w * (k * kp)⁻¹ * w⁻¹ = k * (kp * w * kp⁻¹) * k⁻¹ * w⁻¹ := by group
        rw [e, h3] at h1
        exact h1
      have hkQ : k ∈ pCoreOf 2 K :=
        cK.hSec.centralizerMod_le cK.hsimple cK.hQ' ⟨hk, cK.hSec.KZ hk, hkw⟩
      have hkQH : k ∈ pCoreOf 2 (mcOf T) :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) hkQ
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkQH) (Subgroup.mem_sup_left hkp)
    have hPcore : L ≤ perfectCore (Kp ⊔ pCoreOf 2 (mcOf T)) :=
      le_perfectCore_of_perfect hpQ hLp
    rwa [hcore] at hPcore

end ClaimX

section Comb

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem perfect_le_comp (S : Setting146 G T M) (c23 : Conc14623 T M)
    {K Kp U₁ U₂ V₁ V₂ : Subgroup G} {s t : G}
    (cK : ThreeC.CCtx T M K U₁ U₂ s) (cKp : ThreeC.CCtx T M Kp V₁ V₂ t)
    (hne : Kp ≠ K) (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    (hkz : perfectCore (mcOf T) = K ⊔ Kp)
    (hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥) (hc22Kp : ⁅⁅uOfL22 T M, Kp⁆, K⁆ = ⊥)
    {L : Subgroup G} (hLH : L ≤ mcOf T) (hLp : ⁅L, L⁆ = L) (hLs : IsSimpleGroup (KBar L))
    (hL168 : (pCoreOf 2 L).relIndex L = 168)
    {b : G} (hbH : b ∈ mcOf T) (hbnQ : b ∉ pCoreOf 2 (mcOf T))
    (hbL : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 (mcOf T))
    (hnsw : conjSub b K ≠ Kp) : L ≤ K ∨ L ≤ Kp := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hnK, hnKp⟩ := hcon
  have hK := cK.hKc
  have hKp := cKp.hKc
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := by
    have h1 : conjSub b K ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK hbH
    rcases hcomps _ h1 with h | h
    · exact mem_normalizer_of_conjSub_eq h
    · exact absurd h hnsw
  have hbKp : b ∈ Subgroup.normalizer (Kp : Set G) := by
    have h1 : conjSub b Kp ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hKp hbH
    rcases hcomps _ h1 with h | h
    · exfalso
      apply hne
      have : conjSub b Kp = conjSub b K := by rw [h, conjSub_eq_of_mem_normalizer hbK]
      exact (conjSub_inj b).mp this
    · exact mem_normalizer_of_conjSub_eq h
  have hkz' : perfectCore (mcOf T) = Kp ⊔ K := by rw [hkz, sup_comm]
  have h₁ := claim_X S cK hKp hkz hc22K hLH hLp hLs hL168 hnKp hbH hbK hbL
  have h₂ := claim_X S cKp hK hkz' hc22Kp hLH hLp hLs hL168 hnK hbH hbKp hbL
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  refine hbnQ (mem_pCoreOf_of_trivial3 S c23 cK hKp hcomps hbH
    (fun y hy => h₁ y (Subgroup.mem_sup_left hy)) (fun y hy => h₁ y (Subgroup.mem_sup_right hy)) ?_)
  refine trivial_on_cPart S hKpH hbH ?_
  intro y hy
  rw [cKp.hsup] at hy
  exact h₂ y hy

end Comb

end CFSG.Quasithin.ThreeD
