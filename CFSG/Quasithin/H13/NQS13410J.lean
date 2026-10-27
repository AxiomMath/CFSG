module

public import CFSG.Quasithin.H13.NQS13410F
public import CFSG.Quasithin.H13.NQS13410H
public import CFSG.Quasithin.H13.NQS13410I
public import CFSG.Quasithin.H13.U3S13227
public import CFSG.Quasithin.EmptyFaithful.Der6DAux

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
@[expose] def centQuotOf (K Q W : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ K ⊓ normalizer (W : Set G) ∧ ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, haQ⟩ ⟨hb, hbQ⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_⟩
    have h1 := (mem_normalizer_iff.mp (mem_inf.1 ha).2 _).mp (hbQ q hq)
    have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
        a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by group
    rw [e]
    exact mul_mem h1 (haQ q hq)
  inv_mem' := by
    rintro a ⟨ha, haQ⟩
    refine ⟨inv_mem ha, fun q hq => ?_⟩
    have h1 := (mem_normalizer_iff.mp (inv_mem (mem_inf.1 ha).2) _).mp (haQ q hq)
    have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a⁻¹ * (a * q * a⁻¹ * q⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

omit [Finite G] in
theorem mem_centQuotOf {K Q W : Subgroup G} {k : G} :
    k ∈ centQuotOf K Q W ↔
      k ∈ K ⊓ normalizer (W : Set G) ∧ ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W :=
  Iff.rfl

omit [Finite G] in
theorem centQuotOf_conj {K Q W : Subgroup G} (hKW : K ≤ normalizer (W : Set G))
    (hKQ : K ≤ normalizer (Q : Set G)) :
    ∀ g ∈ K, ∀ n ∈ centQuotOf K Q W, g * n * g⁻¹ ∈ centQuotOf K Q W := by
  intro g hg n hn
  obtain ⟨hn, hnQ⟩ := mem_centQuotOf.1 hn
  have hgKW : g ∈ K ⊓ normalizer (W : Set G) := mem_inf.2 ⟨hg, hKW hg⟩
  refine mem_centQuotOf.2 ⟨mul_mem (mul_mem hgKW hn) (inv_mem hgKW), fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem (hKQ hg)) q).mp hq
  have h1 := (mem_normalizer_iff.mp (hKW hg) _).mp (hnQ _ hq')
  have e : g * n * g⁻¹ * q * (g * n * g⁻¹)⁻¹ * q⁻¹ =
      g * (n * (g⁻¹ * q * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * q * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h1

theorem not_a5_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hK5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    [IsMulCommutative ↥W] (hW5 : AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hWR : W ≤ reducedAggregate (K ⊔ T)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hRdef
  set Q := pCoreOf 2 (K ⊔ T) with hQdef
  obtain ⟨-, ⟨hTK, -, -, huniqK⟩, ⟨⟨V₀, hV₀⟩, hK3⟩, -⟩ := h1332 G T L S.h13 K hKf
  have hKperf : ⁅K, K⁆ = K := hKf.1.2.1.2.1
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := (hK3 V₀ hV₀).2.2.1.quasisimple
  have hZK := center_eq_bot_of_simple_types (Or.inl hK5)
  have hred := twoReduced_R2 (K ⊔ T)
  have hWe : IsElemAbelian 2 W := ⟨‹_›, fun w hw => hred.2.2.1.2 w (hWR hw)⟩
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hWe.2 w w.2)⟩
  have hWQ : W ≤ Q := hWR.trans (R2_le_pCoreOf (K ⊔ T))
  have hQC : Q ≤ centralizer (W : Set G) :=
    (pCoreOf_le_centralizer_R2 (K ⊔ T)).trans (centralizer_le hWR)
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  obtain ⟨R5⟩ := A5.exists_rawData5_of_nat hKW hW5
  have hW1 : W ≠ ⊥ := by
    intro h
    have h16 := Nat.card_congr R5.ψ.toEquiv
    rw [A5.card_W5, h, Subgroup.card_bot] at h16
    omega
  have hNL : normalizer (W : Set G) ≤ normalizer (K : Set G) := by
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨W, hW1, hW2, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
    have := huniqK M' hM' ((sup_le hKW hTW).trans hle)
    exact this ▸ hle
  obtain ⟨F⟩ := A5.exists_frame R5 hNL S.h13.sylow.1 hTW hsyl
  obtain ⟨g, hgK, hg⟩ := (F.image_L A5Model.c3p).2 A5.c3p_sign
  obtain ⟨⟨y, hyNW⟩, ⟨m, hm, hym⟩, hρy, j, hyj⟩ :=
    exists_odd_part F.ρ g (by rw [hg]; exact A5.c3p_cube)
  rw [hg] at hρy
  have hym' : y ^ m = 1 := hym
  have hyK : y ∈ K := by
    have hyj' : y = (g : G) ^ j := hyj
    rw [hyj']
    exact pow_mem hgK j
  have hyfix : ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
    intro w hwW hwT
    have hfix : ∀ σ : Perm (Fin 5), A5.InK4 σ →
        A5Model.pact σ (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      intro σ hσ
      obtain ⟨t, htT, rfl⟩ := F.K4_T σ hσ
      rw [← F.equiv t ⟨w, hwW⟩]
      congr 1
      apply Subtype.ext
      rw [A5.conjAct_val]
      have := mem_centralizer_iff.mp hwT (t : G) htT
      calc (t : G) * w * (t : G)⁻¹ = w * t * (t : G)⁻¹ := by rw [this]
        _ = w := by group
    have hy : A5Model.pact (F.ρ ⟨y, hyNW⟩) (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      rw [hρy]
      rcases A5.fixed_K4 _ hfix with h1 | h4
      · rw [h1, map_one]
      · rw [h4]
        exact A5Model.pact_W4 A5.c3p_four
    rw [← F.equiv ⟨y, hyNW⟩ ⟨w, hwW⟩] at hy
    have h2 := congrArg Subtype.val (F.ψ.injective hy)
    rw [A5.conjAct_val] at h2
    have h2' : y * w * y⁻¹ = w := h2
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [h2']
  have hyZ := mem_centralizer_Z_of hTW hZW hyK hyfix
  have hyW : y ∉ centralizer (W : Set G) := fun h => by
    have h1 := A5.Frame.rho_eq_one_of_mem F ⟨y, hyNW⟩ h
    rw [hρy] at h1
    exact absurd h1 (by decide)
  have hy3 : y ^ 3 = 1 := by
    have h3 : F.ρ (⟨y, hyNW⟩ ^ 3) = 1 := by rw [map_pow, hρy, A5.c3p_cube]
    have h3C : y ^ 3 ∈ centralizer (W : Set G) := by
      simpa using A5.Frame.mem_centralizer_of_rho F (⟨y, hyNW⟩ ^ 3) h3
    have h1 : y ^ 3 ∈ A6.o2Z K := by rw [ho2Z]; exact mem_inf.2 ⟨pow_mem hyK 3, h3C⟩
    obtain ⟨s, hs⟩ :=
      LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, o2Z_le_pCoreOf_of_center hZK h1⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have := congrArg Subtype.val hs
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym', one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyW (h ▸ one_mem _)
  have hyL1 : y ∈ L₁ := mem_L1_of_pow_three h1332 h1228 S he hyZ (k := 1) (by simpa using hy3)
  have hL1K' : L₁ ≤ K :=
    L1_le_of_pow_three h1332 h1228 S he hL1K hyK hyZ hy1 (k := 1) (by simpa using hy3)
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRN : R ≤ normalizer (W : Set G) := hRT.trans hTW
  have hQ2 : IsPGroup 2 ↥Q := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl
  have hKTQ : K ⊔ T ≤ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQR : Q ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (sup_le (hL1K'.trans (le_sup_left.trans hKTQ)) (le_sup_right.trans hKTQ)) hQ2
  have hWR' : W ≤ R := hWQ.trans hQR
  have hyR : y ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
  have hyQ : y ∈ normalizer (Q : Set G) := hKTQ (mem_sup_left hyK)
  have hRK4 : ∀ r : ↥(normalizer (W : Set G)), (r : G) ∈ R → A5.InK4 (F.ρ r) := by
    intro r hr
    have hyr : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyR r).mp hr
    have h2 := F.T_D (⟨y, hyNW⟩ * r * ⟨y, hyNW⟩⁻¹) (hRT hyr)
    rw [map_mul, map_mul, map_inv, hρy] at h2
    exact inK4_of_conj_c3p _ (F.T_D r (hRT hr)) h2
  have hJ : thompsonJ R ≤ R ⊓ centralizer (W : Set G) :=
    iSup₂_le fun A hA => le_inf hA.1
      (a5Frame_le_centralizer_of_isMaxElemAbelian F hWe hWR' hRN hRK4 hA)
  have hCK2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
    rw [← ho2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  have hTQ : T ⊓ centralizer (W : Set G) = Q :=
    U3.inf_centralizer_eq_pCoreOf_sup hTsyl hTK hKW hTW (le_centralizer_iff.mp hQC) hCK2
  have hRCQ : R ⊓ centralizer (W : Set G) ≤ Q := fun r hr => by
    rw [← hTQ]
    exact mem_inf.2 ⟨hRT (mem_inf.1 hr).1, (mem_inf.1 hr).2⟩
  have hQeq : R ⊓ centralizer (W : Set G) = Q := le_antisymm hRCQ (le_inf hQR hQC)
  have hBQ : baum R = baum Q := by rw [baum_eq_baum_centralizer hWe hWR' hJ, hQeq]
  have hAQ : ∀ A, IsMaxElemAbelian R A → IsMaxElemAbelian Q A := fun A hA =>
    ⟨(B6.le_thompsonJ hA).trans (hJ.trans hRCQ), hA.2.1, fun B hB hBe =>
      hA.2.2 B (hB.trans hQR) hBe⟩
  have hRR1 : R = U3.r1Of T L V := (U3.s134Plus_L1 S he).pCoreOf_eq_r1Of
  have hcontra : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ T → L ⊔ T ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → False := by
    intro X hX1 hXT hLX hKX
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨X, hX1, S.h13.sylow.1.to_le hXT, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
    have hM := S.uniqueM.2 M' ⟨hM', hLX.trans hle⟩
    exact hKM (hKX.trans (hM ▸ hle))
  rcases U3.s134_lemma13_2_2_seven hC137 h1332 S with ⟨C, hCB, hC1, hCchar, hCN⟩ | hB
  ·
    rw [← hRR1, hBQ] at hCB hCchar
    have := hCchar
    refine hcontra C hC1 (hCB.trans (inf_le_left.trans hQT)) hCN ?_
    have h2 : normalizer (baum Q : Set G) ≤ normalizer (C : Set G) := by
      have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (C.subgroupOf (baum Q))
      rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at h3
    exact (le_sup_left.trans hKTQ).trans ((normalizer_le_normalizer_baum Q).trans h2)
  ·
    have hc16 : (centralizer ({y} : Set G)).relIndex R ≤ 16 :=
      s134_relIndex_R_le_sixteen S hB hyL1 hy3
    have hRQn : R ≤ normalizer (Q : Set G) := hRT.trans (le_sup_right.trans hKTQ)
    have hRCy : R ⊓ centralizer ({y} : Set G) ≤ Q := by
      intro r hr
      obtain ⟨hrR, hry⟩ := mem_inf.1 hr
      have hrN : r ∈ normalizer (W : Set G) := hRN hrR
      have hcomm : F.ρ ⟨r, hrN⟩ * A5Model.c3p = A5Model.c3p * F.ρ ⟨r, hrN⟩ := by
        have h1 : (⟨r, hrN⟩ * ⟨y, hyNW⟩ : ↥(normalizer (W : Set G))) = ⟨y, hyNW⟩ * ⟨r, hrN⟩ :=
          Subtype.ext (mem_centralizer_singleton_iff.mp hry)
        have h2 := congrArg F.ρ h1
        rwa [map_mul, map_mul, hρy] at h2
      exact hRCQ (mem_inf.2 ⟨hrR, A5.Frame.mem_centralizer_of_rho F ⟨r, hrN⟩
        (k4_comm_c3p _ (hRK4 ⟨r, hrN⟩ hrR) hcomm)⟩)
    have hsup : Q ⊔ (R ⊓ centralizer ({y} : Set G)) = Q := sup_eq_left.2 hRCy
    have hcRQ : (centralizer ({y} : Set G)).relIndex R =
        Q.relIndex R * (centralizer ({y} : Set G)).relIndex Q := by
      have h1 := U3.relIndex_centralizer_eq_mul (x := y) hQR hRQn
      rwa [hsup] at h1
    have hRQ : ¬ R ≤ Q := by
      intro hle
      obtain ⟨s, hsT, hs⟩ := F.K4_T A5Model.pa (Or.inr (Or.inl rfl))
      set g₁ := (s : G) * y * (s : G)⁻¹ * y⁻¹ with hg₁
      have hg₁L1 : g₁ ∈ L₁ :=
        mul_mem ((mem_normalizer_iff.mp (U3.s134_T_le_normalizer_L1 S hsT) y).mp hyL1)
          (inv_mem hyL1)
      have hg₁N : g₁ ∈ normalizer (W : Set G) :=
        mul_mem (mul_mem (mul_mem s.2 hyNW) (inv_mem s.2)) (inv_mem hyNW)
      have hρg₁ : F.ρ ⟨g₁, hg₁N⟩ =
          A5Model.pa * A5Model.c3p * A5Model.pa⁻¹ * A5Model.c3p⁻¹ := by
        have e : (⟨g₁, hg₁N⟩ : ↥(normalizer (W : Set G))) =
            s * ⟨y, hyNW⟩ * s⁻¹ * ⟨y, hyNW⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hs, hρy]
      obtain ⟨a, m₁, hm₁, hn₁⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₁).ne'
      have hua : (g₁ ^ m₁) ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm m₁, ← hn₁, pow_orderOf_eq_one]
      have huL1 : g₁ ^ m₁ ∈ L₁ := pow_mem hg₁L1 _
      have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
      have huV : g₁ ^ m₁ ∈ normalizer (V : Set G) := S.frame.L_le (hL1L huL1)
      have hρu : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ∈ A6.K4L := by
        have h16 : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ^ 16 = 1 := by
          refine U3.pow_sixteen_of_two_pow (k := a) ?_
          rw [← map_pow]
          have h1 : (⟨g₁ ^ m₁, huV⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ a = 1 :=
            Subtype.ext (by simpa using hua)
          rw [h1, map_one]
        exact U3.A4_two_K4 _ (U3.s134_rho_L1 S huV huL1) h16
      have huR : g₁ ^ m₁ ∈ R := s134_pCoreOf_L1_le_R S
        ((U3.s134Plus_L1 S he).mem_pCoreOf_of_K4 (x := ⟨g₁ ^ m₁, huV⟩) huL1 hρu)
      have h1 := A5.Frame.rho_eq_one_of_mem F (⟨g₁, hg₁N⟩ ^ m₁) (hQC (hle huR))
      rw [map_pow, hρg₁] at h1
      obtain ⟨hk1, -, hk2⟩ := pa_comm_c3p
      obtain ⟨b, hb⟩ := hm₁
      rw [hb, pow_succ, pow_mul, hk2, one_pow, one_mul] at h1
      exact hk1 h1
    have hRQ4 : 4 ≤ Q.relIndex R := by
      have h1 := U3.relIndex_sup_eq_one_or hy3 hR2 hQR hRQn hyQ hyR
      rw [hsup] at h1
      exact h1.resolve_left fun h => hRQ (relIndex_eq_one.mp h)
    have hcW : 4 ≤ (centralizer ({y} : Set G)).relIndex W :=
      U3.four_le_relIndex_centralizer hy3 hyNW hW2 fun h => hyW (mem_centralizer_iff.mpr
        fun w hw => mem_centralizer_singleton_iff.mp (h hw))
    have hcQ4 : 4 ≤ (centralizer ({y} : Set G)).relIndex Q :=
      hcW.trans (U3.relIndex_centralizer_le hWQ)
    have hcQ : (centralizer ({y} : Set G)).relIndex Q = 4 := by
      have h1 : Q.relIndex R * (centralizer ({y} : Set G)).relIndex Q ≤ 16 := by
        rw [← hcRQ]
        exact hc16
      have h2 : (centralizer ({y} : Set G)).relIndex Q ≤ 4 := by nlinarith
      omega
    have hcW4 : (centralizer ({y} : Set G)).relIndex W = 4 :=
      le_antisymm ((U3.relIndex_centralizer_le hWQ).trans hcQ.le) hcW
    have hQn : Q ≤ normalizer (W : Set G) := hQT.trans hTW
    have hQWC : Q ≤ W ⊔ (Q ⊓ centralizer ({y} : Set G)) := by
      have h1 := U3.relIndex_centralizer_eq_mul (x := y) hWQ hQn
      rw [hcQ, hcW4] at h1
      exact relIndex_eq_one.mp (by omega)
    have hQy : ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ W := by
      intro q hq
      obtain ⟨w, hw, c, hc, rfl⟩ :=
        Vol2.Ch11.SecC.mem_sup_of_le_normalizer (inf_le_left.trans hQn) (hQWC hq)
      have hcy : c * y = y * c := mem_centralizer_singleton_iff.mp (mem_inf.1 hc).2
      have hcy' : c * y⁻¹ = y⁻¹ * c := by
        calc c * y⁻¹ = y⁻¹ * (y * c) * y⁻¹ := by group
          _ = y⁻¹ * (c * y) * y⁻¹ := by rw [← hcy]
          _ = y⁻¹ * c := by group
      have e : y * (w * c) * y⁻¹ * (w * c)⁻¹ = y * w * y⁻¹ * w⁻¹ := by
        calc y * (w * c) * y⁻¹ * (w * c)⁻¹ = y * w * (c * y⁻¹) * c⁻¹ * w⁻¹ := by group
          _ = y * w * (y⁻¹ * c) * c⁻¹ * w⁻¹ := by rw [hcy']
          _ = y * w * y⁻¹ * w⁻¹ := by group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.mp hyNW w).mp hw) (inv_mem hw)
    have hyO : y ∉ pCoreOf 2 K := fun h => by
      obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨y, h⟩
      have hs' : y ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
      exact hy1 (mem_bot.1 (mem_of_pow_odd_mem (m := 3) hs' (Nat.odd_iff.2 rfl)
        (by rw [hy3]; exact one_mem _)))
    have hNK : centQuotOf K Q W = K :=
      Der6D.eq_of_normal_of_not_le_pCoreOf hKperf hq hZK
        (fun k hk => (mem_inf.1 (mem_centQuotOf.1 hk).1).1)
        (centQuotOf_conj hKW (le_sup_left.trans hKTQ))
        fun h => hyO (h (mem_centQuotOf.2 ⟨mem_inf.2 ⟨hyK, hyNW⟩, hQy⟩))
    have hKA : ∀ A, IsMaxElemAbelian Q A → K ≤ normalizer (A : Set G) := by
      intro A hA
      have hWA : W ≤ A := by
        intro w hw
        rw [eq_omegaOneOf_centralizer hA]
        refine Subgroup.subset_closure ⟨mem_inf.2 ⟨hWQ hw, mem_centralizer_iff.2 fun a ha =>
          (mem_centralizer_iff.mp (hQC (hA.1 ha)) w hw).symm⟩, hWe.2 w hw⟩
      refine A5.le_normalizer_of_forall_conj_mem fun k hk a ha => ?_
      have hk' : k ∈ centQuotOf K Q W := by rw [hNK]; exact hk
      have e : k * a * k⁻¹ = (k * a * k⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (hWA ((mem_centQuotOf.1 hk').2 a (hA.1 ha))) ha
    have hR1C : U3.r1Of T L V ⊓ centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
      rw [← U3.s134_cT S]
      exact le_antisymm (inf_le_inf_right _ fun x hx => ((U3.s134_mem_r1Of_iff S).1 hx).1)
        (le_inf (U3.s134_cT_le_r1Of S) inf_le_right)
    have hAJ : ∀ A, IsMaxElemAbelian (pCoreOf 2 (L ⊔ T)) A → IsMaxElemAbelian Q A := by
      intro A hA
      rw [← hR1C] at hA
      have h1 := (U3.s134_lemma13_2_2_six S).2.1 A hA
      rw [← hRR1] at h1
      exact hAQ A h1
    set X := thompsonJ (pCoreOf 2 (L ⊔ T)) with hX
    have hKX : K ≤ normalizer (X : Set G) := by
      refine A5.le_normalizer_of_forall_conj_mem fun k hk x hx => ?_
      have hle : X ≤ X.comap (MulAut.conj k).toMonoidHom :=
        iSup₂_le fun A hA a ha => by
          rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact B6.le_thompsonJ hA ((mem_normalizer_iff.mp (hKA A (hAJ A hA) hk) a).mp ha)
      have h1 := hle hx
      rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have hXT : X ≤ T := by
      refine (iSup₂_le fun A hA => hA.1 : X ≤ pCoreOf 2 (L ⊔ T)).trans ?_
      rw [← U3.s134_cT S]
      exact inf_le_left
    have hX1 : X ≠ ⊥ := by
      obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
      intro hX0
      have hAX : A ≤ X := B6.le_thompsonJ hA
      rw [hX0] at hAX
      have hVab := U3.s134_elemAbelian_V S
      have hVO : V ≤ pCoreOf 2 (L ⊔ T) := by
        rw [← U3.s134_cT S]
        exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
          congrArg Subtype.val (hVab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
      have h1 := hA.2.2 V hVO hVab
      rw [le_bot_iff.1 hAX, Subgroup.card_bot, S.card_V] at h1
      omega
    exact hcontra X hX1 hXT ((LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_thompsonJ _)) hKX

end CFSG.Quasithin.H13.NQS134
