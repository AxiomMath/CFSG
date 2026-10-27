module

public import CFSG.Walter.Bender1970.S3.TransitivitySetup

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

namespace Bender37

variable {G : Type} [Group G] [Finite G] (S : Bender37 G)

theorem W_le_centralizer_of_le_V {R : Subgroup G} (hRV : R ≤ S.V) :
    S.W ≤ Subgroup.centralizer (R : Set G) :=
  S.W_le_centralizer_V.trans (Subgroup.centralizer_le hRV)

theorem W_le_centralizer_singleton {v : G} (hv : v ∈ S.V) :
    S.W ≤ Subgroup.centralizer ({v} : Set G) :=
  S.W_le_centralizer_V.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))

include S in
theorem centralizer_ne_top {R : Subgroup G} (hR : R ≠ ⊥) :
    Subgroup.centralizer (R : Set G) ≠ ⊤ := by
  intro h
  apply hR
  rw [eq_bot_iff]
  intro r hr
  have hc : r ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (R : Set G) := h ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) r hr).symm
  rwa [S.hG.center_eq_bot] at hc

theorem ne_bot_of_card {R : Subgroup G} (hR2 : S.p ^ 2 ≤ Nat.card R) : R ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hR2
  have := S.hp.one_lt
  nlinarith

theorem not_isCyclic {R : Subgroup G} (hRV : R ≤ S.V) (hR2 : S.p ^ 2 ≤ Nat.card R) :
    ¬ IsCyclic R := by
  intro hcyc
  have h1 : Monoid.exponent R ∣ S.p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (S.hVexp x (hRV x.2))
  rw [IsCyclic.exponent_eq_card] at h1
  have h2 := Nat.le_of_dvd S.hp.pos h1
  have := S.hp.one_lt
  nlinarith

theorem isMulCommutative_of_le_V {R : Subgroup G} (hRV : R ≤ S.V) : IsMulCommutative R := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := congrArg Subtype.val (S.hVcomm.is_comm.comm ⟨a, hRV a.2⟩ ⟨b, hRV b.2⟩)
  exact h

theorem sup_W_ne_top {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) : K ⊔ S.W ≠ ⊤ := by
  have := S.hG.isSimpleGroup
  intro h
  have hN : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h]
    exact sup_le Subgroup.le_normalizer hK.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h' | h'
  · exact hK1 h'
  · exact hK.1 h'

theorem qCoreOf_inf_mem_U {X : Subgroup G} (hWX : S.W ≤ X) (hX : X ≠ ⊤) {q : ℕ} (hq : q.Prime)
    (hqπ : q ∉ S.primes) {Y : Subgroup G} (hWY : S.W ≤ Subgroup.normalizer (Y : Set G)) :
    qCoreOf X q ⊓ Y ∈ S.U := by
  obtain ⟨hinv, -, hodd, -, -⟩ := S.qCoreOf_props hWX hq hqπ
  have hWN : S.W ≤ Subgroup.normalizer ((qCoreOf X q ⊓ Y : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) (hWX hw)) (hWY hw)
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ inf_le_left.trans (Subgroup.map_subtype_le _))), hWN,
    commutator_zpowers_eq_self_of_conj_eq_inv (hWN S.t_mem_W) (fun x hx => hinv x hx.1)
      (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))⟩

theorem not_dvd_card_qCoreOf {X : Subgroup G} {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    ¬ S.p ∣ Nat.card (qCoreOf X q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro h
  obtain ⟨k, hk⟩ := (qCoreOf_isPGroup X q).exists_card_eq
  rw [hk] at h
  exact S.ne_p_of_not_mem_primes hqπ ((Nat.prime_dvd_prime_iff_eq S.hp hq).mp
    (S.hp.dvd_of_dvd_pow h)).symm

theorem V_component
    {X : Subgroup G} (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G}
    (hL : IsComponentOf L X) :
    S.V ≤ Subgroup.normalizer (L : Set G) ∧
      (∀ R ≤ S.V, ¬ R ≤ Subgroup.centralizer (L : Set G) → ∀ w ∈ S.V,
        ∃ r ∈ R, r⁻¹ * w ∈ Subgroup.centralizer (L : Set G)) ∧
      Nat.card S.V ≤ S.p * Nat.card (S.V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXA := S.hG.isAStar X hX
  have htX := S.t_mem hWX
  have htp : IsPGroup 2 (Subgroup.zpowers (⟨S.t, htX⟩ : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, S.ht, pow_one])
  obtain ⟨T, hT⟩ := htp.exists_le_sylow
  obtain ⟨-, -, hE⟩ := bender1970_2_5_subgroup hXA htX S.ht T (hT (Subgroup.mem_zpowers _)) rfl
  obtain ⟨hUN, hn, hcyc, -⟩ := hE L hL
  have hVU := S.V_le_oddCoreOf hWX
  have hcyc' : IsCyclic (oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer
      ({S.t} : Set G))) ⧸ (Subgroup.centralizer (L : Set G)).subgroupOf
        (oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({S.t} : Set G))))) := hcyc
  exact ⟨hVU.trans hUN, fun R hRV hRL w hw =>
    exists_mem_inv_mul_mem_of_isCyclic hcyc' hVU S.hp S.hVexp hRV hRL hw,
    card_le_mul_card_inf_of_isCyclic hcyc' hVU S.hp S.hVexp⟩

theorem Q_centralizer_le_normalizer
    {R : Subgroup G} (hRV : R ≤ S.V) {v : G} (hvR : v ∈ R)
    (hv1 : v ≠ 1) :
    S.Q (Subgroup.centralizer ({v} : Set G)) ≤
      Subgroup.normalizer (S.Q (Subgroup.centralizer (R : Set G)) : Set G) := by
  set Xv := Subgroup.centralizer ({v} : Set G) with hXv
  set XR := Subgroup.centralizer (R : Set G) with hXR
  set M := S.Q XR with hM
  have hR1 : R ≠ ⊥ := fun h => hv1 (by rw [h] at hvR; exact Subgroup.mem_bot.mp hvR)
  have hWXR : S.W ≤ XR := S.W_le_centralizer_of_le_V hRV
  have hXRt : XR ≠ ⊤ := S.centralizer_ne_top hR1
  have hXRXv : XR ≤ Xv := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvR)
  have hWXv : S.W ≤ Xv := hWXR.trans hXRXv
  have hXvt : Xv ≠ ⊤ := S.hG.centralizer_ne_top hv1
  have hMU : M ∈ S.U := S.Q_mem_U hWXR hXRt
  have hMXv : M ≤ S.Q Xv := S.le_Q_of_mem_U hWXv hXvt hMU (S.Q_le.trans hXRXv)
  refine sSup_le fun L hP => ?_
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  ·
    have hcent : S.Q Xv ≤ Subgroup.centralizer (qCoreOf Xv q : Set G) := by
      refine sSup_le fun P' hP' => ?_
      rcases hP' with ⟨r, hr, hrπ, rfl⟩ | ⟨hL', -⟩
      · by_cases hrq : r = q
        · subst hrq
          have hab := (S.qCoreOf_props hWXv hr hrπ).2.1
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
        · exact qCoreOf_centralizer_of_ne Xv hq hr (Ne.symm hrq)
      · exact (le_sSup (s := {E : Subgroup G | IsComponentOf E Xv}) hL').trans
          ((componentLayerOf_le_centralizer_fitting Xv).trans
            (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf Xv q hq)))
    exact (Subgroup.le_centralizer_iff.mp (hMXv.trans hcent)).trans
      (Subgroup.centralizer_le_normalizer _)
  ·
    obtain ⟨hVL, hVRL, -⟩ := S.V_component hWXv hXvt hL
    by_cases hRL : R ≤ Subgroup.centralizer (L : Set G)
    ·
      have hLXR : L ≤ XR := Subgroup.le_centralizer_iff.mp hRL
      exact (S.le_Q_of_mem_pieces (X := XR) (Or.inr ⟨IsComponentOf.of_le hL hLXR hXRXv, hLH⟩)).trans
        Subgroup.le_normalizer
    ·
      have hMV : M ≤ ⁅M, S.V⁆ := by
        refine sSup_le fun P' hP' => ?_
        refine le_trans ?_ (Subgroup.commutator_mono (S.le_Q_of_mem_pieces hP') le_rfl)
        rcases hP' with ⟨q, hq, hqπ, rfl⟩ | ⟨hL', hL'H⟩
        · have hVN : S.V ≤ Subgroup.normalizer (qCoreOf XR q : Set G) :=
            (S.V_le_W.trans hWXR).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in XR q))
          have : Fact q.Prime := ⟨hq⟩
          have hsolv : Group.IsSolvable (qCoreOf XR q) := by
            have := (qCoreOf_isPGroup XR q).isNilpotent
            infer_instance
          have hcop : Nat.Coprime (Nat.card S.V) (Nat.card (qCoreOf XR q)) := by
            have : Fact S.p.Prime := ⟨S.hp⟩
            obtain ⟨a, ha⟩ := S.V_isPGroup.exists_card_eq
            obtain ⟨b, hb⟩ := (qCoreOf_isPGroup XR q).exists_card_eq
            rw [ha, hb]
            exact Nat.Coprime.pow a b ((Nat.coprime_primes S.hp hq).mpr
              (Ne.symm (S.ne_p_of_not_mem_primes hqπ)))
          have h1 := le_sup_commutator_of_coprime hVN hsolv hcop
          have h2 : qCoreOf XR q ⊓ Subgroup.centralizer (S.V : Set G) = ⊥ :=
            le_bot_iff.mp ((inf_le_inf_left _ S.hCV).trans (S.qCoreOf_inf_H hWXR hq hqπ).le)
          rwa [h2, bot_sup_eq] at h1
        · obtain ⟨hVL', -, -⟩ := S.V_component hWXR hXRt hL'
          rcases commutator_eq_bot_or_le_of_isComponentOf hL' hVL' with h | h
          · exfalso
            exact hL'H ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans S.hCV)
          · exact h
      have hMVL : ⁅M, S.V⁆ ≤ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.commutator_le]
        intro m hm w hw
        obtain ⟨r, hrR, hrw⟩ := hVRL R hRV hRL w hw
        set c := r⁻¹ * w with hc
        have hmR : m ∈ XR := S.Q_le hm
        have hmr : r * m = m * r := (Subgroup.mem_centralizer_iff.mp hmR) r hrR
        have hmL : m ∈ Subgroup.normalizer (L : Set G) :=
          generalizedFitting_le_normalizer_component hL
            (S.Q_le_generalizedFitting (hMXv hm))
        have hmc : ⁅m, c⁆ ∈ Subgroup.centralizer (L : Set G) := by
          refine commutatorElement_mem_centralizer_of_conj hmL (Or.inl fun n hn => ?_)
          have := (Subgroup.mem_centralizer_iff.mp hrw) n hn
          rw [← this]
          group
        have hrN : r ∈ Subgroup.normalizer
            ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
          Bender35.mem_normalizer_centralizer (hVL (hRV hrR))
        have heq : ⁅m, w⁆ = r * ⁅m, c⁆ * r⁻¹ := by
          have hw' : w = r * c := by rw [hc]; group
          rw [hw']
          simp only [commutatorElement_def]
          calc m * (r * c) * m⁻¹ * (r * c)⁻¹ = (m * r) * c * m⁻¹ * c⁻¹ * r⁻¹ := by group
            _ = (r * m) * c * m⁻¹ * c⁻¹ * r⁻¹ := by rw [hmr]
            _ = r * (m * c * m⁻¹ * c⁻¹) * r⁻¹ := by group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp hrN _).mp hmc
      exact (Subgroup.le_centralizer_iff.mp (hMV.trans hMVL)).trans
        (Subgroup.centralizer_le_normalizer _)

theorem le_iSup_Q
    {K : Subgroup G} (hK : K ∈ S.U) {R : Subgroup G} (hRV : R ≤ S.V)
    (hR2 : S.p ^ 2 ≤ Nat.card R) :
    K ≤ ⨆ (v : G) (_ : v ∈ R) (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G)) := by
  set J := ⨆ (v : G) (_ : v ∈ R) (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G))
  have hJ : ∀ v ∈ R, v ≠ 1 → S.Q (Subgroup.centralizer ({v} : Set G)) ≤ J := fun v hv hv1 =>
    le_iSup₂_of_le (f := fun (v : G) (_ : v ∈ R) =>
      ⨆ (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G))) v hv (le_iSup_of_le hv1 le_rfl)
  by_cases hK1 : K = ⊥
  · rw [hK1]
    exact bot_le
  set X := K ⊔ S.W with hXdef
  have hWX : S.W ≤ X := le_sup_right
  have hX : X ≠ ⊤ := S.sup_W_ne_top hK hK1
  refine (S.le_Q_of_mem_U hWX hX hK le_sup_left).trans (sSup_le fun L hP => ?_)
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · have hRN : R ≤ Subgroup.normalizer (qCoreOf X q : Set G) :=
      (hRV.trans (S.V_le_W.trans hWX)).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q))
    refine (le_iSup_inf_centralizer S.hp (S.isMulCommutative_of_le_V hRV)
      (fun x hx => S.hVexp x (hRV hx)) hR2 hRN (S.not_dvd_card_qCoreOf hq hqπ)).trans
      (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    have hWe := S.W_le_centralizer_singleton (hRV he)
    exact (S.le_Q_of_mem_U hWe (S.hG.centralizer_ne_top he1)
      (S.qCoreOf_inf_mem_U hWX hX hq hqπ (hWe.trans Subgroup.le_normalizer)) inf_le_right).trans
      (hJ e he he1)
  · obtain ⟨u, huR, hu1, hLu⟩ := exists_ne_one_mem_centralizer_of_isComponentOf
      (S.hG.isAStar X hX) (S.t_mem hWX) S.ht (hRV.trans (S.V_le_oddCoreOf hWX))
      (S.not_isCyclic hRV hR2) hL
    have hWu := S.W_le_centralizer_singleton (hRV huR)
    exact (S.le_orbit L).trans ((S.le_Q_of_mem_U hWu (S.hG.centralizer_ne_top hu1)
      (S.orbit_mem_U hWX hX hL hLH) (S.orbit_le hLu (hWu.trans Subgroup.le_normalizer))).trans
      (hJ u huR hu1))

theorem exists_Q_ne_bot
    {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) :
    ∃ R ≤ S.V, S.p ^ 2 ≤ Nat.card R ∧ S.Q (Subgroup.centralizer (R : Set G)) ≠ ⊥ := by
  set X := K ⊔ S.W with hXdef
  have hWX : S.W ≤ X := le_sup_right
  have hX : X ≠ ⊤ := S.sup_W_ne_top hK hK1
  have hQ : S.Q X ≠ ⊥ := fun h =>
    hK1 (le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWX hX hK le_sup_left))
  obtain ⟨L, hP, hP1⟩ : ∃ P ∈ S.pieces X, P ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hQ (le_bot_iff.mp (sSup_le fun P hP => (hcon P hP).le))
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · have hVN : S.V ≤ Subgroup.normalizer (qCoreOf X q : Set G) :=
      (S.V_le_W.trans hWX).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q))
    obtain ⟨B, hBV, hcard, hB⟩ := exists_inf_centralizer_ne_bot S.hp S.hVcomm S.hVexp
      S.V_ne_bot hVN (S.not_dvd_card_qCoreOf hq hqπ) hP1
    have hB2 : S.p ^ 2 ≤ Nat.card B := by
      have h3 := S.hV3
      rw [hcard, pow_succ, mul_comm] at h3
      exact Nat.le_of_mul_le_mul_left h3 S.hp.pos
    refine ⟨B, hBV, hB2, fun h => hB ?_⟩
    have hWB := S.W_le_centralizer_of_le_V hBV
    exact le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWB (S.centralizer_ne_top (S.ne_bot_of_card hB2))
      (S.qCoreOf_inf_mem_U hWX hX hq hqπ (hWB.trans Subgroup.le_normalizer)) inf_le_right)
  · obtain ⟨-, -, hcard⟩ := S.V_component hWX hX hL
    set R := S.V ⊓ Subgroup.centralizer (L : Set G) with hR
    have hR2 : S.p ^ 2 ≤ Nat.card R := by
      have h3 := S.hV3.trans hcard
      rw [pow_succ, mul_comm] at h3
      exact Nat.le_of_mul_le_mul_left h3 S.hp.pos
    refine ⟨R, inf_le_left, hR2, fun h => ?_⟩
    have hWR := S.W_le_centralizer_of_le_V (inf_le_left : R ≤ S.V)
    have hLR : L ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.le_centralizer_iff.mp inf_le_right
    have hO := S.le_Q_of_mem_U hWR (S.centralizer_ne_top (S.ne_bot_of_card hR2))
      (S.orbit_mem_U hWX hX hL hLH) (S.orbit_le hLR (hWR.trans Subgroup.le_normalizer))
    rw [h] at hO
    exact ne_bot_of_isComponentOf hL (le_bot_iff.mp ((S.le_orbit L).trans hO))

theorem exists_max_U
    {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) :
    ∃ M₀ ∈ S.U, M₀ ≠ ⊥ ∧ ∀ K' ∈ S.U, K' ≤ M₀ := by
  obtain ⟨R, hRV, hR2, hM⟩ := S.exists_Q_ne_bot hK hK1
  set M := S.Q (Subgroup.centralizer (R : Set G)) with hMdef
  have hWR := S.W_le_centralizer_of_le_V hRV
  have hMU : M ∈ S.U := S.Q_mem_U hWR (S.centralizer_ne_top (S.ne_bot_of_card hR2))
  have hall : ∀ K' ∈ S.U, K' ≤ Subgroup.normalizer (M : Set G) := fun K' hK' =>
    (S.le_iSup_Q hK' hRV hR2).trans (iSup₂_le fun v hv => iSup_le fun hv1 =>
      S.Q_centralizer_le_normalizer hRV hv hv1)
  set X := Subgroup.normalizer (M : Set G) with hXdef
  have hWX : S.W ≤ X := hMU.2.1
  have hX : X ≠ ⊤ := S.hG.normalizer_ne_top hM hMU.1
  refine ⟨S.Q X, S.Q_mem_U hWX hX, fun h => hK1 ?_,
    fun K' hK' => S.le_Q_of_mem_U hWX hX hK' (hall K' hK')⟩
  exact le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWX hX hK (hall K hK))

theorem H_le_normalizer {M₀ : Subgroup G} (hM₀ : M₀ ∈ S.U) (hM₀1 : M₀ ≠ ⊥)
    (hmax : ∀ K ∈ S.U, K ≤ M₀) : S.H ≤ Subgroup.normalizer (M₀ : Set G) := by
  set X := Subgroup.normalizer (M₀ : Set G) with hXdef
  have hWX : S.W ≤ X := hM₀.2.1
  have hX : X ≠ ⊤ := S.hG.normalizer_ne_top hM₀1 hM₀.1
  have hQ : S.Q X = M₀ :=
    le_antisymm (hmax _ (S.Q_mem_U hWX hX)) (S.le_Q_of_mem_U hWX hX hM₀ Subgroup.le_normalizer)
  have step : ∀ A : Subgroup G, S.W ≤ A → A ≤ X → ∀ k ∈ S.H,
      k ∈ Subgroup.normalizer (A : Set G) → k ∈ X := by
    intro A hWA hAX k hkH hkA
    have h1 := S.map_conj_Q (X := X) hkH
    rw [hQ] at h1
    have hWXk : S.W ≤ X.map (MulAut.conj k).toMonoidHom := by
      intro w hw
      have hwA : w ∈ A.map (MulAut.conj k).toMonoidHom := by
        rw [map_conj_eq_of_mem_normalizer hkA]
        exact hWA hw
      exact Subgroup.map_mono hAX hwA
    have hXk : X.map (MulAut.conj k).toMonoidHom ≠ ⊤ := by
      intro h
      apply hX
      have h2 := map_conj_map_conj_inv k X
      rw [h, Subgroup.map_top_of_surjective _ (MulAut.conj k⁻¹).surjective] at h2
      exact h2.symm
    have h2 : M₀.map (MulAut.conj k).toMonoidHom ≤ M₀ := h1 ▸ hmax _ (S.Q_mem_U hWXk hXk)
    have h3 : M₀.map (MulAut.conj k).toMonoidHom = M₀ :=
      Subgroup.eq_of_le_of_card_ge h2
        (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
    exact Bender35.mem_normalizer_of_map_conj_eq h3
  suffices key : ∀ A : Subgroup S.H, A.IsSubnormal → S.W.subgroupOf S.H ≤ A →
      A.map S.H.subtype ≤ X → S.H ≤ X by
    refine key _ S.W_isSubnormal_H le_rfl ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left S.W_le_H]
    exact hWX
  intro A hA
  induction hA with
  | top =>
    intro _ h
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  | step A K hAK _ hN ih =>
    intro hWA hAX
    refine ih (hWA.trans hAK) ?_
    rintro _ ⟨k, hk, rfl⟩
    refine step (A.map S.H.subtype) ?_ hAX k k.2 ?_
    · intro w hw
      exact ⟨⟨w, S.W_le_H hw⟩, hWA (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
    · have hkN : k ∈ Subgroup.normalizer (A : Set S.H) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mp hN) hk
      exact Subgroup.le_normalizer_map S.H.subtype ⟨k, hkN, rfl⟩

theorem forall_U_eq_bot :
    ∀ K ∈ S.U, K = ⊥ := by
  have := S.hG.isSimpleGroup
  intro K hK
  by_contra hK1
  obtain ⟨M₀, hM₀, hM₀1, hmax⟩ := S.exists_max_U hK hK1
  have hHN := S.H_le_normalizer hM₀ hM₀1 hmax
  rcases S.hH.le_iff.mp hHN with h | h
  · have hn : M₀.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₀ with h' | h'
    · exact hM₀1 h'
    · exact hM₀.1 h'
  · have hM₀H : M₀ ≤ S.H := h ▸ Subgroup.le_normalizer
    exact hM₀1 (S.eq_bot_of_le_commutator hM₀H hM₀.2.2.ge)

theorem eq_H_of_forall_U_eq_bot (hU : ∀ K ∈ S.U, K = ⊥) {B : Subgroup G} (hB : IsCoatom B)
    (hWB : S.W ≤ B) : S.H = B := by
  have hQB : S.Q B = ⊥ := hU _ (S.Q_mem_U hWB hB.1)
  have hFB : generalizedFittingSubgroupOf B ≤ S.H := by
    refine sup_le ?_ ?_
    · rw [fittingSubgroupOf_eq_iSup_qCoreOf B]
      refine iSup_le fun q => ?_
      have hq := Nat.prime_of_mem_primeFactors q.1.2
      by_cases hqπ : q.1.1 ∈ S.primes
      · exact (S.qCoreOf_le_centralizer hWB hq hqπ).trans S.hCH
      · exact (S.le_Q_of_mem_pieces (Or.inl ⟨_, hq, hqπ, rfl⟩)).trans (hQB ▸ bot_le)
    · refine sSup_le fun L hL => ?_
      by_contra hLH
      exact ne_bot_of_isComponentOf hL
        (le_bot_iff.mp (hQB ▸ S.le_Q_of_mem_pieces (Or.inr ⟨hL, hLH⟩)))
  refine bender1970_1_7_iii_equalityOfMaximal S.hG.isSimpleGroup S.H S.hH S.W S.W_le_F
    S.W_isSubnormal S.inf_centralizer_W_le hWB hB (Or.inl S.two_le_card_primes_F)
    ⟨generalizedFittingSubgroupOf B, hFB, le_rfl, ?_, inf_le_left⟩
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.IsSubnormal.top

theorem centralizer_le
    {v : G} (hv : v ∈ S.V) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ S.H := by
  rcases eq_top_or_exists_le_coatom (Subgroup.centralizer ({v} : Set G)) with h | ⟨B, hB, hCB⟩
  · exact absurd h (S.hG.centralizer_ne_top hv1)
  · rw [S.eq_H_of_forall_U_eq_bot S.forall_U_eq_bot hB
      ((S.W_le_centralizer_singleton hv).trans hCB)]
    exact hCB

end Bender37

end CFSG.Walter
