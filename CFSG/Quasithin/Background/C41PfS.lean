module

public import CFSG.Quasithin.Background.C41PfR
public import CFSG.Quasithin.Background.C41PfP
public import CFSG.Quasithin.Background.C41PfQ
public import CFSG.Quasithin.Vol2.Ch12Sec7L5p
public import CFSG.Quasithin.Vol2.Ch9KGFFSpConj
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.Open hiding StatedSp StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.Ch9.KGFF.SpM
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem c41Sp4Block_holds : C41Sp4Block G := by
  intro H R M L V K hP h1 h2 hSp hmax
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.hyp
  have hSp₀ := hSp
  obtain ⟨hshort, F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβeq⟩ := hSp₀
  have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF']; norm_num)
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four (le_of_eq hF'.symm)
  have hFk : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, by rw [hF']; norm_num⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : Fˣ, (δ : F) ≠ 1 := by
    have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF']
    have : Nontrivial Fˣ := by
      rw [← Finite.one_lt_card_iff_nontrivial, hU3]
      norm_num
    obtain ⟨δ, hδ⟩ := exists_ne (1 : Fˣ)
    exact ⟨δ, fun h => hδ (Units.ext h)⟩
  set W0 := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW0
  set M0 := conjClosure L M with hM0
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hM0K : M0 ≤ K := hP.le
  have hM0M : M0 ≤ M := C2Nine.conjClosure_le_M h
  have hM0perf : ⁅M0, M0⁆ = M0 := C2Nine.perfect_conjClosure_of_hyp h
  have hMM0 : M ≤ Subgroup.normalizer (M0 : Set G) := le_normalizer_conjClosure L M
  have hNK : M0 ≤ Subgroup.normalizer (K : Set G) := hM0K.trans Subgroup.le_normalizer
  have hO2KR : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 K)
        (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hO2R : pCoreOf 2 K ≤ R := hO2KR.trans (pCoreOf_sup_le_of_hyp h hKH hNK)
  have hZsp : Subgroup.center ↥(StatedSp 2 F) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
  have hαC := map_eq_one_iff_mem_centralizer hP.le_normalizer h1 α hαs hαk hZsp
  have hKW : K ≤ Subgroup.normalizer (W0 : Set G) := le_normalizer_omegaOneCenter K R
  have hpO : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := C2A3Orbits.pCoreOf_eq_map_pCore K
  have hker : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    rw [← MonoidHom.mem_ker, hαk, hpO]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', he⟩
      rwa [show k' = k from Subtype.ext he] at hk'
  have hCO : K ⊓ Subgroup.centralizer (W0 : Set G) ≤ pCoreOf 2 K := fun x hx =>
    (hker ⟨x, hx.1⟩).mp ((hαC ⟨x, hx.1⟩).mpr hx.2)
  have hCM : K ⊓ Subgroup.centralizer (W0 : Set G) ≤ M ⊓ K := fun x hx =>
    ⟨h.le_M (hO2R (hCO hx)), hx.1⟩
  have hMKmax : IsMaxParabolic2 K (M ⊓ K) :=
    isMaxParabolic2_of_autOn hKW inf_le_right hCM hCO hmax
  set P' : Subgroup ↥(StatedSp 2 F) := ((M ⊓ K).subgroupOf K).map α with hP'
  have hP'par : IsParabolic2 ⊤ P' := isParabolic2_map_top α hαs hαk hMKmax.1
  have hO2MK : pCoreOf 2 K ≤ M ⊓ K := fun x hx => ⟨h.le_M (hO2R hx), pCoreOf_le 2 K hx⟩
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hMKmax.2.1
    refine le_antisymm inf_le_right fun k hk => ?_
    have hmem : α ⟨k, hk⟩ ∈ P' := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, he⟩ := hmem
    have h3 : α (m⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h4 := hO2MK ((hker _).mp h3)
    have e : k = (m : G) * ((m⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact (M ⊓ K).mul_mem hm h4
  set X : Subgroup ↥(StatedSp 2 F) := (M0.subgroupOf K).map α with hX
  have hXP : X ≤ P' := Subgroup.map_mono fun x hx => ⟨hM0M hx, hM0K hx⟩
  have hXperf : ⁅X, X⁆ = X := by
    have h1' : ⁅M0.subgroupOf K, M0.subgroupOf K⁆ = M0.subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM0K, hM0perf]
    rw [hX, ← Subgroup.map_commutator, h1']
  have hM0O : X = ⊥ → M0 ≤ pCoreOf 2 K := by
    intro hb m hm
    refine (hker ⟨m, hM0K hm⟩).mp ?_
    have : α ⟨m, hM0K hm⟩ ∈ X := ⟨⟨m, hM0K hm⟩, hm, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact this
  have hXne : X ≠ ⊥ := by
    intro hb
    apply hP.not_commutator_le
    rw [Subgroup.commutator_le]
    intro m hm k hk
    have hmO := hM0O hb hm
    have h3 : k * m⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp
        ((pCoreOf 2 K).inv_mem hmO)
    have e : ⁅m, k⁆ = m * (k * m⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 K).mul_mem hmO h3
  have hXnorm : ∀ p ∈ P', ∀ x ∈ X, p * x * p⁻¹ ∈ X := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m₀, hm₀, rfl⟩
    refine ⟨m * m₀ * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMM0 hm.1) m₀).mp hm₀
  have hXcore : X ≤ perfectCore P' := le_perfectCore_of_perfect hXP hXperf
  obtain ⟨g, j, hgj⟩ := (CFSG.Quasithin.H13.Ch9.KGFF.sp4_perfectCore_parabolic_conj hFk hP'par
    hP'ne).resolve_left fun hb => hXne (le_bot_iff.mp (hb ▸ hXcore))
  set N := perfectCore (Q2 F j) with hN
  have hconj : ∀ y : ↥(StatedSp 2 F), y ∈ perfectCore P' ↔ g⁻¹ * y * g ∈ N := by
    intro y
    rw [hgj]
    constructor
    · rintro ⟨n, hn, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hn
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  set Y : Subgroup ↥(StatedSp 2 F) := X.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYN : Y ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hconj x).mp (hXcore hx)
    simpa [MulAut.conj_apply] using this
  have hYnorm : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    rintro n hn _ ⟨x, hx, rfl⟩
    have hgn : g * n * g⁻¹ ∈ perfectCore P' := (hconj _).mpr (by simpa [mul_assoc] using hn)
    have h3 := hXnorm _ (perfectCore_le _ hgn) x hx
    refine ⟨_, h3, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hYperf : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hXperf]
  have hYne : Y ≠ ⊥ := by
    intro hb
    apply hXne
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hb
    rw [hY, Subgroup.map_map, Subgroup.map_bot] at this
    have e : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun y => by simp [MulAut.conj_apply, mul_assoc]
    rwa [e, Subgroup.map_id] at this
  have hYeq : Y = N := SpN.eq_perfectCore_of_normal hK4 hFk hYN hYnorm hYperf hYne
  have hXmem : ∀ n ∈ N, ∃ m : ↥K, (m : G) ∈ M0 ∧ α m = g * n * g⁻¹ := by
    intro n hn
    rw [← hYeq] at hn
    obtain ⟨x, hx, hxe⟩ := hn
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨m, hm, ?_⟩
    rw [← hxe]
    simp [mul_assoc]
  have hXsub : ∀ m : ↥K, (m : G) ∈ M0 → g⁻¹ * α m * g ∈ N := by
    intro m hm
    have : (MulAut.conj g⁻¹).toMonoidHom (α m) ∈ Y := ⟨α m, ⟨m, hm, rfl⟩, rfl⟩
    rw [hYeq] at this
    simpa [MulAut.conj_apply] using this
  set T : Subgroup G :=
    ((((rad j).map (MulAut.conj g).toMonoidHom).comap α).map K.subtype) ⊓ M0 with hT
  have hT2 : IsPGroup 2 ↥T := by
    rintro ⟨t, ⟨⟨k, ⟨r, hr, hre⟩, rfl⟩, -⟩⟩
    obtain ⟨a, ha⟩ := rad_isPGroup hFk j ⟨r, hr⟩
    have hra : r ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h3 : α (k ^ 2 ^ a) = 1 := by
      rw [map_pow, ← hre]
      show ((MulAut.conj g) r) ^ 2 ^ a = 1
      rw [MulAut.conj_apply, conj_pow, hra, mul_one, mul_inv_cancel]
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, (hker _).mp h3⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_subtype]
    rw [pow_add, pow_mul]
    exact hb'
  have hTnorm : M0 ≤ Subgroup.normalizer (T : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨⟨k, ⟨r, hr, hre⟩, rfl⟩, htM⟩ := ht
    refine ⟨⟨⟨m, hM0K hm⟩ * k * ⟨m, hM0K hm⟩⁻¹, ?_, rfl⟩, ?_⟩
    · have hn := hXsub ⟨m, hM0K hm⟩ hm
      refine ⟨(g⁻¹ * α ⟨m, hM0K hm⟩ * g) * r * (g⁻¹ * α ⟨m, hM0K hm⟩ * g)⁻¹,
        conj_mem_rad hn hr, ?_⟩
      simp only [map_mul, map_inv, ← hre, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · exact M0.mul_mem (M0.mul_mem hm htM) (M0.inv_mem hm)
  have hTO : T ≤ pCoreOf 2 M0 := le_pCoreOf_of_le_normalizer 2 inf_le_right hTnorm hT2
  have hO2M0 : pCoreOf 2 M0 ≤ pCoreOf 2 (M0 ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 M0).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 M0)
        ((h.le_M.trans hMM0).trans (normalizer_le_normalizer_pCoreOf 2 M0)))
      (pCoreOf_isPGroup 2 M0)
  have hVcen : ∀ v ∈ V, ∀ q ∈ pCoreOf 2 (M0 ⊔ R), q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.V_center hv)).2 q hq
  have hVK : V ≤ K := h.V_le.trans hM0K
  have hO2KM0R : pCoreOf 2 K ≤ pCoreOf 2 (M0 ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 (hO2R.trans le_sup_right)
      (sup_le (hM0K.trans (le_normalizer_pCoreOf 2 K))
        (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hVO : V ≤ pCoreOf 2 K := fun v hv => hP.charTwo
    ⟨hVK hv, Subgroup.mem_centralizer_iff.mpr fun q hq => hVcen v hv q (hO2KM0R hq)⟩
  have hVU : V ≤ blockU K := by
    calc V = ⁅V, M0⁆ := h.V_comm.symm
      _ ≤ ⁅pCoreOf 2 K, K⁆ := Subgroup.commutator_mono hVO hM0K
  have hM0V : M0 ≤ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right (H₁ := V) (H₂ := M0)
    rwa [h.V_comm] at this
  set bv : ↥V → (Fin 2 ⊕ Fin 2 → F) := fun v => Multiplicative.toAdd (β ⟨v, hVU v.2⟩) with hbv
  have hconjV : ∀ (m : ↥K) (v : ↥V) (hmv : (m : G) * v * (m : G)⁻¹ ∈ V),
      bv ⟨_, hmv⟩ = spMat (α m) *ᵥ bv v := fun m v hmv =>
    hβeq m ⟨v, hVU v.2⟩ ⟨_, hVU hmv⟩ rfl
  have hfix : ∀ r ∈ rad j, ∀ v : ↥V, spMat (g * r * g⁻¹) *ᵥ bv v = bv v := by
    intro r hr v
    obtain ⟨m, hm, hme⟩ := hXmem r (rad_le j hr)
    have hmT : (m : G) ∈ T := ⟨⟨m, ⟨r, hr, by rw [hme]; rfl⟩, rfl⟩, hm⟩
    have hc : (m : G) * v * (m : G)⁻¹ = v := by
      rw [hVcen v v.2 m (hO2M0 (hTO hmT)), mul_inv_cancel_right]
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V := by rw [hc]; exact v.2
    have := hconjV m v hmv
    rw [← hme]
    rw [show (⟨_, hmv⟩ : ↥V) = v from Subtype.ext hc] at this
    exact this.symm
  have hVne : ∃ v : ↥V, bv v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h.V_ne
    have hVZ : V ≤ blockZ K := by
      intro v hv
      have h0 := hall ⟨v, hv⟩
      have hk : (⟨v, hVU hv⟩ : ↥(blockU K)) ∈ β.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd h0
      rw [hβk] at hk
      exact hk
    rw [eq_bot_iff, ← h.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hz := hVZ hv
    have hcm : (m : G) * v = v * m := Subgroup.mem_centralizer_iff.mp hz.2 m (hM0K hm)
    rw [Subgroup.mem_bot, commutatorElement_def, hcm.symm]
    group
  have hcommZ : ∀ (v : ↥V) (m : ↥K), (m : G) ∈ M0 → spMat (α m) *ᵥ bv v = bv v →
      ⁅(v : G), (m : G)⁆ ∈ blockZ K := by
    intro v m hm hmv
    have hmv' : (m : G) * v * (m : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hM0V hm) v).mp v.2
    have h3 := hconjV m v hmv'
    rw [hmv] at h3
    set a : ↥(blockU K) := ⟨v, hVU v.2⟩
    set b : ↥(blockU K) := ⟨_, hVU hmv'⟩
    have hab : a * b⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : β b = β a := by
        apply Multiplicative.toAdd.injective
        exact h3
      rw [this, mul_inv_cancel]
    rw [hβk] at hab
    have e : ⁅(v : G), (m : G)⁆ = ((a * b⁻¹ : ↥(blockU K)) : G) := by
      simp only [a, b, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hab
  have hj : j = 1 := by
    rcases fin_two_cases j with hj0 | hj1
    · exfalso
      subst hj0
      obtain ⟨v₀, hv₀⟩ := hVne
      apply hv₀
      have hfixM0 : ∀ v : ↥V, ∀ m : ↥K, (m : G) ∈ M0 → spMat (α m) *ᵥ bv v = bv v := by
        intro v m hm
        set w := spMat g⁻¹ *ᵥ bv v with hw
        have hR0 : ∀ r ∈ rad (K := F) 0, spMat r *ᵥ w = w := fun r hr =>
          (conj_fixed_iff g r (bv v)).mp (hfix r hr v)
        have hn := hXsub m hm
        have h3 := fixed_zero (hR0 _ (x_one_mem_rad hK4 δ hδ)) (hR0 _ (u_eAlt_mem_rad hK4 δ hδ)) hn
        have h4 := (conj_fixed_iff g (g⁻¹ * α m * g) (bv v)).mpr h3
        rwa [show g * (g⁻¹ * α m * g) * g⁻¹ = α m by group] at h4
      have hVZ : V ≤ blockZ K := by
        rw [← h.V_comm, Subgroup.commutator_le]
        intro v hv m hm
        exact hcommZ ⟨v, hv⟩ ⟨m, hM0K hm⟩ hm (hfixM0 ⟨v, hv⟩ ⟨m, hM0K hm⟩ hm)
      have hk : (⟨v₀, hVU v₀.2⟩ : ↥(blockU K)) ∈ β.ker := by
        rw [hβk]
        exact hVZ v₀.2
      rw [MonoidHom.mem_ker] at hk
      show Multiplicative.toAdd (β ⟨v₀, hVU v₀.2⟩) = 0
      rw [hk]
      rfl
    · exact hj1
  subst hj
  set W : Submodule F (Fin 2 ⊕ Fin 2 → F) :=
    (CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F)).map
      ((CFSG.Quasithin.H13.S127.L5.Sp4.mulVecEquiv g : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] _) :
        (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)) with hW
  have hmemW : ∀ y, y ∈ W ↔ spMat g⁻¹ *ᵥ y ∈ CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F) := by
    intro y
    rw [hW, Submodule.mem_map_equiv]
    rfl
  have hWfr : Module.finrank F ↥W = 2 := by
    rw [hW, LinearEquiv.finrank_map_eq]
    exact CFSG.Quasithin.H13.S127.L5.Sp4.finrank_ell0
  have hell0 : ∀ y : Fin 2 ⊕ Fin 2 → F,
      y ∈ CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F) ↔ y ∈ isoFlag 2 F 2 := by
    intro y
    rw [CFSG.Quasithin.H13.S127.L5.Sp4.mem_ell0, mem_isoFlag]
    constructor
    · intro hy
      refine ⟨hy, fun i hi => ?_⟩
      have := i.isLt
      omega
    · exact fun hy => hy.1
  have hgg : ∀ y : Fin 2 ⊕ Fin 2 → F, spMat g *ᵥ (spMat g⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← spMat_mul, mul_inv_cancel, spMat_one, Matrix.one_mulVec]
  have hVW : ∀ v : ↥V, bv v ∈ W := by
    intro v
    rw [hmemW, hell0]
    exact SpN.mem_isoFlag_of_fixed_rad_one hK4 hδ fun r hr =>
      (conj_fixed_iff g r (bv v)).mp (hfix r hr v)
  have hWV : ∀ y ∈ W, ∃ v : ↥V, bv v = y := by
    intro y hy
    by_cases hy0 : y = 0
    · refine ⟨1, ?_⟩
      rw [hy0]
      show Multiplicative.toAdd (β ⟨1, hVU V.one_mem⟩) = 0
      rw [show (⟨1, hVU V.one_mem⟩ : ↥(blockU K)) = 1 from rfl, map_one]
      rfl
    obtain ⟨v₀, hv₀⟩ := hVne
    set a := spMat g⁻¹ *ᵥ bv v₀ with ha
    set b := spMat g⁻¹ *ᵥ y with hb
    have haL : a ∈ CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F) := (hmemW _).mp (hVW v₀)
    have hbL : b ∈ CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F) := (hmemW _).mp hy
    have hinl : ∀ c ∈ CFSG.Quasithin.H13.S127.L5.Sp4.ell0 (F := F),
        (fun i => c (Sum.inl i)) = 0 → c = 0 := by
      intro c hc h0
      funext i
      rcases i with i | i
      · exact congrFun h0 i
      · exact hc i
    have ha0 : (fun i => a (Sum.inl i)) ≠ 0 := fun h0 => hv₀ (by
      have := hinl a haL h0
      rw [← hgg (bv v₀), ← ha, this, Matrix.mulVec_zero])
    have hb0 : (fun i => b (Sum.inl i)) ≠ 0 := fun h0 => hy0 (by
      have := hinl b hbL h0
      rw [← hgg y, ← hb, this, Matrix.mulVec_zero])
    obtain ⟨A, hA⟩ := SpN.exists_sl2_mulVec_eq ha0 hb0
    have hn : spLevi 1 A ∈ perfectCore (Q2 F 1) := spLevi_mem_perfectCore hK4 1 A
    have hna : spMat (spLevi 1 A) *ᵥ a = b := by
      funext i
      rw [spLevi_one_eq]
      rcases i with i | i
      · rw [mulVec_ell_inl]
        exact congrFun hA i
      · rw [mulVec_ell_inr]
        have hz : (a ∘ Sum.inr : Fin 2 → F) = 0 := funext fun k => haL k
        rw [hz, Matrix.mulVec_zero]
        exact (hbL i).symm
    obtain ⟨m, hm, hme⟩ := hXmem _ hn
    have hmv : (m : G) * v₀ * (m : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hM0V hm) v₀).mp v₀.2
    refine ⟨⟨_, hmv⟩, ?_⟩
    rw [hconjV m v₀ hmv, hme, spMat_mul, spMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← ha, hna, hb, hgg]
  have hVZn : V ≤ Subgroup.normalizer (blockZ K : Set G) := fun v hv =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 v (hVK hv), mul_inv_cancel_right]
      exact hz
  have hWiff : ∀ u : ↥(blockU K), (u : G) ∈ V ⊔ blockZ K ↔ Multiplicative.toAdd (β u) ∈ W := by
    refine fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · have hx : (u : G) ∈ ((V : Set G) * (blockZ K : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right V (blockZ K) hVZn]
        exact hu
      obtain ⟨v, hv, z, hz, hvz⟩ := hx
      have hz1 : β ⟨z, hz.1⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hβk]
        exact hz
      have e : u = ⟨v, hVU hv⟩ * ⟨z, hz.1⟩ := Subtype.ext hvz.symm
      rw [e, map_mul, hz1, mul_one]
      exact hVW ⟨v, hv⟩
    · obtain ⟨v, hv⟩ := hWV _ hu
      have hk : (⟨v, hVU v.2⟩ : ↥(blockU K))⁻¹ * u ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : β ⟨v, hVU v.2⟩ = β u := by
          apply Multiplicative.toAdd.injective
          exact hv
        rw [this, inv_mul_cancel]
      rw [hβk] at hk
      have e : (u : G) = v * (((⟨v, hVU v.2⟩ : ↥(blockU K))⁻¹ * u : ↥(blockU K)) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem_sup v.2 hk
  have hFL : IsFLineVia (blockU K) (V ⊔ blockZ K) β := ⟨sup_le hVU inf_le_left, W, hWfr, hWiff⟩
  have hXN : ∀ x ∈ X, g⁻¹ * x * g ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    exact hXsub m hm
  have hNX : ∀ n ∈ N, g * n * g⁻¹ ∈ X := by
    intro n hn
    obtain ⟨m, hm, hme⟩ := hXmem n hn
    exact ⟨m, hm, hme⟩
  have hqN : ∀ p ∈ P', ∀ n ∈ N, (g⁻¹ * p * g) * n * (g⁻¹ * p * g)⁻¹ ∈ N := by
    intro p hp n hn
    have h3 := hXN _ (hXnorm p hp _ (hNX n hn))
    convert h3 using 1
    group
  have hPrad : ∀ p ∈ P', ∀ r ∈ rad (K := F) 1, ∃ r' ∈ rad (K := F) 1,
      p⁻¹ * (g * r * g⁻¹) * p = g * r' * g⁻¹ := by
    intro p hp r hr
    set q := g⁻¹ * p⁻¹ * g with hq
    have hp' : p⁻¹ ∈ P' := P'.inv_mem hp
    set Rq : Subgroup ↥(StatedSp 2 F) := (rad (K := F) 1).map (MulAut.conj q).toMonoidHom with hRq
    have hRqN : Rq ≤ N := by
      rintro _ ⟨r₀, hr₀, rfl⟩
      exact hqN p⁻¹ hp' r₀ (rad_le 1 hr₀)
    have hRqn : ∀ n ∈ N, ∀ y ∈ Rq, n * y * n⁻¹ ∈ Rq := by
      rintro n hn _ ⟨r₀, hr₀, rfl⟩
      have hn' : q⁻¹ * n * q⁻¹⁻¹ ∈ N := by
        have := hqN p hp n hn
        convert this using 1
        simp only [hq]
        group
      refine ⟨(q⁻¹ * n * q⁻¹⁻¹) * r₀ * (q⁻¹ * n * q⁻¹⁻¹)⁻¹, conj_mem_rad hn' hr₀, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hRq2 : IsPGroup 2 ↥Rq := (rad_isPGroup hFk 1).map _
    have hle := SpN.le_rad_of_isPGroup hK4 hRqN hRqn hRq2
    refine ⟨q * r * q⁻¹, hle ⟨r, hr, rfl⟩, ?_⟩
    simp only [hq]
    group
  have hWfix : ∀ y, y ∈ W ↔ ∀ r ∈ rad (K := F) 1, spMat (g * r * g⁻¹) *ᵥ y = y := by
    intro y
    rw [hmemW, hell0]
    constructor
    · intro hy r hr
      exact (conj_fixed_iff g r y).mpr (SpN.fixed_of_mem_rad_one hr hy)
    · intro hy
      exact SpN.mem_isoFlag_of_fixed_rad_one hK4 hδ fun r hr => (conj_fixed_iff g r y).mp (hy r hr)
  have hPW : ∀ p ∈ P', ∀ y ∈ W, spMat p *ᵥ y ∈ W := by
    intro p hp y hy
    rw [hWfix] at hy ⊢
    intro r hr
    obtain ⟨r', hr', he⟩ := hPrad p hp r hr
    have e : g * r * g⁻¹ * p = p * (g * r' * g⁻¹) := by
      rw [← he]
      group
    rw [Matrix.mulVec_mulVec, ← spMat_mul, e, spMat_mul, ← Matrix.mulVec_mulVec, hy r' hr']
  have hUn : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := pCoreOf 2 K) (H₂ := K)
  have hVZM0 : ⁅V ⊔ blockZ K, M0⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro a ha m hm
    have hx : a ∈ ((V : Set G) * (blockZ K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V (blockZ K) hVZn]
      exact ha
    obtain ⟨v, hv, z, hz, rfl⟩ := hx
    have hzm : (m : G) * z = z * m := Subgroup.mem_centralizer_iff.mp hz.2 m (hM0K hm)
    have e : ⁅v * z, m⁆ = ⁅v, m⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc v * z * m * (v * z)⁻¹ * m⁻¹ = v * (z * m) * z⁻¹ * v⁻¹ * m⁻¹ := by group
        _ = v * m * v⁻¹ * m⁻¹ := by rw [← hzm]; group
    rw [e, ← h.V_comm]
    exact Subgroup.commutator_mem_commutator hv hm
  have hMKN : M ⊓ K ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    apply mem_normalizer_of_map_le
    have hxM0 : M0.map (MulAut.conj x).toMonoidHom = M0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMM0 hx.1)
    have hVx : V.map (MulAut.conj x).toMonoidHom ≤ V ⊔ blockZ K := by
      rintro _ ⟨v, hv, rfl⟩
      have hu : x * v * x⁻¹ ∈ blockU K := (Subgroup.mem_normalizer_iff.mp (hUn hx.2) v).mp (hVU hv)
      refine (hWiff ⟨_, hu⟩).mpr ?_
      rw [hβeq ⟨x, hx.2⟩ ⟨v, hVU hv⟩ ⟨_, hu⟩ rfl]
      exact hPW _ ⟨⟨x, hx.2⟩, hx, rfl⟩ _ (hVW ⟨v, hv⟩)
    calc V.map (MulAut.conj x).toMonoidHom = ⁅V, M0⁆.map (MulAut.conj x).toMonoidHom := by
          rw [h.V_comm]
      _ = ⁅V.map (MulAut.conj x).toMonoidHom, M0⁆ := by rw [Subgroup.map_commutator, hxM0]
      _ ≤ ⁅V ⊔ blockZ K, M0⁆ := Subgroup.commutator_mono hVx le_rfl
      _ ≤ V := hVZM0
  have hMKeq : M ⊓ K = K ⊓ Subgroup.normalizer (V : Set G) :=
    le_antisymm (fun x hx => ⟨hx.2, hMKN hx⟩)
      (fun x hx => ⟨h.V_norm ⟨hKH hx.1, hx.2⟩, hx.1⟩)
  have hψN : ∀ m : ↥M0, (MulAut.conj g⁻¹).toMonoidHom (α (Subgroup.inclusion hM0K m)) ∈ N :=
    fun m => by simpa [MulAut.conj_apply] using hXsub (Subgroup.inclusion hM0K m) m.2
  set ψ : ↥M0 →* ↥N :=
    (((MulAut.conj g⁻¹).toMonoidHom.comp α).comp (Subgroup.inclusion hM0K)).codRestrict N hψN
    with hψ
  have hψv : ∀ m : ↥M0,
      ((ψ m : ↥N) : ↥(StatedSp 2 F)) = g⁻¹ * α (Subgroup.inclusion hM0K m) * g := by
    intro m
    simp [hψ]
  have hψs : Function.Surjective ψ := by
    rintro ⟨n, hn⟩
    obtain ⟨m, hm, hme⟩ := hXmem n hn
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hψv]
    show g⁻¹ * α m * g = n
    rw [hme]
    group
  set φ : ↥M0 →* Matrix.SpecialLinearGroup (Fin 2) F := (blkN 1).comp ψ with hφ
  have hφs : Function.Surjective φ := fun A => by
    obtain ⟨n, hn⟩ := blkN_surjective hK4 1 A
    obtain ⟨m, rfl⟩ := hψs n
    exact ⟨m, hn⟩
  have hpO0 : pCoreOf 2 M0 = (CFSG.pCore 2 ↥M0).map M0.subtype :=
    C2A3Orbits.pCoreOf_eq_map_pCore M0
  have hφk : φ.ker = CFSG.pCore 2 ↥M0 := by
    apply le_antisymm
    · intro m hm
      rw [MonoidHom.mem_ker] at hm
      have hr : ((ψ m : ↥N) : ↥(StatedSp 2 F)) ∈ rad (K := F) 1 := mem_rad (ψ m).2 hm
      have hmT : (m : G) ∈ T := by
        refine ⟨⟨Subgroup.inclusion hM0K m, ⟨_, hr, ?_⟩, rfl⟩, m.2⟩
        rw [hψv]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hmO := hTO hmT
      rw [hpO0] at hmO
      obtain ⟨m', hm', he⟩ := hmO
      rwa [← show m' = m from Subtype.ext he]
    · intro m hm
      set S : Subgroup ↥(StatedSp 2 F) := ((CFSG.pCore 2 ↥M0).map ψ).map N.subtype with hS
      have hSN : S ≤ N := by
        rintro _ ⟨n, -, rfl⟩
        exact n.2
      have hSn : ∀ n ∈ N, ∀ y ∈ S, n * y * n⁻¹ ∈ S := by
        intro n hn y hy
        obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hy
        obtain ⟨m₁, hm₁⟩ := hψs ⟨n, hn⟩
        refine ⟨ψ (m₁ * q * m₁⁻¹), ⟨m₁ * q * m₁⁻¹, CFSG.pCore_normal.conj_mem q hq m₁, rfl⟩, ?_⟩
        simp [map_mul, map_inv, hm₁]
      have hS2 : IsPGroup 2 ↥S := (CFSG.pCore_isPGroup.map ψ).map _
      have hmr : ((ψ m : ↥N) : ↥(StatedSp 2 F)) ∈ rad (K := F) 1 :=
        SpN.le_rad_of_isPGroup hK4 hSN hSn hS2 ⟨ψ m, ⟨m, hm, rfl⟩, rfl⟩
      obtain ⟨hg', hb1⟩ := blkN_eq_one_of_mem_rad hmr
      rw [MonoidHom.mem_ker]
      exact hb1
  have hpsl : IsPSL 2 2 2 (ModO2 M0) :=
    isPSL_two_two_two_of_equiv_sl2 hF'
      ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
  exact ⟨hSp, F, inferInstance, inferInstance, α, β, hF, ⟨hαs, hαk, hβs, hβk, hβeq⟩, hFL, hMKmax,
    hMKeq, hpsl⟩

end CFSG.Quasithin.C41Pf
