module

public import CFSG.Quasithin.Vol2.Ch7Sec77L3C
public import CFSG.Quasithin.Vol2.Ch7Sec77L3K

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem th_pow_three_eq_one
    (hc : S.Coord θ e) :
    θ ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : θ ^ 3 ∈ pCoreOf 2 L :=
    inf_centralizer_L_le hc ⟨L.pow_mem hc.mem 3, th_pow_three_mem hc⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, h1⟩
  exact eq_one_of_odd_of_pow_two_pow (Odd.of_dvd_nat hc.odd (orderOf_pow_dvd 3))
    (by simpa using congrArg Subtype.val hk)

theorem vm_inf_centralizer_eq_bot (hc : S.Coord θ e) :
    S.vm e ⊓ Subgroup.centralizer ({θ} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvθ : v * θ = θ * v := Subgroup.mem_centralizer_singleton_iff.1 hv.2
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_vm hc (y := θ) (m := 1) (by simp) hv.1 hvθ.symm)

theorem le_relIndex_of_vm_le (hc : S.Coord θ e) {X : Subgroup G} (hX : S.vm e ≤ X) :
    16 ≤ (Subgroup.centralizer ({θ} : Set G)).relIndex X := by
  have h1 : (Subgroup.centralizer ({θ} : Set G)).relIndex (S.vm e) = 16 := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, vm_inf_centralizer_eq_bot hc,
      Subgroup.relIndex_bot_left, card_vm]
  rw [← h1]
  exact Subgroup.relIndex_le_of_le_right hX
    ((Subgroup.centralizer _).subgroupOf X).index_ne_zero_of_finite

theorem relIndex_centralizer_V (hc : S.Coord θ e) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex (fsuV T I) = 16 := by
  refine le_antisymm ?_ (le_relIndex_of_vm_le hc vm_le)
  have h1 : (Subgroup.centralizer ({θ} : Set G)).relIndex (S.vm e) ≤ 16 := by
    have := Subgroup.relIndex_dvd_card (Subgroup.centralizer ({θ} : Set G)) (S.vm e)
    rw [card_vm] at this
    exact Nat.le_of_dvd (by norm_num) this
  refine le_trans (relIndex_le_of_forall_conj fun v hv => ?_) h1
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_V0_mul_vm hc hv
  refine ⟨b, hb, ?_⟩
  have haθ : a * θ = θ * a := Subgroup.mem_centralizer_singleton_iff.1 ha.2
  have hbV : b ∈ fsuV T I := vm_le hb
  have hθN : θ ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN (S.L_le_fsuM hc.mem)
  have h2 : b * θ * b⁻¹ * θ⁻¹ ∈ fsuV T I := by
    have h3 : θ * b⁻¹ * θ⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.1 hθN _).1 ((fsuV T I).inv_mem hbV)
    have e : b * θ * b⁻¹ * θ⁻¹ = b * (θ * b⁻¹ * θ⁻¹) := by group
    rw [e]
    exact (fsuV T I).mul_mem hbV h3
  have hcomm : a * (b * θ * b⁻¹ * θ⁻¹) = (b * θ * b⁻¹ * θ⁻¹) * a :=
    congrArg Subtype.val (S.comm.is_comm.comm ⟨a, ha.1⟩ ⟨_, h2⟩)
  calc a * b * θ * (a * b)⁻¹ = a * (b * θ * b⁻¹ * θ⁻¹) * θ * a⁻¹ := by group
    _ = (b * θ * b⁻¹ * θ⁻¹) * (a * θ) * a⁻¹ := by rw [hcomm]; group
    _ = (b * θ * b⁻¹ * θ⁻¹) * (θ * a) * a⁻¹ := by rw [haθ]
    _ = b * θ * b⁻¹ := by group

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem vm_facts (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hL₀K : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ K)
    (hTpK : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hH : K ⊔ T ⊓ Subgroup.centralizer (Vp : Set G) = H) :
    S.vm e ≤ c134Q (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)) K ∧
      (∀ w ∈ S.vm e, w ∈ Subgroup.centralizer (K : Set G) → w = 1) ∧
      S.vm e ≤ Subgroup.centralizer
        (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  have hθK : θ ∈ K := hL₀K (S.th_mem_oTwoUpper hc C.conf.vp_le)
  obtain ⟨hVmU, hVmZ⟩ := C.vm_le_blockU hF hK hθK (S.L_le_fsuM hc.mem) hc.odd (th_not_mem hc)
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Q) := by
    have hKn : (K.subgroupOf (K ⊔ Q)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hQN)
    exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
      (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn)
  have h1 : S.vm e ≤ c134Q (K ⊔ Q) K := hVmU.trans (Subgroup.commutator_mono hOK le_rfl)
  have h2 : ∀ w ∈ S.vm e, w ∈ Subgroup.centralizer (K : Set G) → w = 1 := fun w hw hwK => by
    have : w ∈ S.vm e ⊓ blockZ K := ⟨hw, hVmU hw, hwK⟩
    rw [hVmZ] at this
    exact this
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef, ← S.hQ]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hQTp : Q ≤ Tp :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le C.conf.vp_le_V))
  have hKQH : K ⊔ Q ≤ H := sup_le (le_of_mem_cComp hK) (hQTp.trans C.conf.tp_le_H)
  have hHKQ : H ≤ Subgroup.normalizer ((K ⊔ Q : Subgroup G) : Set G) := by
    rw [← hH]
    exact sup_le (le_sup_left.trans Subgroup.le_normalizer)
      (le_normalizer_sup_of hTpK (inf_le_left.trans hTQ))
  have hOKQ : pCoreOf 2 (K ⊔ Q) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKQH)
      (hHKQ.trans (normalizer_le_normalizer_pCoreOf (r := 2) (K ⊔ Q))) (pCoreOf_isPGroup 2 _)
  obtain ⟨-, hred⟩ := C.isTwoReduced_U hF
  have hOU := CFSG.Quasithin.pCoreOf_le_centralizer_of_isTwoReducedIn hred
  refine ⟨h1, h2, fun w hw => Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 (hOU (hOKQ hx)) w (C.V_le_U (vm_le hw))).symm

theorem inf_centralizer_le_of_sl3
    (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
    (hθK : θ ∈ K) :
    Subgroup.centralizer ({θ} : Set G) ⊓ (T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K) ≤
      pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set ψ := eX.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm with hψ
  have hθ3 := th_pow_three_eq_one hc
  have hθO : θ ∉ pCoreOf 2 K := fun h => th_not_mem hc (C.pCoreOf_le_centralizer hF hK h)
  have hg3 : ψ (QuotientGroup.mk ⟨θ, hθK⟩) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨θ, hθK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
    rw [this, QuotientGroup.mk_one, map_one]
  have hg1 : ψ (QuotientGroup.mk ⟨θ, hθK⟩) ≠ 1 := by
    intro h
    apply hθO
    rw [map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff] at h
    exact coe_mem_pCoreOf h
  have hQ2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    C.conf.sylH.2.1.to_le
      (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le C.conf.vp_le_V)))
  rintro x ⟨hxθ, hxQ, hxK⟩
  obtain ⟨k, hk⟩ := hQ2 ⟨x, hxQ⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxθ' : x * θ = θ * x := Subgroup.mem_centralizer_singleton_iff.1 hxθ
  have ht : ψ (QuotientGroup.mk ⟨x, hxK⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨x, hxK⟩ : ↥K) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, QuotientGroup.mk_one, map_one]
  have hct : ψ (QuotientGroup.mk ⟨x, hxK⟩) * ψ (QuotientGroup.mk ⟨θ, hθK⟩) =
      ψ (QuotientGroup.mk ⟨θ, hθK⟩) * ψ (QuotientGroup.mk ⟨x, hxK⟩) := by
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have : (⟨x, hxK⟩ : ↥K) * ⟨θ, hθK⟩ = ⟨θ, hθK⟩ * ⟨x, hxK⟩ := Subtype.ext hxθ'
    rw [this]
  have h1 := eq_one_of_pow_two_pow_of_commute ht hg3 hg1 hct
  rw [map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff] at h1
  exact coe_mem_pCoreOf h1

theorem not_inf_centralizer_le_of_sl3
    (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (eK : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hCK : K ⊓ Subgroup.centralizer ((omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
      Subgroup.centralizer (fsuV T I : Set G))) : Subgroup G) : Set G) ≤ pCoreOf 2 K)
    (hP : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) (autOn (fsuM T L ⊓ H ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
        Subgroup.centralizer (fsuV T I : Set G))))))
    (hL₀K : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ K) :
    ¬ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊓
      Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 K := by
  classical
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hWdef
  set L₀ := oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) with hL₀def
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hθL₀ : θ ∈ L₀ := S.th_mem_oTwoUpper hc C.conf.vp_le
  have hθK : θ ∈ K := hL₀K hθL₀
  have hθ3 := th_pow_three_eq_one hc
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Q) := by
    have hKn : (K.subgroupOf (K ⊔ Q)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hQN)
    exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
      (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn)
  have hOW : ∀ o ∈ pCoreOf 2 K, o ∈ Subgroup.centralizer (W : Set G) := fun o ho =>
    Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1
        (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf _ hw).2 o (hOK ho)).symm
  set θs : MulAut ↥W := conjAct W ⟨θ, hKW hθK⟩ with hθs
  have hθsK : θs ∈ autOn K W := CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, hθK, rfl⟩
  have hθs3 : θs ^ 3 = 1 := by
    rw [hθs, ← map_pow]
    have : (⟨θ, hKW hθK⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hθ3)
    rw [this, map_one]
  have hθs1 : θs ≠ 1 := by
    intro h
    have h1 : θ ∈ Subgroup.centralizer (W : Set G) :=
      (CFSG.QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (W : Set G)) le_rfl
        ⟨θ, hKW hθK⟩).1 h
    exact th_not_mem hc (C.pCoreOf_le_centralizer hF hK (hCK ⟨hθK, h1⟩))
  have hθO2 : Subgroup.zpowers θ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    (Subgroup.zpowers_le).mpr (le_normalizer_pCoreOf 2 K hθK)
  have hL₀ : L₀ ≤ pCoreOf 2 K ⊔ Subgroup.zpowers θ :=
    C.oTwoUpper_le_sup.trans (sup_le_sup_right hle _)
  have hconj : ∀ g : ↥(Subgroup.normalizer (W : Set G)), (g : G) ∈ fsuM T L ⊓ H ⊓ K →
      ∃ j : ℕ, conjAct W g * θs * (conjAct W g)⁻¹ = θs ^ j := by
    intro g hg
    have hgL₀ : (g : G) ∈ Subgroup.normalizer (L₀ : Set G) :=
      normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨S.fsuM_le_normalizer_L hg.1.1, Subgroup.le_normalizer (C.conf.hHG hg.1.2)⟩)
    have h1 : (g : G) * θ * (g : G)⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.1 hgL₀ θ).1 hθL₀
    have h2 := hL₀ h1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hθO2] at h2
    obtain ⟨o, ho, z, hz, hoz⟩ := h2
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, θ ^ j = z := (mem_powers_iff_mem_zpowers).mpr hz
    refine ⟨j, ?_⟩
    have hoN : o ∈ Subgroup.normalizer (W : Set G) := hKW (pCoreOf_le 2 K ho)
    have ho1 : conjAct W ⟨o, hoN⟩ = 1 :=
      (CFSG.QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (W : Set G)) le_rfl
        ⟨o, hoN⟩).2 (hOW o ho)
    have e : g * ⟨θ, hKW hθK⟩ * g⁻¹ = ⟨o, hoN⟩ * ⟨θ, hKW hθK⟩ ^ j := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact hoz.symm)
    calc conjAct W g * θs * (conjAct W g)⁻¹ = conjAct W (g * ⟨θ, hKW hθK⟩ * g⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = θs ^ j := by rw [e, map_mul, map_pow, ho1, one_mul]
  obtain ⟨⟨-, S0, hS0, hS0P⟩, -, -⟩ := hP
  have hS0P' : ∀ s ∈ S0, s ∈ autOn (fsuM T L ⊓ H ⊓ K) W := fun s hs =>
    hS0P ⟨hS0.1 hs, Subgroup.le_normalizer hs⟩
  have hsθ : ∀ s ∈ S0, s * θs * s⁻¹ = θs ∨ s * θs * s⁻¹ = θs ^ 2 := by
    intro s hs
    obtain ⟨g, hgP, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 (hS0P' s hs)
    obtain ⟨j, hj⟩ := hconj g hgP
    have e : θs ^ j = θs ^ (j % 3) := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hθs3, one_pow, one_mul]
    rw [hj, e]
    have hj3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : j % 3
    · exfalso
      apply hθs1
      have h2 : conjAct W g * θs * (conjAct W g)⁻¹ = 1 := by rw [hj, e]; exact pow_zero θs
      calc θs = (conjAct W g)⁻¹ * (conjAct W g * θs * (conjAct W g)⁻¹) * conjAct W g := by
            group
        _ = 1 := by rw [h2]; group
    · left
      rw [pow_one]
    · right
      rfl
  have hKs : Nat.card ↥(autOn K W) = 168 := by
    rw [Nat.card_congr eK.toEquiv,
      Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv,
      card_statedSL_three_two]
  have hS0card : 2 < Nat.card S0 := by
    obtain ⟨a, ha⟩ := hS0.2.1.exists_card_eq
    have h1 := Subgroup.card_mul_index (S0.subgroupOf (autOn K W))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0.1).toEquiv, ha, hKs] at h1
    by_contra hle2
    push Not at hle2
    rw [ha] at hle2
    have ha1 : a ≤ 1 := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
      omega
    apply hS0.2.2
    interval_cases a
    · simp only [pow_zero, one_mul] at h1
      omega
    · simp only [pow_one] at h1
      omega
  have hninj : ¬ Function.Injective
      (fun s : ↥S0 => decide ((s : MulAut ↥W) * θs * (s : MulAut ↥W)⁻¹ = θs)) := by
    intro hinj
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  simp only [Function.Injective, not_forall] at hninj
  obtain ⟨s₁, s₂, hf, hne⟩ := hninj
  have hθs2 : θs ^ 2 ≠ θs := by
    intro h
    apply hθs1
    have h' : θs * θs = θs * 1 := by rw [mul_one, ← pow_two]; exact h
    exact mul_left_cancel h'
  have heq : (s₁ : MulAut ↥W) * θs * (s₁ : MulAut ↥W)⁻¹ =
      (s₂ : MulAut ↥W) * θs * (s₂ : MulAut ↥W)⁻¹ := by
    rcases hsθ s₁ s₁.2 with h1 | h1 <;> rcases hsθ s₂ s₂.2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      simp [h1, h2, hθs2] at hf
    · exfalso
      simp [h1, h2, hθs2] at hf
    · rw [h1, h2]
  set t : MulAut ↥W := (s₁ : MulAut ↥W)⁻¹ * s₂ with htdef
  have htS : t ∈ S0 := S0.mul_mem (S0.inv_mem s₁.2) s₂.2
  have ht1 : t ≠ 1 := by
    intro h
    exact hne (Subtype.ext (inv_mul_eq_one.1 h))
  have htc : t * θs = θs * t := by
    rw [htdef]
    calc (s₁ : MulAut ↥W)⁻¹ * s₂ * θs =
          (s₁ : MulAut ↥W)⁻¹ * ((s₂ : MulAut ↥W) * θs * (s₂ : MulAut ↥W)⁻¹) * s₂ := by group
      _ = (s₁ : MulAut ↥W)⁻¹ * ((s₁ : MulAut ↥W) * θs * (s₁ : MulAut ↥W)⁻¹) * s₂ := by
          rw [heq]
      _ = θs * ((s₁ : MulAut ↥W)⁻¹ * s₂) := by group
  obtain ⟨k, hk⟩ := hS0.2.1 ⟨t, htS⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : eK ⟨t, hS0.1 htS⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, hS0.1 htS⟩ : ↥(autOn K W)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    rw [this, map_one]
  have h2 : eK ⟨θs, hθsK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨θs, hθsK⟩ : ↥(autOn K W)) ^ 3 = 1 := Subtype.ext (by simpa using hθs3)
    rw [this, map_one]
  have h3 : eK ⟨θs, hθsK⟩ ≠ 1 := fun h =>
    hθs1 (congrArg Subtype.val ((map_eq_one_iff eK eK.injective).1 h))
  have h4 : eK ⟨t, hS0.1 htS⟩ * eK ⟨θs, hθsK⟩ = eK ⟨θs, hθsK⟩ * eK ⟨t, hS0.1 htS⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htc
  have h5 := eq_one_of_pow_two_pow_of_commute h1 h2 h3 h4
  exact ht1 (congrArg Subtype.val ((map_eq_one_iff eK eK.injective).1 h5))

theorem le_relIndex_Q_of_sl3
    (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (eK : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hCK : K ⊓ Subgroup.centralizer ((omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
      Subgroup.centralizer (fsuV T I : Set G))) : Subgroup G) : Set G) ≤ pCoreOf 2 K)
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
    (hP : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) (autOn (fsuM T L ⊓ H ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
        Subgroup.centralizer (fsuV T I : Set G))))))
    (hL₀K : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ K) :
    32 ≤ (Subgroup.centralizer ({θ} : Set G)).relIndex
      (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set Cθ := Subgroup.centralizer ({θ} : Set G) with hCθ
  have hne : ∀ {A B : Subgroup G}, A.relIndex B ≠ 0 := fun {A B} =>
    (A.subgroupOf B).index_ne_zero_of_finite
  have hθK : θ ∈ K := hL₀K (S.th_mem_oTwoUpper hc C.conf.vp_le)
  have hOQ : pCoreOf 2 K ≤ Q := le_inf
    ((CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
      (C.conf.sylH.pCoreOf_le.trans inf_le_left))
    (C.pCoreOf_le_centralizer hF hK)
  have hOQK : pCoreOf 2 K ≤ Q ⊓ K := le_inf hOQ (pCoreOf_le 2 K)
  have h1 : Cθ.relIndex (Q ⊓ K) ≤ Cθ.relIndex Q :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have h2 : Cθ ⊓ (Q ⊓ K) = Cθ ⊓ pCoreOf 2 K :=
    le_antisymm (le_inf inf_le_left (C.inf_centralizer_le_of_sl3 hF hK eX hθK))
      (inf_le_inf_left _ hOQK)
  have h3 : Cθ.relIndex (Q ⊓ K) = Cθ.relIndex (pCoreOf 2 K) * (pCoreOf 2 K).relIndex (Q ⊓ K) := by
    rw [← Subgroup.inf_relIndex_right Cθ (Q ⊓ K), h2,
      ← Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right hOQK, Subgroup.inf_relIndex_right]
  obtain ⟨hVmU, -⟩ := C.vm_le_blockU hF hK hθK (S.L_le_fsuM hc.mem) hc.odd (th_not_mem hc)
  have h4 : 16 ≤ Cθ.relIndex (pCoreOf 2 K) :=
    le_relIndex_of_vm_le hc (hVmU.trans (c134Q_le_pCoreOf (le_refl K)))
  have h5 : 2 ≤ (pCoreOf 2 K).relIndex (Q ⊓ K) := by
    have hne1 : (pCoreOf 2 K).relIndex (Q ⊓ K) ≠ 1 := by
      intro h
      apply C.not_inf_centralizer_le_of_sl3 hF hK hQN eK hCK hP hL₀K
      refine le_trans (le_inf ?_ ?_) (Subgroup.relIndex_eq_one.1 h)
      ·
        have hOL : pCoreOf 2 L ≤ Q := by
          rw [hQdef, ← S.hQ]
          have hLn : (L.subgroupOf (fsuL0 T L ⊔ T)).Normal := by
            rw [← S.hL]
            exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
              (sup_le Subgroup.le_normalizer S.T_le_normalizer_L)
          rw [← S.hL] at hLn ⊢
          exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
            (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hLn)
        exact (le_inf (inf_le_left.trans ((oTwoUpper_le _).trans inf_le_left)) inf_le_right).trans
          ((inf_centralizer_L_le hc).trans hOL)
      · exact inf_le_left.trans hL₀K
    have hne0 : (pCoreOf 2 K).relIndex (Q ⊓ K) ≠ 0 := hne
    omega
  calc 32 = 16 * 2 := by norm_num
    _ ≤ Cθ.relIndex (pCoreOf 2 K) * (pCoreOf 2 K).relIndex (Q ⊓ K) := Nat.mul_le_mul h4 h5
    _ = Cθ.relIndex (Q ⊓ K) := h3.symm
    _ ≤ Cθ.relIndex Q := h1

theorem relIndex_Q_le_of_sl3
    (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
    (hL₀K : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ K)
    (hi : IsC134Case 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))
      (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) K) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex
      (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤ 8 * 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  have hθK : θ ∈ K := hL₀K (S.th_mem_oTwoUpper hc C.conf.vp_le)
  have hθO : θ ∉ pCoreOf 2 K := fun h => th_not_mem hc (C.pCoreOf_le_centralizer hF hK h)
  have hθR : θ ∈ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
    S.L_le_normalizer_Q hc.mem
  have hR2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    C.conf.sylH.2.1.to_le
      (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le C.conf.vp_le_V)))
  have hOR : pCoreOf 2 K ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := le_inf
    ((CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
      (C.conf.sylH.pCoreOf_le.trans inf_le_left))
    (C.pCoreOf_le_centralizer hF hK)
  have hKX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 :=
    (Nat.card_congr eX.toEquiv).trans card_statedSL_three_two
  exact relIndex_le_of_c134Two hθK (th_pow_three_eq_one hc) hθO hθR hR2 hQN hOR hKX hi

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
