module

public import CFSG.Quasithin.Background.SimsE213M
public import CFSG.Quasithin.Vol2.E2FourteenB
public import CFSG.Quasithin.EmptyFaithful.SBd8Psl2
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem inf_eq_inf_normalizer
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g)
    (hZ : V ⊓ conjSubgroup V g ≠ ⊥) :
    M ⊓ I = I ⊓ Subgroup.normalizer (V : Set Γ) := by
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  obtain ⟨hp, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds E2.kgI22One_holds h
    (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) (e ▸ hIV)
  rw [e] at hZ
  exact E2.inf_eq_inf_normalizer_of_central hTI (hp.normalizer_le.trans inf_le_left) hZ inf_le_left
    fun z hz x hx => hp.mem_center hz hx

theorem autI_le_normalizer
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hIV : I = V ⊔ conjSubgroup V g) :
    autI h.elem I ≤ Subgroup.normalizer
      (autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I) : Set (MulAut (IntMod V h.elem))) := by
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  obtain ⟨hp, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds E2.kgI22One_holds h
    (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) (e ▸ hIV)
  have hAN : B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) ≤ Subgroup.normalizer (V : Set Γ) :=
    hp.A_le_pCoreOf.trans hp.pCoreOf_le_normalizer
  have hBN : kerIn (M ⊓ I) I ⊓ V ≤ Subgroup.normalizer (V : Set Γ) :=
    inf_le_right.trans Subgroup.le_normalizer
  have hBC : kerIn (M ⊓ I) I ⊓ V ≤ Subgroup.centralizer (V : Set Γ) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hp.comm hv hb.2
  refine E2.autI_le_normalizer_autI h.elem hp.le_normalizer_P ?_
  rw [e, ← hp.conjSub_kerIn_inf_eq, autI_sup h.elem hBN hAN,
    autI_eq_bot_of_le_centralizer h.elem hBC, bot_sup_eq]

theorem isBorelIn_of_psl_or_sz {H T M V I : Subgroup Γ} (hI : IsInIHTV H T M V I) {k : ℕ}
    (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨-, -, hsyl, -, k', -, hc⟩ := hI
  rcases hc with ⟨-, -, hB⟩ | ⟨-, p, a, hp', hp2, -, ⟨e⟩⟩ | ⟨-, -, -, hB, -⟩
  · exact hB
  · exfalso
    have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
    obtain ⟨hcard, -⟩ := E2.exists_conj_of_mem_center hk hY hS
    have h2 := E2.card_le_two_of_isPGroup_dihedral (hp'.odd_of_ne_two hp2).pow e hS.2.1
    have h3 := Subgroup.card_le_of_le (inf_le_left : E2.star (M ⊓ I) I (T ⊓ I) ⊓
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ≤
        E2.star (M ⊓ I) I (T ⊓ I))
    rw [hcard] at h3
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · exact hB

theorem exists_ne_one_odd_of_card {X : Subgroup Γ} {k : ℕ} (hk : 1 < k)
    (hXc : Nat.card X = 2 ^ k - 1) : ∃ y ∈ X, y ≠ 1 ∧ Odd (orderOf y) := by
  obtain ⟨y, hyX, hy1⟩ : ∃ y ∈ X, y ≠ 1 := by
    by_contra hne
    push Not at hne
    have hXb : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hne
    rw [hXb, Subgroup.card_bot] at hXc
    have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  refine ⟨y, hyX, hy1, ?_⟩
  have h4 : Odd (Nat.card X) := by
    rw [hXc]
    exact Ch3E213M.odd_two_pow_sub_one (by omega)
  exact Odd.of_dvd_nat h4 (Subgroup.orderOf_dvd_natCard X hyX)

theorem not_mem_pCoreOf_of_odd {I : Subgroup Γ} {y : Γ} (hy1 : y ≠ 1) (hyo : Odd (orderOf y)) :
    y ∉ pCoreOf 2 I := by
  intro hyK
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I ⟨y, hyK⟩
  have hn' : y ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact hy1 (E2.eq_one_of_two_pow_of_odd hn' hyo)

theorem inf_centralizer_eq_of_psl
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g)
    (hZ : V ⊓ conjSubgroup V g ≠ ⊥) {k : ℕ} (hk : 1 < k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I)) {X : Subgroup Γ} (hXM : X ≤ M ⊓ I)
    (hXc : Nat.card X = 2 ^ k - 1) :
    V ⊓ conjSubgroup V g = V ⊓ Subgroup.centralizer (X : Set Γ) := by
  have h1 := inf_eq_inf_normalizer h hTI hI hg hIV hZ
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  have hg' : g⁻¹ ∈ I := I.inv_mem hg
  obtain ⟨hp, hVZ, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) hg' hgen
  rw [e]
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hBorel := isBorelIn_of_psl_or_sz hI hk (Or.inl hY)
  obtain ⟨hP2, hVeq⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds hp hsyl hTMI hg' hgen hVZ hMN hBorel hk (Or.inl hY)
  have hPJ := hP2.resolve_right (E2.not_isSz_three_of_isPSL hY)
  have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
  obtain ⟨-, -, hfix, -⟩ := E2.exists_natural_of_psl hp hsyl hg' hgen hMN hJ hPJ hBor hVeq hk hY
  obtain ⟨y, hyX, hy1, hyo⟩ := exists_ne_one_odd_of_card hk hXc
  have hyJ : y ∉ kerIn (M ⊓ I) I := by
    rw [← hJ]
    exact not_mem_pCoreOf_of_odd hy1 hyo
  obtain ⟨hfP, hfV⟩ := hfix y (hXM hyX) hyJ hyo
  refine le_antisymm (fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun x hx => (hp.mem_center hz (hXM hx).2).symm⟩)
    fun v hv => ?_
  have hvy : y * v * y⁻¹ = v := by
    rw [(Subgroup.mem_centralizer_iff.mp hv.2 y hyX), mul_inv_cancel_right]
  have hvJ := hfV v hv.1 hvy
  refine hfP v (Subgroup.mem_sup_left ⟨hvJ, hv.1⟩) ?_
  rw [hvy, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem inf_centralizer_le_of_sz
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hIV : I = V ⊔ conjSubgroup V g) {k : ℕ} (hk : 1 < k) (hY : IsSz k (E2.StarQuot (M ⊓ I) I))
    {X : Subgroup Γ} (hXM : X ≤ M ⊓ I) (hXc : Nat.card X = 2 ^ k - 1) :
    V ⊓ Subgroup.centralizer (X : Set Γ) ≤ V ⊓ pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  obtain ⟨hp, -, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) (e ▸ hIV)
  obtain ⟨y, hyX, hy1, hyo⟩ := exists_ne_one_odd_of_card hk hXc
  rintro v ⟨hv, hvc⟩
  refine ⟨hv, ?_⟩
  by_contra hvJ
  rw [hJ] at hvJ
  have hvI : v ∈ I := hp.V_le hv
  have hyI : y ∈ I := (hXM hyX).2
  set π := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hπ
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e₀⟩⟩ := hY
  let ψ : E2.StarQuot (M ⊓ I) I ≃* ↥(CFSG.Open.Sz a) := e₀.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hv1 : π ⟨v, hvI⟩ ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hvJ
  have hv2 : π ⟨v, hvI⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨v, hvI⟩ : I) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h.elem.2 v hv)
    rw [this, map_one]
  have hord : orderOf (ψ (π ⟨v, hvI⟩)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hv2 hv1
  have hcomm : (⟨y, hyI⟩ : I) * ⟨v, hvI⟩ = ⟨v, hvI⟩ * ⟨y, hyI⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hvc y hyX)
  have hyc : ψ (π ⟨y, hyI⟩) ∈
      Subgroup.centralizer ({ψ (π ⟨v, hvI⟩)} : Set ↥(CFSG.Open.Sz a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun w => ψ (π w)) hcomm
    simpa only [map_mul] using this
  obtain ⟨n, hn⟩ := CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_involution_centralizer ha _
    hord ⟨_, hyc⟩
  have hn' : π ⟨y, hyI⟩ ^ 2 ^ n = 1 := by
    apply ψ.injective
    rw [map_pow, map_one]
    exact congrArg Subtype.val hn
  have hyo' : Odd (orderOf (π ⟨y, hyI⟩)) := by
    have h1 : orderOf (π ⟨y, hyI⟩) ∣ orderOf (⟨y, hyI⟩ : I) := orderOf_map_dvd π _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hyo h1
  have hy' := E2.eq_one_of_two_pow_of_odd hn' hyo'
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← hJ] at hy'
  exact not_mem_pCoreOf_of_odd hy1 hyo hy'

end E214

open E214

theorem e214_one
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI _TI _JI _B _A _P _Z : Subgroup Γ) (_k : ℕ) (hMI : MI = M ⊓ I) (_hTI : _TI = T ⊓ I)
    (_hJI : _JI = kerIn MI I) (_hB : _B = V ⊓ pCoreOf 2 I)
    (_hA : _A = conjSubgroup V g ⊓ pCoreOf 2 I) (_hP : _P = _A ⊔ _B)
    (_hZ : _Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (_k : ℕ∞)) :
    MI = I ⊓ Subgroup.normalizer (V : Set Γ) := by
  rw [hMI]
  exact inf_eq_inf_normalizer h hTI hI hg hIV hZ

theorem e214_six
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (_hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (_hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI _TI _JI _B A _P _Z : Subgroup Γ) (_k : ℕ) (_hMI : MI = M ⊓ I) (_hTI' : _TI = T ⊓ I)
    (_hJI : _JI = kerIn MI I) (_hB : _B = V ⊓ pCoreOf 2 I)
    (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (_hP : _P = A ⊔ _B)
    (_hZ' : _Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (_k : ℕ∞)) :
    autI h.elem A ≤ autI h.elem I ∧
      autI h.elem I ≤ Subgroup.normalizer (autI h.elem A : Set (MulAut (IntMod V h.elem))) := by
  subst hA
  exact ⟨autI_mono h.elem (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)),
    autI_le_normalizer h hI hg hIV⟩

theorem e214_nine_psl
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI _TI _JI _B _A _P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (_hTI' : _TI = T ⊓ I)
    (_hJI : _JI = kerIn MI I) (_hB : _B = V ⊓ pCoreOf 2 I)
    (_hA : _A = conjSubgroup V g ⊓ pCoreOf 2 I) (_hP : _P = _A ⊔ _B)
    (hZdef : Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞)) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
        Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) →
      1 < k → ∀ X : Subgroup Γ, X ≤ MI → Nat.card X = 2 ^ k - 1 →
        Z = V ⊓ Subgroup.centralizer (X : Set Γ) := by
  subst hMI hZdef
  rintro ⟨F, _, _, hF, ⟨θ⟩⟩ hk X hXM hXc
  exact inf_centralizer_eq_of_psl h hTI hI hg hIV hZ hk
    (SBd8.Psl2.isPSL_of_statedSL hk hF θ) hXM hXc

@[expose] def E214NineSz : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ), E2.Hyp28 H T M V → CharTwo H →
    IsTISetIn V M → ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I →
      I = V ⊔ conjSubgroup V g → V ⊓ conjSubgroup V g ≠ ⊥ → ∀ k : ℕ, 1 < k →
        IsSz k (E2.StarQuot (M ⊓ I) I) → ∀ X : Subgroup Γ, X ≤ M ⊓ I →
          Nat.card X = 2 ^ k - 1 →
            V ⊓ pCoreOf 2 I ⊓ Subgroup.centralizer (X : Set Γ) ≤ V ⊓ conjSubgroup V g

theorem e214_nine
    (hSz : E214NineSz)
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (hJI : JI = kerIn MI I) (hB : B = V ⊓ pCoreOf 2 I)
    (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (hP : P = A ⊔ B)
    (hZdef : Z = V ⊓ conjSubgroup V g)
    (hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞)) :
    ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
          Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) ∨
        IsSz k (E2.StarQuot MI I)) →
      1 < k → ∀ X : Subgroup Γ, X ≤ MI → Nat.card X = 2 ^ k - 1 →
        Z = V ⊓ Subgroup.centralizer (X : Set Γ) := by
  rintro (hL | hY) hk1 X hXM hXc
  · exact e214_nine_psl Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB
      hA hP hZdef hk hL hk1 X hXM hXc
  subst hMI hZdef
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  obtain ⟨hp, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds E2.kgI22One_holds h
    (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) (e ▸ hIV)
  have hle := hSz Γ H T M V h hc hTI I g hI hg hIV hZ k hk1 hY X hXM hXc
  have hVB := inf_centralizer_le_of_sz h hI hg hIV hk1 hY hXM hXc
  rw [e] at hle ⊢
  exact le_antisymm (fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hp.mem_center hz (hXM hx).2).symm⟩) fun v hv => hle ⟨hVB hv, hv.2⟩

end CFSG.Quasithin.SimsE2
