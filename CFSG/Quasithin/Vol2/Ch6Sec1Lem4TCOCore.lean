module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOIrr
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOXb

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L216 CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self unipSL_zero)
open scoped MatrixGroups Matrix Pointwise

theorem two_elem_upper_unip {F : Type} [Field F] [Finite F] [CharP F 2] {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    ∃ b : F, g = unipSL b := by
  have hfix := (upper_pow hg (2 ^ k)).2
  rw [hk] at hfix
  have h1 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 ^ k = 1 := by
    simpa using hfix.symm
  have h2 : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h2)
  exact ⟨_, eq_unipSL_of_upper hg h3⟩


set_option maxHeartbeats 400000 in
theorem l216CoreFact_holds : L216CoreFact := by
  intro G _ _ T M L V X h horth hXL _hX2 hX5 hXn hTX
  obtain ⟨F, _, _, _, hF, ψ, Y, -, -, -, -, hψ⟩ :=
    IsOrthCh5.exists_sylowCoord (m := 2) (show IsOrthCh5 L V (2 * 2) from horth)
      h.isSylowTwoOf_inf_ch6
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.L_le_normalizer
  have hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := h.sup_inf_centralizer_le_T_ch6
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hTL2 : IsPGroup 2 ↥(T ⊓ L) := by
    intro x
    obtain ⟨k, hk⟩ := hT2 ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hV2 : IsPGroup 2 ↥V := fun v => by
    obtain ⟨k, hk⟩ := hT2 ⟨(v : G), h.le_T v.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hVne : V ≠ ⊥ := h.ne_bot
  have hTXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTX
  have hne : Ub T hLV ψ hXL ≠ ⊥ := Ub_ne_bot hLV ψ hXL hF16 hC hψ hTX hX5
  have hsup : ∀ y ∈ Xb hLV ψ hXL, (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    fun y hy => Xb_le_borel hLV ψ hXL hne hC hψ hXn hy
  obtain ⟨s, hsX, hζ5, hζ1⟩ := exists_zeta hLV ψ hXL hF16 hC hψ hTX hXn hX5
  have hU : ∀ b : F, unipSL b ∈ Xb hLV ψ hXL := fun b =>
    Ub_le_Xb hLV ψ hXL (unip_mem_Ub hLV ψ hXL hF16 hC hψ hXn hne hsX (hsup s hsX) hζ5 hζ1 b)
  have hXTL : X ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    X_le_normalizer_TL hLV ψ hXL hC hψ hsup
  have hTTL : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro s' hs'
    refine ⟨T.mul_mem (T.mul_mem ht hs'.1) (T.inv_mem ht), ?_⟩
    have htN : t ∈ Subgroup.normalizer (L : Set G) := h.toHyp5_0_1.normal (h.T_le ht)
    exact (Subgroup.mem_normalizer_iff.mp htN s').mp hs'.2
  have hA : ∀ y : ↥(autOn L V), (y : MulAut V) ∈ autOn X V → ψ y ∈ Xb hLV ψ hXL := by
    intro y hy
    obtain ⟨n, hnX, hn⟩ := AutOn.mem_autOn_iff.mp hy
    have hnL : (n : G) ∈ L := hXL hnX
    have e : y = autHom hLV ⟨(n : G), hnL⟩ := Subtype.ext (by rw [← hn]; rfl)
    rw [e, ← coordHom_apply]
    exact (mem_Xb_iff hLV ψ hXL _).mpr ⟨⟨(n : G), hnX⟩, rfl⟩
  have hB : ∀ y : ↥(autOn L V), ψ y ∈ Xb hLV ψ hXL → (y : MulAut V) ∈ autOn X V := by
    intro y hy
    obtain ⟨x, hx⟩ := (mem_Xb_iff hLV ψ hXL _).mp hy
    have e : y = autHom hLV ⟨(x : G), hXL x.2⟩ := ψ.injective hx.symm
    rw [e]
    exact AutOn.conjAct_mem_autOn_of_mem (hLV (hXL x.2)) x.2
  have hGXnorm : ∀ γ ∈ autOn (X ⊔ T) V, ∀ x ∈ autOn X V, γ * x * γ⁻¹ ∈ autOn X V := by
    intro γ hγ x hx
    obtain ⟨n, hnXT, rfl⟩ := AutOn.mem_autOn_iff.mp hγ
    have hcn := conjAct_mem_normalizer_autOn n (hTXN hnXT)
    exact (Subgroup.mem_normalizer_iff.mp hcn x).mp hx
  have hUGX : ∀ u ∈ autOn (T ⊓ L) V, u ∈ autOn X V := by
    intro u hu
    have huL : u ∈ autOn L V := AutOn.autOn_mono inf_le_right hu
    obtain ⟨b, hb⟩ := (hψ ⟨u, huL⟩).mp hu
    exact hB ⟨u, huL⟩ (by rw [hb]; exact hU b)
  have hQGX : ∀ y ∈ pCoreOf 2 (autOn (X ⊔ T) V), y ∈ autOn X V → y ∈ autOn (T ⊓ L) V := by
    intro y hyQ hyX
    have hyL : y ∈ autOn L V := AutOn.autOn_mono hXL hyX
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autOn (X ⊔ T) V)) ⟨y, hyQ⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hup : (ψ ⟨y, hyL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hsup _ (hA ⟨y, hyL⟩ hyX)
    have hpow : ψ ⟨y, hyL⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨y, hyL⟩ : ↥(autOn L V)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
      rw [this, map_one]
    obtain ⟨b, hb⟩ := two_elem_upper_unip hup hpow
    exact (hψ ⟨y, hyL⟩).mpr ⟨b, hb⟩
  have h2 : autOn (T ⊓ L) V ≤ pCoreOf 2 (autOn (X ⊔ T) V) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (AutOn.autOn_mono (inf_le_left.trans le_sup_right)) ?_ (AutOn.isPGroup_autOn hTL2)
    intro γ hγ
    obtain ⟨n, hnXT, rfl⟩ := AutOn.mem_autOn_iff.mp hγ
    exact conjAct_mem_normalizer_autOn n (sup_le hXTL hTTL hnXT)
  have h1 : pCoreOf 2 (autOn (X ⊔ T) V) ≤ autOn (T ⊓ L) V := by
    intro q hq
    have hqΓ : q ∈ autOn (X ⊔ T) V := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    have hQnorm : ∀ γ ∈ autOn (X ⊔ T) V, ∀ y ∈ pCoreOf 2 (autOn (X ⊔ T) V),
        γ * y * γ⁻¹ ∈ pCoreOf 2 (autOn (X ⊔ T) V) := fun γ hγ y hy =>
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hγ) y).mp hy
    obtain ⟨xs, hxs⟩ := (mem_Xb_iff hLV ψ hXL s).mp hsX
    set σ₀ : ↥(autOn L V) := autHom hLV ⟨(xs : G), hXL xs.2⟩ with hσ₀def
    have hψσ₀ : ψ σ₀ = s := hxs
    have hσ₀X : (σ₀ : MulAut V) ∈ autOn X V :=
      AutOn.conjAct_mem_autOn_of_mem (hLV (hXL xs.2)) xs.2
    have hσ₀Γ : (σ₀ : MulAut V) ∈ autOn (X ⊔ T) V := AutOn.autOn_mono le_sup_left hσ₀X
    have hcomm1 : q * (σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹ ∈ autOn (T ⊓ L) V := by
      apply hQGX
      · have e : q * (σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹ =
            q * ((σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 (autOn (X ⊔ T) V)).mul_mem hq
          (hQnorm _ hσ₀Γ q⁻¹ ((pCoreOf 2 (autOn (X ⊔ T) V)).inv_mem hq))
      · have e : q * (σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹ =
            (q * (σ₀ : MulAut V) * q⁻¹) * (σ₀ : MulAut V)⁻¹ := by group
        rw [e]
        exact (autOn X V).mul_mem (hGXnorm q hqΓ _ hσ₀X) ((autOn X V).inv_mem hσ₀X)
    have hcL : q * (σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹ ∈ autOn L V :=
      AutOn.autOn_mono inf_le_right hcomm1
    obtain ⟨b, hb⟩ := (hψ ⟨_, hcL⟩).mp hcomm1
    have hqσ : q * (σ₀ : MulAut V) * q⁻¹ = (q * (σ₀ : MulAut V) * q⁻¹ * (σ₀ : MulAut V)⁻¹) *
        (σ₀ : MulAut V) := by group
    have hqσL : q * (σ₀ : MulAut V) * q⁻¹ ∈ autOn L V := by
      rw [hqσ]
      exact (autOn L V).mul_mem hcL σ₀.2
    have hu10 : ((unipSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [coe_unipSL]
      simp
    have hu00 : ((unipSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      rw [coe_unipSL]
      simp
    have hχ1 : ((ψ ⟨q * (σ₀ : MulAut V) * q⁻¹, hqσL⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (s : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have e : (⟨q * (σ₀ : MulAut V) * q⁻¹, hqσL⟩ : ↥(autOn L V)) =
          ⟨_, hcL⟩ * σ₀ := Subtype.ext hqσ
      rw [e, map_mul, hb, hψσ₀, upper_mul_zero_zero hu10 (hsup s hsX), hu00, one_mul]
    obtain ⟨n, hnXT, hqn⟩ := AutOn.mem_autOn_iff.mp hqΓ
    have hnXT' : (n : G) ∈ (X : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X T hTX]
      exact hnXT
    obtain ⟨xq, hxq, tq, htq, hxt⟩ := Set.mem_mul.mp hnXT'
    have hN1 : xq ∈ Subgroup.normalizer (V : Set G) := hLV (hXL hxq)
    have hN2 : tq ∈ Subgroup.normalizer (V : Set G) := h.T_le_normalizer htq
    have hqeq : q = conjAct V ⟨xq, hN1⟩ * conjAct V ⟨tq, hN2⟩ := by
      rw [← hqn, ← map_mul]
      congr 1
      exact Subtype.ext hxt.symm
    set xh : MulAut V := conjAct V ⟨xq, hN1⟩ with hxhdef
    set th : MulAut V := conjAct V ⟨tq, hN2⟩ with hthdef
    have hxhX : xh ∈ autOn X V := AutOn.conjAct_mem_autOn_of_mem hN1 hxq
    have hxhL : xh ∈ autOn L V := AutOn.autOn_mono hXL hxhX
    have htL : tq ∈ Subgroup.normalizer (L : Set G) := h.toHyp5_0_1.normal (h.T_le htq)
    have hthN : th ∈ Subgroup.normalizer ((autOn L V : Subgroup (MulAut V)) : Set (MulAut V)) :=
      conjAct_mem_normalizer_autOn ⟨tq, hN2⟩ htL
    have hthU : th ∈ Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) :
        Set (MulAut V)) :=
      conjAct_mem_normalizer_autOn ⟨tq, hN2⟩ (hTTL htq)
    have hthΓ : th ∈ autOn (X ⊔ T) V := AutOn.conjAct_mem_autOn_of_mem hN2 ((le_sup_right : T ≤ X ⊔ T) htq)
    obtain ⟨hh, σ, hhup, hformula, -⟩ :=
      exists_upper_of_normalizes (F := F) (n := 4) (by norm_num) (by rw [hF16]; norm_num) ψ hψ
        ⟨th, hthN⟩ hthU
    have hτX : th * (σ₀ : MulAut V) * th⁻¹ ∈ autOn X V := hGXnorm th hthΓ _ hσ₀X
    have hτup : ((ψ ((autOn L V).normalizerMonoidHom ⟨th, hthN⟩ σ₀) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      apply hsup
      apply hA
      exact hτX
    have hxup : ((ψ ⟨xh, hxhL⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
      hsup _ (hA ⟨xh, hxhL⟩ hxhX)
    have hχτ : ((ψ ((autOn L V).normalizerMonoidHom ⟨th, hthN⟩ σ₀) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = (s : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have e2 : (⟨q * (σ₀ : MulAut V) * q⁻¹, hqσL⟩ : ↥(autOn L V)) =
          ⟨xh, hxhL⟩ * (autOn L V).normalizerMonoidHom ⟨th, hthN⟩ σ₀ * ⟨xh, hxhL⟩⁻¹ := by
        apply Subtype.ext
        show q * (σ₀ : MulAut V) * q⁻¹ = xh * (th * (σ₀ : MulAut V) * th⁻¹) * xh⁻¹
        rw [hqeq]
        group
      rw [← hχ1, e2, map_mul, map_mul, map_inv]
      exact (upper_conj_zero_zero hτup hxup).symm
    have hmapentry : ∀ g : SL(2, F), ((Matrix.SpecialLinearGroup.map σ.toRingHom g : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F).map σ := fun g => by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      rfl
    have hψσ₀up : ((ψ σ₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [hψσ₀]
      exact hsup s hsX
    have hmapup : ((Matrix.SpecialLinearGroup.map σ.toRingHom (ψ σ₀) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [hmapentry]
      simp [Matrix.map_apply, hψσ₀up]
    have hmap00 : ((Matrix.SpecialLinearGroup.map σ.toRingHom (ψ σ₀) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = σ ((s : Matrix (Fin 2) (Fin 2) F) 0 0) := by
      rw [hmapentry, hψσ₀]
      simp [Matrix.map_apply]
    have hσζ : σ ((s : Matrix (Fin 2) (Fin 2) F) 0 0) = (s : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      rw [← hmap00, ← hχτ, hformula σ₀, upper_conj_zero_zero hmapup hhup]
    have hσid : ∀ x : F, σ x = x := fun x =>
      ringHom_eq_id_of_mul hζ5 hζ1 hF16 σ.toRingHom hσζ x
    have hmapid : ∀ g : SL(2, F), Matrix.SpecialLinearGroup.map σ.toRingHom g = g := by
      intro g
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [hmapentry]
      simp [Matrix.map_apply, hσid]
    have hformula' : ∀ y : ↥(autOn L V),
        ψ ((autOn L V).normalizerMonoidHom ⟨th, hthN⟩ y) = hh * ψ y * hh⁻¹ := by
      intro y
      rw [hformula y, hmapid]
    set ℓ : ↥(autOn L V) := ψ.symm hh with hℓdef
    have hψℓ : ψ ℓ = hh := by
      rw [hℓdef, MulEquiv.apply_symm_apply]
    have hcommθ : ∀ y ∈ autOn L V, y * ((ℓ : MulAut V)⁻¹ * th) = ((ℓ : MulAut V)⁻¹ * th) * y := by
      intro y hy
      have e : (autOn L V).normalizerMonoidHom ⟨th, hthN⟩ ⟨y, hy⟩ = ℓ * ⟨y, hy⟩ * ℓ⁻¹ := by
        apply ψ.injective
        rw [hformula' ⟨y, hy⟩, map_mul, map_mul, map_inv, hψℓ]
      have e0 : th * y * th⁻¹ = (ℓ : MulAut V) * y * (ℓ : MulAut V)⁻¹ := congrArg Subtype.val e
      have e' : th * y = (ℓ : MulAut V) * y * (ℓ : MulAut V)⁻¹ * th := by
        calc th * y = (th * y * th⁻¹) * th := by group
          _ = (ℓ : MulAut V) * y * (ℓ : MulAut V)⁻¹ * th := by rw [e0]
      apply Eq.symm
      calc ((ℓ : MulAut V)⁻¹ * th) * y = (ℓ : MulAut V)⁻¹ * (th * y) := by group
        _ = (ℓ : MulAut V)⁻¹ * ((ℓ : MulAut V) * y * (ℓ : MulAut V)⁻¹ * th) := by rw [e']
        _ = y * ((ℓ : MulAut V)⁻¹ * th) := by group
    obtain ⟨k, hk⟩ := hT2 ⟨tq, htq⟩
    have htk : tq ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have htpow : th ^ 2 ^ k = 1 := by
      rw [hthdef, ← map_pow]
      have h0 : (⟨tq, hN2⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using htk)
      rw [h0, map_one]
    have hcommℓ : Commute (ℓ : MulAut V) ((ℓ : MulAut V)⁻¹ * th) := hcommθ _ ℓ.2
    have hθpow_eq : ((ℓ : MulAut V)⁻¹ * th) ^ 2 ^ k = ((ℓ : MulAut V) ^ 2 ^ k)⁻¹ := by
      have ht : th = (ℓ : MulAut V) * ((ℓ : MulAut V)⁻¹ * th) := by group
      have hpow := hcommℓ.mul_pow (2 ^ k)
      rw [← ht, htpow] at hpow
      exact eq_inv_of_mul_eq_one_right hpow.symm
    have hzL : ((ℓ : MulAut V)⁻¹ * th) ^ 2 ^ k ∈ autOn L V := by
      rw [hθpow_eq]
      exact (autOn L V).inv_mem ((autOn L V).pow_mem ℓ.2 _)
    have hzcent : ∀ x : SL(2, F),
        ψ ⟨_, hzL⟩ * x = x * ψ ⟨_, hzL⟩ := by
      intro x
      obtain ⟨y, rfl⟩ := ψ.surjective x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hc : Commute (y : MulAut V) (((ℓ : MulAut V)⁻¹ * th) ^ 2 ^ k) :=
        (show Commute (y : MulAut V) ((ℓ : MulAut V)⁻¹ * th) from hcommθ _ y.2).pow_right _
      exact hc.symm.eq
    have hz1 : ((ℓ : MulAut V)⁻¹ * th) ^ 2 ^ k = 1 := by
      have hψz : ψ ⟨_, hzL⟩ = 1 := eq_one_of_central hzcent
      have : (⟨_, hzL⟩ : ↥(autOn L V)) = 1 := ψ.injective (by rw [hψz, map_one])
      exact congrArg Subtype.val this
    have hθ1 : (ℓ : MulAut V)⁻¹ * th = 1 :=
      eq_one_of_two_pow_centralizes horth hLV hV2 hVne _ hz1 hcommθ
    have hthℓ : th = (ℓ : MulAut V) := by
      calc th = (ℓ : MulAut V) * ((ℓ : MulAut V)⁻¹ * th) := by group
        _ = (ℓ : MulAut V) := by rw [hθ1, mul_one]
    obtain ⟨ℓ2, hℓ2L, hℓ2⟩ := AutOn.mem_autOn_iff.mp ℓ.2
    have hcj : conjAct V ℓ2 = conjAct V ⟨tq, hN2⟩ := by
      rw [hℓ2]
      exact hthℓ.symm
    have hcent := inv_mul_mem_centralizer hcj
    have hmemLT : ((ℓ2⁻¹ * ⟨tq, hN2⟩ : Subgroup.normalizer (V : Set G)) : G) ∈
        (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, hcent⟩
      exact (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((le_sup_left : L ≤ L ⊔ T) hℓ2L)) ((le_sup_right : T ≤ L ⊔ T) htq)
    have hT' := hC hmemLT
    have hℓ2T : (ℓ2 : G) ∈ T := by
      have e : (ℓ2 : G) = tq * (((ℓ2⁻¹ * ⟨tq, hN2⟩ : Subgroup.normalizer (V : Set G)) : G))⁻¹ := by
        simp [mul_assoc]
      rw [e]
      exact T.mul_mem htq (T.inv_mem hT')
    have hthU' : th ∈ autOn (T ⊓ L) V := by
      have hm : conjAct V ℓ2 ∈ autOn (T ⊓ L) V := AutOn.conjAct_mem_autOn_of_mem ℓ2.2 ⟨hℓ2T, hℓ2L⟩
      rw [hcj] at hm
      exact hm
    have hqX : q ∈ autOn X V := by
      rw [hqeq]
      exact (autOn X V).mul_mem hxhX (hUGX _ hthU')
    exact hQGX q hq hqX
  exact le_antisymm h1 h2



end CFSG.Quasithin.H13.T614
