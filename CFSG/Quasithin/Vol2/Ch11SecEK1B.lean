module

public import CFSG.Quasithin.Vol2.Ch11SecAKA8
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11SecAKA2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

theorem factParInSp4_holds : FactParInSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU _ s hs hcomm
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (KGNat.four_le_card hn hK)
  have hpt := KGNat.factPointSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hfix := KGNat.factRadicalFixedSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hτZ : s ∈ SecA.stabW (⊥ : Subgroup W) :=
    SecA.mem_stabW.mpr fun z => ⟨fun hz => bot_maps s z hz, fun hz => by
      have h1 := bot_maps s⁻¹ _ hz
      rwa [MulAut.inv_apply_self] at h1⟩
  have hτ2 : ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hτc : ∀ x : ↥(perfectCore (H ⊓ SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ SecA.stabW U)) ∧
          s * (x : MulAut W) * s⁻¹ = (y : MulAut W) * x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hcomm x x.2)
    refine ⟨y, by exact hy, ?_⟩
    have hyx' : (y : MulAut W) = s * x * s⁻¹ * (x : MulAut W)⁻¹ := hyx
    rw [hyx', inv_mul_cancel_right]
  obtain ⟨f, hf, g, -, hUeq⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU
  obtain ⟨N, -, hact⟩ := KGNat.KA.exists_core hK4 hf g hUeq hfix hpt hτ2 hτZ (hSH s hs) hτc
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hseq : s = psiSp π g N := MulEquiv.ext fun w => hinj _ _ (hact w)
  rw [hseq, psiSp_apply]
  exact (π (g * N * g⁻¹)).2

theorem factParInG2_holds : FactParInG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU s hs hcomm
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 : SecA.IsFlagW H P ⊥ (Nat.card K) 1 U := by rw [hK]; exact hU
  have hUeq := eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU1
  subst hUeq
  have hs' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have hsZW : s ∈ SecA.stabW (⊥ : Subgroup W) :=
    SecA.mem_stabW.mpr fun z => ⟨fun hz => bot_maps s z hz, fun hz => by
      have h1 := bot_maps s⁻¹ _ hz
      rwa [MulAut.inv_apply_self] at h1⟩
  have hU₃f : SecA.IsFlagW H P ⊥ (2 ^ n) 3 (hf.pre (gmapG g (stdF K 3)).toAddSubgroup) := by
    rw [← hK]
    exact isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 3) (card_stdF (by norm_num))
  have hsU₃ := (factN13G2_holds K n hn hK W hW H ⊥ π hπ P hP _ _ hU hU₃f s hsZW
    (hSH s hs)).mp (hSU hs)
  have hx0 : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hx0 s (bot_maps s) (bot_maps s⁻¹) hs'
  have hσid := sigma_eq_id_of_centralizesG h4 hf hc0 hc1 g (bot_maps s) (hSU hs) hsU₃ hcomm hσ
  set T := hf.autMap s (bot_maps s) with hTdef
  have hTf : ∀ w, T (f w) = f (s w) := hf.autMap_apply s (bot_maps s)
  have hT'f : ∀ w, hf.autMap s⁻¹ (bot_maps s⁻¹) (f w) = f (s⁻¹ w) :=
    hf.autMap_apply s⁻¹ (bot_maps s⁻¹)
  let TL : (Ix3 → K) ≃ₗ[K] (Ix3 → K) :=
    { toFun := T
      invFun := hf.autMap s⁻¹ (bot_maps s⁻¹)
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl
      left_inv := fun x => by
        obtain ⟨w, rfl⟩ := hf.surj x
        rw [hTf, hT'f, MulAut.inv_apply_self]
      right_inv := fun x => by
        obtain ⟨w, rfl⟩ := hf.surj x
        rw [hT'f, hTf, MulAut.apply_inv_self] }
  let A : (Ix3 → K) ≃ₗ[K] (Ix3 → K) := ((g2LE g).trans TL).trans (g2LE g⁻¹)
  have hAapp : ∀ w, A w = g2Act g⁻¹ (T (g2Act g w)) := fun w => rfl
  have hA : ∀ γ : ↥(cayleyGroup K), ∃ γ' : ↥(cayleyGroup K),
      ∀ w, A (g2Act γ w) = g2Act γ' (A w) := by
    intro γ
    have hk : s * ((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) * s⁻¹ ∈ H :=
      hSH s hs _ (rhoG hc0 hc1 π _).2
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hk⟩
    refine ⟨g⁻¹ * δ * g, fun w => ?_⟩
    obtain ⟨x, hx⟩ := hf.surj (g2Act g w)
    rw [hAapp, hAapp]
    have e1 : g2Act g (g2Act γ w) =
        f (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) := by
      rw [IsCoord.actG hf hc0 hc1, hx, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    have e2 : s (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) =
        ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) (s x) := by
      rw [hδ]
      change _ = (s * _ * s⁻¹) (s x)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e1, ← hx, hTf, hTf, e2, IsCoord.actG hf hc0 hc1, g2Act_mul_apply, g2Act_mul_apply,
      g2Act_apply_inv]
  obtain ⟨c, h₀, hc0', hAeq⟩ := exists_eq_smul_of_normG2 hK hn A hA
  have hTc : ∀ v, T v = c • g2Act (g * h₀ * g⁻¹) v := by
    intro v
    have h1 := hAeq (g2Act g⁻¹ v)
    rw [hAapp, g2Act_apply_inv] at h1
    have h2 := congrArg (g2Act g) h1
    rw [g2Act_apply_inv, G2Q8.g2Act_smul] at h2
    rw [h2, g2Act_mul_apply, g2Act_mul_apply]
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hpow : ∀ j : ℕ, ∀ w, f ((s ^ j) w) = c ^ j • g2Act ((g * h₀ * g⁻¹) ^ j) (f w) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, pow_zero, one_smul, map_one]; rfl
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ← hTf, ih, hσ, hσid, hTc, smul_smul, pow_succ,
        pow_succ']
      simp only [g2Act_mul_apply]
  have hscal : ∀ v, g2Act ((g * h₀ * g⁻¹) ^ 2 ^ m) v = (c ^ 2 ^ m)⁻¹ • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    have h1 := hpow (2 ^ m) w
    rw [hm', MulAut.one_apply] at h1
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc0'), one_smul]
  have hcm : c ^ 2 ^ m = 1 := by
    have h1 := scalar_eq_one hscal
    rwa [inv_eq_one] at h1
  have hc1' : c = 1 := eq_one_of_pow_two_pow hcm
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hseq : s = ((rhoG hc0 hc1 π (g * h₀ * g⁻¹) : ↥H) : MulAut W) := MulEquiv.ext fun w =>
    hinj _ _ (by rw [← hTf, hTc, hc1', one_smul, IsCoord.actG hf hc0 hc1])
  rw [hseq]
  exact (rhoG hc0 hc1 π _).2

end CFSG.Quasithin.Vol2.Ch11.SecE
