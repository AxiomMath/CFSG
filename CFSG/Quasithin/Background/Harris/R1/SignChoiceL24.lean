module

public import CFSG.Quasithin.Background.Harris.R1.SignChoiceMod
public import CFSG.Quasithin.Background.Harris.R1.Invol
public import CFSG.Quasithin.Background.Harris.R1.CoxA5
public import CFSG.Quasithin.Background.Harris.R1.SignChoiceFin

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem coe_gprod_five (p a c d f : Ω) :
    ((gprod C.wU [p, a, c, d, f] : ↥(vBeta K1 L2 S Zs)) : G) =
      C.zf p * (C.zf a * (C.zf c * (C.zf d * C.zf f))) := by
  simp [gprod, FamCtx.wU]

theorem exists_lines (e : Fin 5 ≃ Ω)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    ∃ z ∈ Zs, z ≠ 1 ∧ z = C.cm (e 0) (e 1) ∧ ∃ σ : Ω → G, IsSignChoice C z σ ∧
      σ (e 0) = σ (e 1) * σ (e 2) * σ (e 3) * σ (e 4) := by
  have hij : e 0 ≠ e 1 := fun h => by simpa using e.injective h
  refine ⟨C.cm (e 0) (e 1), C.cm_mem _ _, C.cm_ne_one hij, rfl, ?_⟩
  set z := C.cm (e 0) (e 1) with hzdef
  have hz : z ∈ Zs := C.cm_mem _ _
  have hz1 : z ≠ 1 := C.cm_ne_one hij
  have hcard : Fintype.card Ω = 5 := by rw [← Fintype.card_congr e]; simp
  have hodd : Odd (Fintype.card Ω) := by rw [hcard]; decide
  have hl₀ : [e 0, e 1, e 2, e 3, e 4].Nodup := by
    simp [List.nodup_cons, e.injective.eq_iff]
  have hall : ∀ ω, ω ∈ [e 0, e 1, e 2, e 3, e 4] := by
    intro ω
    obtain ⟨i, rfl⟩ := e.surjective ω
    fin_cases i <;> simp
  have hP := FamCtxLemmas.gprod_univ_mem_Zs C hij hodd hcen _ hl₀ hall
  rw [coe_gprod_five] at hP
  set R := C.zf (e 1) * (C.zf (e 2) * (C.zf (e 3) * C.zf (e 4))) with hR
  set P := C.zf (e 0) * R with hPdef
  have hsq : C.zf (e 0) * C.zf (e 0) = 1 := C.Vf_sq (C.zf_mem _)
  refine ⟨fun ω => if ω = e 0 then C.zf (e 0) * P else C.zf ω, ?_, ?_⟩
  · intro ω
    by_cases h : ω = e 0
    · subst h
      simp only [ite_true]
      rcases Zs_cases C hz hz1 hP with h1 | h1
      · left; rw [h1, mul_one]
      · right
        rw [h1]
        exact C.Zs_central (C.zf_mem_U _) hz
    · left; simp [h]
  · have h1 : e 1 ≠ e 0 := fun h => by simpa using e.injective h
    have h2 : e 2 ≠ e 0 := fun h => by simpa using e.injective h
    have h3 : e 3 ≠ e 0 := fun h => by simpa using e.injective h
    have h4 : e 4 ≠ e 0 := fun h => by simpa using e.injective h
    simp only [ite_true, h1, h2, h3, h4, ite_false]
    calc C.zf (e 0) * P = (C.zf (e 0) * C.zf (e 0)) * R := by rw [hPdef, mul_assoc]
      _ = R := by rw [hsq, one_mul]
      _ = _ := by rw [hR]; group


theorem sign_act_eq_one (k : ↥K1) : Equiv.Perm.sign (C.D.act k) = 1 := by
  have : Group.IsPerfect ↥K1 := A36A.isPerfect_of_mem_cComp C.h.cComp_mem
  have hker := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp C.D.act)
  rw [Group.IsPerfect.commutator_eq_top] at hker
  exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k))

variable {z : G} {σ : Ω → G}

theorem exists_signStab_lift (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) (τ : Equiv.Perm Ω) (hτ : Equiv.Perm.sign τ = 1) :
    ∃ k, ∃ hk : k ∈ signStab C σ, C.D.act ⟨k, signStab_le C σ hk⟩ = τ := by
  have hn : 1 < Fintype.card Ω := by omega
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  obtain ⟨k₀, hk₀⟩ := exists_act_eq C hΩ hL24 τ hτ
  obtain ⟨q, hqW, k', hk', hkq⟩ := exists_mul_signStab C hz hz1 hσ hn hWK k₀.2
  refine ⟨k', hk', ?_⟩
  have hqK : q ∈ K1 := hWK hqW
  have : (⟨k', signStab_le C σ hk'⟩ : ↥K1) = ⟨q, hqK⟩⁻¹ * k₀ := by
    apply Subtype.ext
    show k' = q⁻¹ * (k₀ : G)
    rw [hkq]; group
  rw [this, map_mul, map_inv, act_eq_one_of_mem_vBeta C hqW hqK, inv_one, one_mul, hk₀]


theorem exists_involution_lift (e : Fin 5 ≃ Ω) (hΩ : Fintype.card Ω = 5)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ a, ∃ ha : a ∈ signStab C σ, a * a = 1 ∧
      ∀ i, C.D.act ⟨a, signStab_le C σ ha⟩ (e i) = e (CFSG.Quasithin.J2Cz.pa i) := by
  have hn : 1 < Fintype.card Ω := by omega
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  obtain ⟨t₀, ht₀K, ht₀sq, ht₀W⟩ := exists_involution_outside_pCore C hΩ hL24 hcen hQ hQK
  set τ₀ : Equiv.Perm Ω := C.D.act ⟨t₀, ht₀K⟩ with hτ₀
  have hτ₀sq : τ₀ * τ₀ = 1 := by
    have : C.D.act (⟨t₀, ht₀K⟩ * ⟨t₀, ht₀K⟩) = 1 := by
      have h1 : (⟨t₀, ht₀K⟩ * ⟨t₀, ht₀K⟩ : ↥K1) = 1 := Subtype.ext ht₀sq
      rw [h1, map_one]
    rwa [map_mul] at this
  have hτ₀1 : τ₀ ≠ 1 := fun h => ht₀W (by
    rw [hQK]; exact act_eq_one_mem_vBeta C hΩ hL24 hQK h)
  set δ : Equiv.Perm (Fin 5) := e.symm.permCongr τ₀ with hδ
  have hδsq : δ * δ = 1 := by
    rw [hδ, ← Equiv.permCongr_mul, hτ₀sq]; ext; simp [Equiv.permCongr_apply]
  have hδ1 : δ ≠ 1 := fun h => hτ₀1 (by
    have : e.symm.permCongr τ₀ = e.symm.permCongr 1 := by rw [← hδ, h]; ext; simp [Equiv.permCongr_apply]
    exact (e.symm.permCongr).injective this)
  have hδs : Equiv.Perm.sign δ = 1 := by
    rw [hδ, Equiv.Perm.sign_permCongr]; exact sign_act_eq_one C _
  obtain ⟨c, hcs, hc⟩ := exists_conj_pa δ hδsq hδ1 hδs
  obtain ⟨kc, hkc⟩ := exists_act_eq C hΩ hL24 (e.permCongr c) (by rw [Equiv.Perm.sign_permCongr, hcs])
  set t₁ : G := (kc : G) * t₀ * (kc : G)⁻¹ with ht₁
  have ht₁K : t₁ ∈ K1 := K1.mul_mem (K1.mul_mem kc.2 ht₀K) (K1.inv_mem kc.2)
  have ht₁sq : t₁ * t₁ = 1 := by
    have : t₁ * t₁ = (kc : G) * (t₀ * t₀) * (kc : G)⁻¹ := by rw [ht₁]; group
    rw [this, ht₀sq]; group
  have hact₁ : C.D.act ⟨t₁, ht₁K⟩ = e.permCongr CFSG.Quasithin.J2Cz.pa := by
    have hmul : (⟨t₁, ht₁K⟩ : ↥K1) = kc * ⟨t₀, ht₀K⟩ * kc⁻¹ := rfl
    rw [hmul, map_mul, map_mul, map_inv, hkc, ← hτ₀]
    have : τ₀ = e.permCongr δ := by ext; simp [hδ, Equiv.permCongr_apply]
    have hinvc : (e.permCongr c)⁻¹ = e.permCongr c⁻¹ := Equiv.Perm.ext (fun _ => rfl)
    rw [this, hinvc, ← Equiv.permCongr_mul, ← Equiv.permCongr_mul, hc]
  obtain ⟨q, hqW, k, hk, htq⟩ := exists_mul_signStab C hz hz1 hσ hn hWK ht₁K
  have hqK : q ∈ K1 := hWK hqW
  have hkK : k ∈ K1 := signStab_le C σ hk
  have hπk : ∀ i, C.D.act ⟨k, hkK⟩ (e i) = e (CFSG.Quasithin.J2Cz.pa i) := by
    have : (⟨k, hkK⟩ : ↥K1) = ⟨q, hqK⟩⁻¹ * ⟨t₁, ht₁K⟩ := by
      apply Subtype.ext
      show k = q⁻¹ * t₁
      rw [htq]; group
    intro i
    rw [this, map_mul, map_inv, act_eq_one_of_mem_vBeta C hqW hqK, inv_one, one_mul, hact₁]
    simp [Equiv.permCongr_apply]
  exact ⟨k, hk, sq_eq_one_of_lift C e hΩ hL24 hz hz1 hσ hcen hQK hk ht₁sq hqW htq hπk, hπk⟩


omit [Fintype Ω] [DecidableEq Ω] in
theorem IsSignChoice.sq_eq_one (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) (ω : Ω) :
    σ ω * σ ω = 1 := by
  obtain ⟨ζ, hζ, h⟩ := hσ.exists_eq C hz ω
  have hc : C.zf ω * ζ = ζ * C.zf ω := C.Zs_central (C.zf_mem_U ω) hζ
  rw [h]
  calc ζ * C.zf ω * (ζ * C.zf ω) = ζ * (C.zf ω * ζ) * C.zf ω := by group
    _ = ζ * (ζ * C.zf ω) * C.zf ω := by rw [hc]
    _ = (ζ * ζ) * (C.zf ω * C.zf ω) := by group
    _ = 1 := by rw [C.Zs_sq hζ, C.Vf_sq (C.zf_mem ω), one_mul]

omit [Fintype Ω] [DecidableEq Ω] in
theorem IsSignChoice.pair_sq (hz : z ∈ Zs) {i₀ j₀ : Ω} (hij₀ : i₀ ≠ j₀)
    (hzcm : z = C.cm i₀ j₀) (hσ : IsSignChoice C z σ) {ω ω' : Ω} (h : ω ≠ ω') :
    σ ω * σ ω' * (σ ω * σ ω') = z := by
  obtain ⟨ζ, hζ, h1⟩ := hσ.exists_eq C hz ω
  obtain ⟨ζ', hζ', h2⟩ := hσ.exists_eq C hz ω'
  have hc1 : C.zf ω * ζ = ζ * C.zf ω := C.Zs_central (C.zf_mem_U ω) hζ
  have hc2 : C.zf ω' * ζ' = ζ' * C.zf ω' := C.Zs_central (C.zf_mem_U ω') hζ'
  have hs1 : σ ω = C.zf ω * ζ := by rw [h1, hc1]
  have hs2 : σ ω' = C.zf ω' * ζ' := by rw [h2, hc2]
  have hi1 := hσ.sq_eq_one C hz ω
  have hi2 := hσ.sq_eq_one C hz ω'
  have hinv1 : (σ ω)⁻¹ = σ ω := inv_eq_of_mul_eq_one_right hi1
  have hinv2 : (σ ω')⁻¹ = σ ω' := inv_eq_of_mul_eq_one_right hi2
  have e1 : σ ω * σ ω' * (σ ω * σ ω') = σ ω * σ ω' * (σ ω)⁻¹ * (σ ω')⁻¹ := by
    rw [hinv1, hinv2]; group
  rw [e1, hs1, hs2]
  have hζ1 : ζ * C.zf ω' = C.zf ω' * ζ := C.Zs_central (C.zf_mem_U ω') hζ |>.symm
  have hcomm := F112J2.commutator_mul_central (a := C.zf ω) (b := C.zf ω') (ε := ζ) (δ := ζ')
    (C.Zs_central (C.zf_mem_U ω') hζ |>.symm)
    (C.Zs_central (F112J2.Zs_le_vBeta K1 L2 S Zs hζ') hζ |>.symm)
    (C.Zs_central (C.zf_mem_U ω) hζ' |>.symm)
  rw [hcomm]
  have hcm : C.cm ω ω' = C.cm i₀ j₀ := C.cm_const hij₀ h
  rw [hzcm]
  exact hcm


@[expose] def permOmega (e : Fin 5 ≃ Ω) : Equiv.Perm (Fin 5) →* Equiv.Perm Ω :=
  MonoidHom.mk' e.permCongr (fun p q => Equiv.permCongr_mul e p q)

theorem permOmega_apply (e : Fin 5 ≃ Ω) (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permOmega e p (e i) = e (p i) := by
  simp [permOmega, Equiv.permCongr_apply]

theorem act_eq_permOmega (e : Fin 5 ≃ Ω) {k : ↥K1} {p : Equiv.Perm (Fin 5)}
    (h : ∀ i, C.D.act k (e i) = e (p i)) : C.D.act k = permOmega e p :=
  Equiv.ext fun ω => by
    obtain ⟨i, rfl⟩ := e.surjective ω
    rw [h i, permOmega_apply]

theorem mem_Zs_of_act_eq_one (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) {x : G} (hx : x ∈ signStab C σ)
    (h : C.D.act ⟨x, signStab_le C σ hx⟩ = 1) : x ∈ Zs := by
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  have hW := act_eq_one_mem_vBeta C hΩ hL24 hQK h
  exact (signStab_inf_vBeta C hz hz1 hσ hcen hWK).le ⟨hW, hx⟩

theorem Zs_le_signStab (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) : Zs ≤ signStab C σ := fun x hx => by
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  have := (signStab_inf_vBeta C hz hz1 hσ hcen hWK).ge hx
  exact this.2


include C in
theorem Zs_comm_K1 {x k : G} (hx : x ∈ Zs) (hk : k ∈ K1) : x * k = k * x :=
  Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) x hx

theorem exists_b (e : Fin 5 ≃ Ω) (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ b, ∃ hb : b ∈ signStab C σ, b * b * b = 1 ∧
      C.D.act ⟨b, signStab_le C σ hb⟩ = permOmega e CFSG.Quasithin.J2Cz.pb := by
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  obtain ⟨b₁, hb₁, hact⟩ := exists_signStab_lift C hΩ hL24 hz hz1 hσ hQK
    (permOmega e CFSG.Quasithin.J2Cz.pb) (by
      show Equiv.Perm.sign (e.permCongr CFSG.Quasithin.J2Cz.pb) = 1
      rw [Equiv.Perm.sign_permCongr]; exact sign_pb)
  have hb₁K : b₁ ∈ K1 := signStab_le C σ hb₁
  have hb3 : b₁ * b₁ * b₁ ∈ signStab C σ := (signStab C σ).mul_mem ((signStab C σ).mul_mem hb₁ hb₁) hb₁
  have hact3 : C.D.act ⟨b₁ * b₁ * b₁, signStab_le C σ hb3⟩ = 1 := by
    have : (⟨b₁ * b₁ * b₁, signStab_le C σ hb3⟩ : ↥K1) =
        ⟨b₁, hb₁K⟩ * ⟨b₁, hb₁K⟩ * ⟨b₁, hb₁K⟩ := rfl
    rw [this, map_mul, map_mul, hact, ← map_mul, ← map_mul, pb_cube, map_one]
  have hZ := mem_Zs_of_act_eq_one C hΩ hL24 hz hz1 hσ hcen hQK hb3 hact3
  rcases Zs_cases C hz hz1 hZ with h1 | h1
  · exact ⟨b₁, hb₁, h1, hact⟩
  · have hzs : z ∈ signStab C σ := Zs_le_signStab C hz hz1 hσ hcen hQK hz
    have hzK : z ∈ K1 := signStab_le C σ hzs
    have hzb : z * b₁ = b₁ * z := Zs_comm_K1 C hz hb₁K
    have hbz : b₁ * z ∈ signStab C σ := (signStab C σ).mul_mem hb₁ hzs
    refine ⟨b₁ * z, hbz, ?_, ?_⟩
    · have hzz : z * z = 1 := C.Zs_sq hz
      calc b₁ * z * (b₁ * z) * (b₁ * z) = b₁ * (z * b₁) * (z * b₁) * z := by group
        _ = b₁ * (b₁ * z) * (b₁ * z) * z := by rw [hzb]
        _ = b₁ * b₁ * (z * b₁) * z * z := by group
        _ = b₁ * b₁ * (b₁ * z) * z * z := by rw [hzb]
        _ = (b₁ * b₁ * b₁) * (z * z) * z := by group
        _ = 1 := by rw [h1, hzz, mul_one, hzz]
    · have : (⟨b₁ * z, signStab_le C σ hbz⟩ : ↥K1) = ⟨b₁, hb₁K⟩ * ⟨z, hzK⟩ := rfl
      rw [this, map_mul, hact, act_eq_one_of_mem_vBeta C (F112J2.Zs_le_vBeta K1 L2 S Zs hz) hzK,
        mul_one]

theorem exists_a_b (e : Fin 5 ≃ Ω) (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ a b, ∃ (ha : a ∈ signStab C σ) (hb : b ∈ signStab C σ), a * a = 1 ∧ b * b * b = 1 ∧
      (a * b) ^ 5 = 1 ∧ C.D.act ⟨a, signStab_le C σ ha⟩ = permOmega e CFSG.Quasithin.J2Cz.pa ∧
      C.D.act ⟨b, signStab_le C σ hb⟩ = permOmega e CFSG.Quasithin.J2Cz.pb := by
  obtain ⟨a₁, ha₁, ha₁sq, hπa⟩ := exists_involution_lift C e hΩ hL24 hz hz1 hσ hcen hQ hQK
  obtain ⟨b, hb, hb3, hactb⟩ := exists_b C e hΩ hL24 hz hz1 hσ hcen hQK
  have ha₁K : a₁ ∈ K1 := signStab_le C σ ha₁
  have hbK : b ∈ K1 := signStab_le C σ hb
  have hacta : C.D.act ⟨a₁, ha₁K⟩ = permOmega e CFSG.Quasithin.J2Cz.pa := act_eq_permOmega C e hπa
  have hab : (a₁ * b) ^ 5 ∈ signStab C σ := (signStab C σ).pow_mem ((signStab C σ).mul_mem ha₁ hb) 5
  have hactab : C.D.act ⟨(a₁ * b) ^ 5, signStab_le C σ hab⟩ = 1 := by
    have : (⟨(a₁ * b) ^ 5, signStab_le C σ hab⟩ : ↥K1) = (⟨a₁, ha₁K⟩ * ⟨b, hbK⟩) ^ 5 := rfl
    rw [this, map_pow, map_mul, hacta, hactb, ← map_mul, ← map_pow, pab_five, map_one]
  have hZ := mem_Zs_of_act_eq_one C hΩ hL24 hz hz1 hσ hcen hQK hab hactab
  rcases Zs_cases C hz hz1 hZ with h1 | h1
  · exact ⟨a₁, b, ha₁, hb, ha₁sq, hb3, h1, hacta, hactb⟩
  · have hzs : z ∈ signStab C σ := Zs_le_signStab C hz hz1 hσ hcen hQK hz
    have hzK : z ∈ K1 := signStab_le C σ hzs
    have hza : z * a₁ = a₁ * z := Zs_comm_K1 C hz ha₁K
    have hzb : z * b = b * z := Zs_comm_K1 C hz hbK
    have hzz : z * z = 1 := C.Zs_sq hz
    have haz : a₁ * z ∈ signStab C σ := (signStab C σ).mul_mem ha₁ hzs
    refine ⟨a₁ * z, b, haz, hb, ?_, hb3, ?_, ?_, hactb⟩
    · calc a₁ * z * (a₁ * z) = a₁ * (z * a₁) * z := by group
        _ = a₁ * (a₁ * z) * z := by rw [hza]
        _ = (a₁ * a₁) * (z * z) := by group
        _ = 1 := by rw [ha₁sq, hzz, one_mul]
    · have hcomm : Commute (a₁ * b) z := by
        show a₁ * b * z = z * (a₁ * b)
        calc a₁ * b * z = a₁ * (b * z) := by group
          _ = a₁ * (z * b) := by rw [hzb]
          _ = (a₁ * z) * b := by group
          _ = (z * a₁) * b := by rw [hza]
          _ = z * (a₁ * b) := by group
      have e1 : a₁ * z * b = (a₁ * b) * z := by
        calc a₁ * z * b = a₁ * (z * b) := by group
          _ = a₁ * (b * z) := by rw [hzb]
          _ = _ := by group
      rw [e1, hcomm.mul_pow, h1]
      have hz4 : z ^ 5 = z := by
        calc z ^ 5 = z * z * z * z * z := by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
          _ = (z * z) * (z * z) * z := by simp only [mul_assoc]
          _ = z := by rw [hzz, one_mul, one_mul]
      rw [hz4, hzz]
    · have : (⟨a₁ * z, signStab_le C σ haz⟩ : ↥K1) = ⟨a₁, ha₁K⟩ * ⟨z, hzK⟩ := rfl
      rw [this, map_mul, hacta,
        act_eq_one_of_mem_vBeta C (F112J2.Zs_le_vBeta K1 L2 S Zs hz) hzK, mul_one]


theorem exists_word_lift (e : Fin 5 ≃ Ω) {a b : G} (haK : a ∈ K1) (hbK : b ∈ K1)
    (hacta : C.D.act ⟨a, haK⟩ = permOmega e CFSG.Quasithin.J2Cz.pa)
    (hactb : C.D.act ⟨b, hbK⟩ = permOmega e CFSG.Quasithin.J2Cz.pb) (w : List Bool) :
    ∃ h : ↥K1, (h : G) ∈ Subgroup.closure ({a, b} : Set G) ∧ C.D.act h = permOmega e (evalW w) := by
  induction w with
  | nil => exact ⟨1, Subgroup.one_mem _, by simp [evalW]⟩
  | cons c w ih =>
    obtain ⟨h, hh, hact⟩ := ih
    have hev : evalW (c :: w) = (if c then CFSG.Quasithin.J2Cz.pa else CFSG.Quasithin.J2Cz.pb) *
        evalW w := by
      simp [evalW]
    cases c
    · refine ⟨⟨b, hbK⟩ * h, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hh
      · rw [map_mul, hactb, hact, hev]; simp [map_mul]
    · refine ⟨⟨a, haK⟩ * h, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hh
      · rw [map_mul, hacta, hact, hev]; simp [map_mul]

theorem eval_lift (e : Fin 5 ≃ Ω) {a b : G} (haK : a ∈ K1) (hbK : b ∈ K1)
    (hacta : C.D.act ⟨a, haK⟩ = permOmega e CFSG.Quasithin.J2Cz.pa)
    (hactb : C.D.act ⟨b, hbK⟩ = permOmega e CFSG.Quasithin.J2Cz.pb) (w : List Bool) :
    ∃ h : ↥K1, (h : G) = CoxA5.eval a b w ∧ C.D.act h = permOmega e (evalW w) := by
  induction w with
  | nil => exact ⟨1, rfl, by simp [evalW]⟩
  | cons c w ih =>
    obtain ⟨h, hh, hact⟩ := ih
    have hev : evalW (c :: w) = (if c then CFSG.Quasithin.J2Cz.pa else CFSG.Quasithin.J2Cz.pb) *
        evalW w := by
      simp [evalW]
    have hev' : CoxA5.eval a b (c :: w) = (if c then a else b) * CoxA5.eval a b w := by
      simp [CoxA5.eval]
    cases c
    · refine ⟨⟨b, hbK⟩ * h, ?_, ?_⟩
      · rw [hev']; simp [hh]
      · rw [map_mul, hactb, hact, hev]; simp [map_mul]
    · refine ⟨⟨a, haK⟩ * h, ?_, ?_⟩
      · rw [hev']; simp [hh]
      · rw [map_mul, hacta, hact, hev]; simp [map_mul]

theorem evalW_eq_one {w : List Bool} (hw : w ∈ CoxA5.covNf) (h : evalW w = 1) : w = [] := by
  revert w
  decide +kernel

include C in
theorem exists_normalized_gens (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ (z : G) (x : Fin 5 → G) (a b : G),
      z ∈ Zs ∧ z ≠ 1 ∧ (∀ i, x i ∈ vBeta K1 L2 S Zs) ∧ a ∈ K1 ∧ b ∈ K1 ∧
      z * z = 1 ∧ (∀ i, z * x i = x i * z) ∧ (∀ i, x i * x i = 1) ∧
      (∀ i j, i ≠ j → x i * x j * (x i * x j) = z) ∧ x 0 = x 1 * x 2 * x 3 * x 4 ∧
      a * a = 1 ∧ b * b * b = 1 ∧ (a * b) ^ 5 = 1 ∧ z * a = a * z ∧ z * b = b * z ∧
      (∀ i, a * x i * a⁻¹ = x (CFSG.Quasithin.J2Cz.pa i)) ∧
      (∀ i, b * x i * b⁻¹ = x (CFSG.Quasithin.J2Cz.pb i)) ∧
      Subgroup.closure ({z, x 1, x 2, x 3, x 4} : Set G) = pCoreOf 2 K1 ∧
      Subgroup.closure ({z, x 1, x 2, x 3, x 4, a, b} : Set G) = K1 ∧
      Subgroup.closure ({a, b} : Set G) ⊓ pCoreOf 2 K1 = ⊥ := by
  have hn : 1 < Fintype.card Ω := by omega
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  let e : Fin 5 ≃ Ω := (Fintype.equivFinOfCardEq hΩ).symm
  obtain ⟨z, hz, hz1, hzcm, σ, hσ, hσ0⟩ := exists_lines C e hcen
  obtain ⟨a, b, ha, hb, ha2, hb3, hab5, hacta, hactb⟩ :=
    exists_a_b C e hΩ hL24 hz hz1 hσ hcen hQ hQK
  have haK : a ∈ K1 := signStab_le C σ ha
  have hbK : b ∈ K1 := signStab_le C σ hb
  have hzK : z ∈ K1 := hWK (F112J2.Zs_le_vBeta K1 L2 S Zs hz)
  have hij₀ : e 0 ≠ e 1 := fun h => by simpa using e.injective h
  set x : Fin 5 → G := fun i => σ (e i) with hx
  have hxW : ∀ i, x i ∈ vBeta K1 L2 S Zs := fun i => hσ.mem_vBeta C hz (e i)
  have hzz : z * z = 1 := C.Zs_sq hz
  have hne : ∀ i j : Fin 5, i ≠ j → e i ≠ e j := fun i j h h' => h (e.injective h')
  have hconj : ∀ (k : G) (hk : k ∈ signStab C σ) (p : Equiv.Perm (Fin 5)),
      C.D.act ⟨k, signStab_le C σ hk⟩ = permOmega e p → ∀ i, k * x i * k⁻¹ = x (p i) := by
    intro k hk p hp i
    obtain ⟨hk', h⟩ := hk
    have := h (e i)
    rw [hp, permOmega_apply] at this
    exact this
  have hG5 : ∀ y ∈ ({z, x 1, x 2, x 3, x 4} : Set G), y ∈ vBeta K1 L2 S Zs := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact F112J2.Zs_le_vBeta K1 L2 S Zs hz
    all_goals exact hxW _
  have hcl1 : Subgroup.closure ({z, x 1, x 2, x 3, x 4} : Set G) = pCoreOf 2 K1 := by
    rw [hQK]
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr hG5
    · rw [C.U_eq_closure hz hz1, Subgroup.closure_le]
      rintro y (rfl | ⟨ω, rfl⟩)
      · exact Subgroup.subset_closure (by simp)
      · obtain ⟨ζ, hζ, hσω⟩ := hσ.exists_eq C hz ω
        have hσmem : σ ω ∈ Subgroup.closure ({z, x 1, x 2, x 3, x 4} : Set G) := by
          obtain ⟨i, rfl⟩ := e.surjective ω
          fin_cases i
          · show σ (e 0) ∈ _
            rw [hσ0]
            refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_ <;>
              exact Subgroup.subset_closure (by simp [hx])
          all_goals exact Subgroup.subset_closure (by simp [hx])
        have hζmem : ζ ∈ Subgroup.closure ({z, x 1, x 2, x 3, x 4} : Set G) := by
          rcases Zs_cases C hz hz1 hζ with rfl | rfl
          · exact Subgroup.one_mem _
          · exact Subgroup.subset_closure (by simp)
        have : C.zf ω = ζ⁻¹ * σ ω := by rw [hσω]; group
        rw [SetLike.mem_coe, this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hζmem) hσmem
  refine ⟨z, x, a, b, hz, hz1, hxW, haK, hbK, hzz,
    fun i => (C.Zs_central (hxW i) hz).symm,
    fun i => hσ.sq_eq_one C hz (e i),
    fun i j h => hσ.pair_sq C hz hij₀ hzcm (hne i j h), hσ0, ha2, hb3, hab5,
    Zs_comm_K1 C hz haK, Zs_comm_K1 C hz hbK,
    hconj a ha _ hacta, hconj b hb _ hactb, hcl1, ?_, ?_⟩
  swap
  ·
    rw [eq_bot_iff]
    intro y ⟨hy1, hy2⟩
    have hle : Subgroup.closure ({a, b} : Set G) ≤ signStab C σ := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    rw [hQK] at hy2
    have hyZ : y ∈ Zs := (signStab_inf_vBeta C hz hz1 hσ hcen hWK).le ⟨hy2, hle hy1⟩
    rw [Subgroup.mem_bot]
    rcases Zs_cases C hz hz1 hyZ with h | h
    · exact h
    · exfalso
      subst h
      obtain ⟨w, hw, hwy⟩ := CoxA5.closure_words a b ha2 hb3 hab5 y hy1
      obtain ⟨h', hh', hact⟩ := eval_lift C e haK hbK hacta hactb w
      have hyK : y ∈ K1 := hWK (F112J2.Zs_le_vBeta K1 L2 S Zs hz)
      have h1 : C.D.act h' = 1 := by
        have : h' = ⟨y, hyK⟩ := Subtype.ext (by rw [hh', hwy])
        rw [this]; exact act_eq_one_of_mem_vBeta C (F112J2.Zs_le_vBeta K1 L2 S Zs hz) hyK
      have h2 : permOmega e (evalW w) = 1 := by rw [← hact, h1]
      have h3 : evalW w = 1 := by
        apply (e.permCongr).injective
        show permOmega e (evalW w) = permOmega e 1
        rw [h2, map_one]
      have hw0 := evalW_eq_one hw h3
      subst hw0
      exact hz1 (by rw [← hwy]; simp [CoxA5.eval])
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hzK
    · exact hWK (hxW _)
    · exact hWK (hxW _)
    · exact hWK (hxW _)
    · exact hWK (hxW _)
    · exact haK
    · exact hbK
  · intro k hk
    set Γ := Subgroup.closure ({z, x 1, x 2, x 3, x 4, a, b} : Set G) with hΓ
    have hWΓ : vBeta K1 L2 S Zs ≤ Γ := by
      rw [← hQK, ← hcl1]
      exact Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto)
    have hABΓ : Subgroup.closure ({a, b} : Set G) ≤ Γ :=
      Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto)
    set φ : Equiv.Perm (Fin 5) := e.symm.permCongr (C.D.act ⟨k, hk⟩) with hφ
    have hφs : Equiv.Perm.sign φ = 1 := by
      rw [hφ, Equiv.Perm.sign_permCongr]; exact sign_act_eq_one C _
    obtain ⟨w, -, hw⟩ := exists_word φ hφs
    obtain ⟨h, hhΓ, hact⟩ := exists_word_lift C e haK hbK hacta hactb w
    have hact' : C.D.act h = C.D.act ⟨k, hk⟩ := by
      rw [hact, hw, hφ]
      ext ω
      simp [permOmega, Equiv.permCongr_apply]
    have hker : C.D.act (h⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hact', inv_mul_cancel]
    have hW := act_eq_one_mem_vBeta C hΩ hL24 hQK hker
    have : k = (h : G) * ((h⁻¹ * ⟨k, hk⟩ : ↥K1) : G) := by
      show k = (h : G) * ((h : G)⁻¹ * k)
      group
    rw [this]
    exact Γ.mul_mem (hABΓ hhΓ) (hWΓ hW)

end CFSG.Quasithin.Background.Harris.R1
