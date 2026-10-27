module

public import CFSG.Quasithin.H13.L32NLem1444h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

theorem card_cube_one :
    Fintype.card {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A * A * A = 1} = 3 := by
  decide

variable {G : Type} [Group G] [Finite G]

namespace Setup3

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup3 G T L V V₂ g D Q₁ Q₂)
include S

theorem comm_mem_Q_of_mem_K {x y : G} (hx : x ∈ oTwoUpper (l32nH T V))
    (hy : y ∈ oTwoUpper (l32nH T V)) : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  have hxH : x ∈ l32nH T V := oTwoUpper_le _ hx
  have hyH : y ∈ l32nH T V := oTwoUpper_le _ hy
  have hx' : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot (l32nH T V)) ∈
      imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := ⟨⟨x, hxH⟩, hx, rfl⟩
  have hy' : (QuotientGroup.mk ⟨y, hyH⟩ : OTwoQuot (l32nH T V)) ∈
      imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := ⟨⟨y, hyH⟩, hy, rfl⟩
  have hc := congrArg Subtype.val (S.kElem.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
  simp only [Subgroup.coe_mul] at hc
  have h1 : (QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ * ⟨x, hxH⟩⁻¹ * ⟨y, hyH⟩⁻¹ : ↥(l32nH T V)) :
      OTwoQuot (l32nH T V)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hc]
    group
  rw [QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, by simp⟩

theorem cube_mem_Q_of_mem_K {k : G} (hk : k ∈ oTwoUpper (l32nH T V)) :
    k ^ 3 ∈ pCoreOf 2 (l32nH T V) := by
  have hkH : k ∈ l32nH T V := oTwoUpper_le _ hk
  have hkK : (QuotientGroup.mk ⟨k, hkH⟩ : OTwoQuot (l32nH T V)) ∈
      imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := ⟨⟨k, hkH⟩, hk, rfl⟩
  have h1 := S.kElem.2 _ hkK
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, by simp⟩

theorem rho_cube_of_mem_K {k : G} (hk : k ∈ oTwoUpper (l32nH T V))
    (hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V) :
    D.ρ ⟨k, hkN⟩ (D.ρ ⟨k, hkN⟩ (D.ρ ⟨k, hkN⟩ w)) = w := by
  have h2 := S.rho_eq_one_of_mem_Q (S.cube_mem_Q_of_mem_K hk)
    ((Subgroup.normalizer _).pow_mem hkN 3)
  have h3 : D.ρ ⟨k ^ 3, (Subgroup.normalizer _).pow_mem hkN 3⟩ = D.ρ ⟨k, hkN⟩ ^ 3 := by
    rw [← map_pow]
    rfl
  rw [h3] at h2
  have := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h2
  simpa [pow_succ] using this

theorem exists_k₁ (hK9 : Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) = 9) :
    ∃ k ∈ oTwoUpper (l32nH T V), k ∉ pCoreOf 2 (l32nH T V) ∧
      ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G), ∀ w ∈ D.hat Q₂, D.ρ ⟨k, hkN⟩ w = w := by
  set K := oTwoUpper (l32nH T V) with hKdef
  have hKH : K ≤ l32nH T V := oTwoUpper_le _
  have hKN : K ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hKH.trans (L14332.l32nH_le_normalizer_fsuU T V)
  have hpres : ∀ k : ↥K, ∀ w ∈ D.hat Q₂, D.ρ ⟨k, hKN k.2⟩ w ∈ D.hat Q₂ := fun k w hw =>
    rho_mem_hat (hKN k.2) (fun a ha => (Subgroup.mem_normalizer_iff.mp (S.K_norm k.2).2 a).mp ha)
      hw
  set b := S.basis₂
  let M : ↥K → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun k =>
    LinearMap.toMatrix b b ((D.ρ ⟨k, hKN k.2⟩).toLinearMap.restrict (hpres k))
  have hρmul : ∀ k k' : ↥K, D.ρ ⟨((k * k' : ↥K) : G), hKN (k * k').2⟩ =
      D.ρ ⟨k, hKN k.2⟩ * D.ρ ⟨k', hKN k'.2⟩ := by
    intro k k'
    rw [← map_mul]
    rfl
  have hM1 : M 1 = 1 := by
    have h1 : D.ρ ⟨((1 : ↥K) : G), hKN (1 : ↥K).2⟩ = 1 := by
      rw [show (⟨((1 : ↥K) : G), hKN (1 : ↥K).2⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1
        from rfl, map_one]
    have e : (D.ρ ⟨((1 : ↥K) : G), hKN (1 : ↥K).2⟩).toLinearMap.restrict (hpres 1) = 1 := by
      ext x
      show D.ρ ⟨((1 : ↥K) : G), hKN (1 : ↥K).2⟩ (x : D.V) = (x : D.V)
      rw [h1]
      rfl
    show LinearMap.toMatrix b b _ = 1
    rw [e, LinearMap.toMatrix_one]
  have hMmul : ∀ k k' : ↥K, M (k * k') = M k * M k' := by
    intro k k'
    have e : (D.ρ ⟨((k * k' : ↥K) : G), hKN (k * k').2⟩).toLinearMap.restrict (hpres (k * k')) =
        (D.ρ ⟨k, hKN k.2⟩).toLinearMap.restrict (hpres k) *
          (D.ρ ⟨k', hKN k'.2⟩).toLinearMap.restrict (hpres k') := by
      ext x
      show D.ρ ⟨((k * k' : ↥K) : G), hKN (k * k').2⟩ (x : D.V) =
        D.ρ ⟨k, hKN k.2⟩ (D.ρ ⟨k', hKN k'.2⟩ (x : D.V))
      rw [hρmul]
      rfl
    show LinearMap.toMatrix b b _ = LinearMap.toMatrix b b _ * LinearMap.toMatrix b b _
    rw [e, LinearMap.toMatrix_mul]
  let ψ : ↥K →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    { toFun := M, map_one' := hM1, map_mul' := hMmul }
  have hM3 : ∀ k : ↥K, M k * M k * M k = 1 := by
    intro k
    rw [← hMmul, ← hMmul]
    have e : (D.ρ ⟨((k * k * k : ↥K) : G), hKN (k * k * k).2⟩).toLinearMap.restrict
        (hpres (k * k * k)) = 1 := by
      ext x
      show D.ρ ⟨((k * k * k : ↥K) : G), hKN (k * k * k).2⟩ (x : D.V) = (x : D.V)
      rw [hρmul, hρmul]
      exact S.rho_cube_of_mem_K k.2 (hKN k.2) x
    show LinearMap.toMatrix b b _ = 1
    rw [e, LinearMap.toMatrix_one]
  have hrange : Nat.card ψ.toHomUnits.range ≤ 3 := by
    have hinj : Function.Injective (fun u : ψ.toHomUnits.range =>
        (⟨((u : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod 2)), by
          obtain ⟨k, hk⟩ := u.2
          rw [← hk]
          exact hM3 k⟩ : {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A * A * A = 1})) := by
      intro u v huv
      exact Subtype.ext (Units.ext (congrArg Subtype.val huv))
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A * A * A = 1}),
      card_cube_one] at this
  by_contra hall
  push Not at hall
  have hker : ∀ k ∈ ψ.toHomUnits.ker, ((k : ↥K) : G) ∈ pCoreOf 2 (l32nH T V) := by
    intro k hk
    by_contra hkQ
    obtain ⟨hkN, w, hw, hne⟩ := hall k k.2 hkQ
    apply hne
    have hk1 : M k = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hk)
    have hb := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod 2) =>
      (Matrix.toLin b b N) ⟨w, hw⟩) hk1
    simp only [M, Matrix.toLin_toMatrix, LinearMap.restrict_apply, Matrix.toLin_one] at hb
    exact congrArg Subtype.val hb
  have hcardK := card_eq_card_imageOTwoQuot_mul (l32nH T V) K hKH
  rw [hK9] at hcardK
  have h1 := Subgroup.card_ker_mul_card_range ψ.toHomUnits
  have h2 : Nat.card ψ.toHomUnits.ker ≤ Nat.card ↥(K ⊓ pCoreOf 2 (l32nH T V)) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥K) : G), (k : ↥K).2, hker k k.2⟩) ?_
    intro a b hab
    have h : ((a : ↥K) : G) = ((b : ↥K) : G) :=
      congrArg (fun x : ↥(K ⊓ pCoreOf 2 (l32nH T V)) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h)
  have hpos : 0 < Nat.card ↥(K ⊓ pCoreOf 2 (l32nH T V)) := Nat.card_pos
  have h3 : Nat.card ↥K ≤ Nat.card ↥(K ⊓ pCoreOf 2 (l32nH T V)) * 3 := by
    rw [← h1]
    exact Nat.mul_le_mul h2 hrange
  omega

omit [Finite G] S in
theorem comm_mul_mem_Q {σ a b : G} (ha : a ∈ l32nH T V)
    (h1 : σ * a * σ⁻¹ * a⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (h2 : σ * b * σ⁻¹ * b⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    σ * (a * b) * σ⁻¹ * (a * b)⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  have hQn : l32nH T V ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    le_normalizer_pCoreOf (r := 2) (l32nH T V)
  have h3 : a * (σ * b * σ⁻¹ * b⁻¹) * a⁻¹ ∈ pCoreOf 2 (l32nH T V) :=
    (Subgroup.mem_normalizer_iff.mp (hQn ha) _).mp h2
  have e : σ * (a * b) * σ⁻¹ * (a * b)⁻¹ =
      (σ * a * σ⁻¹ * a⁻¹) * (a * (σ * b * σ⁻¹ * b⁻¹) * a⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h3

omit [Finite G] S in
theorem comm_pow_mem_Q {σ a : G} (ha : a ∈ l32nH T V)
    (h1 : σ * a * σ⁻¹ * a⁻¹ ∈ pCoreOf 2 (l32nH T V)) (m : ℕ) :
    σ * a ^ m * σ⁻¹ * (a ^ m)⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    exact comm_mul_mem_Q ((l32nH T V).pow_mem ha m) ih h1

theorem exists_c0 (hK9 : Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) = 9)
    {σ : G} (hσH : σ ∈ l32nH T V) (hσ2 : σ * σ = 1) (h12 : ∀ q ∈ Q₁, σ * q * σ⁻¹ ∈ Q₂)
    (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) :
    ∃ c ∈ oTwoUpper (l32nH T V), c ^ 3 = 1 ∧
      (∀ (hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V),
        D.ρ ⟨c, hcN⟩ w = w → w = 0) ∧ σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₁, hk₁K, hk₁Q, hk₁triv⟩ := S.exists_k₁ hK9
  set K := oTwoUpper (l32nH T V) with hKdef
  have hKH : K ≤ l32nH T V := oTwoUpper_le _
  have hHN : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  have hk₂K : σ * k₁ * σ⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hσH) k₁).mp hk₁K
  set c' := k₁ * (σ * k₁ * σ⁻¹) with hc'
  have hc'K : c' ∈ K := K.mul_mem hk₁K hk₂K
  have hσN := hHN hσH
  have hk₁N := hHN (hKH hk₁K)
  set ρσ := D.ρ ⟨σ, hσN⟩ with hρσ
  set ρk := D.ρ ⟨k₁, hk₁N⟩ with hρk
  have hρσ2 : ∀ w, ρσ (ρσ w) = w := by
    intro w
    have h1 : ρσ * ρσ = 1 := by
      rw [hρσ, ← map_mul]
      rw [show (⟨σ, hσN⟩ * ⟨σ, hσN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 from
        Subtype.ext hσ2, map_one]
    exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h1
  have hσ₁ : ∀ w ∈ D.hat Q₁, ρσ w ∈ D.hat Q₂ := fun w hw => by
    obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [hρσ, D.ρ_π _ q hqU]
    exact L128A.HatU.π_mem_hat D (h12 q hq) (L128A.HatU.conj_mem hσN hqU)
  have hσ₂ : ∀ w ∈ D.hat Q₂, ρσ w ∈ D.hat Q₁ := fun w hw => by
    obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [hρσ, D.ρ_π _ q hqU]
    exact L128A.HatU.π_mem_hat D (h21 q hq) (L128A.HatU.conj_mem hσN hqU)
  have hk₁₁ : ∀ w ∈ D.hat Q₁, ρk w ∈ D.hat Q₁ := fun w hw =>
    rho_mem_hat hk₁N (fun a ha => (Subgroup.mem_normalizer_iff.mp (S.K_norm hk₁K).1 a).mp ha) hw
  have hfpf₁ : ∀ w ∈ D.hat Q₁, ρk w = w → w = 0 := by
    intro w hw hfix
    by_contra h0
    have htriv := trivial_of_fix S.basis₁ hk₁₁ (fun v _ => S.rho_cube_of_mem_K hk₁K hk₁N v) hw h0
      hfix
    apply hk₁Q
    rw [← S.cHat]
    refine (L14332.rho_eq_one_iff_mem (D := D) (hKH hk₁K) hk₁N).mp (LinearEquiv.ext fun v => ?_)
    have hv : v ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
    have htriv' : ∀ w ∈ D.hat Q₁, D.ρ ⟨k₁, hk₁N⟩ w = w := htriv
    rw [map_add, htriv' v₁ hv₁, hk₁triv hk₁N v₂ hv₂]
    rfl
  have hσk : D.ρ ⟨σ * k₁ * σ⁻¹, hHN (hKH hk₂K)⟩ = ρσ * ρk * ρσ := by
    have e : (⟨σ * k₁ * σ⁻¹, hHN (hKH hk₂K)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨σ, hσN⟩ * ⟨k₁, hk₁N⟩ * ⟨σ, hσN⟩ :=
      Subtype.ext (show σ * k₁ * σ⁻¹ = σ * k₁ * σ by rw [hσinv])
    rw [e, map_mul, map_mul]
  have hc'ρ : D.ρ ⟨c', hHN (hKH hc'K)⟩ = ρk * (ρσ * ρk * ρσ) := by
    rw [← hσk, hρk, ← map_mul]
    rfl
  have hc'₁ : ∀ w ∈ D.hat Q₁, D.ρ ⟨c', hHN (hKH hc'K)⟩ w = ρk w := by
    intro w hw
    rw [hc'ρ]
    show ρk (ρσ (ρk (ρσ w))) = ρk w
    rw [hk₁triv hk₁N _ (hσ₁ w hw), hρσ2]
  have hc'₂ : ∀ w ∈ D.hat Q₂, D.ρ ⟨c', hHN (hKH hc'K)⟩ w = ρσ (ρk (ρσ w)) := by
    intro w hw
    rw [hc'ρ]
    show ρk (ρσ (ρk (ρσ w))) = ρσ (ρk (ρσ w))
    exact hk₁triv hk₁N _ (hσ₁ _ (hk₁₁ _ (hσ₂ w hw)))
  have hc'pres₁ : ∀ w ∈ D.hat Q₁, D.ρ ⟨c', hHN (hKH hc'K)⟩ w ∈ D.hat Q₁ := fun w hw => by
    rw [hc'₁ w hw]
    exact hk₁₁ w hw
  have hc'pres₂ : ∀ w ∈ D.hat Q₂, D.ρ ⟨c', hHN (hKH hc'K)⟩ w ∈ D.hat Q₂ := fun w hw => by
    rw [hc'₂ w hw]
    exact hσ₁ _ (hk₁₁ _ (hσ₂ w hw))
  have hc'fpf : ∀ w, D.ρ ⟨c', hHN (hKH hc'K)⟩ w = w → w = 0 := by
    intro w hw
    have hw' : w ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw'
    set ρc := D.ρ ⟨c', hHN (hKH hc'K)⟩
    have hdiff : ρc w₁ - w₁ ∈ D.hat Q₁ ⊓ D.hat Q₂ := by
      refine ⟨Submodule.sub_mem _ (hc'pres₁ w₁ hw₁) hw₁, ?_⟩
      have e : ρc w₁ - w₁ = w₂ - ρc w₂ := by
        rw [map_add] at hw
        calc ρc w₁ - w₁ = (ρc w₁ + ρc w₂) - w₁ - ρc w₂ := by abel
          _ = (w₁ + w₂) - w₁ - ρc w₂ := by rw [hw]
          _ = w₂ - ρc w₂ := by abel
      rw [e]
      exact Submodule.sub_mem _ hw₂ (hc'pres₂ w₂ hw₂)
    rw [S.hat_Q_inf, Submodule.mem_bot, sub_eq_zero] at hdiff
    have hfix₂ : ρc w₂ = w₂ := by
      rw [map_add, hdiff] at hw
      exact add_left_cancel hw
    have hz₁ : w₁ = 0 := hfpf₁ w₁ hw₁ (by rw [← hc'₁ w₁ hw₁]; exact hdiff)
    have hz₂ : w₂ = 0 := by
      rw [hc'₂ w₂ hw₂] at hfix₂
      have h3 : ρk (ρσ w₂) = ρσ w₂ := by
        have := congrArg ρσ hfix₂
        rwa [hρσ2] at this
      have h4 := hfpf₁ _ (hσ₂ w₂ hw₂) h3
      have := congrArg ρσ h4
      rwa [hρσ2, map_zero] at this
    rw [hz₁, hz₂, add_zero]
  have hcomm' : σ * c' * σ⁻¹ * c'⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
    have e : σ * c' * σ⁻¹ * c'⁻¹ = (σ * k₁ * σ⁻¹) * k₁ * (σ * k₁ * σ⁻¹)⁻¹ * k₁⁻¹ := by
      rw [hc']
      calc σ * (k₁ * (σ * k₁ * σ⁻¹)) * σ⁻¹ * (k₁ * (σ * k₁ * σ⁻¹))⁻¹ =
          σ * k₁ * σ * k₁ * σ⁻¹ * k₁⁻¹ * σ⁻¹ * k₁⁻¹ := by group
        _ = σ * k₁ * σ⁻¹ * k₁ * σ * k₁⁻¹ * σ⁻¹ * k₁⁻¹ := by rw [hσinv]
        _ = (σ * k₁ * σ⁻¹) * k₁ * (σ * k₁ * σ⁻¹)⁻¹ * k₁⁻¹ := by group
    rw [e]
    exact S.comm_mem_Q_of_mem_K hk₂K hk₁K
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (l32nH T V)) ⟨_, S.cube_mem_Q_of_mem_K hc'K⟩
  have hn' : (c' ^ 3) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨c' ^ 2 ^ n, K.pow_mem hc'K _, ?_, ?_, comm_pow_mem_Q (hKH hc'K) hcomm' _⟩
  · rw [← pow_mul, mul_comm, pow_mul, hn']
  · intro hcN w hw
    have hρpow : D.ρ ⟨c' ^ 2 ^ n, hcN⟩ = D.ρ ⟨c', hHN (hKH hc'K)⟩ ^ 2 ^ n := by
      rw [← map_pow]
      rfl
    have hρ3 : D.ρ ⟨c', hHN (hKH hc'K)⟩ ^ 3 = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have := S.rho_cube_of_mem_K hc'K (hHN (hKH hc'K)) v
      simpa [pow_succ] using this
    have hmod : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
      have h0 : 2 ^ n % 3 ≠ 0 := by
        intro h
        have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
        exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)
      omega
    rw [hρpow, ← Nat.div_add_mod (2 ^ n) 3, pow_add, pow_mul, hρ3, one_pow, one_mul] at hw
    rcases hmod with h | h <;> rw [h] at hw
    · exact hc'fpf w (by simpa using hw)
    · apply hc'fpf w
      have h1 : D.ρ ⟨c', hHN (hKH hc'K)⟩ (D.ρ ⟨c', hHN (hKH hc'K)⟩ w) = w := by
        simpa [pow_two] using hw
      have h2 := congrArg (D.ρ ⟨c', hHN (hKH hc'K)⟩) h1
      have h3 : D.ρ ⟨c', hHN (hKH hc'K)⟩ (D.ρ ⟨c', hHN (hKH hc'K)⟩
          (D.ρ ⟨c', hHN (hKH hc'K)⟩ w)) = w := by
        have := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) hρ3
        simpa [pow_succ] using this
      rw [h3] at h2
      exact h2.symm

end Setup3

end L1444

end CFSG.Quasithin.H13
