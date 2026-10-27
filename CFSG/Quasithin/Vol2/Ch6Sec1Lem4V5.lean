module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FiveOverNorm614 (W : Type) [Group W] : Prop :=
  ∀ S P : Subgroup W, IsSylowTwoOf S ⊤ → S ≤ P → Nat.card P = 5 * Nat.card S →
    P ≤ Subgroup.normalizer (S : Set W)

theorem fiveOverNorm614_of_noFiveOver {W : Type} [Group W] (h : FiveNorm.NoFiveOver W) :
    FiveOverNorm614 W :=
  fun S P hS hSP hcard => absurd hcard (h S P hS hSP)

@[expose] def TitsCenterFact614 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → Odd (Nat.card (Subgroup.center X)) →
    CFSG.Blueprint.ReeTitsModel (X ⧸ Subgroup.center X) .Tits 2 1 → Subgroup.center X = ⊥

variable {Γ : Type} [Group Γ]

theorem conj_mem_of_rho614 [Finite Γ] {K T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hTs : IsSylowTwoOf (T ⊓ K) K) (hZL : Subgroup.center (ModO2 K ⧸ Subgroup.center (ModO2 K)) = ⊥)
    {x : Γ} (hxN : x ∈ Subgroup.normalizer (K : Set Γ))
    (hx : rho614 K ⟨x, hxN⟩ ∈ Subgroup.normalizer
      ((((T ⊓ K).subgroupOf (Subgroup.normalizer (K : Set Γ))).map (rho614 K) :
        Subgroup (MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K)))) : Set _))
    {t : Γ} (ht : t ∈ T ⊓ K) : x * t * x⁻¹ ∈ T ⊓ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := rho614 K with hρ
  set D' := ((T ⊓ K).subgroupOf (Subgroup.normalizer (K : Set Γ))).map ρ with hD'
  have hkK : x * t * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN t).mp ht.2
  set k := x * t * x⁻¹ with hk
  have htN : t ∈ Subgroup.normalizer (K : Set Γ) := Subgroup.le_normalizer ht.2
  have hρt : ρ ⟨t, htN⟩ ∈ D' := ⟨⟨t, htN⟩, ht, rfl⟩
  have hρk : ρ ⟨k, Subgroup.le_normalizer hkK⟩ ∈ D' := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hx _).mp hρt
    have e : ρ ⟨k, Subgroup.le_normalizer hkK⟩ = ρ ⟨x, hxN⟩ * ρ ⟨t, htN⟩ * (ρ ⟨x, hxN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact h1
  obtain ⟨⟨t', ht'N⟩, ht', he⟩ := hρk
  have ht'TK : t' ∈ T ⊓ K := ht'
  set kb : ModO2 K := ((⟨k, hkK⟩ : ↥K) : ModO2 K) with hkb
  set tb : ModO2 K := ((⟨t', ht'TK.2⟩ : ↥K) : ModO2 K) with htb
  have hz : kb * tb⁻¹ ∈ Subgroup.center (ModO2 K) := by
    have h1 : (((kb * tb⁻¹ : ModO2 K)) : ModO2 K ⧸ Subgroup.center (ModO2 K)) = 1 := by
      have e1 : ρ ⟨k, Subgroup.le_normalizer hkK⟩ = ρ ⟨t', Subgroup.le_normalizer ht'TK.2⟩ := by
        rw [← he]
      rw [hρ, rho614_of_mem K hkK, rho614_of_mem K ht'TK.2] at e1
      have hinj : Function.Injective
          (MulAut.conj : ModO2 K ⧸ Subgroup.center (ModO2 K) →* MulAut _) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro y hy
        have hyc : y ∈ Subgroup.center (ModO2 K ⧸ Subgroup.center (ModO2 K)) := by
          rw [Subgroup.mem_center_iff]
          intro z
          have := congrArg (fun φ : MulAut _ => φ z) (MonoidHom.mem_ker.mp hy)
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this.symm
        rw [hZL] at hyc
        exact hyc
      have e2 := hinj e1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, e2, mul_inv_cancel]
    rwa [QuotientGroup.eq_one_iff] at h1
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht.1⟩
  have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := hT2 ⟨t', ht'TK.1⟩
  have htb' : t' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hka : k ^ 2 ^ a = 1 := by
    rw [hk, conj_pow, hta]
    group
  have hkb2 : kb ^ 2 ^ (a + b) = 1 := by
    rw [hkb, ← QuotientGroup.mk_pow]
    have : (⟨k, hkK⟩ : ↥K) ^ 2 ^ (a + b) = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_add, pow_mul, hka, one_pow]
    rw [this, QuotientGroup.mk_one]
  have htb2 : tb ^ 2 ^ (a + b) = 1 := by
    rw [htb, ← QuotientGroup.mk_pow]
    have : (⟨t', ht'TK.2⟩ : ↥K) ^ 2 ^ (a + b) = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_add, mul_comm, pow_mul, htb', one_pow]
    rw [this, QuotientGroup.mk_one]
  set z := kb * tb⁻¹ with hzdef
  have hzc : Commute z tb := (Subgroup.mem_center_iff.mp hz tb).symm
  have hz2 : z ^ 2 ^ (a + b) = 1 := by
    have e : kb = z * tb := by rw [hzdef]; group
    have h1 := hkb2
    rw [e, hzc.mul_pow, htb2, mul_one] at h1
    exact h1
  have hzodd : z ^ Nat.card (Subgroup.center (ModO2 K)) = 1 := by
    have h := congrArg Subtype.val
      (pow_card_eq_one' (x := (⟨z, hz⟩ : ↥(Subgroup.center (ModO2 K)))))
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  have hz1 := eq_one_of_pow_two_of_odd614 hz2 hzodd (odd_card_center_modO2_614 K)
  have hkt : kb = tb := by
    have : kb * tb⁻¹ = 1 := hz1
    exact mul_inv_eq_one.mp this
  rw [hkb, htb, QuotientGroup.eq] at hkt
  have h2 := mem_pCoreOf_of_mem_pCore614 hkt
  have hO : pCoreOf 2 K ≤ T ⊓ K := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs
  have h3 := hO h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  have e : k = t' * (k⁻¹ * t')⁻¹ := by group
  rw [e]
  exact (T ⊓ K).mul_mem ht'TK ((T ⊓ K).inv_mem h3)

theorem le_normalizer_of_rho614 [Finite Γ] {K T X : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hTs : IsSylowTwoOf (T ⊓ K) K) (hZL : Subgroup.center (ModO2 K ⧸ Subgroup.center (ModO2 K)) = ⊥)
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hX : ∀ x (hx : x ∈ X), rho614 K ⟨x, hXK hx⟩ ∈ Subgroup.normalizer
      ((((T ⊓ K).subgroupOf (Subgroup.normalizer (K : Set Γ))).map (rho614 K) :
        Subgroup (MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K)))) : Set _)) :
    X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
  intro x hxX
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_of_rho614 hT2 hTs hZL (hXK hxX) (hX x hxX) hh, fun hh => ?_⟩
  have := conj_mem_of_rho614 hT2 hTs hZL (hXK (X.inv_mem hxX)) (hX _ (X.inv_mem hxX)) hh
  simpa [mul_assoc] using this

theorem kg614FiveChar2_of
    (hfon : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → Ch1.SQTKCharTwoLie W →
      FiveOverNorm614 W ∨ CFSG.Blueprint.ReeTitsModel W .Tits 2 1)
    (hT : TitsCenterFact614) : KG614FiveChar2 := by
  intro Γ _ _ H K T X hyp hW
  classical
  obtain ⟨-, -, hKq, -, hT2, hTK, hTs, -, hXO, hX5, hXn, hTX, hXK, hXinn, hXnt⟩ := hyp
  have hperf : commutator (ModO2 K) = ⊤ := by
    have := hKq.1
    exact Group.IsPerfect.commutator_eq_top
  have hLs : IsSimpleGroup (ModO2 K ⧸ Subgroup.center (ModO2 K)) := hKq.2.1
  obtain ⟨a, b, hab⟩ := hKq.2.2
  have hZL := FiveNorm.center_eq_bot_of_isSimpleGroup hab
  unfold Five614Concl
  rcases hfon _ hLs hW with hF | hTits
  · left
    have : Finite (MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K))) :=
      Finite.of_injective _ DFunLike.coe_injective
    have hDs := isSylowTwoOf_rho614 hT2 hTs
    obtain ⟨h5, hQN⟩ := exists_five_overgroup614 (rho614 K) hXK hTK
      (inf_le_left : T ⊓ K ≤ T) inf_le_left inf_le_right hT2 hXn hX5 hXO hTX
      (fun x hx => rho614_mem_range (hXinn hx) (hXK hx)) (exists_rho614_ne_one hXK hperf hXnt)
      hDs
    obtain ⟨S, P, hSs, hSP, hcard, hSmap, hPmap⟩ :=
      exists_pullback_inn614 hZL hDs le_sup_right hQN h5
    have hPN := hF S P hSs hSP hcard
    refine le_normalizer_of_rho614 hT2 hTs hZL hXK fun x hx => ?_
    have h1 : rho614 K ⟨x, hXK hx⟩ ∈ ((X.subgroupOf (Subgroup.normalizer (K : Set Γ))).map
        (rho614 K)) := ⟨⟨x, hXK hx⟩, hx, rfl⟩
    have h2 : rho614 K ⟨x, hXK hx⟩ ∈ P.map (MulAut.conj : _ →* MulAut _) := by
      rw [hPmap]
      exact Subgroup.mem_sup_left h1
    obtain ⟨p, hp, hpe⟩ := h2
    rw [← hpe, ← hSmap]
    exact Subgroup.le_normalizer_map _ ⟨p, hPN hp, rfl⟩
  · right
    right
    have : Group.IsPerfect (ModO2 K) := hKq.1
    have hZ := hT (ModO2 K) this (odd_card_center_modO2_614 K) hTits
    exact CFSG.SectionRank.reeTitsModel_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)) hTits

end CFSG.Quasithin.H13
