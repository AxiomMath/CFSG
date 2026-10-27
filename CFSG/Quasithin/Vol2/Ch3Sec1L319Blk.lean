module

public import CFSG.Quasithin.Vol2.Ch3zXLev
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Sl2
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch3z G6

section Perm

theorem perm_eq_one_of_conj_fix {m : ℕ} (p : Fin m) (σ : Equiv.Perm (Fin m))
    (h : ∀ τ : Equiv.Perm (Fin m), (τ * σ * τ⁻¹) p = p) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i = p
  · subst hi
    have := h 1
    simpa using this
  · have h1 := h (Equiv.swap p i)
    have e1 : (Equiv.swap p i)⁻¹ p = i := by
      rw [Equiv.swap_inv, Equiv.swap_apply_left]
    have e2 : (Equiv.swap p i * σ * (Equiv.swap p i)⁻¹) p = Equiv.swap p i (σ i) := by
      simp [Equiv.Perm.mul_apply, e1]
    rw [e2] at h1
    have h3 : σ i = Equiv.swap p i p := by
      have := congrArg (Equiv.swap p i) h1
      rwa [Equiv.swap_apply_self] at this
    rw [h3, Equiv.swap_apply_left]
    rfl

theorem perm_eq_one_of_central {m : ℕ} (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (h : ∀ τ : Equiv.Perm (Fin m), τ * σ = σ * τ) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i ∧ j ≠ σ i := by
    have hlt : ({i, σ i} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
      have := Finset.card_le_two (a := i) (b := σ i)
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨j, fun h' => hj (by simp [h']), fun h' => hj (by simp [h'])⟩
  have h1 := congrArg (fun f : Equiv.Perm (Fin m) => f i) (h (Equiv.swap i j))
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  have hne' : σ i ≠ i := by simpa using hne
  rw [Equiv.swap_apply_of_ne_of_ne hne' (Ne.symm hj.2)] at h1
  exact hj.1 (σ.injective (by simpa using h1.symm))

theorem sym_block_core_bot {Γ : Type*} [Group Γ] {H M E : Subgroup Γ} {m : ℕ}
    (θ : ↥H ≃* Equiv.Perm (Fin m)) (p : Fin m)
    (hM : ∀ x : ↥H, (x : Γ) ∈ M → θ x ∈ MulAction.stabilizer (Equiv.Perm (Fin m)) p)
    (hEH : E ≤ H) (hEn : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E) (hEM : E ≤ M) : E = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  have h1 : θ ⟨e, hEH he⟩ = 1 := by
    refine perm_eq_one_of_conj_fix p _ fun τ => ?_
    set y : ↥H := θ.symm τ with hy
    have hmem : ((y * ⟨e, hEH he⟩ * y⁻¹ : ↥H) : Γ) ∈ E := hEn y y.2 e he
    have := hM (y * ⟨e, hEH he⟩ * y⁻¹) (hEM hmem)
    rw [map_mul, map_mul, map_inv, hy, MulEquiv.apply_symm_apply] at this
    exact this
  have h2 : (⟨e, hEH he⟩ : ↥H) = 1 := θ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem sym_block_center_bot {Γ : Type*} [Group Γ] {H : Subgroup Γ} {m : ℕ} (hm : 3 ≤ m)
    (θ : ↥H ≃* Equiv.Perm (Fin m)) {x : Γ} (hxH : x ∈ H) (hx : ∀ g ∈ H, g * x = x * g) : x = 1 := by
  have h1 : θ ⟨x, hxH⟩ = 1 := by
    refine perm_eq_one_of_central hm _ fun τ => ?_
    have := hx (θ.symm τ : Γ) (θ.symm τ).2
    have h2 : θ.symm τ * ⟨x, hxH⟩ = ⟨x, hxH⟩ * θ.symm τ := Subtype.ext this
    have h3 := congrArg θ h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3
  have h2 : (⟨x, hxH⟩ : ↥H) = 1 := θ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end Perm

section Natural

variable {V : Type} [CommGroup V]

theorem natBlock_core_bot {H Q E : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ} (he : 1 ≤ e)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hN : NatBlockData H U e)
    (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q H) (hEH : E ≤ H)
    (hEn : ∀ g ∈ H, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set (MulAut V))) : E = ⊥ := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply sl2_eq_one_of_mulVec
    intro w
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd w)
    have h1 := hβeq γ u (hUinv _ (π γ).2 _ u.2)
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ : ↥U) = u := by
      apply Subtype.ext
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa using h3.symm
  have hQH : Q ≤ H := hQ.1
  have hcardH : Nat.card H = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπs⟩),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have : Finite H := Finite.of_surjective π hπs
  have : Finite Q := Finite.of_injective (Subgroup.inclusion hQH) (Subgroup.inclusion_injective hQH)
  have hQcard : Nat.card Q = Nat.card K := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ.2.1
    have hidx : Odd (Q.subgroupOf H).index :=
      Nat.not_even_iff_odd.mp (fun h => hQ.2.2 (even_iff_two_dvd.mp h))
    have h1 : Nat.card (Q.subgroupOf H) * (Q.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (Q.subgroupOf H) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    rw [h2, hk, hcardH, hK] at h1
    have hm : Odd ((2 ^ e) ^ 2 - 1) := by
      have h2e : Even ((2 ^ e) ^ 2) := (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
        two_ne_zero⟩)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) h2e odd_one
    have hc1 : Nat.Coprime (2 ^ k) ((2 ^ e) ^ 2 - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    have hc2 : Nat.Coprime (2 ^ e) (Q.subgroupOf H).index :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hidx)
    have hd1 : 2 ^ k ∣ 2 ^ e := hc1.dvd_of_dvd_mul_right ⟨_, h1.symm⟩
    have hd2 : 2 ^ e ∣ 2 ^ k := by
      have : 2 ^ e ∣ 2 ^ k * (Q.subgroupOf H).index := ⟨_, h1⟩
      exact hc2.dvd_of_dvd_mul_right this
    have : k = e := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd1)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2)
    rw [hk, hK, this]
  have hchar : CharP K 2 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    haveI := Fintype.ofFinite K
    obtain ⟨n, hpp, hcard⟩ := FiniteField.card K p
    have hdvd : p ∣ 2 ^ e := by
      rw [← hK, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self p (by exact_mod_cast n.pos.ne')
    have : p ∣ 2 := hpp.dvd_of_dvd_pow hdvd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this
    exact this ▸ hp
  let E' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (E.subgroupOf H).comap π
  let Q' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (Q.subgroupOf H).comap π
  have hQ'card : Nat.card Q' = Nat.card K := by
    have : Nat.card Q' = Nat.card (Q.subgroupOf H) :=
      Nat.card_congr (Equiv.subtypeEquiv (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).toEquiv
        (fun γ => Iff.rfl))
    rw [this, ← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hE'mem : ∀ γ, γ ∈ E' ↔ ((π γ : ↥H) : MulAut V) ∈ E := fun γ => Iff.rfl
  have hE'n : E'.Normal := by
    refine ⟨fun γ hγ δ => ?_⟩
    rw [hE'mem] at hγ ⊢
    have := hEn (π δ : ↥H) (π δ).2 _ hγ
    simpa using this
  have hE'N : E' ≤ Subgroup.normalizer (Q' : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    intro γ hγ
    have hγN := hEQ ((hE'mem γ).mp hγ)
    rw [Subgroup.mem_normalizer_iff]
    intro δ
    have hmem : ∀ γ' : Matrix.SpecialLinearGroup (Fin 2) K, γ' ∈ Q' ↔ ((π γ' : ↥H) : MulAut V) ∈ Q :=
      fun γ' => Iff.rfl
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    have := Subgroup.mem_normalizer_iff.mp hγN ((π δ : ↥H) : MulAut V)
    simpa using this
  have hE'bot : E' = ⊥ := sl2_normal_le_normalizer_sylow E' Q' hE'n hQ'card hE'N
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨γ, hγ⟩ := hπs ⟨x, hEH hx⟩
  have hγE : γ ∈ E' := by
    rw [hE'mem, hγ]
    exact hx
  rw [hE'bot, Subgroup.mem_bot] at hγE
  subst hγE
  have := congrArg Subtype.val hγ
  simpa using this.symm

end Natural

section Blocks

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {𝓗 : Finset (Subgroup (MulAut V))}

theorem BlkCtx.ffJ_le_normalizer_block (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    ffJ X ≤ Subgroup.normalizer (H : Set (MulAut V)) := by
  rw [h.ffJ_eq]
  refine iSup₂_le fun H' hH' x hx => ?_
  by_cases hne : H' = H
  · subst hne
    exact Subgroup.le_normalizer hx
  · refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
    · have := h.comm_of_ne hH' hH hne hx hy
      rw [this, mul_inv_cancel_right]
      exact hy
    · have := h.comm_of_ne hH' hH hne (H'.inv_mem hx) hy
      rw [this, inv_mul_cancel_right]
      exact hy

theorem BlkCtx.block_props (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    (∀ E : Subgroup (MulAut V), E ≤ H → (∀ g ∈ H, ∀ e ∈ E, g * e * g⁻¹ ∈ E) → E ≤ M → E = ⊥) ∧
    (∀ x ∈ H, (∀ g ∈ H, g * x = x * g) → x = 1) ∧
    (∀ x ∈ H, (∀ v ∈ commV H, x v = v) → x = 1) := by
  have hUinv : ∀ h' ∈ H, ∀ u ∈ commV H, h' u ∈ commV H := fun _ hx _ hu =>
    apply_mem_commV_of_mem hx hu
  rcases h.types H hH with ⟨e, he1, hbin, hM⟩ | ⟨k, hk1, π, hreal, hM⟩
  · have hZ : commV H ⊓ fixV (ffJ X) = ⊥ := by rw [h.fixV_ffJ, inf_bot_eq]
    rw [hZ] at hbin
    have hnat := natBlockData_of_binaryNatural hbin
    have hQ := h.isSylowTwoOf_block hH
    have hcore : ∀ E : Subgroup (MulAut V), E ≤ H → (∀ g ∈ H, ∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        E ≤ M → E = ⊥ := by
      intro E hEH hEn hEM
      refine natBlock_core_bot he1 hUinv hnat hQ hEH hEn ?_
      intro x hx
      have : x ∈ M ⊓ H := ⟨hEM hx, hEH hx⟩
      rw [hM] at this
      exact this.2
    refine ⟨hcore, fun x hxH hxc => ?_, ?_⟩
    ·
      have hxN : x ∈ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) := by
        have hfix : ∀ y ∈ T ⊓ H, x * y * x⁻¹ = y := fun y hy => by
          have := hxc y hy.2
          rw [← this]; group
        refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
        · rw [hfix y hy]; exact hy
        · have : x⁻¹ * y * x = y := by
            have := hfix y hy
            calc x⁻¹ * y * x = x⁻¹ * (x * y * x⁻¹) * x := by rw [this]
              _ = y := by group
          rw [this]; exact hy
      have hxM : x ∈ M := by
        have : x ∈ M ⊓ H := by rw [hM]; exact ⟨hxH, hxN⟩
        exact this.1
      have hzp : Subgroup.zpowers x = ⊥ := by
        refine hcore _ (Subgroup.zpowers_le.mpr hxH) ?_ (Subgroup.zpowers_le.mpr hxM)
        intro g hg y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcomm : g * x = x * g := hxc g hg
        have h1 : g * x * g⁻¹ = x := by rw [hcomm]; group
        rw [← conj_zpow, h1]
        exact Subgroup.zpow_mem_zpowers x n
      have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [hzp] at this
      exact Subgroup.mem_bot.mp this
    · intro x hxH hxtriv
      obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hnat
      obtain ⟨γ, hγ⟩ := hπs ⟨x, hxH⟩
      have hγ1 : γ = 1 := by
        apply sl2_eq_one_of_mulVec
        intro w
        obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd w)
        have h1 := hβeq γ u (hUinv _ (π γ).2 _ u.2)
        have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ : ↥(commV H)) = u := by
          apply Subtype.ext
          rw [hγ]
          exact hxtriv _ u.2
        rw [h2, hu] at h1
        have h3 := congrArg Multiplicative.toAdd h1
        simpa using h3.symm
      subst hγ1
      have := congrArg Subtype.val hγ
      simpa using this.symm
  · obtain ⟨θ, β, hθπ, hβeq, hβr, hβk⟩ := isSymCore_of_realizes' hreal
    have hm3 : 3 ≤ 2 * k + 1 := by omega
    have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
    refine ⟨fun E hEH hEn hEM => ?_, fun x hxH hxc => ?_, fun x hxH hxtriv => ?_⟩
    · refine sym_block_core_bot θ ⟨0, by omega⟩ ?_ hEH hEn hEM
      intro x hxM
      have hmem : (x : MulAut V) ∈ M ⊓ H := ⟨hxM, x.2⟩
      have hx' : x ∈ (M ⊓ H).subgroupOf H := hmem
      rw [hM] at hx'
      obtain ⟨σ, hσ, hσx⟩ := hx'
      have : θ x = σ := by
        rw [← hσx, ← hθπ σ]
        exact θ.apply_symm_apply σ
      rw [this]
      exact hσ
    · exact sym_block_center_bot hm3 θ hxH hxc
    · have h1 : coreAct (2 * k + 1) (θ ⟨x, hxH⟩) = 1 := by
        refine MulEquiv.ext fun u => ?_
        have h2 := hβeq ⟨x, hxH⟩ u
        have hβu : β u ∈ commV H := by rw [← hβr]; exact ⟨u, rfl⟩
        have h4 : β (coreAct (2 * k + 1) (θ ⟨x, hxH⟩) u) = β u := by
          rw [h2]
          exact hxtriv _ hβu
        exact (MonoidHom.ker_eq_bot_iff β).mp hβk h4
      have h5 := (coreAct_eq_one_iff (2 * k + 1) hodd _).mp h1
      have h6 : (⟨x, hxH⟩ : ↥H) = 1 := θ.injective (by rw [h5, map_one])
      exact congrArg Subtype.val h6

theorem BlkCtx.kerIn_eq_bot (h : BlkCtx X T M 𝓗) (hO : pCoreOf 2 X = ⊥) : kerIn M X = ⊥ := by
  have hmp := h.mp
  set D := kerIn M X with hD
  have hDX : D ≤ X := hmp.kerIn_le_H
  have hDn : X ≤ Subgroup.normalizer (D : Set (MulAut V)) := le_normalizer_kerIn M X
  have hodd : ∀ x ∈ D, Odd (orderOf x) := by
    have hS := hmp.isSylowTwoOf_pCoreOf_kerIn
    rw [hO] at hS
    have h2 : ¬ 2 ∣ Nat.card D := by
      have := hS.2.2
      rwa [Subgroup.bot_subgroupOf, Subgroup.index_bot] at this
    intro x hx
    have h1 : orderOf x ∣ Nat.card D := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (orderOf x) with he | ho
      · exact absurd (even_iff_two_dvd.mp he |>.trans h1) h2
      · exact Nat.odd_iff.mp ho)
  have hJX : ffJ X ≤ X := by
    rw [h.ffJ_eq]
    exact iSup₂_le fun H hH => h.mem_le hH
  have hTR : twoResidual X ≤ ffJ X := by
    refine twoResidual_le_of_isTwoQuotient hJX (B6.le_normalizer_ffJ X) ?_
    exact B6.isTwoQuotient_of_sup_eq hmp.isSylow.2.1 (B6.le_normalizer_ffJ X)
      (by rw [sup_comm]; exact h.eq_sup.symm)
  have hDJ : D ≤ ffJ X := fun x hx => hTR (F6.mem_twoResidual_of_odd (hDX hx) (hodd x hx))
  have hcomm : ∀ H ∈ 𝓗, ∀ y ∈ D, ∀ g ∈ H, y * g = g * y := by
    intro H hH y hy g hg
    have hgX : g ∈ X := h.mem_le hH hg
    set E : Subgroup (MulAut V) := D ⊓ H with hE
    have hEbot : E = ⊥ := by
      refine (BlkCtx.block_props h hH).1 E inf_le_right ?_ (inf_le_left.trans kerIn_le)
      intro g' hg' e he
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hDn (h.mem_le hH hg')) e).mp he.1
        exact this
      · exact H.mul_mem (H.mul_mem hg' he.2) (H.inv_mem hg')
    have hc : y * g * y⁻¹ * g⁻¹ ∈ E := by
      refine ⟨?_, ?_⟩
      · have h1 : g * y⁻¹ * g⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (hDn hgX) y⁻¹).mp (D.inv_mem hy)
        have := D.mul_mem hy h1
        simpa [mul_assoc] using this
      · have hn := BlkCtx.ffJ_le_normalizer_block h hH (hDJ hy)
        have h2 : y * g * y⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hn g).mp hg
        exact H.mul_mem h2 (H.inv_mem hg)
    rw [hEbot, Subgroup.mem_bot] at hc
    calc y * g = (y * g * y⁻¹ * g⁻¹) * g * y := by group
      _ = g * y := by rw [hc]; group
  have hfix : ∀ y ∈ D, ∀ H ∈ 𝓗, ∀ v ∈ commV H, y v = v := by
    intro y hy H hH v hv
    let P : Subgroup (MulAut V) :=
      { carrier := {z | ∃ k ∈ H, ∀ w ∈ commV H, z w = k w}
        one_mem' := ⟨1, H.one_mem, fun w _ => rfl⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
          refine ⟨k₁ * k₂, H.mul_mem hk₁ hk₂, fun w hw => ?_⟩
          show z₁ (z₂ w) = k₁ (k₂ w)
          rw [h₂ w hw, h₁ _ (apply_mem_commV_of_mem hk₂ hw)]
        inv_mem' := by
          rintro z ⟨k, hk, hz⟩
          refine ⟨k⁻¹, H.inv_mem hk, fun w hw => ?_⟩
          have hkw : k⁻¹ w ∈ commV H := apply_mem_commV_of_mem (H.inv_mem hk) hw
          have h1 : z (k⁻¹ w) = w := by rw [hz _ hkw]; simp
          have h2 : z⁻¹ w = k⁻¹ w := by
            have := congrArg (fun u => z⁻¹ u) h1
            simpa using this.symm
          exact h2 }
    have hJP : ffJ X ≤ P := by
      rw [h.ffJ_eq]
      refine iSup₂_le fun H' hH' z hz => ?_
      by_cases hne : H' = H
      · subst hne
        exact ⟨z, hz, fun w _ => rfl⟩
      · exact ⟨1, H.one_mem, fun w hw => by simpa using h.act_commV_of_ne hH hH' (Ne.symm hne) hz hw⟩
    obtain ⟨k, hk, hyk⟩ := hJP (hDJ hy)
    have hkc : ∀ g ∈ H, g * k = k * g := by
      intro g hg
      have hf := (BlkCtx.block_props h hH).2.2 (g * k * g⁻¹ * k⁻¹) ?_ ?_
      · calc g * k = (g * k * g⁻¹ * k⁻¹) * k * g := by group
          _ = k * g := by rw [hf]; group
      · exact H.mul_mem (H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg)) (H.inv_mem hk)
      · intro w hw
        have hyg := hcomm H hH y hy g hg
        have hcm : ∀ u ∈ commV H, k (g u) = g (k u) := by
          intro u hu
          have h1 : y (g u) = g (y u) := by
            have := congrArg (fun z : MulAut V => z u) hyg
            simpa [MulAut.mul_apply] using this
          rw [← hyk _ (apply_mem_commV_of_mem hg hu), h1, hyk _ hu]
        have ha : k⁻¹ w ∈ commV H := apply_mem_commV_of_mem (H.inv_mem hk) hw
        have hb : g⁻¹ (k⁻¹ w) ∈ commV H := apply_mem_commV_of_mem (H.inv_mem hg) ha
        show (g * k * g⁻¹ * k⁻¹) w = w
        simp only [MulAut.mul_apply]
        rw [← hcm _ hb]
        simp
    have hk1 : k = 1 := (BlkCtx.block_props h hH).2.1 k hk (fun g hg => hkc g hg)
    rw [hyk v hv, hk1]
    rfl
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun v => ?_
  let Fx : Subgroup V :=
    { carrier := {w | y w = w}
      one_mem' := map_one y
      mul_mem' := fun {a b} ha hb => by
        show y (a * b) = a * b
        rw [map_mul, show y a = a from ha, show y b = b from hb]
      inv_mem' := fun {a} ha => by
        show y a⁻¹ = a⁻¹
        rw [map_inv, show y a = a from ha] }
  have hle : ⨆ H ∈ 𝓗, commV H ≤ Fx := iSup₂_le fun H hH w hw => hfix y hy H hH w hw
  have hv' : v ∈ Fx := hle (by rw [h.iSup_comm]; trivial)
  exact hv'

end Blocks

end CFSG.Quasithin.H13.L319
