module

public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.H13.A5Inputs
public import CFSG.Quasithin.H13.A5Setting

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint
open scoped Pointwise

@[expose] def Dsub : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | InD σ}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : Equiv.Perm (Fin 5), InD a → InD b → InD (a * b) := by decide +kernel
    exact key a b ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : Equiv.Perm (Fin 5), InD a → InD a⁻¹ := by decide +kernel
    exact key a ha)

theorem mem_Dsub {σ : Equiv.Perm (Fin 5)} : σ ∈ Dsub ↔ InD σ := Iff.rfl

theorem card_Dsub : Nat.card Dsub = 8 := by
  have : Fintype.card {σ : Equiv.Perm (Fin 5) // InD σ} = 8 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

@[expose] noncomputable def Dsyl : Sylow 2 (Equiv.Perm (Fin 5)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard Dsub (by
    rw [card_Dsub, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h : Nat.factorial 5 = 2 ^ 3 * 15 := by decide
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]; rfl)

theorem InK4_of_D_alt : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ.sign = 1 → InK4 σ := by
  decide +kernel

theorem eq_one_of_normal_two : ∀ σ : Equiv.Perm (Fin 5), σ ^ 8 = 1 →
    (∀ τ : Equiv.Perm (Fin 5), τ.sign = 1 → (τ * σ * τ⁻¹) ^ 8 = 1 ∧
      (∀ ν : Equiv.Perm (Fin 5), ν.sign = 1 → (σ * (ν * σ * ν⁻¹)) ^ 8 = 1)) → σ = 1 := by
  decide +kernel

section Faithful

variable {G : Type} [Group G] [Finite G] {T L : Subgroup G}

theorem oTwoRes_eq_of_faithful (h : quasithinIsFaithfulLocal T L) : oTwoRes L = L := by
  refine h.2.1 _ (oTwoRes_le L) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (oTwoRes_le L)]
    intro y k hy hk
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes L hk) y).mp hy
  · intro x hx
    obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, Subgroup.subset_closure ⟨L.pow_mem hx _, m, hm, ?_⟩⟩
    rw [← pow_mul, ← hnm, pow_orderOf_eq_one]

theorem charTwo_of_faithful (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (h : quasithinIsFaithfulLocal T L) : CharTwo L := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH' : InH (S : Subgroup G) (L ⊔ (S : Subgroup G)) := ⟨le_sup_right, h.1.2.2.2⟩
  exact A4.charTwo_of_subnormal (subnormal_of_mem_cComp (cComp_of_isLocal h.1))
    (CFSG.Quasithin.charTwo_of_inH hEven S hH')

end Faithful

section Ext

variable {G : Type} [Group G] {L V : Subgroup G}
  (R : RawData5 L (Subgroup.centralizer (V : Set G)) V)

@[expose] noncomputable def alphaOf (g : ↥(Subgroup.normalizer (V : Set G))) : MulAut W5 :=
  (R.ψ.symm.trans (conjAct V g)).trans R.ψ

theorem alphaOf_apply (g : ↥(Subgroup.normalizer (V : Set G))) (x : W5) :
    alphaOf R g x = R.ψ (conjAct V g (R.ψ.symm x)) := rfl

theorem alphaOf_mul (g h : ↥(Subgroup.normalizer (V : Set G))) :
    alphaOf R (g * h) = alphaOf R g * alphaOf R h := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, alphaOf_apply, alphaOf_apply, alphaOf_apply, map_mul, MulAut.mul_apply,
    MulEquiv.symm_apply_apply]

theorem alphaOf_L (l : ↥L) : alphaOf R ⟨l, R.hnorm l.2⟩ = pact (R.θ l : Equiv.Perm (Fin 5)) := by
  refine MulEquiv.ext fun x => ?_
  rw [alphaOf_apply, R.equiv, MulEquiv.apply_symm_apply]

theorem exists_perm_alphaOf (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgL : (g : G) ∈ Subgroup.normalizer (L : Set G)) :
    ∃ π : Equiv.Perm (Fin 5), alphaOf R g = pact π := by
  have hconj : ∀ l : ↥L, ∃ l' : ↥L, (l' : G) = g * l * (g : G)⁻¹ := fun l =>
    ⟨⟨g * l * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hgL l).mp l.2⟩, rfl⟩
  have key : ∀ (l l' : ↥L), (l' : G) = g * l * (g : G)⁻¹ → ∀ x,
      alphaOf R g (pact (R.θ l : Equiv.Perm (Fin 5)) x) =
        pact (R.θ l' : Equiv.Perm (Fin 5)) (alphaOf R g x) := by
    intro l l' hl' x
    rw [← alphaOf_L, ← alphaOf_L, ← MulAut.mul_apply, ← MulAut.mul_apply, ← alphaOf_mul,
      ← alphaOf_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hl']
    group
  obtain ⟨π, hπ⟩ := exists_pact_of_normalizes (alphaOf R g) (fun σ hσ => by
      obtain ⟨l, hl⟩ := R.surj ⟨σ, hσ⟩
      obtain ⟨l', hl'⟩ := hconj l
      refine ⟨R.θ l', (R.θ l').2, fun x => ?_⟩
      have := key l l' hl' x
      rwa [hl] at this)
    (fun τ hτ => by
      obtain ⟨l', hl'⟩ := R.surj ⟨τ, hτ⟩
      let l : ↥L := ⟨(g : G)⁻¹ * l' * g, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l').mp l'.2
        simpa using this⟩
      refine ⟨R.θ l, (R.θ l).2, fun x => ?_⟩
      have := key l l' (by simp [l]; group) x
      rwa [hl'] at this)
  exact ⟨π, MulEquiv.ext hπ⟩

end Ext

section Rho

variable {G : Type} [Group G] {L V : Subgroup G}
  (R : RawData5 L (Subgroup.centralizer (V : Set G)) V)
  (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] noncomputable def rho0 : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 5) where
  toFun g := Classical.choose (exists_perm_alphaOf R g (hNL g.2))
  map_one' := by
    apply pact_injective
    rw [← Classical.choose_spec (exists_perm_alphaOf R 1
      (hNL (1 : ↥(Subgroup.normalizer (V : Set G))).2)), map_one]
    refine MulEquiv.ext fun x => ?_
    rw [alphaOf_apply, map_one, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]
  map_mul' g h := by
    apply pact_injective
    rw [← Classical.choose_spec (exists_perm_alphaOf R (g * h) (hNL (g * h).2)), map_mul,
      ← Classical.choose_spec (exists_perm_alphaOf R g (hNL g.2)),
      ← Classical.choose_spec (exists_perm_alphaOf R h (hNL h.2)), alphaOf_mul]

theorem pact_rho0 (g : ↥(Subgroup.normalizer (V : Set G))) :
    pact (rho0 R hNL g) = alphaOf R g :=
  (Classical.choose_spec (exists_perm_alphaOf R g (hNL g.2))).symm

theorem rho0_L (l : ↥L) : rho0 R hNL ⟨l, R.hnorm l.2⟩ = (R.θ l : Equiv.Perm (Fin 5)) := by
  apply pact_injective
  rw [pact_rho0, alphaOf_L]

theorem psi_conjAct_rho0 (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    R.ψ (conjAct V g v) = pact (rho0 R hNL g) (R.ψ v) := by
  rw [pact_rho0, alphaOf_apply, MulEquiv.symm_apply_apply]

end Rho

section FrameExist

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_frame (R : RawData5 L (Subgroup.centralizer (V : Set G)) V)
    (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsylL : IsSylowTwoOf (T ⊓ L) L) : Nonempty (Frame T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ0 := rho0 R hNL with hρ0
  let P : Subgroup (Equiv.Perm (Fin 5)) :=
    (T.subgroupOf (Subgroup.normalizer (V : Set G))).map ρ0
  have hP : IsPGroup 2 P :=
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map ρ0
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨π, hπ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) Q Dsyl
  let ρ : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 5) :=
    (MulAut.conj π).toMonoidHom.comp ρ0
  have hρ : ∀ g, ρ g = π * ρ0 g * π⁻¹ := fun g => rfl
  have hTD : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD (ρ g) := by
    intro g hg
    have h1 : ρ0 g ∈ (Q : Subgroup (Equiv.Perm (Fin 5))) := hPQ ⟨g, hg, rfl⟩
    have h2 : MulAut.conj π (ρ0 g) ∈ MulAut.conj π • (Q : Subgroup (Equiv.Perm (Fin 5))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hπ] at h2
    exact h2
  have hρL : ∀ l : ↥L, ρ ⟨l, R.hnorm l.2⟩ = π * (R.θ l : Equiv.Perm (Fin 5)) * π⁻¹ := by
    intro l
    rw [hρ, rho0_L]
  have hK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
      ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ := by
    let φ : ↥((T ⊓ L).subgroupOf L) →* A5 := R.θ.comp ((T ⊓ L).subgroupOf L).subtype
    have hφ2 : IsPGroup 2 φ.range := by
      have h1 : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
        hsylL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have h1top : IsPGroup 2 (⊤ : Subgroup ↥((T ⊓ L).subgroupOf L)) :=
        h1.of_equiv Subgroup.topEquiv.symm
      have := h1top.map φ
      rwa [← MonoidHom.range_eq_map] at this
    have hidx : φ.range.index ∣ ((T ⊓ L).subgroupOf L).index := by
      have : φ.range = ((T ⊓ L).subgroupOf L).map R.θ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [this]
      exact Subgroup.index_map_dvd _ R.surj
    have hodd : ¬ 2 ∣ φ.range.index := fun h => hsylL.2.2 (h.trans hidx)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hφ2
    have hmul := Subgroup.card_mul_index φ.range
    rw [hk, card_A5] at hmul
    have hk2 : k = 2 := by
      have hk6 : k ≤ 5 := by
        by_contra hk6
        have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        rcases Nat.eq_zero_or_pos φ.range.index with h0 | hpos
        · rw [h0] at hmul; omega
        · nlinarith
      interval_cases k <;> omega
    let K4' : Subgroup A5 := K4.map (conjA π⁻¹)
    have hle : φ.range ≤ K4' := by
      rintro _ ⟨⟨t, ht⟩, rfl⟩
      rw [Subgroup.mem_subgroupOf] at ht
      have hD := hTD ⟨t, hTV ht.1⟩ ht.1
      have hs : (ρ ⟨t, hTV ht.1⟩).sign = 1 := by
        have : (⟨t, hTV ht.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨(⟨t, ht.2⟩ : ↥L), R.hnorm ht.2⟩ := rfl
        rw [this, hρL, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
        have := (R.θ ⟨t, ht.2⟩).2
        rw [Equiv.Perm.mem_alternatingGroup] at this
        rw [this]
        simp
      have hk4 := InK4_of_D_alt _ hD hs
      refine ⟨conjA π (R.θ ⟨t, ht.2⟩), ?_, ?_⟩
      · have : (⟨t, hTV ht.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨(⟨t, ht.2⟩ : ↥L), R.hnorm ht.2⟩ := rfl
        rw [this, hρL] at hk4
        exact hk4
      · apply Subtype.ext
        rw [conjA_coe, conjA_coe]
        group
        rfl
    have hcard : Nat.card K4' = 4 := by
      rw [Subgroup.card_map_of_injective (conjA_injective _), card_K4]
    have heq : φ.range = K4' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hk, hk2]; norm_num)
    intro σ hσ
    have hσA : σ.sign = 1 := by rcases hσ with rfl | rfl | rfl | rfl <;> decide
    have hmem : conjA π⁻¹ ⟨σ, hσA⟩ ∈ φ.range := by
      rw [heq]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨⟨t, ht⟩, hφt⟩ := hmem
    rw [Subgroup.mem_subgroupOf] at ht
    refine ⟨⟨t, hTV ht.1⟩, ht.1, ?_⟩
    have : (⟨t, hTV ht.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨(⟨t, ht.2⟩ : ↥L), R.hnorm ht.2⟩ := rfl
    rw [this, hρL]
    have h2 := congrArg (fun a : A5 => (a : Equiv.Perm (Fin 5))) hφt
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, conjA_coe] at h2
    rw [show (R.θ ⟨t, ht.2⟩ : Equiv.Perm (Fin 5)) = π⁻¹ * σ * π by
      rw [show (⟨t, ht.2⟩ : ↥L) = (((⟨t, by rw [Subgroup.mem_subgroupOf]; exact ht⟩ :
        ↥((T ⊓ L).subgroupOf L)) : ↥L)) from rfl]
      rw [h2]; group]
    group
  refine ⟨{ L_le := R.hnorm
            T_le := hTV
            ψ := R.ψ.trans (pact π)
            ρ := ρ
            equiv := fun g v => ?_
            image_L := fun σ => ?_
            T_D := hTD
            K4_T := hK4 }⟩
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, psi_conjAct_rho0 R hNL, hρ,
      ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    rw [hρ0]
    group
  · constructor
    · rintro ⟨g, hgL, rfl⟩
      have : g = ⟨(⟨g, hgL⟩ : ↥L), R.hnorm hgL⟩ := rfl
      rw [this, hρL, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
      have := (R.θ ⟨g, hgL⟩).2
      rw [Equiv.Perm.mem_alternatingGroup] at this
      rw [this]
      simp
    · intro hσ
      have hσ' : π⁻¹ * σ * π ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, hσ,
          Equiv.Perm.sign_inv]
        simp
      obtain ⟨l, hl⟩ := R.surj ⟨π⁻¹ * σ * π, hσ'⟩
      refine ⟨⟨l, R.hnorm l.2⟩, l.2, ?_⟩
      rw [hρL, hl]
      group

end FrameExist

theorem conjAct_val {G : Type} [Group G] (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G)))
    (x : ↥V) : ((conjAct V g x : ↥V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

section Reduced

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem Frame.rho_eq_one_of_mem (F : Frame T L V) (g : ↥(Subgroup.normalizer (V : Set G)))
    (hg : (g : G) ∈ Subgroup.centralizer (V : Set G)) : F.ρ g = 1 := by
  apply pact_injective
  refine MulEquiv.ext fun x => ?_
  obtain ⟨v, rfl⟩ := F.ψ.surjective x
  rw [← F.equiv, map_one, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [conjAct_val]
  have := Subgroup.mem_centralizer_iff.mp hg v v.2
  calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [this]
    _ = v := by group

omit [Finite G] in
theorem Frame.mem_centralizer_of_rho (F : Frame T L V) (g : ↥(Subgroup.normalizer (V : Set G)))
    (hg : F.ρ g = 1) : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := F.equiv g ⟨v, hv⟩
  rw [hg, map_one, MulAut.one_apply] at h
  have := congrArg Subtype.val (F.ψ.injective h)
  rw [conjAct_val] at this
  calc v * g = g * v * (g : G)⁻¹ * g := by rw [this]
    _ = g * v := by group

theorem pow_eight_of_pow_two_pow {σ : Equiv.Perm (Fin 5)} {k : ℕ} (h : σ ^ 2 ^ k = 1) :
    σ ^ 8 = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf σ ∣ 120 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [hjeq] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    have := this.trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
  exact Nat.pow_dvd_pow 2 hj3 |>.trans (by norm_num)

omit [Finite G] in
theorem Frame.le_centralizer (F : Frame T L V) {D : Subgroup G} (hDLT : D ≤ L ⊔ T)
    (hn : L ⊔ T ≤ Subgroup.normalizer (D : Set G))
    (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G)) :
    D ≤ Subgroup.centralizer (V : Set G) := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le F.L_le F.T_le
  have hD8 : ∀ d (hd : d ∈ D), (F.ρ ⟨d, hLTV (hDLT hd)⟩) ^ 8 = 1 := by
    intro d hd
    obtain ⟨k, hk⟩ := h2 d hd
    refine pow_eight_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    exact F.rho_eq_one_of_mem _ (by simpa using hk)
  intro d hd
  refine F.mem_centralizer_of_rho ⟨d, hLTV (hDLT hd)⟩ (eq_one_of_normal_two _ (hD8 d hd) ?_)
  intro τ hτ
  obtain ⟨l, hlL, rfl⟩ := (F.image_L τ).2 hτ
  have hlD : (l : G) * d * (l : G)⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hn (le_sup_left (a := L) hlL)) d).mp hd
  refine ⟨?_, fun ν hν => ?_⟩
  · have := hD8 _ hlD
    have e : (⟨(l : G) * d * (l : G)⁻¹, hLTV (hDLT hlD)⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = l * ⟨d, hLTV (hDLT hd)⟩ * l⁻¹ := rfl
    rwa [e, map_mul, map_mul, map_inv] at this
  · obtain ⟨l', hl'L, rfl⟩ := (F.image_L ν).2 hν
    have hl'D : (l' : G) * d * (l' : G)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hn (le_sup_left (a := L) hl'L)) d).mp hd
    have hprod : d * ((l' : G) * d * (l' : G)⁻¹) ∈ D := D.mul_mem hd hl'D
    have := hD8 _ hprod
    have e : (⟨d * ((l' : G) * d * (l' : G)⁻¹), hLTV (hDLT hprod)⟩ :
        ↥(Subgroup.normalizer (V : Set G))) =
        ⟨d, hLTV (hDLT hd)⟩ * (l' * ⟨d, hLTV (hDLT hd)⟩ * l'⁻¹) := rfl
    rwa [e, map_mul, map_mul, map_mul, map_inv] at this

end Reduced

section Exist

variable {G : Type} [Group G] [Finite G] {T L : Subgroup G}

omit [Finite G] in
theorem pow_mem_mul_of_normalizes {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) : ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht n) l).mp hl
    · rw [pow_succ, he]
      group

theorem exists_setting (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h : QTH13 G T L)
    (hA5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5))) :
    ∃ V : Subgroup G, Nonempty (Setting G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTN, hmax, hMmax, huniq⟩ := h132two G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨⟨V, hV⟩, hall⟩ := h132fsu G T L h L h.faithful
  obtain ⟨hVT, hTV, hfsu⟩ := hall V hV
  obtain ⟨R⟩ := h132A5 G T L h L h.faithful hA5 V hV
  have hVne : V ≠ ⊥ := hV.2.1
  have hab : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => R.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
    have hx2 : (⟨x, hx⟩ : ↥V) * ⟨x, hx⟩ = 1 := by
      apply R.ψ.injective
      rw [map_mul, map_one]
      show Multiplicative.ofAdd (Multiplicative.toAdd (R.ψ ⟨x, hx⟩) +
        Multiplicative.toAdd (R.ψ ⟨x, hx⟩)) = 1
      rw [Ev_add_self]
      rfl
    have := congrArg Subtype.val hx2
    simpa [pow_two] using this
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa using hab.2 g g.2)⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := R.hnorm
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hVne, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame R hNL h.sylow.1 hTV hsylL
  have hO2 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
    F.le_centralizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => by
        obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
        exact ⟨k, by
          have := congrArg Subtype.val hk
          simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
          rw [this]
          exact Subgroup.one_mem _⟩
  have hCL : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨φ, hφ, hker⟩ := hA5
    have hc1 : Nat.card ↥L = Nat.card φ.ker * 60 := by
      rw [← card_A5, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hc2 : Nat.card ↥L = Nat.card R.θ.ker * 60 := by
      rw [← card_A5, ← Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective R.θ R.surj).toEquiv, mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup R.θ.ker
    have hle : φ.ker ≤ R.θ.ker := by
      intro x hx
      rw [hker] at hx
      rw [R.ker_eq, Subgroup.mem_subgroupOf]
      have hxO : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
      have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
          (hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      exact hO2 (hO2L hxO)
    have heq : φ.ker = R.θ.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
    intro x hx
    have hxk : (⟨x, hx.1⟩ : ↥L) ∈ φ.ker := by
      rw [heq, R.ker_eq, Subgroup.mem_subgroupOf]
      exact hx.2
    rw [hker] at hxk
    have hxO : x ∈ pCoreOf 2 L := ⟨⟨x, hx.1⟩, hxk, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨x, hxO⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := h.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mem_mul_of_normalizes hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := hCL l' ⟨hl', hC⟩
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk]
  have hCn : L ⊔ T ≤
      Subgroup.normalizer (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ L ⊔ T, ∀ c, c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) →
        g * c * g⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      intro g hg c hc
      refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg), ?_⟩
      show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V :=
        (Subgroup.mem_normalizer_iff''.mp (hLTV hg) v).mp hv
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * v := by group
    intro c
    refine ⟨key g hg c, fun hc => ?_⟩
    simpa [mul_assoc] using key g⁻¹ ((L ⊔ T).inv_mem hg) _ hc
  have hcLT : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    le_antisymm
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hO2)
  exact ⟨V, ⟨{
    h13 := h
    a5 := hA5
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    oTwoRes_L := oTwoRes_eq_of_faithful h.faithful
    charTwo_L := charTwo_of_faithful h.qtke.2.1 h.sylow h.faithful
    reduced := ⟨hVT.trans le_sup_right, hLTV, hab, fun D hDLT hDn hD2 =>
      F.le_centralizer hDLT hDn hD2⟩
    cLT := hcLT
    frame := F
    irr := hV
    fsu := hfsu }⟩⟩

end Exist

end CFSG.Quasithin.H13.A5
