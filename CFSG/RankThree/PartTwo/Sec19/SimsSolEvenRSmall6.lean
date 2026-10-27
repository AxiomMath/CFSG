module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Perm
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Base
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallII
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall (PresPair exists_pair_witness conj_normalized
  conj_mem_of_comm two_pow_of_mem_conj inf_conj_eq_bot card_conj comm_R_conj K_comm_W
  mem_Q_of_pi_eq exists_lift_pow_three comm_of_pow_three R_normalized conj_ne_of_not_mem
  add_mem_range_heartToBar)
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

@[expose] def Lemma3Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6), C.PiData →
    (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X) →
    (∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r) → Nat.card ↥(Rc X) = 4 →
    ∀ g : G, ∀ hTM : conjSubgroup g (Rc X) ≤ M, conjSubgroup g (Rc X) ≠ Rc X →
      conjSubgroup g (Rc X) ⊓ C.K = ⊥ → ∀ π : Perm (Fin 6),
      (∀ t (ht : t ∈ conjSubgroup g (Rc X)), InP π (C.θ ⟨t, hTM ht⟩)) →
      ∃ z : ↥X, (z : G) ∈ Subgroup.normalizer ((conjSubgroup g (Rc X) : Subgroup G) : Set G) ∧
        (z : G) ^ 3 = 1 ∧ C.θ ⟨z, C.S.le z.2⟩ ≠ 1

@[expose] def CaseIISix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6), C.PiData →
    (Nonempty C.UIso ∨ Function.Injective C.β) →
    (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X) →
    (∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r) → 3 ≤ Nat.card ↥(Rc X) →
    (∀ g : G, g ∉ M → conjSubgroup g (Rc X) ≤ M →
      conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M ≠ ⊥) →
    ∀ g : G, g ∉ M → conjSubgroup g (Rc X) ≤ M → False

theorem comm_of_comm_conj (S : Setting G M X 6) {g : G} (hTM : conjSubgroup g (Rc X) ≤ M)
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M = ⊥) {t : G}
    (ht : t ∈ conjSubgroup g (Rc X)) (ht1 : t ≠ 1) {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M)
    (hqt : q * t = t * q) {τ : G} (hτ : τ ∈ conjSubgroup g (Rc X)) : q * τ = τ * q := by
  set T := conjSubgroup g (Rc X) with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have h1 : q * τ * q⁻¹ ∈ T := conj_normalized S (conj_mem_of_comm S ht ht1 hqt) hτ
  have h3 : q * τ * q⁻¹ * τ⁻¹ ∈ Q := by
    have h4 : τ * q⁻¹ * τ⁻¹ ∈ Q := pCoreOf_normalized M (hTM hτ) (Q.inv_mem hq)
    have e : q * τ * q⁻¹ * τ⁻¹ = q * (τ * q⁻¹ * τ⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq h4
  have h5 : q * τ * q⁻¹ * τ⁻¹ ∈ T ⊓ Q := ⟨T.mul_mem h1 (T.inv_mem hτ), h3⟩
  rw [hTQ, Subgroup.mem_bot] at h5
  calc q * τ = (q * τ * q⁻¹ * τ⁻¹) * (τ * q) := by group
    _ = τ * q := by rw [h5, one_mul]

theorem eq_of_theta_eq (C : Cfg G M X 6) {T : Subgroup G} (hTM : T ≤ M) (hTK : T ⊓ C.K = ⊥)
    {a b : G} (ha : a ∈ T) (hb : b ∈ T) (h : C.θ ⟨a, hTM ha⟩ = C.θ ⟨b, hTM hb⟩) : a = b := by
  have hab : a * b⁻¹ ∈ C.K := by
    rw [C.mem_K]
    refine ⟨M.mul_mem (hTM ha) (M.inv_mem (hTM hb)), ?_⟩
    have e : (⟨a * b⁻¹, M.mul_mem (hTM ha) (M.inv_mem (hTM hb))⟩ : ↥M) =
        ⟨a, hTM ha⟩ * (⟨b, hTM hb⟩ : ↥M)⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  have h1 : a * b⁻¹ ∈ T ⊓ C.K := ⟨T.mul_mem ha (T.inv_mem hb), hab⟩
  rw [hTK, Subgroup.mem_bot] at h1
  calc a = a * b⁻¹ * b := by group
    _ = b := by rw [h1, one_mul]

theorem mem_centralizer_of_odd_of_commute {C : Cfg G M X 6} (D : C.PiData) {y : G} (hyM : y ∈ M)
    {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) (π : Perm (Fin 6))
    (hc : C.θ ⟨y, hyM⟩ * sig1 π = sig1 π * C.θ ⟨y, hyM⟩) :
    y ∈ Subgroup.centralizer (X : Set G) := by
  have hθm : C.θ ⟨y, hyM⟩ ^ m = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyM⟩ : ↥M) ^ m = 1 := Subtype.ext (by simpa using hym)
    rw [e, map_one]
  have h1 := eq_one_of_commute_of_pow_odd π hc hm hθm
  exact mem_centralizer_of_odd D (C.mem_K.2 ⟨hyM, h1⟩) hm hym

theorem sig1_ne_one (π : Perm (Fin 6)) : sig1 π ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : Perm (Fin 6) => σ (π 0)) h
  simp only [sig1, Perm.mul_apply, Perm.one_apply] at h1
  rw [swap_apply_of_ne_of_ne (π.injective.ne (by decide)) (π.injective.ne (by decide)),
    swap_apply_left] at h1
  exact π.injective.ne (by decide : (1 : Fin 6) ≠ 0) h1

theorem exists_threeCycle_barAct_eq (v : permBar 6) :
    ∃ c : Perm (Fin 6), c.IsThreeCycle ∧ barAct c v = v := by
  classical
  obtain ⟨I, -, rfl⟩ := exists_supp_of_len v
  have key : ∀ J : Finset (Fin 6), 2 < J.card →
      ∃ c : Perm (Fin 6), c.IsThreeCycle ∧ barAct c (barInd J) = barInd J := by
    intro J hJ
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.1 hJ
    refine ⟨CFSG.CGT.PushingUpLit.BHS.cyc i j k,
      CFSG.CGT.PushingUpLit.BHS.cyc_isThreeCycle hij hik hjk, ?_⟩
    rw [barAct_barInd, (image_eq_iff_mem_setStab _ J).2
      (altOn_le_setStab J (cyc_mem_altOn_of_mem hi hj hk hij hik hjk))]
  by_cases h3 : 2 < I.card
  · exact key I h3
  · have hc : 2 < Iᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨c, hc3, hcv⟩ := key Iᶜ hc
    exact ⟨c, hc3, by rw [← barInd_compl]; exact hcv⟩

theorem exists_pairing_conj (C : Cfg G M X 6) (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    {g : G} (hTM : conjSubgroup g (Rc X) ≤ M) (hcard : 3 ≤ Nat.card ↥(Rc X))
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M = ⊥)
    (hTK : conjSubgroup g (Rc X) ⊓ C.K = ⊥) :
    ∃ π : Perm (Fin 6), ∀ t (ht : t ∈ conjSubgroup g (Rc X)), InP π (C.θ ⟨t, hTM ht⟩) := by
  classical
  set T := conjSubgroup g (Rc X) with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have : Fintype ↥T := Fintype.ofFinite _
  have hthree : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rw [← Fintype.two_lt_card_iff, ← Nat.card_eq_fintype_card, hT, card_conj]
    omega
  set P : Subgroup (Perm (Fin 6)) := (T.subgroupOf M).map C.θ with hP
  have hmemP : ∀ τ ∈ P, ∃ t ∈ T, ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = τ := by
    rintro τ ⟨t, ht, rfl⟩
    exact ⟨t, Subgroup.mem_subgroupOf.1 ht, t.2, rfl⟩
  have h2T : 2 ∣ Nat.card ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 ↥T :=
      (isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G))).map (MulAut.conj g).toMonoidHom
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    have hcT : 3 ≤ Nat.card ↥T := by rw [hT, card_conj]; exact hcard
    rw [hk] at hcT ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hcT
    exact dvd_pow_self 2 hk0
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 h2T
  have ht₀M : (t₀ : G) ∈ M := hTM t₀.2
  set σ := C.θ ⟨t₀, ht₀M⟩ with hσ
  have hσP : σ ∈ P := ⟨⟨t₀, ht₀M⟩, Subgroup.mem_subgroupOf.2 t₀.2, rfl⟩
  have ht₀1 : (t₀ : G) ≠ 1 := by
    intro h
    have : t₀ = 1 := Subtype.ext h
    rw [this, orderOf_one] at ht₀
    exact absurd ht₀ (by norm_num)
  have hσ1 : σ ≠ 1 := fun h => ht₀1 (eq_of_theta_eq C hTM hTK t₀.2 T.one_mem
    (h.trans (map_one C.θ).symm))
  have hσ2 : σ * σ = 1 := by
    have h1 : (t₀ : G) * t₀ = 1 := by
      have := pow_orderOf_eq_one t₀
      rw [ht₀, pow_two] at this
      exact congrArg Subtype.val this
    rw [hσ, ← map_mul]
    have e : (⟨t₀, ht₀M⟩ : ↥M) * ⟨t₀, ht₀M⟩ = 1 := Subtype.ext h1
    rw [e, map_one]
  have hpairs : ∀ τ ∈ P, τ ≠ 1 → ∀ i j : Fin 6, i ≠ j →
      (PresPair τ i j ↔ PresPair σ i j) := by
    intro τ hτ hτ1 i j hij
    obtain ⟨t, htT, htM, rfl⟩ := hmemP τ hτ
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hτ1 (by rw [show (⟨(1 : G), htM⟩ : ↥M) = 1 from rfl, map_one])
    obtain ⟨w, hwW, hw⟩ := exists_pair_witness C (by norm_num) hW hij
    have hwQ : w ∈ Q := C.S.W_le_Q hwW
    rw [← hw ⟨t, htM⟩, ← hw ⟨t₀, ht₀M⟩]
    constructor
    · intro h
      exact (comm_of_comm_conj C.S hTM hTQ htT ht1 hwQ h.symm t₀.2).symm
    · intro h
      exact (comm_of_comm_conj C.S hTM hTQ t₀.2 ht₀1 hwQ h.symm htT).symm
  have h3 : ∃ τ ∈ P, τ ≠ 1 ∧ τ ≠ σ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hthree
    have hval : ∀ x : ↥T, C.θ ⟨x, hTM x.2⟩ = 1 ∨ C.θ ⟨x, hTM x.2⟩ = σ := by
      intro x
      by_cases h1 : C.θ ⟨x, hTM x.2⟩ = 1
      · exact Or.inl h1
      · exact Or.inr (hcon _ ⟨⟨x, hTM x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩ h1)
    have hinj' : ∀ x y : ↥T, C.θ ⟨x, hTM x.2⟩ = C.θ ⟨y, hTM y.2⟩ → x = y := fun x y h =>
      Subtype.ext (eq_of_theta_eq C hTM hTK x.2 y.2 h)
    rcases hval a with ha | ha <;> rcases hval b with hb | hb <;> rcases hval c with hc | hc
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hac (hinj' a c (ha.trans hc.symm))
    · exact hbc (hinj' b c (hb.trans hc.symm))
    · exact hbc (hinj' b c (hb.trans hc.symm))
    · exact hac (hinj' a c (ha.trans hc.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))
  obtain ⟨π, hπ⟩ := exists_pairing_of_presPair hσP hσ1 hσ2 hpairs h3
  exact ⟨π, fun t ht => hπ _ ⟨⟨t, hTM ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩⟩

theorem card_eq_four_of_pairing (C : Cfg G M X 6) {g : G} (hTM : conjSubgroup g (Rc X) ≤ M)
    (hcard : 3 ≤ Nat.card ↥(Rc X)) (hTK : conjSubgroup g (Rc X) ⊓ C.K = ⊥) {π : Perm (Fin 6)}
    (hπ : ∀ t (ht : t ∈ conjSubgroup g (Rc X)), InP π (C.θ ⟨t, hTM ht⟩)) :
    Nat.card ↥(Rc X) = 4 ∧
      (∃ t ∈ conjSubgroup g (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig1 π) ∧
      (∃ t ∈ conjSubgroup g (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig2 π) := by
  classical
  set T := conjSubgroup g (Rc X) with hT
  set P : Subgroup (Perm (Fin 6)) := (T.subgroupOf M).map C.θ with hP
  have hmemP : ∀ τ ∈ P, ∃ t ∈ T, ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = τ := by
    rintro τ ⟨t, ht, rfl⟩
    exact ⟨t, Subgroup.mem_subgroupOf.1 ht, t.2, rfl⟩
  have hPπ : ∀ τ ∈ P, InP π τ := by
    intro τ hτ
    obtain ⟨t, htT, htM, rfl⟩ := hmemP τ hτ
    exact hπ t htT
  have hTP : Nat.card ↥T = Nat.card ↥P := by
    refine Nat.card_congr (Equiv.ofBijective (fun t : ↥T => (⟨C.θ ⟨t, hTM t.2⟩,
      ⟨⟨t, hTM t.2⟩, Subgroup.mem_subgroupOf.2 t.2, rfl⟩⟩ : ↥P)) ⟨fun x y h => ?_, fun τ => ?_⟩)
    · exact Subtype.ext (eq_of_theta_eq C hTM hTK x.2 y.2 (congrArg Subtype.val h))
    · obtain ⟨t, htT, htM, ht⟩ := hmemP τ τ.2
      exact ⟨⟨t, htT⟩, Subtype.ext ht⟩
  have hP4 : Nat.card ↥P ≤ 4 := by
    set s : Finset (Perm (Fin 6)) := {1, sig1 π, sig2 π, sig3 π} with hs
    have hsub : (P : Set (Perm (Fin 6))) ⊆ (s : Set (Perm (Fin 6))) := by
      intro τ hτ
      rcases hPπ τ hτ with h | h | h | h <;> simp [hs, h]
    calc Nat.card ↥P = Nat.card (P : Set (Perm (Fin 6))) := rfl
      _ ≤ Nat.card (s : Set (Perm (Fin 6))) := Nat.card_mono s.finite_toSet hsub
      _ = s.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ 4 := Finset.card_le_four
  have hT4 : Nat.card ↥T = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 ↥T :=
      (isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G))).map (MulAut.conj g).toMonoidHom
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    have hcT : 3 ≤ Nat.card ↥T := by rw [hT, card_conj]; exact hcard
    have hle : Nat.card ↥T ≤ 4 := hTP ▸ hP4
    rw [hk] at hcT hle ⊢
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> norm_num at hcT
      · rcases Nat.lt_or_ge k 3 with h' | h'
        · omega
        · have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h'
          omega
    rw [hk2]
    norm_num
  obtain ⟨h1, h2, -⟩ := inP_iff_of_card hPπ (by rw [← hTP]; omega)
  exact ⟨(card_conj (X := X) g).symm.trans hT4, hmemP _ h1, hmemP _ h2⟩

theorem inv_conj_inf_K {C : Cfg G M X 6} (D : C.PiData)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hR4 : Nat.card ↥(Rc X) = 4) {g : G} (hgM : g ∉ M) {π : Perm (Fin 6)}
    (ht₁ : ∃ t ∈ conjSubgroup g (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig1 π) :
    conjSubgroup g⁻¹ (Rc X) ⊓ C.K = ⊥ := by
  classical
  set R := Rc X with hRdef
  have hR : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hR4
    omega
  have hgM' : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hne' : conjSubgroup g⁻¹ R ≠ R := conj_ne_of_not_mem C.S hR hgM'
  have hRC : ∀ s ∈ R, s ∈ Subgroup.centralizer (X : Set G) := fun s hs => by
    rw [hRdef, C.S.R_eq_inf] at hs
    exact (Subgroup.mem_inf.1 hs).2
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨huT', huK⟩ := Subgroup.mem_inf.1 hu
  have hr : g * u * g⁻¹ ∈ R := by simpa using mem_conjSubgroup.1 huT'
  set r := g * u * g⁻¹ with hrdef
  have hur : u = g⁻¹ * r * g := by rw [hrdef]; group
  by_contra hu1
  have hr1 : r ≠ 1 := by
    intro h
    apply hu1
    rw [hur, h]
    group
  have hv : Multiplicative.toAdd (D.π ⟨u, huK⟩) ≠ 0 := by
    intro hv0
    have hπ1 : D.π ⟨u, huK⟩ = 1 := Multiplicative.toAdd.injective hv0
    have huC : u ∈ Subgroup.centralizer (X : Set G) := (D.ker _).1 hπ1
    obtain ⟨j, hj⟩ := two_pow_of_mem_conj huT'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
    have h2 : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have huR := hRsyl _ h2 (Subgroup.zpowers_le.2 huC) (Subgroup.mem_zpowers u)
    have h5 : u ∈ R ⊓ conjSubgroup g⁻¹ R := ⟨huR, huT'⟩
    rw [inf_conj_eq_bot C.S hne', Subgroup.mem_bot] at h5
    exact hu1 h5
  obtain ⟨c, hc3, hcv⟩ := exists_threeCycle_barAct_eq (Multiplicative.toAdd (D.π ⟨u, huK⟩))
  obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc3
  have hxu : (x : G) * u = u * x :=
    comm_of_pow_three D (k := ⟨u, huK⟩) hx3 (by rw [hxc]; exact hcv)
  set x' := g * (x : G) * g⁻¹ with hx'
  have hx'r : x' * r = r * x' := by
    rw [hx', hrdef]
    calc g * (x : G) * g⁻¹ * (g * u * g⁻¹) = g * ((x : G) * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  have hx'M : x' ∈ M :=
    C.S.centralizer_le_of_mem_R hr hr1 (Subgroup.mem_centralizer_singleton_iff.2 hx'r)
  have hx'T : ∀ t ∈ conjSubgroup g R, x' * t = t * x' := by
    intro t ht
    have h1 : g⁻¹ * t * g ∈ R := mem_conjSubgroup.1 ht
    have h2 : (g⁻¹ * t * g) * x = x * (g⁻¹ * t * g) :=
      (Subgroup.mem_centralizer_iff.1 (hRC _ h1) x x.2).symm
    calc x' * t = g * ((x : G) * (g⁻¹ * t * g)) * g⁻¹ := by rw [hx']; group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h2]
      _ = t * x' := by rw [hx']; group
  obtain ⟨t₁, ht₁T, ht₁M, hθt₁⟩ := ht₁
  have hc : C.θ ⟨x', hx'M⟩ * sig1 π = sig1 π * C.θ ⟨x', hx'M⟩ := by
    rw [← hθt₁, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx'T t₁ ht₁T)
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', conj_pow, hx3]
    group
  have hx'C := mem_centralizer_of_odd_of_commute D hx'M (by decide) hx'3 π hc
  have hx'n : ∀ s ∈ R, x' * s * x'⁻¹ ∈ R := fun s hs =>
    R_normalized C.S (C.S.centralizer_le hx'C) hs
  have hx'R := comm_of_pow_three_of_fixes hR4 hx'n hx'3 hr hr1 hx'r
  have hx'1 : x' = 1 := eq_one_of_odd_of_comm_R C.S hx'C hx'R (by decide) hx'3
  have hx1 : (x : G) = 1 := by
    have : (x : G) = g⁻¹ * x' * g := by rw [hx']; group
    rw [this, hx'1]
    group
  have hc1 : c = 1 := by
    rw [← hxc]
    have : x = 1 := Subtype.ext hx1
    rw [this, map_one]
    rfl
  have h3 := hc3.orderOf
  rw [hc1, orderOf_one] at h3
  norm_num at h3

theorem conj_mem_centralizer {C : Cfg G M X 6} (D : C.PiData) (hR : Rc X ≠ ⊥) {g : G}
    {π' : Perm (Fin 6)}
    (ht₁ : ∃ t ∈ conjSubgroup g⁻¹ (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig1 π') {z : G}
    (hzX : z ∈ X) (hzN : z ∈ Subgroup.normalizer ((conjSubgroup g (Rc X) : Subgroup G) : Set G))
    (hz3 : z ^ 3 = 1) : g⁻¹ * z * g ∈ Subgroup.centralizer (X : Set G) := by
  set R := Rc X with hRdef
  set z' := g⁻¹ * z * g with hz'
  have hRC : ∀ s ∈ R, s ∈ Subgroup.centralizer (X : Set G) := fun s hs => by
    rw [hRdef, C.S.R_eq_inf] at hs
    exact (Subgroup.mem_inf.1 hs).2
  have hz'M : z' ∈ M := by
    rw [← C.S.normalizer_R hR, Subgroup.mem_normalizer_iff]
    intro s
    have h := Subgroup.mem_normalizer_iff.1 hzN (g * s * g⁻¹)
    have e1 : g * s * g⁻¹ ∈ conjSubgroup g R ↔ s ∈ R := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * s * g⁻¹) * g = s by group]
    have e2 : z * (g * s * g⁻¹) * z⁻¹ ∈ conjSubgroup g R ↔ z' * s * z'⁻¹ ∈ R := by
      rw [mem_conjSubgroup, show g⁻¹ * (z * (g * s * g⁻¹) * z⁻¹) * g = z' * s * z'⁻¹ by
        rw [hz']; group]
    rw [e1, e2] at h
    exact h
  obtain ⟨t₁, ht₁T, ht₁M, hθt₁⟩ := ht₁
  have hz't : z' * t₁ = t₁ * z' := by
    have h1 : g * t₁ * g⁻¹ ∈ R := by simpa using mem_conjSubgroup.1 ht₁T
    have h2 : (g * t₁ * g⁻¹) * z = z * (g * t₁ * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 (hRC _ h1) z hzX).symm
    calc z' * t₁ = g⁻¹ * (z * (g * t₁ * g⁻¹)) * g := by rw [hz']; group
      _ = g⁻¹ * ((g * t₁ * g⁻¹) * z) * g := by rw [h2]
      _ = t₁ * z' := by rw [hz']; group
  have hc : C.θ ⟨z', hz'M⟩ * sig1 π' = sig1 π' * C.θ ⟨z', hz'M⟩ := by
    rw [← hθt₁, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hz't
  have hz'3 : z' ^ 3 = 1 := by
    rw [hz', inv_conj_pow, hz3]
    group
  exact mem_centralizer_of_odd_of_commute D hz'M (by decide) hz'3 π' hc

theorem false_of_residual {C : Cfg G M X 6} (D : C.PiData)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hR : Rc X ≠ ⊥) {g : G} (hTM : conjSubgroup g (Rc X) ≤ M) {π : Perm (Fin 6)}
    (hπ : ∀ t (ht : t ∈ conjSubgroup g (Rc X)), InP π (C.θ ⟨t, hTM ht⟩))
    (hs1 : ∃ t ∈ conjSubgroup g (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig1 π)
    (hs2 : ∃ t ∈ conjSubgroup g (Rc X), ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = sig2 π)
    (hTM' : conjSubgroup g⁻¹ (Rc X) ≤ M) (hTK' : conjSubgroup g⁻¹ (Rc X) ⊓ C.K = ⊥)
    {π' : Perm (Fin 6)}
    (hπ' : ∀ t (ht : t ∈ conjSubgroup g⁻¹ (Rc X)), InP π' (C.θ ⟨t, hTM' ht⟩))
    {z : G} (hzX : z ∈ X)
    (hzN : z ∈ Subgroup.normalizer ((conjSubgroup g (Rc X) : Subgroup G) : Set G))
    (hz3 : z ^ 3 = 1) (hzθ : C.θ ⟨z, C.S.le hzX⟩ ≠ 1)
    (hz' : g⁻¹ * z * g ∈ Subgroup.centralizer (X : Set G)) : False := by
  classical
  set R := Rc X with hRdef
  set T := conjSubgroup g R with hT
  set T' := conjSubgroup g⁻¹ R with hT'
  have hRC : ∀ s ∈ R, s ∈ Subgroup.centralizer (X : Set G) := fun s hs => by
    rw [hRdef, C.S.R_eq_inf] at hs
    exact (Subgroup.mem_inf.1 hs).2
  have hmemT' : ∀ x : G, x ∈ T' ↔ g * x * g⁻¹ ∈ R := fun x => by
    rw [hT', mem_conjSubgroup]
    simp
  have hpres : ∀ {i j : Fin 6}, i ≠ j → (∀ σ, InP π' σ → PresPair σ i j) →
      ∃ w ∈ blockU X, (∀ t ∈ T', t * w = w * t) ∧
        ∀ m : ↥M, ((m : G) * w = w * m ↔ PresPair (C.θ m) i j) := by
    intro i j hij hP
    obtain ⟨w, hwW, hw⟩ := exists_pair_witness C (by norm_num) hW hij
    exact ⟨w, hwW, fun t ht => (hw ⟨t, hTM' ht⟩).2 (hP _ (hπ' t ht)), hw⟩
  have h01 : π' 0 ≠ π' 1 := π'.injective.ne (by decide)
  have h23 : π' 2 ≠ π' 3 := π'.injective.ne (by decide)
  obtain ⟨w₁, hw₁W, hw₁T, hw₁⟩ := hpres h01 fun σ h => (presPair_of_inP h).1
  obtain ⟨w₂, hw₂W, hw₂T, hw₂⟩ := hpres h23 fun σ h => (presPair_of_inP h).2
  have hlift : ∀ c : Perm (Fin 6), c ∈ alternatingGroup (Fin 6) → ∃ m : ↥M, C.θ m = c := by
    intro c hc
    obtain ⟨x, hx⟩ := C.exists_lift hc
    exact ⟨_, hx⟩
  have hne3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      ∃ m : ↥M, C.θ m = CFSG.CGT.PushingUpLit.BHS.cyc a b c := fun a b c hab hac hbc =>
    hlift _ (CFSG.CGT.PushingUpLit.BHS.cyc_isThreeCycle hab hac hbc).mem_alternatingGroup
  have hπ'ne : ∀ i j : Fin 6, i ≠ j → π' i ≠ π' j := fun i j h => π'.injective.ne h
  have hw₁1 : w₁ ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := hne3 (π' 0) (π' 2) (π' 3) (hπ'ne 0 2 (by decide)) (hπ'ne 0 3 (by decide))
      (hπ'ne 2 3 (by decide))
    have hp := (hw₁ m).1 (by rw [h]; group)
    rw [hm] at hp
    rcases hp with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 0 3 (by decide))
        (hπ'ne 2 3 (by decide))] at h1
      exact hπ'ne 3 0 (by decide) h1
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 0 3 (by decide))
        (hπ'ne 2 3 (by decide))] at h1
      exact hπ'ne 3 1 (by decide) h1
  have hw₂1 : w₂ ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := hne3 (π' 2) (π' 0) (π' 1) (hπ'ne 2 0 (by decide)) (hπ'ne 2 1 (by decide))
      (hπ'ne 0 1 (by decide))
    have hp := (hw₂ m).1 (by rw [h]; group)
    rw [hm] at hp
    rcases hp with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 2 1 (by decide))
        (hπ'ne 0 1 (by decide))] at h1
      exact hπ'ne 1 2 (by decide) h1
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 2 1 (by decide))
        (hπ'ne 0 1 (by decide))] at h1
      exact hπ'ne 1 3 (by decide) h1
  have hw₁₂ : w₁ ≠ w₂ := by
    intro h
    obtain ⟨m, hm⟩ := hne3 (π' 2) (π' 4) (π' 5) (hπ'ne 2 4 (by decide)) (hπ'ne 2 5 (by decide))
      (hπ'ne 4 5 (by decide))
    have hp1 : PresPair (C.θ m) (π' 0) (π' 1) := by
      rw [hm]
      left
      exact ⟨CFSG.CGT.PushingUpLit.BHS.cyc_apply_of_ne (hπ'ne 0 2 (by decide))
          (hπ'ne 0 4 (by decide)) (hπ'ne 0 5 (by decide)),
        CFSG.CGT.PushingUpLit.BHS.cyc_apply_of_ne (hπ'ne 1 2 (by decide))
          (hπ'ne 1 4 (by decide)) (hπ'ne 1 5 (by decide))⟩
    have hp2 := (hw₂ m).1 (h ▸ (hw₁ m).2 hp1)
    rw [hm] at hp2
    rcases hp2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 2 5 (by decide))
        (hπ'ne 4 5 (by decide))] at h1
      exact hπ'ne 5 2 (by decide) h1
    · rw [CFSG.CGT.PushingUpLit.BHS.cyc_apply_first (hπ'ne 2 5 (by decide))
        (hπ'ne 4 5 (by decide))] at h1
      exact hπ'ne 5 3 (by decide) h1
  set F' : Subgroup G := blockU X ⊓ Subgroup.centralizer (T' : Set G) with hF'
  have hw₁F : w₁ ∈ F' := Subgroup.mem_inf.2 ⟨hw₁W, Subgroup.mem_centralizer_iff.2 hw₁T⟩
  have hw₂F : w₂ ∈ F' := Subgroup.mem_inf.2 ⟨hw₂W, Subgroup.mem_centralizer_iff.2 hw₂T⟩
  have hF'3 : 3 ≤ Nat.card ↥F' := by
    have hsub : ((({1, w₁, w₂} : Finset G) : Set G)) ⊆ (F' : Set G) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact F'.one_mem
      · exact hw₁F
      · exact hw₂F
    have hc : ({1, w₁, w₂} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hw₁₂]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hw₁1, Ne.symm hw₂1⟩
    calc 3 = ({1, w₁, w₂} : Finset G).card := hc.symm
      _ = Nat.card ((({1, w₁, w₂} : Finset G) : Set G)) := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ Nat.card (F' : Set G) := Nat.card_mono (Set.toFinite _) hsub
      _ = Nat.card ↥F' := rfl
  set F : Subgroup G := conjSubgroup g F' with hF
  have hFcard : Nat.card ↥F = Nat.card ↥F' :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hmemF : ∀ f ∈ F, g⁻¹ * f * g ∈ blockU X ∧ ∀ t ∈ T', t * (g⁻¹ * f * g) = g⁻¹ * f * g * t :=
    fun f hf => by
      obtain ⟨hW', hC'⟩ := Subgroup.mem_inf.1 (mem_conjSubgroup.1 hf)
      exact ⟨hW', fun t ht => Subgroup.mem_centralizer_iff.1 hC' t ht⟩
  have hFX : ∀ f ∈ F, g⁻¹ * f * g ∈ X := fun f hf =>
    blockU_le_self X (hmemF f hf).1
  have hFR : ∀ f ∈ F, ∀ s ∈ R, f * s = s * f := by
    intro f hf s hs
    have h1 : g⁻¹ * s * g ∈ T' := by
      rw [hmemT', show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
      exact hs
    have h2 := (hmemF f hf).2 _ h1
    calc f * s = g * ((g⁻¹ * f * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = s * f := by group
  have hFM : F ≤ M := fun f hf => by
    rw [← C.S.normalizer_R hR]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun s hs => (hFR f hf s hs).symm)
  have hFT : ∀ f ∈ F, ∀ t ∈ T, f * t = t * f := by
    intro f hf t ht
    have h1 : g⁻¹ * t * g ∈ R := mem_conjSubgroup.1 ht
    have h2 : (g⁻¹ * t * g) * (g⁻¹ * f * g) = (g⁻¹ * f * g) * (g⁻¹ * t * g) :=
      (Subgroup.mem_centralizer_iff.1 (hRC _ h1) _ (hFX f hf)).symm
    calc f * t = g * ((g⁻¹ * f * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = t * f := by group
  have hFz : ∀ f ∈ F, f * z = z * f := by
    intro f hf
    have h2 : (g⁻¹ * f * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * f * g) :=
      Subgroup.mem_centralizer_iff.1 hz' _ (hFX f hf)
    calc f * z = g * ((g⁻¹ * f * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = z * f := by group
  obtain ⟨t₁, ht₁T, ht₁M, hθt₁⟩ := hs1
  obtain ⟨t₂, ht₂T, ht₂M, hθt₂⟩ := hs2
  set τ := C.θ ⟨z, C.S.le hzX⟩ with hτ
  have hzM : z ∈ M := C.S.le hzX
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have e : (⟨z, hzM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [e, map_one]
  have hτn : ∀ t (ht : t ∈ T) (ht' : t ∈ M), InP π (τ * C.θ ⟨t, ht'⟩ * τ⁻¹) := by
    intro t ht ht'
    have h1 : z * t * z⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hzN t).1 ht
    have e : τ * C.θ ⟨t, ht'⟩ * τ⁻¹ = C.θ ⟨z * t * z⁻¹, hTM h1⟩ := by
      rw [hτ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hπ _ h1
  have h1 : InP π (τ * sig1 π * τ⁻¹) := hθt₁ ▸ hτn t₁ ht₁T ht₁M
  have h2 : InP π (τ * sig2 π * τ⁻¹) := hθt₂ ▸ hτn t₂ ht₂T ht₂M
  set H : Subgroup (Perm (Fin 6)) := (F.subgroupOf M).map C.θ with hH
  have hHc : ∀ ρ ∈ H, ρ * sig1 π = sig1 π * ρ ∧ ρ * sig2 π = sig2 π * ρ ∧ ρ * τ = τ * ρ := by
    rintro ρ ⟨f, hf, rfl⟩
    have hf' : (f : G) ∈ F := Subgroup.mem_subgroupOf.1 hf
    refine ⟨?_, ?_, ?_⟩
    · rw [← hθt₁, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFT _ hf' _ ht₁T)
    · rw [← hθt₂, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFT _ hf' _ ht₂T)
    · rw [hτ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFz _ hf')
  have hH2 := card_le_two_of_commute π hτ3 hzθ h1 h2 hHc
  have hFK : ∀ f ∈ F, f ∈ C.K → f = 1 := by
    intro f hf hfK
    have hfix : ∀ t ∈ T, ∀ ht : t ∈ M, barAct (C.θ ⟨t, ht⟩)
        (Multiplicative.toAdd (D.π ⟨f, hfK⟩)) = Multiplicative.toAdd (D.π ⟨f, hfK⟩) := by
      intro t ht htM
      have := D.equivar ⟨t, htM⟩ ⟨f, hfK⟩ ⟨f, hfK⟩ (by
        show f = t * f * t⁻¹
        rw [← hFT f hf t ht]
        group)
      exact this.symm
    have hfz : barAct τ (Multiplicative.toAdd (D.π ⟨f, hfK⟩)) =
        Multiplicative.toAdd (D.π ⟨f, hfK⟩) := by
      have := D.equivar ⟨z, hzM⟩ ⟨f, hfK⟩ ⟨f, hfK⟩ (by
        show f = z * f * z⁻¹
        rw [← hFz f hf]
        group)
      exact this.symm
    have hv0 := eq_zero_of_fixed π hτ3 hzθ h1 h2 (hθt₁ ▸ hfix t₁ ht₁T ht₁M)
      (hθt₂ ▸ hfix t₂ ht₂T ht₂M) hfz
    have hπ1 : D.π ⟨f, hfK⟩ = 1 := Multiplicative.toAdd.injective hv0
    have hfC : f ∈ Subgroup.centralizer (X : Set G) := (D.ker _).1 hπ1
    have hf2 : f * f = 1 := by
      have h1 : (g⁻¹ * f * g) * (g⁻¹ * f * g) = 1 := by
        have := C.S.elemU.2 _ (hmemF f hf).1
        rwa [pow_two] at this
      calc f * f = g * ((g⁻¹ * f * g) * (g⁻¹ * f * g)) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h2f : IsPGroup 2 (Subgroup.zpowers f) := by
      have hd : orderOf f ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hf2)
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hfR : f ∈ R := hRsyl _ h2f (Subgroup.zpowers_le.2 hfC) (Subgroup.mem_zpowers f)
    have hf'T : g⁻¹ * f * g ∈ T' := by
      rw [hmemT', show g * (g⁻¹ * f * g) * g⁻¹ = f by group]
      exact hfR
    have hf'K : g⁻¹ * f * g ∈ C.K := RSmall.Q_le_K C (C.S.W_le_Q (hmemF f hf).1)
    have h5 : g⁻¹ * f * g ∈ T' ⊓ C.K := ⟨hf'T, hf'K⟩
    rw [hTK', Subgroup.mem_bot] at h5
    calc f = g * (g⁻¹ * f * g) * g⁻¹ := by group
      _ = 1 := by rw [h5]; group
  have hinj : Function.Injective (fun f : ↥F => (⟨C.θ ⟨f, hFM f.2⟩,
      ⟨⟨f, hFM f.2⟩, Subgroup.mem_subgroupOf.2 f.2, rfl⟩⟩ : ↥H)) := by
    intro a b hab
    have hθ : C.θ ⟨a, hFM a.2⟩ = C.θ ⟨b, hFM b.2⟩ := congrArg Subtype.val hab
    have hK : (a : G) * (b : G)⁻¹ ∈ C.K := by
      rw [C.mem_K]
      refine ⟨M.mul_mem (hFM a.2) (M.inv_mem (hFM b.2)), ?_⟩
      have e : (⟨(a : G) * (b : G)⁻¹, M.mul_mem (hFM a.2) (M.inv_mem (hFM b.2))⟩ : ↥M) =
          ⟨a, hFM a.2⟩ * (⟨b, hFM b.2⟩ : ↥M)⁻¹ := rfl
      rw [e, map_mul, map_inv, hθ, mul_inv_cancel]
    have h1 := hFK _ (F.mul_mem a.2 (F.inv_mem b.2)) hK
    exact Subtype.ext (by
      calc (a : G) = (a : G) * (b : G)⁻¹ * b := by group
        _ = b := by rw [h1, one_mul])
  have hle := Nat.card_le_card_of_injective _ hinj
  omega

omit [Finite G] in
private theorem exists_two_ne_one {T : Subgroup G} (hT : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ τ₁ ∈ T, ∃ τ₂ ∈ T, τ₁ ≠ 1 ∧ τ₂ ≠ 1 ∧ τ₁ ≠ τ₂ := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hT
  by_cases ha : (a : G) = 1
  · refine ⟨b, b.2, c, c.2, fun h => hab (Subtype.ext (ha.trans h.symm)),
      fun h => hac (Subtype.ext (ha.trans h.symm)), fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : (b : G) = 1
    · exact ⟨a, a.2, c, c.2, ha, fun h => hbc (Subtype.ext (hb.trans h.symm)),
        fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩

theorem false_of_caseI_inf_K (C : Cfg G M X 6) (D : C.PiData)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    {g : G} (hTM : conjSubgroup g (Rc X) ≤ M) (hne : conjSubgroup g (Rc X) ≠ Rc X)
    (hcard : 3 ≤ Nat.card ↥(Rc X))
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M = ⊥)
    (hK : ∃ t ∈ conjSubgroup g (Rc X), t ∈ C.K ∧ t ≠ 1) : False := by
  classical
  set T := conjSubgroup g (Rc X) with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have : Fintype ↥T := Fintype.ofFinite _
  have hthree : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rw [← Fintype.two_lt_card_iff, ← Nat.card_eq_fintype_card, hT, card_conj]
    omega
  have hTC : ∀ τ ∈ T, τ ∈ Subgroup.centralizer (X : Set G) → τ = 1 := by
    intro τ hτ hτC
    obtain ⟨j, hj⟩ := two_pow_of_mem_conj hτ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
    have h2 : IsPGroup 2 (Subgroup.zpowers τ) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hR' := hRsyl _ h2 (Subgroup.zpowers_le.2 hτC)
    have h5 : τ ∈ Rc X ⊓ T := ⟨hR' (Subgroup.mem_zpowers τ), hτ⟩
    rw [inf_conj_eq_bot C.S hne, Subgroup.mem_bot] at h5
    exact h5
  obtain ⟨t, htT, htK, ht1⟩ := hK
  have hTK : ∀ τ ∈ T, τ ∈ C.K := by
    intro τ hτ
    have hτM := hTM hτ
    rw [C.mem_K]
    refine ⟨hτM, (C.theta_eq_one_iff C.S.five_le_degree ⟨τ, hτM⟩).2 fun u v hv => ?_⟩
    have hut : (u : G) * t = t * u := (K_comm_W C htK u.2).symm
    have hτu := comm_of_comm_conj C.S hTM hTQ htT ht1 (C.S.W_le_Q u.2) hut hτ
    have hvu : v = u := Subtype.ext (by
      rw [hv]
      show τ * (u : G) * τ⁻¹ = u
      rw [← hτu]
      group)
    rw [hvu]
  have hnot : ∀ τ (hτ : τ ∈ T), τ ≠ 1 →
      Multiplicative.toAdd (D.π ⟨τ, hTK τ hτ⟩) ∉ Set.range (heartToBar (n := 6)) := by
    rintro τ hτ hτ1 ⟨u, hu⟩
    obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
    have hwQ : (w : G) ∈ Q := C.S.W_le_Q w.2
    have hπw : D.π ⟨τ, hTK τ hτ⟩ = D.π ⟨w, RSmall.Q_le_K C hwQ⟩ := by
      apply Multiplicative.toAdd.injective
      rw [D.π_W ⟨w, RSmall.Q_le_K C hwQ⟩ w rfl, hw, toAdd_ofAdd, hu]
    have hτQ := mem_Q_of_pi_eq D hRsyl (k := ⟨τ, hTK τ hτ⟩) (two_pow_of_mem_conj hτ) hwQ hπw
    have h5 : τ ∈ T ⊓ Q := ⟨hτ, hτQ⟩
    rw [hTQ, Subgroup.mem_bot] at h5
    exact hτ1 h5
  have hsq : ∀ τ ∈ T, τ * τ = 1 := by
    intro τ hτ
    apply hTC _ (T.mul_mem hτ hτ)
    have h0 : D.π (⟨τ, hTK τ hτ⟩ * ⟨τ, hTK τ hτ⟩) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one, permBar_add_self]
    exact (D.ker _).1 h0
  obtain ⟨τ₁, h₁, τ₂, h₂, h₁1, h₂1, h₁₂⟩ := exists_two_ne_one hthree
  have h12 : τ₁ * τ₂ ≠ 1 := by
    intro h
    apply h₁₂
    calc τ₁ = τ₁ * (τ₂ * τ₂) := by rw [hsq τ₂ h₂, mul_one]
      _ = (τ₁ * τ₂) * τ₂ := by group
      _ = τ₂ := by rw [h, one_mul]
  apply hnot _ (T.mul_mem h₁ h₂) h12
  have e : D.π ⟨τ₁ * τ₂, hTK _ (T.mul_mem h₁ h₂)⟩ =
      D.π ⟨τ₁, hTK τ₁ h₁⟩ * D.π ⟨τ₂, hTK τ₂ h₂⟩ := by
    rw [← map_mul]
    rfl
  rw [e, toAdd_mul]
  exact add_mem_range_heartToBar (hnot τ₁ h₁ h₁1) (hnot τ₂ h₂ h₂1)

theorem false_of_caseI_six (C : Cfg G M X 6) (D : C.PiData)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r) (hL3 : Lemma3Lift)
    {g : G} (hTM : conjSubgroup g (Rc X) ≤ M) (hne : conjSubgroup g (Rc X) ≠ Rc X)
    (hcard : 3 ≤ Nat.card ↥(Rc X))
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M = ⊥) : False := by
  classical
  set R := Rc X with hRdef
  set T := conjSubgroup g R with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  by_cases hK : ∃ t ∈ T, t ∈ C.K ∧ t ≠ 1
  · exact false_of_caseI_inf_K C D hRsyl hTM hne hcard hTQ hK
  have hTK : T ⊓ C.K = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    by_contra h1
    exact hK ⟨t, (Subgroup.mem_inf.1 ht).1, (Subgroup.mem_inf.1 ht).2, h1⟩
  have hR : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hgM : g ∉ M := fun hg => hne
    (Setting.map_conj_eq_of_normalized (fun x hx => R_normalized C.S hg hx)
      (fun x hx => R_normalized C.S (M.inv_mem hg) hx))
  obtain ⟨π, hπ⟩ := exists_pairing_conj C hW hTM hcard hTQ hTK
  obtain ⟨hR4, hs1, hs2⟩ := card_eq_four_of_pairing C hTM hcard hTK hπ
  have hRQ : ∀ r ∈ R, r ∈ Q := fun r hr => by
    rw [hRdef, C.S.R_eq_inf] at hr
    exact (Subgroup.mem_inf.1 hr).1
  obtain ⟨t₁, ht₁T, ht₁M, hθt₁⟩ := hs1
  have ht₁1 : t₁ ≠ 1 := by
    rintro rfl
    have : sig1 π = 1 := by
      rw [← hθt₁]
      exact map_one C.θ
    exact sig1_ne_one π this
  have hTM' : conjSubgroup g⁻¹ R ≤ M := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ R := by simpa using mem_conjSubgroup.1 hx
    have h2 : (g * x * g⁻¹) * t₁ = t₁ * (g * x * g⁻¹) :=
      comm_R_conj C.S hR hTM hne h1 ht₁T
    have h3 := conj_mem_of_comm C.S ht₁T ht₁1 h2
    simpa [mul_assoc] using h3
  have hgM' : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hne' : conjSubgroup g⁻¹ R ≠ R := conj_ne_of_not_mem C.S hR hgM'
  have hTK' : conjSubgroup g⁻¹ R ⊓ C.K = ⊥ :=
    inv_conj_inf_K D hRsyl hR4 hgM ⟨t₁, ht₁T, ht₁M, hθt₁⟩
  have hTQ' : conjSubgroup g⁻¹ R ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← hTK']
    exact ⟨(Subgroup.mem_inf.1 hx).1, RSmall.Q_le_K C (Subgroup.mem_inf.1 hx).2⟩
  obtain ⟨π', hπ'⟩ := exists_pairing_conj C hW hTM' hcard hTQ' hTK'
  obtain ⟨-, hs1', -⟩ := card_eq_four_of_pairing C hTM' hcard hTK' hπ'
  obtain ⟨z, hzN, hz3, hzθ⟩ := hL3 G M X C D hRsyl hRab hR4 g hTM hne hTK π hπ
  have hz' := conj_mem_centralizer D hR hs1' z.2 hzN hz3
  exact false_of_residual D hW hRsyl hR hTM hπ ⟨t₁, ht₁T, ht₁M, hθt₁⟩ hs2 hTM' hTK' hπ' z.2 hzN
    hz3 hzθ hz'

theorem false_of_three_le_six (C : Cfg G M X 6) (D : C.PiData)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r) (hL3 : Lemma3Lift) (hII : CaseIISix)
    {g : G} (hgM : g ∉ M) (hTM : conjSubgroup g (Rc X) ≤ M) (hcard : 3 ≤ Nat.card ↥(Rc X)) :
    False := by
  have hR : Rc X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  refine hII G M X C D hW hRsyl hRab hcard (fun g' hg'M hT'M hT'Q => ?_) g hgM hTM
  exact false_of_caseI_six C D hW hRsyl hRab hL3 hT'M (conj_ne_of_not_mem C.S hR hg'M) hcard hT'Q

theorem card_Rc_le_two_six_of_tight (C : Cfg G M X 6) (D : C.PiData) (hL3 : Lemma3Lift)
    (hII : CaseIISix)
    (htight : Subgroup.centralizer (X : Set G) = ⊥ ∨
      (Rc X ≠ ⊥ ∧
        (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X) ∧
        ((IsCyclic ↥(Rc X) ∧ Nat.card ↥(Rc X) = 4) ∨ CFSG.Open.IsElemAbelian 2 (Rc X)) ∧
        ∃ g : G, conjSubgroup g (Rc X) ≤ M ∧ conjSubgroup g (Rc X) ≠ Rc X)) :
    Nat.card ↥(Rc X) ≤ 2 := by
  rcases htight with hC | ⟨-, hRsyl, hab, g, hTM, hne⟩
  · have hR : Rc X = ⊥ := by
      apply le_bot_iff.1
      rw [← hC]
      exact CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self _
    rw [hR, Subgroup.card_bot]
    omega
  · by_contra hcard
    push Not at hcard
    have hW : Nonempty C.UIso ∨ Function.Injective C.β := by
      have h2 := C.card_blockZ_le_two
      have h1 : 0 < Nat.card ↥(blockZ X) := Nat.card_pos
      rcases (show Nat.card ↥(blockZ X) = 1 ∨ Nat.card ↥(blockZ X) = 2 by omega) with h | h
      · exact Or.inr (C.beta_injective_of_card h)
      · exact Or.inl (C.nonempty_uIso h)
    have hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r := by
      intro r hr r' hr'
      rcases hab with ⟨hcyc, -⟩ | hel
      · exact congrArg Subtype.val
          ((IsCyclic.isMulCommutative (α := ↥(Rc X))).is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
      · exact congrArg Subtype.val (hel.1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
    have hgM : g ∉ M := by
      intro hg
      apply hne
      exact Setting.map_conj_eq_of_normalized (fun x hx => R_normalized C.S hg hx)
        (fun x hx => R_normalized C.S (M.inv_mem hg) hx)
    exact false_of_three_le_six C D hW hRsyl hRab hL3 hII hgM hTM (by omega)

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
