module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallII
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallLen
public import CFSG.CGT.PushingUpLit.SolK.CaseII

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

local instance instPermBarAddCommGroupΩ (n : ℕ) : AddCommGroup (permBar n) :=
  { (inferInstance : AddGroup (permBar n)) with
    add_comm := fun x y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm] }

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem barPt_not_mem_range (hn : Even n) (a : Fin n) :
    barPt a ∉ Set.range (heartToBar (n := n)) := by
  rintro ⟨u, hu⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [heartToBar_mk, QuotientAddGroup.eq] at hu
  have hx : ∑ i, (x : Fin n → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight, AddMonoidHom.mem_ker] using this
  have hsum : ∑ i, (-(x : Fin n → ZMod 2) + (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2)) i =
      1 := by
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, hx,
      neg_zero, zero_add, Finset.sum_pi_single', Finset.mem_univ, if_true]
  rcases (mem_zmultiples_allOnes_iff _).1 hu with h0 | h1
  · rw [h0] at hsum
    simp at hsum
  · rw [h1] at hsum
    simp only [allOnes, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hsum
    obtain ⟨k, hk⟩ := hn
    rw [hk] at hsum
    have : ((k + k : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_add, ← two_mul]
      exact mul_eq_zero_of_left (by decide) _
    rw [this] at hsum
    exact absurd hsum (by decide)

theorem presPair_of_conj_swap {σ : Perm (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (h : σ * swap a b * σ⁻¹ = swap a b) : PresPair σ a b := by
  rw [← swap_apply_apply] at h
  have h1 := congrArg (fun f : Perm (Fin n) => f (σ a)) h
  simp only [swap_apply_left] at h1
  unfold PresPair
  by_cases ha : σ a = a
  · left
    refine ⟨ha, ?_⟩
    rw [ha, swap_apply_left] at h1
    exact h1
  · by_cases hb' : σ a = b
    · right
      refine ⟨hb', ?_⟩
      rw [hb', swap_apply_right] at h1
      exact h1
    · rw [swap_apply_of_ne_of_ne ha hb'] at h1
      exact absurd (σ.injective h1.symm) hab

theorem K_normalized (C : Cfg G M X n) {m k : G} (hm : m ∈ M) (hk : k ∈ C.K) :
    m * k * m⁻¹ ∈ C.K := by
  obtain ⟨hkM, hθ⟩ := C.mem_K.1 hk
  refine C.mem_K.2 ⟨M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm), ?_⟩
  have e : (⟨m * k * m⁻¹, M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm)⟩ : ↥M) =
      ⟨m, hm⟩ * ⟨k, hkM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hθ, mul_one, mul_inv_cancel]

theorem C_le_K (C : Cfg G M X n) {c : G} (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    c ∈ C.K := by
  have hcM : c ∈ M := C.S.centralizer_le hc
  refine C.mem_K.2 ⟨hcM, (C.theta_eq_one_iff C.S.five_le_degree ⟨c, hcM⟩).2 fun u v hv => ?_⟩
  have hcu : c * (u : G) = u * c :=
    (Subgroup.mem_centralizer_iff.1 hc u (blockU_le_self X u.2)).symm
  have : v = u := Subtype.ext (by
    rw [hv]
    show c * (u : G) * c⁻¹ = u
    rw [hcu]
    group)
  rw [this]

theorem eq_one_of_odd_of_two_pow {H : Type*} [Group H] {r : H} {m j : ℕ} (hm : Odd m)
    (h1 : r ^ m = 1) (h2 : r ^ (2 ^ j) = 1) : r = 1 := by
  have h := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [((Nat.coprime_two_right.2 hm).pow_right j).gcd_eq_one, pow_one] at h

theorem pi_commutator_eq_one {C : Cfg G M X n} (D : C.PiData) (y q : ↥C.K) :
    D.π (y * q * y⁻¹ * q⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (D.π y), mul_inv_cancel,
    one_mul, mul_inv_cancel]

omit [Finite G] in
theorem swap_ne_one_of_ne {a b : Fin n} (hab : a ≠ b) : swap a b ≠ 1 := by
  intro h
  have := congrArg (fun f : Perm (Fin n) => f a) h
  simp only [swap_apply_left, Perm.one_apply] at this
  exact hab this.symm

theorem presPair_of_mem_conj (C : Cfg G M X n) {g : G} (hTM : conjSubgroup g (Rc X) ≤ M)
    {a b : Fin n} (hab : a ≠ b)
    (hall : ∀ τ (hτ : τ ∈ conjSubgroup g (Rc X)),
      C.θ ⟨τ, hTM hτ⟩ = 1 ∨ C.θ ⟨τ, hTM hτ⟩ = swap a b)
    {s : G} (hs : s ∈ conjSubgroup g (Rc X)) (hsθ : C.θ ⟨s, hTM hs⟩ = swap a b)
    {h : G} (hh : h ∈ M) (hgh : g⁻¹ * h * g ∈ M) : PresPair (C.θ ⟨h, hh⟩) a b := by
  apply presPair_of_conj_swap hab
  have h1 : h * s * h⁻¹ ∈ conjSubgroup g (Rc X) := conj_normalized C.S hgh hs
  have e : C.θ ⟨h * s * h⁻¹, hTM h1⟩ = C.θ ⟨h, hh⟩ * swap a b * (C.θ ⟨h, hh⟩)⁻¹ := by
    rw [← hsθ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rcases hall _ h1 with h2 | h2
  · exfalso
    rw [e] at h2
    apply swap_ne_one_of_ne hab
    have := congrArg (fun x => (C.θ ⟨h, hh⟩)⁻¹ * x * C.θ ⟨h, hh⟩) h2
    simpa [mul_assoc] using this
  · rw [← e]
    exact h2

theorem false_of_caseII (C : Cfg G M X n) (D : C.PiData) (hn : 6 ≤ n)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r)
    (hI : ∀ g : G, g ∉ M → conjSubgroup g (Rc X) ≤ M →
      conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M ≠ ⊥)
    {g : G} (hgM : g ∉ M) (hTM : conjSubgroup g (Rc X) ≤ M) (hcard : 3 ≤ Nat.card ↥(Rc X)) :
    False := by
  classical
  set R := Rc X with hRdef
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set T := conjSubgroup g R with hTdef
  have hR : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hne : T ≠ R := conj_ne_of_not_mem C.S hR hgM
  have hRQ : ∀ r ∈ R, r ∈ Q := fun r hr => by
    rw [hRdef, C.S.R_eq_inf] at hr
    exact (Subgroup.mem_inf.1 hr).1
  have hRC : ∀ r ∈ R, r ∈ Subgroup.centralizer (X : Set G) := fun r hr => by
    rw [hRdef, C.S.R_eq_inf] at hr
    exact (Subgroup.mem_inf.1 hr).2
  have hQC : ∀ x ∈ Q, x ∈ Subgroup.centralizer (X : Set G) → x ∈ R := fun x hx hxC => by
    rw [hRdef, C.S.R_eq_inf]
    exact Subgroup.mem_inf.2 ⟨hx, hxC⟩
  have hTQ : T ⊓ Q ≠ ⊥ := hI g hgM hTM
  obtain ⟨a, b, hab, t₁, ht₁T, ht₁W, ht₁1, hTK, hall, ⟨s, hsT, hsθ⟩, hπt₁, hQg⟩ :=
    caseII_structure C D hn hRsyl hgM hTM hcard hTQ
  have hgM' : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hTM' : conjSubgroup g⁻¹ R ≤ M := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ R := by simpa using mem_conjSubgroup.1 hx
    have h2 := hQg _ (hRQ _ h1)
    simpa [mul_assoc] using h2
  have hTQ' : conjSubgroup g⁻¹ R ⊓ Q ≠ ⊥ := hI g⁻¹ hgM' hTM'
  obtain ⟨a', b', hab', t₁', ht₁'T, ht₁'W, ht₁'1, hTK', hall', ⟨s', hs'T, hs'θ⟩, hπt₁', hQg'⟩ :=
    caseII_structure C D hn hRsyl hgM' hTM' hcard hTQ'
  have hQg'' : ∀ q ∈ Q, g * q * g⁻¹ ∈ M := fun q hq => by simpa using hQg' q hq
  have ht₁'sq : t₁' * t₁' = 1 := by
    have := C.S.elemU.2 t₁' ht₁'W
    rwa [pow_two] at this
  have hmemT' : ∀ x : G, x ∈ conjSubgroup g⁻¹ R ↔ g * x * g⁻¹ ∈ R := fun x => by
    rw [mem_conjSubgroup]
    simp
  have hodd : ∀ y ∈ C.K, Odd (orderOf y) → ∀ r ∈ R, y * r * y⁻¹ = r := by
    intro y hyK hoy r hr
    have hy'M : g⁻¹ * y * g ∈ M := conj_mem_of_comm C.S ht₁T ht₁1 (K_comm_W C hyK ht₁W)
    set y' := g⁻¹ * y * g with hy'
    have hoy' : Odd (orderOf y') := by
      have h1 : orderOf ((MulAut.conj g⁻¹) y) = orderOf y := MulEquiv.orderOf_eq _ y
      have h2 : (MulAut.conj g⁻¹) y = y' := by simp [hy', MulAut.conj_apply]
      rw [h2] at h1
      rw [h1]
      exact hoy
    have hyM : y ∈ M := C.K_le hyK
    have hy'T' : ∀ τ ∈ conjSubgroup g⁻¹ R, y' * τ * y'⁻¹ ∈ conjSubgroup g⁻¹ R := by
      intro τ hτ
      rw [hmemT'] at hτ ⊢
      have e : g * (y' * τ * y'⁻¹) * g⁻¹ = y * (g * τ * g⁻¹) * y⁻¹ := by rw [hy']; group
      rw [e]
      exact R_normalized C.S hyM hτ
    have hy't₁' : y' * t₁' * y'⁻¹ = t₁' := by
      have h1 := hy'T' t₁' ht₁'T
      have h2 : y' * t₁' * y'⁻¹ ∈ Q := pCoreOf_normalized M hy'M (C.S.W_le_Q ht₁'W)
      rcases hTK' _ h1 (Q_le_K C h2) with h | h
      · exfalso
        apply ht₁'1
        have : t₁' = y'⁻¹ * (y' * t₁' * y'⁻¹) * y' := by group
        rw [this, h]
        group
      · exact h
    have hdich : ∀ τ ∈ conjSubgroup g⁻¹ R,
        y' * τ * y'⁻¹ * τ⁻¹ = 1 ∨ y' * τ * y'⁻¹ * τ⁻¹ = t₁' := by
      intro τ hτ
      have hτM := hTM' hτ
      have hyτ := hy'T' τ hτ
      have hyτM : y' * τ * y'⁻¹ ∈ M := M.mul_mem (M.mul_mem hy'M hτM) (M.inv_mem hy'M)
      have hcM : y' * τ * y'⁻¹ * τ⁻¹ ∈ M := M.mul_mem hyτM (M.inv_mem hτM)
      refine hTK' _ ((conjSubgroup g⁻¹ R).mul_mem hyτ ((conjSubgroup g⁻¹ R).inv_mem hτ))
        (C.mem_K.2 ⟨hcM, ?_⟩)
      have hθyτ : C.θ ⟨y' * τ * y'⁻¹, hyτM⟩ =
          C.θ ⟨y', hy'M⟩ * C.θ ⟨τ, hτM⟩ * (C.θ ⟨y', hy'M⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      have hcdef : (⟨y' * τ * y'⁻¹ * τ⁻¹, hcM⟩ : ↥M) =
          ⟨y' * τ * y'⁻¹, hyτM⟩ * (⟨τ, hτM⟩ : ↥M)⁻¹ := rfl
      rw [hcdef, map_mul, map_inv]
      rcases hall' τ hτ with h1 | h1
      · rw [hθyτ, h1]
        group
      · have hθ1 : C.θ ⟨y' * τ * y'⁻¹, hyτM⟩ = swap a' b' := by
          rcases hall' _ hyτ with h2 | h2
          · exfalso
            rw [hθyτ, h1] at h2
            apply swap_ne_one_of_ne hab'
            have := congrArg (fun x => (C.θ ⟨y', hy'M⟩)⁻¹ * x * C.θ ⟨y', hy'M⟩) h2
            simpa [mul_assoc] using this
          · exact h2
        rw [hθ1, h1, mul_inv_cancel]
    have hy'c : ∀ τ ∈ conjSubgroup g⁻¹ R, y' * τ * y'⁻¹ = τ := fun τ hτ =>
      comm_of_odd_order hoy' hy't₁' ht₁'sq (hdich τ hτ)
    have hrT' : g⁻¹ * r * g ∈ conjSubgroup g⁻¹ R := by
      rw [hmemT']
      simpa [mul_assoc] using hr
    have h4 := hy'c _ hrT'
    have e : y' * (g⁻¹ * r * g) * y'⁻¹ = g⁻¹ * (y * r * y⁻¹) * g := by rw [hy']; group
    rw [e] at h4
    have h5 := congrArg (fun z => g * z * g⁻¹) h4
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h5
    simpa [mul_assoc] using h5
  have hCR : ∀ c ∈ Subgroup.centralizer (X : Set G), c ∈ R := by
    intro c hc
    have hcK := C_le_K C hc
    have hcM : c ∈ M := C.K_le hcK
    obtain ⟨k, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    have h1 : c ^ m' ∈ R := by
      have hj : (c ^ m') ^ (2 ^ k) = 1 := by
        rw [← pow_mul, mul_comm, ← hm]
        exact pow_orderOf_eq_one c
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
      have h2 : IsPGroup 2 (Subgroup.zpowers (c ^ m')) :=
        IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
      exact hRsyl _ h2 (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ hc m'))
        (Subgroup.mem_zpowers _)
    have h2 : c ^ (2 ^ k) = 1 := by
      set y := c ^ (2 ^ k) with hydef
      have hyC : y ∈ Subgroup.centralizer (X : Set G) := Subgroup.pow_mem _ hc _
      have hyK := C_le_K C hyC
      have hyM : y ∈ M := C.K_le hyK
      have hym : y ^ m' = 1 := by
        rw [hydef, ← pow_mul, ← hm]
        exact pow_orderOf_eq_one c
      have hoy : Odd (orderOf y) := hm'.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
      have hyR := hodd y hyK hoy
      have hyQ : ∀ q ∈ Q, y * q = q * y := by
        intro q hq
        set r := y * q * y⁻¹ * q⁻¹ with hrdef
        have hrQ : r ∈ Q := Q.mul_mem (pCoreOf_normalized M hyM hq) (Q.inv_mem hq)
        have hrC : r ∈ Subgroup.centralizer (X : Set G) := by
          have := pi_commutator_eq_one D ⟨y, hyK⟩ ⟨q, Q_le_K C hq⟩
          exact (D.ker _).1 this
        have hrR : r ∈ R := hQC r hrQ hrC
        have hyr : y * r * y⁻¹ = r := hyR r hrR
        have hpow : ∀ j : ℕ, y ^ j * q * (y ^ j)⁻¹ = r ^ j * q := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            calc y ^ (j + 1) * q * (y ^ (j + 1))⁻¹ = y * (y ^ j * q * (y ^ j)⁻¹) * y⁻¹ := by
                  rw [pow_succ']
                  group
              _ = y * (r ^ j * q) * y⁻¹ := by rw [ih]
              _ = (y * r ^ j * y⁻¹) * (y * q * y⁻¹) := by group
              _ = (y * r * y⁻¹) ^ j * (y * q * y⁻¹) := by rw [conj_pow]
              _ = r ^ j * (r * q) := by
                  rw [hyr]
                  congr 1
                  rw [hrdef]
                  group
              _ = r ^ (j + 1) * q := by rw [pow_succ, mul_assoc (r ^ j) r q]
        have hq' := hpow (orderOf y)
        rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hq'
        have hr1 : r ^ orderOf y = 1 := by
          have := congrArg (fun z => z * q⁻¹) hq'
          simpa using this.symm
        obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G)) ⟨r, hrR⟩
        have hj' : r ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
        have hr : r = 1 := eq_one_of_odd_of_two_pow hoy hr1 hj'
        calc y * q = r * (q * y) := by rw [hrdef]; group
          _ = q * y := by rw [hr, one_mul]
      have hyQ' : y ∈ Q := C.S.charTwo M C.S.maxLocal.1 ⟨hyM,
        Subgroup.mem_centralizer_iff.2 fun q hq => (hyQ q hq).symm⟩
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨y, hyQ'⟩
      have hj' : y ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      exact eq_one_of_odd_of_two_pow hoy (pow_orderOf_eq_one y) hj'
    have hcop : Nat.Coprime m' (2 ^ k) := (Nat.coprime_two_right.2 hm').pow_right k
    exact mem_of_pow_mem_of_coprime R hcop h1 (by rw [h2]; exact R.one_mem)
  have hKQ : C.K ≤ Q := by
    refine le_pCoreOf_of_normalized C.K_le (fun m hm k hk => K_normalized C hm hk) ?_
    rintro ⟨k, hk⟩
    have hk2 : k * k ∈ R := by
      refine hCR _ ((D.ker ⟨k * k, C.K.mul_mem hk hk⟩).1 ?_)
      apply Multiplicative.toAdd.injective
      have e : D.π ⟨k * k, C.K.mul_mem hk hk⟩ = D.π ⟨k, hk⟩ * D.π ⟨k, hk⟩ := by
        rw [← map_mul]
        rfl
      rw [e, toAdd_mul, permBar_add_self, toAdd_one]
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G)) ⟨k * k, hk2⟩
    refine ⟨j + 1, Subtype.ext ?_⟩
    have hj' : (k * k) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, pow_two, hj']
  have hsM : s ∈ M := hTM hsT
  have hs'M : s' ∈ M := hTM' hs'T
  have hQR : ¬ ∀ q ∈ Q, ∀ r ∈ R, q * r = r * q := by
    intro hQR
    have heven : ∀ m (hm : m ∈ M), Equiv.Perm.sign (C.θ ⟨m, hm⟩) = 1 →
        ∀ r ∈ R, m * r * m⁻¹ = r := by
      intro m hm hsign r hr
      obtain ⟨x, hx⟩ := C.exists_lift (Equiv.Perm.mem_alternatingGroup.2 hsign)
      have hxM : (x : G) ∈ M := C.S.le x.2
      have hk : (x : G)⁻¹ * m ∈ C.K := by
        refine C.mem_K.2 ⟨M.mul_mem (M.inv_mem hxM) hm, ?_⟩
        have e : (⟨(x : G)⁻¹ * m, M.mul_mem (M.inv_mem hxM) hm⟩ : ↥M) =
            (⟨x, hxM⟩ : ↥M)⁻¹ * ⟨m, hm⟩ := rfl
        rw [e, map_mul, map_inv, hx, inv_mul_cancel]
      have hkr := hQR _ (hKQ hk) r hr
      have hxr : (x : G) * r = r * x := Subgroup.mem_centralizer_iff.1 (hRC r hr) x x.2
      calc m * r * m⁻¹ = (x : G) * (((x : G)⁻¹ * m) * r * ((x : G)⁻¹ * m)⁻¹) * (x : G)⁻¹ := by
            group
        _ = (x : G) * r * (x : G)⁻¹ := by
            rw [show ((x : G)⁻¹ * m) * r * ((x : G)⁻¹ * m)⁻¹ = r by rw [hkr]; group]
        _ = r := by rw [hxr]; group
    have hMR : ∀ m (hm : m ∈ M), ∀ r ∈ R, m * r * m⁻¹ = r := by
      intro m hm r hr
      rcases Int.units_eq_one_or (Equiv.Perm.sign (C.θ ⟨m, hm⟩)) with h | h
      · exact heven m hm h r hr
      · have hms : m * s⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hsM)
        have hsign : Equiv.Perm.sign (C.θ ⟨m * s⁻¹, hms⟩) = 1 := by
          have e : (⟨m * s⁻¹, hms⟩ : ↥M) = ⟨m, hm⟩ * (⟨s, hsM⟩ : ↥M)⁻¹ := rfl
          rw [e, map_mul, map_inv, map_mul, map_inv, h, hsθ, Equiv.Perm.sign_swap hab]
          decide
        have h1 := heven _ hms hsign r hr
        have hsr : s * r = r * s := (comm_R_conj C.S hR hTM hne hr hsT).symm
        calc m * r * m⁻¹ = (m * s⁻¹) * (s * r * s⁻¹) * (m * s⁻¹)⁻¹ := by group
          _ = (m * s⁻¹) * r * (m * s⁻¹)⁻¹ := by
              rw [show s * r * s⁻¹ = r by rw [hsr]; group]
          _ = r := h1
    have hsr : g⁻¹ * s * g ∈ R := mem_conjSubgroup.1 hsT
    apply swap_ne_one_of_ne hab
    rw [← hsθ]
    refine (C.theta_eq_one_iff C.S.five_le_degree _).2 fun u v hv => ?_
    have h1 := hMR _ (hQg _ (C.S.W_le_Q u.2)) _ hsr
    have h2 : (u : G) * s * (u : G)⁻¹ = s := by
      have := congrArg (fun z => g * z * g⁻¹) h1
      simpa [mul_assoc] using this
    have hvu : v = u := Subtype.ext (by
      rw [hv]
      show s * (u : G) * s⁻¹ = u
      have h3 : (u : G) * s = s * u := by
        calc (u : G) * s = ((u : G) * s * (u : G)⁻¹) * u := by group
          _ = s * u := by rw [h2]
      rw [← h3]
      group)
    rw [hvu]
  have hodd_q : ∃ q, ∃ hq : q ∈ Q,
      Multiplicative.toAdd (D.π ⟨q, Q_le_K C hq⟩) ∉ Set.range (heartToBar (n := n)) := by
    by_contra h
    push Not at h
    apply hQR
    intro q hq r hr
    obtain ⟨u, hu⟩ := h q hq
    obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
    have hwQ : (w : G) ∈ Q := C.S.W_le_Q w.2
    have hπ : D.π (⟨q, Q_le_K C hq⟩ * (⟨w, Q_le_K C hwQ⟩ : ↥C.K)⁻¹) = 1 := by
      have e : D.π ⟨w, Q_le_K C hwQ⟩ = D.π ⟨q, Q_le_K C hq⟩ := by
        apply Multiplicative.toAdd.injective
        rw [D.π_W ⟨w, Q_le_K C hwQ⟩ w rfl, hw, toAdd_ofAdd, hu]
      rw [map_mul, map_inv, e, mul_inv_cancel]
    have hqw : q * (w : G)⁻¹ ∈ R :=
      hQC _ (Q.mul_mem hq (Q.inv_mem hwQ)) ((D.ker _).1 hπ)
    have h1 := hRab _ hqw r hr
    have h2 : (w : G) * r = r * w := W_comm_Q C w.2 (hRQ r hr)
    calc q * r = (q * (w : G)⁻¹) * ((w : G) * r) := by group
      _ = (q * (w : G)⁻¹) * (r * w) := by rw [h2]
      _ = (q * (w : G)⁻¹ * r) * w := by group
      _ = (r * (q * (w : G)⁻¹)) * w := by rw [h1]
      _ = r * q := by group
  obtain ⟨q₀, hq₀, hq₀odd⟩ := hodd_q
  obtain ⟨q, hq, hqπ⟩ : ∃ q, ∃ hq : q ∈ Q,
      Multiplicative.toAdd (D.π ⟨q, Q_le_K C hq⟩) = barPt a := by
    obtain ⟨u, hu⟩ := add_mem_range_heartToBar (barPt_not_mem_range C.even_n a) hq₀odd
    obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
    have hwQ : (w : G) ∈ Q := C.S.W_le_Q w.2
    refine ⟨q₀ * w, Q.mul_mem hq₀ hwQ, ?_⟩
    have e : D.π ⟨q₀ * w, Q_le_K C (Q.mul_mem hq₀ hwQ)⟩ =
        D.π ⟨q₀, Q_le_K C hq₀⟩ * D.π ⟨w, Q_le_K C hwQ⟩ := by
      rw [← map_mul]
      rfl
    rw [e, toAdd_mul, D.π_W ⟨w, Q_le_K C hwQ⟩ w rfl, hw, toAdd_ofAdd, hu,
      add_comm (barPt a), ← add_assoc, permBar_add_self, zero_add]
  have hπt₁'fix : ∀ c : Perm (Fin n), c a' = a' → c b' = b' →
      barAct c (Multiplicative.toAdd (D.π ⟨t₁', C.blockU_le_K ht₁'W⟩)) =
        Multiplicative.toAdd (D.π ⟨t₁', C.blockU_le_K ht₁'W⟩) := by
    intro c hca hcb
    rw [hπt₁', map_add, barAct_barPt, barAct_barPt, hca, hcb]
  have hliftT' : ∀ c : Perm (Fin n), c.IsThreeCycle → c a' = a' → c b' = b' →
      ∃ x : ↥X, (x : G) ^ 3 = 1 ∧ (C.α x : Perm (Fin n)) = c ∧ g * x * g⁻¹ ∈ M := by
    intro c hc hca hcb
    obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc
    have hxt : (x : G) * t₁' = t₁' * x :=
      comm_of_pow_three D (k := ⟨t₁', C.blockU_le_K ht₁'W⟩) hx3
        (by rw [hxc]; exact hπt₁'fix c hca hcb)
    exact ⟨x, hx3, hxc, by simpa using conj_mem_of_comm C.S ht₁'T ht₁'1 hxt⟩
  have hθq : C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ = 1 ∨ C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ = swap a' b' := by
    set N : Subgroup (Perm (Fin n)) := ((conjSubgroup g⁻¹ Q).comap M.subtype).map C.θ with hNdef
    have hN2 : IsPGroup 2 N :=
      (((isPGroup_pCoreOf' M).map (MulAut.conj g⁻¹).toMonoidHom).comap_subtype).map C.θ
    have hNab : ∀ τ ∈ N, PresPair τ a' b' := by
      rintro τ ⟨y, hy, rfl⟩
      have hy' : g * (y : G) * g⁻¹ ∈ Q := by simpa using mem_conjSubgroup.1 hy
      exact presPair_of_mem_conj C hTM' hab' hall' hs'T hs'θ y.2
        (by simpa using pCoreOf_le_self M hy')
    have hnorm : ∀ c : Perm (Fin n), c.IsThreeCycle → c a' = a' → c b' = b' →
        ∀ τ ∈ N, c * τ * c⁻¹ ∈ N := by
      intro c hc hca hcb τ hτ
      obtain ⟨x, -, hxc, hgx⟩ := hliftT' c hc hca hcb
      obtain ⟨y, hy, rfl⟩ := hτ
      have hxM : (x : G) ∈ M := C.S.le x.2
      have hy' : g * (y : G) * g⁻¹ ∈ Q := by simpa using mem_conjSubgroup.1 hy
      refine ⟨⟨x, hxM⟩ * y * ⟨x, hxM⟩⁻¹, ?_, ?_⟩
      · show (x : G) * y * (x : G)⁻¹ ∈ conjSubgroup g⁻¹ Q
        rw [mem_conjSubgroup]
        have e : g⁻¹⁻¹ * ((x : G) * y * (x : G)⁻¹) * g⁻¹ =
            (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact pCoreOf_normalized M hgx hy'
      · rw [map_mul, map_mul, map_inv, C.θ_X x, hxc]
    have hφN : C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ ∈ N := by
      refine ⟨⟨g⁻¹ * q * g, hQg q hq⟩, ?_, rfl⟩
      show g⁻¹ * q * g ∈ conjSubgroup g⁻¹ Q
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hq
    obtain ⟨c₁, hc₁a, hc₁b⟩ :=
      CFSG.HardMathSupport.RichardWeiss.Proving.exists_ne_pair_heart (by omega) a b
    obtain ⟨c₂, hc₂a, hc₂b, hc₂c₁⟩ : ∃ c₂ : Fin n, c₂ ≠ a ∧ c₂ ≠ b ∧ c₂ ≠ c₁ := by
      have hlt : ({a, b, c₁} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        have h3 : ({a, b, c₁} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
        omega
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      exact ⟨p, hp.1, hp.2.1, hp.2.2⟩
    obtain ⟨c₃, hc₃a, hc₃b, hc₃c₁, hc₃c₂⟩ :
        ∃ c₃ : Fin n, c₃ ≠ a ∧ c₃ ≠ b ∧ c₃ ≠ c₁ ∧ c₃ ≠ c₂ := by
      have hlt : ({a, b, c₁, c₂} : Finset (Fin n)).card <
          (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        have h4 : ({a, b, c₁, c₂} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
        omega
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      exact ⟨p, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
    have hc3 : (swap c₁ c₂ * swap c₁ c₃).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same (Ne.symm hc₂c₁) (Ne.symm hc₃c₁) (Ne.symm hc₃c₂)
    have hca : (swap c₁ c₂ * swap c₁ c₃) a = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hc₁a) (Ne.symm hc₃a),
        swap_apply_of_ne_of_ne (Ne.symm hc₁a) (Ne.symm hc₂a)]
    have hcb : (swap c₁ c₂ * swap c₁ c₃) b = b := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hc₁b) (Ne.symm hc₃b),
        swap_apply_of_ne_of_ne (Ne.symm hc₁b) (Ne.symm hc₂b)]
    obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc3
    have hxM : (x : G) ∈ M := C.S.le x.2
    have hxt : (x : G) * t₁ = t₁ * x :=
      comm_of_pow_three D (k := ⟨t₁, C.blockU_le_K ht₁W⟩) hx3
        (by rw [hxc, hπt₁, map_add, barAct_barPt, barAct_barPt, hca, hcb])
    have hyM : g⁻¹ * x * g ∈ M := conj_mem_of_comm C.S ht₁T ht₁1 hxt
    have hy3 : (g⁻¹ * (x : G) * g) ^ 3 = 1 := by
      have e : g⁻¹ * (x : G) * g = (MulAut.conj g⁻¹) x := by simp [MulAut.conj_apply]
      rw [e, ← map_pow, hx3, map_one]
    have hψ3 : C.θ ⟨g⁻¹ * x * g, hyM⟩ ^ 3 = 1 := by
      have e : (⟨g⁻¹ * x * g, hyM⟩ : ↥M) ^ 3 = 1 :=
        Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hy3)
      rw [← map_pow, e, map_one]
    have hψ1 : C.θ ⟨g⁻¹ * x * g, hyM⟩ ≠ 1 := by
      intro h1
      have hyQ : g⁻¹ * x * g ∈ Q := hKQ (C.mem_K.2 ⟨hyM, h1⟩)
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨_, hyQ⟩
      have hj' : (g⁻¹ * (x : G) * g) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      have hy1 := eq_one_of_odd_of_two_pow (by decide : Odd 3) hy3 hj'
      have hx1 : (x : G) = 1 := by
        have e : (x : G) = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [e, hy1]
        group
      apply hc3.ne_one
      rw [← hxc, show x = 1 from Subtype.ext hx1, map_one]
      rfl
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hψord : orderOf (C.θ ⟨g⁻¹ * x * g, hyM⟩) = 3 := orderOf_eq_prime hψ3 hψ1
    have hψfix : C.θ ⟨g⁻¹ * x * g, hyM⟩ a' = a' ∧ C.θ ⟨g⁻¹ * x * g, hyM⟩ b' = b' := by
      rcases presPair_of_mem_conj C hTM' hab' hall' hs'T hs'θ hyM
          (by simpa [mul_assoc] using hxM) with h | ⟨h1, h2⟩
      · exact h
      · exfalso
        have h4 : (C.θ ⟨g⁻¹ * x * g, hyM⟩ ^ 3) a' = b' := by
          simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, h1, h2]
        rw [hψ3, Perm.one_apply] at h4
        exact hab' h4
    have hxq : (x : G) * q * (x : G)⁻¹ ∈ Q := pCoreOf_normalized M hxM hq
    have hrQ : q⁻¹ * ((x : G) * q * (x : G)⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq) hxq
    have hrR : q⁻¹ * ((x : G) * q * (x : G)⁻¹) ∈ R := by
      refine hQC _ hrQ ((D.ker ⟨q⁻¹ * ((x : G) * q * (x : G)⁻¹), Q_le_K C hrQ⟩).1 ?_)
      have e : D.π ⟨q⁻¹ * ((x : G) * q * (x : G)⁻¹), Q_le_K C hrQ⟩ =
          (D.π ⟨q, Q_le_K C hq⟩)⁻¹ * D.π ⟨(x : G) * q * (x : G)⁻¹, Q_le_K C hxq⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv,
        D.equivar ⟨x, hxM⟩ ⟨q, Q_le_K C hq⟩ ⟨(x : G) * q * (x : G)⁻¹, Q_le_K C hxq⟩ rfl,
        C.θ_X x, hxc, hqπ, barAct_barPt, hca, neg_add_cancel, toAdd_one]
    have hr'T : g⁻¹ * (q⁻¹ * ((x : G) * q * (x : G)⁻¹)) * g ∈ conjSubgroup g⁻¹ R :=
      (hmemT' _).2 (by simpa [mul_assoc] using hrR)
    have hfix : C.θ ⟨g⁻¹ * x * g, hyM⟩ * C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ *
          (C.θ ⟨g⁻¹ * x * g, hyM⟩)⁻¹ = C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ ∨
        C.θ ⟨g⁻¹ * x * g, hyM⟩ * C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ *
          (C.θ ⟨g⁻¹ * x * g, hyM⟩)⁻¹ = C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ * swap a' b' := by
      have e : C.θ ⟨g⁻¹ * x * g, hyM⟩ * C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ *
            (C.θ ⟨g⁻¹ * x * g, hyM⟩)⁻¹ =
          C.θ ⟨g⁻¹ * q * g, hQg q hq⟩ * C.θ ⟨_, hTM' hr'T⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show g⁻¹ * x * g * (g⁻¹ * q * g) * (g⁻¹ * x * g)⁻¹ =
          g⁻¹ * q * g * (g⁻¹ * (q⁻¹ * ((x : G) * q * (x : G)⁻¹)) * g)
        group
      rw [e]
      rcases hall' _ hr'T with h | h
      · left
        rw [h, mul_one]
      · right
        rw [h]
    exact mem_swap_of_threeCycle_fixed hn hab' hN2 hNab hnorm hψord hψfix.1 hψfix.2 hφN hfix
  have hr's : g * s' * g⁻¹ ∈ R := (hmemT' s').1 hs'T
  obtain ⟨e, heQ, heQ', heπ⟩ : ∃ e, ∃ he : e ∈ Q, g⁻¹ * e * g ∈ Q ∧
      Multiplicative.toAdd (D.π ⟨e, Q_le_K C he⟩) = barPt a := by
    rcases hθq with h1 | h1
    · exact ⟨q, hq, hKQ (C.mem_K.2 ⟨hQg q hq, h1⟩), hqπ⟩
    · have hqr : q * (g * s' * g⁻¹) ∈ Q := Q.mul_mem hq (hRQ _ hr's)
      refine ⟨q * (g * s' * g⁻¹), hqr, ?_, ?_⟩
      · apply hKQ
        have hM' : g⁻¹ * (q * (g * s' * g⁻¹)) * g ∈ M := hQg _ hqr
        refine C.mem_K.2 ⟨hM', ?_⟩
        have e : (⟨g⁻¹ * (q * (g * s' * g⁻¹)) * g, hM'⟩ : ↥M) =
            ⟨g⁻¹ * q * g, hQg q hq⟩ * ⟨s', hs'M⟩ := Subtype.ext (by
              show g⁻¹ * (q * (g * s' * g⁻¹)) * g = g⁻¹ * q * g * s'
              group)
        rw [e, map_mul, h1, hs'θ, swap_mul_self]
      · have e : D.π ⟨q * (g * s' * g⁻¹), Q_le_K C hqr⟩ =
            D.π ⟨q, Q_le_K C hq⟩ * D.π ⟨g * s' * g⁻¹, C_le_K C (hRC _ hr's)⟩ := by
          rw [← map_mul]
          rfl
        rw [e, (D.ker ⟨g * s' * g⁻¹, C_le_K C (hRC _ hr's)⟩).2 (hRC _ hr's), mul_one, hqπ]
  set e' := g⁻¹ * e * g with he'def
  have hpiD : ∀ d (hd : d ∈ Q), g⁻¹ * d * g ∈ Q →
      (Multiplicative.toAdd (D.π ⟨d, Q_le_K C hd⟩) = 0 ∨
        Multiplicative.toAdd (D.π ⟨d, Q_le_K C hd⟩) = barPt a + barPt b) →
      ∀ hd' : g⁻¹ * d * g ∈ Q,
      Multiplicative.toAdd (D.π ⟨g⁻¹ * d * g, Q_le_K C hd'⟩) = 0 ∨
        Multiplicative.toAdd (D.π ⟨g⁻¹ * d * g, Q_le_K C hd'⟩) = barPt a' + barPt b' := by
    intro d hd _ hπd hd'
    have hT'Q : ∀ z (hz : z ∈ Q), g * z * g⁻¹ ∈ R →
        Multiplicative.toAdd (D.π ⟨z, Q_le_K C hz⟩) = 0 ∨
          Multiplicative.toAdd (D.π ⟨z, Q_le_K C hz⟩) = barPt a' + barPt b' := by
      intro z hz hzR
      rcases hTK' z ((hmemT' z).2 hzR) (Q_le_K C hz) with h | h
      · left
        have : (⟨z, Q_le_K C hz⟩ : ↥C.K) = 1 := Subtype.ext h
        rw [this, map_one]
        rfl
      · right
        have : (⟨z, Q_le_K C hz⟩ : ↥C.K) = ⟨t₁', C.blockU_le_K ht₁'W⟩ := Subtype.ext h
        rw [this, hπt₁']
    rcases hπd with h0 | h0
    ·
      have hdR : d ∈ R := hQC d hd ((D.ker _).1 (Multiplicative.toAdd.injective
        (h0.trans toAdd_one.symm)))
      exact hT'Q _ hd' (by simpa [mul_assoc] using hdR)
    ·
      have ht₁Q : t₁ ∈ Q := C.S.W_le_Q ht₁W
      have hdt : d * t₁⁻¹ ∈ Q := Q.mul_mem hd (Q.inv_mem ht₁Q)
      have hπdt : D.π ⟨d * t₁⁻¹, Q_le_K C hdt⟩ = 1 := by
        have e : (⟨d * t₁⁻¹, Q_le_K C hdt⟩ : ↥C.K) =
            ⟨d, Q_le_K C hd⟩ * (⟨t₁, C.blockU_le_K ht₁W⟩ : ↥C.K)⁻¹ := rfl
        rw [e, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, h0, hπt₁, toAdd_one, add_neg_cancel]
      have hdtR : d * t₁⁻¹ ∈ R := hQC _ hdt ((D.ker _).1 hπdt)
      have hr₁ : g⁻¹ * t₁ * g ∈ R := mem_conjSubgroup.1 ht₁T
      have hz : g⁻¹ * (d * t₁⁻¹) * g ∈ Q := by
        have e : g⁻¹ * (d * t₁⁻¹) * g = (g⁻¹ * d * g) * (g⁻¹ * t₁ * g)⁻¹ := by group
        rw [e]
        exact Q.mul_mem hd' (Q.inv_mem (hRQ _ hr₁))
      have h1 := hT'Q _ hz (by simpa [mul_assoc] using hdtR)
      have e : D.π ⟨g⁻¹ * d * g, Q_le_K C hd'⟩ =
          D.π ⟨g⁻¹ * (d * t₁⁻¹) * g, Q_le_K C hz⟩ *
            D.π ⟨g⁻¹ * t₁ * g, C_le_K C (hRC _ hr₁)⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show g⁻¹ * d * g = g⁻¹ * (d * t₁⁻¹) * g * (g⁻¹ * t₁ * g)
        group
      rw [e, (D.ker ⟨g⁻¹ * t₁ * g, C_le_K C (hRC _ hr₁)⟩).2 (hRC _ hr₁), mul_one]
      exact h1
  have he'Q : e' ∈ Q := heQ'
  have hmod : ∀ h' (hh' : h' ∈ M), g * h' * g⁻¹ ∈ M →
      barAct (C.θ ⟨h', hh'⟩) (Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩)) =
          Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩) ∨
        barAct (C.θ ⟨h', hh'⟩) (Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩)) =
          Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩) + (barPt a' + barPt b') := by
    intro h' hh' hgh'
    set h := g * h' * g⁻¹ with hhdef
    have hghg : g⁻¹ * h * g = h' := by rw [hhdef]; group
    have hheh : h * e * h⁻¹ ∈ Q := pCoreOf_normalized M hgh' heQ
    have hd : h * e * h⁻¹ * e⁻¹ ∈ Q := Q.mul_mem hheh (Q.inv_mem heQ)
    have hh'e' : h' * e' * h'⁻¹ ∈ Q := pCoreOf_normalized M hh' he'Q
    have e1 : g⁻¹ * (h * e * h⁻¹ * e⁻¹) * g = h' * e' * h'⁻¹ * e'⁻¹ := by
      rw [he'def, ← hghg]
      group
    have hd' : g⁻¹ * (h * e * h⁻¹ * e⁻¹) * g ∈ Q := by
      rw [e1]
      exact Q.mul_mem hh'e' (Q.inv_mem he'Q)
    have hpres := presPair_of_mem_conj C hTM hab hall hsT hsθ hgh' (by rw [hghg]; exact hh')
    have hπd : Multiplicative.toAdd (D.π ⟨h * e * h⁻¹ * e⁻¹, Q_le_K C hd⟩) = 0 ∨
        Multiplicative.toAdd (D.π ⟨h * e * h⁻¹ * e⁻¹, Q_le_K C hd⟩) = barPt a + barPt b := by
      have e2 : D.π ⟨h * e * h⁻¹ * e⁻¹, Q_le_K C hd⟩ =
          D.π ⟨h * e * h⁻¹, Q_le_K C hheh⟩ * (D.π ⟨e, Q_le_K C heQ⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e2, toAdd_mul, toAdd_inv,
        D.equivar ⟨h, hgh'⟩ ⟨e, Q_le_K C heQ⟩ ⟨h * e * h⁻¹, Q_le_K C hheh⟩ rfl, heπ,
        barAct_barPt]
      rcases hpres with ⟨ha, -⟩ | ⟨ha, -⟩
      · left
        rw [ha, add_neg_cancel]
      · right
        rw [ha, permBar_neg_eq, add_comm]
    have h1 := hpiD _ hd hd' hπd hd'
    have e3 : D.π ⟨g⁻¹ * (h * e * h⁻¹ * e⁻¹) * g, Q_le_K C hd'⟩ =
        D.π ⟨h' * e' * h'⁻¹, Q_le_K C hh'e'⟩ * (D.π ⟨e', Q_le_K C he'Q⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext e1
    rw [e3, toAdd_mul, toAdd_inv,
      D.equivar ⟨h', hh'⟩ ⟨e', Q_le_K C he'Q⟩ ⟨h' * e' * h'⁻¹, Q_le_K C hh'e'⟩ rfl] at h1
    rcases h1 with h1 | h1
    · left
      exact add_neg_eq_zero.1 h1
    · right
      rw [add_neg_eq_iff_eq_add] at h1
      rw [h1, add_comm]
  have hcases := eq_of_threeCycle_fixes_mod (by omega) hab'
    (v := Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩)) fun c hc hca hcb => by
      obtain ⟨x, -, hxc, hgx⟩ := hliftT' c hc hca hcb
      have := hmod x (C.S.le x.2) hgx
      rwa [C.θ_X x, hxc] at this
  have heπ0 : ∀ z (hz : z ∈ C.K), Multiplicative.toAdd (D.π ⟨z, hz⟩) =
      Multiplicative.toAdd (D.π ⟨e, Q_le_K C heQ⟩) → z ∈ T → z ∈ Q → False := by
    intro z hz hzπ hzT hzQ
    have hzab : Multiplicative.toAdd (D.π ⟨z, hz⟩) ∈ Set.range (heartToBar (n := n)) := by
      rcases hTK z hzT hz with h1 | h1
      · have : (⟨z, hz⟩ : ↥C.K) = 1 := Subtype.ext h1
        rw [this, map_one]
        exact ⟨0, map_zero _⟩
      · have : (⟨z, hz⟩ : ↥C.K) = ⟨t₁, C.blockU_le_K ht₁W⟩ := Subtype.ext h1
        rw [this, hπt₁, ← heartToBar_pairEW]
        exact ⟨_, rfl⟩
    rw [hzπ, heπ] at hzab
    exact barPt_not_mem_range C.even_n a hzab
  have hπe' : ∃ a'' : Fin n, Multiplicative.toAdd (D.π ⟨e', Q_le_K C he'Q⟩) = barPt a'' := by
    rcases hcases with h0 | h0 | h0 | h0
    · exfalso
      have he'R : e' ∈ R := hQC _ he'Q ((D.ker _).1 (Multiplicative.toAdd.injective
        (h0.trans toAdd_one.symm)))
      exact heπ0 e (Q_le_K C heQ) rfl (mem_conjSubgroup.2 he'R) heQ
    · exact ⟨a', h0⟩
    · exact ⟨b', h0⟩
    · exfalso
      have hu : g * t₁' * g⁻¹ ∈ R := (hmemT' t₁').1 ht₁'T
      have he't : e' * t₁'⁻¹ ∈ Q := Q.mul_mem he'Q (Q.inv_mem (C.S.W_le_Q ht₁'W))
      have hπ0 : D.π ⟨e' * t₁'⁻¹, Q_le_K C he't⟩ = 1 := by
        have e4 : (⟨e' * t₁'⁻¹, Q_le_K C he't⟩ : ↥C.K) =
            ⟨e', Q_le_K C he'Q⟩ * (⟨t₁', C.blockU_le_K ht₁'W⟩ : ↥C.K)⁻¹ := rfl
        rw [e4, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, h0, hπt₁', toAdd_one, add_neg_cancel]
      have he'tR : e' * t₁'⁻¹ ∈ R := hQC _ he't ((D.ker _).1 hπ0)
      have hzQ : e * (g * t₁' * g⁻¹)⁻¹ ∈ Q := Q.mul_mem heQ (Q.inv_mem (hRQ _ hu))
      have hzT : e * (g * t₁' * g⁻¹)⁻¹ ∈ T := by
        rw [hTdef, mem_conjSubgroup]
        have e5 : g⁻¹ * (e * (g * t₁' * g⁻¹)⁻¹) * g = e' * t₁'⁻¹ := by rw [he'def]; group
        rw [e5]
        exact he'tR
      refine heπ0 _ (Q_le_K C hzQ) ?_ hzT hzQ
      have e6 : D.π ⟨e, Q_le_K C heQ⟩ = D.π ⟨e * (g * t₁' * g⁻¹)⁻¹, Q_le_K C hzQ⟩ *
          D.π ⟨g * t₁' * g⁻¹, C_le_K C (hRC _ hu)⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show e = e * (g * t₁' * g⁻¹)⁻¹ * (g * t₁' * g⁻¹)
        group
      rw [e6, (D.ker ⟨g * t₁' * g⁻¹, C_le_K C (hRC _ hu)⟩).2 (hRC _ hu), mul_one]
  obtain ⟨a'', ha''⟩ := hπe'
  have hCe' := centralizer_le_of_length_one C D (by omega) hKQ he'Q ha''
  obtain ⟨c₁, hc₁a, hc₁b⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.exists_ne_pair_heart
    (by omega) a b
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Fin n, c₂ ≠ a ∧ c₂ ≠ b ∧ c₂ ≠ c₁ := by
    have hlt : ({a, b, c₁} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 : ({a, b, c₁} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    exact ⟨p, hp.1, hp.2.1, hp.2.2⟩
  obtain ⟨hc₂a, hc₂b, hc₂c₁⟩ := hc₂
  have hc : (swap b c₁ * swap b c₂).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (Ne.symm hc₁b) (Ne.symm hc₂b) (Ne.symm hc₂c₁)
  have hca : (swap b c₁ * swap b c₂) a = a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab (Ne.symm hc₂a),
      swap_apply_of_ne_of_ne hab (Ne.symm hc₁a)]
  have hcb : (swap b c₁ * swap b c₂) b = c₂ := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hc₂b hc₂c₁]
  obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc
  have hxe : (x : G) * e = e * x := comm_of_pow_three D (k := ⟨e, Q_le_K C heQ⟩) hx3
    (by rw [hxc, heπ, barAct_barPt, hca])
  have hgx : g⁻¹ * x * g ∈ M := by
    refine hCe' (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    calc g⁻¹ * x * g * e' = g⁻¹ * (x * e) * g := by rw [he'def]; group
      _ = g⁻¹ * (e * x) * g := by rw [hxe]
      _ = e' * (g⁻¹ * x * g) := by rw [he'def]; group
  have hpres := presPair_of_mem_conj C hTM hab hall hsT hsθ (C.S.le x.2) hgx
  rw [C.θ_X x, hxc] at hpres
  rcases hpres with ⟨-, h⟩ | ⟨-, h⟩
  · rw [hcb] at h
    exact hc₂b h
  · rw [hcb] at h
    exact hc₂a h

theorem false_of_three_le (C : Cfg G M X n) (D : C.PiData) (hn : 8 ≤ n)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r)
    {g : G} (hgM : g ∉ M) (hTM : conjSubgroup g (Rc X) ≤ M) (hcard : 3 ≤ Nat.card ↥(Rc X)) :
    False := by
  have hR : Rc X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  exact false_of_caseII C D (by omega) hRsyl hRab
    (fun g' hg'M hT'M h => false_of_caseI C D hn hW hRsyl hT'M (conj_ne_of_not_mem C.S hR hg'M)
      hcard h)
    hgM hTM hcard

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
