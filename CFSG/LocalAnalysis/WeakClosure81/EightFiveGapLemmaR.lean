module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

structure LemmaRHyp {G : Type} [Group G] (V E K : Subgroup G) {X : Type} [Group X]
    (φ : ↥K →* X) : Prop where
  isTI : CFSG.CGT.Timmesfeld75.IsTI V
  elemAbelian_V : IsElemAbelian 2 V
  elemAbelian_E : IsElemAbelian 2 E
  inf_ne_bot : V ⊓ E ≠ ⊥
  le_K : V ≤ K
  le_normalizer : K ≤ Subgroup.normalizer (E : Set G)
  surjective : Function.Surjective φ
  ker_iff : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (E : Set G)

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_commute_ne_one {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {c y : G} (hc : c ∈ V) (hc1 : c ≠ 1)
    (hy : y * c = c * y) : y ∈ Subgroup.normalizer (V : Set G) := by
  have key : ∀ z : G, z * c = c * z → ∀ x ∈ V, z⁻¹ * x * z ∈ V := by
    intro z hz x hx
    have hcz : c ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup z V := by
      refine ⟨hc, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.2 ?_⟩
      have : z⁻¹ * c * z = c := by
        rw [mul_assoc, ← hz, ← mul_assoc, inv_mul_cancel, one_mul]
      rwa [this]
    rcases hTI z with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at hcz
      exact hc1 hcz
    · have hx' : x ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup z V := by
        rw [h]
        exact hx
      exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.1 hx'.2
  have hy' : y⁻¹ * c = c * y⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy, mul_assoc, mul_inv_cancel, mul_one]
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using key y⁻¹ hy' x hx
  · simpa [mul_assoc] using key y hy (y * x * y⁻¹) hx

namespace LemmaRHyp

variable {V E K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}

theorem mem_normalizer_of_mem_E (h : LemmaRHyp V E K φ) {e : G} (he : e ∈ E) :
    e ∈ Subgroup.normalizer (V : Set G) := by
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.inf_ne_bot
  refine mem_normalizer_of_commute_ne_one h.isTI (c := (c : G)) c.2.1 ?_ ?_
  · intro h1
    exact hc1 (Subtype.ext h1)
  · exact congrArg Subtype.val (h.elemAbelian_E.1.is_comm.comm ⟨e, he⟩ ⟨(c : G), c.2.2⟩)

theorem comm_of_fixed (h : LemmaRHyp V E K φ) {v : ↥K} (hvV : (v : G) ∈ V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X} (hPp : ∀ x ∈ P, x ^ p = 1)
    (hinv : ∀ x ∈ P, φ v * x * (φ v)⁻¹ = x⁻¹) {B : Subgroup X} (hBP : B ≤ P) (hB : B ≠ ⊥)
    {e : G} (heE : e ∈ E) (hfix : ∀ y : ↥K, φ y ∈ B → (y : G) * e = e * (y : G)) :
    (v : G) * e = e * (v : G) := by
  set d : G := e * (v : G) * e⁻¹ * (v : G)⁻¹ with hd
  have heve : e * (v : G) * e⁻¹ ∈ V :=
    ((Subgroup.mem_normalizer_iff.1 (h.mem_normalizer_of_mem_E heE)) (v : G)).1 hvV
  have hdV : d ∈ V := by
    rw [hd]
    exact V.mul_mem heve (V.inv_mem hvV)
  have hconj : ∀ z ∈ P, (φ v)⁻¹ * z * φ v = z⁻¹ := by
    intro z hz
    have h1 : φ v * z⁻¹ * (φ v)⁻¹ = z := by
      have h := hinv z⁻¹ (P.inv_mem hz)
      simpa using h
    calc (φ v)⁻¹ * z * φ v
        = (φ v)⁻¹ * (φ v * z⁻¹ * (φ v)⁻¹) * φ v := by rw [h1]
      _ = z⁻¹ := by group
  have hcomm_d : ∀ y : ↥K, φ y ∈ B → (y : G) * d = d * (y : G) := by
    intro y hyB
    have hmemB : φ (v⁻¹ * y * v) ∈ B := by
      have hφ' : φ (v⁻¹ * y * v) = (φ y)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        exact hconj (φ y) (hBP hyB)
      rw [hφ']
      exact B.inv_mem hyB
    have hfix1 : ((v⁻¹ * y * v : ↥K) : G) * e = e * ((v⁻¹ * y * v : ↥K) : G) :=
      hfix (v⁻¹ * y * v) hmemB
    have hXe : Commute ((v : G)⁻¹ * (y : G) * (v : G)) e := by
      show ((v : G)⁻¹ * (y : G) * (v : G)) * e = e * ((v : G)⁻¹ * (y : G) * (v : G))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hfix1
    have hyw : Commute (y : G) ((v : G) * e * (v : G)⁻¹) := by
      simpa only [show (v : G) * ((v : G)⁻¹ * (y : G) * (v : G)) * (v : G)⁻¹ = (y : G)
        by group] using hXe.conj (v : G)
    have hye : Commute (y : G) e := hfix y hyB
    have hde : d = e * ((v : G) * e * (v : G)⁻¹)⁻¹ := by
      rw [hd]; group
    rw [hde]
    exact hye.mul_right hyw.inv_right
  have hd_eq_one : d = 1 := by
    by_contra hd1
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
    set bX : X := (b : X) with hbX
    have hbB : bX ∈ B := b.2
    have hbX1 : bX ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨y, hyφ⟩ := h.surjective bX
    have hy_norm : (y : G) ∈ Subgroup.normalizer (V : Set G) :=
      mem_normalizer_of_commute_ne_one h.isTI hdV hd1 (hcomm_d y (by rw [hyφ]; exact hbB))
    have hyvy : (y : G) * (v : G) * (y : G)⁻¹ ∈ V :=
      ((Subgroup.mem_normalizer_iff.1 hy_norm) (v : G)).1 hvV
    set c : G := (y : G) * (v : G) * (y : G)⁻¹ * (v : G)⁻¹ with hc
    have hcV : c ∈ V := by
      rw [hc]
      exact V.mul_mem hyvy (V.inv_mem hvV)
    let c' : ↥K := ⟨c, h.le_K hcV⟩
    have hc'coe : (c' : G) = c := rfl
    have hc'sq : c' * c' = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one, hc'coe, ← pow_two]
      exact h.elemAbelian_V.2 c hcV
    have hb1' : φ v * bX⁻¹ * (φ v)⁻¹ = bX := by
      have h := hinv bX⁻¹ (P.inv_mem (hBP hbB))
      simpa using h
    have hφc' : φ c' = bX * bX := by
      have hc'coe' : c' = y * v * y⁻¹ * v⁻¹ := by
        apply Subtype.ext
        simp only [hc'coe, hc, Subgroup.coe_mul, Subgroup.coe_inv]
      calc φ c' = φ (y * v * y⁻¹ * v⁻¹) := by rw [hc'coe']
        _ = bX * φ v * bX⁻¹ * (φ v)⁻¹ := by simp only [map_mul, map_inv, hyφ]
        _ = bX * bX := by
              rw [show bX * φ v * bX⁻¹ * (φ v)⁻¹ =
                    bX * (φ v * bX⁻¹ * (φ v)⁻¹) by group, hb1']
    have hφc'sq : (φ c') ^ 2 = 1 := by
      rw [← map_pow, pow_two, hc'sq, map_one]
    have hb4 : bX ^ 4 = 1 := by
      have h := hφc'sq
      rw [hφc'] at h
      have h' : bX ^ 4 = (bX * bX) ^ 2 := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, pow_two]
      rw [h', h]
    have hbdvd : orderOf bX ∣ Nat.gcd 4 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb4)
        (orderOf_dvd_of_pow_eq_one (hPp bX (hBP hbB)))
    have hcop4 : Nat.Coprime 4 p := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      simpa using h2.pow_left 2
    exact hbX1 (orderOf_eq_one_iff.mp (Nat.dvd_one.1 (by
      rw [show Nat.gcd 4 p = 1 from hcop4] at hbdvd
      exact hbdvd)))
  have hconj' : e * (v : G) * e⁻¹ = (v : G) := by
    have h := hd_eq_one
    rw [hd] at h
    exact mul_inv_eq_one.1 (by simpa [mul_assoc] using h)
  calc (v : G) * e = (e * (v : G) * e⁻¹) * e := by rw [hconj']
    _ = e * (v : G) := by rw [mul_assoc, inv_mul_cancel, mul_one]

theorem comm_of_forall_fixed (h : LemmaRHyp V E K φ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup X} (hPa : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 2) {v : ↥K}
    (hv : ∀ B : Subgroup X, B ≤ P → B ≠ ⊥ → ∀ e ∈ E,
      (∀ y : ↥K, φ y ∈ B → (y : G) * e = e * (y : G)) → (v : G) * e = e * (v : G)) :
    ∀ e ∈ E, (v : G) * e = e * (v : G) := by
  let ν : ↥K →* MulAut ↥E :=
    (Subgroup.normalizerMonoidHom E).comp (Subgroup.inclusion h.le_normalizer)
  have hν : ∀ (y : ↥K) (e : ↥E),
      (((ν y) e : ↥E) : G) = (y : G) * (e : G) * (y : G)⁻¹ := fun y e =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E
      (Subgroup.inclusion h.le_normalizer y) e
  have hker : φ.ker ≤ ν.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hν y e, MulAut.one_apply]
    have hc := (Subgroup.mem_centralizer_iff.1 ((h.ker_iff y).1 hy)) (e : G) e.2
    rw [← hc]; group
  let α : X →* MulAut ↥E := (φ.liftOfSurjective h.surjective) ⟨ν, hker⟩
  have hα : ∀ y : ↥K, α (φ y) = ν y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply (f := φ) (f_inv := Function.surjInv h.surjective)
      (hf := Function.rightInverse_surjInv h.surjective) (g := ⟨ν, hker⟩) (x := y)
  let α' : ↥P →* MulAut ↥E := α.comp P.subtype
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by
    rw [hPcard]; exact pow_ne_zero 2 hp.ne_zero)
  haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hPcard]; nlinarith [hp.two_le])
  letI : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with mul_comm := fun a b => hPa.1.is_comm.comm a b }
  haveI : @CFSG.IsElementaryAbelian p ↥P CommGroup.toGroup :=
    { toIsMulCommutative := ⟨⟨mul_comm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hPa.2 (a : P) a.2) }
  have hcop : ¬ p ∣ Nat.card ↥E := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (IsElemAbelian.isPGroup h.elemAbelian_E)
    rw [hm]
    intro hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdiv))
  let C : Subgroup ↥E := (Subgroup.centralizer ({(v : G)} : Set G)).subgroupOf E
  have htop := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top p hp α' hcop
  have hle : (⊤ : Subgroup ↥E) ≤ C := by
    rw [← htop]
    refine iSup₂_le fun B hB => ?_
    intro e he
    have hBne : B ≠ ⊥ := by
      intro hbot
      have h1 : B.index = Nat.card ↥P := by rw [hbot, Subgroup.index_bot]
      rw [hB, hPcard] at h1
      nlinarith [hp.two_le]
    have hB'le : B.map P.subtype ≤ P := Subgroup.map_subtype_le B
    have hB'ne : B.map P.subtype ≠ ⊥ := by
      intro hbot
      exact hBne ((Subgroup.map_eq_bot_iff_of_injective B P.subtype_injective).1 hbot)
    have hfix : ∀ y : ↥K, φ y ∈ B.map P.subtype →
        (y : G) * (e : G) = (e : G) * (y : G) := by
      intro y hy
      obtain ⟨b, hbB, hbφ⟩ := Subgroup.mem_map.1 hy
      have h1 : α' b e = e :=
        (CFSG.SolvableSignalizer.mem_fixedBySubgroup α' B e).1 he b hbB
      have h2 : ν y e = e := by
        have h2' : α (P.subtype b) e = e := h1
        rw [hbφ] at h2'
        rwa [hα y] at h2'
      have h3 : (y : G) * (e : G) * (y : G)⁻¹ = (e : G) := by
        have hh := hν y e
        rw [h2] at hh
        exact hh.symm
      calc (y : G) * (e : G) = (y : G) * (e : G) * (y : G)⁻¹ * (y : G) := by group
        _ = (e : G) * (y : G) := by rw [h3]
    have hcomm := hv (B.map P.subtype) hB'le hB'ne (e : G) e.2 hfix
    have hmem : (e : G) ∈ Subgroup.centralizer ({(v : G)} : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hcomm
    exact Subgroup.mem_subgroupOf.2 hmem
  intro e he
  have hmem : (⟨e, he⟩ : ↥E) ∈ C := hle (Subgroup.mem_top _)
  have hc := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hmem)) (v : G)
    (Set.mem_singleton _)
  simpa using hc

theorem false_of_inverted (h : LemmaRHyp V E K φ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup X} (hPa : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 2) {v : ↥K}
    (hvV : (v : G) ∈ V) (hinv : ∀ x ∈ P, φ v * x * (φ v)⁻¹ = x⁻¹) : False := by
  have hcomm := h.comm_of_forall_fixed hp hp2 hPa hPcard
    (fun B hBP hB e he hfix => h.comm_of_fixed hvV hp hp2 hPa.2 hinv hBP hB he hfix)
  have hφv : φ v = 1 := by
    refine (h.ker_iff v).2 (Subgroup.mem_centralizer_iff.2 fun e he => ?_)
    exact (hcomm e he).symm
  have hPbot : P = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall P).2 fun x hx => ?_
    have h1 := hinv x hx
    rw [hφv, one_mul, inv_one, mul_one] at h1
    have h2 : x * x = 1 := mul_eq_one_iff_eq_inv.2 h1
    have h3 : x ^ 2 = 1 := by rw [pow_two, h2]
    have h4 := hPa.2 x hx
    have hc : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have hdvd : orderOf x ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h4)
    rw [Nat.Coprime.gcd_eq_one hc] at hdvd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  have h1 : Nat.card P = 1 := by
    rw [hPbot]
    exact Subgroup.card_bot
  rw [hPcard] at h1
  have : 1 < p ^ 2 := by nlinarith [hp.two_le]
  omega

end LemmaRHyp

end CFSG.LocalAnalysis.WeakClosure81

end
