module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2Steps

public section

namespace CFSG.Quasithin.SzI47J2Z

open CFSG.Open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI.InvolutionCounting
open CFSG.LieType.BorelTits J2Cz J2Cz.QM

@[expose] def Good (p : QM) : Prop :=
  p * p = 1 ∧ p ≠ 1 ∧
    (phiAHom p * p = J2Cz.QM.z ∨ (phiAHom p * p) * (phiAHom p * p) = J2Cz.QM.z)

instance : DecidablePred Good := fun p => by unfold Good; infer_instance

theorem card_good : Nat.card {p : QM // Good p} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pow_four_eq_one : ∀ c : QM, c ^ 4 = 1 := by decide +kernel

theorem eq_z_or_sq_eq_z : ∀ c : QM, ∀ k : Fin 4, c ^ (k : ℕ) = J2Cz.QM.z →
    c = J2Cz.QM.z ∨ c * c = J2Cz.QM.z := by decide +kernel

theorem eq_z_or_sq_eq_z_of_pow_eq (c : QM) (m : ℕ) (h : c ^ m = J2Cz.QM.z) :
    c = J2Cz.QM.z ∨ c * c = J2Cz.QM.z := by
  have h1 : c ^ m = c ^ (m % 4) := by
    calc c ^ m = c ^ (4 * (m / 4) + m % 4) := by rw [Nat.div_add_mod]
      _ = c ^ (m % 4) := by rw [pow_add, pow_mul, pow_four_eq_one, one_pow, one_mul]
  rw [h1] at h
  exact eq_z_or_sq_eq_z c ⟨m % 4, Nat.mod_lt _ (by norm_num)⟩ h

variable {G : Type} [Group G] {z : G} (F : J2Frame G z)

theorem sq_t_mul_emb (p : QM) :
    (F.t * F.emb p) * (F.t * F.emb p) = F.emb (phiAHom p * p) := by
  have h1 := F.conj_emb ⟨F.t, F.t_mem_centralizer⟩ p
  rw [F.czAct_t] at h1
  have h2 : F.t * F.emb p * F.t⁻¹ = F.emb (phiAHom p) := h1
  calc F.t * F.emb p * (F.t * F.emb p)
      = (F.t * F.emb p * F.t⁻¹) * (F.t * F.t) * F.emb p := by group
    _ = F.emb (phiAHom p) * 1 * F.emb p := by rw [h2, F.t_mul_t]
    _ = F.emb (phiAHom p * p) := by rw [map_mul, mul_one]

theorem mem_centralizer_of_mem_pairs {p : G × G} (hp : p ∈ thompsonPairs F.t z z) :
    p.1 ∈ Subgroup.centralizer ({z} : Set G) ∧ p.2 ∈ Subgroup.centralizer ({z} : Set G) :=
  mem_centralizer_of_mem_thompsonPairs F.t_mul_t
    (by rw [← pow_two]; exact F.isTypeH2.sq) (by rw [← pow_two]; exact F.isTypeH2.sq) hp

@[expose] def invOutside (z : G) : Set G :=
  {a | a ∈ Subgroup.centralizer ({z} : Set G) ∧ a * a = 1 ∧
    a ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))}

@[expose] def fib (a : G) : Set G := {b | (a, b) ∈ thompsonPairs F.t z z}

theorem mem_fib {a b : G} :
    b ∈ fib F a ↔ IsConj F.t a ∧ IsConj z b ∧ z ∈ Subgroup.zpowers (a * b) :=
  Iff.rfl

theorem mem_fib_conj {h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G)) (a b : G) :
    h * b * h⁻¹ ∈ fib F (h * a * h⁻¹) ↔ b ∈ fib F a := by
  have hz : h * z * h⁻¹ = z := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hh
    calc h * z * h⁻¹ = z * h * h⁻¹ := by rw [h1]
      _ = z := by group
  have key := conj_mem_thompsonPairs_iff (u := F.t) (z := z) (w := z) h (p := (a, b))
  rw [hz] at key
  exact key

theorem exists_conj_t {a : G} (ha : a ∈ invOutside z) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G), h * F.t * h⁻¹ = a := by
  obtain ⟨haH, ha2, haQ⟩ := ha
  obtain ⟨g, hgH, hg⟩ := F.exists_conj_eq_t haH ha2 haQ
  refine ⟨g⁻¹, Subgroup.inv_mem _ hgH, ?_⟩
  calc g⁻¹ * F.t * g⁻¹⁻¹ = g⁻¹ * (g * a * g⁻¹) * g := by rw [hg]; group
    _ = a := by group

@[expose] noncomputable def lc : Fin 4 → G
  | 0 => 1
  | 1 => F.t
  | 2 => F.a
  | 3 => F.t * F.a

theorem lc_mem_L (i : Fin 4) : lc F i ∈ F.L := by
  fin_cases i
  · exact F.L.one_mem
  · exact F.t_mem_L
  · exact F.a_mem_L
  · exact F.L.mul_mem F.t_mem_L F.a_mem_L

theorem lc_mem_X (i : Fin 4) : lc F i ∈ F.X := by
  fin_cases i
  · exact F.X.one_mem
  · exact F.t_mem_X
  · exact F.a_mem_X
  · exact F.X.mul_mem F.t_mem_X F.a_mem_X

theorem lc_injective : Function.Injective (lc F) := by
  have d01 : (1 : G) ≠ F.t := F.t_ne_one.symm
  have d02 : (1 : G) ≠ F.a := F.a_ne_one.symm
  have d03 : (1 : G) ≠ F.t * F.a := F.ta_ne_one.symm
  have d12 : F.t ≠ F.a := fun h => F.ta_ne_one (by rw [← h]; exact F.t_mul_t)
  have d13 : F.t ≠ F.t * F.a := fun h => F.a_ne_one
    (mul_left_cancel (a := F.t) (b := F.a) (c := 1) (by rw [mul_one]; exact h.symm))
  have d23 : F.a ≠ F.t * F.a := fun h => F.t_ne_one
    (mul_right_cancel (a := F.t) (b := F.a) (c := 1) (by rw [one_mul]; exact h.symm))
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h ‹_› | exact absurd h.symm ‹_›

variable [Finite G]

theorem card_T : Nat.card F.T = 16 := by
  refine le_antisymm F.card_T_le ?_
  have hlT : ∀ i, lc F i ∈ F.T := fun i => ⟨lc_mem_X F i, F.le (lc_mem_L F i)⟩
  let φ : Fin 4 × ↥F.W → ↥F.T := fun q =>
    ⟨lc F q.1 * q.2, F.T.mul_mem (hlT q.1) (F.W_le_T q.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, ⟨w, hw⟩⟩ ⟨j, ⟨w', hw'⟩⟩ h
    have h1 : lc F i * w = lc F j * w' := congrArg Subtype.val h
    have h2 : (lc F j)⁻¹ * lc F i = w' * w⁻¹ := by
      calc (lc F j)⁻¹ * lc F i = (lc F j)⁻¹ * (lc F i * w) * w⁻¹ := by group
        _ = (lc F j)⁻¹ * (lc F j * w') * w⁻¹ := by rw [h1]
        _ = w' * w⁻¹ := by group
    have h3 : (lc F j)⁻¹ * lc F i = 1 := F.eq_one_of_mem_L_of_mem_Q
      (F.L.mul_mem (F.L.inv_mem (lc_mem_L F j)) (lc_mem_L F i))
      (h2 ▸ Subgroup.mul_mem _ hw'.2 (Subgroup.inv_mem _ hw.2))
    have hij : i = j := lc_injective F (inv_mul_eq_one.mp h3).symm
    subst hij
    have hww : w = w' := mul_left_cancel h1
    subst hww
    rfl
  have h1 := Nat.card_le_card_of_injective φ hinj
  rwa [Nat.card_prod, Nat.card_fin, F.card_W] at h1

theorem isConj_t_iff (hcount : involutionClassCount G = 2) {a : G}
    (haH : a ∈ Subgroup.centralizer ({z} : Set G)) :
    IsConj F.t a ↔ (a * a = 1 ∧ a ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := by
  constructor
  · intro h
    have ha2 : a * a = 1 := mul_self_eq_one_of_isConj F.t_mul_t h
    refine ⟨ha2, fun haQ => ?_⟩
    have ha1 : a ≠ 1 := fun h1 => F.t_ne_one (isConj_one_right.mp (by rw [h1] at h; exact h.symm))
    exact F.not_isConj_t hcount ((F.isTypeH2.isConj_of_mem_pCoreOf haQ ha2 ha1).trans h.symm)
  · rintro ⟨ha2, haQ⟩
    obtain ⟨g, -, hg⟩ := F.exists_conj_eq_t haH ha2 haQ
    exact isConj_iff.mpr ⟨g⁻¹, by rw [← hg]; group⟩

include F in
theorem isConj_z_iff (hcount : involutionClassCount G = 2) {b : G}
    (hbH : b ∈ Subgroup.centralizer ({z} : Set G)) :
    IsConj z b ↔ (b ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ b * b = 1 ∧ b ≠ 1) := by
  have hz2 : z * z = 1 := by rw [← pow_two]; exact F.isTypeH2.sq
  constructor
  · intro h
    have hb2 : b * b = 1 := mul_self_eq_one_of_isConj hz2 h
    have hb1 : b ≠ 1 := fun h1 => F.isTypeH2.ne_one (isConj_one_right.mp (by
      rw [h1] at h; exact h.symm))
    refine ⟨?_, hb2, hb1⟩
    by_contra hbQ
    exact F.not_isConj_t hcount (h.trans ((isConj_t_iff F hcount hbH).mpr ⟨hb2, hbQ⟩).symm)
  · rintro ⟨hbQ, hb2, hb1⟩
    exact F.isTypeH2.isConj_of_mem_pCoreOf hbQ hb2 hb1

theorem z_mem_zpowers_iff (p : QM) :
    z ∈ Subgroup.zpowers (F.t * F.emb p) ↔
      (phiAHom p * p = J2Cz.QM.z ∨ (phiAHom p * p) * (phiAHom p * p) = J2Cz.QM.z) := by
  set g := F.t * F.emb p with hg
  set c := phiAHom p * p with hc
  have hg2 : g * g = F.emb c := sq_t_mul_emb F p
  have hg2' : g ^ 2 = F.emb c := by rw [pow_two]; exact hg2
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have h1 : F.emb (c ^ m) = F.emb J2Cz.QM.z := by
        rw [map_pow, ← hg2', ← pow_mul, F.emb_z]
        exact hn
      exact eq_z_or_sq_eq_z_of_pow_eq c m (F.emb_injective h1)
    · exfalso
      have h1 : F.emb (c ^ m) * (F.t * F.emb p) = z := by
        calc F.emb (c ^ m) * (F.t * F.emb p) = g ^ (2 * m) * g := by
              rw [map_pow, ← hg2', ← pow_mul]
          _ = g ^ (2 * m + 1) := (pow_succ g (2 * m)).symm
          _ = z := hn
      have h2 : F.t = (F.emb (c ^ m))⁻¹ * z * (F.emb p)⁻¹ := by
        calc F.t = (F.emb (c ^ m))⁻¹ * (F.emb (c ^ m) * (F.t * F.emb p)) * (F.emb p)⁻¹ := by
              group
          _ = _ := by rw [h1]
      apply F.t_not_mem_Q
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (F.emb_mem _))
        F.isTypeH2.z_mem_pCoreOf) (Subgroup.inv_mem _ (F.emb_mem _))
  · intro h
    rcases h with h | h
    · have h1 : z = g ^ 2 := by rw [hg2', h, F.emb_z]
      rw [h1]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2
    · have h1 : z = g ^ 2 * g ^ 2 := by rw [hg2', ← map_mul, h, F.emb_z]
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2)

theorem fst_mem_invOutside (hcount : involutionClassCount G = 2) {p : G × G}
    (hp : p ∈ thompsonPairs F.t z z) : p.1 ∈ invOutside z := by
  have hH := (mem_centralizer_of_mem_pairs F hp).1
  have h := (isConj_t_iff F hcount hH).mp hp.1
  exact ⟨hH, h.1, h.2⟩

theorem fib_t_eq (hcount : involutionClassCount G = 2) :
    fib F F.t = F.emb '' {p : QM | Good p} := by
  ext b
  constructor
  · intro hb
    have hbH := (mem_centralizer_of_mem_pairs F hb).2
    obtain ⟨hbQ, hb2, hb1⟩ := (isConj_z_iff F hcount hbH).mp ((mem_fib F).mp hb).2.1
    obtain ⟨p, rfl⟩ := F.exists_emb_eq hbQ
    refine ⟨p, ⟨?_, ?_, (z_mem_zpowers_iff F p).mp ((mem_fib F).mp hb).2.2⟩, rfl⟩
    · apply F.emb_injective
      rw [map_mul, map_one]
      exact hb2
    · rintro rfl
      exact hb1 (map_one _)
  · rintro ⟨p, ⟨hp2, hp1, hp3⟩, rfl⟩
    have hbQ := F.emb_mem p
    have hbH := pCoreOf_le 2 _ hbQ
    refine (mem_fib F).mpr ⟨IsConj.refl _, (isConj_z_iff F hcount hbH).mpr ⟨hbQ, ?_, ?_⟩,
      (z_mem_zpowers_iff F p).mpr hp3⟩
    · rw [← map_mul, hp2, map_one]
    · intro h1
      exact hp1 (F.emb_injective (h1.trans (map_one F.emb).symm))

theorem card_fib_t (hcount : involutionClassCount G = 2) : Nat.card (fib F F.t) = 8 := by
  rw [fib_t_eq F hcount, Nat.card_image_of_injective F.emb_injective]
  exact card_good

theorem card_fib (hcount : involutionClassCount G = 2) {a : G} (ha : a ∈ invOutside z) :
    Nat.card (fib F a) = 8 := by
  obtain ⟨h, hh, rfl⟩ := exists_conj_t F ha
  have e : ↥(fib F F.t) ≃ ↥(fib F (h * F.t * h⁻¹)) :=
    (MulAut.conj h).toEquiv.subtypeEquiv (fun b => (mem_fib_conj F hh F.t b).symm)
  rw [← Nat.card_congr e]
  exact card_fib_t F hcount

include F in
theorem card_invOutside : Nat.card (invOutside z) = 120 := by
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) with hH
  set t' : ↥H := ⟨F.t, F.t_mem_centralizer⟩ with ht'
  have h1 := card_centralizer_mul_card_conjugatesOf t'
  have hX : ∀ c : ↥(Subgroup.centralizer ({t'} : Set ↥H)), ((c : ↥H) : G) ∈ F.X := fun c => by
    rw [F.mem_X]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hX' : ∀ s : ↥F.T, (⟨(s : G), s.2.2⟩ : ↥H) ∈ Subgroup.centralizer ({t'} : Set ↥H) := fun s =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (F.mem_X.mp s.2.1))
  have hT : Nat.card ↥(Subgroup.centralizer ({t'} : Set ↥H)) = 16 := by
    rw [← card_T F]
    exact Nat.card_congr
      { toFun := fun c => ⟨((c : ↥H) : G), hX c, (c : ↥H).2⟩
        invFun := fun s => ⟨⟨(s : G), s.2.2⟩, hX' s⟩
        left_inv := fun c => rfl
        right_inv := fun s => rfl }
  have hH1920 : Nat.card ↥H = 1920 := F.isTypeH2.card_centralizer
  rw [hT, hH1920] at h1
  have h2 : Nat.card ↥(_root_.conjugatesOf t') = 120 := by omega
  have h3 : invOutside z = Subtype.val '' _root_.conjugatesOf t' := by
    ext a
    constructor
    · intro ha
      obtain ⟨h, hh, hha⟩ := exists_conj_t F ha
      exact ⟨⟨a, ha.1⟩, isConj_iff.mpr ⟨⟨h, hh⟩, Subtype.ext hha⟩, rfl⟩
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp ha'
      have hc' : (c : G) * F.t * (c : G)⁻¹ = (a' : G) := congrArg Subtype.val hc
      refine ⟨a'.2, ?_, fun haQ => F.t_not_mem_Q ?_⟩
      · rw [← hc']
        calc (c : G) * F.t * (c : G)⁻¹ * ((c : G) * F.t * (c : G)⁻¹)
            = (c : G) * (F.t * F.t) * (c : G)⁻¹ := by group
          _ = 1 := by rw [F.t_mul_t]; group
      · have hn := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H c.2)) F.t
        exact hn.mpr (by rw [hc']; exact haQ)
  rw [h3, Nat.card_image_of_injective Subtype.val_injective]
  exact h2

theorem card_pairs (hcount : involutionClassCount G = 2) :
    Nat.card (thompsonPairs F.t z z) = 960 := by
  have : Fintype ↥(invOutside z) := Fintype.ofFinite _
  let e : ↥(thompsonPairs F.t z z) ≃ Σ a : ↥(invOutside z), ↥(fib F a) :=
    { toFun := fun p => ⟨⟨p.1.1, fst_mem_invOutside F hcount p.2⟩, ⟨p.1.2, p.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have h8 : ∀ a : ↥(invOutside z), Nat.card ↥(fib F a) = 8 := fun a => card_fib F hcount a.2
  simp only [h8, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_invOutside F]

end CFSG.Quasithin.SzI47J2Z

namespace CFSG.Quasithin

theorem j2PairCountZ_holds : J2PairCountZ := fun _ _ _ _ hcount F =>
  SzI47J2Z.card_pairs F hcount

end CFSG.Quasithin
