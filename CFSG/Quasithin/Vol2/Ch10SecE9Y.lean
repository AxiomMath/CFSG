module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecQ34LK

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_eq {W : Subgroup G} {n c : G} (hc : c ∈ Subgroup.normalizer (W : Set G))
    (h : ∀ w ∈ W, n * w * n⁻¹ = c * w * c⁻¹) :
    ∀ k : ℕ, ∀ w ∈ W, n ^ k * w * (n ^ k)⁻¹ = c ^ k * w * (c ^ k)⁻¹ := by
  intro k
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    have hcw : c * w * c⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hc w).mp hw
    calc n ^ (k + 1) * w * (n ^ (k + 1))⁻¹ = n ^ k * (n * w * n⁻¹) * (n ^ k)⁻¹ := by group
      _ = n ^ k * (c * w * c⁻¹) * (n ^ k)⁻¹ := by rw [h w hw]
      _ = c ^ k * (c * w * c⁻¹) * (c ^ k)⁻¹ := ih _ hcw
      _ = c ^ (k + 1) * w * (c ^ (k + 1))⁻¹ := by group

theorem exists_acts_of_odd {N M W : Subgroup G} (hNW : N ≤ Subgroup.normalizer (W : Set G))
    (hcop : ∀ d ∈ N, Nat.Coprime (orderOf d) 6 → d ∈ M)
    (hwit : ∀ n ∈ N, Odd (orderOf n) →
      ∃ y ∈ N, y ∈ Subgroup.centralizer (W : Set G) ∧ ¬ 3 ∣ orderOf (n * y⁻¹))
    {n : G} (hn : n ∈ N) (hodd : Odd (orderOf n)) :
    ∃ m ∈ N ⊓ M, ∀ w ∈ W, n * w * n⁻¹ = m * w * m⁻¹ := by
  obtain ⟨y, hyN, hyW, h3⟩ := hwit n hn hodd
  set c := n * y⁻¹ with hc
  have hcN : c ∈ N := N.mul_mem hn (N.inv_mem hyN)
  have hnc : ∀ w ∈ W, n * w * n⁻¹ = c * w * c⁻¹ := by
    intro w hw
    have h1 := Subgroup.mem_centralizer_iff.mp hyW w hw
    have h2 : y⁻¹ * w * y = w := by
      rw [mul_assoc, h1]; group
    rw [hc, show n * y⁻¹ * w * (n * y⁻¹)⁻¹ = n * (y⁻¹ * w * y) * n⁻¹ by group, h2]
  obtain ⟨a, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hkd : 2 ^ a ∣ orderOf c := ⟨r, hor⟩
  have hdo : orderOf (c ^ 2 ^ a) = r := by
    rw [orderOf_pow' c (pow_ne_zero a two_ne_zero), Nat.gcd_eq_right hkd, hor,
      Nat.mul_div_cancel_left r (pow_pos two_pos a)]
  have hd6 : Nat.Coprime (orderOf (c ^ 2 ^ a)) 6 := by
    rw [hdo, show (6 : ℕ) = 2 * 3 by norm_num]
    refine Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hr) ?_
    have hrd : r ∣ orderOf c := ⟨2 ^ a, by rw [hor, mul_comm]⟩
    exact Nat.Coprime.coprime_dvd_left hrd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have hdM : c ^ 2 ^ a ∈ M := hcop _ (N.pow_mem hcN _) hd6
  set m₀ := orderOf n with hm₀
  rcases Nat.lt_or_ge 1 m₀ with h1 | h1
  · have hcopk : Nat.Coprime (2 ^ a) m₀ :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopk h1
    refine ⟨(c ^ 2 ^ a) ^ e, ⟨N.pow_mem (N.pow_mem hcN _) e, M.pow_mem hdM e⟩, fun w hw => ?_⟩
    have hne : n ^ (2 ^ a * e) = n := by
      rw [← pow_mod_orderOf, ← hm₀, he, pow_one]
    rw [← pow_mul, ← conj_pow_eq (hNW hcN) hnc (2 ^ a * e) w hw, hne]
  · have hn1 : n = 1 := by
      have h0 : m₀ ≠ 0 := (orderOf_pos n).ne'
      exact orderOf_eq_one_iff.mp (by omega)
    exact ⟨1, ⟨N.one_mem, M.one_mem⟩, fun w _ => by rw [hn1]⟩

theorem exists_acts_all {N M W T : Subgroup G} (hNW : N ≤ Subgroup.normalizer (W : Set G))
    (hTM : T ≤ M) (hTsyl : IsSylowTwoOf T N)
    (hodd : ∀ n ∈ N, Odd (orderOf n) → ∃ m ∈ N ⊓ M, ∀ w ∈ W, n * w * n⁻¹ = m * w * m⁻¹)
    {g : G} (hg : g ∈ N) : ∃ m ∈ N ⊓ M, ∀ w ∈ W, g * w * g⁻¹ = m * w * m⁻¹ := by
  let H₀ : Subgroup G :=
    { carrier := {g | g ∈ N ∧ ∃ m ∈ N ⊓ M, ∀ w ∈ W, g * w * g⁻¹ = m * w * m⁻¹}
      one_mem' := ⟨N.one_mem, 1, ⟨N.one_mem, M.one_mem⟩, fun _ _ => rfl⟩
      mul_mem' := by
        rintro a b ⟨haN, ma, hma, ha⟩ ⟨hbN, mb, hmb, hb⟩
        refine ⟨N.mul_mem haN hbN, ma * mb, ⟨N.mul_mem hma.1 hmb.1, M.mul_mem hma.2 hmb.2⟩,
          fun w hw => ?_⟩
        have hbw : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hNW hbN) w).mp hw
        calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
          _ = ma * (b * w * b⁻¹) * ma⁻¹ := ha _ hbw
          _ = ma * (mb * w * mb⁻¹) * ma⁻¹ := by rw [hb w hw]
          _ = ma * mb * w * (ma * mb)⁻¹ := by group
      inv_mem' := by
        rintro a ⟨haN, ma, hma, ha⟩
        refine ⟨N.inv_mem haN, ma⁻¹, ⟨N.inv_mem hma.1, M.inv_mem hma.2⟩, fun w hw => ?_⟩
        have haw : a⁻¹ * w * a ∈ W := by
          have := (Subgroup.mem_normalizer_iff.mp (hNW (N.inv_mem haN)) w).mp hw
          simpa using this
        have h1 := ha _ haw
        rw [show a * (a⁻¹ * w * a) * a⁻¹ = w by group] at h1
        calc a⁻¹ * w * a⁻¹⁻¹ = ma⁻¹ * (ma * (a⁻¹ * w * a) * ma⁻¹) * ma := by group
          _ = ma⁻¹ * w * ma⁻¹⁻¹ := by rw [← h1]; group }
  have hle : N ≤ H₀ := by
    refine (C10P34.le_oTwoUpper_sup hTsyl).trans (sup_le ?_ fun τ hτ => ?_)
    · refine (Subgroup.closure_le _).mpr fun n hn => ?_
      exact ⟨hn.1, hodd n hn.1 hn.2⟩
    · exact ⟨hTsyl.1 hτ, τ, ⟨hTsyl.1 hτ, hTM hτ⟩, fun _ _ => rfl⟩
  exact (hle hg).2

variable {T L I : Subgroup G}

theorem conjugate_fsuUL_of_not_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t τ : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (hτ : τ ∈ T)
    (hτn : τ ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate (fsuUL T L I) τ = CFSG.conjugate (fsuUL T L I) t ∧
      CFSG.conjugate (CFSG.conjugate (fsuUL T L I) t) τ = fsuUL T L I := by
  have hLτ : CFSG.conjugate L τ = CFSG.conjugate L t :=
    (SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hτ)).resolve_left
      (fun h => hτn (SecA.conjugate_eq_self_iff.mp h))
  have htτ : t * τ ∈ Subgroup.normalizer (L : Set G) := by
    have h2 := SecA.index_T1 h37 h38 hyp
    have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨t, ht⟩) (b := ⟨τ, hτ⟩)).mpr
      (iff_of_false (fun h => htn (Subgroup.mem_subgroupOf.mp h).2)
        (fun h => hτn (Subgroup.mem_subgroupOf.mp h).2))
    exact (Subgroup.mem_subgroupOf.mp h3).2
  constructor
  · rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L hτ), hLτ,
      ← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
  · rw [SecA.conjugate_conjugate, SecA.conjugate_commutator_fsuVM
      (Subgroup.mul_mem _ (SecA.le_fsuM T L ht) (SecA.le_fsuM T L hτ)),
      SecA.conjugate_eq_self_iff.mpr htτ]

theorem isSylowTwoOf_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (hC0 : fsuCVM T L I = ⊥)
    {W : Subgroup G}
    (hact : ∀ g ∈ Subgroup.normalizer (T1 T L : Set G),
      ∃ m ∈ Subgroup.normalizer (T1 T L : Set G) ⊓ fsuM T L,
        ∀ w ∈ W, g * w * g⁻¹ = m * w * m⁻¹)
    {v : G} (hv : v ∈ fsuUL T L I) (hv1 : v ≠ 1) (hvW : v ∈ W)
    (hvT : T1 T L ≤ Subgroup.centralizer ({v} : Set G)) :
    IsSylowTwoOf (T1 T L) (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hT1p : IsPGroup 2 ↥(T1 T L) := hyp.fsu.sylow.1.to_le inf_le_left
  obtain ⟨S, hT1S, hS⟩ := exists_isSylowTwoOf_of_le hvT hT1p
  by_contra hns
  have hlt : T1 T L < S := lt_of_le_of_ne hT1S fun h => hns (h ▸ hS)
  obtain ⟨x, hxS, hxT1, hxN⟩ := exists_mem_normalizer_not_mem_of_lt hS.isPGroup hlt
  have hTN := T1_normal h37 h38 hyp
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
    ⟨hTN, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTN⟩
  have hxp : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hS.isPGroup.to_le (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨S', hxS', hS'⟩ := exists_isSylowTwoOf_of_le (Subgroup.zpowers_le.mpr hxN) hxp
  obtain ⟨h, hhN, hS'eq⟩ := hTsyl.exists_conj hS'
  set g := h⁻¹ with hg
  have hgN : g ∈ Subgroup.normalizer (T1 T L : Set G) := Subgroup.inv_mem _ hhN
  have hτ : g * x * g⁻¹ ∈ T := by
    have h1 := hxS' (Subgroup.mem_zpowers x)
    rw [hS'eq, Subgroup.mem_map] at h1
    obtain ⟨τ₀, hτ₀, hτ₀x⟩ := h1
    have e : τ₀ = g * x * g⁻¹ := by
      rw [hg, ← hτ₀x]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    exact e ▸ hτ₀
  have hτn : g * x * g⁻¹ ∉ Subgroup.normalizer (L : Set G) := by
    intro h
    apply hxT1
    have h1 : g * x * g⁻¹ ∈ T1 T L := ⟨hτ, h⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp h1
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2
    exact h2
  have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hxS)
  obtain ⟨m, hm, hmv⟩ := hact g hgN
  set u := g * v * g⁻¹ with hu
  have hτu : (g * x * g⁻¹) * u * (g * x * g⁻¹)⁻¹ = u := by
    rw [hu, show g * x * g⁻¹ * (g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * v) * x⁻¹ * g⁻¹ by group,
      hxv]
    group
  have hum : u = m * v * m⁻¹ := hmv v hvW
  have hmM : m⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem hm.2
  have huV : u ∈ CFSG.conjugate (fsuUL T L I) m⁻¹ := by
    rw [SecA.mem_conjugate_iff, hum, show m⁻¹ * (m * v * m⁻¹) * m⁻¹⁻¹ = v by group]
    exact hv
  rw [SecA.conjugate_commutator_fsuVM hmM] at huV
  obtain ⟨hV1, hV2⟩ := conjugate_fsuUL_of_not_mem h37 h38 hyp ht htn hτ hτn
  have hcap : u ∈ fsuUL T L I ⊓ CFSG.conjugate (fsuUL T L I) t := by
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hmM with h1 | h1
    · rw [h1] at huV
      refine ⟨huV, ?_⟩
      rw [← hV1]
      exact SecA.mem_conjugate_iff.mpr (hτu.symm ▸ huV)
    · rw [h1, ← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)] at huV
      refine ⟨?_, huV⟩
      rw [← hV2]
      exact SecA.mem_conjugate_iff.mpr (hτu.symm ▸ huV)
  have h0 := SecA.inf_conjugate_le_fsuCVM hyp ht htn hcap
  rw [hC0, Subgroup.mem_bot, hu] at h0
  apply hv1
  have := congrArg (fun z => g⁻¹ * z * g) h0
  simp only [mul_one, inv_mul_cancel] at this
  rw [← this]
  group

end CFSG.Quasithin.Vol2.Ch10.SecB
