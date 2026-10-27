module

public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofA7
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Frattini

variable {K : Type} [Group K] [Finite K]

theorem exists_mem_sup_mul_mem_normalizer {p : ℕ} [hp : Fact p.Prime] {N : Subgroup K}
    [N.Normal] (hN : ¬ p ∣ Nat.card N) {E : Subgroup K} (hE : IsPGroup p E) {k₀ : K}
    (hk : E.map (MulAut.conj k₀).toMonoidHom ≤ E ⊔ N) :
    ∃ m ∈ E ⊔ N, m⁻¹ * k₀ ∈ Subgroup.normalizer (E : Set K) := by
  set M := E ⊔ N with hMdef
  set E' := E.map (MulAut.conj k₀).toMonoidHom with hE'def
  have hE'c : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj k₀).injective
  have hdisj : N ⊓ E = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 : Nat.card ↥(N ⊓ E) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk⟩ := (hE.to_le (inf_le_right : N ⊓ E ≤ E)).exists_card_eq
    rcases k with _ | k
    · simpa using hk
    · exfalso
      apply hN
      rw [hk] at h1
      exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans h1
  have hM : Nat.card M = Nat.card E * Nat.card N := by
    have h1 := Subgroup.relIndex_mul_card N M
    have h2 : N.relIndex M = N.relIndex E := Subgroup.relIndex_sup_right E N
    have h3 := Subgroup.relIndex_mul_card N E
    rw [hdisj, Subgroup.card_bot, mul_one] at h3
    rw [inf_of_le_left le_sup_right, h2, h3] at h1
    exact h1.symm
  obtain ⟨k, hk'⟩ := hE.exists_card_eq
  have hfac : (Nat.card M).factorization p = k := by
    rw [hM, hk', Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) Nat.card_pos.ne',
      Nat.Prime.factorization_pow hp.out, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hN, add_zero]
  have hEM : Nat.card (E.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hk', hfac]
  have hE'M : Nat.card (E'.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hk).toEquiv, hE'c, hk', hfac]
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) (Sylow.ofCard _ hEM) (Sylow.ofCard _ hE'M)
  have hm' : E'.subgroupOf M = (E.subgroupOf M).map (MulAut.conj m).toMonoidHom := by
    have := congrArg (fun S : Sylow p M => (S : Subgroup M)) hm
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
    rw [← this, Subgroup.pointwise_smul_def]
    rfl
  have hE'eq : E' = E.map (MulAut.conj (m : K)).toMonoidHom := by
    have h1 : E' = (E'.subgroupOf M).map M.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hk]
    have h2 : E = (E.subgroupOf M).map M.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left le_sup_left]
    rw [h1, hm', Subgroup.map_map]
    conv_rhs => rw [h2, Subgroup.map_map]
    congr 1
  refine ⟨m, m.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : k₀ * x * k₀⁻¹ ∈ E' := ⟨x, hx, rfl⟩
    rw [hE'eq] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : (m : K) * y * (m : K)⁻¹ = k₀ * x * k₀⁻¹ := hyx
    have : (m : K)⁻¹ * k₀ * x * ((m : K)⁻¹ * k₀)⁻¹ = y := by
      calc (m : K)⁻¹ * k₀ * x * ((m : K)⁻¹ * k₀)⁻¹
          = (m : K)⁻¹ * (k₀ * x * k₀⁻¹) * (m : K) := by group
        _ = (m : K)⁻¹ * ((m : K) * y * (m : K)⁻¹) * (m : K) := by rw [hyx']
        _ = y := by group
    rw [this]
    exact hy
  · intro hx
    have hmem : (m : K) * ((m : K)⁻¹ * k₀ * x * ((m : K)⁻¹ * k₀)⁻¹) * (m : K)⁻¹ ∈ E' := by
      rw [hE'eq]
      exact ⟨_, hx, rfl⟩
    have heq : (m : K) * ((m : K)⁻¹ * k₀ * x * ((m : K)⁻¹ * k₀)⁻¹) * (m : K)⁻¹ =
        k₀ * x * k₀⁻¹ := by group
    rw [heq] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : k₀ * y * k₀⁻¹ = k₀ * x * k₀⁻¹ := hyx
    have : y = x := by
      have := congrArg (fun z => k₀⁻¹ * z * k₀) hyx'
      simpa [mul_assoc] using this
    rw [← this]
    exact hy

omit [Finite K] in
theorem conj_pow_eq_of_conj_eq {E : Subgroup K} {u v : K}
    (h : ∀ y ∈ E, u * y * u⁻¹ = v * y * v⁻¹) (hv : ∀ y ∈ E, v * y * v⁻¹ ∈ E) :
    ∀ n : ℕ, ∀ y ∈ E, u ^ n * y * (u ^ n)⁻¹ = v ^ n * y * (v ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    calc u ^ (n + 1) * y * (u ^ (n + 1))⁻¹ = u ^ n * (u * y * u⁻¹) * (u ^ n)⁻¹ := by group
      _ = u ^ n * (v * y * v⁻¹) * (u ^ n)⁻¹ := by rw [h y hy]
      _ = v ^ n * (v * y * v⁻¹) * (v ^ n)⁻¹ := ih _ (hv y hy)
      _ = v ^ (n + 1) * y * (v ^ (n + 1))⁻¹ := by group

end Frattini

section J2

variable {X : Type} [Group X] [Finite X]

theorem j2_card_normalizer_center (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) :
    Nat.card (Subgroup.normalizer
      (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
        Set X)) = 2160 := by
  obtain ⟨-, -, ⟨-, -, ⟨eN⟩⟩, -⟩ := h415 X hX P _ rfl _ rfl
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3 : Nat.card Z = 3 := (Sec14.j2_sylow_facts h415 hX P).1
  have hPGL : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2)) = 720 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.GorensteinWalter.pgl2_card_formula (GaloisField 3 2)
    rw [GaloisField.card 3 2 (by norm_num)] at h
    rw [h]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Z.subgroupOf (Subgroup.normalizer (Z : Set X))), Nat.card_congr eN.toEquiv, hPGL,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hZ3]

theorem j2_card_normalizer_le (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {W : Subgroup X}
    (hW : Nat.card W = 3) : Nat.card (Subgroup.normalizer (W : Set X)) ≤ 2160 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW, pow_one])
  obtain ⟨P, hWP⟩ := hW3.exists_le_sylow
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3 : Nat.card Z = 3 := (Sec14.j2_sylow_facts h415 hX P).1
  by_cases hWZ : W = Z
  · rw [hWZ, j2_card_normalizer_center h415 hX P]
  obtain ⟨a, haW, haZ⟩ : ∃ a ∈ W, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact hWZ (Subgroup.eq_of_le_of_card_ge hcon (by rw [hW, hZ3]))
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have ha3 : a ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨a, haW⟩ : W))
    rw [hW] at h
    exact congrArg Subtype.val h
  have hWa : W = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haW) ?_).symm
    rw [hW, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have haC : a ∈ Subgroup.centralizer (Z : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 a (hWP haW)).symm
  set A := Subgroup.zpowers a ⊔ Z with hAdef
  have hAP : A ≤ P := sup_le (Subgroup.zpowers_le.mpr (hWP haW)) inf_le_left
  have haA : a ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hA9 : Nat.card A = 9 := by
    rw [KFacts.KS14.card_eq_three_mul_card_inf haC haZ ha3 le_rfl haA,
      inf_of_le_right le_sup_right, hZ3]
  obtain ⟨-, ⟨e⟩, -⟩ := (h415 X hX P Z rfl _ rfl).2.2.2.1 A ⟨hAP, hA9⟩ a haA haZ
  rw [hWa, Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_perm, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem j2_pow_six_conj (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup X}
    (hE : Nat.card E = 9) {g : X} (hg : g ∈ Subgroup.normalizer (E : Set X)) {e : X}
    (he : e ∈ E) : g ^ 6 * e * (g ^ 6)⁻¹ = e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3 : Nat.card Z = 3 := (Sec14.j2_sylow_facts h415 hX P).1
  obtain ⟨a, haE, haZ⟩ : ∃ a ∈ E, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le hcon
    omega
  obtain ⟨⟨eAut⟩, -⟩ := (h415 X hX P Z rfl _ rfl).2.2.2.1 E ⟨hEP, hE⟩ a haE haZ
  have h6 : Nat.card (Sec4.autIn ⊤ E) = 6 := by
    rw [Nat.card_congr eAut.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  set σ := E.normalizerMonoidHom ⟨g, hg⟩ with hσdef
  have hσ : σ ∈ Sec4.autIn ⊤ E := Sec4.mem_autIn_iff.mpr ⟨g, hg, Subgroup.mem_top g, rfl⟩
  have hσ6 : σ ^ 6 = 1 := by
    have h := pow_card_eq_one' (x := (⟨σ, hσ⟩ : Sec4.autIn ⊤ E))
    rw [h6] at h
    exact congrArg Subtype.val h
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hσ6 ⟨e, he⟩)
  rw [hσdef, ← map_pow] at h1
  exact h1

end J2

section A7

open Equiv

def a7c1 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

def a7c2 : alternatingGroup (Fin 7) :=
  ⟨swap 3 4 * swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

def a7g : alternatingGroup (Fin 7) :=
  ⟨swap 0 3 * (swap 1 5 * swap 1 2 * swap 1 4), Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

def a7E : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers a7c1 ⊔ Subgroup.zpowers a7c2

theorem a7c1_pow_three : a7c1 ^ 3 = 1 := by decide

theorem a7c2_pow_three : a7c2 ^ 3 = 1 := by decide

theorem a7c1_comm : a7c1 * a7c2 = a7c2 * a7c1 := by decide

theorem a7g_c1 : a7g * a7c1 * a7g⁻¹ = a7c2 := by decide

theorem a7g_c2 : a7g * a7c2 * a7g⁻¹ = a7c1⁻¹ := by decide

theorem a7g_pow_four : a7g ^ 4 = 1 := by decide

theorem a7g_sq_c1 : a7g ^ 2 * a7c1 * (a7g ^ 2)⁻¹ = a7c1⁻¹ := by decide

theorem a7c1_ne_inv : a7c1⁻¹ ≠ a7c1 := by decide

theorem a7c1_not_mem : a7c1 ∉ Subgroup.zpowers a7c2 := by
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime a7c2_pow_three (by decide)]
  decide

theorem card_a7E : Nat.card a7E = 9 := by
  have hC : a7c1 ∈ Subgroup.centralizer
      (Subgroup.zpowers a7c2 : Set (alternatingGroup (Fin 7))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (a7c1_comm.symm : Commute a7c2 a7c1) k).eq
  rw [a7E, KFacts.KS14.card_eq_three_mul_card_inf hC a7c1_not_mem a7c1_pow_three le_rfl
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)), inf_of_le_right le_sup_right,
    Nat.card_zpowers, orderOf_eq_prime a7c2_pow_three (by decide)]

theorem a7E_le_centralizer : a7E ≤ Subgroup.centralizer (a7E : Set (alternatingGroup (Fin 7))) := by
  have h1 : a7E ≤ Subgroup.centralizer ({a7c1} : Set (alternatingGroup (Fin 7))) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr a7c1_comm.symm))
  have h2 : a7E ≤ Subgroup.centralizer ({a7c2} : Set (alternatingGroup (Fin 7))) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr a7c1_comm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (h1 hh)
  · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (h2 hh)

theorem a7E_comm {x y : alternatingGroup (Fin 7)} (hx : x ∈ a7E) (hy : y ∈ a7E) :
    x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (a7E_le_centralizer hy) x hx)

theorem a7g_conj_mem {y : alternatingGroup (Fin 7)} (hy : y ∈ a7E) :
    a7g * y * a7g⁻¹ ∈ a7E := by
  have hle : a7E ≤ a7E.comap (MulAut.conj a7g).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · show a7g * a7c1 * a7g⁻¹ ∈ a7E
      rw [a7g_c1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · show a7g * a7c2 * a7g⁻¹ ∈ a7E
      rw [a7g_c2]
      exact inv_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  exact hle hy

end A7

section Cases

variable {X : Type} [Group X] [Finite X] {K : Type} [Group K] [Finite K]

theorem card_a7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem false_of_three_dvd_card_ker (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (ι : K →* X)
    (hι : Function.Injective ι) (f : K →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) (h240 : Nat.card f.ker ∣ 240) (h3 : 3 ∣ Nat.card f.ker) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := f.ker with hNdef
  obtain ⟨Q⟩ : Nonempty (Sylow 3 N) := inferInstance
  have hQ1 : (Q : Subgroup N) ≠ ⊥ := Q.ne_bot_of_dvd_card h3
  have hQ3 : Nat.card (Q : Subgroup N) = 3 := by
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    have hdvd : 3 ^ k ∣ 240 := hk ▸ (Subgroup.card_subgroup_dvd_card _).trans h240
    have hk1 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : 3 ^ 2 ∣ 240 := (pow_dvd_pow 3 hk2).trans hdvd
      norm_num at this
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hQ1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    rw [hk, show k = 1 by omega, pow_one]
  set Z := (Q : Subgroup N).map N.subtype with hZdef
  have hZ3 : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective N.subtype_injective, hQ3]
  have hfr : Subgroup.normalizer (Z : Set K) ⊔ N = ⊤ := Q.normalizer_sup_eq_top
  have hsurj : Function.Surjective (f.comp (Subgroup.normalizer (Z : Set K)).subtype) := by
    intro y
    obtain ⟨k, rfl⟩ := hf y
    have hk : k ∈ ((Subgroup.normalizer (Z : Set K) ⊔ N : Subgroup K) : Set K) := by
      rw [hfr]
      trivial
    rw [Subgroup.mul_normal] at hk
    obtain ⟨a, ha, n, hn, rfl⟩ := hk
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, (f.mem_ker).mp hn, mul_one]
  have h1 : 2520 ≤ Nat.card (Subgroup.normalizer (Z : Set K)) := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [card_a7] at this
  have h2 : Nat.card (Subgroup.normalizer (Z : Set K)) ≤
      Nat.card (Subgroup.normalizer ((Z.map ι : Subgroup X) : Set X)) := by
    rw [← Subgroup.card_map_of_injective hι]
    exact Subgroup.card_le_of_le (Subgroup.le_normalizer_map ι)
  have h3' := j2_card_normalizer_le h415 hX (W := Z.map ι)
    (by rw [Subgroup.card_map_of_injective hι, hZ3])
  omega

theorem false_of_not_three_dvd_card_ker (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (ι : K →* X)
    (hι : Function.Injective ι) (f : K →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) (h3 : ¬ 3 ∣ Nat.card f.ker) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := f.ker with hNdef
  set M := a7E.comap f with hMdef
  let φM : M →* a7E := (f.comp M.subtype).codRestrict a7E (fun x => x.2)
  have hφM : Function.Surjective φM := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := hf y
    exact ⟨⟨k, hy⟩, rfl⟩
  have h9M : 9 ∣ Nat.card M := card_a7E ▸ Subgroup.card_dvd_of_surjective hφM
  obtain ⟨S⟩ : Nonempty (Sylow 3 M) := inferInstance
  have h9S : 9 ∣ Nat.card (S : Subgroup M) := by
    have hidx : Nat.Coprime 9 (S : Subgroup M).index :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index)
    rw [← Subgroup.card_mul_index (S : Subgroup M)] at h9M
    exact hidx.dvd_of_dvd_mul_right h9M
  set E := (S : Subgroup M).map M.subtype with hEdef
  have hEc : Nat.card E = Nat.card (S : Subgroup M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have hE3 : IsPGroup 3 E := S.isPGroup'.map M.subtype
  have hEM : E ≤ M := Subgroup.map_subtype_le _
  have hNM : N ≤ M := MonoidHom.ker_le_comap f a7E
  have hdisj : N ⊓ E = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 : Nat.card ↥(N ⊓ E) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk⟩ := (hE3.to_le (inf_le_right : N ⊓ E ≤ E)).exists_card_eq
    rcases k with _ | k
    · simpa using hk
    · exfalso
      apply h3
      rw [hk] at h1
      exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans h1
  have hinj : ∀ x ∈ E, ∀ y ∈ E, f x = f y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ N ⊓ E := Subgroup.mem_inf.mpr
      ⟨by rw [hNdef, f.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel], mul_mem (inv_mem hx) hy⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem
  have hinj' : Function.Injective (f.comp E.subtype) := fun x y hxy =>
    Subtype.ext (hinj x x.2 y y.2 hxy)
  have hEcardf : Nat.card (E.map f) = Nat.card E := by
    have : E.map f = (f.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv]
  have hEf : E.map f ≤ a7E := Subgroup.map_le_iff_le_comap.mpr hEM
  have hE9 : Nat.card E = 9 := by
    refine le_antisymm ?_ (Nat.le_of_dvd Nat.card_pos (hEc ▸ h9S))
    have := Subgroup.card_le_of_le hEf
    rwa [hEcardf, card_a7E] at this
  have hEfeq : E.map f = a7E :=
    Subgroup.eq_of_le_of_card_ge hEf (by rw [hEcardf, hE9, card_a7E])
  have hmemf : ∀ e ∈ E, f e ∈ a7E := fun e he => hEfeq ▸ ⟨e, he, rfl⟩
  obtain ⟨e1, he1, hfe1⟩ : ∃ e1 ∈ E, f e1 = a7c1 := by
    have : a7c1 ∈ E.map f := hEfeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a7c1)
    exact this
  obtain ⟨k₀, hk₀⟩ := hf a7g
  have hk : E.map (MulAut.conj k₀).toMonoidHom ≤ E ⊔ N := by
    rintro _ ⟨x, hx, rfl⟩
    show k₀ * x * k₀⁻¹ ∈ E ⊔ N
    have hfx : f (k₀ * x * k₀⁻¹) ∈ E.map f := by
      rw [hEfeq, map_mul, map_mul, map_inv, hk₀]
      exact a7g_conj_mem (hmemf x hx)
    obtain ⟨e, he, hfe⟩ := hfx
    have heq : k₀ * x * k₀⁻¹ = e * (e⁻¹ * (k₀ * x * k₀⁻¹)) := by group
    rw [heq]
    refine mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right ?_)
    rw [f.mem_ker, map_mul, map_inv, hfe, inv_mul_cancel]
  obtain ⟨m, hm, hkN⟩ := exists_mem_sup_mul_mem_normalizer h3 hE3 hk
  set k := m⁻¹ * k₀ with hkdef
  have hfm : f m ∈ a7E := (sup_le hEM hNM : E ⊔ N ≤ M) hm
  have hact : ∀ y ∈ a7E, f k * y * (f k)⁻¹ = a7g * y * a7g⁻¹ := by
    intro y hy
    have hgy : a7g * y * a7g⁻¹ ∈ a7E := a7g_conj_mem hy
    rw [hkdef, map_mul, map_inv, hk₀]
    calc (f m)⁻¹ * a7g * y * ((f m)⁻¹ * a7g)⁻¹ = (f m)⁻¹ * ((a7g * y * a7g⁻¹) * f m) := by group
      _ = (f m)⁻¹ * (f m * (a7g * y * a7g⁻¹)) := by rw [a7E_comm hgy hfm]
      _ = a7g * y * a7g⁻¹ := by group
  have hpow := conj_pow_eq_of_conj_eq hact (fun y hy => a7g_conj_mem hy)
  have hk4 : k ^ 4 * e1 * (k ^ 4)⁻¹ = e1 := by
    refine hinj _ ((Subgroup.mem_normalizer_iff.mp (pow_mem hkN 4) e1).mp he1) e1 he1 ?_
    rw [map_mul, map_mul, map_inv, map_pow, hpow 4 (f e1) (hmemf e1 he1), a7g_pow_four, one_mul,
      inv_one, mul_one]
  have hk2 : k ^ 2 * e1 * (k ^ 2)⁻¹ ≠ e1 := by
    intro h
    have h' := congrArg f h
    rw [map_mul, map_mul, map_inv, map_pow, hpow 2 (f e1) (hmemf e1 he1), hfe1, a7g_sq_c1] at h'
    exact a7c1_ne_inv h'
  have hk6 : k ^ 6 * e1 * (k ^ 6)⁻¹ = e1 := by
    have hιk : ι k ∈ Subgroup.normalizer ((E.map ι : Subgroup X) : Set X) :=
      Subgroup.le_normalizer_map ι ⟨k, hkN, rfl⟩
    have h6 := j2_pow_six_conj h415 hX (E := E.map ι)
      (by rw [Subgroup.card_map_of_injective hι, hE9]) hιk ⟨e1, he1, rfl⟩
    apply hι
    rw [map_mul, map_mul, map_inv, map_pow]
    exact h6
  have hk4' : (k ^ 4)⁻¹ * e1 * k ^ 4 = e1 := by
    calc (k ^ 4)⁻¹ * e1 * k ^ 4 = (k ^ 4)⁻¹ * (k ^ 4 * e1 * (k ^ 4)⁻¹) * k ^ 4 := by rw [hk4]
      _ = e1 := by group
  apply hk2
  calc k ^ 2 * e1 * (k ^ 2)⁻¹ = k ^ 6 * ((k ^ 4)⁻¹ * e1 * k ^ 4) * (k ^ 6)⁻¹ := by group
    _ = k ^ 6 * e1 * (k ^ 6)⁻¹ := by rw [hk4']
    _ = e1 := hk6

end Cases

end Proof15Res2

open Proof15Res2

theorem ks1515J2NoA7_of (h415 : Sec4.Item4_15) : KS1515J2NoA7 := by
  intro X _ hX K _ ι hι f hf
  have hXc : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 hX
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  have : Finite K := Finite.of_injective ι hι
  have hKc : Nat.card f.ker * 2520 = Nat.card K := by
    rw [← card_a7]
    exact Subgroup.card_ker_mul_card_of_surjective hf
  have hKdvd : Nat.card K ∣ 604800 := hXc ▸ Subgroup.card_dvd_of_injective ι hι
  have h240 : Nat.card f.ker ∣ 240 := by
    rw [← hKc, show (604800 : ℕ) = 240 * 2520 by norm_num] at hKdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hKdvd
  by_cases h3 : 3 ∣ Nat.card f.ker
  · exact false_of_three_dvd_card_ker h415 hX ι hι f hf h240 h3
  · exact false_of_not_three_dvd_card_ker h415 hX ι hι f hf h3

theorem ks1515J2NoA7 :
    KS1515J2NoA7 :=
  ks1515J2NoA7_of Sec4.Sporadic.rank3II_4_15

end CFSG.RankThree.PartTwo.Sec15
