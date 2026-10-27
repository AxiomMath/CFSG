module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace SBc17

theorem center_alt_bot {n : ℕ} (hn : 4 ≤ n) : Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
  alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)

theorem false_of_a5_borel_alt {S : Subgroup (alternatingGroup (Fin 5))} (hS2 : IsPGroup 2 S)
    (hSodd : ¬ 2 ∣ S.index) {g : alternatingGroup (Fin 5)} (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1)
    (hgN : g ∈ Subgroup.normalizer (S : Set (alternatingGroup (Fin 5)))) : False := by
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hidx := S.index_mul_card
  rw [hA, hk] at hidx
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h
    have : 2 ^ 3 ∣ 60 := h8.trans ⟨S.index, by rw [← hidx]; ring⟩
    omega
  have hcard : Nat.card S ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hk0 : k = 2 := by
    interval_cases k
    · exfalso
      apply hSodd
      simp only [pow_zero, mul_one] at hidx
      rw [hidx]
      decide
    · exfalso
      apply hSodd
      rw [pow_one] at hidx
      omega
    · rfl
  let ρ : Equiv.Perm (alternatingGroup (Fin 5)) := (MulAut.conj g).toEquiv
  have hρ : ∀ x, ρ x = g * x * g⁻¹ := fun x => rfl
  have hρpow : ∀ n : ℕ, ∀ x, (ρ ^ n) x = g ^ n * x * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, hρ, ih, pow_succ]
      simp [mul_assoc]
  have hρ5 : ρ ^ 5 = 1 := by
    ext x
    rw [hρpow, hg5]
    simp
  classical
  let B : Finset (alternatingGroup (Fin 5)) := (S : Set (alternatingGroup (Fin 5))).toFinset
  have hBcard : B.card ≤ 4 := by
    have : B.card = Nat.card S := by
      simp only [B, Set.toFinset_card, Nat.card_eq_fintype_card]
      rfl
    omega
  have hρB : ∀ x, ρ x ∈ B ↔ x ∈ B := by
    intro x
    simp only [B, Set.mem_toFinset, SetLike.mem_coe, hρ]
    exact (Subgroup.mem_normalizer_iff.mp hgN x).symm
  have hfix := perm_fix_of_invariant_small ρ hρ5 B hρB hBcard
  have hcen : ∀ s ∈ S, s * g = g * s := by
    intro s hs
    have h1 := hfix s (by simpa [B] using hs)
    rw [hρ] at h1
    calc s * g = g * s * g⁻¹ * g := by rw [h1]
      _ = g * s := by group
  have hdec : ∀ g s : alternatingGroup (Fin 5), g ^ 5 = 1 → g ≠ 1 → s * g = g * s →
      ∃ k : Fin 5, s = g ^ (k : ℕ) := by decide +kernel
  have hS1 : ∀ s ∈ S, s = 1 := by
    intro s hs
    obtain ⟨j, hj⟩ := hdec g s hg5 hg1 (hcen s hs)
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    have hm' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hs5 : s ^ 5 = 1 := by
      rw [hj, ← pow_mul, mul_comm, pow_mul, hg5, one_pow]
    have h1 : orderOf s ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h2 : orderOf s ∣ 5 := orderOf_dvd_of_pow_eq_one hs5
    have h3 : orderOf s ∣ Nat.gcd (2 ^ m) 5 := Nat.dvd_gcd h1 h2
    have hcop : Nat.Coprime (2 ^ m) 5 := Nat.Coprime.pow_left m (by norm_num)
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hSbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr hS1
  have h1 : Nat.card S = 1 := by rw [hSbot]; exact Subgroup.card_bot
  rw [hk0] at hk
  omega

section Transfer

variable {G : Type} [Group G]

theorem ker_actOn_eq_pCore {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hCO : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) :
    (actOn hJV).ker = CFSG.pCore 2 ↥J := by
  ext x
  rw [MonoidHom.mem_ker, actOn_eq_one_iff, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1,
    Subgroup.mem_subgroupOf]
  exact ⟨fun h => hCO ⟨x.2, h⟩, fun h => hOC h⟩

theorem autOn_nonempty_mulEquiv {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hCO : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) {S : Type*} [Group S]
    {α : ↥J →* S} (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥J) :
    Nonempty (↥(autOn J V) ≃* S) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective (actOn hJV) (actOn_surjective hJV)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_actOn_eq_pCore hJV hOC hCO).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

end Transfer

variable {G : Type} [Group G] [Finite G]

theorem false_of_a5 {J M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J)
    {α : ↥J →* alternatingGroup (Fin 5)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥J) (hB : IsBorelIn (autOn J V) (autOn (M ⊓ J) V)) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  have hD' : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J :=
    hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hα hker (center_alt_bot (by norm_num)))
  obtain ⟨hmem, hord⟩ := act_five hJV hD' haM ha5
  obtain ⟨Ss, hSs, hBeq⟩ := hB
  obtain ⟨e⟩ := autOn_nonempty_mulEquiv hJV hOC hD' hα hker
  have hmem' := hmem
  rw [hBeq] at hmem'
  set â : MulAut ↥V := conjAct V ⟨a, hJV haM.2⟩ with hâ
  set x : ↥(autOn J V) := ⟨â, hmem'.1⟩ with hx
  have hx5 : x ^ 5 = 1 := by
    apply Subtype.ext
    show â ^ 5 = 1
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hx1 : x ≠ 1 := by
    intro h
    have h' : â = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hord
    omega
  have hSs' : IsPGroup 2 (Ss.subgroupOf (autOn J V)) := hSs.2.1.comap_subtype (K := autOn J V)
  set S₀ : Subgroup (alternatingGroup (Fin 5)) :=
    (Ss.subgroupOf (autOn J V)).map e.toMonoidHom with hS₀
  have hS₀2 : IsPGroup 2 S₀ := hSs'.map e.toMonoidHom
  have hS₀odd : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.index_map_equiv (H := Ss.subgroupOf (autOn J V)) e
    have h' : S₀.index = (Ss.subgroupOf (autOn J V)).index := h
    rw [h']
    exact hSs.2.2
  refine false_of_a5_borel_alt hS₀2 hS₀odd (g := e x) ?_ ?_ ?_
  · rw [← map_pow, hx5, map_one]
  · intro h
    exact hx1 (e.injective (h.trans (map_one e).symm))
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hnorm : â ∈ Subgroup.normalizer (Ss : Set (MulAut ↥V)) := hmem'.2
    have e1 : e x * e z * (e x)⁻¹ = e (x * z * x⁻¹) := by simp
    rw [e1]
    simp only [hS₀, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hnorm (z : MulAut ↥V)

theorem nat_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_stabilizer_alt_six (z : Fin 6) :
    Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin 6)) z ⊓ alternatingGroup (Fin 6)) = 60 := by
  have h : ∀ z : Fin 6, (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin 6) => σ z = z ∧ Equiv.Perm.sign σ = 1)).card = 60 := by
    decide +kernel
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← h z]
  congr 1
  apply Finset.filter_congr
  intro σ _
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]

theorem six_dvd_card_perm {P : Subgroup (Equiv.Perm (Fin 6))} (hPA : P ≤ alternatingGroup (Fin 6))
    (h8 : 8 ∣ Nat.card P) {g : Equiv.Perm (Fin 6)} (hgP : g ∈ P) (hg5 : g ^ 5 = 1)
    (hg1 : g ≠ 1) : 6 ∣ Nat.card P := by
  classical
  obtain ⟨x₁, hx₁⟩ : ∃ x, g x ≠ x := by
    by_contra h
    push Not at h
    exact hg1 (Equiv.ext h)
  set O : Finset (Fin 6) := (MulAction.orbit ↥P x₁).toFinset with hOdef
  have hmemO : ∀ y, y ∈ O ↔ ∃ p : ↥P, (p : Equiv.Perm (Fin 6)) x₁ = y := by
    intro y
    simp [hOdef, MulAction.mem_orbit_iff]
  have hinv : ∀ q ∈ P, ∀ y, q y ∈ O ↔ y ∈ O := by
    intro q hq y
    rw [hmemO, hmemO]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨⟨q⁻¹, P.inv_mem hq⟩ * p, ?_⟩
      show q⁻¹ ((p : Equiv.Perm (Fin 6)) x₁) = y
      rw [hp]
      simp
    · rintro ⟨p, hp⟩
      refine ⟨⟨q, hq⟩ * p, ?_⟩
      show q ((p : Equiv.Perm (Fin 6)) x₁) = q y
      rw [hp]
  have hx₁O : x₁ ∈ O := (hmemO x₁).mpr ⟨1, rfl⟩
  have hge5 : 5 ≤ O.card := by
    by_contra h
    push Not at h
    exact hx₁ (perm_fix_of_invariant_small g hg5 O (fun y => hinv g hgP y) (by omega) x₁ hx₁O)
  have hle6 : O.card ≤ 6 := by simpa using Finset.card_le_univ O
  rcases (by omega : O.card = 5 ∨ O.card = 6) with h5 | h6
  · exfalso
    have hcompl : (Oᶜ).card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h5]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcompl
    have hzO : z ∈ Oᶜ := by rw [hz]; exact Finset.mem_singleton_self z
    have hPz : P ≤ MulAction.stabilizer (Equiv.Perm (Fin 6)) z ⊓ alternatingGroup (Fin 6) := by
      intro q hq
      refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, hPA hq⟩
      have h1 : q z ∈ Oᶜ := by
        rw [Finset.mem_compl] at hzO ⊢
        rw [hinv q hq z]
        exact hzO
      rw [hz, Finset.mem_singleton] at h1
      exact h1
    have hdvd : Nat.card P ∣ 60 := by
      have := Subgroup.card_dvd_of_le hPz
      rwa [card_stabilizer_alt_six z] at this
    have : 8 ∣ 60 := h8.trans hdvd
    omega
  · have horb : Nat.card (MulAction.orbit ↥P x₁) = 6 := by
      rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
      exact h6
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥P x₁
    simp only [← Nat.card_eq_fintype_card] at h
    rw [horb] at h
    exact ⟨_, h.symm⟩

theorem false_of_index_three_alt_six {P : Subgroup (alternatingGroup (Fin 6))} (h : P.index = 3) :
    False := by
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  let φ := MulAction.toPermHom ↥(alternatingGroup (Fin 6)) (↥(alternatingGroup (Fin 6)) ⧸ P)
  rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have hfin : Finite (↥(alternatingGroup (Fin 6)) ⧸ P) := inferInstance
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, nat_card_alt_six] at h1
    have hc : Nat.card (↥(alternatingGroup (Fin 6)) ⧸ P) = 3 := h
    rw [hc] at h1
    norm_num at h1
  · have hPtop : P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ φ.ker := by rw [hk]; exact Subgroup.mem_top x
      rw [MonoidHom.mem_ker] at hx
      have h2 := congrArg (fun f : Equiv.Perm (↥(alternatingGroup (Fin 6)) ⧸ P) =>
        f (QuotientGroup.mk 1)) hx
      simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
        id_eq] at h2
      have h3 : (QuotientGroup.mk (x * 1) : ↥(alternatingGroup (Fin 6)) ⧸ P) =
          QuotientGroup.mk 1 := h2
      rw [QuotientGroup.eq] at h3
      simpa using P.inv_mem h3
    rw [hPtop, Subgroup.index_top] at h
    omega

theorem eq_top_of_sylow_five_alt_six {P S : Subgroup (alternatingGroup (Fin 6))} (hSP : S ≤ P)
    (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.index) {g : alternatingGroup (Fin 6)} (hgP : g ∈ P)
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : P = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hidx := S.index_mul_card
  rw [nat_card_alt_six, hk] at hidx
  have hk3 : k = 3 := by
    have hk4 : k ≤ 3 := by
      by_contra hh
      push Not at hh
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hh
      have : 2 ^ 4 ∣ 360 := h16.trans ⟨S.index, by rw [← hidx]; ring⟩
      omega
    interval_cases k
    · exfalso; apply hSodd; simp only [pow_zero, mul_one] at hidx; rw [hidx]; decide
    · exfalso; apply hSodd; rw [pow_one] at hidx; omega
    · exfalso; apply hSodd; omega
    · rfl
  have hS8 : Nat.card S = 8 := by rw [hk, hk3]; norm_num
  have h8 : 8 ∣ Nat.card P := hS8 ▸ Subgroup.card_dvd_of_le hSP
  have h5 : 5 ∣ Nat.card P := by
    have := orderOf_dvd_natCard (⟨g, hgP⟩ : ↥P)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hg5 hg1] at this
  set Pp : Subgroup (Equiv.Perm (Fin 6)) := P.map (alternatingGroup (Fin 6)).subtype with hPp
  have hPpcard : Nat.card Pp = Nat.card P :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective
  have hPpA : Pp ≤ alternatingGroup (Fin 6) := Subgroup.map_subtype_le P
  have hgPp : (g : Equiv.Perm (Fin 6)) ∈ Pp := ⟨g, hgP, rfl⟩
  have hg5' : (g : Equiv.Perm (Fin 6)) ^ 5 = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin 6) => (z : Equiv.Perm (Fin 6))) hg5
    simpa using this
  have hg1' : (g : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have h6 : 6 ∣ Nat.card P := by
    rw [← hPpcard]
    exact six_dvd_card_perm hPpA (by rw [hPpcard]; exact h8) hgPp hg5' hg1'
  have h120 : 120 ∣ Nat.card P := by omega
  have hP360 := P.index_mul_card
  rw [nat_card_alt_six] at hP360
  have hidx3 : P.index = 1 := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : P.index ∣ 3 := by
      obtain ⟨m, hm⟩ := h120
      refine ⟨m, ?_⟩
      rw [hm] at hP360
      nlinarith
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h1 | h3
    · exact h1
    · exact (false_of_index_three_alt_six h3).elim
  exact Subgroup.index_eq_one.mp hidx3

theorem false_of_a6 {J M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J)
    {α : ↥J →* alternatingGroup (Fin 6)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥J)
    (hmax : IsMaxParabolic2 (autOn J V) (autOn (M ⊓ J) V)) {a : G} (haM : a ∈ M ⊓ J)
    (ha5 : orderOf a = 5) : False := by
  have hD' : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J :=
    hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hα hker (center_alt_bot (by norm_num)))
  obtain ⟨hmem, hord⟩ := act_five hJV hD' haM ha5
  obtain ⟨⟨hPle, Ss, hSs, hN⟩, hne, -⟩ := hmax
  obtain ⟨e⟩ := autOn_nonempty_mulEquiv hJV hOC hD' hα hker
  set â : MulAut ↥V := conjAct V ⟨a, hJV haM.2⟩ with hâ
  set x : ↥(autOn J V) := ⟨â, hPle hmem⟩ with hx
  have hx5 : x ^ 5 = 1 := by
    apply Subtype.ext
    show â ^ 5 = 1
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hx1 : x ≠ 1 := by
    intro h
    have h' : â = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hord
    omega
  set P₀ : Subgroup (alternatingGroup (Fin 6)) :=
    ((autOn (M ⊓ J) V).subgroupOf (autOn J V)).map e.toMonoidHom with hP₀
  set S₀ : Subgroup (alternatingGroup (Fin 6)) :=
    (Ss.subgroupOf (autOn J V)).map e.toMonoidHom with hS₀
  have hS₀2 : IsPGroup 2 S₀ := (hSs.2.1.comap_subtype (K := autOn J V)).map e.toMonoidHom
  have hS₀odd : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.index_map_equiv (H := Ss.subgroupOf (autOn J V)) e
    have h' : S₀.index = (Ss.subgroupOf (autOn J V)).index := h
    rw [h']
    exact hSs.2.2
  have hSP : S₀ ≤ P₀ := by
    refine Subgroup.map_mono fun y hy => ?_
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hN ⟨y.2, Subgroup.le_normalizer hy⟩
  have hgP : e x ∈ P₀ := Subgroup.mem_map_of_mem _ (by
    rw [Subgroup.mem_subgroupOf]
    exact hmem)
  have htop : P₀ = ⊤ := by
    refine eq_top_of_sylow_five_alt_six hSP hS₀2 hS₀odd hgP ?_ ?_
    · rw [← map_pow, hx5, map_one]
    · intro h
      exact hx1 (e.injective (h.trans (map_one e).symm))
  have hP1 : (autOn (M ⊓ J) V).subgroupOf (autOn J V) = ⊤ := by
    have := congrArg (Subgroup.comap e.toMonoidHom) htop
    rw [hP₀, Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
    exact this
  exact hne (le_antisymm hPle (Subgroup.subgroupOf_eq_top.mp hP1))

end SBc17

end CFSG.Quasithin
