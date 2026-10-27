module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16n9b_case4_data {T : Type} [CommGroup T] [Finite T] {X : Subgroup (MulAut T)}
    {r d : ℕ} (hS : SymSumOfConj X (⊤ : Subgroup T) r d) :
    ∃ (ι : Type) (_ : Fintype ι) (Y : ι → Subgroup T), iSupIndep Y ∧ Function.Injective Y ∧
      ⨆ i, Y i = ⊤ ∧ Fintype.card ι = r + 1 ∧ (∀ i, rk ↥(Y i) = d) ∧
      (∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) ∧
      ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i) := by
  obtain ⟨Z, hZ, hind, hsup, hcard, hsym⟩ := hS
  have hfin : (conjSubs X Z).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; omega)
  letI : Fintype ↥(conjSubs X Z) := hfin.fintype
  refine ⟨↥(conjSubs X Z), inferInstance, Subtype.val, ?_, Subtype.val_injective,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (sSupIndep_iff (conjSubs X Z)).1 hind
  · rw [← sSup_eq_iSup']; exact hsup
  · exact (Set.fintypeCard_eq_ncard (conjSubs X Z)).trans hcard
  · intro i
    obtain ⟨g, hg, hgi⟩ := i.2
    rw [hgi, s16n9b_rk_map, hZ]
  · intro g hg i
    obtain ⟨h, hh, hi⟩ := i.2
    refine ⟨⟨Z.map (g * h).toMonoidHom, g * h, X.mul_mem hg hh, rfl⟩, ?_⟩
    show (i.1).map g.toMonoidHom = Z.map (g * h).toMonoidHom
    rw [hi, Subgroup.map_map]
    rfl
  · intro π
    obtain ⟨g, hg, hgπ⟩ := hsym π
    exact ⟨g, hg, fun i => hgπ i⟩

private theorem s16n9b_case4_ker_card_elemAbelianOfRank {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16n9b_case4_ker_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16n9b_case4_ker_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private noncomputable def s16n9b_case4_ker_permFun {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) : ι :=
  Classical.choose (hperm (g : MulAut T) g.2 i)

private theorem s16n9b_case4_ker_permFun_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16n9b_case4_ker_permFun hperm g i) :=
  Classical.choose_spec (hperm (g : MulAut T) g.2 i)

private theorem s16n9b_case4_ker_permFun_injective {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) :
    Function.Injective (s16n9b_case4_ker_permFun hperm g) := by
  intro i j hij
  apply hinj
  have hi := s16n9b_case4_ker_permFun_spec hperm g i
  have hj := s16n9b_case4_ker_permFun_spec hperm g j
  rw [hij] at hi
  exact Subgroup.map_injective (g : MulAut T).injective (hi.trans hj.symm)

private noncomputable def s16n9b_case4_ker_perm {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) : Equiv.Perm ι :=
  Equiv.ofBijective (s16n9b_case4_ker_permFun hperm g)
    ⟨s16n9b_case4_ker_permFun_injective hinj hperm g,
      (Finite.injective_iff_surjective).1 (s16n9b_case4_ker_permFun_injective hinj hperm g)⟩

private theorem s16n9b_case4_ker_perm_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16n9b_case4_ker_perm hinj hperm g i) := by
  exact s16n9b_case4_ker_permFun_spec hperm g i
private theorem s16n9b_case4_ker_perm_mul {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g h : ↥X) :
    s16n9b_case4_ker_perm hinj hperm (g * h) =
      s16n9b_case4_ker_perm hinj hperm g * s16n9b_case4_ker_perm hinj hperm h := by
  ext i
  apply hinj
  rw [← s16n9b_case4_ker_perm_spec hinj hperm (g * h) i, Equiv.Perm.mul_apply,
    ← s16n9b_case4_ker_perm_spec hinj hperm g (s16n9b_case4_ker_perm hinj hperm h i),
    ← s16n9b_case4_ker_perm_spec hinj hperm h i]
  rw [Subgroup.map_map]
  rfl

private noncomputable def s16n9b_case4_ker_rho {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) : ↥X →* Equiv.Perm ι :=
  MonoidHom.mk' (s16n9b_case4_ker_perm hinj hperm)
    (s16n9b_case4_ker_perm_mul hinj hperm)

private theorem s16n9b_case4_ker_rho_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16n9b_case4_ker_rho hinj hperm g i) :=
  s16n9b_case4_ker_perm_spec hinj hperm g i

private theorem s16n9b_case4_ker_rho_surjective {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)) :
    Function.Surjective (s16n9b_case4_ker_rho hinj hperm) := by
  intro π
  obtain ⟨g, hg, hgπ⟩ := hsurj π
  refine ⟨⟨g, hg⟩, ?_⟩
  ext i
  apply hinj
  exact (s16n9b_case4_ker_rho_spec hinj hperm ⟨g, hg⟩ i).symm.trans (hgπ i)

theorem s16n9b_case4_kernel {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X A : Subgroup (MulAut T)} {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r)
    (hA : IsElemAbelianOfRank p r ↥A) (hAP : A ≤ pCoreOf p X)
    (hge : 3 ≤ CFSG.Open.pRank p X) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hinj : Function.Injective Y) (hsup : ⨆ i, Y i = ⊤)
    (hcard : Fintype.card ι = r + 1) (hrk : ∀ i, rk ↥(Y i) = dParam p)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)) :
    ∃ F : Subgroup (MulAut T), F ≤ X ∧ IsElemAbelian p F ∧ p ^ 3 ≤ Nat.card F ∧
      (∀ f ∈ F, ∀ i, (Y i).map f.toMonoidHom = Y i) ∧
      (p = 7 → ∃ Q : Subgroup (MulAut T), Q ≤ X ∧ IsPGroup 7 ↥Q ∧ Q ≠ ⊥ ∧
        (∀ φ ∈ X, Q.map (MulAut.conj φ).toMonoidHom = Q) ∧
        ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i) := by
  classical
  have hpp : p.Prime := by rcases hp with h | h <;> (rw [h]; norm_num)
  have hpodd : p ≠ 2 := by rcases hp with h | h <;> (rw [h]; norm_num)
  let ρ : ↥X →* Equiv.Perm ι := s16n9b_case4_ker_rho hinj hperm
  have hρsurj : Function.Surjective ρ :=
    s16n9b_case4_ker_rho_surjective hinj hperm hsurj
  have hAcard : Nat.card ↥A = p ^ r := s16n9b_case4_ker_card_elemAbelianOfRank hA
  have hAne : A ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hAcard]
    exact one_lt_pow' hpp.one_lt (by omega)
  have hAX : A ≤ X := hAP.trans (Subgroup.map_subtype_le _)
  have hAel : IsElemAbelian p A := by
    have hcp := s16n9b_case4_ker_rank_comm_pow hA
    refine ⟨isMulCommutative_iff.2 hcp.1, fun x hx => ?_⟩
    simpa using congrArg Subtype.val (hcp.2 ⟨x, hx⟩)
  have hpCoreP : IsPGroup p ↥(pCoreOf p X) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥X)).map X.subtype
  have hQne : pCoreOf p X ≠ ⊥ := by
    intro hbot
    exact hAne (le_bot_iff.1 (hbot ▸ hAP))
  have hQnorm : ∀ φ ∈ X,
      (pCoreOf p X).map (MulAut.conj φ).toMonoidHom = pCoreOf p X := by
    intro φ hφ
    let α : MulAut ↥X := X.normalizerMonoidHom ⟨φ, X.le_normalizer hφ⟩
    have hcomp : X.subtype.comp α.toMonoidHom =
        (MulAut.conj φ).toMonoidHom.comp X.subtype := by
      ext y
      simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    calc (pCoreOf p X).map (MulAut.conj φ).toMonoidHom
        = ((CFSG.pCore p ↥X).map X.subtype).map (MulAut.conj φ).toMonoidHom := rfl
      _ = (CFSG.pCore p ↥X).map ((MulAut.conj φ).toMonoidHom.comp X.subtype) := by
            rw [Subgroup.map_map]
      _ = (CFSG.pCore p ↥X).map (X.subtype.comp α.toMonoidHom) := by rw [hcomp]
      _ = ((CFSG.pCore p ↥X).map α.toMonoidHom).map X.subtype := by rw [Subgroup.map_map]
      _ = (CFSG.pCore p ↥X).map X.subtype := by
            rw [Subgroup.characteristic_iff_map_eq.mp
              (inferInstance : (CFSG.pCore p ↥X).Characteristic) α]
      _ = pCoreOf p X := rfl
  have hQtriv_big : 4 ≤ Fintype.card ι → ∀ q : ↥X, q ∈ CFSG.pCore p ↥X → ρ q = 1 := by
    intro hI4 q hq
    have hNnorm : ((CFSG.pCore p ↥X).map ρ).Normal :=
      (inferInstance : (CFSG.pCore p ↥X).Normal).map ρ hρsurj
    have hNp : IsPGroup p ↥((CFSG.pCore p ↥X).map ρ) :=
      (CFSG.pCore_isPGroup (p := p) (G := ↥X)).map ρ
    have hbot : (CFSG.pCore p ↥X).map ρ = ⊥ :=
      s16n9b_case4_perm_normal hpp hpodd hI4 hNnorm hNp
    have hmem : ρ q ∈ (CFSG.pCore p ↥X).map ρ := Subgroup.mem_map.2 ⟨q, hq, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have pcore_triv_big : 4 ≤ Fintype.card ι → ∀ a ∈ pCoreOf p X, ∀ i,
      (Y i).map a.toMonoidHom = Y i := by
    intro hI4 a ha i
    obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.1 ha
    have h1 : (Y i).map a.toMonoidHom = Y (ρ q i) := by
      rw [← hqval]
      exact s16n9b_case4_ker_rho_spec hinj hperm q i
    rw [hQtriv_big hI4 q hq] at h1
    simpa using h1
  have hPtriv_small : ∀ P : Subgroup (MulAut T), P ≤ X → IsPGroup p ↥P →
      Fintype.card ι < p → ∀ g ∈ P, ∀ i, (Y i).map g.toMonoidHom = Y i := by
    intro P hPX hPp hlt g hg i
    have hPp' : IsPGroup p ↥(P.subgroupOf X) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
    have hNp : IsPGroup p ↥((P.subgroupOf X).map ρ) := hPp'.map ρ
    have hbot : (P.subgroupOf X).map ρ = ⊥ := s16n9b_case4_perm_small hpp hlt hNp
    have hmem : ρ ⟨g, hPX hg⟩ ∈ (P.subgroupOf X).map ρ :=
      Subgroup.mem_map.2 ⟨⟨g, hPX hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
    rw [hbot] at hmem
    have hρg : ρ ⟨g, hPX hg⟩ = 1 := Subgroup.mem_bot.1 hmem
    have h1 : (Y i).map g.toMonoidHom = Y (ρ ⟨g, hPX hg⟩ i) :=
      s16n9b_case4_ker_rho_spec hinj hperm ⟨g, hPX hg⟩ i
    rw [hρg] at h1
    simpa using h1
  by_cases hge3 : 3 ≤ r
  ·
    have hI4 : 4 ≤ Fintype.card ι := by rw [hcard]; omega
    have hA3 : p ^ 3 ≤ Nat.card ↥A := by
      rw [hAcard]
      exact (Nat.pow_le_pow_iff_right hpp.one_lt).2 hge3
    refine ⟨A, hAX, hAel, hA3, ?_, ?_⟩
    · intro f hf i
      exact pcore_triv_big hI4 f (hAP hf) i
    · intro hp7
      subst hp7
      refine ⟨pCoreOf 7 X, Subgroup.map_subtype_le _, hpCoreP, hQne, hQnorm, ?_⟩
      intro q hq i
      exact pcore_triv_big hI4 q hq i
  ·
    have hr2 : r = 2 := by omega
    have hι3 : Fintype.card ι = 3 := by rw [hcard, hr2]
    obtain ⟨E, hEX, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt X
    have hE3 : p ^ 3 ≤ Nat.card ↥E := by
      rw [hEcard]
      exact (Nat.pow_le_pow_iff_right hpp.one_lt).2 hge
    have hEY : ∀ e ∈ E, ∀ i, (Y i).map e.toMonoidHom = Y i := by
      rcases hp with hp3 | hp7
      · subst hp3
        have hrk2 : ∀ i, rk ↥(Y i) = 2 := by
          intro i
          rw [hrk i, s16n9b_case4_ker_dParam_three]
        exact s16n9b_case4_perm_E hT hι3 hind hinj hsup hrk2 hEel hE3
          (fun g hg i => hperm g (hEX hg) i)
      · subst hp7
        exact hPtriv_small E hEX (IsElemAbelian.isPGroup hEel) (by rw [hι3]; norm_num)
    refine ⟨E, hEX, hEel, hE3, hEY, ?_⟩
    intro hp7
    subst hp7
    refine ⟨pCoreOf 7 X, Subgroup.map_subtype_le _, hpCoreP, hQne, hQnorm, ?_⟩
    intro q hq i
    exact hPtriv_small (pCoreOf 7 X) (Subgroup.map_subtype_le _) hpCoreP
      (by rw [hι3]; norm_num) q hq i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
