module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2U3Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2U3Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2U3SU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped Matrix Pointwise

@[expose] def K_19_19_su3TorusIrred : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = (2 ^ n) ^ 2 → 4 ≤ n → Even n →
    ∀ T H : Subgroup ↥(StatedSU 3 (2 ^ n) K), IsMulCommutative ↥T →
      Nat.card T = 2 ^ n - 1 → ⁅H, H⁆ = H →
      T ≤ Subgroup.normalizer (H : Set ↥(StatedSU 3 (2 ^ n) K)) →
      (∀ W : Submodule K (Fin 3 → K),
        (∀ t ∈ T, ∀ w ∈ W, (((t : ↥(StatedSU 3 (2 ^ n) K)) :
          Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) →
        (∀ h ∈ H, ∀ w ∈ W, (((h : ↥(StatedSU 3 (2 ^ n) K)) :
          Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) →
      H = ⊤

namespace TorusQS

section Generic

private theorem commutator_eq_top_of_commutator_eq_self' {G : Type*} [Group G] {H : Subgroup G}
    (h : ⁅H, H⁆ = H) : commutator ↥H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

private theorem commutator_range_eq_self' {G Y : Type*} [Group G] [Group Y]
    (hG : commutator G = ⊤) (f : G →* Y) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hG]

private theorem injective_of_isPGroup_ker_of_odd' {G Y : Type*} [Group G] [Group Y] [Finite G]
    (f : G →* Y) (hk : IsPGroup 2 f.ker) (hG : Odd (Nat.card G)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk'⟩ := hk.exists_card_eq
  have hdvd : Nat.card f.ker ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hk'] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hG) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  rw [hk0, pow_zero] at hk'
  exact Subgroup.eq_bot_of_card_eq _ hk'

private theorem odd_card_of_isZModSq' {X : Type} [Group X] [Finite X] {A : Subgroup X} {n : ℕ}
    (hn : 1 ≤ n) (hA : IsZModSq A n) : Odd (Nat.card A) := by
  rw [S19.card_eq_of_isZModSq hA]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact ⟨m - 1, by omega⟩
  exact hodd.mul hodd

private theorem eq_bot_of_normal_isPGroup_of_mulEquiv' {G Y : Type*} [Group G] [Group Y]
    (e : G ≃* Y) (hY : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) {P : Subgroup G}
    (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp
    (hY (P.map e.toMonoidHom) (hP.map e.toMonoidHom e.surjective) (h2.map e.toMonoidHom))

theorem exists_normalClosure_bar2_equiv_of_le {X Y : Type} [Group X] [Group Y]
    {I J : Subgroup X} (hJI : J ≤ I) (φ : ↥I →* Y) (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 φ.ker) (hJ : commutator ↥J = ⊤) {N : Subgroup Y} [N.Normal]
    [IsSimpleGroup ↥N] (hN2 : ¬ IsPGroup 2 ↥N) (hRN : (J.subgroupOf I).map φ ≤ N)
    (hR : (J.subgroupOf I).map φ ≠ ⊥) :
    ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧ Nonempty (Bar2 K ≃* ↥N) ∧ J ≤ K := by
  have hON : ∀ P : Subgroup ↥N, P.Normal → IsPGroup 2 P → P = ⊥ := fun P hP h2 =>
    eq_bot_of_normal_isPGroup_of_simple hN2 hP h2
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup ↥I,
      M = Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) := ⟨_, rfl⟩
  have hMn : M.Normal := by rw [hMdef]; exact Subgroup.normalClosure_normal
  have hJM : J.subgroupOf I ≤ M := by rw [hMdef]; exact Subgroup.le_normalClosure
  have hKI : M.map I.subtype ≤ I := Subgroup.map_subtype_le M
  have hKM : (M.map I.subtype).subgroupOf I = M :=
    Subgroup.comap_map_eq_self_of_injective I.subtype_injective M
  have hJK : J ≤ M.map I.subtype := fun x hx =>
    ⟨⟨x, hJI hx⟩, hJM (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hJ'J' : ⁅J.subgroupOf I, J.subgroupOf I⁆ = J.subgroupOf I := by
    rw [← Subgroup.inclusion_range hJI]; exact commutator_range_eq_self' hJ _
  have hMM : ⁅M, M⁆ = M := by
    refine le_antisymm (Subgroup.commutator_le_self M) ?_
    have h : Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) ≤ ⁅M, M⁆ :=
      Subgroup.normalClosure_le_normal fun x hx => by
        have hx' : x ∈ ⁅J.subgroupOf I, J.subgroupOf I⁆ := by rw [hJ'J']; exact hx
        exact Subgroup.commutator_mono hJM hJM hx'
    rwa [← hMdef] at h
  have hImK : ((M.map I.subtype).subgroupOf I).map φ = N := by
    rw [hKM, hMdef, Subgroup.map_normalClosure _ _ hφ, ← Subgroup.coe_map]
    set C := Subgroup.normalClosure (((J.subgroupOf I).map φ : Subgroup Y) : Set Y)
    have hCN : C ≤ N := Subgroup.normalClosure_le_normal hRN
    have hCn : (C.subgroupOf N).Normal := (Subgroup.normalClosure_normal).subgroupOf N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.subgroupOf N) with h | h
    · refine absurd (eq_bot_iff.mpr fun y hy => ?_) hR
      have hyC : y ∈ C := Subgroup.le_normalClosure hy
      have : (⟨y, hCN hyC⟩ : ↥N) ∈ C.subgroupOf N := hyC
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · refine le_antisymm hCN fun y hy => ?_
      have : (⟨y, hy⟩ : ↥N) ∈ C.subgroupOf N := h ▸ Subgroup.mem_top _
      exact this
  obtain ⟨eK⟩ := nonempty_bar2_equiv_of_map_eq φ hk hKI hImK hON
  exact ⟨M.map I.subtype, hKI, by rw [hKM]; exact hMn, by rw [← Subgroup.map_commutator, hMM],
    ⟨eK⟩, hJK⟩

theorem nonempty_mulEquiv_prod_of_fst_eq_top {P₁ P₂ : Type} [Group P₁] [Group P₂]
    [IsSimpleGroup P₁] (hZ₁ : Subgroup.center P₁ = ⊥) {S : Subgroup P₂}
    {R : Subgroup (P₁ × P₂)} (hfst : R.map (MonoidHom.fst P₁ P₂) = ⊤)
    (hsnd : R.map (MonoidHom.snd P₁ P₂) = S) {h : P₁} (hh : h ≠ 1)
    (hN : ((h, 1) : P₁ × P₂) ∈ Subgroup.normalizer (R : Set (P₁ × P₂))) :
    Nonempty (↥R ≃* P₁ × ↥S) := by
  set ι : P₁ × ↥S →* P₁ × P₂ := MonoidHom.prodMap (MonoidHom.id P₁) S.subtype with hιdef
  have hι : Function.Injective ι := fun x y hxy =>
    Prod.ext (by simpa [hιdef] using congrArg Prod.fst hxy)
      (Subtype.ext (by simpa [hιdef] using congrArg Prod.snd hxy))
  have hRι : R ≤ ι.range := fun x hx => by
    have : x.2 ∈ S := hsnd ▸ ⟨x, hx, rfl⟩
    exact ⟨(x.1, ⟨x.2, this⟩), rfl⟩
  have hR' : R.comap ι = ⊤ := by
    refine eq_top_of_fst_snd_eq_top ?_ ?_ (h := h) ?_ ?_
    · refine eq_top_iff.mpr fun a _ => ?_
      obtain ⟨x, hx, rfl⟩ : a ∈ R.map (MonoidHom.fst P₁ P₂) := hfst ▸ Subgroup.mem_top a
      exact ⟨(x.1, ⟨x.2, hsnd ▸ ⟨x, hx, rfl⟩⟩), hx, rfl⟩
    · refine eq_top_iff.mpr fun s _ => ?_
      obtain ⟨x, hx, hxs⟩ : (s : P₂) ∈ R.map (MonoidHom.snd P₁ P₂) := hsnd ▸ s.2
      exact ⟨(x.1, s), by
        show ι (x.1, s) ∈ R
        have : ι (x.1, s) = x := Prod.ext rfl hxs.symm
        rw [this]; exact hx, rfl⟩
    · rw [hZ₁, Subgroup.mem_bot]; exact hh
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      show ι y ∈ R ↔ ι ((h, 1) * y * (h, 1)⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp hN (ι y)
  have hRr : R = ι.range := by
    refine le_antisymm hRι fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    have : y ∈ R.comap ι := hR' ▸ Subgroup.mem_top y
    exact this
  exact ⟨(MulEquiv.subgroupCongr hRr).trans (MonoidHom.ofInjective hι).symm⟩

theorem not_isQuasisimple_bar2_of_fst_eq_top {P₁ P₂ : Type} [Group P₁] [Group P₂]
    [IsSimpleGroup P₁] (hZ₁ : Subgroup.center P₁ = ⊥) (hnp₁ : ¬ IsPGroup 2 P₁)
    {S : Subgroup P₂} [IsSimpleGroup ↥S] (hZS : Subgroup.center ↥S = ⊥) (hnpS : ¬ IsPGroup 2 ↥S)
    {R : Subgroup (P₁ × P₂)} (hfst : R.map (MonoidHom.fst P₁ P₂) = ⊤)
    (hsnd : R.map (MonoidHom.snd P₁ P₂) = S) {h : P₁} (hh : h ≠ 1)
    (hN : ((h, 1) : P₁ × P₂) ∈ Subgroup.normalizer (R : Set (P₁ × P₂))) :
    ¬ CFSG.IsQuasisimple (↥R ⧸ CFSG.pCore 2 ↥R) := by
  intro hq
  obtain ⟨e⟩ := nonempty_mulEquiv_prod_of_fst_eq_top hZ₁ hfst hsnd hh hN
  have hO : CFSG.pCore 2 (P₁ × ↥S) = ⊥ :=
    eq_bot_of_normal_isPGroup_prod hnp₁ hnpS (CFSG.pCore_normal (p := 2)) CFSG.pCore_isPGroup
  obtain ⟨f⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
    e.toMonoidHom e.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact IsPGroup.of_bot)
  have e2 := f.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  exact not_isQuasisimple_prod hZ₁ hZS
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (hq.of_mulEquiv e2.symm)))

end Generic

theorem exists_mulEquiv_statedSU_of_isU3 {Y : Type} [Group Y] {n : ℕ} (hY : IsU3 Y n)
    (heven : Even n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 2 ∧
      Nonempty (Y ≃* StatedSU 3 (2 ^ n) K) := by
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have hmod : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
    have hnot : ¬ 3 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
      norm_num
    exact Nat.prime_three.coprime_iff_not_dvd.2 hnot
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K := unitaryFieldDataOfCard hK
  have hbot : unitaryScalars h 3 = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, card_unitaryScalars h (by norm_num : 1 ≤ 3), hgcd]
  have hinj : Function.Injective (unitaryProj h 3) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj]
    exact hbot
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e0.trans ((unitaryPSUEquivStated hK).symm.trans
    (MulEquiv.ofBijective (unitaryProj h 3) ⟨hinj, unitaryProj_surjective h 3⟩).symm)⟩⟩

theorem two_le_pRank_u3_of_even {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsU3 X n)
    (heven : Even n) (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    have hmod : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
    omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hKu : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [hKu]; exact hpd.mul_right _)
  have hζq : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hpd)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_torus hp3 hζ (i₀ := (0 : Fin 3))
    (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide)
    (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq0
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζq,
        CFSG.SectionRank.ClassicalEven.torusVec_one]))
    (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq0
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζq,
        CFSG.SectionRank.ClassicalEven.torusVec_one]))

theorem perfect_eq_bot_or_top_of_isL2_of_card {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hn : 2 ≤ n) (hY : IsL2 Y n) {T Q : Subgroup Y} (hTc : IsMulCommutative T)
    (hT : Nat.card T = 2 ^ n - 1) (hQ : ⁅Q, Q⁆ = Q)
    (hTQ : T ≤ Subgroup.normalizer (Q : Set Y)) : Q = ⊥ ∨ Q = ⊤ := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_sl2_of_isL2 hY
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hT]
    omega
  obtain ⟨d, hd⟩ := exists_ne (1 : T)
  have hd1 : (d : Y) ≠ 1 := fun h => hd (Subtype.ext h)
  have hdT : (d : Y) ^ (2 ^ n - 1) = 1 := by
    rw [← hT, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
  have hdF : (d : Y) ^ (Nat.card F - 1) = 1 := by rw [hF]; exact hdT
  have hCd : Nat.card (Subgroup.centralizer ({(d : Y)} : Set Y)) = 2 ^ n - 1 := by
    rw [← CFSG.LocalAnalysis.EvenBN.Common.centralizer_zpowers,
      CFSG.LocalAnalysis.EvenBN.Common.card_centralizer_zpowers e hd1 hdF, hF]
  have hTC : T ≤ Subgroup.centralizer ({(d : Y)} : Set Y) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hTc.is_comm.comm ⟨t, ht⟩ d))
  have hTeq : T = Subgroup.centralizer ({(d : Y)} : Set Y) :=
    Subgroup.eq_of_le_of_card_ge hTC (by rw [hCd, hT])
  exact perfect_eq_bot_or_top_of_isL2 hn hY hd1 hdT hQ (hTeq ▸ hTQ)

theorem su3_trichotomy_coords (hU : K_19_19_su3TorusIrred) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 4 ≤ n) (heven : Even n)
    {T R : Subgroup (StatedSU 3 (2 ^ n) K)} (hTc : IsMulCommutative T)
    (hT : Nat.card T = 2 ^ n - 1) (hRR : ⁅R, R⁆ = R)
    (hTR : T ≤ Subgroup.normalizer (R : Set (StatedSU 3 (2 ^ n) K)))
    {v : Fin 3 → K} (hvT : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v)
    (hvU : ∀ w : Fin 3 → K,
      (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w) → ∃ c : K, w = c • v)
    {L : Subgroup (StatedSU 3 (2 ^ n) K)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v)
    (hL2 : IsL2 L n) : R = ⊥ ∨ R = L ∨ R = ⊤ := by
  have hn2 : 2 ≤ n := by omega
  by_cases hred : ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ t ∈ T, ∀ w ∈ W, ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) ∧
      ∀ h ∈ R, ∀ w ∈ W, ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W
  · obtain ⟨W, hW0, hW1, hWT, hWR⟩ := hred
    have hRL : R ≤ L := fun g hg => (hL g).mpr
      (fixes_of_reducible_su3 hK hT hRR hvT hvU hWT hWR hW0 hW1 g hg)
    have hTL : T ≤ L := fun b hb => (hL b).mpr (hvT b hb)
    have hRQ : (R.subgroupOf L).map L.subtype = R := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hRL]
    have hQ : ⁅R.subgroupOf L, R.subgroupOf L⁆ = R.subgroupOf L :=
      Subgroup.map_injective L.subtype_injective (by rw [Subgroup.map_commutator, hRQ, hRR])
    have hTc' : IsMulCommutative (T.subgroupOf L) := by
      refine ⟨⟨fun a b => (Subgroup.subgroupOfEquivOfLe hTL).injective ?_⟩⟩
      rw [map_mul, map_mul]
      exact hTc.is_comm.comm _ _
    have hT' : Nat.card (T.subgroupOf L) = 2 ^ n - 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT]
    have hTQ : T.subgroupOf L ≤ Subgroup.normalizer ((R.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro q
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hTR (Subgroup.mem_subgroupOf.mp ht)) q
    rcases perfect_eq_bot_or_top_of_isL2_of_card hn2 hL2 hTc' hT' hQ hTQ with h | h
    · left
      rw [← hRQ, h, Subgroup.map_bot]
    · right; left
      rw [← hRQ, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · right; right
    refine hU K n hK hn heven T R hTc hT hRR hTR fun W hWT hWR => ?_
    by_contra h
    exact hred ⟨W, fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1), hWT, hWR⟩

theorem perfect_u3_trichotomy (hU : K_19_19_su3TorusIrred) {Y : Type} [Group Y] [Finite Y]
    {n : ℕ} (hY : IsU3 Y n) (hn : 4 ≤ n) (heven : Even n) {T : Subgroup Y}
    (hTc : IsMulCommutative T) (hT : Nat.card T = 2 ^ n - 1) :
    ∃ L : Subgroup Y, IsL2 L n ∧ T ≤ L ∧ ∀ R : Subgroup Y, ⁅R, R⁆ = R →
      T ≤ Subgroup.normalizer (R : Set Y) → R = ⊥ ∨ R = L ∨ R = ⊤ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_statedSU_of_isU3 hY heven
  have hn2 : 2 ≤ n := by omega
  set T' := T.map e.toMonoidHom with hT'def
  have hTc' : IsMulCommutative T' := by
    have : IsMulCommutative T := hTc
    exact Subgroup.map_isMulCommutative T e.toMonoidHom
  have hT' : Nat.card T' = 2 ^ n - 1 := by rw [Subgroup.card_map_of_injective e.injective, hT]
  obtain ⟨v, -, hvT, hvU, L', hL', hL'2⟩ := exists_fixVec_isL2_of_torus hK hn2 hTc' hT'
  have hLf : (L'.map e.symm.toMonoidHom).map e.toMonoidHom = L' := by
    rw [Subgroup.map_map]
    simp
  have hTL' : T' ≤ L' := fun b hb => (hL' b).mpr (hvT b hb)
  refine ⟨L'.map e.symm.toMonoidHom, CFSG.Blueprint.LieModel.of_mulEquiv
    ((MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr hLf)).symm hL'2,
    fun t ht => ⟨e t, hTL' ⟨t, ht, rfl⟩, by simp⟩, fun R hRR hTR => ?_⟩
  have hRR' : ⁅R.map e.toMonoidHom, R.map e.toMonoidHom⁆ = R.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, hRR]
  have hTR' : T' ≤ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hTR
  rcases su3_trichotomy_coords hU hK hn heven hTc' hT' hRR' hTR' hvT hvU hL' hL'2 with
    h | h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h)
  · exact Or.inr (Or.inl
      (Subgroup.map_injective (f := e.toMonoidHom) e.injective (h.trans hLf.symm)))
  · refine Or.inr (Or.inr (Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_))
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]

theorem eq_bot_prod_of_map_fst_eq_bot {P₁ P₂ : Type} [Group P₁] [Group P₂]
    {R : Subgroup (P₁ × P₂)} (h : R.map (MonoidHom.fst P₁ P₂) = ⊥) :
    R = (⊥ : Subgroup P₁).prod (R.map (MonoidHom.snd P₁ P₂)) := by
  have h1 : ∀ x ∈ R, x.1 = 1 := fun x hx => by
    have : x.1 ∈ R.map (MonoidHom.fst P₁ P₂) := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  refine le_antisymm (fun x hx => Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr (h1 x hx),
    Subgroup.mem_map_of_mem (MonoidHom.snd P₁ P₂) hx⟩) fun x hx => ?_
  obtain ⟨hx1, y, hy, hyx⟩ := Subgroup.mem_prod.mp hx
  have : x = y := Prod.ext ((Subgroup.mem_bot.mp hx1).trans (h1 y hy).symm) hyx.symm
  rw [this]
  exact hy

theorem eq_prod_bot_of_map_snd_eq_bot {P₁ P₂ : Type} [Group P₁] [Group P₂]
    {R : Subgroup (P₁ × P₂)} (h : R.map (MonoidHom.snd P₁ P₂) = ⊥) :
    R = (R.map (MonoidHom.fst P₁ P₂)).prod (⊥ : Subgroup P₂) := by
  have h2 : ∀ x ∈ R, x.2 = 1 := fun x hx => by
    have : x.2 ∈ R.map (MonoidHom.snd P₁ P₂) := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  refine le_antisymm (fun x hx => Subgroup.mem_prod.mpr
    ⟨Subgroup.mem_map_of_mem (MonoidHom.fst P₁ P₂) hx, Subgroup.mem_bot.mpr (h2 x hx)⟩)
    fun x hx => ?_
  obtain ⟨⟨y, hy, hyx⟩, hx2⟩ := Subgroup.mem_prod.mp hx
  have : x = y := Prod.ext hyx.symm ((Subgroup.mem_bot.mp hx2).trans (h2 y hy).symm)
  rw [this]
  exact hy

theorem simple_facts_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) (hY : IsL2 Y n) :
    IsSimpleGroup Y ∧ Subgroup.center Y = ⊥ ∧ ¬ IsPGroup 2 Y :=
  ⟨isSimpleGroup_of_isL2 hn hY, center_eq_bot_of_isL2 hY, not_isPGroup_two_of_isL2 hn hY⟩

theorem simple_facts_of_isU3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU3 Y n) :
    IsSimpleGroup Y ∧ Subgroup.center Y = ⊥ ∧ ¬ IsPGroup 2 Y := by
  have := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hY
  exact ⟨this, S17.center_eq_bot_of_isU3 hY,
    not_isPGroup_two_of_simple (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hY)⟩

theorem map_perfect_normalizer {G Y : Type*} [Group G] [Group Y] (f : G →* Y)
    {T R : Subgroup G} (hRR : ⁅R, R⁆ = R) (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R.map f, R.map f⁆ = R.map f ∧
      T.map f ≤ Subgroup.normalizer ((R.map f : Subgroup Y) : Set Y) :=
  ⟨by rw [← Subgroup.map_commutator, hRR],
    (Subgroup.map_mono hTR).trans (Subgroup.le_normalizer_map f)⟩

theorem l2u3_image_cases (hU : K_19_19_su3TorusIrred) {P₁ P₂ : Type} [Group P₁] [Group P₂]
    [Finite P₁] [Finite P₂] {n : ℕ} (hn : 4 ≤ n) (heven : Even n) (h₁ : IsL2 P₁ n)
    (h₂ : IsU3 P₂ n) {T R : Subgroup (P₁ × P₂)} (hT : IsZModSq T n) (hRR : ⁅R, R⁆ = R)
    (hTR : T ≤ Subgroup.normalizer (R : Set (P₁ × P₂)))
    (hq : CFSG.IsQuasisimple (↥R ⧸ CFSG.pCore 2 ↥R)) :
    ∃ L : Subgroup P₂, IsL2 L n ∧ (R = (⊤ : Subgroup P₁).prod ⊥ ∨
      R = (⊥ : Subgroup P₁).prod L ∨ R = (⊥ : Subgroup P₁).prod ⊤) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hT1, hT2, hTp⟩ := torus_l2u3 hn2 heven h₁ h₂ hT
  have : IsMulCommutative T := S19.isMulCommutative_of_isZModSq hT
  obtain ⟨hR₁, hT₁⟩ := map_perfect_normalizer (MonoidHom.fst P₁ P₂) hRR hTR
  obtain ⟨hR₂, hT₂⟩ := map_perfect_normalizer (MonoidHom.snd P₁ P₂) hRR hTR
  obtain ⟨L, hL, -, htri⟩ := perfect_u3_trichotomy hU h₂ hn heven
    (Subgroup.map_isMulCommutative T _) hT2
  refine ⟨L, hL, ?_⟩
  have := isSimpleGroup_of_isL2 hn2 h₁
  rcases perfect_eq_bot_or_top_of_isL2_of_card hn2 h₁ (Subgroup.map_isMulCommutative T _) hT1
      hR₁ hT₁ with h1 | h1
  · have hR := eq_bot_prod_of_map_fst_eq_bot h1
    rcases htri _ hR₂ hT₂ with h2 | h2 | h2 <;> rw [h2] at hR
    · rw [Subgroup.bot_prod_bot] at hR
      subst hR
      exact absurd IsPGroup.of_bot (not_isPGroup_two_of_isQuasisimple_bar2 hq)
    · exact Or.inr (Or.inl hR)
    · exact Or.inr (Or.inr hR)
  have : Nontrivial ↥(T.map (MonoidHom.fst P₁ P₂)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hT1]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨h, hh⟩ := exists_ne (1 : ↥(T.map (MonoidHom.fst P₁ P₂)))
  have hh1 : (h : P₁) ≠ 1 := fun e => hh (Subtype.ext e)
  have hN : ((h : P₁), (1 : P₂)) ∈ Subgroup.normalizer (R : Set (P₁ × P₂)) :=
    hTR (hTp.ge (Subgroup.mem_prod.mpr ⟨h.2, Subgroup.one_mem _⟩))
  rcases htri _ hR₂ hT₂ with h2 | h2 | h2
  · exact Or.inl ((eq_prod_bot_of_map_snd_eq_bot h2).trans (by rw [h1]))
  · obtain ⟨hLs, hLZ, hLp⟩ := simple_facts_of_isL2 hn2 hL
    exact absurd hq (not_isQuasisimple_bar2_of_fst_eq_top (center_eq_bot_of_isL2 h₁)
      (not_isPGroup_two_of_isL2 hn2 h₁) hLZ hLp h1 h2 hh1 hN)
  · obtain ⟨hTs, hTZ, hTp2⟩ := simple_facts_of_isU3
      (CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv.symm h₂ :
        IsU3 ↥(⊤ : Subgroup P₂) n)
    exact absurd hq (not_isQuasisimple_bar2_of_fst_eq_top (center_eq_bot_of_isL2 h₁)
      (not_isPGroup_two_of_isL2 hn2 h₁) hTZ hTp2 h1 h2 hh1 hN)

noncomputable def botProdEquiv {P₁ P₂ : Type} [Group P₁] [Group P₂] (S : Subgroup P₂) :
    ↥((⊥ : Subgroup P₁).prod S) ≃* ↥S :=
  (Subgroup.prodEquiv ⊥ S).trans MulEquiv.uniqueProd

theorem map_ne_bot_of_isQuasisimple {X Y : Type} [Group X] [Group Y] {I J : Subgroup X}
    (hJI : J ≤ I) (φ : ↥I →* Y) (hk : IsPGroup 2 φ.ker) (hq : CFSG.IsQuasisimple (Bar2 J)) :
    (J.subgroupOf I).map φ ≠ ⊥ := by
  intro hR0
  apply not_isPGroup_two_of_isQuasisimple_bar2 hq
  have hker : (restr φ hJI).ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : restr φ hJI x ∈ (restr φ hJI).range := ⟨x, rfl⟩
    rw [range_restr, hR0, Subgroup.mem_bot] at hx
    exact hx
  have h2 := isPGroup_ker_restr φ hk hJI
  rw [hker] at h2
  exact h2.of_equiv Subgroup.topEquiv

theorem torusQS_l2u3_qs_bot_prod {X P₁ P₂ : Type} [Group X] [Group P₁] [Group P₂]
    [Finite P₁] [Finite P₂] {I J : Subgroup X} {n : ℕ} (hn : 2 ≤ n) (h₂ : IsU3 P₂ n)
    (φ : ↥I →* P₁ × P₂)
    (hφ : Function.Surjective φ) (hk : IsPGroup 2 φ.ker) (hJI : J ≤ I)
    (hJ : commutator ↥J = ⊤) (hq : CFSG.IsQuasisimple (Bar2 J)) {L : Subgroup P₂}
    (hL : IsL2 L n) (hRL : (J.subgroupOf I).map φ = (⊥ : Subgroup P₁).prod L) :
    IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
      CFSG.IsQuasisimple (Bar2 K) ∧ J ≤ K ∧ IsU3 (Bar2 K) n := by
  obtain ⟨hLs, -, hLp⟩ := simple_facts_of_isL2 hn hL
  have hOR : ∀ P : Subgroup ↥((⊥ : Subgroup P₁).prod L), P.Normal → IsPGroup 2 P → P = ⊥ :=
    fun P hP h2 => eq_bot_of_normal_isPGroup_of_mulEquiv' (botProdEquiv L)
      (fun Q hQ hQ2 => eq_bot_of_normal_isPGroup_of_simple hLp hQ hQ2) hP h2
  obtain ⟨eJ⟩ := nonempty_bar2_equiv_of_map_eq φ hk hJI hRL hOR
  have : ((⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂)).Normal := by
    rw [← MonoidHom.ker_fst]; exact MonoidHom.normal_ker _
  have hU3 : IsU3 ↥((⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂)) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv prodBotTopEquiv.symm h₂
  obtain ⟨hNs, -, hNp⟩ := simple_facts_of_isU3 hU3
  obtain ⟨K, hKI, hKn, hKK, ⟨eK⟩, hJK⟩ := exists_normalClosure_bar2_equiv_of_le hJI φ hφ hk hJ hNp
    (by rw [hRL]; exact Subgroup.prod_mono le_rfl le_top) (map_ne_bot_of_isQuasisimple hJI φ hk hq)
  exact ⟨CFSG.Blueprint.LieModel.of_mulEquiv (eJ.trans (botProdEquiv L)).symm hL, K, hKI, hKn,
    hKK, (isQuasisimple_of_simple'
      (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hU3)).of_mulEquiv eK, hJK,
    CFSG.Blueprint.LieModel.of_mulEquiv eK.symm hU3⟩

theorem torusQS_l2u3_qs_of_coords (hU : K_19_19_su3TorusIrred) {X P₁ P₂ : Type} [Group X]
    [Finite X] [Group P₁] [Group P₂] [Finite P₁] [Finite P₂] {I A J : Subgroup X} {n p : ℕ}
    (hn : 4 ≤ n) (heven : Even n) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n + 1)
    (h₁ : IsL2 P₁ n) (h₂ : IsU3 P₂ n) (φ : ↥I →* P₁ × P₂) (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 φ.ker) (hT : IsZModSq ↥((A.subgroupOf I).map φ) n) (hJI : J ≤ I)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hJ : commutator ↥J = ⊤)
    (hq : CFSG.IsQuasisimple (Bar2 J)) (hpr : CFSG.Open.pRank p (⊤ : Subgroup ↥J) ≤ 1) :
    IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
      CFSG.IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
      (J ⊔ CFSG.Open.pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n) := by
  have hn2 : 2 ≤ n := by omega
  set ψ := restr φ hJI with hψdef
  have hkψ : IsPGroup 2 ψ.ker := isPGroup_ker_restr φ hk hJI
  have hTR : (A.subgroupOf I).map φ ≤ Subgroup.normalizer (ψ.range : Set (P₁ × P₂)) := by
    rw [hψdef, range_restr φ hJI]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map φ)
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_normalizer_iff]
    intro j
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hAJ ha) (j : X)
  obtain ⟨eJ⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
    ψ.rangeRestrict ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hkψ)
  obtain ⟨L, hL, h | h | h⟩ := l2u3_image_cases hU hn heven h₁ h₂ hT
    (commutator_range_eq_self' hJ ψ) hTR (hq.of_mulEquiv eJ.symm)
  · have : ((⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂)).Normal := by
      rw [← MonoidHom.ker_snd]; exact MonoidHom.normal_ker _
    obtain ⟨hL2, K, hKI, hKn, hKK, hKq, hJK, hJO⟩ := conclusion_of_normal_image hJI φ hφ hk hJ hn2
      ((range_restr φ hJI).symm.trans h)
      (CFSG.Blueprint.LieModel.of_mulEquiv prodTopBotEquiv.symm h₁)
    exact ⟨hL2, K, hKI, hKn, hKK,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hKq),
      hJK, Or.inl hJO⟩
  · obtain ⟨hL2, K, hKI, hKn, hKK, hKq, hJK, hKU⟩ := torusQS_l2u3_qs_bot_prod hn2 h₂ φ hφ hk hJI
      hJ hq hL ((range_restr φ hJI).symm.trans h)
    exact ⟨hL2, K, hKI, hKn, hKK, hKq, hJK, Or.inr (Or.inr hKU)⟩
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    have hpR : CFSG.Open.pRank p ψ.range ≤ 1 := by rw [pRank_range_eq ψ hkψ hp hp2]; exact hpr
    rw [h, ← CFSG.Quasithin.pRank_top_subtype,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt prodBotTopEquiv] at hpR
    have := two_le_pRank_u3_of_even h₂ heven hp hpd
    omega

end TorusQS

open TorusQS

theorem even_four_le_of_isPowTwo {n : ℕ} (hpow : IsPowTwo n) (hn : 3 ≤ n) : Even n ∧ 4 ≤ n := by
  obtain ⟨k, rfl⟩ := hpow
  rcases k with _ | _ | k
  · norm_num at hn
  · norm_num at hn
  · refine ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, ?_⟩
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem k_19_19_torusQS_l2u3_of_irred (hU : K_19_19_su3TorusIrred) : K_19_19_torusQS_l2u3 := by
  intro X _ _ I A J n p hn hp hp2 hshape hAI hA hJI hAJ hO hpr hcase _
  obtain ⟨hprod, hpow, hcong⟩ := hshape
  obtain ⟨heven, hn4⟩ := even_four_le_of_isPowTwo hpow hn
  rcases hcase with hg | hq
  · exact Or.inl (subset_pCore_mul_of_not_three_dvd_relIndex hAI hJI hAJ hg.1
      (not_three_dvd_relIndex_of_l2u3 (by omega) heven hprod hAI hA))
  right
  obtain ⟨P₁, P₂, _, _, ⟨eI⟩, h₁, h₂⟩ := hprod
  have : Finite (Bar2 I) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  have : Finite (P₁ × P₂) := Finite.of_equiv _ eI.toEquiv
  have : Finite P₁ := Finite.of_injective (fun a : P₁ => ((a, 1) : P₁ × P₂))
    (fun a b h => congrArg Prod.fst h)
  have : Finite P₂ := Finite.of_injective (fun b : P₂ => ((1, b) : P₁ × P₂))
    (fun a b h => congrArg Prod.snd h)
  have hJ : commutator ↥J = ⊤ := commutator_eq_top_of_commutator_eq_self'
    (commutator_eq_self_of_oUpperTwo hO (by have := hq.1; exact Group.IsPerfect.commutator_eq_top))
  set φ : ↥I →* P₁ × P₂ := eI.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) with hφdef
  have hk : IsPGroup 2 φ.ker := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).to_le fun x hx => by
    have h0 : eI (QuotientGroup.mk' (CFSG.pCore 2 ↥I) x) = 1 := hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) x = 1 := (MulEquiv.map_eq_one_iff eI).mp h0
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hginj : Function.Injective (restr φ hAI) :=
    injective_of_isPGroup_ker_of_odd' _ (isPGroup_ker_restr φ hk hAI)
      (odd_card_of_isZModSq' (by omega) hA)
  have hTZ : IsZModSq ↥((A.subgroupOf I).map φ) n := by
    obtain ⟨e⟩ := hA
    exact ⟨(MulEquiv.subgroupCongr (range_restr φ hAI)).symm.trans
      ((MonoidHom.ofInjective hginj).symm.trans e)⟩
  exact torusQS_l2u3_qs_of_coords hU hn4 heven hp hp2 (P2214R.dvd_of_cong hcong) h₁ h₂ φ
    (eI.surjective.comp (QuotientGroup.mk'_surjective _)) hk hTZ hJI hAJ hJ hq
    (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hpr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
