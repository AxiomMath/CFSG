module

public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.RankThree.PartOne.KLC.G2
public import CFSG.Quasithin.EmptyFaithful.A38c4Main
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4A318

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Assembly.LowTwoRank

@[expose] def InspFFG2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (m n p : ℕ), 2 ≤ m → 2 ≤ n → Nat.card F = 2 ^ m →
    ∀ K : Subgroup ↥(CFSG.Open.quasithinG2 F), IsPSL 2 2 n ↥K → p.Prime → p ≠ 2 →
      p ∣ 2 ^ n - 1 → p ∣ 2 ^ (2 * m) - 1

namespace FFG2

theorem isPSL_map {X Y : Type} [Group X] [Group Y] {K : Subgroup X} (e : X ≃* Y) {n : ℕ}
    (hK : IsPSL 2 2 n ↥K) : IsPSL 2 2 n ↥(K.map e.toMonoidHom) := by
  obtain ⟨hadm, F, hF, hFin, hcard, ⟨eK⟩⟩ := hK
  exact ⟨hadm, F, hF, hFin, hcard,
    ⟨(K.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩⟩

theorem center_quasithinG2_eq_bot {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m) : Subgroup.center ↥(CFSG.Open.quasithinG2 F) = ⊥ := by
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.B42G2Id.exists_ne_zero_ne_one_of_three_le (K := F)
    (hF ▸ CFSG.Quasithin.B42G2Id.three_le_two_pow hm)
  have hZc : Subgroup.center ↥(CFSG.Quasithin.Explicit.cayleyGroup F) = ⊥ :=
    CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have e₀ : ↥(CFSG.Open.quasithinG2 F) ≃* ↥(CFSG.Quasithin.Explicit.cayleyGroup F) :=
    MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  rw [eq_bot_iff]
  intro x hx
  have hx' : e₀ x ∈ Subgroup.center ↥(CFSG.Quasithin.Explicit.cayleyGroup F) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := e₀.surjective y
    rw [← map_mul, ← map_mul, hx y']
  rw [hZc, Subgroup.mem_bot, map_eq_one_iff _ e₀.injective] at hx'
  rw [Subgroup.mem_bot]
  exact hx'

theorem isSimpleGroup_of_quasisimple {X : Type} [Group X] (hX : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := hX.2.2
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a' b'])
  let ι : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact IsSimpleGroup.isSimpleGroup_of_surjective ι.toMonoidHom ι.surjective


theorem two_le_pRank_g2 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    {m p : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) (e : X ≃* ↥(CFSG.Open.quasithinG2 F))
    (hp : p.Prime) (hpm : p ∣ 2 ^ (2 * m) - 1) : 2 ≤ CFSG.pRank p X := by
  have hZ := center_quasithinG2_eq_bot hm hF
  have hG2 := CFSG.Quasithin.factG2Cayley_holds F m hm hF
  have eq : ↥(CFSG.Open.quasithinG2 F) ⧸ Subgroup.center ↥(CFSG.Open.quasithinG2 F) ≃*
      ↥(CFSG.Open.quasithinG2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hM₀ : CFSG.Blueprint.LieModel
      (↥(CFSG.Open.quasithinG2 F) ⧸ Subgroup.center ↥(CFSG.Open.quasithinG2 F)) .G2 0 2 m :=
    Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hG2⟩)
  have hM : CFSG.Blueprint.LieModel X .G2 0 2 m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eq.trans e.symm) hM₀
  obtain ⟨K', _, _, hK'card, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartOne.Sec66T.exists_adjoint_equiv
      CFSG.RankThree.PartOne.Sec66T.untwistedTag_G2 hM
  have : CharP K' 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hK'card
  have h12 : p ∣ Nat.card K' ^ 2 - 1 := by rwa [hK'card, ← pow_mul, mul_comm]
  exact CFSG.RankThree.PartOne.KLC.two_le_pRank_of_orth_roots
    (τ := CFSG.Blueprint.Chevalley.Tag.G2) (K := K') CFSG.RankThree.PartOne.KLC.g2Orth_commute hp
    h12 e'

theorem false_of_g2
    (hR1 : InspFFG2) {G : Type} [Group G] [Finite G]
    {L K : Subgroup G} {n m p : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ m) (e : ↥L ≃* ↥(CFSG.Open.quasithinG2 F))
    (hLq : CFSG.IsQuasisimple ↥L) (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hm1 : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    by_contra h0
    have : m = 0 := by omega
    subst this
    norm_num at h2
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm : m = 1 := by omega
    subst hm
    exact CFSG.Quasithin.R3c2.not_isQuasisimple_quasithinG2_two (by rw [hF]; norm_num) e hLq
  have hpq : p ∣ 2 ^ (2 * m) - 1 := by
    have hKs : IsPSL 2 2 n ↥(K.subgroupOf L) := by
      obtain ⟨hadm, F', hF'f, hF'fin, hcard, ⟨eK⟩⟩ := hK
      exact ⟨hadm, F', hF'f, hF'fin, hcard, ⟨(Subgroup.subgroupOfEquivOfLe hKL).trans eK⟩⟩
    exact hR1 F m n p hm2 hn hF _ (isPSL_map e hKs) hp hp2 hpn
  have hrank : 2 ≤ CFSG.Open.pRank p L := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact two_le_pRank_g2 hm2 hF e hp hpq
  rcases hcase with h | ⟨rfl, S, _, φ, hφ, hker, s, q', -, hS⟩
  · omega
  obtain ⟨-, -, hnot⟩ := CFSG.Quasithin.factA318Excl_holds.1 F m hm2 hF
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e x ∈ Subgroup.center ↥(CFSG.Open.quasithinG2 F) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [center_quasithinG2_eq_bot hm2 hF, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hx'
    rw [Subgroup.mem_bot]
    exact hx'
  have hLs : IsSimpleGroup ↥L := isSimpleGroup_of_quasisimple hLq hZ
  have : IsSimpleGroup S := L436.isSimpleGroup_of_isPSLEps3q hS
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : S)
      obtain ⟨x, rfl⟩ := hφ y
      exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
  have hperf : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ = CFSG.Open.quasithinG2 F := by
    have hL := Group.isPerfect_def.mp hLq.1
    have hG : commutator ↥(CFSG.Open.quasithinG2 F) = ⊤ := by
      rw [commutator_def] at hL ⊢
      rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← Subgroup.map_commutator,
        hL]
    rw [← Subgroup.map_subtype_commutator, hG, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨r', e', -, -, -, hS'⟩ := hS
  let ψ : S ≃* ↥L := (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
  let χ : ↥(CFSG.Open.quasithinG2 F) ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    MulEquiv.subgroupCongr hperf.symm
  exact (hnot S s r' e' hS').2 ((χ.toMonoidHom.comp e.toMonoidHom).comp ψ.toMonoidHom)
    ((χ.surjective.comp e.surjective).comp ψ.surjective)

end FFG2

end CFSG.Quasithin.H13.Ch4
