module

public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch11SecD551C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_eq_self {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    conjClosure K T = K :=
  le_antisymm (conjClosure_le fun _ ht x hx => (Subgroup.mem_normalizer_iff.mp (hTK ht) x).mp hx)
    (le_conjClosure _ _)

omit [Finite G] in
theorem conjV_eq_one_of_mem_centralizer {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hc : x ∈ Subgroup.centralizer (W : Set G)) :
    SecA.conjV W x hx = 1 := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [SecA.conjV_apply_coe]
  have := Subgroup.mem_centralizer_iff.mp hc w w.2
  change x * (w : G) * x⁻¹ = (w : G)
  rw [← this]
  group

omit [Finite G] in
theorem nonempty_autOn_equiv {K W : Subgroup G} (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    Nonempty (↥(autOn K W) ≃* ↥K ⧸ CFSG.pCore 2 ↥K) := by
  set ψ : ↥K →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hKN) with hψ
  have hrange : ψ.range = autOn K W := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKN k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  set ψ' : ↥K →* ↥(autOn K W) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict with hψ'
  have hψ's : Function.Surjective ψ' :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hψk : ∀ k : ↥K, ψ' k = 1 ↔ ψ k = 1 := by
    intro k
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      simpa [hψ'] using this
    · intro h1
      apply Subtype.ext
      simpa [hψ'] using h1
  have hle : CFSG.pCore 2 ↥K ≤ ψ'.ker := by
    intro k hk
    have hkO : (k : G) ∈ pCoreOf 2 K := by
      rw [← SecD.pCoreOf_subgroupOf] at hk
      exact hk
    rw [MonoidHom.mem_ker, hψk]
    exact conjV_eq_one_of_mem_centralizer (hKN k.2) (hO hkO)
  set φ := QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ' hle with hφ
  have hφs : Function.Surjective φ := by
    intro a
    obtain ⟨k, rfl⟩ := hψ's a
    exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk _ _ _⟩
  have hφi : Function.Injective φ := by
    rcases hs.eq_bot_or_eq_top_of_normal φ.ker with h0 | h0
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h0
    · exfalso
      apply hne
      intro k hk
      have h1 : φ (QuotientGroup.mk ⟨k, hk⟩) = 1 := (MonoidHom.mem_ker).mp (h0 ▸ Subgroup.mem_top _)
      rw [hφ, QuotientGroup.lift_mk, hψk] at h1
      exact SecD.mem_centralizer_of_conjV_eq_one (hKN hk) h1
  exact ⟨(MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm⟩

theorem isQuasisimple_of_isSimpleGroup_of_perfect {X : Type} [Group X] [hs : IsSimpleGroup X]
    [hp : Group.IsPerfect X] : CFSG.IsQuasisimple X := by
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact Group.IsPerfect.not_isMulCommutative X ⟨⟨hc⟩⟩
  have hZ : Subgroup.center X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a)
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hp, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem isFaithfulLocal_of (hK : QuasithinUnique.quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) {T Kp : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T Kp)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G))
    (hne : ⁅omegaOneCenterOf (pCoreOf 2 (Kp ⊔ T)), Kp⁆ ≠ ⊥) :
    quasithinIsFaithfulLocal T Kp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc := hmax.1
  have hKp : Kp ∈ cComp (Kp ⊔ T) := hloc.2.1
  have hperf : ⁅Kp, Kp⁆ = Kp := perfect_of_mem_cComp hKp
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (Kp ⊔ T) :=
    charTwo_of_inH hK.2.1 S ⟨hS ▸ le_sup_right, hloc.2.2.2⟩
  have hKM : Kp ≤ Kp ⊔ T := le_sup_left
  have hMK : Kp ⊔ T ≤ Subgroup.normalizer (Kp : Set G) := sup_le Subgroup.le_normalizer hTKp
  have hsub : IsSubnormal Kp (Kp ⊔ T) := A3.subnormal_of_normal hKM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK)
  have hKp1 : Kp ≠ ⊥ := by
    rintro rfl
    exact hne (Subgroup.commutator_bot_right _)
  have hXc : IsXClass Kp :=
    ⟨hKp1, (C2Nine.oTwoUpper_eq_of_perfect hperf).symm, A4.charTwo_of_subnormal hsub hchar⟩
  refine ⟨hloc, fun N hNK hN hpow => C2Nine.eq_of_perfect_of_pow_mem hperf hNK hN hpow,
    lemma_1_2_7_two hK hs hnab (a37ForSQTK_of_cat h37) (a39ForSQTK_of_cat h39) hT hmax, ?_⟩
  exact (a4_9 hXc hsub).mp hne

end CFSG.Quasithin.Vol2.Ch11.SecE
