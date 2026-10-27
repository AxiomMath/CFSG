module

public import CFSG.Quasithin.Background.C41PfM
public import CFSG.Quasithin.Background.C41PfG
public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Sporadic.Schreier.TitsIso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C41Pf

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod
open scoped commutatorElement

section Type345

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_isPSL_of_parabolic {K P P₀ : Subgroup G} {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hψs : Function.Surjective ψ)
    (hψker : ∀ k : ↥K, ψ k = 1 → (k : G) ∈ pCoreOf 2 K)
    (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
    (hPN : P ≤ Subgroup.normalizer (P₀ : Set G)) (hperf : ⁅P₀, P₀⁆ = P₀) (hP₀1 : P₀ ≠ ⊥) :
    ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ Nonempty (ModO2 P₀ ≃* SpecialLinearGroup (Fin m) (ZMod 2)) := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK', S, hS, hSP⟩ := hpar
  have hP₀K : P₀ ≤ K := hP₀P.trans hPK'
  have hO2S : pCoreOf 2 K ≤ S :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hSP' : S ≤ P := fun s hs => hSP ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  set S' : Subgroup ↥K := S.subgroupOf K with hS'
  have hS'syl : CFSG.QuasithinUnique.IsSylowTwoOf (S'.map ψ) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hSp : IsPGroup 2 ↥S' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      exact hSp.map ψ
    · show ¬ 2 ∣ (S'.map ψ).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro h2
      exact hS.2.2 (h2.trans (Subgroup.index_map_dvd _ hψs))
  obtain ⟨Pu, hPu⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    hPu ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Pu
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hUsyl hS'syl
  set θ₀ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ₀def
  have hθ₀ : ∀ k, θ₀ k = g⁻¹ * ψ k * g := fun k => by
    simp [θ₀]
  have hθ₀ker : ∀ k, θ₀ k = 1 → (k : G) ∈ pCoreOf 2 K := fun k hk => by
    apply hψker
    rw [hθ₀] at hk
    have : ψ k = g * (g⁻¹ * ψ k * g) * g⁻¹ := by group
    rw [this, hk]
    group
  have hθS : S'.map θ₀ = unitriangular n (ZMod 2) := by
    rw [hθ₀def, ← Subgroup.map_map, ← hg, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (SpecialLinearGroup (Fin n) (ZMod 2)) := by
      ext x : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  set P' : Subgroup ↥K := P.subgroupOf K with hP'
  set Q := P'.map θ₀ with hQ
  have hUQ : upperTriangular n (ZMod 2) ≤ Q := by
    refine (upperTriangular_le_unitriangular hK2).trans ?_
    rw [← hθS]
    exact Subgroup.map_mono fun x hx => hSP' hx
  obtain ⟨hQI, -⟩ := borel_overgroups Q hUQ
  set I := borelOvergroupCuts Q with hI
  have hIcuts : ∀ c ∈ I, 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  have hQtop : Q ≠ ⊤ := by
    intro hQt
    apply hPK
    refine le_antisymm hPK' fun k hk => ?_
    obtain ⟨p, hp, hpk⟩ : θ₀ ⟨k, hk⟩ ∈ Q := hQt ▸ Subgroup.mem_top _
    have h1 : θ₀ (p⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hpk, inv_mul_cancel]
    have h3 : ((p⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ P := hSP' (hO2S (hθ₀ker _ h1))
    have h4 : (p : G) ∈ P := hp
    have := P.mul_mem h4 h3
    simpa using this
  set P₀' : Subgroup ↥K := P₀.subgroupOf K with hP₀'
  set R₀ := P₀'.map θ₀ with hR₀
  have hR₀Q : R₀ ≤ Q := Subgroup.map_mono fun x hx => hP₀P hx
  have hR₀N : Q ≤ Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨p * x * p⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 (hPN hp) x).1 hx
    · rintro ⟨x, hx, hxy⟩
      refine ⟨p⁻¹ * x * p, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hPN (P.inv_mem hp)) x).1 hx
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simpa using this
      · rw [map_mul, map_mul, map_inv, hxy]
        group
  have hR₀perf : ⁅R₀, R₀⁆ = R₀ := by
    have hP₀'perf : ⁅P₀', P₀'⁆ = P₀' := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, hP₀', Subgroup.map_subgroupOf_eq_of_le hP₀K, hperf]
    rw [hR₀, ← Subgroup.map_commutator, hP₀'perf]
  have hP₀ne : ¬ P₀ ≤ pCoreOf 2 K := by
    intro hle
    have hp : IsPGroup 2 ↥P₀ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hle
    exact hP₀1 (eq_bot_of_perfect_of_isPGroup hperf hp)
  have hR₀ne : R₀ ≠ ⊥ := by
    intro hbot
    apply hP₀ne
    intro x hx
    have h1 : θ₀ ⟨x, hP₀K hx⟩ = 1 := by
      have : θ₀ ⟨x, hP₀K hx⟩ ∈ R₀ := ⟨⟨x, hP₀K hx⟩, hx, rfl⟩
      rw [hbot] at this
      exact this
    exact hθ₀ker _ h1
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m', h, hm3, ha, hb, hno⟩
  · exfalso
    have hbot := perfectCore_eq_bot_of_small hK2 (by omega) hsmall
    apply hR₀ne
    rw [eq_bot_iff, ← hbot]
    exact le_perfectCore_of_perfect (hR₀Q.trans hQI.le) hR₀perf
  have hmn : m' < n := by
    by_contra hmn
    apply hQtop
    have hIe : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨h1, h2⟩ := hIcuts c hc
      exact hno c hc ⟨by omega, by omega⟩
    rw [hQI, hIe, flagStabilizer_empty]
  have hR₀eq : R₀ = perfectCore (flagStabilizer n (ZMod 2) I) :=
    eq_perfectCore_of_normal hn5 (by omega) h hm3 ha hb hno (hR₀Q.trans hQI.le)
      (hQI.ge.trans hR₀N) hR₀perf hR₀ne
  set bb := bigBlockHom (K := ZMod 2) I a m' h ha hb with hbb
  have hbbs : Function.Surjective bb := bigBlockHom_surjective hK2 h hm3 ha hb hno
  have hθmem : ∀ x : ↥P₀, θ₀ ⟨x, hP₀K x.2⟩ ∈ perfectCore (flagStabilizer n (ZMod 2) I) :=
    fun x => hR₀eq ▸ ⟨⟨x, hP₀K x.2⟩, x.2, rfl⟩
  set α' : ↥P₀ →* ↥(perfectCore (flagStabilizer n (ZMod 2) I)) :=
    (θ₀.comp (Subgroup.inclusion hP₀K)).codRestrict _ hθmem with hα'
  have hα'v : ∀ x, ((α' x : ↥(perfectCore (flagStabilizer n (ZMod 2) I))) :
      SpecialLinearGroup (Fin n) (ZMod 2)) = θ₀ ⟨x, hP₀K x.2⟩ := fun x => rfl
  have hα's : Function.Surjective α' := by
    rintro ⟨y, hy⟩
    rw [← hR₀eq] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  set α := bb.comp α' with hα
  have hαs : Function.Surjective α := hbbs.comp hα's
  have hker2 : IsPGroup 2 ↥α.ker := by
    rintro ⟨x, hx⟩
    have hU := unitriangular_of_bigBlockHom hK2 hn5 h hm3 ha hb hno (α' x) hx
    obtain ⟨j, hj⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) (by omega) ⟨_, hU⟩
    have hj' : θ₀ ⟨x, hP₀K x.2⟩ ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa [hα'v] using this
    have h1 : θ₀ (⟨x, hP₀K x.2⟩ ^ 2 ^ j) = 1 := by rw [map_pow, hj']
    obtain ⟨i, hi⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hθ₀ker _ h1⟩
    refine ⟨j + i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hi
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    simpa using this
  have hsimp := sl_isSimple_of_card_two hK2 hm3
  have hnab := sl_nonabelian_of_card_two hK2 hm3
  have hkerα : α.ker = CFSG.pCore 2 ↥P₀ := (pCore_two_eq_ker hnab α hαs hker2).symm
  have hm' : m' = 3 ∨ m' = 4 := by omega
  exact ⟨m', hm', ⟨modO2EquivOfHom hnab α hαs hker2⟩⟩

end Type345

section Lift

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isParabolic2_of_autOn {K P W : Subgroup G} (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hPK : P ≤ K) (hCP : K ⊓ Subgroup.centralizer (W : Set G) ≤ P)
    (hC2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (W : Set G)))
    (hpar : IsParabolic2 (autOn K W) (autOn P W)) : IsParabolic2 K P := by
  obtain ⟨-, S', hS', hB⟩ := hpar
  let φ : ↥K →* ↥(autOn K W) :=
    ((conjAct W).comp (Subgroup.inclusion hKN)).codRestrict (autOn K W) fun k =>
      ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφ1 : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro k
    have h0 := A4.conjAct_eq_one_iff (g := Subgroup.inclusion hKN k)
    exact ⟨fun h => h0.mp (congrArg Subtype.val h), fun h => Subtype.ext (h0.mpr h)⟩
  set T' : Subgroup ↥(autOn K W) := S'.subgroupOf (autOn K W) with hT'
  set S₀ : Subgroup ↥K := T'.comap φ with hS₀
  set S : Subgroup G := S₀.map K.subtype with hS
  have hSK : S ≤ K := Subgroup.map_subtype_le _
  have hSsyl : IsSylowTwoOf S K := by
    refine ⟨hSK, ?_, ?_⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩⟩
      obtain ⟨a, ha⟩ := hS'.2.1 ⟨((φ k : ↥(autOn K W)) : MulAut ↥W), hk⟩
      have h1 : φ (k ^ 2 ^ a) = 1 := by
        rw [map_pow]
        apply Subtype.ext
        have := congrArg Subtype.val ha
        simpa using this
      have h2 : ((k ^ 2 ^ a : ↥K) : G) ∈ K ⊓ Subgroup.centralizer (W : Set G) :=
        ⟨(k ^ 2 ^ a).2, (hφ1 _).mp h1⟩
      obtain ⟨b, hb⟩ := hC2 ⟨_, h2⟩
      refine ⟨a + b, Subtype.ext ?_⟩
      have := congrArg Subtype.val hb
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      simpa using this
    · have hsub : (S₀.map K.subtype).subgroupOf K = S₀ := by
        ext k
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨k', hk', he⟩
          rwa [show k = k' from Subtype.ext he.symm]
        · intro hk
          exact ⟨k, hk, rfl⟩
      rw [hS, hsub, hS₀, Subgroup.index_comap_of_surjective T' hφ]
      exact hS'.2.2
  refine ⟨hPK, S, hSsyl, ?_⟩
  rintro x ⟨hxK, hxN⟩
  have hconj : ∀ y : ↥K, (y : G) ∈ Subgroup.normalizer (S : Set G) → ∀ s ∈ S',
      ((φ y : ↥(autOn K W)) : MulAut ↥W) * s * ((φ y : ↥(autOn K W)) : MulAut ↥W)⁻¹ ∈ S' := by
    intro y hy s hs
    obtain ⟨z, hz⟩ := hφ ⟨s, hS'.1 hs⟩
    have hzS : (z : G) ∈ S := ⟨z, show φ z ∈ T' by rw [hz]; exact hs, rfl⟩
    obtain ⟨w, hw, hwe⟩ := (Subgroup.mem_normalizer_iff.mp hy z).mp hzS
    have hw' : w = y * z * y⁻¹ := Subtype.ext hwe
    have hwT : φ w ∈ T' := hw
    rw [hw', map_mul, map_mul, map_inv, hz] at hwT
    exact hwT
  have hkN : ((φ ⟨x, hxK⟩ : ↥(autOn K W)) : MulAut ↥W) ∈
      autOn K W ⊓ Subgroup.normalizer (S' : Set (MulAut ↥W)) := by
    refine ⟨(φ ⟨x, hxK⟩).2, Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs =>
      hconj ⟨x, hxK⟩ hxN s hs, fun hs => ?_⟩⟩
    have h1 := hconj ⟨x, hxK⟩⁻¹ (Subgroup.inv_mem _ hxN) _ hs
    simpa [map_inv, mul_assoc] using h1
  obtain ⟨y, hy, hye⟩ := hB hkN
  have hyK : (y : G) ∈ K := hPK hy
  have h2 : conjAct W (y⁻¹ * Subgroup.inclusion hKN ⟨x, hxK⟩) = 1 := by
    rw [map_mul, map_inv, hye]
    exact inv_mul_cancel _
  have h3 : (y : G)⁻¹ * x ∈ Subgroup.centralizer (W : Set G) := by
    simpa using A4.conjAct_eq_one_iff.mp h2
  have h4 : (y : G)⁻¹ * x ∈ P := hCP ⟨K.mul_mem (K.inv_mem hyK) hxK, h3⟩
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact P.mul_mem hy h4

end Lift

section InspH

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem c41InspH_of (hK0 : C41KZero G) (hA3 : A3Orbits G) : C41InspH G := by
  intro H R M L V K hP _ _ hc
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  have h := hP.hyp
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_omegaOneCenter K R
  obtain ⟨he45, hpar, -⟩ := hc
  obtain ⟨n, hn4, hn5, hn, ⟨e⟩⟩ : ∃ n : ℕ, 4 ≤ n ∧ n ≤ 5 ∧ (n = 4 ∨ n = 5) ∧
      Nonempty (↥(autOn K W) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) := by
    rcases he45 with he | he
    · exact ⟨4, le_rfl, by norm_num, Or.inl rfl, he⟩
    · exact ⟨5, by norm_num, le_rfl, Or.inr rfl, he⟩
  set E : SpecialLinearGroup (Fin n) (ZMod 2) ≃* ↥(autOn K W) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).trans e.symm with hE
  let φ : ↥K →* ↥(autOn K W) :=
    ((conjAct W).comp (Subgroup.inclusion hKN)).codRestrict (autOn K W) fun k =>
      ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφ1 : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro k
    have h0 := A4.conjAct_eq_one_iff (g := Subgroup.inclusion hKN k)
    exact ⟨fun h => h0.mp (congrArg Subtype.val h), fun h => Subtype.ext (h0.mpr h)⟩
  have hO2W : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G) :=
    pCoreOf_le_centralizer hP.le_normalizer
  have hnt : ¬ K ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK2 (m := n) (by omega)
    have h1 : ∀ c : SpecialLinearGroup (Fin n) (ZMod 2), E c = 1 := by
      intro c
      obtain ⟨k, hk⟩ := hφ (E c)
      rw [← hk]
      exact (hφ1 k).mpr (hle k.2)
    apply hab
    apply E.injective
    rw [map_mul, map_mul, h1 a, h1 b]
  have hsq : SQTKGroup (↥K ⧸ CFSG.pCore 2 ↥K) := S153D.sqtkGroup_quot_pCore (h.sqtk.mono hKH)
  have hL345 : IsL345Type ↥(autOn K W) := by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, hK2, ⟨e⟩⟩)
    · exact Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, hK2, ⟨e⟩⟩)
  obtain ⟨f⟩ := S153D.nonempty_quot_mulEquiv_autOn asA36NoOddCover_holds hKN hP.quasi hsq hO2W
    hnt hL345
  have hmemK : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', he⟩
      rwa [show k = k' from Subtype.ext he.symm]
  have hkerφ : φ.ker = CFSG.pCore 2 ↥K := by
    have hle : CFSG.pCore 2 ↥K ≤ φ.ker := fun k hk =>
      MonoidHom.mem_ker.mpr ((hφ1 k).mpr (hO2W ((hmemK k).mp hk)))
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    have hc2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr f.toEquiv] at hc1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv] at hc2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc1.symm.trans hc2)).symm.le
  have hCK : K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rintro x ⟨hxK, hxC⟩
    have hk : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := MonoidHom.mem_ker.mpr ((hφ1 _).mpr hxC)
    rw [hkerφ] at hk
    exact (hmemK _).mp hk
  have hO2M : pCoreOf 2 K ≤ M := by
    have hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
      hP.le.trans Subgroup.le_normalizer
    have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 K)
          (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
        (pCoreOf_isPGroup 2 K)
    exact hle.trans ((pCoreOf_sup_le_of_hyp h hKH hNK).trans h.le_M)
  have hparK : IsParabolic2 K (M ⊓ K) :=
    isParabolic2_of_autOn hKN inf_le_right (le_inf (hCK.trans hO2M) inf_le_left)
      ((pCoreOf_isPGroup 2 K).to_le hCK) hpar
  set ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) := E.symm.toMonoidHom.comp φ with hψ
  have hψs : Function.Surjective ψ := E.symm.surjective.comp hφ
  have hψker : ∀ k : ↥K, ψ k = 1 → (k : G) ∈ pCoreOf 2 K := by
    intro k hk
    have h1 : φ k = 1 := by
      have := congrArg E hk
      simpa [hψ] using this
    exact hCK ⟨k.2, (hφ1 k).mp h1⟩
  have hMK : M ⊓ K ≠ K := fun he => hP.not_le (he ▸ inf_le_left)
  obtain ⟨m, hm, ⟨f₀⟩⟩ := exists_isPSL_of_parabolic hn4 hn5 ψ hψs hψker hparK hMK
    (le_inf (C2Nine.conjClosure_le_M h) hP.le) (inf_le_left.trans (le_normalizer_conjClosure L M))
    (C2Nine.perfect_conjClosure_of_hyp h) (fun hb => ne_bot_of_mem_cComp h.comp
      (eq_bot_iff.mpr ((le_conjClosure L M).trans hb.le)))
  have hm3 : 3 ≤ m := by omega
  have : IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) := sl_isSimple_of_card_two hK2 hm3
  have hS : IsSimpleGroup (ModO2 (conjClosure L M)) := f₀.isSimpleGroup
  have hKt : IsPSL 4 2 1 (ModO2 K) ∨ IsPSL 5 2 1 (ModO2 K) := by
    have hK' := isPSL_of_mulEquiv_sl (by omega) (f.trans E.symm)
    rcases hn with rfl | rfl
    · exact Or.inl hK'
    · exact Or.inr hK'
  have hM₀t : IsPSL 3 2 1 (ModO2 (conjClosure L M)) ∨ IsPSL 4 2 1 (ModO2 (conjClosure L M)) := by
    have hM' := isPSL_of_mulEquiv_sl hm3 f₀
    rcases hm with rfl | rfl
    · exact Or.inl hM'
    · exact Or.inr hM'
  exact c41Conclusion_of_case hK0 hA3 hP hS (Or.inr (Or.inr (Or.inr ⟨hKt, hparK, hM₀t⟩)))

end InspH

end CFSG.Quasithin.C41Pf
