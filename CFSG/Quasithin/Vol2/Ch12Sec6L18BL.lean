module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18Stmt
public import CFSG.Quasithin.Vol2.Ch12Sec6L20c
public import CFSG.Quasithin.Vol2.Ch12Sec6L16d
public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.Quasithin.H13.VolIC113c
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.F6F613Basic
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits Equiv Equiv.Perm
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126BL

abbrev P3 (i : Fin 8) : Prop := i.val < 3

@[expose] noncomputable def sym3 : Subgroup (Perm (Fin 8)) :=
  (Perm.ofSubtype : Perm {i : Fin 8 // P3 i} →* Perm (Fin 8)).range

theorem mem_sym3 {σ : Perm (Fin 8)} : σ ∈ sym3 ↔ ∀ i : Fin 8, 3 ≤ i.val → σ i = i := by
  constructor
  · rintro ⟨τ, rfl⟩ i hi
    exact ofSubtype_apply_of_not_mem τ (by simp [P3]; omega)
  · intro h
    have h₂ : ∀ x, σ x ≠ x → P3 x := fun x hx => by
      by_contra hn
      exact hx (h x (by simp [P3] at hn; omega))
    have h₁ : ∀ x, P3 (σ x) ↔ P3 x := by
      intro x
      by_cases hx : P3 x
      · refine ⟨fun _ => hx, fun _ => ?_⟩
        by_contra hn
        have h3 : 3 ≤ (σ x).val := by simp [P3] at hn; omega
        have hσx : σ x = x := σ.injective (h (σ x) h3)
        exact hn (by rw [hσx]; exact hx)
      · have hxx : σ x = x := h x (by simp [P3] at hx; omega)
        rw [hxx]
    exact ⟨σ.subtypePerm h₁, ofSubtype_subtypePerm h₁ h₂⟩

theorem card_sym3 : Nat.card sym3 = 6 := by
  rw [sym3, MonoidHom.range_eq_map, Subgroup.card_map_of_injective ofSubtype_injective,
    Subgroup.card_top, Nat.card_perm]
  have : Nat.card {i : Fin 8 // P3 i} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [this]
  rfl

@[expose] def c3 : Perm (Fin 8) := swap 0 1 * swap 1 2

theorem c3_mem_sym3 : c3 ∈ sym3 := mem_sym3.2 (by decide)

theorem swap01_mem_sym3 : swap (0 : Fin 8) 1 ∈ sym3 := mem_sym3.2 (by decide)

theorem isThreeCycle_c3 : c3.IsThreeCycle := by
  rw [c3, swap_comm 0 1]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem orderOf_c3 : orderOf c3 = 3 := isThreeCycle_c3.orderOf

theorem c3_mem_alt : c3 ∈ alternatingGroup (Fin 8) := isThreeCycle_c3.mem_alternatingGroup

theorem orderOf_swap01 : orderOf (swap (0 : Fin 8) 1) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem sym3_le_closure :
    sym3 ≤ Subgroup.closure {swap (0 : Fin 8) 1, swap (1 : Fin 8) 2} := by
  rintro _ ⟨τ, rfl⟩
  have hτ : τ ∈ Subgroup.closure {σ : Perm {i : Fin 8 // P3 i} | σ.IsSwap} := by
    rw [closure_isSwap]
    trivial
  refine Subgroup.closure_induction (p := fun x _ => ofSubtype x ∈
    Subgroup.closure {swap (0 : Fin 8) 1, swap (1 : Fin 8) 2}) ?_ ?_ ?_ ?_ hτ
  · rintro _ ⟨a, b, hab, rfl⟩
    rw [ofSubtype_swap_eq]
    have h01 : swap (0 : Fin 8) 1 ∈ Subgroup.closure {swap (0 : Fin 8) 1, swap (1 : Fin 8) 2} :=
      Subgroup.subset_closure (by simp)
    have h12 : swap (1 : Fin 8) 2 ∈ Subgroup.closure {swap (0 : Fin 8) 1, swap (1 : Fin 8) 2} :=
      Subgroup.subset_closure (by simp)
    have h02 : swap (0 : Fin 8) 2 ∈ Subgroup.closure {swap (0 : Fin 8) 1, swap (1 : Fin 8) 2} := by
      have e : swap (0 : Fin 8) 2 = swap 0 1 * swap 1 2 * swap 0 1 := by decide
      rw [e]
      exact mul_mem (mul_mem h01 h12) h01
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [P3] at ha hb
    have hab' : a ≠ b := fun h => hab (Subtype.ext h)
    show swap a b ∈ _
    have key : ∀ a b : Fin 8, a.val < 3 → b.val < 3 → a ≠ b →
        swap a b = swap 0 1 ∨ swap a b = swap 1 2 ∨ swap a b = swap 0 2 := by decide
    rcases key a b ha hb hab' with h | h | h <;> rw [h]
    · exact h01
    · exact h12
    · exact h02
  · simp only [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact inv_mem hx

theorem sym3_inf_alt : sym3 ⊓ alternatingGroup (Fin 8) = Subgroup.zpowers c3 := by
  have hle : Subgroup.zpowers c3 ≤ sym3 ⊓ alternatingGroup (Fin 8) :=
    Subgroup.zpowers_le.mpr ⟨c3_mem_sym3, c3_mem_alt⟩
  have hcard : Nat.card ↥(sym3 ⊓ alternatingGroup (Fin 8)) = 3 := by
    let f : ↥sym3 →* ℤˣ := Perm.sign.comp sym3.subtype
    have hf : Function.Surjective f := by
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one f⟩
      · exact ⟨⟨swap 0 1, swap01_mem_sym3⟩, sign_swap (show (0 : Fin 8) ≠ 1 by decide)⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, card_sym3,
      Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at h1
    have h2 : Nat.card f.ker = Nat.card ↥(sym3 ⊓ alternatingGroup (Fin 8)) :=
      Nat.card_congr
        { toFun := fun x => ⟨((x : ↥sym3) : Perm (Fin 8)), (x : ↥sym3).2,
            mem_alternatingGroup.mpr x.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, mem_alternatingGroup.mp y.2.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    omega
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_zpowers, orderOf_c3]

theorem zpowers_c3_cases {σ : Perm (Fin 8)} (h : σ ∈ Subgroup.zpowers c3) (h1 : σ ≠ 1) :
    σ = c3 ∨ σ = c3 ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  rw [← zpow_mod_orderOf, orderOf_c3] at h1 ⊢
  have hk : (k % ((3 : ℕ) : ℤ)) = 0 ∨ (k % ((3 : ℕ) : ℤ)) = 1 ∨ (k % ((3 : ℕ) : ℤ)) = 2 := by
    omega
  rcases hk with hk | hk | hk <;> rw [hk] at h1 ⊢
  · exact absurd (zpow_zero c3) h1
  · left
    exact zpow_one c3
  · right
    exact zpow_ofNat c3 2

@[expose] def d3 : Perm (Fin 8) := swap 1 2 * swap 2 3

theorem d3_mem_alt : d3 ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, d3, map_mul, sign_swap (show (1 : Fin 8) ≠ 2 by decide),
    sign_swap (show (2 : Fin 8) ≠ 3 by decide)]
  rfl

theorem alt8_nonabelian : ∃ a b : ↥(alternatingGroup (Fin 8)), a * b ≠ b * a :=
  ⟨⟨c3, c3_mem_alt⟩, ⟨d3, d3_mem_alt⟩, fun h => absurd (congrArg Subtype.val h) (by decide)⟩

@[expose] noncomputable def toHeart : D8 →* Multiplicative (AltHeart 8) :=
  QuotientGroup.lift (natKer 8) (C124.altHeartHom 8) (by
    intro x hx
    rw [MonoidHom.mem_ker, C124.altHeartHom_eq_one_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hx : (x : PermMod 8) ∈ Subgroup.zpowers
      (allOnes 8))
    have hk' : (x : PermMod 8) = allOnes 8 ^ k := hk.symm
    intro i j
    rw [hk']
    simp [allOnes])

theorem toHeart_mk (m : ↥(coreMod 8)) :
    toHeart (QuotientGroup.mk m) = C124.altHeartHom 8 m := rfl

theorem toHeart_injective : Function.Injective toHeart := by
  intro a b h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [toHeart_mk, toHeart_mk] at h
  rw [QuotientGroup.eq]
  have h1 : a⁻¹ * b ∈ (C124.altHeartHom 8).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [C124.ker_altHeartHom 8 (by norm_num)] at h1
  exact (Subgroup.mem_subgroupOf.mp h1).1

theorem toHeart_surjective : Function.Surjective toHeart := by
  intro y
  obtain ⟨m, hm⟩ := C124.altHeartHom_surjective 8 y
  exact ⟨QuotientGroup.mk m, hm⟩

theorem toHeart_dAct (σ : Perm (Fin 8)) (d : D8) (x : ↥(CFSG.QuasithinUnique.evenWeight 8))
    (hx : (QuotientAddGroup.mk x : AltHeart 8) = Multiplicative.toAdd (toHeart d)) :
    (QuotientAddGroup.mk (permWeight 8 σ x) : AltHeart 8) =
      Multiplicative.toAdd (toHeart (dAct σ d)) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective d
  rw [dAct_mk, toHeart_mk]
  rw [toHeart_mk] at hx
  have h2 : Multiplicative.toAdd (C124.altHeartHom 8 (coreAct 8 σ m)) =
      (QuotientAddGroup.mk (permWeight 8 σ (Multiplicative.toAdd (C124.coreEvenEquiv 8 m))) :
        AltHeart 8) := rfl
  rw [h2]
  have h3 : (QuotientAddGroup.mk x : AltHeart 8) =
      QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv 8 m)) := by
    rw [hx]
    rfl
  rw [QuotientAddGroup.eq] at h3 ⊢
  intro i j
  have := h3 (σ⁻¹ i) (σ⁻¹ j)
  simpa [permWeight] using this

theorem card_evenWeight_three : Nat.card (CFSG.QuasithinUnique.evenWeight 3) = 4 := by
  classical
  have h : Nat.card (CFSG.QuasithinUnique.evenWeight 3) =
      Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight
      (fun x => by simp [CFSG.QuasithinUnique.evenWeight, AddMonoidHom.mem_ker])
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem inf_centralizer_eq_pCoreOf (hH : Hyp126 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) :
    L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_hyp1223 hyp hred
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hO2' : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hO2
    exact ⟨x, hx, rfl⟩
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2' with hψdef
  have hψ : Function.Surjective ψ := QuotientGroup.lift_surjective_of_surjective _ φ hφ hO2'
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨hψker, -⟩ := SteinbergBM.five_quasisimple_centerless_image hyp.quasisimple
    alt8_nonabelian ψ hψ
  have hdvd := CFSG.RankThree.PartOne.card_ker_dvd_card_hopfMultiplier
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩ hyp.quasisimple.1 ψ hψ hψker.le
  rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup le_rfl] at hdvd
  have h2 : IsPGroup 2 ψ.ker := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; rfl)
  have hbot : ψ.ker = ⊥ := by
    have hle : ψ.ker ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) := le_sSup ⟨inferInstance, h2⟩
    rw [pCore_two_quotient_pCore_two] at hle
    exact le_bot_iff.1 hle
  have hkerφ : φ.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm (fun x hx => ?_) hO2'
    have h1 : (x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hψdef, QuotientGroup.lift_mk]
      exact hx
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hsub : (Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L :=
    hker.symm.trans hkerφ
  calc L ⊓ Subgroup.centralizer (V : Set G) = Subgroup.centralizer (V : Set G) ⊓ L :=
        inf_comm _ _
    _ = ((Subgroup.centralizer (V : Set G)).subgroupOf L).map L.subtype :=
        (Subgroup.subgroupOf_map_subtype _ _).symm
    _ = pCoreOf 2 L := by
        rw [hsub]
        rfl

omit [Finite G] in
theorem actsAs_one_of_mem_centralizer (F : Frame126 T L V) {x : G}
    (hx : x ∈ Subgroup.centralizer (V : Set G)) : ActsAs F x 1 := by
  intro v w hw
  have : w = v := Subtype.ext (by
    rw [hw, ← Subgroup.mem_centralizer_iff.1 hx v v.2]
    group)
  rw [this, dAct_one]

omit [Finite G] [IsMulCommutative ↥V] in
theorem five_le_card {α : Type*} [Fintype α] [DecidableEq α] {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ Fintype.card α := by
  have h : ({a, b, c, d, e} : Finset α).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde]
  rw [← h]
  exact Finset.card_le_univ _

theorem swap01_conj : ∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val →
    swap 0 1 * swap a b * swap 0 1 = swap a b := by
  decide

end S126BL

open S126BL in
theorem blockL12618_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) :
    BlockL12618 := by
  intro G _ _ T L V _ F v Kv S hC hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hyp := hH.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hT2 : IsPGroup 2 ↥T := hyp.sylow.1
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  have hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) := by
    rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hA | h3
    · exact absurd hA hyp.notAlt
    obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
    obtain ⟨⟨-, -, hred, -⟩, -⟩ := hall V hyp.irrPlus
    exact hred
  set Q := Qv T V with hQdef
  have hQeq : Q = (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := Qv_eq h1222 hH
  have hQ2 : IsPGroup 2 ↥Q := hT2.to_le inf_le_left
  have hVQ : V ≤ Q := V_le_Qv h1222 hH
  have hQLT : Q ≤ L ⊔ T := by rw [hQeq]; exact inf_le_left
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by rw [hQeq]; exact inf_le_right
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := LT_le_normalizer_Qv h1222 hH
  set R := Rv T L v with hRdef
  have hQR : Q ≤ R := Qv_le_Rv h1222 hH hv
  have hR2 : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 _
  have hRX0 : R ≤ L ⊔ T := (pCoreOf_le 2 _).trans inf_le_left
  have hRY := Rv_le_centralizerSection hD2 hC
  have hRact : ∀ x ∈ R, ActsAs F x 1 ∨ ActsAs F x (swap 0 1) := fun x hx => by
    obtain ⟨σ, hσ, hσ1⟩ := actsAs_of_mem_centralizerSection h1222 F hH hv hβ (hRY hx)
    rcases hσ1 with rfl | rfl
    · exact Or.inl hσ
    · exact Or.inr hσ
  have hmemQ : ∀ x ∈ L ⊔ T, ActsAs F x 1 → x ∈ Q := fun x hx h1 => by
    rw [hQeq]
    exact ⟨hx, mem_centralizer_of_actsAs_one F hVL hLV (hXL hx) (hXV hx) h1⟩
  have hRQ : ¬ R ≤ Q := fun h => hN (by
    rw [le_antisymm h hQR]
    exact normalizer_Qv_le_M h331 h1222 hH)
  obtain ⟨r, hr, hrQ⟩ := IsConcreteLE.not_le_iff_exists.1 hRQ
  have hrσ : ActsAs F r (swap 0 1) := by
    rcases hRact r hr with h | h
    · exact absurd (hmemQ r (hRX0 hr) h) hrQ
    · exact h
  obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨c3, c3_mem_alt⟩
  have hlσ : ActsAs F l c3 := by
    have := S126L19a.actsAs_psi F hH l
    rwa [hl] at this
  have hlLT : (l : G) ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) l.2
  set ν := S126L20c.nu F hH hXL hXV with hνdef
  set X : Subgroup G := (sym3.comap ν).map (L ⊔ T).subtype with hXdef
  have hmemX : ∀ {x : G} (hx : x ∈ L ⊔ T) {σ : Perm (Fin 8)}, ActsAs F x σ →
      (x ∈ X ↔ σ ∈ sym3) := by
    intro x hx σ hσ
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : ν y ∈ sym3 := hy
      rwa [show ν y = σ from S126L20c.nu_eq F hH hXL hXV (x := y) hσ] at hy'
    · intro h
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show ν ⟨x, hx⟩ ∈ sym3
      rwa [S126L20c.nu_eq F hH hXL hXV (x := ⟨x, hx⟩) hσ]
  have hXLT : X ≤ L ⊔ T := Subgroup.map_subtype_le _
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hXLT.trans hXL
  have hXNV : X ≤ Subgroup.normalizer (V : Set G) := hXLT.trans hXV
  have hQX : Q ≤ X := fun q hq =>
    (hmemX (hQLT hq) (actsAs_one_of_mem_centralizer F (hQC hq))).2 (one_mem _)
  have hRX : R ≤ X := fun x hx => by
    rcases hRact x hx with h | h
    · exact (hmemX (hRX0 hx) h).2 (one_mem _)
    · exact (hmemX (hRX0 hx) h).2 swap01_mem_sym3
  have hlX : (l : G) ∈ X := (hmemX hlLT hlσ).2 c3_mem_sym3
  have hXC : X ⊓ Subgroup.centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQX hQC)
    rw [hQeq]
    exact inf_le_inf_right _ hXLT
  have hrangeX : (S126L20c.nu F hH hXN hXNV).range = sym3 := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (hmemX (hXLT x.2) (S126L20c.actsAs_nu F hH hXN hXNV x)).1 x.2
    · refine sym3_le_closure.trans ((Subgroup.closure_le _).2 ?_)
      rintro σ (rfl | rfl)
      · exact (S126L20c.mem_range_nu F hH hXN hXNV).2 ⟨r, hRX hr, hrσ⟩
      · refine (S126L20c.mem_range_nu F hH hXN hXNV).2 ⟨r * l, X.mul_mem (hRX hr) hlX, ?_⟩
        have := hrσ.mul hlσ (hXV hlLT)
        rwa [show swap (0 : Fin 8) 1 * c3 = swap 1 2 by decide] at this
  have hcardX : Nat.card X = Nat.card Q * 6 := by
    rw [S126L20c.card_eq_mul F hH hXN hXNV, hXC, hrangeX, card_sym3]
  have hRN : R ≤ Subgroup.normalizer (L : Set G) := hRX0.trans hXL
  have hRNV : R ≤ Subgroup.normalizer (V : Set G) := hRX0.trans hXV
  have hRC : R ⊓ Subgroup.centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQR hQC)
    rw [hQeq]
    exact inf_le_inf_right _ hRX0
  have hrangeR : (S126L20c.nu F hH hRN hRNV).range = Subgroup.zpowers (swap 0 1) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rcases hRact x x.2 with h | h
      · rw [S126L20c.nu_eq F hH hRN hRNV h]
        exact one_mem _
      · rw [S126L20c.nu_eq F hH hRN hRNV h]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact (S126L20c.mem_range_nu F hH hRN hRNV).2 ⟨r, hr, hrσ⟩
  have hcardR : Nat.card R = Nat.card Q * 2 := by
    rw [S126L20c.card_eq_mul F hH hRN hRNV, hRC, hrangeR, Nat.card_zpowers, orderOf_swap01]
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hRXrel : R.relIndex X = 3 := by
    have h := Subgroup.relIndex_mul_card R X
    rw [inf_of_le_left hRX, hcardR, hcardX] at h
    have h' : Nat.card Q * (R.relIndex X * 2) = Nat.card Q * 6 := by
      rw [← h]
      ring
    have := Nat.eq_of_mul_eq_mul_left hQpos h'
    omega
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf R X :=
    ⟨hRX, hR2, by show ¬ 2 ∣ R.relIndex X; rw [hRXrel]; decide⟩
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hcardX' : Nat.card X = 2 ^ (k + 1) * 3 := by
    rw [hcardX, hk]
    ring
  have hXsq : IsSQTKIn X := F6.isSQTKIn_of_card_eq_two_pow_mul_three hcardX'
  have hXsolv : Group.IsSolvable ↥X := F6.isSolvable_of_card_eq_two_pow_mul_three hcardX'
  have hQO : Q ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hQX (hXLT.trans hLTQ) hQ2
  have hXchar : CFSG.QuasithinUnique.CharTwo X := by
    rintro x ⟨hxX, hxC⟩
    have hxCV : x ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.centralizer_le (fun w hw => hQO (hVQ hw)) hxC
    exact hQO (hXC ▸ ⟨hxX, hxCV⟩)
  by_cases hcase : ∃ C : Subgroup G, C ≤ R ∧ C ≠ ⊥ ∧ (C.subgroupOf R).Characteristic ∧
      X ≤ Subgroup.normalizer (C : Set G)
  · exfalso
    obtain ⟨C, hCR, hC1, hCchar, hXC'⟩ := hcase
    have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      CFSG.QuasithinUnique.normalizer_le_normalizer_of_characteristic hCR hCchar
    set Y := X ⊔ ((L ⊔ T) ⊓ Gv v) with hYdef
    have hYC : Y ≤ Subgroup.normalizer (C : Set G) :=
      sup_le hXC' ((le_normalizer_pCoreOf 2 ((L ⊔ T) ⊓ Gv v)).trans hNRC)
    have hYLT : Y ≤ L ⊔ T := sup_le hXLT inf_le_left
    have hYN : Y ≤ Subgroup.normalizer (L : Set G) := hYLT.trans hXL
    have hYNV : Y ≤ Subgroup.normalizer (V : Set G) := hYLT.trans hXV
    have hgen : ∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val → a ≠ b →
        swap a b ∈ (S126L20c.nu F hH hYN hYNV).range := by
      intro a b ha hb hab
      have hmem : swap 0 1 * swap a b ∈ alternatingGroup (Fin 8) := by
        rw [mem_alternatingGroup, map_mul, sign_swap (show (0 : Fin 8) ≠ 1 by decide),
          sign_swap hab]
        rfl
      obtain ⟨m, hm⟩ := S126L19a.psi_surjective F hH ⟨_, hmem⟩
      have hmσ : ActsAs F m (swap 0 1 * swap a b) := by
        have := S126L19a.actsAs_psi F hH m
        rwa [hm] at this
      have hmLT : (m : G) ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) m.2
      have hmr : (m : G) * r ∈ L ⊔ T := (L ⊔ T).mul_mem hmLT (hRX0 hr)
      have hact : ActsAs F ((m : G) * r) (swap a b) := by
        have := hmσ.mul hrσ (hXV (hRX0 hr))
        rwa [swap01_conj a b ha hb] at this
      have h0 : (swap a b) 0 = 0 :=
        swap_apply_of_ne_of_ne (fun h => by rw [← h] at ha; simp at ha)
          (fun h => by rw [← h] at hb; simp at hb)
      have h1 : (swap a b) 1 = 1 :=
        swap_apply_of_ne_of_ne (fun h => by rw [← h] at ha; simp at ha)
          (fun h => by rw [← h] at hb; simp at hb)
      have hmrv : (m : G) * r ∈ Gv v :=
        (mem_Gv_iff h1222 F hH hv hβ (hXL hmr) (hXV hmr) hact).2 (Or.inl ⟨h0, h1⟩)
      exact (S126L20c.mem_range_nu F hH hYN hYNV).2
        ⟨(m : G) * r, Subgroup.mem_sup_right ⟨hmr, hmrv⟩, hact⟩
    have hrangeY : (S126L20c.nu F hH hYN hYNV).range = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      have hσ : σ ∈ Submonoid.closure
          (Set.range fun i : Fin 7 => swap (Fin.castSucc i) (Fin.succ i)) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ 7]
        exact Submonoid.mem_top σ
      refine (Submonoid.closure_le (S := (S126L20c.nu F hH hYN hYNV).range.toSubmonoid)).2
        ?_ hσ
      rintro _ ⟨i, rfl⟩
      show swap (Fin.castSucc i) (Fin.succ i) ∈ (S126L20c.nu F hH hYN hYNV).range
      fin_cases i
      · exact (S126L20c.mem_range_nu F hH hYN hYNV).2 ⟨r, Subgroup.mem_sup_left (hRX hr), hrσ⟩
      · refine (S126L20c.mem_range_nu F hH hYN hYNV).2
          ⟨r * l, Subgroup.mem_sup_left (X.mul_mem (hRX hr) hlX), ?_⟩
        have := hrσ.mul hlσ (hXV hlLT)
        rwa [show swap (0 : Fin 8) 1 * c3 = swap 1 2 by decide] at this
      all_goals exact hgen _ _ (by decide) (by decide) (by decide)
    have hLTY : L ⊔ T ≤ Y := by
      intro x hx
      obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH (hXL hx) (hXV hx)
      obtain ⟨y, hy, hyσ⟩ := (S126L20c.mem_range_nu F hH hYN hYNV).1
        (by rw [hrangeY]; exact Subgroup.mem_top σ)
      have hyx : y⁻¹ * x ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (hYLT hy)) hx
      have h1 : ActsAs F (y⁻¹ * x) 1 := by
        have := hyσ.inv.mul hσ (hXV hx)
        rwa [inv_mul_cancel] at this
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact Y.mul_mem hy (Subgroup.mem_sup_left (hQX (hmemQ _ hyx h1)))
    exact hN (hNRC.trans (normalizer_le_M h331 hH hC1 (hR2.to_le hCR) (hLTY.trans hYC)))
  push Not at hcase
  have hcgs : cgsIn X R ≤ R := by
    refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCchar => ?_
    have hRC' : R ≤ X ⊓ Subgroup.normalizer (C : Set G) := le_inf hRX
      (Subgroup.le_normalizer.trans
        (CFSG.QuasithinUnique.normalizer_le_normalizer_of_characteristic hCR hCchar))
    have hmul := Subgroup.relIndex_mul_relIndex R (X ⊓ Subgroup.normalizer (C : Set G)) X hRC'
      inf_le_left
    rw [hRXrel] at hmul
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (Dvd.intro _ hmul) with h1 | h1
    · exact Subgroup.relIndex_eq_one.1 h1
    · exfalso
      rw [h1] at hmul
      have hb : (X ⊓ Subgroup.normalizer (C : Set G)).relIndex X = 1 := by omega
      exact hcase C hCR hC1 hCchar ((Subgroup.relIndex_eq_one.1 hb).trans inf_le_right)
  obtain ⟨n, Lb, -, hLb, hprod⟩ := asc129StatementSolv G X R R hXsq hXchar hRsyl hcgs hRX hXsolv
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have hXR : X ≤ R := fun x hx => by
        obtain ⟨m, hm, y, -, rfl⟩ := hprod x hx
        simpa using hm
      have h1 := Subgroup.relIndex_eq_one.2 hXR
      rw [hRXrel] at h1
      exact absurd h1 (by norm_num)
    · exact h
  set L₁ := Lb ⟨0, hn0⟩ with hL₁def
  obtain ⟨hchi, -, -⟩ := hLb ⟨0, hn0⟩
  have hblock : CFSG.QuasithinUnique.IsBlock2 X L₁ := hchi.1
  have hA3 : CFSG.QuasithinUnique.IsAltType L₁ 3 :=
    C1Pack.isAltType_three_of_isChiBlock_of_isSolvable
      (C1GN.isChiBlock_of_isChi0Block hblock hchi) hXsolv
  have hsh : CFSG.QuasithinUnique.IsShort2 L₁ := hblock.1
  have hL₁X : L₁ ≤ X := hblock.2.1
  have hL₁L : L₁ ≤ L := (C1Pack.isShort2_eq_oTwoUpper hsh).le.trans
    ((oTwoUpper_mono (hL₁X.trans hXLT)).trans
      (oTwoUpper_le_of_pow_mem fun g hg => E1.exists_pow_mem_of_mem_sup hT2 hTL hg))
  have hLeven : ∀ x ∈ L, ∀ σ : Perm (Fin 8), ActsAs F x σ → σ ∈ alternatingGroup (Fin 8) := by
    intro x hx σ hσ
    have h1 := S126L19a.actsAs_psi F hH ⟨x, hx⟩
    rw [hσ.unique h1 (hLV hx)]
    exact (S126L19a.psi F hH ⟨x, hx⟩).2
  set νX := S126L20c.nu F hH hXN hXNV with hνXdef
  have hνXmem : ∀ x : ↥X, νX x ∈ sym3 := fun x => by
    rw [← hrangeX]
    exact ⟨x, rfl⟩
  have hνL₁ : ∀ x (hx : x ∈ L₁), νX ⟨x, hL₁X hx⟩ ∈ Subgroup.zpowers c3 := fun x hx => by
    rw [← sym3_inf_alt]
    exact ⟨hνXmem _, hLeven x (hL₁L hx) _ (S126L20c.actsAs_nu F hH hXN hXNV ⟨x, hL₁X hx⟩)⟩
  have hL₁Q : ¬ L₁ ≤ Q := by
    intro h
    have h2 : IsPGroup 2 ↥L₁ := hQ2.to_le h
    obtain ⟨α, hα, -⟩ := hA3
    have hdvd := Subgroup.card_dvd_of_surjective hα
    rw [nat_card_alternatingGroup, Nat.card_fin] at hdvd
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  obtain ⟨x₁, hx₁, hx₁Q⟩ := IsConcreteLE.not_le_iff_exists.1 hL₁Q
  have hx₁1 : νX ⟨x₁, hL₁X hx₁⟩ ≠ 1 := fun h => hx₁Q (by
    rw [hQeq]
    exact ⟨hXLT (hL₁X hx₁), (S126L20c.nu_eq_one_iff F hH hXN hXNV _).1 h⟩)
  obtain ⟨l₁, hl₁, hl₁σ⟩ : ∃ l₁ ∈ L₁, ActsAs F l₁ c3 := by
    have hact := S126L20c.actsAs_nu F hH hXN hXNV ⟨x₁, hL₁X hx₁⟩
    rcases zpowers_c3_cases (hνL₁ x₁ hx₁) hx₁1 with h | h
    · refine ⟨x₁, hx₁, ?_⟩
      rw [h] at hact
      exact hact
    · refine ⟨x₁ ^ 2, L₁.pow_mem hx₁ 2, ?_⟩
      have := hact.pow (hXNV (hL₁X hx₁)) 2
      rwa [h, ← pow_mul, show c3 ^ (2 * 2) = c3 by decide] at this
  have hl₁X : l₁ ∈ X := hL₁X hl₁
  have hl₁L : l₁ ∈ L := hL₁L hl₁
  have hL₁NQ : L₁ ≤ Subgroup.normalizer (Q : Set G) := (hL₁X.trans hXLT).trans hLTQ
  have hcommQ : (Q : Set G) * L₁ = L₁ * Q := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L₁ hL₁NQ,
      ← Subgroup.coe_mul_of_left_le_normalizer_right L₁ Q hL₁NQ, sup_comm]
  obtain ⟨hO2Q, -⟩ := a4_2_2 (C1Pack.isShort2_eq_oTwoUpper hsh) (IsBlock2.isSubnormal hblock)
    hQX hQ2 hcommQ
  have hWX : L₁ ⊔ Q ≤ X := sup_le hL₁X hQX
  have hmemW : ∀ x (hx : x ∈ X), νX ⟨x, hx⟩ ∈ Subgroup.zpowers c3 → x ∈ L₁ ⊔ Q := by
    intro x hx h
    by_cases h1 : νX ⟨x, hx⟩ = 1
    · have hxQ : x ∈ Q := by
        rw [hQeq]
        exact ⟨hXLT hx, (S126L20c.nu_eq_one_iff F hH hXN hXNV _).1 h1⟩
      exact Subgroup.mem_sup_right hxQ
    · have hact := S126L20c.actsAs_nu F hH hXN hXNV ⟨x, hx⟩
      have key : ∀ y ∈ L₁, ActsAs F y (νX ⟨x, hx⟩) → x ∈ L₁ ⊔ Q := by
        intro y hy hyσ
        have hyx : y⁻¹ * x ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (hXLT (hL₁X hy)))
          (hXLT hx)
        have h1' : ActsAs F (y⁻¹ * x) 1 := by
          have := hyσ.inv.mul hact (hXNV hx)
          rwa [inv_mul_cancel] at this
        have e : x = y * (y⁻¹ * x) := by group
        rw [e]
        exact (L₁ ⊔ Q).mul_mem (Subgroup.mem_sup_left hy)
          (Subgroup.mem_sup_right (hmemQ _ hyx h1'))
      rcases zpowers_c3_cases h h1 with h2 | h2
      · exact key l₁ hl₁ (by rw [h2]; exact hl₁σ)
      · refine key (l₁ ^ 2) (L₁.pow_mem hl₁ 2) ?_
        rw [h2]
        exact hl₁σ.pow (hXNV hl₁X) 2
  have hWmem : ∀ x ∈ L₁ ⊔ Q, ∀ hx : x ∈ X, νX ⟨x, hx⟩ ∈ Subgroup.zpowers c3 := by
    intro x hxW
    have hle : L₁ ⊔ Q ≤ ((Subgroup.zpowers c3).comap νX).map X.subtype := by
      refine sup_le (fun y hy => ⟨⟨y, hL₁X hy⟩, hνL₁ y hy, rfl⟩) (fun q hq => ?_)
      refine ⟨⟨q, hQX hq⟩, ?_, rfl⟩
      show νX ⟨q, hQX hq⟩ ∈ Subgroup.zpowers c3
      rw [(S126L20c.nu_eq_one_iff F hH hXN hXNV ⟨q, hQX hq⟩).2 (hQC hq)]
      exact one_mem _
    obtain ⟨y, hy, hyx⟩ := hle hxW
    intro hx
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hWn : ((L₁ ⊔ Q).subgroupOf X).Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have hw' := hWmem _ hw w.2
    refine hmemW _ (X.mul_mem (X.mul_mem g.2 w.2) (X.inv_mem g.2)) ?_
    show νX (g * w * g⁻¹) ∈ _
    rw [map_mul, map_mul, map_inv, ← sym3_inf_alt]
    rw [← sym3_inf_alt] at hw'
    exact ⟨sym3.mul_mem (sym3.mul_mem (hνXmem g) hw'.1) (sym3.inv_mem (hνXmem g)),
      (alternatingGroup.normal (α := Fin 8)).conj_mem _ hw'.2 _⟩
  have hXW : X ≤ Subgroup.normalizer ((L₁ ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).1 hWn
  have hL₁n : (L₁.subgroupOf X).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [hO2Q] at hy ⊢
    exact conj_mem_oTwoUpper (hXW g.2) hy
  have hXL₁ : X ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁X).1 hL₁n
  have hl₁R : l₁ ∉ R := fun h => by
    rcases hRact l₁ h with h1 | h1
    · exact absurd (hl₁σ.unique h1 (hXNV hl₁X)) (by decide)
    · exact absurd (hl₁σ.unique h1 (hXNV hl₁X)) (by decide)
  have hXeq : L₁ ⊔ R = X := by
    have hle : L₁ ⊔ R ≤ X := sup_le hL₁X hRX
    have hmul := Subgroup.relIndex_mul_relIndex R (L₁ ⊔ R) X le_sup_right hle
    rw [hRXrel] at hmul
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (Dvd.intro _ hmul) with h1 | h1
    · exact absurd ((Subgroup.relIndex_eq_one.1 h1) (Subgroup.mem_sup_left hl₁)) hl₁R
    · rw [h1] at hmul
      have hb : (L₁ ⊔ R).relIndex X = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.1 hb)
  have hRNL₁ : R ≤ Subgroup.normalizer (L₁ : Set G) := hRX.trans hXL₁
  have hsylL : CFSG.QuasithinUnique.IsSylowTwoOf R (L₁ ⊔ R) := hXeq ▸ hRsyl
  obtain ⟨hO, -, -, -, -, -⟩ := VolI.asC113c_holds G L₁ R hsylL hRNL₁ hsh 3 (Or.inl rfl) hA3
  set U := CFSG.QuasithinUnique.blockU L₁ with hUdef
  have hL₁NU : L₁ ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of_le
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L₁))
      Subgroup.le_normalizer
  have hDNU : R ⊓ Subgroup.centralizer (L₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of_le
      ((inf_le_left.trans hRNL₁).trans (normalizer_le_normalizer_pCoreOf 2 L₁))
      (inf_le_left.trans hRNL₁)
  have hQU : ∀ q ∈ Q, ⁅q, l₁⁆ ∈ U := by
    intro q hq
    have hq' : q ∈ U ⊔ (R ⊓ Subgroup.centralizer (L₁ : Set G)) := by
      rw [← hO, hXeq]
      exact hQO hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hDNU hq'
    have hbl : l₁ * b = b * l₁ := Subgroup.mem_centralizer_iff.1 hb.2 l₁ hl₁
    have e : ⁅a * b, l₁⁆ = a * (l₁ * a⁻¹ * l₁⁻¹) := by
      rw [commutatorElement_def]
      calc a * b * l₁ * (a * b)⁻¹ * l₁⁻¹ = a * (b * l₁) * b⁻¹ * a⁻¹ * l₁⁻¹ := by group
        _ = a * (l₁ * b) * b⁻¹ * a⁻¹ * l₁⁻¹ := by rw [hbl]
        _ = a * (l₁ * a⁻¹ * l₁⁻¹) := by group
    rw [e]
    exact U.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hL₁NU hl₁) _).1 (U.inv_mem ha))
  have hU4 : Nat.card ↥U = 4 := by
    obtain ⟨-, -, -, β, hβs, hβk, -⟩ := id hA3
    rw [VolI.blockZ_eq_bot_of_alt3 hsh hA3, Subgroup.bot_subgroupOf] at hβk
    have hβi : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hβk
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)]
    exact card_evenWeight_three
  have hl₁N : l₁ ∈ Subgroup.normalizer (V : Set G) := hXNV hl₁X
  have hcomm : ∀ (w : ↥V) (i : Fin 8), F.β w = QuotientGroup.mk (pe i 3) →
      ∃ hc : ⁅(w : G), l₁⁆ ∈ V, F.β ⟨_, hc⟩ = QuotientGroup.mk (pe i (c3 i)) := by
    intro w i hw
    have hmem : l₁ * w * l₁⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hl₁N w).1 w.2
    have e0 : ⁅(w : G), l₁⁆ = w * (l₁ * w * l₁⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    have hc : ⁅(w : G), l₁⁆ ∈ V := by
      rw [e0]
      exact V.mul_mem w.2 (V.inv_mem hmem)
    refine ⟨hc, ?_⟩
    have e : (⟨_, hc⟩ : ↥V) = w * (⟨_, hmem⟩ : ↥V)⁻¹ := Subtype.ext e0
    rw [e, map_mul, map_inv, hl₁σ w ⟨_, hmem⟩ rfl, hw, dAct_mk, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, S126L20a.pe_mul_inv_coreAct c3 i 3 (by decide)]
  obtain ⟨w₀, hw₀⟩ := F.β_surj (QuotientGroup.mk (pe 0 3))
  obtain ⟨w₁, hw₁⟩ := F.β_surj (QuotientGroup.mk (pe 1 3))
  obtain ⟨w₂, hw₂⟩ := F.β_surj (QuotientGroup.mk (pe 2 3))
  obtain ⟨hc₀, hβ₀⟩ := hcomm w₀ 0 hw₀
  obtain ⟨hc₁, hβ₁⟩ := hcomm w₁ 1 hw₁
  obtain ⟨hc₂, hβ₂⟩ := hcomm w₂ 2 hw₂
  rw [show c3 0 = 1 by decide] at hβ₀
  rw [show c3 1 = 2 by decide] at hβ₁
  rw [show c3 2 = 0 by decide] at hβ₂
  have hne1 : ∀ {a b : Fin 8}, a ≠ b → (QuotientGroup.mk (pe a b) : D8) ≠ 1 :=
    fun hab => S126L20a.mk_ne_one (Or.inl (S126L20a.wt_pe hab))
  have hnepe : ∀ {a b c d : Fin 8}, a ≠ b → ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) →
      (QuotientGroup.mk (pe a b) : D8) ≠ QuotientGroup.mk (pe c d) :=
    fun hab hcd h => hcd (mk_pe_eq_mk_pe hab h)
  have hβne : ∀ {x y : G} (hx : x ∈ V) (hy : y ∈ V), F.β ⟨x, hx⟩ ≠ F.β ⟨y, hy⟩ → x ≠ y := by
    rintro x y hx hy h rfl
    exact h rfl
  have hc₀1 : ⁅(w₀ : G), l₁⁆ ≠ 1 := fun h => hne1 (show (0 : Fin 8) ≠ 1 by decide)
    (by rw [← hβ₀]; exact (by
      have : (⟨_, hc₀⟩ : ↥V) = 1 := Subtype.ext h
      rw [this, map_one]))
  have hc₁1 : ⁅(w₁ : G), l₁⁆ ≠ 1 := fun h => hne1 (show (1 : Fin 8) ≠ 2 by decide)
    (by rw [← hβ₁]; exact (by
      have : (⟨_, hc₁⟩ : ↥V) = 1 := Subtype.ext h
      rw [this, map_one]))
  have hc₂1 : ⁅(w₂ : G), l₁⁆ ≠ 1 := fun h => hne1 (show (2 : Fin 8) ≠ 0 by decide)
    (by rw [← hβ₂]; exact (by
      have : (⟨_, hc₂⟩ : ↥V) = 1 := Subtype.ext h
      rw [this, map_one]))
  have hc₀₁ : ⁅(w₀ : G), l₁⁆ ≠ ⁅(w₁ : G), l₁⁆ :=
    hβne hc₀ hc₁ (by rw [hβ₀, hβ₁]; exact hnepe (by decide) (by decide))
  have hc₀₂ : ⁅(w₀ : G), l₁⁆ ≠ ⁅(w₂ : G), l₁⁆ :=
    hβne hc₀ hc₂ (by rw [hβ₀, hβ₂]; exact hnepe (by decide) (by decide))
  have hc₁₂ : ⁅(w₁ : G), l₁⁆ ≠ ⁅(w₂ : G), l₁⁆ :=
    hβne hc₁ hc₂ (by rw [hβ₁, hβ₂]; exact hnepe (by decide) (by decide))
  have hcU : ∀ w : ↥V, ⁅(w : G), l₁⁆ ∈ U := fun w => hQU w (hVQ w.2)
  have hUV : U ≤ V := by
    intro u hu
    by_contra huV
    classical
    have := Fintype.ofFinite ↥U
    have h5 := five_le_card (α := ↥U) (a := ⟨u, hu⟩) (b := 1) (c := ⟨_, hcU w₀⟩)
      (d := ⟨_, hcU w₁⟩) (e := ⟨_, hcU w₂⟩)
      (fun h => huV (by rw [show u = 1 from congrArg Subtype.val h]; exact V.one_mem))
      (fun h => huV (by rw [show u = _ from congrArg Subtype.val h]; exact hc₀))
      (fun h => huV (by rw [show u = _ from congrArg Subtype.val h]; exact hc₁))
      (fun h => huV (by rw [show u = _ from congrArg Subtype.val h]; exact hc₂))
      (fun h => hc₀1 (congrArg Subtype.val h).symm)
      (fun h => hc₁1 (congrArg Subtype.val h).symm)
      (fun h => hc₂1 (congrArg Subtype.val h).symm)
      (fun h => hc₀₁ (congrArg Subtype.val h))
      (fun h => hc₀₂ (congrArg Subtype.val h))
      (fun h => hc₁₂ (congrArg Subtype.val h))
    rw [← Nat.card_eq_fintype_card, hU4] at h5
    omega
  have hQV : ∀ q ∈ Q, ⁅q, l₁⁆ ∈ V := fun q hq => hUV (hQU q hq)
  have hO2LV : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_hyp1223 hyp hred
  have hO2L : pCoreOf 2 L ≤ Q := fun n hn => by
    rw [hQeq]
    exact ⟨(le_sup_left : L ≤ L ⊔ T) (pCoreOf_le 2 L hn), hO2LV hn⟩
  let N : Subgroup G :=
    { carrier := {ℓ | ℓ ∈ L ∧ ∀ n ∈ pCoreOf 2 L, ⁅n, ℓ⁆ ∈ V}
      one_mem' := ⟨L.one_mem, fun n _ => by
        rw [commutatorElement_def, mul_one, mul_inv_cancel, inv_one, mul_one]
        exact V.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, fun n hn => by
        have e : ⁅n, a * b⁆ = ⁅n, a⁆ * (a * ⁅n, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact V.mul_mem (ha.2 n hn) ((Subgroup.mem_normalizer_iff.1 (hLV ha.1) _).1 (hb.2 n hn))⟩
      inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, fun n hn => by
        have e : ⁅n, a⁻¹⁆ = a⁻¹ * ⁅n, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hLV (L.inv_mem ha.1)) _).1
          (V.inv_mem (ha.2 n hn))⟩ }
  have hNL : N ≤ L := fun x hx => hx.1
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2), fun n hn => ?_⟩
    have hn' : (g : G)⁻¹ * n * (g : G)⁻¹⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.1 (hLO (L.inv_mem g.2)) n).1 hn
    have e : ⁅n, (g : G) * x * (g : G)⁻¹⁆ =
        (g : G) * ⁅(g : G)⁻¹ * n * (g : G)⁻¹⁻¹, (x : G)⁆ * (g : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    show ⁅n, (g : G) * x * (g : G)⁻¹⁆ ∈ V
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hLV g.2) _).1 (hx.2 _ hn')
  have hl₁N : l₁ ∈ N := ⟨hl₁L, fun n hn => hQV n (hO2L hn)⟩
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hmapN : (N.subgroupOf L).map (S126L19a.psi F hH) = ⊤ := by
    have hn : ((N.subgroupOf L).map (S126L19a.psi F hH)).Normal :=
      hNn.map _ (S126L19a.psi_surjective F hH)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N.subgroupOf L).map (S126L19a.psi F hH)) with h | h
    · exfalso
      have hmem : S126L19a.psi F hH ⟨l₁, hl₁L⟩ ∈ (N.subgroupOf L).map (S126L19a.psi F hH) :=
        ⟨⟨l₁, hl₁L⟩, hl₁N, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h1 := S126L19a.actsAs_psi F hH ⟨l₁, hl₁L⟩
      rw [hmem, OneMemClass.coe_one] at h1
      exact absurd (hl₁σ.unique h1 (hLV hl₁L)) (by decide)
    · exact h
  have hLN : ∀ x ∈ L, x ∈ N ⊔ pCoreOf 2 L := by
    intro x hx
    obtain ⟨m, hm, hmx⟩ : S126L19a.psi F hH ⟨x, hx⟩ ∈
        (N.subgroupOf L).map (S126L19a.psi F hH) := by
      rw [hmapN]
      exact Subgroup.mem_top _
    have hmxL : (m : G)⁻¹ * x ∈ L := L.mul_mem (L.inv_mem m.2) hx
    have h1 : ActsAs F ((m : G)⁻¹ * x) 1 := by
      have h2 := (S126L19a.actsAs_psi F hH m).inv.mul (S126L19a.actsAs_psi F hH ⟨x, hx⟩)
        (hLV hx)
      rwa [hmx, inv_mul_cancel] at h2
    have hO : (m : G)⁻¹ * x ∈ pCoreOf 2 L := by
      rw [← S126BL.inf_centralizer_eq_pCoreOf hH hred]
      exact ⟨hmxL, mem_centralizer_of_actsAs_one F hVL hLV
        (hXL ((le_sup_left : L ≤ L ⊔ T) hmxL)) (hLV hmxL) h1⟩
    have e : x = m * ((m : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hm))
      (Subgroup.mem_sup_right hO)
  have hLNN : L ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).1 hNn
  have hNeq : N = L := hyp.faithful.2.1 N hNL hNn fun x hx =>
    E1.exists_pow_mem_of_mem_sup (pCoreOf_isPGroup 2 L) ((pCoreOf_le 2 L).trans hLNN)
      (hLN x hx)
  have hVL' : V ≤ L := by
    rw [← hVL]
    exact Lem12.commutator_le_of_le_normalizer (hVT.trans hTL)
  have hVO : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL' hLV (hQ2.to_le hVQ)
  have hUL : CFSG.QuasithinUnique.blockU L = V := by
    apply le_antisymm
    · rw [CFSG.QuasithinUnique.blockU, Subgroup.commutator_le]
      intro n hn ℓ hℓ
      have hℓN : ℓ ∈ N := hNeq ▸ hℓ
      exact hℓN.2 n hn
    · calc V = ⁅V, L⁆ := hVL.symm
        _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hVO le_rfl
  have hZL : CFSG.QuasithinUnique.blockZ L = V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [CFSG.QuasithinUnique.blockZ, hUL]
  have hshortL : CFSG.QuasithinUnique.IsShort2 L := by
    refine ⟨fun N' _ h2 => ?_, ?_, ⟨?_, ?_⟩, Or.inl hyp.quasisimple, ⟨?_, fun W hW1 hW2 hW3 => ?_⟩⟩
    · have hmap : N'.map L.subtype = L := by
        refine hyp.faithful.2.1 (N'.map L.subtype) (Subgroup.map_subtype_le N') ?_
          fun x hx => ?_
        · have h1 : (N'.map L.subtype).subgroupOf L = N' :=
            Subgroup.comap_map_eq_self_of_injective L.subtype_injective N'
          rw [h1]
          infer_instance
        · obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk ⟨x, hx⟩)
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
          exact ⟨k, ⟨_, hk, rfl⟩⟩
      rw [eq_top_iff]
      intro y _
      have hy : (y : G) ∈ N'.map L.subtype := by rw [hmap]; exact y.2
      obtain ⟨z, hz, hzy⟩ := hy
      rwa [Subtype.ext hzy] at hz
    · exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mp hyp.faithful.2.2.1
    · rw [hUL, CFSG.QuasithinUnique.blockQ]
      exact le_inf hVO (Subgroup.le_centralizer_iff.mp hO2LV)
    · intro x hx
      rw [hUL] at hx
      simpa using congrArg Subtype.val (sq_eq_one_of_hyp1223 hyp hred ⟨x, hx⟩)
    · rw [hZL, hUL]
      exact hyp.irrPlus.2.2.2.2.1
    · rw [hZL] at hW1 ⊢
      rw [hUL] at hW2 ⊢
      exact irreducible_of_hyp1223 hyp W hW1 hW2 hW3
  have hkerψ : (S126L19a.psi F hH).ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    have h1 : S126L19a.psi F hH x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
      constructor
      · intro h
        have h2 := S126L19a.actsAs_psi F hH x
        rw [h, OneMemClass.coe_one] at h2
        exact mem_centralizer_of_actsAs_one F hVL hLV (hXL ((le_sup_left : L ≤ L ⊔ T) x.2))
          (hLV x.2) h2
      · intro h
        apply Subtype.ext
        exact (S126L19a.actsAs_psi F hH x).unique (actsAs_one_of_mem_centralizer F h) (hLV x.2)
    rw [h1]
    constructor
    · intro hx
      have hx' : (x : G) ∈ pCoreOf 2 L := by
        rw [← S126BL.inf_centralizer_eq_pCoreOf hH hred]
        exact ⟨x.2, hx⟩
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact hO2LV ⟨x, hx, rfl⟩
  let hUsub : ↥(CFSG.QuasithinUnique.blockU L) ≃* ↥V := MulEquiv.subgroupCongr hUL
  have hcoe : ∀ u : ↥(CFSG.QuasithinUnique.blockU L), ((hUsub u : ↥V) : G) = (u : G) :=
    fun u => rfl
  refine ⟨hshortL, S126L19a.psi F hH, S126L19a.psi_surjective F hH, hkerψ,
    toHeart.comp (F.β.comp hUsub.toMonoidHom),
    toHeart_surjective.comp (F.β_surj.comp hUsub.surjective), ?_, ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show toHeart (F.β (hUsub u)) = 1 ↔ (u : G) ∈ CFSG.QuasithinUnique.blockZ L
    rw [← map_one toHeart, toHeart_injective.eq_iff, F.β_ker, hZL, hcoe]
    exact ⟨fun h => ⟨hUL ▸ u.2, h⟩, fun h => h.2⟩
  · intro ℓ u w huw x hx
    have h1 : F.β (hUsub w) = dAct (S126L19a.psi F hH ℓ) (F.β (hUsub u)) :=
      S126L19a.actsAs_psi F hH ℓ (hUsub u) (hUsub w) (by
        rw [hcoe, hcoe, huw, Subgroup.coe_inv])
    show (QuotientAddGroup.mk (permWeight 8 (S126L19a.psi F hH ℓ : Perm (Fin 8)) x) :
      AltHeart 8) = Multiplicative.toAdd (toHeart (F.β (hUsub w)))
    rw [h1]
    exact toHeart_dAct _ _ x hx

end CFSG.Quasithin.H13

end
