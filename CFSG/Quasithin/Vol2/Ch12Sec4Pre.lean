module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec4A5Data
public import CFSG.Quasithin.Vol2.Ch12Sec4Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def L52TenSylowFixedLine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V S : Subgroup G), L ≤ Subgroup.normalizer (V : Set G) →
    (∀ v ∈ V, v ^ 2 = 1) → (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → Nat.card V = 2 ^ 10 →
    IsIrreducibleUnder L V →
    Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
    QuasithinUnique.IsSylowTwoOf S L →
      Nat.card ↥(V ⊓ Subgroup.centralizer (S : Set G)) = 2

theorem g2NaturalCohomologyOne_of_cover (h : G2NaturalCover) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ H : Subgroup (MulAut V), commV H = ⊤ → G2NaturalDerived H ⊤ (fixV H) 1 →
        Nat.card (fixV H) ≤ 2 := by
  intro V _ _ hsq H hc hg2
  rcases h V hsq H (fixV H) le_rfl hc hg2 with h0 | ⟨h2, -, -⟩
  · rw [h0, Subgroup.card_bot]
    norm_num
  · exact h2.le

variable {G : Type} [Group G]

theorem commutator_le_of_relIndex_le_four [Finite G] {L V Z : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hZL : Z ≤ Subgroup.centralizer (L : Set G)) (P : Subgroup ↥L) [P.Normal]
    (hP : ∀ x ∈ P, (x : G) ∈ Subgroup.centralizer (V : Set G)) (hs : IsSimpleGroup (↥L ⧸ P))
    (hcard : 24 < Nat.card (↥L ⧸ P)) (hidx : Z.relIndex V ≤ 4) : ⁅V, L⁆ ≤ Z := by
  classical
  let φ : ↥L →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hLV)
  have hφ : ∀ (l : ↥L) (v : ↥V), ((φ l v : ↥V) : G) = (l : G) * v * (l : G)⁻¹ := fun l v =>
    A5Mod.conjAct_apply_coe V ⟨l, hLV l.2⟩ v
  have hφZ : ∀ (l : ↥L) (v : ↥V), (v : G) ∈ Z → φ l v = v := by
    intro l v hv
    apply Subtype.ext
    rw [hφ]
    have h1 := Subgroup.mem_centralizer_iff.1 (hZL hv) l l.2
    calc (l : G) * v * (l : G)⁻¹ = (v : G) * l * (l : G)⁻¹ := by rw [h1]
      _ = v := by group
  have hmap : ∀ l : ↥L, (Z.subgroupOf V).map (φ l).toMonoidHom = Z.subgroupOf V := by
    intro l
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : (u : G) ∈ Z := hu
      show φ l u ∈ Z.subgroupOf V
      rw [hφZ l u hu']
      exact hu
    · intro hv
      refine ⟨v, hv, ?_⟩
      show φ l v = v
      exact hφZ l v (Subgroup.mem_subgroupOf.1 hv)
  let ρ : ↥L →* Equiv.Perm (↥V ⧸ Z.subgroupOf V) :=
    { toFun := fun l => (QuotientGroup.congr (Z.subgroupOf V) (Z.subgroupOf V) (φ l)
        (hmap l)).toEquiv
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          show QuotientGroup.mk (φ 1 v) = QuotientGroup.mk v
          rw [map_one, MulAut.one_apply]
      map_mul' := fun a b => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          show QuotientGroup.mk (φ (a * b) v) = QuotientGroup.mk (φ a (φ b v))
          rw [map_mul, MulAut.mul_apply] }
  have hρ : ∀ (l : ↥L) (v : ↥V), ρ l (QuotientGroup.mk v) = QuotientGroup.mk (φ l v) :=
    fun l v => rfl
  have hPker : P ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | H v =>
      rw [hρ, Equiv.Perm.coe_one, id_eq]
      congr 1
      apply Subtype.ext
      rw [hφ]
      have h1 := Subgroup.mem_centralizer_iff.1 (hP x hx) v v.2
      calc (x : G) * v * (x : G)⁻¹ = (v : G) * x * (x : G)⁻¹ := by rw [h1]
        _ = v := by group
  let ρ' : ↥L ⧸ P →* Equiv.Perm (↥V ⧸ Z.subgroupOf V) := QuotientGroup.lift P ρ hPker
  have htriv : ρ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with h | h
    · exfalso
      have hinj : Function.Injective ρ' := (MonoidHom.ker_eq_bot_iff ρ').1 h
      have h1 := Nat.card_le_card_of_injective ρ' hinj
      rw [Nat.card_perm] at h1
      have h2 : Nat.card (↥V ⧸ Z.subgroupOf V) ≤ 4 := hidx
      have h3 : (Nat.card (↥V ⧸ Z.subgroupOf V)).factorial ≤ Nat.factorial 4 :=
        Nat.factorial_le h2
      have h4 : Nat.factorial 4 = 24 := rfl
      omega
    · rw [eq_top_iff]
      rintro l -
      have h1 : ρ' (QuotientGroup.mk l) = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
      rw [QuotientGroup.lift_mk] at h1
      exact h1
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 : ρ ⟨l, hl⟩ = 1 := (MonoidHom.mem_ker).1 (htriv ▸ Subgroup.mem_top _)
  have h2 := congrArg (fun f : Equiv.Perm (↥V ⧸ Z.subgroupOf V) => f (QuotientGroup.mk ⟨v, hv⟩))
    h1
  simp only [Equiv.Perm.coe_one, id_eq] at h2
  rw [hρ] at h2
  have h3 := QuotientGroup.eq.1 h2
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 : ((φ ⟨l, hl⟩ ⟨v, hv⟩)⁻¹ * ⟨v, hv⟩ : ↥V) = (l * v * l⁻¹)⁻¹ * v := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
  rw [h4] at h3
  have hlv : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) _).1 (inv_mem hv)
  have hc : v * (l * v⁻¹ * l⁻¹) = (l * v⁻¹ * l⁻¹) * v :=
    congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : ↥V) ⟨_, hlv⟩)
  rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group, hc,
    show (l * v⁻¹ * l⁻¹) * v = (l * v * l⁻¹)⁻¹ * v by group]
  exact h3

theorem inf_centralizer_ne_bot_of_isPGroup [Finite G] {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem card_dvd_card_quotient_pCore [Finite G] {L V : Subgroup G}
    (hP : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) {X : Type*} [Group X]
    (φ : ↥L →* X) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    Nat.card X ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have h1 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hP ⟨x, hx, rfl⟩
  have h2 := Subgroup.index_dvd_of_le h1
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top] at h2
  exact h2

theorem five_dvd_card_alternating {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8) :
    5 ∣ Nat.card (alternatingGroup (Fin m)) := by
  interval_cases m <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

theorem nonempty_autOn_mulEquiv_quotient [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    Nonempty (↥(autOn L V) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hinj : Function.Injective (autOnQuot hLV hO2) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (autOnQuot hLV hO2).ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      apply hnc
      intro l hl
      have h1 : autOnQuot hLV hO2 (QuotientGroup.mk ⟨l, hl⟩) = 1 :=
        (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
      rw [autOnQuot_mk] at h1
      exact (mem_ker_autOnSurj hLV ⟨l, hl⟩).1 h1
  exact ⟨(MulEquiv.ofBijective _ ⟨hinj, autOnQuot_surjective hLV hO2⟩).symm⟩

theorem card_eq_of_surjective_of_simple [Finite G] {L V : Subgroup G}
    (hP : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {X : Type*} [Group X] [Nontrivial X]
    (φ : ↥L →* X) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    Nat.card X = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have h1 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hP ⟨x, hx, rfl⟩
  let ψ := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ h1
  have hψs : Function.Surjective ψ := QuotientGroup.lift_surjective_of_surjective _ _ hφ _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact (Nat.card_congr (MulEquiv.ofBijective ψ
      ⟨(MonoidHom.ker_eq_bot_iff ψ).1 h, hψs⟩).toEquiv).symm
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨y, rfl⟩ := hψs x
    exact hx ((MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top y))

theorem card_subgroupOf_eq_card_inf (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(K ⊓ H) := by
  rw [← Subgroup.inf_subgroupOf_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_of_hatA6 {Q : Type} [Group Q] [Finite Q] (hZ3 : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) : Nat.card Q = 1080 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ3,
    Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_quot_of_sl_three {Q : Type*} [Group Q]
    (h : Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) : Nat.card Q = 168 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two]

theorem card_quot_of_sl_five {Q : Type*} [Group Q]
    (h : Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) : Nat.card Q = 9999360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_sl_five_zmod_two]

theorem modules_cases_of_hyp1223 [Finite G] (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) :
    ∃ _ : IsMulCommutative ↥V,
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
        Nat.card V ≤ 2 ^ 4) ∧
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
        G2NaturalDerived (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) 1) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        Nat.card V = 2 ^ 10 → IsIrreducibleUnder L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hc, hmod⟩ := hall V hyp.irrPlus
  refine ⟨hc, ?_⟩
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred
  have hcardU : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := card_of_lieModel_psu_three_three
  have hsimp5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := fun ⟨e⟩ => by
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact e.isSimpleGroup
  rcases hmod with ⟨m, hm, ⟨e⟩, hnat⟩ | ⟨⟨e⟩, hV4, -⟩ | ⟨⟨e⟩, -, hirr⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, hg2⟩ |
      ⟨-, hZ3, ⟨e⟩, -, -, -⟩
  · have hQ := Nat.card_congr e.toEquiv
    have hVn := (card_and_sq_of_binaryNaturalSL hnat).1
    refine ⟨fun h => ?_, fun h => ?_, fun h hV10 => ?_⟩
    · rw [card_quot_of_sl_three h] at hQ
      rcases hm with rfl | rfl | rfl
      · rw [hVn]; norm_num
      · rw [card_sl_four_zmod_two] at hQ; norm_num at hQ
      · rw [card_sl_five_zmod_two] at hQ; norm_num at hQ
    · exfalso
      rw [hcardU h] at hQ
      rcases hm with rfl | rfl | rfl
      · rw [card_sl_three_zmod_two] at hQ; norm_num at hQ
      · rw [card_sl_four_zmod_two] at hQ; norm_num at hQ
      · rw [card_sl_five_zmod_two] at hQ; norm_num at hQ
    · exfalso
      rw [card_quot_of_sl_five h] at hQ
      rcases hm with rfl | rfl | rfl
      · rw [card_sl_three_zmod_two] at hQ; norm_num at hQ
      · rw [card_sl_four_zmod_two] at hQ; norm_num at hQ
      · rw [hVn] at hV10; norm_num at hV10
  · have hQ := Nat.card_congr e.toEquiv
    rw [card_sl_three_zmod_two] at hQ
    refine ⟨fun _ => hV4.le, fun h => ?_, fun h _ => ?_⟩
    · rw [hcardU h] at hQ; norm_num at hQ
    · rw [card_quot_of_sl_five h] at hQ; norm_num at hQ
  · have hQ := Nat.card_congr e.toEquiv
    rw [card_sl_five_zmod_two] at hQ
    refine ⟨fun h => ?_, fun h => ?_, fun _ _ => hirr⟩
    · rw [card_quot_of_sl_three h] at hQ; norm_num at hQ
    · rw [hcardU h] at hQ; norm_num at hQ
  · have h5 := (five_dvd_card_alternating hm5 hm8).trans
      (card_dvd_card_quotient_pCore hO2 φ hφ hker)
    refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_⟩
    · rw [card_quot_of_sl_three h] at h5; norm_num at h5
    · rw [hcardU h] at h5; norm_num at h5
    · exfalso
      have : Nontrivial (alternatingGroup (Fin m)) :=
        (alternatingGroup.isSimpleGroup (by simp; omega)).toNontrivial
      have h1 := card_eq_of_surjective_of_simple hO2 (hsimp5 h) φ hφ hker
      rw [card_quot_of_sl_five h] at h1
      interval_cases m <;> rw [nat_card_alternatingGroup] at h1 <;>
        norm_num [Nat.factorial] at h1
  · have h5 := (five_dvd_card_alternating (m := 7) (by norm_num) (by norm_num)).trans
      (card_dvd_card_quotient_pCore hO2 φ hφ hker)
    refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_⟩
    · rw [card_quot_of_sl_three h] at h5; norm_num at h5
    · rw [hcardU h] at h5; norm_num at h5
    · exfalso
      have : Nontrivial (alternatingGroup (Fin 7)) :=
        (alternatingGroup.isSimpleGroup (by simp)).toNontrivial
      have h1 := card_eq_of_surjective_of_simple hO2 (hsimp5 h) φ hφ hker
      rw [card_quot_of_sl_five h, nat_card_alternatingGroup] at h1
      norm_num [Nat.factorial] at h1
  · have hQ := hcardU hU
    refine ⟨fun h => ?_, fun _ => hg2, fun h _ => ?_⟩
    · rw [card_quot_of_sl_three h] at hQ; norm_num at hQ
    · rw [card_quot_of_sl_five h] at hQ; norm_num at hQ
  · have hQ := card_of_hatA6 hZ3 e
    refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_⟩
    · rw [card_quot_of_sl_three h] at hQ; norm_num at hQ
    · rw [hcardU h] at hQ; norm_num at hQ
    · rw [card_quot_of_sl_five h] at hQ; norm_num at hQ

theorem four_lt_relIndex_of_simple [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, L⁆ = V)
    (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (h24 : 24 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    4 < (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
  by_contra hle
  push Not at hle
  have h1 := commutator_le_of_relIndex_le_four hLV inf_le_right (CFSG.pCore 2 ↥L)
    (fun x hx => by
      exact hO2 ⟨x, hx, rfl⟩) hs h24 hle
  rw [hcomm] at h1
  apply hnc
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.1 (h1 hv).2 l hl).symm

theorem pre1242_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hG2c : G2NaturalCover)
    (hL52 : L52TenSylowFixedLine) : Pre1242 := by
  have hG2 := g2NaturalCohomologyOne_of_cover hG2c
  intro G _ _ T L V hcx
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨hc, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hV1
    rw [← hcomm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
  have hGz : ∀ z : G, z ≠ 1 → z ^ 2 = 1 → L ⊔ T ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro z hz1 hz2 hLT
    have hzP : z ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
      have hle : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hnorm : Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
        have h1 : Subgroup.centralizer ({z} : Set G) =
            Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        rw [h1]
        exact Subgroup.centralizer_le_normalizer _
      have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm hzp
        (Subgroup.mem_zpowers z)
    obtain ⟨M', hM', hle⟩ := exists_inM_of_pCoreOf_ne_bot (fun h => hz1 (by
      rw [h] at hzP
      exact hzP))
    rw [← huniq M' hM' (hLT.trans hle)]
    exact hle
  have hZmem : ∀ z ∈ V, z ∈ Subgroup.centralizer (T : Set G) → z ∈ quasithinOmegaOneCenter T :=
    fun z hz hzT => Subgroup.subset_closure ⟨⟨hVT hz, hzT⟩, hsq z hz⟩
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_right
  have hcardU : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := card_of_lieModel_psu_three_three
  have hsimp5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := fun ⟨e⟩ => by
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact e.isSimpleGroup
  rcases hcx.cx with ⟨hq, hZV⟩ | ⟨hq5, hcard, hCM⟩
  ·
    have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
      have hle2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 := by
        rcases hq with h3' | hU
        ·
          have hV16 := hcases.1 h3'
          obtain ⟨e⟩ := h3'
          have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
            have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
            exact e.isSimpleGroup
          have hidx := four_lt_relIndex_of_simple hLV hcomm hnc hO2 hs3
            (by rw [card_quot_of_sl_three ⟨e⟩]; norm_num)
          have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
          rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V)] at h1
          have h2 := E3.relIndex_eq_two_pow hVp (V ⊓ Subgroup.centralizer (L : Set G))
          have h8 : 8 ≤ (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
            rw [h2] at hidx ⊢
            have hm : 3 ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) := by
              by_contra hm
              push Not at hm
              interval_cases (E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G))) <;>
                norm_num at hidx
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
          by_contra hgt
          push Not at hgt
          have : 8 * 3 ≤ Nat.card V := by
            rw [← h1]
            exact Nat.mul_le_mul h8 hgt
          omega
        ·
          have hg2 := hcases.2.1 hU
          have hfix := fixV_autOn_eq (K := L) (V := V) hLV
          have h1 := hG2 ↥V (fun v => Subtype.ext (by simpa using hsq v v.2)) (autOn L V)
            (commV_autOn_eq_top hLV hcomm) (by rw [hfix]; exact hg2)
          rw [hfix, card_subgroupOf_eq_card_inf] at h1
          exact h1
      have hne1 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ≠ 1 := fun h =>
        hZV (Subgroup.card_eq_one.1 h)
      have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
      omega
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZV
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzeq := zpowers_eq_of_card_eq_two hZ2 hzZ hz1'
    have hTZ : T ≤ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTV ht, F7.normalizer_le_normalizer_centralizer L (hyp.normalizes ht)⟩
    have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
      have h1 := le_centralizer_normalizer_of_card_eq_two hZ2 hzZ
      rw [Subgroup.mem_centralizer_iff] at h1 ⊢
      intro t ht
      exact h1 t (hTZ ht)
    refine ⟨z, ⟨hzZ.1, hZmem z hzZ.1 hzT⟩, orderOf_eq_prime (hsq z hzZ.1) hz1',
      hGz z hz1' (hsq z hzZ.1) ?_, fun _ => hzeq.symm, fun h5 => ?_⟩
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hzZ.2 x hx
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hzT x hx
    · exfalso
      rcases hq with h3' | hU
      · have h1 := card_quot_of_sl_three h3'
        rw [card_quot_of_sl_five h5] at h1
        norm_num at h1
      · have h1 := hcardU hU
        rw [card_quot_of_sl_five h5] at h1
        norm_num at h1
  ·
    have hirr := hcases.2.2 hq5 hcard
    have hs5 := hsimp5 hq5
    obtain ⟨e5⟩ := hq5
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hs5 hnc
    have hsylTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal
        (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
        (sup_le Subgroup.le_normalizer hyp.normalizes)
    have hline := hL52 G L V (T ⊓ L) hLV hsq hab hcard hirr ⟨eA.trans e5⟩ hsylTL
    have hCT : V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
      inf_centralizer_ne_bot_of_isPGroup hyp.sylow.1 hVT hTV hV1
    have hle : V ⊓ Subgroup.centralizer (T : Set G) ≤
        V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)
    have hCT2 : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
      have h1 := Subgroup.card_le_of_le hle
      rw [hline] at h1
      have h2 : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) ≠ 1 := fun h =>
        hCT (Subgroup.card_eq_one.1 h)
      have h3 : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) := Nat.card_pos
      omega
    have hZV : V ⊓ quasithinOmegaOneCenter T = V ⊓ Subgroup.centralizer (T : Set G) :=
      le_antisymm (inf_le_inf_left _ hZT) (fun x hx => ⟨hx.1, hZmem x hx.1 hx.2⟩)
    rw [← hZV] at hCT2
    have hne : V ⊓ quasithinOmegaOneCenter T ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hCT2
      norm_num at hCT2
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzeq := zpowers_eq_of_card_eq_two hCT2 hzZ hz1'
    refine ⟨z, hzZ, orderOf_eq_prime (hsq z hzZ.1) hz1', ?_, fun h => ?_, fun _ => hzeq.symm⟩
    · have h1 : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer
          ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) := by
        rw [← hzeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [h1]
      exact hCM
    · exfalso
      rcases h with h3' | hU
      · have h1 := card_quot_of_sl_three h3'
        rw [card_quot_of_sl_five ⟨e5⟩] at h1
        norm_num at h1
      · have h1 := hcardU hU
        rw [card_quot_of_sl_five ⟨e5⟩] at h1
        norm_num at h1

end CFSG.Quasithin.H13
