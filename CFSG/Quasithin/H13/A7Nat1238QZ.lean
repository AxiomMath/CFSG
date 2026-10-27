module

public import CFSG.Quasithin.H13.A7Nat1238QOff
public import CFSG.Quasithin.H13.A7Nat1238Ke
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.H13.A7NatMain
public import CFSG.Quasithin.Vol2.Ch1Chief

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def commTo (X Y : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (X : Set G) ∧ g ∈ normalizer (Y : Set G) ∧
    ∀ x ∈ X, x * g * x⁻¹ * g⁻¹ ∈ Y}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haX, haY, ha⟩ ⟨hbX, hbY, hb⟩
    refine ⟨mul_mem haX hbX, mul_mem haY hbY, fun x hx => ?_⟩
    have h1 := ha x hx
    have h2 : a * (x * b * x⁻¹ * b⁻¹) * a⁻¹ ∈ Y := (mem_normalizer_iff.1 haY _).1 (hb x hx)
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haX, haY, ha⟩
    refine ⟨inv_mem haX, inv_mem haY, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ X := (mem_normalizer_iff.1 (inv_mem haX) x).1 hx
    have h1 := ha _ hx'
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ =
        (a⁻¹ * x * a⁻¹⁻¹ * a * (a⁻¹ * x * a⁻¹⁻¹)⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

theorem mem_commTo {X Y : Subgroup G} {g : G} :
    g ∈ commTo X Y ↔ g ∈ normalizer (X : Set G) ∧ g ∈ normalizer (Y : Set G) ∧
      ∀ x ∈ X, x * g * x⁻¹ * g⁻¹ ∈ Y := Iff.rfl

theorem commutator_le_of_le_commTo {X Y L : Subgroup G} (h : L ≤ commTo X Y) : ⁅X, L⁆ ≤ Y := by
  rw [commutator_le]
  intro x hx l hl
  rw [commutatorElement_def]
  exact (h hl).2.2 x hx

theorem le_commTo_of_eq_commutator {X Y L J : Subgroup G} (hLJ : L = ⁅L, J⁆)
    (hLX : L ≤ normalizer (X : Set G)) (hLY : L ≤ normalizer (Y : Set G))
    (hJ : J ≤ commTo X Y) : L ≤ commTo X Y := by
  rw [hLJ, commutator_le]
  intro l hl j hj
  rw [commutatorElement_def]
  refine mul_mem ?_ (inv_mem (hJ hj))
  obtain ⟨hjX, hjY, hjc⟩ := hJ hj
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · exact mul_mem (mul_mem (hLX hl) hjX) (inv_mem (hLX hl))
  · exact mul_mem (mul_mem (hLY hl) hjY) (inv_mem (hLY hl))
  · have hx' : l⁻¹ * x * l⁻¹⁻¹ ∈ X := (mem_normalizer_iff.1 (inv_mem (hLX hl)) x).1 hx
    have h1 := hjc _ hx'
    have h2 : l * (l⁻¹ * x * l⁻¹⁻¹ * j * (l⁻¹ * x * l⁻¹⁻¹)⁻¹ * j⁻¹) * l⁻¹ ∈ Y :=
      (mem_normalizer_iff.1 (hLY hl) _).1 h1
    have e : x * (l * j * l⁻¹) * x⁻¹ * (l * j * l⁻¹)⁻¹ =
        l * (l⁻¹ * x * l⁻¹⁻¹ * j * (l⁻¹ * x * l⁻¹⁻¹)⁻¹ * j⁻¹) * l⁻¹ := by group
    rw [e]
    exact h2

variable [Finite G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

omit [Finite G] in
theorem comm_mem_pCoreOf_of_centralizes (h : A7NatPre T L V ψ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hLp : ⁅L, L⁆ = L) {t : G}
    (htL : t ∈ normalizer (L : Set G)) (htV : t ∈ centralizer (V : Set G)) {l : G}
    (hl : l ∈ L) : l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L := by
  classical
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L with hQ
  have hcL : ∀ l ∈ L, l * t * l⁻¹ * t⁻¹ ∈ L := fun l hl => by
    have h1 : t * l⁻¹ * t⁻¹ ∈ L := (mem_normalizer_iff.1 htL _).1 (inv_mem hl)
    have := mul_mem hl h1
    simpa [mul_assoc] using this
  have hcV : ∀ l ∈ L, l * t * l⁻¹ * t⁻¹ ∈ centralizer (V : Set G) := fun l hl =>
    mul_mem (conj_mem_centralizer_of_mem_normalizer (h.L_le hl) htV) (inv_mem htV)
  have hcZ : ∀ l : L, (QuotientGroup.mk (⟨_, hcL l l.2⟩ : L) : Q) ∈ center Q := by
    intro l
    rw [mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have h1 := commutator_mem_pCoreOf_of_centralizer h hLq (hcL l l.2) (hcV l l.2) y.2
      rw [pCoreOf_eq_map_cfsgPCore] at h1
      obtain ⟨z, hz, hzeq⟩ := h1
      have hz' : (⟨_, hcL l l.2⟩ : L) * y * (⟨_, hcL l l.2⟩ : L)⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L := by
        have : z = (⟨_, hcL l l.2⟩ : L) * y * (⟨_, hcL l l.2⟩ : L)⁻¹ * y⁻¹ := Subtype.ext hzeq
        rwa [← this]
      have h2 := (QuotientGroup.eq_one_iff _).2 hz'
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      have h3 := congrArg (· * (QuotientGroup.mk y : Q) * (QuotientGroup.mk (⟨_, hcL l l.2⟩ : L)))
        h2
      simp only [one_mul, mul_assoc] at h3
      simpa [mul_assoc] using h3.symm
  let φ : ↥L →* ↥(center Q) :=
    { toFun := fun l => ⟨_, hcZ l⟩
      map_one' := by
        apply Subtype.ext
        show (QuotientGroup.mk (⟨_, hcL 1 (one_mem L)⟩ : L) : Q) = 1
        rw [QuotientGroup.eq_one_iff]
        have : (⟨_, hcL 1 (one_mem L)⟩ : L) = 1 := Subtype.ext (by simp)
        rw [this]
        exact one_mem _
      map_mul' := fun a b => by
        apply Subtype.ext
        show (QuotientGroup.mk (⟨_, hcL (a * b) (mul_mem a.2 b.2)⟩ : L) : Q) =
          QuotientGroup.mk (⟨_, hcL a a.2⟩ : L) * QuotientGroup.mk (⟨_, hcL b b.2⟩ : L)
        have e : (⟨_, hcL (a * b) (mul_mem a.2 b.2)⟩ : L) =
            a * (⟨_, hcL b b.2⟩ : L) * a⁻¹ * (⟨_, hcL a a.2⟩ : L) :=
          Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
        rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
        have hc := mem_center_iff.1 (hcZ b) (QuotientGroup.mk a)
        rw [hc, mul_inv_cancel_right]
        exact mem_center_iff.1 (hcZ a) _ }
  have hperf : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff).2 hLp
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hperf]
    exact Abelianization.commutator_subset_ker φ
  have h1 : (⟨l, hl⟩ : L) ∈ φ.ker := by rw [hker]; exact mem_top _
  have h2 : (QuotientGroup.mk (⟨_, hcL l hl⟩ : L) : Q) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 h1)
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩

theorem inf_centralizer_le_pCoreOf (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) :
    T ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLp : ⁅L, L⁆ = L := hyp.maximal.1.2.1.2.1
  have hO2L : pCoreOf 2 L ≤ T := by
    have hLn : (L.subgroupOf (L ⊔ T)).Normal :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le le_normalizer hyp.normalizes)
    exact (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T)
      le_sup_left hLn).trans (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (isSylowTwoOf_of_le hyp.sylow le_sup_right))
  have hconj : ∀ g ∈ L ⊔ T, ∀ n ∈ T ⊓ centralizer (V : Set G),
      g * n * g⁻¹ ∈ T ⊓ centralizer (V : Set G) := by
    have key : ∀ g ∈ L ⊔ T,
        g ∈ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
      intro g hg
      refine (sup_le ?_ ?_ : L ⊔ T ≤ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) :
        Set G)) hg
      · intro l hl
        rw [mem_normalizer_iff]
        have hfwd : ∀ l ∈ L, ∀ n ∈ T ⊓ centralizer (V : Set G),
            l * n * l⁻¹ ∈ T ⊓ centralizer (V : Set G) := by
          intro l hl n hn
          refine Subgroup.mem_inf.2 ⟨?_, conj_mem_centralizer_of_mem_normalizer (h.L_le hl)
            (Subgroup.mem_inf.1 hn).2⟩
          have h1 := hO2L (comm_mem_pCoreOf_of_centralizes h hyp.quasisimple hLp
            (hyp.normalizes (Subgroup.mem_inf.1 hn).1) (Subgroup.mem_inf.1 hn).2 hl)
          have e : l * n * l⁻¹ = (l * n * l⁻¹ * n⁻¹) * n := by group
          rw [e]
          exact T.mul_mem h1 (Subgroup.mem_inf.1 hn).1
        intro n
        refine ⟨fun hn => hfwd l hl n hn, fun hn => ?_⟩
        have := hfwd l⁻¹ (inv_mem hl) _ hn
        simpa [mul_assoc] using this
      · intro s hs
        rw [mem_normalizer_iff]
        have hfwd : ∀ s ∈ T, ∀ n ∈ T ⊓ centralizer (V : Set G),
            s * n * s⁻¹ ∈ T ⊓ centralizer (V : Set G) := fun s hs n hn =>
          Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem hs (Subgroup.mem_inf.1 hn).1) (T.inv_mem hs),
            conj_mem_centralizer_of_mem_normalizer (h.T_le hs) (Subgroup.mem_inf.1 hn).2⟩
        intro n
        refine ⟨fun hn => hfwd s hs n hn, fun hn => ?_⟩
        have := hfwd s⁻¹ (inv_mem hs) _ hn
        simpa [mul_assoc] using this
    exact fun g hg n hn => (mem_normalizer_iff.1 (key g hg) n).1 hn
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    (fun g hg => ?_) (hyp.sylow.1.to_le inf_le_left)
  rw [mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hconj g hg n hn, fun hn => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ hn
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_of_forall_commute {U : Subgroup G} {x : G}
    (h : ∀ u ∈ U, x * u = u * x) : x ∈ normalizer (U : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have e : x * g * x⁻¹ = g := by rw [h g hg, mul_inv_cancel_right]
    rw [e]
    exact hg
  · intro hg
    have h1 := h _ hg
    have h2 : x * g * x⁻¹ = g := by
      apply mul_left_cancel (a := x)
      rw [h1]
      group
    rw [← h2]
    exact hg

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_commute {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G} (hg : g ∈ X ⊔ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hXN : X ≤ normalizer (Y : Set G) := fun x hx =>
    mem_normalizer_of_forall_commute fun u hu => h x hx u hu
  have hg' : g ∈ (↑(X ⊔ Y) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

omit [Finite G] in
theorem card_sup_mul_card_inf_of_commute [Finite G] {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  let φ : X × Y →* G := X.subtype.noncommCoprod Y.subtype (fun x y => h x x.2 y y.2)
  have hφ : ∀ (x : X) (y : Y), φ (x, y) = (x : G) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hrange : φ.range = X ⊔ Y := by
    ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact Subgroup.mul_mem_sup x.2 y.2
    · intro hg
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute h hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hφ _ _⟩
  have hker : Nat.card φ.ker = Nat.card (X ⊓ Y : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : G), k.1.1.2, by
          have h1 : (k.1.1 : G) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          have h2 : (k.1.1 : G) = (k.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [h2]
          exact Y.inv_mem k.1.2.2⟩
        invFun := fun g => ⟨(⟨g, g.2.1⟩, ⟨(g : G)⁻¹, Y.inv_mem g.2.2⟩), by
          rw [MonoidHom.mem_ker, hφ]
          exact mul_inv_cancel _⟩
        left_inv := fun k => by
          refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext ?_))
          have h1 : (k.1.1 : G) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          exact inv_eq_of_mul_eq_one_right h1
        right_inv := fun g => Subtype.ext rfl }
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h

open CFSG.Quasithin.BlueprintB2 in
theorem commutator_le_of_isMaxElemAbelian (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ)
    (hTP : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ t σ) (hred : IsTwoReducedIn (L ⊔ T) V)
    {A : Subgroup G} (hAmax : IsMaxElemAbelian T A) :
    ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ T)), A⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set V₀ := omegaOneCenterOf Q with hV₀
  have hQT : Q ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_le hyp.sylow le_sup_right)
  have hV₀Q : V₀ ≤ Q := A4.omegaOneCenterOf_le Q
  have hV₀T : V₀ ≤ T := hV₀Q.trans hQT
  have hQV₀ : Q ≤ centralizer (V₀ : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.1
      (A4.centerOf_le_centralizer Q (A4.omegaOneCenterOf_le_centerOf Q hx)) q hq).symm
  have hTV₀ : T ≤ normalizer (V₀ : Set G) := le_sup_right.trans
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf Q))
  have hV₀el : IsElementaryAbelian 2 V₀ := isElementaryAbelian_iff.2
    ⟨fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb,
      fun x hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩
  have hVQ : V ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1
    (hyp.sylow.1.to_le h.le_T)
  have hQCV : Q ≤ centralizer (V : Set G) := by
    refine hred.2.2.2 Q (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [h1]
    exact one_mem _
  have hVV₀ : V ≤ V₀ := by
    intro v hv
    refine Subgroup.subset_closure ⟨⟨hVQ hv, ?_⟩, ?_⟩
    · show v ∈ centralizer (Q : Set G)
      rw [mem_centralizer_iff]
      intro q hq
      exact (mem_centralizer_iff.1 (hQCV hq) v hv).symm
    · have := congrArg Subtype.val (sq_eq_one_of_vec ψ ⟨v, hv⟩)
      simpa [pow_two] using this
  have hCT : T ⊓ centralizer (V : Set G) ≤ centralizer (V₀ : Set G) :=
    (inf_centralizer_le_pCoreOf hyp h).trans hQV₀
  have hAT : A ≤ T := hAmax.1
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans h.T_le
  have hAel : IsElementaryAbelian 2 A := (isElemAbelian_iff_isElementaryAbelian 2).1 hAmax.2.1
  have hAeq : A ⊓ centralizer (V₀ : Set G) = A ⊓ centralizer (V : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (centralizer_le hVV₀)) ?_
    rintro a ⟨haA, haV⟩
    exact ⟨haA, hCT ⟨hAT haA, haV⟩⟩
  have hidx₀ : (V₀ ⊓ centralizer (A : Set G)).relIndex V₀ ≤
      (A ⊓ centralizer (V : Set G)).relIndex A := by
    have : (V₀.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀T).2 hTV₀
    have h1 := relIndex_inf_centralizer_le (p := 2) (V := V₀.subgroupOf T)
      (A := A.subgroupOf T) (isElementaryAbelian_subgroupOf hV₀el)
      (isElementaryAbelian_subgroupOf hAel) (fun E hE => by
        have h2 := hAmax.2.2 (E.map (T : Subgroup G).subtype) (map_subtype_le E)
          ((isElemAbelian_iff_isElementaryAbelian 2).2 (isElementaryAbelian_map hE _))
        rwa [card_map_of_injective (subtype_injective _), ← card_subgroupOf_eq hAT] at h2)
    rw [centralizer_subgroupOf_eq hAT, centralizer_subgroupOf_eq hV₀T, ← inf_subgroupOf_eq,
      ← inf_subgroupOf_eq, relIndex_subgroupOf hV₀T, relIndex_subgroupOf hAT] at h1
    rwa [hAeq] at h1
  set lamN : normalizer (V : Set G) →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  set f : A →* Perm (Fin 7) := lamN.comp (inclusion hAN) with hfdef
  have hf_spec : ∀ a : A, IsCoordAct ψ a (f a) := fun a =>
    coordRep_spec ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hf_eq : ∀ (a : A) {σ : Perm (Fin 7)}, IsCoordAct ψ a σ → f a = σ := fun a σ hσ =>
    IsCoordAct.unique ψ (hAN a.2) (hf_spec a) hσ
  have hfP : f.range ≤ sevenP := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨σ, hσP, hσ⟩ := hTP a (hAT a.2)
    rw [hf_eq a hσ]
    exact hσP
  have hf2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have ha2 : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact (isElementaryAbelian_iff.1 hAel).2 a a.2)
    rw [ha2, map_one]
  have hker : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact coordRep_eq_one_iff ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hcardA : (A ⊓ centralizer (V : Set G)).relIndex A = Nat.card f.range := by
    rw [inf_relIndex_left, relIndex, ← hker, index_ker]
  have hcardV : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩,
      ?_, ?_⟩) ⟨?_, ?_⟩)
    · exact (mem_evenWeight).1 (vec_mem ψ _)
    · rintro _ ⟨a, rfl⟩
      have h1 := hf_spec a ⟨(x : G), (mem_inf.1 x.2).1⟩ ⟨(x : G), (mem_inf.1 x.2).1⟩ (by
        show (x : G) = a * x * (a : G)⁻¹
        rw [mem_centralizer_iff.1 (mem_inf.1 x.2).2 a a.2, mul_inv_cancel_right])
      exact h1.symm
    · intro x y hxy
      have h1 : vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩ = vec ψ ⟨(y : G), (mem_inf.1 y.2).1⟩ :=
        congrArg (fun z : fixE (f.range : Set (Perm (Fin 7))) => (z : Fin 7 → ZMod 2)) hxy
      have h2 : (x : G) = y := congrArg (fun z : V => (z : G)) (vec_injective ψ h1)
      exact Subtype.ext h2
    · rintro ⟨v, hv1, hv2⟩
      obtain ⟨x, hx⟩ := exists_vec_eq ψ (mem_evenWeight.2 hv1)
      refine ⟨⟨x, mem_inf.2 ⟨x.2, ?_⟩⟩, Subtype.ext hx⟩
      rw [mem_centralizer_iff]
      intro a ha
      let y : V := ⟨a * x * a⁻¹, (mem_normalizer_iff.1 (hAN ha) x).1 x.2⟩
      have h1 := hf_spec ⟨a, ha⟩ x y rfl
      rw [hx, hv2 _ ⟨⟨a, ha⟩, rfl⟩, ← hx] at h1
      have h2 : a * (x : G) * a⁻¹ = x := congrArg Subtype.val (vec_injective ψ h1)
      calc a * (x : G) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h2]
  have hbound := card_mul_fixE_le hfP hf2
  have hV64 : (V ⊓ centralizer (A : Set G)).relIndex V *
      Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = 64 := by
    have h1 := relIndex_mul_card (V ⊓ centralizer (A : Set G)) V
    rwa [inf_of_le_left inf_le_left, nat_card_of_vec ψ] at h1
  have hpos : 0 < Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hidxV : (A ⊓ centralizer (V : Set G)).relIndex A ≤
      (V ⊓ centralizer (A : Set G)).relIndex V := by
    rw [hcardA]
    rw [← hcardV] at hbound
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_pos_right hlt hpos
    omega
  set C := V₀ ⊓ centralizer (A : Set G) with hC
  have hcommVC : ∀ x ∈ V, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    A4.mul_comm_of_mem_omegaOneCenterOf (hVV₀ hx) (mem_inf.1 hy).1
  have hVC : V ⊓ C = V ⊓ centralizer (A : Set G) := by
    rw [hC, ← inf_assoc, inf_of_le_left hVV₀]
  have hsup := card_sup_mul_card_inf_of_commute hcommVC
  rw [hVC] at hsup
  have hV₀card : C.relIndex V₀ * Nat.card C = Nat.card V₀ := by
    have h1 := relIndex_mul_card C V₀
    rwa [inf_of_le_left inf_le_left] at h1
  have hVcard : (V ⊓ centralizer (A : Set G)).relIndex V *
      Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = Nat.card V := by
    have h1 := relIndex_mul_card (V ⊓ centralizer (A : Set G)) V
    rwa [inf_of_le_left inf_le_left] at h1
  have hWV₀ : V ⊔ C ≤ V₀ := sup_le hVV₀ inf_le_left
  have hcardW : Nat.card V₀ ≤ Nat.card (V ⊔ C : Subgroup G) := by
    have h1 : Nat.card (V ⊔ C : Subgroup G) = (V ⊓ centralizer (A : Set G)).relIndex V *
        Nat.card C := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hsup, ← hVcard]
      ring
    rw [h1, ← hV₀card]
    exact Nat.mul_le_mul_right _ (hidx₀.trans hidxV)
  have hW : V ⊔ C = V₀ := Subgroup.eq_of_le_of_card_ge hWV₀ hcardW
  rw [commutator_le]
  intro x hx a ha
  rw [← hW] at hx
  obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommVC hx
  have hca : c * a = a * c := (mem_centralizer_iff.1 (mem_inf.1 hc).2 a ha).symm
  have e : ⁅v * c, a⁆ = v * (a * v⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc v * c * a * (v * c)⁻¹ * a⁻¹ = v * (c * a) * c⁻¹ * v⁻¹ * a⁻¹ := by group
      _ = v * (a * v⁻¹ * a⁻¹) := by rw [hca]; group
  rw [e]
  exact mul_mem hv ((mem_normalizer_iff.1 (hAN ha) _).1 (inv_mem hv))


theorem commutator_omegaOneCenter_le_of_alt7_natural (hyp : Hyp1223 G T L V)
    (h : A7NatPre T L V ψ) (hTP : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ t σ)
    (hred : IsTwoReducedIn (L ⊔ T) V) (hJ : L = ⁅L, thompsonJ T⁆) :
    ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ T)), L⁆ ≤ V := by
  set V₀ := omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) with hV₀
  have hLTV₀ : L ⊔ T ≤ normalizer (V₀ : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hJ' : thompsonJ T ≤ commTo V₀ V := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    refine ⟨hLTV₀ (le_sup_right (b := T) (hA.1 ha)), h.T_le (hA.1 ha), fun x hx => ?_⟩
    have h1 := commutator_le_of_isMaxElemAbelian hyp h hTP hred hA
      (commutator_mem_commutator hx ha)
    rwa [commutatorElement_def] at h1
  exact commutator_le_of_le_commTo
    (le_commTo_of_eq_commutator hJ (le_sup_left.trans hLTV₀) h.L_le hJ')

end CFSG.Quasithin.H13.A7
