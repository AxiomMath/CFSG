module

public import CFSG.Milestones.ASVolI.C135.NC
public import CFSG.Milestones.ASVolI.C135.P4a
public import CFSG.Milestones.ASVolI.C135.P4c
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Fin

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q mem_pCoreOf_iff')
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll msPair_facts)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem burnsideC135_exists_H1 {X R L : Subgroup G} {F : Type} [Field F] [Fintype F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hF : Fintype.card F = 2) (hMS : IsMSPair X R)
    (hL : L ∈ cComp X) (hG : (X : Set G) = (L : Set G) * (R : Set G))
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hα : IsModO2Surj L α)
    (hCL : X ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (h1 : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L (c134Q X L) (centerOf (c134Q X L)) α true 2) :
    ∃ (β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F))
      (βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)),
      burnsideC135_H1 X R L α β βU := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF
  have hLX : L ≤ X := le_of_mem_cComp hL
  obtain ⟨hRX, hTR, hRp⟩ := msPair_facts hMS
  obtain ⟨S₀, hS₀, hRS₀⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge hRX hRp
  have hQT : c134Q X L ≤ pCoreOf 2 X :=
    (MS93.commutator_le_pCoreOf hLX hXL).trans
      (MS93.pCoreOf_le_pCoreOf_of_le_normalizer hLX hXL)
  have hQS₀ : c134Q X L ≤ S₀ := hQT.trans (hTR.trans hRS₀)
  have hXQ : X ≤ Subgroup.normalizer (c134Q X L : Set G) := le_normalizer_c134Q hXL
  obtain ⟨β, βU, hβs, hβk, hβeq, hD, hS₀W⟩ :=
    burnsideC135_exists_invariant_dualSplit hα hLX hXL hS₀ hQS₀ hXQ h1 h2
  refine ⟨β, βU, ⟨hF, hMS, hL, hG, hXL, hα, hCL, h1, hβs, hβk, hβeq, hD, fun x hx => ?_⟩⟩
  have hx' : x ∈ (L : Set G) * (R : Set G) := hG ▸ hx
  obtain ⟨l, hl, r, hr, rfl⟩ := hx'
  exact Subgroup.mul_mem _ (hD.norm₁ hl) (hS₀W (hRS₀ hr))

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem isElemAbelian_U : IsElemAbelian 2 (centerOf (c134Q X L)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
  · rw [sq]
    exact burnsideC135_U_sq H.dsg hu

theorem U_ne_bot : centerOf (c134Q X L) ≠ ⊥ := by
  intro h
  obtain ⟨u, hu⟩ := H.dsg.natU_onto (Multiplicative.ofAdd (Pi.single 0 1))
  have hu1 : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (h ▸ u.2))
  rw [hu1, map_one] at hu
  have := congrFun (congrArg Multiplicative.toAdd hu) 0
  simp at this

theorem exists_maxElemAbelian_not_le :
    ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ pCoreOf 2 X := by
  obtain ⟨-, hTR, -⟩ := msPair_facts H.ms
  by_contra hcon
  push Not at hcon
  have hJT : thompsonJ R ≤ pCoreOf 2 X := iSup₂_le fun A hA => hcon A hA
  have hJeq : thompsonJ R = thompsonJ (pCoreOf 2 X) := thompsonJ_eq_of_le hJT hTR
  have hUR : centerOf (c134Q X L) ≤ R := ((inf_le_left).trans H.Q_le).trans hTR
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian R
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    have h1 := hA₀.2.2 _ hUR H.isElemAbelian_U
    rw [h, Subgroup.card_bot] at h1
    exact H.U_ne_bot (Subgroup.eq_bot_of_card_le _ h1)
  have hJne : thompsonJ R ≠ ⊥ := fun h =>
    hA₀ne (le_bot_iff.mp (h ▸ (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian R A) => A) A₀ hA₀)))
  refine H.ms.2.2 (thompsonJ R) (thompsonJ_le_self R) hJne
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R) ?_
  rw [hJeq]
  intro g hg
  have hgT : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X hg
  have h1 := cjSub_thompsonJ hgT
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h1, mem_cjSub] at hx
    simpa [mul_assoc] using hx

@[expose] noncomputable def q0 : QC (centerOf (c134Q X L)) ⊥ F where
  κ u := Multiplicative.toAdd (βU u)
  mul u v := by
    show Multiplicative.toAdd (βU (u * v)) =
      Multiplicative.toAdd (βU u) + Multiplicative.toAdd (βU v)
    rw [map_mul, toAdd_mul]
  surj v := by
    obtain ⟨u, hu⟩ := H.dsg.natU_onto (Multiplicative.ofAdd v)
    exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
  ker u := by
    show Multiplicative.toAdd (βU u) = 0 ↔ (u : G) ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : βU u = βU 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h
      exact congrArg Subtype.val (burnsideC135_βU_injective H.dsg h1)
    · intro h
      have : u = 1 := Subtype.ext h
      rw [this, map_one]
      rfl

@[expose] noncomputable def q1 : QC (burnsideC135_Wc β 1) (centerOf (c134Q X L)) F where
  κ w := Multiplicative.toAdd (burnsideC135_βc β 1 w)
  mul u v := by
    show Multiplicative.toAdd (burnsideC135_βc β 1 (u * v)) =
      Multiplicative.toAdd (burnsideC135_βc β 1 u) + Multiplicative.toAdd (burnsideC135_βc β 1 v)
    rw [map_mul, toAdd_mul]
  surj v := by
    obtain ⟨u, hu⟩ := H.dsg.dual₁_onto (Multiplicative.ofAdd v)
    exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
  ker w := by
    show Multiplicative.toAdd (burnsideC135_βc β 1 w) = 0 ↔ (w : G) ∈ centerOf (c134Q X L)
    have h := H.dsg.dual₁_ker
    constructor
    · intro h0
      have h3 : w ∈ (burnsideC135_βc β 1).ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective h0
      rw [h, Subgroup.mem_subgroupOf] at h3
      exact h3
    · intro h0
      have h3 : w ∈ (burnsideC135_βc β 1).ker := by
        rw [h, Subgroup.mem_subgroupOf]
        exact h0
      rw [MonoidHom.mem_ker] at h3
      rw [h3]
      rfl

@[expose] noncomputable def q2 : QC (c134Q X L) (burnsideC135_Wc β 1) F where
  κ q := Multiplicative.toAdd (β q) 1
  mul u v := by
    show Multiplicative.toAdd (β (u * v)) 1 =
      Multiplicative.toAdd (β u) 1 + Multiplicative.toAdd (β v) 1
    rw [map_mul, toAdd_mul, Pi.add_apply]
  surj v := by
    obtain ⟨u, hu⟩ := H.βs (Multiplicative.ofAdd (fun _ => v))
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd (β u) 1 = v
    rw [hu]
    rfl
  ker q := by
    show Multiplicative.toAdd (β q) 1 = 0 ↔ (q : G) ∈ burnsideC135_Wc β 1
    constructor
    · intro h0
      exact burnsideC135_mem_Wc.mpr ⟨q.2, h0⟩
    · intro h0
      obtain ⟨hh, h3⟩ := burnsideC135_mem_Wc.mp h0
      exact h3

theorem q1_κ (w : ↥(burnsideC135_Wc β 1)) :
    H.q1.κ w = Multiplicative.toAdd (burnsideC135_βc β 1 w) := rfl

theorem q2_κ (q : ↥(c134Q X L)) : H.q2.κ q = Multiplicative.toAdd (β q) 1 := rfl

theorem nat₀ (g : ↥L) (x : ↥(centerOf (c134Q X L))) :
    H.q0.κ (cnj ((H.le.trans H.normU) g.2) x) =
      ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        H.q0.κ x :=
  H.dsg.natU_act g x (cnj ((H.le.trans H.normU) g.2) x) rfl

theorem nat₁ (g : ↥L) (x : ↥(burnsideC135_Wc β 1)) :
    H.q1.κ (cnj ((H.le.trans H.normW) g.2) x) =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ H.q1.κ x := by
  show Multiplicative.toAdd (burnsideC135_βc β 1 (cnj ((H.le.trans H.normW) g.2) x)) =
    ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd (burnsideC135_βc β 1 x)
  rw [H.dsg.dual₁_act g x (cnj ((H.le.trans H.normW) g.2) x) rfl, coe_dualHom]

theorem nat₂ (g : ↥L) (x : ↥(c134Q X L)) :
    H.q2.κ (cnj ((H.le.trans H.normQ) g.2) x) =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ H.q2.κ x := by
  show Multiplicative.toAdd (β (cnj ((H.le.trans H.normQ) g.2) x)) 1 =
    ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd (β x) 1
  rw [H.βeq g x (cnj ((H.le.trans H.normQ) g.2) x) rfl 1, moduleAct_true_eq]

theorem mem_T_of_rep {A : Subgroup G} (hAX : A ≤ X) (a : ↥A)
    (h : H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A) a = 1) : (a : G) ∈ pCoreOf 2 X := by
  refine H.centralizer_U_le ⟨hAX a.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have h3 := H.q0.rep_κ (hAX.trans H.normU) (le_normalizer_bot A) a ⟨u, hu⟩
  rw [h, Equiv.Perm.one_apply] at h3
  have h4 : (⟨u, hu⟩ : ↥(centerOf (c134Q X L))) = cnj ((hAX.trans H.normU) a.2) ⟨u, hu⟩ :=
    burnsideC135_βU_injective H.dsg (Multiplicative.toAdd.injective h3)
  have h7 : u = (a : G) * u * (a : G)⁻¹ := by
    have h8 := congrArg Subtype.val h4
    rw [coe_cnj] at h8
    exact h8
  calc u * (a : G) = (a : G) * u * (a : G)⁻¹ * a := by rw [← h7]
    _ = a * u := by group

theorem offender {A : Subgroup G} (hAX : A ≤ X) (hA : IsElemAbelian 2 A)
    (hAT : ¬ A ≤ pCoreOf 2 X) :
    Nat.card (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)).range * Nat.card F *
        Nat.card (fixAll (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A))) *
        Nat.card (fixAll (H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU))) <
        2 * Nat.card F ^ 6 ∧
      Nat.card (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)).range *
        Nat.card (fixAll (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A))) *
        Nat.card (fixAll (H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW))) <
        2 * Nat.card F ^ 6 := by
  have hne : (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)).range ≠ ⊥ := by
    intro h
    apply hAT
    intro b hb
    apply H.mem_T_of_rep hAX ⟨b, hb⟩
    rw [← Subgroup.mem_bot, ← h]
    exact ⟨⟨b, hb⟩, rfl⟩
  exact burnsideC135_offender (slNat α) (slNat_surjective H.surj.1) H.q0 H.q1 H.q2
    (H.le.trans H.normU) (H.le.trans H.normW) (H.le.trans H.normQ) H.nat₀ H.nat₁ H.nat₂
    (hAX.trans H.normU) (hAX.trans H.normW) (hAX.trans H.normQ) (hAX.trans H.normL) hA hne

theorem card_le_range_mul {A : Subgroup G} (hAX : A ≤ X) :
    Nat.card A ≤ Nat.card (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)).range *
      Nat.card ↥(A ⊓ pCoreOf 2 X) := by
  rw [← Subgroup.card_ker_mul_card_range (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)),
    mul_comm]
  refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.1.2,
    H.mem_T_of_rep hAX x.1 (MonoidHom.mem_ker.mp x.2)⟩) ?_)
  intro x y hxy
  have h := Subtype.ext_iff.mp hxy
  exact Subtype.ext (Subtype.ext h)

theorem card_inf_U_le {A : Subgroup G} (hAX : A ≤ X) (hA : IsElemAbelian 2 A) :
    Nat.card ↥(A ⊓ centerOf (c134Q X L)) ≤
      Nat.card (fixAll (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A))) := by
  refine Nat.card_le_card_of_injective (fun x => ⟨H.q0.κ ⟨x, x.2.2⟩, fun a =>
    H.q0.rep_κ_of_commute (hAX.trans H.normU) (le_normalizer_bot A) a ⟨x, x.2.2⟩
      (CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hA a.2 x.2.1)⟩) ?_
  intro x y hxy
  have h : Multiplicative.toAdd (βU ⟨x, x.2.2⟩) = Multiplicative.toAdd (βU ⟨y, y.2.2⟩) :=
    Subtype.ext_iff.mp hxy
  have h' := burnsideC135_βU_injective H.dsg (Multiplicative.toAdd.injective h)
  exact Subtype.ext (congrArg (fun z : ↥(centerOf (c134Q X L)) => (z : G)) h')

theorem card_inf_W_le {A : Subgroup G} (hAX : A ≤ X) (hA : IsElemAbelian 2 A) :
    Nat.card ↥(A ⊓ burnsideC135_Wc β 1) ≤
      Nat.card (fixAll (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A))) *
        Nat.card (fixAll (H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU))) := by
  have hle : A ⊓ burnsideC135_Wc β 1 ≤ burnsideC135_Wc β 1 := inf_le_right
  rw [← Subgroup.card_ker_mul_card_range (H.q1.hom.comp (Subgroup.inclusion hle))]
  refine Nat.mul_le_mul ((Nat.card_le_card_of_injective (fun x =>
    (⟨x.1.1, x.1.2.1, (H.q1.ker (Subgroup.inclusion hle x.1)).mp
      (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp x.2))⟩ :
        ↥(A ⊓ centerOf (c134Q X L)))) ?_).trans (H.card_inf_U_le hAX hA)) ?_
  · intro x y h
    have h' := Subtype.ext_iff.mp h
    exact Subtype.ext (Subtype.ext h')
  · refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      intro a
      rw [← hx]
      exact H.q1.rep_κ_of_commute _ _ a (Subgroup.inclusion hle x)
        (CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hA a.2 x.2.1)
    · intro x y h
      have h' := Subtype.ext_iff.mp h
      exact Subtype.ext (Multiplicative.toAdd.injective h')

end burnsideC135_H1

end CFSG.ASVolI

end
