module

public import CFSG.Quasithin.Background.E3ClosedTwo
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin
namespace E5

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def dFam (j : ℕ) (P : Subgroup G) : Set (Subgroup G) :=
  {D₁ | D₁ ≤ omegaOneCenterOf (H13.thompsonJk j P) ∧
    Nat.card ↥(omegaOneCenterOf (H13.thompsonJk j P)) ≤ 2 ^ j * Nat.card ↥D₁}

theorem thompsonJk_le (j : ℕ) (P : Subgroup G) : H13.thompsonJk j P ≤ P :=
  iSup₂_le fun _ hA => hA.1

theorem le_thompsonJk {j : ℕ} {P A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 2 A)
    (hcard : ∀ B : Subgroup G, B ≤ P → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ j * Nat.card A) :
    A ≤ H13.thompsonJk j P :=
  le_iSup₂_of_le (f := fun A (_ : A ≤ P ∧ IsElemAbelian 2 A ∧
      ∀ B : Subgroup G, B ≤ P → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ j * Nat.card A) => A)
    A ⟨hAP, hA, hcard⟩ le_rfl

theorem le_thompsonJk_of_isMaxElemAbelian {j : ℕ} {P A : Subgroup G}
    (hA : IsMaxElemAbelian P A) : A ≤ H13.thompsonJk j P :=
  le_thompsonJk hA.1 hA.2.1 fun B hBP hB =>
    (hA.2.2 B hBP hB).trans (Nat.le_mul_of_pos_left _ (by positivity))

theorem le_normalizer_thompsonJk (j : ℕ) (P : Subgroup G) :
    P ≤ Subgroup.normalizer (H13.thompsonJk j P : Set G) := by
  have key : ∀ g ∈ P, cjSub g (H13.thompsonJk j P) ≤ H13.thompsonJk j P := by
    intro g hg
    change (H13.thompsonJk j P).map (MulAut.conj g).toMonoidHom ≤ _
    unfold H13.thompsonJk
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    change cjSub g A ≤ _
    refine le_thompsonJk (cjSub_le (Subgroup.le_normalizer hg) hA.1) (isElemAbelian_cjSub hA.2.1)
      fun B hBP hB => ?_
    rw [card_cjSub]
    exact hA.2.2 B hBP hB
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ cjSub g (H13.thompsonJk j P) := by
      rw [mem_cjSub]; simpa [mul_assoc] using hx
    exact key g hg h1
  · intro hx
    have h1 : x ∈ cjSub g⁻¹ (H13.thompsonJk j P) := by
      rw [mem_cjSub]; simpa [mul_assoc] using hx
    exact key g⁻¹ (P.inv_mem hg) h1

theorem omegaOneCenterOf_le_of_isMaxElemAbelian [Finite G] {j : ℕ} {P A : Subgroup G}
    (hA : IsMaxElemAbelian P A) : omegaOneCenterOf (H13.thompsonJk j P) ≤ A := by
  set D := omegaOneCenterOf (H13.thompsonJk j P)
  have hAJ : A ≤ H13.thompsonJk j P := le_thompsonJk_of_isMaxElemAbelian hA
  have hcomm : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := fun d hd a ha =>
    (mem_centralizer_of_mem_omegaOneCenterOf hd (hAJ ha)).symm
  have hDA : IsElemAbelian 2 (D ⊔ A) :=
    B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_omegaOneCenterOf _) hA.2.1 hcomm
  have hDP : D ⊔ A ≤ P :=
    sup_le ((omegaOneCenterOf_le _).trans (thompsonJk_le j P)) hA.1
  have heq : A = D ⊔ A :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (hA.2.2 _ hDP hDA)
  rw [heq]
  exact le_sup_left

theorem le_omegaOneCenterOf_of_le_centralizer [Finite G] {j : ℕ} {P V : Subgroup G}
    (hVP : V ≤ P) (hV : IsElemAbelian 2 V)
    (hJ : H13.thompsonJk j P ≤ Subgroup.centralizer (V : Set G)) :
    V ≤ omegaOneCenterOf (H13.thompsonJk j P) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian P
  have hAJ : A ≤ H13.thompsonJk j P := le_thompsonJk_of_isMaxElemAbelian hA
  have hcomm : ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := fun v hv a ha =>
    (Subgroup.mem_centralizer_iff.1 (hJ (hAJ ha)) v hv)
  have hVA : IsElemAbelian 2 (V ⊔ A) := B2F.isElemAbelian_sup_of_commute hV hA.2.1 hcomm
  have hVJ : V ⊔ A ≤ H13.thompsonJk j P := by
    refine le_thompsonJk (sup_le hVP hA.1) hVA fun B hBP hB => ?_
    exact (hA.2.2 B hBP hB).trans ((Subgroup.card_le_of_le le_sup_right).trans
      (Nat.le_mul_of_pos_left _ (by positivity)))
  intro v hv
  refine mem_omegaOneCenterOf (hVJ (le_sup_left (a := V) hv)) (fun y hy => ?_) (hV.2 v hv)
  exact (Subgroup.mem_centralizer_iff.1 (hJ hy) v hv).symm

theorem isInvColl_maxElemAbelian (H : Subgroup G) :
    E1.IsInvColl H {A | IsMaxElemAbelian H A} where
  le A hA := hA.1
  isElemAbelian A hA := hA.2.1
  conj A hA h hh := by
    refine ⟨cjSub_le (Subgroup.le_normalizer hh) hA.1, isElemAbelian_cjSub hA.2.1,
      fun B hBH hB => ?_⟩
    show Nat.card B ≤ Nat.card (cjSub h A)
    rw [card_cjSub]
    exact hA.2.2 B hBH hB

theorem weakClosure_maxElemAbelian [Finite G] {H P : Subgroup G} (hP : IsSylowIn 2 P H) :
    E1.weakClosure P {A | IsMaxElemAbelian H A} = thompsonJ P := by
  unfold E1.weakClosure thompsonJ
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => iSup_le fun hAP => ?_
    exact le_iSup₂_of_le (f := fun A (_ : IsMaxElemAbelian P A) => A) A
      ⟨hAP, hA.2.1, fun B hBP hB => hA.2.2 B (hBP.trans hP.le) hB⟩ le_rfl
  · refine iSup₂_le fun A hA => ?_
    exact le_iSup₂_of_le A (isMaxElemAbelian_of_isSylowTwoOf hP hA) (le_iSup_of_le hA.1 le_rfl)

@[expose] def quotStab (Q W : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (W : Set G) ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ W}
  one_mem' := ⟨Subgroup.one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨Subgroup.mul_mem _ hxN hyN, fun q hq => ?_⟩
    have e : ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxN _).1 (hy q hq)) (hx q hq)
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨Subgroup.inv_mem _ hxN, fun q hq => ?_⟩
    have e : ⁅x⁻¹, q⁆ = x⁻¹ * (⁅x, q⁆)⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) _).1
      (Subgroup.inv_mem _ (hx q hq))

theorem mem_quotStab_iff {Q W : Subgroup G} {x : G} :
    x ∈ quotStab Q W ↔ x ∈ Subgroup.normalizer (W : Set G) ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ W := Iff.rfl

theorem mem_centralizer_of_odd [Finite G] {Q W : Subgroup G} (hWQ : W ≤ Q) (hQ : IsPGroup 2 Q)
    {x : G} (hxW : x ∈ Subgroup.centralizer (W : Set G)) (hxS : x ∈ quotStab Q W)
    (hodd : Odd (orderOf x)) : x ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  set w := ⁅x, q⁆ with hw
  have hwW : w ∈ W := hxS.2 q hq
  have hxw : x * w = w * x := (Subgroup.mem_centralizer_iff.1 hxW w hwW).symm
  have hstep : x * q * x⁻¹ = w * q := by
    rw [hw, commutatorElement_def]; group
  have hpow : ∀ n : ℕ, x ^ n * q * (x ^ n)⁻¹ = w ^ n * q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxwn : x * w ^ n = w ^ n * x := (Commute.pow_right hxw n).eq
      calc x ^ (n + 1) * q * (x ^ (n + 1))⁻¹ = x * (x ^ n * q * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * (w ^ n * q) * x⁻¹ := by rw [ih]
        _ = w ^ n * (x * q * x⁻¹) := by
          rw [← mul_assoc x, hxwn]; group
        _ = w ^ (n + 1) * q := by rw [hstep]; group
  have h1 : w ^ orderOf x = 1 := by
    have := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.1 this.symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨w, hWQ hwW⟩
  have hdvd : orderOf w ∣ orderOf x := orderOf_dvd_of_pow_eq_one h1
  have hw1 : orderOf w = 1 := by
    rw [← Subgroup.orderOf_mk w (hWQ hwW), ha] at hdvd ⊢
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)) hdvd
  have hw1' : w = 1 := orderOf_eq_one_iff.1 hw1
  rw [hw1', one_mul] at hstep
  calc q * x = x * q * x⁻¹ * x := by rw [hstep]
    _ = x * q := by group

theorem mem_normalizer_centralizer {g : G} {W : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) w).1 hw
    have := hx _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * w := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hw' : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hg w).1 hw
    have := hx _ hw'
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [this]
      _ = x * w := by group

@[expose] def wFam (j : ℕ) (P Q : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ Q ∧ IsElemAbelian 2 B ∧ ∀ B' : Subgroup G, B' ≤ P → IsElemAbelian 2 B' →
    Nat.card B' ≤ 2 ^ j * Nat.card B}

@[expose] def wGen (j : ℕ) (P Q : Subgroup G) : Subgroup G := ⨆ B ∈ wFam j P Q, B

theorem le_wGen {j : ℕ} {P Q B : Subgroup G} (hB : B ∈ wFam j P Q) : B ≤ wGen j P Q :=
  le_iSup₂_of_le (f := fun B (_ : B ∈ wFam j P Q) => B) B hB le_rfl

theorem wGen_le (j : ℕ) (P Q : Subgroup G) : wGen j P Q ≤ Q :=
  iSup₂_le fun _ hB => hB.1

theorem wGen_le_thompsonJk {j : ℕ} {P Q : Subgroup G} (hQP : Q ≤ P) :
    wGen j P Q ≤ H13.thompsonJk j P :=
  iSup₂_le fun _ hB => le_thompsonJk (hB.1.trans hQP) hB.2.1 hB.2.2

theorem le_normalizer_wGen (j : ℕ) {P Q K : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) :
    K ≤ Subgroup.normalizer (wGen j P Q : Set G) := by
  have key : ∀ g ∈ K, cjSub g (wGen j P Q) ≤ wGen j P Q := by
    intro g hg
    change (wGen j P Q).map (MulAut.conj g).toMonoidHom ≤ _
    unfold wGen
    rw [Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB => ?_
    change cjSub g B ≤ _
    refine le_wGen ⟨cjSub_le (hKQ hg) hB.1, isElemAbelian_cjSub hB.2.1, fun B' hB'P hB' => ?_⟩
    rw [card_cjSub]
    exact hB.2.2 B' hB'P hB'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ cjSub g (wGen j P Q) := by
      rw [mem_cjSub]; simpa [mul_assoc] using hx
    exact key g hg h1
  · intro hx
    have h1 : x ∈ cjSub g⁻¹ (wGen j P Q) := by
      rw [mem_cjSub]; simpa [mul_assoc] using hx
    exact key g⁻¹ (K.inv_mem hg) h1

theorem mem_normalizer_of_cjSub_eq {g : G} {X : Subgroup G} (h : cjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ cjSub g X := by rw [mem_cjSub]; simpa [mul_assoc] using hx
    rwa [h] at h1
  · intro hx
    rw [← h, mem_cjSub] at hx
    simpa [mul_assoc] using hx

theorem le_normalizer_thompsonJ (S : Subgroup G) :
    S ≤ Subgroup.normalizer (thompsonJ S : Set G) := fun _ hg =>
  mem_normalizer_of_cjSub_eq (cjSub_thompsonJ (Subgroup.le_normalizer hg))

section Dichotomy

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem perfectCore_le_twoResidual (H : Subgroup Γ) : perfectCore H ≤ twoResidual H := by
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup Γ) ≤ H) IsPGroup.of_bot
  refine perfectCore_le_of_sup_solvable (twoResidual_le H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le H)).2
      (le_normalizer_twoResidual H)) ?_ (E1.isSolvable_of_isPGroup_two hT.2.1)
  rw [sup_comm]
  exact (sup_twoResidual_eq hT).symm

theorem exists_pow_mem_of_mem_sup_pCore {C : Subgroup Γ} [C.Normal] {y : Γ}
    (hy : y ∈ C ⊔ CFSG.Open.pCore 2 Γ) : ∃ l : ℕ, y ^ 2 ^ l ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' C
  have hQ : IsPGroup 2 ↥((CFSG.Open.pCore 2 Γ).map π) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).map π
  have hmap : (C ⊔ CFSG.Open.pCore 2 Γ).map π = (CFSG.Open.pCore 2 Γ).map π := by
    rw [Subgroup.map_sup]
    have : C.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  have hy' : π y ∈ (CFSG.Open.pCore 2 Γ).map π := hmap ▸ Subgroup.mem_map_of_mem π hy
  obtain ⟨l, hl⟩ := hQ ⟨π y, hy'⟩
  refine ⟨l, ?_⟩
  have h1 : π (y ^ 2 ^ l) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hl
  rwa [← QuotientGroup.ker_mk' C, MonoidHom.mem_ker]

theorem dichotomy {S B D X : Subgroup Γ} (hE : E1.EOne Γ B ∨ E1.ETwo Γ S B) (hDB : D ≤ B)
    (hD2 : IsPGroup 2 D) [hXn : X.Normal] (hDX : D ≤ X)
    (hX : twoResidual X ≤ Subgroup.centralizer (CFSG.Open.pCore 2 Γ : Set Γ)) :
    twoResidual (⊤ : Subgroup Γ) ≤ Subgroup.centralizer (CFSG.Open.pCore 2 Γ : Set Γ) ∨
      D ≤ CFSG.Open.pCore 2 Γ := by
  set Q := CFSG.Open.pCore 2 Γ with hQdef
  set C := Subgroup.centralizer (Q : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  rcases hE with hE | hE
  ·
    obtain ⟨p, hp, hp2, h22, -, hPB, hB2⟩ := hE
    have : Fact p.Prime := ⟨hp⟩
    set π := QuotientGroup.mk' Q with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
    have hDb : D.map π ≤ E1.barO2 Γ B := Subgroup.map_mono hDB
    have hdvd : Nat.card (D.map π) ∣ 2 := hB2 ▸ Subgroup.card_dvd_of_le hDb
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · right
      have hbot : D.map π = ⊥ := Subgroup.card_eq_one.1 h1
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    · left
      have hDeq : D.map π = E1.barO2 Γ B :=
        Subgroup.eq_of_le_of_card_ge hDb (by rw [hB2, h2])
      set Pb := CFSG.Open.pCore p (Γ ⧸ Q) with hPb
      set Xb := X.map π with hXb
      have hXbn : Xb.Normal := Subgroup.Normal.map hXn π hπs
      have hBX : E1.barO2 Γ B ≤ Xb := hDeq ▸ Subgroup.map_mono hDX
      have hPX : Pb ≤ Xb := by
        calc Pb = ⁅Pb, E1.barO2 Γ B⁆ := hPB
          _ ≤ ⁅Pb, Xb⁆ := Subgroup.commutator_mono le_rfl hBX
          _ ≤ Xb := Subgroup.commutator_le_right Pb Xb
      have hPres : Pb ≤ twoResidual Xb := by
        intro x hx
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient Xb x (hPX hx)
        obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p) ⟨x, hx⟩
        have ha' : x ^ p ^ a ∈ twoResidual Xb := by
          have : x ^ p ^ a = 1 := congrArg Subtype.val ha
          rw [this]
          exact Subgroup.one_mem _
        refine E1.mem_of_pow_mem_of_coprime ?_ ha' hk
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have hPC : Pb ≤ C.map π := by
        calc Pb ≤ twoResidual Xb := hPres
          _ = (twoResidual X).map π := (E1.map_twoResidual π X).symm
          _ ≤ C.map π := Subgroup.map_mono hX
      have hcomap : E1.oTwoP Γ p ≤ C ⊔ Q := by
        have h1 : E1.oTwoP Γ p = Pb.comap π := rfl
        rw [h1]
        calc Pb.comap π ≤ (C.map π).comap π := Subgroup.comap_mono hPC
          _ = C ⊔ Q := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      refine twoResidual_le_of_isTwoQuotient le_top
        (fun g _ => (Subgroup.normalizer_eq_top_iff.2 hCn) ▸ Subgroup.mem_top g) ?_
      intro y _
      obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP Γ p) (fun q => by
          have hq : q ∈ E1.oTwoPTwo Γ p := by rw [h22]; exact Subgroup.mem_top q
          exact hq) y
      obtain ⟨l, hl⟩ := exists_pow_mem_of_mem_sup_pCore (hcomap hk)
      refine ⟨k + l, ?_⟩
      rwa [pow_add, pow_mul]
  ·
    obtain ⟨h2c, h2top, hres, L, hL, hlayer, -⟩ := hE
    set R := CFSG.solvableRadical Γ with hRdef
    set π := QuotientGroup.mk' R with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
    have hrad : CFSG.solvableRadical (Γ ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot Γ
    set Xb := X.map π with hXb
    have hXbn : Xb.Normal := Subgroup.Normal.map hXn π hπs
    by_cases hX1 : Xb = ⊥
    · right
      have hXR : X ≤ R := by
        rwa [hXb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hX1
      have h1 := E3.inf_solvableRadical_eq_inf_pCore h2c hD2
      intro d hd
      have hd' : d ∈ R ⊓ D := ⟨hXR (hDX hd), hd⟩
      rw [h1] at hd'
      exact hd'.1
    · left
      obtain ⟨K, hK, hKX⟩ := E3.exists_component_le_of_normal hrad hX1
      have hKL : ∃ t ∈ (E1.tauOf ⊤ S B).map π, K = A1b.conjSub t L := by
        by_contra hno
        push Not at hno
        have hle : CFSG.layer (Γ ⧸ R) ≤ Subgroup.centralizer (K : Set (Γ ⧸ R)) := by
          rw [hlayer]
          refine iSup₂_le fun t ht => ?_
          have hcL : CFSG.IsComponent (A1b.conjSub t L) :=
            CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL
          have := (CFSG.LocalCores.distinct_components_commute hK hcL).resolve_left (hno t ht)
          rw [Subgroup.commutator_comm] at this
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
        have hKc : K ≤ Subgroup.centralizer (K : Set (Γ ⧸ R)) :=
          (CFSG.LocalCores.component_le_layer hK).trans hle
        have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
          (Subgroup.mem_centralizer_iff.1 (hKc ha) b hb).symm
        exact E3.component_not_isSolvable hK
          (Group.isSolvable_of_comm fun a b => Subtype.ext (hab a a.2 b b.2))
      obtain ⟨t, -, hKt⟩ := hKL
      have hlay : CFSG.layer (Γ ⧸ R) ≤ Xb := by
        rw [hlayer]
        refine iSup₂_le fun t' _ => ?_
        have e : A1b.conjSub t' L = A1b.conjSub (t' * t⁻¹) K := by
          rw [hKt, ← A1b.conjSub_mul, inv_mul_cancel_right]
        rw [e]
        intro x hx
        rw [A1b.mem_conjSub_iff] at hx
        have := hXbn.conj_mem _ (hKX hx) (t' * t⁻¹)
        simpa [mul_assoc] using this
      have hlay2 : CFSG.layer (Γ ⧸ R) ≤ C.map π := by
        calc CFSG.layer (Γ ⧸ R) ≤ perfectCore Xb :=
              le_perfectCore_of_perfect hlay CFSG.LocalCores.layer_perfect
          _ ≤ twoResidual Xb := perfectCore_le_twoResidual Xb
          _ = (twoResidual X).map π := (E1.map_twoResidual π X).symm
          _ ≤ C.map π := Subgroup.map_mono hX
      have hR : twoResidual (⊤ : Subgroup Γ) ≤ C ⊔ R := by
        refine (twoResidual_le_of_isTwoQuotient le_top
          (fun g _ => (Subgroup.normalizer_eq_top_iff.2 (E1.instNormalOInftyE Γ)) ▸
            Subgroup.mem_top g)
          (fun y _ => E1.exists_pow_mem_of_mem_pCore (M := oInftyE Γ)
            (fun q => by rw [h2top]; exact Subgroup.mem_top _) y)).trans ?_
        have h1 : oInftyE Γ = (CFSG.layer (Γ ⧸ R)).comap π := rfl
        rw [h1]
        calc (CFSG.layer (Γ ⧸ R)).comap π ≤ (C.map π).comap π := Subgroup.comap_mono hlay2
          _ = C ⊔ R := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
      rw [hres] at hR ⊢
      calc perfectCore (⊤ : Subgroup Γ) = perfectCore (perfectCore (⊤ : Subgroup Γ)) :=
            (perfectCore_eq_self_of_perfect (perfectCore_perfect _)).symm
        _ ≤ perfectCore (C ⊔ R) := perfectCore_mono hR
        _ ≤ C := perfectCore_le_of_sup_solvable le_sup_left
            ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
              (le_top.trans (Subgroup.normalizer_eq_top_iff.2 hCn).ge)) rfl hRs

end Dichotomy

section Core

variable [Finite G]

theorem twoResidual_le_iSup {j : ℕ} {H P A K : Subgroup G} (hP : IsSylowIn 2 P H)
    (hA : IsMaxElemAbelian H A) (hAP : A ≤ P) (hK : E1.IsE j H P A K) :
    twoResidual K ≤ ⨆ D₁ ∈ dFam j P, H ⊓ Subgroup.centralizer (D₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 K with hQdef
  set D := omegaOneCenterOf (H13.thompsonJk j P) with hDdef
  set A₁ := A ⊓ Q with hA₁def
  set Φ := ⨆ D₁ ∈ dFam j P, H ⊓ Subgroup.centralizer (D₁ : Set G) with hΦ
  have hAmax : IsMaxElemAbelian P A :=
    ⟨hAP, hA.2.1, fun B hBP hB => hA.2.2 B (hBP.trans hP.le) hB⟩
  obtain ⟨hAK, hAcard⟩ := E3.card_le_of_isE hP hAP hA.2.1 hK
  have hKH : K ≤ H := hK.1
  have hDA : D ≤ A := omegaOneCenterOf_le_of_isMaxElemAbelian hAmax
  have hDK : D ≤ K := hDA.trans hAK
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hPK : IsSylowIn 2 (P ⊓ K) K := hK.2.2.1
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQP : Q ≤ P := (hPK.le_of_normal hQK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQK).2 hKQ) hQ2).trans inf_le_left
  have hcardA : ∀ B : Subgroup G, B ≤ P → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A :=
    fun B hBP hB => hA.2.2 B (hBP.trans hP.le) hB
  have hA₁ : A₁ ∈ wFam j P Q := ⟨inf_le_right, B2F.isElemAbelian_mono inf_le_left hA.2.1,
    fun B hBP hB => (hcardA B hBP hB).trans hAcard⟩
  set W := wGen j P Q with hWdef
  have hA₁W : A₁ ≤ W := le_wGen hA₁
  have hWQ : W ≤ Q := wGen_le j P Q
  have hWJ : W ≤ H13.thompsonJk j P := wGen_le_thompsonJk hQP
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_wGen j hKQ
  have hDW : D ≤ Subgroup.centralizer (W : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw)
  set X := K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W with hXdef
  have hXK : X ≤ K := inf_le_left.trans inf_le_left
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
      intro k hk x ⟨⟨hxK, hxC⟩, hxN, hxS⟩
      refine ⟨⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1
          (mem_normalizer_centralizer (hKW hk)) x).1 hxC
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKW hk) hxN) (Subgroup.inv_mem _ (hKW hk))
      · intro q hq
        have hq' : k⁻¹ * q * k⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (hKQ (K.inv_mem hk)) q).1 hq
        have e : ⁅k * x * k⁻¹, q⁆ = k * ⁅x, k⁻¹ * q * k⁻¹⁻¹⁆ * k⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hKW hk) _).1 (hxS _ hq')
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hDX : D ≤ X := by
    intro d hd
    refine ⟨⟨hDK hd, hDW hd⟩, hKW (hDK hd), fun q hq => ?_⟩
    have hQD : q ∈ Subgroup.normalizer (D : Set G) :=
      normalizer_le_normalizer_omegaOneCenterOf _ (le_normalizer_thompsonJk j P (hQP hq))
    have h1 : ⁅d, q⁆ ∈ D := by
      have : q * d⁻¹ * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hQD _).1 (D.inv_mem hd)
      have e : ⁅d, q⁆ = d * (q * d⁻¹ * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem hd this
    have h2 : ⁅d, q⁆ ∈ Q := by
      have : d * q * d⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hKQ (hDK hd)) q).1 hq
      have e : ⁅d, q⁆ = (d * q * d⁻¹) * q⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Q.mul_mem this (Q.inv_mem hq)
    exact hA₁W ⟨hDA h1, h2⟩
  have hXres : twoResidual X ≤ Subgroup.centralizer (Q : Set G) := by
    have hle : twoResidual X ≤ X ⊓ Subgroup.centralizer (Q : Set G) := by
      refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have hxN : x ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hx
        have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
          mem_normalizer_centralizer (hKQ (hXK hx))
        constructor
        · rintro ⟨hy1, hy2⟩
          exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hy1,
            (Subgroup.mem_normalizer_iff.1 hxC y).1 hy2⟩
        · rintro ⟨hy1, hy2⟩
          exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).2 hy1,
            (Subgroup.mem_normalizer_iff.1 hxC y).2 hy2⟩
      · intro y hy
        obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
        refine ⟨k, X.pow_mem hy _, ?_⟩
        have hord : orderOf (y ^ 2 ^ k) = m := by
          rw [orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
            Nat.mul_div_cancel_left _ (by positivity)]
        have hyX := X.pow_mem hy (2 ^ k)
        exact mem_centralizer_of_odd hWQ hQ2 hyX.1.2 hyX.2 (hord ▸ hm)
    exact hle.trans inf_le_right
  have hdich : twoResidual K ≤ Subgroup.centralizer (Q : Set G) ∨ D ≤ Q := by
    have hXn : (X.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2 hKX
    have hE : E1.EOne ↥K (A.subgroupOf K) ∨ E1.ETwo ↥K ((P ⊓ K).subgroupOf K) (A.subgroupOf K) := by
      rcases hK.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hD2 : IsPGroup 2 (D.subgroupOf K) :=
      (B2F.isPGroup_of_isElemAbelian hDel).of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
    have hXK' : twoResidual (X.subgroupOf K) ≤
        Subgroup.centralizer (CFSG.Open.pCore 2 ↥K : Set ↥K) := by
      intro y hy
      have hy' : (y : G) ∈ twoResidual X := by
        have h1 : (twoResidual (X.subgroupOf K)).map K.subtype = twoResidual X := by
          rw [E1.map_twoResidual, Subgroup.map_subgroupOf_eq_of_le hXK]
        rw [← h1]
        exact Subgroup.mem_map_of_mem _ hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzQ : (z : G) ∈ Q := Subgroup.mem_map_of_mem K.subtype hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hXres hy') _ hzQ)
    rcases dichotomy hE (Subgroup.subgroupOf_mono K hDA) hD2 (hXn := hXn)
      (Subgroup.subgroupOf_mono K hDX) hXK' with h | h
    · left
      rw [E1.twoResidual_eq_map_top K]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (h hy) z hz)
    · right
      intro d hd
      have := h (show (⟨d, hDK hd⟩ : ↥K) ∈ D.subgroupOf K from hd)
      exact ⟨_, this, rfl⟩
  rcases hdich with h1 | h2
  ·
    have hrel : Q.relIndex A ≤ 2 ^ j := by
      have h1 := Subgroup.relIndex_mul_card Q A
      have hQA : Q ⊓ A = A ⊓ Q := inf_comm Q A
      have h2 : Q.relIndex A * Nat.card ↥(Q ⊓ A) ≤ 2 ^ j * Nat.card ↥(Q ⊓ A) := by
        rw [h1, hQA]; exact hAcard
      exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
    have hD₁ : D ⊓ Q ∈ dFam j P := by
      refine ⟨inf_le_left, ?_⟩
      have h3 := Subgroup.relIndex_mul_card Q D
      have h4 : Q.relIndex D ≤ Q.relIndex A :=
        Subgroup.relIndex_le_of_le_right hDA (E3.relIndex_ne_zero' _ _)
      calc Nat.card ↥D = Q.relIndex D * Nat.card ↥(Q ⊓ D) := h3.symm
        _ ≤ 2 ^ j * Nat.card ↥(D ⊓ Q) := by
          rw [inf_comm]; exact Nat.mul_le_mul_right _ (h4.trans hrel)
    refine le_iSup₂_of_le (f := fun D₁ (_ : D₁ ∈ dFam j P) =>
      H ⊓ Subgroup.centralizer (D₁ : Set G)) (D ⊓ Q) hD₁ ?_
    exact le_inf ((twoResidual_le K).trans hKH)
      (h1.trans (Subgroup.centralizer_le (fun x hx => hx.2)))
  ·
    have hDW' : D ≤ W := fun d hd => hA₁W ⟨hDA hd, h2 hd⟩
    set E := omegaOneCenterOf W with hEdef
    have hDE : D ≤ E := fun d hd =>
      mem_omegaOneCenterOf (hDW' hd)
        (fun w hw => (Subgroup.mem_centralizer_iff.1 (hDW hd) w hw)) (hDel.2 d hd)
    have hKE : K ≤ Subgroup.normalizer (E : Set G) :=
      hKW.trans (normalizer_le_normalizer_omegaOneCenterOf W)
    have hEel : IsElemAbelian 2 E := B2F.isElemAbelian_omegaOneCenterOf W
    have hEA₁ : IsElemAbelian 2 (E ⊔ A₁) :=
      B2F.isElemAbelian_sup_of_commute hEel hA₁.2.1 fun e he a ha =>
        (mem_centralizer_of_mem_omegaOneCenterOf he (hA₁W ha)).symm
    have hEA₁H : E ⊔ A₁ ≤ H :=
      sup_le (((omegaOneCenterOf_le W).trans hWQ).trans (hQP.trans hP.le))
        (inf_le_left.trans (hAP.trans hP.le))
    have hrelE : A₁.relIndex E ≤ 2 ^ j := by
      have h3 := Subgroup.relIndex_mul_card A₁ (E ⊔ A₁)
      have e : A₁ ⊓ (E ⊔ A₁) = A₁ := inf_eq_left.2 le_sup_right
      rw [e] at h3
      have h4 : A₁.relIndex (E ⊔ A₁) * Nat.card ↥A₁ ≤ 2 ^ j * Nat.card ↥A₁ := by
        rw [h3]; exact (hA.2.2 _ hEA₁H hEA₁).trans hAcard
      exact (Subgroup.relIndex_le_of_le_right le_sup_left (E3.relIndex_ne_zero' _ _)).trans
        (Nat.le_of_mul_le_mul_right h4 Nat.card_pos)
    have hconjE : ∀ k ∈ K, cjSub k E = E := fun k hk =>
      Subgroup.eq_of_le_of_card_ge (cjSub_le (hKE hk) le_rfl) (by rw [card_cjSub])
    have hgen : ∀ k ∈ K, cjSub k A ≤ Φ := by
      intro k hk
      have hD₁ : D ⊓ cjSub k A₁ ∈ dFam j P := by
        refine ⟨inf_le_left, ?_⟩
        have h5 : (cjSub k A₁).relIndex E = A₁.relIndex E := by
          conv_lhs => rw [← hconjE k hk]
          exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective
        have h6 : (cjSub k A₁).relIndex D ≤ (cjSub k A₁).relIndex E :=
          Subgroup.relIndex_le_of_le_right hDE (E3.relIndex_ne_zero' _ _)
        have h7 := Subgroup.relIndex_mul_card (cjSub k A₁) D
        calc Nat.card ↥D = (cjSub k A₁).relIndex D * Nat.card ↥(cjSub k A₁ ⊓ D) := h7.symm
          _ ≤ 2 ^ j * Nat.card ↥(D ⊓ cjSub k A₁) := by
            rw [inf_comm]; exact Nat.mul_le_mul_right _ (h6.trans (h5 ▸ hrelE))
      refine le_iSup₂_of_le (f := fun D₁ (_ : D₁ ∈ dFam j P) =>
        H ⊓ Subgroup.centralizer (D₁ : Set G)) (D ⊓ cjSub k A₁) hD₁ ?_
      refine le_inf ((cjSub_le (Subgroup.le_normalizer hk) hAK).trans hKH) ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy2 : y ∈ cjSub k A₁ := (Subgroup.mem_inf.1 hy).2
      rw [mem_cjSub] at hx hy2
      have hc : (k⁻¹ * y * k) * (k⁻¹ * x * k) = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
        have := hA.2.1.1
        exact setLike_mul_comm (Subgroup.mem_inf.1 hy2).1 hx
      have e1 : y * x = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      have e2 : x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      rw [e1, e2, hc]
    calc twoResidual K ≤ conjClosure A K := E1.twoResidual_le_conjClosure ⟨j, hK⟩
      _ ≤ Φ := conjClosure_le fun k hk a ha =>
          hgen k hk (by rw [mem_cjSub]; simpa [mul_assoc] using ha)

theorem e5_2_centralizer {j : ℕ} {H P : Subgroup G} (hP : IsSylowIn 2 P H) (hH : E1.InE j H) :
    (H ⊓ Subgroup.normalizer (thompsonJ P : Set G)) ⊔
      (⨆ D₁ ∈ dFam j P, H ⊓ Subgroup.centralizer (D₁ : Set G)) = H := by
  refine le_antisymm (sup_le inf_le_left (iSup₂_le fun _ _ => inf_le_left)) ?_
  have hEF := (E1.inE_iff_inEFor hP).1 hH _ (isInvColl_maxElemAbelian H)
  rw [weakClosure_maxElemAbelian hP] at hEF
  calc H = E1.eGen j H P {A | IsMaxElemAbelian H A} ⊔
        (H ⊓ Subgroup.normalizer (thompsonJ P : Set G)) := hEF.symm
    _ ≤ _ := by
      refine sup_le ?_ le_sup_left
      refine iSup₂_le fun A hA => iSup_le fun hAP => iSup₂_le fun K hK => ?_
      have hKeq : (P ⊓ K) ⊔ twoResidual K = K := sup_twoResidual_eq hK.2.2.1
      rw [← hKeq]
      refine sup_le ?_ ((twoResidual_le_iSup hP hA hAP hK).trans le_sup_right)
      exact le_sup_of_le_left (le_inf (inf_le_right.trans hK.1)
        (inf_le_left.trans (le_normalizer_thompsonJ P)))

end Core

end E5
end CFSG.Quasithin
