module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421Setting
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19
public import CFSG.Quasithin.Background.B1Key
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15421

section Products

variable {Γ : Type*} [Group Γ]

theorem mem_iSup_of_odd {s : ℕ} {H D : Fin s → Subgroup Γ}
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) (hDH : ∀ i, D i ≤ H i)
    (hsq : ∀ i, ∀ h ∈ H i, h ^ 2 ∈ D i) {x : Γ} (hx : x ∈ ⨆ i, H i)
    (ho : Odd (orderOf x)) : x ∈ ⨆ i, D i := by
  classical
  have hc : Pairwise fun i j : Fin s => ∀ x y : Γ, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  have hcD : Pairwise fun i j : Fin s => ∀ x y : Γ, x ∈ D i → y ∈ D j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x (hDH i hx) y (hDH j hy)
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hc)] at hx
  obtain ⟨u, rfl⟩ := hx
  set x := Subgroup.noncommPiCoprod hc u with hxdef
  let v : ∀ i, D i := fun i => ⟨((u i : Γ)) ^ 2, hsq i _ (u i).2⟩
  have hsq' : x ^ 2 = Subgroup.noncommPiCoprod hcD v := by
    rw [hxdef, ← map_pow, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply]
    exact Finset.noncommProd_congr rfl (fun i _ => by simp [v]) _
  have hmem : x ^ 2 ∈ ⨆ i, D i := by
    rw [hsq', ← Subgroup.noncommPiCoprod_range (hcomm := hcD)]
    exact ⟨v, rfl⟩
  obtain ⟨m, hm⟩ := ho
  have e : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact Subgroup.pow_mem _ hmem _

theorem commute_of_mem_iSup {s : ℕ} {D : Fin s → Subgroup Γ}
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, a * b = b * a)
    (hab : ∀ i, ∀ a ∈ D i, ∀ b ∈ D i, a * b = b * a) {x y : Γ} (hx : x ∈ ⨆ i, D i)
    (hy : y ∈ ⨆ i, D i) : x * y = y * x := by
  classical
  have hc : Pairwise fun i j : Fin s => ∀ x y : Γ, x ∈ D i → y ∈ D j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hc)] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  funext i
  exact Subtype.ext (hab i _ (u i).2 _ (w i).2)

end Products

section Images

variable {G : Type*} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_commutator {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autI hV ⁅A, B⁆ = ⁅autI hV A, autI hV B⁆ := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : ⁅A, B⁆.subgroupOf N = ⁅A.subgroupOf N, B.subgroupOf N⁆ := by
    have e : ⁅A.subgroupOf N, B.subgroupOf N⁆.map N.subtype = ⁅A, B⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
        Subgroup.map_subgroupOf_eq_of_le hB]
    rw [← e]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  unfold autI
  rw [h1, Subgroup.map_commutator]

theorem autI_le_of_odd {K : Subgroup G} (hK : K = oTwoUpper K)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) {N : Subgroup (MulAut (IntMod V hV))}
    (h : ∀ x (hx : x ∈ K), Odd (orderOf x) → convI hV ⟨x, hKN hx⟩ ∈ N) : autI hV K ≤ N := by
  have key : ∀ x ∈ oTwoUpper K, ∀ hxN : x ∈ Subgroup.normalizer (V : Set G),
      convI hV ⟨x, hxN⟩ ∈ N := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun _ => h x hx.1 hx.2
    | one =>
      intro _
      have e : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (V : Set G)) = 1 := rfl
      rw [e, map_one]
      exact N.one_mem
    | mul x y hx hy ihx ihy =>
      intro _
      have hxN := hKN (oTwoUpper_le K hx)
      have hyN := hKN (oTwoUpper_le K hy)
      have e : (⟨x * y, Subgroup.mul_mem _ hxN hyN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
      rw [e, map_mul]
      exact N.mul_mem (ihx hxN) (ihy hyN)
    | inv x hx ih =>
      intro _
      have hxN := hKN (oTwoUpper_le K hx)
      have e : (⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨x, hxN⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact N.inv_mem (ih hxN)
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  exact key g (hK ▸ hg) g.2

end Images

section NoComponent

variable {W : Type} [CommGroup W] [Finite W]

private abbrev SL22 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

private theorem sl22_not_commute : ∀ a ∈ (Finset.univ : Finset SL22),
    ∀ b ∈ (Finset.univ : Finset SL22), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
      a * b ≠ b * a := by
  decide

private theorem card_sl22 : Nat.card SL22 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem exists_isFFStarMin_le {X A : Subgroup (MulAut W)} (hA : IsFFStarOffender X A) :
    ∃ B, IsFFStarMin X B ∧ B ≤ A := by
  have hAA : FFLe X A A := ⟨hA.isA2, hA.isA2, le_rfl, rfl⟩
  obtain ⟨B, ⟨hBP, hBA⟩, hmin⟩ := Set.exists_min_image
    {B : Subgroup (MulAut W) | IsFFStarOffender X B ∧ FFLe X B A} (fun B => Nat.card B)
    (Set.toFinite _) ⟨A, hA, hAA⟩
  refine ⟨B, ⟨hBP, fun C hC hCB => ?_⟩, hBA.2.2.1⟩
  have hCA : FFLe X C A := ⟨hCB.1, hBA.2.1, hCB.2.2.1.trans hBA.2.2.1, hCB.2.2.2.trans hBA.2.2.2⟩
  exact Subgroup.eq_of_le_of_card_ge hCB.2.2.1 (hmin C ⟨hC, hCA⟩)

theorem eq_bot_of_le_centralizer_fitting {X B : Subgroup (MulAut W)}
    (hO : CFSG.Open.pCore 2 ↥X = ⊥) (hnc : ∀ K : Subgroup ↥X, ¬ CFSG.IsComponent K)
    (hBX : B ≤ X) (hB : IsPGroup 2 B)
    (hBC : B ≤ Subgroup.centralizer ((fittingOfSub X : Subgroup (MulAut W)) : Set (MulAut W))) :
    B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup ↥X)) :=
    B1.fitting_card_odd ((CFSG.pCore_eq_open ↥X 2).trans hO)
  have hlayer : CFSG.layer ↥X = ⊥ := by
    rw [CFSG.layer, sSup_eq_bot]
    exact fun K hK => absurd hK (hnc K)
  have hC : Subgroup.centralizer (CFSG.fittingSubgroup ↥X : Set ↥X) ≤ CFSG.fittingSubgroup ↥X := by
    have h := CFSG.centralizer_generalizedFitting_le ↥X
    rwa [CFSG.generalizedFitting, hlayer, sup_bot_eq] at h
  set B' := B.subgroupOf X
  have hB'C : B' ≤ Subgroup.centralizer (CFSG.fittingSubgroup ↥X : Set ↥X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : (f : MulAut W) ∈ fittingOfSub X := ⟨f, hf, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hBC hb) _ hf')
  have hB'2 : IsPGroup 2 B' := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBX).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB'2
  have hdvd : 2 ^ k ∣ Nat.card (CFSG.fittingSubgroup ↥X) :=
    hk ▸ Subgroup.card_dvd_of_le (hB'C.trans hC)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.fittingSubgroup ↥X)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : Nat.card B' = 1 := by rw [hk]; exact Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hB'bot : B' = ⊥ := Subgroup.eq_bot_of_card_eq B' h1
  rw [← Subgroup.map_subgroupOf_eq_of_le hBX]
  change B'.map X.subtype = ⊥
  rw [hB'bot, Subgroup.map_bot]

theorem ffJ_eq_iSup_of_noComponent (hB19 : InputB19) (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hO : CFSG.Open.pCore 2 ↥X = ⊥) (hFF : IsFFModule X)
    (hnc : ∀ K : Subgroup ↥X, ¬ CFSG.IsComponent K) :
    ∃ (s : ℕ) (H : Fin s → Subgroup (MulAut W)),
      (∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) ∧
      (∀ i, oddCoreOfSub (H i) ≤ H i) ∧
      (∀ i, ∀ a ∈ oddCoreOfSub (H i), ∀ b ∈ oddCoreOfSub (H i), a * b = b * a) ∧
      (∀ i, ∀ h ∈ H i, h ^ 2 ∈ oddCoreOfSub (H i)) ∧ ffJ X = ⨆ i, H i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Pst : Set (Subgroup (MulAut W)) := {A | IsFFStarMin X A} with hPst
  have hnotC : ∀ B, IsFFStarMin X B → ⁅fittingOfSub X, B⁆ ≠ ⊥ := by
    intro B hB hbot
    have hBC : B ≤ Subgroup.centralizer
        ((fittingOfSub X : Subgroup (MulAut W)) : Set (MulAut W)) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    exact hB.1.2.1 (eq_bot_of_le_centralizer_fitting hO hnc hB.1.1
      (B6.isPGroup_two_of_isElemAbelian2 hB.1.2.2.1) hBC)
  obtain ⟨B₀, hB₀⟩ := (B1_7 hW hFF).1
  have hFne : ⁅fittingOfSub X, ffJP Pst X⁆ ≠ ⊥ := by
    intro hbot
    apply hnotC B₀ hB₀
    refine le_bot_iff.mp (hbot ▸ Subgroup.commutator_mono le_rfl ?_)
    exact le_iSup_of_le B₀ (le_iSup_of_le hB₀ (le_iSup_of_le hB₀.1.1 le_rfl))
  have hO' : pCoreOf 2 X = ⊥ := by
    change (CFSG.Open.pCore 2 ↥X).map X.subtype = ⊥
    rw [hO, Subgroup.map_bot]
  obtain ⟨s, H, h1, h1', h2, h2c, -, -, -, -, h4, -⟩ := hB19 W hW X hO' hFne
  set F := ⁅fittingOfSub X, ffJP Pst X⁆ with hF
  have hcardH : ∀ i, Nat.card ↥(H i) = 6 := fun i => by
    obtain ⟨e⟩ := (h1 i).2
    rw [Nat.card_congr e.toEquiv, card_sl22]
  have hDH : ∀ i, oddCoreOfSub (H i) ≤ H i := fun i => Subgroup.map_subtype_le _
  have hDF : ∀ i, oddCoreOfSub (H i) ≤ F := fun i =>
    h2.2.2 ▸ le_iSup (fun j => oddCoreOfSub (H j)) i
  have hW0 : ffJP {A | IsFFStarOffender X A}
      (X ⊓ Subgroup.centralizer ((F : Subgroup (MulAut W)) : Set (MulAut W))) = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun A => iSup_le fun hA => iSup_le fun hAC => ?_)
    exfalso
    obtain ⟨B, hB, hBA⟩ := exists_isFFStarMin_le hA
    obtain ⟨i, hi⟩ := (h4 B).mp ⟨hB, hnotC B hB⟩
    obtain ⟨e⟩ := (h1 i).2
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1.2.1
    have hb2 : b ^ 2 = 1 := hB.1.2.2.1.2 b hbB
    have hcard3 := h2c i
    obtain ⟨f, hf1⟩ : ∃ f : ↥(oddCoreOfSub (H i)), f ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Subsingleton ↥(oddCoreOfSub (H i)) := ⟨fun x y => (hcon x).trans (hcon y).symm⟩
      rw [Nat.card_unique] at hcard3
      omega
    have hf3 : f ^ 3 = 1 := by rw [← hcard3]; exact pow_card_eq_one'
    have hbf : b * f = f * b :=
      (Subgroup.mem_centralizer_iff.mp ((hAC.trans inf_le_right) (hBA hbB)) f (hDF i f.2)).symm
    have hbH : b ∈ H i := hi.1 hbB
    have hfH : (f : MulAut W) ∈ H i := hDH i f.2
    set b' : ↥(H i) := ⟨b, hbH⟩
    set f' : ↥(H i) := ⟨f, hfH⟩
    have hb'2 : e b' ^ 2 = 1 := by
      rw [← map_pow]
      have : b' ^ 2 = 1 := Subtype.ext hb2
      rw [this, map_one]
    have hb'1 : e b' ≠ 1 := by
      rw [Ne, map_eq_one_iff e e.injective]
      exact fun h => hb1 (Subtype.ext (congrArg Subtype.val h : b = 1))
    have hf'3 : e f' ^ 3 = 1 := by
      rw [← map_pow]
      have : f' ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hf3)
      rw [this, map_one]
    have hf'1 : e f' ≠ 1 := by
      rw [Ne, map_eq_one_iff e e.injective]
      intro h
      have h' : ((f' : ↥(H i)) : MulAut W) = 1 := by rw [h]; rfl
      exact hf1 (Subtype.ext h')
    apply sl22_not_commute _ (Finset.mem_univ _) _ (Finset.mem_univ _) hb'2 hb'1 hf'3 hf'1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbf
  refine ⟨s, H, ?_, hDH, ?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    exact h1'.1 (some i) (some j) (fun h => hij (Option.some_injective _ h)) a ha b hb
  · intro i a ha b hb
    have hc : IsCyclic ↥(oddCoreOfSub (H i)) := isCyclic_of_prime_card (h2c i)
    let _ : CommGroup ↥(oddCoreOfSub (H i)) := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(oddCoreOfSub (H i))) ⟨b, hb⟩)
  · intro i h hh
    have hcardD : Nat.card ↥(CFSG.oddCore ↥(H i)) = 3 := by
      rw [← h2c i, oddCoreOfSub, Subgroup.card_map_of_injective (H i).subtype_injective]
    have hidx : (CFSG.oddCore ↥(H i)).index = 2 := by
      have := (CFSG.oddCore ↥(H i)).card_mul_index
      rw [hcardD, hcardH i] at this
      omega
    exact ⟨_, Subgroup.sq_mem_of_index_two hidx ⟨h, hh⟩, rfl⟩
  · rw [← h1'.2.2, iSup_option]
    simp only [Option.elim]
    rw [hW0, bot_sup_eq]

end NoComponent

section OTwo

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_right_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : ⁅H, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHK hh) k).mp hk) (K.inv_mem hk)

theorem mem_normalizer_oTwoUpper {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    g ∈ Subgroup.normalizer (oTwoUpper N : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine mem_oTwoUpper_of_odd ((Subgroup.mem_normalizer_iff.mp hg y).mp hy.1) ?_
    rw [gold_orderOf_conj]
    exact hy.2
  | one => simp
  | mul y z _ _ ihy ihz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ih =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

theorem oTwoUpper_sup_eq {L Q : Subgroup G} (hL : L = oTwoUpper L) (hQ : IsPGroup 2 Q)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) : oTwoUpper (L ⊔ Q) = L := by
  refine le_antisymm ?_ (hL.le.trans (oTwoUpper_mono le_sup_left))
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_of_odd_of_mem_mul hQ hQL (sup_comm L Q ▸ hx) ho

theorem not_isPGroup_of_relIndex_eq_three {L : Subgroup G}
    (h3 : (pCoreOf 2 L).relIndex L = 3) : ¬ IsPGroup 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hL
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hL
  have hc := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
  rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L), h3, hk] at hc
  have h3k : 3 ∣ 2 ^ k := ⟨_, hc.symm⟩
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3k
  omega

end OTwo

section Setting

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

variable (s : Setting15419 G T)

omit [Finite G] in
theorem omegaOneCenter_le_T₀ :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter s.T₀ := by
  have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun z hz => hz.1
  have hET : omegaOneCenterOf (thompsonJ T) ≤ T :=
    ((B2F.omegaOneCenterOf_le_centerOf _).trans inf_le_left).trans (thompsonJ_le_self T)
  have hZS : quasithinOmegaOneCenter T ≤ baum T :=
    hZ.trans (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hET)))
  refine (Subgroup.closure_le _).mpr fun z hz => Subgroup.subset_closure ⟨⟨?_, ?_⟩, hz.2⟩
  · exact baum_le_T₀ s (hZS (Subgroup.subset_closure hz))
  · exact Subgroup.centralizer_le (T₀_le s) hz.1.2

omit [Finite G] in
theorem inf_centralizer_le (h8 : Stmt1548 G T) :
    s.I ⊓ Subgroup.centralizer (quasithinOmegaOneCenter s.T₀ : Set G) ≤ T :=
  inf_le_right.trans ((Subgroup.centralizer_le (omegaOneCenter_le_T₀ s)).trans h8.le)

theorem inf_centralizer_eq (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T)
    (hF : CharTwo s.I) (hT₀ : IsSylowTwoOf s.T₀ s.I) :
    s.I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter s.T₀) s.I : Set G) =
      pCoreOf 2 s.I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := conjClosure (quasithinOmegaOneCenter s.T₀) s.I with hVdef
  have hred := (conjClosure_isTwoReducedIn_of_charTwo hT₀ hF le_rfl).2.2
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 s.I)
    (pCoreOf_le_centralizer_of_isTwoReducedIn hred))
  have hCT : s.I ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
    (inf_le_inf_left _ (Subgroup.centralizer_le (le_conjClosure _ _))).trans
      (inf_centralizer_le s h8)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hyp.sylow.1.to_le hCT)
  exact B2F.le_normalizer_inf Subgroup.le_normalizer
    ((le_normalizer_conjClosure _ _).trans (B2F.normalizer_le_normalizer_centralizer V))

theorem thompsonJ_le_thompsonJ_I (hT₀ : IsSylowTwoOf s.T₀ s.I) :
    thompsonJ T ≤ thompsonJ s.I := by
  rw [thompsonJ_eq_of_le (thompsonJ_le_T₀ s) (T₀_le s)]
  exact thompsonJ_le_thompsonJ_of_isSylowTwoOf hT₀

theorem not_thompsonJ_le (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T)
    (hF : CharTwo s.I) (hT₀ : IsSylowTwoOf s.T₀ s.I) :
    ¬ thompsonJ s.I ≤
      Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter s.T₀) s.I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJ
  have hJI : thompsonJ T ≤ s.I := (thompsonJ_le_T₀ s).trans (le_sup_right.trans le_sup_left)
  have hJO : thompsonJ T ≤ pCoreOf 2 s.I := by
    rw [← inf_centralizer_eq s hyp h8 hF hT₀]
    exact le_inf hJI ((thompsonJ_le_thompsonJ_I s hT₀).trans hJ)
  have hLI : s.L₁ ≤ s.I := le_sup_left.trans le_sup_left
  have hL : s.L₁ ≤ pCoreOf 2 s.I := by
    rw [← (commutator_L₁ s)]
    exact (Subgroup.commutator_mono hLI hJO).trans
      (commutator_le_right_of_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  exact not_isPGroup_of_relIndex_eq_three (factor_L₁ s).relIndex_eq
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.I).to_le hL)

end Setting

end L15421

end CFSG.Quasithin.EmptyFaithfulMultiple
