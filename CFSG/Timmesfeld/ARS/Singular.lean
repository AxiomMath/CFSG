module

public import CFSG.Timmesfeld.ARS.Sec8Regular
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Timmesfeld.ARS.Sec3Plane

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def pts (R : Set (Subgroup G)) (T : Subgroup G) : Set (Subgroup G) :=
  {P | P ∈ R ∧ P ≤ T}

@[expose] def normSet (R : Set (Subgroup G)) (T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ R ∧ ∀ x ∈ X, conjSub T x = T}

namespace Singular

theorem card_pts_mul [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {U : Subgroup G}
    (hU : CoveredBy R U) {A : Subgroup G} (hA : A ∈ R) :
    Nat.card (pts R U) * (Nat.card A - 1) = Nat.card U - 1 := by
  classical
  let f : (Σ D : pts R U, {x : G // x ∈ D.1 ∧ x ≠ 1}) → {x : G // x ∈ U ∧ x ≠ 1} :=
    fun p => ⟨p.2.1, p.1.2.2 p.2.2.1, p.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨D, x, hx, hx1⟩ ⟨D', x', hx', hx'1⟩ h
      have hxx : x = x' := congrArg Subtype.val h
      subst hxx
      have hDD : D = D' :=
        Subtype.ext (Sec3.eq_of_mem_of_mem hR hiso D.2.1 D'.2.1 hx hx' hx1)
      subst hDD
      rfl
    · rintro ⟨x, hx, hx1⟩
      obtain ⟨T, hT, hTU, hxT⟩ := hU x hx hx1
      exact ⟨⟨⟨T, hT, hTU⟩, x, hxT, hx1⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  have : Fintype (pts R U) := Fintype.ofFinite _
  rw [Nat.card_sigma, Plane.card_subtype_mem_ne_one] at hcard
  rw [← hcard]
  calc Nat.card (pts R U) * (Nat.card A - 1) = ∑ _D : pts R U, (Nat.card A - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    _ = ∑ D : pts R U, Nat.card {x : G // x ∈ D.1 ∧ x ≠ 1} :=
        Finset.sum_congr rfl fun D _ => by
          rw [Plane.card_subtype_mem_ne_one, hR.card_eq D.2.1 hA]

variable (h : Hyp G R) {S : Set (Subgroup G)} (hS : S ⊆ R)
  (hcol : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P)
include h hS hcol

omit h hS in
theorem gen_le_M_of_mem {E : Subgroup G} (hE : E ∈ S) : gen S ≤ M R E :=
  gen_le fun B hB => by
    by_cases hBE : B = E
    · rw [hBE]; exact QD.le_M_self
    · exact QD.le_M (hcol E hE B hB (Ne.symm hBE))

theorem mem_insert_lambdaSet_of_mem {E P : Subgroup G} (hE : E ∈ S) (hP : P ∈ pts R (gen S)) :
    P ∈ insert E (lambdaSet R E) := by
  have hset := (Q_eq_M h (hS hE)).2.1
  have hmem : P ∈ {B | B ∈ R ∧ B ≤ M R E} := ⟨hP.1, hP.2.trans (gen_le_M_of_mem hcol hE)⟩
  rwa [hset] at hmem

theorem gen_le_M {P : Subgroup G} (hP : P ∈ pts R (gen S)) : gen S ≤ M R P :=
  gen_le fun E hE => by
    rcases mem_insert_lambdaSet_of_mem h hS hcol hE hP with rfl | hPE
    · exact QD.le_M_self
    · exact QD.le_M (mem_lambdaSet_comm (hS hE) hPE)

theorem mem_lambdaSet {P Q : Subgroup G} (hP : P ∈ pts R (gen S)) (hQ : Q ∈ pts R (gen S))
    (hPQ : P ≠ Q) : Q ∈ lambdaSet R P := by
  have hset := (Q_eq_M h hP.1).2.1
  have hmem : Q ∈ {B | B ∈ R ∧ B ≤ M R P} := ⟨hQ.1, hQ.2.trans (gen_le_M h hS hcol hP)⟩
  rw [hset] at hmem
  rcases hmem with rfl | hmem
  · exact absurd rfl hPQ
  · exact hmem

theorem commuting_gen : Commuting (gen S) (gen S) :=
  commuting_gen_of_pairwise fun B hB C hC => by
    by_cases hBC : B = C
    · rw [hBC]; exact h.root.commuting_self (hS hC)
    · exact (hcol B hB C hC hBC).1.2.2

theorem coveredBy_gen : CoveredBy R (gen S) := by
  have := h.finite
  have hiso := h.noIsolated
  intro x hx hx1
  let U : Subgroup G :=
    { carrier := {y | y = 1 ∨ ∃ P ∈ pts R (gen S), y ∈ P}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | ⟨P, hP, ha⟩) (rfl | ⟨Q, hQ, hb⟩)
        · exact Or.inl (one_mul 1)
        · exact Or.inr ⟨Q, hQ, by rwa [one_mul]⟩
        · exact Or.inr ⟨P, hP, by rwa [mul_one]⟩
        · by_cases hPQ : P = Q
          · subst hPQ
            exact Or.inr ⟨P, hP, P.mul_mem ha hb⟩
          by_cases hab : a * b = 1
          · exact Or.inl hab
          have hl := mem_lambdaSet h hS hcol hP hQ hPQ
          obtain ⟨C, hC, hCle, habC⟩ :=
            hl.2 (a * b) (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))
              hab
          exact Or.inr ⟨C, ⟨hC, hCle.trans (sup_le hP.2 hQ.2)⟩, habC⟩
      inv_mem' := by
        rintro a (rfl | ⟨P, hP, ha⟩)
        · exact Or.inl inv_one
        · exact Or.inr ⟨P, hP, P.inv_mem ha⟩ }
  have hle : gen S ≤ U := gen_le fun B hB y hy => Or.inr ⟨B, ⟨hS hB, le_gen hB⟩, hy⟩
  rcases hle hx with h1 | ⟨P, hP, hxP⟩
  · exact absurd h1 hx1
  · exact ⟨P, hP.1, hP.2, hxP⟩

omit h hS hcol in
theorem conjSub_eq_of_mem_normalizer [Finite G] {T : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (T : Set G)) : conjSub T u = T := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hu t).1 ht
  · rw [conjSub, Subgroup.card_map_of_injective fun _ _ e => (MulAut.conj u).injective e]

theorem mem_normSet_of_le_M {C U : Subgroup G} (hC : C ∈ pts R (gen S)) (hU : U ∈ R)
    (hUM : U ≤ M R C) : U ∈ normSet R (gen S) := by
  have := h.finite
  have hcomm : ⁅M R C, M R C⁆ = C := (Q_eq_M h hC.1).2.2.1
  have hTM := gen_le_M h hS hcol hC
  refine ⟨hU, fun u hu => conjSub_eq_of_mem_normalizer ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have key : ∀ t ∈ gen S, u * t * u⁻¹ ∈ gen S := fun t ht => by
    have hc : ⁅u, t⁆ ∈ C := hcomm ▸ Subgroup.commutator_mem_commutator (hUM hu) (hTM ht)
    have e : u * t * u⁻¹ = ⁅u, t⁆ * t := by rw [commutatorElement_def]; group
    rw [e]
    exact (gen S).mul_mem (hC.2 hc) ht
  refine ⟨key t, fun ht => ?_⟩
  have hc : ⁅u⁻¹, u * t * u⁻¹⁆ ∈ C :=
    hcomm ▸ Subgroup.commutator_mem_commutator ((M R C).inv_mem (hUM hu)) (hTM ?_)
  · have e : t = ⁅u⁻¹, u * t * u⁻¹⁆ * (u * t * u⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (gen S).mul_mem (hC.2 hc) ht
  · exact ht

theorem exists_conjSub_eq {P Q : Subgroup G} (hP : P ∈ pts R (gen S)) (hQ : Q ∈ pts R (gen S)) :
    ∃ g ∈ ⨆ X ∈ normSet R (gen S), X, conjSub P g = Q := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_cases hPQ : P = Q
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hPQ, conjSub_of_mem (Subgroup.one_mem Q)]
  have hl := mem_lambdaSet h hS hcol hP hQ hPQ
  obtain ⟨C, hC, hCle, hCP, hCQ⟩ := exists_mem_le_sup_ne_ne hR hiso hP.1 hl P Q
  have hCpt : C ∈ pts R (gen S) := ⟨hC, hCle.trans (sup_le hP.2 hQ.2)⟩
  have hPC : P ∈ lambdaSet R C := mem_lambdaSet h hS hcol hCpt hP hCP
  have hsup : C ⊔ P = P ⊔ Q :=
    sup_eq_of_le_of_commuting hR hiso hP.1 hQ.1 hC hP.1 hl.1.2.2 hCle le_sup_left hCP
  obtain ⟨U, hU, u, hu, huPQ⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hC hPC hP.1
    le_sup_right (Ne.symm hCP) hQ.1 (hsup ▸ le_sup_right) (Ne.symm hCQ)
  have hUN := mem_normSet_of_le_M h hS hcol hCpt hU.1.1 (QD.le_M hU)
  exact ⟨u, Subgroup.mem_iSup_of_mem U (Subgroup.mem_iSup_of_mem hUN hu), huPQ⟩

theorem exists_mem_lambdaSet_not_commuting {P Q : Subgroup G} (hP : P ∈ pts R (gen S))
    (hQ : Q ∈ pts R (gen S)) (hPQ : P ≠ Q) :
    ∃ X ∈ normSet R (gen S), X ∈ lambdaSet R Q ∧ ¬ Commuting P X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hl := mem_lambdaSet h hS hcol hQ hP (Ne.symm hPQ)
  obtain ⟨C, hC, hCle, hCQ, hCP⟩ := exists_mem_le_sup_ne_ne hR hiso hQ.1 hl Q P
  obtain ⟨U, hU, u, hu, huPC⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hQ.1 hl hP.1
    le_sup_right hPQ hC hCle hCQ
  refine ⟨U, mem_normSet_of_le_M h hS hcol hQ hU.1.1 (QD.le_M hU), hU, fun hcomm => hCP ?_⟩
  rw [← huPC, conjSub_of_forall_commute fun p hp => (hcomm p hp u hu).symm]

theorem exists_not_commuting {P Q : Subgroup G} (hP : P ∈ pts R (gen S))
    (hQ : Q ∈ pts R (gen S)) (hPQ : P ≠ Q) : ∃ X ∈ normSet R (gen S), ¬ Commuting P X := by
  obtain ⟨X, hX, -, hPX⟩ := exists_mem_lambdaSet_not_commuting h hS hcol hP hQ hPQ
  exact ⟨X, hX, hPX⟩

theorem commutator_le_of_mem_lambdaSet {P X : Subgroup G} (hP : P ∈ pts R (gen S))
    (hXP : X ∈ lambdaSet R P) : ⁅gen S, X⁆ ≤ P := by
  have hcomm : ⁅M R P, M R P⁆ = P := (Q_eq_M h hP.1).2.2.1
  exact hcomm ▸ Subgroup.commutator_mono (gen_le_M h hS hcol hP) (QD.le_M hXP)

theorem not_opposite_of_mem_normSet {X B : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hB : B ∈ pts R (gen S)) : ¬ Opposite X B := by
  have := h.finite
  have hR := h.root
  intro hXB
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX.1
  have hopp := opposite_conjSub_of_opposite hR hX.1 hB.1 hXB hx hx1
  have hle : conjSub B x ≤ gen S := by
    rw [← hX.2 x hx]
    exact Subgroup.map_mono hB.2
  exact hopp.not_commuting (hR.ne_bot B hB.1)
    ((commuting_gen h hS hcol).mono hB.2 hle)

theorem special_of_not_commuting {X B : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hB : B ∈ pts R (gen S)) (hXB : ¬ Commuting X B) :
    Special R X B ∧ ⁅X, B⁆ ∈ pts R (gen S) ∧ X ∈ lambdaSet R ⁅X, B⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hne : X ≠ B := fun e => hXB (by rw [e]; exact hR.commuting_self hB.1)
  rcases hR.rel X hX.1 B hB.1 hne with hc | ho | hs
  · exact absurd hc hXB
  · exact absurd ho (not_opposite_of_mem_normSet h hS hcol hX hB)
  refine ⟨hs, ⟨hs.1, ?_⟩, (mem_lambdaSet_commutator hR hiso hX.1 hB.1 hs).1⟩
  rw [Subgroup.commutator_le]
  intro x hx b hb
  have hxb : x * b * x⁻¹ ∈ gen S := by
    rw [← hX.2 x hx]
    exact ⟨b, hB.2 hb, rfl⟩
  rw [commutatorElement_def]
  exact (gen S).mul_mem hxb ((gen S).inv_mem (hB.2 hb))

theorem exists_mem_lambdaSet {X : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hXT : ¬ Commuting X (gen S)) : ∃ P ∈ pts R (gen S), X ∈ lambdaSet R P := by
  have hB : ∃ B ∈ S, ¬ Commuting X B := by
    by_contra hall
    push Not at hall
    exact hXT (commuting_iff_le_centralizer.2 (gen_le fun B hB =>
      commuting_iff_le_centralizer.1 (hall B hB)))
  obtain ⟨B, hBS, hXB⟩ := hB
  obtain ⟨-, hP, hXP⟩ :=
    special_of_not_commuting h hS hcol hX ⟨hS hBS, le_gen hBS⟩ hXB
  exact ⟨_, hP, hXP⟩

theorem commutator_eq_of_mem_lambdaSet {X P B : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hP : P ∈ pts R (gen S)) (hXP : X ∈ lambdaSet R P) (hB : B ∈ pts R (gen S))
    (hXB : ¬ Commuting X B) : ⁅X, B⁆ = P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hs, hP', -⟩ := special_of_not_commuting h hS hcol hX hB hXB
  have hle : ⁅X, B⁆ ≤ P := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hB.2 le_rfl).trans
      (commutator_le_of_mem_lambdaSet h hS hcol hP hXP)
  by_contra hne
  have hbot := inf_eq_bot hR hiso hP'.1 hP.1 hne
  rw [inf_eq_left.2 hle] at hbot
  exact hR.ne_bot _ hs.1 hbot

omit hS hcol in
theorem conjSub_eq_of_le {P : Subgroup G} {g : G} (hle : conjSub P g ≤ P) : conjSub P g = P := by
  have := h.finite
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [conjSub, Subgroup.card_map_of_injective fun _ _ e => (MulAut.conj g).injective e])

theorem opposite_of_not_commuting {X Y P Q : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hY : Y ∈ normSet R (gen S)) (hP : P ∈ pts R (gen S)) (hQ : Q ∈ pts R (gen S))
    (hXP : X ∈ lambdaSet R P) (hYQ : Y ∈ lambdaSet R Q) (hPY : ¬ Commuting P Y)
    (hQX : ¬ Commuting Q X) : Opposite X Y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPX : Commuting P X := hXP.1.2.2
  have hQY : Commuting Q Y := hYQ.1.2.2
  have hPQ : P ≠ Q := fun e => hQX (e ▸ hPX)
  have hXY : X ≠ Y := fun e => hPY (e ▸ hPX)
  have hXQ' : ¬ Commuting X Q := fun c => hQX c.symm
  have hYP' : ¬ Commuting Y P := fun c => hPY c.symm
  have hXQ : ⁅X, Q⁆ = P := commutator_eq_of_mem_lambdaSet h hS hcol hX hP hXP hQ hXQ'
  have hYP : ⁅Y, P⁆ = Q := commutator_eq_of_mem_lambdaSet h hS hcol hY hQ hYQ hP hYP'
  have hsXQ := (special_of_not_commuting h hS hcol hX hQ hXQ').1
  have hsYP := (special_of_not_commuting h hS hcol hY hP hYP').1
  rcases hR.rel X hX.1 Y hY.1 hXY with hc | ho | hs
  ·
    exfalso
    apply hPY
    refine (Sec3.commuting_of_forall_conjSub_eq hR hY.1 hP.1 (fun y hy => ?_) hiso).symm
    have hXy : conjSub X y = X := conjSub_of_forall_commute fun x hx => (hc x hx y hy).symm
    have hQy : conjSub Q y ≤ gen S := by
      rw [← hY.2 y hy]
      exact Subgroup.map_mono hQ.2
    refine conjSub_eq_of_le h ?_
    rw [← hXQ, conjSub, Subgroup.map_commutator]
    change ⁅conjSub X y, conjSub Q y⁆ ≤ ⁅X, Q⁆
    rw [hXy, hXQ]
    calc ⁅X, conjSub Q y⁆ ≤ ⁅X, gen S⁆ := Subgroup.commutator_mono le_rfl hQy
      _ = ⁅gen S, X⁆ := Subgroup.commutator_comm _ _
      _ ≤ P := commutator_le_of_mem_lambdaSet h hS hcol hP hXP
  · exact ho
  ·
    exfalso
    have hPQc : Commuting P Q := (commuting_gen h hS hcol).mono hP.2 hQ.2
    set L : Subgroup G := P ⊔ Q with hLdef
    have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_conjSub_le fun x hx => by
      rw [conjSub, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · change conjSub P x ≤ L
        rw [conjSub_of_forall_commute fun p hp => (hPX p hp x hx).symm]
        exact le_sup_left
      · rintro _ ⟨q, hq, rfl⟩
        change x * q * x⁻¹ ∈ L
        have hc : ⁅x, q⁆ ∈ P := hXQ ▸ Subgroup.commutator_mem_commutator hx hq
        have e : x * q * x⁻¹ = ⁅x, q⁆ * q := by rw [commutatorElement_def]; group
        rw [e]
        exact L.mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hq)
    have hYL : Y ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_conjSub_le fun y hy => by
      rw [conjSub, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, hp, rfl⟩
        change y * p * y⁻¹ ∈ L
        have hc : ⁅y, p⁆ ∈ Q := hYP ▸ Subgroup.commutator_mem_commutator hy hp
        have e : y * p * y⁻¹ = ⁅y, p⁆ * p := by rw [commutatorElement_def]; group
        rw [e]
        exact L.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hp)
      · change conjSub Q y ≤ L
        rw [conjSub_of_forall_commute fun q hq => (hQY q hq y hy).symm]
        exact le_sup_right
    have hL2 : IsPGroup 2 L := isPGroup_sup_of_commuting (hR.isPGroup hP.1) (hR.isPGroup hQ.1) hPQc
    have hH2 : IsPGroup 2 ↥(X ⊔ Y) := Special.isPGroup_sup hR hX.1 hY.1 hs
    have hK2 : IsPGroup 2 ↥(L ⊔ (X ⊔ Y)) :=
      IsPGroup.to_sup_of_normal_left' hL2 hH2 (sup_le hXL hYL)
    set K : Subgroup G := L ⊔ (X ⊔ Y) with hKdef
    have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer (sup_le hXL hYL)
    have := Fact.mk Nat.prime_two
    have : Group.IsNilpotent K := hK2.isNilpotent
    have hN : (L.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKL
    have hNb : L.subgroupOf K ≠ ⊥ := by
      intro hb
      have hPb : P = ⊥ := by
        rw [eq_bot_iff]
        intro p hp
        have : (⟨p, (le_sup_left.trans le_sup_left : P ≤ K) hp⟩ : K) ∈ L.subgroupOf K :=
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hp)
        rw [hb, Subgroup.mem_bot] at this
        exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
      exact hR.ne_bot P hP.1 hPb
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hNb)
    have hzL : ((z : K) : G) ∈ L := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 z.2).1
    have hzc : ∀ k : K, k * (z : K) = (z : K) * k :=
      fun k => Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2 k
    have hz1' : ((z : K) : G) ≠ 1 := fun e => hz1 (Subtype.ext (Subtype.ext e))
    obtain ⟨p, hp, q, hq, hpq⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hPQc a ha b hb) hzL
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX.1
    have hxK : x ∈ K := ((le_sup_left : X ≤ X ⊔ Y).trans le_sup_right : X ≤ K) hx
    have hzx : x * ((z : K) : G) = ((z : K) : G) * x := congrArg Subtype.val (hzc ⟨x, hxK⟩)
    have hpx : Commute p x := hPX p hp x hx
    have hqx : Commute x q := by
      rw [← hpq] at hzx
      have e : p * (x * q) = p * (q * x) := by
        calc p * (x * q) = (p * x) * q := by group
          _ = (x * p) * q := by rw [hpx.eq]
          _ = x * (p * q) := by group
          _ = p * q * x := hzx
          _ = p * (q * x) := by group
      exact mul_left_cancel e
    have hq1 : q = 1 := eq_one_of_commute_of_special hR hiso hX.1 hQ.1 hsXQ hx hx1 hq hqx
    obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hY.1
    have hyK : y ∈ K := ((le_sup_right : Y ≤ X ⊔ Y).trans le_sup_right : Y ≤ K) hy
    have hzy : y * ((z : K) : G) = ((z : K) : G) * y := congrArg Subtype.val (hzc ⟨y, hyK⟩)
    rw [← hpq, hq1, mul_one] at hzy
    have hp1 : p = 1 := eq_one_of_commute_of_special hR hiso hY.1 hP.1 hsYP hy hy1 hp hzy
    exact hz1' (by rw [← hpq, hp1, hq1, one_mul])

theorem exists_pts_not_commuting {X Y : Subgroup G} (hXT : ¬ Commuting X (gen S))
    (hYT : ¬ Commuting Y (gen S)) :
    ∃ C ∈ pts R (gen S), ¬ Commuting C X ∧ ¬ Commuting C Y := by
  have hex : ∀ {Z : Subgroup G}, ¬ Commuting Z (gen S) →
      ∃ t ∈ gen S, t ∉ Subgroup.centralizer (Z : Set G) := by
    intro Z hZ
    by_contra hall
    push Not at hall
    exact hZ (commuting_iff_le_centralizer.2 fun t ht => hall t ht)
  obtain ⟨a, ha, haX⟩ := hex hXT
  obtain ⟨b, hb, hbY⟩ := hex hYT
  have ht : ∃ t ∈ gen S, t ∉ Subgroup.centralizer (X : Set G) ∧
      t ∉ Subgroup.centralizer (Y : Set G) := by
    by_cases haY : a ∈ Subgroup.centralizer (Y : Set G)
    · by_cases hbX : b ∈ Subgroup.centralizer (X : Set G)
      · refine ⟨a * b, (gen S).mul_mem ha hb, fun h' => haX ?_, fun h' => hbY ?_⟩
        · have := (Subgroup.centralizer (X : Set G)).mul_mem h'
            ((Subgroup.centralizer _).inv_mem hbX)
          rwa [mul_inv_cancel_right] at this
        · have := (Subgroup.centralizer (Y : Set G)).mul_mem
            ((Subgroup.centralizer _).inv_mem haY) h'
          rwa [inv_mul_cancel_left] at this
      · exact ⟨b, hb, hbX, hbY⟩
    · exact ⟨a, ha, haX, haY⟩
  obtain ⟨t, htT, htX, htY⟩ := ht
  have ht1 : t ≠ 1 := fun e => htX (e ▸ Subgroup.one_mem _)
  obtain ⟨C, hC, hCT, htC⟩ := coveredBy_gen h hS hcol t htT ht1
  refine ⟨C, ⟨hC, hCT⟩, fun hc => htX ?_, fun hc => htY ?_⟩
  · exact Subgroup.mem_centralizer_iff.2 fun x hx => (hc t htC x hx).symm
  · exact Subgroup.mem_centralizer_iff.2 fun y hy => (hc t htC y hy).symm

theorem reflTransGen_oppGraph {X Y : Subgroup G} (hX : X ∈ normSet R (gen S))
    (hY : Y ∈ normSet R (gen S)) (hXT : ¬ Commuting X (gen S)) (hYT : ¬ Commuting Y (gen S)) :
    Relation.ReflTransGen (oppGraph (normSet R (gen S))) X Y := by
  obtain ⟨P, hP, hXP⟩ := exists_mem_lambdaSet h hS hcol hX hXT
  obtain ⟨Q, hQ, hYQ⟩ := exists_mem_lambdaSet h hS hcol hY hYT
  obtain ⟨C, hC, hCX, hCY⟩ := exists_pts_not_commuting h hS hcol hXT hYT
  have hPC : P ≠ C := fun e => hCX (e ▸ hXP.1.2.2)
  have hQC : Q ≠ C := fun e => hCY (e ▸ hYQ.1.2.2)
  obtain ⟨Z₁, hZ₁, hZ₁C, hPZ₁⟩ := exists_mem_lambdaSet_not_commuting h hS hcol hP hC hPC
  obtain ⟨Z₂, hZ₂, hZ₂C, hQZ₂⟩ := exists_mem_lambdaSet_not_commuting h hS hcol hQ hC hQC
  have hXZ₁ := opposite_of_not_commuting h hS hcol hX hZ₁ hP hC hXP hZ₁C hPZ₁ hCX
  have hYZ₂ := opposite_of_not_commuting h hS hcol hY hZ₂ hQ hC hYQ hZ₂C hQZ₂ hCY
  have hZ₁T : ¬ Commuting Z₁ (gen S) := fun c => hPZ₁ (c.symm.mono hP.2 le_rfl)
  have hZ₂T : ¬ Commuting Z₂ (gen S) := fun c => hQZ₂ (c.symm.mono hQ.2 le_rfl)
  obtain ⟨C', hC', hC'Z₁, hC'Z₂⟩ := exists_pts_not_commuting h hS hcol hZ₁T hZ₂T
  have hCC' : C ≠ C' := fun e => hC'Z₁ (e ▸ hZ₁C.1.2.2)
  obtain ⟨W, hW, hWC', hCW⟩ := exists_mem_lambdaSet_not_commuting h hS hcol hC hC' hCC'
  have hWZ₁ := opposite_of_not_commuting h hS hcol hW hZ₁ hC' hC hWC' hZ₁C hC'Z₁ hCW
  have hWZ₂ := opposite_of_not_commuting h hS hcol hW hZ₂ hC' hC hWC' hZ₂C hC'Z₂ hCW
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single ⟨hX, hZ₁, hXZ₁⟩) ⟨hZ₁, hW, hWZ₁.symm⟩) ⟨hW, hZ₂, hWZ₂⟩)
    ⟨hZ₂, hY, hYZ₂.symm⟩

end Singular

end CFSG.Timmesfeld.ARS
