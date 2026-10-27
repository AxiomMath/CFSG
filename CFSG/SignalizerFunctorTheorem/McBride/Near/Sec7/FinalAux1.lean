module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxGen

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

section Conj

variable {G : Type*} [Group G]

abbrev cj (a : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj a).toMonoidHom

theorem mem_cj_iff {a : G} {X : Subgroup G} {z : G} : z ∈ cj a X ↔ a⁻¹ * z * a ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨a⁻¹ * z * a, h, by simp [mul_assoc]⟩

theorem cj_one (X : Subgroup G) : cj 1 X = X := by
  ext x; simp

theorem cj_cj (a c : G) (X : Subgroup G) : cj a (cj c X) = cj (a * c) X := by
  ext x; simp [mul_assoc]

theorem cj_inf (a : G) (X Y : Subgroup G) : cj a (X ⊓ Y) = cj a X ⊓ cj a Y :=
  Subgroup.map_inf _ _ _ (MulAut.conj a).injective

theorem cj_sup (a : G) (X Y : Subgroup G) : cj a (X ⊔ Y) = cj a X ⊔ cj a Y :=
  Subgroup.map_sup _ _ _

theorem cj_eq_of_mem_normalizer {a : G} {X : Subgroup G}
    (h : a ∈ Subgroup.normalizer (X : Set G)) : cj a X = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp h

theorem cj_bot (a : G) : cj a (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem cj_eq_bot_iff {a : G} {X : Subgroup G} : cj a X = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj a).injective

theorem cj_le_iff {a : G} {X Y : Subgroup G} : cj a X ≤ cj a Y ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj a).injective

theorem cj_inj {a : G} {X Y : Subgroup G} : cj a X = cj a Y ↔ X = Y :=
  Subgroup.map_injective (MulAut.conj a).injective |>.eq_iff

theorem cj_inv_cj (a : G) (X : Subgroup G) : cj a⁻¹ (cj a X) = X := by
  rw [cj_cj, inv_mul_cancel, cj_one]

theorem cj_cj_inv (a : G) (X : Subgroup G) : cj a (cj a⁻¹ X) = X := by
  rw [cj_cj, mul_inv_cancel, cj_one]

end Conj

section Pi

theorem not_isSolvable_pi {J : Type*} [Group J] [hJ : IsSimpleGroup J] {n : ℕ} (hn : 1 ≤ n)
    (hnab : ∃ a b : J, a * b ≠ b * a) : ¬ Group.IsSolvable (Fin n → J) := by
  intro hsol
  let f : (Fin n → J) →* J := Pi.evalMonoidHom (fun _ => J) ⟨0, hn⟩
  have hf : Function.Surjective f := fun x => ⟨Pi.mulSingle ⟨0, hn⟩ x, by simp [f]⟩
  have : Group.IsSolvable J := Group.isSolvable_of_surjective hf
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)

theorem not_isSimpleGroup_pi {J : Type*} [Group J] (hnab : ∃ a b : J, a * b ≠ b * a) {n : ℕ}
    (hn : 2 ≤ n) : ¬ IsSimpleGroup (Fin n → J) := by
  intro hs
  obtain ⟨a, b, hab⟩ := hnab
  have hx : ∃ x : J, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hab (by rw [hcon a, hcon b])
  obtain ⟨x, hx1⟩ := hx
  let f : (Fin n → J) →* J := Pi.evalMonoidHom (fun _ => J) ⟨0, by omega⟩
  rcases hs.eq_bot_or_eq_top_of_normal f.ker with h | h
  · have hmem : (Pi.mulSingle (⟨1, by omega⟩ : Fin n) x : Fin n → J) ∈ f.ker := by
      simp [f, MonoidHom.mem_ker]
    rw [h, Subgroup.mem_bot] at hmem
    have := congrFun hmem ⟨1, by omega⟩
    simp at this
    exact hx1 this
  · have hmem : (Pi.mulSingle (⟨0, by omega⟩ : Fin n) x : Fin n → J) ∈ f.ker := by
      rw [h]; trivial
    simp [f, MonoidHom.mem_ker] at hmem
    exact hx1 hmem

end Pi

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure Data (h : Counterexample p A θ) (E : Subgroup G) : Prop where
  hE : E ∈ signalizerFunctorEk p 1 A
  hEs : Group.IsSolvable (thetaOf θ E)
  nonsolv : ∀ f ∈ A, f ∉ E → ¬ Group.IsSolvable (θ f)
  notSimple : ∀ f ∈ A, f ∉ E → ¬ IsSimpleGroup ↥(kOf (θ f))
  khat_eq : ∀ f ∈ A, f ∉ E → θ f = khat (θ f)
  le_of_mem : ∀ f ∈ A, f ∉ E → ∀ X ∈ assoc p A θ, kOf (θ f) ≤ X → X ≤ θ f
  frob : IsFrobeniusWithKernel (dTwo p A θ) (dOne p A θ)
  decomp : ∀ B ∈ signalizerFunctorEk p 2 A, E ≤ B → ∀ F : Subgroup G, IsDirectPair E F B →
    IsDirectProduct {S | ∃ L ∈ lcal (thetaOf θ F), S = L ⊓ sThree p A θ ⊓ thetaOf θ E}
        (sThree p A θ ⊓ thetaOf θ B) ∧
      Nonempty (↥(sThree p A θ ⊓ thetaOf θ B) ≃* (Fin p → ↥(dTwo p A θ)))

structure Setting (p : ℕ) (A E B : Subgroup G) : Prop where
  hE : E ∈ signalizerFunctorEk p 1 A
  hB : B ∈ signalizerFunctorEk p 2 A
  hEB : E ≤ B

section Elementary

variable {E B : Subgroup G}


omit [Finite G] in
theorem Setting.mem_A (hS : Setting p A E B) {b : G} (hb : b ∈ B) : b ∈ A := hS.hB.1 hb

omit [Finite G] in
theorem ne_one_of_not_mem {b : G} (hbE : b ∉ E) : b ≠ 1 := fun h => hbE (h ▸ one_mem E)

theorem Setting.zpowers_mem (h : Counterexample p A θ) (hS : Setting p A E B) {b : G} (hb : b ∈ B)
    (hbE : b ∉ E) : Subgroup.zpowers b ∈ signalizerFunctorEk p 1 A :=
  zpowers_mem_signalizerFunctorEk_one h.hyp.prime h.hyp.elemAbelian (hS.mem_A hb)
    (ne_one_of_not_mem hbE)

theorem Setting.inf_zpowers (h : Counterexample p A θ) (hS : Setting p A E B) {b : G}
    (hb : b ∈ B) (hbE : b ∉ E) : E ⊓ Subgroup.zpowers b = ⊥ :=
  CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le h.hyp.prime
    (by rw [(hS.zpowers_mem h hb hbE).2, pow_one])
    (fun hle => hbE (hle (Subgroup.mem_zpowers b)))

theorem Setting.sup_zpowers (h : Counterexample p A θ) (hS : Setting p A E B) {b : G}
    (hb : b ∈ B) (hbE : b ∉ E) : E ⊔ Subgroup.zpowers b = B := by
  have hz := hS.zpowers_mem h hb hbE
  have hsup := CFSG.SignalizerFunctorTheorem.sup_mem_Ek_succ h.hyp.elemAbelian hS.hE hz
    (hS.inf_zpowers h hb hbE)
  exact Subgroup.eq_of_le_of_card_ge (sup_le hS.hEB (Subgroup.zpowers_le.mpr hb))
    (by rw [hS.hB.2, hsup.2])

theorem Setting.isDirectPair (h : Counterexample p A θ) (hS : Setting p A E B) {b : G}
    (hb : b ∈ B) (hbE : b ∉ E) : IsDirectPair E (Subgroup.zpowers b) B where
  commute x hx y hy := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (commute_of_mem h.hyp.elemAbelian.1 (hS.mem_A (hS.hEB hx)) (hS.mem_A hb)).zpow_right k
  inf_eq_bot := hS.inf_zpowers h hb hbE
  sup_eq := hS.sup_zpowers h hb hbE

theorem Setting.exists_mem_not_mem (h : Counterexample p A θ) (hS : Setting p A E B) :
    ∃ b ∈ B, b ∉ E := by
  by_contra hcon
  push Not at hcon
  have hle : B ≤ E := fun b hb => hcon b hb
  have := Subgroup.card_le_of_le hle
  rw [hS.hB.2, hS.hE.2] at this
  have h2 : p ^ 2 ≤ p ^ 1 := this
  have := Nat.pow_lt_pow_right h.hyp.prime.one_lt (show 1 < 2 by norm_num)
  omega

end Elementary


section Components

theorem Data.cset_apply
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E) {b : G}
    (hbA : b ∈ A) (hbE : b ∉ E) : θ b ∈ cset p A θ ⊥ :=
  h.apply_mem_cset_bot hbA (ne_one_of_not_mem hbE) (D.nonsolv b hbA hbE)

theorem Data.sol_apply
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E) {b : G}
    (hbA : b ∈ A) (hbE : b ∉ E) : sol (θ b) = ⊥ :=
  h.sol_eq_bot_of_mem_cset (D.cset_apply hbA hbE)

theorem Data.isDirectProduct_lcal
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E)
    {b : G} (hbA : b ∈ A) (hbE : b ∉ E) : IsDirectProduct (lcal (θ b)) (kOf (θ b)) :=
  isDirectProduct_lcal_kOf (D.sol_apply hbA hbE)

omit [Finite G] in
theorem lcal_ne_bot {X L : Subgroup G} (hL : L ∈ lcal X) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hL
  rw [hbot] at hnc
  exact hnc inferInstance

theorem Data.lcal_nonempty
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E) {b : G}
    (hbA : b ∈ A) (hbE : b ∉ E) : (lcal (θ b)).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hK := (D.isDirectProduct_lcal hbA hbE).sSup_eq
  rw [hne, sSup_empty] at hK
  exact Counterexample.kOf_ne_bot_of_not_isSolvable (D.nonsolv b hbA hbE) hK.symm

omit [Finite G] in
theorem map_conj_mem_lcal_apply (hθ : NearFunctor p A θ) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : L ∈ lcal (θ b)) {a : G} (ha : a ∈ A) : cj a L ∈ lcal (θ b) :=
  map_conj_mem_lcal hL (hθ.isFunctor.normalized b hbA hb1 ha)


theorem Data.E_le_normalizer_lcal
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : E ≤ Subgroup.normalizer (L : Set G) := by
  have hθ := h.hyp.nearFunctor
  have hbA : b ∈ A := hS.hB.1 hb
  have hb1 := ne_one_of_not_mem hbE
  obtain ⟨e, heA, he1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one hθ.prime hS.hE
  suffices he : e ∈ Subgroup.normalizer (L : Set G) from Subgroup.zpowers_le.mpr he
  by_contra hnot
  have hep : e ^ p = 1 := hθ.elemAbelian.2 e heA
  have hdp := D.isDirectProduct_lcal hbA hbE
  have hA' : ∀ a ∈ Subgroup.zpowers e, ∀ J ∈ lcal (θ b),
      J.map (MulAut.conj a).toMonoidHom ∈ lcal (θ b) :=
    fun a ha J hJ => map_conj_mem_lcal_apply hθ hbA hb1 hJ (Subgroup.zpowers_le.mpr heA ha)
  have hproj := projIn_centralizer_eq hdp hA' hL
  rw [Sec6Gen.zpowers_inf_normalizer_eq_bot hθ.prime hep hnot] at hproj
  have hle : kOf (θ b) ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set G) ≤
      thetaOf θ (Subgroup.zpowers e) := by
    have h1 := hθ.isFunctor.inf_centralizer_eq_thetaOf hbA hb1 (B := Subgroup.zpowers e)
      (Subgroup.zpowers_le.mpr heA)
    exact (inf_le_inf_right _ (kOf_le (θ b))).trans
      (h1.le.trans (thetaOf_anti (le_sup_right (a := Subgroup.zpowers b))))
  have hsolE := D.hEs
  have hsolX : Group.IsSolvable ↥(kOf (θ b) ⊓ Subgroup.centralizer
      (Subgroup.zpowers e : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hsolP := Thm210.isSolvable_projIn hdp hL inf_le_left hsolX
  rw [hproj] at hsolP
  have hLle : L ≤ L ⊓ Subgroup.centralizer (((⊥ : Subgroup G)) : Set G) := by
    refine le_inf le_rfl fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  have hLsol : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLle)
  exact Thm53A.not_isSolvable_of_mem_lcal hL hLsol


theorem lcal_kOf_eq_lcal {X : Subgroup G} (hX : sol X = ⊥) : lcal (kOf X) = lcal X :=
  (isSemisimple_kOf hX).lcal_eq.trans (simpleComponents_kOf hX)

theorem Data.dsub_le_normalizer_lcal
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E)
    {b : G} (hbA : b ∈ A) (hbE : b ∉ E) {L : Subgroup G} (hL : L ∈ lcal (θ b)) :
    dsub A θ ≤ Subgroup.normalizer (L : Set G) := by
  intro d hd
  have hdb : d ∈ θ b := dsub_le_apply hbA (ne_one_of_not_mem hbE) hd
  have hdk : d ∈ khat (θ b) := by rw [← D.khat_eq b hbA hbE]; exact hdb
  exact Thm53A.normalizer_of_mem_khat (D.sol_apply hbA hbE) hdk L hL

theorem Data.exists_cj_eq
    {h : Counterexample p A θ} {E : Subgroup G} (D : Data h E) {b : G}
    (hbA : b ∈ A) (hbE : b ∉ E) {L L' : Subgroup G} (hL : L ∈ lcal (θ b))
    (hL' : L' ∈ lcal (θ b)) : ∃ a ∈ A, L' = cj a L := by
  have hθ := h.hyp.nearFunctor
  have hb1 := ne_one_of_not_mem hbE
  have hcs := D.cset_apply hbA hbE
  have hsol := D.sol_apply hbA hbE
  rw [← lcal_kOf_eq_lcal hsol] at hL hL'
  obtain ⟨g, hg, rfl⟩ := h.exists_conj_eq_of_mem_lcal_kOf hcs hL hL'
  rw [lcal_kOf_eq_lcal hsol] at hL
  have hg' : g ∈ ((dsub A θ : Set G) * (A : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (dsub A θ) A (admits_dsub hθ)]
    exact hg
  obtain ⟨d, hd, a, ha, rfl⟩ := hg'
  refine ⟨a, ha, ?_⟩
  show cj (d * a) L = cj a L
  rw [← cj_cj]
  exact cj_eq_of_mem_normalizer
    (D.dsub_le_normalizer_lcal hbA hbE (map_conj_mem_lcal_apply hθ hbA hb1 hL ha) hd)


omit [Finite G] in
theorem mem_normalizer_of_forall_commute {b : G} {L : Subgroup G}
    (hc : ∀ x ∈ L, Commute b x) : b ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [(hc x hx).eq]
    simpa using hx
  · intro h
    set y := b * x * b⁻¹ with hy
    have h1 : b * y = y * b := (hc _ h).eq
    have hxy : x = y := by
      calc x = b⁻¹ * y * b := by simp [hy, mul_assoc]
        _ = b⁻¹ * (y * b) := by rw [mul_assoc]
        _ = b⁻¹ * (b * y) := by rw [h1]
        _ = y := by group
    rw [hxy]
    exact h

theorem Data.B_le_normalizer_lcal
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : B ≤ Subgroup.normalizer (L : Set G) := by
  have hθ := h.hyp.nearFunctor
  have hbA := hS.mem_A hb
  rw [← hS.sup_zpowers h hb hbE]
  refine sup_le (D.E_le_normalizer_lcal hS hb hbE hL) (Subgroup.zpowers_le.mpr ?_)
  refine mem_normalizer_of_forall_commute fun x hx => ?_
  have := hθ.isFunctor.le_centralizer b hbA (ne_one_of_not_mem hbE) (lcal_le hL hx)
  exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

theorem eq_or_eq_of_le_of_card {p : ℕ} (hp : p.Prime) {A B N : Subgroup G}
    (hAc : Nat.card A = p ^ 3) (hBc : Nat.card B = p ^ 2) (hBN : B ≤ N) (hNA : N ≤ A) :
    N = B ∨ N = A := by
  have hdvd : Nat.card N ∣ p ^ 3 := hAc ▸ Subgroup.card_dvd_of_le hNA
  obtain ⟨i, hi, hNi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hBN' : p ^ 2 ≤ p ^ i := hBc ▸ hNi ▸ Subgroup.card_le_of_le hBN
  have hi2 : 2 ≤ i := (Nat.pow_le_pow_iff_right hp.one_lt).mp hBN'
  interval_cases i
  · left
    exact (Subgroup.eq_of_le_of_card_ge hBN (by rw [hBc, hNi])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hNA (by rw [hAc, hNi])

theorem Data.inf_normalizer_lcal
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : A ⊓ Subgroup.normalizer (L : Set G) = B := by
  have hbA := hS.mem_A hb
  have hBN := D.B_le_normalizer_lcal hS hb hbE hL
  rcases eq_or_eq_of_le_of_card h.hyp.prime h.hyp.card hS.hB.2 (le_inf hS.hB.1 hBN)
    inf_le_left with h1 | h1
  · exact h1
  · exfalso
    have hAN : A ≤ Subgroup.normalizer (L : Set G) := h1 ▸ inf_le_right
    have hall : ∀ L' ∈ lcal (θ b), L' = L := by
      intro L' hL'
      obtain ⟨a, ha, rfl⟩ := D.exists_cj_eq hbA hbE hL hL'
      exact cj_eq_of_mem_normalizer (hAN ha)
    have hK := (D.isDirectProduct_lcal hbA hbE).sSup_eq
    have hset : lcal (θ b) = {L} := Set.eq_singleton_iff_unique_mem.mpr ⟨hL, hall⟩
    rw [hset, sSup_singleton] at hK
    obtain ⟨-, -, hLs, -⟩ := mem_lcal_iff.mp hL
    subst hK
    exact D.notSimple b hbA hbE hLs


omit [Finite G] in
theorem cj_eq_cj_iff {a a' : G} {X : Subgroup G} :
    cj a X = cj a' X ↔ a⁻¹ * a' ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change cj a X = cj a' X ↔ cj (a⁻¹ * a') X = X
  constructor
  · intro h
    have := congrArg (cj a⁻¹) h
    rw [cj_inv_cj, cj_cj] at this
    exact this.symm
  · intro h
    have h2 : cj a' X = cj a (cj (a⁻¹ * a') X) := by rw [cj_cj, mul_inv_cancel_left]
    rw [h2, h]

theorem Data.card_lcal
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    Nat.card ↥(lcal (θ b)) = p := by
  have hθ := h.hyp.nearFunctor
  have hbA := hS.mem_A hb
  have hb1 := ne_one_of_not_mem hbE
  obtain ⟨L₀, hL₀⟩ := D.lcal_nonempty hbA hbE
  have hstab := D.inf_normalizer_lcal hS hb hbE hL₀
  let f : A → ↥(lcal (θ b)) := fun a =>
    ⟨cj (a : G) L₀, map_conj_mem_lcal_apply hθ hbA hb1 hL₀ a.2⟩
  have hfeq : ∀ a a' : A, f a = f a' ↔ (a⁻¹ * a' : A) ∈ B.subgroupOf A := by
    intro a a'
    simp only [f, Subtype.mk.injEq]
    rw [cj_eq_cj_iff, Subgroup.mem_subgroupOf, ← hstab]
    exact ⟨fun h => ⟨(a⁻¹ * a').2, h⟩, fun h => h.2⟩
  have hfs : Function.Surjective f := by
    rintro ⟨L, hL⟩
    obtain ⟨a, ha, rfl⟩ := D.exists_cj_eq hbA hbE hL₀ hL
    exact ⟨⟨a, ha⟩, rfl⟩
  let g : A ⧸ B.subgroupOf A → ↥(lcal (θ b)) :=
    Quotient.lift f (fun a a' hr => by
      have hr' : a⁻¹ * a' ∈ B.subgroupOf A := QuotientGroup.leftRel_apply.mp hr
      exact (hfeq a a').mpr hr')
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro x y
      induction x using QuotientGroup.induction_on
      induction y using QuotientGroup.induction_on
      intro hxy
      exact QuotientGroup.eq.mpr ((hfeq _ _).mp hxy)
    · intro y
      obtain ⟨a, rfl⟩ := hfs y
      exact ⟨a, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg)]
  have h1 := Subgroup.card_mul_index (B.subgroupOf A)
  have h2 : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.hB.1).toEquiv
  rw [h2, hS.hB.2, h.hyp.card] at h1
  show (B.subgroupOf A).index = p
  exact Nat.eq_of_mul_eq_mul_left (pow_pos h.hyp.prime.pos 2) (by rw [h1]; ring)

end Components


end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
