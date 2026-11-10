
module

public import CFSG.Quasithin.Vol2.Ch12Sec5KG
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.Walter.J1

@[expose] public section

namespace CFSG.Quasithin.H13.S125KG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem le_inSubgroup_perfectResidual_of_le {G : Type} [Group G] {P N : Subgroup G}
    (hPN : P ≤ N) (hP : P ≤ ⁅P, P⁆) : P ≤ CFSG.inSubgroup CFSG.perfectResidual N := by
  have hmap : (P.subgroupOf N).map N.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPN
  have hP' : P.subgroupOf N ≤ ⁅P.subgroupOf N, P.subgroupOf N⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, Subgroup.map_commutator, hmap]
    exact hP
  have key : ∀ n, P.subgroupOf N ≤ derivedSeries N n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih => rw [derivedSeries_succ]; exact hP'.trans (Subgroup.commutator_mono ih ih)
  intro x hx
  exact ⟨⟨x, hPN hx⟩, (le_iInf key : P.subgroupOf N ≤ CFSG.perfectResidual N)
    (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem card_modEq_one_of_fixedPointFree {X : Type} [Group X] [Finite X] {E : Subgroup X} {v : X}
    {p : ℕ} [Fact p.Prime] (hv : orderOf v = p) (hvE : v ∈ Subgroup.normalizer (E : Set X))
    (hfix : ∀ e ∈ E, v * e = e * v → e = 1) : Nat.card E ≡ 1 [MOD p] := by
  have hPN : Subgroup.zpowers v ≤ Subgroup.normalizer (E : Set X) := Subgroup.zpowers_le.mpr hvE
  let _ : MulAction ↥(Subgroup.zpowers v) ↥E :=
    { smul := fun g e => ⟨(g : X) * e * (g : X)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hPN g.2) e).mp e.2⟩
      one_smul := fun e => Subtype.ext (show ((1 : ↥(Subgroup.zpowers v)) : X) * e *
          ((1 : ↥(Subgroup.zpowers v)) : X)⁻¹ = e by simp)
      mul_smul := fun g h e => Subtype.ext (show ((g * h : ↥(Subgroup.zpowers v)) : X) * e *
          ((g * h : ↥(Subgroup.zpowers v)) : X)⁻¹ =
          (g : X) * ((h : X) * e * (h : X)⁻¹) * (g : X)⁻¹ by
        simp only [Subgroup.coe_mul]
        group) }
  have hP : IsPGroup p ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  have h := hP.card_modEq_card_fixedPoints ↥E
  have h1 : ∀ e ∈ MulAction.fixedPoints ↥(Subgroup.zpowers v) ↥E, e = 1 := by
    intro e he
    have h2 : v * e * v⁻¹ = e := congrArg Subtype.val (he ⟨v, Subgroup.mem_zpowers v⟩)
    refine Subtype.ext (hfix e e.2 ?_)
    calc v * e = v * e * v⁻¹ * v := by group
      _ = e * v := by rw [h2]
  have hone : (1 : ↥E) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers v) ↥E := fun g =>
    Subtype.ext (show (g : X) * ((1 : ↥E) : X) * (g : X)⁻¹ = ((1 : ↥E) : X) by simp)
  have hfp : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers v) ↥E) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((h1 a a.2).trans (h1 b b.2).symm)⟩, ⟨⟨1, hone⟩⟩⟩
  rwa [hfp] at h

theorem card_comap_mulEquiv {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y) (Z : Subgroup Y) :
    Nat.card (Z.comap ψ.toMonoidHom) = Nat.card Z := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective Z]
  exact (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm

end CFSG.Quasithin.H13.S125KG

namespace CFSG.Quasithin.H13.S125KG.M24

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b m24_hyp)
open scoped commutatorElement

abbrev Γ : Type := ↥CFSG.Blueprint.NativeSporadic.M24

noncomputable abbrev elt (w : List ℕ) : Γ := wordElt m24a m24b w

theorem tab_one : tab 24 (1 : Γ) = List.range 24 := by
  simp [tab]

theorem tab_letter (l : ℕ) : tab 24 ((#[m24a, m24b] : Array Γ).getD l 1) = letTab l := by
  rcases l with _ | _ | l
  · simp [letTab, CFSG.QuasithinUnique.K1.SporadicPerm.m24_tab_a]
  · simp [letTab, CFSG.QuasithinUnique.K1.SporadicPerm.m24_tab_b]
  · simp [letTab, tab_one]

theorem tab_elt (w : List ℕ) : tab 24 (elt w) = wTab w := by
  induction w with
  | nil => simp [elt, wordElt, evalElt_nil, wTab, tab_one]
  | cons l w ih =>
    rw [elt, wordElt, evalElt_cons, tab_mul, tab_letter, ← wordElt, ← elt, ih]
    rfl

theorem eq_of_tab_eq {g h : Γ} (e : tab 24 g = tab 24 h) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro j
  have h1 := tab_getD (n := 24) g j
  have h2 := tab_getD (n := 24) h j
  rw [e] at h1
  exact Fin.ext (h1.symm.trans h2)

theorem elt_append (w w' : List ℕ) : elt (w ++ w') = elt w * elt w' := by
  simp [elt, wordElt, evalElt, List.map_append, List.prod_append]

theorem elt_nil : elt [] = 1 := by simp [elt, wordElt, evalElt]

theorem elt_cons (l : ℕ) (w : List ℕ) :
    elt (l :: w) = (#[m24a, m24b] : Array Γ).getD l 1 * elt w := by
  simp [elt, wordElt, evalElt]

theorem elt_eq_one {w : List ℕ} (h : wTab w = List.range 24) : elt w = 1 :=
  eq_of_tab_eq (by rw [tab_elt, h, tab_one])

theorem a_mul_a : m24a * m24a = 1 := by
  have h := elt_eq_one (w := [0, 0]) (by decide)
  simpa [elt, wordElt, evalElt] using h

theorem b_mul_b_mul_b : m24b * m24b * m24b = 1 := by
  have h := elt_eq_one (w := [1, 1, 1]) (by decide)
  rw [elt_cons, elt_cons, elt_cons, elt_nil, mul_one] at h
  change m24b * (m24b * m24b) = 1 at h
  rw [← mul_assoc] at h
  exact h

theorem elt_invW (w : List ℕ) : elt (invW w) = (elt w)⁻¹ := by
  induction w with
  | nil => simp [invW, elt_nil]
  | cons l w ih =>
    have e : invW (l :: w) = invW w ++
        (if l = 0 then [0] else if l = 1 then [1, 1] else []) := by
      simp [invW, List.reverse_cons, List.flatMap_append]
    rw [e, elt_append, ih, elt_cons, mul_inv_rev]
    congr 1
    rcases l with _ | _ | l
    · have : m24a⁻¹ = m24a := inv_eq_of_mul_eq_one_left a_mul_a
      simp [elt_cons, elt_nil, this]
    · have : m24b⁻¹ = m24b * m24b := inv_eq_of_mul_eq_one_left b_mul_b_mul_b
      simp [elt_cons, elt_nil, this]
    · simp [elt_nil]

theorem lab_elt (w : List ℕ) : lab 24 (codeSetLab 24) m24Delta (elt w) = labW w := by
  rw [lab, tab_elt]
  rfl

theorem elt_commW (v u : List ℕ) : elt (commW v u) = ⁅elt v, elt u⁆ := by
  rw [commW, elt_append, elt_append, elt_append, elt_invW, elt_invW, commutatorElement_def]

theorem elt_a : elt [0] = m24a := by
  rw [elt_cons, elt_nil, mul_one]
  rfl

theorem elt_pow_three (w : List ℕ) : elt w ^ 3 = elt (w ++ w ++ w) := by
  rw [elt_append, elt_append, pow_succ, pow_succ, pow_one]

theorem elt_pow_seven (w : List ℕ) : elt w ^ 7 = elt (w ++ w ++ w ++ w ++ w ++ w ++ w) := by
  simp only [elt_append]
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_one]

theorem elt_mem_of_mem_foldr {H : Subgroup Γ} (L : List (List ℕ)) (hL : ∀ q ∈ L, elt q ∈ H) :
    ∀ p ∈ L.foldr (fun q acc => acc ++ acc.map (q ++ ·)) [[]], elt p ∈ H := by
  induction L with
  | nil =>
    intro p hp
    rw [List.foldr_nil, List.mem_singleton] at hp
    rw [hp, elt_nil]
    exact H.one_mem
  | cons q L ih =>
    intro p hp
    have ih' := ih fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')
    simp only [List.foldr_cons, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨p', hp', rfl⟩
    · exact ih' p hp
    · rw [elt_append]
      exact H.mul_mem (hL q List.mem_cons_self) (ih' p' hp')

theorem length_foldr (L : List (List ℕ)) :
    (L.foldr (fun q acc => acc ++ acc.map (q ++ ·)) [[]]).length = 2 ^ L.length := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [List.foldr_cons, List.length_append, List.length_map, ih, List.length_cons,
      pow_succ]
    omega

theorem isSolvable_of_card_eq {G : Type*} [Group G] [Finite G] (h : Nat.card G = 3072) :
    Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, show (3072 : ℕ) = 2 ^ 10 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

theorem eq_top_of_m24
    {X : Type} [Group X]
    {K₀ : Subgroup X} [K₀.Normal] (hK₀ : Nonempty (↥K₀ ≃* NativeSporadic.M24))
    (hC : Subgroup.centralizer (K₀ : Set X) ≤ K₀) : K₀ = ⊤ := by
  obtain ⟨e⟩ := hK₀
  rw [eq_top_iff]
  intro x _
  obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner
    ((e.symm.trans (MulAut.conjNormal x)).trans e)
  set k : ↥K₀ := e.symm h with hk
  have hconj : ∀ y : ↥K₀, x * (y : X) * x⁻¹ = (k : X) * y * (k : X)⁻¹ := by
    intro y
    have h1 := congrArg (fun α : MulAut NativeSporadic.M24 => α (e y)) hh
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : MulAut.conjNormal x y = k * y * k⁻¹ := by
      apply e.injective
      rw [← h1, map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    simpa using h3
  have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hconj ⟨y, hy⟩
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [← h1]
      _ = (k : X)⁻¹ * x * y := by group
  have := K₀.mul_mem k.2 (hC hc)
  simpa using this

theorem om_size [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {j : ℕ} (hj : j < 13) :
    m24LatK.Om[j]!.lbl.size = [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 := by
  rw [m24_Om_size j hj]
  interval_cases j <;> rfl

noncomputable def kgCtx [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    LatCtx Γ 24 (List ℕ) :=
  m24Ctx

theorem kgCtx_J [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    kgCtx.J = 13 := m24_J

theorem orderOf_elt' {w w' : List ℕ} {p : ℕ} [Fact p.Prime] (hpow : elt w ^ p = elt w')
    (h1 : elt w' = 1) (h2 : elt w ≠ 1) : orderOf (elt w) = p :=
  orderOf_eq_prime (by rw [hpow]; exact h1) h2

theorem member_lt [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {j : ℕ} (hj : j < 13) :
    memberOrTop 13 kgCtx.Y j = kgCtx.Y j :=
  ite_eq_left hj

theorem member_top [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    memberOrTop 13 kgCtx.Y 13 = ⊤ :=
  ite_eq_right (lt_irrefl 13)

theorem card_member [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {j : ℕ} (hj : j ≤ 13) :
    Nat.card (memberOrTop 13 kgCtx.Y j) =
      [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 * 1024 := by
  have h := kgCtx.member_card (j := j)
  rw [kgCtx_J] at h
  rw [h]
  change (if j < 13 then m24LatK.Om[j]!.lbl.size else m24Ctx.D.O.lbl.size) * 1024 = _
  by_cases hj' : j < 13
  · rw [ite_eq_left hj', om_size hj']
  · rw [ite_eq_right hj', m24_O_size]
    obtain rfl : j = 13 := by omega
    rfl

theorem kgCtx_S_card [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card kgCtx.S = 1024 :=
  kgCtx.S_card

theorem kgCtx_S_sylow [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    IsSylowTwoOf kgCtx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨kgCtx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index kgCtx.S
  rw [kgCtx_S_card, m24_card] at h1
  have h2 : kgCtx.S.index = 239085 := by omega
  rw [h2]
  norm_num

variable {X : Type} [Group X]

theorem exists_equiv [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (hX : Nonempty (X ≃* Γ)) {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) : ∃ ψ : X ≃* Γ, S.map ψ.toMonoidHom = kgCtx.S := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp (isSylowTwoOf_map e hS)
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp kgCtx_S_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : kgCtx.S = (S.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem card_S [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (ψ : X ≃* Γ) {S : Subgroup X}
    (hψ : S.map ψ.toMonoidHom = kgCtx.S) : Nat.card S = 1024 := by
  rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hψ, kgCtx_S_card]

theorem exists_member_map [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (ψ : X ≃* Γ) {S Z : Subgroup X}
    (hψ : S.map ψ.toMonoidHom = kgCtx.S) (hSZ : S ≤ Z) :
    ∃ j ≤ 13, Z.map ψ.toMonoidHom = memberOrTop 13 kgCtx.Y j ∧
      Nat.card Z = [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 * 1024 := by
  obtain ⟨j, hj, h⟩ := kgCtx.complete (Z.map ψ.toMonoidHom) (by
    rw [← hψ]; exact Subgroup.map_mono hSZ)
  rw [kgCtx_J] at hj h
  refine ⟨j, hj, h, ?_⟩
  rw [← card_member hj, ← h]
  exact (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm

theorem map_N [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (ψ : X ≃* Γ) {S N D : Subgroup X}
    (hψ : S.map ψ.toMonoidHom = kgCtx.S) (hc : Config63 S N D) :
    N.map ψ.toMonoidHom = kgCtx.Y 2 := by
  obtain ⟨hSD, hDN, hNc, -, -⟩ := hc
  obtain ⟨j, hj, h, hcard⟩ := exists_member_map ψ hψ (hSD.trans hDN)
  rw [hNc, card_S ψ hψ] at hcard
  rw [h]
  interval_cases j <;> first | (simp at hcard; done) | exact member_lt (by norm_num)

theorem pCoreOf_eq [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    [Finite X] (ψ : X ≃* Γ)
    {S N D : Subgroup X} (hS : IsSylowTwoOf S ⊤) (hψ : S.map ψ.toMonoidHom = kgCtx.S)
    (hc : Config63 S N D) {Q : Subgroup Γ} (hQc : Nat.card Q = 64) (hQY : Q ≤ kgCtx.Y 2)
    (hQN : kgCtx.Y 2 ≤ Subgroup.normalizer (Q : Set Γ)) :
    pCoreOf 2 N = Q.comap ψ.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 := map_N ψ hψ hc
  have hSN : S ≤ N := hc.1.trans hc.2.1
  have hNc : Nat.card N = 64512 := by rw [hc.2.2.1, card_S ψ hψ]
  have hcard : Nat.card (Q.comap ψ.toMonoidHom) = 64 := by
    rw [card_comap_mulEquiv, hQc]
  have hQN' : Q.comap ψ.toMonoidHom ≤ N := by
    intro x hx
    have h1 : ψ x ∈ kgCtx.Y 2 := hQY hx
    rw [← hN2] at h1
    exact (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective).mp h1
  have hnorm : N ≤ Subgroup.normalizer (Q.comap ψ.toMonoidHom : Set X) := by
    intro n hn
    have h1 : ψ n ∈ kgCtx.Y 2 := by
      rw [← hN2]
      exact Subgroup.mem_map_of_mem _ hn
    have h2 := hQN h1
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    change ψ.toMonoidHom (n * q * n⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp h2 _).mp hq
  have hp : IsPGroup 2 ↥(Q.comap ψ.toMonoidHom) :=
    IsPGroup.of_card (n := 6) (hcard.trans (by norm_num))
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQN' hnorm hp
  have h64 : Nat.card (pCoreOf 2 N) = 64 := by
    rcases m24_overgroups (X := X) ⟨ψ⟩ hS hSN with h | ⟨m, hm, h1, h2, -⟩
    · exfalso
      have h3 : Nat.card N = Nat.card X := by rw [h, Subgroup.card_top]
      rw [hNc, Nat.card_congr ψ.toEquiv, m24_card] at h3
      norm_num at h3
    · rw [h2]
      have key : ∀ m ∈ m24Mems, m.order = 64512 → m.o2 = 64 := by decide
      exact key m hm (h1.symm.trans hNc)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h64, hcard])).symm

end CFSG.Quasithin.H13.S125KG.M24
