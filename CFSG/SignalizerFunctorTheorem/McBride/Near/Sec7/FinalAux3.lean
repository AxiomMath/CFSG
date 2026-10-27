module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAuxSylow

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

section Coord

variable {G : Type*} [Group G] [Finite G]

theorem coord_mem_of_mem_sSup {S : Set (Subgroup G)} {K J Z : Subgroup G}
    (hK : IsDirectProduct S K) (hJ : J ∈ S) {X : Set (Subgroup G)} (hXK : ∀ Y ∈ X, Y ≤ K)
    (hX : ∀ Y (hY : Y ∈ X), ∀ x (hx : x ∈ Y), ((hK.coord hJ ⟨x, hXK Y hY hx⟩ : J) : G) ∈ Z)
    {x : G}
    (hx : x ∈ sSup X) :
    ((hK.coord hJ ⟨x, (sSup_le hXK) hx⟩ : J) : G) ∈ Z := by
  let φ : ↥K →* G := J.subtype.comp (hK.coord hJ)
  have hle : sSup X ≤ (Z.comap φ).map K.subtype := by
    refine sSup_le fun Y hY x hx => ?_
    exact ⟨⟨x, hXK Y hY hx⟩, hX Y hY x hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := hle hx
  have : k = ⟨x, (sSup_le hXK) hx⟩ := Subtype.ext hkx
  rw [this] at hk
  exact hk

end Coord

section VPart

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure VData (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E V : Subgroup G) (r : ℕ) :
    Prop where
  prime : r.Prime
  mem : V ∈ assoc p A θ
  pgroup : IsPGroup r V
  comm : IsMulCommutative V
  sylow : ∀ f ∈ A, f ∉ E → IsPGroup r (cenIn V {f}) ∧ ¬ r ∣ (cenIn V {f}).relIndex (θ f)
  gen : ∀ f ∈ A, f ∉ E →
    cenIn V {f} ⊔ (thetaOf θ (E ⊔ Subgroup.zpowers f) ⊓ sThree p A θ) = kOf (θ f)

omit [Finite G] in
theorem isMulCommutative_of_le {X Y : Subgroup G} (hXY : X ≤ Y) (hY : IsMulCommutative Y) :
    IsMulCommutative X :=
  isMulCommutative_iff.mpr fun a b => by
    have h := hY.is_comm.comm (⟨a, hXY a.2⟩ : Y) ⟨b, hXY b.2⟩
    simpa [Subtype.ext_iff] using h

theorem Data.le_inf_sup_Ff
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r) {b : G} (hb : b ∈ B)
    (hbE : b ∉ E) {L : Subgroup G} (hL : L ∈ lcal (θ b)) :
    L ≤ (V ⊓ L) ⊔ Ff p A θ E L := by
  have hbA := hS.mem_A hb
  have hdp := D.isDirectProduct_lcal hbA hbE
  have hgen := hV.gen b hbA hbE
  rw [hS.sup_zpowers h hb hbE, inf_comm] at hgen
  set P := cenIn V {b} with hP
  have hPK : P ≤ kOf (θ b) := hgen ▸ le_sup_left
  have hTK : sThree p A θ ⊓ thetaOf θ B ≤ kOf (θ b) := hgen ▸ le_sup_right
  obtain ⟨hPr, hidx⟩ := hV.sylow b hbA hbE
  have hidx' : ¬ r ∣ P.relIndex (kOf (θ b)) := fun hdvd => hidx (by
    rw [← Subgroup.relIndex_mul_relIndex P (kOf (θ b)) (θ b) hPK (kOf_le _)]
    exact Dvd.dvd.mul_right hdvd _)
  have hPab : IsMulCommutative P := isMulCommutative_of_le inf_le_left hV.comm
  have hmax : ∀ Q : Subgroup G, Q ≤ kOf (θ b) → IsPGroup r Q → P ≤ Q → Q ≤ P :=
    fun Q hQK hQr hPQ =>
      le_of_isPGroup_of_relIndex_coprime hV.prime hPK hPr hidx' hQK hQr hPQ
  set Z := (V ⊓ L) ⊔ Ff p A θ E L with hZ
  have hTc : ∀ t (ht : t ∈ sThree p A θ ⊓ thetaOf θ B),
      ((hdp.coord hL ⟨t, hTK ht⟩ : L) : G) ∈ Ff p A θ E L := by
    intro t ht
    have hdpF := D.isDirectProduct_Ff hS hb hbE
    have hFK : ∀ Y ∈ {S | ∃ L' ∈ lcal (θ b), S = Ff p A θ E L'}, Y ≤ kOf (θ b) := by
      rintro _ ⟨L', hL', rfl⟩
      exact (Ff_le_left E L').trans (hdp.le hL')
    have ht' : t ∈ sSup {S | ∃ L' ∈ lcal (θ b), S = Ff p A θ E L'} := by
      rw [hdpF.sSup_eq]; exact ht
    refine coord_mem_of_mem_sSup hdp hL hFK ?_ ht'
    rintro _ ⟨L', hL', rfl⟩ x hx
    by_cases hLL : L' = L
    · subst hLL
      rw [hdp.coord_of_mem hL' (Ff_le_left E L' hx)]
      exact hx
    · rw [hdp.coord_of_mem_ne hL hL' hLL (Ff_le_left E L' hx)]
      exact one_mem _
  have hmain : ∀ x (hx : x ∈ P ⊔ (sThree p A θ ⊓ thetaOf θ B)),
      ((hdp.coord hL ⟨x, (sup_le hPK hTK) hx⟩ : L) : G) ∈ Z := by
    intro x hx
    have hx' : x ∈ sSup ({P, sThree p A θ ⊓ thetaOf θ B} : Set (Subgroup G)) := by
      rw [sSup_pair]; exact hx
    refine coord_mem_of_mem_sSup hdp hL (X := {P, sThree p A θ ⊓ thetaOf θ B}) ?_ ?_ hx'
    · rintro Y (rfl | rfl)
      · exact hPK
      · exact hTK
    · rintro Y (rfl | rfl) y hy
      · have := coord_mem_of_maximal hV.prime hdp hPK hPab hPr hmax hL hy
        exact Subgroup.mem_sup_left ⟨(inf_le_left : P ≤ V) this, (hdp.coord hL ⟨y, hPK hy⟩).2⟩
      · exact Subgroup.mem_sup_right (hTc y hy)
  intro x hx
  have hxK : x ∈ P ⊔ (sThree p A θ ⊓ thetaOf θ B) := hgen ▸ hdp.le hL hx
  have := hmain x hxK
  rwa [hdp.coord_of_mem hL hx] at this

end VPart

section Ws

variable {p : ℕ} {G : Type u} [Group G] [Finite G]

@[expose] def Vs (V : Subgroup G) (Y : Fin p → Subgroup G) (i : Fin p) : Subgroup G :=
  V ⊓ ⨅ j, ⨅ (_ : j ≠ i), Subgroup.centralizer (Y j : Set G)

@[expose] def Ws (V : Subgroup G) (Y : Fin p → Subgroup G) (i : Fin p) : Subgroup G :=
  Y i ⊔ Vs V Y i

omit [Finite G] in
theorem mem_Vs_iff {V : Subgroup G} {Y : Fin p → Subgroup G} {i : Fin p} {x : G} :
    x ∈ Vs V Y i ↔ x ∈ V ∧ ∀ j, j ≠ i → ∀ y ∈ Y j, y * x = x * y := by
  simp only [Vs, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]

omit [Finite G] in
theorem Vs_le (V : Subgroup G) (Y : Fin p → Subgroup G) (i : Fin p) : Vs V Y i ≤ V :=
  inf_le_left

omit [Finite G] in
theorem Ws_le_centralizer {V : Subgroup G} (hV : IsMulCommutative V) {T : Subgroup G}
    {Y : Fin p → Subgroup G} (hY : IsIDP Y T) {i j : Fin p} (hij : i ≠ j) :
    Ws V Y i ≤ Subgroup.centralizer (Ws V Y j : Set G) := by
  unfold Ws
  rw [CFSG.SignalizerFunctorTheorem.centralizer_sup]
  refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hY.commute i j hij x hx y hy).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((mem_Vs_iff.mp hv).2 i hij x hx).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((mem_Vs_iff.mp hx).2 j hij.symm y hy)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hV.is_comm.comm (⟨y, Vs_le V Y j hy⟩ : V) ⟨x, Vs_le V Y i hx⟩) |>
      fun h => by simpa [Subtype.ext_iff] using h

omit [Finite G] in
theorem Ws_commute {V : Subgroup G} (hV : IsMulCommutative V) {T : Subgroup G}
    {Y : Fin p → Subgroup G} (hY : IsIDP Y T) {i j : Fin p} (hij : i ≠ j) {x y : G}
    (hx : x ∈ Ws V Y i) (hy : y ∈ Ws V Y j) : Commute x y :=
  (Subgroup.mem_centralizer_iff.mp (Ws_le_centralizer hV hY hij hx) y hy).symm

omit [Finite G] in
theorem cj_Vs_le {V : Subgroup G} {Y : Fin p → Subgroup G} (hYinj : Function.Injective Y)
    {a : G} (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hperm : ∀ k, ∃ k', cj a⁻¹ (Y k) = Y k') {i j : Fin p} (hij : cj a (Y i) = Y j) :
    cj a (Vs V Y i) ≤ Vs V Y j := by
  intro x hx
  have hx₀ := mem_Vs_iff.mp (mem_cj_iff.mp hx)
  refine mem_Vs_iff.mpr ⟨?_, fun k hk y hy => ?_⟩
  · have : x ∈ cj a V := mem_cj_iff.mpr hx₀.1
    rwa [cj_eq_of_mem_normalizer haV] at this
  · obtain ⟨k', hk'⟩ := hperm k
    have hy' : a⁻¹ * y * a ∈ Y k' := by
      rw [← hk']
      exact mem_cj_iff.mpr (by rw [show (a⁻¹)⁻¹ * (a⁻¹ * y * a) * a⁻¹ = y by group]; exact hy)
    have hk'i : k' ≠ i := by
      rintro rfl
      apply hk
      apply hYinj
      rw [← hij, ← hk', cj_cj_inv]
    have h1 := hx₀.2 k' hk'i _ hy'
    have h2 : y * x = x * y := by
      calc y * x = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by rw [h1]
        _ = x * y := by group
    exact h2

end Ws

section Main

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem kOf_mem_assoc (hθ : NearFunctor p A θ) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) :
    kOf (θ b) ∈ assoc p A θ :=
  mem_assoc_of_le hθ.prime (apply_mem_assoc hθ hbA hb1) (kOf_le _)
    (Thm41Aux.admits_kOf (hθ.isFunctor.normalized b hbA hb1))

omit [Finite G] in
theorem Decomp.injective {E B : Subgroup G} {Y : Fin p → Subgroup G}
    (hY : Decomp p A θ E B Y) : Function.Injective Y :=
  hY.isIDP.injective hY.ne_bot

omit [Finite G] in
theorem Decomp.cj_Vs {E B V : Subgroup G} {Y : Fin p → Subgroup G} (hY : Decomp p A θ E B Y)
    (hV : A ≤ Subgroup.normalizer (V : Set G)) {a : G} (ha : a ∈ A) {i j : Fin p}
    (hij : cj a (Y i) = Y j) : cj a (Vs V Y i) = Vs V Y j := by
  refine le_antisymm (cj_Vs_le hY.injective (hV ha)
    (fun k => hY.perm a⁻¹ (inv_mem ha) k) hij) ?_
  have h1 : cj a⁻¹ (Y j) = Y i := by rw [← hij, cj_inv_cj]
  have h2 := cj_Vs_le (V := V) hY.injective (hV (inv_mem ha)) (a := a⁻¹)
    (fun k => by simpa only [inv_inv] using hY.perm a ha k) h1
  have h3 := (cj_le_iff (a := a)).mpr h2
  rwa [cj_cj_inv] at h3

omit [Finite G] in
theorem Decomp.cj_Ws {E B V : Subgroup G} {Y : Fin p → Subgroup G} (hY : Decomp p A θ E B Y)
    (hV : A ≤ Subgroup.normalizer (V : Set G)) {a : G} (ha : a ∈ A) {i j : Fin p}
    (hij : cj a (Y i) = Y j) : cj a (Ws V Y i) = Ws V Y j := by
  unfold Ws
  rw [cj_sup, hij, hY.cj_Vs hV ha hij]

theorem Setting.ne_bot_E {E B : Subgroup G} (h : Counterexample p A θ) (hS : Setting p A E B) :
    E ≠ ⊥ := fun hbot => by
  have := hS.hE.2
  rw [hbot, Subgroup.card_bot, pow_one] at this
  exact h.hyp.prime.one_lt.ne this

theorem Setting.ne_bot_B {E B : Subgroup G} (h : Counterexample p A θ) (hS : Setting p A E B) :
    B ≠ ⊥ := fun hbot => by
  have := hS.hB.2
  rw [hbot, Subgroup.card_bot] at this
  have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h.hyp.prime.one_lt
  omega

theorem Decomp.Ws_le_wsub {E B V : Subgroup G} {Y : Fin p → Subgroup G}
    (hY : Decomp p A θ E B Y) (h : Counterexample p A θ) (hS : Setting p A E B)
    (hV : V ∈ assoc p A θ) (i : Fin p) : Ws V Y i ≤ wsub p A θ := by
  have hθ := h.hyp.nearFunctor
  refine sup_le ?_ ((Vs_le V Y i).trans (le_sSup hV))
  have := le_sSup (thetaOf_mem_assoc hθ hS.hB.1 (hS.ne_bot_B h))
  exact (hY.isIDP.le i).trans (inf_le_right.trans this)

theorem Data.exists_le_Ws
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    {Y : Fin p → Subgroup G} (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r)
    (hY : Decomp p A θ E B Y) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : ∃ i, L ≤ Ws V Y i := by
  have hbA := hS.mem_A hb
  have hdp := D.isDirectProduct_lcal hbA hbE
  obtain ⟨e, he⟩ := hY.comp b hb hbE
  refine ⟨e ⟨L, hL⟩, (D.le_inf_sup_Ff hS hV hb hbE hL).trans ?_⟩
  have hFf : Ff p A θ E L = Y (e ⟨L, hL⟩) := he ⟨L, hL⟩
  have hVL : V ⊓ L ≤ Vs V Y (e ⟨L, hL⟩) := by
    intro x hx
    refine mem_Vs_iff.mpr ⟨hx.1, fun k hk y hy => ?_⟩
    have hY' : Y k = Ff p A θ E (e.symm k) := by rw [he (e.symm k), Equiv.apply_symm_apply]
    have hLL' : ((e.symm k : ↥(lcal (θ b))) : Subgroup G) ≠ L := fun heq => hk (by
      have : e.symm k = ⟨L, hL⟩ := Subtype.ext heq
      rw [← this, Equiv.apply_symm_apply])
    have hyL : y ∈ ((e.symm k : ↥(lcal (θ b))) : Subgroup G) :=
      Ff_le_left E _ (hY' ▸ hy)
    exact (hdp.commute L hL _ (e.symm k).2 (Ne.symm hLL') x hx.2 y hyL).eq.symm
  unfold Ws
  rw [hFf, sup_comm]
  exact sup_le_sup_left hVL _

theorem Data.kOf_le_iSup_Ws
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    {Y : Fin p → Subgroup G} (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r)
    (hY : Decomp p A θ E B Y) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    kOf (θ b) ≤ ⨆ i, Ws V Y i := by
  rw [← (D.isDirectProduct_lcal (hS.mem_A hb) hbE).sSup_eq]
  refine sSup_le fun L hL => ?_
  obtain ⟨i, hi⟩ := D.exists_le_Ws hS hV hY hb hbE hL
  exact hi.trans (le_iSup (fun i => Ws V Y i) i)

theorem Data.iSup_Ws_eq
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    {Y : Fin p → Subgroup G} (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r)
    (hY : Decomp p A θ E B Y) : ⨆ i, Ws V Y i = wsub p A θ := by
  have hθ := h.hyp.nearFunctor
  set S : Set (Subgroup G) := {X | ∃ b ∈ B, b ∉ E ∧ X = kOf (θ b)} with hSdef
  have hSsub : S ⊆ assoc p A θ := by
    rintro _ ⟨b, hb, hbE, rfl⟩
    exact kOf_mem_assoc hθ (hS.mem_A hb) (ne_one_of_not_mem hbE)
  have hSle : sSup S ≤ ⨆ i, Ws V Y i := by
    refine sSup_le ?_
    rintro _ ⟨b, hb, hbE, rfl⟩
    exact D.kOf_le_iSup_Ws hS hV hY hb hbE
  have hup : ⨆ i, Ws V Y i ≤ wsub p A θ := iSup_le fun i => hY.Ws_le_wsub h hS hV.mem i
  rcases h.sSup_mem_assoc_or_le hSsub with hle | hmem
  · refine le_antisymm hup ?_
    exact (sSup_le hle).trans hSle
  · exfalso
    obtain ⟨b₀, hb₀, hb₀E⟩ := hS.exists_mem_not_mem h
    obtain ⟨e, heA, he1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one hθ.prime hS.hE
    have hb₀A := hS.mem_A hb₀
    have hb₀1 := ne_one_of_not_mem hb₀E
    have heE : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
    have hb₁B : e * b₀ ∈ B := mul_mem (hS.hEB heE) hb₀
    have hb₁E : e * b₀ ∉ Subgroup.zpowers e := fun hmem' => hb₀E (by
      have := mul_mem (inv_mem heE) hmem'
      simpa using this)
    have hb₁A := hS.mem_A hb₁B
    have hb₁1 := ne_one_of_not_mem hb₁E
    have hK0 : kOf (θ b₀) ≤ sSup S := le_sSup ⟨b₀, hb₀, hb₀E, rfl⟩
    have hK1 : kOf (θ (e * b₀)) ≤ sSup S := le_sSup ⟨e * b₀, hb₁B, hb₁E, rfl⟩
    have hX : sSup S ≤ θ b₀ := D.le_of_mem b₀ hb₀A hb₀E (sSup S) hmem hK0
    have hK1le : kOf (θ (e * b₀)) ≤ θ e := by
      intro x hx
      have hx0 : x ∈ θ b₀ := hX (hK1 hx)
      have hx1 : x ∈ θ (e * b₀) := kOf_le _ hx
      have hc0 : Commute x b₀ :=
        Subgroup.mem_centralizer_singleton_iff.mp (hθ.isFunctor.le_centralizer b₀ hb₀A hb₀1 hx0)
      have hc1 : Commute x (e * b₀) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (hθ.isFunctor.le_centralizer (e * b₀) hb₁A hb₁1 hx1)
      have hce : Commute x e := by
        have := hc1.mul_right hc0.inv_right
        simpa using this
      exact hθ.isFunctor.balance (e * b₀) hb₁A hb₁1 e heA he1
        ⟨hx1, Subgroup.mem_centralizer_singleton_iff.mpr hce⟩
    have hsol : Group.IsSolvable ↥(kOf (θ (e * b₀))) := by
      have := D.hEs
      rw [hθ.isFunctor.thetaOf_zpowers heA he1] at this
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK1le)
    exact h.not_isSolvable_kOf (D.cset_apply hb₁A hb₁E) hsol

theorem Decomp.isIDP_Ws
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    {Y : Fin p → Subgroup G} (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r)
    (hY : Decomp p A θ E B Y) : IsIDP (Ws V Y) (wsub p A θ) := by
  have hW := D.iSup_Ws_eq hS hV hY
  refine ⟨fun i j hij x hx y hy => Ws_commute hV.comm hY.isIDP hij hx hy, ?_, hW⟩
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxi, hxj⟩ := Subgroup.mem_inf.mp hx
  have hle : (⨆ j, ⨆ (_ : j ≠ i), Ws V Y j) ≤ Subgroup.centralizer (Ws V Y i : Set G) :=
    iSup₂_le fun j hj => Ws_le_centralizer hV.comm hY.isIDP hj
  have hxC : x ∈ Subgroup.centralizer (Ws V Y i : Set G) := hle hxj
  have hWle : (⨆ k, Ws V Y k) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine iSup_le fun k => ?_
    by_cases hki : k = i
    · subst hki
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxC w hw
    · intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (Ws_le_centralizer hV.comm hY.isIDP (Ne.symm hki) hxi)
        w hw
  have hxW : x ∈ wsub p A θ := by
    rw [← hW]
    exact (le_iSup (fun k => Ws V Y k) i) hxi
  have hxZ : x ∈ wsub p A θ ⊓ Subgroup.centralizer (wsub p A θ : Set G) := by
    refine ⟨hxW, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [← hW] at hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWle hw)
  rw [h.center_sSup_eq_bot] at hxZ
  exact hxZ

omit [Finite G] in
theorem Decomp.Ws_ne_bot {E B : Subgroup G} {Y : Fin p → Subgroup G}
    (hY : Decomp p A θ E B Y) (V : Subgroup G) (i : Fin p) : Ws V Y i ≠ ⊥ := fun hbot =>
  hY.ne_bot i (le_bot_iff.mp (hbot ▸ le_sup_left))

theorem thm71_of_data
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ} (D : Data h E)
    (hS : Setting p A E B) (hV : VData p A θ E V r) :
    ∃ W : Fin p → Subgroup G, Function.Injective W ∧
      IsDirectProduct (Set.range W) (wsub p A θ) ∧
      (∀ a ∈ A, ∀ i, ∃ j, (W i).map (MulAut.conj a).toMonoidHom = W j) ∧
      (∀ i j, ∃ a ∈ A, (W i).map (MulAut.conj a).toMonoidHom = W j) ∧
      (∀ i, A ⊓ Subgroup.normalizer (W i : Set G) = B) ∧
      ∀ b ∈ B, b ∉ E →
        IsDirectProduct (Set.range fun i => W i ⊓ kOf (θ b)) (kOf (θ b)) := by
  obtain ⟨Y, hY⟩ := D.exists_decomp hS
  have hIDP := hY.isIDP_Ws D hS hV
  have hinj : Function.Injective (Ws V Y) := hIDP.injective (hY.Ws_ne_bot V)
  have hVA : A ≤ Subgroup.normalizer (V : Set G) := hV.mem.1
  have hperm : ∀ a ∈ A, ∀ i, ∃ j, cj a (Ws V Y i) = Ws V Y j := by
    intro a ha i
    obtain ⟨j, hj⟩ := hY.perm a ha i
    exact ⟨j, hY.cj_Ws hVA ha hj⟩
  refine ⟨Ws V Y, hinj, hIDP.isDirectProduct_range, hperm, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨a, ha, haij⟩ := hY.trans i j
    exact ⟨a, ha, hY.cj_Ws hVA ha haij⟩
  · intro i
    refine le_antisymm ?_ (le_inf hS.hB.1 fun β hβ => ?_)
    · rintro a ⟨ha, haN⟩
      obtain ⟨j, hj⟩ := hY.perm a ha i
      have h1 := hY.cj_Ws hVA ha hj
      rw [cj_eq_of_mem_normalizer haN] at h1
      have hji : j = i := (hinj h1).symm
      subst hji
      exact hY.stab a ha j hj
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (hY.cj_Ws hVA (hS.hB.1 hβ) (hY.fixed β hβ i))
  · intro b hb hbE
    have hbA := hS.mem_A hb
    refine IsIDP.isDirectProduct_range ⟨fun i j hij x hx y hy =>
      hIDP.commute i j hij x hx.1 y hy.1, hIDP.indep.mono fun i => inf_le_left, ?_⟩
    refine le_antisymm (iSup_le fun i => inf_le_right) ?_
    refine le_trans (le_of_eq (D.isDirectProduct_lcal hbA hbE).sSup_eq.symm)
      (sSup_le fun L hL => ?_)
    obtain ⟨i, hi⟩ := D.exists_le_Ws hS hV hY hb hbE hL
    exact le_iSup_of_le i (le_inf hi ((D.isDirectProduct_lcal hbA hbE).le hL))

end Main

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
