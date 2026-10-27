module

public import CFSG.Quasithin.Background.RonanE111Semi
public import CFSG.Quasithin.EmptyFaithful.E111RMemA
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def actT (T A : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (A : Set G)

@[expose] def actE (T A J : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (A : Set G)

structure JData (E J D Y : Subgroup G) (𝒟 : Set (Subgroup G)) : Prop where
  SM : SemisimpleMod E D Y 𝒟
  nonempty : 𝒟.Nonempty
  D_le : D ≤ J
  perf : ⁅D, D⁆ = D
  Ysolv : Group.IsSolvable ↥Y
  Y_normal : (Y.subgroupOf D).Normal
  E_Y : ∀ e ∈ E, A1b.conjSub e Y = Y

variable [Finite G] {X T A J C : Subgroup G} [Fintype ↥C]

@[expose] noncomputable def dimg (hC : DiagComm J C) (U : Subgroup G) : Subgroup G :=
  (U.subgroupOf J).map (diagHom J C hC)

theorem mem_dimg_iff (hC : DiagComm J C) {U : Subgroup G} {x : G} :
    x ∈ dimg hC U ↔ ∃ u : ↥J, (u : G) ∈ U ∧ diagHom J C hC u = x := by
  unfold dimg
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr hu, rfl⟩

theorem dimg_mono (hC : DiagComm J C) {U U' : Subgroup G} (h : U ≤ U') : dimg hC U ≤ dimg hC U' := by
  unfold dimg
  apply Subgroup.map_mono
  intro u hu
  exact Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hu))

theorem dimg_J (h : DiagSetting X T A J C) : dimg h.diagComm J = diagSub J C h.diagComm := by
  unfold dimg diagSub
  rw [Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem mem_actT_iff {k : G} : k ∈ actT T A ↔ k ∈ T ∧ k ∈ Subgroup.centralizer (A : Set G) := by
  simp only [actT, Subgroup.mem_inf]

theorem mem_actE_iff {e : G} : e ∈ actE T A J ↔
    e ∈ T ∧ e ∈ Subgroup.normalizer (J : Set G) ∧ e ∈ Subgroup.centralizer (A : Set G) := by
  simp only [actE, Subgroup.mem_inf, and_assoc]

theorem dimg_le_diagSub (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) :
    dimg h.diagComm U ≤ diagSub J C h.diagComm := by
  rw [← dimg_J h]
  exact dimg_mono h.diagComm hU

theorem dimg_fix (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {c : G} (hc : c ∈ C) :
    A1b.conjSub c (dimg h.diagComm U) = dimg h.diagComm U := by
  refine E111R.conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_iff.mp (h.le_centralizer_diag hc) x (dimg_le_diagSub h hU hx)

theorem conjSub_dimg_le (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {e : G}
    (he : e ∈ Subgroup.normalizer (J : Set G)) (heC : ∀ c ∈ C, e * c = c * e) :
    A1b.conjSub e (dimg h.diagComm U) ≤ dimg h.diagComm (A1b.conjSub e U) := by
  intro x hx
  rw [A1b.mem_conjSub_iff] at hx
  obtain ⟨u, hu, hux⟩ := (mem_dimg_iff h.diagComm).mp hx
  have hJ : e * (u : G) * e⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp he u).mp u.2
  refine (mem_dimg_iff h.diagComm).mpr ⟨⟨e * (u : G) * e⁻¹, hJ⟩, ?_, ?_⟩
  · rw [A1b.mem_conjSub_iff]
    show e⁻¹ * (e * (u : G) * e⁻¹) * e ∈ U
    have hid : e⁻¹ * (e * (u : G) * e⁻¹) * e = (u : G) := by group
    rw [hid]
    exact hu
  · rw [← conj_diagHom_of_comm h.diagComm u he heC, hux]
    group

theorem conj_dimg_eq (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {e : G}
    (he : e ∈ Subgroup.normalizer (J : Set G)) (heC : ∀ c ∈ C, e * c = c * e) :
    A1b.conjSub e (dimg h.diagComm U) = dimg h.diagComm (A1b.conjSub e U) := by
  refine le_antisymm (conjSub_dimg_le h hU he heC) ?_
  have hV : A1b.conjSub e U ≤ J :=
    (A1b.conjSub_mono e hU).trans (le_of_eq (E111R.conjSub_eq_of_mem_normalizer he))
  have he' : e⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ he
  have heC' : ∀ c ∈ C, e⁻¹ * c = c * e⁻¹ := fun c hc =>
    Commute.inv_left (show Commute e c from heC c hc)
  have key := conjSub_dimg_le h hV he' heC'
  have hU' : A1b.conjSub e⁻¹ (A1b.conjSub e U) = U := by
    rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  rw [hU'] at key
  have key2 := A1b.conjSub_mono e key
  rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at key2
  exact key2

theorem block_dichotomy (h : DiagSetting X T A J C) {k : G} (hk : k ∈ actT T A) :
    (∃ e ∈ actE T A J, ∃ c ∈ C, ∃ c' ∈ C, k = c' * e * c⁻¹) ∨
      (∀ x ∈ conjSub k (diagSub J C h.diagComm), ∀ y ∈ diagSub J C h.diagComm, x * y = y * x) := by
  obtain ⟨hkT, hkA⟩ := mem_actT_iff.mp hk
  by_cases hex : ∃ c ∈ C, ∃ c' ∈ C, A1b.conjSub (k * c) J = A1b.conjSub c' J
  · left
    obtain ⟨c, hc, c', hc', heq⟩ := hex
    set m := c'⁻¹ * (k * c) with hm
    have hmS : m ∈ Subgroup.normalizer (J : Set G) := by
      apply mem_normalizer_of_conjSub_eq
      rw [hm, A1b.conjSub_mul, heq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    have hmT : m ∈ T := by
      rw [hm]
      exact T.mul_mem (T.inv_mem (h.AT (h.CA hc'))) (T.mul_mem hkT (h.AT (h.CA hc)))
    have hmA : m ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * c'⁻¹ = c'⁻¹ * a := h.comm ha (h.CA (C.inv_mem hc'))
      have h2 : a * k = k * a := Subgroup.mem_centralizer_iff.mp hkA a ha
      have h3 : a * c = c * a := h.comm ha (h.CA hc)
      rw [hm]
      calc a * (c'⁻¹ * (k * c)) = (a * c'⁻¹) * (k * c) := by group
        _ = (c'⁻¹ * a) * (k * c) := by rw [h1]
        _ = c'⁻¹ * ((a * k) * c) := by group
        _ = c'⁻¹ * ((k * a) * c) := by rw [h2]
        _ = c'⁻¹ * (k * (a * c)) := by group
        _ = c'⁻¹ * (k * (c * a)) := by rw [h3]
        _ = c'⁻¹ * (k * c) * a := by group
    refine ⟨m, mem_actE_iff.mpr ⟨hmT, hmS, hmA⟩, c, hc, c', hc', ?_⟩
    rw [hm]
    group
  · right
    push Not at hex
    have hcomm := commute_conj_diagHom h.diagComm (h.commute_of_ne fun c hc c' hc' =>
      hex c hc c' hc')
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y

theorem conjSub_dimg_stab (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {e : G}
    (he : e ∈ actE T A J) {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) :
    conjSub (c' * e * c⁻¹) (dimg h.diagComm U) = dimg h.diagComm (conjSub e U) := by
  change A1b.conjSub (c' * e * c⁻¹) (dimg h.diagComm U) = dimg h.diagComm (A1b.conjSub e U)
  obtain ⟨-, heN, heA⟩ := mem_actE_iff.mp he
  have heC : ∀ d ∈ C, e * d = d * e := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp heA d (h.CA hd)).symm
  have hV : A1b.conjSub e U ≤ J :=
    (A1b.conjSub_mono e hU).trans (le_of_eq (E111R.conjSub_eq_of_mem_normalizer heN))
  rw [A1b.conjSub_mul, A1b.conjSub_mul, dimg_fix h hU (C.inv_mem hc), conj_dimg_eq h hU heN heC,
    dimg_fix h hV hc']

@[expose] noncomputable def wrN (hC : DiagComm J C) (T A D : Subgroup G) : Subgroup G :=
  ⨆ k ∈ actT T A, conjSub k (dimg hC D)

@[expose] noncomputable def wrY (hC : DiagComm J C) (T A Y : Subgroup G) : Subgroup G :=
  ⨆ k ∈ actT T A, conjSub k (dimg hC Y)

@[expose] noncomputable def wrFam (hC : DiagComm J C) (T A S₀ Y : Subgroup G) : Set (Subgroup G) :=
  (fun k : G => conjSub k (dimg hC S₀ ⊔ wrY hC T A Y)) '' (actT T A : Set G)

theorem wr_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hx' : x ∈ ⨆ b : Bool, cond b H K := by
    rw [iSup_bool_eq]
    exact hx
  refine Subgroup.iSup_induction (fun b : Bool => cond b H K)
    (C := fun x => ∃ h ∈ H, ∃ k ∈ K, h * k = x) hx' ?_
    ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩ ?_
  · intro b y hy
    cases b
    · exact ⟨1, H.one_mem, y, hy, one_mul y⟩
    · exact ⟨y, hy, 1, K.one_mem, mul_one y⟩
  · rintro a b ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
    refine ⟨h * h', H.mul_mem hh hh', (h'⁻¹ * k * h'⁻¹⁻¹) * k', ?_, ?_⟩
    · exact K.mul_mem (hHK h'⁻¹ (H.inv_mem hh') k hk) hk'
    · group

theorem wr_commutator_sup_le {Y P₁ P₂ : Subgroup G}
    (h₁ : ∀ p ∈ P₁, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) (h₂ : ∀ p ∈ P₂, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y)
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b * a⁻¹ * b⁻¹ ∈ Y) :
    ⁅P₁ ⊔ Y, P₂ ⊔ Y⁆ ≤ Y := by
  refine Subgroup.commutator_le.mpr fun s hs t ht => ?_
  obtain ⟨a, ha, y, hy, rfl⟩ := wr_mem_sup h₁ hs
  obtain ⟨b, hb, y', hy', rfl⟩ := wr_mem_sup h₂ ht
  have hy1 : b⁻¹ * y * b ∈ Y := by
    have h := h₂ b⁻¹ (P₂.inv_mem hb) y hy
    rwa [inv_inv] at h
  have hW : (b⁻¹ * y * b) * (y' * y⁻¹) ∈ Y := Y.mul_mem hy1 (Y.mul_mem hy' (Y.inv_mem hy))
  have hV : a * ((b⁻¹ * y * b) * (y' * y⁻¹)) * a⁻¹ ∈ Y := h₁ a ha _ hW
  have hX : a * ((b⁻¹ * y * b) * (y' * y⁻¹)) * a⁻¹ * y'⁻¹ ∈ Y := Y.mul_mem hV (Y.inv_mem hy')
  have hZ : b * (a * ((b⁻¹ * y * b) * (y' * y⁻¹)) * a⁻¹ * y'⁻¹) * b⁻¹ ∈ Y := h₂ b hb _ hX
  rw [commutatorElement_def]
  have key : a * y * (b * y') * (a * y)⁻¹ * (b * y')⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * ((b⁻¹ * y * b) * (y' * y⁻¹)) * a⁻¹ * y'⁻¹) * b⁻¹) := by
    group
  rw [key]
  exact Y.mul_mem (hcomm a ha b hb) hZ

theorem wr_isSolvable_sup {V W : Subgroup G} (hV : Group.IsSolvable ↥V)
    (hW : Group.IsSolvable ↥W) (hc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) :
    Group.IsSolvable ↥(V ⊔ W) := by
  haveI := hV
  haveI := hW
  let φ : ↥V × ↥W →* G := MonoidHom.noncommCoprod V.subtype W.subtype
    (fun m n => hc (m : G) m.2 (n : G) n.2)
  have hr : φ.range = V ⊔ W := by
    apply le_antisymm
    · rintro _ ⟨⟨v, w⟩, rfl⟩
      exact Subgroup.mul_mem_sup v.2 w.2
    · intro x hx
      have hcW : ∀ h ∈ V, ∀ k ∈ W, h * k * h⁻¹ ∈ W := fun h hh k hk => by
        have e := hc h hh k hk
        have e' : h * k * h⁻¹ = k := by rw [e]; group
        rw [e']
        exact hk
      obtain ⟨v, hv, w, hw, rfl⟩ := wr_mem_sup hcW hx
      exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), rfl⟩
  have hsurj : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
  have h1 : Group.IsSolvable ↥φ.range := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_surjective (f := (MulEquiv.subgroupCongr hr).toMonoidHom)
    (MulEquiv.subgroupCongr hr).surjective

theorem wr_isSolvable_finset (s : Finset (Subgroup G))
    (hsol : ∀ V ∈ s, Group.IsSolvable ↥V)
    (hcomm : ∀ V ∈ s, ∀ V' ∈ s, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x) :
    Group.IsSolvable ↥(sSup (s : Set (Subgroup G))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, sSup_empty]
    infer_instance
  | insert a s ha ih =>
    have hsol' : ∀ V ∈ s, Group.IsSolvable ↥V := fun V hV =>
      hsol V (Finset.mem_insert_of_mem hV)
    have hcomm' : ∀ V ∈ s, ∀ V' ∈ s, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x :=
      fun V hV V' hV' hne =>
        hcomm V (Finset.mem_insert_of_mem hV) V' (Finset.mem_insert_of_mem hV') hne
    have ih' := ih hsol' hcomm'
    rw [Finset.coe_insert, sSup_insert]
    refine wr_isSolvable_sup (hsol a (Finset.mem_insert_self a s)) ih' ?_
    have hcen : sSup (s : Set (Subgroup G)) ≤ Subgroup.centralizer (a : Set G) := by
      refine sSup_le fun V hV => ?_
      have hVs : V ∈ s := by exact_mod_cast hV
      have hne : a ≠ V := fun e => ha (e ▸ hVs)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcomm a (Finset.mem_insert_self a s) V (Finset.mem_insert_of_mem hVs) hne x hx y hy
    intro v hv w hw
    exact Subgroup.mem_centralizer_iff.mp (hcen hw) v hv

theorem wr_isSolvable_sSup {𝒱 : Set (Subgroup G)} (hsol : ∀ V ∈ 𝒱, Group.IsSolvable ↥V)
    (hcomm : ∀ V ∈ 𝒱, ∀ V' ∈ 𝒱, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x) :
    Group.IsSolvable ↥(sSup 𝒱) := by
  have hfin : 𝒱.Finite := Set.toFinite 𝒱
  have hfin' : (hfin.toFinset : Set (Subgroup G)) = 𝒱 := hfin.coe_toFinset
  rw [← hfin']
  refine wr_isSolvable_finset hfin.toFinset ?_ ?_
  · intro V hV
    exact hsol V ((Set.Finite.mem_toFinset hfin).mp hV)
  · intro V hV V' hV' hne
    exact hcomm V ((Set.Finite.mem_toFinset hfin).mp hV) V'
      ((Set.Finite.mem_toFinset hfin).mp hV') hne

theorem wr_isSylowIn_iSup {ι : Type*} [Finite ι] {T : Subgroup G} (hT2 : IsPGroup 2 T)
    {F : ι → Subgroup G}
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hind : _root_.iSupIndep F) (hF : ∀ i, IsSylowIn 2 (T ⊓ F i) (F i)) :
    IsSylowIn 2 (T ⊓ ⨆ i, F i) (⨆ i, F i) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype ι := Fintype.ofFinite _
  set K : ι → Subgroup G := fun i => T ⊓ F i with hK
  have hKc : Pairwise fun i j : ι => ∀ x y : G, x ∈ K i → y ∈ K j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x y hx.2 hy.2
  have hKi : _root_.iSupIndep K := hind.mono fun i => inf_le_right
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hKc) hKi
  set P := ⨆ i, K i with hP
  have hcardP : Nat.card ↥P = ∏ i : ι, Nat.card ↥(K i) := by
    rw [hP, ← Subgroup.noncommPiCoprod_range (hcomm := hKc),
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
  have hPE : P ≤ ⨆ i, F i := iSup_le fun i => inf_le_right.trans (le_iSup F i)
  have hPT : P ≤ T := iSup_le fun i => inf_le_left
  have hinj' := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hcardE : Nat.card ↥(⨆ i, F i) = ∏ i : ι, Nat.card ↥(F i) := by
    rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm),
      ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv, Nat.card_pi]
  have hSyl : IsSylowIn 2 P (⨆ i, F i) := by
    refine isSylowIn_of_card_eq hPE ?_
    rw [hcardP, hcardE, Nat.factorization_prod fun i _ => Nat.card_pos.ne']
    rw [Finset.sum_apply', ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => (hF i).card_eq
  refine ⟨inf_le_right, hT2.to_le inf_le_left, fun h2 => hSyl.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P (T ⊓ ⨆ i, F i) (⨆ i, F i) (le_inf hPT hPE) inf_le_right]
  exact Dvd.dvd.mul_left h2 _

theorem wrY_eq (hC : DiagComm J C) (T A Y : Subgroup G) :
    wrY hC T A Y = ⨆ k ∈ actT T A, A1b.conjSub k (dimg hC Y) := rfl

theorem wrN_eq (hC : DiagComm J C) (T A D : Subgroup G) :
    wrN hC T A D = ⨆ k ∈ actT T A, A1b.conjSub k (dimg hC D) := rfl

theorem wrFam_eq (hC : DiagComm J C) (T A S₀ Y : Subgroup G) :
    wrFam hC T A S₀ Y = (fun k : G => A1b.conjSub k (dimg hC S₀ ⊔ wrY hC T A Y)) ''
      (actT T A : Set G) := rfl

theorem dimg_commutator_mem (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {x : G}
    (hx : x ∈ ⁅U, U⁆) :
    ∃ hxJ : x ∈ J, diagHom J C h.diagComm ⟨x, hxJ⟩ ∈
      ⁅dimg h.diagComm U, dimg h.diagComm U⁆ := by
  set Q := ⁅dimg h.diagComm U, dimg h.diagComm U⁆ with hQ
  set M : Subgroup G := (Q.comap (diagHom J C h.diagComm)).map J.subtype with hM
  have hle : ⁅U, U⁆ ≤ M := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have ha' : diagHom J C h.diagComm ⟨a, hU ha⟩ ∈ dimg h.diagComm U :=
      (mem_dimg_iff h.diagComm).mpr ⟨⟨a, hU ha⟩, ha, rfl⟩
    have hb' : diagHom J C h.diagComm ⟨b, hU hb⟩ ∈ dimg h.diagComm U :=
      (mem_dimg_iff h.diagComm).mpr ⟨⟨b, hU hb⟩, hb, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⁅(⟨a, hU ha⟩ : ↥J), ⟨b, hU hb⟩⁆, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator ha' hb'
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp (hle hx)
  rw [Subgroup.mem_comap] at hp
  exact ⟨p.2, hp⟩

theorem wr_dimg_le_normalizer (h : DiagSetting X T A J C) {U V : Subgroup G} (hU : U ≤ J)
    (hV : V ≤ J) (hn : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ ∈ V) :
    dimg h.diagComm U ≤ Subgroup.normalizer (dimg h.diagComm V : Set G) := by
  have key : ∀ x ∈ dimg h.diagComm U, ∀ z ∈ dimg h.diagComm V,
      x * z * x⁻¹ ∈ dimg h.diagComm V := by
    intro x hx z hz
    obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
    obtain ⟨v, hv, rfl⟩ := (mem_dimg_iff h.diagComm).mp hz
    refine (mem_dimg_iff h.diagComm).mpr ⟨u * v * u⁻¹, hn u hu v hv, ?_⟩
    rw [map_mul, map_mul, map_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact key x hx z hz
  · intro hz
    have h1 := key x⁻¹ (Subgroup.inv_mem _ hx) _ hz
    have e : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
    rw [e] at h1
    exact h1

theorem wr_actE_normalizer {e : G} (he : e ∈ actE T A J) :
    e ∈ Subgroup.normalizer (J : Set G) :=
  (mem_actE_iff.mp he).2.1

theorem wr_actE_comm (h : DiagSetting X T A J C) {e : G} (he : e ∈ actE T A J) :
    ∀ c ∈ C, e * c = c * e := fun c hc =>
  (Subgroup.mem_centralizer_iff.mp (mem_actE_iff.mp he).2.2 c (h.CA hc)).symm

theorem wr_conjSub_dimg (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) {c c' e : G}
    (he : e ∈ actE T A J) (hc : c ∈ C) (hc' : c' ∈ C) :
    A1b.conjSub (c' * e * c⁻¹) (dimg h.diagComm U) = dimg h.diagComm (A1b.conjSub e U) :=
  conjSub_dimg_stab h hU he hc hc'

theorem wr_block_mem (h : DiagSetting X T A J C) {k : G} (hk : k ∈ actT T A) :
    A1b.conjSub k (diagSub J C h.diagComm) ∈ diagFam T A J C h.diagComm :=
  ⟨⟨k, hk⟩, rfl⟩

theorem wr_I_mem (h : DiagSetting X T A J C) :
    diagSub J C h.diagComm ∈ diagFam T A J C h.diagComm := by
  have := wr_block_mem h (actT T A).one_mem
  rwa [A1b.conjSub_one] at this

theorem wr_block_comm (h : DiagSetting X T A J C) {k k' : G} (hk : k ∈ actT T A)
    (hk' : k' ∈ actT T A) (hne : A1b.conjSub k (diagSub J C h.diagComm) ≠
      A1b.conjSub k' (diagSub J C h.diagComm)) :
    ∀ x ∈ A1b.conjSub k (diagSub J C h.diagComm), ∀ y ∈ A1b.conjSub k' (diagSub J C h.diagComm),
      x * y = y * x :=
  h.semiFam.comm _ (wr_block_mem h hk) _ (wr_block_mem h hk') hne

theorem wr_conjSub_I_of_decomp (h : DiagSetting X T A J C) {k e c c' : G} (he : e ∈ actE T A J)
    (hc : c ∈ C) (hc' : c' ∈ C) (hk : k = c' * e * c⁻¹) :
    A1b.conjSub k (diagSub J C h.diagComm) = diagSub J C h.diagComm := by
  obtain ⟨-, heN, -⟩ := mem_actE_iff.mp he
  rw [hk, A1b.conjSub_mul, A1b.conjSub_mul, h.conjSub_diag_of_mem (C.inv_mem hc),
    h.conjSub_diag_of_comm heN (wr_actE_comm h he), h.conjSub_diag_of_mem hc']

theorem wr_stab_decomp (h : DiagSetting X T A J C) {n : G} (hn : n ∈ actT T A)
    (hI : A1b.conjSub n (diagSub J C h.diagComm) = diagSub J C h.diagComm) :
    ∃ e ∈ actE T A J, ∃ c ∈ C, ∃ c' ∈ C, n = c' * e * c⁻¹ := by
  rcases block_dichotomy h hn with H | H
  · exact H
  · exfalso
    obtain ⟨a, b, hab⟩ := h.diag_nonabelian
    apply hab
    have ha : (a : G) ∈ A1b.conjSub n (diagSub J C h.diagComm) := by
      rw [hI]
      exact a.2
    have hb : (b : G) ∈ diagSub J C h.diagComm := b.2
    exact Subtype.ext (H _ ha _ hb)

theorem wr_block_comm_I (h : DiagSetting X T A J C) {k : G} (hk : k ∈ actT T A)
    (hkI : A1b.conjSub k (diagSub J C h.diagComm) ≠ diagSub J C h.diagComm) :
    ∀ x ∈ A1b.conjSub k (diagSub J C h.diagComm), ∀ y ∈ diagSub J C h.diagComm,
      x * y = y * x := by
  rcases block_dichotomy h hk with H | H
  · obtain ⟨e, he, c, hc, c', hc', hke⟩ := H
    exact absurd (wr_conjSub_I_of_decomp h he hc hc' hke) hkI
  · exact H

theorem wr_stab_dimg (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e U = U) {k : G} (hk : k ∈ actT T A)
    (hI : A1b.conjSub k (diagSub J C h.diagComm) = diagSub J C h.diagComm) :
    A1b.conjSub k (dimg h.diagComm U) = dimg h.diagComm U := by
  obtain ⟨e, he, c, hc, c', hc', rfl⟩ := wr_stab_decomp h hk hI
  rw [wr_conjSub_dimg h hU he hc hc', hE e he]

theorem wr_same_block_dimg (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e U = U) {k k' : G} (hk : k ∈ actT T A)
    (hk' : k' ∈ actT T A)
    (hI : A1b.conjSub k (diagSub J C h.diagComm) = A1b.conjSub k' (diagSub J C h.diagComm)) :
    A1b.conjSub k (dimg h.diagComm U) = A1b.conjSub k' (dimg h.diagComm U) := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = k⁻¹ * k' := ⟨_, rfl⟩
  have hn : n ∈ actT T A := by
    rw [hn_def]
    exact (actT T A).mul_mem ((actT T A).inv_mem hk) hk'
  have hnI : A1b.conjSub n (diagSub J C h.diagComm) = diagSub J C h.diagComm := by
    rw [hn_def, A1b.conjSub_mul, ← hI, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  obtain ⟨e, he, c, hc, c', hc', hne⟩ := wr_stab_decomp h hn hnI
  have hnD : A1b.conjSub n (dimg h.diagComm U) = dimg h.diagComm U := by
    rw [hne, wr_conjSub_dimg h hU he hc hc', hE e he]
  have hkk' : k' = k * n := by rw [hn_def]; group
  rw [hkk', A1b.conjSub_mul, hnD]

theorem wr_inf_wrY (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) :
    diagSub J C h.diagComm ⊓ wrY h.diagComm T A Y ≤ dimg h.diagComm Y := by
  have hI_mem := wr_I_mem h
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥(diagFam T A J C h.diagComm), (i₀ : Subgroup G) = diagSub J C h.diagComm :=
    ⟨⟨_, hI_mem⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = ⨆ (j : ↥(diagFam T A J C h.diagComm))
      (_ : j ≠ i₀), (j : Subgroup G) := ⟨_, rfl⟩
  have hdisj : Disjoint (diagSub J C h.diagComm) B := by
    rw [hB, ← hi₀]
    exact h.semiFam.iSupIndep i₀
  have hIB : diagSub J C h.diagComm ⊓ B = ⊥ := disjoint_iff.mp hdisj
  have hBc : B ≤ Subgroup.centralizer (diagSub J C h.diagComm : Set G) := by
    rw [hB]
    refine iSup₂_le fun j hj => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h.semiFam.comm (diagSub J C h.diagComm) hI_mem (j : Subgroup G) j.2
      (fun e => hj (Subtype.ext (e.symm.trans hi₀.symm))) x hx y hy
  have hYB : wrY h.diagComm T A Y ≤ dimg h.diagComm Y ⊔ B := by
    rw [wrY_eq]
    refine iSup₂_le fun k hk => ?_
    by_cases hkI : A1b.conjSub k (diagSub J C h.diagComm) = diagSub J C h.diagComm
    · rw [wr_stab_dimg h hYJ hE hk hkI]
      exact le_sup_left
    · refine le_sup_of_le_right (le_trans (A1b.conjSub_mono k (dimg_le_diagSub h hYJ)) ?_)
      rw [hB]
      exact le_iSup₂_of_le (⟨A1b.conjSub k (diagSub J C h.diagComm), wr_block_mem h hk⟩ :
        ↥(diagFam T A J C h.diagComm))
        (fun e => hkI ((congrArg Subtype.val e).trans hi₀)) le_rfl
  have hHK : ∀ y ∈ dimg h.diagComm Y, ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    have hyb : y * b = b * y :=
      Subgroup.mem_centralizer_iff.mp (hBc hb) y (dimg_le_diagSub h hYJ hy)
    rw [hyb, mul_inv_cancel_right]
    exact hb
  intro x hx
  obtain ⟨hxI, hxW⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, k, hk, hyk⟩ := wr_mem_sup hHK (hYB hxW)
  have hkI : k ∈ diagSub J C h.diagComm := by
    have e : k = y⁻¹ * x := by rw [← hyk]; group
    rw [e]
    exact (diagSub J C h.diagComm).mul_mem
      ((diagSub J C h.diagComm).inv_mem (dimg_le_diagSub h hYJ hy)) hxI
  have hk1 : k = 1 := by
    have hmem : k ∈ diagSub J C h.diagComm ⊓ B := Subgroup.mem_inf.mpr ⟨hkI, hk⟩
    rw [hIB, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hk1, mul_one] at hyk
  rw [← hyk]
  exact hy

theorem wr_join_induction {ι : Type*} (s : Set ι) (F : ι → Subgroup G) {P : G → Prop} {x : G}
    (hx : x ∈ ⨆ i ∈ s, F i) (mem : ∀ i ∈ s, ∀ y ∈ F i, P y) (one : P 1)
    (mul : ∀ a b, P a → P b → P (a * b)) : P x := by
  refine Subgroup.iSup_induction (fun i : ι => ⨆ (_ : i ∈ s), F i) (C := P) hx ?_ one mul
  intro i y hy
  by_cases hi : i ∈ s
  · rw [iSup_pos hi] at hy
    exact mem i hi y hy
  · rw [iSup_neg hi, Subgroup.mem_bot] at hy
    rw [hy]
    exact one

theorem wr_conjSub_le_of_mem {K W : Subgroup G} {g : G} (hg : g ∈ K) :
    A1b.conjSub g (⨆ k ∈ K, A1b.conjSub k W) ≤ ⨆ k ∈ K, A1b.conjSub k W := by
  rw [conjSub_iSup₂]
  refine iSup₂_le fun k hk => ?_
  rw [← A1b.conjSub_mul]
  exact le_iSup₂_of_le (g * k) (K.mul_mem hg hk) le_rfl

theorem wr_conjSub_eq_of_mem {K W : Subgroup G} {g : G} (hg : g ∈ K) :
    A1b.conjSub g (⨆ k ∈ K, A1b.conjSub k W) = ⨆ k ∈ K, A1b.conjSub k W :=
  E111R.conjSub_eq_of_mem_normalizer
    (E111R.mem_normalizer_of_conjSub_le (wr_conjSub_le_of_mem hg)
      (wr_conjSub_le_of_mem (K.inv_mem hg)))

theorem wr_conjSub_le_normal {X U : Subgroup G} (hX : X.Normal) (g : G) (hU : U ≤ X) :
    A1b.conjSub g U ≤ X := by
  intro x hx
  rw [A1b.mem_conjSub_iff] at hx
  have := hX.conj_mem (g⁻¹ * x * g) (hU hx) g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

theorem wr_normal_conjSub {S N : Subgroup G} (g : G) (hNS : N ≤ S)
    (hn : (N.subgroupOf S).Normal) :
    ((A1b.conjSub g N).subgroupOf (A1b.conjSub g S)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (A1b.conjSub_mono g hNS)]
  have h1 : S ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).mp hn
  calc A1b.conjSub g S ≤ A1b.conjSub g (Subgroup.normalizer (N : Set G)) :=
        A1b.conjSub_mono g h1
    _ = Subgroup.normalizer ((A1b.conjSub g N : Subgroup G) : Set G) :=
        A1b.conjSub_normalizer g N

theorem wr_conjSub_commutator (g : G) (U V : Subgroup G) :
    A1b.conjSub g ⁅U, V⁆ = ⁅A1b.conjSub g U, A1b.conjSub g V⁆ := by
  unfold A1b.conjSub
  rw [Subgroup.map_commutator]

theorem wr_conj_actE_D {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {e : G} (he : e ∈ actE T A J) :
    A1b.conjSub e D = D := by
  have key : ∀ g ∈ actE T A J, A1b.conjSub g D ≤ D := by
    intro g hg
    calc A1b.conjSub g D = A1b.conjSub g (⨆ S ∈ 𝒟, S) := by rw [hJD.SM.gen]
      _ = ⨆ S ∈ 𝒟, A1b.conjSub g S := conjSub_iSup₂ g (fun S (_ : S ∈ 𝒟) => S)
      _ ≤ ⨆ S ∈ 𝒟, S := iSup₂_le fun S hS =>
          le_iSup₂_of_le (A1b.conjSub g S) (hJD.SM.conj S hS g hg) le_rfl
      _ = D := hJD.SM.gen
  have h2 : D ≤ A1b.conjSub e D := by
    have h3 := A1b.conjSub_mono e (key e⁻¹ ((actE T A J).inv_mem he))
    rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at h3
    exact h3
  exact le_antisymm (key e he) h2

theorem wr_dimg_le_wrY (h : DiagSetting X T A J C) {Y : Subgroup G} :
    dimg h.diagComm Y ≤ wrY h.diagComm T A Y := by
  rw [wrY_eq]
  exact le_iSup₂_of_le (1 : G) (actT T A).one_mem (le_of_eq (A1b.conjSub_one _).symm)

theorem wr_dimg_le_wrN (h : DiagSetting X T A J C) {D : Subgroup G} :
    dimg h.diagComm D ≤ wrN h.diagComm T A D := by
  rw [wrN_eq]
  exact le_iSup₂_of_le (1 : G) (actT T A).one_mem (le_of_eq (A1b.conjSub_one _).symm)

theorem wr_wrY_le_wrN (h : DiagSetting X T A J C) {Y D : Subgroup G} (hYD : Y ≤ D) :
    wrY h.diagComm T A Y ≤ wrN h.diagComm T A D := by
  rw [wrY_eq, wrN_eq]
  exact iSup₂_mono fun k _ => A1b.conjSub_mono k (dimg_mono h.diagComm hYD)

theorem wr_conjSub_wrY (h : DiagSetting X T A J C) {Y : Subgroup G} {k : G}
    (hk : k ∈ actT T A) : A1b.conjSub k (wrY h.diagComm T A Y) = wrY h.diagComm T A Y := by
  rw [wrY_eq]
  exact wr_conjSub_eq_of_mem hk

theorem wr_conjSub_wrN (h : DiagSetting X T A J C) {D : Subgroup G} {k : G}
    (hk : k ∈ actT T A) : A1b.conjSub k (wrN h.diagComm T A D) = wrN h.diagComm T A D := by
  rw [wrN_eq]
  exact wr_conjSub_eq_of_mem hk

theorem wr_dimg_le_normalizer_conj (h : DiagSetting X T A J C) {U Y : Subgroup G} (hUJ : U ≤ J)
    (hYJ : Y ≤ J) (hUN : U ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {k : G} (hk : k ∈ actT T A) :
    dimg h.diagComm U ≤ Subgroup.normalizer (A1b.conjSub k (dimg h.diagComm Y) : Set G) := by
  by_cases hkI : A1b.conjSub k (diagSub J C h.diagComm) = diagSub J C h.diagComm
  · rw [wr_stab_dimg h hYJ hE hk hkI]
    refine wr_dimg_le_normalizer h hUJ hYJ ?_
    intro u hu v hv
    exact (Subgroup.mem_normalizer_iff.mp (hUN hu) v).mp hv
  · intro d hd
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact wr_block_comm_I h hk hkI w (A1b.conjSub_mono k (dimg_le_diagSub h hYJ) hw) d
      (dimg_le_diagSub h hUJ hd)

theorem wr_dimg_le_normalizer_wrY (h : DiagSetting X T A J C) {U D Y : Subgroup G}
    (hUD : U ≤ D) (hDJ : D ≤ J) (hYJ : Y ≤ J) (hDN : D ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) :
    dimg h.diagComm U ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) := by
  intro d hd
  refine E111R.mem_normalizer_of_conjSub_eq ?_
  rw [wrY_eq, conjSub_iSup₂]
  refine iSup_congr fun k => iSup_congr fun hk => ?_
  exact E111R.conjSub_eq_of_mem_normalizer
    (wr_dimg_le_normalizer_conj h (hUD.trans hDJ) hYJ (hUD.trans hDN) hE hk hd)

theorem wr_conj_dimg_le_normalizer (h : DiagSetting X T A J C) {U D Y : Subgroup G}
    (hUD : U ≤ D) (hDJ : D ≤ J) (hYJ : Y ≤ J) (hDN : D ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {n : G} (hn : n ∈ actT T A) :
    A1b.conjSub n (dimg h.diagComm U) ≤
      Subgroup.normalizer (wrY h.diagComm T A Y : Set G) := by
  have hn' : n⁻¹ ∈ actT T A := (actT T A).inv_mem hn
  have hsub : dimg h.diagComm U ≤
      Subgroup.normalizer (A1b.conjSub n⁻¹ (wrY h.diagComm T A Y) : Set G) := by
    rw [wr_conjSub_wrY h hn']
    exact wr_dimg_le_normalizer_wrY h hUD hDJ hYJ hDN hE
  have := A1b.conjSub_mono n hsub
  rwa [A1b.conjSub_normalizer, ← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at this

theorem wr_conjSub_sup (g : G) (U V : Subgroup G) :
    A1b.conjSub g (U ⊔ V) = A1b.conjSub g U ⊔ A1b.conjSub g V := by
  unfold A1b.conjSub
  rw [Subgroup.map_sup]

theorem wr_simple_core (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y)
    {N' : Subgroup G} (hYN' : wrY h.diagComm T A Y ≤ N')
    (hN'Z : N' ≤ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)
    (hnorm : (N'.subgroupOf (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)).Normal) :
    N' = wrY h.diagComm T A Y ∨ N' = dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := by
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYJ : Y ≤ J := hYS₀.trans hS₀J
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hYS₀.trans hS₀D)).mp hJD.Y_normal
  have hdS₀N : dimg h.diagComm S₀ ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) :=
    wr_dimg_le_normalizer_wrY h hS₀D hJD.D_le hYJ hDN hE
  have hdY : dimg h.diagComm Y ≤ wrY h.diagComm T A Y := wr_dimg_le_wrY h
  set Y' := wrY h.diagComm T A Y with hY'
  set Φ := diagHom J C h.diagComm with hΦ
  set Z := dimg h.diagComm S₀ ⊔ Y' with hZ
  set K : Subgroup ↥J := N'.comap Φ ⊓ S₀.subgroupOf J with hK
  set N'' : Subgroup G := K.map J.subtype with hN''
  have hmemK : ∀ k : ↥J, k ∈ K ↔ Φ k ∈ N' ∧ (k : G) ∈ S₀ := fun k => by
    rw [hK, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hN''S₀ : N'' ≤ S₀ := by
    intro x hx
    rw [hN''] at hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact ((hmemK k).mp hk).2
  have hYN'' : Y ≤ N'' := by
    intro y hy
    have hyJ : y ∈ J := hYJ hy
    rw [hN'']
    refine Subgroup.mem_map.mpr ⟨⟨y, hyJ⟩, (hmemK ⟨y, hyJ⟩).mpr ⟨?_, hYS₀ hy⟩, rfl⟩
    exact hYN' (hdY ((mem_dimg_iff h.diagComm).mpr ⟨⟨y, hyJ⟩, hy, rfl⟩))
  have hN''n : (N''.subgroupOf S₀).Normal := by
    refine normal_subgroupOf_of_conj hN''S₀ fun s hs x hx => ?_
    rw [hN''] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hsJ : s ∈ J := hS₀J hs
    refine Subgroup.mem_map.mpr ⟨(⟨s, hsJ⟩ : ↥J) * k * (⟨s, hsJ⟩ : ↥J)⁻¹, ?_, rfl⟩
    rw [hmemK]
    obtain ⟨hkN, hkS⟩ := (hmemK k).mp hk
    constructor
    · rw [map_mul, map_mul, map_inv]
      have hσZ : Φ ⟨s, hsJ⟩ ∈ Z :=
        (le_sup_left : dimg h.diagComm S₀ ≤ Z) ((mem_dimg_iff h.diagComm).mpr ⟨⟨s, hsJ⟩, hs, rfl⟩)
      have hkZ : Φ k ∈ Z := hN'Z hkN
      have key := hnorm.conj_mem ⟨Φ k, hkZ⟩ (Subgroup.mem_subgroupOf.mpr hkN) ⟨Φ ⟨s, hsJ⟩, hσZ⟩
      exact Subgroup.mem_subgroupOf.mp key
    · exact S₀.mul_mem (S₀.mul_mem hs hkS) (S₀.inv_mem hs)
  rcases hJD.SM.simple S₀ hS₀ N'' hYN'' hN''S₀ hN''n with hcase | hcase
  · left
    have hHK : ∀ d ∈ dimg h.diagComm S₀, ∀ y ∈ Y', d * y * d⁻¹ ∈ Y' := fun d hd y hy =>
      (Subgroup.mem_normalizer_iff.mp (hdS₀N hd) y).mp hy
    refine le_antisymm ?_ hYN'
    intro x hx
    obtain ⟨d, hd, y, hy, rfl⟩ := wr_mem_sup hHK (hN'Z hx)
    have hdN' : d ∈ N' := by
      have h1 : d * y * y⁻¹ ∈ N' := N'.mul_mem hx (N'.inv_mem (hYN' hy))
      rwa [mul_inv_cancel_right] at h1
    obtain ⟨σ, hσS, rfl⟩ := (mem_dimg_iff h.diagComm).mp hd
    have hσK : σ ∈ K := (hmemK σ).mpr ⟨hdN', hσS⟩
    have hσY : (σ : G) ∈ Y := by
      have hmem : (σ : G) ∈ N'' := by
        rw [hN'']
        exact Subgroup.mem_map.mpr ⟨σ, hσK, rfl⟩
      rw [hcase] at hmem
      exact hmem
    exact Y'.mul_mem (hdY ((mem_dimg_iff h.diagComm).mpr ⟨σ, hσY, rfl⟩)) hy
  · right
    have hdS : dimg h.diagComm S₀ ≤ N' := by
      intro x hx
      obtain ⟨σ, hσS, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
      have hσN : (σ : G) ∈ N'' := by
        rw [hcase]
        exact hσS
      rw [hN''] at hσN
      obtain ⟨k, hk, hkσ⟩ := Subgroup.mem_map.mp hσN
      have hkσ' : k = σ := Subtype.ext hkσ
      rw [← hkσ']
      exact ((hmemK k).mp hk).1
    exact le_antisymm hN'Z (sup_le hdS hYN')

theorem wr_simple (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {k : G} (hk : k ∈ actT T A) {N' : Subgroup G}
    (hYN' : wrY h.diagComm T A Y ≤ N')
    (hN'S : N' ≤ A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y))
    (hnorm : (N'.subgroupOf (A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y))).Normal) :
    N' = wrY h.diagComm T A Y ∨
      N' = A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) := by
  have hk' : k⁻¹ ∈ actT T A := (actT T A).inv_mem hk
  have hcZ : A1b.conjSub k⁻¹ (A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)) =
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := by
    rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  have hcN : A1b.conjSub k (A1b.conjSub k⁻¹ N') = N' := by
    rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
  have hM1 : wrY h.diagComm T A Y ≤ A1b.conjSub k⁻¹ N' := by
    have := A1b.conjSub_mono k⁻¹ hYN'
    rwa [wr_conjSub_wrY h hk'] at this
  have hM2 : A1b.conjSub k⁻¹ N' ≤ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := by
    have := A1b.conjSub_mono k⁻¹ hN'S
    rwa [hcZ] at this
  have hM3 : ((A1b.conjSub k⁻¹ N').subgroupOf
      (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)).Normal := by
    have := wr_normal_conjSub k⁻¹ hN'S hnorm
    rwa [hcZ] at this
  rcases wr_simple_core h hJD hS₀ hE hM1 hM2 hM3 with hM | hM
  · left
    rw [← hcN, hM, wr_conjSub_wrY h hk]
  · right
    rw [← hcN, hM]

theorem wr_nonab_core (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) :
    ¬ ⁅dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y,
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y⁆ ≤ wrY h.diagComm T A Y := by
  intro hle
  apply hJD.SM.nonab S₀ hS₀
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYJ : Y ≤ J := (hJD.SM.Y_le S₀ hS₀).trans hS₀J
  intro x hx
  have hxS : x ∈ S₀ := E111R.commutator_le_self S₀ hx
  have hxJ : x ∈ J := hS₀J hxS
  obtain ⟨hxJ', hmem⟩ := dimg_commutator_mem h hS₀J hx
  have hmem' : diagHom J C h.diagComm ⟨x, hxJ⟩ ∈ wrY h.diagComm T A Y :=
    ((Subgroup.commutator_mono (le_sup_left : dimg h.diagComm S₀ ≤ _)
      (le_sup_left : dimg h.diagComm S₀ ≤ _)).trans hle) hmem
  have hI : diagHom J C h.diagComm ⟨x, hxJ⟩ ∈ diagSub J C h.diagComm := by
    rw [← dimg_J h]
    exact (mem_dimg_iff h.diagComm).mpr ⟨⟨x, hxJ⟩, hxJ, rfl⟩
  have hYd := wr_inf_wrY h hYJ hE (Subgroup.mem_inf.mpr ⟨hI, hmem'⟩)
  obtain ⟨y, hy, hyx⟩ := (mem_dimg_iff h.diagComm).mp hYd
  have hyx' : y = ⟨x, hxJ⟩ := diagHom_injective h.diagComm h.center_trivial hyx
  have hxy : (y : G) = x := congrArg Subtype.val hyx'
  rw [← hxy]
  exact hy

theorem wr_comm_core (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {n : G} (hn : n ∈ actT T A)
    (hne : A1b.conjSub n (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) ≠
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) :
    ⁅dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y,
      A1b.conjSub n (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)⁆ ≤ wrY h.diagComm T A Y := by
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYJ : Y ≤ J := hYS₀.trans hS₀J
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hYS₀.trans hS₀D)).mp hJD.Y_normal
  have hdY : dimg h.diagComm Y ≤ wrY h.diagComm T A Y := wr_dimg_le_wrY h
  have hS₀N := wr_dimg_le_normalizer_wrY h hS₀D hJD.D_le hYJ hDN hE
  have hnorm0 : ∀ p ∈ dimg h.diagComm S₀, ∀ y ∈ wrY h.diagComm T A Y,
      p * y * p⁻¹ ∈ wrY h.diagComm T A Y := fun p hp y hy =>
    (Subgroup.mem_normalizer_iff.mp (hS₀N hp) y).mp hy
  by_cases hI : A1b.conjSub n (diagSub J C h.diagComm) = diagSub J C h.diagComm
  · obtain ⟨e, he, c, hc, c', hc', rfl⟩ := wr_stab_decomp h hn hI
    have hS₁𝒟 : A1b.conjSub e S₀ ∈ 𝒟 := hJD.SM.conj S₀ hS₀ e he
    have hS₁D : A1b.conjSub e S₀ ≤ D := hJD.SM.le_D _ hS₁𝒟
    have hconjZ : A1b.conjSub (c' * e * c⁻¹)
        (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) =
        dimg h.diagComm (A1b.conjSub e S₀) ⊔ wrY h.diagComm T A Y := by
      rw [wr_conjSub_sup, wr_conjSub_dimg h hS₀J he hc hc', wr_conjSub_wrY h hn]
    have hS₁ne : A1b.conjSub e S₀ ≠ S₀ := by
      intro heq
      apply hne
      rw [hconjZ, heq]
    have hS₁N := wr_dimg_le_normalizer_wrY h hS₁D hJD.D_le hYJ hDN hE
    have hcomm : ∀ a ∈ dimg h.diagComm S₀, ∀ b ∈ dimg h.diagComm (A1b.conjSub e S₀),
        a * b * a⁻¹ * b⁻¹ ∈ wrY h.diagComm T A Y := by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_dimg_iff h.diagComm).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_dimg_iff h.diagComm).mp hb
      have hc1 : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ Y := by
        have hcm := hJD.SM.comm S₀ hS₀ _ hS₁𝒟 (Ne.symm hS₁ne)
          (Subgroup.commutator_mem_commutator hx hy)
        rwa [commutatorElement_def] at hcm
      have hc2 : diagHom J C h.diagComm (x * y * x⁻¹ * y⁻¹) ∈ dimg h.diagComm Y :=
        (mem_dimg_iff h.diagComm).mpr ⟨x * y * x⁻¹ * y⁻¹, hc1, rfl⟩
      have hc3 : diagHom J C h.diagComm (x * y * x⁻¹ * y⁻¹) =
          diagHom J C h.diagComm x * diagHom J C h.diagComm y *
            (diagHom J C h.diagComm x)⁻¹ * (diagHom J C h.diagComm y)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [← hc3]
      exact hdY hc2
    rw [hconjZ]
    exact wr_commutator_sup_le hnorm0
      (fun p hp y hy => (Subgroup.mem_normalizer_iff.mp (hS₁N hp) y).mp hy) hcomm
  · have hcomm : ∀ a ∈ dimg h.diagComm S₀, ∀ b ∈ A1b.conjSub n (dimg h.diagComm S₀),
        a * b * a⁻¹ * b⁻¹ ∈ wrY h.diagComm T A Y := by
      intro a ha b hb
      have hbI : b ∈ A1b.conjSub n (diagSub J C h.diagComm) :=
        A1b.conjSub_mono n (dimg_le_diagSub h hS₀J) hb
      have haI : a ∈ diagSub J C h.diagComm := dimg_le_diagSub h hS₀J ha
      have hab : a * b = b * a := (wr_block_comm_I h hn hI b hbI a haI).symm
      have e1 : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [hab]
        group
      rw [e1]
      exact (wrY h.diagComm T A Y).one_mem
    have hdist2 : A1b.conjSub n (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) =
        A1b.conjSub n (dimg h.diagComm S₀) ⊔ wrY h.diagComm T A Y := by
      rw [wr_conjSub_sup, wr_conjSub_wrY h hn]
    rw [hdist2]
    exact wr_commutator_sup_le hnorm0
      (fun p hp y hy =>
        (Subgroup.mem_normalizer_iff.mp
          (wr_conj_dimg_le_normalizer h hS₀D hJD.D_le hYJ hDN hE hn hp) y).mp hy) hcomm

theorem wr_comm_pair (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {k k' : G} (hk : k ∈ actT T A)
    (hk' : k' ∈ actT T A)
    (hne : A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) ≠
      A1b.conjSub k' (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)) :
    ⁅A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y),
      A1b.conjSub k' (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)⁆ ≤ wrY h.diagComm T A Y := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = k⁻¹ * k' := ⟨_, rfl⟩
  have hn : n ∈ actT T A := by
    rw [hn_def]
    exact (actT T A).mul_mem ((actT T A).inv_mem hk) hk'
  have hkk : A1b.conjSub k' (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) =
      A1b.conjSub k (A1b.conjSub n (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)) := by
    rw [hn_def, ← A1b.conjSub_mul, mul_inv_cancel_left]
  have hne' : A1b.conjSub n (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) ≠
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := by
    intro heq
    apply hne
    rw [hkk, heq]
  have key := wr_comm_core h hJD hS₀ hE hn hne'
  rw [hkk, ← wr_conjSub_commutator]
  exact (A1b.conjSub_mono k key).trans (le_of_eq (wr_conjSub_wrY h hk))

theorem wr_mem_normalizer {K W : Subgroup G} {g : G} (hg : g ∈ K) :
    g ∈ Subgroup.normalizer ((⨆ k ∈ K, A1b.conjSub k W : Subgroup G) : Set G) :=
  E111R.mem_normalizer_of_conjSub_le (wr_conjSub_le_of_mem hg) (wr_conjSub_le_of_mem (K.inv_mem hg))

theorem wr_isSolvable_conj (g : G) {P : Subgroup G} (hP : Group.IsSolvable ↥P) :
    Group.IsSolvable ↥(A1b.conjSub g P) := by
  haveI := hP
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toMonoidHom)
    (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective

theorem wr_isSolvable_dimg (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hY : Group.IsSolvable ↥Y) : Group.IsSolvable ↥(dimg h.diagComm Y) := by
  haveI := hY
  have hinj : Function.Injective (diagHom J C h.diagComm) :=
    diagHom_injective h.diagComm h.center_trivial
  haveI : Group.IsSolvable ↥(Y.subgroupOf J) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYJ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYJ).symm.surjective
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective (Y.subgroupOf J) (diagHom J C h.diagComm) hinj).toMonoidHom)
    (Subgroup.equivMapOfInjective (Y.subgroupOf J) (diagHom J C h.diagComm) hinj).surjective

theorem wr_isSolvable_wrY (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) (hY : Group.IsSolvable ↥Y) :
    Group.IsSolvable ↥(wrY h.diagComm T A Y) := by
  have e : (⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm Y)) =
      sSup ((fun k : G => A1b.conjSub k (dimg h.diagComm Y)) '' (actT T A : Set G)) :=
    sSup_image.symm
  rw [wrY_eq, e]
  apply wr_isSolvable_sSup
  · rintro V ⟨k, -, rfl⟩
    exact wr_isSolvable_conj k (wr_isSolvable_dimg h hYJ hY)
  · rintro V ⟨k, hk, rfl⟩ V' ⟨k', hk', rfl⟩ hne x hx y hy
    by_cases hI : A1b.conjSub k (diagSub J C h.diagComm) =
        A1b.conjSub k' (diagSub J C h.diagComm)
    · exact absurd (wr_same_block_dimg h hYJ hE hk hk' hI) hne
    · exact wr_block_comm h hk hk' hI x (A1b.conjSub_mono k (dimg_le_diagSub h hYJ) hx) y
        (A1b.conjSub_mono k' (dimg_le_diagSub h hYJ) hy)

theorem wr_dimg_le_commutator (h : DiagSetting X T A J C) {D : Subgroup G} (hDJ : D ≤ J)
    (hperf : ⁅D, D⁆ = D) : dimg h.diagComm D ≤ ⁅dimg h.diagComm D, dimg h.diagComm D⁆ := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
  have hu' : (u : G) ∈ ⁅D, D⁆ := by
    rw [hperf]
    exact hu
  obtain ⟨hJ', hmem⟩ := dimg_commutator_mem h hDJ hu'
  exact hmem

theorem wr_commutator_wrN (h : DiagSetting X T A J C) {D : Subgroup G} (hDJ : D ≤ J)
    (hperf : ⁅D, D⁆ = D) :
    ⁅wrN h.diagComm T A D, wrN h.diagComm T A D⁆ = wrN h.diagComm T A D := by
  apply le_antisymm (E111R.commutator_le_self _)
  have hsub : ∀ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm D) ≤ wrN h.diagComm T A D :=
    fun k hk => by
      rw [wrN_eq]
      exact le_iSup₂_of_le k hk le_rfl
  have hle : (⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm D)) ≤
      ⁅wrN h.diagComm T A D, wrN h.diagComm T A D⁆ := by
    refine iSup₂_le fun k hk => ?_
    have h1 := A1b.conjSub_mono k (wr_dimg_le_commutator h hDJ hperf)
    rw [wr_conjSub_commutator] at h1
    exact h1.trans (Subgroup.commutator_mono (hsub k hk) (hsub k hk))
  rw [← wrN_eq] at hle
  exact hle

theorem wr_semisimple (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) :
    SemisimpleMod (actT T A) (wrN h.diagComm T A D) (wrY h.diagComm T A Y)
      (wrFam h.diagComm T A S₀ Y) := by
  have hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y := hJD.E_Y
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYD : Y ≤ D := hYS₀.trans hS₀D
  have hYJ : Y ≤ J := hYD.trans hJD.D_le
  have hZN : dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y ≤ wrN h.diagComm T A D :=
    sup_le ((dimg_mono h.diagComm hS₀D).trans (wr_dimg_le_wrN h)) (wr_wrY_le_wrN h hYD)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro S hS
    rw [wrFam_eq] at hS
    obtain ⟨k, hk, hkS⟩ := hS
    rw [← hkS]
    calc wrY h.diagComm T A Y = A1b.conjSub k (wrY h.diagComm T A Y) :=
          (wr_conjSub_wrY h hk).symm
      _ ≤ A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) :=
          A1b.conjSub_mono k le_sup_right
  ·
    intro S hS
    rw [wrFam_eq] at hS
    obtain ⟨k, hk, hkS⟩ := hS
    rw [← hkS]
    calc A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) ≤
          A1b.conjSub k (wrN h.diagComm T A D) := A1b.conjSub_mono k hZN
      _ = wrN h.diagComm T A D := wr_conjSub_wrN h hk
  ·
    intro S hS N hYN hNS hn
    rw [wrFam_eq] at hS
    obtain ⟨k, hk, hkS⟩ := hS
    subst hkS
    exact wr_simple h hJD hS₀ hE hk hYN hNS hn
  ·
    intro S hS hle
    rw [wrFam_eq] at hS
    obtain ⟨k, hk, hkS⟩ := hS
    subst hkS
    beta_reduce at hle
    apply wr_nonab_core h hJD hS₀ hE
    have h1 := A1b.conjSub_mono k⁻¹ hle
    rw [← wr_conjSub_commutator, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one,
      wr_conjSub_wrY h ((actT T A).inv_mem hk)] at h1
    exact h1
  ·
    intro S hS S' hS' hne
    rw [wrFam_eq] at hS hS'
    obtain ⟨k, hk, hkS⟩ := hS
    obtain ⟨k', hk', hkS'⟩ := hS'
    subst hkS hkS'
    beta_reduce at hne
    exact wr_comm_pair h hJD hS₀ hE hk hk' hne
  ·
    rw [wrFam_eq, iSup_image]
    set M : Subgroup G :=
      ⨆ k ∈ actT T A, A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) with hM
    apply le_antisymm
    · refine iSup₂_le fun k hk => ?_
      exact (A1b.conjSub_mono k hZN).trans_eq (wr_conjSub_wrN h hk)
    · have hsubZ : ∀ S ∈ 𝒟, dimg h.diagComm S ≤ M := by
        intro S hS
        obtain ⟨t, ht, hts⟩ := hJD.SM.trans S₀ hS₀ S hS
        have e1 : A1b.conjSub t (dimg h.diagComm S₀) = dimg h.diagComm (A1b.conjSub t S₀) := by
          have := wr_conjSub_dimg h hS₀J ht C.one_mem C.one_mem
          simpa only [one_mul, inv_one, mul_one] using this
        rw [hts] at e1
        rw [← e1]
        have ht' : t ∈ actT T A :=
          mem_actT_iff.mpr ⟨(mem_actE_iff.mp ht).1, (mem_actE_iff.mp ht).2.2⟩
        exact (A1b.conjSub_mono t le_sup_left).trans (le_iSup₂_of_le t ht' le_rfl)
      have hdimgD : dimg h.diagComm D ≤ M := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
        have hu' : (u : G) ∈ ⨆ S ∈ 𝒟, S := by
          rw [hJD.SM.gen]
          exact hu
        have hmem : ∀ S ∈ 𝒟, ∀ y ∈ (fun S : Subgroup G => S) S,
            ∃ hg : y ∈ J, diagHom J C h.diagComm ⟨y, hg⟩ ∈ M := by
          intro S hS y hy
          have hyJ : y ∈ J := hJD.D_le ((hJD.SM.le_D S hS) hy)
          exact ⟨hyJ, hsubZ S hS ((mem_dimg_iff h.diagComm).mpr ⟨⟨y, hyJ⟩, hy, rfl⟩)⟩
        have hone : ∃ hg : (1 : G) ∈ J, diagHom J C h.diagComm ⟨1, hg⟩ ∈ M := by
          refine ⟨J.one_mem, ?_⟩
          have e0 : diagHom J C h.diagComm ⟨1, J.one_mem⟩ = 1 := map_one _
          rw [e0]
          exact M.one_mem
        have hmul : ∀ a b : G, (∃ hg : a ∈ J, diagHom J C h.diagComm ⟨a, hg⟩ ∈ M) →
            (∃ hg : b ∈ J, diagHom J C h.diagComm ⟨b, hg⟩ ∈ M) →
            ∃ hg : a * b ∈ J, diagHom J C h.diagComm ⟨a * b, hg⟩ ∈ M := by
          rintro a b ⟨ha1, hA⟩ ⟨hb1, hB⟩
          refine ⟨J.mul_mem ha1 hb1, ?_⟩
          have e2 : diagHom J C h.diagComm ⟨a * b, J.mul_mem ha1 hb1⟩ =
              diagHom J C h.diagComm ⟨a, ha1⟩ * diagHom J C h.diagComm ⟨b, hb1⟩ :=
            map_mul (diagHom J C h.diagComm) (⟨a, ha1⟩ : ↥J) (⟨b, hb1⟩ : ↥J)
          rw [e2]
          exact M.mul_mem hA hB
        obtain ⟨hu1, hres⟩ := wr_join_induction 𝒟 (fun S : Subgroup G => S)
          (P := fun g => ∃ hg : g ∈ J, diagHom J C h.diagComm ⟨g, hg⟩ ∈ M) hu' hmem hone hmul
        exact hres
      rw [wrN_eq]
      refine iSup₂_le fun k hk => ?_
      exact (A1b.conjSub_mono k hdimgD).trans_eq (wr_conjSub_eq_of_mem hk)
  ·
    intro S hS t ht
    rw [wrFam_eq] at hS ⊢
    obtain ⟨k, hk, hkS⟩ := hS
    refine ⟨t * k, (actT T A).mul_mem ht hk, ?_⟩
    rw [← hkS]
    show A1b.conjSub (t * k) (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) =
      A1b.conjSub t (A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y))
    rw [A1b.conjSub_mul]
  ·
    intro S hS S' hS'
    rw [wrFam_eq] at hS hS'
    obtain ⟨k, hk, hkS⟩ := hS
    obtain ⟨k', hk', hkS'⟩ := hS'
    rw [← hkS, ← hkS']
    refine ⟨k' * k⁻¹, (actT T A).mul_mem hk' ((actT T A).inv_mem hk), ?_⟩
    show A1b.conjSub (k' * k⁻¹) (A1b.conjSub k (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)) =
      A1b.conjSub k' (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)
    rw [← A1b.conjSub_mul, inv_mul_cancel_right]

theorem wr_card_dimg (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J) :
    Nat.card ↥(dimg h.diagComm U) = Nat.card ↥U := by
  have hinj : Function.Injective (diagHom J C h.diagComm) :=
    diagHom_injective h.diagComm h.center_trivial
  unfold dimg
  rw [Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv

theorem wr_sylow_dimg (h : DiagSetting X T A J C) {D : Subgroup G} (hDJ : D ≤ J)
    (hT2 : IsPGroup 2 T) (hSylD : IsSylowIn 2 (T ⊓ D) D) :
    IsSylowIn 2 (T ⊓ dimg h.diagComm D) (dimg h.diagComm D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTD : dimg h.diagComm (T ⊓ D) ≤ T ⊓ dimg h.diagComm D := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_dimg_iff h.diagComm).mp hx
    obtain ⟨huT, huD⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨?_, (mem_dimg_iff h.diagComm).mpr ⟨u, huD, rfl⟩⟩
    refine diagHom_mem_of h.diagComm u ?_
    intro c hc
    exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) huT) (T.inv_mem (h.AT (h.CA hc)))
  have hD0 : Nat.card ↥D ≠ 0 := Nat.card_pos.ne'
  have hcardTD : Nat.card ↥(T ⊓ D) = 2 ^ (Nat.card ↥D).factorization 2 := hSylD.card_eq
  have hP2 : IsPGroup 2 ↥(T ⊓ dimg h.diagComm D) := hT2.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP2
  have hdiv : Nat.card ↥(T ⊓ dimg h.diagComm D) ∣ Nat.card ↥(dimg h.diagComm D) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hkD : k ≤ (Nat.card ↥D).factorization 2 := by
    have h1 : 2 ^ k ∣ Nat.card ↥D := by
      rw [← wr_card_dimg h hDJ, ← hk]
      exact hdiv
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hD0).mp h1
  have hle : Nat.card ↥(dimg h.diagComm (T ⊓ D)) ≤ Nat.card ↥(T ⊓ dimg h.diagComm D) :=
    Subgroup.card_le_of_le hTD
  have hDJ' : T ⊓ D ≤ J := inf_le_right.trans hDJ
  rw [wr_card_dimg h hDJ', hcardTD, hk] at hle
  have hvk : (Nat.card ↥D).factorization 2 ≤ k :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hkv : k = (Nat.card ↥D).factorization 2 := le_antisymm hkD hvk
  refine isSylowIn_of_card_eq inf_le_right ?_
  rw [hk, wr_card_dimg h hDJ, hkv]

theorem wr_conjSub_inf (g : G) (V W : Subgroup G) :
    A1b.conjSub g (V ⊓ W) = A1b.conjSub g V ⊓ A1b.conjSub g W := by
  unfold A1b.conjSub
  exact Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem wr_sylow_conj {U : Subgroup G} {g : G} (hgT : g ∈ T)
    (hSyl : IsSylowIn 2 (T ⊓ U) U) : IsSylowIn 2 (T ⊓ A1b.conjSub g U) (A1b.conjSub g U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTT : A1b.conjSub g T = T := E111R.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hgT)
  have hconj : A1b.conjSub g (T ⊓ U) = T ⊓ A1b.conjSub g U := by
    rw [wr_conjSub_inf, hTT]
  refine isSylowIn_of_card_eq inf_le_right ?_
  rw [← hconj, E111R.card_conjSub, E111R.card_conjSub]
  exact hSyl.card_eq

theorem wr_sylow_wrN (h : DiagSetting X T A J C) {D : Subgroup G} (hDJ : D ≤ J)
    (hT2 : IsPGroup 2 T) (hSylD : IsSylowIn 2 (T ⊓ D) D)
    (hED : ∀ e ∈ actE T A J, A1b.conjSub e D = D) :
    IsSylowIn 2 (T ⊓ wrN h.diagComm T A D) (wrN h.diagComm T A D) := by
  have hex : ∀ b : ↥(diagFam T A J C h.diagComm), ∃ k, k ∈ actT T A ∧
      A1b.conjSub k (diagSub J C h.diagComm) = (b : Subgroup G) := by
    intro b
    obtain ⟨⟨k, hk⟩, hkb⟩ := b.2
    exact ⟨k, hk, hkb⟩
  choose kOf hkOf using hex
  have hFle : ∀ b, A1b.conjSub (kOf b) (dimg h.diagComm D) ≤ (b : Subgroup G) := fun b =>
    (A1b.conjSub_mono (kOf b) (dimg_le_diagSub h hDJ)).trans_eq (hkOf b).2
  have hFsyl : ∀ b, IsSylowIn 2 (T ⊓ A1b.conjSub (kOf b) (dimg h.diagComm D))
      (A1b.conjSub (kOf b) (dimg h.diagComm D)) := fun b =>
    wr_sylow_conj (mem_actT_iff.mp (hkOf b).1).1 (wr_sylow_dimg h hDJ hT2 hSylD)
  have hFN : (⨆ b, A1b.conjSub (kOf b) (dimg h.diagComm D)) = wrN h.diagComm T A D := by
    apply le_antisymm
    · refine iSup_le fun b => ?_
      rw [wrN_eq]
      exact le_iSup₂_of_le (kOf b) (hkOf b).1 le_rfl
    · rw [wrN_eq]
      refine iSup₂_le fun k hk => ?_
      have hEq : A1b.conjSub (kOf (⟨A1b.conjSub k (diagSub J C h.diagComm), wr_block_mem h hk⟩ :
          ↥(diagFam T A J C h.diagComm))) (dimg h.diagComm D) =
          A1b.conjSub k (dimg h.diagComm D) :=
        wr_same_block_dimg h hDJ hED (hkOf _).1 hk (hkOf _).2
      exact le_iSup_of_le _ (le_of_eq hEq.symm)
  have hind : _root_.iSupIndep (fun b : ↥(diagFam T A J C h.diagComm) =>
      A1b.conjSub (kOf b) (dimg h.diagComm D)) := h.semiFam.iSupIndep.mono hFle
  have hcomm : Pairwise fun i j : ↥(diagFam T A J C h.diagComm) => ∀ x y : G,
      x ∈ A1b.conjSub (kOf i) (dimg h.diagComm D) →
        y ∈ A1b.conjSub (kOf j) (dimg h.diagComm D) → Commute x y :=
    fun i j hij x y hx hy =>
      h.semiFam.comm (i : Subgroup G) i.2 (j : Subgroup G) j.2
        (fun e => hij (Subtype.ext e)) x (hFle i hx) y (hFle j hy)
  have key := wr_isSylowIn_iSup (ι := ↥(diagFam T A J C h.diagComm)) hT2 hcomm hind hFsyl
  rw [hFN] at key
  exact key

theorem wr_sylow_of_normal_sup [Finite G] {H N P : Subgroup G} (hNH : N ≤ H) (hPH : P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hsup : P ⊔ N = H) (hP2 : IsPGroup 2 P)
    (hSyl : IsSylowIn 2 (P ⊓ N) N) : IsSylowIn 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hPH, hP2, ?_⟩
  have hN' : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hPN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N := fun p hp n hn =>
    (Subgroup.mem_normalizer_iff.mp (hHN (hPH hp)) n).mp hn
  have hsup' : P.subgroupOf H ⊔ N.subgroupOf H = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hxH : (x : G) ∈ P ⊔ N := by
      rw [hsup]
      exact x.2
    obtain ⟨p, hp, n, hn, hpn⟩ := wr_mem_sup hPN hxH
    have hx : x = (⟨p, hPH hp⟩ : ↥H) * ⟨n, hNH hn⟩ := Subtype.ext hpn.symm
    rw [hx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hp) (Subgroup.mem_subgroupOf.mpr hn)
  have key : (N.subgroupOf H).relIndex (P.subgroupOf H ⊔ N.subgroupOf H) =
      (N.subgroupOf H).relIndex (P.subgroupOf H) :=
    Subgroup.relIndex_sup_right (P.subgroupOf H) (N.subgroupOf H)
  rw [hsup', Subgroup.relIndex_top_right] at key
  have hi : (N.subgroupOf H).index * Nat.card ↥(N.subgroupOf H) = Nat.card ↥H :=
    Subgroup.index_mul_card (N.subgroupOf H)
  have hj : (P.subgroupOf H).index * Nat.card ↥(P.subgroupOf H) = Nat.card ↥H :=
    Subgroup.index_mul_card (P.subgroupOf H)
  have hk : (N.subgroupOf H).relIndex (P.subgroupOf H) *
      Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H)) = Nat.card ↥(P.subgroupOf H) :=
    Subgroup.relIndex_mul_card (N.subgroupOf H) (P.subgroupOf H)
  have hk' := hk
  rw [← key] at hk'
  have hi0 : (N.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hNc : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hPc : Nat.card ↥(P.subgroupOf H) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hinf : (N.subgroupOf H) ⊓ (P.subgroupOf H) = (P ⊓ N).subgroupOf H := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_comm
  have hIc : Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H)) = Nat.card ↥(P ⊓ N) := by
    rw [hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPH)).toEquiv
  have hq : Nat.card ↥(P ⊓ N) = 2 ^ (Nat.card ↥N).factorization 2 := hSyl.card_eq
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.card ↥N := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = c.factorization 2 := ⟨_, rfl⟩
  obtain ⟨i, hi_def⟩ : ∃ i, i = (N.subgroupOf H).index := ⟨_, rfl⟩
  obtain ⟨j, hj_def⟩ : ∃ j, j = (P.subgroupOf H).index := ⟨_, rfl⟩
  rw [← hi_def] at hi hi0 hk'
  rw [← hj_def] at hj
  rw [hNc, ← hc] at hi
  rw [hPc] at hj hk'
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Nat.card_pos.ne'
  have e1 : i * (j * Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H))) = i * c := by
    calc i * (j * Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H)))
        = j * (i * Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H))) := by ring
      _ = j * Nat.card ↥P := by rw [hk']
      _ = Nat.card ↥H := hj
      _ = i * c := hi.symm
  have e2 : j * Nat.card ↥((N.subgroupOf H) ⊓ (P.subgroupOf H)) = c :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hi0) e1
  have hq' : Nat.card ↥(P ⊓ N) = 2 ^ v := by
    rw [hq, hv, hc]
  rw [hIc, hq'] at e2
  have hnd : ¬ 2 ∣ j := by
    rintro ⟨s, hs⟩
    have hdvd : 2 ^ (v + 1) ∣ c := ⟨s, by rw [← e2, hs]; ring⟩
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hc0).mp hdvd
    rw [← hv] at hle
    omega
  show ¬ 2 ∣ (P.subgroupOf H).index
  rw [← hj_def]
  exact hnd

theorem wreath_struct (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hSylD : IsSylowIn 2 (T ⊓ D) D) :
    dimg h.diagComm D ≤ wrN h.diagComm T A D ∧
    wrN h.diagComm T A D ≤ X ∧
    wrY h.diagComm T A Y ≤ wrN h.diagComm T A D ∧
    actT T A ≤ Subgroup.normalizer (wrN h.diagComm T A D : Set G) ∧
    actT T A ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) ∧
    wrN h.diagComm T A D ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) ∧
    ⁅wrN h.diagComm T A D, wrN h.diagComm T A D⁆ = wrN h.diagComm T A D ∧
    Group.IsSolvable ↥(wrY h.diagComm T A Y) ∧
    SemisimpleMod (actT T A) (wrN h.diagComm T A D) (wrY h.diagComm T A Y)
      (wrFam h.diagComm T A S₀ Y) ∧
    (wrFam h.diagComm T A S₀ Y).Nonempty ∧
    IsSylowIn 2 (T ⊓ (wrN h.diagComm T A D ⊔ actT T A)) (wrN h.diagComm T A D ⊔ actT T A) := by
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYD : Y ≤ D := hYS₀.trans hS₀D
  have hYJ : Y ≤ J := hYD.trans hJD.D_le
  have hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y := hJD.E_Y
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYD).mp hJD.Y_normal
  have hT2 : IsPGroup 2 T := h.red.2.2.2.2.2.1.isPGroup
  have hT0N : actT T A ≤ Subgroup.normalizer ((wrN h.diagComm T A D : Subgroup G) : Set G) := by
    intro g hg
    rw [wrN_eq]
    exact wr_mem_normalizer hg
  have c2 : wrN h.diagComm T A D ≤ X := by
    rw [wrN_eq]
    refine iSup₂_le fun k _ => ?_
    exact wr_conjSub_le_normal h.red.1 k ((dimg_le_diagSub h hJD.D_le).trans h.diag_le)
  have c5 : actT T A ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) := by
    intro g hg
    rw [wrY_eq]
    exact wr_mem_normalizer hg
  have c6 : wrN h.diagComm T A D ≤ Subgroup.normalizer (wrY h.diagComm T A Y : Set G) := by
    rw [wrN_eq]
    refine iSup₂_le fun k hk => ?_
    exact wr_conj_dimg_le_normalizer h le_rfl hJD.D_le hYJ hDN hE hk
  have c7 := wr_commutator_wrN h hJD.D_le hJD.perf
  have c8 := wr_isSolvable_wrY h hYJ hE hJD.Ysolv
  have c9 := wr_semisimple h hJD hS₀
  have c10 : (wrFam h.diagComm T A S₀ Y).Nonempty := by
    rw [wrFam_eq]
    exact ⟨_, 1, (actT T A).one_mem, rfl⟩
  have c11 : IsSylowIn 2 (T ⊓ (wrN h.diagComm T A D ⊔ actT T A))
      (wrN h.diagComm T A D ⊔ actT T A) := by
    have hSylN : IsSylowIn 2 (T ⊓ wrN h.diagComm T A D) (wrN h.diagComm T A D) :=
      wr_sylow_wrN h hJD.D_le hT2 hSylD (fun e he => wr_conj_actE_D hJD he)
    have hNH : wrN h.diagComm T A D ≤ wrN h.diagComm T A D ⊔ actT T A := le_sup_left
    have hHN : wrN h.diagComm T A D ⊔ actT T A ≤
        Subgroup.normalizer ((wrN h.diagComm T A D : Subgroup G) : Set G) :=
      sup_le Subgroup.le_normalizer hT0N
    have hT0T : actT T A ≤ T := fun g hg => (mem_actT_iff.mp hg).1
    have hsup : (T ⊓ (wrN h.diagComm T A D ⊔ actT T A)) ⊔ wrN h.diagComm T A D =
        wrN h.diagComm T A D ⊔ actT T A := by
      apply le_antisymm
      · exact sup_le inf_le_right le_sup_left
      · refine sup_le le_sup_right (fun g hg => ?_)
        exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hT0T hg, Subgroup.mem_sup_right hg⟩)
    have hSyl : IsSylowIn 2 ((T ⊓ (wrN h.diagComm T A D ⊔ actT T A)) ⊓ wrN h.diagComm T A D)
        (wrN h.diagComm T A D) := by
      have e : (T ⊓ (wrN h.diagComm T A D ⊔ actT T A)) ⊓ wrN h.diagComm T A D =
          T ⊓ wrN h.diagComm T A D := by
        exact le_antisymm (inf_le_inf_right _ inf_le_left)
          (le_inf (le_inf inf_le_left (inf_le_right.trans le_sup_left)) inf_le_right)
      rw [e]
      exact hSylN
    exact wr_sylow_of_normal_sup hNH inf_le_right hHN hsup (hT2.to_le inf_le_left) hSyl
  exact ⟨wr_dimg_le_wrN h, c2, wr_wrY_le_wrN h hYD, hT0N, c5, c6, c7, c8, c9, c10, c11⟩

end CFSG.Quasithin.RonanE111
