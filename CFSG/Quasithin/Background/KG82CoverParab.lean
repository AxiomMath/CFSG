module

public import CFSG.Quasithin.Background.KG82CoverStd
public import CFSG.LocalAnalysis.OddStandard.ThmCL34OneClass
public import CFSG.Quasithin.Background.KG82CoverCore

public section

namespace CFSG.Quasithin.H.L34Cov

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.GrSLit.L34Facts MulAction
open scoped commutatorElement Pointwise

theorem mul_self_of_closure {ws : List (List ℕ)}
    (hc : ∀ u ∈ ws, ∀ v ∈ ws, wordL (u ++ v) = wordL (v ++ u))
    (hs : ∀ u ∈ ws, wordL (u ++ u) = List.range 42) :
    ∀ x ∈ Subgroup.closure (wordSet ws), x * x = 1 := by
  have hpair : (wordSet ws).Pairwise Commute := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ -
    show wordPerm u * wordPerm v = wordPerm v * wordPerm u
    rw [← wordPerm_append, ← wordPerm_append, eq_of_wordL (hc u hu v hv)]
  have hcomm : ∀ x ∈ Subgroup.closure (wordSet ws), ∀ y ∈ Subgroup.closure (wordSet ws),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Subgroup.isMulCommutative_closure hpair).is_comm.comm
      (⟨x, hx⟩ : ↥(Subgroup.closure (wordSet ws))) ⟨y, hy⟩)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [← wordPerm_append]
    exact eq_one_of_wordL (hs u hu)
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y, ← hcomm x hx y hy]
          simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem isPGroup_of_mul_self {G : Type*} [Group G] {H : Subgroup G} (h : ∀ x ∈ H, x * x = 1) :
    IsPGroup 2 ↥H := fun x => ⟨1, Subtype.ext (by rw [pow_one, sq]; exact h _ x.2)⟩

theorem mem_normalizer_subgroupOf {G : Type*} [Group G] {K E : Subgroup G} {x : ↥K}
    (hx : (x : G) ∈ Subgroup.normalizer (E : Set G)) :
    x ∈ Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 hx n

theorem parData_std
    {d : StdData} (hd : StdOk d) {p : Fin 42} (hp : d.p = p.val)
    (hQ : (Subgroup.closure (wordSet d.pW)).subgroupOf S = stabilizer ↥S p)
    (hcQ : Nat.card (stabilizer ↥S p) = 960) :
    ParData (stabilizer ↥S p) ((Subgroup.closure (wordSet d.eW)).subgroupOf S)
      ((Subgroup.closure (wordSet d.vW)).subgroupOf S) (T0.subgroupOf S) ∧
    ⁅stabilizer ↥S p, stabilizer ↥S p⁆ = stabilizer ↥S p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hK42, hfix, hfixK⟩, ⟨hEc, hEs, hVc, hVs, -⟩, hN, ⟨hX, hD⟩, ⟨hVcl, hVinv, hmv⟩,
    hperf⟩ := hd
  set E' := Subgroup.closure (wordSet d.eW) with hE'
  set V' := Subgroup.closure (wordSet d.vW) with hV'
  set P' := Subgroup.closure (wordSet d.pW) with hP'
  set Q := stabilizer ↥S p with hQdef
  have hfixP : ∀ w, (wordL w).getD d.p 0 = d.p → wordPerm w ∈ P' := by
    intro w hw
    have h1 : (⟨wordPerm w, wordPerm_mem w⟩ : ↥S) ∈ Q := by
      rw [hQdef, mem_stabilizer_iff']
      exact Fin.ext ((apply_of_wordL w p).trans (hp ▸ hw))
    rw [← hQ, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hmemfix : ∀ w ∈ d.eW ++ d.vW ++ [d.yW, d.hW] ++ d.aW ++ d.bW ++ wT₀, wordPerm w ∈ P' :=
    fun w hw => hfixP w (hfix w hw)
  have hEP : E' ≤ P' := (Subgroup.closure_le _).2 (by
    rintro _ ⟨w, hw, rfl⟩
    exact hmemfix w (by simp [hw]))
  have hVP : V' ≤ P' := (Subgroup.closure_le _).2 (by
    rintro _ ⟨w, hw, rfl⟩
    exact hmemfix w (by simp [hw]))
  have hTP : T0 ≤ P' := (Subgroup.closure_le _).2 (by
    rintro _ ⟨w, hw, rfl⟩
    exact hmemfix w (by simp [hw]))
  have hyP : wordPerm d.yW ∈ P' := hmemfix _ (by simp)
  have hhP : wordPerm d.hW ∈ P' := hmemfix _ (by simp)
  have hES : E' ≤ S := closure_wordSet_le _
  have hVS : V' ≤ S := closure_wordSet_le _
  have hPS : P' ≤ S := closure_wordSet_le _
  have hEsq := mul_self_of_closure hEc hEs
  have hVsq := mul_self_of_closure hVc hVs
  have hPE : P' ≤ Subgroup.normalizer (E' : Set (Equiv.Perm (Fin 42))) := by
    rw [hP', Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hconj : ∀ j < d.eW.length,
        wordPerm d.pW[k] * wordPerm (d.eW.getD j []) * (wordPerm d.pW[k])⁻¹ ∈ E' ∧
        (wordPerm d.pW[k])⁻¹ * wordPerm (d.eW.getD j []) * wordPerm d.pW[k] ∈ E' := by
      intro j hj
      obtain ⟨h1, h2, h3, h4⟩ := hN k hk j hj
      rw [List.getD_eq_getElem _ _ hk] at h1 h2
      refine ⟨?_, ?_⟩
      · rw [← wordPerm_invW, ← wordPerm_append, ← wordPerm_append, eq_of_wordL h1]
        exact wordPerm_prodW_mem _ h3
      · rw [← wordPerm_invW, ← wordPerm_append, ← wordPerm_append, eq_of_wordL h2]
        exact wordPerm_prodW_mem _ h4
    have hgen : ∀ x ∈ E', ∀ c : Bool, (if c then wordPerm d.pW[k] * x * (wordPerm d.pW[k])⁻¹
        else (wordPerm d.pW[k])⁻¹ * x * wordPerm d.pW[k]) ∈ E' := by
      intro x hx c
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
        have := hconj j hj
        rw [List.getD_eq_getElem _ _ hj] at this
        cases c
        · exact this.2
        · exact this.1
      | one => cases c <;> simp
      | mul x y _ _ ihx ihy =>
        cases c
        · have e : (wordPerm d.pW[k])⁻¹ * (x * y) * wordPerm d.pW[k] =
              ((wordPerm d.pW[k])⁻¹ * x * wordPerm d.pW[k]) *
                ((wordPerm d.pW[k])⁻¹ * y * wordPerm d.pW[k]) := by group
          simp only [Bool.false_eq_true, ↓reduceIte] at ihx ihy ⊢
          rw [e]
          exact E'.mul_mem ihx ihy
        · have e : wordPerm d.pW[k] * (x * y) * (wordPerm d.pW[k])⁻¹ =
              (wordPerm d.pW[k] * x * (wordPerm d.pW[k])⁻¹) *
                (wordPerm d.pW[k] * y * (wordPerm d.pW[k])⁻¹) := by group
          simp only [↓reduceIte] at ihx ihy ⊢
          rw [e]
          exact E'.mul_mem ihx ihy
      | inv x _ ihx =>
        cases c
        · have e : (wordPerm d.pW[k])⁻¹ * x⁻¹ * wordPerm d.pW[k] =
              ((wordPerm d.pW[k])⁻¹ * x * wordPerm d.pW[k])⁻¹ := by group
          simp only [Bool.false_eq_true, ↓reduceIte] at ihx ⊢
          rw [e]
          exact E'.inv_mem ihx
        · have e : wordPerm d.pW[k] * x⁻¹ * (wordPerm d.pW[k])⁻¹ =
              (wordPerm d.pW[k] * x * (wordPerm d.pW[k])⁻¹)⁻¹ := by group
          simp only [↓reduceIte] at ihx ⊢
          rw [e]
          exact E'.inv_mem ihx
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => by simpa using hgen n hn true, fun hn => ?_⟩
    have := hgen _ hn false
    simpa [mul_assoc] using this
  have hEK : ∀ e ∈ E', ∀ k ∈ d.K, ∀ hk : k < 42, e ⟨k, hk⟩ = ⟨k, hk⟩ := by
    have hle : E' ≤ fixingSubgroup (Equiv.Perm (Fin 42)) {x : Fin 42 | x.val ∈ d.K} := by
      rw [hE', Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, mem_fixingSubgroup_iff]
      intro x hx
      exact Fin.ext ((apply_of_wordL w x).trans (hfixK w hw x.val hx))
    intro e he k hk hk42
    exact (mem_fixingSubgroup_iff _).1 (hle he) ⟨k, hk42⟩ hk
  have hT0EV : ∀ t ∈ T0, ∃ e ∈ E', ∃ v ∈ V', t = e * v := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      obtain ⟨h1, h2, h3⟩ := hD k hk
      rw [List.getD_eq_getElem _ _ hk] at h1
      exact ⟨_, wordPerm_prodW_mem _ h2, _, wordPerm_prodW_mem _ h3,
        by rw [eq_of_wordL h1, wordPerm_append]⟩
    | one => exact ⟨1, E'.one_mem, 1, V'.one_mem, (mul_one 1).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨e, he, v, hv, rfl⟩ := hx
      obtain ⟨e', he', v', hv', rfl⟩ := hy
      have hc : v * e' * v⁻¹ ∈ E' :=
        (Subgroup.mem_normalizer_iff.1 (hPE (hVP hv)) e').1 he'
      exact ⟨e * (v * e' * v⁻¹), E'.mul_mem he hc, v * v', V'.mul_mem hv hv', by group⟩
    | inv x _ hx =>
      obtain ⟨e, he, v, hv, rfl⟩ := hx
      have hc : v⁻¹ * e⁻¹ * v⁻¹⁻¹ ∈ E' :=
        (Subgroup.mem_normalizer_iff.1 (hPE (hVP (V'.inv_mem hv))) e⁻¹).1 (E'.inv_mem he)
      rw [inv_inv] at hc
      exact ⟨v⁻¹ * e⁻¹ * v, hc, v⁻¹, V'.inv_mem hv, by group⟩
  have hVlist : ∀ v ∈ V', ∃ b ∈ d.AV, v = wordPerm b :=
    fun v hv => mem_list_of_closed (by simp [StdData.AV]) hVcl hVinv hv
  have hcoreP : E' ≤ T0 → ∀ x ∈ T0, (wordPerm d.hW)⁻¹ * x * wordPerm d.hW ∈ T0 → x ∈ E' := by
    intro hET x hx hxh
    obtain ⟨e, he, v, hv, rfl⟩ := hT0EV x hx
    obtain ⟨b, hb, rfl⟩ := hVlist v hv
    by_cases hb0 : b = []
    · subst hb0
      simpa [wordPerm] using he
    exfalso
    set h := wordPerm d.hW
    have he' : h⁻¹ * e * h ∈ E' := by
      have := (Subgroup.mem_normalizer_iff.1 (hPE (P'.inv_mem hhP)) e).1 he
      simpa using this
    have h1 : h⁻¹ * wordPerm b * h ∈ T0 := by
      have e1 : h⁻¹ * wordPerm b * h = (h⁻¹ * e * h)⁻¹ * (h⁻¹ * (e * wordPerm b) * h) := by
        group
      rw [e1]
      exact T0.mul_mem (T0.inv_mem (hET he')) hxh
    obtain ⟨e₂, he₂, v₂, hv₂, he₂v⟩ := hT0EV _ h1
    obtain ⟨b', hb', rfl⟩ := hVlist v₂ hv₂
    obtain ⟨k, hk, hmove⟩ := hmv b hb hb0 b' hb'
    have hk42 := hK42 k hk
    have e2 : wordPerm (invW d.hW ++ b ++ d.hW ++ invW b') = e₂ := by
      rw [wordPerm_append, wordPerm_append, wordPerm_append, wordPerm_invW, wordPerm_invW, he₂v]
      group
    apply hmove
    rw [← apply_of_wordL _ ⟨k, hk42⟩, e2, hEK e₂ he₂ k hk hk42]
  have hQ' : Q = P'.subgroupOf S := hQ.symm
  have hle : (E'.subgroupOf S) ≤ Q := fun x hx => by
    rw [hQ', Subgroup.mem_subgroupOf]
    exact hEP hx
  have hnorm : Q ≤ Subgroup.normalizer ((E'.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
    fun x hx => by
      rw [hQ', Subgroup.mem_subgroupOf] at hx
      exact mem_normalizer_subgroupOf (hPE hx)
  have hsq : ∀ e ∈ E'.subgroupOf S, e * e = 1 := fun e he => Subtype.ext (hEsq _ he)
  have hleF : T0.subgroupOf S ≤ Q := fun x hx => by
    rw [hQ', Subgroup.mem_subgroupOf]
    exact hTP hx
  have hcardF : Nat.card ↥((T0.subgroupOf S).subgroupOf Q) = 2 ^ (Nat.card ↥Q).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleF).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_S).toEquiv, card_T0, hcQ,
      factorization_960]
    norm_num
  have hsyl : ∀ M : Subgroup ↥S, M ≤ Q → Q ≤ Subgroup.normalizer (M : Set ↥S) →
      IsPGroup 2 ↥M → M ≤ T0.subgroupOf S := by
    intro M hMQ hQM hM2
    have hMn : (M.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMQ).2 hQM
    have hM2' : IsPGroup 2 ↥(M.subgroupOf Q) :=
      hM2.of_equiv (Subgroup.subgroupOfEquivOfLe hMQ).symm
    have h1 := hM2'.le_sylow_of_normal (Sylow.ofCard _ hcardF)
    intro m hm
    have := h1 (show (⟨m, hMQ hm⟩ : ↥Q) ∈ M.subgroupOf Q from hm)
    exact this
  have hET : E' ≤ T0 := by
    intro x hx
    have h1 := hsyl _ hle hnorm (isPGroup_of_mul_self hsq) (show (⟨x, hES hx⟩ : ↥S) ∈
      E'.subgroupOf S from hx)
    exact h1
  have hhQ : (⟨wordPerm d.hW, wordPerm_mem _⟩ : ↥S) ∈ Q := by
    rw [hQ', Subgroup.mem_subgroupOf]
    exact hhP
  refine ⟨⟨hle, hnorm, hsq, fun N hNQ hQN hN2 => ?_, ?_, fun v hv => Subtype.ext (hVsq _ hv),
    hleF, fun f hf => ?_, ?_⟩, ?_⟩
  ·
    have hNF := hsyl N hNQ hQN hN2
    intro n hn
    have h1 : (⟨wordPerm d.hW, wordPerm_mem _⟩ : ↥S)⁻¹ * n * ⟨wordPerm d.hW, wordPerm_mem _⟩ ∈
        N := by
      have := (Subgroup.mem_normalizer_iff.1 (hQN (Q.inv_mem hhQ)) n).1 hn
      simpa using this
    exact hcoreP hET _ (hNF hn) (hNF h1)
  ·
    have hgen : E' ≤ (⁅E'.subgroupOf S, Q⁆).map S.subtype := by
      rw [hE', Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      obtain ⟨h1, h2⟩ := hX j hj
      rw [List.getD_eq_getElem _ _ hj] at h1
      have hx := wordPerm_prodW_mem d.eW h2
      have hyQ : (⟨wordPerm d.yW, wordPerm_mem _⟩ : ↥S) ∈ Q := by
        rw [hQ', Subgroup.mem_subgroupOf]
        exact hyP
      refine ⟨⁅(⟨_, hES hx⟩ : ↥S), ⟨wordPerm d.yW, wordPerm_mem _⟩⁆,
        Subgroup.commutator_mem_commutator (show (⟨_, hES hx⟩ : ↥S) ∈ E'.subgroupOf S from hx)
          hyQ, ?_⟩
      rw [← eq_of_wordL h1, wordPerm_append, wordPerm_append, wordPerm_append, wordPerm_invW,
        wordPerm_invW]
      simp [commutatorElement_def]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hgen hx
    rwa [Subtype.ext hyx] at hy
  ·
    obtain ⟨e, he, v, hv, hev⟩ := hT0EV _ hf
    exact ⟨⟨e, hES he⟩, he, ⟨v, hVS hv⟩, hv, Subtype.ext hev⟩
  ·
    have h1 := (T0.subgroupOf S).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_S).toEquiv, card_T0, card_S] at h1
    rw [show (T0.subgroupOf S).index = 315 by omega]
    decide
  ·
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    have hgen : P' ≤ (⁅Q, Q⁆).map S.subtype := by
      rw [hP', Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      have h1 := hperf k hk
      rw [List.getD_eq_getElem _ _ hk] at h1
      have ha : wordPerm (d.aW.getD k []) ∈ P' := by
        by_cases hka : k < d.aW.length
        · rw [List.getD_eq_getElem _ _ hka]
          exact hmemfix _ (by simp [List.getElem_mem])
        · rw [List.getD_eq_default _ _ (by omega)]
          exact P'.one_mem
      have hb : wordPerm (d.bW.getD k []) ∈ P' := by
        by_cases hkb : k < d.bW.length
        · rw [List.getD_eq_getElem _ _ hkb]
          exact hmemfix _ (by simp [List.getElem_mem])
        · rw [List.getD_eq_default _ _ (by omega)]
          exact P'.one_mem
      have haQ : (⟨_, hPS ha⟩ : ↥S) ∈ Q := by
        rw [hQ', Subgroup.mem_subgroupOf]
        exact ha
      have hbQ : (⟨_, hPS hb⟩ : ↥S) ∈ Q := by
        rw [hQ', Subgroup.mem_subgroupOf]
        exact hb
      refine ⟨⁅(⟨_, hPS ha⟩ : ↥S), ⟨_, hPS hb⟩⁆, Subgroup.commutator_mem_commutator haQ hbQ, ?_⟩
      rw [← eq_of_wordL h1, wordPerm_append, wordPerm_append, wordPerm_append, wordPerm_invW,
        wordPerm_invW]
      simp [commutatorElement_def]
    intro x hx
    rw [hQ', Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hgen hx
    rwa [Subtype.ext hyx] at hy

theorem conj_smul_eq_map {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    MulAut.conj g • H = H.map (MulAut.conj g).toMonoidHom := rfl

theorem parData_of_card
    (Q : Subgroup ↥S) (hQ : Nat.card Q = 960) :
    (∃ E V F : Subgroup ↥S, ParData Q E V F) ∧ ⁅Q, Q⁆ = Q := by
  obtain ⟨g, hg | hg⟩ := exists_conj_eq_stab Q hQ
  · obtain ⟨hd, hp⟩ := parData_std std₁_ok (p := 2) rfl P1_eq_stab card_stab_two
    rw [hg, conj_smul_eq_map]
    exact ⟨⟨_, _, _, hd.map_equiv (MulAut.conj g)⟩, by rw [← Subgroup.map_commutator, hp]⟩
  · obtain ⟨hd, hp⟩ := parData_std std₂_ok (p := 23) rfl P2_eq_stab card_stab_tt
    rw [hg, conj_smul_eq_map]
    exact ⟨⟨_, _, _, hd.map_equiv (MulAut.conj g)⟩, by rw [← Subgroup.map_commutator, hp]⟩

theorem LRep.eq {l l' : List ℕ} {g : Equiv.Perm (Fin 42)} (h : LRep l g) (h' : LRep l' g) :
    l = l' := by
  refine List.ext_getElem (h.1.trans h'.1.symm) fun i hi hi' => ?_
  have hi42 : i < 42 := h.1 ▸ hi
  have e1 := h.2 ⟨i, hi42⟩
  have e2 := h'.2 ⟨i, hi42⟩
  rw [List.getD_eq_getElem _ _ hi] at e1
  rw [List.getD_eq_getElem _ _ hi'] at e2
  rw [e1, e2]

theorem wordPerm_ne_one {w : List ℕ} (h : wordL w ≠ List.range 42) : wordPerm w ≠ 1 :=
  fun h1 => h ((lrep_wordL w).eq (h1 ▸ lrep_range))

theorem triple_S : Triple ↥S := by
  obtain ⟨-, ⟨hEc, hEs, -⟩, -⟩ := std₁_ok
  have hne := triW_ne
  have hmem : ∀ i < 3, std₁.eW.getD i [] ∈ std₁.eW := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by simp [std₁]; omega)]
    exact List.getElem_mem _
  set e : ℕ → ↥S := fun i => ⟨wordPerm (std₁.eW.getD i []), wordPerm_mem _⟩
  have hsq : ∀ i < 3, e i * e i = 1 := fun i hi => Subtype.ext (by
    show wordPerm _ * wordPerm _ = 1
    rw [← wordPerm_append]
    exact eq_one_of_wordL (hEs _ (hmem i hi)))
  have hcm : ∀ i < 3, ∀ j < 3, e i * e j = e j * e i := fun i hi j hj => Subtype.ext (by
    show wordPerm _ * wordPerm _ = wordPerm _ * wordPerm _
    rw [← wordPerm_append, ← wordPerm_append]
    exact eq_of_wordL (hEc _ (hmem i hi) _ (hmem j hj)))
  have hne' : ∀ w ∈ triW, (⟨wordPerm w, wordPerm_mem w⟩ : ↥S) ≠ 1 := fun w hw h1 =>
    wordPerm_ne_one (hne w hw) (congrArg Subtype.val h1)
  have hm : ∀ u v : List ℕ, (⟨wordPerm u, wordPerm_mem u⟩ : ↥S) * ⟨wordPerm v, wordPerm_mem v⟩ =
      ⟨wordPerm (u ++ v), wordPerm_mem _⟩ := fun u v => Subtype.ext (wordPerm_append u v).symm
  refine ⟨e 0, e 1, e 2, hsq 0 (by norm_num), hsq 1 (by norm_num), hsq 2 (by norm_num),
    hcm 0 (by norm_num) 1 (by norm_num), hcm 0 (by norm_num) 2 (by norm_num),
    hcm 1 (by norm_num) 2 (by norm_num), hne' _ (by simp [triW]), hne' _ (by simp [triW]),
    hne' _ (by simp [triW]), ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact hne' _ (by simp [triW])
  · rw [hm]
    exact hne' _ (by simp [triW])
  · rw [hm]
    exact hne' _ (by simp [triW])
  · rw [hm, hm]
    exact hne' _ (by simp [triW])

theorem statedPSL_of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 2 2) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G' .PSL 3 2 2 :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem isConj_S :
    ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  have hL : CFSG.Blueprint.LieModel ↥(⊤ : Subgroup ↥S) .PSL 3 2 2 :=
    Or.inl ⟨by decide, statedPSL_of_equiv Subgroup.topEquiv.symm exact_model.2.2.1⟩
  exact CFSG.OddStandard.ThmC.l34OneClass ↥S ⊤ inferInstance hL (by simp)

end CFSG.Quasithin.H.L34Cov
