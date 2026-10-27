module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

namespace H9Conj

variable {W : Type} [CommGroup W]

theorem mem_conjAut {A : Subgroup (MulAut W)} {m x : MulAut W} :
    x ∈ conjAut A m ↔ m⁻¹ * x * m ∈ A := by
  unfold conjAut
  rw [Subgroup.mem_map_equiv]
  simp

theorem conjAut_eq_b1 (A : Subgroup (MulAut W)) (m : MulAut W) :
    conjAut A m = B1.conjAut m A := by
  ext x
  rw [mem_conjAut, B1.mem_conjAut]

theorem conjAut_le_conjAut {A B : Subgroup (MulAut W)} {m : MulAut W} :
    conjAut A m ≤ conjAut B m ↔ A ≤ B := by
  rw [conjAut_eq_b1, conjAut_eq_b1]
  exact B1.conjAut_le_iff

theorem conjAut_conjAut_inv (A : Subgroup (MulAut W)) (m : MulAut W) :
    conjAut (conjAut A m⁻¹) m = A := by
  rw [conjAut_eq_b1, conjAut_eq_b1]
  exact B1.conjAut_conjAut_inv m A

theorem card_conjAut (A : Subgroup (MulAut W)) (m : MulAut W) :
    Nat.card (conjAut A m) = Nat.card A := by
  rw [conjAut_eq_b1]
  exact B1.card_conjAut m A

theorem isElemAbelian2_conjAut {A : Subgroup (MulAut W)} {m : MulAut W} (h : IsElemAbelian2 A) :
    IsElemAbelian2 (conjAut A m) := by
  rw [conjAut_eq_b1]
  exact B1.isElemAbelian2_conjAut h

theorem fixV_conjAut (A : Subgroup (MulAut W)) (m : MulAut W) :
    fixV (conjAut A m) = (fixV A).map m.toMonoidHom := by
  rw [conjAut_eq_b1]
  exact B1.fixV_conjAut m A

theorem card_fixV_conjAut (A : Subgroup (MulAut W)) (m : MulAut W) :
    Nat.card (fixV (conjAut A m)) = Nat.card (fixV A) := by
  rw [conjAut_eq_b1]
  exact B1.card_fixV_conjAut m A

theorem mQuot_conjAut (P X : Subgroup (MulAut W)) (m : MulAut W) :
    mQuot (conjAut P m) (conjAut X m) = mQuot P X := by
  unfold mQuot conjAut
  rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj m).toMonoidHom) _ _
    (MulAut.conj m).injective]

theorem fixV_le_gammaCheck {k : ℕ} {P X : Subgroup (MulAut W)} (hX : X ≤ P)
    (hXk : mQuot P X ≤ k) : fixV X ≤ gammaCheck k P := by
  unfold gammaCheck
  exact le_iSup₂_of_le (f := fun X (_ : X ≤ P) => ⨆ (_ : mQuot P X ≤ k), fixV X) X hX
    (le_iSup_of_le hXk le_rfl)

theorem gammaCheck_le {k : ℕ} {P : Subgroup (MulAut W)} {S : Subgroup W}
    (h : ∀ X ≤ P, mQuot P X ≤ k → fixV X ≤ S) : gammaCheck k P ≤ S := by
  unfold gammaCheck
  exact iSup₂_le fun X hX => iSup_le fun hXk => h X hX hXk

theorem gammaCheck_mono {k k' : ℕ} (h : k ≤ k') (P : Subgroup (MulAut W)) :
    gammaCheck k P ≤ gammaCheck k' P :=
  gammaCheck_le fun _ hX hXk => fixV_le_gammaCheck hX (hXk.trans h)

theorem gammaCheck_conjAut (k : ℕ) (P : Subgroup (MulAut W)) (m : MulAut W) :
    gammaCheck k (conjAut P m) = (gammaCheck k P).map m.toMonoidHom := by
  apply le_antisymm
  · refine gammaCheck_le fun X hX hXk => ?_
    have hXY : conjAut (conjAut X m⁻¹) m = X := conjAut_conjAut_inv X m
    have hYP : conjAut X m⁻¹ ≤ P := by
      rw [← conjAut_le_conjAut (m := m), hXY]
      exact hX
    have hYk : mQuot P (conjAut X m⁻¹) ≤ k := by
      rw [← mQuot_conjAut P _ m, hXY]
      exact hXk
    rw [← hXY, fixV_conjAut]
    exact Subgroup.map_mono (fixV_le_gammaCheck hYP hYk)
  · rw [Subgroup.map_le_iff_le_comap]
    refine gammaCheck_le fun Y hY hYk => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← fixV_conjAut]
    exact fixV_le_gammaCheck (conjAut_le_conjAut.mpr hY) (by rw [mQuot_conjAut]; exact hYk)

theorem card_gammaCheck_conjAut (k : ℕ) (P : Subgroup (MulAut W)) (m : MulAut W) :
    Nat.card (gammaCheck k (conjAut P m)) = Nat.card (gammaCheck k P) := by
  rw [gammaCheck_conjAut]
  exact Subgroup.card_map_of_injective (f := m.toMonoidHom) m.injective

theorem card_W [Finite W] {n : ℕ} {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
    (hyp : H9Hyp n M L T W₁ W₂) : Nat.card W = 2 ^ n * 2 ^ n := by
  obtain ⟨t, -, -, ht⟩ := hyp.swap
  have h2 : Nat.card W₂ = 2 ^ n := by
    rw [ht, Subgroup.card_map_of_injective (f := t.toMonoidHom) t.injective, hyp.card₁]
  have hbij : Function.Bijective (fun g => g.1 * g.2 : W₁ × W₂ → W) := by
    refine ⟨Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hyp.inf), fun w => ?_⟩
    have hw : w ∈ W₁ ⊔ W₂ := by
      rw [hyp.sup]
      exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hw
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hyz⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hyp.card₁, h2]

theorem card_gammaCheck_three_of_lemH93Use (hH93 : LemH93Use) [Finite W]
    {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} (hyp : H9Hyp 4 M L T W₁ W₂)
    {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hA : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 4) :
    2 ^ 7 ≤ Nat.card (gammaCheck 3 A) := by
  obtain ⟨A₀, A₁, A₂, -, hconj, ⟨-, hA₀⟩, -, -, h7⟩ := hH93 W M L T W₁ W₂ hyp
  obtain ⟨m, -, hm⟩ := hconj A hAM hA hcard
  rcases hm with h | h | h <;> rw [h, card_gammaCheck_conjAut]
  · have h1 : gammaCheck 3 A₀ = ⊤ := by
      rw [eq_top_iff, ← hA₀]
      exact gammaCheck_mono (by norm_num) _
    rw [h1, Subgroup.card_top, card_W hyp]
    norm_num
  · exact (h7 A₁ (Set.mem_insert _ _)).2.2
  · exact (h7 A₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2.2

theorem e16_facts_of_lemH93Use (hH93 : LemH93Use) [Finite W] {M L T : Subgroup (MulAut W)}
    {W₁ W₂ : Subgroup W} (hyp : H9Hyp 4 M L T W₁ W₂) {A : Subgroup (MulAut W)} (hAM : A ≤ M)
    (hA : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 4) :
    Nat.card (fixV A) ≠ 2 ^ 3 ∧ (gammaCheck 2 A ≠ ⊤ →
      Nat.card (gammaCheck 2 A) = 2 ^ 6 ∧ Nat.card (fixV A) ≤ 2 ^ 2 ∧
        (Nat.card (fixV A) = 2 ^ 2 → ∀ a ∈ A, (∀ w ∈ gammaCheck 2 A, a w = w) → a = 1)) := by
  obtain ⟨A₀, A₁, A₂, -, hconj, ⟨hA₀c, hA₀⟩, ⟨hA₁c, hA₁g⟩, ⟨hA₂c, hA₂g, hfaith⟩, -⟩ :=
    hH93 W M L T W₁ W₂ hyp
  obtain ⟨m, -, hm⟩ := hconj A hAM hA hcard
  rcases hm with rfl | rfl | rfl
  · refine ⟨by rw [card_fixV_conjAut, hA₀c]; norm_num, fun h => absurd ?_ h⟩
    rw [gammaCheck_conjAut, hA₀]
    exact Subgroup.map_top_of_surjective _ m.surjective
  · refine ⟨by rw [card_fixV_conjAut, hA₁c]; norm_num, fun _ =>
      ⟨by rw [card_gammaCheck_conjAut, hA₁g], by rw [card_fixV_conjAut, hA₁c]; norm_num,
        fun h => by rw [card_fixV_conjAut, hA₁c] at h; norm_num at h⟩⟩
  · refine ⟨by rw [card_fixV_conjAut, hA₂c]; norm_num, fun _ =>
      ⟨by rw [card_gammaCheck_conjAut, hA₂g], by rw [card_fixV_conjAut, hA₂c],
        fun _ x hx hfix => ?_⟩⟩
    have h1 : m⁻¹ * x * m = 1 := hfaith _ (mem_conjAut.mp hx) fun w hw => by
      have hmw : m w ∈ gammaCheck 2 (conjAut A₂ m) := by
        rw [gammaCheck_conjAut]
        exact Subgroup.mem_map_of_mem m.toMonoidHom hw
      have h2 := hfix _ hmw
      simp only [MulAut.mul_apply]
      rw [h2]
      simp
    calc x = m * (m⁻¹ * x * m) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem conjAut_one (A : Subgroup (MulAut W)) : conjAut A 1 = A := by
  ext x
  rw [mem_conjAut]
  simp

theorem map_eq_of_mem_stabV {U : Subgroup W} {l : MulAut W} (hl : l ∈ stabV U) :
    U.map l.toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hl y).mp hy
  · intro hx
    refine ⟨l⁻¹ x, ?_, by simp⟩
    have h := hl (l⁻¹ x)
    rw [show l (l⁻¹ x) = x from MulAut.apply_inv_self _ _ _] at h
    exact h.mpr hx

theorem map_W₁_of_not_mem {n : ℕ} {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
    (hyp : H9Hyp n M L T W₁ W₂) {m : MulAut W} (hmM : m ∈ M) (hmL : m ∉ L) :
    W₁.map m.toMonoidHom = W₂ := by
  obtain ⟨t, htT, htL, ht⟩ := hyp.swap
  have htM : t ∈ M := hyp.sylow_le htT
  have hidx : (L.subgroupOf M).index = 2 := hyp.index
  have hl : t⁻¹ * m ∈ L := by
    have h := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, htM⟩ : ↥M)⁻¹) (b := ⟨m, hmM⟩)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h.mpr ⟨fun h1 => absurd (by simpa using L.inv_mem h1) htL, fun h1 => absurd h1 hmL⟩
  have e : W₁.map m.toMonoidHom = (W₁.map (t⁻¹ * m).toMonoidHom).map t.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [e, map_eq_of_mem_stabV (hyp.inv₁ hl), ht]

theorem card_fixV_inf_le_of_lemH92 (hH92 : LemH92) [Finite W] {M L T : Subgroup (MulAut W)}
    {W₁ W₂ : Subgroup W} {β : W → W → ZMod 2} (hyp : H9Hyp 5 M L T W₁ W₂)
    (hβ : IsDualH9 L W₁ W₂ β) {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hA : IsElemAbelian2 A)
    (hcard : 2 ^ 5 ≤ Nat.card A) :
    Nat.card ↥(fixV A ⊓ W₁) ≤ 2 ^ 2 ∨ Nat.card ↥(fixV A ⊓ W₂) ≤ 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨U, hUW₁, hUcard, -, h3a, h3b, h4⟩, -⟩ := hH92 W M L T W₁ W₂ β hyp hβ
  have hAp : IsPGroup 2 ↥A := isPGroup_of_isElemAbelian2 hA
  have hdvd : 2 ^ 5 ∣ Nat.card ↥A := by
    rw [card_eq_two_pow_of_isPGroup hAp] at hcard ⊢
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hcard)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hA'A : K.map A.subtype ≤ A := Subgroup.map_subtype_le K
  have hA'card : Nat.card (K.map A.subtype) = 2 ^ 5 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hA'e : IsElemAbelian2 (K.map A.subtype) :=
    ⟨fun x hx y hy => hA.1 x (hA'A hx) y (hA'A hy), fun x hx => hA.2 x (hA'A hx)⟩
  obtain ⟨m, hmM, hm⟩ := h3b _ (hA'A.trans hAM) hA'e hA'card
  have hA₀M : pCoreOf 2 (L ⊓ stabV U) ≤ M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans hyp.le)
  have hA₀card : Nat.card (pCoreOf 2 (L ⊓ stabV U)) = 2 ^ 6 :=
    ((h3a _ hA₀M).mpr ⟨1, M.one_mem, (conjAut_one _).symm⟩).2
  obtain ⟨-, -, -, hdesc, hF⟩ := h4 (conjAut (K.map A.subtype) m) hm
    (by rw [card_conjAut, hA'card, hA₀card]; norm_num)
  have hβ1 : ∀ u ∈ W₁, β u 1 = 0 := fun u hu => by
    have h := hβ.2.1 u hu 1 W₂.one_mem 1 W₂.one_mem
    rw [mul_one, CharTwo.add_self_eq_zero] at h
    exact h
  have hUF : U ≤ fixV (conjAut (K.map A.subtype) m) := fun u hu =>
    (hdesc u).mpr ⟨u, hu, 1, W₂.one_mem, fun u' hu' => hβ1 u' (hUW₁ hu'), (mul_one u).symm⟩
  have hdisj : Disjoint U (fixV (conjAut (K.map A.subtype) m) ⊓ W₂) := by
    rw [disjoint_iff, eq_bot_iff, ← hyp.inf]
    exact inf_le_inf hUW₁ inf_le_right
  have hinj : Function.Injective (fun p : ↥U × ↥(fixV (conjAut (K.map A.subtype) m) ⊓ W₂) =>
      (⟨(p.1 : W) * p.2, (fixV (conjAut (K.map A.subtype) m)).mul_mem (hUF p.1.2) p.2.2.1⟩ :
        ↥(fixV (conjAut (K.map A.subtype) m)))) := by
    intro p q hpq
    exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val hpq)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hUcard, hF] at hle
  have hF2 : Nat.card ↥(fixV (conjAut (K.map A.subtype) m) ⊓ W₂) ≤ 2 ^ 2 := by omega
  rw [fixV_conjAut] at hF2
  by_cases hmL : m ∈ L
  · right
    rw [← map_eq_of_mem_stabV (hyp.inv₂ hmL), ← Subgroup.map_inf_eq _ _ _ m.injective,
      Subgroup.card_map_of_injective (f := m.toMonoidHom) m.injective] at hF2
    exact (Subgroup.card_le_of_le (inf_le_inf_right _ (B1.fixV_le_fixV hA'A))).trans hF2
  · left
    rw [← map_W₁_of_not_mem hyp hmM hmL, ← Subgroup.map_inf_eq _ _ _ m.injective,
      Subgroup.card_map_of_injective (f := m.toMonoidHom) m.injective] at hF2
    exact (Subgroup.card_le_of_le (inf_le_inf_right _ (B1.fixV_le_fixV hA'A))).trans hF2

theorem lemH93Use_of_lemH93 (hH93 : LemH93) : LemH93Use := by
  intro W _ _ M L T W₁ W₂ hyp
  obtain ⟨-, -, -, A₁, A₂, hAi, -, hA₂L, hconj, -, -, -, -, ⟨hA₀c, hA₀⟩,
    ⟨hA₁c, r, -, -, -, hr, hrc⟩, h6, h7, hfaith⟩ := hH93 W M L T W₁ W₂ hyp
  obtain ⟨a, ha, haL⟩ := Set.not_subset.mp hA₂L
  obtain ⟨-, h6c, -, h6g⟩ := h6 a ha haL
  exact ⟨_, A₁, A₂, hAi, hconj, ⟨hA₀c, hA₀⟩, ⟨hA₁c, by rw [hr, hrc]⟩, ⟨h6c, h6g, hfaith⟩, h7⟩

theorem lemH92Use_of_lemH92 (hH92 : LemH92) : LemH92Use := by
  intro W _ _ M L T W₁ W₂ β hyp hβ A hAM hA hcard
  obtain ⟨-, h2, -, h5⟩ := hH92 W M L T W₁ W₂ β hyp hβ
  exact ⟨h2 A hAM hA hcard, h5 A hAM hA hcard,
    card_fixV_inf_le_of_lemH92 hH92 hyp hβ hAM hA hcard⟩

end H9Conj

namespace Sec121Tr

variable {G : Type} [Group G] {V : Subgroup G}

open Sec121H9

theorem card_commV_autI (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (commV (autI hV X)) = Nat.card (⁅X, V⁆ : Subgroup G) := by
  have hmap : (commV (autI hV X)).map (valHom hV) = ⁅X, V⁆ := by
    unfold commV
    rw [MonoidHom.map_closure, Subgroup.commutator_def]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, w, rfl⟩, rfl⟩
      obtain ⟨⟨b, hbN⟩, hbX, rfl⟩ := (mem_autI hV).1 ha
      refine ⟨b, hbX, w.val, w.val_mem, ?_⟩
      rw [valHom_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
    · rintro ⟨b, hbX, y, hy, rfl⟩
      refine ⟨_, ⟨convI hV ⟨b, hXN hbX⟩, convI_mem_autI hV hbX (hXN hbX), IntMod.mk hV ⟨y, hy⟩,
        rfl⟩, ?_⟩
      rw [valHom_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
      rfl
  rw [← hmap, Subgroup.card_map_of_injective (valHom_injective hV)]

theorem card_closure_comm (hV : IsElemAbelian 2 V) {B Y : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) (hYV : Y ≤ V) :
    Nat.card (Subgroup.closure
        {x : IntMod V hV | ∃ a ∈ autI hV B, ∃ w ∈ subI hV Y, x = a w * w⁻¹}) =
      Nat.card (⁅B, Y⁆ : Subgroup G) := by
  have hmap : (Subgroup.closure
      {x : IntMod V hV | ∃ a ∈ autI hV B, ∃ w ∈ subI hV Y, x = a w * w⁻¹}).map (valHom hV) =
        ⁅B, Y⁆ := by
    rw [MonoidHom.map_closure, Subgroup.commutator_def]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, w, hw, rfl⟩, rfl⟩
      obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := (mem_autI hV).1 ha
      refine ⟨b, hbB, w.val, hw, ?_⟩
      rw [valHom_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
    · rintro ⟨b, hbB, y, hy, rfl⟩
      refine ⟨_, ⟨convI hV ⟨b, hBN hbB⟩, convI_mem_autI hV hbB (hBN hbB),
        IntMod.mk hV ⟨y, hYV hy⟩, hy, rfl⟩, ?_⟩
      rw [valHom_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
      rfl
  rw [← hmap, Subgroup.card_map_of_injective (valHom_injective hV)]

theorem card_fixV_autI_inf_subI (hV : IsElemAbelian 2 V) {B Y : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) (hYV : Y ≤ V) :
    Nat.card ↥(fixV (autI hV B) ⊓ subI hV Y) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (B : Set G)) := by
  have e : fixV (autI hV B) ⊓ subI hV Y = subI hV (Y ⊓ Subgroup.centralizer (B : Set G)) := by
    ext v
    rw [Subgroup.mem_inf, mem_fixV_autI hV hBN, mem_subI, mem_subI, Subgroup.mem_inf]
    exact and_comm
  rw [e, card_subI hV (inf_le_left.trans hYV)]

end Sec121Tr

theorem isDualH9_of_isDualPairing121 {G : Type} [Group G] {L V V₁ V₂ : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) {β : G → G → ZMod 2}
    (hβ : IsDualPairing121 L V₁ V₂ β) :
    IsDualH9 (autI hV L) (subI hV V₁) (subI hV V₂) (fun w w' => β w.val w'.val) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hβ
  refine ⟨fun a ha b hb c hc => ?_, fun a ha c hc d hd => ?_, fun a ha ha1 => ?_,
    fun c hc hc1 => ?_, fun l hl a ha c hc => ?_⟩
  · show β (a * b).val c.val = β a.val c.val + β b.val c.val
    rw [IntMod.val_mul]
    exact h1 _ ha _ hb _ hc
  · show β a.val (c * d).val = β a.val c.val + β a.val d.val
    rw [IntMod.val_mul]
    exact h2 _ ha _ hc _ hd
  · have ha1' : a.val ≠ 1 := fun h => ha1 (IntMod.val_injective (h.trans IntMod.val_one.symm))
    obtain ⟨c, hc, hac⟩ := h3 a.val ha ha1'
    exact ⟨IntMod.mk hV ⟨c, hV₂V hc⟩, hc, hac⟩
  · have hc1' : c.val ≠ 1 := fun h => hc1 (IntMod.val_injective (h.trans IntMod.val_one.symm))
    obtain ⟨a, ha, hac⟩ := h4 c.val hc hc1'
    exact ⟨IntMod.mk hV ⟨a, hV₁V ha⟩, ha, hac⟩
  · obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := (mem_autI hV).1 hl
    show β (convI hV ⟨g, hgN⟩ a).val (convI hV ⟨g, hgN⟩ c).val = β a.val c.val
    rw [convI_apply_val, convI_apply_val]
    exact h5 g hgL a.val ha c.val hc

end CFSG.Quasithin.H13
