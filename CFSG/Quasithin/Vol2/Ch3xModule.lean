module

public import CFSG.Quasithin.EmptyFaithful.S1417System
public import CFSG.Quasithin.Background.E2SolvBaumann
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ch3x

theorem exists_card_three_sq_mem {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : Nat.card L = 6) :
    ∃ A : Subgroup X, A ≤ L ∧ Nat.card A = 3 ∧ ∀ l ∈ L, l ^ 2 ∈ A := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥L))
  have hP : Nat.card (P : Subgroup ↥L) = 3 := by
    rw [P.card_eq_multiplicity, hL]
    have h6 : (6 : ℕ).factorization 3 = 1 := by
      have : (6 : ℕ) = 2 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization Nat.prime_three, Nat.Prime.factorization Nat.prime_two]
    rw [h6]; norm_num
  have hidx : (P : Subgroup ↥L).index = 2 := by
    have := (P : Subgroup ↥L).card_mul_index
    rw [hL, hP] at this
    omega
  have hn : (P : Subgroup ↥L).Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨(P : Subgroup ↥L).map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hP]
  · intro l hl
    have h1 := Subgroup.pow_index_mem (P : Subgroup ↥L) (⟨l, hl⟩ : ↥L)
    rw [hidx] at h1
    exact ⟨_, h1, rfl⟩


section Blocks

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_eq_six_of_actsAsNaturalL2 {L : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ActsAsNaturalL2 L U) : Nat.card L = 6 := by
  obtain ⟨e, -, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem exists_mul_of_mem_sup_of_commute {Z : Type*} [Group Z] {a B : Subgroup Z}
    (hcomm : ∀ l ∈ a, ∀ z ∈ B, l * z = z * l) {y : Z} (hy : y ∈ a ⊔ B) :
    ∃ l ∈ a, ∃ z ∈ B, y = l * z := by
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, a.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, a.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, z, hz, rfl⟩ := hx
    obtain ⟨l', hl', z', hz', rfl⟩ := hy
    refine ⟨l * l', a.mul_mem hl hl', z * z', B.mul_mem hz hz', ?_⟩
    have h := hcomm l' hl' z hz
    calc l * z * (l' * z') = l * (z * l') * z' := by group
      _ = l * (l' * z) * z' := by rw [h]
      _ = l * l' * (z * z') := by group
  | inv x _ hx =>
    obtain ⟨l, hl, z, hz, rfl⟩ := hx
    refine ⟨l⁻¹, a.inv_mem hl, z⁻¹, B.inv_mem hz, ?_⟩
    have h := hcomm l hl z hz
    have h' : z⁻¹ * l⁻¹ = l⁻¹ * z⁻¹ := by
      calc z⁻¹ * l⁻¹ = (l * z)⁻¹ := by group
        _ = (z * l)⁻¹ := by rw [h]
        _ = l⁻¹ * z⁻¹ := by group
    rw [mul_inv_rev, h']

theorem exists_odd_sq_mem_of_blockSystem {Xg Y : Subgroup (MulAut W)}
    {I : Finset (Subgroup (MulAut W))} (hS : S1417.BlockSystem Xg Y I) :
    ∃ Y₃ : Subgroup (MulAut W), Y₃ ≤ Y ∧ Odd (Nat.card Y₃) ∧ ∀ y ∈ Y, y ^ 2 ∈ Y₃ := by
  classical
  have key : ∀ s : Finset (Subgroup (MulAut W)), s ⊆ I →
      ∃ A : Subgroup (MulAut W), A ≤ ⨆ L ∈ s, L ∧ Odd (Nat.card A) ∧
        ∀ y ∈ (⨆ L ∈ s, L : Subgroup (MulAut W)), y ^ 2 ∈ A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨⊥, bot_le, by simp, fun y hy => ?_⟩
      have : y = 1 := by simpa using hy
      simp [this]
    | insert a s ha ih =>
      intro hsub
      have haI : a ∈ I := hsub (Finset.mem_insert_self a s)
      obtain ⟨A₀, hA₀, hA₀odd, hA₀sq⟩ := ih ((Finset.subset_insert a s).trans hsub)
      obtain ⟨Aa, hAaL, hAa3, hAasq⟩ :=
        exists_card_three_sq_mem (card_eq_six_of_actsAsNaturalL2 (hS.nat a haI))
      have hcomm : ∀ l ∈ a, ∀ y ∈ (⨆ L ∈ s, L : Subgroup (MulAut W)), l * y = y * l := by
        intro l hl y hy
        have hle : (⨆ L ∈ s, L : Subgroup (MulAut W)) ≤
            Subgroup.centralizer ({l} : Set (MulAut W)) := by
          refine iSup₂_le fun L hL x hx => ?_
          have hLI : L ∈ I := hsub (Finset.mem_insert_of_mem hL)
          have hne : a ≠ L := fun h => ha (h ▸ hL)
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact hS.comm a haI L hLI hne l hl x hx
        exact Subgroup.mem_centralizer_iff.mp (hle hy) l (Set.mem_singleton l)
      refine ⟨Aa ⊔ A₀, ?_, ?_, ?_⟩
      · rw [Finset.iSup_insert (t := fun L : Subgroup (MulAut W) => L)]
        exact sup_le_sup hAaL hA₀
      · have hc : ∀ x ∈ Aa, ∀ z ∈ A₀, x * z = z * x := fun x hx z hz =>
          hcomm x (hAaL hx) z (hA₀ hz)
        have h1 := B2F.card_sup_mul_card_inf_of_commute (A := Aa) (B := A₀) hc
        have h2 : Odd (Nat.card ↥(Aa ⊔ A₀) * Nat.card ↥(Aa ⊓ A₀)) := by
          rw [h1, hAa3]; exact Nat.odd_mul.mpr ⟨by decide, hA₀odd⟩
        exact (Nat.odd_mul.mp h2).1
      · intro y hy
        rw [Finset.iSup_insert (t := fun L : Subgroup (MulAut W) => L)] at hy
        obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
        have h := hcomm l hl z hz
        have e : (l * z) ^ 2 = l ^ 2 * z ^ 2 := by
          calc (l * z) ^ 2 = l * z * (l * z) := pow_two _
            _ = l * (z * l) * z := by group
            _ = l * (l * z) * z := by rw [← h]
            _ = l ^ 2 * z ^ 2 := by rw [pow_two, pow_two]; group
        rw [e]
        exact Subgroup.mul_mem_sup (hAasq l hl) (hA₀sq z hz)
  obtain ⟨A, hA, hodd, hsq⟩ := key I le_rfl
  exact ⟨A, hA.trans (le_of_eq hS.Y_eq.symm), hodd, fun y hy => hsq y (hS.Y_eq ▸ hy)⟩


end Blocks

section Reduced

variable {Q : Type*} [CommGroup Q]

theorem exists_fixed_ne_one_of_two_elements [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {P D : Subgroup (MulAut Q)} (hDP : D ≤ P) {W : Subgroup Q}
    (hW : ∀ p ∈ P, ∀ w ∈ W, p w ∈ W) (hne : W ≠ ⊥)
    (hD : ∀ d ∈ D, ∃ k : ℕ, ∀ w ∈ W, (d ^ 2 ^ k) w = w) :
    ∃ m ∈ W, m ≠ 1 ∧ ∀ d ∈ D, d m = m := by
  have hstab : D ≤ stabSub W := by
    intro d hd w
    constructor
    · intro h
      have h1 := hW d⁻¹ (P.inv_mem (hDP hd)) _ h
      simpa using h1
    · exact hW d (hDP hd) w
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hQ w)
  have hB : IsPGroup 2 ↥(autSub D W) := by
    intro φ
    obtain ⟨g, hgD, hφ⟩ := mem_autSub.mp φ.2
    obtain ⟨k, hk⟩ := hD (g : MulAut Q) hgD
    refine ⟨k, Subtype.ext ?_⟩
    show (φ : MulAut ↥W) ^ 2 ^ k = 1
    rw [← hφ, ← map_pow]
    ext w
    have hw := hk w.1 w.2
    have h1 : ((g ^ 2 ^ k : stabSub W) : MulAut Q) = (g : MulAut Q) ^ 2 ^ k := rfl
    show ((resHom W (g ^ 2 ^ k) w : W) : Q) = w.1
    rw [resHom_apply, h1]
    exact hw
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hTop : (⊤ : Subgroup ↥W) ≠ ⊥ := by
    intro h
    have : a ∈ (⊥ : Subgroup ↥W) := h ▸ trivial
    exact ha1 (Subgroup.mem_bot.mp this)
  obtain ⟨m, -, hm1, hmfix⟩ :=
    B1.exists_fixed_ne_one hW2 hB (M := ⊤) (fun _ _ _ _ => trivial) hTop
  refine ⟨m.1, m.2, fun h => hm1 (Subtype.ext h), fun d hd => ?_⟩
  have := hmfix (resHom W ⟨d, hstab hd⟩) (mem_autSub.mpr ⟨⟨d, hstab hd⟩, hd, rfl⟩)
  have h2 := congrArg Subtype.val this
  rwa [resHom_apply] at h2

theorem exists_twoReduced_minimal [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {P K : Subgroup (MulAut Q)} (hKP : K ≤ P) (hKn : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (hne : commSub (⊤ : Subgroup Q) K ≠ ⊥) :
    ∃ W : Subgroup Q, (∀ p ∈ P, ∀ w ∈ W, p w ∈ W) ∧ commSub W K ≠ ⊥ ∧
      ∀ D : Subgroup (MulAut Q), D ≤ P → (∀ p ∈ P, ∀ d ∈ D, p * d * p⁻¹ ∈ D) →
        (∀ d ∈ D, ∃ k : ℕ, ∀ w ∈ W, (d ^ 2 ^ k) w = w) → ∀ d ∈ D, ∀ w ∈ W, d w = w := by
  classical
  let S : Set (Subgroup Q) := {W | (∀ p ∈ P, ∀ w ∈ W, p w ∈ W) ∧ commSub W K ≠ ⊥}
  have hS : S.Nonempty := ⟨⊤, fun _ _ _ _ => trivial, hne⟩
  obtain ⟨W, hW⟩ := (Set.toFinite S).exists_minimal hS
  obtain ⟨hWP, hWne⟩ := hW.prop
  have hWK : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W := fun k hk => hWP k (hKP hk)
  have hcommP : ∀ p ∈ P, ∀ c ∈ commSub W K, p c ∈ commSub W K := by
    intro p hp c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hc
      refine Subgroup.subset_closure ⟨p * x * p⁻¹, hKn p hp x hx, p w, hWP p hp w hw, ?_⟩
      simp [MulAut.mul_apply]
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact (commSub W K).mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact (commSub W K).inv_mem ha
  have hW'le : commSub W K ≤ W := commSub_le_of_invariant hWK
  have hdec := B1.coprime_decomp hQ hodd (M := W) hWK
  have hW'K : ∀ y ∈ K, ∀ m ∈ commSub W K, y m ∈ commSub W K := fun y hy => hcommP y (hKP hy)
  have hdec' := B1.coprime_decomp hQ hodd (M := commSub W K) hW'K
  have hfixW' : commSub W K ⊓ fixV K = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hdec.2]
    intro x hx
    exact ⟨⟨hW'le hx.1, hx.2⟩, hx.1⟩
  have hidem : commSub (commSub W K) K = commSub W K := by
    have := hdec'.1
    rwa [hfixW', bot_sup_eq] at this
  have hcomm_eq : commSub W K = W := by
    refine le_antisymm hW'le (hW.2 (y := commSub W K) ⟨hcommP, ?_⟩ hW'le)
    rw [hidem]
    exact hWne
  have hfixW : W ⊓ fixV K = ⊥ := by
    have := hdec.2
    rwa [hcomm_eq, inf_eq_left.mpr inf_le_left] at this
  have hWbot : W ≠ ⊥ := fun h => hWne (le_bot_iff.mp (h ▸ hW'le))
  refine ⟨W, hWP, hWne, ?_⟩
  intro D hDP hDn hD d hd w hw
  by_contra hdw
  set W₀ : Subgroup Q := W ⊓ fixV D with hW₀
  have hW₀P : ∀ p ∈ P, ∀ x ∈ W₀, p x ∈ W₀ := by
    intro p hp x hx
    refine ⟨hWP p hp x hx.1, fun e he => ?_⟩
    have h1 := hx.2 (p⁻¹ * e * p) (by simpa [mul_assoc] using hDn p⁻¹ (P.inv_mem hp) e he)
    have h2 : (e * p) x = p x := by
      have := congrArg p h1
      simpa [MulAut.mul_apply] using this
    simpa [MulAut.mul_apply] using h2
  obtain ⟨m, hmW, hm1, hmfix⟩ := exists_fixed_ne_one_of_two_elements hQ hDP hWP hWbot hD
  have hW₀ne : W₀ ≠ ⊥ := fun h => hm1 (Subgroup.mem_bot.mp (h ▸ (⟨hmW, hmfix⟩ : m ∈ W₀)))
  have hW₀le : W₀ ≤ W := inf_le_left
  have hcomm0 : commSub W₀ K = ⊥ := by
    by_contra hc
    have := hW.2 (y := W₀) ⟨hW₀P, hc⟩ hW₀le hw
    exact hdw (this.2 d hd)
  have hle : W₀ ≤ fixV K := commSub_eq_bot_iff.mp hcomm0
  exact hW₀ne (le_bot_iff.mp (hfixW ▸ le_inf hW₀le hle))


end Reduced

section Translate

variable {G : Type} [Group G] [Finite G]

theorem exists_internal_twoReduced {P K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hPN : P ≤ Subgroup.normalizer (V : Set G)) (hVP : V ≤ P) (hKP : K ≤ P)
    (hKn : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K)
    (hodd : Odd (Nat.card (autI hV K))) (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    ∃ W : Subgroup G, W ≤ V ∧ IsElemAbelian 2 W ∧ IsTwoReducedIn P W ∧
      ¬ P ≤ Subgroup.centralizer (W : Set G) := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKP.trans hPN
  have hKP' : autI hV K ≤ autI hV P := autI_mono hV hKP
  have hconj : ∀ (g h : Subgroup.normalizer (V : Set G)),
      convI hV g * convI hV h * (convI hV g)⁻¹ = convI hV (g * h * g⁻¹) := by
    intro g h
    simp [map_mul, map_inv]
  have hKn' : ∀ p ∈ autI hV P, ∀ k ∈ autI hV K, p * k * p⁻¹ ∈ autI hV K := by
    intro p hp k hk
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hp
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hk
    rw [hconj]
    exact (mem_autI hV).2 ⟨g * h * g⁻¹, hKn _ hg _ hh, rfl⟩
  have hne : commSub (⊤ : Subgroup (IntMod V hV)) (autI hV K) ≠ ⊥ := by
    intro h
    have h1 : (⊤ : Subgroup (IntMod V hV)) ≤ fixV (autI hV K) := commSub_eq_bot_iff.mp h
    have h2 := E2.map_valHom_fixV (hV := hV) hKN
    apply hKV
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have : v ∈ (fixV (autI hV K)).map (E2.valHom hV) :=
      ⟨IntMod.mk hV ⟨v, hv⟩, h1 trivial, rfl⟩
    rw [h2] at this
    exact (Subgroup.mem_centralizer_iff.mp this.2 k hk).symm
  obtain ⟨W₀, hW₀P, hW₀ne, hW₀red⟩ :=
    exists_twoReduced_minimal (fun q : IntMod V hV => IntMod.sq_eq_one q) hKP' hKn' hodd hne
  set W : Subgroup G := W₀.map (E2.valHom hV) with hW
  have hWV : W ≤ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.val_mem
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono hWV hV
  have hWmem : ∀ p ∈ P, ∀ x ∈ W, p * x * p⁻¹ ∈ W := by
    intro p hp x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hpv : convI hV ⟨p, hPN hp⟩ ∈ autI hV P := (mem_autI hV).2 ⟨⟨p, hPN hp⟩, hp, rfl⟩
    exact ⟨_, hW₀P _ hpv w hw, convI_apply_val hV ⟨p, hPN hp⟩ w⟩
  have hPW : P ≤ Subgroup.normalizer (W : Set G) := fun p hp =>
    B6.mem_normalizer_of_forall_mem (fun x hx => hWmem p hp x hx) (fun x hx => by
      simpa using hWmem p⁻¹ (P.inv_mem hp) x hx)
  have hred : IsTwoReducedIn P W := by
    refine ⟨hWV.trans hVP, hPW, hWel, ?_⟩
    intro D hDP hDn hD d hd
    have hDn' : ∀ p ∈ P, ∀ e ∈ D, p * e * p⁻¹ ∈ D := fun p hp e he =>
      (Subgroup.mem_normalizer_iff.mp (hDn hp) e).mp he
    have hnorm : ∀ p ∈ autI hV P, ∀ e ∈ autI hV D, p * e * p⁻¹ ∈ autI hV D := by
      intro p hp e he
      obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hp
      obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 he
      rw [hconj]
      exact (mem_autI hV).2 ⟨g * h * g⁻¹, hDn' _ hg _ hh, rfl⟩
    have htwo : ∀ φ ∈ autI hV D, ∃ k : ℕ, ∀ w ∈ W₀, (φ ^ 2 ^ k) w = w := by
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
      obtain ⟨k, hk⟩ := hD g hg
      refine ⟨k, fun w hw => ?_⟩
      apply IntMod.val_injective
      rw [← map_pow]
      show (convI hV (g ^ 2 ^ k) w).val = w.val
      rw [convI_apply_val]
      have h1 := Subgroup.mem_centralizer_iff.mp hk (E2.valHom hV w) ⟨w, hw, rfl⟩
      have e : ((g ^ 2 ^ k : Subgroup.normalizer (V : Set G)) : G) = (g : G) ^ 2 ^ k := rfl
      rw [e]
      calc (g : G) ^ 2 ^ k * w.val * ((g : G) ^ 2 ^ k)⁻¹ =
          ((g : G) ^ 2 ^ k * w.val) * ((g : G) ^ 2 ^ k)⁻¹ := rfl
        _ = w.val := by
          have h2 : (g : G) ^ 2 ^ k * w.val = w.val * (g : G) ^ 2 ^ k := h1.symm
          rw [h2, mul_inv_cancel_right]
    have hfix := hW₀red (autI hV D) (autI_mono hV hDP) hnorm htwo
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have h1 := hfix (convI hV ⟨d, hPN (hDP hd)⟩) ((mem_autI hV).2 ⟨⟨d, hPN (hDP hd)⟩, hd, rfl⟩) w hw
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    show (E2.valHom hV w) * d = d * (E2.valHom hV w)
    have h3 : d * w.val * d⁻¹ = w.val := h2
    calc (E2.valHom hV w) * d = (d * w.val * d⁻¹) * d := by rw [h3]; rfl
      _ = d * w.val := by group
  have hnc : ¬ P ≤ Subgroup.centralizer (W : Set G) := by
    intro hPC
    apply hW₀ne
    rw [commSub_eq_bot_iff]
    intro w hw k hk
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hk
    have hgC : (g : G) ∈ Subgroup.centralizer (W : Set G) := hPC (hKP hg)
    have h1 := Subgroup.mem_centralizer_iff.mp hgC (E2.valHom hV w) ⟨w, hw, rfl⟩
    apply IntMod.val_injective
    show (convI hV g w).val = w.val
    rw [convI_apply_val]
    calc (g : G) * w.val * (g : G)⁻¹ = ((g : G) * w.val) * (g : G)⁻¹ := rfl
      _ = w.val := by
        have h2 : (g : G) * w.val = w.val * (g : G) := h1.symm
        rw [h2, mul_inv_cancel_right]
  exact ⟨W, hWV, hWel, hred, hnc⟩

end Translate

section Odd

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_two_pow_mem_of_odd {N : Subgroup G} {x : G} {k : ℕ} (hx : Odd (orderOf x))
    (h : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hx)
  have h1 : x ∈ Subgroup.zpowers (x ^ 2 ^ k) := mem_zpowers_pow_iff.mpr hcop
  exact (Subgroup.zpowers_le.2 h) h1

omit [Finite G] in
theorem mem_of_sq_mem_of_odd {N : Subgroup G} {y : G} (ho : Odd (orderOf y)) (h : y ^ 2 ∈ N) :
    y ∈ N := by
  obtain ⟨m, hm⟩ := ho
  have h1 : y ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one y
  have : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc y = y ^ (2 * m + 1) * y := by rw [h1, one_mul]
      _ = y ^ (2 * (m + 1)) := by rw [← pow_succ]; exact congrArg _ (by omega)
  rw [this]
  exact N.pow_mem h _

theorem odd_mem_of_mem_sup_normalizer {J T : Subgroup G} (hT : IsPGroup 2 T)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) {x : G} (hx : x ∈ J ⊔ T)
    (ho : Odd (orderOf x)) : x ∈ J := by
  have hDN : T ⊔ J ≤ Subgroup.normalizer (J : Set G) := sup_le hTJ Subgroup.le_normalizer
  obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hT hDN rfl x (by rwa [sup_comm] at hx)
  exact mem_of_pow_two_pow_mem_of_odd ho hk

theorem odd_card_autI_oTwoUpper {M₁ T P V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : IsPGroup 2 T) (hTM : T ≤ M₁) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hPJ : P ≤ thompsonJ M₁ ⊔ T) {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hS : S1417.BlockSystem (autI hV M₁) (autI hV (thompsonJ M₁)) I) :
    Odd (Nat.card (autI hV (oTwoUpper P))) := by
  obtain ⟨Y₃, hY₃Y, hY₃odd, hY₃sq⟩ := exists_odd_sq_mem_of_blockSystem hS
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ M₁ : Set G) :=
    (hTM.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_thompsonJ M₁)
  have hgen : ∀ x ∈ P, Odd (orderOf x) → ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      convI hV ⟨x, hx⟩ ∈ Y₃ := by
    intro x hxP ho
    have hxJ : x ∈ thompsonJ M₁ := odd_mem_of_mem_sup_normalizer hT hTJ (hPJ hxP) ho
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hPN hxP
    refine ⟨hxN, ?_⟩
    have hy : convI hV ⟨x, hxN⟩ ∈ autI hV (thompsonJ M₁) :=
      (mem_autI hV).2 ⟨⟨x, hxN⟩, hxJ, rfl⟩
    have hodd : Odd (orderOf (convI hV ⟨x, hxN⟩)) := by
      have h1 : orderOf (convI hV ⟨x, hxN⟩) ∣ orderOf (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) :=
        orderOf_map_dvd (convI hV) _
      have h2 : orderOf (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) = orderOf x :=
        (orderOf_submonoid (H := (Subgroup.normalizer (V : Set G)).toSubmonoid)
          (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G))).symm
      exact Odd.of_dvd_nat (h2 ▸ ho) h1
    exact mem_of_sq_mem_of_odd hodd (hY₃sq _ hy)
  have hle : autI hV (oTwoUpper P) ≤ Y₃ := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    have key : ∀ z ∈ oTwoUpper P, ∃ hz : z ∈ Subgroup.normalizer (V : Set G),
        convI hV ⟨z, hz⟩ ∈ Y₃ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem x hx => exact hgen x hx.1 hx.2
      | one =>
        refine ⟨Subgroup.one_mem _, ?_⟩
        have h : convI hV (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (V : Set G)) = 1 := by
          rw [← map_one (convI hV)]; rfl
        rw [h]; exact Y₃.one_mem
      | mul a b _ _ iha ihb =>
        obtain ⟨hA, hA'⟩ := iha
        obtain ⟨hB, hB'⟩ := ihb
        refine ⟨Subgroup.mul_mem _ hA hB, ?_⟩
        have h : convI hV (⟨a * b, Subgroup.mul_mem _ hA hB⟩ : Subgroup.normalizer (V : Set G)) =
            convI hV ⟨a, hA⟩ * convI hV ⟨b, hB⟩ := by rw [← map_mul]; rfl
        rw [h]; exact Y₃.mul_mem hA' hB'
      | inv a _ iha =>
        obtain ⟨hA, hA'⟩ := iha
        refine ⟨Subgroup.inv_mem _ hA, ?_⟩
        have h : convI hV (⟨a⁻¹, Subgroup.inv_mem _ hA⟩ : Subgroup.normalizer (V : Set G)) =
            (convI hV ⟨a, hA⟩)⁻¹ := by rw [← map_inv]; rfl
        rw [h]; exact Y₃.inv_mem hA'
    obtain ⟨hz, hY⟩ := key g hg
    exact hY
  exact Odd.of_dvd_nat hY₃odd (Subgroup.card_dvd_of_le hle)

end Odd

end Ch3x

end CFSG.Quasithin
