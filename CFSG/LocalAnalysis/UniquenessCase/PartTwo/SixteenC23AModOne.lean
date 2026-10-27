module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open

variable {V : Type} [CommGroup V]

private def c23a_mulInvHom (x : MulAut V) : V →* V where
  toFun := fun e => x e * e⁻¹
  map_one' := by simp
  map_mul' := fun a b => by
    show x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl

private theorem c23a_mul_inv_mem_commSub (W : Subgroup V) (X : Subgroup (MulAut V))
    {x : MulAut V} (hx : x ∈ X) {e : V} (he : e ∈ W) : x e * e⁻¹ ∈ commSub W X :=
  Subgroup.subset_closure ⟨x, hx, e, he, rfl⟩

private theorem c23a_pow_mem {x : MulAut V} {E : Subgroup V} (hx : ∀ e ∈ E, x e ∈ E) (n : ℕ) :
    ∀ e ∈ E, (x ^ n) e ∈ E := by
  induction n with
  | zero => intro e he; simpa using he
  | succ n ih =>
      intro e he
      rw [pow_succ']
      simpa [MulAut.mul_apply] using hx ((x ^ n) e) (ih e he)

private theorem c23a_pow_apply_eq {x l : MulAut V} {E : Subgroup V}
    (hx : ∀ e ∈ E, x e ∈ E) (hl : ∀ e ∈ E, l e ∈ E) (h : ∀ e ∈ E, x e = l e) (n : ℕ) :
    ∀ e ∈ E, (x ^ n) e = (l ^ n) e := by
  induction n with
  | zero => intro e _; simp
  | succ n ih =>
      intro e he
      rw [pow_succ', pow_succ']
      simp only [MulAut.mul_apply]
      rw [← ih e he]
      exact h ((x ^ n) e) (c23a_pow_mem hx n e he)

private theorem c23a_commSub_sup (W₁ W₂ : Subgroup V) (X : Subgroup (MulAut V)) :
    commSub (W₁ ⊔ W₂) X = commSub W₁ X ⊔ commSub W₂ X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hw
    have h1 : x y * y⁻¹ ∈ commSub W₁ X := c23a_mul_inv_mem_commSub W₁ X hx hy
    have h2 : x z * z⁻¹ ∈ commSub W₂ X := c23a_mul_inv_mem_commSub W₂ X hx hz
    have hkey : x (y * z) * (y * z)⁻¹ = (x y * y⁻¹) * (x z * z⁻¹) := by
      rw [map_mul, mul_inv_rev]; ac_rfl
    rw [hkey]
    exact (commSub W₁ X ⊔ commSub W₂ X).mul_mem
      (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem c23a_commSub_zpowers_eq [Finite V] {E : Subgroup V} {x l : MulAut V}
    (hxE : ∀ e ∈ E, x e ∈ E) (hlE : ∀ e ∈ E, l e ∈ E) (h : ∀ e ∈ E, x e = l e) :
    commSub E (Subgroup.zpowers x) = commSub E (Subgroup.zpowers l) := by
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => MulEquiv.ext (congrFun h))
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, x ^ n = y := by
      have hy' : y ∈ Submonoid.powers x := (mem_powers_iff_mem_zpowers).2 hy
      exact (Submonoid.mem_powers_iff y x).1 hy'
    rw [c23a_pow_apply_eq hxE hlE h n w hw]
    exact c23a_mul_inv_mem_commSub E (Subgroup.zpowers l)
      (Subgroup.mem_zpowers_iff.2 ⟨(n : ℤ), zpow_natCast l n⟩) hw
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, l ^ n = y := by
      have hy' : y ∈ Submonoid.powers l := (mem_powers_iff_mem_zpowers).2 hy
      exact (Submonoid.mem_powers_iff y l).1 hy'
    rw [← c23a_pow_apply_eq hxE hlE h n w hw]
    exact c23a_mul_inv_mem_commSub E (Subgroup.zpowers x)
      (Subgroup.mem_zpowers_iff.2 ⟨(n : ℤ), zpow_natCast x n⟩) hw

private theorem c23a_block_smul_mem {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) {l : MulAut V} (hl : l ∈ L) : ∀ e ∈ E, l e ∈ E := by
  obtain ⟨D⟩ := h.nat
  obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
  intro e he
  have hcoe : ((D.ρ γ : ↥L) : MulAut V) = l := congrArg Subtype.val hγ
  rw [← hcoe]
  exact D.inv γ e he

private theorem c23a_orderOf_eq_two_pow_of_agree [Finite V] {L : Subgroup (MulAut V)}
    {E Z : Subgroup V} (hblk : C23ABlock L E Z) {t l : MulAut V}
    (hEt : ∀ e ∈ E, t e ∈ E) (hl : l ∈ L) (hlE : ∀ e ∈ E, l e ∈ E)
    (hagree : ∀ e ∈ E, t e = l e) {j : ℕ} (hj : orderOf t = 2 ^ j) :
    ∃ a : ℕ, orderOf l = 2 ^ a := by
  have htpow : t ^ (2 ^ j) = 1 := by rw [← hj]; exact pow_orderOf_eq_one t
  have hfix : ∀ e ∈ E, (l ^ (2 ^ j)) e = e := by
    intro e he
    have h1 : (t ^ (2 ^ j)) e = e := by rw [htpow, MulAut.one_apply]
    have h2 : (t ^ (2 ^ j)) e = (l ^ (2 ^ j)) e :=
      c23a_pow_apply_eq hEt hlE hagree (2 ^ j) e he
    rw [← h2, h1]
  have h1 : l ^ (2 ^ j) = 1 := c23a_eq_one_of_fix hblk (pow_mem hl _) hfix
  have hdvd : orderOf l ∣ 2 ^ j := orderOf_dvd_iff_pow_eq_one.2 h1
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨a, ha⟩

private theorem c23a_three_le_rk_commSub_of_swap [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {E Z E' : Subgroup V} (hblk : C23ABlock L E Z)
    (hinf : E ⊓ E' ≤ Z) {t : MulAut V} (hsw : ∀ e ∈ E, t e ∈ E') :
    3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  let f : ↥E →* V := (c23a_mulInvHom t).comp E.subtype
  have hf : ∀ e : ↥E, f e = t (e : V) * (e : V)⁻¹ := fun e => rfl
  have hker_le : Nat.card ↥f.ker ≤ Nat.card ↥Z := by
    refine Nat.card_le_card_of_injective
      (fun u : ↥f.ker => (⟨(u.1 : V), ?_⟩ : ↥Z))
      (fun u v huv => Subtype.ext (Subtype.ext (congrArg (fun z : ↥Z => (z : V)) huv)))
    have h1 : t (u.1 : V) * (u.1 : V)⁻¹ = 1 := by
      have h := u.2
      rw [MonoidHom.mem_ker] at h
      rwa [hf] at h
    have h2 : t (u.1 : V) = (u.1 : V) := mul_inv_eq_one.1 h1
    exact hinf ⟨u.1.2, h2 ▸ hsw _ u.1.2⟩
  have hrange_le : Nat.card ↥f.range ≤ Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥f.range => (⟨(x : V), ?_⟩ : ↥(commSub ⊤ (Subgroup.zpowers t))))
      (fun x y hxy =>
        Subtype.ext (congrArg (fun z : ↥(commSub ⊤ (Subgroup.zpowers t)) => (z : V)) hxy))
    obtain ⟨e, he⟩ := MonoidHom.mem_range.1 x.2
    rw [← he, hf]
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, (e : V), Subgroup.mem_top _, rfl⟩
  have hcardE : Nat.card ↥E = 2 ^ 3 * Nat.card ↥Z := c23a_block_card_eq hblk
  haveI : Nonempty ↥Z := ⟨⟨1, Z.one_mem⟩⟩
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hchain : 2 ^ 3 * Nat.card ↥Z ≤ Nat.card ↥Z *
      Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    rw [← hcardE, ← Subgroup.card_ker_mul_card_range f]
    exact Nat.mul_le_mul hker_le hrange_le
  have hleT : 2 ^ 3 ≤ Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) :=
    Nat.le_of_mul_le_mul_left (by rw [mul_comm (Nat.card ↥Z) (2 ^ 3)]; exact hchain) hZpos
  have hcardT : Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) =
      2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := card_eq_two_pow hV _
  have : 2 ^ 3 ≤ 2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by rwa [← hcardT]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this

theorem c23a_modPair_oneSided [Finite V] {Mb L₁ L₂ : Subgroup (MulAut V)}
    {E₁ E₂ Z₁ Z₂ : Subgroup V} (h : C23AModPair Mb L₁ L₂ E₁ E₂ Z₁ Z₂) {t : MulAut V}
    (ht : t ∈ Mb) (ht2 : ∃ j : ℕ, orderOf t = 2 ^ j) (ht1 : t ≠ 1)
    (hr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 2) :
    (((∀ y ∈ E₂, t y = y) ∧ commSub ⊤ (Subgroup.zpowers t) ≤ E₁) ∨
      ((∀ y ∈ E₁, t y = y) ∧ commSub ⊤ (Subgroup.zpowers t) ≤ E₂)) ∧
      2 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  classical
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => MulEquiv.ext (congrFun h))
  rcases h.perm t ht with ⟨hN₁, hN₂, hE₁, hE₂⟩ | ⟨hsw₁, hsw₂⟩
  · obtain ⟨l₁, hl₁, hl₁e⟩ := c23a_normalizer_act h.blk₁ hN₁ hE₁
    obtain ⟨l₂, hl₂, hl₂e⟩ := c23a_normalizer_act h.blk₂ hN₂ hE₂
    have hlE₁ : ∀ e ∈ E₁, l₁ e ∈ E₁ := c23a_block_smul_mem h.blk₁ hl₁
    have hlE₂ : ∀ e ∈ E₂, l₂ e ∈ E₂ := c23a_block_smul_mem h.blk₂ hl₂
    obtain ⟨j, hj⟩ := ht2
    have hl₁2 : ∃ a : ℕ, orderOf l₁ = 2 ^ a :=
      c23a_orderOf_eq_two_pow_of_agree h.blk₁ hE₁ hl₁ hlE₁ hl₁e hj
    have hl₂2 : ∃ a : ℕ, orderOf l₂ = 2 ^ a :=
      c23a_orderOf_eq_two_pow_of_agree h.blk₂ hE₂ hl₂ hlE₂ hl₂e hj
    let X₁ := commSub E₁ (Subgroup.zpowers l₁)
    let X₂ := commSub E₂ (Subgroup.zpowers l₂)
    have hX₁_le : X₁ ≤ E₁ := by
      change commSub E₁ (Subgroup.zpowers l₁) ≤ E₁
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, l₁ ^ n = x := by
        have hx' : x ∈ Submonoid.powers l₁ := (mem_powers_iff_mem_zpowers).2 hx
        exact (Submonoid.mem_powers_iff x l₁).1 hx'
      exact E₁.mul_mem (c23a_pow_mem hlE₁ n w hw) (E₁.inv_mem hw)
    have hX₂_le : X₂ ≤ E₂ := by
      change commSub E₂ (Subgroup.zpowers l₂) ≤ E₂
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, l₂ ^ n = x := by
        have hx' : x ∈ Submonoid.powers l₂ := (mem_powers_iff_mem_zpowers).2 hx
        exact (Submonoid.mem_powers_iff x l₂).1 hx'
      exact E₂.mul_mem (c23a_pow_mem hlE₂ n w hw) (E₂.inv_mem hw)
    have hT : commSub ⊤ (Subgroup.zpowers t) = X₁ ⊔ X₂ := by
      rw [← h.sup, c23a_commSub_sup, c23a_commSub_zpowers_eq hE₁ hlE₁ hl₁e,
        c23a_commSub_zpowers_eq hE₂ hlE₂ hl₂e]
    by_cases h1 : l₁ = 1
    · by_cases h2 : l₂ = 1
      · exfalso
        apply ht1
        apply MulEquiv.ext
        intro v
        have hv : v ∈ E₁ ⊔ E₂ := by rw [h.sup]; exact Subgroup.mem_top v
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
        have hfy : t y = y := by rw [hl₁e y hy, h1, MulAut.one_apply]
        have hfz : t z = z := by rw [hl₂e z hz, h2, MulAut.one_apply]
        rw [map_mul, hfy, hfz, MulAut.one_apply]
      · have hfix₁ : ∀ y ∈ E₁, t y = y := by
          intro y hy; rw [hl₁e y hy, h1, MulAut.one_apply]
        have hX₁bot : X₁ = ⊥ := by
          change commSub E₁ (Subgroup.zpowers l₁) = ⊥
          rw [h1, Subgroup.zpowers_one_eq_bot]
          exact commSub_eq_bot_iff.2 (by
            intro v _
            exact mem_fixV.2 (fun x hx => by rw [Subgroup.mem_bot.mp hx, MulAut.one_apply]))
        have hT₂ : commSub ⊤ (Subgroup.zpowers t) = X₂ := by
          rw [hT, hX₁bot, bot_sup_eq]
        refine ⟨Or.inr ⟨hfix₁, ?_⟩, ?_⟩
        · rw [hT₂]; exact hX₂_le
        · rw [hT₂]
          exact c23a_two_le_rk_commSub h.exp2 h.blk₂ h.ne₂ hl₂ h2 hl₂2
    · by_cases h2 : l₂ = 1
      · have hfix₂ : ∀ y ∈ E₂, t y = y := by
          intro y hy; rw [hl₂e y hy, h2, MulAut.one_apply]
        have hX₂bot : X₂ = ⊥ := by
          change commSub E₂ (Subgroup.zpowers l₂) = ⊥
          rw [h2, Subgroup.zpowers_one_eq_bot]
          exact commSub_eq_bot_iff.2 (by
            intro v _
            exact mem_fixV.2 (fun x hx => by rw [Subgroup.mem_bot.mp hx, MulAut.one_apply]))
        have hT₁ : commSub ⊤ (Subgroup.zpowers t) = X₁ := by
          rw [hT, hX₂bot, sup_bot_eq]
        refine ⟨Or.inl ⟨hfix₂, ?_⟩, ?_⟩
        · rw [hT₁]; exact hX₁_le
        · rw [hT₁]
          exact c23a_two_le_rk_commSub h.exp2 h.blk₁ h.ne₁ hl₁ h1 hl₁2
      · have hnotZ₁ : ¬ X₁ ≤ Z₁ := by
          change ¬ commSub E₁ (Subgroup.zpowers l₁) ≤ Z₁
          exact c23a_not_commSub_le h.blk₁ hl₁ h1
        have hlt : X₁ ⊓ Z₁ < X₁ :=
          lt_of_le_of_ne inf_le_left (fun heq => hnotZ₁ (heq ▸ inf_le_right))
        have hleZ : X₁ ⊓ X₂ ≤ Z₁ := le_trans (inf_le_inf hX₁_le hX₂_le) h.inf₁
        have hle : X₁ ⊓ X₂ ≤ X₁ ⊓ Z₁ := le_inf inf_le_left hleZ
        have hlt2 : rk ↥(X₁ ⊓ X₂) < rk ↥X₁ :=
          lt_of_le_of_lt (rk_mono hle) (c23a_rk_lt_of_lt h.exp2 hlt)
        have hsum := rk_sup_add_rk_inf X₁ X₂
        have h2X₂ : 2 ≤ rk ↥X₂ :=
          c23a_two_le_rk_commSub h.exp2 h.blk₂ h.ne₂ hl₂ h2 hl₂2
        have h3 : 3 ≤ rk ↥(X₁ ⊔ X₂) := by omega
        have hTge : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by rwa [hT]
        omega
  · have h3 : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      c23a_three_le_rk_commSub_of_swap h.exp2 h.blk₁ h.inf₁ hsw₁
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
