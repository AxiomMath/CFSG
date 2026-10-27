module

public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch10SecAElemAb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace Six

variable {V : Type} [CommGroup V]

theorem card_sup_le [Finite V] (H K : Subgroup V) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have h := card_sup_mul_card_inf H K
  have hpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  calc Nat.card ↥(H ⊔ K) ≤ Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = _ := h

theorem card_iSup_eq_prod [Finite V] {ι : Type} [Fintype ι] [DecidableEq ι] (J : ι → Subgroup V)
    (hJ : ∀ k, J k ⊓ (⨆ (m : ι) (_ : m ≠ k), J m) = ⊥) :
    Nat.card ↥(⨆ k, J k) = ∏ k, Nat.card ↥(J k) := by
  have key : ∀ s : Finset ι, Nat.card ↥(⨆ k ∈ s, J k) = ∏ k ∈ s, Nat.card ↥(J k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert k₀ s hk₀ ih =>
      rw [Finset.iSup_insert, Finset.prod_insert hk₀]
      have hle : (⨆ k ∈ s, J k) ≤ ⨆ (m : ι) (_ : m ≠ k₀), J m :=
        iSup₂_le fun k hk => le_iSup₂_of_le k (fun h => hk₀ (h ▸ hk)) le_rfl
      have hinf : J k₀ ⊓ (⨆ k ∈ s, J k) = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_left _ hle).trans (hJ k₀).le)
      have h := card_sup_mul_card_inf (J k₀) (⨆ k ∈ s, J k)
      rw [hinf, Subgroup.card_bot, mul_one, ih] at h
      exact h
  simpa using key Finset.univ

theorem eq_of_mul_eq_mul {W R : Subgroup V} (hinf : W ⊓ R = ⊥) {a b c d : V} (ha : a ∈ W)
    (hc : c ∈ W) (hb : b ∈ R) (hd : d ∈ R) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : c⁻¹ * a = d * b⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
      _ = c⁻¹ * (c * d) * b⁻¹ := by rw [h]
      _ = d * b⁻¹ := by group
  have hW : c⁻¹ * a ∈ W ⊓ R := Subgroup.mem_inf.mpr
    ⟨W.mul_mem (W.inv_mem hc) ha, h1 ▸ R.mul_mem hd (R.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at hW
  have hR : d * b⁻¹ = 1 := h1 ▸ hW
  exact ⟨(inv_mul_eq_one.mp hW).symm, (mul_inv_eq_one.mp hR).symm⟩

theorem fixV_le_sup {W R : Subgroup V} (hsup : W ⊔ R = ⊤) (hinf : W ⊓ R = ⊥)
    {D : Subgroup (MulAut V)} (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W)
    (hR : ∀ d ∈ D, ∀ r ∈ R, d r ∈ R) : fixV D ≤ (W ⊓ fixV D) ⊔ (R ⊓ fixV D) := by
  intro v hv
  have hvt : v ∈ W ⊔ R := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨w, hw, r, hr, rfl⟩ := Subgroup.mem_sup.mp hvt
  have key : ∀ d ∈ D, d w = w ∧ d r = r := fun d hd =>
    eq_of_mul_eq_mul hinf (hW d hd w hw) hw (hR d hd r hr) hr (by rw [← map_mul]; exact hv d hd)
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hw, fun d hd => (key d hd).1⟩)
    (Subgroup.mem_inf.mpr ⟨hr, fun d hd => (key d hd).2⟩)

theorem peel [Finite V] {W R : Subgroup V} (hsup : W ⊔ R = ⊤) (hinf : W ⊓ R = ⊥)
    {D : Subgroup (MulAut V)} (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W)
    (hR : ∀ d ∈ D, ∀ r ∈ R, d r ∈ R) {e : ℕ}
    (he : e * Nat.card V ≤ Nat.card D * Nat.card (fixV D))
    (hD8 : Nat.card D ≤ 8 * Nat.card ↥(D ⊓ centSub W))
    (hW16 : 16 * Nat.card ↥(W ⊓ fixV D) ≤ Nat.card W) :
    2 * e * Nat.card V ≤ Nat.card ↥(D ⊓ centSub W) * Nat.card (fixV (D ⊓ centSub W)) := by
  set B := D ⊓ centSub W with hB
  have h1 : Nat.card (fixV D) ≤ Nat.card ↥(W ⊓ fixV D) * Nat.card ↥(R ⊓ fixV D) :=
    (Subgroup.card_le_of_le (fixV_le_sup hsup hinf hW hR)).trans (card_sup_le _ _)
  have h2 : Nat.card ↥(R ⊓ fixV D) ≤ Nat.card ↥(R ⊓ fixV B) :=
    Subgroup.card_le_of_le (inf_le_inf_left R (B1.fixV_le_fixV inf_le_left))
  have h3 : Nat.card W * Nat.card ↥(R ⊓ fixV B) ≤ Nat.card (fixV B) := by
    have hle : W ⊔ (R ⊓ fixV B) ≤ fixV B :=
      sup_le (fun w hw x hx => (Subgroup.mem_inf.mp hx).2 w hw) inf_le_right
    have hi : W ⊓ (R ⊓ fixV B) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_left W inf_le_left).trans hinf.le)
    have h := card_sup_mul_card_inf W (R ⊓ fixV B)
    rw [hi, Subgroup.card_bot, mul_one] at h
    rw [← h]
    exact Subgroup.card_le_of_le hle
  have key : 16 * (2 * e * Nat.card V) ≤ 16 * (Nat.card B * Nat.card (fixV B)) := by
    calc 16 * (2 * e * Nat.card V) = 32 * (e * Nat.card V) := by ring
      _ ≤ 32 * (Nat.card D * Nat.card (fixV D)) := by gcongr
      _ ≤ 32 * ((8 * Nat.card B) * (Nat.card ↥(W ⊓ fixV D) * Nat.card ↥(R ⊓ fixV D))) := by
          gcongr
      _ = 16 * Nat.card B * ((16 * Nat.card ↥(W ⊓ fixV D)) * Nat.card ↥(R ⊓ fixV D)) := by
          ring
      _ ≤ 16 * Nat.card B * (Nat.card W * Nat.card ↥(R ⊓ fixV B)) := by gcongr
      _ ≤ 16 * Nat.card B * Nat.card (fixV B) := by gcongr
      _ = 16 * (Nat.card B * Nat.card (fixV B)) := by ring
  exact Nat.le_of_mul_le_mul_left key (by norm_num)

theorem commutator_eq_bot_or {K A : Subgroup (MulAut V)} [hs : IsSimpleGroup ↥K]
    (hA : A ≤ Subgroup.normalizer (K : Set (MulAut V))) : ⁅K, A⁆ = ⊥ ∨ ⁅K, A⁆ = K := by
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hn : (⁅K, A⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  rcases hs.eq_bot_or_eq_top_of_normal (⁅K, A⁆.subgroupOf K) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hle
  · right
    exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem center_eq_bot {K : Subgroup (MulAut V)} [hs : IsSimpleGroup ↥K]
    (hnc : ∃ a b : ↥K, a * b ≠ b * a) : Subgroup.center ↥K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem commutator_self_eq {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K]
    (hnc : ∃ a b : ↥K, a * b ≠ b * a) : ⁅K, K⁆ = K := by
  rcases commutator_eq_bot_or (K := K) (A := K) Subgroup.le_normalizer with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h b.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc a a.2)
  · exact h

theorem allTwoChiefFactorsCentral_of_simple {K : Subgroup (MulAut V)} [hs : IsSimpleGroup ↥K]
    (hc : Nat.card ↥K = 168) : AllTwoChiefFactorsCentral K := by
  intro A B hAB
  obtain ⟨hlt, hAK, hKA, hKB, -, h2⟩ := hAB
  exfalso
  have hBK : B ≤ K := hlt.le.trans hAK
  have hnA : (A.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  have hnB : (B.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKB
  rcases hs.eq_bot_or_eq_top_of_normal (A.subgroupOf K) with hA | hA
  · have hA' : A = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hA).eq_bot_of_le hAK
    exact not_lt_bot (hA' ▸ hlt)
  · have hAeq : A = K := le_antisymm hAK (Subgroup.subgroupOf_eq_top.mp hA)
    rcases hs.eq_bot_or_eq_top_of_normal (B.subgroupOf K) with hB | hB
    · have hBeq : B = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hB).eq_bot_of_le hBK
      have hp : IsPGroup 2 ↥K := fun x => by
        obtain ⟨k, hk⟩ := h2 x (hAeq ▸ x.2)
        rw [hBeq, Subgroup.mem_bot] at hk
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
      rw [hc] at hn
      have h7 : 7 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7)
        (hn ▸ (by norm_num : 7 ∣ 168)))
      norm_num at h7
    · exact hlt.ne (le_antisymm hBK (Subgroup.subgroupOf_eq_top.mp hB) |>.trans hAeq.symm)

theorem mem_commV_of_mem_normalizer {K : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (K : Set (MulAut V))) {w : V} (hw : w ∈ commV K) :
    a w ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer ha hw

theorem mem_fixV_of_mem_normalizer {H : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (H : Set (MulAut V))) {w : V} (hw : w ∈ fixV H) :
    a w ∈ fixV H :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer ha hw

theorem mem_normalizer_sup {K₁ K₂ : Subgroup (MulAut V)} {a : MulAut V}
    (h₁ : a ∈ Subgroup.normalizer (K₁ : Set (MulAut V)))
    (h₂ : a ∈ Subgroup.normalizer (K₂ : Set (MulAut V))) :
    a ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_sup, h₁, h₂]

theorem le_centralizer_sup {B K₁ K₂ : Subgroup (MulAut V)}
    (h₁ : ∀ b ∈ B, ∀ k ∈ K₁, b * k = k * b) (h₂ : ∀ b ∈ B, ∀ k ∈ K₂, b * k = k * b) :
    B ≤ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.le_centralizer_iff]
  exact sup_le (fun k hk => Subgroup.mem_centralizer_iff.mpr fun b hb => h₁ b hb k hk)
    (fun k hk => Subgroup.mem_centralizer_iff.mpr fun b hb => h₂ b hb k hk)

section Summands

variable {K : Subgroup (MulAut V)} {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}

theorem le_stabSub_of_realizes {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) : K ≤ stabSub I :=
  B1.le_stabSub_of_invariant fun k hk u hu => hI.2.2.2.1 ⟨k, hk⟩ u hu

theorem card_of_realizes {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) : Nat.card ↥I = 2 ^ 3 := by
  obtain ⟨e, -⟩ := B5.exists_linModel hI
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem card_mulAut_of_realizes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) :
    Nat.card (MulAut ↥I) = 168 := by
  rw [card_mulAut_of_sq_eq_one (fun w => Subtype.ext (by simpa using hV w))
    (card_of_realizes hI), card_GL_three_two]

theorem eq_one_of_fix [hs : IsSimpleGroup ↥K] {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) {k : MulAut V}
    (hk : k ∈ K) (hfix : ∀ u ∈ I, k u = u) : k = 1 := by
  set ρ : ↥K →* MulAut ↥I := (resHom I).comp (Subgroup.inclusion (le_stabSub_of_realizes hI))
  rcases hs.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · have hmem : (⟨k, hk⟩ : ↥K) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      ext u
      exact hfix u u.2
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨e, -⟩ := B5.exists_linModel hI
    have : Nontrivial ↥I := e.toEquiv.nontrivial
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥I)
    apply hu
    refine Subtype.ext (B5.nat_fixed_eq_one (by norm_num) hI u u.2 fun l hl => ?_)
    have hl' : (⟨l, hl⟩ : ↥K) ∈ ρ.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hl'
    exact congrArg Subtype.val (DFunLike.congr_fun hl' u)

theorem mem_irrPlus_of_realizes {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) : I ∈ IrrPlus K ⊤ := by
  have hfix : I ⊓ fixV K = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.mpr
      (B5.nat_fixed_eq_one (by norm_num) hI u (Subgroup.mem_inf.mp hu).1
        fun l hl => (Subgroup.mem_inf.mp hu).2 l hl)
  obtain ⟨hinv, hlt, hirr⟩ := B5.isIrr_of_realizes (by norm_num) hI
  have hinv' : ∀ x ∈ K, ∀ w ∈ I, x w ∈ I := fun x hx w hw => hinv ⟨x, hx⟩ w hw
  rw [mem_irrPlus_top_iff, hfix]
  refine ⟨hinv', ?_, hlt, fun J hJ _ hJI => hirr J ((isInv_iff K J).mpr hJ) bot_le hJI⟩
  have hle : commSub I K ≤ I := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact I.mul_mem (hinv' x hx w hw) (I.inv_mem hw)
  have hJinv : XMod.IsInv ↥K (commSub I K) := commOf_eq_commSub K I ▸ XMod.isInv_commOf I
  rcases hirr (commSub I K) hJinv bot_le hle with h | h
  · exfalso
    rw [commSub_eq_bot_iff] at h
    have h' : I ≤ I ⊓ fixV K := le_inf le_rfl h
    rw [hfix] at h'
    exact hlt.ne' (le_bot_iff.mp h')
  · exact h

theorem commute_of_fix [IsSimpleGroup ↥K] {I : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π) {d : MulAut V}
    (hdK : d ∈ Subgroup.normalizer (K : Set (MulAut V))) (hfix : ∀ u ∈ I, d u = u) :
    ∀ k ∈ K, d * k = k * d := by
  intro k hk
  have hc : d * k * d⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hdK k).mp hk) (K.inv_mem hk)
  have h1 : d * k * d⁻¹ * k⁻¹ = 1 := by
    refine eq_one_of_fix hI hc fun u hu => ?_
    have hku : k⁻¹ u ∈ I := hI.2.2.2.1 ⟨k⁻¹, K.inv_mem hk⟩ u hu
    have hdku : d⁻¹ (k⁻¹ u) = k⁻¹ u := by
      change d.symm (k⁻¹ u) = k⁻¹ u
      rw [MulEquiv.symm_apply_eq]
      exact (hfix _ hku).symm
    have hkk : k (k⁻¹ u) = u := k.apply_symm_apply u
    simp only [MulAut.mul_apply]
    rw [hdku, hkk, hfix u hu]
  calc d * k = (d * k * d⁻¹ * k⁻¹) * (k * d) := by group
    _ = k * d := by rw [h1, one_mul]

theorem fix_of_fix [Finite V] (hV : ∀ v : V, v ^ 2 = 1) [IsSimpleGroup ↥K]
    (hc : Nat.card ↥K = 168) (hnc : ∃ a b : ↥K, a * b ≠ b * a) {I J : Subgroup V}
    (hI : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K I ⊥ π)
    (hJ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K J ⊥ π) {d : MulAut V}
    (hdK : d ∈ Subgroup.normalizer (K : Set (MulAut V))) (hdJ : d ∈ stabSub J)
    (hfix : ∀ u ∈ I, d u = u) : ∀ u ∈ J, d u = u := by
  have hcomm := commute_of_fix hI hdK hfix
  set ρ : ↥K →* MulAut ↥J := (resHom J).comp (Subgroup.inclusion (le_stabSub_of_realizes hJ))
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    exact Subtype.ext (eq_one_of_fix hJ k.2 fun u hu =>
      congrArg Subtype.val (DFunLike.congr_fun hk (⟨u, hu⟩ : ↥J)))
  have hbij : Function.Bijective ρ :=
    hinj.bijective_of_nat_card_le (by rw [card_mulAut_of_realizes hV hJ, hc])
  obtain ⟨k₀, hk₀⟩ := hbij.2 (resHom J ⟨d, hdJ⟩)
  have hcen : k₀ ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply hinj
    rw [map_mul, map_mul, hk₀]
    ext u
    exact (DFunLike.congr_fun (hcomm k k.2) (u : V)).symm
  rw [center_eq_bot hnc, Subgroup.mem_bot] at hcen
  intro u hu
  have h := congrArg Subtype.val (DFunLike.congr_fun hk₀ ⟨u, hu⟩)
  rw [hcen, map_one] at h
  exact h.symm

theorem two_pow_le_eight {n : ℕ} (h : 2 ^ n ∣ 168) : 2 ^ n ≤ 8 := by
  by_contra hc
  push Not at hc
  have h4 : 4 ≤ n := by
    by_contra h'
    push Not at h'
    interval_cases n <;> simp_all
  have : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 h4).trans h
  norm_num at this

theorem summand_bound [Finite V] (hV : ∀ v : V, v ^ 2 = 1) [IsSimpleGroup ↥K]
    (hc : Nat.card ↥K = 168) (hnc : ∃ a b : ↥K, a * b ≠ b * a) {W : Subgroup V}
    (hsum : DirectSumOfCopies K W ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    {D : Subgroup (MulAut V)} (hDK : D ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hD2 : IsPGroup 2 ↥D) (hDI : ∀ d ∈ D, ∀ I ∈ IrrPlus K ⊤, I.map d.toMonoidHom = I)
    (hnt : ¬ D ≤ centSub W) :
    Nat.card D ≤ 8 * Nat.card ↥(D ⊓ centSub W) ∧ 16 * Nat.card ↥(W ⊓ fixV D) ≤ Nat.card W := by
  obtain ⟨I, π', -, hindep, hW, hreal⟩ := hsum
  have hWeq : W = ⨆ i, I i := by rw [← hW, bot_sup_eq]
  have hstab : ∀ d ∈ D, ∀ i, d ∈ stabSub (I i) := by
    intro d hd i
    rw [mem_stabSub]
    intro u
    have hmap := hDI d hd (I i) (mem_irrPlus_of_realizes (hreal i))
    constructor
    · intro hu
      rw [← hmap] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      rwa [← d.injective hwu]
    · intro hu
      rw [← hmap]
      exact ⟨u, hu, rfl⟩
  have coh : ∀ d ∈ D, ∀ i j, (∀ u ∈ I i, d u = u) → ∀ u ∈ I j, d u = u :=
    fun d hd i j h => fix_of_fix hV hc hnc (hreal i) (hreal j) (hDK hd) (hstab d hd j) h
  have trivW : ∀ d ∈ D, (∀ u ∈ I 0, d u = u) → ∀ w ∈ W, d w = w := by
    intro d hd h w hw
    have hle : W ≤ MonoidHom.eqLocus d.toMonoidHom (MonoidHom.id V) := by
      rw [hWeq]
      exact iSup_le fun j u hu => coh d hd 0 j h u hu
    exact hle hw
  have hcent : D ⊓ centSub W = D ⊓ centSub (I 0) := by
    have hI0 : I 0 ≤ W := hWeq ▸ le_iSup I 0
    refine le_antisymm (inf_le_inf_left D fun g hg => mem_centSub.mpr fun u hu =>
        mem_centSub.mp hg u (hI0 hu))
      fun g hg => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1, mem_centSub.mpr
        (trivW g (Subgroup.mem_inf.mp hg).1 (mem_centSub.mp (Subgroup.mem_inf.mp hg).2))⟩
  have hD0 : D ≤ stabSub (I 0) := fun d hd => hstab d hd 0
  refine ⟨?_, ?_⟩
  · have hcard := card_autSub_mul hD0
    have h2 : IsPGroup 2 ↥(autSub D (I 0)) :=
      (hD2.comap_of_injective (stabSub (I 0)).subtype Subtype.val_injective).map (resHom (I 0))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have hdvd : Nat.card ↥(autSub D (I 0)) ∣ 168 := by
      have h := Subgroup.card_subgroup_dvd_card (autSub D (I 0))
      rwa [card_mulAut_of_realizes hV (hreal 0)] at h
    have h8 : Nat.card ↥(autSub D (I 0)) ≤ 8 := by
      rw [hn]
      rw [hn] at hdvd
      exact two_pow_le_eight hdvd
    rw [hcent, ← hcard]
    exact Nat.mul_le_mul_right _ h8
  · obtain ⟨d, hd, hdW⟩ := IsConcreteLE.not_le_iff_exists.mp hnt
    have hnti : ∀ i, ∃ u ∈ I i, d u ≠ u := by
      intro i
      by_contra hne
      push Not at hne
      exact hdW (mem_centSub.mpr fun w hw => trivW d hd (coh d hd i 0 hne) w hw)
    set f : V →* V := d.toMonoidHom / MonoidHom.id V with hf
    have hfu : ∀ u, f u = d u / u := fun u => MonoidHom.div_apply _ _ u
    have hfI : ∀ i, (I i).map f ≤ I i := by
      rintro i _ ⟨u, hu, rfl⟩
      rw [hfu]
      exact div_mem ((mem_stabSub.mp (hstab d hd i) u).mpr hu) hu
    have hfne : ∀ i, (I i).map f ≠ ⊥ := by
      intro i hbot
      obtain ⟨u, hu, hdu⟩ := hnti i
      have hmem : f u ∈ (I i).map f := ⟨u, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot, hfu, div_eq_one] at hmem
      exact hdu hmem
    have hind : ∀ i, (I i).map f ⊓ (⨆ (m : Fin 4) (_ : m ≠ i), (I m).map f) = ⊥ := by
      intro i
      have h0 : I i ⊓ (⨆ (m : Fin 4) (_ : m ≠ i), I m) = ⊥ := by
        simpa only [bot_sup_eq] using hindep i
      exact le_bot_iff.mp ((inf_le_inf (hfI i) (iSup₂_mono fun m _ => hfI m)).trans h0.le)
    have h16 : 16 ≤ Nat.card ↥(W.map f) := by
      rw [hWeq, Subgroup.map_iSup, card_iSup_eq_prod _ hind]
      calc 16 = ∏ _i : Fin 4, 2 := by simp
        _ ≤ ∏ i, Nat.card ↥((I i).map f) :=
          Finset.prod_le_prod fun i _ => (Subgroup.one_lt_card_iff_ne_bot _).mpr (hfne i)
    have hker : W ⊓ fixV D ≤ f.ker ⊓ W := by
      intro v hv
      refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hv).1⟩
      rw [MonoidHom.mem_ker, hfu, mem_fixV.mp (Subgroup.mem_inf.mp hv).2 d hd, div_self']
    have hWc : Nat.card ↥(W.map f) * Nat.card ↥(f.ker ⊓ W) = Nat.card W := by
      rw [← Subgroup.relIndex_ker W f]
      exact Subgroup.relIndex_mul_card _ _
    rw [← hWc]
    exact Nat.mul_le_mul h16 (Subgroup.card_le_of_le hker)

theorem step [Finite V] (hV : ∀ v : V, v ^ 2 = 1) [IsSimpleGroup ↥K]
    (hc : Nat.card ↥K = 168) (hnc : ∃ a b : ↥K, a * b ≠ b * a) {W R : Subgroup V}
    (hsum : DirectSumOfCopies K W ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (hsup : W ⊔ R = ⊤) (hinf : W ⊓ R = ⊥) {D : Subgroup (MulAut V)}
    (hDK : D ≤ Subgroup.normalizer (K : Set (MulAut V))) (hD2 : IsPGroup 2 ↥D)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hDR : ∀ d ∈ D, ∀ r ∈ R, d r ∈ R)
    (hDI : ∀ d ∈ D, ∀ I ∈ IrrPlus K ⊤, I.map d.toMonoidHom = I) {e : ℕ}
    (he : e * Nat.card V ≤ Nat.card D * Nat.card (fixV D)) :
    ∃ B ≤ D, B ≤ centSub W ∧ e * Nat.card V ≤ Nat.card B * Nat.card (fixV B) ∧
      (¬ D ≤ centSub W → 2 * e * Nat.card V ≤ Nat.card B * Nat.card (fixV B)) := by
  by_cases hD : D ≤ centSub W
  · exact ⟨D, le_rfl, hD, he, fun h => absurd hD h⟩
  · obtain ⟨h8, h16⟩ := summand_bound hV hc hnc hsum hDK hD2 hDI hD
    have hp := peel hsup hinf hDW hDR he h8 h16
    refine ⟨D ⊓ centSub W, inf_le_left, inf_le_right, le_trans ?_ hp, fun _ => hp⟩
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by norm_num)

end Summands

theorem false_of_isFFStarOffender [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y A : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥Y)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q → Q = ⊥)
    (h3 : ¬ 3 ∣ Nat.card ↥Y) (hA : IsFFStarOffender Y A) : False := by
  have hFFY : IsFFModule Y :=
    ((B1_4_5 hV Y).out 2 1).1 (⟨A, hA⟩ : {B | IsFFStarOffender Y B}.Nonempty)
  obtain ⟨𝓗, hle, hJ, -, -, -, -, hnat, -⟩ := B1_8 hV hsolv hO2 hFFY
  have hAJ : A ≤ ffJ Y := le_iSup₂_of_le A hA le_rfl
  obtain ⟨H, hH⟩ : ∃ H, H ∈ 𝓗 := by
    by_contra hne
    push Not at hne
    have hbot : ffJ Y = ⊥ := by
      rw [hJ]
      exact iSup₂_eq_bot.mpr fun H hH => absurd hH (hne H)
    exact hA.2.1 (le_bot_iff.mp (hbot ▸ hAJ))
  obtain ⟨e, -, -⟩ := hnat H hH
  have h6 : Nat.card ↥H = 6 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_two]
  exact h3 ((show 3 ∣ Nat.card ↥H by rw [h6]; norm_num).trans
    (Subgroup.card_dvd_of_le (hle H hH)))

theorem false_of_strong [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y B : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥Y)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q → Q = ⊥)
    (hBY : B ≤ Y) (hBe : IsElemAbelian2 B)
    (hB : 2 * Nat.card V ≤ Nat.card B * Nat.card (fixV B)) : False := by
  have hV0 : 0 < Nat.card V := Nat.card_pos
  have hBne : B ≠ ⊥ := by
    rintro rfl
    rw [B1.card_bot_mul_card_fixV] at hB
    omega
  have hB2 : IsA2 Y B := ⟨hBY, hBne, hBe⟩
  have hlt : rAV B < 1 :=
    (rAV_lt_one_iff hV hB2).2 (lt_of_lt_of_le (by omega : Nat.card V < 2 * Nat.card V) hB)
  obtain ⟨B', -, hB', hB'lt⟩ := B1_4_4_lt hV hB2 hlt
  have hFFY : IsFFModule Y :=
    ((B1_4_5 hV Y).out 2 1).1 (⟨B', hB'⟩ : {B | IsFFStarOffender Y B}.Nonempty)
  exact (B1_8_3 hV hsolv hO2 hFFY).2 B' ⟨hB', hB'lt⟩

end Six

open Six in
theorem not_isFFModule_of_four_copies {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (h154 : AsB15Part4) {X Y K₁ K₂ : Subgroup (MulAut V)}
    (hK₁ : IsComponentOf K₁ X) (hK₂ : IsComponentOf K₂ X)
    (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hsum₁ : DirectSumOfCopies K₁ (commV K₁) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (hsum₂ : DirectSumOfCopies K₂ (commV K₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (htop : commV K₁ ⊔ (commV K₂ ⊔ fixV (K₁ ⊔ K₂)) = ⊤)
    (hinf₁ : commV K₁ ⊓ (commV K₂ ⊔ fixV (K₁ ⊔ K₂)) = ⊥)
    (hinf₂ : commV K₂ ⊓ (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) = ⊥)
    (hXY : X ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) ≤ Y)
    (hsolv : Group.IsSolvable ↥Y)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q → Q = ⊥)
    (h3 : ¬ 3 ∣ Nat.card ↥Y) : ¬ IsFFModule X := by
  intro hFF
  have := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  have hs₁ : IsSimpleGroup ↥K₁ := e₁.isSimpleGroup
  have hs₂ : IsSimpleGroup ↥K₂ := e₂.isSimpleGroup
  have hc₁ : Nat.card ↥K₁ = 168 :=
    (Nat.card_congr e₁.toEquiv).trans CFSG.QuasithinUnique.Vol2Native.A312L.Seven.card_slThree
  have hc₂ : Nat.card ↥K₂ = 168 :=
    (Nat.card_congr e₂.toEquiv).trans CFSG.QuasithinUnique.Vol2Native.A312L.Seven.card_slThree
  have hnc : ∀ {K : Subgroup (MulAut V)}, (↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∃ a b : ↥K, a * b ≠ b * a := by
    intro K e
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_nonabelian
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hnc₁ := hnc e₁
  have hnc₂ := hnc e₂
  obtain ⟨A₀, hA₀⟩ := ((B1_4_5 hV X).out 1 2).1 hFF
  obtain ⟨A, -, hA⟩ := B1.exists_isFFStarMin_le hA₀
  have hAo : IsFFStarOffender X A := hA.1
  have hN₁ : A ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) := h154 V hV X A hAo K₁ hK₁
  have hN₂ : A ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) := h154 V hV X A hAo K₂ hK₂
  have hAe : IsElemAbelian2 A := hAo.2.2.1
  have hsub : ∀ {B : Subgroup (MulAut V)}, B ≤ A → IsElemAbelian2 B := fun hBA =>
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  have h2grp : ∀ {B : Subgroup (MulAut V)}, B ≤ A → IsPGroup 2 ↥B := fun hBA x =>
    ⟨1, Subtype.ext (by simpa using hAe.2 x (hBA x.2))⟩
  have he₀ : 1 * Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have h := hAo.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rw [B1.card_bot_mul_card_fixV] at h
    simpa using h
  have hW₁ : ∀ a ∈ A, ∀ w ∈ commV K₁, a w ∈ commV K₁ := fun a ha w hw =>
    mem_commV_of_mem_normalizer (hN₁ ha) hw
  have hW₂ : ∀ a ∈ A, ∀ w ∈ commV K₂, a w ∈ commV K₂ := fun a ha w hw =>
    mem_commV_of_mem_normalizer (hN₂ ha) hw
  have hC : ∀ a ∈ A, ∀ w ∈ fixV (K₁ ⊔ K₂), a w ∈ fixV (K₁ ⊔ K₂) := fun a ha w hw =>
    mem_fixV_of_mem_normalizer (mem_normalizer_sup (hN₁ ha) (hN₂ ha)) hw
  have hR₁ : ∀ a ∈ A, ∀ w ∈ commV K₂ ⊔ fixV (K₁ ⊔ K₂), a w ∈ commV K₂ ⊔ fixV (K₁ ⊔ K₂) :=
    isInv_sup hW₂ hC
  have hR₂ : ∀ a ∈ A, ∀ w ∈ commV K₁ ⊔ fixV (K₁ ⊔ K₂), a w ∈ commV K₁ ⊔ fixV (K₁ ⊔ K₂) :=
    isInv_sup hW₁ hC
  have htop₂ : commV K₂ ⊔ (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) = ⊤ := by rw [sup_left_comm]; exact htop
  have hcomm : ∀ {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K],
      DirectSumOfCopies K (commV K) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 →
      ∀ d ∈ Subgroup.normalizer (K : Set (MulAut V)), d ∈ centSub (commV K) →
        ∀ k ∈ K, d * k = k * d := by
    intro K _ hsum d hdK hd
    obtain ⟨I, π, -, -, hW, hreal⟩ := hsum
    have hI0 : I 0 ≤ commV K := by rw [← hW, bot_sup_eq]; exact le_iSup I 0
    exact commute_of_fix (hreal 0) hdK fun u hu => mem_centSub.mp hd u (hI0 hu)
  have hbot : ∀ {K : Subgroup (MulAut V)}, ⁅K, A⁆ = ⊥ → ∀ a ∈ A, ∀ k ∈ K, a * k = k * a :=
    fun h a ha k hk =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk) a ha
  have htopK : ∀ {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K], Nat.card ↥K = 168 →
      DirectSumOfCopies K (commV K) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 →
      A ≤ Subgroup.normalizer (K : Set (MulAut V)) → ⁅K, A⁆ = K → ¬ A ≤ centSub (commV K) := by
    intro K _ hcK hsum hNK h hle
    have h' : ⁅K, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm hsum a (hNK ha) (hle ha) k hk
    have hK : K = ⊥ := h.symm.trans h'
    have : Nat.card ↥K = 1 := by rw [hK, Subgroup.card_bot]
    omega
  have hfixI : ∀ {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K], Nat.card ↥K = 168 →
      (∃ a b : ↥K, a * b ≠ b * a) → ⁅K, A⁆ = K →
      ∀ a ∈ A, ∀ I ∈ IrrPlus K ⊤, I.map a.toMonoidHom = I := by
    intro K _ hcK hncK h
    exact B1_5_3 hV hA (C2Nine.oTwoUpper_eq_of_perfect (commutator_self_eq hncK)) h
      (allTwoChiefFactorsCentral_of_simple hcK)
  rcases commutator_eq_bot_or hN₁ with h₁ | h₁ <;> rcases commutator_eq_bot_or hN₂ with h₂ | h₂
  ·
    have hAY : A ≤ Y := (le_inf hAo.1 (le_centralizer_sup (hbot h₁) (hbot h₂))).trans hXY
    exact false_of_isFFStarOffender hV hsolv hO2 h3 ⟨hAY, hAo.2⟩
  ·
    obtain ⟨B, hBA, hBW, -, hB⟩ := step hV hc₂ hnc₂ hsum₂ htop₂ hinf₂ hN₂ (h2grp le_rfl) hW₂
      hR₂ (hfixI hc₂ hnc₂ h₂) he₀
    have hBc : B ≤ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      le_centralizer_sup (fun b hb => hbot h₁ b (hBA hb))
        (fun b hb => hcomm hsum₂ b (hN₂ (hBA hb)) (hBW hb))
    exact false_of_strong hV hsolv hO2 ((le_inf (hBA.trans hAo.1) hBc).trans hXY) (hsub hBA)
      (by simpa using hB (htopK hc₂ hsum₂ hN₂ h₂))
  ·
    obtain ⟨B, hBA, hBW, -, hB⟩ := step hV hc₁ hnc₁ hsum₁ htop hinf₁ hN₁ (h2grp le_rfl) hW₁
      hR₁ (hfixI hc₁ hnc₁ h₁) he₀
    have hBc : B ≤ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      le_centralizer_sup (fun b hb => hcomm hsum₁ b (hN₁ (hBA hb)) (hBW hb))
        (fun b hb => hbot h₂ b (hBA hb))
    exact false_of_strong hV hsolv hO2 ((le_inf (hBA.trans hAo.1) hBc).trans hXY) (hsub hBA)
      (by simpa using hB (htopK hc₁ hsum₁ hN₁ h₁))
  ·
    obtain ⟨B₁, hB₁A, hB₁W, -, hB₁⟩ := step hV hc₁ hnc₁ hsum₁ htop hinf₁ hN₁ (h2grp le_rfl)
      hW₁ hR₁ (hfixI hc₁ hnc₁ h₁) he₀
    have he₁ := hB₁ (htopK hc₁ hsum₁ hN₁ h₁)
    obtain ⟨B, hBB₁, hBW, hB, -⟩ := step hV hc₂ hnc₂ hsum₂ htop₂ hinf₂ (hB₁A.trans hN₂)
      (h2grp hB₁A) (fun d hd => hW₂ d (hB₁A hd)) (fun d hd => hR₂ d (hB₁A hd))
      (fun d hd => hfixI hc₂ hnc₂ h₂ d (hB₁A hd)) he₁
    have hBA : B ≤ A := hBB₁.trans hB₁A
    have hBc : B ≤ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      le_centralizer_sup (fun b hb => hcomm hsum₁ b (hN₁ (hBA hb)) (hB₁W (hBB₁ hb)))
        (fun b hb => hcomm hsum₂ b (hN₂ (hBA hb)) (hBW hb))
    exact false_of_strong hV hsolv hO2 ((le_inf (hBA.trans hAo.1) hBc).trans hXY) (hsub hBA)
      (by simpa using hB)

end CFSG.Quasithin.Vol2.Ch10.SecA
