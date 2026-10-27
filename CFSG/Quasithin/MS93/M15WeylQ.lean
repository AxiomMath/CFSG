module

public import CFSG.Quasithin.MS93.M15G2Off
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Off

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

section Weyl

variable {F : Type} [Field F]

variable (F) in
abbrev WeylQ (Z : Subgroup (Multiplicative (quasithinZorn F))) : Type :=
  ↥(zornO0 F) ⧸ Z.subgroupOf (zornO0 F)

variable {Z : Subgroup (Multiplicative (quasithinZorn F))}

@[expose] def weylMk (Z : Subgroup (Multiplicative (quasithinZorn F))) (x : quasithinZorn F)
    (hx : cayleyTr x = 0) : WeylQ F Z :=
  QuotientGroup.mk ⟨Multiplicative.ofAdd x, hx⟩

theorem weylMk_surjective (q : WeylQ F Z) : ∃ x, ∃ hx : cayleyTr x = 0, q = weylMk Z x hx := by
  obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨Multiplicative.toAdd m, hm, rfl⟩

theorem weylMk_congr {x y : quasithinZorn F} (h : x = y) (hx : cayleyTr x = 0)
    (hy : cayleyTr y = 0) : weylMk Z x hx = weylMk Z y hy := by
  subst h
  rfl

theorem cayleyTr_add' (x y : quasithinZorn F) : cayleyTr (x + y) = cayleyTr x + cayleyTr y := by
  simp only [cayleyTr, Prod.fst_add, Prod.snd_add]
  ring

theorem cayleyTr_neg' (x : quasithinZorn F) : cayleyTr (-x) = -cayleyTr x := by
  simp only [cayleyTr, Prod.fst_neg, Prod.snd_neg]
  ring

theorem cayleyTr_sub' (x y : quasithinZorn F) : cayleyTr (x - y) = cayleyTr x - cayleyTr y := by
  simp only [cayleyTr, Prod.fst_sub, Prod.snd_sub]
  ring

theorem weylMk_zero (h : cayleyTr (0 : quasithinZorn F) = 0) : weylMk Z 0 h = 1 := rfl

theorem weylMk_add {x y : quasithinZorn F} (hx : cayleyTr x = 0) (hy : cayleyTr y = 0)
    (hxy : cayleyTr (x + y) = 0) : weylMk Z (x + y) hxy = weylMk Z x hx * weylMk Z y hy := rfl

theorem weylMk_neg {x : quasithinZorn F} (hx : cayleyTr x = 0) (hx' : cayleyTr (-x) = 0) :
    weylMk Z (-x) hx' = (weylMk Z x hx)⁻¹ := rfl

theorem weylMk_sub {x y : quasithinZorn F} (hx : cayleyTr x = 0) (hy : cayleyTr y = 0)
    (hxy : cayleyTr (x - y) = 0) : weylMk Z (x - y) hxy = weylMk Z x hx * (weylMk Z y hy)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← weylMk_add hxy hy (by rw [sub_add_cancel]; exact hx)]
  exact weylMk_congr (sub_add_cancel x y) _ _

theorem weylMk_eq_one_iff {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    weylMk Z x hx = 1 ↔ Multiplicative.ofAdd x ∈ Z := by
  rw [weylMk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem weylMk_eq_iff {x y : quasithinZorn F} (hx : cayleyTr x = 0) (hy : cayleyTr y = 0) :
    weylMk Z x hx = weylMk Z y hy ↔ Multiplicative.ofAdd (x - y) ∈ Z := by
  rw [← weylMk_eq_one_iff ((cayleyTr_sub' x y).trans (by rw [hx, hy, sub_zero])),
    weylMk_sub hx hy, mul_inv_eq_one]

@[expose] def rbar (Z : Subgroup (Multiplicative (quasithinZorn F))) : Subgroup (WeylQ F Z) :=
  ((zornR F).subgroupOf (zornO0 F)).map (QuotientGroup.mk' (Z.subgroupOf (zornO0 F)))

@[expose] def weylImage (Z : Subgroup (Multiplicative (quasithinZorn F)))
    (T : AddSubgroup (quasithinZorn F)) : Subgroup (WeylQ F Z) where
  carrier := {q | ∃ t ∈ T, ∃ ht : cayleyTr t = 0, q = weylMk Z t ht}
  mul_mem' := by
    rintro _ _ ⟨t, ht, htr, rfl⟩ ⟨t', ht', htr', rfl⟩
    exact ⟨t + t', T.add_mem ht ht', by rw [cayleyTr_add', htr, htr', add_zero],
      (weylMk_add htr htr' _).symm⟩
  one_mem' := ⟨0, T.zero_mem, by simp [cayleyTr], (weylMk_zero _).symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, htr, rfl⟩
    exact ⟨-t, T.neg_mem ht, by rw [cayleyTr_neg', htr, neg_zero], (weylMk_neg htr _).symm⟩

@[expose] def IsWeylAct (Z : Subgroup (Multiplicative (quasithinZorn F)))
    (ρ : ↥(cayleyGroup F) →* MulAut (WeylQ F Z)) : Prop :=
  ∀ (γ : ↥(cayleyGroup F)) (x : quasithinZorn F) (hx : cayleyTr x = 0),
    ρ γ (weylMk Z x hx) = weylMk Z (cgE γ x) ((cg_tr γ x).trans hx)

@[expose] def weylProj (hZ : Z ≤ zornR F) : WeylQ F Z →* Multiplicative (Ix3 → F) :=
  QuotientGroup.lift (Z.subgroupOf (zornO0 F))
    { toFun := fun m =>
        Multiplicative.ofAdd (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn F))))
      map_one' := by
        show Multiplicative.ofAdd (zP 0) = 1
        rw [← zmk_zero, zP_zmk, q6_zero]
        rfl
      map_mul' := fun m m' => by
        show Multiplicative.ofAdd (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn F)) +
          Multiplicative.toAdd (m' : Multiplicative (quasithinZorn F)))) = _
        rw [zP_add]
        rfl }
    (fun m hm => by
      obtain ⟨c, hc⟩ := hZ (Subgroup.mem_subgroupOf.1 hm)
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd
        (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn F)))) = 1
      rw [hc, ← zmk_R, zP_zmk, q6_zero]
      rfl)

theorem weylProj_mk (hZ : Z ≤ zornR F) {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    weylProj hZ (weylMk Z x hx) = Multiplicative.ofAdd (zP x) := rfl

theorem weylProj_surjective (hZ : Z ≤ zornR F) : Function.Surjective (weylProj hZ) := fun w =>
  ⟨weylMk Z (zI (Multiplicative.toAdd w)) (cayleyTr_zI _), by rw [weylProj_mk, zP_zI]; rfl⟩

theorem card_comap_eq_mul {G H : Type*} [Group G] [Group H] [Finite G] {f : G →* H}
    (hf : Function.Surjective f) (S : Subgroup H) :
    Nat.card (S.comap f) = Nat.card S * Nat.card f.ker := by
  have : Finite H := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (S.comap f)
  have h2 := Subgroup.card_mul_index S
  rw [Subgroup.index_comap_of_surjective S hf] at h1
  have h3 : Nat.card G = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hi : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (S.comap f) * S.index = Nat.card S * Nat.card f.ker * S.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h4

variable [CharP F 2]

theorem mem_rbar_iff {q : WeylQ F Z} :
    q ∈ rbar Z ↔ ∃ c : F, q = weylMk Z (zmk c 0 0 0 0 0 0 c) (cayleyTr_R c) := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    have e : m = Multiplicative.ofAdd (zmk c 0 0 0 0 0 0 c) := by
      rw [zmk_R, ← hc]
      rfl
    subst e
    rfl
  · rintro ⟨c, rfl⟩
    exact ⟨⟨Multiplicative.ofAdd (zmk c 0 0 0 0 0 0 c), cayleyTr_R c⟩, ⟨c, zmk_R c⟩, rfl⟩

omit [CharP F 2] in
theorem fix_of_comm_mem (hZ : Z ≤ zornR F) (γ : ↥(cayleyGroup F)) {x : quasithinZorn F}
    (hx : cayleyTr x = 0) (h : Multiplicative.ofAdd (cgE γ x - x) ∈ Z) : cgE γ x = x := by
  obtain ⟨c, hc⟩ := hZ h
  have hc' : cgE γ x - x = zmk c 0 0 0 0 0 0 c := by
    rw [zmk_R]
    exact hc
  have h0 := comm_eq_zero_of_mem_R γ hx hc'
  rw [h0, zmk_zero] at hc'
  exact sub_eq_zero.1 hc'

theorem weylProj_eq_one_iff (hZ : Z ≤ zornR F) {q : WeylQ F Z} :
    weylProj hZ q = 1 ↔ q ∈ rbar Z := by
  obtain ⟨x, hx, rfl⟩ := weylMk_surjective q
  rw [weylProj_mk, mem_rbar_iff]
  constructor
  · intro h
    have hP : zP x = 0 := congrArg Multiplicative.toAdd h
    have e := trace_zero_eq hx
    rw [hP, zI_zero, zero_add, cayleyOne_eq, zmk_smul, mul_zero, mul_one] at e
    exact ⟨x.1, weylMk_congr e _ _⟩
  · rintro ⟨c, hc⟩
    rw [weylMk_eq_iff] at hc
    obtain ⟨d, hd⟩ := hZ hc
    have h1 : x = zmk d 0 0 0 0 0 0 d + zmk c 0 0 0 0 0 0 c := by
      rw [← sub_eq_iff_eq_add, zmk_R d]
      exact hd
    rw [h1, zmk_add, zP_zmk]
    simp only [add_zero, q6_zero]
    rfl

theorem ker_weylProj (hZ : Z ≤ zornR F) : (weylProj hZ).ker = rbar Z := by
  ext q
  rw [MonoidHom.mem_ker, weylProj_eq_one_iff]

theorem card_weylQ [Finite F] (hZ : Z ≤ zornR F) :
    Nat.card (WeylQ F Z) = Nat.card F ^ 6 * Nat.card (rbar Z) := by
  have := card_comap_eq_mul (weylProj_surjective hZ) ⊤
  rw [Subgroup.comap_top, Subgroup.card_top, Subgroup.card_top, ker_weylProj] at this
  rw [this]
  congr 1
  exact card_Q

variable {ρ : ↥(cayleyGroup F) →* MulAut (WeylQ F Z)}

omit [CharP F 2] in
theorem IsWeylAct.comm (hρ : IsWeylAct Z ρ) (γ : ↥(cayleyGroup F)) {x : quasithinZorn F}
    (hx : cayleyTr x = 0) :
    ρ γ (weylMk Z x hx) * (weylMk Z x hx)⁻¹ =
      weylMk Z (cgE γ x - x) ((cayleyTr_sub' _ _).trans (by rw [cg_tr, hx, sub_zero])) := by
  rw [hρ, weylMk_sub]

theorem IsWeylAct.fix_rbar (hρ : IsWeylAct Z ρ) (γ : ↥(cayleyGroup F)) {q : WeylQ F Z}
    (hq : q ∈ rbar Z) : ρ γ q = q := by
  obtain ⟨c, rfl⟩ := mem_rbar_iff.1 hq
  rw [hρ]
  exact weylMk_congr (cgE_R γ c) _ _

theorem IsWeylAct.injective (hZ : Z ≤ zornR F) (hρ : IsWeylAct Z ρ) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine eq_one_of_fix_O0 fun x hx => fix_of_comm_mem hZ γ hx ?_
  have h1 : ρ γ (weylMk Z x hx) = weylMk Z x hx := by
    rw [hγ]
    rfl
  rw [hρ, weylMk_eq_iff] at h1
  exact h1

theorem IsWeylAct.mem_rbar_of_fixed (hZ : Z ≤ zornR F) (hρ : IsWeylAct Z ρ) {q : WeylQ F Z}
    (h : ∀ γ, ρ γ q = q) : q ∈ rbar Z := by
  obtain ⟨x, hx, rfl⟩ := weylMk_surjective q
  have hfix : ∀ γ : ↥(cayleyGroup F), cgE γ x = x := fun γ => by
    refine fix_of_comm_mem hZ γ hx ?_
    have h1 := h γ
    rw [hρ, weylMk_eq_iff] at h1
    exact h1
  exact mem_rbar_iff.2 ⟨x.1, weylMk_congr (eq_R_of_fixed hx hfix) _ _⟩

theorem weylProj_act (hZ : Z ≤ zornR F) (hρ : IsWeylAct Z ρ) (γ : ↥(cayleyGroup F))
    (q : WeylQ F Z) :
    weylProj hZ (ρ γ q) =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (weylProj hZ q))) := by
  obtain ⟨x, hx, rfl⟩ := weylMk_surjective q
  rw [hρ, weylProj_mk, weylProj_mk, toAdd_ofAdd, g2Act_apply, g2_zP_apply γ x hx]

theorem comm_mem_rbar_iff (hZ : Z ≤ zornR F) (hρ : IsWeylAct Z ρ) (γ : ↥(cayleyGroup F))
    (q : WeylQ F Z) :
    ρ γ q * q⁻¹ ∈ rbar Z ↔
      g2Act γ (Multiplicative.toAdd (weylProj hZ q)) = Multiplicative.toAdd (weylProj hZ q) := by
  rw [← weylProj_eq_one_iff hZ, map_mul, map_inv, mul_inv_eq_one, weylProj_act hZ hρ]
  constructor
  · intro h
    exact congrArg Multiplicative.toAdd h
  · intro h
    rw [h]
    rfl

@[expose] def fixSubM (Γ : Subgroup ↥(cayleyGroup F)) : Subgroup (Multiplicative (Ix3 → F)) :=
  AddSubgroup.toSubgroup (fixSub Γ).toAddSubgroup

end Weyl

section Char

variable {F : Type} [Field F] [CharP F 2] [Finite F]
  {Z : Subgroup (Multiplicative (quasithinZorn F))} {ρ : ↥(cayleyGroup F) →* MulAut (WeylQ F Z)}

theorem weyl_comm_char {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hZ : Z ≤ zornR F)
    (hρ : IsWeylAct Z ρ) {B : Subgroup (MulAut (WeylQ F Z))} (hBρ : B ≤ ρ.range) (hB1 : B ≠ ⊥)
    (hBe : IsElemAbelian2 B)
    (hoff : Nat.card (WeylQ F Z) ≤ Nat.card B * Nat.card ↥(fixQuot B (rbar Z))) (q : WeylQ F Z) :
    (q ∈ rbar Z ∧ q ≠ 1) ↔ (q ∈ commV B ∧ ∀ b ∈ B, ∀ w, b w * w⁻¹ ≠ q) := by
  have hρi := hρ.injective hZ
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = B.comap ρ := ⟨_, rfl⟩
  have hΓB : Γ.map ρ = B := by
    rw [hΓ]
    exact Subgroup.map_comap_eq_self hBρ
  have hmemB : ∀ b, b ∈ B ↔ ∃ γ ∈ Γ, ρ γ = b := fun b => by
    rw [← hΓB, Subgroup.mem_map]
  have hmemΓ : ∀ γ, γ ∈ Γ ↔ ρ γ ∈ B := fun γ => by
    rw [hΓ, Subgroup.mem_comap]
  have hΓ1 : ∀ γ ∈ Γ, γ * γ = 1 := fun γ hγ => hρi (by
    rw [map_mul, map_one, ← sq]
    exact hBe.2 _ ((hmemΓ γ).1 hγ))
  have hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ := fun γ hγ δ hδ => hρi (by
    rw [map_mul, map_mul]
    exact hBe.1 _ ((hmemΓ γ).1 hγ) _ ((hmemΓ δ).1 hδ))
  have hΓne : Γ ≠ ⊥ := by
    intro h
    apply hB1
    rw [← hΓB, h, Subgroup.map_bot]
  have hcΓ : Nat.card Γ = Nat.card B := by
    rw [← hΓB, Subgroup.card_map_of_injective hρi]
  have hfix : fixQuot B (rbar Z) = (fixSubM Γ).comap (weylProj hZ) := by
    ext q
    rw [mem_fixQuot, Subgroup.mem_comap]
    show _ ↔ ∀ γ ∈ Γ, g2Act γ (Multiplicative.toAdd (weylProj hZ q)) =
      Multiplicative.toAdd (weylProj hZ q)
    constructor
    · intro h γ hγ
      exact (comm_mem_rbar_iff hZ hρ γ q).1 (h _ ((hmemΓ γ).1 hγ))
    · intro h b hb
      obtain ⟨γ, hγ, rfl⟩ := (hmemB b).1 hb
      exact (comm_mem_rbar_iff hZ hρ γ q).2 (h γ hγ)
  have hcfix : Nat.card (fixQuot B (rbar Z)) = Nat.card (fixSub Γ) * Nat.card (rbar Z) := by
    rw [hfix, card_comap_eq_mul (weylProj_surjective hZ), ker_weylProj]
    rfl
  have hoff' : Nat.card F ^ 6 ≤ Nat.card ↥Γ * Nat.card (fixSub Γ) := by
    have hpos : 0 < Nat.card (rbar Z) := Nat.card_pos
    rw [card_weylQ hZ, hcfix, ← hcΓ, ← mul_assoc] at hoff
    exact Nat.le_of_mul_le_mul_right hoff hpos
  obtain ⟨g, hg⟩ := eq_conj_A1_of_offender hF hn hΓ1 hΓc hΓne hoff'
  have htr : ∀ t ∈ o0Comm Γ, cayleyTr t = 0 := by
    rintro _ ⟨γ, -, y, hy, rfl⟩
    rw [cayleyTr_sub', cg_tr, hy, sub_zero]
  have hsingle : ∀ t ∈ o0Comm Γ, ∀ ht : cayleyTr t = 0,
      ∃ b ∈ B, ∃ w, b w * w⁻¹ = weylMk Z t ht := by
    rintro _ ⟨γ, hγ, y, hy, rfl⟩ ht
    exact ⟨ρ γ, (hmemB _).2 ⟨γ, hγ, rfl⟩, weylMk Z y hy, hρ.comm γ hy⟩
  have hsingle' : ∀ b ∈ B, ∀ w, ∃ t ∈ o0Comm Γ, ∃ ht : cayleyTr t = 0,
      b w * w⁻¹ = weylMk Z t ht := by
    intro b hb w
    obtain ⟨γ, hγ, rfl⟩ := (hmemB b).1 hb
    obtain ⟨y, hy, rfl⟩ := weylMk_surjective w
    exact ⟨_, ⟨γ, hγ, y, hy, rfl⟩, _, hρ.comm γ hy⟩
  have hconj : ∀ s ∈ o0Comm (A1 F), cgE g s ∈ o0Comm Γ := fun s hs => by
    rw [hg]
    exact (mem_o0Comm_conj_iff g).2 ⟨s, hs, rfl⟩
  constructor
  · rintro ⟨hq, hq1⟩
    obtain ⟨c, rfl⟩ := mem_rbar_iff.1 hq
    refine ⟨?_, ?_⟩
    ·
      obtain ⟨t₁, ht₁, t₂, ht₂, he⟩ := exists_sub_o0Comm_A1 c
      have h1 := hconj t₁ ht₁
      have h2 := hconj t₂ ht₂
      have e : zmk c 0 0 0 0 0 0 c = cgE g t₁ - cgE g t₂ := by
        rw [← map_sub, ← he, cgE_R]
      rw [weylMk_congr e _ ((cayleyTr_sub' _ _).trans (by rw [htr _ h1, htr _ h2, sub_zero])),
        weylMk_sub (htr _ h1) (htr _ h2)]
      obtain ⟨b₁, hb₁, w₁, hw₁⟩ := hsingle _ h1 (htr _ h1)
      obtain ⟨b₂, hb₂, w₂, hw₂⟩ := hsingle _ h2 (htr _ h2)
      rw [← hw₁, ← hw₂]
      exact (commV B).mul_mem (Subgroup.subset_closure ⟨b₁, hb₁, w₁, rfl⟩)
        ((commV B).inv_mem (Subgroup.subset_closure ⟨b₂, hb₂, w₂, rfl⟩))
    ·
      intro b hb w hbw
      apply hq1
      obtain ⟨t, ht, htr', he⟩ := hsingle' b hb w
      have hZt : Multiplicative.ofAdd (t - zmk c 0 0 0 0 0 0 c) ∈ Z := by
        rw [← weylMk_eq_iff htr' (cayleyTr_R c), ← he, hbw]
      obtain ⟨d, hd⟩ := hZ hZt
      obtain ⟨γ, -, y, hy, rfl⟩ := ht
      have h1 : cgE γ y - y = zmk (d + c) 0 0 0 0 0 0 (d + c) := by
        have h2 : cgE γ y - y - zmk c 0 0 0 0 0 0 c = zmk d 0 0 0 0 0 0 d := by
          rw [zmk_R d]
          exact hd
        rw [sub_eq_iff_eq_add, zmk_add] at h2
        rw [h2]
        apply zmk_congr <;> ring
      have h0 := comm_eq_zero_of_mem_R γ hy h1
      rw [h0, zmk_zero] at h1
      rw [← hbw, he]
      exact (weylMk_congr h1 _ (by simp [cayleyTr])).trans (weylMk_zero _)
  · rintro ⟨hq, hns⟩
    have hq1 : q ≠ 1 := by
      rintro rfl
      exact hns 1 B.one_mem 1 (by rw [map_one, one_mul, inv_one])
    refine ⟨?_, hq1⟩
    have hcT : commV B ≤ weylImage Z ((tA1 F).map (cgE g).toLinearMap.toAddMonoidHom) := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨b, hb, w, rfl⟩
      obtain ⟨t, ht, htr', he⟩ := hsingle' b hb w
      rw [hg] at ht
      obtain ⟨s, hs, rfl⟩ := (mem_o0Comm_conj_iff g).1 ht
      exact ⟨cgE g s, AddSubgroup.mem_map.2 ⟨s, mem_tA1_of_mem_o0Comm hs, rfl⟩, htr', he⟩
    obtain ⟨_, hst, hstr, rfl⟩ := hcT hq
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.1 hst
    by_cases hR : ∃ c : F, s = zmk c 0 0 0 0 0 0 c
    · obtain ⟨c, rfl⟩ := hR
      exact mem_rbar_iff.2 ⟨c, weylMk_congr (cgE_R g c) _ _⟩
    · exfalso
      have hs' := mem_o0Comm_A1 hs fun c h => hR ⟨c, h⟩
      obtain ⟨b, hb, w, hbw⟩ := hsingle _ (hconj s hs') hstr
      exact hns b hb w hbw

theorem comm_char_of_equiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hZ : Z ≤ zornR F)
    (hρ : IsWeylAct Z ρ) {V : Type} [CommGroup V] [Finite V] (e : V ≃* WeylQ F Z)
    {A : Subgroup (MulAut V)} {C : Subgroup V}
    (hAρ : A.map (MulAut.congr e).toMonoidHom ≤ ρ.range) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hC : ∀ v, v ∈ C ↔ e v ∈ rbar Z) (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A C))
    (v : V) : (v ∈ C ∧ v ≠ 1) ↔ (v ∈ commV A ∧ ∀ a ∈ A, ∀ w : V, a w * w⁻¹ ≠ v) := by
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hB1 : A.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hfixB : fixQuot (A.map (MulAut.congr e).toMonoidHom) (rbar Z) =
      (fixQuot A C).map e.toMonoidHom := by
    ext q
    rw [Subgroup.mem_map_equiv, mem_fixQuot, mem_fixQuot]
    constructor
    · intro h a ha
      rw [hC, map_mul, map_inv, ← H13.congr_apply_eq e a, MulEquiv.apply_symm_apply]
      exact h _ ⟨a, ha, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩
      have h1 := (hC _).1 (h a ha)
      rw [map_mul, map_inv, ← H13.congr_apply_eq e a, MulEquiv.apply_symm_apply] at h1
      exact h1
  have hoffB : Nat.card (WeylQ F Z) ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixQuot (A.map (MulAut.congr e).toMonoidHom) (rbar Z)) := by
    rw [hfixB, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective hφinj, ← Nat.card_congr e.toEquiv]
    exact hoff
  have key := weyl_comm_char hF hn hZ hρ hAρ hB1 (H13.isElemAbelian2_map_congr e hAe) hoffB (e v)
  have hcomm : e v ∈ commV (A.map (MulAut.congr e).toMonoidHom) ↔ v ∈ commV A := by
    rw [H13.commV_map_congr]
    exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  have hsing : (∀ b ∈ A.map (MulAut.congr e).toMonoidHom, ∀ w, b w * w⁻¹ ≠ e v) ↔
      (∀ a ∈ A, ∀ w : V, a w * w⁻¹ ≠ v) := by
    constructor
    · intro h a ha w hw
      apply h _ ⟨a, ha, rfl⟩ (e w)
      change MulAut.congr e a (e w) * (e w)⁻¹ = e v
      rw [H13.congr_apply_eq, ← map_inv, ← map_mul, hw]
    · rintro h _ ⟨a, ha, rfl⟩ w hw
      apply h a ha (e.symm w)
      apply e.injective
      rw [map_mul, map_inv, ← H13.congr_apply_eq, MulEquiv.apply_symm_apply]
      exact hw
  exact (and_congr (hC v) (not_congr (MulEquiv.map_eq_one_iff e)).symm).trans
    (key.trans (and_congr hcomm hsing))

end Char

end CFSG.Quasithin.MS93
