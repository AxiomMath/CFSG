module

public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.Quasithin.EmptyFaithful.S1565M7
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.Background.GoldschmidtE23SymFin
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.G64Realize
import CFSG.Open.MatrixFixedVectors
import CFSG.Quasithin.EmptyFaithful.S146zUC2Alg
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

namespace FFTwo

variable {V : Type} [CommGroup V]

@[expose] def fixMod (B : Subgroup (MulAut V)) (W C : Subgroup V) : Subgroup V where
  carrier := {w | w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ C}
  one_mem' := ⟨W.one_mem, fun b _ => by simp⟩
  mul_mem' := fun {x y} ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨W.mul_mem hx hy, fun b hb => by
    have e : b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    rw [e]
    exact C.mul_mem (hx' b hb) (hy' b hb)⟩
  inv_mem' := fun {x} ⟨hx, hx'⟩ => ⟨W.inv_mem hx, fun b hb => by
    have e : b x⁻¹ * x⁻¹⁻¹ = (b x * x⁻¹)⁻¹ := by rw [map_inv, inv_inv, mul_inv, inv_inv]
    rw [e]
    exact C.inv_mem (hx' b hb)⟩

theorem mem_fixMod {B : Subgroup (MulAut V)} {W C : Subgroup V} {w : V} :
    w ∈ fixMod B W C ↔ w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ C := Iff.rfl

@[expose] def proj₁ (G₁ G₂ A : Subgroup (MulAut V)) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    Subgroup (MulAut V) where
  carrier := {g | g ∈ G₁ ∧ ∃ h ∈ G₂, g * h ∈ A}
  one_mem' := ⟨G₁.one_mem, 1, G₂.one_mem, by simp⟩
  mul_mem' := fun {x y} ⟨hx, h, hh, hxh⟩ ⟨hy, k, hk, hyk⟩ => ⟨G₁.mul_mem hx hy, h * k,
    G₂.mul_mem hh hk, by
      have e : x * y * (h * k) = (x * h) * (y * k) :=
        calc x * y * (h * k) = x * (y * h) * k := by group
          _ = x * (h * y) * k := by rw [hcomm y hy h hh]
          _ = (x * h) * (y * k) := by group
      rw [e]
      exact A.mul_mem hxh hyk⟩
  inv_mem' := fun {x} ⟨hx, h, hh, hxh⟩ => ⟨G₁.inv_mem hx, h⁻¹, G₂.inv_mem hh, by
    have e : x⁻¹ * h⁻¹ = (x * h)⁻¹ :=
      calc x⁻¹ * h⁻¹ = (h * x)⁻¹ := by group
        _ = (x * h)⁻¹ := by rw [hcomm x hx h hh]
    rw [e]
    exact A.inv_mem hxh⟩

variable [Finite V]

omit [Finite V] in
theorem fix_mod_of_fixV {G G' A : Subgroup (MulAut V)} {W W' C : Subgroup V}
    (hGW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hG'W : ∀ g ∈ G', ∀ w ∈ W, g w * w⁻¹ ∈ C)
    (hGW' : ∀ g ∈ G, ∀ w ∈ W', g w * w⁻¹ ∈ C) (hG'W' : ∀ g ∈ G', ∀ w ∈ W', g w ∈ W')
    (hCG : ∀ g ∈ G, ∀ c ∈ C, g c = c) (hCW' : C ≤ W') (hWW : W ⊓ W' ≤ C)
    {x h : MulAut V} (hx : x ∈ G) (hh : h ∈ G') (hxh : x * h ∈ A) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W') (hv : w * w' ∈ fixV A) : x w * w⁻¹ ∈ C := by
  set c₁ := h w * w⁻¹ with hc₁
  have hc₁C : c₁ ∈ C := hG'W h hh w hw
  set u := h w' with hu
  have huW' : u ∈ W' := hG'W' h hh w' hw'
  set c₂ := x u * u⁻¹ with hc₂
  have hc₂C : c₂ ∈ C := hGW' x hx u huW'
  have h1 : (x * h) (w * w') = w * w' := hv _ hxh
  have e1 : h w = c₁ * w := by rw [hc₁, inv_mul_cancel_right]
  have e2 : x u = c₂ * u := by rw [hc₂, inv_mul_cancel_right]
  have e3 : (x * h) (w * w') = c₁ * x w * (c₂ * u) := by
    rw [MulAut.mul_apply, map_mul, map_mul, e1, map_mul, hCG x hx c₁ hc₁C, ← e2]
  rw [e3] at h1
  have e4 : x w * w⁻¹ = (c₁ * c₂)⁻¹ * (w' * u⁻¹) := by
    have h2 : c₁ * x w * (c₂ * u) * (w * w')⁻¹ = 1 := by rw [h1, mul_inv_cancel]
    apply Additive.ofMul.injective
    have h3 := congrArg Additive.ofMul h2
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at h3 ⊢
    linear_combination (norm := abel) h3
  have hW : x w * w⁻¹ ∈ W := W.mul_mem (hGW x hx w hw) (W.inv_mem hw)
  have hW' : x w * w⁻¹ ∈ W' := by
    rw [e4]
    exact W'.mul_mem (W'.inv_mem (W'.mul_mem (hCW' hc₁C) (hCW' hc₂C)))
      (W'.mul_mem hw' (W'.inv_mem huW'))
  exact hWW ⟨hW, hW'⟩

theorem card_mul_card_fixV_le_of_factors {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hGinf : G₁ ⊓ G₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = C)
    (hC₁ : ∀ g ∈ G₁, ∀ c ∈ C, g c = c) (hC₂ : ∀ g ∈ G₂, ∀ c ∈ C, g c = c)
    (hW₁ : ∀ g ∈ G₁, ∀ w ∈ W₁, g w ∈ W₁) (hW₂ : ∀ g ∈ G₂, ∀ w ∈ W₂, g w ∈ W₂)
    (h₁₂ : ∀ g ∈ G₁, ∀ w ∈ W₂, g w * w⁻¹ ∈ C) (h₂₁ : ∀ g ∈ G₂, ∀ w ∈ W₁, g w * w⁻¹ ∈ C)
    (hb₁ : ∀ B : Subgroup (MulAut V), B ≤ G₁ → IsElemAbelian2 B →
      Nat.card ↥B * Nat.card ↥(fixMod B W₁ C) ≤ Nat.card ↥W₁)
    (hb₂ : ∀ B : Subgroup (MulAut V), B ≤ G₂ → IsElemAbelian2 B →
      Nat.card ↥B * Nat.card ↥(fixMod B W₂ C) ≤ Nat.card ↥W₂)
    {A : Subgroup (MulAut V)} (hA : A ≤ G₁ ⊔ G₂) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V := by
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  set A₁ := proj₁ G₁ G₂ A hcomm with hA₁
  set A₂ := proj₁ G₂ G₁ A hcomm' with hA₂
  have hCW₁ : C ≤ W₁ := hinf ▸ inf_le_left
  have hCW₂ : C ≤ W₂ := hinf ▸ inf_le_right
  have hdec : ∀ a ∈ A, ∃ a₁ ∈ G₁, ∃ a₂ ∈ G₂, a = a₁ * a₂ := fun a ha =>
    (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hcomm)).1 (hA ha)
  have hcardA : Nat.card ↥A ≤ Nat.card ↥A₁ * Nat.card ↥A₂ := by
    rw [← Nat.card_prod]
    classical
    let f : ↥A → ↥A₁ × ↥A₂ := fun a =>
      (⟨(hdec a a.2).choose, (hdec a a.2).choose_spec.1, (hdec a a.2).choose_spec.2.choose,
          (hdec a a.2).choose_spec.2.choose_spec.1,
          by rw [← (hdec a a.2).choose_spec.2.choose_spec.2]; exact a.2⟩,
        ⟨(hdec a a.2).choose_spec.2.choose, (hdec a a.2).choose_spec.2.choose_spec.1,
          (hdec a a.2).choose, (hdec a a.2).choose_spec.1, by
            rw [← hcomm _ (hdec a a.2).choose_spec.1 _ (hdec a a.2).choose_spec.2.choose_spec.1,
              ← (hdec a a.2).choose_spec.2.choose_spec.2]
            exact a.2⟩)
    refine Nat.card_le_card_of_injective f fun a b h => ?_
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ => (p.1 : MulAut V) * p.2) h
    simp only [f] at h1
    rw [← (hdec a a.2).choose_spec.2.choose_spec.2, ← (hdec b b.2).choose_spec.2.choose_spec.2]
      at h1
    exact Subtype.ext h1
  have helem : ∀ {G G' : Subgroup (MulAut V)} (hc : ∀ a ∈ G, ∀ b ∈ G', a * b = b * a),
      G ⊓ G' = ⊥ → IsElemAbelian2 (proj₁ G G' A hc) := by
    intro G G' hc hGG'
    have hcz : ∀ x ∈ G ⊓ G', x = 1 := fun x hx => by rwa [hGG', Subgroup.mem_bot] at hx
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨hxG, h, hh, hxh⟩ := hx
      obtain ⟨hyG, k, hk, hyk⟩ := hy
      have h1 := hA2.1 _ hxh _ hyk
      have e1 : x * h * (y * k) = (x * y) * (h * k) :=
        calc x * h * (y * k) = x * (h * y) * k := by group
          _ = x * (y * h) * k := by rw [hc y hyG h hh]
          _ = (x * y) * (h * k) := by group
      have e2 : y * k * (x * h) = (y * x) * (k * h) :=
        calc y * k * (x * h) = y * (k * x) * h := by group
          _ = y * (x * k) * h := by rw [hc x hxG k hk]
          _ = (y * x) * (k * h) := by group
      rw [e1, e2] at h1
      have h2 : (y * x)⁻¹ * (x * y) = (k * h) * (h * k)⁻¹ := by
        calc (y * x)⁻¹ * (x * y) = (y * x)⁻¹ * ((x * y) * (h * k)) * (h * k)⁻¹ := by group
          _ = (y * x)⁻¹ * ((y * x) * (k * h)) * (h * k)⁻¹ := by rw [h1]
          _ = (k * h) * (h * k)⁻¹ := by group
      have h3 := hcz _ ⟨G.mul_mem (G.inv_mem (G.mul_mem hyG hxG)) (G.mul_mem hxG hyG),
        h2 ▸ G'.mul_mem (G'.mul_mem hk hh) (G'.inv_mem (G'.mul_mem hh hk))⟩
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    · obtain ⟨hxG, h, hh, hxh⟩ := hx
      have h1 := hA2.2 _ hxh
      have e : (x * h) ^ 2 = x ^ 2 * h ^ 2 := by
        rw [sq, sq, sq]
        calc x * h * (x * h) = x * (h * x) * h := by group
          _ = x * (x * h) * h := by rw [hc x hxG h hh]
          _ = x * x * (h * h) := by group
      rw [e] at h1
      have h2 : x ^ 2 = (h ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hcz _ ⟨G.pow_mem hxG 2, h2 ▸ G'.inv_mem (G'.pow_mem hh 2)⟩
  have hA₁e : IsElemAbelian2 A₁ := helem hcomm hGinf
  have hA₂e : IsElemAbelian2 A₂ := helem hcomm' ((inf_comm _ _).trans hGinf)
  have hA₁G : A₁ ≤ G₁ := fun x hx => hx.1
  have hA₂G : A₂ ≤ G₂ := fun x hx => hx.1
  set F₁ := fixMod A₁ W₁ C with hF₁
  set F₂ := fixMod A₂ W₂ C with hF₂
  have hfix : fixV A ≤ F₁ ⊔ F₂ := by
    intro v hv
    have hv' : v ∈ W₁ ⊔ W₂ := hsup ▸ Subgroup.mem_top v
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hv'
    refine Subgroup.mul_mem_sup ⟨hw₁, fun x hx => ?_⟩ ⟨hw₂, fun y hy => ?_⟩
    · obtain ⟨hxG, h, hh, hxh⟩ := hx
      exact fix_mod_of_fixV hW₁ h₂₁ h₁₂ hW₂ hC₁ hCW₂ hinf.le hxG hh hxh hw₁ hw₂ hv
    · obtain ⟨hyG, h, hh, hyh⟩ := hy
      have hv2 : w₂ * w₁ ∈ fixV A := by rw [mul_comm]; exact hv
      exact fix_mod_of_fixV hW₂ h₁₂ h₂₁ hW₁ hC₂ hCW₁ (by rw [inf_comm, hinf]) hyG hh hyh
        hw₂ hw₁ hv2
  have hcomV : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x := fun x _ y _ => mul_comm x y
  have hcomW : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := fun x _ y _ => mul_comm x y
  have hFF := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomV
  have hWW := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomW
  rw [hsup, hinf, Subgroup.card_top] at hWW
  have hCF : C ≤ F₁ ⊓ F₂ := fun c hc => ⟨⟨hCW₁ hc, fun x hx => by
      rw [hC₁ x (hA₁G hx) c hc, mul_inv_cancel]; exact C.one_mem⟩,
    ⟨hCW₂ hc, fun x hx => by rw [hC₂ x (hA₂G hx) c hc, mul_inv_cancel]; exact C.one_mem⟩⟩
  have h1 : Nat.card ↥(fixV A) ≤ Nat.card ↥(F₁ ⊔ F₂) := Subgroup.card_le_of_le hfix
  have h2 : Nat.card ↥C ≤ Nat.card ↥(F₁ ⊓ F₂) := Subgroup.card_le_of_le hCF
  have hb₁' := hb₁ A₁ hA₁G hA₁e
  have hb₂' := hb₂ A₂ hA₂G hA₂e
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have key : Nat.card ↥A * Nat.card ↥(fixV A) * Nat.card ↥C ≤ Nat.card V * Nat.card ↥C := by
    calc Nat.card ↥A * Nat.card ↥(fixV A) * Nat.card ↥C
        ≤ (Nat.card ↥A₁ * Nat.card ↥A₂) * (Nat.card ↥(F₁ ⊔ F₂) * Nat.card ↥(F₁ ⊓ F₂)) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul hcardA (Nat.mul_le_mul h1 h2)
      _ = (Nat.card ↥A₁ * Nat.card ↥F₁) * (Nat.card ↥A₂ * Nat.card ↥F₂) := by
          rw [hFF]
          ring
      _ ≤ Nat.card ↥W₁ * Nat.card ↥W₂ := Nat.mul_le_mul hb₁' hb₂'
      _ = Nat.card V * Nat.card ↥C := hWW.symm
  exact Nat.le_of_mul_le_mul_right key hCpos

section Natural

private theorem ff_card_eq_card_ker_mul_card_range {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Nat.card G = Nat.card ↥f.ker * Nat.card ↥f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

private theorem ff_card_multiplicative_fin_two_fun (K : Type) [Finite K] :
    Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp

private abbrev FFFixNat (K : Type) [Field K] (B : Subgroup ↥(StatedSL 2 K)) : Type :=
  {x : Multiplicative (Fin 2 → K) // ∀ g ∈ B, natAct (StatedSL 2 K) g x = x}

private theorem ff_card_natAct_fixed_le {K : Type} [Field K] [Finite K] (g : ↥(StatedSL 2 K))
    (hg : g ≠ 1) :
    Nat.card {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x} ≤ Nat.card K :=
  (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).le.trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le fun h => hg (Subtype.ext (Units.ext h)))

private theorem ff_card_exp_two_le_field {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B ≤ Nat.card K :=
  CFSG.Quasithin.S146zU.UC2.card_le_field_of_exp_two hK B hB

private theorem ff_card_mul_card_fixNat_le {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B * Nat.card (FFFixNat K B) ≤ Nat.card K ^ 2 := by
  by_cases hbot : B = ⊥
  · subst hbot
    rw [Subgroup.card_bot, one_mul]
    calc Nat.card (FFFixNat K ⊥) ≤ Nat.card (Multiplicative (Fin 2 → K)) :=
          Finite.card_subtype_le _
      _ = Nat.card K ^ 2 := ff_card_multiplicative_fin_two_fun K
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hg1 : (a : ↥(StatedSL 2 K)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hfix : Nat.card (FFFixNat K B) ≤ Nat.card K := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : FFFixNat K B => (⟨x.1, x.2 (a : ↥(StatedSL 2 K)) a.2⟩ :
          {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x}))
        ?_) (ff_card_natAct_fixed_le _ hg1)
      intro x y h
      have h1 : (x : Multiplicative (Fin 2 → K)) = (y : Multiplicative (Fin 2 → K)) :=
        congrArg (fun z : {x : Multiplicative (Fin 2 → K) //
          natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x} => (z : Multiplicative (Fin 2 → K))) h
      exact Subtype.ext h1
    calc Nat.card ↥B * Nat.card (FFFixNat K B) ≤ Nat.card K * Nat.card K :=
          Nat.mul_le_mul (ff_card_exp_two_le_field hK B hB) hfix
      _ = Nat.card K ^ 2 := (sq _).symm


theorem card_mul_card_fixMod_le_natural {G : Subgroup (MulAut V)} {W C : Subgroup V}
    {n : ℕ} (h : BinaryNaturalSL G W C 2 n) {B : Subgroup (MulAut V)} (hBG : B ≤ G)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card ↥B * Nat.card ↥(fixMod B W C) ≤ Nat.card ↥W := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥G,
      (FFModel.nat (StatedSL 2 K)).RealizesVia G W C π := hR
  have hinj : Function.Injective π := natural_realizes_injective _ hπ
  have hCW : C ≤ W := hπ.2.1
  obtain ⟨hsurj, hUinv, hZinv, β, hβs, hβk, hβe⟩ := SzN15.NatReal.of_realizesVia hπ
  set B' : Subgroup ↥(StatedSL 2 K) := (B.subgroupOf G).comap π with hB'
  have hcardB : Nat.card ↥B = Nat.card ↥B' := by
    have e1 : Nat.card ↥B = Nat.card ↥(B.subgroupOf G) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv).symm
    have e2 : (B'.map π) = B.subgroupOf G := Subgroup.map_comap_eq_self_of_surjective hsurj _
    rw [e1, ← e2]
    exact Subgroup.card_map_of_injective hinj
  have hB'2 : ∀ x ∈ B', x ^ 2 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hB2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hβker : Nat.card ↥β.ker = Nat.card ↥C := by
    have e : β.ker = C.subgroupOf W := by
      ext u
      rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv
  have hW : Nat.card ↥W = Nat.card ↥C * Nat.card K ^ 2 := by
    have h1 := ff_card_eq_card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, ff_card_multiplicative_fin_two_fun,
      hβker] at h1
    exact h1
  set F := (fixMod B W C).subgroupOf W with hF
  have hFcard : Nat.card ↥(fixMod B W C) = Nat.card ↥F :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun w hw => (mem_fixMod.mp hw).1).toEquiv).symm
  let βF : ↥F →* Multiplicative (Fin 2 → K) := β.comp F.subtype
  have hβFker : Nat.card ↥βF.ker ≤ Nat.card ↥C := by
    rw [← hβker]
    refine Nat.card_le_card_of_injective (fun x : ↥βF.ker => (⟨((x : ↥F) : ↥W), x.2⟩ : ↥β.ker))
      fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥β.ker => (z : ↥W)) h))
  have hβFrange : Nat.card ↥βF.range ≤ Nat.card (FFFixNat K B') := by
    refine Nat.card_le_card_of_injective
      (fun y : ↥βF.range => (⟨(y : Multiplicative (Fin 2 → K)), ?_⟩ : FFFixNat K B'))
      fun (y z : ↥βF.range) h =>
        Subtype.ext (congrArg (fun q : FFFixNat K B' => (q : Multiplicative (Fin 2 → K))) h)
    obtain ⟨⟨u, hu⟩, hy⟩ := y.2
    intro g hg
    rw [← hy]
    have hgB : ((π g : ↥G) : MulAut V) ∈ B := Subgroup.mem_subgroupOf.mp hg
    have hu' : (u : V) ∈ fixMod B W C := Subgroup.mem_subgroupOf.mp hu
    have hgu : ((π g : ↥G) : MulAut V) (u : V) ∈ W := hUinv (π g) u u.2
    have h1 := hβe g u hgu
    show natAct (StatedSL 2 K) g (β u) = β u
    rw [← h1]
    have h2 : ((π g : ↥G) : MulAut V) (u : V) * (u : V)⁻¹ ∈ C := hu'.2 _ hgB
    have h3 : β ⟨((π g : ↥G) : MulAut V) (u : V), hgu⟩ * (β u)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact (hβk _).mpr h2
    exact mul_inv_eq_one.mp h3
  have hFc : Nat.card ↥F = Nat.card ↥βF.ker * Nat.card ↥βF.range :=
    ff_card_eq_card_ker_mul_card_range βF
  have hbound := ff_card_mul_card_fixNat_le hK B' hB'2
  rw [hcardB, hFcard, hFc, hW]
  calc Nat.card ↥B' * (Nat.card ↥βF.ker * Nat.card ↥βF.range)
      ≤ Nat.card ↥B' * (Nat.card ↥C * Nat.card (FFFixNat K B')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hβFker hβFrange)
    _ = Nat.card ↥C * (Nat.card ↥B' * Nat.card (FFFixNat K B')) := by ring
    _ ≤ Nat.card ↥C * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hbound

end Natural

section Sym

open Equiv

omit [CommGroup V] in
theorem card_mul_card_fixΔ_le {B₀ : Subgroup (Perm (Fin 5))}
    (hc : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) (h2 : ∀ x ∈ B₀, x * x = 1) :
    Nat.card ↥B₀ * Nat.card ↥(GE23.fixΔ B₀) ≤ 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card (Perm (Fin 5))).factorization 2 = 3 := by
    have h120 : Nat.card (Perm (Fin 5)) = 2 ^ 3 * 15 := by
      rw [Nat.card_perm, Nat.card_fin]
      rfl
    rw [h120, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let D : Sylow 2 (Perm (Fin 5)) := Sylow.ofCard GE23.d8 (by rw [GE23.card_d8, hfac]; norm_num)
  have hp : IsPGroup 2 ↥B₀ := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact h2 _ x.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) P D
  set B₀' := B₀.map (MulAut.conj g).toMonoidHom with hB₀'
  have hB₀'D : B₀' ≤ GE23.d8 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g).toMonoidHom x ∈ (g • P : Sylow 2 (Perm (Fin 5))) :=
      Subgroup.mem_map_of_mem _ (hP hx)
    rw [hg] at h1
    exact h1
  have hcardB : Nat.card ↥B₀' = Nat.card ↥B₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hfixcard : Nat.card ↥(GE23.fixΔ B₀') = Nat.card ↥(GE23.fixΔ B₀) := by
    let e : ↥(GE23.fixΔ B₀) ≃ ↥(GE23.fixΔ B₀') :=
      { toFun := fun y => ⟨G6.coreAct 5 g y, fun σ hσ => by
          obtain ⟨x, hx, rfl⟩ := hσ
          have h1 := y.2 x hx
          show G6.coreAct 5 (g * x * g⁻¹) (G6.coreAct 5 g y) = G6.coreAct 5 g y
          rw [← MulAut.mul_apply, ← map_mul, show g * x * g⁻¹ * g = g * x by group, map_mul,
            MulAut.mul_apply, h1]⟩
        invFun := fun y => ⟨G6.coreAct 5 g⁻¹ y, fun σ hσ => by
          have h1 := y.2 (g * σ * g⁻¹) ⟨σ, hσ, rfl⟩
          rw [← MulAut.mul_apply, ← map_mul, show σ * g⁻¹ = g⁻¹ * (g * σ * g⁻¹) by group,
            map_mul, MulAut.mul_apply, h1]⟩
        left_inv := fun y => Subtype.ext (by
          show G6.coreAct 5 g⁻¹ (G6.coreAct 5 g y) = y
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
        right_inv := fun y => Subtype.ext (by
          show G6.coreAct 5 g (G6.coreAct 5 g⁻¹ y) = y
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]) }
    exact (Nat.card_congr e).symm
  set S : Finset (Perm (Fin 5)) := GE23.d8list.toFinset.filter (· ∈ B₀') with hS
  have hSmem : ∀ σ, σ ∈ S ↔ σ ∈ B₀' := by
    intro σ
    rw [hS, Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨GE23.mem_d8_iff.mp (hB₀'D h), h⟩⟩
  have hc' : ∀ x ∈ B₀', ∀ y ∈ B₀', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have h2' : ∀ x ∈ B₀', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h2 x hx, map_one]
  have hcl := GE23.fixVec_classify S (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (fun a ha b hb => ⟨(hSmem _).2 (B₀'.mul_mem ((hSmem a).1 ha) ((hSmem b).1 hb)),
      hc' a ((hSmem a).1 ha) b ((hSmem b).1 hb), h2' a ((hSmem a).1 ha)⟩)
    ((hSmem 1).2 B₀'.one_mem)
  have hScard : S.card = Nat.card ↥B₀' := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hSmem)
  rw [← hcardB, ← hfixcard, GE23.card_fixΔ hSmem, ← hScard]
  exact hcl.1

theorem zpowers_allOnes_inf_coreMod_five :
    Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxz : x ∈ Subgroup.zpowers (G6.allOnes 5) := (Subgroup.mem_inf.mp hx).1
  have hxc : x ∈ G6.coreMod 5 := (Subgroup.mem_inf.mp hx).2
  rw [Subgroup.mem_bot]
  have h2 : G6.allOnes 5 ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    show (1 : ZMod 2) + 1 = 0
    decide
  have h1 : G6.allOnes 5 ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    revert this
    decide
  have hord : orderOf (G6.allOnes 5) = 2 := orderOf_eq_prime h2 h1
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hxz
  simp only [Finset.mem_image, Finset.mem_range] at hxz
  obtain ⟨k, hk, rfl⟩ := hxz
  interval_cases k
  · rfl
  · exfalso
    rw [pow_one] at hxc
    have := G6.mem_coreMod.mp hxc
    revert this
    decide

theorem card_mul_card_fixMod_le_sym {G : Subgroup (MulAut V)} {W C : Subgroup V}
    (h : SymmetricNatural G W C 5) {B : Subgroup (MulAut V)} (hBG : B ≤ G)
    (hB : IsElemAbelian2 B) :
    Nat.card ↥B * Nat.card ↥(fixMod B W C) ≤ Nat.card ↥W := by
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 5) →* ↥G, (FFModel.symDn 5).RealizesVia G W C π := h
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful (by norm_num)) hπ
  obtain ⟨hsurj, hCW, -, hUinv, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  set B' : Subgroup (Perm (Fin 5)) := (B.subgroupOf G).comap π with hB'
  have hcardB : Nat.card ↥B = Nat.card ↥B' := by
    have e1 : Nat.card ↥B = Nat.card ↥(B.subgroupOf G) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv).symm
    have e2 : (B'.map π) = B.subgroupOf G := Subgroup.map_comap_eq_self_of_surjective hsurj _
    rw [e1, ← e2]
    exact Subgroup.card_map_of_injective hinj
  have hmemB : ∀ x ∈ B', ((π x : ↥G) : MulAut V) ∈ B := fun x hx => Subgroup.mem_subgroupOf.mp hx
  have hc' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy => hinj (Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul]
    exact hB.1 _ (hmemB x hx) _ (hmemB y hy)))
  have h2' : ∀ x ∈ B', x * x = 1 := fun x hx => hinj (Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul, map_one, Subgroup.coe_one]
    rw [← sq]
    exact hB.2 _ (hmemB x hx)))
  set M := ↥(FFModel.symDn 5).sec ⧸ (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec
  have hmk : Function.Injective (QuotientGroup.mk' ((FFModel.symDn 5).ker.subgroupOf
      (FFModel.symDn 5).sec)) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hm
    have hm' := (eq_bot_iff.mp zpowers_allOnes_inf_coreMod_five) hm
    exact Subtype.ext (Subgroup.mem_bot.mp hm')
  have hMcard : Nat.card M = 16 := by
    have : Nat.card M = Nat.card ↥(FFModel.symDn 5).sec :=
      (Nat.card_congr (Equiv.ofBijective _ ⟨hmk, QuotientGroup.mk'_surjective _⟩)).symm
    rw [this]
    exact GE23.card_coreMod
  have hβker : Nat.card ↥β.ker = Nat.card ↥C := by
    have e : β.ker = C.subgroupOf W := by
      ext u
      rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv
  have hW : Nat.card ↥W = Nat.card ↥C * 16 := by
    have h1 := ff_card_eq_card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hMcard, hβker] at h1
    exact h1
  set F := (fixMod B W C).subgroupOf W with hF
  have hFcard : Nat.card ↥(fixMod B W C) = Nat.card ↥F :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun w hw => (mem_fixMod.mp hw).1).toEquiv).symm
  let βF : ↥F →* M := β.comp F.subtype
  have hβFker : Nat.card ↥βF.ker ≤ Nat.card ↥C := by
    rw [← hβker]
    refine Nat.card_le_card_of_injective (fun x : ↥βF.ker => (⟨((x : ↥F) : ↥W), x.2⟩ : ↥β.ker))
      fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥β.ker => (z : ↥W)) h))
  have hβFrange : Nat.card ↥βF.range ≤ Nat.card ↥(GE23.fixΔ B') := by
    have hsub : ∀ y ∈ βF.range, ∃ m : ↥(GE23.fixΔ B'),
        QuotientGroup.mk' ((FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec)
          ⟨((m : ↥(G6.coreMod 5)) : G6.PermMod 5), (m : ↥(G6.coreMod 5)).2⟩ = y := by
      rintro y ⟨⟨u, hu⟩, rfl⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective
        ((FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec) (β u)
      refine ⟨⟨⟨m.1, m.2⟩, fun σ hσ => ?_⟩, hm⟩
      have hσB := hmemB σ hσ
      have hu' : (u : V) ∈ fixMod B W C := Subgroup.mem_subgroupOf.mp hu
      have hgu : ((π σ : ↥G) : MulAut V) (u : V) ∈ W := hUinv (π σ) u u.2
      have hact : (FFModel.symDn 5).act σ (m : (FFModel.symDn 5).Amb) ∈
          (FFModel.symDn 5).sec := G6.permAct_mem_coreMod σ m.2
      have h1 := hβe σ u m hgu hact hm.symm
      have h2 : ((π σ : ↥G) : MulAut V) (u : V) * (u : V)⁻¹ ∈ C := hu'.2 _ hσB
      have h3 : β ⟨((π σ : ↥G) : MulAut V) (u : V), hgu⟩ = β u := by
        have h4 : β ⟨((π σ : ↥G) : MulAut V) (u : V), hgu⟩ * (β u)⁻¹ = 1 := by
          rw [← map_inv, ← map_mul]
          exact (hβk _).mpr h2
        exact mul_inv_eq_one.mp h4
      have h1' := h3.symm.trans h1
      have h5 := hmk (hm.trans h1')
      apply Subtype.ext
      exact (congrArg Subtype.val h5).symm
    classical
    let f : ↥(GE23.fixΔ B') → M := fun m =>
      QuotientGroup.mk' ((FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec)
        ⟨((m : ↥(G6.coreMod 5)) : G6.PermMod 5), (m : ↥(G6.coreMod 5)).2⟩
    have hf : Function.Injective f := fun a b hab => Subtype.ext (Subtype.ext
      (congrArg Subtype.val (hmk hab)))
    calc Nat.card ↥βF.range ≤ Nat.card (Set.range f) := by
          refine Nat.card_le_card_of_injective (fun y : ↥βF.range => (⟨(y : M), ?_⟩ :
            Set.range f)) fun y z h => Subtype.ext (congrArg (fun q : Set.range f => (q : M)) h)
          obtain ⟨m, hm⟩ := hsub y y.2
          exact ⟨m, hm⟩
      _ = Nat.card ↥(GE23.fixΔ B') := Nat.card_range_of_injective hf
  have hFc : Nat.card ↥F = Nat.card ↥βF.ker * Nat.card ↥βF.range :=
    ff_card_eq_card_ker_mul_card_range βF
  have hbound := card_mul_card_fixΔ_le hc' h2'
  rw [hcardB, hFcard, hFc, hW]
  calc Nat.card ↥B' * (Nat.card ↥βF.ker * Nat.card ↥βF.range)
      ≤ Nat.card ↥B' * (Nat.card ↥C * Nat.card ↥(GE23.fixΔ B')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hβFker hβFrange)
    _ = Nat.card ↥C * (Nat.card ↥B' * Nat.card ↥(GE23.fixΔ B')) := by ring
    _ ≤ Nat.card ↥C * 16 := Nat.mul_le_mul_left _ hbound

end Sym

end FFTwo

end CFSG.Quasithin.H13.A6
