module

public import CFSG.Quasithin.Background.SmithD321Fac
public import CFSG.Quasithin.Background.SmithD321SQ
public import CFSG.Quasithin.Vol2.Ch11SecOE3F
public import CFSG.Quasithin.Background.SmithD37Flag
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34GL32
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.EmptyFaithful.S146F3
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.SmithD321Kplus
public import CFSG.Quasithin.Background.SmithD321Sym
public import CFSG.Quasithin.Background.SmithD321Three
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import CFSG.Timmesfeld.Orders.Classical

public section

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Pointwise

namespace CFSG.Quasithin.SmithD321

section Inner

variable {Γ : Type*} [Group Γ]

theorem induces_inner_mul {L : Subgroup Γ} {a b : Γ}
    (ha : ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹)
    (hb : ∃ l ∈ L, ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹) :
    ∃ l ∈ L, ∀ x ∈ L, (a * b) * x * (a * b)⁻¹ = l * x * l⁻¹ := by
  obtain ⟨l₁, hl₁, h₁⟩ := ha
  obtain ⟨l₂, hl₂, h₂⟩ := hb
  refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, fun x hx => ?_⟩
  have h3 := h₁ _ (L.mul_mem (L.mul_mem hl₂ hx) (L.inv_mem hl₂))
  calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * (l₂ * x * l₂⁻¹) * a⁻¹ := by rw [h₂ x hx]
    _ = l₁ * (l₂ * x * l₂⁻¹) * l₁⁻¹ := h3
    _ = (l₁ * l₂) * x * (l₁ * l₂)⁻¹ := by group

theorem induces_inner_inv {L : Subgroup Γ} {a : Γ}
    (ha : ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    ∃ l ∈ L, ∀ x ∈ L, a⁻¹ * x * a⁻¹⁻¹ = l * x * l⁻¹ := by
  obtain ⟨l, hl, h⟩ := ha
  refine ⟨l⁻¹, L.inv_mem hl, fun x hx => ?_⟩
  have h1 := h _ (L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl)
  calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (l * (l⁻¹ * x * l) * l⁻¹) * a := by group
    _ = a⁻¹ * (a * (l⁻¹ * x * l) * a⁻¹) * a := by rw [h1]
    _ = l⁻¹ * x * l⁻¹⁻¹ := by group

theorem induces_inner_pow {L : Subgroup Γ} {a : Γ}
    (ha : ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) (n : ℕ) :
    ∃ l ∈ L, ∀ x ∈ L, a ^ n * x * (a ^ n)⁻¹ = l * x * l⁻¹ := by
  induction n with
  | zero => exact ⟨1, L.one_mem, fun x _ => by simp⟩
  | succ n ih =>
    rw [pow_succ]
    exact induces_inner_mul ih ha

theorem exists_subgroup_induces_inner (G L : Subgroup Γ) :
    ∃ H : Subgroup ↥G, ∀ g : ↥G,
      g ∈ H ↔ ∃ l ∈ L, ∀ x ∈ L, (g : Γ) * x * (g : Γ)⁻¹ = l * x * l⁻¹ :=
  ⟨{ carrier := {g | ∃ l ∈ L, ∀ x ∈ L, (g : Γ) * x * (g : Γ)⁻¹ = l * x * l⁻¹}
     one_mem' := ⟨1, L.one_mem, fun x _ => by simp⟩
     mul_mem' := fun ha hb => induces_inner_mul ha hb
     inv_mem' := fun ha => induces_inner_inv ha }, fun _ => Iff.rfl⟩

theorem index_eq_two_of_mul_mem {G : Type*} [Group G] {H : Subgroup G} {a : G} (ha : a ∉ H)
    (h : ∀ b c, b ∉ H → c ∉ H → b * c ∈ H) : H.index = 2 := by
  refine Subgroup.index_eq_two_iff.2 ⟨a, fun b => ?_⟩
  by_cases hb : b ∈ H
  · have hba : b * a ∉ H := fun hba => ha (by simpa using H.mul_mem (H.inv_mem hb) hba)
    exact Or.inr ⟨hb, hba⟩
  · exact Or.inl ⟨h b a hb ha, hb⟩

end Inner

section Homog

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem inf_eq_bot_of_not_iso {A : Type*} [Group A] [MulDistribMulAction A Q]
    {X Y : Subgroup Q} (hX : XMod.IsIrr A X) (hY : XMod.IsIrr A Y)
    (hXY : ¬ XMod.Iso A X Y) : X ⊓ Y = ⊥ := by
  rcases hX.2.2 (X ⊓ Y) (hX.1.inf hY.1) bot_le inf_le_left with h | h
  · exact h
  · rcases hY.2.2 X hX.1 bot_le (h.symm.le.trans inf_le_right) with h' | h'
    · exact absurd h' hX.2.1.ne'
    · exact absurd (by rw [h']; exact XMod.Iso.refl Y) hXY

theorem inf_sup_eq_bot_of_not_iso {A : Type*} [Group A] [MulDistribMulAction A Q]
    {X Y Z : Subgroup Q} (hX : XMod.IsIrr A X) (hY : XMod.IsIrr A Y) (hZ : XMod.IsIrr A Z)
    (hZX : ¬ XMod.Iso A Z X) (hZY : ¬ XMod.Iso A Z Y) : Z ⊓ (X ⊔ Y) = ⊥ := by
  rcases hZ.2.2 (Z ⊓ (X ⊔ Y)) (hZ.1.inf (hX.1.sup hY.1)) bot_le inf_le_left with h | h
  · exact h
  · have hle : Z ≤ ⨆ b : Bool, cond b X Y := by
      rw [iSup_bool_eq]
      exact h.symm.le.trans inf_le_right
    obtain ⟨b, hb⟩ := exists_iso_of_le_iSup (S := fun b => cond b X Y)
      (fun b => by cases b; exacts [hY, hX]) hZ hle
    cases b
    · exact absurd hb hZY
    · exact absurd hb hZX

theorem smul_eq_of_isInv {Λ : Subgroup Γ} {W : Subgroup Q} (hW : XMod.IsInv ↥Λ W) {l : Γ}
    (hl : l ∈ Λ) : l • W = W := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    have h1 := hW ⟨l, hl⟩ _ hq
    rwa [show (⟨l, hl⟩ : ↥Λ) • l⁻¹ • q = q from smul_inv_smul l q] at h1
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact hW ⟨l⁻¹, Λ.inv_mem hl⟩ q hq

theorem iso_of_odd_index [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {G Λ P : Subgroup Γ}
    (hΛG : ∀ g ∈ G, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hodd : Odd (P.subgroupOf G).index)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) (hPV : ∀ p ∈ P, p • V = V)
    (hrk : rk ↥(⨆ g ∈ G, g • V) ≤ 2 * rk ↥V) :
    ∀ g ∈ G, XMod.Iso ↥Λ (g • V) V := by
  have hN : XMod.Normalizes ↥Λ ↥G Q := normalizes_of_conj Λ G hΛG
  obtain ⟨St, hSt⟩ : ∃ St : Subgroup ↥G, ∀ t : ↥G, t ∈ St ↔ XMod.Iso ↥Λ ((t : Γ) • V) V := by
    refine ⟨{ carrier := {t | XMod.Iso ↥Λ ((t : Γ) • V) V}
              one_mem' := by
                change XMod.Iso ↥Λ ((1 : Γ) • V) V
                rw [one_smul]
                exact XMod.Iso.refl V
              mul_mem' := fun {a b} ha hb => by
                change XMod.Iso ↥Λ (((a : Γ) * (b : Γ)) • V) V
                rw [mul_smul]
                exact (XMod.iso_smul hN a hb).trans ha
              inv_mem' := fun {a} ha => by
                change XMod.Iso ↥Λ ((a : Γ)⁻¹ • V) V
                have h1 : XMod.Iso ↥Λ ((a : Γ)⁻¹ • (a : Γ) • V) ((a : Γ)⁻¹ • V) :=
                  XMod.iso_smul hN a⁻¹ ha
                rw [inv_smul_smul] at h1
                exact XMod.Iso.symm hV.1 h1 }, fun _ => Iff.rfl⟩
  have hPSt : P.subgroupOf G ≤ St := fun t ht => by
    rw [hSt, hPV _ (Subgroup.mem_subgroupOf.1 ht)]
    exact XMod.Iso.refl V
  have hStodd : Odd St.index := Odd.of_dvd_nat hodd (Subgroup.index_dvd_of_le hPSt)
  have hSt2 : St.index ≠ 2 := fun h2 => by rw [h2] at hStodd; exact absurd hStodd (by decide)
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg, hgV⟩ := hcon
  have hg₁ : (⟨g, hg⟩ : ↥G) ∉ St := fun h => hgV ((hSt _).1 h)
  set g₁ : ↥G := ⟨g, hg⟩
  obtain ⟨g₂, hg₂, hg₁₂⟩ : ∃ g₂ : ↥G, g₂ ∉ St ∧ g₁⁻¹ * g₂ ∉ St := by
    by_contra hcon
    push Not at hcon
    refine hSt2 (index_eq_two_of_mul_mem hg₁ fun b c hb hc => ?_)
    have h1 := St.mul_mem (St.inv_mem (hcon b⁻¹ fun h => hb (by simpa using St.inv_mem h)))
      (hcon c hc)
    rwa [show (g₁⁻¹ * b⁻¹)⁻¹ * (g₁⁻¹ * c) = b * c by group] at h1
  have hirr : ∀ t : ↥G, XMod.IsIrr ↥Λ ((t : Γ) • V) := fun t => isIrr_smul hN t hV
  have hYX : ¬ XMod.Iso ↥Λ ((g₁ : Γ) • V) V := fun h => hg₁ ((hSt _).2 h)
  have hZX : ¬ XMod.Iso ↥Λ ((g₂ : Γ) • V) V := fun h => hg₂ ((hSt _).2 h)
  have hZY : ¬ XMod.Iso ↥Λ ((g₂ : Γ) • V) ((g₁ : Γ) • V) := fun h => by
    have h1 : XMod.Iso ↥Λ ((g₁ : Γ)⁻¹ • (g₂ : Γ) • V) ((g₁ : Γ)⁻¹ • (g₁ : Γ) • V) :=
      XMod.iso_smul hN g₁⁻¹ h
    rw [inv_smul_smul, smul_smul] at h1
    exact hg₁₂ ((hSt _).2 h1)
  have hXY : V ⊓ (g₁ : Γ) • V = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_not_iso (hirr g₁) hV hYX
  have hZXY := inf_sup_eq_bot_of_not_iso hV (hirr g₁) (hirr g₂) hZX hZY
  have hle : (g₂ : Γ) • V ⊔ (V ⊔ (g₁ : Γ) • V) ≤ ⨆ g ∈ G, g • V := by
    refine sup_le (le_iSup₂_of_le (g₂ : Γ) g₂.2 le_rfl)
      (sup_le (le_iSup₂_of_le (1 : Γ) G.one_mem (one_smul Γ V).ge)
        (le_iSup₂_of_le (g₁ : Γ) g₁.2 le_rfl))
  have h1 := rk_sup_add_rk_inf V ((g₁ : Γ) • V)
  have h2 := rk_sup_add_rk_inf ((g₂ : Γ) • V) (V ⊔ (g₁ : Γ) • V)
  have h3 := rk_mono hle
  rw [hXY, rk_bot, rk_smul] at h1
  rw [hZXY, rk_bot, rk_smul] at h2
  have h0 : rk ↥V = 0 := by omega
  exact hV.2.1.ne' ((rk_eq_zero_iff hQ).1 h0)

theorem exists_mul_mul_of_out_two {G L P : Subgroup Γ} (hLG : L ≤ G) (hPG : P ≤ G)
    (hodd : Odd (P.subgroupOf G).index)
    (hout : ∀ g₁ ∈ G, ∀ g₂ ∈ G, (¬ ∃ l ∈ L, ∀ x ∈ L, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ L, ∀ x ∈ L, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L, ∀ x ∈ L, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹) :
    ∀ g ∈ G, ∃ l ∈ L, ∃ c ∈ G, (∀ x ∈ L, c * x = x * c) ∧ ∃ τ ∈ P, g = l * c * τ := by
  have key : ∀ g ∈ G, (∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L, ∃ c ∈ G, (∀ x ∈ L, c * x = x * c) ∧ g = l * c := by
    rintro g hg ⟨l, hl, h⟩
    refine ⟨l, hl, l⁻¹ * g, G.mul_mem (G.inv_mem (hLG hl)) hg, fun x hx => ?_, by group⟩
    calc l⁻¹ * g * x = l⁻¹ * (g * x * g⁻¹) * g := by group
      _ = l⁻¹ * (l * x * l⁻¹) * g := by rw [h x hx]
      _ = x * (l⁻¹ * g) := by group
  intro g hg
  by_cases hin : ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹
  · obtain ⟨l, hl, c, hc, hcL, rfl⟩ := key g hg hin
    exact ⟨l, hl, c, hc, hcL, 1, P.one_mem, by rw [mul_one]⟩
  obtain ⟨τ, hτ, hτn⟩ : ∃ τ ∈ P, ¬ ∃ l ∈ L, ∀ x ∈ L, τ * x * τ⁻¹ = l * x * l⁻¹ := by
    by_contra hcon
    obtain ⟨H, hH⟩ := exists_subgroup_induces_inner G L
    have hPH : P.subgroupOf G ≤ H := fun t ht => by
      rw [hH]
      by_contra h
      exact hcon ⟨t, Subgroup.mem_subgroupOf.1 ht, h⟩
    have hgH : (⟨g, hg⟩ : ↥G) ∉ H := fun h => hin ((hH _).1 h)
    have h2 : H.index = 2 := index_eq_two_of_mul_mem hgH fun b c hb hc =>
      (hH _).2 (hout b b.2 c c.2 (fun h => hb ((hH _).2 h)) fun h => hc ((hH _).2 h))
    have h3 := Subgroup.index_dvd_of_le hPH
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)
  have hτ' : τ⁻¹ ∈ G := G.inv_mem (hPG hτ)
  have hτn' : ¬ ∃ l ∈ L, ∀ x ∈ L, τ⁻¹ * x * τ⁻¹⁻¹ = l * x * l⁻¹ := fun h =>
    hτn (by simpa using induces_inner_inv h)
  obtain ⟨l, hl, c, hc, hcL, he⟩ := key _ (G.mul_mem hg hτ') (hout g hg τ⁻¹ hτ' hin hτn')
  exact ⟨l, hl, c, hc, hcL, τ, hτ, by rw [← he]; group⟩

theorem iso_of_factorization {G Λ P : Subgroup Γ} {V : Subgroup Q}
    (hV : XMod.IsInv ↥Λ V) (hPV : ∀ p ∈ P, p • V = V)
    (hfac : ∀ g ∈ G, ∃ l ∈ Λ, ∃ c ∈ G, (∀ x ∈ Λ, c * x = x * c) ∧ ∃ τ ∈ P, g = l * c * τ) :
    ∀ g ∈ G, XMod.Iso ↥Λ (g • V) V := by
  intro g hg
  obtain ⟨l, hl, c, -, hc, τ, hτ, rfl⟩ := hfac g hg
  have hcV : XMod.IsInv ↥Λ (c • V) := fun a q hq => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq ⊢
    have h1 : c⁻¹ * (a : Γ) = (a : Γ) * c⁻¹ := by
      calc c⁻¹ * (a : Γ) = c⁻¹ * ((a : Γ) * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * (a : Γ)) * c⁻¹ := by rw [hc a a.2]
        _ = (a : Γ) * c⁻¹ := by group
    change c⁻¹ • (a : Γ) • q ∈ V
    rw [smul_smul, h1, mul_smul]
    exact hV a _ hq
  rw [mul_smul, mul_smul, hPV τ hτ, smul_eq_of_isInv hcV hl]
  exact iso_smul_of_comm hV hc

end Homog

section Out

variable {Γ : Type*} [Group Γ]

theorem exists_conj_hom_mulAut {G L : Subgroup Γ} (hGL : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    ∃ φ : ↥G →* MulAut ↥L,
      ∀ (g : ↥G) (x : ↥L), ((φ g x : ↥L) : Γ) = (g : Γ) * x * (g : Γ)⁻¹ := by
  have hinv : ∀ g ∈ G, ∀ l ∈ L, g⁻¹ * l * g ∈ L := fun g hg l hl => by
    simpa using hGL g⁻¹ (G.inv_mem hg) l hl
  refine ⟨{ toFun := fun g =>
              { toFun := fun x => ⟨g * x * g⁻¹, hGL g g.2 x x.2⟩
                invFun := fun x => ⟨g⁻¹ * x * g, hinv g g.2 x x.2⟩
                left_inv := fun x => Subtype.ext (by simp [mul_assoc])
                right_inv := fun x => Subtype.ext (by simp [mul_assoc])
                map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
            map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
            map_mul' := fun a b => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc]) },
          fun _ _ => rfl⟩

theorem induces_inner_iff_eq_conj {G L : Subgroup Γ} {φ : ↥G →* MulAut ↥L}
    (hφ : ∀ (g : ↥G) (x : ↥L), ((φ g x : ↥L) : Γ) = (g : Γ) * x * (g : Γ)⁻¹) (g : ↥G) :
    (∃ l ∈ L, ∀ x ∈ L, (g : Γ) * x * (g : Γ)⁻¹ = l * x * l⁻¹) ↔
      ∃ k : ↥L, φ g = MulAut.conj k := by
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨⟨l, hl⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hφ, h x x.2, MulAut.conj_apply]
    rfl
  · rintro ⟨k, hk⟩
    refine ⟨k, k.2, fun x hx => ?_⟩
    have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨x, hx⟩ : ↥L) : Γ)) hk
    simpa [hφ, MulAut.conj_apply] using h1

end Out

section L32

open CFSG.QuasithinUnique.DoubleA3 (IsInner isInner_iff_conj out_mul32)
open CFSG.QuasithinUnique.Setup.Family (GL32 slEquivGL)
open CFSG.LieType.SteinbergBR.AltFiveGL3 (congr_conj)

variable {Γ : Type} [Group Γ]

theorem out_two_of_isPSL32 {G L : Subgroup Γ} (hL : IsPSL 3 2 1 ↥L)
    (hGL : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    ∀ g₁ ∈ G, ∀ g₂ ∈ G, (¬ ∃ l ∈ L, ∀ x ∈ L, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ L, ∀ x ∈ L, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L, ∀ x ∈ L, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹ := by
  obtain ⟨e₀⟩ := nonempty_mulEquiv_slThree_of_isPSL hL
  let e : ↥L ≃* GL32 := e₀.trans (slEquivGL 3)
  obtain ⟨φ, hφ⟩ := exists_conj_hom_mulAut hGL
  have key : ∀ g : ↥G, (∃ l ∈ L, ∀ x ∈ L, (g : Γ) * x * (g : Γ)⁻¹ = l * x * l⁻¹) ↔
      IsInner (MulAut.congr e (φ g)) := by
    intro g
    rw [induces_inner_iff_eq_conj hφ, isInner_iff_conj]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨e k, by rw [hk, congr_conj]⟩
    · rintro ⟨k', hk'⟩
      refine ⟨e.symm k', (MulAut.congr e).injective ?_⟩
      rw [hk', congr_conj, MulEquiv.apply_symm_apply]
  intro g₁ hg₁ g₂ hg₂ h₁ h₂
  refine (key (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩)).2 ?_
  rw [map_mul φ, map_mul (MulAut.congr e)]
  exact out_mul32 _ _ (fun h => h₁ ((key ⟨g₁, hg₁⟩).2 h)) fun h => h₂ ((key ⟨g₂, hg₂⟩).2 h)

end L32

section Alt5

open CFSG.LieType.SteinbergBR.AltFiveGL3 (autEquivPerm autEquivPerm_symm_eq_conj)

variable {Γ : Type*} [Group Γ]

theorem out_two_of_alt5 {G L : Subgroup Γ} (hL : Nonempty (↥L ≃* alternatingGroup (Fin 5)))
    (hGL : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    ∀ g₁ ∈ G, ∀ g₂ ∈ G, (¬ ∃ l ∈ L, ∀ x ∈ L, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ L, ∀ x ∈ L, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L, ∀ x ∈ L, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹ := by
  obtain ⟨e⟩ := hL
  obtain ⟨φ, hφ⟩ := exists_conj_hom_mulAut hGL
  let s : ↥G →* ℤˣ := Equiv.Perm.sign.comp ((autEquivPerm e).toMonoidHom.comp φ)
  have key : ∀ g : ↥G, (∃ l ∈ L, ∀ x ∈ L, (g : Γ) * x * (g : Γ)⁻¹ = l * x * l⁻¹) ↔ s g = 1 := by
    intro g
    rw [induces_inner_iff_eq_conj hφ]
    constructor
    · rintro ⟨k, hk⟩
      have h1 := autEquivPerm_symm_eq_conj e (e k).2
      simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply] at h1
      change Equiv.Perm.sign (autEquivPerm e (φ g)) = 1
      rw [hk, ← h1, MulEquiv.apply_symm_apply]
      exact Equiv.Perm.mem_alternatingGroup.1 (e k).2
    · intro h
      have hσ : autEquivPerm e (φ g) ∈ alternatingGroup (Fin 5) :=
        Equiv.Perm.mem_alternatingGroup.2 h
      refine ⟨e.symm ⟨_, hσ⟩, ?_⟩
      rw [← autEquivPerm_symm_eq_conj e hσ, MulEquiv.symm_apply_apply]
  intro g₁ hg₁ g₂ hg₂ h₁ h₂
  have s₁ : s ⟨g₁, hg₁⟩ = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => h₁ ((key ⟨g₁, hg₁⟩).2 h)
  have s₂ : s ⟨g₂, hg₂⟩ = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => h₂ ((key ⟨g₂, hg₂⟩).2 h)
  refine (key (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩)).2 ?_
  rw [map_mul, s₁, s₂]
  exact Int.units_mul_self (-1)

theorem inner_of_odd_of_out_two {G L : Subgroup Γ}
    (hout : ∀ g₁ ∈ G, ∀ g₂ ∈ G, (¬ ∃ l ∈ L, ∀ x ∈ L, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ L, ∀ x ∈ L, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L, ∀ x ∈ L, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹) {y : Γ} (hy : y ∈ G)
    {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ = l * x * l⁻¹ := by
  by_contra h
  obtain ⟨k, rfl⟩ := hm
  have h2 := induces_inner_pow (hout y hy y hy h h) (k + 1)
  have hy' : (y * y) ^ (k + 1) = y := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hym, one_mul]
  rw [hy'] at h2
  exact h h2

end Alt5

section Rank

theorem eq_one_of_mem_center_slThree_two {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h1 : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
  rw [Fintype.card_fin] at hr
  refine Subtype.ext ?_
  rw [← hrA, h1 r hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_central_of_isPSL32 {Γ : Type} [Group Γ] {X : Subgroup Γ}
    (hX : IsPSL 3 2 1 ↥X) {l : Γ} (hl : l ∈ X) (hlX : ∀ x ∈ X, l * x = x * l) : l = 1 := by
  obtain ⟨σ⟩ := nonempty_mulEquiv_slThree_of_isPSL hX
  have h1 : σ ⟨l, hl⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    refine Subgroup.mem_center_iff.2 fun B => ?_
    obtain ⟨y, rfl⟩ := σ.surjective B
    rw [← map_mul σ, ← map_mul σ]
    exact congrArg σ (Subtype.ext (hlX y y.2).symm)
  have h2 : (⟨l, hl⟩ : ↥X) = 1 :=
    σ.injective (by rw [eq_one_of_mem_center_slThree_two h1, map_one])
  exact congrArg Subtype.val h2

theorem rk_le_three_of_isPSL32 {Γ : Type} [Group Γ] [Finite Γ] {X E : Subgroup Γ}
    (hX : IsPSL 3 2 1 ↥X) (hEX : ∀ e ∈ E, ∀ x ∈ X, e * x * e⁻¹ ∈ X)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEC : ∀ e ∈ E, (∀ x ∈ X, e * x = x * e) → e = 1) : rk ↥E ≤ 3 := by
  obtain ⟨σ⟩ := nonempty_mulEquiv_slThree_of_isPSL hX
  have huniq : ∀ l₁ ∈ X, ∀ l₂ ∈ X, (∀ x ∈ X, l₁ * x * l₁⁻¹ = l₂ * x * l₂⁻¹) → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ h
    have h3 := eq_one_of_central_of_isPSL32 hX (X.mul_mem (X.inv_mem h₂) h₁) fun x hx => by
      calc l₂⁻¹ * l₁ * x = l₂⁻¹ * (l₁ * x * l₁⁻¹) * l₁ := by group
        _ = l₂⁻¹ * (l₂ * x * l₂⁻¹) * l₁ := by rw [h x hx]
        _ = x * (l₂⁻¹ * l₁) := by group
    calc l₁ = l₂ * (l₂⁻¹ * l₁) := by group
      _ = l₂ := by rw [h3, mul_one]
  have hmul : ∀ a b la lb : Γ, lb ∈ X → (∀ x ∈ X, a * x * a⁻¹ = la * x * la⁻¹) →
      (∀ x ∈ X, b * x * b⁻¹ = lb * x * lb⁻¹) →
      ∀ x ∈ X, (a * b) * x * (a * b)⁻¹ = (la * lb) * x * (la * lb)⁻¹ := by
    intro a b la lb hlb ha hb x hx
    calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (lb * x * lb⁻¹) * a⁻¹ := by rw [hb x hx]
      _ = la * (lb * x * lb⁻¹) * la⁻¹ := ha _ (X.mul_mem (X.mul_mem hlb hx) (X.inv_mem hlb))
      _ = (la * lb) * x * (la * lb)⁻¹ := by group
  obtain ⟨H, hH⟩ := exists_subgroup_induces_inner E X
  have hEH : Nat.card E ≤ 2 * Nat.card H := by
    by_cases hall : ∀ a, a ∈ H
    · rw [show H = ⊤ from eq_top_iff.2 fun a _ => hall a, Subgroup.card_top]
      omega
    · obtain ⟨a, ha⟩ := not_forall.1 hall
      have h2 : H.index = 2 := index_eq_two_of_mul_mem ha fun b c hb hc =>
        (hH _).2 (out_two_of_isPSL32 hX hEX b b.2 c c.2 (fun h => hb ((hH _).2 h))
          fun h => hc ((hH _).2 h))
      have h3 := H.card_mul_index
      rw [h2] at h3
      omega
  choose l hlX hl using fun g : ↥H => (hH g).1 g.2
  have hcomm : ∀ g₁ g₂ : ↥H, l g₁ * l g₂ = l g₂ * l g₁ := by
    intro g₁ g₂
    refine huniq _ (X.mul_mem (hlX g₁) (hlX g₂)) _ (X.mul_mem (hlX g₂) (hlX g₁)) fun x hx => ?_
    rw [← hmul _ _ _ _ (hlX g₂) (hl g₁) (hl g₂) x hx,
      ← hmul _ _ _ _ (hlX g₁) (hl g₂) (hl g₁) x hx, hEc _ (g₁ : ↥E).2 _ (g₂ : ↥E).2]
  have hsq : ∀ g : ↥H, l g * l g = 1 := by
    intro g
    refine huniq _ (X.mul_mem (hlX g) (hlX g)) _ X.one_mem fun x hx => ?_
    rw [← hmul _ _ _ _ (hlX g) (hl g) (hl g) x hx, ← sq, hE2 _ (g : ↥E).2]
  let f : ↥H → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun g =>
    ((σ ⟨l g, hlX g⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hf : Function.Injective f := by
    intro g₁ g₂ h
    have h' : σ ⟨l g₁, hlX g₁⟩ = σ ⟨l g₂, hlX g₂⟩ := Subtype.ext h
    have h1 : l g₁ = l g₂ := congrArg Subtype.val (σ.injective h')
    have h2 := hEC _ (E.mul_mem (E.inv_mem (g₂ : ↥E).2) (g₁ : ↥E).2) fun x hx => by
      have h3 := hl g₁ x hx
      rw [h1, ← hl g₂ x hx] at h3
      calc ((g₂ : ↥E) : Γ)⁻¹ * ((g₁ : ↥E) : Γ) * x
          = ((g₂ : ↥E) : Γ)⁻¹ * (((g₁ : ↥E) : Γ) * x * ((g₁ : ↥E) : Γ)⁻¹) * ((g₁ : ↥E) : Γ) := by
            group
        _ = ((g₂ : ↥E) : Γ)⁻¹ * (((g₂ : ↥E) : Γ) * x * ((g₂ : ↥E) : Γ)⁻¹) * ((g₁ : ↥E) : Γ) := by
            rw [h3]
        _ = x * (((g₂ : ↥E) : Γ)⁻¹ * ((g₁ : ↥E) : Γ)) := by group
    exact Subtype.ext (Subtype.ext (inv_mul_eq_one.1 h2).symm)
  have hH4 : Nat.card H ≤ 4 := by
    have h1 := SmithD310U.card_le_sq (K := ZMod 2) (S := Set.range f) (by decide) ?_ ?_
    · rwa [Nat.card_range_of_injective hf, Nat.card_zmod] at h1
    · rintro _ ⟨g, rfl⟩
      change ((σ ⟨l g, hlX g⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) * (σ ⟨l g, hlX g⟩ : Matrix _ _ _) = 1
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul σ,
        show (⟨l g, hlX g⟩ * ⟨l g, hlX g⟩ : ↥X) = 1 from Subtype.ext (hsq g), map_one,
        Matrix.SpecialLinearGroup.coe_one]
    · rintro _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩
      change ((σ ⟨l g₁, hlX g₁⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) * (σ ⟨l g₂, hlX g₂⟩ : Matrix _ _ _) =
        (σ ⟨l g₂, hlX g₂⟩ : Matrix _ _ _) * (σ ⟨l g₁, hlX g₁⟩ : Matrix _ _ _)
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        ← map_mul σ, ← map_mul σ,
        show (⟨l g₁, hlX g₁⟩ * ⟨l g₂, hlX g₂⟩ : ↥X) = ⟨l g₂, hlX g₂⟩ * ⟨l g₁, hlX g₁⟩ from
          Subtype.ext (hcomm g₁ g₂)]
  have hP : IsPGroup 2 ↥E :=
    isPGroup_two_of_sq_eq_one fun g => Subtype.ext (by simpa using hE2 g g.2)
  have hc := card_eq_two_pow_of_isPGroup hP
  by_contra hlt
  have h16 : 16 ≤ 2 ^ rk ↥E := (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ 4 ≤ _)
  omega

end Rank

section LiftReal

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

omit [Finite W] in
theorem realizes_lift_of_resJ (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    {X : Subgroup (MulAut W)} (hXM : X ≤ M) (hXs : IsSimpleGroup ↥X) {U : Subgroup W}
    (hUX : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) {J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hJU : J ≤ tilde Mp ⊤ U)
    (hJX : letI := qAct hMp; ∀ g ∈ X.subgroupOf M, ∀ j ∈ J, g • j ∈ J)
    (hnt : letI := qAct hMp; ∃ x ∈ X.subgroupOf M, ∃ j ∈ J, x • j ≠ j)
    {D : FFModel} (hJR : letI := qAct hMp; D.Realizes (resJ (X.subgroupOf M) J hJX).range ⊤ ⊥) :
    D.Realizes X (U ⊓ J.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))))
      (U ⊓ J.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) ⊓ fixV Mp) := by
  let _i := qAct hMp
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  set Λ := X.subgroupOf M with hΛ
  set P := U ⊓ J.comap κ with hP
  have hΛs : IsSimpleGroup ↥Λ := (Subgroup.subgroupOfEquivOfLe hXM).isSimpleGroup
  have hinj := resJ_injective_of_isSimpleGroup hΛs hJX hnt
  let ρ : ↥X →* ↥(resJ Λ J hJX).range :=
    (resJ Λ J hJX).rangeRestrict.comp (Subgroup.subgroupOfEquivOfLe hXM).symm.toMonoidHom
  have hρ : Function.Bijective ρ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 := congrArg Subtype.val hxy
      exact (Subgroup.subgroupOfEquivOfLe hXM).symm.injective (hinj h1)
    · obtain ⟨l, rfl⟩ := (resJ Λ J hJX).rangeRestrict_surjective z
      exact ⟨Subgroup.subgroupOfEquivOfLe hXM l, by
        simp [ρ, MulEquiv.symm_apply_apply]⟩
  set e := MulEquiv.ofBijective ρ hρ with he
  have heρ : ∀ x : ↥X, ((e x : ↥(resJ Λ J hJX).range) : MulAut ↥J) =
      resJ Λ J hJX ⟨⟨x, hXM x.2⟩, Subgroup.mem_subgroupOf.2 x.2⟩ := fun x => rfl
  obtain ⟨πJ, hsurj, -, hkerle, -, -, hsec, hkerinv, βJ, hβs, hβk, hβe⟩ := hJR
  have hgMp : ∀ g ∈ M, ∀ w ∈ fixV Mp, g w ∈ fixV Mp := by
    intro g hg w hw
    refine mem_fixV.2 fun x hx => ?_
    have hx' : g⁻¹ * x * g ∈ Mp := (Subgroup.mem_normalizer_iff''.1 (hMp hg) x).1 hx
    have h1 : (g⁻¹ * x * g) w = w := mem_fixV.1 hw _ hx'
    calc x (g w) = g ((g⁻¹ * x * g) w) := by simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = g w := by rw [h1]
  have hPX : ∀ h : ↥X, ∀ u ∈ P, (h : MulAut W) u ∈ P := fun h u hu =>
    ⟨hUX h h.2 u hu.1, hJX ⟨h, hXM h.2⟩ (Subgroup.mem_subgroupOf.2 h.2) (κ u) hu.2⟩
  let incl : ↥P →* ↥(⊤ : Subgroup ↥J) :=
    { toFun := fun p => ⟨⟨κ p, p.2.2⟩, trivial⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hincl : ∀ p : ↥P, (((incl p : ↥(⊤ : Subgroup ↥J)) : ↥J) : W ⧸ modFix Mp ⊤) = κ p :=
    fun p => rfl
  refine ⟨e.symm.toMonoidHom.comp πJ, e.symm.surjective.comp hsurj, inf_le_left, hkerle, hPX,
    fun h z hz => ⟨hPX h z hz.1, hgMp _ (hXM h.2) z hz.2⟩, hsec, hkerinv, βJ.comp incl, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    obtain ⟨w, hwU, hw⟩ := hJU (u : ↥J).2
    refine ⟨⟨w, hwU, ?_⟩, ?_⟩
    · show κ w ∈ J
      rw [hw]
      exact (u : ↥J).2
    · rw [MonoidHom.comp_apply, ← hu]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact hw
  · intro p
    rw [MonoidHom.comp_apply, hβk]
    constructor
    · intro h
      have h1 : ((incl p : ↥(⊤ : Subgroup ↥J)) : ↥J) = 1 := h
      have h2 : κ p = 1 := by rw [← hincl, h1]; rfl
      exact ⟨p.2, (hker _).1 h2⟩
    · intro h
      show ((incl p : ↥(⊤ : Subgroup ↥J)) : ↥J) = 1
      apply Subtype.ext
      rw [hincl]
      exact (hker _).2 h.2
  · intro γ u m hu hm hbu
    have h1 := hβe γ (incl u) m trivial hm hbu
    rw [MonoidHom.comp_apply]
    convert h1 using 2
    apply Subtype.ext
    apply Subtype.ext
    rw [hincl]
    have h2 : ((πJ γ : ↥(resJ Λ J hJX).range) : MulAut ↥J) =
        resJ Λ J hJX ⟨⟨(e.symm (πJ γ) : MulAut W), hXM (e.symm (πJ γ)).2⟩,
          Subgroup.mem_subgroupOf.2 (e.symm (πJ γ)).2⟩ := by
      rw [← heρ, MulEquiv.apply_symm_apply]
    show _ = (((πJ γ : ↥(resJ Λ J hJX).range) : MulAut ↥J) (incl u : ↥J) : W ⧸ modFix Mp ⊤)
    rw [h2, resJ_apply]
    rfl

end LiftReal



section TranslateV

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem smul_eq_map (t : MulAut W) (V : Subgroup W) : t • V = V.map t.toMonoidHom := rfl

omit [Finite W] in
theorem orbSup_map_of_mem {T : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (ht : t ∈ T) : orbSup T (V.map t.toMonoidHom) = orbSup T V := by
  refine le_antisymm (orbSup_le fun s hs => ?_) (orbSup_le fun s hs => ?_)
  · rw [Subgroup.map_map]
    exact map_le_orbSup (T.mul_mem hs ht)
  · have h1 : V.map s.toMonoidHom = (V.map t.toMonoidHom).map (s * t⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext v
      simp
    rw [h1]
    exact map_le_orbSup (T.mul_mem hs (T.inv_mem ht))

theorem d3Std_map {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V)
    {t : MulAut W} (ht : t ∈ T) : D3Std M Mp T L (V.map t.toMonoidHom) := by
  have htM : t ∈ M := hD.hyp.sylow.1 ht
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := fun s hs =>
    hD.hyp.Mp_normal (hD.hyp.sylow.1 hs)
  have horb := orbSup_map_of_mem (V := V) ht
  refine ⟨{ hD.hyp with
    irr := Vol2.Ch11.OE3.map_mem_irrPlus (hTMp ht) hD.hyp.irr
    o2inv := ?_
    gen := ?_ }, ?_, ?_⟩
  · rintro g hg _ ⟨v, hv, rfl⟩
    have htH : t ∈ Mp ⊔ T := (le_sup_right : T ≤ Mp ⊔ T) ht
    have hg' : t⁻¹ * g * t ∈ pCoreOf 2 (Mp ⊔ T) := by
      obtain ⟨g', hg', rfl⟩ := hg
      have hn := (CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := ↥(Mp ⊔ T))).conj_mem g' hg'
        ⟨t, htH⟩⁻¹
      refine ⟨_, hn, ?_⟩
      simp
    refine ⟨(t⁻¹ * g * t) v, hD.hyp.o2inv _ hg' v hv, ?_⟩
    simp [MulAut.mul_apply]
  · rw [eq_top_iff, ← hD.hyp.gen]
    refine iSup₂_le fun m hm => ?_
    have h1 : V.map m.toMonoidHom = (V.map t.toMonoidHom).map (m * t⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext v
      simp
    rw [h1]
    exact le_iSup₂_of_le (m * t⁻¹) (M.mul_mem hm (M.inv_mem htM)) le_rfl
  · rw [horb]
    exact hD.qhat
  · rw [horb]
    set VT := orbSup T V with hVT
    have hW : ∀ s ∈ T, ∀ w ∈ VT, s • w ∈ VT := fun s hs w hw => mem_orbSup_of_mem_map hs hw
    have hV := hD.irrT
    have hIp : V.map t.toMonoidHom ∈ IrrPlus Mp VT :=
      ⟨map_le_orbSup ht, (Vol2.Ch11.OE3.map_mem_irrPlus (hTMp ht) hD.hyp.irr).2⟩
    refine (forall_smul_eq_iff_mem_irrPlusOn hTMp hW hIp).1 fun s hs => ?_
    let _q := quotAct hTMp hW
    have hfix := (forall_smul_eq_iff_mem_irrPlusOn hTMp hW hV.1).2 hV
    obtain ⟨hsT, hiso⟩ := hs
    have hs' : t⁻¹ * s * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht) hsT) ht
    have e1 : tilde Mp VT (s • V.map t.toMonoidHom) =
        (⟨s * t, T.mul_mem hsT ht⟩ : ↥T) • tilde Mp VT V := by
      rw [tilde_smul hTMp hW]
      show tilde Mp VT (s • (t • V)) = tilde Mp VT ((s * t) • V)
      rw [mul_smul]
    have e2 : tilde Mp VT (V.map t.toMonoidHom) = (⟨t, ht⟩ : ↥T) • tilde Mp VT V := by
      rw [tilde_smul hTMp hW]
      rfl
    rw [e1, e2] at hiso
    have h3 := XMod.iso_smul (normalizes_quot hTMp hW) (⟨t, ht⟩⁻¹ : ↥T) hiso
    rw [smul_smul, smul_smul, inv_mul_cancel, one_smul] at h3
    have h4 : (⟨t, ht⟩⁻¹ * ⟨s * t, T.mul_mem hsT ht⟩ : ↥T) • tilde Mp VT V =
        tilde Mp VT ((t⁻¹ * s * t) • V) := by
      rw [tilde_smul hTMp hW]
      congr 2
    rw [h4] at h3
    have h5 := hfix (t⁻¹ * s * t) ⟨hs', h3⟩
    show s • (t • V) = t • V
    calc s • t • V = t • (t⁻¹ * s * t) • V := by rw [smul_smul, smul_smul]; group
      _ = t • V := by rw [h5]

end TranslateV

section SwapV

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem D321Sit.swapV (hS : D321Sit M Mp T L V t A r) :
    D321Sit M Mp T (conjAutSub t L) (V.map t.toMonoidHom) t⁻¹ A r :=
  ⟨{ hS.swap.toD321Base with hD := d3Std_map hS.swap.hD hS.htT },
    hS.hr, hS.hr2, by rw [orbSup_map_of_mem hS.htT]; exact hS.htop, hS.hAQ, hS.hAT, hS.hAr⟩

theorem D321Base.conjAutSub_inv (hB : D321Base M Mp T L V t) :
    conjAutSub t⁻¹ L = conjAutSub t L := by
  rcases hB.hTperm t⁻¹ (T.inv_mem hB.htT) with h | h
  · exfalso
    apply hB.htn
    have h1 : conjAutSub t (conjAutSub t⁻¹ L) = conjAutSub t L := by rw [h]
    rw [← conjAutSub_mul, mul_inv_cancel] at h1
    have h2 : conjAutSub 1 L = L := by
      ext x
      simp [mem_conjAutSub]
    rw [h2] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm
  · exact h

theorem D321Base.swapV_fix (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    ∀ v ∈ V.map t.toMonoidHom, ∀ g ∈ conjAutSub t⁻¹ (conjAutSub t L), g v = v := by
  rintro _ ⟨v, hv, rfl⟩ g hg
  rw [conjAutSub_inv_conjAutSub] at hg
  have h1 : t⁻¹ * g * t ∈ conjAutSub t L := by
    rw [← hB.conjAutSub_inv, mem_conjAutSub]
    have e : t⁻¹⁻¹ * (t⁻¹ * g * t) * t⁻¹ = g := by group
    rw [e]
    exact hg
  have h2 := hVt v hv _ h1
  have h3 : g (t v) = t ((t⁻¹ * g * t) v) := by simp [MulAut.mul_apply]
  show g (t v) = t v
  rw [h3, h2]

omit [Finite W] in
theorem commSub_map_conjAutSub (t : MulAut W) (U : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (U.map t.toMonoidHom) (conjAutSub t X) = (commSub U X).map t.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, MulAut.conj_apply]
  · rintro ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, t w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, MulAut.conj_apply]

theorem D321Base.swapV_caseIIa (hB : D321Base M Mp T L V t)
    (hUV : commSub (orbSup T V) L = V) :
    commSub (orbSup T (V.map t.toMonoidHom)) (conjAutSub t L) = V.map t.toMonoidHom := by
  have h1 : (orbSup T V).map t.toMonoidHom = orbSup T V := by
    refine le_antisymm (map_orbSup_le hB.htT) fun w hw => ?_
    refine ⟨t⁻¹ w, mem_orbSup_of_mem_map (T.inv_mem hB.htT) hw, ?_⟩
    simp
  rw [orbSup_map_of_mem hB.htT, ← h1, commSub_map_conjAutSub, hUV]

end SwapV



section SideFacts

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

structure SideFL (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (X : Subgroup (MulAut W)) (I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) : Prop where
  le : X ≤ M
  simple : IsSimpleGroup ↥(X.subgroupOf M)
  a38 : A38Types ↥(X.subgroupOf M)
  inv : letI := qAct hMp;
    ∀ x ∈ X.subgroupOf M, ∀ y ∈ tilde Mp ⊤ (commV X), x • y ∈ tilde Mp ⊤ (commV X)
  ss : letI := qAct hMp; tilde Mp ⊤ (commV X) ≤ ⨆ (J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    (_ : J ≤ tilde Mp ⊤ (commV X) ∧ XMod.IsIrr ↥(X.subgroupOf M) J), J
  rk_eq : letI := qAct hMp; ∀ J ≤ tilde Mp ⊤ (commV X), XMod.IsIrr ↥(X.subgroupOf M) J →
    rk ↥J = rk ↥I
  moved : letI := qAct hMp; ∀ J ≤ tilde Mp ⊤ (commV X), XMod.IsIrr ↥(X.subgroupOf M) J →
    ∃ x ∈ X.subgroupOf M, ∃ j ∈ J, x • j ≠ j
  irr : letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) I
  le_Y : I ≤ tilde Mp ⊤ (commV X)
  two_le : 2 * rk ↥I ≤ rk ↥(tilde Mp ⊤ (commV X))

variable {T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

omit [Finite W] in
theorem isIrr_smul_of_mem_normalizer (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    {X : Subgroup (MulAut W)} {g : ↥M} (hg : (g : MulAut W) ∈ Subgroup.normalizer (X : Set _))
    {I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hI : letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) I) :
    letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) (g • I) := by
  let _i := qAct hMp
  let G' : Subgroup ↥M := (Subgroup.normalizer (X : Set (MulAut W))).subgroupOf M
  have hN : XMod.Normalizes ↥(X.subgroupOf M) ↥G' (W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    intro s a
    refine ⟨⟨s * a * s⁻¹, Subgroup.mem_subgroupOf.2 ?_⟩, fun q => ?_⟩
    · have hs : ((s : ↥M) : MulAut W) ∈ Subgroup.normalizer (X : Set (MulAut W)) :=
        Subgroup.mem_subgroupOf.1 s.2
      exact (Subgroup.mem_normalizer_iff.1 hs _).1 (Subgroup.mem_subgroupOf.1 a.2)
    · change (s : ↥M) • ((a : ↥M) • q) = ((s : ↥M) * a * (s : ↥M)⁻¹) • ((s : ↥M) • q)
      rw [smul_smul, smul_smul, inv_mul_cancel_right]
  exact isIrr_smul hN ⟨g, Subgroup.mem_subgroupOf.2 hg⟩ hI

theorem sideFL_of (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (htop : orbSup T V ≠ ⊤) :
    SideFL hB.hD.hyp.Mp_normal L (tilde Mp ⊤ V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hLM := hB.L_le
  have := hB.hsimp
  set Y := tilde Mp ⊤ (commV L) with hY
  set Vq := tilde Mp ⊤ V with hVq
  have hirr := hB.irr_L hVt
  let ι := {g : ↥M // (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))}
  let S : ι → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)) := fun g => (g : ↥M) • Vq
  have hYS : tilde Mp ⊤ (commV L) = ⨆ g : ι, S g := by
    rw [hB.tildeU_eq_iSup hVt, iSup_subtype']
  have hS : ∀ g : ι, XMod.IsIrr ↥(L.subgroupOf M) (S g) := fun g =>
    isIrr_smul_of_mem_normalizer hB.hD.hyp.Mp_normal g.2 hirr
  have hSrk : ∀ g : ι, rk ↥(S g) = rk ↥Vq := fun g => rk_smul _ _
  refine ⟨hLM, (Subgroup.subgroupOfEquivOfLe hLM).isSimpleGroup,
    a38Types_congr (Subgroup.subgroupOfEquivOfLe hLM).symm hB.hA38, ?_, ?_, ?_, ?_, hirr,
    hB.tildeV_le_tildeU hVt, ?_⟩
  · rintro x hx _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hx)) u hu,
      rfl⟩
  · conv_lhs => rw [hYS]
    conv_rhs => rw [hYS]
    exact le_iSup_isIrr_of_iSup hS
  · intro J hJY hJ
    rw [hYS] at hJY
    exact rk_eq_of_le_iSup hS hSrk hJ hJY
  · intro J hJY hJ
    by_contra hcon
    push Not at hcon
    apply hJ.2.1.ne'
    rw [eq_bot_iff, ← hB.fixed_eq_bot]
    intro j hj
    refine XMod.mem_fixed.2 ⟨trivial, fun m => ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hB.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 m.2)
    have hbj : (⟨b, hB.Lt_le hb⟩ : ↥M) • j = j :=
      (XMod.mem_fixed.1 (hB.tildeU_le_fixed hVt (hJY hj))).2
        ⟨⟨b, hB.Lt_le hb⟩, Subgroup.mem_subgroupOf.2 hb⟩
    have haj : (⟨a, hLM ha⟩ : ↥M) • j = j := hcon _ (Subgroup.mem_subgroupOf.2 ha) j hj
    have hm : ((m : ↥M)) = (⟨a, hLM ha⟩ : ↥M) * ⟨b, hB.Lt_le hb⟩ := Subtype.ext hab
    show ((m : ↥M)) • j = j
    rw [hm, mul_smul, hbj, haj]
  ·
    obtain ⟨g, hg⟩ : ∃ g : ι, ¬ S g ≤ Vq := by
      by_contra hcon
      push Not at hcon
      apply hB.not_le_orbSup htop
      intro u hu
      have h1 : QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) u ∈ Vq := by
        have : QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) u ∈ tilde Mp ⊤ (commV L) :=
          ⟨u, hu, rfl⟩
        rw [hYS] at this
        exact (iSup_le hcon) this
      obtain ⟨v, hv, hvu⟩ := h1
      have hz : v⁻¹ * u ∈ fixV Mp := by
        rw [← modFix_top_eq, ← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) (v⁻¹ * u) = 1
        rw [map_mul, map_inv, hvu, inv_mul_cancel]
      have : u = v * (v⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (le_orbSup T V hv) hz
    have hinf : S g ⊓ Vq = ⊥ := by
      rcases (hS g).2.2 _ ((hS g).1.inf hirr.1) bot_le inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) hg
    have h1 := rk_sup_add_rk_inf (S g) Vq
    rw [hinf, rk_bot, hSrk] at h1
    have h2 : S g ⊔ Vq ≤ tilde Mp ⊤ (commV L) := by
      rw [hYS]
      exact sup_le (le_iSup S g) (hYS ▸ hB.tildeV_le_tildeU hVt)
    have := rk_mono h2
    omega

end SideFacts

section FLSide

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem fl_side (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) {X : Subgroup (MulAut W)}
    {I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))} (hF : SideFL hS.hD.hyp.Mp_normal X I)
    {B : Subgroup (MulAut W)} (hBA : B ≤ A) (hBX : B ≤ Subgroup.normalizer (X : Set (MulAut W)))
    {q₀ : ℚ} (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥(X.subgroupOf M))) :
    letI := qAct hS.hD.hyp.Mp_normal
    q₀ * (mRel (B.subgroupOf M) (X.subgroupOf M) : ℚ) * rk ↥(tilde Mp ⊤ (commV X)) ≤
      rk ↥I * nB (B.subgroupOf M) (tilde Mp ⊤ (commV X)) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hAM := hS.A_le
  have hBM : B ≤ M := hBA.trans hAM
  obtain ⟨hAc, hA2⟩ := hS.elemAb
  have hPc : ∀ a ∈ B.subgroupOf M, ∀ b ∈ B.subgroupOf M, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hAc _ (hBA (Subgroup.mem_subgroupOf.1 ha)) _ (hBA (Subgroup.mem_subgroupOf.1 hb)))
  have hP2 : ∀ a ∈ B.subgroupOf M, a ^ 2 = 1 := fun a ha =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hA2 _ (hBA (Subgroup.mem_subgroupOf.1 ha)))
  have hPX : ∀ a ∈ B.subgroupOf M, ∀ x ∈ X.subgroupOf M, a * x * a⁻¹ ∈ X.subgroupOf M :=
    fun a ha x hx => Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hBX (Subgroup.mem_subgroupOf.1 ha)) _).1
        (Subgroup.mem_subgroupOf.1 hx))
  have hYP : ∀ a ∈ B.subgroupOf M, ∀ y ∈ tilde Mp ⊤ (commV X), a • y ∈ tilde Mp ⊤ (commV X) := by
    rintro a ha _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (hBX (Subgroup.mem_subgroupOf.1 ha)) u hu, rfl⟩
  have hcub := isCubicOn_qAct hS.hD.hyp.Mp_normal
    (le_bot_iff.1 ((commSeries_mono hBA 3).trans hS.cubic.le)) (tilde Mp ⊤ (commV X))
  exact nB_ge_of_a38 hA21 hB42 h9 hS.hD.hyp.qsqtk hS.quot_sq hF.simple hF.a38 hPc hP2 hPX hYP
    hF.inv hcub hF.ss hF.rk_eq hF.moved hq₀

theorem le_normalizer_Lt (hS : D321Sit M Mp T L V t A r)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    A ≤ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
  fun _ ha => mem_normalizer_iff_conjAutSub.2
    (hS.conj_Lt_of_mem_normalizer (hS.A_le ha) (hAL ha))

theorem rk_le_mRel_add (hS : D321Sit M Mp T L V t A r)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) :
    rk ↥A ≤ mRel (A.subgroupOf M) (L.subgroupOf M) +
      mRel (A.subgroupOf M) ((conjAutSub t L).subgroupOf M) := by
  set P := A.subgroupOf M with hP
  set C₁ := P ⊓ Subgroup.centralizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) with hC₁
  set C₂ := P ⊓ Subgroup.centralizer (((conjAutSub t L).subgroupOf M : Subgroup ↥M) : Set ↥M)
    with hC₂
  have hrkP : rk ↥P = rk ↥A := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.A_le).toEquiv]
  have hdisj : C₁ ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have haA : (a : MulAut W) ∈ A := Subgroup.mem_subgroupOf.1 ha.1.1
    have hcL : ∀ x ∈ L, (a : MulAut W) * x = x * a := fun x hx => by
      have := Subgroup.mem_centralizer_iff.1 ha.1.2 ⟨x, hS.L_le hx⟩
        (Subgroup.mem_subgroupOf.2 hx)
      exact (congrArg Subtype.val this).symm
    have hcLt : ∀ x ∈ conjAutSub t L, (a : MulAut W) * x = x * a := fun x hx => by
      have := Subgroup.mem_centralizer_iff.1 ha.2.2 ⟨x, hS.Lt_le hx⟩
        (Subgroup.mem_subgroupOf.2 hx)
      exact (congrArg Subtype.val this).symm
    have hcMp : (a : MulAut W) ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
      refine ⟨haA, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := hS.exists_mul_of_mem_Mp hx
      rw [mul_assoc, ← hcLt c hc, ← mul_assoc, ← hcL b hb, mul_assoc]
    rw [hAC, Subgroup.mem_bot] at hcMp
    rw [Subgroup.mem_bot]
    exact Subtype.ext hcMp
  have h1 : rk ↥(C₁ ⊔ C₂) + rk ↥(C₁ ⊓ C₂) = rk ↥C₁ + rk ↥C₂ :=
    B2F.rk_sup_add_rk_inf_of_commute fun a ha b hb => by
      have hab := hS.elemAb.1 _ (Subgroup.mem_subgroupOf.1 ha.1) _
        (Subgroup.mem_subgroupOf.1 hb.1)
      exact Subtype.ext hab
  have h2 : rk ↥(C₁ ⊔ C₂) ≤ rk ↥P := rk_mono (sup_le inf_le_left inf_le_left)
  have h3 : rk ↥C₁ ≤ rk ↥P := rk_mono inf_le_left
  have h4 : rk ↥C₂ ≤ rk ↥P := rk_mono inf_le_left
  rw [hdisj, rk_bot] at h1
  show rk ↥A ≤ (rk ↥P - rk ↥C₁) + (rk ↥P - rk ↥C₂)
  clear_value C₁ C₂ P
  omega

theorem isPSL_iff_subgroupOf (hS : D321Sit M Mp T L V t A r) {n p f : ℕ} :
    (IsPSL n p f ↥(L.subgroupOf M) ↔ IsPSL n p f ↥L) ∧
      (IsPSL n p f ↥((conjAutSub t L).subgroupOf M) ↔ IsPSL n p f ↥L) := by
  have e₁ := Subgroup.subgroupOfEquivOfLe hS.L_le
  have e₂ := (Subgroup.subgroupOfEquivOfLe hS.Lt_le).trans
    (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm
  exact ⟨⟨fun h => SmithD37.isPSL_transfer e₁.symm h, fun h => SmithD37.isPSL_transfer e₁ h⟩,
    ⟨fun h => SmithD37.isPSL_transfer e₂.symm h, fun h => SmithD37.isPSL_transfer e₂ h⟩⟩

theorem nonswap_bound (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {q₀ : ℚ}
    (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥L)) :
    letI := qAct hS.hD.hyp.Mp_normal
    q₀ * rk ↥(tilde Mp ⊤ (commV L)) ≤ 2 * rk ↥(tilde Mp ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hF' := sideFL_of hS.swapV.toD321Base (D321Base.swapV_fix hS.toD321Base hVt) hS.swapV.htop
  have hq₁ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥(L.subgroupOf M)) := by
    rcases hq₀ with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun h => h2 ((isPSL_iff_subgroupOf hS).1.1 h)⟩
  have hq₂ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥((conjAutSub t L).subgroupOf M)) := by
    rcases hq₀ with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun h => h2 ((isPSL_iff_subgroupOf hS).2.1 h)⟩
  have h₁ := fl_side hA21 hB42 h9 hS hF le_rfl hAL hq₁
  have h₂ := fl_side hA21 hB42 h9 hS hF' le_rfl (le_normalizer_Lt hS hAL) hq₂
  have hm : rk ↥(tilde Mp ⊤ (commV (conjAutSub t L))) = rk ↥(tilde Mp ⊤ (commV L)) := by
    rw [← hS.smul_tildeU, rk_smul]
  have hd : rk ↥(tilde Mp ⊤ (V.map t.toMonoidHom)) = rk ↥(tilde Mp ⊤ V) := by
    rw [← smul_eq_map, ← smul_tildeQ hS.hD.hyp.Mp_normal ⟨t, hS.t_mem⟩, rk_smul]
  rw [hm, hd] at h₂
  have hsum : nB (A.subgroupOf M) (tilde Mp ⊤ (commV L)) +
      nB (A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L))) ≤ 2 * rk ↥A := by
    have hinv₁ : XMod.IsInv ↥(A.subgroupOf M) (tilde Mp ⊤ (commV L)) := by
      rintro ⟨a, ha⟩ _ ⟨u, hu, rfl⟩
      exact ⟨_, B15P4.map_commV_mem (hAL (Subgroup.mem_subgroupOf.1 ha)) u hu, rfl⟩
    have hinv₂ : XMod.IsInv ↥(A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L))) := by
      rintro ⟨a, ha⟩ _ ⟨u, hu, rfl⟩
      exact ⟨_, B15P4.map_commV_mem (le_normalizer_Lt hS hAL (Subgroup.mem_subgroupOf.1 ha)) u
        hu, rfl⟩
    have hd' : tilde Mp ⊤ (commV L) ⊓ tilde Mp ⊤ (commV (conjAutSub t L)) = ⊥ := by
      rw [← hS.smul_tildeU]
      exact hS.inf_tildeU hVt
    have hs' : tilde Mp ⊤ (commV L) ⊔ tilde Mp ⊤ (commV (conjAutSub t L)) = ⊤ := by
      rw [← hS.smul_tildeU]
      exact hS.sup_tildeU
    have := nB_sup_of_disjoint (A.subgroupOf M) hinv₁ hinv₂ hd'
    rw [hs'] at this
    have h2 := hS.nB_le
    omega
  have hrel := rk_le_mRel_add hS hAC
  have hpos := hS.rk_pos
  have hq0 : 0 ≤ q₀ := by rcases hq₀ with h | ⟨h, -⟩ <;> rw [h] <;> norm_num
  set m := rk ↥(tilde Mp ⊤ (commV L))
  set d := rk ↥(tilde Mp ⊤ V)
  set a := mRel (A.subgroupOf M) (L.subgroupOf M)
  set a' := mRel (A.subgroupOf M) ((conjAutSub t L).subgroupOf M)
  set n₁ := nB (A.subgroupOf M) (tilde Mp ⊤ (commV L))
  set n₂ := nB (A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L)))
  have e1 : (q₀ * m) * (rk ↥A : ℚ) ≤ (2 * d) * (rk ↥A : ℚ) := by
    have hsumQ : ((n₁ : ℚ) + n₂) ≤ 2 * (rk ↥A : ℚ) := by exact_mod_cast hsum
    have hrelQ : (rk ↥A : ℚ) ≤ (a : ℚ) + a' := by exact_mod_cast hrel
    calc (q₀ * m) * (rk ↥A : ℚ) ≤ (q₀ * m) * ((a : ℚ) + a') :=
          mul_le_mul_of_nonneg_left hrelQ (mul_nonneg hq0 (Nat.cast_nonneg m))
      _ = q₀ * a * m + q₀ * a' * m := by ring
      _ ≤ d * n₁ + d * n₂ := add_le_add h₁ h₂
      _ = d * ((n₁ : ℚ) + n₂) := by ring
      _ ≤ d * (2 * (rk ↥A : ℚ)) := mul_le_mul_of_nonneg_left hsumQ (Nat.cast_nonneg d)
      _ = (2 * d) * (rk ↥A : ℚ) := by ring
  have hposQ : (0 : ℚ) < rk ↥A := by exact_mod_cast hpos
  exact le_of_mul_le_mul_right e1 hposQ

theorem rk_eq_add_one_of_swap (hS : D321Sit M Mp T L V t A r) {a₀ : MulAut W} (ha₀ : a₀ ∈ A)
    (ha₀L : a₀ ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    rk ↥A = rk ↥(A ⊓ Subgroup.normalizer (L : Set (MulAut W))) + 1 := by
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have hidx : ((A ⊓ N).subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a₀, ha₀⟩, fun b => ?_⟩
    have hbM : (b : MulAut W) ∈ M := hS.A_le b.2
    have ha₀M : a₀ ∈ M := hS.A_le ha₀
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
    by_cases hb : (b : MulAut W) ∈ N
    · refine Or.inr ⟨⟨b.2, hb⟩, fun h => ha₀L ?_⟩
      have := N.mul_mem (N.inv_mem hb) h.2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · refine Or.inl ⟨⟨A.mul_mem b.2 ha₀, ?_⟩, fun h => hb h.2⟩
      have h1 := hS.inv_mul_mem_normalizer (M.inv_mem hbM) ha₀M
        (fun h => hb (by simpa using N.inv_mem h)) ha₀L
      rwa [inv_inv] at h1
  have hcard := (A ⊓ N).subgroupOf A |>.card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  unfold rk
  rw [← hcard, padicValNat.mul Nat.card_pos.ne' (by norm_num), padicValNat_self]

theorem le_normalizer_of_count (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) :
    A ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  by_contra hnot
  obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hnot
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have hAM := hS.A_le
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  set Y := tilde Mp ⊤ (commV L) with hY
  set d := rk ↥(tilde Mp ⊤ V) with hd
  have hd3 : 3 ≤ d := three_le_rk_of_a38 hS.quot_sq hF.simple hF.a38
    (fun g hg j hj => hF.irr.1 ⟨g, hg⟩ j hj) (hF.moved _ hF.le_Y hF.irr)
  set a₀' : ↥M := ⟨a₀, hAM ha₀⟩ with ha₀'
  have hswap : a₀' • Y = tilde Mp ⊤ (commV (conjAutSub t L)) := by
    rw [hY, smul_tildeQ, smul_eq_map, map_commV_conjAutSub, (hS.conj_swap (hAM ha₀) ha₀L).1]
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hS.elemAb.1 _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
  have ha2 : a₀' ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hS.elemAb.2 a₀ ha₀)
  have hA₀A : (A ⊓ N).subgroupOf M ≤ A.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx).1
  have hsplit : ∀ x ∈ A.subgroupOf M, x ∈ (A ⊓ N).subgroupOf M ∨
      a₀'⁻¹ * x ∈ (A ⊓ N).subgroupOf M := by
    intro x hx
    have hxA := Subgroup.mem_subgroupOf.1 hx
    by_cases hxN : (x : MulAut W) ∈ N
    · exact Or.inl (Subgroup.mem_subgroupOf.2 ⟨hxA, hxN⟩)
    · refine Or.inr (Subgroup.mem_subgroupOf.2 ⟨A.mul_mem (A.inv_mem ha₀) hxA, ?_⟩)
      exact hS.inv_mul_mem_normalizer (hAM ha₀) x.2 ha₀L hxN
  have hP' : XMod.IsInv ↥((A ⊓ N).subgroupOf M) Y := by
    rintro ⟨a, ha⟩ _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (Subgroup.mem_subgroupOf.1 ha).2 u hu, rfl⟩
  have hdisj : Y ⊓ a₀' • Y = ⊥ := by
    rw [hswap, ← hS.smul_tildeU]
    exact hS.inf_tildeU hVt
  have hidx := nB_index_two (A := A.subgroupOf M) (Subgroup.mem_subgroupOf.2 ha₀) ha2 hAc hA₀A
    hsplit hP' hdisj
  have htop' : Y ⊔ a₀' • Y = ⊤ := by
    rw [hswap, ← hS.smul_tildeU]
    exact hS.sup_tildeU
  rw [htop'] at hidx
  have hnB := hS.nB_le
  have hcent : ∀ a ∈ A ⊓ N, (∀ x ∈ L, a * x = x * a) → a = 1 := by
    intro a ha hcL
    have haA : a ∈ A := ha.1
    have hca : a * a₀ = a₀ * a := hS.elemAb.1 _ haA _ ha₀
    have hcLt : ∀ y ∈ conjAutSub t L, a * y = y * a := by
      intro y hy
      rw [← (hS.conj_swap (hAM ha₀) ha₀L).1, mem_conjAutSub] at hy
      have h1 : Commute a (a₀⁻¹ * y * a₀) := hcL _ hy
      have hca' : Commute a a₀ := hca
      have h2 : Commute a (a₀ * (a₀⁻¹ * y * a₀) * a₀⁻¹) :=
        (hca'.mul_right h1).mul_right hca'.inv_right
      have e : a₀ * (a₀⁻¹ * y * a₀) * a₀⁻¹ = y := by group
      rw [e] at h2
      exact h2
    have hcMp : a ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
      refine ⟨haA, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := hS.exists_mul_of_mem_Mp hx
      rw [mul_assoc, ← hcLt c hc, ← mul_assoc, ← hcL b hb, mul_assoc]
    rw [hAC, Subgroup.mem_bot] at hcMp
    exact hcMp
  have hrel : mRel ((A ⊓ N).subgroupOf M) (L.subgroupOf M) = rk ↥(A ⊓ N) := by
    have hbot : (A ⊓ N).subgroupOf M ⊓
        Subgroup.centralizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have hcL : ∀ x ∈ L, (a : MulAut W) * x = x * a := fun x hx => by
        have := Subgroup.mem_centralizer_iff.1 ha.2 ⟨x, hS.L_le hx⟩
          (Subgroup.mem_subgroupOf.2 hx)
        exact (congrArg Subtype.val this).symm
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hcent _ (Subgroup.mem_subgroupOf.1 ha.1) hcL)
    unfold mRel
    rw [hbot, rk_bot, Nat.sub_zero]
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAM)).toEquiv]
  have hrkA : rk ↥A = rk ↥(A ⊓ N) + 1 := rk_eq_add_one_of_swap hS ha₀ ha₀L
  have hm2 : 2 * d ≤ rk ↥Y := hF.two_le
  have hmain : ∀ q₀ : ℚ, 0 < q₀ →
      q₀ * (rk ↥(A ⊓ N) : ℚ) * rk ↥Y ≤ d * nB ((A ⊓ N).subgroupOf M) Y →
      2 * q₀ * (rk ↥(A ⊓ N) : ℚ) ≤ nB ((A ⊓ N).subgroupOf M) Y := by
    intro q₀ hq hfl
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hm2Q : (2 : ℚ) * d ≤ rk ↥Y := by exact_mod_cast hm2
    have h1 : q₀ * (rk ↥(A ⊓ N) : ℚ) * (2 * d) ≤ q₀ * (rk ↥(A ⊓ N) : ℚ) * rk ↥Y :=
      mul_le_mul_of_nonneg_left hm2Q (mul_nonneg hq.le (Nat.cast_nonneg _))
    have h2 : (2 * q₀ * (rk ↥(A ⊓ N) : ℚ)) * d ≤ (nB ((A ⊓ N).subgroupOf M) Y : ℚ) * d := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hdpos
  have hsum : rk ↥Y + nB ((A ⊓ N).subgroupOf M) Y ≤ 2 * (rk ↥(A ⊓ N) + 1) := by
    rw [← hidx, ← hrkA]
    exact hnB
  by_cases hL3 : IsPSL 3 2 1 ↥L
  · have hfl := fl_side hA21 hB42 h9 hS hF (inf_le_left : A ⊓ N ≤ A) inf_le_right
      (Or.inl rfl : (1 / 2 : ℚ) = 1 / 2 ∨ _)
    rw [hrel] at hfl
    have h1 := hmain _ (by norm_num) hfl
    have hr3 : rk ↥(A ⊓ N) ≤ 3 := rk_le_three_of_isPSL32 hL3
      (fun e he x hx => (Subgroup.mem_normalizer_iff.1 he.2 x).1 hx)
      (fun a ha b hb => hS.elemAb.1 _ ha.1 _ hb.1) (fun e he => hS.elemAb.2 e he.1)
      (fun e he hc => hcent e he hc)
    have h2 : ((rk ↥(A ⊓ N) : ℕ) : ℚ) ≤ nB ((A ⊓ N).subgroupOf M) Y := by linarith
    have h3' : rk ↥(A ⊓ N) ≤ nB ((A ⊓ N).subgroupOf M) Y := by exact_mod_cast h2
    clear_value d Y N
    omega
  · have hfl := fl_side hA21 hB42 h9 hS hF (inf_le_left : A ⊓ N ≤ A) inf_le_right
      (Or.inr ⟨rfl, fun h' => hL3 ((isPSL_iff_subgroupOf hS).1.1 h')⟩ : (1 : ℚ) = 1 / 2 ∨ _)
    rw [hrel] at hfl
    have h1 := hmain _ (by norm_num) hfl
    have h2 : (2 * (rk ↥(A ⊓ N) : ℕ) : ℚ) ≤ nB ((A ⊓ N).subgroupOf M) Y := by linarith
    have h3' : 2 * rk ↥(A ⊓ N) ≤ nB ((A ⊓ N).subgroupOf M) Y := by exact_mod_cast h2
    clear_value d Y N
    omega

end FLSide



section HomogSit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem map_V_of_mem_T0 (hU : commSub (orbSup T V) L = V) {s : MulAut W} (hsT : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) : V.map s.toMonoidHom = V := by
  have h1 : (orbSup T V).map s.toMonoidHom = orbSup T V := by
    refine le_antisymm (map_orbSup_le hsT) fun w hw => ?_
    refine ⟨s⁻¹ w, mem_orbSup_of_mem_map (T.inv_mem hsT) hw, ?_⟩
    simp
  have h2 : conjAutSub s L = L := mem_normalizer_iff_conjAutSub.1 hsN
  calc V.map s.toMonoidHom = (commSub (orbSup T V) L).map s.toMonoidHom := by rw [hU]
    _ = commSub ((orbSup T V).map s.toMonoidHom) (conjAutSub s L) :=
        (commSub_map_conjAutSub s _ _).symm
    _ = V := by rw [h1, h2, hU]

theorem smul_tildeV_of_mem_T0 (hB : D321Base M Mp T L V t) (hU : commSub (orbSup T V) L = V)
    (p : ↥M) (hp : p ∈ (T ⊓ Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M) :
    letI := qAct hB.hD.hyp.Mp_normal
    p • tilde Mp ⊤ V = tilde Mp ⊤ V := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hp' := Subgroup.mem_subgroupOf.1 hp
  rw [smul_tildeQ, smul_eq_map, map_V_of_mem_T0 hU hp'.1 hp'.2]

theorem odd_index_T0 (hB : D321Base M Mp T L V t) :
    Odd (((T ⊓ Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M).subgroupOf
      ((Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M)).index := by
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have h := hB.sylow_T0.2.2
  have e : (((T ⊓ N).subgroupOf M).subgroupOf (N.subgroupOf M)).index =
      (T ⊓ N).relIndex (M ⊓ N) := by
    rw [← Subgroup.inf_subgroupOf_left N M, ← Subgroup.relIndex_subgroupOf inf_le_left]
    rfl
  rw [e]
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)

theorem isPGroup_T0 (hB : D321Base M Mp T L V t) :
    IsPGroup 2 ↥((T ⊓ Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M) :=
  hB.sylow_T0.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hB.T_le)).symm

omit [Finite W] in
theorem normalizes_Λ (L : Subgroup (MulAut W)) :
    ∀ g ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M, ∀ l ∈ L.subgroupOf M,
      g * l * g⁻¹ ∈ L.subgroupOf M := fun _ hg _ hl =>
  Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (Subgroup.mem_subgroupOf.1 hg) _).1
    (Subgroup.mem_subgroupOf.1 hl))

theorem tildeU_eq_iSup' (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) =
      ⨆ g ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M, g • tilde Mp ⊤ V :=
  hB.tildeU_eq_iSup hVt

theorem iso_of_rk_le_two (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V)
    (hrk : letI := qAct hB.hD.hyp.Mp_normal;
      rk ↥(tilde Mp ⊤ (commV L)) ≤ 2 * rk ↥(tilde Mp ⊤ V)) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∀ g ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M,
      XMod.Iso ↥(L.subgroupOf M) (g • tilde Mp ⊤ V) (tilde Mp ⊤ V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [tildeU_eq_iSup' hB hVt] at hrk
  exact iso_of_odd_index hB.quot_sq (normalizes_Λ L) (odd_index_T0 hB) (hB.irr_L hVt)
    (smul_tildeV_of_mem_T0 hB hU) hrk

theorem factorization_of_out_two (hB : D321Base M Mp T L V t)
    (hout : ∀ g₁ ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M,
      ∀ g₂ ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M,
      (¬ ∃ l ∈ L.subgroupOf M, ∀ x ∈ L.subgroupOf M, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ L.subgroupOf M, ∀ x ∈ L.subgroupOf M, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ L.subgroupOf M, ∀ x ∈ L.subgroupOf M,
        (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹) :
    ∀ g ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M, ∃ l ∈ L.subgroupOf M,
      ∃ c ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M,
        (∀ x ∈ L.subgroupOf M, c * x = x * c) ∧
        ∃ τ ∈ (T ⊓ Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M, g = l * c * τ :=
  exists_mul_mul_of_out_two
    (fun _ hl => Subgroup.mem_subgroupOf.2 (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hl)))
    (fun _ hτ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hτ).2) (odd_index_T0 hB) hout

end HomogSit

section OutTwo

variable {Γ : Type} [Group Γ]

theorem out_two_of_cases {G X : Subgroup Γ}
    (hX : IsPSL 3 2 1 ↥X ∨ Nonempty (↥X ≃* alternatingGroup (Fin 5)))
    (hGX : ∀ g ∈ G, ∀ l ∈ X, g * l * g⁻¹ ∈ X) :
    ∀ g₁ ∈ G, ∀ g₂ ∈ G, (¬ ∃ l ∈ X, ∀ x ∈ X, g₁ * x * g₁⁻¹ = l * x * l⁻¹) →
      (¬ ∃ l ∈ X, ∀ x ∈ X, g₂ * x * g₂⁻¹ = l * x * l⁻¹) →
      ∃ l ∈ X, ∀ x ∈ X, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = l * x * l⁻¹ := by
  rcases hX with h | h
  · exact out_two_of_isPSL32 h hGX
  · exact out_two_of_alt5 h hGX

theorem cases_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPSL 3 2 1 Y ∨ Nonempty (Y ≃* alternatingGroup (Fin 5))) :
    IsPSL 3 2 1 X ∨ Nonempty (X ≃* alternatingGroup (Fin 5)) :=
  h.imp (SmithD37.isPSL_transfer e) fun ⟨f⟩ => ⟨e.trans f⟩

end OutTwo

section KplusSit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem kplus_of (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hU : commSub (orbSup T V) L = V)
    (hLo : IsPSL 3 2 1 ↥L ∨ Nonempty (↥L ≃* alternatingGroup (Fin 5))) {k : ℕ}
    (hY : letI := qAct hS.hD.hyp.Mp_normal;
      IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) k) :
    letI := qAct hS.hD.hyp.Mp_normal
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card ↥L ∧ ∃ (y : MulAut W) (hy : y ∈ M),
      (∀ l ∈ L, y * l = l * y) ∧
      (∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy⟩ : ↥M) ^ p • q = q) ∧
      (∃ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy⟩ : ↥M) • q ≠ q) ∧
      ∃ c' < k, Nat.card (Module.End ↥(XMod.opRing ↥(L.subgroupOf M)
          (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod (hS.irr_L hVt).1)) ^ k ≡
        Nat.card (Module.End ↥(XMod.opRing ↥(L.subgroupOf M)
          (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod (hS.irr_L hVt).1)) ^ c' [MOD p] := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  set Λ := L.subgroupOf M with hΛ
  set Y := tilde Mp ⊤ (commV L) with hYdef
  set Vq := tilde Mp ⊤ V with hVq
  have hLM := hS.L_le
  have hI := hS.irr_L hVt
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hLoΛ : IsPSL 3 2 1 ↥Λ ∨ Nonempty (↥Λ ≃* alternatingGroup (Fin 5)) :=
    cases_congr (Subgroup.subgroupOfEquivOfLe hLM) hLo
  have hfac := factorization_of_out_two hS.toD321Base (out_two_of_cases hLoΛ (normalizes_Λ L))
  have hYG : ∀ g ∈ N.subgroupOf M, ∀ q ∈ Y, g • q ∈ Y := by
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (Subgroup.mem_subgroupOf.1 hg) u hu, rfl⟩
  have hd0 : rk ↥Vq ≠ 0 := fun h => hI.2.1.ne' ((rk_eq_zero_iff hS.quot_sq).1 h)
  have hne : ¬ Y ≤ Vq := by
    intro hle
    have h1 := rk_mono hle
    have h2 : 2 * rk ↥Vq ≤ rk ↥Y := hF.two_le
    omega
  have hPG : (T ⊓ N).subgroupOf M ≤ N.subgroupOf M := fun τ hτ =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hτ).2
  obtain ⟨p, hp, hp2, y, hyG, hyΛ, ⟨n, hyn⟩, hyp, hymove⟩ := exists_pElement_of_factorization
    (normalizes_Λ L) hPG (isPGroup_T0 hS.toD321Base) (odd_index_T0 hS.toD321Base) hYG
    (hS.tildeV_le_tildeU hVt) (fun _ hl => smul_eq_of_isInv hI.1 hl)
    (smul_tildeV_of_mem_T0 hS.toD321Base hU) hfac
    (tildeU_eq_iSup' hS.toD321Base hVt).le hne
  have hyL : ∀ l ∈ L, (y : MulAut W) * l = l * y := fun l hl =>
    congrArg Subtype.val (hyΛ ⟨l, hLM hl⟩ (Subgroup.mem_subgroupOf.2 hl))
  have hyn' : (y : MulAut W) ^ (p ^ n) = 1 := by
    rw [← Subgroup.coe_pow, hyn]
    rfl
  have hpL : ¬ p ∣ Nat.card ↥L := by
    intro hpL
    have hyNt : (y : MulAut W) ∈ Subgroup.normalizer
        ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
      mem_normalizer_iff_conjAutSub.2
        (hS.conj_Lt_of_mem_normalizer y.2 (Subgroup.mem_subgroupOf.1 hyG))
    have hLot := cases_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm hLo
    have houtt := out_two_of_cases hLot (G := Subgroup.normalizer
        ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)))
      (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 hg l).1 hl)
    have hinner := inner_of_odd_of_out_two houtt hyNt (hp.odd_of_ne_two hp2).pow hyn'
    have hyLt := hS.mem_Lt_of_inner hp hp2 hpL y.2 hyL hyn' hinner
    obtain ⟨q, hq, hqy⟩ := hymove
    exact hqy ((XMod.mem_fixed.1 (hS.tildeU_le_fixed hVt hq)).2
      ⟨y, Subgroup.mem_subgroupOf.2 hyLt⟩)
  have hyΛ' : ∀ l ∈ Λ, l * y = y * l := fun l hl => (hyΛ l hl).symm
  have hYy : ∀ q ∈ Y, y • q ∈ Y := hYG y hyG
  set F := Y ⊓ XMod.fixed ↥(Subgroup.zpowers y) ⊤ with hFdef
  have hFinv : XMod.IsInv ↥Λ F := by
    rintro ⟨l, hl⟩ q ⟨hqY, hqF⟩
    refine ⟨hY.1 ⟨l, hl⟩ q hqY, (mem_fixed_zpowers_iff (b := y)).2 ?_⟩
    have h1 := (mem_fixed_zpowers_iff (b := y)).1 hqF
    show y • (l • q) = l • q
    rw [smul_smul, hyΛ l hl, mul_smul, h1]
  obtain ⟨c', hc'⟩ := IsotypicOfLength.exists_of_le hS.quot_sq hI hY hFinv inf_le_left
  have hlt : c' < k := by
    obtain ⟨q, hq, hqy⟩ := hymove
    have hFY : F < Y := lt_of_le_of_ne inf_le_left fun h => by
      have hqF : q ∈ F := h ▸ hq
      exact hqy ((mem_fixed_zpowers_iff (b := y)).1 hqF.2)
    have h1 := Subgroup.card_lt_of_lt hFY
    rw [card_eq_two_pow hS.quot_sq F, card_eq_two_pow hS.quot_sq Y] at h1
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h1
    rw [hc'.2.2, hY.2.2] at h2
    exact Nat.lt_of_mul_lt_mul_right h2
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, hp2, hpL, y, y.2, hyL, hyp, hymove, c', hlt,
    card_end_pow_modEq hS.quot_sq hI hY hyΛ' hYy hyp hc'⟩

end KplusSit

section KplusCases

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem card_eq_168_of_isPSL32 {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_eq_60_of_alt5 {X : Type} [Group X] (h : Nonempty (X ≃* alternatingGroup (Fin 5))) :
    Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem perfect_Λ (hB : D321Base M Mp T L V t) :
    ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hB.L_le,
    hB.perfect]

theorem kplus_l32 (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hU : commSub (orbSup T V) L = V) (hL3 : IsPSL 3 2 1 ↥L)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1) {k : ℕ}
    (hY : letI := qAct hS.hD.hyp.Mp_normal;
      IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) k)
    (hk : k ≤ 4) :
    letI := qAct hS.hD.hyp.Mp_normal
    k = 4 ∧ ∃ (y : MulAut W) (hy : y ∈ M), (∀ l ∈ L, y * l = l * y) ∧
      (∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy⟩ : ↥M) ^ 5 • q = q) ∧
      ∃ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy⟩ : ↥M) • q ≠ q := by
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨p, hp, hp2, hpL, y, hy, hyL, hyp, hymove, c', hc', hmod⟩ :=
    kplus_of hS hVt hU (Or.inl hL3) hY
  obtain ⟨K, hKf, hKfin, hK, π, hR⟩ := hnat
  have hE := card_end_eq_two_of_nat hS.hD.hyp.Mp_normal hS.L_le hK hR (hS.irr_L hVt)
  rw [hE] at hmod
  have h168 := card_eq_168_of_isPSL32 hL3
  rcases prime_of_two_pow_modEq hp hp2 hk hc' hmod with rfl | rfl | ⟨rfl, rfl, -⟩
  · exact absurd (by rw [h168]; norm_num) hpL
  · exact absurd (by rw [h168]; norm_num) hpL
  · exact ⟨rfl, y, hy, hyL, hyp, hymove⟩

theorem false_of_alt5 (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V)
    (hA5 : Nonempty (↥L ≃* alternatingGroup (Fin 5)))
    (hcard : letI := qAct hS.hD.hyp.Mp_normal; Nat.card ↥(tilde Mp ⊤ V) = 2 ^ 4)
    (hY : letI := qAct hS.hD.hyp.Mp_normal;
      IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) 2) : False := by
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨p, hp, hp2, hpL, y, hy, hyL, hyp, hymove, c', hc', hmod⟩ :=
    kplus_of hS hVt hU (Or.inr hA5) hY
  have hI := hS.irr_L hVt
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hIc : XMod.commOf ↥(L.subgroupOf M) (tilde Mp ⊤ V) = tilde Mp ⊤ V :=
    commOf_eq_self_of_isIrr hI (hF.moved _ hF.le_Y hF.irr)
  have hlt := card_end_lt_card (perfect_Λ hS.toD321Base) hI hIc
  obtain ⟨m, hm⟩ := exists_card_eq_card_end_pow hI
  rw [hcard] at hlt hm
  have he := eq_two_or_four_of_pow (even_card_end hS.quot_sq hI) hlt hm
  have h60 := card_eq_60_of_alt5 hA5
  rcases prime_of_end_pow_two_modEq hp hp2 he hc' hmod with rfl | rfl
  · exact hpL (by rw [h60]; norm_num)
  · exact hpL (by rw [h60]; norm_num)

end KplusCases

section FFSideSec

def FFType {Q : Type} [CommGroup Q] (H : Subgroup (MulAut Q)) : Prop :=
  (∃ n, 2 ≤ n ∧ BinaryNaturalSL H ⊤ ⊥ 2 n) ∨ (BinaryNaturalSL H ⊤ ⊥ 3 1 ∧ IsPSL 3 2 1 ↥H) ∨
    (AlternatingNatural H ⊤ ⊥ 5 ∧ Nat.card Q = 2 ^ 4)

theorem ffType_of_concl {Q : Type} [CommGroup Q] [Finite Q] {G H F : Subgroup (MulAut Q)}
    (h : A38B42Concl G H F) : FFType H := by
  rcases h with ⟨-, n, hn, h, -, -⟩ | ⟨-, h, h3, -⟩ | ⟨-, h, hc, -⟩
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl ⟨h, h3⟩)
  · exact Or.inr (Or.inr ⟨h, hc⟩)

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

def FFSide (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (X : Subgroup (MulAut W)) :
    Prop :=
  letI := qAct hMp
  ∃ J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)), J ≤ tilde Mp ⊤ (commV X) ∧
    XMod.IsIrr ↥(X.subgroupOf M) J ∧
    ∃ hJX : ∀ g ∈ X.subgroupOf M, ∀ j ∈ J, g • j ∈ J, FFType (resJ (X.subgroupOf M) J hJX).range

theorem strict_or_ffSide (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) {X : Subgroup (MulAut W)}
    {I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))} (hF : SideFL hS.hD.hyp.Mp_normal X I)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hm : 0 < mRel (A.subgroupOf M) (X.subgroupOf M)) :
    letI := qAct hS.hD.hyp.Mp_normal
    (mRel (A.subgroupOf M) (X.subgroupOf M) : ℚ) * rk ↥(tilde Mp ⊤ (commV X)) <
        rk ↥I * nB (A.subgroupOf M) (tilde Mp ⊤ (commV X)) ∨
      FFSide hS.hD.hyp.Mp_normal X := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hAM := hS.A_le
  obtain ⟨hAc, hA2⟩ := hS.elemAb
  have hPc : ∀ a ∈ A.subgroupOf M, ∀ b ∈ A.subgroupOf M, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hP2 : ∀ a ∈ A.subgroupOf M, a ^ 2 = 1 := fun a ha =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hA2 _ (Subgroup.mem_subgroupOf.1 ha))
  have hPX : ∀ a ∈ A.subgroupOf M, ∀ x ∈ X.subgroupOf M, a * x * a⁻¹ ∈ X.subgroupOf M :=
    fun a ha x hx => Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hAX (Subgroup.mem_subgroupOf.1 ha)) _).1
        (Subgroup.mem_subgroupOf.1 hx))
  have hYP : ∀ a ∈ A.subgroupOf M, ∀ y ∈ tilde Mp ⊤ (commV X), a • y ∈ tilde Mp ⊤ (commV X) := by
    rintro a ha _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (hAX (Subgroup.mem_subgroupOf.1 ha)) u hu, rfl⟩
  have hcub := isCubicOn_qAct hS.hD.hyp.Mp_normal
    (le_bot_iff.1 ((commSeries_mono le_rfl 3).trans hS.cubic.le)) (tilde Mp ⊤ (commV X))
  have hI0 : rk ↥I ≠ 0 := fun h => hF.irr.2.1.ne' ((rk_eq_zero_iff hS.quot_sq).1 h)
  have hY0 : tilde Mp ⊤ (commV X) ≠ ⊥ := by
    intro h
    have h1 := hF.two_le
    rw [h, rk_bot] at h1
    omega
  rcases ff_or_nB_gt_of_a38 hA21 hB42 h9 hS.hD.hyp.qsqtk hS.quot_sq hF.simple hF.a38 hPc hP2 hPX
    hYP hF.inv hcub hF.ss hF.rk_eq hF.moved hm hY0 with h | ⟨J, hJY, hJ, hJ', hJX, F, hB4, hFF, hC⟩
  · exact Or.inl h
  · exact Or.inr ⟨J, hJY, hJ, hJX, ffType_of_concl hC⟩

theorem ffSide_or (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    FFSide hS.hD.hyp.Mp_normal L ∨ FFSide hS.hD.hyp.Mp_normal (conjAutSub t L) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hF' := sideFL_of hS.swapV.toD321Base (D321Base.swapV_fix hS.toD321Base hVt) hS.swapV.htop
  have hm : rk ↥(tilde Mp ⊤ (commV (conjAutSub t L))) = rk ↥(tilde Mp ⊤ (commV L)) := by
    rw [← hS.smul_tildeU, rk_smul]
  have hd : rk ↥(tilde Mp ⊤ (V.map t.toMonoidHom)) = rk ↥(tilde Mp ⊤ V) := by
    rw [← smul_eq_map, ← smul_tildeQ hS.hD.hyp.Mp_normal ⟨t, hS.t_mem⟩, rk_smul]
  have hsum : nB (A.subgroupOf M) (tilde Mp ⊤ (commV L)) +
      nB (A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L))) ≤ 2 * rk ↥A := by
    have hinv₁ : XMod.IsInv ↥(A.subgroupOf M) (tilde Mp ⊤ (commV L)) := by
      rintro ⟨a, ha⟩ _ ⟨u, hu, rfl⟩
      exact ⟨_, B15P4.map_commV_mem (hAL (Subgroup.mem_subgroupOf.1 ha)) u hu, rfl⟩
    have hinv₂ : XMod.IsInv ↥(A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L))) := by
      rintro ⟨a, ha⟩ _ ⟨u, hu, rfl⟩
      exact ⟨_, B15P4.map_commV_mem (le_normalizer_Lt hS hAL (Subgroup.mem_subgroupOf.1 ha)) u
        hu, rfl⟩
    have hd' : tilde Mp ⊤ (commV L) ⊓ tilde Mp ⊤ (commV (conjAutSub t L)) = ⊥ := by
      rw [← hS.smul_tildeU]
      exact hS.inf_tildeU hVt
    have hs' : tilde Mp ⊤ (commV L) ⊔ tilde Mp ⊤ (commV (conjAutSub t L)) = ⊤ := by
      rw [← hS.smul_tildeU]
      exact hS.sup_tildeU
    have := nB_sup_of_disjoint (A.subgroupOf M) hinv₁ hinv₂ hd'
    rw [hs'] at this
    have h2 := hS.nB_le
    omega
  have hrel := rk_le_mRel_add hS hAC
  have hpos := hS.rk_pos
  have hm2 : 2 * rk ↥(tilde Mp ⊤ V) ≤ rk ↥(tilde Mp ⊤ (commV L)) := hF.two_le
  set m := rk ↥(tilde Mp ⊤ (commV L)) with hmdef
  set d := rk ↥(tilde Mp ⊤ V) with hddef
  set a := mRel (A.subgroupOf M) (L.subgroupOf M) with hadef
  set a' := mRel (A.subgroupOf M) ((conjAutSub t L).subgroupOf M) with ha'def
  set n₁ := nB (A.subgroupOf M) (tilde Mp ⊤ (commV L)) with hn₁
  set n₂ := nB (A.subgroupOf M) (tilde Mp ⊤ (commV (conjAutSub t L))) with hn₂
  have hs1 : (a : ℚ) * m ≤ d * n₁ ∧ (0 < a → (a : ℚ) * m < d * n₁) := by
    refine ⟨?_, fun ha => (strict_or_ffSide hA21 hB42 h9 hS hF hAL ha).resolve_right h1⟩
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.cast_zero, zero_mul]
      positivity
    · exact ((strict_or_ffSide hA21 hB42 h9 hS hF hAL ha).resolve_right h1).le
  have hs2 : (a' : ℚ) * m ≤ d * n₂ ∧ (0 < a' → (a' : ℚ) * m < d * n₂) := by
    have key : 0 < a' → (a' : ℚ) * m < d * n₂ := fun ha => by
      have h := (strict_or_ffSide hA21 hB42 h9 hS hF' (le_normalizer_Lt hS hAL) ha).resolve_right
        h2
      rw [hm, hd] at h
      exact h
    refine ⟨?_, key⟩
    rcases Nat.eq_zero_or_pos a' with ha | ha
    · rw [ha, Nat.cast_zero, zero_mul]
      positivity
    · exact (key ha).le
  have e4 : (a : ℚ) * m + a' * m < d * n₁ + d * n₂ := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · have ha' : 0 < a' := by omega
      have := hs2.2 ha'
      have := hs1.1
      linarith
    · have := hs1.2 ha
      have := hs2.1
      linarith
  have e1 : (rk ↥A : ℚ) * m ≤ (a : ℚ) * m + a' * m := by
    have h0 : (rk ↥A : ℚ) ≤ (a : ℚ) + a' := by exact_mod_cast hrel
    have := mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg m : (0 : ℚ) ≤ m)
    linarith [show ((a : ℚ) + a') * m = (a : ℚ) * m + a' * m by ring]
  have e2 : (d : ℚ) * n₁ + d * n₂ ≤ 2 * ((d : ℚ) * rk ↥A) := by
    have h0 : ((n₁ : ℚ) + n₂) ≤ 2 * (rk ↥A : ℚ) := by exact_mod_cast hsum
    have := mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg d : (0 : ℚ) ≤ d)
    linarith [show (d : ℚ) * ((n₁ : ℚ) + n₂) = d * n₁ + d * n₂ by ring,
      show (d : ℚ) * (2 * (rk ↥A : ℚ)) = 2 * ((d : ℚ) * rk ↥A) by ring]
  have e3 : 2 * ((d : ℚ) * rk ↥A) ≤ (rk ↥A : ℚ) * m := by
    have h0 : (2 * d : ℚ) ≤ m := by exact_mod_cast hm2
    have := mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg (rk ↥A) : (0 : ℚ) ≤ rk ↥A)
    linarith [show (2 * d : ℚ) * rk ↥A = 2 * ((d : ℚ) * rk ↥A) by ring,
      show (m : ℚ) * rk ↥A = (rk ↥A : ℚ) * m by ring]
  linarith

omit [Finite W] in
theorem tilde_inf_comap {U : Subgroup W} {J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hJU : J ≤ tilde Mp ⊤ U) :
    tilde Mp ⊤ (U ⊓ J.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)))) = J := by
  refine le_antisymm ?_ fun j hj => ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact hu.2
  · obtain ⟨u, hu, rfl⟩ := hJU hj
    exact ⟨u, ⟨hu, hj⟩, rfl⟩

theorem type_of_ffSide (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hff : FFSide hS.hD.hyp.Mp_normal L) :
    (∃ n, 2 ≤ n ∧ BinaryNaturalSL L V (V ⊓ fixV Mp) 2 n) ∨
      (IsPSL 3 2 1 ↥L ∧ BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1) ∨
      (Nonempty (↥L ≃* alternatingGroup (Fin 5)) ∧
        letI := qAct hS.hD.hyp.Mp_normal; Nat.card ↥(tilde Mp ⊤ V) = 2 ^ 4) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hMp := hS.hD.hyp.Mp_normal
  obtain ⟨J, hJY, hJ, hJX, hT⟩ := hff
  have hLM := hS.L_le
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hnt := hF.moved J hJY hJ
  have hinj := resJ_injective_of_isSimpleGroup hF.simple hJX hnt
  let eR : ↥(resJ (L.subgroupOf M) J hJX).range ≃* ↥L :=
    (MonoidHom.ofInjective hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hLM)
  obtain ⟨g, hgJ⟩ : ∃ g : {g : ↥M // (g : MulAut W) ∈ N},
      XMod.Iso ↥(L.subgroupOf M) J ((g : ↥M) • tilde Mp ⊤ V) := by
    have h1 := hJY
    rw [hS.tildeU_eq_iSup hVt, iSup_subtype'] at h1
    exact SmithD391.exists_iso_of_le_iSup
      (fun g => isIrr_smul_of_mem_normalizer hMp g.2 (hS.irr_L hVt)) hJ h1
  have hgM : ((g : ↥M) : MulAut W) ∈ M := (g : ↥M).2
  have hgN : ((g : ↥M) : MulAut W) ∈ N := g.2
  have hlift : ∀ {D : FFModel}, D.Realizes (resJ (L.subgroupOf M) J hJX).range ⊤ ⊥ →
      D.Realizes L V (V ⊓ fixV Mp) := by
    intro D hD
    have hUX : ∀ x ∈ L, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu =>
      B15P4.map_commV_mem (Subgroup.le_normalizer hx) u hu
    obtain ⟨π, hπ⟩ := realizes_lift_of_resJ hMp hLM hS.hsimp hUX hJY hJX hnt hD
    set gV := V.map ((g : ↥M) : MulAut W).toMonoidHom with hgV
    have hIL : ∀ x ∈ L, ∀ u ∈ gV, x u ∈ gV := fun x hx u hu =>
      hS.Mp_inv_map hgM x (hS.L_le_Mp hx) u hu
    have hiso : XMod.Iso ↥(L.subgroupOf M) (tilde Mp ⊤ gV)
        (tilde Mp ⊤ (commV L ⊓ J.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))))) := by
      rw [tilde_inf_comap hJY, hgV, ← smul_eq_map, ← smul_tildeQ hMp]
      exact XMod.Iso.symm hJ.1 hgJ
    have h2 := realizesVia_of_iso_tilde hMp hLM hπ hIL hiso
    have h3 := realizesVia_conjAutSub h2 ((g : ↥M) : MulAut W)⁻¹
    have e1 : conjAutSub ((g : ↥M) : MulAut W)⁻¹ L = L :=
      mem_normalizer_iff_conjAutSub.1 (N.inv_mem hgN)
    have e2 : gV.map ((g : ↥M) : MulAut W)⁻¹.toMonoidHom = V := by
      rw [hgV, Subgroup.map_map]
      convert Subgroup.map_id V
      ext v
      simp
    have e3 : (gV ⊓ fixV Mp).map ((g : ↥M) : MulAut W)⁻¹.toMonoidHom = V ⊓ fixV Mp := by
      rw [Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _), e2, map_fixV_conjAutSub,
        mem_normalizer_iff_conjAutSub.1 (hMp (M.inv_mem hgM))]
    rw [e2, e3] at h3
    have h4 : D.Realizes (conjAutSub ((g : ↥M) : MulAut W)⁻¹ L) V (V ⊓ fixV Mp) := ⟨_, h3⟩
    rw [e1] at h4
    exact h4
  rcases hT with ⟨n, hn, K, hKf, hKfin, hK, hR⟩ | ⟨⟨K, hKf, hKfin, hK, hR⟩, h3⟩ | ⟨hR, hc⟩
  · exact Or.inl ⟨n, hn, K, hKf, hKfin, hK, hlift hR⟩
  · exact Or.inr (Or.inl ⟨SmithD37.isPSL_transfer eR.symm h3, K, hKf, hKfin, hK, hlift hR⟩)
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · obtain ⟨π, hπ⟩ := hR
      have hπi : Function.Injective π :=
        FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
      exact ⟨eR.symm.trans (MulEquiv.ofBijective π ⟨hπi, hπ.1⟩).symm⟩
    · have h1 := card_eq_of_iso hgJ
      rw [hc, card_eq_two_pow hS.quot_sq, rk_smul, ← card_eq_two_pow hS.quot_sq] at h1
      exact h1.symm

end FFSideSec

section Assembly

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem not_isPSL_two_of_isPSL32 {X : Type} [Group X] {n : ℕ} (h3 : IsPSL 3 2 1 X)
    (h2 : IsPSL 2 2 n X) : False := by
  have e3 := card_eq_168_of_isPSL32 h3
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h2).1 rfl] at e3
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> revert e3 <;> decide
  · have hq : 16 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    unfold ordA at e3
    simp only [show 2 - 1 = 1 from rfl, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one,
      show (1 + 1 : ℕ) = 2 from rfl, Finset.Icc_self, Finset.prod_singleton] at e3
    set q := 2 ^ n with hqdef
    have h1 : 256 ≤ q ^ 2 := by nlinarith
    have h2 : 16 * 255 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) :=
      Nat.div_le_div_left (Nat.gcd_le_left _ two_pos) (Nat.gcd_pos_of_pos_left _ two_pos)
    have h4 : 16 * 255 / 2 ≤ q * (q ^ 2 - 1) / 2 := Nat.div_le_div_right h2
    omega

theorem inf_fixV_L (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : V ⊓ fixV L = V ⊓ fixV Mp := by
  refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩) (inf_le_inf_left _ (fixV_anti hB.L_le_Mp))
  rw [hB.hMp, fixV_sup]
  exact ⟨hv.2, mem_fixV.2 fun g hg => hVt v hv.1 g hg⟩

theorem binaryNaturalSL_conj (hB : D321Base M Mp T L V t) {d n : ℕ}
    (h : BinaryNaturalSL L V (V ⊓ fixV Mp) d n) :
    BinaryNaturalSL (conjAutSub t L) (V.map t.toMonoidHom) (V.map t.toMonoidHom ⊓ fixV Mp) d n := by
  obtain ⟨K, hKf, hKfin, hK, π, hR⟩ := h
  have h2 := realizesVia_conjAutSub hR t
  rw [Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _), map_fixV_conjAutSub,
    mem_normalizer_iff_conjAutSub.1 (hB.hD.hyp.Mp_normal hB.t_mem)] at h2
  exact ⟨K, hKf, hKfin, hK, _, h2⟩

theorem isotypic_of_iso (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hiso : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ g ∈ (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M,
        XMod.Iso ↥(L.subgroupOf M) (g • tilde Mp ⊤ V) (tilde Mp ⊤ V)) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ k : ℕ, IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) k := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hI := hB.irr_L hVt
  have hinv : XMod.IsInv ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) := by
    rintro ⟨x, hx⟩ _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hx)) u hu,
      rfl⟩
  have hle : tilde Mp ⊤ (commV L) ≤ isoComp ↥(L.subgroupOf M) (tilde Mp ⊤ V) := by
    rw [tildeU_eq_iSup' hB hVt]
    exact iSup₂_le fun g hg => le_isoComp
      (isIrr_smul_of_mem_normalizer hB.hD.hyp.Mp_normal (Subgroup.mem_subgroupOf.1 hg) hI)
      (hiso g hg)
  obtain ⟨k, hk⟩ := exists_rk_eq_mul hB.quot_sq hI hinv hle
  exact ⟨k, hinv, hle, hk⟩

theorem family_of_isotypic (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) {k : ℕ}
    (hY : letI := qAct hB.hD.hyp.Mp_normal;
      IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) k) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ S : Fin k → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)),
      (∀ i, XMod.IsInv ↥(L.subgroupOf M) (S i) ∧
        XMod.Iso ↥(L.subgroupOf M) (S i) (tilde Mp ⊤ V)) ∧
      (∀ i, S i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), S j = ⊥) ∧
      (⨆ i, S i) = tilde Mp ⊤ (commV L) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hI := hB.irr_L hVt
  let ι := {g : ↥M // (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))}
  let J : ι → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)) := fun g => (g : ↥M) • tilde Mp ⊤ V
  have hJsup : (⨆ g, J g) = tilde Mp ⊤ (commV L) := by
    rw [hB.tildeU_eq_iSup hVt, iSup_subtype']
  have hJ : ∀ g, XMod.IsIrr ↥(L.subgroupOf M) (J g) ∧
      XMod.Iso ↥(L.subgroupOf M) (J g) (tilde Mp ⊤ V) := by
    intro g
    have hirr := isIrr_smul_of_mem_normalizer hB.hD.hyp.Mp_normal g.2 hI
    refine ⟨hirr, iso_of_le_isoComp hirr ((le_iSup J g).trans (hJsup.le.trans hY.2.1))⟩
  have hk : rk ↥(⨆ g, J g) = k * rk ↥(tilde Mp ⊤ V) := by
    rw [hJsup]
    exact hY.2.2
  obtain ⟨S, hSJ, hind, hsup⟩ := exists_family_of_iSup hB.quot_sq hI J hJ hk
  refine ⟨S, fun i => ?_, hind, hsup.trans hJsup⟩
  obtain ⟨j, hj⟩ := hSJ i
  rw [hj]
  exact ⟨(hJ j).1.1, (hJ j).2⟩

theorem isotypic_two (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hU : commSub (orbSup T V) L = V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hL3 : ¬ IsPSL 3 2 1 ↥L) :
    letI := qAct hS.hD.hyp.Mp_normal
    IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) (tilde Mp ⊤ V) 2 := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hb := nonswap_bound hA21 hB42 h9 hS hVt hAC hAL (q₀ := 1) (Or.inr ⟨rfl, hL3⟩)
  have hb' : rk ↥(tilde Mp ⊤ (commV L)) ≤ 2 * rk ↥(tilde Mp ⊤ V) := by
    rw [one_mul] at hb
    exact_mod_cast hb
  obtain ⟨k, hY⟩ := isotypic_of_iso hS.toD321Base hVt (iso_of_rk_le_two hS.toD321Base hVt hU hb')
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have h2 : 2 * rk ↥(tilde Mp ⊤ V) ≤ rk ↥(tilde Mp ⊤ (commV L)) := hF.two_le
  have hd0 : 0 < rk ↥(tilde Mp ⊤ V) := Nat.pos_of_ne_zero fun h =>
    (hS.irr_L hVt).2.1.ne' ((rk_eq_zero_iff hS.quot_sq).1 h)
  have hk : k = 2 := by
    have h3 := hY.2.2
    rw [h3] at hb' h2
    have h4 : k * rk ↥(tilde Mp ⊤ V) = 2 * rk ↥(tilde Mp ⊤ V) := le_antisymm hb' h2
    exact Nat.eq_of_mul_eq_mul_right hd0 h4
  rw [hk] at hY
  exact hY

end Assembly

end CFSG.Quasithin.SmithD321
