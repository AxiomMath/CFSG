module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def suppMoved (Δ : Set (Subgroup G)) (t : G) : Set (Subgroup G) :=
  {D | D ∈ Δ ∧ conjSubgroup D t ≠ D}

@[expose] def suppAct (Δ : Set (Subgroup G)) (t : G) : Set (Subgroup G) :=
  {D | D ∈ Δ ∧ ¬ D ≤ centralizer ({t} : Set G)}

@[expose] def suppFix (Δ : Set (Subgroup G)) (t : G) : Set (Subgroup G) :=
  {D | D ∈ suppAct Δ t ∧ conjSubgroup D t = D}

private theorem mem_Y_comm {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a b : G}
    (ha : a ∈ Y) (hb : b ∈ Y) : a * b = b * a := by
  haveI := hY.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Y) ⟨b, hb⟩)

private theorem conjSubgroup_sSup (Δ : Set (Subgroup G)) (t : G) :
    conjSubgroup (sSup Δ) t = sSup ((fun D => conjSubgroup D t) '' Δ) := by
  have h : conjSubgroup (sSup Δ) t =
      (sSup Δ).map (MulAut.conj t⁻¹).toMonoidHom := rfl
  rw [h, sSup_eq_iSup', Subgroup.map_iSup, sSup_image, ← iSup_subtype'']
  simp only [conjSubgroup]

private theorem conjSubgroup_sSup_eq_self {Y : Subgroup G} {Δ : Set (Subgroup G)}
    (hspan : sSup Δ = Y) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ) : conjSubgroup Y t = Y := by
  have hle : conjSubgroup Y t ≤ Y := by
    rw [← hspan, conjSubgroup_sSup]
    apply sSup_le
    rintro E ⟨D, hD, rfl⟩
    exact hspan ▸ le_sSup (hperm D hD)
  have h2 : conjSubgroup (conjSubgroup Y t) t = Y := by
    rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
  refine le_antisymm hle ?_
  have h3 : conjSubgroup (conjSubgroup Y t) t ≤ conjSubgroup Y t :=
    E3.conjSubgroup_mono_left t hle
  rwa [h2] at h3

private theorem mem_comm_conj {Y : Subgroup G} {Δ : Set (Subgroup G)}
    (hspan : sSup Δ = Y) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ) {y : G} (hy : y ∈ Y) :
    y * t * y⁻¹ * t⁻¹ ∈ Y := by
  have hYt := conjSubgroup_sSup_eq_self hspan ht hperm
  have hx : t * y⁻¹ * t⁻¹ ∈ Y := by
    refine hYt ▸ mem_conjSubgroup_iff.mpr ?_
    have h1 : t * (t * y⁻¹ * t⁻¹) * t⁻¹ = y⁻¹ := by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      calc t * (t * y⁻¹ * t⁻¹) * t⁻¹
          = (t * t) * y⁻¹ * (t⁻¹ * t⁻¹) := by group
        _ = y⁻¹ := by rw [ht, htinv, ht]; group
    rw [h1]
    exact Y.inv_mem hy
  rw [show y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) by group]
  exact Y.mul_mem hy hx

private theorem eq_of_mul_eq_mul {D₀ D₁ : Subgroup G} (hinf : D₀ ⊓ D₁ = ⊥)
    {p q r s : G} (hp : p ∈ D₀) (hq : q ∈ D₁) (hr : r ∈ D₀) (hs : s ∈ D₁)
    (h : p * q = r * s) : p = r ∧ q = s := by
  have h1 : p⁻¹ * r = q * s⁻¹ := by
    calc p⁻¹ * r = p⁻¹ * (r * s) * s⁻¹ := by group
      _ = p⁻¹ * (p * q) * s⁻¹ := by rw [← h]
      _ = q * s⁻¹ := by group
  have h2 : p⁻¹ * r ∈ D₀ ⊓ D₁ :=
    ⟨D₀.mul_mem (D₀.inv_mem hp) hr, h1 ▸ D₁.mul_mem hq (D₁.inv_mem hs)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have hpr : p = r := by rwa [inv_mul_eq_one] at h2
  refine ⟨hpr, ?_⟩
  rw [hpr] at h
  exact mul_left_cancel h

private theorem rk_subgroupOf_eq {U V : Subgroup G} (h : U ≤ V) :
    rk ↥(U.subgroupOf V) = rk ↥U := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

private theorem mQuot_inf_eq_rk_sub {Y : Subgroup G} (hY : IsPGroup 2 Y) (C : Subgroup G) :
    E3.mQuot Y (Y ⊓ C) = rk ↥Y - rk ↥(Y ⊓ C) := by
  have hgoal : E3.mQuot Y (Y ⊓ C) = rkIdx ((Y ⊓ C).subgroupOf Y) :=
    E3.mQuot_eq_rkIdx Y (Y ⊓ C)
  rw [hgoal, rkIdx]
  have h := rk_add_rkIdx ((Y ⊓ C).subgroupOf Y)
  rw [rkIdx, rk_subgroupOf_eq inf_le_left] at h
  omega

private theorem mem_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (z : G) :
    z ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = z := by
  constructor
  · intro h
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro w (hw | hw)
      · exact ⟨w, hw, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, w, hw, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [hcomm y₂ hy₂ z₁ hz₁]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
      simpa [mul_inv_rev] using (congrArg Inv.inv (hcomm y hy z hz)).symm
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

private theorem card_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun p => ⟨p.1.1 * p.2.1, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_comm hcomm z.1).mp z.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hinj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ h
    have h' : h₁.1 * k₁.1 = h₂.1 * k₂.1 := congrArg Subtype.val h
    have hkey : h₁.1⁻¹ * h₂.1 = k₁.1 * k₂.1⁻¹ := by
      calc h₁.1⁻¹ * h₂.1 = h₁.1⁻¹ * (h₂.1 * k₂.1) * k₂.1⁻¹ := by group
        _ = h₁.1⁻¹ * (h₁.1 * k₁.1) * k₂.1⁻¹ := by rw [← h']
        _ = k₁.1 * k₂.1⁻¹ := by group
    have hmem : h₁.1⁻¹ * h₂.1 ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem h₁.2) h₂.2, hkey ▸ K.mul_mem k₁.2 (K.inv_mem k₂.2)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      rwa [inv_mul_eq_one] at hmem
    have hk : k₁ = k₂ := by
      apply Subtype.ext
      rw [hh] at h'
      exact mul_left_cancel h'
    exact Prod.ext hh hk
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

private theorem rk_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    rk ↥(H ⊔ K) = rk ↥H + rk ↥K := by
  unfold rk
  rw [card_sup_of_comm hcomm hinf, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']

private theorem mQuot_inf_sup {Y Y₁ Y₂ : Subgroup G} (hY : IsElemAbelian 2 Y)
    (hY₁ : Y₁ ≤ Y) (hY₂ : Y₂ ≤ Y) (hsup : Y₁ ⊔ Y₂ = Y) (hinf : Y₁ ⊓ Y₂ = ⊥)
    {t : G} (hst₁ : ∀ y ∈ Y₁, t * y * t⁻¹ ∈ Y₁) (hst₂ : ∀ y ∈ Y₂, t * y * t⁻¹ ∈ Y₂) :
    E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) =
      E3.mQuot Y₁ (Y₁ ⊓ centralizer ({t} : Set G)) +
        E3.mQuot Y₂ (Y₂ ⊓ centralizer ({t} : Set G)) := by
  have hcomm₁₂ : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y = y * x :=
    fun x hx y hy => mem_Y_comm hY (hY₁ hx) (hY₂ hy)
  have hCY : Y ⊓ centralizer ({t} : Set G) =
      (Y₁ ⊓ centralizer ({t} : Set G)) ⊔ (Y₂ ⊓ centralizer ({t} : Set G)) := by
    apply le_antisymm
    · rintro z ⟨hzY, hzC⟩
      have hzY' : z ∈ Y₁ ⊔ Y₂ := by rw [hsup]; exact hzY
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_comm hcomm₁₂ z).mp hzY'
      have hzc : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hzC
        have h2 : t * (a * b) * t⁻¹ = a * b := by
          calc t * (a * b) * t⁻¹ = ((a * b) * t) * t⁻¹ := by rw [← h]
            _ = a * b := by group
        rwa [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group] at h2
      obtain ⟨ha_eq, hb_eq⟩ :=
        eq_of_mul_eq_mul hinf (hst₁ a ha) (hst₂ b hb) ha hb hzc
      refine Subgroup.mul_mem_sup ⟨ha, ?_⟩ ⟨hb, ?_⟩
      · change a ∈ Subgroup.centralizer ({t} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 : t * a = a * t := by
          calc t * a = (t * a * t⁻¹) * t := by group
            _ = a * t := by rw [ha_eq]
        exact h2.symm
      · change b ∈ Subgroup.centralizer ({t} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 : t * b = b * t := by
          calc t * b = (t * b * t⁻¹) * t := by group
            _ = b * t := by rw [hb_eq]
        exact h2.symm
    · apply sup_le
      · exact le_inf (le_trans inf_le_left hY₁) inf_le_right
      · exact le_inf (le_trans inf_le_left hY₂) inf_le_right
  have hY2 : IsPGroup 2 Y := hY.isPGroup
  have hY₁2 : IsPGroup 2 Y₁ := (hY.mono hY₁).isPGroup
  have hY₂2 : IsPGroup 2 Y₂ := (hY.mono hY₂).isPGroup
  have hbot : (Y₁ ⊓ centralizer ({t} : Set G)) ⊓ (Y₂ ⊓ centralizer ({t} : Set G)) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    rintro x ⟨⟨hx1, -⟩, hx2, -⟩
    exact Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
  have hrkY : rk ↥Y = rk ↥Y₁ + rk ↥Y₂ := by
    rw [← hsup]
    exact rk_sup_of_comm hcomm₁₂ hinf
  have hrkC : rk ↥(Y ⊓ centralizer ({t} : Set G)) =
      rk ↥(Y₁ ⊓ centralizer ({t} : Set G)) + rk ↥(Y₂ ⊓ centralizer ({t} : Set G)) := by
    rw [hCY]
    exact rk_sup_of_comm (fun x hx y hy => mem_Y_comm hY (hY₁ hx.1) (hY₂ hy.1)) hbot
  have hle1 : rk ↥(Y₁ ⊓ centralizer ({t} : Set G)) ≤ rk ↥Y₁ := rk_mono inf_le_left
  have hle2 : rk ↥(Y₂ ⊓ centralizer ({t} : Set G)) ≤ rk ↥Y₂ := rk_mono inf_le_left
  rw [mQuot_inf_eq_rk_sub hY2 (centralizer ({t} : Set G)),
    mQuot_inf_eq_rk_sub hY₁2 (centralizer ({t} : Set G)),
    mQuot_inf_eq_rk_sub hY₂2 (centralizer ({t} : Set G))]
  rw [hrkY, hrkC]
  omega

private theorem rk_inf_centralizer_sup_eq {Y D₀ D₁ : Subgroup G} (hY : IsElemAbelian 2 Y)
    (hD₀ : D₀ ≤ Y) (hD₁ : D₁ ≤ Y) (hinf : D₀ ⊓ D₁ = ⊥) {t : G} (ht : t * t = 1)
    (hst₀ : ∀ a ∈ D₀, t * a * t⁻¹ ∈ D₁) (hst₁ : ∀ b ∈ D₁, t * b * t⁻¹ ∈ D₀) :
    rk ↥((D₀ ⊔ D₁) ⊓ centralizer ({t} : Set G)) = rk ↥D₀ := by
  have hfixed : ∀ a ∈ D₀, t * (a * (t * a * t⁻¹)) * t⁻¹ = a * (t * a * t⁻¹) := by
    intro a ha
    have hta : t * a * t⁻¹ ∈ D₁ := hst₀ a ha
    have hcancel : t * (t * a * t⁻¹) * t⁻¹ = a := by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
        _ = a := by rw [ht, htinv, ht]; group
    calc t * (a * (t * a * t⁻¹)) * t⁻¹
        = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by group
      _ = (t * a * t⁻¹) * a := by rw [hcancel]
      _ = a * (t * a * t⁻¹) :=
        mem_Y_comm (Y := Y) hY (a := t * a * t⁻¹) (b := a) (hD₁ hta) (hD₀ ha)
  let f : ↥D₀ → ↥((D₀ ⊔ D₁) ⊓ centralizer ({t} : Set G)) := fun a =>
    ⟨a.1 * (t * a.1 * t⁻¹), by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem_sup a.2 (hst₀ a.1 a.2)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hfixed a.1 a.2
        have h2 : (a.1 * (t * a.1 * t⁻¹)) * t = t * (a.1 * (t * a.1 * t⁻¹)) := by
          conv_lhs => rw [← h1]
          group
        exact h2⟩
  have hf_inj : Function.Injective f := by
    intro a a' h
    have h' : a.1 * (t * a.1 * t⁻¹) = a'.1 * (t * a'.1 * t⁻¹) :=
      congrArg Subtype.val h
    exact Subtype.ext
      (eq_of_mul_eq_mul hinf a.2 (hst₀ a.1 a.2) a'.2 (hst₀ a'.1 a'.2) h').1
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      (mem_sup_of_comm (fun x hx y hy => mem_Y_comm hY (hD₀ hx) (hD₁ hy)) z.1).mp z.2.1
    have hzc : (t * p * t⁻¹) * (t * q * t⁻¹) = p * q := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
      rw [← hpq] at h
      have h2 : t * (p * q) * t⁻¹ = p * q := by
        calc t * (p * q) * t⁻¹ = ((p * q) * t) * t⁻¹ := by rw [← h]
          _ = p * q := by group
      rwa [show t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) by group] at h2
    have hswap : (t * q * t⁻¹) * (t * p * t⁻¹) = (t * p * t⁻¹) * (t * q * t⁻¹) :=
      mem_Y_comm hY (hD₀ (hst₁ q hq)) (hD₁ (hst₀ p hp))
    have hzc' : (t * q * t⁻¹) * (t * p * t⁻¹) = p * q := by rw [hswap]; exact hzc
    have hpq' : t * p * t⁻¹ = q :=
      (eq_of_mul_eq_mul hinf (hst₁ q hq) (hst₀ p hp) hp hq hzc').2
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    show p * (t * p * t⁻¹) = z.1
    rw [hpq', hpq]
  have hcard : Nat.card ↥((D₀ ⊔ D₁) ⊓ centralizer ({t} : Set G)) = Nat.card ↥D₀ :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  unfold rk
  rw [hcard]

private theorem sSup_sdiff_pair_inf_sup_eq_bot {Δ : Set (Subgroup G)} (hind : sSupIndep Δ)
    {D₀ D₁ : Subgroup G} (hD₀ : D₀ ∈ Δ) (hD₁ : D₁ ∈ Δ) (hne : D₁ ≠ D₀)
    (hcomm : ∀ x ∈ D₀, ∀ y ∈ D₁, x * y = y * x) :
    sSup (Δ \ {D₀, D₁}) ⊓ (D₀ ⊔ D₁) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hz'⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_comm hcomm z).mp hz'
  have hsub₀ : Δ \ {D₀, D₁} ⊆ Δ \ {D₀} := by
    intro E hE
    exact ⟨hE.1, fun h => hE.2 (Or.inl (by simpa using h))⟩
  have hz₀ : a * b ∈ sSup (Δ \ {D₀}) := (sSup_le_sSup hsub₀) hz
  have hb₀ : b ∈ sSup (Δ \ {D₀}) :=
    (le_sSup (s := Δ \ {D₀}) ⟨hD₁, by simpa using hne⟩) hb
  have ha₀ : a ∈ sSup (Δ \ {D₀}) := by
    have h : a = (a * b) * b⁻¹ := by group
    rw [h]
    exact (sSup (Δ \ {D₀})).mul_mem hz₀ ((sSup (Δ \ {D₀})).inv_mem hb₀)
  have ha_bot : a = 1 := by
    have : a ∈ D₀ ⊓ sSup (Δ \ {D₀}) := ⟨ha, ha₀⟩
    rwa [(hind hD₀).eq_bot, Subgroup.mem_bot] at this
  have hsub₁ : Δ \ {D₀, D₁} ⊆ Δ \ {D₁} := by
    intro E hE
    exact ⟨hE.1, fun h => hE.2 (Or.inr (by simpa using h))⟩
  have hb₁ : b ∈ sSup (Δ \ {D₁}) := by
    have : a * b ∈ sSup (Δ \ {D₁}) := (sSup_le_sSup hsub₁) hz
    rwa [ha_bot, one_mul] at this
  have hb_bot : b = 1 := by
    have : b ∈ D₁ ⊓ sSup (Δ \ {D₁}) := ⟨hb, hb₁⟩
    rwa [(hind hD₁).eq_bot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, ha_bot, hb_bot, mul_one]

private theorem s15_Support_rank_formula_aux :
    ∀ (n : ℕ) (Y : Subgroup G) (Δ : Set (Subgroup G)) (γ : ℕ) (t : G),
      Δ.ncard = n → IsElemAbelian 2 Y → sSupIndep Δ → sSup Δ = Y →
      (∀ D ∈ Δ, rk ↥D = γ) → t * t = 1 → (∀ D ∈ Δ, conjSubgroup D t ∈ Δ) →
      Even (suppMoved Δ t).ncard ∧
        E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) =
          (∑ᶠ D ∈ suppFix Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) +
            γ * ((suppMoved Δ t).ncard / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y Δ γ t hcard hY hind hspan hγ ht hperm
    classical
    by_cases hne : Δ = ∅
    · rw [hne] at hspan ⊢
      have hYbot : Y = ⊥ := by rw [← hspan]; simp
      rw [hYbot]
      refine ⟨?_, ?_⟩
      · simp [suppMoved]
      · simp [suppMoved, suppFix, suppAct, E3.mQuot_self]
    · obtain ⟨D₀, hD₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
      let D₁ : Subgroup G := conjSubgroup D₀ t
      have hD₁ : D₁ ∈ Δ := hperm D₀ hD₀
      let o : Set (Subgroup G) := {D₀, D₁}
      let Δ' : Set (Subgroup G) := Δ \ o
      have hΔ'sub : Δ' ⊆ Δ := Set.sdiff_subset
      have ho_sub : o ⊆ Δ := by
        intro E hE
        change E ∈ ({D₀, D₁} : Set (Subgroup G)) at hE
        rcases (by simpa using hE : E = D₀ ∨ E = D₁) with rfl | rfl
        · exact hD₀
        · exact hD₁
      have hΔ'union : Δ' ∪ o = Δ := by
        change Δ \ o ∪ o = Δ
        exact Set.sdiff_union_of_subset ho_sub
      have hD₁t : conjSubgroup D₁ t = D₀ := by
        change conjSubgroup (conjSubgroup D₀ t) t = D₀
        rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
      have hD₀Y : D₀ ≤ Y := hspan ▸ le_sSup hD₀
      have hD₁Y : D₁ ≤ Y := hspan ▸ le_sSup hD₁
      have hperm' : ∀ D ∈ Δ', conjSubgroup D t ∈ Δ' := by
        intro D hD
        obtain ⟨hDΔ, hDo⟩ := hD
        refine ⟨hperm D hDΔ, fun hmem => hDo ?_⟩
        change conjSubgroup D t ∈ ({D₀, D₁} : Set (Subgroup G)) at hmem
        change D ∈ ({D₀, D₁} : Set (Subgroup G))
        rcases (by simpa using hmem : conjSubgroup D t = D₀ ∨
          conjSubgroup D t = D₁) with h | h
        · right
          have h1 : D = conjSubgroup (conjSubgroup D t) t := by
            rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
          rw [h1, h]
          exact Set.mem_singleton_iff.mpr rfl
        · left
          have h1 : D = conjSubgroup (conjSubgroup D t) t := by
            rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
          rw [h1, h, hD₁t]
      have hssub : Δ' ⊂ Δ :=
        ⟨hΔ'sub, fun hΔΔ' => (hΔΔ' hD₀).2 (Or.inl rfl)⟩
      have hcard' : Δ'.ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard hssub
      have hY'le : sSup Δ' ≤ Y := by
        rw [← hspan]
        exact sSup_le_sSup hΔ'sub
      have hY'el : IsElemAbelian 2 (sSup Δ') := hY.mono hY'le
      have hγ' : ∀ D ∈ Δ', rk ↥D = γ := fun D hD => hγ D (hΔ'sub hD)
      obtain ⟨heven', hform'⟩ :=
        ih Δ'.ncard hcard' (sSup Δ') Δ' γ t rfl hY'el (hind.mono hΔ'sub) rfl hγ' ht hperm'
      have hst' : ∀ y ∈ sSup Δ', t * y * t⁻¹ ∈ sSup Δ' := by
        intro y hy
        have hconj : conjSubgroup (sSup Δ') t = sSup Δ' := by
          rw [conjSubgroup_sSup]
          congr 1
          apply Set.Subset.antisymm
          · rintro E ⟨D, hD, rfl⟩; exact hperm' D hD
          · intro E hE
            refine ⟨conjSubgroup E t, hperm' E hE, ?_⟩
            show conjSubgroup (conjSubgroup E t) t = E
            rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
        exact mem_conjSubgroup_iff.mp (hconj.symm ▸ hy)
      have hY₀le : sSup o ≤ Y := by
        rw [← hspan]
        exact sSup_le_sSup ho_sub
      have hsup : sSup Δ' ⊔ sSup o = Y := by
        rw [← sSup_union, hΔ'union, hspan]
      have hXsub : suppFix Δ' t ⊆ suppFix Δ t := by
        rintro D ⟨hDact, hDfix⟩
        exact ⟨⟨hΔ'sub hDact.1, hDact.2⟩, hDfix⟩
      by_cases hfix : D₁ = D₀
      · have ho : o = {D₀} := by
          change ({D₀, D₁} : Set (Subgroup G)) = {D₀}
          rw [hfix]
          simp
        have hY₀ : sSup o = D₀ := by rw [ho, sSup_singleton]
        have hΔ'eq : Δ' = Δ \ {D₀} := by
          change Δ \ o = Δ \ {D₀}
          rw [ho]
        have hst0 : ∀ y ∈ sSup o, t * y * t⁻¹ ∈ sSup o := by
          intro y hy
          rw [hY₀] at hy ⊢
          have hconj : conjSubgroup D₀ t = D₀ := by simpa only [D₁] using hfix
          exact mem_conjSubgroup_iff.mp (hconj.symm ▸ hy)
        have hinf : sSup Δ' ⊓ sSup o = ⊥ := by
          rw [hY₀, hΔ'eq, eq_bot_iff]
          intro x hx
          have : x ∈ D₀ ⊓ sSup (Δ \ {D₀}) := ⟨hx.2, hx.1⟩
          rwa [(hind hD₀).eq_bot, Subgroup.mem_bot] at this
        have hadd := mQuot_inf_sup hY hY'le hY₀le hsup hinf hst' hst0
        have hY₀m : E3.mQuot (sSup o) (sSup o ⊓ centralizer ({t} : Set G)) =
            E3.mQuot D₀ (D₀ ⊓ centralizer ({t} : Set G)) := by rw [hY₀]
        have hfix_o : ∀ D ∈ o, conjSubgroup D t = D := by
          intro D hD
          change D ∈ ({D₀, D₁} : Set (Subgroup G)) at hD
          rcases (by simpa using hD : D = D₀ ∨ D = D₁) with rfl | rfl
          · simpa only [D₁] using hfix
          · rw [hD₁t]; exact hfix.symm
        have hmoved : suppMoved Δ t = suppMoved Δ' t := by
          ext D
          constructor
          · rintro ⟨hDΔ, hDt⟩
            have hD' : D ∈ Δ' := by
              by_contra h
              have hDo : D ∈ o := by
                have h1 := hΔ'union ▸ hDΔ
                rw [Set.mem_union] at h1
                exact h1.resolve_left h
              exact hDt (hfix_o D hDo)
            exact ⟨hD', hDt⟩
          · rintro ⟨hD', hDt⟩
            exact ⟨hΔ'sub hD', hDt⟩
        have hfixeq : suppFix Δ t = suppFix Δ' t ∪ (suppFix Δ t ∩ {D₀}) := by
          apply Set.Subset.antisymm
          · intro D hD
            by_cases h : D ∈ Δ'
            · exact Or.inl ⟨⟨h, hD.1.2⟩, hD.2⟩
            · have hDo : D ∈ o := by
                have h1 := hΔ'union ▸ hD.1.1
                rw [Set.mem_union] at h1
                exact h1.resolve_left h
              have hDeq : D = D₀ := by
                change D ∈ ({D₀, D₁} : Set (Subgroup G)) at hDo
                rcases (by simpa using hDo : D = D₀ ∨ D = D₁) with rfl | rfl
                · rfl
                · exact hfix
              exact Or.inr ⟨hD, by simp [hDeq]⟩
          · rintro D (hD | hD)
            · exact hXsub hD
            · exact hD.1
        have hdisj : Disjoint (suppFix Δ' t) (suppFix Δ t ∩ {D₀}) := by
          rw [Set.disjoint_left]
          rintro D hD' ⟨-, hD0⟩
          have hDeq : D = D₀ := Set.mem_singleton_iff.mp hD0
          rw [hDeq] at hD'
          exact hD'.1.1.2 (Or.inl rfl)
        have hD'not : D₀ ∉ suppFix Δ' t := by
          rintro ⟨⟨hD'0, -⟩, -⟩
          exact hD'0.2 (Or.inl rfl)
        have hfixsum :
            (∑ᶠ D ∈ suppFix Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) =
              (∑ᶠ D ∈ suppFix Δ' t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) +
                (if D₀ ∈ suppFix Δ t then
                  E3.mQuot D₀ (D₀ ⊓ centralizer ({t} : Set G)) else 0) := by
          rw [hfixeq, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
          congr 1
          by_cases h : D₀ ∈ suppFix Δ t
          · have hc : D₀ ∈ suppFix Δ' t ∪ (suppFix Δ t ∩ {D₀}) := Or.inr ⟨h, rfl⟩
            rw [if_pos hc]
            have hsingle : suppFix Δ t ∩ {D₀} = {D₀} := by
              ext D; constructor
              · rintro ⟨-, h0⟩; exact h0
              · rintro rfl; exact ⟨h, rfl⟩
            rw [hsingle, finsum_mem_singleton]
          · have hc : ¬ (D₀ ∈ suppFix Δ' t ∪ (suppFix Δ t ∩ {D₀})) := by
              rintro (h1 | ⟨h2, -⟩)
              · exact hD'not h1
              · exact h h2
            rw [if_neg hc]
            have hempty : suppFix Δ t ∩ {D₀} = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro D ⟨hD, h0⟩
              exact h (Set.mem_singleton_iff.mp h0 ▸ hD)
            rw [hempty, finsum_mem_empty]
        have hzero : D₀ ∉ suppFix Δ t →
            E3.mQuot D₀ (D₀ ⊓ centralizer ({t} : Set G)) = 0 := by
          intro h
          have hle : D₀ ≤ centralizer ({t} : Set G) := by
            by_contra hle
            exact h ⟨⟨hD₀, hle⟩, by simpa only [D₁] using hfix⟩
          rw [inf_eq_left.mpr hle, E3.mQuot_self]
        have hz : (if D₀ ∈ suppFix Δ t then
              E3.mQuot D₀ (D₀ ⊓ centralizer ({t} : Set G)) else 0) =
            E3.mQuot D₀ (D₀ ⊓ centralizer ({t} : Set G)) := by
          by_cases h : D₀ ∈ suppFix Δ t
          · rw [if_pos h]
          · rw [if_neg h, hzero h]
        refine ⟨by rw [hmoved]; exact heven', ?_⟩
        rw [hadd, hform', hY₀m, hfixsum, hz, hmoved]
        ring
      · have hD₁ne : D₀ ≠ D₁ := fun h => hfix h.symm
        have ho : sSup o = D₀ ⊔ D₁ := by
          change sSup ({D₀, D₁} : Set (Subgroup G)) = D₀ ⊔ D₁
          rw [show ({D₀, D₁} : Set (Subgroup G)) = {D₀} ∪ {D₁} from rfl]
          simp only [sSup_union, sSup_singleton]
        have hinfD : D₀ ⊓ D₁ = ⊥ :=
          (hind.pairwiseDisjoint hD₀ hD₁ hD₁ne).eq_bot
        have hst₀ : ∀ a ∈ D₀, t * a * t⁻¹ ∈ D₁ := by
          intro a ha
          refine mem_conjSubgroup_iff.mpr ?_
          have hcancel : t * (t * a * t⁻¹) * t⁻¹ = a := by
            have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
            calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
              _ = a := by rw [ht, htinv, ht]; group
          rw [hcancel]; exact ha
        have hst₁ : ∀ b ∈ D₁, t * b * t⁻¹ ∈ D₀ := fun b hb => mem_conjSubgroup_iff.mp hb
        have hst0 : ∀ y ∈ sSup o, t * y * t⁻¹ ∈ sSup o := by
          intro y hy
          have hconj : conjSubgroup (sSup o) t = sSup o := by
            rw [conjSubgroup_sSup]
            congr 1
            change (fun D => conjSubgroup D t) '' ({D₀, D₁} : Set (Subgroup G)) = {D₀, D₁}
            rw [Set.image_pair]
            have h0 : conjSubgroup D₀ t = D₁ := rfl
            have h1 : conjSubgroup D₁ t = D₀ := hD₁t
            rw [h0, h1]
            exact (Set.pair_comm D₀ D₁).symm
          exact mem_conjSubgroup_iff.mp (hconj.symm ▸ hy)
        have hinf : sSup Δ' ⊓ sSup o = ⊥ := by
          rw [ho]
          exact sSup_sdiff_pair_inf_sup_eq_bot hind hD₀ hD₁ hfix
            (fun x hx y hy => mem_Y_comm hY (hD₀Y hx) (hD₁Y hy))
        have hadd := mQuot_inf_sup hY hY'le hY₀le hsup hinf hst' hst0
        have hY₀m : E3.mQuot (sSup o) (sSup o ⊓ centralizer ({t} : Set G)) = γ := by
          rw [ho]
          have hsupY : D₀ ⊔ D₁ ≤ Y := ho ▸ hY₀le
          have hY2 : IsPGroup 2 ↥(D₀ ⊔ D₁) := (hY.mono hsupY).isPGroup
          rw [mQuot_inf_eq_rk_sub hY2 (centralizer ({t} : Set G))]
          have hrk : rk ↥(D₀ ⊔ D₁) = rk ↥D₀ + rk ↥D₁ :=
            rk_sup_of_comm (fun x hx y hy => mem_Y_comm hY (hD₀Y hx) (hD₁Y hy)) hinfD
          have hdiag := rk_inf_centralizer_sup_eq hY hD₀Y hD₁Y hinfD ht hst₀ hst₁
          rw [hrk, hγ D₀ hD₀, hγ D₁ hD₁, hdiag, hγ D₀ hD₀]
          omega
        have hmoved : suppMoved Δ t = suppMoved Δ' t ∪ {D₀, D₁} := by
          ext D
          constructor
          · rintro ⟨hDΔ, hDt⟩
            by_cases h : D ∈ Δ'
            · exact Or.inl ⟨h, hDt⟩
            · right
              have hDo : D ∈ o := by
                have h1 := hΔ'union ▸ hDΔ
                rw [Set.mem_union] at h1
                exact h1.resolve_left h
              change D ∈ ({D₀, D₁} : Set (Subgroup G)) at hDo
              exact hDo
          · rintro (⟨hD', hDt⟩ | hD01)
            · exact ⟨hΔ'sub hD', hDt⟩
            · change D ∈ ({D₀, D₁} : Set (Subgroup G)) at hD01
              rcases (by simpa using hD01 : D = D₀ ∨ D = D₁) with rfl | rfl
              · exact ⟨hD₀, hfix⟩
              · exact ⟨hD₁, by rw [hD₁t]; exact hD₁ne⟩
        have hdisj_moved : Disjoint (suppMoved Δ' t) ({D₀, D₁} : Set (Subgroup G)) := by
          rw [Set.disjoint_left]
          rintro D hD' (h | h)
          · rw [h] at hD'; exact hD'.1.2 (Or.inl rfl)
          · rw [h] at hD'; exact hD'.1.2 (Or.inr rfl)
        have hcard_moved : (suppMoved Δ t).ncard = (suppMoved Δ' t).ncard + 2 := by
          rw [hmoved, Set.ncard_union_eq hdisj_moved (Set.toFinite _) (Set.toFinite _),
            Set.ncard_pair hD₁ne]
        have hfixeq : suppFix Δ t = suppFix Δ' t := by
          apply Set.Subset.antisymm
          · intro D hD
            have hD' : D ∈ Δ' := by
              by_contra h
              have hDo : D ∈ o := by
                have h1 := hΔ'union ▸ hD.1.1
                rw [Set.mem_union] at h1
                exact h1.resolve_left h
              change D ∈ ({D₀, D₁} : Set (Subgroup G)) at hDo
              rcases (by simpa using hDo : D = D₀ ∨ D = D₁) with rfl | rfl
              · exact hfix hD.2
              · have h2 := hD.2
                rw [hD₁t] at h2
                exact hD₁ne h2
            exact ⟨⟨hD', hD.1.2⟩, hD.2⟩
          · exact hXsub
        have hfixsum :
            (∑ᶠ D ∈ suppFix Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) =
              (∑ᶠ D ∈ suppFix Δ' t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) := by
          rw [hfixeq]
        refine ⟨?_, ?_⟩
        · rw [hcard_moved]; exact heven'.add even_two
        · rw [hadd, hform', hY₀m, hfixsum, hcard_moved]
          have hdiv : (suppMoved Δ' t).ncard / 2 + 1 = ((suppMoved Δ' t).ncard + 2) / 2 := by
            obtain ⟨k, hk⟩ := heven'
            omega
          rw [← hdiv]
          ring

theorem s15_Support_rank_formula {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hind : sSupIndep Δ) (hspan : sSup Δ = Y) {γ : ℕ}
    (hγ : ∀ D ∈ Δ, rk ↥D = γ) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ) :
    Even (suppMoved Δ t).ncard ∧
      E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) =
        (∑ᶠ D ∈ suppFix Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G))) +
          γ * ((suppMoved Δ t).ncard / 2) :=
  s15_Support_rank_formula_aux Δ.ncard Y Δ γ t rfl hY hind hspan hγ ht hperm

theorem s15_Support_comm_mem {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hspan : sSup Δ = Y) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ) {y : G} (hy : y ∈ Y) :
    y * t * y⁻¹ * t⁻¹ ∈ ⨆ D ∈ suppAct Δ t, D := by
  classical
  let S : Subgroup G := ⨆ D ∈ suppAct Δ t, D
  have hCst : conjSubgroup (centralizer ({t} : Set G)) t ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hx' : x = t * x * t⁻¹ :=
      calc x = t⁻¹ * (t * x * t⁻¹ * t) := by group
        _ = t⁻¹ * (t * (t * x * t⁻¹)) := by rw [hx]
        _ = t * x * t⁻¹ := by group
    have h2 : t * x = x * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [← hx']
    exact h2.symm
  have hmem : ∀ D ∈ Δ, ∀ x ∈ D, x ∈ Y ∧ x * t * x⁻¹ * t⁻¹ ∈ S := by
    intro D hD x hx
    refine ⟨hspan ▸ le_sSup hD hx, ?_⟩
    by_cases hDC : D ≤ centralizer ({t} : Set G)
    · have hc : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hDC hx)
      have h1 : x * t * x⁻¹ * t⁻¹ = 1 := by
        calc x * t * x⁻¹ * t⁻¹ = t * x * x⁻¹ * t⁻¹ := by rw [hc]
          _ = 1 := by group
      rw [h1]
      exact S.one_mem
    · have hDact : D ∈ suppAct Δ t := ⟨hD, hDC⟩
      have hD1act : conjSubgroup D t ∈ suppAct Δ t := by
        refine ⟨hperm D hD, fun hC1 => hDC ?_⟩
        have hle : D ≤ conjSubgroup (centralizer ({t} : Set G)) t := by
          have hD_eq : D = conjSubgroup (conjSubgroup D t) t := by
            rw [conjSubgroup_conjSubgroup, ht, conjSubgroup_one]
          rw [hD_eq]
          exact E3.conjSubgroup_mono_left t hC1
        exact hle.trans hCst
      have hz : t * x⁻¹ * t⁻¹ ∈ conjSubgroup D t := by
        rw [mem_conjSubgroup_iff]
        rw [show t * (t * x⁻¹ * t⁻¹) * t⁻¹ = x⁻¹ by
          have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
          calc t * (t * x⁻¹ * t⁻¹) * t⁻¹ = (t * t) * x⁻¹ * (t⁻¹ * t⁻¹) := by group
            _ = x⁻¹ := by rw [ht, htinv, ht]; group]
        exact D.inv_mem hx
      have hleS : D ⊔ conjSubgroup D t ≤ S :=
        sup_le (le_iSup_of_le D (le_iSup_of_le hDact le_rfl))
          (le_iSup_of_le (conjSubgroup D t) (le_iSup_of_le hD1act le_rfl))
      simpa only [mul_assoc] using hleS (Subgroup.mul_mem_sup hx hz)
  let H : Subgroup G :=
    { carrier := {z | z ∈ Y ∧ z * t * z⁻¹ * t⁻¹ ∈ S}
      one_mem' := ⟨Y.one_mem, by simp [S]⟩
      mul_mem' := by
        rintro x z ⟨hxY, hxS⟩ ⟨hzY, hzS⟩
        refine ⟨Y.mul_mem hxY hzY, ?_⟩
        have hzt : z * t * z⁻¹ * t⁻¹ ∈ Y := mem_comm_conj hspan ht hperm hzY
        have hcomm : x * (z * t * z⁻¹ * t⁻¹) * x⁻¹ = z * t * z⁻¹ * t⁻¹ := by
          rw [mem_Y_comm hY hxY hzt]
          group
        have hmul : (x * z) * t * (x * z)⁻¹ * t⁻¹ =
            x * (z * t * z⁻¹ * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * t⁻¹) := by group
        rw [hmul, hcomm]
        exact S.mul_mem hzS hxS
      inv_mem' := by
        rintro x ⟨hxY, hxS⟩
        refine ⟨Y.inv_mem hxY, ?_⟩
        have hYt : conjSubgroup Y t = Y := conjSubgroup_sSup_eq_self hspan ht hperm
        have htx : t * x * t⁻¹ ∈ Y := mem_conjSubgroup_iff.mp (hYt.symm ▸ hxY)
        have heq : x⁻¹ * t * x * t⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by
          have h1 : (x * t * x⁻¹ * t⁻¹)⁻¹ = (t * x * t⁻¹) * x⁻¹ := by group
          have h2 : x⁻¹ * t * x * t⁻¹ = x⁻¹ * (t * x * t⁻¹) := by group
          rw [h1, h2]
          exact mem_Y_comm hY (Y.inv_mem hxY) htx
        rw [inv_inv, heq]
        exact S.inv_mem hxS }
  have hYH : Y ≤ H := by
    rw [← hspan]
    exact sSup_le fun D hD => fun x hx => hmem D hD x hx
  exact (hYH hy).2

theorem s15_Support_act_eq (Δ : Set (Subgroup G)) (t : G) :
    suppAct Δ t = suppFix Δ t ∪ suppMoved Δ t := by
  ext D
  constructor
  · rintro ⟨hD, hC⟩
    by_cases h : conjSubgroup D t = D
    · exact Or.inl ⟨⟨hD, hC⟩, h⟩
    · exact Or.inr ⟨hD, h⟩
  · rintro (⟨hD, -⟩ | ⟨hD, hne⟩)
    · exact hD
    · refine ⟨hD, fun hC => hne ?_⟩
      have hc : ∀ y ∈ D, y * t = t * y := fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.1 (hC hy)
      ext x
      rw [mem_conjSubgroup_iff]
      constructor
      · intro hx
        have h1 := hc _ hx
        have hx' : x = t * x * t⁻¹ :=
          calc x = t⁻¹ * (t * x * t⁻¹ * t) := by group
            _ = t⁻¹ * (t * (t * x * t⁻¹)) := by rw [h1]
            _ = t * x * t⁻¹ := by group
        rw [hx']
        exact hx
      · intro hx
        have h1 := hc x hx
        have : t * x * t⁻¹ = x := by
          calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [h1]
            _ = x := by group
        rw [this]
        exact hx

theorem s15_Support_disjoint (Δ : Set (Subgroup G)) (t : G) :
    Disjoint (suppFix Δ t) (suppMoved Δ t) := by
  rw [Set.disjoint_left]
  rintro D ⟨-, hfix⟩ ⟨-, hne⟩
  exact hne hfix

theorem s15_Support_one_le {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {Δ : Set (Subgroup G)}
    (hspan : sSup Δ = Y) {t : G} {D : Subgroup G} (hD : D ∈ suppAct Δ t) :
    1 ≤ E3.mQuot D (D ⊓ centralizer ({t} : Set G)) := by
  have hDY : D ≤ Y := hspan ▸ le_sSup hD.1
  have hD2 : IsPGroup 2 D := hY.isPGroup.to_le hDY
  by_contra h0
  have h0' : E3.mQuot D (D ⊓ centralizer ({t} : Set G)) = 0 := by omega
  exact hD.2 (inf_eq_left.1 ((E3.mQuot_eq_zero_iff hD2 inf_le_left).1 h0'))

private theorem ncard_le_finsum {S : Set (Subgroup G)} {c : Subgroup G → ℕ}
    (h : ∀ D ∈ S, 1 ≤ c D) : S.ncard ≤ ∑ᶠ D ∈ S, c D := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum c hS, Set.ncard_eq_toFinset_card S hS]
  calc hS.toFinset.card = ∑ _D ∈ hS.toFinset, 1 := by simp
    _ ≤ ∑ D ∈ hS.toFinset, c D :=
        Finset.sum_le_sum fun D hD => h D (hS.mem_toFinset.1 hD)

private theorem eq_one_of_finsum_eq_ncard {S : Set (Subgroup G)} {c : Subgroup G → ℕ}
    (h : ∀ D ∈ S, 1 ≤ c D) (heq : ∑ᶠ D ∈ S, c D = S.ncard) : ∀ D ∈ S, c D = 1 := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum c hS, Set.ncard_eq_toFinset_card S hS] at heq
  intro D hD
  by_contra hne
  have hD' : D ∈ hS.toFinset := hS.mem_toFinset.2 hD
  have hlt : 1 < c D := lt_of_le_of_ne (h D hD) (Ne.symm hne)
  have : hS.toFinset.card < ∑ D ∈ hS.toFinset, c D := by
    calc hS.toFinset.card = ∑ _D ∈ hS.toFinset, 1 := by simp
      _ < ∑ D ∈ hS.toFinset, c D :=
          Finset.sum_lt_sum (fun D hD => h D (hS.mem_toFinset.1 hD)) ⟨D, hD', hlt⟩
  omega

theorem s15_Support_ncard_act_le {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hind : sSupIndep Δ) (hspan : sSup Δ = Y) {γ : ℕ}
    (hγ : ∀ D ∈ Δ, rk ↥D = γ) (hγ2 : 2 ≤ γ) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ) :
    (suppAct Δ t).ncard ≤ E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) := by
  obtain ⟨⟨k, hk⟩, hform⟩ := s15_Support_rank_formula hY hind hspan hγ ht hperm
  rw [hform, s15_Support_act_eq,
    Set.ncard_union_eq (s15_Support_disjoint Δ t) (Set.toFinite _) (Set.toFinite _)]
  have h1 := ncard_le_finsum (S := suppFix Δ t)
    (c := fun D => E3.mQuot D (D ⊓ centralizer ({t} : Set G)))
    (fun D hD => s15_Support_one_le hY hspan hD.1)
  have h2 : (suppMoved Δ t).ncard / 2 = k := by omega
  have h3 : 2 * k ≤ γ * k := Nat.mul_le_mul_right k hγ2
  rw [h2]
  omega

theorem s15_Support_conj_eq_of_lt {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hind : sSupIndep Δ) (hspan : sSup Δ = Y) {γ : ℕ}
    (hγ : ∀ D ∈ Δ, rk ↥D = γ) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ)
    (hn : E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) < γ) :
    suppMoved Δ t = ∅ := by
  obtain ⟨⟨k, hk⟩, hform⟩ := s15_Support_rank_formula hY hind hspan hγ ht hperm
  have h2 : (suppMoved Δ t).ncard / 2 = k := by omega
  rw [h2] at hform
  have hk0 : k = 0 := by
    by_contra hne
    have : γ ≤ γ * k := Nat.le_mul_of_pos_right γ (Nat.pos_of_ne_zero hne)
    omega
  have hcard : (suppMoved Δ t).ncard = 0 := by omega
  exact (Set.ncard_eq_zero (Set.toFinite _)).1 hcard

theorem s15_Support_eq_finsum {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hind : sSupIndep Δ) (hspan : sSup Δ = Y) {γ : ℕ}
    (hγ : ∀ D ∈ Δ, rk ↥D = γ) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ)
    (hn : E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) < γ) :
    E3.mQuot Y (Y ⊓ centralizer ({t} : Set G)) =
      ∑ᶠ D ∈ suppAct Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G)) := by
  have hmv := s15_Support_conj_eq_of_lt hY hind hspan hγ ht hperm hn
  obtain ⟨-, hform⟩ := s15_Support_rank_formula hY hind hspan hγ ht hperm
  have hact : suppAct Δ t = suppFix Δ t := by
    rw [s15_Support_act_eq, hmv, Set.union_empty]
  rw [hact, hform, hmv]
  simp

theorem s15_Support_eq_of_ncard_eq {Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    {Δ : Set (Subgroup G)} (hind : sSupIndep Δ) (hspan : sSup Δ = Y) {γ : ℕ}
    (hγ : ∀ D ∈ Δ, rk ↥D = γ) (hγ3 : 3 ≤ γ) {t : G} (ht : t * t = 1)
    (hperm : ∀ D ∈ Δ, conjSubgroup D t ∈ Δ)
    (hcard : (suppAct Δ t).ncard = E3.mQuot Y (Y ⊓ centralizer ({t} : Set G))) :
    ∀ D ∈ suppAct Δ t,
      conjSubgroup D t = D ∧ E3.mQuot D (D ⊓ centralizer ({t} : Set G)) = 1 := by
  obtain ⟨⟨k, hk⟩, hform⟩ := s15_Support_rank_formula hY hind hspan hγ ht hperm
  have h2 : (suppMoved Δ t).ncard / 2 = k := by omega
  have h1 := ncard_le_finsum (S := suppFix Δ t)
    (c := fun D => E3.mQuot D (D ⊓ centralizer ({t} : Set G)))
    (fun D hD => s15_Support_one_le hY hspan hD.1)
  have hu : (suppAct Δ t).ncard = (suppFix Δ t).ncard + (suppMoved Δ t).ncard := by
    rw [s15_Support_act_eq,
      Set.ncard_union_eq (s15_Support_disjoint Δ t) (Set.toFinite _) (Set.toFinite _)]
  rw [hform, h2] at hcard
  have hk0 : k = 0 := by
    by_contra hne
    have : 3 * k ≤ γ * k := Nat.mul_le_mul_right k hγ3
    have hpos : 0 < k := Nat.pos_of_ne_zero hne
    omega
  have hmv : suppMoved Δ t = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 (by omega)
  have hact : suppAct Δ t = suppFix Δ t := by
    rw [s15_Support_act_eq, hmv, Set.union_empty]
  have hsum : ∑ᶠ D ∈ suppFix Δ t, E3.mQuot D (D ⊓ centralizer ({t} : Set G)) =
      (suppFix Δ t).ncard := by
    rw [hmv, Set.ncard_empty] at hu
    omega
  have hone := eq_one_of_finsum_eq_ncard
    (fun D hD => s15_Support_one_le hY hspan hD.1) hsum
  intro D hD
  rw [hact] at hD
  exact ⟨hD.2, hone D hD⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
