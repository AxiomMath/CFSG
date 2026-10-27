module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheckB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocSubs
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem range_mem (hF : J4Facts)
    {A : Subgroup J} (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A) {B : List ℕ}
    (hB : MaskList (A ⊓ Eg uJ 11) B) {a : J} (ha : a ∈ A) (haP : a ∈ P0) {t : List ℕ}
    (hat : Acts a t) {c : ℕ} (hc : c < 2048) : (actT t c ^^^ c) ∈ B := by
  have hM := hF.mat
  refine (hB _).2 ⟨Nat.xor_lt_two_pow (actT_lt hat.1 c) hc, ?_⟩
  have e : eta uJ 11 (actT t c ^^^ c) = a * eta uJ 11 c * a⁻¹ * (eta uJ 11 c)⁻¹ := by
    rw [← eta_mul_eta hM, ← hat.2 c hc, eta_inv hM]
  rw [e]
  refine ⟨?_, ?_⟩
  · have h1 : eta uJ 11 c * a⁻¹ * (eta uJ 11 c)⁻¹ ∈ A :=
      hn _ (Eg_le_P0 (eta_mem_Eg 11 le_rfl c)) a⁻¹ (A.inv_mem ha)
    have : a * eta uJ 11 c * a⁻¹ * (eta uJ 11 c)⁻¹ =
        a * (eta uJ 11 c * a⁻¹ * (eta uJ 11 c)⁻¹) := by group
    rw [this]
    exact A.mul_mem ha h1
  · exact (Eg uJ 11).mul_mem (Hj_normalizes_Eg hM a (P0_le_Hj haP) _ (eta_mem_Eg 11 le_rfl c))
      ((Eg uJ 11).inv_mem (eta_mem_Eg 11 le_rfl c))

theorem fix_mem (hF : J4Facts) {A : Subgroup J}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {B : List ℕ} (hB : MaskList (A ⊓ Eg uJ 11) B)
    {a : J} (ha : a ∈ A) {t : List ℕ} (hat : Acts a t) : ∀ c ∈ B, actT t c = c := by
  have hM := hF.mat
  intro c hc
  obtain ⟨hlt, hcA, -⟩ := (hB c).1 hc
  have h1 := hcomm a ha _ hcA
  have h2 := hat.2 c hlt
  have h3 : a * eta uJ 11 c * a⁻¹ = eta uJ 11 c := by rw [h1]; group
  rw [h3] at h2
  exact (eta_inj' hM hlt (actT_lt hat.1 c) h2).symm

theorem natCard_mem_le {α : Type*} [DecidableEq α] (L : List α) :
    Nat.card {c : α // c ∈ L} ≤ L.length := by
  have h1 : Nat.card {c : α // c ∈ L} = Nat.card ↥L.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => (List.mem_toFinset).symm)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact List.toFinset_card_le L

theorem relIndex_le_xcnt
    (hF : J4Facts) {A : Subgroup J} (hAP : A ≤ P0) (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) {B : List ℕ}
    (hB : MaskList (A ⊓ Eg uJ 11) B) : (Eg uJ 11).relIndex A ≤ xcnt B := by
  classical
  have hM := hF.mat
  have hT : ∀ a : A, ∃ t ∈ tabL, Acts (a : J) t := fun a => table_of_mem hM a (hAP a.2)
  choose tbl htbl hacts using hT
  have hx : ∀ a : A, tbl a ∈ xset B := by
    intro a
    refine mem_xset.2 ⟨htbl a, ?_, fix_mem hF hcomm hB a.2 (hacts a), fun c hc =>
      range_mem hF hn hB a.2 (hAP a.2) (hacts a) hc⟩
    have h := (hacts a).mul (hacts a)
    have h1 : (a : J) * (a : J) = 1 := hsq a a.2
    rw [h1] at h
    exact h.unique hM Acts.one
  let f : (A ⧸ (Eg uJ 11).subgroupOf A) → {t : List ℕ // t ∈ xset B} :=
    fun q => ⟨tbl q.out, hx q.out⟩
  have hf : Function.Injective f := by
    intro q1 q2 h12
    have h12' : tbl q1.out = tbl q2.out := congrArg Subtype.val h12
    set a1 := q1.out with ha1
    set a2 := q2.out with ha2
    have hA2 : Acts (a2 : J) (tbl a1) := by rw [h12']; exact hacts a2
    have hcen : ∀ y ∈ Eg uJ 11, ((a1 : J)⁻¹ * (a2 : J)) * y = y * ((a1 : J)⁻¹ * (a2 : J)) := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have e1 := (hacts a1).2 c hc
      have e2 := hA2.2 c hc
      calc (a1 : J)⁻¹ * (a2 : J) * eta uJ 11 c
          = (a1 : J)⁻¹ * ((a2 : J) * eta uJ 11 c * (a2 : J)⁻¹) * (a2 : J) := by group
        _ = (a1 : J)⁻¹ * ((a1 : J) * eta uJ 11 c * (a1 : J)⁻¹) * (a2 : J) := by rw [e2, e1]
        _ = eta uJ 11 c * ((a1 : J)⁻¹ * (a2 : J)) := by group
    have hmem : (a1 : J)⁻¹ * (a2 : J) ∈ Eg uJ 11 :=
      centralizer_Hj hM hF _ (Hj.mul_mem (Hj.inv_mem (P0_le_Hj (hAP a1.2)))
        (P0_le_Hj (hAP a2.2))) hcen
    have : (a1 : A ⧸ (Eg uJ 11).subgroupOf A) = a2 := by
      rw [QuotientGroup.eq]
      exact hmem
    calc q1 = (a1 : A ⧸ (Eg uJ 11).subgroupOf A) := (QuotientGroup.out_eq' q1).symm
      _ = a2 := this
      _ = q2 := QuotientGroup.out_eq' q2
  calc (Eg uJ 11).relIndex A = Nat.card (A ⧸ (Eg uJ 11).subgroupOf A) := rfl
    _ ≤ Nat.card {t : List ℕ // t ∈ xset B} := Nat.card_le_card_of_injective f hf
    _ ≤ (xset B).length := natCard_mem_le _

theorem card_C_ge
    (hF : J4Facts) {A : Subgroup J} (hAP : A ≤ P0)
    (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A) {B : List ℕ} (hBs : B ∈ subs)
    (hB : MaskList (A ⊓ Eg uJ 11) B) (hAE : ¬ A ≤ Eg uJ 11) : 16 ≤ B.length := by
  classical
  have hM := hF.mat
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ Eg uJ 11 := by
    by_contra hcon
    apply hAE
    intro x hx
    by_contra hxE
    exact hcon ⟨x, hx, hxE⟩
  obtain ⟨t, htL, hat⟩ := table_of_mem hM a (hAP haA)
  have ht1 : t ≠ idT := by
    intro ht
    subst ht
    apply haE
    refine centralizer_Hj hM hF a (P0_le_Hj (hAP haA)) (fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have := hat.2 c hc
    rw [actT_idT hc] at this
    calc a * eta uJ 11 c = (a * eta uJ 11 c * a⁻¹) * a := by group
      _ = eta uJ 11 c * a := by rw [this]
  have h16 := rank_ge htL ht1
  have hsub : (Finset.range 2048).image (fun c => actT t c ^^^ c) ⊆ B.toFinset := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
    exact List.mem_toFinset.2 (range_mem hF hn hB haA (hAP haA) hat (Finset.mem_range.1 hc))
  calc 16 ≤ ((Finset.range 2048).image (fun c => actT t c ^^^ c)).card := h16
    _ ≤ B.toFinset.card := Finset.card_le_card hsub
    _ = B.length := List.toFinset_card_of_nodup (nodup_of_pairwise_lt (subs_prop hBs).2.1)

end CFSG.Quasithin.J4Loc
