module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Basic

theorem zU_le_u128 {V V₁ : Subgroup G} : zU128 V V₁ ≤ u128 V V₁ := fun x hx =>
  (mem_centerOf_iff'.1 hx).1

theorem Dg_le_i128 (h1289 : Lemma12_8_9W) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    CFSG.conjugate (zU128 V V₁) g ≤ i128 T L V V₁ := by
  have h := (h1289 G T L V 4 V₁ V₂ hs g hgP hgN).1
  intro d hd
  rw [h]
  exact Subgroup.mem_sup_right (conj_mono' zU_le_u128 g hd)

theorem wc_centralizes_Dg (h1289 : Lemma12_8_9W) (h12813 : Lemma12_8_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) {d : G}
    (hd : d ∈ CFSG.conjugate (zU128 V V₁) g) {w : G} (hw : w ∈ wcSub T L V V₁) :
    d * w * d⁻¹ = w := by
  have hdI := Dg_le_i128 h1289 hs hgP hgN hd
  have hdC := Dg_le_centralizer_V h12813 hs hgP hgN hd
  have hC : wcSub T L V V₁ ≤ Subgroup.centralizer ({d} : Set G) := by
    unfold wcSub
    refine sup_le ?_ ?_
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (mem_centerOf_iff'.1 hc).2 h hdI
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.1 hdC) v (hs.v1.1 hv)).symm
  have h := Subgroup.mem_centralizer_iff.1 (hC hw) d (Set.mem_singleton d)
  calc d * w * d⁻¹ = w * d * d⁻¹ := by rw [h]
    _ = w := by group

theorem wc_normalized {T L V V₁ V₂ : Subgroup G} {y : G}
    (hy1 : y ∈ Subgroup.normalizer (i128 T L V V₁ : Set G))
    (hy2 : y ∈ Subgroup.normalizer (V₁ : Set G)) :
    ∀ x ∈ wcSub T L V V₁, y * x * y⁻¹ ∈ wcSub T L V V₁ := by
  intro x hx
  unfold wcSub at hx ⊢
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact Subgroup.mem_sup_left (conj_centerOf_mem hy1 hz)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hy2 z).1 hz)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem relIndex_wc_zU (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (D : HatModelU (u128 V V₁))
    (hDg4 : Nat.card ↥(D.img (CFSG.conjugate (zU128 V V₁) g)) = 4) :
    (wcSub T L V V₁).relIndex (zU128 V V₁) = 4 := by
  have h := card_zU_eq h1222 h12213 h1289 h12810 h12813 hs hgP hgN D hDg4
  have hwZ : wcSub T L V V₁ ⊓ zU128 V V₁ = wcSub T L V V₁ :=
    inf_eq_left.2 (wcSub_le_zU h1222 h12213 h12810 hs hgP hgN)
  have h1 := Subgroup.relIndex_mul_card (H := wcSub T L V V₁) (K := zU128 V V₁)
  rw [hwZ] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h)

theorem natCard_submodule_two {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (P : Submodule (ZMod 2) M) : Nat.card ↥P = 2 ^ Module.finrank (ZMod 2) P := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥P), ZMod.card]

theorem natCard_inf_eq_submodule {I W : Subgroup G} [IsMulCommutative ↥I]
    [Module (ZMod 2) (Additive ↥I)] [Finite (Additive ↥I)] (P : Submodule (ZMod 2) (Additive ↥I))
    (hfix : ∀ i (hi : i ∈ I), i ∈ W ↔ (Additive.ofMul ⟨i, hi⟩ : Additive ↥I) ∈ P) :
    Nat.card ↥(I ⊓ W) = Nat.card ↥P := by
  let f : ↥(I ⊓ W) → ↥P := fun x =>
    ⟨Additive.ofMul ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩,
      (hfix _ _).1 (Subgroup.mem_inf.1 x.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : (Additive.ofMul ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩ : Additive ↥I) =
          Additive.ofMul ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩ := congrArg Subtype.val hxy
      have h2 := congrArg (fun m : Additive ↥I => ((Additive.toMul m : ↥I) : G)) h1
      exact Subtype.ext h2
    · intro m
      have hi : ((Additive.toMul m.1 : ↥I) : G) ∈ I := (Additive.toMul m.1 : ↥I).2
      have hmemP : (Additive.ofMul ⟨((Additive.toMul m.1 : ↥I) : G), hi⟩ : Additive ↥I) ∈ P := by
        have e : (Additive.ofMul ⟨((Additive.toMul m.1 : ↥I) : G), hi⟩ : Additive ↥I) = m.1 := rfl
        rw [e]
        exact m.2
      refine ⟨⟨((Additive.toMul m.1 : ↥I) : G), Subgroup.mem_inf.2 ⟨hi, (hfix _ hi).2 hmemP⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem sup_eq_of_card (Z I W : Subgroup G) (hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hIZ : I ≤ Z) (hWZ : W ≤ Z) (hW4 : W.relIndex Z = 4) (hI : Nat.card I = 16)
    (hIW : Nat.card ↥(I ⊓ W) = 4) : I ⊔ W = Z := by
  classical
  let I' : Subgroup ↥Z := I.subgroupOf Z
  let W' : Subgroup ↥Z := W.subgroupOf Z
  have hcomm : ∀ (g : ↥Z) (n : G), n ∈ W → ((g : G) * n * (g : G)⁻¹) = n := by
    intro g n hn
    have := hZc (g : G) g.2 n (hWZ hn)
    rw [this]
    group
  haveI hWn : W'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : ((g * n * g⁻¹ : ↥Z) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hcomm g n hn
    rw [e]
    exact hn⟩
  have hcardZ : Nat.card ↥Z = 4 * Nat.card ↥W := by
    have h1 := Subgroup.relIndex_mul_card (H := W) (K := Z)
    rw [inf_eq_left.2 hWZ, hW4] at h1
    exact h1.symm
  have hcardW' : Nat.card ↥W' = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWZ).toEquiv
  have hcardI' : Nat.card ↥I' = 16 := by
    rw [← hI]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIZ).toEquiv
  have hcardIW' : Nat.card ↥(W' ⊓ I') = 4 := by
    rw [← hIW]
    have e : W' ⊓ I' = (W ⊓ I).subgroupOf Z := by
      ext x
      simp only [W', I', Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [e, inf_comm W I]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hIZ : I ⊓ W ≤ Z)).toEquiv
  have hrelI : W'.relIndex I' = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := W') (K := I')
    rw [hcardIW', hcardI'] at h1
    omega
  have hcardZ' : Nat.card ↥(⊤ : Subgroup ↥Z) = 4 * Nat.card ↥W' := by
    rw [hcardW', ← hcardZ]
    exact Nat.card_congr (Subgroup.topEquiv (G := ↥Z)).toEquiv
  have hK : I' ⊔ W' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.relIndex_mul_card (H := W') (K := I' ⊔ W')
    rw [inf_eq_left.2 le_sup_right] at h1
    have h2 : W'.relIndex (I' ⊔ W') = 4 := by
      rw [Subgroup.relIndex_sup_right, hrelI]
    rw [h2] at h1
    rw [← h1, hcardW', hcardZ]

  apply le_antisymm (sup_le hIZ hWZ)
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Z) ∈ I' ⊔ W' := by rw [hK]; exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hmem
  have hyz' : (y : G) * (z : G) = x := by
    have := congrArg Subtype.val hyz
    simpa using this
  rw [← hyz']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hy))
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hz))

end Basic

end CFSG.Quasithin.H13.C1294
