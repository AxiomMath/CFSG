module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLbLayer
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCentralizes
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBstar
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

private theorem inv_mul_centralizes_of_conj {G : Type} [Group G] {L : Subgroup G} {c t : G}
    (htl : ∀ l ∈ L, c * l * c⁻¹ = t * l * t⁻¹) :
    ∀ l ∈ L, t⁻¹ * c * l = l * (t⁻¹ * c) := by
  intro l hl
  have h1 : c * l = t * l * t⁻¹ * c := by
    calc c * l = c * l * c⁻¹ * c := by group
      _ = t * l * t⁻¹ * c := by rw [htl l hl]
  calc t⁻¹ * c * l = t⁻¹ * (c * l) := by group
    _ = t⁻¹ * (t * l * t⁻¹ * c) := by rw [h1]
    _ = l * (t⁻¹ * c) := by group

private theorem centralizer_dPrime_inf_L (hxL : ∀ l ∈ L, x * l = l * x) :
    L ⊓ Subgroup.centralizer (dPrime x φ₁ φ₂ : Set G) =
      Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) ⊓ L := by
  have hCD : Subgroup.centralizer (dPrime x φ₁ φ₂ : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) := by
    rw [dPrime, Subgroup.centralizer_closure]
    apply le_antisymm
    · refine le_inf (Subgroup.centralizer_le ?_) (Subgroup.centralizer_le ?_)
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        simp
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        simp
    · intro g hg
      obtain ⟨hx, hb⟩ := Subgroup.mem_inf.mp hg
      rw [Subgroup.mem_centralizer_iff] at hx hb ⊢
      intro h hh
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact hx _ (by simp)
      · exact hb _ (by simp)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    fun l hl => Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; subst hy; exact hxL l hl)
  rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx, inf_comm]

include h

theorem stdSub_lb :
    LargeEvenStdSub p B x L (dPrime x φ₁ φ₂) (sl3four.map φ₁) := by
  obtain ⟨hcomm, hexp, hxB, hyB, hx1, hy1, hxL, hyK, hxnK, hcent⟩ := h.basic
  have hp3 : p = 3 := h.nbr.2.1
  have hbBs : bElt φ₁ φ₂ ∈ Bs := bElt_mem_bs h
  have hb3 : bElt φ₁ φ₂ ^ 3 = 1 := bElt_pow_three h
  have hbnot : bElt φ₁ φ₂ ∉ Subgroup.zpowers x := bElt_not_mem_zpowers_x h
  have hb1 : bElt φ₁ φ₂ ≠ 1 := fun h1 => hbnot (by rw [h1]; exact Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hexp x hxB
  have hxord : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx3 hx1
  have hbord : orderOf (bElt φ₁ φ₂) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hb3 hb1
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hcardb : Nat.card (Subgroup.zpowers (bElt φ₁ φ₂)) = 3 := by
    rw [Nat.card_zpowers, hbord]
  have hDleBs : dPrime x φ₁ φ₂ ≤ Bs := by
    rw [dPrime, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxB
    · exact hbBs
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers (bElt φ₁ φ₂) = ⊥ := by
    have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers (bElt φ₁ φ₂) ≤ Subgroup.zpowers x :=
      inf_le_left
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (bElt φ₁ φ₂) : Subgroup G) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hcardx] at h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hge : Nat.card (Subgroup.zpowers x) ≤
          Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (bElt φ₁ φ₂) : Subgroup G) := by
        rw [h3, hcardx]
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (bElt φ₁ φ₂) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle hge
      have hle' : Subgroup.zpowers x ≤ Subgroup.zpowers (bElt φ₁ φ₂) := heq ▸ inf_le_right
      have heq2 : Subgroup.zpowers x = Subgroup.zpowers (bElt φ₁ φ₂) :=
        Subgroup.eq_of_le_of_card_ge hle' (by rw [hcardb, hcardx])
      exact hbnot (heq2.symm ▸ Subgroup.mem_zpowers (bElt φ₁ φ₂))
  have hcardD : Nat.card (dPrime x φ₁ φ₂) = p ^ 2 := by
    have hcommxb : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers (bElt φ₁ φ₂),
        a * c = c * a := fun a ha c hc =>
      hcomm a (Subgroup.zpowers_le.mpr hxB ha) c (Subgroup.zpowers_le.mpr hbBs hc)
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) (Subgroup.zpowers (bElt φ₁ φ₂)) hcommxb).1
    rw [hdisj, Subgroup.card_bot, mul_one, hcardx, hcardb] at h1
    have h1' : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers (bElt φ₁ φ₂) : Subgroup G) = 9 := by
      simpa using h1
    rw [dPrime, closure_pair_eq_sup, h1', hp3]
    norm_num
  have hDleB : dPrime x φ₁ φ₂ ≤ B := hDleBs.trans (le_of_eq (bs_eq h))
  unfold LargeEvenStdSub
  refine ⟨?_, ?_⟩
  · unfold LargeEvenStdSubPre
    refine ⟨hDleB, ?_, hcardD, ?_, ?_, ?_, ?_⟩
    · unfold CFSG.Open.IsElemAbelian
      refine ⟨?_, ?_⟩
      · exact ⟨⟨fun a b => Subtype.ext (hcomm a.1 (hDleBs a.2) b.1 (hDleBs b.2))⟩⟩
      · intro z hz
        rw [hp3]
        exact hexp z (hDleBs hz)
    · rw [dPrime]
      exact Subgroup.subset_closure (Set.mem_insert x {bElt φ₁ φ₂})
    · rw [centralizer_dPrime_inf_L hxL]
      exact lb_layer h
    · rw [centralizer_dPrime_inf_L hxL]
      exact isComponentOf_lb h
    · apply le_antisymm
      · refine le_inf hDleB ?_
        rw [dPrime, Subgroup.closure_le]
        rintro z (rfl | rfl)
        · refine Subgroup.mem_centralizer_iff.mpr ?_
          intro k hk
          obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
          have hkL : φ₁ s ∈ L := by rw [← h.coords.range₁]; exact ⟨s, rfl⟩
          exact (hxL (φ₁ s) hkL).symm
        · refine Subgroup.mem_centralizer_iff.mpr ?_
          intro k hk
          obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
          have hζs : zeta5 * s * zeta5⁻¹ = s := by
            have hc := Subgroup.mem_centralizer_singleton_iff.mp (sl3four_le_centralizer hs)
            rw [← hc]; group
          have hbconj := bElt_act_L h s
          rw [hζs] at hbconj
          show φ₁ s * bElt φ₁ φ₂ = bElt φ₁ φ₂ * φ₁ s
          have hb' : bElt φ₁ φ₂ * φ₁ s = φ₁ s * bElt φ₁ φ₂ := by
            calc bElt φ₁ φ₂ * φ₁ s
                = bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ * bElt φ₁ φ₂ := by group
              _ = φ₁ s * bElt φ₁ φ₂ := by rw [hbconj]
          exact hb'.symm
      · intro c hc
        obtain ⟨hcB, hcK⟩ := Subgroup.mem_inf.mp hc
        have hcBs : c ∈ Bs := by rw [bs_eq h]; exact hcB
        obtain ⟨t, ht, htl⟩ := h.coords.actL c hcBs
        have htcent : t ∈ Subgroup.zpowers zeta5 := by
          rw [← centralizes_sl3four_iff ht]
          intro s hs
          have hsL : φ₁ s ∈ L := by rw [← h.coords.range₁]; exact ⟨s, rfl⟩
          have hsK : φ₁ s ∈ sl3four.map φ₁ := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
          have hcKs : c * φ₁ s = φ₁ s * c :=
            (Subgroup.mem_centralizer_iff.mp hcK (φ₁ s) hsK).symm
          have h1 : φ₁ t * φ₁ s * (φ₁ t)⁻¹ = φ₁ s := by
            rw [← htl (φ₁ s) hsL, hcKs]
            group
          have h2 : t * s * t⁻¹ = s := by
            apply h.coords.inj₁
            rw [map_mul, map_mul, map_inv]
            exact h1
          calc t * s = t * s * t⁻¹ * t := by group
            _ = s * t := by rw [h2]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htcent
        have hw_memD : wElt φ₂ ∈ dPrime x φ₁ φ₂ := by
          have hwx : wElt φ₂ ∈ Subgroup.zpowers x := by
            rw [zpowers_x h]
            exact Subgroup.mem_zpowers _
          exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert x {bElt φ₁ φ₂})) hwx
        have hphiZ_memD : φ₁ zeta5 ∈ dPrime x φ₁ φ₂ := by
          have hbD : bElt φ₁ φ₂ ∈ dPrime x φ₁ φ₂ :=
            Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
          have hbdef : bElt φ₁ φ₂ = φ₁ zeta5 * wElt φ₂ := rfl
          have hφζ : φ₁ zeta5 = bElt φ₁ φ₂ * (wElt φ₂)⁻¹ := by rw [hbdef]; group
          rw [hφζ]
          exact Subgroup.mul_mem _ hbD (Subgroup.inv_mem _ hw_memD)
        have hphit_memD : φ₁ t ∈ dPrime x φ₁ φ₂ := by
          have hk' : φ₁ t = (φ₁ zeta5) ^ k := by rw [← hk, map_zpow]
          rw [hk']
          exact Subgroup.zpow_mem _ hphiZ_memD k
        have hc'memBs : (φ₁ t)⁻¹ * c ∈ Bs :=
          Bs.mul_mem (Bs.inv_mem (h.torusL_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩))) hcBs
        have hc'z : (φ₁ t)⁻¹ * c ∈ Subgroup.zpowers x :=
          hcent _ hc'memBs (inv_mul_centralizes_of_conj htl)
        have hc'D : (φ₁ t)⁻¹ * c ∈ dPrime x φ₁ φ₂ :=
          Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert x {bElt φ₁ φ₂})) hc'z
        have hc_eq : c = φ₁ t * ((φ₁ t)⁻¹ * c) := by group
        rw [hc_eq]
        exact Subgroup.mul_mem _ hphit_memD hc'D
  · intro _
    refine IOneOrthEnd.not_largeEvenSmall_of_seven_dvd ?_
    rw [Subgroup.card_map_of_injective h.coords.inj₁, card_sl3four]
    norm_num

end GGHalfCtx

end CFSG.StandardType

end
