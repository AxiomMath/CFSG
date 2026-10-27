module

public import CFSG.LocalAnalysis.WeakClosure81.W16Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isSylowIn_restrict {p : ℕ} {P A B : Subgroup G} (hP : IsSylowIn p P B)
    (hPA : P ≤ A) (hAB : A ≤ B) : IsSylowIn p P A := by
  refine ⟨hPA, hP.isPGroup, fun hdvd => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P A B hPA hAB]
  exact hdvd.mul_right _

private theorem conj_inf_centralizer {V : Subgroup G} {m xr : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    V ⊓ centralizer ({m⁻¹ * xr * m} : Set G) =
      conjSubgroup (V ⊓ centralizer ({xr} : Set G)) m := by
  ext s
  rw [Subgroup.mem_inf, mem_conjSubgroup_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hsV, hsC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hm s).1 hsV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hcomm : (m⁻¹ * xr * m) * s = s * (m⁻¹ * xr * m) :=
      hsC (m⁻¹ * xr * m) (Set.mem_singleton _)
    calc xr * (m * s * m⁻¹) = m * ((m⁻¹ * xr * m) * s) * m⁻¹ := by group
      _ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * s * m⁻¹) * xr := by group
  · rintro ⟨hsV, hsC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hm s).2 hsV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hcomm : xr * (m * s * m⁻¹) = (m * s * m⁻¹) * xr :=
      hsC xr (Set.mem_singleton _)
    have key : m * ((m⁻¹ * xr * m) * s) * m⁻¹ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by
      calc m * ((m⁻¹ * xr * m) * s) * m⁻¹ = xr * (m * s * m⁻¹) := by group
        _ = (m * s * m⁻¹) * xr := hcomm
        _ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key)

theorem exists_minimal_fam16Q {M V₀ U R : Subgroup G} (hne : ∃ H, Fam16Q M V₀ U R H) :
    ∃ H, Fam16Q M V₀ U R H ∧
      ∀ H' : Subgroup G, H' ≤ H → Fam16Q M V₀ U R H' → H' = H := by
  obtain ⟨H, hH, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {H : Subgroup G | Fam16Q M V₀ U R H} hne
  refine ⟨H, hH, fun H' hle hF' => ?_⟩
  by_contra hne'
  exact hmin H' hF' (lt_of_le_of_ne hle hne')

theorem conjSubgroup_le_conjClosure_of_mem {Z H A : Subgroup G} {g : G} (hg : g ∈ H)
    (hA : A ≤ Z) : conjSubgroup A g ≤ conjClosure Z H := fun y hy => by
  rw [mem_conjSubgroup_iff] at hy
  have h1 := mem_conjClosure (H.inv_mem hg) (hA hy)
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem le_normalizer_cTilde_of_hyp15 {M V₀ V : Subgroup G} (h : Hyp15 M V₀ V) :
    M ≤ normalizer (F11.CTilde M V₀ V : Set G) := by
  have hMleV : M ≤ normalizer (V : Set G) := by
    intro m hm
    rw [h.h6.normalizer_eq]
    exact hm
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
    (cTilde_subgroupOf_normal h.h6.elemAbelian hMleV h.h6.le_normalizer₀)

namespace Fam16Q

variable {M V₀ V U S R H : Subgroup G}

theorem isElemAbelian (h : Cex16 M V₀ V U S) (hQ : Fam16Q M V₀ U R H) :
    IsElemAbelian 2 (conjClosure (U ⊔ V₀) H) := by
  have hUV : U ⊔ V₀ ≤ V := sup_le h.le h.hyp.h6.le
  have hsq : ∀ z ∈ U ⊔ V₀, z ^ 2 = 1 := fun z hz => h.hyp.h6.elemAbelian.2 z (hUV hz)
  have hcomm := hQ.2.2
  unfold conjClosure at hcomm ⊢
  refine IsElemAbelian.closure_of_commute (fun a ha b hb =>
    hcomm a (Subgroup.subset_closure ha) b (Subgroup.subset_closure hb)) ?_
  rintro a ⟨k, hk, z, hz, rfl⟩
  rw [conj_pow, hsq z hz]
  group

theorem le_centralizer (h : Cex16 M V₀ V U S) (hQ : Fam16Q M V₀ U R H) :
    conjClosure (U ⊔ V₀) H ≤ centralizer (U : Set G) := fun i hi => by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact B2F.isElemAbelian_comm (hQ.isElemAbelian h)
    (le_sup_left.trans (le_conjClosure (U ⊔ V₀) H) hu) hi

end Fam16Q

namespace Cex16

variable {M V₀ V U S R H : Subgroup G}

theorem conjClosure_le_S (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hSR : S ≤ R) (hQ : Fam16Q M V₀ U R H) : conjClosure (U ⊔ V₀) H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup G := conjClosure (U ⊔ V₀) H with hI
  have hIe : IsElemAbelian 2 I := hQ.isElemAbelian h
  have hIp : IsPGroup 2 I := B2F.isPGroup_of_isElemAbelian hIe
  have hIC : I ≤ centralizer (U : Set G) := hQ.le_centralizer h
  have hSK : S ≤ centralizer (U : Set G) ⊓ normalizer (I : Set G) :=
    le_inf h.S_le_centralizer fun s hs => le_normalizer_conjClosure _ _ (hQ.1 (hSR hs))
  have hIK : I ≤ centralizer (U : Set G) ⊓ normalizer (I : Set G) :=
    le_inf hIC Subgroup.le_normalizer
  have hSyl : IsSylowIn 2 S (centralizer (U : Set G) ⊓ normalizer (I : Set G)) :=
    isSylowIn_restrict (h.isSylowIn_centralizer h1 hS) hSK inf_le_left
  have hnorm : (I.subgroupOf (centralizer (U : Set G) ⊓ normalizer (I : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIK]
    exact inf_le_right
  exact hSyl.le_of_normal hIK hnorm hIp

theorem exists_B (h152 : Thm152 G) (h : Cex16 M V₀ V U S) {R : Subgroup G} {g : G}
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hVg : conjSubgroup V₀ g ≤ R)
    (hcen : ∀ x ∈ conjSubgroup V₀ g, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = U ⊔ V₀) :
    ∃ B : Subgroup G, B ≤ R ∧ (∃ m ∈ M, B = conjSubgroup (conjSubgroup V₀ g) m) ∧
      ¬ U ≤ centralizer (B : Set G) ∧
      ∀ x ∈ B, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = V ⊓ centralizer (B : Set G) := by
  classical
  have hH := h.hyp
  have hex : ∃ m₀ ∈ M, ∃ u ∈ U, m₀ * u * m₀⁻¹ ∉ U ⊔ V₀ := by
    by_contra hcon
    have hall : ∀ m₀ ∈ M, ∀ u ∈ U, m₀ * u * m₀⁻¹ ∈ U ⊔ V₀ := fun m₀ hm₀ u hu => by
      by_contra hn
      exact hcon ⟨m₀, hm₀, u, hu, hn⟩
    obtain ⟨u₀, hu₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.ne_bot
    have huU : (u₀ : G) ∈ U := u₀.2
    have hune : (u₀ : G) ≠ 1 := fun e => hu₀ne (Subtype.ext e)
    have huV : (u₀ : G) ∈ V := h.le huU
    have huV₀ : (u₀ : G) ∉ V₀ := by
      intro hmem
      have hmem' : (u₀ : G) ∈ U ⊓ V₀ := ⟨huU, hmem⟩
      rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem'
      exact hune hmem'
    have hVA : V ≤ U ⊔ V₀ := by
      rw [hH.h6.conjGenerated hH.ne_bot _ huV huV₀]
      exact (Subgroup.closure_le (K := U ⊔ V₀)).2 fun x hx => by
        obtain ⟨m₀, hm₀, rfl⟩ := hx
        exact hall m₀ hm₀ _ huU
    exact h.sup_ne_top h152 (le_antisymm (sup_le h.le hH.h6.le) hVA)
  obtain ⟨m₀, hm₀M, u₁, hu₁U, hm₀u₁⟩ := hex
  set V₂ : Subgroup G := conjSubgroup V₀ g with hV₂def
  have hV₂C : V₂ ≤ F11.CTilde M V₀ V := hVg.trans hR.le
  have hMnormC : M ≤ normalizer (F11.CTilde M V₀ V : Set G) := le_normalizer_cTilde_of_hyp15 hH
  set B₁ : Subgroup G := conjSubgroup V₂ m₀ with hB₁def
  have hB₁C : B₁ ≤ F11.CTilde M V₀ V := by
    have h1 := E3.conjSubgroup_mono_left m₀ hV₂C
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 (hMnormC hm₀M)] at h1
  have hV₂2 : IsPGroup 2 V₂ := E3.isPGroup_conjSubgroup (hH.isPGroup.to_le hH.h6.le) g
  have hB₁2 : IsPGroup 2 B₁ := E3.isPGroup_conjSubgroup hV₂2 m₀
  obtain ⟨d, hdC, hdB₁R⟩ := E3.exists_le_conj_of_isSylowIn hR hB₁C hB₁2
  have hdM : d ∈ M := cTilde_le_M M V₀ V hdC
  set m : G := m₀ * d⁻¹ with hmdef
  have hmM : m ∈ M := M.mul_mem hm₀M (M.inv_mem hdM)
  have hVnorm : m ∈ normalizer (V : Set G) := by
    rw [hH.h6.normalizer_eq]
    exact hmM
  set B : Subgroup G := conjSubgroup B₁ d⁻¹ with hBdef
  have hB_eq : B = conjSubgroup V₂ m := by
    rw [hBdef, hB₁def, hmdef, conjSubgroup_conjSubgroup]
  have hBR : B ≤ R := by
    rw [hBdef]
    calc conjSubgroup B₁ d⁻¹ ≤ conjSubgroup (conjSubgroup R d) d⁻¹ :=
          E3.conjSubgroup_mono_left d⁻¹ hdB₁R
      _ = conjSubgroup R (d * d⁻¹) := conjSubgroup_conjSubgroup R d d⁻¹
      _ = R := by rw [mul_inv_cancel, conjSubgroup_one]
  have hxeq : ∀ x ∈ B, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = conjSubgroup (U ⊔ V₀) m := by
    intro x hx hx1
    rw [hB_eq, mem_conjSubgroup_iff] at hx
    have hy1 : m * x * m⁻¹ ≠ 1 := fun e => hx1 (by
      have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [this, e]
      group)
    have hT := conj_inf_centralizer (V := V) (xr := m * x * m⁻¹) hVnorm
    rw [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at hT
    rw [hT, hcen _ hx hy1]
  have hBne : B ≠ ⊥ := by
    intro hb
    apply hH.ne_bot
    rw [Subgroup.eq_bot_iff_card]
    have hc : Nat.card B = Nat.card V₀ := by
      rw [hB_eq, hV₂def, E3.card_conjSubgroup, E3.card_conjSubgroup]
    rw [← hc, hb]
    exact Subgroup.card_bot
  obtain ⟨b₀, hb₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hb₀1 : (b₀ : G) ≠ 1 := fun e => hb₀ (Subtype.ext e)
  have hCB : V ⊓ centralizer (B : Set G) = conjSubgroup (U ⊔ V₀) m := by
    apply le_antisymm
    · rw [← hxeq b₀ b₀.2 hb₀1]
      exact inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.2 b₀.2))
    · intro s hs
      have hsV : s ∈ V := by
        have := hs
        rw [← hxeq b₀ b₀.2 hb₀1] at this
        exact this.1
      refine Subgroup.mem_inf.2 ⟨hsV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      by_cases hb1 : b = 1
      · rw [hb1, one_mul, mul_one]
      · have hs' : s ∈ V ⊓ centralizer ({b} : Set G) := by
          rw [hxeq b hb hb1]
          exact hs
        exact Subgroup.mem_centralizer_iff.1 hs'.2 b (Set.mem_singleton b)
  have hnotU : ¬ U ≤ centralizer (B : Set G) := by
    intro hUc
    have hUX : U ≤ conjSubgroup (U ⊔ V₀) m := by
      rw [← hCB]
      exact le_inf h.le hUc
    have hmu : m * u₁ * m⁻¹ ∈ U ⊔ V₀ := mem_conjSubgroup_iff.1 (hUX hu₁U)
    have hd'C : d⁻¹ ∈ F11.CTilde M V₀ V := (F11.CTilde M V₀ V).inv_mem hdC
    have hw : d⁻¹ * u₁ * d * u₁⁻¹ ∈ V₀ := by
      have h' := (FourteenTwo.mem_cTilde_iff_comm.1 hd'C).2.2 u₁ (h.le hu₁U)
      simpa using h'
    have hw' : m₀ * (d⁻¹ * u₁ * d * u₁⁻¹) * m₀⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 (hH.h6.le_normalizer₀ hm₀M) _).1 hw
    have hsplit : m₀ * u₁ * m₀⁻¹ =
        (m₀ * (d⁻¹ * u₁ * d * u₁⁻¹) * m₀⁻¹)⁻¹ * (m * u₁ * m⁻¹) := by
      rw [hmdef]
      group
    apply hm₀u₁
    rw [hsplit]
    exact (U ⊔ V₀).mul_mem ((U ⊔ V₀).inv_mem (Subgroup.mem_sup_right hw')) hmu
  exact ⟨B, hBR, ⟨m, hmM, hB_eq⟩, hnotU, fun x hx hx1 => (hxeq x hx hx1).trans hCB.symm⟩

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
