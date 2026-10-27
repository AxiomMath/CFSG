module

public import CFSG.Quasithin.Background.B19Decomp

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V] {X Φ : Subgroup (MulAut V)}

namespace Setting

variable (hV : ∀ v : V, v ^ 2 = 1) (hS : Setting X Φ)
include hV hS

theorem fix_of_comm {t y : MulAut V} (ht : t ∈ tvSet X Φ)
    (hyF : ∀ z ∈ FOf Φ t, z * y = y * z) (hyt : y * t = t * y) :
    ∀ m ∈ commV (FOf Φ t), y m = m := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq] at hyF ⊢
  rw [commV_eq_commSub]
  exact fix_of_comm_inv hV h.x3 h.x1 h.card_commSub (hyF x (Subgroup.mem_zpowers x)) hyt h.inv

theorem GOf_le_ffJP {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ≤ ffJP {A | IsFFStarMin X A} X :=
  hS.GOf_le_of_forall hV ht fun s hs =>
    le_ffJP (isFFStarMin_zpowers_tv hV hs) (Subgroup.zpowers_le.2 hs.1) (Subgroup.mem_zpowers s)

theorem FAll_le_ffJP : FAll X Φ ≤ ffJP {A | IsFFStarMin X A} X :=
  iSup₂_le fun _ ht => FOf_le_GOf.trans (hS.GOf_le_ffJP hV ht)

theorem mem_centralizer_ffJP {c : MulAut V} (hc : c ∈ Φ) (hct : ∀ t ∈ tvSet X Φ, c * t = t * c) :
    c ∈ Subgroup.centralizer (ffJP {A | IsFFStarMin X A} X : Set (MulAut V)) := by
  have hle : ffJP {A | IsFFStarMin X A} X ≤ Subgroup.centralizer {c} := by
    refine iSup_le fun A => iSup_le fun hA => iSup_le fun _ => ?_
    by_cases hnt : ⁅Φ, A⁆ = ⊥
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ⁅c, a⁆ ∈ ⁅Φ, A⁆ := Subgroup.commutator_mem_commutator hc ha
      rw [hnt, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    · obtain ⟨t, ht, rfl⟩ := hS.exists_tv_of_isFFStarMin hV hA hnt
      refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hct t ht).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem FAll_inf_eq_bot :
    FAll X Φ ⊓ (Φ ⊓ Subgroup.centralizer (ffJP {A | IsFFStarMin X A} X : Set (MulAut V))) =
      ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun f hf => ?_
  obtain ⟨hfF, hfΦ, hfC⟩ := hf
  obtain ⟨hsup, -⟩ := hS.decomp_FAll hV
  have hft : ∀ t ∈ tvSet X Φ, f * t = t * f := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 hfC t
      (hS.GOf_le_ffJP hV ht (mem_GOf (Φ := Φ) (t := t)))).symm
  have hW : commV (FAll X Φ) ≤ fixV (Subgroup.zpowers f) := by
    rw [commV_FAll]
    refine iSup₂_le fun t ht m hm => B1.zpowers_fix ?_
    refine hS.fix_of_comm hV ht (fun z hz => ?_) (hft t ht) m hm
    exact (hS.FOf_central hV ht z hz f hfΦ).symm
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ fixV (FAll X Φ) ⊔ commV (FAll X Φ) := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, hu f hfF, hW hw f (Subgroup.mem_zpowers f)]
  rfl

theorem le_FAll_sup :
    Φ ≤ FAll X Φ ⊔
      (Φ ⊓ Subgroup.centralizer (ffJP {A | IsFFStarMin X A} X : Set (MulAut V))) := by
  classical
  obtain ⟨R, hR, hRinj, hRcov⟩ := exists_reps X Φ
  have key : ∀ S : Finset (MulAut V), S ⊆ R → ∀ f ∈ Φ, ∃ a ∈ ⨆ r ∈ S, FOf Φ r, ∃ c ∈ Φ,
      (∀ r ∈ S, c * r = r * c) ∧ f = a * c := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ f hf
      exact ⟨1, Subgroup.one_mem _, f, hf, by simp, by simp⟩
    | insert r₀ S hr₀ ih =>
      intro hSR f hf
      have hr₀R : r₀ ∈ R := hSR (Finset.mem_insert_self _ _)
      have ht₀ := hR r₀ hr₀R
      obtain ⟨a, ha, c, hcΦ, hcS, rfl⟩ := ih (fun r hr => hSR (Finset.mem_insert_of_mem hr)) f hf
      have hr₀r : ∀ r ∈ S, r₀ * r = r * r₀ := by
        intro r hr
        have hrR : r ∈ R := hSR (Finset.mem_insert_of_mem hr)
        have hne : FOf Φ r₀ ≠ FOf Φ r := fun h => hr₀ (hRinj r₀ hr₀R r hrR h ▸ hr)
        exact hS.pair_tt hV ht₀ (hR r hrR) hne
      set K := Φ ⊓ Subgroup.centralizer (↑S : Set (MulAut V)) with hK
      have hcK : c ∈ K := ⟨hcΦ, Subgroup.mem_centralizer_iff.2 fun r hr => (hcS r hr).symm⟩
      have hτcK : r₀ * c * r₀⁻¹ ∈ K := by
        refine ⟨hS.normal r₀ ht₀.1 c hcΦ, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        have h1 := hr₀r r hr
        have h2 := hcS r hr
        have h3 : r * r₀⁻¹ = r₀⁻¹ * r := by
          calc r * r₀⁻¹ = r₀⁻¹ * (r₀ * r) * r₀⁻¹ := by group
            _ = r₀⁻¹ * (r * r₀) * r₀⁻¹ := by rw [h1]
            _ = r₀⁻¹ * r := by group
        calc r * (r₀ * c * r₀⁻¹) = r₀ * r * c * r₀⁻¹ := by rw [← mul_assoc, ← mul_assoc, ← h1]
          _ = r₀ * c * r * r₀⁻¹ := by rw [mul_assoc r₀ r c, ← h2, ← mul_assoc]
          _ = r₀ * c * r₀⁻¹ * r := by rw [mul_assoc (r₀ * c), h3, ← mul_assoc]
      obtain ⟨i, c', hiΦ, -, hc'Φ, hc'K, hcic, hτi, hτc'⟩ :=
        exists_inv_mul_fix hS.odd (hS.sq_tv hV ht₀) hcΦ hcK (hS.normal r₀ ht₀.1 c hcΦ) hτcK
      have hiF : i ∈ FOf Φ r₀ := hS.inverted hV ht₀ i hiΦ hτi
      refine ⟨a * i, ?_, c', hc'Φ, fun r hr => ?_, by rw [hcic, mul_assoc]⟩
      · rw [Finset.iSup_insert]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hiF)
      · rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · calc c' * r = r * c' * r⁻¹ * r := by rw [hτc']
            _ = r * c' := by group
        · exact (Subgroup.mem_centralizer_iff.1 hc'K.2 r hr).symm
  intro f hf
  obtain ⟨a, ha, c, hcΦ, hcR, rfl⟩ := key R le_rfl f hf
  have haF : a ∈ FAll X Φ := iSup₂_le (fun r hr => FOf_le_FAll (hR r hr)) ha
  have hct : ∀ t ∈ tvSet X Φ, c * t = t * c := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := hRcov t ht
    have hG : GOf Φ t = GOf Φ r := hS.GOf_eq_of_FOf_eq hV ht (hR r hr) hrt
    have htG : t ∈ GOf Φ r := hG ▸ mem_GOf
    have hle : GOf Φ r ≤ Subgroup.centralizer {c} := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hS.FOf_central hV (hR r hr) y hy c hcΦ |>.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcR r hr).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle htG)).symm
  exact Subgroup.mul_mem_sup haF ⟨hcΦ, hS.mem_centralizer_ffJP hV hcΦ hct⟩

theorem part5 {A K : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hKX : K ≤ X)
    (hKA : ⁅K, A⁆ = K) :
    K ≤ ffJP {A | IsFFStarMin X A} X ⊓ Subgroup.centralizer (Φ : Set (MulAut V)) := by
  have hFF : IsFFModule X := ⟨A, hA.1.1, hA.1.2.1, hA.1.2.2.1,
    B1.card_mul_card_fixV_of_isFFStarOffender_ge hA.1⟩
  have hstab := B1_7 hV hFF
  have hAX : A ≤ X := hA.1.1
  have hKJ : K ≤ ffJP {A | IsFFStarMin X A} X := by
    rw [← hKA, Subgroup.commutator_le]
    intro k hk a ha
    rw [commutatorElement_def]
    have h1 : k * a * k⁻¹ ∈ ffJP {A | IsFFStarMin X A} X := by
      have hmem := hstab.2.2.1 A hA k (hKX hk)
      refine le_ffJP hmem ?_ ⟨a, ha, rfl⟩
      rintro _ ⟨b, hb, rfl⟩
      exact X.mul_mem (X.mul_mem (hKX hk) (hAX hb)) (X.inv_mem (hKX hk))
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (le_ffJP hA hAX ha))
  refine le_inf hKJ ?_
  by_cases hnt : ⁅Φ, A⁆ = ⊥
  ·
    have hAC : ∀ a ∈ A, ∀ f ∈ Φ, f * a = a * f := by
      intro a ha f hf
      have h1 : ⁅f, a⁆ ∈ ⁅Φ, A⁆ := Subgroup.commutator_mem_commutator hf ha
      rw [hnt, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    rw [← hKA, Subgroup.commutator_le]
    intro k hk a ha
    rw [commutatorElement_def, Subgroup.mem_centralizer_iff]
    intro f hf
    have hk' : k⁻¹ * f * k ∈ Φ := by
      have := hS.normal k⁻¹ (X.inv_mem (hKX hk)) f hf
      simpa using this
    have h1 : f * (k * a * k⁻¹) = (k * a * k⁻¹) * f := by
      have h2 := hAC a ha _ hk'
      calc f * (k * a * k⁻¹) = k * ((k⁻¹ * f * k) * a) * k⁻¹ := by group
        _ = k * (a * (k⁻¹ * f * k)) * k⁻¹ := by rw [h2]
        _ = (k * a * k⁻¹) * f := by group
    calc f * (k * a * k⁻¹ * a⁻¹) = (k * a * k⁻¹) * f * a⁻¹ := by rw [← mul_assoc, h1]
      _ = (k * a * k⁻¹) * (a⁻¹ * (a * f * a⁻¹)) := by group
      _ = (k * a * k⁻¹) * (a⁻¹ * f) := by
          rw [← hAC a ha f hf]
          group
      _ = k * a * k⁻¹ * a⁻¹ * f := by group
  ·
    obtain ⟨t, ht, rfl⟩ := hS.exists_tv_of_isFFStarMin hV hA hnt
    have hsq := hS.sq_tv hV ht
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
    have hFn : ∀ g : MulAut V, (∀ z ∈ FOf Φ t, g * z = z * g) →
        g ∈ Subgroup.normalizer (FOf Φ t : Set (MulAut V)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hg z hz, mul_inv_cancel_right]
        exact hz
      · intro hz
        have h1 : g⁻¹ * (g * z * g⁻¹) * g = g * z * g⁻¹ := by
          rw [mul_assoc, ← hg _ hz]
          group
        have h2 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rw [← h2, h1]
        exact hz
    have hGt : GOf Φ t ≤ commWith (FOf Φ t) t := by
      refine sup_le (fun y hy => ⟨?_, ?_⟩) (Subgroup.zpowers_le.2 ⟨?_, ?_⟩)
      · exact Subgroup.le_normalizer hy
      · rw [commutatorElement_def]
        have h1 : t * y⁻¹ * t⁻¹ = y := by
          rw [show t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ by group, hS.inv_FOf hV ht y hy, inv_inv]
        have e : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
        rw [e, h1]
        exact Subgroup.mul_mem _ hy hy
      · rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          rw [hS.inv_FOf hV ht z hz]
          exact Subgroup.inv_mem _ hz
        · intro hz
          have h1 := hS.inv_FOf hV ht _ hz
          have h2 : t * (t * z * t⁻¹) * t⁻¹ = z := by
            calc t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t⁻¹ * t⁻¹) := by group
              _ = z := by rw [htinv, hsq]; group
          rw [← h2, h1]
          exact Subgroup.inv_mem _ hz
      · rw [commutatorElement_self]
        exact Subgroup.one_mem _
    have hJ : ffJP {A | IsFFStarMin X A} X ≤ commWith (FOf Φ t) t := by
      refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
      by_cases hntB : ⁅Φ, B⁆ = ⊥
      · intro b hb
        have hbF : ∀ y ∈ FOf Φ t, y * b = b * y := by
          intro y hy
          have h1 : ⁅y, b⁆ ∈ ⁅Φ, B⁆ :=
            Subgroup.commutator_mem_commutator (hS.FOf_le hV ht hy) hb
          rw [hntB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1
        have hb2 : b * b = 1 := by rw [← pow_two]; exact hB.1.2.2.1.2 b hb
        obtain ⟨h1, -⟩ := hS.comm_of_sq hV ht hb2 hbF
        refine ⟨hFn b fun z hz => (hbF z hz).symm, ?_⟩
        rw [commutatorElement_eq_one_iff_mul_comm.2 (h1 t mem_GOf).symm]
        exact Subgroup.one_mem _
      · obtain ⟨t', ht', rfl⟩ := hS.exists_tv_of_isFFStarMin hV hB hntB
        refine Subgroup.zpowers_le.2 ?_
        by_cases heq : FOf Φ t' = FOf Φ t
        · have hG := hS.GOf_eq_of_FOf_eq hV ht' ht heq
          exact hGt (hG ▸ mem_GOf)
        · have htt := hS.pair_tt hV ht ht' (Ne.symm heq)
          have ht'F := hS.pair_tF hV ht ht' (Ne.symm heq)
          refine ⟨hFn t' ht'F, ?_⟩
          rw [commutatorElement_eq_one_iff_mul_comm.2 htt.symm]
          exact Subgroup.one_mem _
    have hKF : K ≤ FOf Φ t := by
      rw [← hKA, Subgroup.commutator_le]
      intro k hk a ha
      rcases eq_one_or_eq_of_mem_zpowers hsq ha with h | h
      · rw [h, commutatorElement_one_right]
        exact Subgroup.one_mem _
      · rw [h]
        exact (hJ (hKJ hk)).2
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact hS.FOf_central hV ht k (hKF hk) f hf

end Setting

end CFSG.Quasithin.B19
