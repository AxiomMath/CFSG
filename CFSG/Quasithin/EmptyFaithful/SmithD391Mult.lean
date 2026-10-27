module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Model
public import CFSG.Quasithin.Background.F918N6
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B51SumOffenders
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.FFC5Final
public import CFSG.Quasithin.Background.FFC6U
public import CFSG.Quasithin.Background.FFC7B
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.EmptyFaithful.S153ZQ
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.EmptyFaithful.SmithD391Decomp
public import CFSG.Quasithin.EmptyFaithful.SmithD391Twist
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {X : Type} [CommGroup X]

theorem fixed_top_eq_fixV (F : Subgroup (MulAut X)) :
    XMod.fixed ↥F (⊤ : Subgroup X) = fixV F := by
  ext x
  simp only [XMod.mem_fixed, Subgroup.mem_top, true_and, mem_fixV, Subtype.forall]
  rfl

theorem nB_eq_rk_sub (F : Subgroup (MulAut X)) (U : Subgroup X) :
    nB F U = rk ↥U - rk ↥(U ⊓ fixV F) := by
  unfold nB
  rw [fixed_top_eq_fixV]

theorem nB_top_eq_rkIdx [Finite X] (F : Subgroup (MulAut X)) :
    nB F (⊤ : Subgroup X) = rkIdx (fixV F) := by
  rw [nB_eq_rk_sub, top_inf_eq, rk_top]
  have := rk_add_rkIdx (fixV F)
  omega

section Summands

variable {K : Subgroup (MulAut X)} {U₁ U₂ S : Subgroup X}

theorem iso_of_equiv {S U : Subgroup X} (hS : ∀ k ∈ K, ∀ w ∈ S, k w ∈ S)
    (e : ↥S ≃* ↥U) (he : ∀ (k : ↥K) (w : ↥S), ((e ⟨(k : MulAut X) w, hS k k.2 w w.2⟩ : ↥U) : X) =
      (k : MulAut X) (e w : X)) : XMod.Iso ↥K S U := by
  refine ⟨e, fun k l l' hl => ?_⟩
  have h1 : (⟨(k : MulAut X) l, hS k k.2 l l.2⟩ : ↥S) = l' := Subtype.ext hl
  rw [← h1, he]
  rfl

theorem eq_or_eq_or_iso (hsum : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (hK₁ : ∀ k ∈ K, ∀ u ∈ U₁, k u ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ u ∈ U₂, k u ∈ U₂)
    (hirr₁ : ∀ J : Subgroup X, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₁ → J = ⊥ ∨ J = U₁)
    (hirr₂ : ∀ J : Subgroup X, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₂ → J = ⊥ ∨ J = U₂)
    (hS : XMod.IsIrr ↥K S) :
    S = U₁ ∨ S = U₂ ∨ (XMod.Iso ↥K S U₁ ∧ XMod.Iso ↥K S U₂) := by
  have hSinv : ∀ k ∈ K, ∀ w ∈ S, k w ∈ S := fun k hk w hw => hS.1 ⟨k, hk⟩ w hw
  have hSne : S ≠ ⊥ := hS.2.1.ne'
  have hle : ∀ U : Subgroup X, (∀ k ∈ K, ∀ u ∈ U, k u ∈ U) →
      (∀ J : Subgroup X, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U → J = ⊥ ∨ J = U) →
      S ⊓ U ≠ ⊥ → S = U := by
    intro U hKU hirrU hne
    have hinv : XMod.IsInv ↥K (S ⊓ U) := fun k w hw => ⟨hSinv k k.2 w hw.1, hKU k k.2 w hw.2⟩
    rcases hS.2.2 (S ⊓ U) hinv bot_le inf_le_left with h | h
    · exact absurd h hne
    · have hSU : S ≤ U := h ▸ inf_le_right
      exact (hirrU S hSinv hSU).resolve_left hSne
  by_cases h1 : S ⊓ U₁ = ⊥
  · by_cases h2 : S ⊓ U₂ = ⊥
    · right; right
      obtain ⟨e₂, he₂⟩ := n6_equiv_proj hsum hinf hK₁ hK₂ hirr₂ hSinv hSne h1
      obtain ⟨e₁, he₁⟩ := n6_equiv_proj (by rw [sup_comm]; exact hsum)
        (by rw [inf_comm]; exact hinf) hK₂ hK₁ hirr₁ hSinv hSne h2
      exact ⟨iso_of_equiv hSinv e₁ he₁, iso_of_equiv hSinv e₂ he₂⟩
    · exact Or.inr (Or.inl (hle U₂ hK₂ hirr₂ h2))
  · exact Or.inl (hle U₁ hK₁ hirr₁ h1)

theorem summands_eq {V V' : Subgroup X} (hsum : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (hK₁ : ∀ k ∈ K, ∀ u ∈ U₁, k u ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ u ∈ U₂, k u ∈ U₂)
    (hirr₁ : ∀ J : Subgroup X, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₁ → J = ⊥ ∨ J = U₁)
    (hirr₂ : ∀ J : Subgroup X, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₂ → J = ⊥ ∨ J = U₂)
    (hV : XMod.IsIrr ↥K V) (hV' : XMod.IsIrr ↥K V') (hVV' : V ⊓ V' = ⊥)
    (hnot : ¬ XMod.Iso ↥K V' V) :
    (V = U₁ ∧ V' = U₂) ∨ (V = U₂ ∧ V' = U₁) := by
  have hU₁inv : XMod.IsInv ↥K U₁ := fun k u hu => hK₁ k k.2 u hu
  have hU₂inv : XMod.IsInv ↥K U₂ := fun k u hu => hK₂ k k.2 u hu
  have hVne : V ≠ ⊥ := hV.2.1.ne'
  rcases eq_or_eq_or_iso hsum hinf hK₁ hK₂ hirr₁ hirr₂ hV with h1 | h1 | ⟨h1a, h1b⟩ <;>
    rcases eq_or_eq_or_iso hsum hinf hK₁ hK₂ hirr₁ hirr₂ hV' with h2 | h2 | ⟨h2a, h2b⟩
  · exfalso; apply hVne; rw [← inf_idem V]; nth_rewrite 2 [h1]; rw [← h2]; exact hVV'
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (by rw [h1]; exact h2a) hnot
  · exact Or.inr ⟨h1, h2⟩
  · exfalso; apply hVne; rw [← inf_idem V]; nth_rewrite 2 [h1]; rw [← h2]; exact hVV'
  · exact absurd (by rw [h1]; exact h2b) hnot
  · exact absurd (by rw [h2]; exact XMod.Iso.symm hV.1 h1a) hnot
  · exact absurd (by rw [h2]; exact XMod.Iso.symm hV.1 h1b) hnot
  · exact absurd (h2a.trans (XMod.Iso.symm hV.1 h1a)) hnot

end Summands

section Inner

variable {n : ℕ} {H : Subgroup (MulAut X)} {U₁ U₂ : Subgroup X}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥H}

theorem mem_of_mem_stabSub (hn : 0 < n) (hU : IsIntDirect U₁ U₂ ⊤)
    (hR₁ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U₁ ⊥ π)
    (hR₂ : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U₂ ⊥ π) {f : MulAut X}
    (hfn : ∀ l ∈ H, f * l * f⁻¹ ∈ H) (hf₁ : f ∈ stabSub U₁) (hf₂ : f ∈ stabSub U₂) : f ∈ H := by
  obtain ⟨g, hg⟩ := exists_eq_of_mulAut_nat hR₁ (resHom U₁ ⟨f, hf₁⟩)
  set c : MulAut X := ((π g : ↥H) : MulAut X)⁻¹ * f with hcdef
  have hπg₁ : ((π g : ↥H) : MulAut X) ∈ stabSub U₁ := by
    intro u
    exact ⟨fun h => by simpa using hR₁.2.2.2.1 (π g)⁻¹ _ h, fun h => hR₁.2.2.2.1 (π g) u h⟩
  have hπg₂ : ((π g : ↥H) : MulAut X) ∈ stabSub U₂ := by
    intro u
    exact ⟨fun h => by simpa using hR₂.2.2.2.1 (π g)⁻¹ _ h, fun h => hR₂.2.2.2.1 (π g) u h⟩
  have hc₁ : ∀ u ∈ U₁, c u = u := by
    intro u hu
    have h1 := hg ⟨u, hu⟩
    rw [resHom_apply] at h1
    rw [hcdef, MulAut.mul_apply, show f u = ((π g : ↥H) : MulAut X) u from h1.symm]
    exact MulAut.inv_apply_self _ _ _
  have hcU₂ : c ∈ stabSub U₂ := (stabSub U₂).mul_mem ((stabSub U₂).inv_mem hπg₂) hf₂
  have hcn : ∀ l ∈ H, c * l * c⁻¹ ∈ H := by
    intro l hl
    have h1 := hfn l hl
    have h2 : c * l * c⁻¹ = ((π g : ↥H) : MulAut X)⁻¹ * (f * l * f⁻¹) *
        ((π g : ↥H) : MulAut X) := by
      rw [hcdef]; group
    rw [h2]
    exact H.mul_mem (H.mul_mem (H.inv_mem (π g).2) h1) (π g).2
  have hcc : ∀ l ∈ H, c * l = l * c := by
    intro l hl
    have hk : c * l * c⁻¹ * l⁻¹ ∈ H := H.mul_mem (hcn l hl) (H.inv_mem hl)
    have hc₁' : ∀ u ∈ U₁, c⁻¹ u = u := fun u hu => by
      nth_rewrite 1 [← hc₁ u hu]
      exact MulAut.inv_apply_self _ _ _
    have htriv : ∀ u ∈ U₁, (c * l * c⁻¹ * l⁻¹) u = u := by
      intro u hu
      have hlu : l⁻¹ u ∈ U₁ := hR₁.2.2.2.1 ⟨l⁻¹, H.inv_mem hl⟩ u hu
      have hllu : l (l⁻¹ u) ∈ U₁ := hR₁.2.2.2.1 ⟨l, hl⟩ _ hlu
      simp only [MulAut.mul_apply]
      rw [hc₁' _ hlu, hc₁ _ hllu, MulAut.apply_inv_self]
    have h1 := B51Sum.eq_one_of_realizesVia_nat hR₁ hk htriv
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨h, hh⟩ := exists_eq_of_mulAut_dual hR₂ (resHom U₂ ⟨c, hcU₂⟩)
  have hhu : ∀ w ∈ U₂, ((π h : ↥H) : MulAut X) w = c w := fun w hw => by
    have := hh ⟨w, hw⟩
    rw [resHom_apply] at this
    exact this
  have hπinj : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hR₁
  have hcomm₂ : ∀ g' : ↥(StatedSL n (ZMod 2)), ∀ u ∈ U₂,
      (((π h : ↥H) : MulAut X) * ((π g' : ↥H) : MulAut X)) u =
        (((π g' : ↥H) : MulAut X) * ((π h : ↥H) : MulAut X)) u := by
    intro g' u hu
    have hgu : ((π g' : ↥H) : MulAut X) u ∈ U₂ := hR₂.2.2.2.1 (π g') u hu
    simp only [MulAut.mul_apply]
    rw [hhu _ hgu, hhu u hu]
    have := congrArg (fun φ : MulAut X => φ u) (hcc _ (π g').2)
    simpa [MulAut.mul_apply] using this
  have hhc : h ∈ Subgroup.center ↥(StatedSL n (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g'
    apply hπinj
    rw [map_mul, map_mul]
    have hk : ((π h : ↥H) : MulAut X) * ((π g' : ↥H) : MulAut X) *
        (((π g' : ↥H) : MulAut X) * ((π h : ↥H) : MulAut X))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (π h).2 (π g').2) (H.inv_mem (H.mul_mem (π g').2 (π h).2))
    have htriv : ∀ u ∈ U₂, (((π h : ↥H) : MulAut X) * ((π g' : ↥H) : MulAut X) *
        (((π g' : ↥H) : MulAut X) * ((π h : ↥H) : MulAut X))⁻¹) u = u := by
      intro u hu
      set w := (((π g' : ↥H) : MulAut X) * ((π h : ↥H) : MulAut X))⁻¹ u with hw
      have hwU : w ∈ U₂ := by
        rw [hw, mul_inv_rev, MulAut.mul_apply]
        exact hR₂.2.2.2.1 (π h)⁻¹ _ (hR₂.2.2.2.1 (π g')⁻¹ u hu)
      rw [MulAut.mul_apply, hcomm₂ g' w hwU, hw, MulAut.apply_inv_self]
    have h1 := B51Sum.eq_one_of_realizesVia_dualNat hR₂ hk htriv
    rw [mul_inv_eq_one] at h1
    exact Subtype.ext h1.symm
  rw [center_statedSL_two_eq_bot hn, Subgroup.mem_bot] at hhc
  have hc₂ : ∀ u ∈ U₂, c u = u := fun u hu => by
    rw [← hhu u hu, hhc, map_one]
    rfl
  have hc1 : c = 1 := by
    ext x
    have hx : x ∈ U₁ ⊔ U₂ := by rw [hU.1]; trivial
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, hc₁ u₁ hu₁, hc₂ u₂ hu₂]
    rfl
  have hf : f = ((π g : ↥H) : MulAut X) := by
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1.symm
  rw [hf]
  exact (π g).2

end Inner

section Ineq

variable [Finite X] {n : ℕ} {H : Subgroup (MulAut X)} {U₁ U₂ : Subgroup X}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥H}

theorem two_mul_lt_three_mul_add {α β : ℕ} (hα : 1 ≤ α) (hαβ : α + β ≤ 5) :
    2 * (α * β) < 3 * (α + β) := by
  have hα5 : α ≤ 5 := by omega
  have hβ4 : β ≤ 4 := by omega
  interval_cases α <;> interval_cases β <;> omega

theorem two_mul_one_add_lt {n α : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) (hα : α ≤ n) :
    2 * (1 + α * (n - α)) < 3 * (n + α) := by
  interval_cases n <;> interval_cases α <;> omega

theorem two_mul_rk_lt_of_le (hX : ∀ x : X, x ^ 2 = 1) (hn5 : n ≤ 5) (hU : IsIntDirect U₁ U₂ ⊤)
    (hR₁ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U₁ ⊥ π)
    (hR₂ : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U₂ ⊥ π)
    {F : Subgroup (MulAut X)} (hFH : F ≤ H) (hF1 : F ≠ ⊥) (hFq : IsQuadratic F) :
    2 * rk ↥F < 3 * rkIdx (fixV F) := by
  obtain ⟨e₁, -⟩ := exists_natEquiv hR₁
  obtain ⟨e₂, -⟩ := exists_dualEquiv hR₂
  have hrk₁ : rk ↥U₁ = n := rk_eq_of_equiv e₁
  have hrk₂ : rk ↥U₂ = n := rk_eq_of_equiv e₂
  have hfaith : ∀ f ∈ F, (∀ u ∈ U₁, f u = u) → f = 1 :=
    fun f hf h => B51Sum.eq_one_of_realizesVia_nat hR₁ (hFH hf) h
  have hFU₁ : XMod.IsInv ↥F U₁ := fun f u hu => hR₁.2.2.2.1 ⟨f, hFH f.2⟩ u hu
  have hFU₂ : XMod.IsInv ↥F U₂ := fun f u hu => hR₂.2.2.2.1 ⟨f, hFH f.2⟩ u hu
  have h1 := rk_le_mul_of_faithful hX hfaith
  have hcU : commSub U₁ F ≤ U₁ ⊓ fixV F := by
    refine le_inf ?_ ?_
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨f, hf, u, hu, rfl⟩
      exact U₁.mul_mem (hFU₁ ⟨f, hf⟩ u hu) (U₁.inv_mem hu)
    · refine le_trans ?_ hFq
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨f, hf, u, -, rfl⟩
      exact Subgroup.subset_closure ⟨f, hf, u, rfl⟩
  have hβ := rk_mono hcU
  have hdual := rk_fixV_dual_add_rk_commSub_le hX hR₁ hR₂ hFH
  have hsplit : rkIdx (fixV F) =
      (rk ↥U₁ - rk ↥(U₁ ⊓ fixV F)) + (rk ↥U₂ - rk ↥(U₂ ⊓ fixV F)) := by
    rw [← nB_top_eq_rkIdx, ← hU.1, nB_sup_of_disjoint F hFU₁ hFU₂ hU.2, nB_eq_rk_sub,
      nB_eq_rk_sub]
  have hle₁ : rk ↥(U₁ ⊓ fixV F) ≤ rk ↥U₁ := rk_mono inf_le_left
  have hle₂ : rk ↥(U₂ ⊓ fixV F) ≤ rk ↥U₂ := rk_mono inf_le_left
  have hα1 : 1 ≤ rk ↥U₁ - rk ↥(U₁ ⊓ fixV F) := by
    by_contra h0
    have h0' : rk ↥U₁ ≤ rk ↥(U₁ ⊓ fixV F) := by omega
    have heq : U₁ ⊓ fixV F = U₁ := eq_of_le_of_rk_le hX inf_le_left h0'
    apply hF1
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    refine hfaith f hf fun u hu => ?_
    have : u ∈ U₁ ⊓ fixV F := by rw [heq]; exact hu
    exact (mem_fixV.1 this.2) f hf
  have key := two_mul_lt_three_mul_add (β := rk ↥(commSub U₁ F)) hα1 (by omega)
  have h2 : 2 * rk ↥F ≤ 2 * ((rk ↥U₁ - rk ↥(U₁ ⊓ fixV F)) * rk ↥(commSub U₁ F)) := by omega
  omega

theorem two_mul_rk_lt_of_swap (hX : ∀ x : X, x ^ 2 = 1) (hn : 1 ≤ n) (hn5 : n ≤ 5)
    {V : Subgroup X} (hrkV : rk ↥V = n) {F : Subgroup (MulAut X)} (hFe : IsElemAbelian2 F)
    (hFq : IsQuadratic F) {f₀ : MulAut X} (hf₀ : f₀ ∈ F)
    (hsum : V ⊔ V.map f₀.toMonoidHom = ⊤) (hinf : V ⊓ V.map f₀.toMonoidHom = ⊥)
    (hsplit : ∀ x ∈ F, x ∈ F ⊓ stabSub V ∨ f₀⁻¹ * x ∈ F ⊓ stabSub V) (hf₀n : f₀ ∉ stabSub V) :
    2 * rk ↥F < 3 * rkIdx (fixV F) := by
  have hinv : XMod.IsInv ↥(F ⊓ stabSub V) V := fun c v hv => ((c.2.2 v).2 hv)
  have hsmul : f₀ • V = V.map f₀.toMonoidHom := rfl
  have h1 := nB_index_two (Q := X) hf₀ (hFe.2 f₀ hf₀) hFe.1 inf_le_left hsplit hinv
    (by rw [hsmul]; exact hinf)
  rw [hsmul, hsum, nB_top_eq_rkIdx] at h1
  have h2 := rk_index_two hf₀ hFe.1 hFe.2 inf_le_left (fun h => hf₀n h.2) hsplit
  have hcV : ∀ c ∈ (F ⊓ stabSub V), ∀ v ∈ V, c v ∈ V := fun c hc v hv => (hc.2 v).2 hv
  have hfaith : ∀ c ∈ (F ⊓ stabSub V), (∀ v ∈ V, c v = v) → c = 1 := by
    intro c hc htriv
    ext x
    have hx : x ∈ V ⊔ V.map f₀.toMonoidHom := by rw [hsum]; trivial
    obtain ⟨v, hv, w, hw, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨v', hv', rfl⟩ := hw
    have hcomm : c * f₀ = f₀ * c := hFe.1 c hc.1 f₀ hf₀
    have h3 : c (f₀ v') = f₀ v' := by
      have := congrArg (fun φ : MulAut X => φ v') hcomm
      simp only [MulAut.mul_apply] at this
      rw [this, htriv v' hv']
    rw [map_mul, htriv v hv]
    show v * c (f₀ v') = v * f₀ v'
    rw [h3]
  have hq : commSub V (F ⊓ stabSub V) ≤ fixV (F ⊓ stabSub V) := by
    refine le_trans ?_ (le_trans hFq ?_)
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨c, hc, v, -, rfl⟩
      exact Subgroup.subset_closure ⟨c, hc.1, v, rfl⟩
    · intro x hx
      exact mem_fixV.2 fun c hc => (mem_fixV.1 hx) c hc.1
  have h3 := rk_le_mul_of_quadratic hX hcV hq hfaith
  rw [nB_eq_rk_sub] at h1
  rw [hrkV] at h3 h1
  have hle : rk ↥(V ⊓ fixV (F ⊓ stabSub V)) ≤ rk ↥V := rk_mono inf_le_left
  rw [hrkV] at hle
  have key := two_mul_one_add_lt hn hn5 (Nat.sub_le n (rk ↥(V ⊓ fixV (F ⊓ stabSub V))))
  have h4 : 2 * rk ↥F ≤ 2 * (1 + (n - rk ↥(V ⊓ fixV (F ⊓ stabSub V))) *
      (n - (n - rk ↥(V ⊓ fixV (F ⊓ stabSub V))))) := by
    omega
  omega

end Ineq

section Main

variable [Finite X] {Lb Tb : Subgroup (MulAut X)} {V : Subgroup X} {t : MulAut X}

omit [Finite X] in
theorem mem_stabSub_map_of_split (htT : t ∈ Tb) (htn : t ∉ stabSub V)
    (hsplit : ∀ s ∈ Tb, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) {f : MulAut X} (hfT : f ∈ Tb)
    (hfV : f ∈ stabSub V) : f ∈ stabSub (V.map t.toMonoidHom) := by
  have ht2 : t * t ∈ stabSub V := by
    rcases hsplit (t * t) (Tb.mul_mem htT htT) with h | h
    · exact h
    · rw [inv_mul_cancel_left] at h
      exact absurd h htn
  have hconj : t⁻¹ * f * t ∈ stabSub V := by
    rcases hsplit (t⁻¹ * f * t) (Tb.mul_mem (Tb.mul_mem (Tb.inv_mem htT) hfT) htT) with h | h
    · exact h
    · exfalso
      apply htn
      have h3 : f * t ∈ stabSub V := by
        have := (stabSub V).mul_mem ht2 h
        rwa [show t * t * (t⁻¹ * (t⁻¹ * f * t)) = f * t by group] at this
      have := (stabSub V).mul_mem ((stabSub V).inv_mem hfV) h3
      rwa [inv_mul_cancel_left] at this
  rw [mem_stabSub_iff_map_eq, ← map_mul_aut', show f * t = t * (t⁻¹ * f * t) by group,
    map_mul_aut', mem_stabSub_iff_map_eq.1 hconj]

theorem two_mul_rk_lt_of_quadratic (hX : ∀ x : X, x ^ 2 = 1)
    (hTn : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (hV : XMod.IsIrr ↥Lb V) (htT : t ∈ Tb)
    (hsum : V ⊔ V.map t.toMonoidHom = ⊤) (hinf : V ⊓ V.map t.toMonoidHom = ⊥)
    (hnot : ¬ XMod.Iso ↥Lb (V.map t.toMonoidHom) V)
    (hsplit : ∀ s ∈ Tb, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V)
    {n : ℕ} (hSND : SumNatDual Lb ⊤ n)
    {F : Subgroup (MulAut X)} (hFT : F ≤ Tb) (hFe : IsElemAbelian2 F) (hF1 : F ≠ ⊥)
    (hFq : IsQuadratic F) :
    2 * rk ↥F < 3 * rkIdx (fixV F) := by
  obtain ⟨hn, π, U₁, U₂, hU, hR₁, hR₂⟩ := hSND
  have hd : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn5 : n ≤ 5 := by rcases hn with rfl | rfl <;> norm_num
  have hirr₁ : ∀ J : Subgroup X, (∀ k ∈ Lb, ∀ w ∈ J, k w ∈ J) → J ≤ U₁ → J = ⊥ ∨ J = U₁ :=
    fun J hJ hJU => FFC.irr_of_binaryNatural hd
      (⟨ZMod 2, inferInstance, inferInstance, by simp, π, hR₁⟩ : BinaryNaturalSL Lb U₁ ⊥ n 1)
      J hJ bot_le hJU
  have hirr₂ := n6_irr_of_dualNat hd hR₂
  have hK₁ : ∀ k ∈ Lb, ∀ u ∈ U₁, k u ∈ U₁ := fun k hk u hu => hR₁.2.2.2.1 ⟨k, hk⟩ u hu
  have hK₂ : ∀ k ∈ Lb, ∀ u ∈ U₂, k u ∈ U₂ := fun k hk u hu => hR₂.2.2.2.1 ⟨k, hk⟩ u hu
  have hNt : XMod.Normalizes ↥Lb ↥Tb X := normalizes_of_conj Lb Tb hTn
  have hV' : XMod.IsIrr ↥Lb (V.map t.toMonoidHom) := isIrr_smul hNt ⟨t, htT⟩ hV
  have htn : t ∉ stabSub V := by
    intro h
    have h1 := mem_stabSub_iff_map_eq.1 h
    rw [h1, inf_idem] at hinf
    exact hV.2.1.ne' hinf
  have hsum' := summands_eq hU.1 hU.2 hK₁ hK₂ hirr₁ hirr₂ hV hV' hinf hnot
  obtain ⟨e₁, -⟩ := exists_natEquiv hR₁
  have hrkV : rk ↥V = n := by
    rcases hsum' with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact rk_eq_of_equiv e₁
    · rw [h1]
      obtain ⟨e₂, -⟩ := exists_dualEquiv hR₂
      exact rk_eq_of_equiv e₂
  by_cases hFV : F ≤ stabSub V
  ·
    have hFV' : ∀ f ∈ F, f ∈ stabSub (V.map t.toMonoidHom) :=
      fun f hf => mem_stabSub_map_of_split htT htn hsplit (hFT hf) (hFV hf)
    have hFL : F ≤ Lb := by
      intro f hf
      have hfn : ∀ l ∈ Lb, f * l * f⁻¹ ∈ Lb := hTn f (hFT hf)
      rcases hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mem_of_mem_stabSub (by omega) hU hR₁ hR₂ hfn (h1 ▸ hFV hf) (h2 ▸ hFV' f hf)
      · exact mem_of_mem_stabSub (by omega) hU hR₁ hR₂ hfn (h2 ▸ hFV' f hf) (h1 ▸ hFV hf)
    exact two_mul_rk_lt_of_le hX hn5 hU hR₁ hR₂ hFL hF1 hFq
  ·
    obtain ⟨f₀, hf₀, hf₀n⟩ : ∃ f₀ ∈ F, f₀ ∉ stabSub V := by
      by_contra hcon
      push Not at hcon
      exact hFV hcon
    have ht₀ : t⁻¹ * f₀ ∈ stabSub V := (hsplit f₀ (hFT hf₀)).resolve_left hf₀n
    have hmap : V.map f₀.toMonoidHom = V.map t.toMonoidHom := by
      rw [show f₀ = t * (t⁻¹ * f₀) by group, map_mul_aut', mem_stabSub_iff_map_eq.1 ht₀]
    have hsplitF : ∀ x ∈ F, x ∈ F ⊓ stabSub V ∨ f₀⁻¹ * x ∈ F ⊓ stabSub V := by
      intro x hx
      rcases hsplit x (hFT hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · right
        refine ⟨F.mul_mem (F.inv_mem hf₀) hx, ?_⟩
        have := (stabSub V).mul_mem ((stabSub V).inv_mem ht₀) h
        rwa [show (t⁻¹ * f₀)⁻¹ * (t⁻¹ * x) = f₀⁻¹ * x by group] at this
    exact two_mul_rk_lt_of_swap hX (by omega) hn5 hrkV hFe hFq hf₀ (hmap ▸ hsum) (hmap ▸ hinf)
      hsplitF hf₀n

theorem two_mul_rk_lt (hX : ∀ x : X, x ^ 2 = 1)
    (hTn : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (hV : XMod.IsIrr ↥Lb V) (htT : t ∈ Tb)
    (hsum : V ⊔ V.map t.toMonoidHom = ⊤) (hinf : V ⊓ V.map t.toMonoidHom = ⊥)
    (hnot : ¬ XMod.Iso ↥Lb (V.map t.toMonoidHom) V)
    (hsplit : ∀ s ∈ Tb, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V)
    {n : ℕ} (hSND : SumNatDual Lb ⊤ n)
    {A : Subgroup (MulAut X)} (hAT : A ≤ Tb) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    2 * rk ↥A < 3 * rkIdx (fixV A) := by
  by_contra hcon
  push Not at hcon
  have hcardA : Nat.card ↥A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun x : ↥A =>
      Subtype.ext (by simpa using hAe.2 _ x.2))
  have hcardX : Nat.card X = 2 ^ rk X := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hX)
  have hsplitX := rk_add_rkIdx (fixV A)
  have hA2 : IsA2 Tb A := ⟨hAT, hA1, hAe⟩
  have hle : Nat.card X ≤ Nat.card ↥A * Nat.card ↥(fixV A) := by
    rw [hcardA, card_eq_two_pow hX (fixV A), hcardX, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below hA2
    (Nat.card ↥A * Nat.card ↥(fixV A) - Nat.card X) (by omega)
  obtain ⟨F, hFB, hF, hFq, hFc, -, -⟩ := exists_quadratic_offender_le hX hB
  have hcardF : Nat.card ↥F = 2 ^ rk ↥F :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun x : ↥F =>
      Subtype.ext (by simpa using hF.2.2.1.2 _ x.2))
  have hineq : 2 ^ (rk ↥A + rk ↥(fixV A)) ≤ 2 ^ (rk ↥F + rk ↥(fixV F)) := by
    rw [pow_add, pow_add, ← hcardA, ← hcardF, ← card_eq_two_pow hX (fixV A),
      ← card_eq_two_pow hX (fixV F), hFc]
    omega
  have hineq' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hineq
  have hFA : rk ↥F ≤ rk ↥A := rk_mono (hFB.trans hBA)
  have hsplitF := rk_add_rkIdx (fixV F)
  have hcore := two_mul_rk_lt_of_quadratic hX hTn hV htT hsum hinf hnot hsplit hSND
    ((hFB.trans hBA).trans hAT) hF.2.2.1 hF.2.1 hFq
  omega

end Main

end CFSG.Quasithin.SmithD391
