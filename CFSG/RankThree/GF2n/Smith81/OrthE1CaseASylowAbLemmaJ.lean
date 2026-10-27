module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbRank
import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
import CFSG.RankThree.GF2n.Smith81.OrthE1CtStructure

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {K : Type} [Field K]

theorem lemmaJ_two_eq_zero (S : QSpace K) (h8 : Module.finrank K S.E = 8) : (2 : K) = 0 := by
  have hsymm : ∀ e f : S.E, S.B e f = S.B f e := by
    intro e f
    have h1 := S.Qf_add e f
    have h2 := S.Qf_add f e
    rw [add_comm f e] at h2
    linear_combination h2 - h1
  have hB2 : ∀ e f : S.E, (2 : K) * S.B e f = 0 := by
    intro e f
    have h := S.alt (e + f)
    simp only [map_add, LinearMap.add_apply, S.alt e, S.alt f] at h
    linear_combination h + hsymm e f
  obtain ⟨e0, he0⟩ : ∃ e : S.E, e ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by rw [h8]; norm_num)
  obtain ⟨f0, hf0⟩ : ∃ f : S.E, S.B e0 f ≠ 0 := by
    by_contra hcon
    exact he0 (S.nondeg e0 fun f => not_not.mp (not_exists.mp hcon f))
  exact (mul_eq_zero.mp (hB2 e0 f0)).resolve_right hf0

theorem lemmaJ_finrank_map_add_inf_ker {M : Type} [AddCommGroup M] [Module K M]
    [Module.Finite K M] (A : M →ₗ[K] M) (W : Submodule K M) :
    Module.finrank K ↥(W.map A) + Module.finrank K ↥(LinearMap.ker A ⊓ W) =
      Module.finrank K ↥W := by
  have hfin := LinearMap.finrank_range_add_finrank_ker (A.domRestrict W)
  have hrange : LinearMap.range (A.domRestrict W) = W.map A := by
    rw [show A.domRestrict W = A.comp W.subtype from rfl, LinearMap.range_comp,
      Submodule.range_subtype]
  have hker : LinearMap.ker (A.domRestrict W) =
      Submodule.comap W.subtype (LinearMap.ker A ⊓ W) := by
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf]
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe
    (inf_le_right : LinearMap.ker A ⊓ W ≤ W)).finrank_eq] at hfin
  exact hfin

theorem lemmaJ_coeff_eq_zero (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (h8 : Module.finrank K S.E = 8) (hV4 : Module.finrank K V = 4)
    (T : S.E →ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e))
    (hrk : Module.finrank K (V.map (T - 1)) ≤ 1)
    {c : K} (hT2 : ∀ e, T (T e) = e + c • β e) : c = 0 := by
  have h2 : (2 : K) = 0 := lemmaJ_two_eq_zero S h8
  have hdouble : ∀ x : S.E, x + x = 0 := fun x => by
    rw [← two_smul K x, h2, zero_smul]
  set N : S.E →ₗ[K] S.E := T - 1 with hNdef
  have hNe : ∀ e, N e = T e - e := fun e => by
    rw [hNdef, LinearMap.sub_apply, Module.End.one_apply]
  have hNN : ∀ e, N (N e) = c • β e := by
    intro e
    simp only [hNe, map_sub, hT2]
    rw [show e + c • β e - T e - (T e - e) = c • β e + ((e - T e) + (e - T e)) by abel,
      hdouble, add_zero]
  by_contra hc
  have hNNeq : N ∘ₗ N = c • β := LinearMap.ext fun e => hNN e
  have hrNN : LinearMap.range (N ∘ₗ N) = V := by
    rw [hNNeq, LinearMap.range_smul β c hc, ctS_beta_range_eq S h8 hV4 hβ]
  have hVN : V ≤ LinearMap.range N := by
    intro v hv
    have hv' : v ∈ LinearMap.range (N ∘ₗ N) := by rw [hrNN]; exact hv
    obtain ⟨x, hx⟩ := hv'
    exact LinearMap.mem_range.mpr ⟨N x, hx⟩
  have h1 := lemmaJ_finrank_map_add_inf_ker N V
  have h2' := lemmaJ_finrank_map_add_inf_ker N (LinearMap.range N)
  have hmapN : (LinearMap.range N).map N = V := by
    rw [← hrNN, LinearMap.range_comp]
  have h3 := LinearMap.finrank_range_add_finrank_ker N
  have h4 : Module.finrank K ↥(LinearMap.ker N ⊓ V) ≤ Module.finrank K ↥(LinearMap.ker N) :=
    Submodule.finrank_mono inf_le_left
  have h5 : Module.finrank K ↥(LinearMap.ker N ⊓ V) ≤
      Module.finrank K ↥(LinearMap.ker N ⊓ LinearMap.range N) :=
    Submodule.finrank_mono (inf_le_inf_left _ hVN)
  rw [hmapN] at h2'
  omega

theorem lemmaJ (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (h8 : Module.finrank K S.E = 8) (hV4 : Module.finrank K V = 4)
    (hTS : S.IsTS V)
    (T : S.E →ₗ[K] S.E) (hTQ : ∀ e, S.Qf (T e) = S.Qf e) (hTβ : ∀ e, T (β e) = β (T e))
    (hT2 : ∀ e, T (T e) = e) (hrk : Module.finrank K (V.map (T - 1)) = 1) :
    ∃ μ : K, Module.finrank K
      (LinearMap.range (T ∘ₗ (LinearMap.id + μ • β) - 1)) = 2 := by
  have h2 : (2 : K) = 0 := lemmaJ_two_eq_zero S h8
  have hdouble : ∀ x : S.E, x + x = 0 := fun x => by
    rw [← two_smul K x, h2, zero_smul]
  set N : S.E →ₗ[K] S.E := T - 1 with hNdef
  have hNe : ∀ e, N e = T e - e := fun e => by
    rw [hNdef, LinearMap.sub_apply, Module.End.one_apply]
  have hsymm : ∀ e f : S.E, S.B e f = S.B f e := by
    intro e f
    linear_combination (-1 : K) * KFLin.B_swap S e f + S.B e f * h2
  have hBβ : ∀ e f : S.E, S.B e (β f) = S.B f (β e) := by
    intro e f
    have h := hβ.alt (e + f)
    simp only [map_add, LinearMap.add_apply, hβ.alt e, hβ.alt f] at h
    linear_combination h - S.B f (β e) * h2
  have hTiso : ∀ e f : S.E, S.B (T e) (T f) = S.B e f := by
    intro e f
    rw [KFLin.B_eq_Qf S, KFLin.B_eq_Qf S, ← map_add, hTQ, hTQ, hTQ]
  have hNβ : ∀ e, N (β e) = β (N e) := fun e => by
    simp only [hNe, map_sub, hTβ]
  have hNV : ∀ v ∈ V, N v ∈ V := by
    intro v hv
    apply hβ.ker
    rw [← hNβ v, hβ.kills v hv, map_zero]
  have hNN : ∀ e, N (N e) = 0 := fun e => by
    simp only [hNe, map_sub, hT2]
    rw [show e - T e - (T e - e) = (e - T e) + (e - T e) by abel, hdouble]
  obtain ⟨a, ha0, hNVa, v₀, hv₀, hv₀a⟩ : ∃ a : S.E, a ≠ 0 ∧ (∀ v ∈ V, ∃ c : K, N v = c • a) ∧
      ∃ v₀ ∈ V, N v₀ = a := by
    obtain ⟨a', ha'⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp
      (by omega : 0 < Module.finrank K ↥(V.map N))
    have hspan := (finrank_eq_one_iff_of_nonzero' a' ha').mp hrk
    refine ⟨(a' : S.E), fun h => ha' (Subtype.ext h), fun v hv => ?_,
      Submodule.mem_map.mp a'.2⟩
    obtain ⟨c, hc⟩ := hspan ⟨N v, Submodule.mem_map_of_mem hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hNa : N a = 0 := by
    rw [← hv₀a]
    exact hNN v₀
  have haV : a ∈ V := by
    rw [← hv₀a]
    exact hNV v₀ hv₀
  have hTa : T a = a := by
    have h := hNe a
    rw [hNa] at h
    exact sub_eq_zero.mp h.symm
  have hkerβ : LinearMap.ker β = V := by
    ext e
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hβ.ker e h, fun h => hβ.kills e h⟩
  have hrangeβ : LinearMap.range β = V := ctS_beta_range_eq S h8 hV4 hβ
  obtain ⟨σ, hσ⟩ := beta_section S h8 hV4 hβ
  obtain ⟨F, hFdef⟩ : ∃ F : Submodule K S.E,
      F = LinearMap.BilinForm.orthogonal S.B (Submodule.span K {a}) := ⟨_, rfl⟩
  have hFmem : ∀ e, e ∈ F ↔ S.B e a = 0 := by
    intro e
    rw [hFdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have h1 : S.B a e = 0 := h a (Submodule.mem_span_singleton_self a)
      rw [KFLin.B_swap S a e, h1, neg_zero]
    · intro h n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have h1 : S.B a e = 0 := by linear_combination KFLin.B_swap S a e - h
      rw [map_smul, LinearMap.smul_apply, h1, smul_zero]
  have hF7 : Module.finrank K ↥F = 7 := by
    rw [hFdef]
    have h := LinearMap.BilinForm.finrank_orthogonal (KFLin.B_nondegenerate S)
      (Submodule.span K {a})
    rw [finrank_span_singleton ha0, h8] at h
    exact h
  have hrefl : S.B.IsRefl := by
    intro x y h
    rw [hsymm y x]
    exact h
  have hForth : LinearMap.BilinForm.orthogonal S.B F = Submodule.span K {a} := by
    rw [hFdef]
    exact LinearMap.BilinForm.orthogonal_orthogonal (KFLin.B_nondegenerate S) hrefl _
  have hFperp : ∀ x : S.E, (∀ f ∈ F, S.B f x = 0) → x ∈ Submodule.span K {a} := by
    intro x hx
    rw [← hForth]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr hx
  have hVF : V ≤ F := fun v hv => (hFmem v).mpr (KFLin.B_zero_of_isTS S hTS hv haV)
  have hNeF : ∀ e, e ∈ F → N e ∈ V := by
    intro e he
    refine KFLin.perp_le S hTS h8 hV4 (N e) ?_
    intro v hv
    obtain ⟨c, hc⟩ := hNVa v hv
    have hTea : S.B (T e) a = 0 := by
      have h := hTiso e a
      rw [hTa] at h
      rw [h]
      exact (hFmem e).mp he
    have h1 : S.B (N e) v + S.B (T e) (N v) = 0 := by
      rw [hNe e, hNe v]
      simp only [map_sub, LinearMap.sub_apply, hTiso]
      ring
    rw [hc, map_smul, hTea, smul_zero, add_zero] at h1
    exact h1
  have hchar : ∀ e, N e ∈ V → e ∈ F := by
    intro e he
    rw [hFmem]
    have ha_eq : a = T v₀ - v₀ := by
      rw [← hv₀a, hNe]
    have hkey : S.B e (T v₀ - v₀) = S.B (N e) v₀ := by
      rw [hNe e]
      simp only [map_sub, LinearMap.sub_apply]
      rw [← hTiso e (T v₀), hT2]
    rw [ha_eq, hkey]
    exact KFLin.B_zero_of_isTS S hTS he hv₀
  obtain ⟨b, hb⟩ : ∃ b : S.E, β b = a := by
    have h : a ∈ LinearMap.range β := by
      rw [hrangeβ]
      exact haV
    exact LinearMap.mem_range.mp h
  have hbF : b ∈ F := (hFmem b).mpr (by rw [← hb]; exact hβ.alt b)
  have hbV : b ∉ V := fun h => ha0 (by rw [← hb, hβ.kills b h])
  have hb0 : b ≠ 0 := fun h => ha0 (by rw [← hb, h, map_zero])
  have hNβF : ∀ e ∈ F, N (β e) = 0 := fun e he => by
    rw [hNβ e]
    exact hβ.kills _ (hNeF e he)
  have hTβF : ∀ e ∈ F, T (β e) = β e := fun e he => by
    have h := hNe (β e)
    rw [hNβF e he] at h
    exact sub_eq_zero.mp h.symm
  have hself : ∀ e ∈ F, S.B e (N e) = 0 := fun e he => by
    have h1 := S.Qf_add e (N e)
    have h2' : e + N e = T e := by
      rw [hNe]
      abel
    rw [h2', hTQ, hTS (N e) (hNeF e he)] at h1
    linear_combination -h1
  have hsymN : ∀ e ∈ F, ∀ f ∈ F, S.B e (N f) = S.B f (N e) := by
    intro e he f hf
    have h := hself (e + f) (F.add_mem he hf)
    simp only [map_add, LinearMap.add_apply, hself e he, hself f hf] at h
    linear_combination h - S.B f (N e) * h2
  have hfinNV : Module.finrank K ↥(LinearMap.ker N ⊓ V) = 3 := by
    have h := lemmaJ_finrank_map_add_inf_ker N V
    rw [hrk, hV4] at h
    omega
  have hfinβF : Module.finrank K ↥(F.map β) = 3 := by
    have h := lemmaJ_finrank_map_add_inf_ker β F
    have hker_inf : LinearMap.ker β ⊓ F = V := by
      rw [hkerβ, inf_eq_left.mpr hVF]
    rw [hker_inf, hF7, hV4] at h
    omega
  have hmapF : F.map β = LinearMap.ker N ⊓ V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨LinearMap.mem_ker.mpr (hNβF e he), hβ.range e⟩
    · omega
  have hkerNV_le : LinearMap.ker N ⊓ V ≤ F.map β := le_of_eq hmapF.symm
  have hNbspan : N b ∈ Submodule.span K {a} := by
    apply hFperp
    intro f hf
    rw [hsymN f hf b hbF]
    have hNfmem : N f ∈ LinearMap.ker N ⊓ V :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (hNN f), hNeF f hf⟩
    obtain ⟨g, hg, hgf⟩ := hkerNV_le hNfmem
    rw [← hgf, hBβ b g, hb]
    exact (hFmem g).mp hg
  have hbNx : ∀ x ∈ F, S.B b (N x) = 0 := by
    intro x hx
    rw [hsymN b hbF x hx]
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hNbspan
    rw [← hd, map_smul, (hFmem x).mp hx, smul_zero]
  have hW0F : V ⊔ Submodule.span K {b} ≤ F :=
    sup_le hVF ((Submodule.span_singleton_le_iff_mem b F).mpr hbF)
  have hL1 : ∀ w ∈ V ⊔ Submodule.span K {b}, ∀ x ∈ F,
      S.B w (N x) = 0 ∧ S.B w (β x) = 0 := by
    intro w hw x hx
    obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hvN : S.B v (N x) = 0 := KFLin.B_zero_of_isTS S hTS hv (hNeF x hx)
    have hvβ : S.B v (β x) = 0 := KFLin.B_zero_of_isTS S hTS hv (hβ.range x)
    have hbβx : S.B b (β x) = 0 := by
      rw [hBβ b x, hb]
      exact (hFmem x).mp hx
    constructor
    · simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hvN, hbNx x hx, smul_zero, mul_zero, zero_add, add_zero]
    · simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hvβ, hbβx, smul_zero, mul_zero, zero_add, add_zero]
  have hL2 : ∀ x ∈ F, ∀ w ∈ V ⊔ Submodule.span K {b},
      S.B x (N w) = 0 ∧ S.B x (β w) = 0 := by
    intro x hx w hw
    constructor
    · rw [hsymN x hx w (hW0F hw)]
      exact (hL1 w hw x hx).1
    · rw [hBβ x w]
      exact (hL1 w hw x hx).2
  have hω : ∃ f₁ ∈ F, ∃ f₂ ∈ F, S.B f₁ (β f₂) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : F.map β ≤ Submodule.span K {a} := by
      rintro _ ⟨f, hf, rfl⟩
      apply hFperp
      intro g hg
      exact hcon g hg f hf
    have h := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha0, hfinβF] at h
    omega
  obtain ⟨f₁, hf₁, f₂, hf₂, hc0⟩ := hω
  obtain ⟨P, hPdef⟩ : ∃ P : Submodule K S.E, P = Submodule.span K (Set.range ![f₁, f₂]) :=
    ⟨_, rfl⟩
  have hli : LinearIndependent K ![f₁, f₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h1 : S.B f₁ (β (s • f₁ + t • f₂)) = 0 := by
        rw [hst]
        simp
      simp only [map_add, map_smul, smul_eq_mul, hβ.alt f₁, mul_zero, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hc0
    have hs : s = 0 := by
      have h2' : S.B (s • f₁ + t • f₂) (β f₂) = 0 := by
        rw [hst]
        simp
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hβ.alt f₂, mul_zero, add_zero] at h2'
      exact (mul_eq_zero.mp h2').resolve_right hc0
    exact ⟨hs, ht⟩
  have hPfin : Module.finrank K ↥P = 2 := by
    rw [hPdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hPF : P ≤ F := by
    rw [hPdef, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hf₁
    · simpa using hf₂
  have hPmem : ∀ p ∈ P, ∃ c0 c1 : K, c0 • f₁ + c1 • f₂ = p := by
    intro p hp
    rw [hPdef] at hp
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hp
    exact ⟨c 0, c 1, by rw [Fin.sum_univ_two] at hc; exact hc⟩
  have hWP : (V ⊔ Submodule.span K {b}) ⊓ P = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxP⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c0, c1, rfl⟩ := hPmem x hxP
    have h1 : S.B (c0 • f₁ + c1 • f₂) (β f₂) = 0 := (hL1 _ hxW f₂ hf₂).2
    have h2' : S.B f₁ (β (c0 • f₁ + c1 • f₂)) = 0 := (hL2 f₁ hf₁ _ hxW).2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hβ.alt f₂, hβ.alt f₁, mul_zero, zero_add, add_zero] at h1 h2'
    have hc0' : c0 = 0 := (mul_eq_zero.mp h1).resolve_right hc0
    have hc1' : c1 = 0 := (mul_eq_zero.mp h2').resolve_right hc0
    simp [hc0', hc1']
  have hVb : V ⊓ Submodule.span K {b} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxV, hxb⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxb
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply hbV
      have hb' : b = c⁻¹ • (c • b) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hb']
      exact V.smul_mem c⁻¹ hxV
  have hW0fin : Module.finrank K ↥(V ⊔ Submodule.span K {b}) = 5 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span K {b})
    rw [hVb, finrank_bot, hV4, finrank_span_singleton hb0] at h
    omega
  have hFeq : (V ⊔ Submodule.span K {b}) ⊔ P = F := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hW0F hPF)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V ⊔ Submodule.span K {b}) P
    rw [hWP, finrank_bot, hW0fin, hPfin] at h
    omega
  have hsplit : ∀ e ∈ F, ∃ w ∈ V ⊔ Submodule.span K {b}, ∃ p ∈ P, e = w + p := by
    intro e he
    rw [← hFeq] at he
    obtain ⟨w, hw, p, hp, hwp⟩ := Submodule.mem_sup.mp he
    exact ⟨w, hw, p, hp, hwp.symm⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : K, S.B f₁ (N f₂) = μ * S.B f₁ (β f₂) :=
    ⟨S.B f₁ (N f₂) / S.B f₁ (β f₂), by rw [div_mul_cancel₀ _ hc0]⟩
  have hd11 : S.B f₁ (N f₁) = μ * S.B f₁ (β f₁) := by
    rw [hself f₁ hf₁, hβ.alt f₁, mul_zero]
  have hd22 : S.B f₂ (N f₂) = μ * S.B f₂ (β f₂) := by
    rw [hself f₂ hf₂, hβ.alt f₂, mul_zero]
  have hd21 : S.B f₂ (N f₁) = μ * S.B f₂ (β f₁) := by
    rw [← hsymN f₁ hf₁ f₂ hf₂, ← hBβ f₁ f₂]
    exact hμ
  have hpp : ∀ p ∈ P, ∀ q ∈ P, S.B p (N q) = μ * S.B p (β q) := by
    intro p hp q hq
    obtain ⟨x0, x1, rfl⟩ := hPmem p hp
    obtain ⟨y0, y1, rfl⟩ := hPmem q hq
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination (x0 * y0) * hd11 + (x0 * y1) * hμ + (x1 * y0) * hd21 + (x1 * y1) * hd22
  have hmain : ∀ e ∈ F, ∀ f ∈ F, S.B e (N f) = μ * S.B e (β f) := by
    intro e he f hf
    obtain ⟨w, hw, p, hp, rfl⟩ := hsplit e he
    obtain ⟨w', hw', q, hq, rfl⟩ := hsplit f hf
    have hpF : p ∈ F := hPF hp
    have hqF : q ∈ F := hPF hq
    have hw'F : w' ∈ F := hW0F hw'
    have k1 := (hL1 w hw w' hw'F).1
    have k2 := (hL1 w hw q hqF).1
    have k3 := (hL2 p hpF w' hw').1
    have k4 := (hL1 w hw w' hw'F).2
    have k5 := (hL1 w hw q hqF).2
    have k6 := (hL2 p hpF w' hw').2
    have k7 := hpp p hp q hq
    simp only [map_add, LinearMap.add_apply]
    linear_combination k7 + k1 + k2 + k3 - μ * k4 - μ * k5 - μ * k6
  have hJ1 : ∀ e, (T ∘ₗ (LinearMap.id + μ • β) - 1) e = N e + μ • T (β e) := by
    intro e
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Module.End.one_apply, map_add, map_smul, hNe]
    abel
  have hββ : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hJβ : ∀ e, (T ∘ₗ (LinearMap.id + μ • β)) (β e) =
      β ((T ∘ₗ (LinearMap.id + μ • β)) e) := by
    intro e
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul, hββ, smul_zero, add_zero, hTβ]
  have hJrange : ∀ e ∈ F, N e + μ • β e ∈ Submodule.span K {a} := by
    intro e he
    apply hFperp
    intro g hg
    rw [map_add, map_smul, smul_eq_mul, hmain g hg e he]
    linear_combination (μ * S.B g (β e)) * h2
  refine ⟨μ, ?_⟩
  have hJV : Submodule.map (T ∘ₗ (LinearMap.id + μ • β) - 1) V = Submodule.span K {a} := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨c, hc⟩ := hNVa v hv
      rw [hJ1, hβ.kills v hv, map_zero, smul_zero, add_zero, hc]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_map.mpr ⟨v₀, hv₀, by
        rw [hJ1, hβ.kills v₀ hv₀, map_zero, smul_zero, add_zero, hv₀a]⟩
  have hJinf : LinearMap.range (T ∘ₗ (LinearMap.id + μ • β) - 1) ⊓ V =
      Submodule.span K {a} := by
    apply le_antisymm
    · rintro x ⟨hxR, hxV⟩
      obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hxR
      rw [hJ1] at hxV ⊢
      have hTβV : T (β e) ∈ V := by
        rw [hTβ e]
        exact hβ.range _
      have hNeV : N e ∈ V := by
        have h := V.sub_mem hxV (V.smul_mem μ hTβV)
        rwa [add_sub_cancel_right] at h
      rw [hTβF e (hchar e hNeV)]
      exact hJrange e (hchar e hNeV)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range.mpr ⟨v₀, ?_⟩, haV⟩
      rw [hJ1, hβ.kills v₀ hv₀, map_zero, smul_zero, add_zero, hv₀a]
  rw [finrank_range_sub_one_split S hβ σ hσ (T ∘ₗ (LinearMap.id + μ • β)) hJβ, hJV, hJinf,
    finrank_span_singleton ha0]

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end


