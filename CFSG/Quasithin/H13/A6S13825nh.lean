module

public import CFSG.Quasithin.H13.A6S13825nf
public import CFSG.Quasithin.H13.A6S13825ng
public import CFSG.Quasithin.H13.A6S13825na

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

open L4Ind L13825 CFSG.LieType.BorelTits in
open scoped commutatorElement in
theorem false_of_A6 (h21 : Lem13821) (h16 : Lem13816)
    (h1334 : Stmt13_3_4) (h18 : Lem13818Four) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V))
    (hKn : IsPSL 4 2 1 ↥(S.KSt H K)) (hhat : ¬ IsHatA6 L) (hTK' : ¬ T ≤ K ⊔ pCoreOf 2 H) :
    False := by
  classical
  have hF98 := hS.hF H hH
  have hF := hF98.toHypF91
  set U := conjClosure S.V3 H with hU
  have hab := isElemAbelian_UH hS hH
  have : IsMulCommutative ↥U := hab.1
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := hab.2
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1TH : S.L1 ⊔ T ≤ H := sup_le hL1H hTH
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  obtain ⟨ρ, hρs, hρk, hρL1, hρT, hρU, hρQ, tτ, htτT, htτ⟩ :=
    aut_coords h21 h16 h1334 hS hH hK hKn hhat hTK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := sigmaH (S := S) hH with hσ
  have hσ1 : ∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := sigmaH_eq_one_iff hH hF
  have hkerσ : ρ.ker ≤ σ.ker := fun h hh => by
    rw [MonoidHom.mem_ker] at hh ⊢
    exact (hσ1 h).2 ((hρk h).1 hh)
  set Φ := ρ.liftOfRightInverse (Function.surjInv hρs) (Function.rightInverse_surjInv hρs)
    ⟨σ, hkerσ⟩ with hΦdef
  have hΦ : ∀ h : ↥H, Φ (ρ h) = σ h := fun h =>
    ρ.liftOfRightInverse_comp_apply _ _ ⟨σ, hkerσ⟩ h
  obtain ⟨f, hf1, hfσ, hfs⟩ :
      ∃ f : ↥U →* Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U),
        (∀ x, f x = 1 ↔ (x : G) ∈ fsuV1 T V) ∧
        (∀ h u, σ h (f u) = f (Setup.rho U H hHU h u)) ∧ Function.Surjective f :=
    ⟨InternalSec.secMk _, A6Mod.secMk_eq_one_iff, fun _ _ => rfl,
      InternalSec.secMk_surjective _⟩
  have hsq : ∀ x : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U), x * x = 1 := fun x => by
    rw [← pow_two]
    exact sec_sq_eq_one hU2 x
  have hinv : ∀ x : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U), x⁻¹ = x :=
    fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hU2' : ∀ x : ↥U, x * x = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hU2 _ x.2)
  have hfeq : ∀ x y : ↥U, f x = f y ↔ (x : G) * (y : G) ∈ fsuV1 T V := by
    intro x y
    rw [← Subgroup.coe_mul, ← hf1, map_mul]
    constructor
    · intro h
      rw [h, hsq]
    · intro h
      rw [← hinv (f y)]
      exact eq_inv_of_mul_eq_one_left h
  have hσρ : ∀ (h : ↥H) (u : ↥U), σ h (f u) = f ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hHU h.2) _).mp u.2⟩ := fun h u => by
    rw [hfσ]
    congr 1
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hgH : (g : G) ∈ H := hL1H hgL
  have hg2H : (g : G) * g ∈ H := H.mul_mem hgH hgH
  set v₂ : ↥U := ⟨S.v2, S.v2_mem_UH H⟩ with hv₂
  have hnV1 : ∀ k ∈ H, k * S.v2 * k⁻¹ ∉ fsuV1 T V := by
    intro k hk hmem
    apply S.v2_not_mem_V1
    have := (Subgroup.mem_normalizer_iff.mp (hHV1 (H.inv_mem hk)) _).mp hmem
    simpa [mul_assoc] using this
  set m₀ := f v₂ with hm₀
  have hm₁ : σ ⟨g, hgH⟩ m₀ = f ⟨(g : G) * S.v2 * (g : G)⁻¹, le_conjClosure _ _
      (S.conj_v2_mem_V3 hg)⟩ := hσρ _ _
  have hg2 : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) = (g : G) * g := by
    rw [pow_two]
    rfl
  have hv2g2 := S.v2_mul_conj hg
  rw [hg2] at hv2g2
  have hm₂ : σ ⟨(g : G) * g, hg2H⟩ m₀ = f ⟨(g : G) * g * S.v2 * ((g : G) * g)⁻¹,
      hv2g2 ▸ U.mul_mem (S.v2_mem_UH H) (le_conjClosure _ _ (S.conj_v2_mem_V3 hg))⟩ :=
    hσρ _ _
  obtain ⟨c, hcQ, hc⟩ := hρL1 ⟨g, hgH⟩ hgL
  have hΦc : Φ (MulAut.conj c) m₀ = σ ⟨g, hgH⟩ m₀ := by rw [← hc, hΦ]
  have hΦcc : Φ (MulAut.conj (c * c)) m₀ = σ ⟨(g : G) * g, hg2H⟩ m₀ := by
    have e : (⟨(g : G) * g, hg2H⟩ : ↥H) = ⟨g, hgH⟩ * ⟨g, hgH⟩ := rfl
    rw [map_mul, ← hc, ← map_mul, hΦ, e]
  have hv2V1 := S.v2_not_mem_V1
  have hgv : (g : G) * S.v2 * (g : G)⁻¹ ∉ fsuV1 T V := hnV1 _ hgH
  have hggv : (g : G) * g * S.v2 * ((g : G) * g)⁻¹ ∉ fsuV1 T V := hnV1 _ hg2H
  have hcomm2 : ∀ x y : G, x ∈ U → y ∈ U → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
  have hvsq : S.v2 * S.v2 = 1 := by
    rw [← pow_two]
    exact hU2 _ (S.v2_mem_UH H)
  have hgvU : (g : G) * S.v2 * (g : G)⁻¹ ∈ U := le_conjClosure _ _ (S.conj_v2_mem_V3 hg)
  have hgvsq : (g : G) * S.v2 * (g : G)⁻¹ * ((g : G) * S.v2 * (g : G)⁻¹) = 1 := by
    rw [← pow_two]
    exact hU2 _ hgvU
  have h1 : Φ (MulAut.conj c) m₀ ≠ m₀ := by
    rw [hΦc, hm₁, hm₀, Ne, hfeq]
    intro h
    apply hggv
    rw [← hv2g2, hcomm2 _ _ (S.v2_mem_UH H) hgvU]
    exact h
  have h2 : Φ (MulAut.conj (c * c)) m₀ ≠ m₀ := by
    rw [hΦcc, hm₂, hm₀, Ne, hfeq]
    intro h
    apply hgv
    have e : (g : G) * g * S.v2 * ((g : G) * g)⁻¹ * S.v2 = (g : G) * S.v2 * (g : G)⁻¹ := by
      rw [← hv2g2, hcomm2 _ _ (S.v2_mem_UH H) hgvU, mul_assoc, hvsq, mul_one]
    rw [← e]
    exact h
  have h12 : Φ (MulAut.conj c) m₀ ≠ Φ (MulAut.conj (c * c)) m₀ := by
    rw [hΦc, hΦcc, hm₁, hm₂, Ne, hfeq]
    intro h
    apply hv2V1
    have e : (g : G) * S.v2 * (g : G)⁻¹ * ((g : G) * g * S.v2 * ((g : G) * g)⁻¹) = S.v2 := by
      rw [← hv2g2, ← mul_assoc, hcomm2 _ _ hgvU (S.v2_mem_UH H), mul_assoc, hgvsq, mul_one]
    rw [← e]
    exact h
  have hcc : m₀ * Φ (MulAut.conj c) m₀ = Φ (MulAut.conj (c * c)) m₀ := by
    rw [hΦc, hΦcc, hm₁, hm₂, hm₀, ← map_mul]
    congr 1
    exact Subtype.ext hv2g2
  have hTfix : ∀ t : ↥H, (t : G) ∈ T → σ t m₀ = m₀ := by
    intro t ht
    rw [hσρ, hm₀, hfeq]
    have hc := S.comm_T_v2 ht
    rwa [inv_eq_of_mul_eq_one_right hvsq] at hc
  have hU' : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀ := by
    intro u hu
    obtain ⟨t, ht, htu⟩ := hρU u hu
    rw [← htu, hΦ]
    exact hTfix t ht
  have hτ' : Φ tauW m₀ = m₀ := by
    rw [← htτ, hΦ]
    exact hTfix tτ htτT
  have hX : ∀ h : ↥H, σ h m₀ ∈ Set.range fun A : SL4 => Φ (MulAut.conj A) m₀ := by
    intro h
    obtain ⟨A, ε, hA⟩ := L4Tw.exists_nf (ρ h)
    refine ⟨A, ?_⟩
    rw [← hΦ, hA, L4Tw.nf, map_mul, MulAut.mul_apply]
    cases ε
    · rw [Bool.cond_false, map_one, MulAut.one_apply]
    · rw [Bool.cond_true, hτ']
  have hgen : Subgroup.closure (Set.range fun A : SL4 => Φ (MulAut.conj A) m₀) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨u, rfl⟩ := hfs y
    have hle : U ≤ ((Subgroup.closure (Set.range fun A : SL4 => Φ (MulAut.conj A) m₀)).comap
        f).map U.subtype := by
      refine conjClosure_le fun h hh z hz => ?_
      refine ⟨⟨h * z * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hHU hh) _).mp
        (le_conjClosure _ _ hz)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← hσρ ⟨h, hh⟩ ⟨z, le_conjClosure _ _ hz⟩]
      have hgen1 : ∀ k : ↥H, σ ⟨h, hh⟩ (σ k m₀) ∈
          Subgroup.closure (Set.range fun A : SL4 => Φ (MulAut.conj A) m₀) := fun k => by
        rw [← MulAut.mul_apply, ← map_mul]
        exact Subgroup.subset_closure (hX _)
      rcases S.mem_V3_cases hg hz with hz1 | hz1 | hz1 | hz1
      · rw [(hf1 ⟨z, _⟩).2 hz1, map_one]
        exact Subgroup.one_mem _
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ 1 m₀ := by
          rw [map_one, MulAut.one_apply, hm₀, hfeq]
          exact hz1
        rw [this]
        exact hgen1 1
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ ⟨g, hgH⟩ m₀ := by
          rw [hm₁, hfeq]
          exact hz1
        rw [this]
        exact hgen1 _
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ ⟨(g : G) * g, hg2H⟩ m₀ := by
          rw [hm₂, hfeq]
          rw [hg2] at hz1
          exact hz1
        rw [this]
        exact hgen1 _
    obtain ⟨n, hn, hnu⟩ := hle u.2
    rw [← Subtype.ext hnu]
    exact hn
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKT : K ⊔ T = H := (h21 G T L V S hS H hH K hK).2.2.1.1
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hHK : H = K ⊔ (S.L1 ⊔ T) :=
    le_antisymm (hKT.symm.le.trans (sup_le_sup_left le_sup_right K)) (sup_le hKH hL1TH)
  obtain ⟨γ, γ', g', s, hDγ, hDH, hpos, hle, c', hc'H, hcV⟩ := case2_data hS hH hnt
  have hm := h18 G T L V S hS H hH K hK hKnH hHK hnt γ γ' g' s hDγ hDH hle
  set Vγ := F8.Uγ V H (g' : G) with hVγ
  set Vα := CFSG.Quasithin.conjSub c' Vγ with hVα
  have hVαH : Vα ≤ H := hcV.trans ((pCoreOf_le 2 _).trans hL1TH)
  have hcomm : ⁅⁅U, Vα⁆, Vα⁆ = ⊥ := by
    have h1 := congrArg (CFSG.Quasithin.conjSub c') (S.comm_comm_UH_Vγ hF98 s)
    rwa [← CFSG.Quasithin.conjSub_commutator, ← CFSG.Quasithin.conjSub_commutator,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 H hc'H),
      CFSG.Quasithin.conjSub_bot] at h1
  have hVαab : IsElemAbelian 2 Vα := F7.isElemAbelian_conjSub (hF98.isElemAbelian_Vγ (g := g'))
  set E := (Vα.subgroupOf H).map ρ with hEdef
  set N := ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map ρ with hNdef
  have hEN : E ≤ N := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hcV (Subgroup.mem_subgroupOf.mp hx))
  have hρP : ∀ h : ↥H, (h : G) ∈ S.L1 ⊔ T → ρ h ∈ L4Tw.Ptau := by
    have hle : (S.L1 ⊔ T).subgroupOf H ≤ L4Tw.Ptau.comap ρ := by
      rw [Subgroup.subgroupOf_sup hL1H hTH, sup_le_iff]
      constructor
      · intro h hh
        obtain ⟨q, hq, hqe⟩ := hρL1 h (Subgroup.mem_subgroupOf.mp hh)
        exact ⟨q, hq, false, by rw [hqe, L4Tw.nf_false]⟩
      · intro h hh
        obtain ⟨u, hu, ε, hue⟩ := hρT h (Subgroup.mem_subgroupOf.mp hh)
        exact ⟨u, L4Tw.U_le_Q13 hu, ε, hue⟩
    exact fun h hh => hle (Subgroup.mem_subgroupOf.mpr hh)
  have hE : ∀ x ∈ E, ∃ o, x = L4Tw.enc o := by
    intro x hx
    refine L4Tw.mem_enc_of_normal (N := N) ?_ ?_ ?_ (hEN hx)
    · rintro _ ⟨h, hh, rfl⟩
      exact hρP h (pCoreOf_le 2 _ (Subgroup.mem_subgroupOf.mp hh))
    · intro q hq y hy
      obtain ⟨h₀, hh₀, hh₀q⟩ := hρQ q hq
      obtain ⟨h, hh, rfl⟩ := hy
      refine ⟨h₀ * h * h₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
        rw [map_mul, map_mul, map_inv, hh₀q]⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hh₀) _).mp
        (Subgroup.mem_subgroupOf.mp hh)
    · exact ((pCoreOf_isPGroup 2 _).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 _).trans hL1TH)).symm).map ρ
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (F7.isElemAbelian_comm hVαab (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb))
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact F7.isElemAbelian_pow_eq_one hVαab (Subgroup.mem_subgroupOf.mp ha))
    rw [this, map_one]
  have h4 : 4 ≤ Nat.card E := by
    rw [card_map_subgroupOf ρ hρk hVαH]
    have hY2 : IsPGroup 2 ↥Vα := (pCoreOf_isPGroup 2 _).to_le hcV
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : CFSG.Quasithin.conjSub c' (pCoreOf 2 H) = pCoreOf 2 H :=
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hc'H)
    rw [hVα, ← hQ, ← CFSG.Quasithin.conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx Vγ (Vγ ⊓ pCoreOf 2 H) := Nat.pow_le_pow_right (by norm_num) hm
  have hconj : ∀ k x : ↥H, ρ k * ρ x * (ρ k)⁻¹ = ρ (k * x * k⁻¹) := fun k x => by
    rw [map_mul, map_mul, map_inv]
  have hq : IndQuad.QuadOn Φ (E : Set (MulAut SL4)) := by
    intro h a ha a' ha' v
    obtain ⟨k, rfl⟩ := hρs h
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    obtain ⟨u, rfl⟩ := hfs v
    rw [hconj, hconj, hΦ, hΦ, hfσ, ← map_inv f u, ← map_mul f, hfσ]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    have hku := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem k.2)) _).mp u.2
    rw [inv_inv] at hku
    exact conj_quad hcomm hku (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
  obtain ⟨r, hr⟩ := L4Tw.exists_transv hsq hU' hτ' hgen hcQ h1 h2 h12 hcc hE hEab hE2 h4 hq
  have hστ : sigmaH hH ⟨(tτ : G), tτ.2⟩ = Φ tauW := by
    rw [← htτ, hΦ]
  have hne : sigmaH hH ⟨(tτ : G), tτ.2⟩ ≠ 1 := by
    intro h1'
    have h2' := (hσ1 tτ).1 h1'
    rw [← hρk, htτ] at h2'
    exact L4Tw.tauW_ne_one h2'
  refine hnt _ tτ.2 (inducesTransvMod_of_comm hH tτ.2 hne (r := r) fun v => ?_)
  rw [hστ]
  exact hr v

end Setting4

open L13825 in
theorem lem13825NoA6_of (h21 : Lem13821) (h16 : Lem13816)
    (h1334 : Stmt13_3_4) (h18 : Lem13818Four) : Lem13825NoA6 := by
  intro G _ _ T L V S hS H hH K hK hnt hKn hhat hTK'
  exact Setting4.false_of_A6 h21 h16 h1334 h18 hS hH hK hnt hKn hhat hTK'

end CFSG.Quasithin.H13.A6
