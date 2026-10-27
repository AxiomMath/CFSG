module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.IrrSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.SecModDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.PermNormal

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

theorem conj_mem_of_mem_V {X V C : Subgroup G} (hs : IsSec X C V) {x c : G} (hx : x ∈ V)
    (hc : c ∈ C) : x * c * x⁻¹ ∈ C := by
  have h := hs.comm x hx c (hs.le hc)
  have e : x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
  rw [e]
  exact C.mul_mem h hc

theorem normalize_ker_five {X T : Subgroup G} [Finite G] {θ : ↥X →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hT : IsSylowTwoOf T X) :
    ∃ Ψ : ↥X →* Perm (Fin 5), Function.Surjective Ψ ∧ Ψ.ker = θ.ker ∧
      (T.subgroupOf X).map Ψ = S5Syl := by
  obtain ⟨g₀, hg₀⟩ := exists_conj_S5Syl (card_image_sylow hθs hT)
  refine ⟨(MulAut.conj g₀⁻¹).toMonoidHom.comp θ,
    (MulEquiv.surjective (MulAut.conj g₀⁻¹)).comp hθs, ?_, ?_⟩
  · ext f
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (MulAut.conj g₀⁻¹).map_eq_one_iff
  · rw [← Subgroup.map_map, hg₀, map_conj_map_conj_inv]

theorem epi_of_otwo {X : Subgroup G} (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) :
    ∃ Ψ : ↥X →* Perm (Fin 5), Function.Surjective Ψ ∧ Ψ.ker = (pCoreOf 2 X).subgroupOf X := by
  obtain ⟨e⟩ := he
  have hsub : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
    unfold pCoreOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [hsub]
  ext x
  rw [MonoidHom.mem_ker]
  show e (QuotientGroup.mk x) = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥X
  rw [← map_one e, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem mem_alt_of_oTwoRes_sup {X : Subgroup G} {θ : ↥X →* Perm (Fin 5)}
    (hk : θ.ker = (pCoreOf 2 X).subgroupOf X) {f : G} (hf : f ∈ X)
    (hmem : f ∈ oTwoRes X ⊔ pCoreOf 2 X) : θ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5) := by
  have hle : oTwoRes X ⊔ pCoreOf 2 X ≤ ((alternatingGroup (Fin 5)).comap θ).map X.subtype := by
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxX, m, hm, hxm⟩
      refine ⟨⟨x, hxX⟩, ?_, rfl⟩
      show θ ⟨x, hxX⟩ ∈ alternatingGroup (Fin 5)
      rw [Equiv.Perm.mem_alternatingGroup]
      have h1 : Perm.sign (θ ⟨x, hxX⟩) ^ m = 1 := by
        rw [← map_pow, ← map_pow]
        have : (⟨x, hxX⟩ : ↥X) ^ m = 1 := Subtype.ext (by simpa using hxm)
        rw [this]
        simp
      rcases Int.units_eq_one_or (Perm.sign (θ ⟨x, hxX⟩)) with h | h
      · exact h
      · rw [h, hm.neg_one_pow] at h1
        exact absurd h1 (by decide)
    · intro x hx
      have hxX : x ∈ X := by
        unfold pCoreOf at hx
        exact Subgroup.map_subtype_le _ hx
      refine ⟨⟨x, hxX⟩, ?_, rfl⟩
      show θ ⟨x, hxX⟩ ∈ alternatingGroup (Fin 5)
      have h1 : (⟨x, hxX⟩ : ↥X) ∈ θ.ker := by
        rw [hk]
        exact Subgroup.mem_subgroupOf.mpr hx
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      exact one_mem _
  obtain ⟨y, hy, hyf⟩ := hle hmem
  have : y = ⟨f, hf⟩ := Subtype.ext hyf
  rw [← this]
  exact Subgroup.mem_comap.mp hy

theorem fixW_top_bot [Finite G] {X V C : Subgroup G} (hs : IsSec X C V) (Ψ : ↥X →* Perm (Fin 5))
    (hΨs : Function.Surjective Ψ) (hkC : Ψ.ker ≤ (cSecIn X C V).subgroupOf X)
    (hFix : fixSecIn X C V = C) : fixW (secModule hs Ψ hΨs hkC) ⊤ = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := hs.proj_surjective w
  refine Subgroup.mem_bot.mpr ((hs.proj_eq_one_iff v).mpr ?_)
  have hvF : (v : G) ∈ fixSecIn X C V := by
    apply Subgroup.subset_closure
    refine ⟨v.2, fun a ha => ?_⟩
    have h0 := hw (Ψ ⟨a, ha⟩) (Subgroup.mem_top _)
    rw [secModule_act_proj hs Ψ hΨs hkC] at h0
    have h2 := (hs.proj_eq_proj_iff _ _).mp h0
    have hd : (v : G)⁻¹ * a * v * a⁻¹ ∈ C := by
      have := C.inv_mem h2
      convert this using 1
      change _ = (((a : G) * v * a⁻¹)⁻¹ * v)⁻¹
      group
    have h3 := conj_mem_of_mem_V hs v.2 hd
    convert h3 using 1
    group
  rw [hFix] at hvF
  exact hvF

@[expose] def quotBotEquiv (M : Model 5) (hbot : IsInvSub M ⊤ (⊥ : Subgroup M.W)) :
    (M.quot ⊥ hbot).W ≃* M.W :=
  QuotientGroup.quotientBot

theorem quotBotEquiv_map_act (M : Model 5) (hbot : IsInvSub M ⊤ (⊥ : Subgroup M.W))
    (σ : Perm (Fin 5)) (w : (M.quot ⊥ hbot).W) :
    quotBotEquiv M hbot ((M.quot ⊥ hbot).act σ w) = M.act σ (quotBotEquiv M hbot w) := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
  have h := quotAct_mk M ⊥ hbot σ z
  change quotBotEquiv M hbot (quotAct M ⊥ hbot σ (QuotientGroup.mk z)) = _
  rw [h]
  rfl

theorem model5_faithful_of_fixW_top_bot (M : Model 5) (hfix : fixW M ⊤ = ⊥)
    (hnt : ∃ w : M.W, w ≠ 1) : M.Faithful := by
  obtain ⟨w₀, hw₀⟩ := hnt
  have key : (∀ σ : Perm (Fin 5), ∀ w : M.W, M.act σ w = w) → False := by
    intro h
    apply hw₀
    have hmem : w₀ ∈ fixW M ⊤ := fun b _ => h b w₀
    rw [hfix] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [Model.Faithful, injective_iff_map_eq_one M.act]
  intro σ hσ
  rcases normal_perm_five M.act.ker (MonoidHom.normal_ker M.act) with h | h | h
  · have hσN : σ ∈ M.act.ker := MonoidHom.mem_ker.mpr hσ
    rw [h] at hσN
    exact Subgroup.mem_bot.mp hσN
  · exfalso
    have hAiff : ∀ b : Perm (Fin 5), M.act b = 1 ↔ b ∈ alternatingGroup (Fin 5) := fun b => by
      rw [← h]
      exact MonoidHom.mem_ker.symm
    apply key
    set g : Perm (Fin 5) := Equiv.swap (0 : Fin 5) 1 with hg
    have hg_sign : Perm.sign g = -1 := Equiv.Perm.sign_swap (by decide)
    have hgg : M.act g * M.act g = 1 := by
      rw [← map_mul, hg, Equiv.swap_mul_self, map_one]
    have hτ : ∀ w : M.W, M.act g (M.act g w) = w := fun w => by
      have := congrArg (fun φ : MulAut M.W => φ w) hgg
      simpa [MulAut.mul_apply] using this
    have hsgn : ∀ b : Perm (Fin 5), b ∉ alternatingGroup (Fin 5) → M.act b = M.act g := by
      intro b hb
      have hodd : Perm.sign b = -1 := by
        rw [Equiv.Perm.mem_alternatingGroup] at hb
        rcases Int.units_eq_one_or (Perm.sign b) with h1 | h1
        · exact absurd h1 hb
        · exact h1
      have hev : g⁻¹ * b ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hg_sign, hodd]
        decide
      have h1 : M.act (g⁻¹ * b) = 1 := (hAiff _).mpr hev
      calc M.act b = M.act (g * (g⁻¹ * b)) := by rw [mul_inv_cancel_left]
        _ = M.act g := by rw [map_mul, h1, mul_one]
    have hu : ∀ w : M.W, w * M.act g w = 1 := by
      intro w
      have hmem : w * M.act g w ∈ fixW M ⊤ := by
        rw [mem_fixW]
        intro b _
        by_cases hb : b ∈ alternatingGroup (Fin 5)
        · rw [show M.act b = 1 from (hAiff b).mpr hb]
          rfl
        · rw [hsgn b hb, map_mul, hτ, mul_comm]
      rw [hfix] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hτ1 : ∀ w : M.W, M.act g w = w := by
      intro w
      calc M.act g w = w⁻¹ := eq_inv_of_mul_eq_one_right (hu w)
        _ = w := inv_eq_of_mul_eq_one_right (M.sq w)
    intro b w
    by_cases hb : b ∈ alternatingGroup (Fin 5)
    · rw [show M.act b = 1 from (hAiff b).mpr hb]
      rfl
    · rw [hsgn b hb, hτ1]
  · exfalso
    apply key
    intro b w
    have hb : b ∈ M.act.ker := by
      rw [h]
      exact Subgroup.mem_top b
    rw [MonoidHom.mem_ker.mp hb]
    rfl

theorem irrSecSec_aux [Finite G] {X V C T : Subgroup G} (hs : IsSec X C V) (hCV : C ≠ V)
    (hpc : pCoreOf 2 X ≤ cSecIn X C V) (hFix : fixSecIn X C V = C)
    (hgen : ∀ U : Subgroup G, C ≤ U → U ≤ V → X ≤ Subgroup.normalizer (U : Set G) →
      fixSecIn T C V ≤ U → U = V)
    (Ψ : ↥X →* Perm (Fin 5)) (hΨs : Function.Surjective Ψ)
    (hΨk : Ψ.ker = (pCoreOf 2 X).subgroupOf X) (hPS : (T.subgroupOf X).map Ψ = S5Syl)
    {a : G} (ha : a ∈ oTwoRes X ⊔ pCoreOf 2 X) (haN : a ∉ pCoreOf 2 X)
    (ha23 : a ^ 2 ∈ pCoreOf 2 X ∨ a ^ 3 ∈ pCoreOf 2 X)
    (hidx : secIdx (Subgroup.zpowers a) C V ≤ 8) :
    IsOrthSec X C V ∨ IsNatSec X C V := by
  have := hs.normal_subgroupOf
  have hkC : Ψ.ker ≤ (cSecIn X C V).subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hpc (Subgroup.mem_subgroupOf.mp (hΨk ▸ hx)))
  set M := secModule hs Ψ hΨs hkC with hM
  have hsd : SecData M X C V Ψ (MonoidHom.id hs.W) := secData_secModule hs Ψ hΨs hkC
  have hnt : ∃ w : M.W, w ≠ 1 := by
    have : ∃ v ∈ V, v ∉ C := by
      by_contra h
      push Not at h
      exact hCV (le_antisymm hs.le h)
    obtain ⟨v, hvV, hvC⟩ := this
    refine ⟨hs.proj ⟨v, hvV⟩, fun h => hvC ?_⟩
    exact (hs.proj_eq_one_iff ⟨v, hvV⟩).mp h
  have hfix : fixW M ⊤ = ⊥ := fixW_top_bot hs Ψ hΨs hkC hFix
  have hgen' : ∀ U : Subgroup M.W, IsInvSub M ⊤ U → fixW M S5Syl ≤ U → U = ⊤ := by
    intro U hU hfixU
    set U' : Subgroup G := (U.comap hs.proj).map V.subtype with hU'
    have hU'V : U' ≤ V := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hmem : ∀ x : G, x ∈ U' ↔ ∃ hx : x ∈ V, hs.proj ⟨x, hx⟩ ∈ U := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨x, hx⟩, h, rfl⟩
    have hinv : ∀ k ∈ X, ∀ x ∈ U', k * x * k⁻¹ ∈ U' := by
      intro k hk x hx
      obtain ⟨hxV, hxU⟩ := (hmem x).mp hx
      refine (hmem _).mpr ⟨hs.conj_mem_N ⟨k, hk⟩ ⟨x, hxV⟩, ?_⟩
      have h1 := hU (Ψ ⟨k, hk⟩) (Subgroup.mem_top _) _ hxU
      rw [secModule_act_proj hs Ψ hΨs hkC] at h1
      exact h1
    have hnorm : X ≤ Subgroup.normalizer (U' : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun h => hinv k hk x h, fun h => ?_⟩
      have h1 := hinv k⁻¹ (X.inv_mem hk) _ h
      have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
      rwa [e] at h1
    have hC'U' : C ≤ U' := by
      intro x hx
      refine (hmem x).mpr ⟨hs.le hx, ?_⟩
      have h1 : hs.proj ⟨x, hs.le hx⟩ = 1 := (hs.proj_eq_one_iff _).mpr hx
      rw [h1]
      exact U.one_mem
    have hcle : fixSecIn T C V ≤ U' := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxV, hx⟩
      refine (hmem x).mpr ⟨hxV, hfixU ?_⟩
      intro b hb
      rw [← hPS] at hb
      obtain ⟨t, ht, rfl⟩ := hb
      have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      rw [secModule_act_proj hs Ψ hΨs hkC]
      refine (hs.proj_eq_proj_iff _ _).mpr ?_
      show ((t : G) * x * (t : G)⁻¹)⁻¹ * x ∈ C
      have hc := C.inv_mem (hx (t : G) htT)
      have h3 := conj_mem_of_mem_V hs (V.inv_mem hxV) hc
      convert h3 using 1
      group
    have hU'eq : U' = V := hgen U' hC'U' hU'V hnorm hcle
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hs.proj_surjective w
    have hv : (v : G) ∈ U' := by
      rw [hU'eq]
      exact v.2
    exact ((hmem _).mp hv).2
  have haX : a ∈ X := sup_le (oTwoRes_le X) (Subgroup.map_subtype_le _) ha
  have hσA : Ψ ⟨a, haX⟩ ∈ alternatingGroup (Fin 5) := mem_alt_of_oTwoRes_sup hΨk haX ha
  have hker : ∀ y : ↥X, (y : G) ∈ pCoreOf 2 X → Ψ y = 1 := fun y hy =>
    (MonoidHom.mem_ker).mp (by rw [hΨk]; exact Subgroup.mem_subgroupOf.mpr hy)
  have ha1 : Ψ ⟨a, haX⟩ ≠ 1 := by
    intro h
    apply haN
    have : (⟨a, haX⟩ : ↥X) ∈ Ψ.ker := h
    rw [hΨk, Subgroup.mem_subgroupOf] at this
    exact this
  have ha23' : Ψ ⟨a, haX⟩ ^ 2 = 1 ∨ Ψ ⟨a, haX⟩ ^ 3 = 1 := by
    rcases ha23 with h | h
    · left
      rw [← map_pow]
      exact hker _ h
    · right
      rw [← map_pow]
      exact hker _ h
  have hidx' : idx M (Ψ ⟨a, haX⟩) ≤ 8 := by
    rw [← hsd.secIdx_eq_idx hs.le haX]
    exact hidx
  obtain ⟨-, hiso⟩ := irr M hnt hfix hgen' hσA ha1 ha23' hidx'
  have hcp : cSecIn X C V ≤ pCoreOf 2 X := by
    have hf : M.Faithful := by
      rcases hiso with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
      · exact Model.Faithful.of_iso e' orth_faithful
      · exact Model.Faithful.of_iso e' nat_faithful
    have hCX : cSecIn X C V ≤ X := (Subgroup.closure_le X).mpr fun _ hx => hx.1
    have hcf := (secModule_faithful_iff hs Ψ hΨs hkC).mp hf
    intro x hx
    have h1 : (⟨x, hCX hx⟩ : ↥X) ∈ Ψ.ker := hcf (Subgroup.mem_subgroupOf.mpr hx)
    rw [hΨk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcp' : cSecIn X C V = pCoreOf 2 X := le_antisymm hcp hpc
  have hker' : Ψ.ker = (cSecIn X C V).subgroupOf X := by
    rw [hΨk, hcp']
  rcases hiso with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl (isModelSec_of_iso hs Ψ hΨs hker' e'.symm)
  · exact Or.inr (isModelSec_of_iso hs Ψ hΨs hker' e'.symm)

theorem irrSecSec : CFSG.Quasithin.F53.Stellmacher.IrrSecSec := by
  intro G _ _ X V C T he hs hCV hpc hFix hT hgen a ha haN ha23 hidx
  obtain ⟨Ψ0, hΨ0s, hΨ0k⟩ := epi_of_otwo he
  obtain ⟨Ψ, hΨs, hΨk, hPS⟩ := normalize_ker_five hΨ0s hT
  exact irrSecSec_aux hs hCV hpc hFix hgen Ψ hΨs (hΨk.trans hΨ0k) hPS ha haN ha23 hidx

theorem hss15Sec : CFSG.Quasithin.F53.Stellmacher.Hss15Sec := by
  intro G _ _ X V C he hs hpc hFix s hsX hidx2
  have := hs.normal_subgroupOf
  obtain ⟨Ψ, hΨs, hΨk⟩ := epi_of_otwo he
  have hkC : Ψ.ker ≤ (cSecIn X C V).subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hpc (Subgroup.mem_subgroupOf.mp (hΨk ▸ hx)))
  set M := secModule hs Ψ hΨs hkC with hM
  have hsd : SecData M X C V Ψ (MonoidHom.id hs.W) := secData_secModule hs Ψ hΨs hkC
  have hfix : fixW M ⊤ = ⊥ := fixW_top_bot hs Ψ hΨs hkC hFix
  have h2 : idx M (Ψ ⟨s, hsX⟩) = 2 := (hsd.secIdx_eq_idx hs.le hsX).symm.trans hidx2
  have ht1 : Ψ ⟨s, hsX⟩ ≠ 1 := by
    intro h
    have h1 : idx M (Ψ ⟨s, hsX⟩) = 1 := by
      rw [h]
      unfold idx
      have htop : fixW M (Subgroup.zpowers (1 : Perm (Fin 5))) = ⊤ := by
        rw [eq_top_iff]
        intro w _
        rw [mem_fixW]
        intro b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        simp
      rw [htop, Subgroup.index_top]
    omega
  have hnt : ∃ w : M.W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have htop : fixW M (Subgroup.zpowers (Ψ ⟨s, hsX⟩)) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [mem_fixW]
      intro b _
      rw [hcon w, map_one]
    have h1 : idx M (Ψ ⟨s, hsX⟩) = 1 := by
      unfold idx
      rw [htop, Subgroup.index_top]
    omega
  have hf : M.Faithful := model5_faithful_of_fixW_top_bot M hfix hnt
  have hcp : cSecIn X C V ≤ pCoreOf 2 X := by
    have hCX : cSecIn X C V ≤ X := (Subgroup.closure_le X).mpr fun _ hx => hx.1
    have hcf := (secModule_faithful_iff hs Ψ hΨs hkC).mp hf
    intro x hx
    have h1 : (⟨x, hCX hx⟩ : ↥X) ∈ Ψ.ker := hcf (Subgroup.mem_subgroupOf.mpr hx)
    rw [hΨk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcp' : cSecIn X C V = pCoreOf 2 X := le_antisymm hcp hpc
  have hker' : Ψ.ker = (cSecIn X C V).subgroupOf X := by
    rw [hΨk, hcp']
  obtain ⟨-, ⟨e5⟩⟩ := hss_1_5_top M hf ht1 h2
  have hbot : IsInvSub M ⊤ (⊥ : Subgroup M.W) := by
    intro b _ u hu
    rw [Subgroup.mem_bot.mp hu, map_one]
    exact Subgroup.one_mem _
  have hq := Model.quotCongr M hfix
    (isInvSub_fixW_of_normal M (Subgroup.normal_top : (⊤ : Subgroup (Perm (Fin 5))).Normal)) hbot
  have hb : (M.quot ⊥ hbot).Iso M :=
    { toMulEquiv := quotBotEquiv M hbot
      map_act := quotBotEquiv_map_act M hbot }
  have e' : M.Iso orth := hb.symm.trans (hq.symm.trans e5)
  exact isModelSec_of_iso hs Ψ hΨs hker' e'.symm

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
