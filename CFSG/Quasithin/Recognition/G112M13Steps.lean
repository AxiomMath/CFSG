module

public import CFSG.Quasithin.Recognition.G112M13Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Q : ConclPred}
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {m : ℕ}

private theorem finrank_top_eq (d : ℕ)
    (h : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = d) :
    Module.finrank (ZMod 2) V = d := by
  rwa [finrank_top] at h

theorem step4M (hQ : QContainsM Q) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h4 : G93Case4 (topH Γ L) m) : False := by
  obtain ⟨⟨-, hd, -, hperm⟩, hend, -⟩ := h4
  obtain ⟨φ₀, β, hsurj, hker, hequ⟩ := isPermCoreModule_of_restrictRange_top hperm
  have hF := fstar_map_eq_normalClosure c.h108.component (centralizer_trivial hend)
  have hd6 : Module.finrank (ZMod 2) V = 6 := finrank_top_eq _ hd
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    rcases (hker u).1 hu with h | ⟨he, -⟩
    · exact h
    · exact absurd he (by decide)
  let e : ↥(permCore 7) ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective β ⟨hinj, hsurj⟩
  refine c.setup.notConcl (hQ.c4 B Γ X ⟨hd6, (fstarEquiv hF).trans φ₀, e.symm, fun γ v => ?_⟩)
  set u : ↥(permCore 7) := e.symm v with hu
  have hmem := permAct_mem_permCore
    ((φ₀ (fstarEquiv hF γ) : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) u.2
  have h1 : β ⟨_, hmem⟩ = ((γ : ↥Γ) : GLV V) (β u) := hequ (fstarEquiv hF γ) u ⟨_, hmem⟩ rfl
  have h2 : β u = v := e.apply_symm_apply v
  have h3 : e.symm (((γ : ↥Γ) : GLV V) v) = ⟨_, hmem⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    show _ = β ⟨_, hmem⟩
    rw [h1, h2]
  rw [h3]
  rfl

theorem step6M (hQ : QContainsM Q) (hL2 : SzG11S.NoConfigL2) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h6 : G93Case6 (topH Γ L) m) : False := by
  obtain ⟨n, ⟨hn2, hd, -, -, hnat⟩, -, -⟩ := h6
  have hdV : Module.finrank (ZMod 2) V = 2 * n := finrank_top_eq _ hd
  by_cases hn3 : 3 ≤ n
  · exact hL2 V B Γ v₁ W X X₀ L c.setup.conf c.props n hn3
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 2 := by omega
    subst hn
    obtain ⟨φ, -⟩ := hnat
    have hcardH : Nat.card ↥(normalClosure Γ L) = 60 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_statedSL_two (by norm_num)]
      norm_num
    exact c.setup.notConcl (hQ.c2 B Γ X ⟨by omega,
      Or.inl (ten_dvd_of_card_eq c.h108.L_le hcardH)⟩)

theorem step7M (hQ : QContainsM Q) (hOm : SzG11S.NoConfigOm4Minus)
    (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m) (h7 : G93Case7 (topH Γ L) m) : False := by
  obtain ⟨a, ⟨ha1, hd, -, -, ⟨φ⟩, b, b', hbb, hnat⟩, -, -⟩ := h7
  have hdV : Module.finrank (ZMod 2) V = 4 * a := finrank_top_eq _ hd
  by_cases ha2 : 2 ≤ a
  · exact hOm V B Γ v₁ W X X₀ L c.setup.conf c.props a ha2 b b' hbb
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have ha : a = 1 := by omega
    subst ha
    have hcardH : Nat.card ↥(normalClosure Γ L) = 60 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_statedSL_two (by norm_num)]
      norm_num
    exact c.setup.notConcl (hQ.c2 B Γ X ⟨by omega,
      Or.inl (ten_dvd_of_card_eq c.h108.L_le hcardH)⟩)

theorem step9M (hQ : QContainsM Q) (hSp : SzG11S.NoConfigSp4) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h9 : G93Case9 (topH Γ L) m) : False := by
  obtain ⟨n, ⟨hn1, hd, -, -, hnat, hperm⟩, -, -⟩ := h9
  have hdV : Module.finrank (ZMod 2) V = 4 * n := finrank_top_eq _ hd
  by_cases hn2 : 2 ≤ n
  · exact hSp V B Γ v₁ W X X₀ L c.setup.conf c.props n hn2
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 1 := by omega
    subst hn
    obtain ⟨φ, -⟩ := hperm rfl
    have hcardH : Nat.card ↥(normalClosure Γ L) = 360 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_alternatingGroup_six]
    have hdvd : Nat.card ↥(normalClosure Γ L) ∣ Nat.card ↥Γ :=
      Subgroup.card_dvd_of_le c.h108.H_le
    rw [hcardH] at hdvd
    exact c.setup.notConcl
      (hQ.c2 B Γ X ⟨by omega, Or.inl (Dvd.dvd.trans (by norm_num) hdvd)⟩)

theorem step12M (hQ : QContainsM Q) (h : A8OrthogonalFact) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h12 : G93Case12 (topH Γ L) m) : False := by
  obtain ⟨⟨-, hd, -, hperm⟩, -, -⟩ := h12
  have hd6 : Module.finrank (ZMod 2) V = 6 := finrank_top_eq _ hd
  exact c.setup.notConcl (hQ.c5 B Γ X (h V B (normalClosure Γ L) Γ hd6
    (isPermCoreModule_of_restrictRange_top hperm) c.h108.alt c.h108.nondegenerate
    c.h108.isometry c.h108.H_le (normalClosure_normal Γ L)))

theorem step2M (hQ : QContainsM Q) (hM22 : AutHatM22Bound) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h2 : G93Case2 (topK Γ L X) (topH Γ L) m) : False := by
  obtain ⟨⟨-, hd, ⟨N, hNnormal, hNindex, hN, hHN⟩, hcard⟩, hend, -⟩ := h2
  have hd12 : Module.finrank (ZMod 2) V = 12 := finrank_top_eq _ hd
  let e : ↥(normalClosure Γ L) ≃* ↥N :=
    (restrictRangeTop (normalClosure Γ L)).trans ((MulEquiv.subgroupCongr hHN).trans
      (N.equivMapOfInjective (topK Γ L X).subtype (topK Γ L X).subtype_injective).symm)
  have hautH : Nat.card (MulAut ↥(normalClosure Γ L)) ≤ 887040 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact hM22 ↥N hN
  have hC : Nat.card ↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ≤ 3 := by
    have h1 : Nat.card ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ∣ 3 := by
      have := natCard_centralizer_dvd (K := normalClosure Γ L) (e := 2) (by norm_num) hend
      simpa using this
    exact (Subgroup.card_le_of_le inf_le_right).trans (Nat.le_of_dvd (by norm_num) h1)
  have hle := natCard_le_aut_mul_centralizer (Γ := Γ) (normalClosure_normal Γ L)
  have hup : Nat.card ↥Γ ≤ 2661120 :=
    hle.trans ((Nat.mul_le_mul hautH hC).trans (by norm_num))
  have hK : Nat.card ↥(normalClosure Γ L ⊔ X) ≤ Nat.card ↥Γ :=
    Subgroup.card_le_of_le (sup_le c.h108.H_le c.h108.X_le)
  have hKcard : Nat.card ↥(normalClosure Γ L ⊔ X) = 2661120 := by
    rw [← natCard_restrictRangeTop]
    exact hcard
  have hfinal : Nat.card ↥Γ = 2661120 := by omega
  have hHΓ : normalClosure Γ L ≤ Γ := c.h108.H_le
  have hNormΓ : ((normalClosure Γ L).subgroupOf Γ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := normalClosure_normal Γ L (g : GLV V) g.2 (n : GLV V) hn
    simpa using this
  let e' : ↥((normalClosure Γ L).subgroupOf Γ) ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hHΓ).trans e
  have hQs : CFSG.IsQuasisimple ↥((normalClosure Γ L).subgroupOf Γ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hN.1
  have hZ : Nat.card ↥(Subgroup.center ↥((normalClosure Γ L).subgroupOf Γ)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e'.symm).toEquiv).symm.trans hN.2.1
  have hHat : IsHat ↥((normalClosure Γ L).subgroupOf Γ)
      ↥CFSG.Blueprint.NativeSporadic.M22 := by
    have hcen := Subgroup.map_center_eq e'
    refine ⟨hQs, hZ, ?_⟩
    obtain ⟨φ⟩ := hN.2.2
    exact ⟨(QuotientGroup.congr _ _ e' hcen).trans φ⟩
  have hcardN : Nat.card ↥N = 1330560 := by
    have hm := N.card_mul_index
    rw [hNindex, hcard] at hm
    omega
  have hcardH : Nat.card ↥((normalClosure Γ L).subgroupOf Γ) = 1330560 :=
    (Nat.card_congr e'.toEquiv).trans hcardN
  have hindex : ((normalClosure Γ L).subgroupOf Γ).index = 2 := by
    have hm := ((normalClosure Γ L).subgroupOf Γ).card_mul_index
    rw [hcardH, hfinal] at hm
    omega
  have hirrN : IsIrr (((normalClosure Γ L).subgroupOf Γ).map Γ.subtype) ⊤ := by
    rw [Subgroup.map_subgroupOf_eq_of_le hHΓ]
    exact c.isIrr
  exact c.setup.notConcl (hQ.c13 B Γ X ⟨hd12, (normalClosure Γ L).subgroupOf Γ, hNormΓ, hindex,
    hHat, hirrN⟩)

theorem step15M (hQ : QContainsM Q) (hOm : SzG11S.NoConfigOm4Plus)
    (hOm4 : SzG11S.NoConfigOm4PlusFour) (hIso : Om4Plus4Iso) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h15 : G93Case15 (topH Γ L) m) : False := by
  obtain ⟨n, ⟨hn2, hd, -, -, hnat⟩, hend, -⟩ := h15
  have hdV : Module.finrank (ZMod 2) V = 4 * n := finrank_top_eq _ hd
  by_cases hn3 : 3 ≤ n
  · exact hOm V B Γ v₁ W X X₀ L c.setup.conf c.props n hn3
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 2 := by omega
    subst hn
    have hnatV := isNaturalMatrixModule_of_restrictRange_top hnat
    have hXH : ¬ X ≤ normalClosure Γ L := fun h =>
      hOm4 V B Γ v₁ W X X₀ L c.setup.conf c.props hnatV h
    have hnatV' := hnatV
    obtain ⟨φ, -⟩ := hnatV
    obtain ⟨ω⟩ := hIso
    let ι := φ.trans ω
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hcard4 : Fintype.card (GaloisField 2 2) = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨τ, γ, h1, h2, h3, h4, h5⟩ := exists_S3_in_SL2 (GaloisField 2 2) hcard4
    have hC : ∀ x ∈ Γ, (∀ h ∈ normalClosure Γ L, x * h = h * x) → x = 1 := by
      intro x hxΓ hx
      have hcent : x ∈ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => (hx h hh).symm
      have h3' : x ^ 3 = 1 := by
        have := centralizer_pow_eq_one (K := normalClosure Γ L) (e := 2) (by norm_num) hend hcent
        simpa using this
      exact eq_one_of_central_of_prod_S3 c.setup.conf.sqtk c.h108.H_le ι h1 h2 h3 h4 h5 hxΓ
        (fun h hh => (hx h hh).symm) h3'
    have hF := fstar_map_eq_normalClosure c.h108.component hC
    have hnatF : IsNaturalMatrixModule ((CFSG.Open.genFittingFStar ↥Γ).map Γ.subtype)
        (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) := by
      rw [hF]
      exact hnatV'
    exact c.setup.notConcl (hQ.c7 B Γ X ⟨by omega, hnatF, by
      rw [hF]
      exact hXH⟩)

end Canon

end G11

end CFSG.Quasithin
