module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverQuot
public import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem close16_frattini_lift {M Q : Type} [Group M] [Finite M] [Group Q] (φ : M →* Q)
    {Y A : Subgroup M} (hY : Y.Normal) (hAY : A ≤ Y) {p : ℕ} (hp : p.Prime)
    (hA : Nat.card A = p) (hker : ¬ p ∣ Nat.card ↥(Y ⊓ φ.ker)) {q : Q}
    (hq : q ∈ normalizer ((A.map φ : Subgroup Q) : Set Q)) (hqr : q ∈ φ.range) :
    ∃ n ∈ normalizer (A : Set M), φ n = q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hqr
  let B : Subgroup M := Y ⊓ (A.map φ).comap φ
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hAkernel : A ⊓ φ.ker = ⊥ := by
    have hKp : IsPGroup p ↥(A ⊓ φ.ker) :=
      IsPGroup.to_le (H := A ⊓ φ.ker) (K := A) hAp inf_le_left
    have hle : A ⊓ φ.ker ≤ Y ⊓ φ.ker := inf_le_inf hAY le_rfl
    rcases hKp.card_eq_or_dvd with h1 | hpd
    · exact Subgroup.eq_bot_of_card_eq (H := A ⊓ φ.ker) h1
    · exact absurd (hpd.trans (Subgroup.card_dvd_of_le hle)) hker
  have hAφcard : Nat.card (A.map φ) = Nat.card A := by
    have hdisj : Disjoint A φ.ker := disjoint_iff_inf_le.mpr (le_of_eq hAkernel)
    have hinj : Function.Injective (φ.domRestrict A) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx1 : (x : M) ∈ φ.ker := hx
      have hx2 : (x : M) ∈ A := x.2
      have hx3 : (x : M) = 1 := Subgroup.disjoint_def.1 hdisj hx2 hx1
      exact Subtype.ext hx3
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.domRestrict_range] at h
    exact h.symm
  have hAB : A ≤ B := fun a ha =>
    ⟨hAY ha, Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem φ ha)⟩
  have hAmax : ∀ Z : Subgroup M, Z ≤ B → IsPGroup p Z → Nat.card Z ≤ Nat.card A := by
    intro Z hZB hZp
    have hZK : Z ⊓ φ.ker = ⊥ := by
      have hKp : IsPGroup p ↥(Z ⊓ φ.ker) :=
        IsPGroup.to_le (H := Z ⊓ φ.ker) (K := Z) hZp inf_le_left
      have hle : Z ⊓ φ.ker ≤ Y ⊓ φ.ker :=
        inf_le_inf (hZB.trans inf_le_left) le_rfl
      rcases hKp.card_eq_or_dvd with h1 | hpd
      · exact Subgroup.eq_bot_of_card_eq (H := Z ⊓ φ.ker) h1
      · exact absurd (hpd.trans (Subgroup.card_dvd_of_le hle)) hker
    have hcard : Nat.card (Z.map φ) = Nat.card Z := by
      have hdisj : Disjoint Z φ.ker := disjoint_iff_inf_le.mpr (le_of_eq hZK)
      have hinj : Function.Injective (φ.domRestrict Z) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        have hx1 : (x : M) ∈ φ.ker := hx
        have hx2 : (x : M) ∈ Z := x.2
        have hx3 : (x : M) = 1 := Subgroup.disjoint_def.1 hdisj hx2 hx1
        exact Subtype.ext hx3
      have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rw [MonoidHom.domRestrict_range] at h
      exact h.symm
    have hmaple : Z.map φ ≤ A.map φ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      exact (Subgroup.mem_inf.1 (hZB hz)).2
    haveI : Finite ↥(A.map φ) :=
      Finite.of_surjective (φ.subgroupMap A) (φ.subgroupMap_surjective A)
    rw [← hcard]
    calc Nat.card (Z.map φ) ≤ Nat.card (A.map φ) := Subgroup.card_le_of_le hmaple
      _ = Nat.card A := hAφcard
  have hmB : m ∈ normalizer (B : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine ⟨hY.conj_mem x hx.1 m, ?_⟩
      have h1 : q * φ x * q⁻¹ ∈ A.map φ :=
        (Subgroup.mem_normalizer_iff.1 hq (φ x)).1 hx.2
      simpa [map_mul, map_inv, hm] using h1
    · intro hx
      refine ⟨?_, ?_⟩
      · have hx1 := hY.conj_mem' (m * x * m⁻¹) hx.1 m
        have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
        rwa [e] at hx1
      · have hqinv : q⁻¹ ∈ normalizer ((A.map φ : Subgroup Q) : Set Q) :=
          Subgroup.inv_mem _ hq
        have h1 : q * φ x * q⁻¹ ∈ A.map φ := by
          simpa [map_mul, map_inv, hm] using hx.2
        have h2 := (Subgroup.mem_normalizer_iff.1 hqinv (q * φ x * q⁻¹)).1 h1
        have h3 : q⁻¹ * (q * φ x * q⁻¹) * q = φ x := by group
        simpa [h3] using h2
  have hsyl : ∀ Z : Subgroup M, Z ≤ B → IsPGroup p Z → Nat.card A ≤ Nat.card Z →
      ∃ P : Sylow p B, (P : Subgroup B) = Z.subgroupOf B := by
    intro Z hZB hZp hZc
    obtain ⟨P, hP⟩ := (hZp.comap_subtype (K := B)).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    have h1 := hAmax ((P : Subgroup B).map B.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective B.subtype_injective] at h1
    change Nat.card P ≤ Nat.card (Z.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv]
    omega
  set A₂ := A.map (MulAut.conj m).toMonoidHom with hA₂
  have hA₂B : A₂ ≤ B := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨hY.conj_mem a (hAY ha) m, ?_⟩
    have h1 : q * φ a * q⁻¹ ∈ A.map φ :=
      (Subgroup.mem_normalizer_iff.1 hq (φ a)).1 (Subgroup.mem_map_of_mem φ ha)
    simpa [map_mul, map_inv, hm] using h1
  have hA₂p : IsPGroup p A₂ := hAp.map _
  have hA₂card : Nat.card A₂ = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  obtain ⟨P₁, hP₁⟩ := hsyl A hAB hAp le_rfl
  obtain ⟨P₂, hP₂⟩ := hsyl A₂ hA₂B hA₂p (le_of_eq hA₂card.symm)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq B P₁ P₂
  have hc_inv : c⁻¹ • P₂ = P₁ := by
    have := congrArg (fun S => c⁻¹ • S) hc
    simpa using this.symm
  have hfwd_left : ∀ z ∈ A, ((c : M)⁻¹ * m) * z * ((c : M)⁻¹ * m)⁻¹ ∈ A := by
    intro z hz
    have hzA₂ : m * z * m⁻¹ ∈ A₂ := Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hz
    have hzP₂ : (⟨m * z * m⁻¹, hA₂B hzA₂⟩ : B) ∈ (P₂ : Subgroup B) :=
      hP₂ ▸ Subgroup.mem_subgroupOf.mpr hzA₂
    have h2 : (c : B)⁻¹ * (⟨m * z * m⁻¹, hA₂B hzA₂⟩ : B) * ((c : B)⁻¹)⁻¹ ∈
        (P₁ : Subgroup B) := by
      rw [← hc_inv, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj (c : B)⁻¹) _ hzP₂
    rw [hP₁, Subgroup.mem_subgroupOf] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    convert h2 using 1
    group
  have hfwd_right : ∀ z ∈ A, ((c : M)⁻¹ * m)⁻¹ * z * ((c : M)⁻¹ * m) ∈ A := by
    intro z hz
    have hzP₁ : (⟨z, hAB hz⟩ : B) ∈ (P₁ : Subgroup B) :=
      hP₁ ▸ Subgroup.mem_subgroupOf.mpr hz
    have h2 : (c : B) * (⟨z, hAB hz⟩ : B) * (c : B)⁻¹ ∈ (P₂ : Subgroup B) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hzP₁
    rw [hP₂, Subgroup.mem_subgroupOf] at h2
    obtain ⟨w, hwA, hzw⟩ := Subgroup.mem_map.1 h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hzw
    have e : ((c : M)⁻¹ * m)⁻¹ * z * ((c : M)⁻¹ * m) = w := by
      rw [show w = m⁻¹ * (m * w * m⁻¹) * m by group, hzw]
      group
    rw [e]
    exact hwA
  have hmem : (c : M)⁻¹ * m ∈ normalizer (A : Set M) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro y
    constructor
    · exact hfwd_right y
    · intro hy
      have h1 := hfwd_left (((c : M)⁻¹ * m)⁻¹ * y * ((c : M)⁻¹ * m)) hy
      simpa [mul_assoc] using h1
  have hcB : φ (c : M) ∈ A.map φ := (Subgroup.mem_inf.1 c.2).2
  obtain ⟨a, haA, hac⟩ := Subgroup.mem_map.1 hcB
  refine ⟨a * ((c : M)⁻¹ * m), ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.le_normalizer haA) hmem
  · rw [map_mul, map_mul, map_inv, hac, hm]
    group

theorem close16_barSub_normalizer {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {Y A : Subgroup G} (hYM : Y ≤ D.M)
    (hYn : (Y.subgroupOf D.M).Normal) (hAY : A ≤ Y) {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p)
    (hker : ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M ⊥ V)) {q : MulAut (Vtil ⊥ V hV)}
    (hqM : q ∈ Mbar D.M ⊥ V hV)
    (hq : q ∈ normalizer ((barSub ⊥ V hV A : Subgroup (MulAut (Vtil ⊥ V hV))) :
      Set (MulAut (Vtil ⊥ V hV)))) :
    ∃ n : G, n ∈ normalizer (A : Set G) ∧ n ∈ D.M ∧
      ∃ h : n ∈ stabTil ⊥ V, actTil ⊥ V hV ⟨n, h⟩ = q := by
  classical
  have hMn : D.M ≤ normalizer (V : Set G) := hM.trans (stabTil_le_normalizer ⊥ V)
  have hADM : A ≤ D.M := hAY.trans hYM
  let φ : ↥D.M →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hM)
  have hφker : φ.ker = (F11.CTilde D.M ⊥ V).subgroupOf D.M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hMn]
    constructor
    · rintro h1
      exact ⟨x.2, ⟨hM x.2, h1⟩⟩
    · rintro ⟨-, h, h1⟩
      have hx : (⟨(x : G), hM x.2⟩ : ↥(stabTil ⊥ V)) = ⟨(x : G), h⟩ := Subtype.ext rfl
      show actTil ⊥ V hV ⟨(x : G), hM x.2⟩ = 1
      rw [hx]
      exact h1
  have hYker : (Y.subgroupOf D.M) ⊓ φ.ker =
      (Y ⊓ F11.CTilde D.M ⊥ V).subgroupOf D.M := by
    rw [hφker]
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  have hkercard : Nat.card ↥((Y.subgroupOf D.M) ⊓ φ.ker) =
      Nat.card ↥(Y ⊓ F11.CTilde D.M ⊥ V) := by
    rw [hYker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYM)).toEquiv
  have hA'card : Nat.card ↥(A.subgroupOf D.M) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hADM).toEquiv]
    exact hA
  have hA'Y' : A.subgroupOf D.M ≤ Y.subgroupOf D.M := fun x hx => hAY hx
  have hmapA : (A.subgroupOf D.M).map φ = barSub ⊥ V hV A := by
    ext ψ
    constructor
    · intro hψ
      rw [Subgroup.mem_map] at hψ
      obtain ⟨x, hx, rfl⟩ := hψ
      exact actTil_mem_barSub ⊥ V hV hx (hM x.2)
    · intro hψ
      obtain ⟨g, hgA, hgψ⟩ := (mem_barSub ⊥ V hV A ψ).1 hψ
      refine Subgroup.mem_map.2 ⟨⟨(g : G), hADM hgA⟩, hgA, ?_⟩
      change actTil ⊥ V hV ⟨(g : G), hM (hADM hgA)⟩ = ψ
      rw [show (⟨(g : G), hM (hADM hgA)⟩ : ↥(stabTil ⊥ V)) = g from Subtype.ext rfl]
      exact hgψ
  have hrange : φ.range = Mbar D.M ⊥ V hV := by
    ext ψ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), hM x.2⟩, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, congrArg (actTil ⊥ V hV) (Subtype.ext rfl)⟩
  have hq' : q ∈ normalizer (((A.subgroupOf D.M).map φ : Subgroup
      (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [hmapA]
    exact hq
  have hqrange : q ∈ φ.range := by
    rw [hrange]
    exact hqM
  obtain ⟨x, hxN, hxq⟩ :=
    close16_frattini_lift (M := ↥D.M) (Q := MulAut (Vtil ⊥ V hV)) φ hYn hA'Y' hp hA'card
      (by rw [hkercard]; exact hker) hq' hqrange
  have hxnorm : (x : G) ∈ normalizer (A : Set G) := by
    have h1 : x ∈ (normalizer (A : Set G)).subgroupOf D.M := by
      rw [Subgroup.subgroupOf_normalizer_eq hADM]
      exact hxN
    exact h1
  exact ⟨(x : G), hxnorm, x.2, hM x.2, hxq⟩

theorem close16_exists_lift_barSub {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {J : Subgroup G} (hJ : J ≤ D.M)
    {E : Subgroup (MulAut (Vtil ⊥ V hV))} (hE : E ≤ barSub ⊥ V hV J) {p : ℕ} (hp : p.Prime)
    (hEp : IsPGroup p E) :
    ∃ P : Subgroup G, P ≤ J ∧ IsPGroup p P ∧ barSub ⊥ V hV P = E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥J →* ↥(barSub ⊥ V hV J) :=
    MonoidHom.codRestrict ((actTil ⊥ V hV).comp (Subgroup.inclusion (hJ.trans hM)))
      (barSub ⊥ V hV J)
      (fun g => (mem_barSub ⊥ V hV J _).2 ⟨⟨(g : G), (hJ.trans hM) g.2⟩, g.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, hgψ⟩ := (mem_barSub ⊥ V hV J ψ).1 hψ
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    refine Subtype.ext ?_
    show actTil ⊥ V hV ⟨(g : G), (hJ.trans hM) hg⟩ = ψ
    rw [show (⟨(g : G), (hJ.trans hM) hg⟩ : ↥(stabTil ⊥ V)) = g from Subtype.ext rfl]
    exact hgψ
  let E' : Subgroup ↥(barSub ⊥ V hV J) := E.subgroupOf (barSub ⊥ V hV J)
  have hE'p : IsPGroup p E' :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  let Ppre : Subgroup ↥J := E'.comap φ
  let π : ↥Ppre →* ↥E' :=
    (φ.comp Ppre.subtype).codRestrict E' (fun x => x.2)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hφsurj (y : ↥(barSub ⊥ V hV J))
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show φ x ∈ E'
    rw [hx]
    exact y.2
  obtain ⟨T, hT⟩ :=
    CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift p hp π hπsurj hE'p
  let R : Subgroup ↥J := (T : Subgroup ↥Ppre).map Ppre.subtype
  let P : Subgroup G := R.map J.subtype
  have hPJ : P ≤ J := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := (T.isPGroup'.map Ppre.subtype).map J.subtype
  have hRφ : R.map φ = E' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    · intro z hz
      let w : ↥E' := ⟨z, hz⟩
      have hzT : w ∈ (T : Subgroup ↥Ppre).map π := by
        rw [hT]
        exact Subgroup.mem_top w
      obtain ⟨y, hyT, hyz⟩ := Subgroup.mem_map.1 hzT
      refine Subgroup.mem_map.2 ⟨Ppre.subtype y, ⟨y, hyT, rfl⟩, ?_⟩
      have h2 : (π y : ↥(barSub ⊥ V hV J)) = z := by
        simpa [w] using congrArg Subtype.val hyz
      exact (show (φ (Ppre.subtype y) : ↥(barSub ⊥ V hV J)) = π y from rfl).trans h2
  refine ⟨P, hPJ, hPp, ?_⟩
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨g, hgP, hgψ⟩ := (mem_barSub ⊥ V hV P ψ).1 hψ
    obtain ⟨x, hxR, hxg⟩ := Subgroup.mem_map.1 hgP
    obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.1 hxR
    have hyE : (φ (Ppre.subtype y) : MulAut (Vtil ⊥ V hV)) ∈ E :=
      Subgroup.mem_subgroupOf.1 y.2
    have hg_eq : g = ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := by
      apply Subtype.ext
      rw [show (g : G) = (x : G) from hxg.symm,
        show (x : G) = (Ppre.subtype y : G) from (congrArg Subtype.val hyx).symm]
    rw [← hgψ, hg_eq]
    have hArg : (Subgroup.inclusion (hJ.trans hM) (Ppre.subtype y) : ↥(stabTil ⊥ V)) =
        ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := Subtype.ext rfl
    have hφy : (φ (Ppre.subtype y) : MulAut (Vtil ⊥ V hV)) =
        actTil ⊥ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := by
      show actTil ⊥ V hV (Subgroup.inclusion (hJ.trans hM) (Ppre.subtype y)) =
        actTil ⊥ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩
      exact congrArg (actTil ⊥ V hV) hArg
    rwa [hφy] at hyE
  · intro ψ hψ
    have hψE' : (⟨ψ, hE hψ⟩ : ↥(barSub ⊥ V hV J)) ∈ E' :=
      Subgroup.mem_subgroupOf.2 hψ
    let w : ↥E' := ⟨⟨ψ, hE hψ⟩, hψE'⟩
    have hwT : w ∈ (T : Subgroup ↥Ppre).map π := by
      rw [hT]
      exact Subgroup.mem_top w
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.1 hwT
    have hxR : Ppre.subtype y ∈ R := ⟨y, hyT, rfl⟩
    have hgP : ((Ppre.subtype y : ↥J) : G) ∈ P := ⟨Ppre.subtype y, hxR, rfl⟩
    refine (mem_barSub ⊥ V hV P ψ).2
      ⟨⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩, hgP, ?_⟩
    have h1 : actTil ⊥ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ =
        (φ (Ppre.subtype y) : MulAut (Vtil ⊥ V hV)) := rfl
    rw [h1]
    have h2 : (φ (Ppre.subtype y) : ↥(barSub ⊥ V hV J)) = w := by
      have hπ : (φ (Ppre.subtype y) : ↥(barSub ⊥ V hV J)) =
          (π y : ↥(barSub ⊥ V hV J)) := rfl
      exact hπ.trans (congrArg Subtype.val hyeq)
    exact congrArg Subtype.val h2

theorem close16_not_isCyclic_of_barSub {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {P : Subgroup G} (hP : P ≤ D.M)
    (hnc : ¬ IsCyclic ↥(barSub ⊥ V hV P)) : ¬ IsCyclic ↥P := by
  obtain ⟨φ, hφsurj, -⟩ := close16_exists_hom_barSub hM hP
  intro hcyc
  exact hnc (isCyclic_of_surjective φ hφsurj)

theorem close16_card_barSub {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {Y A : Subgroup G} (hYM : Y ≤ D.M) (hAY : A ≤ Y) {p : ℕ}
    (hp : p.Prime) (hA : IsPGroup p A)
    (hker : ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M ⊥ V)) :
    Nat.card ↥(barSub ⊥ V hV A) = Nat.card ↥A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφsurj, hφker⟩ := close16_exists_hom_barSub hM (hAY.trans hYM)
  have hAKbot : A ⊓ F11.CTilde D.M ⊥ V = ⊥ := by
    have hKp : IsPGroup p ↥(A ⊓ F11.CTilde D.M ⊥ V) :=
      IsPGroup.to_le (H := A ⊓ F11.CTilde D.M ⊥ V) (K := A) hA inf_le_left
    have hle : A ⊓ F11.CTilde D.M ⊥ V ≤ Y ⊓ F11.CTilde D.M ⊥ V :=
      inf_le_inf hAY le_rfl
    rcases hKp.card_eq_or_dvd with h1 | hpd
    · exact Subgroup.eq_bot_of_card_eq (H := A ⊓ F11.CTilde D.M ⊥ V) h1
    · exact absurd (hpd.trans (Subgroup.card_dvd_of_le hle)) hker
  have hkerbot : φ.ker = ⊥ := by
    rw [hφker, hAKbot]
    simp
  have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hkerbot
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hφsurj⟩)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
