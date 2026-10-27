module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootGamma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_corootPt_of_orth_left {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {a b : ↥Bs} (h : GGCorootOrth p A a b) :
    GGCorootPt p A a := by
  obtain ⟨_, φ, hφA, _, _, hφrefl, hφc, _⟩ := h
  refine ⟨?_, φ, hφA, hφrefl, hφc⟩
  rintro rfl
  have hfix : ∀ x : ↥Bs, φ x = x := by
    intro x
    have hx := hφc x
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
    exact mul_inv_eq_one.mp hx
  have hcard : Nat.card {x : ↥Bs // φ x = x} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun x : ↥Bs => hfix x))
  haveI : Nonempty ↥Bs := ⟨1⟩
  have hp1 : p = 1 := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := ↥Bs))
    calc Nat.card ↥Bs * p = Nat.card {x : ↥Bs // φ x = x} * p := by rw [hcard]
      _ = Nat.card ↥Bs := hφrefl.2
      _ = Nat.card ↥Bs * 1 := by rw [mul_one]
  have hp2 : 2 ≤ p := hp.two_le
  omega

private theorem ggTP_conjAut_eq_of_gamma_eq {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    {n₁ n₂ : G} (hn₁L : n₁ ∈ L) (hn₂L : n₂ ∈ L)
    (hn₁ : n₁ ∈ Subgroup.normalizer (Bs : Set G))
    (hn₂ : n₂ ∈ Subgroup.normalizer (Bs : Set G))
    (h : ∀ b : ↥Bs, ggGamma L hBsN (ggConjAut Bs hn₁ b) =
      ggGamma L hBsN (ggConjAut Bs hn₂ b)) :
    ggConjAut Bs hn₁ = ggConjAut Bs hn₂ := by
  classical
  have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hker]; exact Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := hxmem.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hxmem.2
  have hxpow : ∀ k : ℕ, x ^ k ∈ Bs := fun k => Bs.pow_mem hxBs k
  have hn₂invL : n₂⁻¹ ∈ L := L.inv_mem hn₂L
  have hn₂inv : n₂⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hn₂
  have hnL : n₂⁻¹ * n₁ ∈ L := L.mul_mem hn₂invL hn₁L
  have hn : n₂⁻¹ * n₁ ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ hn₂inv hn₁
  have hγ : ∀ b : ↥Bs,
      ggGamma L hBsN (ggConjAut Bs hn b) = ggGamma L hBsN b := by
    intro b
    have hb₁ : n₁ * (b : G) * n₁⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn₁ b).mp b.2
    have hb₂ : n₂ * (b : G) * n₂⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn₂ b).mp b.2
    have hb₂inv : n₂⁻¹ * (n₁ * (b : G) * n₁⁻¹) * (n₂⁻¹)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hn₂inv (n₁ * (b : G) * n₁⁻¹)).mp hb₁
    have hγ₁ : ggGamma L hBsN (ggConjAut Bs hn₁ b) =
        MulAut.conj (⟨n₁, hn₁L⟩ : ↥L) * ggGamma L hBsN b *
          (MulAut.conj (⟨n₁, hn₁L⟩ : ↥L))⁻¹ := by
      rw [show ggConjAut Bs hn₁ b = ⟨n₁ * (b : G) * n₁⁻¹, hb₁⟩ from
        Subtype.ext (ggConjAut_apply Bs hn₁ b)]
      exact ggGamma_conj L hBsN ⟨n₁, hn₁L⟩ b hb₁
    have hγ₂ : ggGamma L hBsN (ggConjAut Bs hn₂ b) =
        MulAut.conj (⟨n₂, hn₂L⟩ : ↥L) * ggGamma L hBsN b *
          (MulAut.conj (⟨n₂, hn₂L⟩ : ↥L))⁻¹ := by
      rw [show ggConjAut Bs hn₂ b = ⟨n₂ * (b : G) * n₂⁻¹, hb₂⟩ from
        Subtype.ext (ggConjAut_apply Bs hn₂ b)]
      exact ggGamma_conj L hBsN ⟨n₂, hn₂L⟩ b hb₂
    have hγn : ggGamma L hBsN (ggConjAut Bs hn b) =
        MulAut.conj (⟨n₂⁻¹ * n₁, hnL⟩ : ↥L) * ggGamma L hBsN b *
          (MulAut.conj (⟨n₂⁻¹ * n₁, hnL⟩ : ↥L))⁻¹ := by
      have hbn : n₂⁻¹ * n₁ * (b : G) * (n₂⁻¹ * n₁)⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hn b).mp b.2
      rw [show ggConjAut Bs hn b = ⟨n₂⁻¹ * n₁ * (b : G) * (n₂⁻¹ * n₁)⁻¹, hbn⟩ from
        Subtype.ext (ggConjAut_apply Bs hn b)]
      exact ggGamma_conj L hBsN ⟨n₂⁻¹ * n₁, hnL⟩ b hbn
    calc
      ggGamma L hBsN (ggConjAut Bs hn b) =
          MulAut.conj (⟨n₂⁻¹ * n₁, hnL⟩ : ↥L) * ggGamma L hBsN b *
            (MulAut.conj (⟨n₂⁻¹ * n₁, hnL⟩ : ↥L))⁻¹ := hγn
      _ = MulAut.conj (⟨n₂, hn₂L⟩ : ↥L)⁻¹ *
            (MulAut.conj (⟨n₁, hn₁L⟩ : ↥L) * ggGamma L hBsN b *
              (MulAut.conj (⟨n₁, hn₁L⟩ : ↥L))⁻¹) *
            (MulAut.conj (⟨n₂, hn₂L⟩ : ↥L)⁻¹)⁻¹ := by
        rw [show (⟨n₂⁻¹ * n₁, hnL⟩ : ↥L) = (⟨n₂, hn₂L⟩ : ↥L)⁻¹ * ⟨n₁, hn₁L⟩ from
          Subtype.ext (by simp [mul_assoc])]
        rw [map_mul]
        group
      _ = MulAut.conj (⟨n₂, hn₂L⟩ : ↥L)⁻¹ *
            (MulAut.conj (⟨n₂, hn₂L⟩ : ↥L) * ggGamma L hBsN b *
              (MulAut.conj (⟨n₂, hn₂L⟩ : ↥L))⁻¹) *
            (MulAut.conj (⟨n₂, hn₂L⟩ : ↥L)⁻¹)⁻¹ := by
        rw [← hγ₁, h b, hγ₂]
      _ = ggGamma L hBsN b := by
        rw [map_inv, inv_inv]
        group
  have hconjn : ggConjAut Bs hn = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    have hb : ((ggConjAut Bs hn b : ↥Bs) : G) = (n₂⁻¹ * n₁) * (b : G) * (n₂⁻¹ * n₁)⁻¹ :=
      ggConjAut_apply Bs hn b
    obtain ⟨l, hlL, k, hbl⟩ := hBsL b b.2
    have hlBs : l ∈ Bs := by
      have : l = (b : G) * (x ^ k)⁻¹ := by rw [hbl]; group
      rw [this]
      exact Bs.mul_mem b.2 (Bs.inv_mem (hxpow k))
    have hlfix : (n₂⁻¹ * n₁) * l * (n₂⁻¹ * n₁)⁻¹ = l := by
      have hγl : ggGamma L hBsN (ggConjAut Bs hn ⟨l, hlBs⟩) =
          ggGamma L hBsN ⟨l, hlBs⟩ := hγ ⟨l, hlBs⟩
      have huγ : ggGamma L hBsN (ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hγl, mul_inv_cancel]
      have huBs : ((ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) : G) ∈ Bs :=
        (ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹).2
      have huC : ((ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) : G) ∈
          Subgroup.centralizer (L : Set G) :=
        (ggGamma_eq_one_iff L hBsN _).mp huγ
      have huL : ((ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) : G) ∈ L := by
        have hval : ((ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) : G) =
            (n₂⁻¹ * n₁) * l * (n₂⁻¹ * n₁)⁻¹ * l⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply]
        rw [hval]
        exact L.mul_mem (L.mul_mem (L.mul_mem hnL hlL) (L.inv_mem hnL)) (L.inv_mem hlL)
      have huBot : ((ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) : G) ∈
          (⊥ : Subgroup G) := by
        rw [← hxL, Subgroup.mem_inf]
        refine ⟨?_, huL⟩
        rw [← hker, Subgroup.mem_inf]
        exact ⟨huBs, huC⟩
      have hu1 : (ggConjAut Bs hn ⟨l, hlBs⟩ * ⟨l, hlBs⟩⁻¹ : ↥Bs) = 1 :=
        Subtype.ext (Subgroup.mem_bot.mp huBot)
      have := mul_inv_eq_one.mp hu1
      calc (n₂⁻¹ * n₁) * l * (n₂⁻¹ * n₁)⁻¹ = ((ggConjAut Bs hn ⟨l, hlBs⟩ : ↥Bs) : G) :=
          (ggConjAut_apply Bs hn ⟨l, hlBs⟩).symm
        _ = l := congrArg Subtype.val this
    have hnx : (n₂⁻¹ * n₁) * x * (n₂⁻¹ * n₁)⁻¹ = x := by
      have hcomm : (n₂⁻¹ * n₁) * x = x * (n₂⁻¹ * n₁) :=
        Subgroup.mem_centralizer_iff.mp hxC (n₂⁻¹ * n₁) hnL
      calc (n₂⁻¹ * n₁) * x * (n₂⁻¹ * n₁)⁻¹ = x * (n₂⁻¹ * n₁) * (n₂⁻¹ * n₁)⁻¹ := by
            rw [hcomm]
        _ = x := by group
    calc ((ggConjAut Bs hn b : ↥Bs) : G)
        = (n₂⁻¹ * n₁) * ((l : G) * x ^ k) * (n₂⁻¹ * n₁)⁻¹ := by rw [hb, hbl]
      _ = ((n₂⁻¹ * n₁) * l * (n₂⁻¹ * n₁)⁻¹) * ((n₂⁻¹ * n₁) * x ^ k * (n₂⁻¹ * n₁)⁻¹) := by
            group
      _ = l * x ^ k := by rw [hlfix, ← conj_pow, hnx]
      _ = (b : G) := hbl.symm
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  have hbn : ((ggConjAut Bs hn b : ↥Bs) : G) = b := by
    have h1 := congrArg (fun φ : MulAut ↥Bs => ((φ b : ↥Bs) : G)) hconjn
    simpa using h1
  have hbEq : ggConjAut Bs hn b = b := Subtype.ext hbn
  have hcomp : ((ggConjAut Bs hn₂ (ggConjAut Bs hn b) : ↥Bs) : G) =
      ((ggConjAut Bs hn₁ b : ↥Bs) : G) := by
    rw [ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
    group
  calc ((ggConjAut Bs hn₁ b : ↥Bs) : G)
      = ((ggConjAut Bs hn₂ (ggConjAut Bs hn b) : ↥Bs) : G) := hcomp.symm
    _ = ((ggConjAut Bs hn₂ b : ↥Bs) : G) := by rw [hbEq]


theorem ggTPStab_le_automizerJ {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hJS : GGTPJStabInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagAll 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K) (hE : GGE6DepPerpCfg 3 Bs L K)
    (hconj : GGE6DepConjSetting 3 Bs x y L) (hyBs : y ∈ Bs) :
    ∀ φ ∈ ggAutomizer L Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ → φ ∈ ggAutomizer J Bs := by
  classical
  obtain ⟨hZ, hBsL, _, _, _, w, _, _, _, hw, _, _, _, _, _, _, hyL, _, _, horth2, _, _, _, _⟩ :=
    hconj
  obtain ⟨-, hcardBs, -, lab₀, hlab₀, hmarkL, -⟩ := hE
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  obtain ⟨lab, hlab, hhas, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ :=
    largeEvenMarking_exists_hasLabel hmarkL
  rw [hlab_eq] at hlab hhas
  have hM := ggInnerDiagOn_relabel hRig hinn.1 hlab hhas
  obtain ⟨hL, lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = lab₀)
    (fun lab hlab hs => hJS lab (hs ▸ hlab₀) hlab)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hs, hBsN, h3⟩ := hP
  have hJSraw : GGTPJStab R I := hP' hsimple hna
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb
  have hkerB : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  have hkerG : (ggGamma L hBsN).ker =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card (ggGamma L hBsN).ker = 3 := by
    rw [hkerG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcfg.card_bstar_inf_centralizer_L
  have h1 : Nat.card (ggGamma L hBsN).range * 3 = 3 ^ 6 := by
    have h := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hkercard] at h
    rw [h, hcardBs]
  have hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5 := by
    have h2 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h2] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range := le_of_eq hcard.symm
  have h33 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by rw [hcard]; norm_num
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hL θ hBsN hBsI hr h33
  have horth2' : GGCorootOrth 3 (ggAutomizer L Bs) ⟨y, hyBs⟩ ⟨w, hw⟩ := by
    simpa using horth2
  have hc0 : GGCorootPt 3 (ggAutomizer L Bs) ⟨y, hyBs⟩ :=
    ggTP_corootPt_of_orth_left Nat.prime_three horth2'
  have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hkerB]; exact Subgroup.mem_zpowers x
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hxmem.2
  have hxp : x ^ 3 = 1 := hBs.2 x hxmem.1
  have hxLz : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer (p := 3) (by norm_num) hxC hxp hZ
  let A := (ggGamma L hBsN).range
  let c : ↥A := (ggGamma L hBsN).rangeRestrict ⟨y, hyBs⟩
  have hc : GGCorootPt 3 (ggTorusAut A) c :=
    ggCorootPt_gamma (p := 3) Nat.prime_three (by norm_num) hBs hBsN hkerB hxLz hyL hc0
  have hstd := hcfg.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstd.2.2.2.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hnbr.2.1, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have hfix : (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)).map L.subtype =
      L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBsN ⟨y, hyBs⟩
  have hJ0 : IsComponentOf (J.comap L.subtype) (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)) := by
    refine (isComponentOf_comap_of_injective L.subtype (Subgroup.subtype_injective L) ?_).1
    rw [hfix]
    exact hJcomp
  intro φ hφmem hφfixy
  obtain ⟨g, hgL, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφmem
  have hφeq : φ = ggConjAut Bs hgN := MulEquiv.ext fun b => Subtype.ext (hφg b)
  let φA : MulAut ↥A := ggConjAut A (conj_mem_normalizer_range_ggGamma hBsN hgL hgN)
  have hφA_mem : φA ∈ ggTorusAut A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : ↥L →* MulAut ↥L).range) (Bs := A)
      ⟨⟨g, hgL⟩, rfl⟩ (conj_mem_normalizer_range_ggGamma hBsN hgL hgN)
  have hover : GGOverGamma hBsN φ φA := by
    rw [hφeq]
    exact ggOverGamma_conjAut hgL hgN
  have hφA_c : φA c = c := by
    have h1 := hover ⟨y, hyBs⟩
    rw [hφfixy] at h1
    simpa [c] using h1.symm
  have hstep := hJSraw ↥L (ggQuotHom θ) A hTB hcard hZ c hc
    (J.comap L.subtype) hJ0
  have hmemA : φA ∈ ggAutomizer ((J.comap L.subtype).map
      (MulAut.conj : ↥L →* MulAut ↥L)) A :=
    hstep φA hφA_mem hφA_c
  obtain ⟨h, hhH, hhN, hhval⟩ := mem_ggAutomizer_iff.mp hmemA
  obtain ⟨j0, hj0JL, hj0eq⟩ := Subgroup.mem_map.mp hhH
  have hj0N : MulAut.conj j0 ∈
      Subgroup.normalizer (A : Set (MulAut ↥L)) := by
    simpa [hj0eq] using hhN
  have hj0val : ∀ a : ↥A, ((φA a : ↥A) : MulAut ↥L) =
      MulAut.conj j0 * (a : MulAut ↥L) * (MulAut.conj j0)⁻¹ := by
    intro a
    have hh := hhval a
    rwa [← hj0eq] at hh
  have hj0J : (j0 : G) ∈ J := by
    simpa [Subgroup.mem_subgroupOf] using hj0JL
  have hj0NBs : (j0 : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range (p := 3) Nat.prime_three
      hBsN hBs hkerB hZ hBsL j0.2 hj0N
  have hgamma : ∀ b : ↥Bs,
      ggGamma L hBsN (ggConjAut Bs hgN b) =
        ggGamma L hBsN (ggConjAut Bs hj0NBs b) := by
    intro b
    have hov := hover b
    rw [hφeq] at hov
    have hovL : (ggGamma L hBsN (ggConjAut Bs hgN b) : MulAut ↥L) =
        (φA ((ggGamma L hBsN).rangeRestrict b) : MulAut ↥L) :=
      congrArg Subtype.val hov
    have hh := hj0val ((ggGamma L hBsN).rangeRestrict b)
    have hb : (j0 : G) * (b : G) * (j0 : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hj0NBs b).mp b.2
    have hgc : (ggGamma L hBsN (ggConjAut Bs hj0NBs b) : MulAut ↥L) =
        MulAut.conj j0 * (ggGamma L hBsN b) * (MulAut.conj j0)⁻¹ := by
      have hbEq : ggConjAut Bs hj0NBs b =
          ⟨(j0 : G) * (b : G) * (j0 : G)⁻¹, hb⟩ :=
        Subtype.ext (ggConjAut_apply Bs hj0NBs b)
      rw [hbEq]
      exact ggGamma_conj L hBsN j0 b hb
    calc (ggGamma L hBsN (ggConjAut Bs hgN b) : MulAut ↥L)
        = (φA ((ggGamma L hBsN).rangeRestrict b) : MulAut ↥L) := hovL
      _ = MulAut.conj j0 * ((ggGamma L hBsN).rangeRestrict b : MulAut ↥L) *
            (MulAut.conj j0)⁻¹ := hh
      _ = MulAut.conj j0 * (ggGamma L hBsN b) * (MulAut.conj j0)⁻¹ := rfl
      _ = (ggGamma L hBsN (ggConjAut Bs hj0NBs b) : MulAut ↥L) := hgc.symm
  have hconjAut_eq : ggConjAut Bs hgN = ggConjAut Bs hj0NBs :=
    ggTP_conjAut_eq_of_gamma_eq hBsN hkerB hxLz hBsL hgL j0.2 hgN hj0NBs hgamma
  have hφeqj : φ = ggConjAut Bs hj0NBs := by
    rw [hφeq, hconjAut_eq]
  rw [hφeqj]
  exact ggConjAut_mem_ggAutomizer hj0J hj0NBs

end CFSG.StandardType

end
