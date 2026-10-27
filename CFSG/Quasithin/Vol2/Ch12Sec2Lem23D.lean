module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem23C
public import CFSG.Quasithin.Background.L3SplitNat
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22Q
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

theorem L3_fix3 (γ : L3.Γ) (h3 : γ ^ 3 = 1) (h1 : γ ≠ 1) :
    ∃ v : L3.Vec, v ≠ 0 ∧ L3.act γ v = v := by
  obtain ⟨g, hg⟩ := L3Small.conj_c₀ γ h3 h1
  have hc₀ : L3.act L3Small.c₀ (fun _ => 1) = fun _ => 1 := by
    unfold L3.act L3Small.c₀
    decide +kernel
  have hne : (fun _ => 1 : L3.Vec) ≠ 0 := by decide
  refine ⟨L3.act g (fun _ => 1), fun h0 => hne ?_, ?_⟩
  · have := congrArg (L3.act g⁻¹) h0
    rwa [L3.act_inv_act, L3.act_zero] at this
  · rw [← hg, L3.act_mul, L3.act_mul, L3.act_inv_act, hc₀]

variable {G : Type} [Group G] [Finite G]

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem false_of_extra3
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) : False := by
  classical
  set Y := yY L V H P with hYdef
  set R₀ := rR V H P with hR₀def
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  obtain ⟨hHs, -⟩ := e.pre
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  obtain ⟨-, -, htop, ⟨hcommV, hnatV⟩, -⟩ := e.concl
  obtain ⟨DV⟩ := hnatV.toL3Coord
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := e.hyp.irrPlus.2.2.1
  have hYQ := e.yY_le_CT h331 h1222
  have hYcomm := e.comm_yY_CT h331 h1222
  have hYsq := e.sq_yY h331 h1222
  have hVY := e.V_le_yY
  have hLY : L ≤ Subgroup.normalizer ((Y : Subgroup G) : Set G) := L_le_normalizer_yY
  set N : Subgroup ↥Y := V.subgroupOf Y with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgT : (g : G) ∈ T := (hYQ g.2).1
    exact (Subgroup.mem_normalizer_iff.mp (hTV hgT) n).mp hn⟩
  have hmkeq : ∀ a b : ↥Y, ((a : ↥Y ⧸ N) = (b : ↥Y ⧸ N)) ↔ (a : G)⁻¹ * b ∈ V := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hcommA : ∀ a b : ↥Y ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y₁ =>
      induction b using QuotientGroup.induction_on with
      | H y₂ =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmkeq]
        have h1 := hYcomm y₁ y₁.2 y₂ (hYQ y₂.2)
        show ((y₁ : G) * y₂)⁻¹ * (y₂ * y₁) ∈ V
        have e1 : ((y₁ : G) * y₂)⁻¹ * (y₂ * y₁) =
            ((y₁ : G) * y₂)⁻¹ * ((y₂ : G) * y₁ * (y₂ : G)⁻¹ * (y₁ : G)⁻¹) * ((y₁ : G) * y₂) := by
          group
        rw [e1]
        have h2 : (y₂ : G) * y₁ * (y₂ : G)⁻¹ * (y₁ : G)⁻¹ ∈ V := h1
        have hyT : (y₁ : G) * y₂ ∈ T := T.mul_mem (hYQ y₁.2).1 (hYQ y₂.2).1
        have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hyT)) _).mp h2
        simpa using this
  let _ : CommGroup (↥Y ⧸ N) := { (inferInstance : Group (↥Y ⧸ N)) with mul_comm := hcommA }
  have hLYm : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y := fun l hl y hy =>
    (Subgroup.mem_normalizer_iff.mp (hLY hl) y).mp hy
  let cY : ↥L → (↥Y →* ↥Y) := fun l =>
    { toFun := fun y => ⟨l * y * l⁻¹, hLYm l l.2 y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (l : G) * (a * b) * (l : G)⁻¹ = (l * a * (l : G)⁻¹) * (l * b * (l : G)⁻¹)
        group) }
  have hcYN : ∀ l : ↥L, N ≤ N.comap (cY l) := by
    intro l y hy
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hy
    exact (Subgroup.mem_normalizer_iff.mp (hLV l.2) _).mp hy
  let actA : ↥L → (↥Y ⧸ N →* ↥Y ⧸ N) := fun l => QuotientGroup.map N N (cY l) (hcYN l)
  have hactmk : ∀ l (y : ↥Y), actA l (y : ↥Y ⧸ N) =
      ((⟨l * y * l⁻¹, hLYm l l.2 y y.2⟩ : ↥Y) : ↥Y ⧸ N) := fun _ _ => rfl
  let _ : MulDistribMulAction ↥L (↥Y ⧸ N) :=
    { smul := fun l a => actA l a
      one_smul := fun a => by
        induction a using QuotientGroup.induction_on with
        | H y =>
          show actA 1 (y : ↥Y ⧸ N) = y
          rw [hactmk]
          congr 1
          apply Subtype.ext
          simp
      mul_smul := fun l₁ l₂ a => by
        induction a using QuotientGroup.induction_on with
        | H y =>
          show actA (l₁ * l₂) (y : ↥Y ⧸ N) = actA l₁ (actA l₂ y)
          rw [hactmk, hactmk, hactmk]
          congr 1
          apply Subtype.ext
          show (l₁ * l₂ : G) * y * (l₁ * l₂ : G)⁻¹ = l₁ * (l₂ * y * (l₂ : G)⁻¹) * (l₁ : G)⁻¹
          group
      smul_one := fun l => map_one (actA l)
      smul_mul := fun l a b => map_mul (actA l) a b }
  let σ : ↥L →* MulAut (↥Y ⧸ N) := MulDistribMulAction.toMulAut ↥L (↥Y ⧸ N)
  have hσmk : ∀ l (y : ↥Y), σ l (y : ↥Y ⧸ N) =
      ((⟨l * y * l⁻¹, hLYm l l.2 y y.2⟩ : ↥Y) : ↥Y ⧸ N) := fun _ _ => rfl
  have hπbij : Function.Bijective DV.π := ⟨DV.π_injective, DV.π_surj⟩
  let eπ : L3.Γ ≃* ↥(autOn L V) := MulEquiv.ofBijective DV.π hπbij
  have hactV : ∀ l : ↥L, A4.actionOn V L hLV l ∈ autOn L V := fun l =>
    (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩
  let actV : ↥L →* ↥(autOn L V) := (A4.actionOn V L hLV).codRestrict (autOn L V) hactV
  let πL : ↥L →* L3.Γ := eπ.symm.toMonoidHom.comp actV
  have hρπ : ∀ l : ↥L, DV.rho (πL l) = A4.actionOn V L hLV l := by
    intro l
    have h1 : DV.π (eπ.symm (actV l)) = actV l := eπ.apply_symm_apply (actV l)
    show ((DV.π (eπ.symm (actV l)) : ↥(autOn L V)) : MulAut ↥V) = _
    rw [h1]
    rfl
  have hπs : Function.Surjective πL := by
    intro γ
    obtain ⟨⟨l, hlN⟩, hl, hlγ⟩ := DV.rho_mem γ
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
    apply DV.rho_injective
    rw [hρπ]
    exact hlγ
  have hπker : ∀ l : ↥L, πL l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro l
    rw [← A4.actionOn_eq_one_iff hLV, ← hρπ]
    constructor
    · intro h0
      rw [h0, map_one]
    · intro h0
      exact DV.rho_injective (by rw [h0, map_one])
  have hker : πL.ker ≤ σ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have hlC := (hπker l).mp hl
    have hlQ : (l : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
      e.centralizer_le_CT h1222 ⟨l.2, hlC⟩
    ext a
    induction a using QuotientGroup.induction_on with
    | H y =>
      show σ l (y : ↥Y ⧸ N) = (y : ↥Y ⧸ N)
      rw [hσmk, hmkeq]
      have h1 := hYcomm y y.2 l hlQ
      show ((l : G) * y * (l : G)⁻¹)⁻¹ * y ∈ V
      have e1 : ((l : G) * y * (l : G)⁻¹)⁻¹ * y =
          (y : G)⁻¹ * ((l : G) * y * (l : G)⁻¹ * (y : G)⁻¹)⁻¹ * y := by group
      rw [e1]
      have hyT : (y : G) ∈ T := (hYQ y.2).1
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hyT)) _).mp (V.inv_mem h1)
      simpa using this
  set ρA : L3.Γ →* MulAut (↥Y ⧸ N) := (πL.liftOfSurjective hπs) ⟨σ, hker⟩ with hρAdef
  have hρA : ∀ l, ρA (πL l) = σ l := fun l =>
    πL.liftOfRightInverse_comp_apply _ _ ⟨σ, hker⟩ l
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Φ := isCyclic_of_prime_card e.cardΦ
  obtain ⟨⟨z, hzΦ⟩, hgenz⟩ := hcyc.exists_generator
  have hz1 : z ≠ 1 := by
    intro h0
    have h3 : Nat.card Φ = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgenz a)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgenz b)
      rw [← hi, ← hj]
      have h1 : (⟨z, hzΦ⟩ : ↥Φ) = 1 := Subtype.ext h0
      rw [h1, one_zpow, one_zpow]
    rw [e.cardΦ] at h3
    norm_num at h3
  have hΦL := e.frattini_le h331 h1222
  have hzL : z ∈ L := hΦL hzΦ
  have hz3 : z ^ 3 = 1 := e.exp z (frattini_map_le P hzΦ)
  set c : L3.Γ := πL ⟨z, hzL⟩ with hcdef
  have hc3 : c ^ 3 = 1 := by
    have h1 : (⟨z, hzL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hcdef, ← map_pow, h1, map_one]
  have hρc : ρA c = σ ⟨z, hzL⟩ := hρA _
  have hR₀Y : R₀ ≤ Y := fun r hr => Subgroup.subset_closure ⟨1, L.one_mem, r, hr, by group⟩
  set E : Subgroup (↥Y ⧸ N) := (R₀.subgroupOf Y).map (QuotientGroup.mk' N) with hEdef
  have hE4 : Nat.card E = 4 := by
    have h1 := B1More.card_map_mul_card_inf_ker (R₀.subgroupOf Y) (QuotientGroup.mk' N)
    have h2 : R₀.subgroupOf Y ⊓ (QuotientGroup.mk' N).ker = (R₀ ⊓ V).subgroupOf Y := by
      rw [QuotientGroup.ker_mk']
      ext y
      simp [Subgroup.mem_subgroupOf, hNdef]
    have h3 : Nat.card ↥((R₀ ⊓ V).subgroupOf Y) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hR₀Y)).toEquiv,
        hR₀def, e.rR_inf_V, e.card_inf]
    have h4 : Nat.card ↥(R₀.subgroupOf Y) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀Y).toEquiv, hR₀def,
        e.card_rR h331 h1222]
    rw [h2, h3, h4, ← hEdef] at h1
    omega
  have hmkmul : ∀ a b : ↥Y, ((a : ↥Y ⧸ N) * (b : ↥Y ⧸ N)) = ((a * b : ↥Y) : ↥Y ⧸ N) :=
    fun a b => (QuotientGroup.mk_mul N a b).symm
  have hmkinv : ∀ a : ↥Y, ((a : ↥Y ⧸ N))⁻¹ = ((a⁻¹ : ↥Y) : ↥Y ⧸ N) :=
    fun a => (QuotientGroup.mk_inv N a).symm
  have hmemE : ∀ y : ↥Y, (y : G) ∈ R₀ → (y : ↥Y ⧸ N) ∈ E := fun y hy =>
    ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hcE : ∀ x : ↥Y ⧸ N, ρA c x * x⁻¹ ∈ E := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [hρc, hσmk, hmkinv, hmkmul]
      apply hmemE
      exact e.comm_CT_mem_rR h331 h1222 z hzΦ y (hYQ y.2)
  have hzR : ∀ a ∈ R₀, z * a * z⁻¹ ∈ R₀ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (e.frattini_le_normalizer_rR h331 h1222 hzΦ) a).mp ha
  have hfixR : ∀ a ∈ R₀, z * a * z⁻¹ = a → a = 1 := fun a ha hza =>
    e.rR_fix h331 h1222 hzΦ hz1 ha hza
  have hEc : ∀ x ∈ E, ∃ y, ρA c y * y⁻¹ = x := by
    rintro _ ⟨⟨r, hrY⟩, hr, rfl⟩
    replace hr : r ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
    obtain ⟨b, hb, hbr⟩ := exists_eq_inv_mul_conj hzR hfixR r hr
    refine ⟨((⟨b, hR₀Y hb⟩ : ↥Y) : ↥Y ⧸ N), ?_⟩
    rw [hρc, hσmk, mul_comm, hmkinv, hmkmul]
    congr 1
    exact Subtype.ext hbr.symm
  have hgenU : ∀ U' : Subgroup (↥Y ⧸ N), (∀ γ, ∀ u ∈ U', ρA γ u ∈ U') → E ≤ U' → U' = ⊤ := by
    intro U' hU' hEU'
    rw [eq_top_iff]
    intro a _
    induction a using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨y, hy⟩ := y
      have key : ∀ g (hg : g ∈ Y), ((⟨g, hg⟩ : ↥Y) : ↥Y ⧸ N) ∈ U' := by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨l, hl, r, hr, rfl⟩ := hx
          have h1 := hU' (πL ⟨l, hl⟩) _ (hEU' (hmemE ⟨r, hR₀Y hr⟩ hr))
          rw [hρA, hσmk] at h1
          exact h1
        | one => exact U'.one_mem
        | mul a b ha hb iha ihb =>
          have := U'.mul_mem iha ihb
          rw [hmkmul] at this
          exact this
        | inv a ha iha =>
          have := U'.inv_mem iha
          rw [hmkinv] at this
          exact this
      exact key y hy
  have hA2 : ∀ a : ↥Y ⧸ N, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H y =>
      rw [hmkmul]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hYsq y y.2))
  have hWL := e.W_le h331 h1222
  obtain ⟨hWc, hW2⟩ := e.W_elem h1222
  have hWnot : ¬ conjClosure (V ⊓ pCoreOf 2 H) P ≤ Subgroup.centralizer (V : Set G) := by
    intro h0
    have h1 : R₀ = conjClosure (V ⊓ pCoreOf 2 H) P := inf_eq_left.mpr h0
    have h2 := e.card_rR h331 h1222
    rw [← hR₀def, h1, e.card_W h331 h1222] at h2
    norm_num at h2
  obtain ⟨w₀, hw₀W, hw₀C⟩ := IsConcreteLE.not_le_iff_exists.mp hWnot
  have hw₀L : w₀ ∈ L := hWL hw₀W
  set a₀ : L3.Γ := πL ⟨w₀, hw₀L⟩ with ha₀def
  have ha₀ : L3.IsInvol a₀ := by
    refine ⟨?_, fun h0 => hw₀C ((hπker _).mp h0)⟩
    have h1 : (⟨w₀, hw₀L⟩ : ↥L) * ⟨w₀, hw₀L⟩ = 1 :=
      Subtype.ext (by show w₀ * w₀ = 1; rw [← pow_two]; exact hW2 w₀ hw₀W)
    rw [ha₀def, ← map_mul, h1, map_one]
  have hfixE : ∀ x ∈ E, ρA a₀ x = x := by
    rintro _ ⟨⟨r, hrY⟩, hr, rfl⟩
    replace hr : r ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
    rw [ha₀def, hρA]
    show σ ⟨w₀, hw₀L⟩ ((⟨r, hrY⟩ : ↥Y) : ↥Y ⧸ N) = _
    rw [hσmk]
    congr 1
    apply Subtype.ext
    show w₀ * r * w₀⁻¹ = r
    rw [hWc w₀ hw₀W r hr.1]
    group
  obtain ⟨α, β, hβ⟩ := L3Split.natural_of hA2 ρA hc3 hE4 hcE hEc hgenU ha₀ hfixE
  have hρinj : ∀ γ, ρA γ = 1 → γ = 1 := by
    intro γ hγ
    have h1 : ∀ v : L3.Vec, L3.act (α γ) v = v := by
      intro v
      obtain ⟨x, hx⟩ := β.surjective (Multiplicative.ofAdd v)
      have h2 := hβ γ x
      rw [hγ, MulAut.one_apply, hx] at h2
      have h3 := congrArg Multiplicative.toAdd h2
      simp only [toAdd_ofAdd] at h3
      exact h3.symm
    have h3 : α γ = 1 := L3.act_injective _ h1
    exact α.injective (h3.trans (map_one α).symm)
  have hc1 : c ≠ 1 := by
    intro h0
    apply hz1
    have hzC : z ∈ Subgroup.centralizer (V : Set G) := (hπker _).mp h0
    exact e.eq_one_of_comm_inf hzΦ fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp hzC) u hu.1).symm
  obtain ⟨-, hΦV₀, -⟩ := e.eq_inf
  have hzV₀ : ∀ a ∈ V ⊓ pCoreOf 2 H, z * a * z⁻¹ ∈ V ⊓ pCoreOf 2 H := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hΦV₀ hzΦ) a).mp ha
  have hfixV₀ : ∀ a ∈ V ⊓ pCoreOf 2 H, z * a * z⁻¹ = a → a = 1 := fun a ha hza =>
    hfixR a (e.V0_le_rR ha) hza
  have hzfixR : ∀ a ∈ R₀, a⁻¹ * (z * a * z⁻¹) ∈ V → a ∈ V := by
    intro a ha hav
    have hav' : a⁻¹ * (z * a * z⁻¹) ∈ V ⊓ pCoreOf 2 H := by
      rw [← e.rR_inf_V]
      exact ⟨R₀.mul_mem (R₀.inv_mem ha) (hzR a ha), hav⟩
    obtain ⟨b, hb, hbe⟩ := exists_eq_inv_mul_conj hzV₀ hfixV₀ _ hav'
    have hab : b * a⁻¹ ∈ R₀ := R₀.mul_mem (e.V0_le_rR hb) (R₀.inv_mem ha)
    have hfx : z * (b * a⁻¹) * z⁻¹ = b * a⁻¹ := by
      have e1 : z * a * z⁻¹ = a * (b⁻¹ * (z * b * z⁻¹)) := by
        rw [← hbe]
        group
      calc z * (b * a⁻¹) * z⁻¹ = (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ := by group
        _ = (z * b * z⁻¹) * (a * (b⁻¹ * (z * b * z⁻¹)))⁻¹ := by rw [e1]
        _ = b * a⁻¹ := by group
    have h1 := hfixR _ hab hfx
    have h2 : a = b := (mul_inv_eq_one.mp h1).symm
    rw [h2]
    exact hb.1
  obtain ⟨v₀, hv₀0, hv₀⟩ := L3_fix3 (α c) (by rw [← map_pow, hc3, map_one])
    (fun h0 => hc1 (α.injective (h0.trans (map_one α).symm)))
  set p : ↥Y ⧸ N := β.symm (Multiplicative.ofAdd v₀) with hpdef
  have hp1 : p ≠ 1 := by
    intro h0
    apply hv₀0
    have h1 := congrArg β h0
    rw [hpdef, MulEquiv.apply_symm_apply, map_one] at h1
    exact congrArg Multiplicative.toAdd h1
  have hpc : ρA c p = p := by
    apply β.injective
    rw [hβ, hpdef, MulEquiv.apply_symm_apply, toAdd_ofAdd, hv₀]
  have hpE : p ∉ E := by
    rintro ⟨⟨r, hrY⟩, hr, hrp⟩
    replace hr : r ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
    apply hp1
    have h1 := hpc
    rw [← hrp, QuotientGroup.mk'_apply, hρc, hσmk, hmkeq] at h1
    have h2 : r⁻¹ * (z * r * z⁻¹) ∈ V := by
      have := V.inv_mem h1
      convert this using 1
      show r⁻¹ * (z * r * z⁻¹) = ((z * r * z⁻¹)⁻¹ * r)⁻¹
      group
    have h3 := hzfixR r hr h2
    rw [← hrp, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h3)
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective p
  have hy₀T : (y₀ : G) ∈ T := (hYQ y₀.2).1
  have hy₀z : (z * y₀ * z⁻¹)⁻¹ * y₀ ∈ V := by
    have h1 := hpc
    rw [← hy₀, hρc, hσmk] at h1
    exact (hmkeq _ _).mp h1
  have hv₀'V : (y₀ : G)⁻¹ * z * y₀ * z⁻¹ ∈ V := by
    have := V.inv_mem hy₀z
    convert this using 1
    group
  have hv₀'R : (y₀ : G)⁻¹ * z * y₀ * z⁻¹ ∈ R₀ := by
    have h1 := e.comm_CT_mem_rR h331 h1222 z hzΦ y₀ (hYQ y₀.2)
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (e.T_le_normalizer_rR h331 h1222 (T.inv_mem hy₀T)) _).mp h1
    convert h2 using 1
    group
  have hv₀'V₀ : (y₀ : G)⁻¹ * z * y₀ * z⁻¹ ∈ V ⊓ pCoreOf 2 H := by
    rw [← e.rR_inf_V]
    exact ⟨hv₀'R, hv₀'V⟩
  obtain ⟨b, hb, hbe⟩ := exists_eq_inv_mul_conj hzV₀ hfixV₀ _ hv₀'V₀
  have hc₁Y : (y₀ : G) * b⁻¹ ∈ Y := Y.mul_mem y₀.2 (Y.inv_mem (hVY hb.1))
  set c₁ : G := (y₀ : G) * b⁻¹ with hc₁
  have hc₁z : z * c₁ * z⁻¹ = c₁ := by
    have h1 : z * y₀ * z⁻¹ = y₀ * ((y₀ : G)⁻¹ * z * y₀ * z⁻¹) := by group
    calc z * c₁ * z⁻¹ = (z * y₀ * z⁻¹) * (z * b * z⁻¹)⁻¹ := by rw [hc₁]; group
      _ = y₀ * ((y₀ : G)⁻¹ * z * y₀ * z⁻¹) * (z * b * z⁻¹)⁻¹ := by rw [h1]
      _ = y₀ * (b⁻¹ * (z * b * z⁻¹)) * (z * b * z⁻¹)⁻¹ := by rw [hbe]
      _ = c₁ := by rw [hc₁]; group
  have hc₁p : ((⟨c₁, hc₁Y⟩ : ↥Y) : ↥Y ⧸ N) = p := by
    rw [← hy₀, hmkeq]
    show ((y₀ : G) * b⁻¹)⁻¹ * y₀ ∈ V
    have e1 : ((y₀ : G) * b⁻¹)⁻¹ * y₀ = b := by group
    rw [e1]
    exact hb.1
  have hR₀V : ¬ R₀ ≤ V := by
    intro h0
    have h1 : Nat.card ↥(R₀ ⊓ V) = Nat.card ↥R₀ := by rw [inf_eq_left.mpr h0]
    rw [hR₀def, e.rR_inf_V, e.card_inf, e.card_rR h331 h1222] at h1
    norm_num at h1
  obtain ⟨r₀, hr₀R, hr₀V⟩ := IsConcreteLE.not_le_iff_exists.mp hR₀V
  have hr₀1 : ((⟨r₀, hR₀Y hr₀R⟩ : ↥Y) : ↥Y ⧸ N) ≠ 1 := by
    intro h0
    apply hr₀V
    have := (QuotientGroup.eq_one_iff _).mp h0
    exact Subgroup.mem_subgroupOf.mp this
  have hβr₀ : Multiplicative.toAdd (β ((⟨r₀, hR₀Y hr₀R⟩ : ↥Y) : ↥Y ⧸ N)) ≠ 0 := by
    intro h0
    apply hr₀1
    apply β.injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd h0
  obtain ⟨γ', hγ'⟩ := L3_transitive _ _ hβr₀ hv₀0
  obtain ⟨l, hl⟩ := hπs (α.symm γ')
  have hlr : σ l ((⟨r₀, hR₀Y hr₀R⟩ : ↥Y) : ↥Y ⧸ N) = p := by
    rw [← hρA, hl]
    apply β.injective
    rw [hβ, MulEquiv.apply_symm_apply, hγ', hpdef, MulEquiv.apply_symm_apply]
  have hlrV : ((l : G) * r₀ * (l : G)⁻¹)⁻¹ * c₁ ∈ V := by
    have h1 := hlr
    rw [hσmk, ← hc₁p, hmkeq] at h1
    exact h1
  have hc₁2 : c₁ * c₁ = 1 := by
    set x := (l : G) * r₀ * (l : G)⁻¹ with hx
    set v' := x⁻¹ * c₁ with hv'
    have hxY : x ∈ Y := hLYm l l.2 r₀ (hR₀Y hr₀R)
    have hxC : x ∈ Subgroup.centralizer (V : Set G) := (hYQ hxY).2
    have hx2 : x * x = 1 := by
      have h1 : r₀ * r₀ = 1 := by rw [← pow_two]; exact (e.rR_elem h1222).2 r₀ hr₀R
      rw [hx]
      calc (l : G) * r₀ * (l : G)⁻¹ * ((l : G) * r₀ * (l : G)⁻¹) = l * (r₀ * r₀) * (l : G)⁻¹ := by
            group
        _ = 1 := by rw [h1]; group
    have hv'2 : v' * v' = 1 := by rw [← pow_two]; exact hV2 v' hlrV
    have hxv : x * v' = v' * x := ((Subgroup.mem_centralizer_iff.mp hxC) v' hlrV).symm
    have hc₁e : c₁ = x * v' := by rw [hv']; group
    rw [hc₁e]
    calc x * v' * (x * v') = x * (v' * x) * v' := by group
      _ = x * (x * v') * v' := by rw [hxv]
      _ = (x * x) * (v' * v') := by group
      _ = 1 := by rw [hx2, hv'2, one_mul]
  obtain ⟨vm, m, hvmV, -, hmv, hmP, -, hminv, -, -, -⟩ := e.exists_m h331 h1222
  obtain ⟨hV₀Z, -, -⟩ := e.eq_inf
  have hHW := e.le_normalizer_W h331 h1222
  have hWZ := e.W_le_center
  have hvmT : vm ∈ T := hVT hvmV
  have hmT : m ∈ T := by
    have h0 := T.mul_mem (hQT hmv) hvmT
    simpa using h0
  have hwm : ∀ w ∈ conjClosure (V ⊓ pCoreOf 2 H) P,
      w * m * w⁻¹ * m⁻¹ ∈ V ⊓ pCoreOf 2 H := by
    intro w hw
    have hvw : vm * w * vm⁻¹ ∈ conjClosure (V ⊓ pCoreOf 2 H) P :=
      (Subgroup.mem_normalizer_iff.mp (hHW (hTH hvmT)) w).mp hw
    have hqc : (m * vm⁻¹) * (vm * w * vm⁻¹) = (vm * w * vm⁻¹) * (m * vm⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hWZ hvw).2) _ hmv
    have e1 : m * w * m⁻¹ = vm * w * vm⁻¹ := by
      calc m * w * m⁻¹ = (m * vm⁻¹) * (vm * w * vm⁻¹) * (m * vm⁻¹)⁻¹ := by group
        _ = (vm * w * vm⁻¹) * (m * vm⁻¹) * (m * vm⁻¹)⁻¹ := by rw [hqc]
        _ = vm * w * vm⁻¹ := by group
    have h1 : w * vm * w⁻¹ * vm⁻¹ ∈ V := by
      have h0 : w * vm * w⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hTV (hQT (hWZ hw).1)) vm).mp hvmV
      exact V.mul_mem h0 (V.inv_mem hvmV)
    have h2 : w * vm * w⁻¹ * vm⁻¹ ∈ pCoreOf 2 H := by
      have h0 : vm * w⁻¹ * vm⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH hvmT)) _).mp
          ((pCoreOf 2 H).inv_mem (hWZ hw).1)
      have e2 : w * vm * w⁻¹ * vm⁻¹ = w * (vm * w⁻¹ * vm⁻¹) := by group
      rw [e2]
      exact (pCoreOf 2 H).mul_mem (hWZ hw).1 h0
    have e3 : w * m * w⁻¹ * m⁻¹ = w * vm * w⁻¹ * vm⁻¹ := by
      have e4 : w * m * w⁻¹ * m⁻¹ = w * (m * w * m⁻¹)⁻¹ := by group
      rw [e4, e1]
      group
    rw [e3]
    exact ⟨h1, h2⟩
  have hmemz : ∀ f ∈ Φ, ∃ k : ℤ, z ^ k = f := fun f hf => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgenz ⟨f, hf⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hc₁zc : z * c₁ = c₁ * z := by
    calc z * c₁ = (z * c₁ * z⁻¹) * z := by group
      _ = c₁ * z := by rw [hc₁z]
  have hc₁Φ : ∀ f ∈ Φ, c₁ * f = f * c₁ := by
    intro f hf
    obtain ⟨k, rfl⟩ := hmemz f hf
    exact (Commute.zpow_left hc₁zc k).symm
  have hc₁T : c₁ ∈ T := (hYQ hc₁Y).1
  have hc₁Q : c₁ * c₁ ∈ pCoreOf 2 H := by
    rw [hc₁2]
    exact (pCoreOf 2 H).one_mem
  have hwc : ∀ w ∈ conjClosure (V ⊓ pCoreOf 2 H) P, w * c₁ * w⁻¹ * c₁⁻¹ ∈ V := by
    intro w hw
    rcases e.mem_or_of_inv h331 h1222 hmT hmP hminv hc₁T hc₁Q hc₁Φ with h1 | h1
    · have hcw : c₁ * w = w * c₁ := (Subgroup.mem_centralizer_iff.mp (hWZ hw).2) c₁ h1
      have e1 : w * c₁ * w⁻¹ * c₁⁻¹ = 1 := by
        calc w * c₁ * w⁻¹ * c₁⁻¹ = (c₁ * w) * w⁻¹ * c₁⁻¹ := by rw [hcw]
          _ = 1 := by group
      rw [e1]
      exact V.one_mem
    · have hq'w : (c₁ * m⁻¹) * w = w * (c₁ * m⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hWZ hw).2) _ h1
      have h2 := hwm w hw
      have hq'c : (c₁ * m⁻¹) * (w * m * w⁻¹ * m⁻¹) = (w * m * w⁻¹ * m⁻¹) * (c₁ * m⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hV₀Z h2).2) _ h1
      have e1 : w * c₁ * w⁻¹ * c₁⁻¹ =
          (c₁ * m⁻¹) * (w * m * w⁻¹ * m⁻¹) * (c₁ * m⁻¹)⁻¹ := by
        calc w * c₁ * w⁻¹ * c₁⁻¹ = (w * (c₁ * m⁻¹)) * m * w⁻¹ * m⁻¹ * (c₁ * m⁻¹)⁻¹ := by group
          _ = ((c₁ * m⁻¹) * w) * m * w⁻¹ * m⁻¹ * (c₁ * m⁻¹)⁻¹ := by rw [hq'w]
          _ = (c₁ * m⁻¹) * (w * m * w⁻¹ * m⁻¹) * (c₁ * m⁻¹)⁻¹ := by group
      rw [e1, hq'c, mul_inv_cancel_right]
      exact h2.1
  have hA8 : Nat.card (↥Y ⧸ N) = 8 := by
    rw [Nat.card_congr β.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hEi : E.index = 2 := by
    have h1 := Subgroup.card_mul_index E
    rw [hE4, hA8] at h1
    omega
  have hWA : ∀ w (hw : w ∈ conjClosure (V ⊓ pCoreOf 2 H) P), ∀ x : ↥Y ⧸ N,
      σ ⟨w, hWL hw⟩ x = x := by
    intro w hw
    have hfE : ∀ x ∈ E, σ ⟨w, hWL hw⟩ x = x := by
      rintro _ ⟨⟨r, hrY⟩, hr, rfl⟩
      replace hr : r ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
      rw [QuotientGroup.mk'_apply, hσmk]
      congr 1
      apply Subtype.ext
      show w * r * w⁻¹ = r
      rw [hWc w hw r hr.1]
      group
    have hfp : σ ⟨w, hWL hw⟩ p = p := by
      rw [← hc₁p, hσmk, hmkeq]
      have h1 := hwc w hw
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hc₁T)) _).mp (V.inv_mem h1)
      convert h2 using 1
      show (w * c₁ * w⁻¹)⁻¹ * c₁ = c₁⁻¹ * (w * c₁ * w⁻¹ * c₁⁻¹)⁻¹ * c₁⁻¹⁻¹
      group
    intro x
    by_cases hx : x ∈ E
    · exact hfE x hx
    · have h1 : p⁻¹ * x ∈ E := by
        rw [Subgroup.mul_mem_iff_of_index_two hEi]
        exact iff_of_false (fun h0 => hpE (by simpa using E.inv_mem h0)) hx
      have e1 : x = p * (p⁻¹ * x) := by group
      rw [e1, map_mul, hfp, hfE _ h1]
  have hσw₀ : σ ⟨w₀, hw₀L⟩ = 1 := by
    ext x
    exact hWA w₀ hw₀W x
  apply ha₀.2
  apply hρinj
  rw [ha₀def, hρA]
  exact hσw₀

end Extra3

end Lem22

theorem lem12223ExtraL32_proved
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) :
    Lem12223ExtraL32 := by
  intro G _ _ T L V H P U I h hyp hNE hC hpre hUO hcard hexp hΦ3 hZ hΦV hVΦ hcent hV₀Z hV₀C _
    _ _ _ _ _ _
  have hX1 : V ⊓ pCoreOf 2 H ≠ ⊥ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := hpre
    intro h0
    have hle : U ⊓ V ≤ V ⊓ pCoreOf 2 H := fun x hx => ⟨hx.2, hUO hx.1⟩
    have hUV0 : U ⊓ V = ⊥ := le_bot_iff.mp (hle.trans (le_of_eq h0))
    have h1 := Subgroup.relIndex_mul_card (U ⊓ V) V
    rw [hidx, inf_assoc, inf_idem, hUV0, Subgroup.card_bot, hC.2.1] at h1
    norm_num at h1
  have hΦX : (frattini ↥P).map P.subtype ≤
      Subgroup.normalizer ((V ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    obtain ⟨-, -, -, -, -, hPH, -⟩ := hpre
    intro f hf
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hΦV hf, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hPH (Lem22.frattini_map_le P hf))⟩
  exact Lem22.Extra3.false_of_extra3 h331 h1222
    ⟨hyp, hNE, hC, hpre, hUO, hcard, hexp, hΦ3, hZ, hΦV, hVΦ, hcent,
      ⟨V ⊓ pCoreOf 2 H, hX1, le_inf inf_le_left hV₀Z, hΦX, hV₀C⟩⟩

end CFSG.Quasithin.H13
