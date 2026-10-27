module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOpp
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS1Pumpup
public import CFSG.LocalAnalysis.StandardType.GGF4BstarFrame
public import CFSG.LocalAnalysis.StandardType.GGNewPlaneLocalAction
public import CFSG.LocalAnalysis.StandardType.GGTPNC2Final
public import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourR3Comm
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeLabel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Timmesfeld.Transvection.PresSp
import CFSG.Timmesfeld.Orders.ClassicalLinear
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

namespace F4Model

theorem exists_f4DiagramRev :
    ∃ ρ : CoxeterMatrix.F₄.Group ≃* CoxeterMatrix.F₄.Group,
      ∀ i, ρ (CoxeterMatrix.F₄.simple i) = CoxeterMatrix.F₄.simple (Fin.rev i) := by
  have hlab : ∀ i j : Fin 4,
      CoxeterMatrix.F₄ (Fin.rev i) (Fin.rev j) = CoxeterMatrix.F₄ i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  have hl : CoxeterMatrix.F₄.IsLiftable fun i => CoxeterMatrix.F₄.simple (Fin.rev i) := by
    intro i j
    have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow (Fin.rev i) (Fin.rev j)
    rw [CoxeterMatrix.toCoxeterSystem_simple, hlab] at h
    exact h
  set φ : CoxeterMatrix.F₄.Group →* CoxeterMatrix.F₄.Group :=
    CoxeterMatrix.F₄.toCoxeterSystem.lift ⟨_, hl⟩ with hφ
  have hφs : ∀ i, φ (CoxeterMatrix.F₄.simple i) = CoxeterMatrix.F₄.simple (Fin.rev i) := by
    intro i
    have h := CoxeterMatrix.F₄.toCoxeterSystem.lift_apply_simple hl i
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    exact h
  have hφφ : φ.comp φ = MonoidHom.id _ := by
    apply CoxeterMatrix.F₄.toCoxeterSystem.ext_simple
    intro i
    rw [CoxeterMatrix.toCoxeterSystem_simple, MonoidHom.comp_apply, hφs, hφs, Fin.rev_rev,
      MonoidHom.id_apply]
  exact ⟨φ.toMulEquiv φ hφφ hφφ, hφs⟩

theorem le_range_of_card_le_48 {W H : Type} [Group W] [Group H] [Finite H] (R : F4Rep W)
    (φ : W →* H) (hφ : Function.Injective φ) (w : W) {X : Subgroup H}
    (hX : ∀ i : Fin 4, i ≠ 0 → φ (w * R.s i * w⁻¹) ∈ X) (hcard : Nat.card X ≤ 48) :
    X ≤ φ.range := by
  classical
  obtain ⟨hlen, hnd, hne⟩ := f4PCWords_spec
  set ψ : W →* H := φ.comp (MulAut.conj w).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := hφ.comp (MulAut.conj w).injective
  have hmem : ∀ l ∈ f4PCWords, ψ (R.wd l) ∈ X := by
    intro l hl
    have h := R.wd_mem_closure_of_ne (k := 0) (hne l hl) (S := (X.comap ψ : Set W))
      (fun i hi => hX i hi)
    rw [Subgroup.closure_eq] at h
    exact h
  have hinj : ∀ l₁ ∈ f4PCWords, ∀ l₂ ∈ f4PCWords, ψ (R.wd l₁) = ψ (R.wd l₂) → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ h
    have hw : R.wd l₁ = R.wd l₂ := hψinj h
    have hm : evalW l₁ = evalW l₂ := M4.toMat_injective (by rw [← R.rho_wd, ← R.rho_wd, hw])
    exact List.inj_on_of_nodup_map hnd h₁ h₂ hm
  have hnd' : (f4PCWords.map fun l => ψ (R.wd l)).Nodup :=
    List.Nodup.map_on hinj (List.Nodup.of_map evalW hnd)
  set S : Finset H := (f4PCWords.map fun l => ψ (R.wd l)).toFinset with hS
  have hScard : S.card = 48 := by
    rw [hS, List.toFinset_card_of_nodup hnd', List.length_map, hlen]
  have hSX : (S : Set H) ⊆ X := by
    intro z hz
    rw [hS, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    exact hmem l hl
  have heq : (S : Set H) = X := by
    refine Set.eq_of_subset_of_ncard_le hSX ?_
    rw [Set.ncard_coe_finset, hScard, ← Nat.card_coe_set_eq]
    exact hcard
  intro z hz
  have hz' : z ∈ (S : Set H) := by
    rw [heq]
    exact hz
  rw [hS, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hz'
  obtain ⟨l, -, rfl⟩ := hz'
  exact ⟨w * R.wd l * w⁻¹, rfl⟩

end F4Model

open F4Model

section Frame

variable {G : Type} [Group G]

theorem exists_f4Pres_tripleB {Bs : Subgroup G} {W : Subgroup (MulAut ↥Bs)} {p : ℕ}
    (e : CoxeterMatrix.F₄.Group ≃* ↥W)
    (he : ∀ i, GGIsReflection p ((e (CoxeterMatrix.F₄.simple i) : ↥W) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {AL : Subgroup (MulAut ↥Bs)} {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (haR : ∀ k, R.IsRefl (a k)) (ha01 : orderOf (a 0 * a 1) = 3)
    (ha12 : orderOf (a 1 * a 2) = 4) (ha02 : orderOf (a 0 * a 2) = 2)
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) → ((e z : ↥W) : MulAut ↥Bs) ∈ AL) :
    ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥W) (a' : Fin 3 → CoxeterMatrix.F₄.Group)
      (g : CoxeterMatrix.F₄.Group),
      (∀ i, GGIsReflection p ((e' (CoxeterMatrix.F₄.simple i) : ↥W) : MulAut ↥Bs)) ∧
      (∀ z, z ∈ Subgroup.closure (Set.range a') → ((e' z : ↥W) : MulAut ↥Bs) ∈ AL) ∧
      (g * a' 0 * g⁻¹ = R.s 0 ∧ g * a' 1 * g⁻¹ = R.s 1 ∧ g * a' 2 * g⁻¹ = R.s 2) := by
  obtain ⟨g, hg | hg⟩ := R.classify (haR 0) (haR 1) (haR 2) ha01 ha12 ha02
  · exact ⟨e, a, g, he, haL, hg⟩
  obtain ⟨ρ, hρ⟩ := exists_f4DiagramRev
  have hρs : ∀ i, ρ.symm (CoxeterMatrix.F₄.simple (Fin.rev i)) = CoxeterMatrix.F₄.simple i := by
    intro i
    rw [← hρ, MulEquiv.symm_apply_apply]
  have hconj : ∀ t : CoxeterMatrix.F₄.Group,
      ρ.symm g * ρ.symm t * (ρ.symm g)⁻¹ = ρ.symm (g * t * g⁻¹) := by
    intro t
    rw [map_mul, map_mul, map_inv]
  obtain ⟨h0, h1, h2⟩ := hg
  refine ⟨ρ.trans e, fun k => ρ.symm (a k), ρ.symm g, fun i => ?_, fun z hz => ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, hρ]
    exact he _
  · rw [MulEquiv.trans_apply]
    apply haL
    have hle : Subgroup.closure (Set.range fun k => ρ.symm (a k)) ≤
        (Subgroup.closure (Set.range a)).comap ρ.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      show ρ (ρ.symm (a k)) ∈ Subgroup.closure (Set.range a)
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    exact hle hz
  · rw [hconj, h0, hRs, hRs]
    exact hρs 0
  · rw [hconj, h1, hRs, hRs]
    exact hρs 1
  · rw [hconj, h2, hRs, hRs]
    exact hρs 2

end Frame

section Config

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.eq_bstar_of_card_le {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hc : GGConfig p B Bs x L D J)
    (h : Nat.card ↥Bs ≤ p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) :
    B = Bs ∧ Nat.card ↥Bs ≤ p ^ 4 := by
  obtain ⟨⟨-, -, -, -, -, hβ, hS, -⟩, hBs, -⟩ := id hc
  obtain ⟨hp, hEl, hxBs, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hEl.2 x hxBs
  have hcx : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hc.bstar_inf_centralizer_L, Nat.card_zpowers, orderOf_eq_prime hxp hS.2.2.1]
  have h4 : Nat.card ↥Bs ≤ p ^ 4 := by
    rw [hcx] at h
    calc Nat.card ↥Bs ≤ p ^ 3 * p := h
      _ = p ^ 4 := by ring
  refine ⟨Subgroup.eq_of_le_of_card_ge hBs.1 ?_, h4⟩
  rw [hS.1.2.1]
  exact h4.trans (Nat.pow_le_pow_right hp.pos hβ.2.2.2)

end Config

theorem ggHasLabel_C_of_mulEquiv_statedSp {X : Type} [Group X] {n f : ℕ} (hn : 2 ≤ n)
    (hf : 2 ≤ f) (e : X ≃* StatedSp n (GaloisField 2 f)) :
    GGHasLabel ⟨.C, n, f⟩ (X ⧸ Subgroup.center X) := by
  apply ggHasLabel_C_of_statedClassicalModel
  have hZ : Subgroup.center X = ⊥ := by
    have h := CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := GaloisField 2 f)
      (n := n) (by omega)
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rw [h, Subgroup.mem_bot] at hez
    rw [Subgroup.mem_bot]
    exact e.injective (hez.trans (map_one e).symm)
  have hS := CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot
    (K := GaloisField 2 f) n
  refine ⟨⟨Nat.prime_two, by omega, hn, fun h => ?_⟩, GaloisField 2 f, inferInstance,
    inferInstance, GaloisField.card 2 f (by omega), ⟨?_⟩⟩
  · have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (e.trans ((QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot).symm)

section FrameFacts

theorem exists_eq_pow_of_frame_fix {H : Type} [Group H] {p : ℕ} (hp : p.Prime)
    {r u r' : MulAut H} {x d : H} (hxp : x ^ p = 1) (hrx : r x = x) (hr'd : r' d = d)
    (hpl : ∀ z, r z = z → u z = z → ∃ i j : ℕ, z = x ^ i * d ^ j) (hr'x : r (r' x) ≠ r' x)
    {b : H} (hrb : r b = b) (hub : u b = b) (hr'b : r' b = b) : ∃ j : ℕ, b = d ^ j := by
  obtain ⟨i, j, hij⟩ := hpl b hrb hub
  have hxi : x ^ i = 1 := by
    by_contra hne
    have hndvd : ¬ p ∣ i := fun ⟨c, hc⟩ => hne (by rw [hc, pow_mul, hxp, one_pow])
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd).symm hp.one_lt
    have hxk : (x ^ i) ^ m = x := by
      rw [← pow_mul, ← Nat.div_add_mod (i * m) p, hm, pow_add, pow_mul, hxp, one_pow, one_mul,
        pow_one]
    have hr'i : r' (x ^ i) = x ^ i := by
      have h1 := hr'b
      rw [hij, map_mul, map_pow, map_pow, hr'd] at h1
      rw [map_pow]
      exact mul_right_cancel h1
    have hrr'i : r (r' (x ^ i)) = r' (x ^ i) := by
      rw [hr'i, map_pow, hrx]
    apply hr'x
    rw [← hxk, map_pow r' (x ^ i) m, map_pow r (r' (x ^ i)) m, hrr'i]
  exact ⟨j, by rw [hij, hxi, one_mul]⟩

theorem forall_not_mem_zpowers_of_frame {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {W : Subgroup (MulAut ↥Bs)} {V : Type} [Group V] (e : V ≃* ↥W) {xB d : ↥Bs}
    (hopp : ∀ (v : V) (k : ℕ), ((e v : ↥W) : MulAut ↥Bs) d ≠ xB ^ k) :
    ∀ w ∈ W, ∀ b : ↥Bs, (b : G) = (d : G) → ((w b : ↥Bs) : G) ∉ Subgroup.zpowers (xB : G) := by
  intro w hw b hbd hmem
  have hb : b = d := Subtype.ext hbd
  subst hb
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  apply hopp (e.symm ⟨w, hw⟩) k
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  exact hk.symm

end FrameFacts

section Assembly


theorem ggF4QGeFourS1Endpoint_of_frame (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hLim : GGCentralImage .PSp 3 f L)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (he : ∀ i, GGIsReflection p
      ((e (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) →
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    {ga : CoxeterMatrix.F₄.Group}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    (w₂ : CoxeterMatrix.F₄.Group)
    (hv : (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun)
    (hrL : ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (huL : ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs) :
    ∃ (z : G) (A : Subgroup G),
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
        GGCentralImage .PSp 3 f A ∧ GGTableBPosImage p Bs .PSp 3 f A ∧
        ∀ c ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group),
          ((e (w₂ * c * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
            ggAutomizer A Bs := by
  classical
  have hR : GGSecFiveRestHyp p B Bs x L D J := hcfg.1
  have hc : GGConfig p B Bs x L D J := hR.1
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hBsG : GGBstar p B Bs := hc.2.1
  have hf1 : 1 ≤ f := by omega
  have hAind : (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e :=
    ⟨hF4W, he⟩
  have hInnL : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  obtain ⟨ψL0, hlocL⟩ := ggKGPosLocalHypSp_of_f4_mp_of_centralImage ggInnerDiagMpInput_holds hcfg
    hf hpf L (Or.inl rfl) hLim
  obtain ⟨ψL, hkerL, hrangeL, hposL, htorL⟩ := ggKGPosSp_tableBPos_torus hlocL
  obtain ⟨-, -, -, hcardL⟩ := id hposL
  have hrk : (ggU .PSp 3 f).D.rank = 3 := rfl
  rw [hrk] at hcardL
  obtain ⟨hB, hcard4⟩ := hc.eq_bstar_of_card_le hcardL
  obtain ⟨hpx, -, hxBs, hLx, -⟩ := hc.tableB_facts
  have hxne : x ≠ 1 := hc.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨xB, hxB⟩ : ∃ xB : ↥Bs, (xB : G) = x := ⟨⟨x, hxBs⟩, rfl⟩
  have hx1 : xB ≠ 1 := fun h => hxne (by rw [← hxB, h, Subgroup.coe_one])
  have hxL : ∀ φ ∈ ggAutomizer L Bs, φ xB = xB := by
    intro φ hφ
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hg xB, hxB]
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
    rw [hgx]
    group
  have hfr := exists_bstarFrame_at hp2 hEl hNT hcard4 hAind e he R hRs haL hga hx1 hxL w₂ hv
  simp only [hRs] at hfr
  obtain ⟨r, hrdef⟩ : ∃ r : MulAut ↥Bs,
      r = ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : MulAut ↥Bs,
      u = ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  obtain ⟨r', hr'def⟩ : ∃ r' : MulAut ↥Bs,
      r' = ((e (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  rw [← hrdef, ← hudef, ← hr'def] at hfr
  rw [← hrdef] at hrL
  rw [← hudef] at huL
  obtain ⟨d, hrx, hux, hrd, hud, hr'd, hpl, hr'x, hmv, hopp⟩ := hfr
  obtain ⟨n, -, hnN, hn, hnc⟩ := exists_r3comm_s1s3_PSp hcfg hpres hf hpf hLim w₂ hudef hr'def huL
  obtain ⟨J', -, hStd, ⟨hJiso⟩, hnbr, -, hJA, -, hrA, huA, hr'A⟩ :=
    exists_s1OppPumpup (ggPumpupInput_of_lBalance hLB) hc hB hNT hAind hpres le_sup_left hf hpf
      hkerL hrangeL hposL htorL w₂ hrdef hudef hr'def hrL huL hxB hrx hux hrd hud hr'd hpl hr'x
      hmv hnN hn hnc
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'def
  set A : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' with hAdef
  have hc' : GGConfig p B Bs x L D' J' := hR.config_of_stdSub hStd
  have hInnA : GGInnerDiagOn Bs A := hNPLA G p B Bs x L D J hR D' J' hStd d A hnbr
  have hq2 : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hJcard : Nat.card J' = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
    rw [Nat.card_congr hJiso.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hq2]
  have hpJ : p ∣ Nat.card J' := by
    rw [hJcard]
    exact Dvd.dvd.mul_left
      (Dvd.dvd.mul_right (hpf.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)) _) _
  have hI1 : Bs ⊓ Subgroup.centralizer (J' : Set G) ≤ D' := by
    rw [← hB]
    exact hStd.1.2.2.2.2.2.2.ge
  have hΛ : LargeEvenInLambda2 ⟨.C, 2, f⟩ := ⟨by omega, le_rfl, fun _ => hf⟩
  obtain ⟨-, hhA⟩ := ggNbrLabel_c2_of_config hB3 hLB hc' hInnL hInnA hnbr hJA hpJ hI1 hf hpf hΛ
    (ggHasLabel_C_of_mulEquiv_statedSp le_rfl hf hJiso)
  have hAN := isComponentOf_of_isNeighborOf hc'.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hc'.2.2 hnbr)
  have hAimg : GGCentralImage .PSp 3 f A := ggF4Ends_centralImage_PSp hAN.1.2.2.1 hf (Or.inr hhA)
  have hd1 : d ≠ 1 := by
    have h := hopp 1 0
    rwa [map_one, OneMemClass.coe_one, MulAut.one_apply, pow_zero] at h
  have hdG1 : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hBCA : Bs ⊓ Subgroup.centralizer (A : Set G) = Subgroup.zpowers (d : G) := by
    have h := inf_centralizer_eq_zpowers_of_sHat hnbr.1
    rw [hB] at h
    exact h
  have hcardA : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card ↥Bs := by
    rw [hBCA, Nat.card_zpowers, orderOf_eq_prime (hEl.2 _ d.2) hdG1]
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := hc.tableB_facts.2.2.2.2
  obtain ⟨ψA0, hlocA⟩ := ggKGPosLocalHypSp_of_innerDiagOn ggInnerDiagMpInput_holds hpp hp2 hBsG
    hf1 hpf hInnA hAimg hcardA
  obtain ⟨ψA, hkerA, hrangeA, hposA, -⟩ := ggKGPosSp_tableBPos_torus hlocA
  obtain ⟨εA, hεA, -, -⟩ := id hposA
  have hAA48 : Nat.card ↥(ggAutomizer A Bs) = 48 := by
    rw [← Nat.card_congr εA.toEquiv, coxeterMatrix_PSp_three]
    exact (ggCoxeterB_card 3 (by norm_num)).trans (by norm_num [Nat.factorial])
  have hgen : ∀ k : Fin 4, k ≠ 0 →
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom) (w₂ * R.s k * w₂⁻¹) ∈
        ggAutomizer A Bs := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · rw [hRs]
      rw [hudef] at huA
      exact huA
    · rw [hRs]
      rw [hrdef] at hrA
      exact hrA
    · rw [hRs]
      rw [hr'def] at hr'A
      exact hr'A
  have hPC : ∀ c ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group),
      ((e (w₂ * c * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
        ggAutomizer A Bs := by
    have hle : Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group) ≤
        (ggAutomizer A Bs).comap
          (((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom).comp
            (MulAut.conj w₂).toMonoidHom) := by
      rw [Subgroup.closure_le]
      rintro c (rfl | rfl | rfl)
      · exact hgen 1 (by decide)
      · exact hgen 2 (by decide)
      · exact hgen 3 (by decide)
    exact fun c hc => hle hc
  have hAAW : ggAutomizer A Bs ≤ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    have h := le_range_of_card_le_48 R
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective) w₂ (X := ggAutomizer A Bs) hgen hAA48.le
    intro φ hφ
    obtain ⟨v, rfl⟩ := h hφ
    exact (e v).2
  have hWRA : GGWeylReflectionGroup p (ggAutomizer A Bs) := by
    have hWB : GGIsWeylMatrix (CoxeterMatrix.B 3) :=
      Or.inl ⟨3, Equiv.refl _, by omega,
        Or.inr (Or.inl ⟨by norm_num, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩
    refine ⟨_, coxeterMatrix (ggU .PSp 3 f).D.isFiniteType, ?_, εA, hεA⟩
    rw [coxeterMatrix_PSp_three]
    exact hWB
  have hfixA : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer A Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro b hb
    have hxp' : xB ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hxB, Subgroup.coe_one]
      exact hEl.2 x hxBs)
    obtain ⟨j, hbd⟩ := exists_eq_pow_of_frame_fix hpp hxp' hrx hr'd hpl hr'x (hb r hrA) (hb u huA)
      (hb r' hr'A)
    have hdC : (d : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hAN.1.1 hh))
    rw [hbd, Subgroup.coe_pow]
    exact pow_mem hdC j
  have hFL : GGFixLineComp Bs (d : G) A := hc'.fixLineComp_nbr_of_fix hB hnbr hfixA
  have hoppW : ∀ w ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs), ∀ b : ↥Bs, (b : G) = (d : G) →
      ((w b : ↥Bs) : G) ∉ Subgroup.zpowers x := by
    rw [← hxB]
    exact forall_not_mem_zpowers_of_frame e hopp
  have hBsN : Bs ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hB]
    exact hAN.2
  exact ⟨(d : G), A, ⟨hFL, hdG1, hBsN, hAAW, hWRA, hoppW⟩, hAimg, ⟨ψA, hkerA, hrangeA, hposA⟩,
    hPC⟩

theorem ggF4QGeFourOppSp_at (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K)
    (hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hLim : GGCentralImage .PSp 3 f L) :
    ∃ (z : G) (A : Subgroup G),
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
        GGCentralImage .PSp 3 f A := by
  classical
  set W := ggAutomizer L Bs ⊔ ggAutomizer K Bs with hWdef
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : W ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨ψL0, hlocL⟩ := ggKGPosLocalHypSp_of_f4_mp_of_centralImage ggInnerDiagMpInput_holds hcfg
    hf hpf L (Or.inl rfl) hLim
  obtain ⟨ψL, -, -, hposL, -⟩ := ggKGPosSp_tableBPos_torus hlocL
  obtain ⟨εL, hεL, -, -⟩ := hposL
  obtain ⟨e, he⟩ := hWF4
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p W CoxeterMatrix.F₄ e := ⟨hF4W, he⟩
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hM
  obtain ⟨R, hRs0⟩ := exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hRs : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs0 k, CoxeterMatrix.toCoxeterSystem_simple]
  have haR : ∀ k, R.IsRefl (a k) := fun k => (F4Rep.isRefl_iff hRs0).2 (ha k)
  obtain ⟨e', a', g, he', haL', hga⟩ :=
    exists_f4Pres_tripleB e he R hRs haR ha01 ha12 ha02 fun z hz => (haL z).1 hz
  have hrL : ((e' (g⁻¹ * CoxeterMatrix.F₄.simple 2 * g⁻¹⁻¹) : ↥W) : MulAut ↥Bs) ∈
      ggAutomizer L Bs := by
    apply haL'
    rw [show g⁻¹ * CoxeterMatrix.F₄.simple 2 * g⁻¹⁻¹ = a' 2 by rw [← hRs 2, ← hga.2.2]; group]
    exact Subgroup.subset_closure ⟨2, rfl⟩
  have huL : ((e' (g⁻¹ * CoxeterMatrix.F₄.simple 1 * g⁻¹⁻¹) : ↥W) : MulAut ↥Bs) ∈
      ggAutomizer L Bs := by
    apply haL'
    rw [show g⁻¹ * CoxeterMatrix.F₄.simple 1 * g⁻¹⁻¹ = a' 1 by rw [← hRs 1, ← hga.2.1]; group]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  obtain ⟨z, A, hEnd, hCI, -, -⟩ := ggF4QGeFourS1Endpoint_of_frame hLB hB3 hNPLA hcfg hf hpf hLim
    he' R hRs haL' hga g⁻¹
    (Or.inl (by rw [mul_inv_cancel, inv_one, map_one, Matrix.one_mulVec])) hrL huL
  exact ⟨z, A, hEnd, hCI⟩

theorem ggF4QGeFourOppSpInput_of_inputs (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput) : GGF4QGeFourOppSpInput := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb _ _ hWF4 f hf hpf hrL
  exact ggF4QGeFourOppSp_at hLB hB3 hNPLA hR hW hq hNb hWF4 hf hpf hrL

end Assembly

end CFSG.StandardType
