module

public import CFSG.Quasithin.H13.A5Y1367b
public import CFSG.Quasithin.H13.A5Y1367a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

theorem conjAct_mem_normalizer_of_le {G : Type} [Group G] {U W Z : Subgroup G} (hWU : W ≤ U)
    (hZU : Z ≤ Subgroup.normalizer (U : Set G)) (hZW : Z ≤ Subgroup.normalizer (W : Set G))
    {g : G} (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (h : conjAct U ⟨g, hgU⟩ ∈
      Subgroup.normalizer ((autOn Z U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))) :
    conjAct W ⟨g, hgW⟩ ∈
      Subgroup.normalizer ((autOn Z W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) := by
  have key : ∀ (c : G) (hcU : c ∈ Subgroup.normalizer (U : Set G))
      (hcW : c ∈ Subgroup.normalizer (W : Set G)),
      (∀ x ∈ autOn Z U, conjAct U ⟨c, hcU⟩ * x * (conjAct U ⟨c, hcU⟩)⁻¹ ∈ autOn Z U) →
      ∀ x ∈ autOn Z W, conjAct W ⟨c, hcW⟩ * x * (conjAct W ⟨c, hcW⟩)⁻¹ ∈ autOn Z W := by
    intro c hcU hcW hc x hx
    obtain ⟨y, hyZ, rfl⟩ := Setup.mem_autOn_iff.1 hx
    have hyU : (y : G) ∈ Subgroup.normalizer (U : Set G) := hZU hyZ
    have hdU : c * y * c⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcU hyU) (Subgroup.inv_mem _ hcU)
    have h1 : conjAct U ⟨c * y * c⁻¹, hdU⟩ ∈ autOn Z U := by
      have e : (⟨c * y * c⁻¹, hdU⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ⟨c, hcU⟩ * ⟨y, hyU⟩ * (⟨c, hcU⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hc _ (Setup.mem_autOn_iff.2 ⟨⟨y, hyU⟩, hyZ, rfl⟩)
    have h2 := conjAct_mem_autOn_of_le hWU hZW hdU
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcW y.2) (Subgroup.inv_mem _ hcW)) h1
    have e : (⟨c * y * c⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hcW y.2)
        (Subgroup.inv_mem _ hcW)⟩ : ↥(Subgroup.normalizer (W : Set G))) =
        ⟨c, hcW⟩ * y * (⟨c, hcW⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at h2
    exact h2
  have hU1 : ∀ x ∈ autOn Z U, conjAct U ⟨g, hgU⟩ * x * (conjAct U ⟨g, hgU⟩)⁻¹ ∈ autOn Z U :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp h x).mp hx
  have hU2 : ∀ x ∈ autOn Z U, conjAct U ⟨g⁻¹, Subgroup.inv_mem _ hgU⟩ * x *
      (conjAct U ⟨g⁻¹, Subgroup.inv_mem _ hgU⟩)⁻¹ ∈ autOn Z U := by
    intro x hx
    have e : (⟨g⁻¹, Subgroup.inv_mem _ hgU⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        (⟨g, hgU⟩)⁻¹ := rfl
    rw [e, map_inv, inv_inv]
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h) x).mp hx
    rwa [inv_inv] at h3
  refine B6.mem_normalizer_of_forall_mem (key g hgU hgW hU1) fun x hx => ?_
  have h4 := key g⁻¹ (Subgroup.inv_mem _ hgU) (Subgroup.inv_mem _ hgW) hU2 x hx
  have e : (⟨g⁻¹, Subgroup.inv_mem _ hgW⟩ : ↥(Subgroup.normalizer (W : Set G))) =
      (⟨g, hgW⟩)⁻¹ := rfl
  rw [e, map_inv, inv_inv] at h4
  exact h4

theorem coe_autOnHom_apply {G : Type} [Group G] {U L : Subgroup G}
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : ↥L) (u : ↥U) :
    ((((InternalSec.autOnHom hLU l : ↥(autOn L U)) : MulAut ↥U) u : ↥U) : G) =
      l * u * (l : G)⁻¹ :=
  Setup.rho_apply_coe hLU l u

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem HK_le_normalizer_Uv {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    S.HK K ≤ Subgroup.normalizer (S.Uv : Set G) :=
  (S.HK_le_Gv hKG).trans S.Gv_le_normalizer_Uv

theorem HK_le_normalizer_plus (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    autOn (S.HK K) (S.WK K) ≤
      Subgroup.normalizer ((S.plus K : Subgroup (MulAut ↥(S.WK K))) :
        Set (MulAut ↥(S.WK K))) := by
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hHW : S.HK K ≤ Subgroup.normalizer (S.WK K : Set G) := hR.2.1
  have hHU := S.HK_le_normalizer_Uv hKG
  have hWU := S.WK_le_Uv hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  set P : Subgroup G := ((Subgroup.normalizer ((S.plus K : Subgroup (MulAut ↥(S.WK K))) :
    Set (MulAut ↥(S.WK K)))).comap (conjAct (S.WK K))).map
      (Subgroup.normalizer (S.WK K : Set G)).subtype with hP
  have hmem : ∀ {g : G} (hgW : g ∈ Subgroup.normalizer (S.WK K : Set G)),
      conjAct (S.WK K) ⟨g, hgW⟩ ∈ Subgroup.normalizer ((S.plus K : Subgroup
        (MulAut ↥(S.WK K))) : Set (MulAut ↥(S.WK K))) → g ∈ P :=
    fun hgW h => ⟨⟨_, hgW⟩, h, rfl⟩
  have hHP : S.HK K ≤ P := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro k hk
      refine hmem (hHW (hKH hk)) (Subgroup.le_normalizer ?_)
      exact Setup.mem_autOn_iff.2 ⟨⟨k, hHW (hKH hk)⟩, hk, rfl⟩
    · intro l hl
      have hlH : l ∈ S.HK K := (le_sup_right.trans le_sup_left : S.Lv ≤ S.HK K) hl
      refine hmem (hHW hlH) ?_
      have hX := (S.inXz_autOn hK hT).1.2.1
      have hlU : conjAct S.Uv ⟨l, hHU hlH⟩ ∈ Subgroup.normalizer ((autOn K S.Uv :
          Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv)) :=
        hX (Setup.mem_autOn_iff.2 ⟨⟨l, hHU hlH⟩, Subgroup.mem_sup_left hl, rfl⟩)
      exact conjAct_mem_normalizer_of_le hWU (hKH.trans hHU) (hKH.trans hHW) _ _ hlU
    · intro t ht
      refine hmem (hHW (S.Tv_le_HK K ht)) ?_
      exact autOn_le_normalizer_autOn hT
        (Setup.mem_autOn_iff.2 ⟨⟨t, hHW (S.Tv_le_HK K ht)⟩, ht, rfl⟩)
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
  obtain ⟨g', hg', hgg⟩ := hHP hg
  have e : g' = g := Subtype.ext hgg
  rw [← e]
  exact hg'

theorem plus_eq_commutator (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    ⁅S.plus K, autOn (thompsonJ S.Tv) (S.WK K)⁆ = S.plus K := by
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hHW : S.HK K ≤ Subgroup.normalizer (S.WK K : Set G) := hR.2.1
  have hHU := S.HK_le_normalizer_Uv hKG
  have hWU := S.WK_le_Uv hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hJT : thompsonJ S.Tv ≤ S.Tv := iSup₂_le fun _ hA => hA.1
  have hJH : thompsonJ S.Tv ≤ S.HK K := hJT.trans (S.Tv_le_HK K)
  have hX := (S.inXz_autOn hK hT).1.2.2.2.2
  rw [← autOn_commutator (hKH.trans hHU) (hJH.trans hHU)] at hX
  have hle : autOn K (S.WK K) ≤ autOn ⁅K, thompsonJ S.Tv⁆ (S.WK K) :=
    autOn_le_of_autOn_le hWU (hKH.trans hHU)
      ((Subgroup.commutator_le_of_le hKH hJH).trans hHW) hX.ge
  rw [autOn_commutator (hKH.trans hHW) (hJH.trans hHW)] at hle
  refine le_antisymm ?_ hle
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (autOn_le_normalizer_autOn (hJT.trans hT))

theorem plus_le_jStar (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    S.plus K ≤ jStar (S.HK K) S.Tv (S.WK K) := by
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  rw [← S.plus_eq_commutator h1222 h517 hF hK hT, Subgroup.commutator_le]
  intro k hk j hj
  have hkN := le_normalizer_jStar (T := S.Tv) (A4.autOn_mono hKH hk)
  have hjJ := autOn_thompsonJ_le_jStar (S.Tv_le_HK K) hR.2.1 hj
  have e : ⁅k, j⁆ = (k * j * k⁻¹) * j⁻¹ := rfl
  rw [e]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hkN j).mp hjJ)
    (Subgroup.inv_mem _ hjJ)

theorem isQuasisimple_plus (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.IsQuasisimple ↥(S.plus K) := by
  show CFSG.IsQuasisimple ↥(autOn K (S.WK K))
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hHW : S.HK K ≤ Subgroup.normalizer (S.WK K : Set G) := hR.2.1
  have hHU := S.HK_le_normalizer_Uv hKG
  have hWU := S.WK_le_Uv hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) := hKH.trans hHU
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hHW
  set φU := InternalSec.autOnHom hKU with hφU
  set φW := InternalSec.autOnHom hKW with hφW
  have hsU : Function.Surjective φU := InternalSec.autOnHom_surjective hKU
  have hsW : Function.Surjective φW := InternalSec.autOnHom_surjective hKW
  have hker : φU.ker ≤ φW.ker := by
    intro k hk
    rw [InternalSec.mem_ker_autOnHom] at hk ⊢
    exact Subgroup.centralizer_le (fun x hx => hWU hx) hk
  set f₀ : ↥(autOn K S.Uv) →* ↥(autOn K (S.WK K)) := φU.liftOfSurjective hsU ⟨φW, hker⟩ with hf₀
  have hf₀φ : ∀ k, f₀ (φU k) = φW k := fun k => by
    rw [hf₀]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hsf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨k, rfl⟩ := hsW y
    exact ⟨φU k, hf₀φ k⟩
  have hO : CFSG.pCore 2 ↥(autOn K (S.WK K)) = ⊥ := by
    have hKn : ((autOn K (S.WK K)).subgroupOf (autOn (S.HK K) (S.WK K))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (A4.autOn_mono hKH)).2
        (S.HK_le_normalizer_plus h1222 h517 hF hK hT)
    have h1 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
      (autOn K (S.WK K)) (autOn (S.HK K) (S.WK K)) (A4.autOn_mono hKH) hKn
    rw [Setup.pCoreOf_autOn_eq_bot hR] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn K (S.WK K)).subtype_injective).mp
      (le_bot_iff.mp h1)
  have hPker : CFSG.pCore 2 ↥(autOn K S.Uv) ≤ f₀.ker := by
    have h1 : (CFSG.pCore 2 ↥(autOn K S.Uv)).map f₀ ≤ CFSG.pCore 2 ↥(autOn K (S.WK K)) :=
      le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal f₀ hsf₀,
        (CFSG.pCore_isPGroup (p := 2)).map f₀⟩
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    exact h1
  set f₁ := QuotientGroup.lift (CFSG.pCore 2 ↥(autOn K S.Uv)) f₀ hPker with hf₁
  have hsf₁ : Function.Surjective f₁ := by
    intro y
    obtain ⟨x, rfl⟩ := hsf₀ y
    exact ⟨QuotientGroup.mk x, QuotientGroup.lift_mk _ _ _⟩
  obtain ⟨x, hx, hxz⟩ := (S.inXz_autOn hK hT).2
  obtain ⟨k, hk⟩ := hsU ⟨x, hx⟩
  have hxk : ((φU k : ↥(autOn K S.Uv)) : MulAut ↥S.Uv) = x := by rw [hk]
  have hzW : S.z ∈ S.WK K := by
    rw [S.WK_eq hT]
    exact le_conjClosure _ _ (Subgroup.mem_zpowers _)
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hK.2.2.1 hsf₁
    ⟨QuotientGroup.mk (φU k), fun h1 => hxz ?_⟩
  rw [hf₁, QuotientGroup.lift_mk, hf₀φ] at h1
  have h2 := congrArg (fun φ : ↥(autOn K (S.WK K)) =>
    (((φ : MulAut ↥(S.WK K)) ⟨S.z, hzW⟩ : ↥(S.WK K)) : G)) h1
  simp only [OneMemClass.coe_one, MulAut.one_apply] at h2
  rw [hφW, coe_autOnHom_apply] at h2
  rw [← hxk]
  apply Subtype.ext
  rw [hφU, coe_autOnHom_apply]
  exact h2

end Setting

end CFSG.Quasithin.H13.A5
