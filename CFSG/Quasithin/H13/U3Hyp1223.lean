module

public import CFSG.Quasithin.H13.U3Transport6
public import CFSG.Quasithin.H13.FiveMenu
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17004
public import Certificates.Certificate17006
public import Certificates.Certificate17951
public import Certificates.Certificate16950
public import Certificates.Certificate18950
public import Certificates.Certificate19953
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem isSimpleGroup_J6
    : IsSimpleGroup J6 := by
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact (MulEquiv.isSimpleGroup_congr (MonoidHom.ofInjective rho6_injective)).1 this

theorem eq_bot_of_isPGroup_of_normal_J6
    {N : Subgroup (GL (Fin 6) (ZMod 2))} (hNJ : N ≤ J6)
    (hN2 : IsPGroup 2 N) (hNn : ∀ j ∈ J6, ∀ n ∈ N, j * n * j⁻¹ ∈ N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_J6
  have hNn' : (N.subgroupOf J6).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J6) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNJ hn⟩ : J6) ∈ N.subgroupOf J6 := hn
    rw [h, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hle : J6 ≤ N := by
      intro σ hσ
      have : (⟨σ, hσ⟩ : J6) ∈ N.subgroupOf J6 := h ▸ mem_top _
      exact this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hN2.to_le hle)
    rw [card_J6] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by decide : 3 ∣ 6048)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem u3_le_reducedAggregate
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) : V ≤ reducedAggregate (L ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : CFSG.IsElementaryAbelian 2 V := hF.2.2.1
  have : CFSG.IsElementaryAbelian 2 V := hVe
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1
  set X := L ⊔ T with hX
  have hXV : X ≤ normalizer (V : Set G) := sup_le hLV hTV
  have hVX : V ≤ X := hF.2.1.trans le_sup_right
  set VX := V.subgroupOf X with hVXdef
  have hVXn : VX.Normal := (normal_subgroupOf_iff_le_normalizer hVX).2 hXV
  have hVXel : CFSG.IsElementaryAbelian 2 VX := IsElementaryAbelian.subgroupOf hVX
  obtain ⟨Φ, -, hΦLs, hΦN⟩ := u3_six_module_transport h1332 hH hU3 hF
  set act := u3ConjLin V (normalizer (V : Set G)) le_rfl
  set ρ : X →* GL (Fin 6) (ZMod 2) :=
    glLin.symm.toMonoidHom.comp ((linConj Φ).toMonoidHom.comp
      (act.comp (Subgroup.inclusion hXV))) with hρ
  have hρapp : ∀ x : X, glLin (ρ x) = linConj Φ (act (Subgroup.inclusion hXV x)) := fun x => by
    simp only [hρ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply]
  have hker : ∀ x : X, ρ x = 1 ↔ x ∈ centralizer (VX : Set X) := by
    intro x
    constructor
    · intro hx
      have h1 : act (Subgroup.inclusion hXV x) = 1 := by
        apply (linConj Φ).injective
        rw [← hρapp, hx, map_one, map_one]
      have h2 := (u3ConjLin_eq_one_iff _).1 h1
      rw [mem_centralizer_iff]
      intro v hv
      apply Subtype.ext
      exact (mem_centralizer_iff.1 h2) v hv
    · intro hx
      apply glLin.injective
      rw [hρapp, map_one]
      have h1 : act (Subgroup.inclusion hXV x) = 1 := by
        rw [u3ConjLin_eq_one_iff]
        rw [mem_centralizer_iff]
        intro v hv
        exact congrArg Subtype.val ((mem_centralizer_iff.1 hx) ⟨v, hVX hv⟩ hv)
      rw [h1, map_one]
  have hρN : ∀ x : X, ρ x ∈ N6 := by
    intro x
    obtain ⟨k, hk, hkx⟩ := hΦN (Subgroup.inclusion hXV x)
    have : ρ x = k := glLin.injective (by rw [hρapp, hkx])
    rw [this]
    exact hk
  have hJimg : ∀ j ∈ J6, ∃ x : X, ρ x = j := by
    intro j hj
    obtain ⟨l, hl, hlj⟩ := hΦLs j hj
    refine ⟨⟨l, le_sup_left (b := T) hl⟩, glLin.injective ?_⟩
    rw [hρapp, ← hlj]
    rfl
  have hmem : VX ∈ primeReducedFamily X 2 := by
    refine ⟨hVXn, hVXel, ?_⟩
    set C := centralizer (VX : Set X) with hC
    set π := QuotientGroup.mk' C with hπ
    set Kt := (CFSG.pCore 2 (X ⧸ C)).comap π with hKt
    have hKtn : Kt.Normal := (CFSG.pCore_normal (p := 2) (G := X ⧸ C)).comap π
    have hKt2 : ∀ k ∈ Kt, ∃ a : ℕ, ρ k ^ 2 ^ a = 1 := by
      intro k hk
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ C)) ⟨π k, hk⟩
      refine ⟨a, ?_⟩
      have h1 : π (k ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      rw [← map_pow]
      exact (hker _).2 h1
    set N : Subgroup (GL (Fin 6) (ZMod 2)) := Kt.map ρ ⊓ J6 with hNdef
    have hN : N = ⊥ := by
      refine eq_bot_of_isPGroup_of_normal_J6 inf_le_right ?_ ?_
      · rintro ⟨n, ⟨k, hk, rfl⟩, -⟩
        obtain ⟨a, ha⟩ := hKt2 k hk
        exact ⟨a, Subtype.ext ha⟩
      · intro σ hσ n hn
        obtain ⟨⟨k, hk, rfl⟩, hnJ⟩ := mem_inf.1 hn
        obtain ⟨x, rfl⟩ := hJimg σ hσ
        exact mem_inf.2 ⟨⟨x * k * x⁻¹, hKtn.conj_mem k hk x, by rw [map_mul, map_mul, map_inv]⟩,
          mul_mem (mul_mem hσ hnJ) (inv_mem hσ)⟩
    have hcomm : ∀ k ∈ Kt, ∀ c ∈ J6, c * ρ k = ρ k * c := by
      intro k hk c hc
      obtain ⟨x, hx⟩ := hJimg c hc
      have hm : ρ (k * x * k⁻¹ * x⁻¹) ∈ N := by
        refine mem_inf.2 ⟨⟨k * x * k⁻¹ * x⁻¹, ?_, rfl⟩, ?_⟩
        · rw [show k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) by group]
          exact mul_mem hk (hKtn.conj_mem k⁻¹ (inv_mem hk) x)
        · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx]
          have hk' : ρ k ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
            rw [normalizer_J6_eq]
            exact hρN k
          exact mul_mem ((mem_normalizer_iff.1 hk' c).1 hc) (inv_mem hc)
      rw [hN, mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv, hx] at hm
      calc c * ρ k = (ρ k * c * (ρ k)⁻¹ * c⁻¹)⁻¹ * (ρ k * c) := by group
        _ = ρ k * c := by rw [hm, inv_one, one_mul]
    have hKtC : Kt ≤ C := by
      intro k hk
      rw [← hker]
      exact eq_one_of_commute_J6 (hcomm k hk)
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hk : k ∈ Kt := hy
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hKtC hk
  have hle := le_sSup hmem
  calc V = VX.map X.subtype := by rw [hVXdef, subgroupOf_map_subtype, inf_eq_left.2 hVX]
    _ ≤ (primeReducedAggregate X 2).map X.subtype := map_mono hle

theorem u3_isIrrPlusIn
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
  obtain ⟨-, -, -, hV64, -, -, hLV, hTV, hirr, hnt, -, -, -⟩ := id hF
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hCL : V ⊓ centralizer (L : Set G) = ⊥ := by
    rcases hirr (V ⊓ centralizer (L : Set G)) inf_le_left
        (fun l hl w hw => by
          rw [show l * w * l⁻¹ = w by
            rw [(mem_centralizer_iff.1 hw.2) l hl, mul_inv_cancel_right]]
          exact hw) with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, v, hv, hlv⟩ := hnt
      have hvC : v ∈ centralizer (L : Set G) := (h.symm ▸ hv : v ∈ V ⊓ _).2
      exact hlv (by rw [(mem_centralizer_iff.1 hvC) l hl, mul_inv_cancel_right])
  have hcomm : ⁅V, L⁆ = V := by
    have hle : ⁅V, L⁆ ≤ V := by
      rw [commutator_le]
      intro v hv l hl
      rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
      exact mul_mem hv ((mem_normalizer_iff.1 (hLV hl) v⁻¹).1 (inv_mem hv))
    have hinv : ∀ l ∈ L, ∀ w ∈ ⁅V, L⁆, l * w * l⁻¹ ∈ ⁅V, L⁆ := by
      intro l hl w hw
      have h1 : (⁅V, L⁆).map (MulAut.conj l).toMonoidHom = ⁅V, L⁆ := by
        rw [Subgroup.map_commutator]
        congr 1
        · ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact (mem_normalizer_iff.1 (hLV hl) y).1 hy
          · intro hx
            refine ⟨l⁻¹ * x * l, ?_, by simp [MulAut.conj_apply]; group⟩
            have := (mem_normalizer_iff.1 (inv_mem (hLV hl)) x).1 hx
            rwa [inv_inv] at this
        · ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact mul_mem (mul_mem hl hy) (inv_mem hl)
          · intro hx
            exact ⟨l⁻¹ * x * l, mul_mem (mul_mem (inv_mem hl) hx) hl,
              by simp [MulAut.conj_apply]; group⟩
      rw [← h1]
      exact ⟨w, hw, rfl⟩
    rcases hirr _ hle hinv with h | h
    · exfalso
      obtain ⟨l, hl, v, hv, hlv⟩ := hnt
      have hm : ⁅l, v⁆ ∈ ⁅V, L⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator hl hv
      rw [h, mem_bot, commutatorElement_def] at hm
      exact hlv (by
        calc l * v * l⁻¹ = l * v * l⁻¹ * v⁻¹ * v := by group
          _ = v := by rw [hm, one_mul])
    · exact h
  refine ⟨u3_le_reducedAggregate h1332 hH hU3 hF, hV1, hLV, hcomm, ?_, ?_, ?_⟩
  · rw [hCL]
    exact bot_lt_iff_ne_bot.2 hV1
  · intro J _ hJV hLJ
    rcases hirr J hJV (fun l hl w hw => (mem_normalizer_iff.1 (hLJ hl) w).1 hw) with h0 | h1
    · left
      rw [h0, hCL]
    · exact Or.inr h1
  · intro J _ hJ _ _
    have hcl : conjClosure V T = V :=
      le_antisymm (conjClosure_le fun t ht v hv => (mem_normalizer_iff.1 (hTV ht) v).1 hv)
        (le_conjClosure V T)
    rw [hcl] at hJ
    exact hJ

theorem u3_hyp1223
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) : Hyp1223 G T L V where
  simple := hH.simple
  nonabelian := hH.nonabelian
  qtke := hH.qtke
  sylow := hH.sylow
  notAlt := fun h' => hH.not_excluded (qt13Excluded_of_alt12_2_2 h')
  maximal := (u3_original_local_maximality_and_unique_normalizer_of_1332 h1332 hH).1.1
  faithful := hH.faithful
  quasisimple := by
    obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm).symm
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup u33Pres_nonabelian)
  normalizes := hF.1
  irrPlus := u3_isIrrPlusIn h1332 hH hU3 hF

end CFSG.Quasithin.H13.U3
