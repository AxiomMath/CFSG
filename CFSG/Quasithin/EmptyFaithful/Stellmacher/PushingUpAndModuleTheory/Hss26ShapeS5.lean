module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeCases
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push
  CFSG.Quasithin.F53Mod CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G]

theorem exists_twist' [Finite G] {X S Z : Subgroup G} [((zZero X Z).subgroupOf Z).Normal]
    {θ : ↥X →* Perm (Fin 5)} {β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z}
    (hsd : SecData nat X (zZero X Z) Z θ β) (hSX : S ≤ X) (hS2 : IsPGroup 2 S)
    (hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X)
    (hcore : ∀ x : ↥X, (x : G) ∈ pCoreOf 2 X → θ x = 1)
    (hev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Perm.sign (θ x) = 1)
    (hsurj : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → ∃ x : ↥X, θ x = τ) :
    ∃ (Ψ : ↥X →* Perm (Fin 5)) (β' : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z),
      NormData X S Z Ψ β' ∧ ∀ x : ↥X, (x : G) ∈ pCoreOf 2 X → Ψ x = 1 := by
  have hp : IsPGroup 2 ↥(S.subgroupOf X) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  obtain ⟨g, hg⟩ := exists_le_conj_S5Syl (hp.map θ)
  have hkerΨ : ∀ f : ↥X, ((MulAut.conj g⁻¹).toMonoidHom.comp θ) f = 1 ↔ θ f = 1 := fun f =>
    (MulAut.conj g⁻¹).map_eq_one_iff
  have hsgn : ∀ f : ↥X, Perm.sign (((MulAut.conj g⁻¹).toMonoidHom.comp θ) f) = Perm.sign (θ f) :=
    fun f => sign_conj_five _ _
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp θ, β.comp (nat.act (g⁻¹)⁻¹).toMonoidHom,
    ⟨hsd.twist g⁻¹, fun x hx => hker x ((hkerΨ x).mp hx),
      fun x hx => (hsgn x).trans (hev x hx), ?_, ?_⟩, fun x hx => (hkerΨ x).mpr (hcore x hx)⟩
  · intro τ hτ
    obtain ⟨x, hx⟩ := hsurj (g * τ * g⁻¹) (by rw [sign_conj_five]; exact hτ)
    refine ⟨x, ?_⟩
    show g⁻¹ * θ x * g⁻¹⁻¹ = τ
    rw [hx]; group
  · intro x hx
    have h1 : θ x ∈ S5Syl.map (MulAut.conj g).toMonoidHom :=
      hg ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h2 := (mem_map_conj S5Syl g (θ x)).mp h1
    show g⁻¹ * θ x * g⁻¹⁻¹ ∈ S5Syl
    simpa using h2

theorem baum_even [Finite G] {X S Z : Subgroup G} [((zZero X Z).subgroupOf Z).Normal]
    {Ψ : ↥X →* Perm (Fin 5)} {β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z}
    (d : NormData X S Z Ψ β) (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (s : ↥X) (hs : (s : G) ∈ baum S) : Perm.sign (Ψ s) = 1 := by
  classical
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  have hoff := d.offender h hA₀ hA₀Q
  by_contra hsign
  have hsS : (s : G) ∈ S := hs.1
  have hσS : Ψ s ∈ S5Syl := d.syl s hsS
  have hσT : Ψ s ∉ S5T := fun hT =>
    hsign (Equiv.Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp hT).2)
  set Y := Z ⊓ Subgroup.centralizer (A₀ : Set G) with hY
  have hY4 : Y.relIndex Z ≤ 4 := (offender_count h hA₀).trans hoff.2.1
  set J := thompsonJ S with hJdef
  set W := omegaOneCenterOf J with hW
  have hAJ : A₀ ≤ J := le_thompsonJ_of_isMax hA₀
  have hJAQ : J ≤ A₀ ⊔ pCoreOf 2 X := d.thompsonJ_le h hA₀ hA₀Q
  have hYW : Y ≤ W := by
    intro y hy
    have hyZ : y ∈ Z := hy.1
    have hyc : ∀ a ∈ A₀, a * y = y * a := fun a ha => Subgroup.mem_centralizer_iff.mp hy.2 a ha
    have hy2 : y ^ 2 = 1 := h.elemAbelian.2 y hyZ
    have hyS : y ∈ S := h.Z_le hyZ
    have hyA : y ∈ A₀ := by
      have hcl : Subgroup.closure ({y} : Set G) = Subgroup.zpowers y :=
        (Subgroup.zpowers_eq_closure y).symm
      have hel : IsElemAbelian 2 (A₀ ⊔ Subgroup.zpowers y) := by
        refine CFSG.Quasithin.B2F.isElemAbelian_sup_of_commute hA₀.2.1 ?_ ?_
        · rw [← hcl]
          exact CFSG.Quasithin.B2F.isElemAbelian_closure (fun a ha b hb => by
            rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]) (fun a ha => by
            rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hy2)
        · intro a ha b hb
          have hb' : b ∈ Subgroup.centralizer ({a} : Set G) := by
            have : Subgroup.zpowers y ≤ Subgroup.centralizer ({a} : Set G) :=
              (Subgroup.zpowers_le).mpr
                (Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha).symm)
            exact this hb
          exact (Subgroup.mem_centralizer_singleton_iff.mp hb').symm
      have hle : A₀ ⊔ Subgroup.zpowers y ≤ S :=
        sup_le hA₀.1 ((Subgroup.zpowers_le).mpr hyS)
      have hc := hA₀.2.2 _ hle hel
      have heq : A₀ = A₀ ⊔ Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge le_sup_left hc
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hyJ : y ∈ J := hAJ hyA
    have hJc : J ≤ Subgroup.centralizer ({y} : Set G) := by
      refine hJAQ.trans (sup_le (fun a ha => ?_) (fun q hq => ?_))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (h.core_le_centralizer hq y hyZ).symm
    refine Subgroup.subset_closure ⟨⟨hyJ, ?_⟩, hy2⟩
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJc hj))
  have hsc : ∀ y ∈ W, y * (s : G) = (s : G) * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hs.2 y hy
  set D := A₀ ⊔ Subgroup.zpowers (s : G) with hD
  have hDX : D ≤ X := sup_le (hA₀.1.trans h.le_self)
    ((Subgroup.zpowers_le).mpr s.2)
  have hYD : Y ≤ Z ⊓ Subgroup.centralizer (D : Set G) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hDc : D ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun a ha => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hy.2 a ha)
      · refine (Subgroup.zpowers_le).mpr ?_
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hsc y (hYW hy)).symm
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hDc hg)
  have h1 : (Z ⊓ Subgroup.centralizer (D : Set G)).relIndex Z ≤ 4 :=
    (relIndex_le_of_le Z hYD).trans hY4
  have h2 := d.index_le hDX
  have hT : S5T ≤ (D.subgroupOf X).map Ψ := by
    rw [← hoff.1]
    exact Subgroup.map_mono (fun a ha => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha)))
  have hσD : Ψ s ∈ (D.subgroupOf X).map Ψ :=
    ⟨s, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), rfl⟩
  have hThat : S5That ≤ (D.subgroupOf X).map Ψ := by
    have key : ∀ σ ∈ S5SylF, σ ∉ S5TF → swap (0 : Fin 5) 2 * σ⁻¹ ∈ S5TF ∧
        swap (1 : Fin 5) 3 * σ⁻¹ ∈ S5TF := by decide +kernel
    obtain ⟨k1, k2⟩ := key _ ((mem_S5Syl_iff _).mp hσS) (fun hm => hσT ((mem_S5T_iff _).mpr hm))
    refine (Subgroup.closure_le _).mpr ?_
    rintro τ (rfl | rfl)
    · have := Subgroup.mul_mem _ (hT ((mem_S5T_iff _).mpr k1)) hσD
      simpa using this
    · have := Subgroup.mul_mem _ (hT ((mem_S5T_iff _).mpr k2)) hσD
      simpa using this
  have h3 := index_fixW_le nat hThat
  rw [index_fixW_S5That] at h3
  omega

namespace SitSigma

variable {H M S : Subgroup G} [Finite G] {δ μ : Geo H M} {U : Subgroup G}

theorem false_of_s5_natural (hBau3 : BaumannS3 G) (hBau5 : BaumannA5 G) (hA : F53Amalgam H M S)
    (hb : 1 < bMin H M)
    (h : SitSigma δ μ U) (hQ : Qv μ ≤ U) (hR : pCoreOf 2 U ≤ Qv δ)
    (he : Nonempty (OTwoQuot U ≃* Equiv.Perm (Fin 5)))
    (hnat : IsNatSec U (zZero U (CFSG.Quasithin.conjClosure
      (quasithinOmegaOneCenter (Qv μ ⊓ U)) U))
      (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U)) : False := by
  have hPn := stab_le_normalizer_of_le hQ
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hP0 : Qv μ ⊓ U ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ U := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  have hJ := not_le_core_of_noCharNormal hPH hP0 hnc
  obtain ⟨-, hSyl, -⟩ := pu1_s5_natural hPH he hnat hJ
  obtain ⟨e⟩ := he
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := hnat
  obtain ⟨φ₀, hφs, hφk⟩ := exists_hom_of_quot e
  have hle : φ₀.ker ≤ θ.ker := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn hPH _ ((hφk x).mp hx))
  have hker : ∀ x : ↥U, θ x = 1 → (x : G) ∈ pCoreOf 2 U := fun x hx =>
    (hφk x).mp (ker_le_of_surjective hφs hθs hle hx)
  have hcore : ∀ x : ↥U, (x : G) ∈ pCoreOf 2 U → θ x = 1 := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn hPH _ hx)
  have hev : ∀ x : ↥U, (x : G) ∈ pResidualOf 2 U → Perm.sign (θ x) = 1 := fun x hx => by
    obtain ⟨_, hs⟩ := sign_eq_one_of_mem_pResidualOf θ hx
    exact hs
  obtain ⟨Ψ, β', d, hΨcore⟩ := exists_twist' hsd hPH.le_self hPH.sylow.2.1 hker hcore hev
    (fun τ _ => hθs τ)
  set P := Qv μ ⊓ U with hPdef
  set B := baum P with hBdef
  have hBP : B ≤ P := inf_le_left
  have hPU : P ≤ U := inf_le_right
  have hBU : B ≤ U := hBP.trans hPU
  set X := CFSG.Quasithin.conjClosure B U with hXdef
  have hXU : X ≤ U :=
    CFSG.Quasithin.conjClosure_le fun u hu b hb => U.mul_mem (U.mul_mem hu (hBU hb)) (U.inv_mem hu)
  have hXN : U ≤ Subgroup.normalizer (X : Set G) := CFSG.Quasithin.le_normalizer_conjClosure B U
  have hBX : B ≤ X := CFSG.Quasithin.le_conjClosure B U
  have hQX : Qv μ ⊓ X = B := by
    have h2 : IsPGroup 2 (Qv μ ⊓ X : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab μ)).to_le inf_le_left
    exact (hSyl.eq_of_le (le_inf (hBP.trans inf_le_left) hBX) inf_le_right h2)
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  have hWA : omegaOneCenterOf (thompsonJ P) ≤ A₀ := omegaOneCenter_le_of_isMax hA₀
  have hA₀B : A₀ ≤ B := fun a ha => ⟨hA₀.1 ha, Subgroup.mem_centralizer_iff.mpr fun w hw => by
    have := hA₀.2.1.1.is_comm.comm (⟨w, hWA hw⟩ : ↥A₀) ⟨a, ha⟩
    exact congrArg Subtype.val this⟩
  have hBR : ¬ B ≤ pCoreOf 2 U := fun hle' => hA₀Q (hA₀B.trans hle')
  set T5 := (X.subgroupOf U).map Ψ with hT5
  have hS5T : S5T ≤ T5 := by
    rw [← (d.offender hPH hA₀ hA₀Q).1]
    exact Subgroup.map_mono fun a ha => Subgroup.mem_subgroupOf.mpr
      (hBX (hA₀B (Subgroup.mem_subgroupOf.mp ha)))
  have hAlt : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → τ ∈ T5 := by
    obtain ⟨x, hx⟩ := d.surj S5c sign_S5c
    have hcj : F53Push.cj (Ψ x) S5T ≤ T5 := by
      intro τ hτ
      rw [F53Push.mem_cj] at hτ
      obtain ⟨a, ha, hax⟩ := hS5T hτ
      refine ⟨x * a * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hXN x.2) a).mp (Subgroup.mem_subgroupOf.mp ha)
      · rw [map_mul, map_mul, map_inv, hax, hx]; group
    intro τ hτ
    have := alt_le_sup_cj (Or.inl rfl) τ hτ
    rw [← hx] at this
    exact (sup_le hS5T hcj) this
  have hXeven : ∀ x : ↥U, (x : G) ∈ X → Perm.sign (Ψ x) = 1 := by
    have hXle : X ≤ ((Perm.sign.comp Ψ).ker).map U.subtype := by
      refine CFSG.Quasithin.conjClosure_le fun u hu b hb => ?_
      refine ⟨⟨u * b * u⁻¹, U.mul_mem (U.mul_mem hu (hBU hb)) (U.inv_mem hu)⟩, ?_, rfl⟩
      show (Perm.sign.comp Ψ) _ = 1
      have hb1 := baum_even d hPH hJ ⟨b, hBU hb⟩ hb
      have : (⟨u * b * u⁻¹, U.mul_mem (U.mul_mem hu (hBU hb)) (U.inv_mem hu)⟩ : ↥U) =
          ⟨u, hu⟩ * ⟨b, hBU hb⟩ * ⟨u, hu⟩⁻¹ := rfl
      rw [MonoidHom.comp_apply, this, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hb1]
      simp
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hXle hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hXst : X ≤ stab δ := hXU.trans h.le_stab
  have hZδ : Zv μ ≤ Qv δ := by
    apply Zv_le_Qv_of_dist_lt
    have h1 : dist μ δ = 1 := dist_eq_one_iff_adj.mpr (SimpleGraph.Adj.symm h.adj)
    have h2 : bMin H M ≤ bAt μ := bMin_le_bAt μ
    omega
  have hZB : Zv μ ≤ B := fun z hz => ⟨h.R_le_P (h.zle hz), Subgroup.mem_centralizer_iff.mpr
    fun w hw => by
      have hwJ := (omegaOneCenterOf_le_inf (thompsonJ P)) hw
      have hwQ : w ∈ Qv μ := (inf_le_left : P ≤ Qv μ) (thompsonJ_le_self P hwJ.1)
      exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2 w hwQ⟩
  have hRXU : pCoreOf 2 X ≤ pCoreOf 2 U :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXU)
      (hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hRQX : pCoreOf 2 X ≤ Qv δ := hRXU.trans hR
  have hzleX : Zv μ ≤ pCoreOf 2 X := fun z hz =>
    pCoreOf_inf_le hXst ⟨hZδ hz, hBX (hZB hz)⟩
  have hXS : IsSylowTwoOf (Qv μ ⊓ X) X := by rw [hQX]; exact hSyl
  have hgen : X ⊔ (stab δ ⊓ stab μ) = stab δ := by
    refine le_antisymm (sup_le hXst inf_le_left) ?_
    refine h.gen.symm.le.trans (sup_le ?_ le_sup_right)
    refine (pResidualOf_sup_eq_of_sylow h.sylow).symm.le.trans
      (sup_le ?_ ((h.P_le_edge hA).trans le_sup_right))
    intro u hu
    have huU : u ∈ U := pResidualOf_le_self U hu
    have hev' := d.ev ⟨u, huU⟩ hu
    obtain ⟨x', hx', hx'eq⟩ := hAlt _ hev'
    have hq : ((⟨u, huU⟩ * x'⁻¹ : ↥U) : G) ∈ pCoreOf 2 U :=
      d.ker _ (by rw [map_mul, map_inv, hx'eq, mul_inv_cancel])
    have key : ((⟨u, huU⟩ * x'⁻¹ : ↥U) : G) * (x' : G) ∈ (stab δ ⊓ stab μ) ⊔ X :=
      Subgroup.mul_mem_sup ((h.P_le_edge hA) (h.R_le_P hq)) (Subgroup.mem_subgroupOf.mp hx')
    rw [sup_comm]
    simpa using key
  have hXσ : SitSigma δ μ X := ⟨h.adj, hXst, hXS, hzleX, hgen⟩
  have hPnX : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G) := by
    rw [hQX]
    exact hPn.trans (normalizer_le_normalizer_baum P)
  let φ : ↥X →* Perm (Fin 5) := Ψ.comp (Subgroup.inclusion hXU)
  have hφ : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
    intro x
    constructor
    · intro hx
      have h1 : (x : G) ∈ pCoreOf 2 U := d.ker (Subgroup.inclusion hXU x) hx
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_left : X ⊓ pCoreOf 2 U ≤ X) ?_
        (((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 U).to_le inf_le_right :
          IsPGroup 2 (X ⊓ pCoreOf 2 U : Subgroup G))) ⟨x.2, h1⟩
      intro g hg
      have hgU : g ∈ U := hXU hg
      have h2 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U hgU
      have h3 : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hg
      rw [Subgroup.mem_normalizer_iff] at h2 h3 ⊢
      intro y
      exact ⟨fun hy => ⟨(h3 y).mp hy.1, (h2 y).mp hy.2⟩,
        fun hy => ⟨(h3 y).mpr hy.1, (h2 y).mpr hy.2⟩⟩
    · intro hx
      exact hΨcore (Subgroup.inclusion hXU x) (hRXU hx)
  obtain ⟨hrange, -⟩ := hXσ.shape_five hBau3 hBau5 hA hPnX hRQX φ hφ
  have hswap : (swap (0 : Fin 5) 1) ∈ φ.range := by rw [hrange]; exact Subgroup.mem_top _
  obtain ⟨x, hx⟩ := hswap
  have h1 := hXeven (Subgroup.inclusion hXU x) x.2
  have h2 : Ψ (Subgroup.inclusion hXU x) = swap 0 1 := hx
  rw [h2, Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

end SitSigma

end CFSG.Quasithin.F53
