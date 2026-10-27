module

public import CFSG.Quasithin.Vol2.Ch3T326B
public import CFSG.Quasithin.Vol2.Ch3T326E
public import CFSG.Quasithin.Vol2.Ch3T326F
public import CFSG.Quasithin.Vol2.Ch10SecCWD
public import CFSG.Quasithin.Vol2.Ch10SecC3A
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Vol2.Ch3T325I
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp

public section

namespace CFSG.Quasithin.H13.Lem3313F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement
open T325 (V₀_le_V V_le_VM T_le_NV isSylowTwoOf_of_le onA_le_normalizer
  actCompat_inclusion_autOn map_mem_irrPlusOn biSup_smul_eq_of_actCompat actCompat_autOn_onA
  mem_cComp_of_quasisimple map_subgroupOf_conjAct qhatOf_autSub_autOn_le)

variable {G : Type} [Group G] [Finite G]

theorem exists_isHStar {T M H : Subgroup G} (hH : InH T H) (hHM : ¬ H ≤ M) :
    ∃ H' : Subgroup G, IsHStar T M H' := by
  obtain ⟨H', ⟨hH1, hH2⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {X : Subgroup G | InH T X ∧ ¬ X ≤ M} ⟨H, hH, hHM⟩
  refine ⟨H', hH1, hH2, fun Y hY hYH hYM => ?_⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM⟩ (lt_of_le_of_ne hYH hne)

theorem exists_ctx (h323 : Stmt3_2_3) (h36 : A36ForSQTK) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    {T L : Subgroup G} (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hne : L ≠ conjClosure L T) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ Subgroup.normalizer (conjClosure L T : Set G)) :
    ∃ V₀ : Subgroup G, T326.Ctx T L V₀ := by
  obtain ⟨⟨hmaxM, hTM⟩, ⟨-, huniq⟩, -⟩ := h323 G T L hs hn hq hT hmax hf hLq
  obtain ⟨V₀, hfsu⟩ := Vol2.Ch10.stmtFSUChoice_of_a36 h323 h36 G T L hs hn hq hT hmax hf hLq
  have h3222 := Vol2.Ch10.tmpL6_3_2_2_two_of h3228 h323
  have h1 : IsTwoReducedIn (fsuM T L) (fsuVM T L V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 (h3222 G T L V₀ hfsu)
  obtain ⟨hVLT, hredV, hO⟩ := h3228 G T L V₀ hfsu
  have h2 : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hredV⟩
  refine ⟨V₀, hfsu, hne, hmaxM, ⟨⟨hmaxM, ?_⟩, fun M' hM' => huniq M' hM'.1 ?_⟩,
    exists_isHStar hH hHM, h1, h2, hO⟩
  · exact sup_le ((le_conjClosure L T).trans Subgroup.le_normalizer) hTM
  · exact sup_le ((T326.conjClosure_le_sup T L).trans hM'.2) (le_sup_right.trans hM'.2)

namespace CtxV

variable {T L V₀ : Subgroup G} (c : T326.Ctx T L V₀)
include c

theorem L_le_NV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
  c.L_le_L₀.trans c.L₀_le_NV

theorem pCoreOf_L_le : pCoreOf 2 L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) :=
  c.pCoreOf_L_le.trans (Subgroup.centralizer_le (V_le_VM T (conjClosure L T) V₀))

theorem not_le_centralizer : ¬ L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := by
  set V := conjClosure V₀ T with hV
  intro h
  have hL₀ : conjClosure L T ≤ Subgroup.centralizer (V : Set G) := by
    refine conjClosure_le fun s hs l hl => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hsv : s⁻¹ * v * s ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (T_le_NV T V₀ (T.inv_mem hs)) v).mp hv
      simpa using this
    have hl' := Subgroup.mem_centralizer_iff.mp (h hl) _ hsv
    calc v * (s * l * s⁻¹) = s * ((s⁻¹ * v * s) * l) * s⁻¹ := by group
      _ = s * (l * (s⁻¹ * v * s)) * s⁻¹ := by rw [hl']
      _ = s * l * s⁻¹ * v := by group
  apply c.V₀_ne_bot
  rw [← c.comm_V₀, eq_bot_iff, Subgroup.commutator_le]
  intro v hv l hl
  have := Subgroup.mem_centralizer_iff.1 (hL₀ hl) v (V₀_le_V T V₀ hv)
  rw [Subgroup.mem_bot, commutatorElement_def, this]
  group

theorem quasi : CFSG.IsQuasisimple ↥(autOn L (conjClosure V₀ T)) := by
  refine isQuasisimple_autOn (L_le_NV c) c.fsu.quasisimple
    (fun x hx => pCoreOf_L_le c ⟨x, ?_, rfl⟩) ?_
  · try with_reducible rfl
    exact hx
  · by_contra hcon
    push Not at hcon
    exact not_le_centralizer c fun l hl => hcon l hl

theorem commute_autOn (hA37 : Vol2Native.A37ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {a b : MulAut ↥(conjClosure V₀ T)}
    (ha : a ∈ autOn L (conjClosure V₀ T))
    (hb : b ∈ autOn (CFSG.conjugate L t) (conjClosure V₀ T)) : a * b = b * a := by
  set V := conjClosure V₀ T with hV
  obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp ha
  obtain ⟨x, hxL, rfl⟩ := Setup.mem_autOn_iff.mp hb
  have hcomm : ⁅(g : G), (x : G)⁆ ∈ Subgroup.centralizer (V : Set G) :=
    pCoreOf_L_le c (Vol2.Ch10.SecA.commutator_conjugate_le_of_fsu hA37 c.fsu ht htn
      (Subgroup.commutator_mem_commutator hgL hxL)).1
  ext v
  rw [MulAut.mul_apply, MulAut.mul_apply]
  simp only [Setup.coe_conjAct_apply]
  set u := (x : G) * ((g : G) * v * (g : G)⁻¹) * (x : G)⁻¹ with hu
  have huV : u ∈ V := by
    have hgv : (g : G) * v * (g : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2
    exact (Subgroup.mem_normalizer_iff.mp x.2 _).mp hgv
  have hc := Subgroup.mem_centralizer_iff.mp hcomm u huV
  rw [commutatorElement_def] at hc
  calc (g : G) * ((x : G) * v * (x : G)⁻¹) * (g : G)⁻¹ =
        (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ * u * ((g : G) * x * (g : G)⁻¹ * (x : G)⁻¹)⁻¹ := by
          rw [hu]; group
    _ = u := by rw [← hc]; group

omit [Finite G] c in
theorem conjAct_mem_autOn {s : G} (hs : s ∈ T) :
    conjAct (conjClosure V₀ T) ⟨s⁻¹, T_le_NV T V₀ (T.inv_mem hs)⟩ ∈
      autOn T (conjClosure V₀ T) :=
  Setup.mem_autOn_iff.2 ⟨_, T.inv_mem hs, rfl⟩

theorem autOn_L₀_eq (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(conjClosure V₀ T)] {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    autOn (conjClosure L T) (conjClosure V₀ T) =
      autOn L (conjClosure V₀ T) ⊔
        conjAutSub (conjAct (conjClosure V₀ T) ⟨s⁻¹, T_le_NV T V₀ (T.inv_mem hs)⟩)
          (autOn L (conjClosure V₀ T)) := by
  set V := conjClosure V₀ T with hV
  have hLs : CFSG.conjugate L s ≤ Subgroup.normalizer (V : Set G) :=
    (Vol2.Ch10.SecA.conjugate_le_fsuL0 hs).trans c.L₀_le_NV
  have e : autOn (conjClosure L T) V = autOn (L ⊔ CFSG.conjugate L s) V :=
    congrArg (fun X => autOn X V) (c.L₀_eq hA37 hA38 hs hsn)
  rw [e, H13.autOn_sup (L_le_NV c) hLs]
  exact congrArg (autOn L V ⊔ ·) (T326.autOn_conjugate (L_le_NV c) (T_le_NV T V₀ (T.inv_mem hs)))

theorem not_mem_normalizer (hA37 : Vol2Native.A37ForSQTKCat)
    [IsMulCommutative ↥(conjClosure V₀ T)] {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    conjAct (conjClosure V₀ T) ⟨s⁻¹, T_le_NV T V₀ (T.inv_mem hs)⟩ ∉
      Subgroup.normalizer (autOn L (conjClosure V₀ T) : Set _) := by
  set V := conjClosure V₀ T with hV
  set K := autOn L V with hK
  set t := conjAct V ⟨s⁻¹, T_le_NV T V₀ (T.inv_mem hs)⟩ with ht
  intro htn
  have hconj : autOn (CFSG.conjugate L s) V = conjAutSub t K :=
    T326.autOn_conjugate (L_le_NV c) (T_le_NV T V₀ (T.inv_mem hs))
  have hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have hy' : t⁻¹ * y * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set (MulAut ↥V))).inv_mem htn) y).mp hy
      rwa [inv_inv] at this
    have hyc : y ∈ autOn (CFSG.conjugate L s) V := by
      rw [hconj]
      show y ∈ K.map (MulAut.conj t).toMonoidHom
      refine Subgroup.mem_map.2 ⟨t⁻¹ * y * t, hy', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact commute_autOn c hA37 hs hsn hx hyc
  have hq := quasi c
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  have hbot : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hab y hy x hx
  rw [hperf] at hbot
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hbot

omit [Finite G] c in
theorem orbSup_eq [IsMulCommutative ↥(conjClosure V₀ T)] :
    orbSup (autOn T (conjClosure V₀ T)) (V₀.subgroupOf (conjClosure V₀ T)) =
      (conjClosure V₀ T).subgroupOf (conjClosure V₀ T) := by
  rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA T)]
  apply Subgroup.map_injective (conjClosure V₀ T).subtype_injective
  rw [map_biSup_smul (T_le_NV T V₀), Subgroup.map_subgroupOf_eq_of_le (V₀_le_V T V₀),
    Subgroup.map_subgroupOf_eq_of_le le_rfl]

omit [Finite G] c in
theorem orbSup_eq_top [IsMulCommutative ↥(conjClosure V₀ T)] :
    orbSup (autOn T (conjClosure V₀ T)) (V₀.subgroupOf (conjClosure V₀ T)) = ⊤ :=
  orbSup_eq.trans (Subgroup.subgroupOf_self _)

theorem irrT [IsMulCommutative ↥(conjClosure V₀ T)] :
    V₀.subgroupOf (conjClosure V₀ T) ∈ IrrPlusOn (autOn (conjClosure L T) (conjClosure V₀ T))
      (orbSup (autOn T (conjClosure V₀ T)) (V₀.subgroupOf (conjClosure V₀ T)))
      (autOn T (conjClosure V₀ T)) := by
  set L₀ := conjClosure L T with hL₀
  set V := conjClosure V₀ T with hV
  have hVV : V ≤ V := le_rfl
  have hLV : L₀ ≤ Subgroup.normalizer (V : Set G) := c.L₀_le_NV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := T_le_NV T V₀
  have h1 := c.irr_V
  set W := ⨆ y ∈ onA V T, y • V₀.subgroupOf V with hW
  have hTX₁ : onA V T ≤ Subgroup.normalizer ((onA V L₀ : Subgroup _) : Set _) :=
    onA_le_normalizer c.T_le_M
  have hTX₂ : autOn T V ≤ Subgroup.normalizer (autOn L₀ V : Set (MulAut ↥V)) :=
    H13.autOn_le_normalizer hLV hTV c.T_le_M
  have hWT : ∀ t ∈ onA V T, ∀ w ∈ W, t • w ∈ W := fun t ht w hw => smul_mem_biSup_smul ht hw
  have hWinv : IsModInv (onA V L₀) W :=
    XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy => isModInv_smul (hTX₁ hy) h1.1.2.1
  have h2 := map_mem_irrPlusOn (Subgroup.inclusion_injective hVV)
    (actCompat_inclusion_autOn hVV hLV hLV) (actCompat_inclusion_autOn hVV hTV hTV) hTX₁ hTX₂
    hWT hWinv h1
  have hI : (V₀.subgroupOf V).map (Subgroup.inclusion hVV) = V₀.subgroupOf V := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hWtop : W = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [map_biSup_smul hTV, Subgroup.map_subgroupOf_eq_of_le (V₀_le_V T V₀), map_subtype_top]
  have hWmap : W.map (Subgroup.inclusion hVV) = orbSup (autOn T V) (V₀.subgroupOf V) := by
    rw [orbSup_eq, hWtop]
    ext x
    constructor
    · rintro ⟨v, -, rfl⟩
      exact v.2
    · intro _
      exact ⟨x, trivial, rfl⟩
  rw [hI, hWmap] at h2
  exact h2

theorem d3Std (h316 : Theorem316Statement) [IsMulCommutative ↥(conjClosure V₀ T)] :
    D3Std (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T))
      (autOn (conjClosure L T) (conjClosure V₀ T)) (autOn T (conjClosure V₀ T))
      (autOn L (conjClosure V₀ T)) (V₀.subgroupOf (conjClosure V₀ T)) := by
  set L₀ := conjClosure L T with hL₀def
  set V := conjClosure V₀ T with hVdef
  set Y := L₀ ⊔ T with hYdef
  set K := autOn L V with hKdef
  set K₀ := autOn L₀ V with hK₀def
  set X := autOn Y V with hXdef
  set S := autOn T V with hSdef
  set I := V₀.subgroupOf V with hIdef
  have hL₀W : L₀ ≤ Subgroup.normalizer (V : Set G) := c.L₀_le_NV
  have hTW : T ≤ Subgroup.normalizer (V : Set G) := T_le_NV T V₀
  have hYW : Y ≤ Subgroup.normalizer (V : Set G) := sup_le hL₀W hTW
  have hLW : L ≤ Subgroup.normalizer (V : Set G) := L_le_NV c
  have hexpW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.elemV.2 w w.2)
  have hKq : CFSG.IsQuasisimple ↥K := quasi c
  have hKK₀ : K ≤ K₀ := InternalSec.autOn_le_autOn_of_le c.L_le_L₀
  have hK₀X : K₀ ≤ X := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hSX : S ≤ X := InternalSec.autOn_le_autOn_of_le le_sup_right
  have hYL₀ : Y ≤ Subgroup.normalizer (L₀ : Set G) := sup_le Subgroup.le_normalizer c.T_le_M
  have hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set (MulAut ↥V)) :=
    H13.autOn_le_normalizer hL₀W hYW hYL₀
  have hSK₀ : S ≤ Subgroup.normalizer (K₀ : Set (MulAut ↥V)) := hSX.trans hXK₀
  have hK₀K : K₀ ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) :=
    H13.autOn_le_normalizer hLW hL₀W (Vol2.Ch10.SecA.fsuL0_le_normalizer c.fsu.maximal.1)
  have hsqY : SQTKGroup ↥Y := InternalSec.sqtkGroup_mono c.sqtkM c.sup_le_M
  have hqsqtk : IsQuotientOfSQTKTC ↥X :=
    ⟨↥Y, inferInstance, inferInstance, fun p hp hp2 => hsqY.1 p hp hp2, hsqY.2,
      InternalSec.autOnHom hYW, InternalSec.autOnHom_surjective hYW⟩
  have hsyl : IsSylowTwoOf S X := by
    have := isSylowTwoOf_map_subgroupOf ((conjAct V).comp (Subgroup.inclusion hYW))
      (isSylowTwoOf_of_le c.fsu.sylow (le_sup_right : T ≤ Y))
    rwa [map_subgroupOf_conjAct le_sup_right hYW, map_subgroupOf_conjAct le_rfl hYW] at this
  have hKsubK₀ : IsSubnormal K K₀ :=
    A3.subnormal_of_normal hKK₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hKK₀).mpr hK₀K)
  have hcomp : K ∈ cComp X := mem_cComp_of_quasisimple hKq (A3.subnormal_trans hKsubK₀
    (A3.subnormal_of_normal hK₀X ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₀X).mpr hXK₀)))
  have hK₀S : K₀ ≤ K₀ ⊔ S := le_sup_left
  have hcompKS : K ∈ cComp (K₀ ⊔ S) := mem_cComp_of_quasisimple hKq (A3.subnormal_trans hKsubK₀
    (A3.subnormal_of_normal hK₀S ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₀S).mpr
      (sup_le Subgroup.le_normalizer hSK₀))))
  have hMpeq : K₀ = conjClosure K S := T326.autOn_conjClosure hLW hTW
  have hirrT : I ∈ IrrPlusOn K₀ (orbSup S I) S := irrT c
  have hgen : (⨆ m ∈ X, I.map m.toMonoidHom) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← orbSup_eq_top (T := T) (V₀ := V₀)]
    change (⨆ m ∈ S, I.map m.toMonoidHom) ≤ ⨆ m ∈ X, I.map m.toMonoidHom
    exact biSup_mono fun m hm => hSX hm
  have hSylF : IsSylowTwoOf S (K₀ ⊔ S) := F7.isSylowTwoOf_mono_right hsyl le_sup_right
    (sup_le hK₀X hSX)
  have hWT : ∀ t ∈ S, ∀ w ∈ orbSup S I, t • w ∈ orbSup S I := fun t ht w hw =>
    mem_orbSup_of_mem_map ht hw
  have hcomm : ∀ g ∈ pCoreOf 2 (K₀ ⊔ S), ∀ m ∈ K₀, g * m = m * g := by
    intro g hg
    have key : K₀ ≤ Subgroup.centralizer ({g} : Set (MulAut ↥V)) := by
      rw [hMpeq]
      refine conjClosure_le fun s hs k hk => ?_
      have hs' : s⁻¹ ∈ K₀ ⊔ S := Subgroup.mem_sup_right (S.inv_mem hs)
      have hg' : s⁻¹ * g * s ∈ pCoreOf 2 (K₀ ⊔ S) := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hs') g).mp hg
        rwa [inv_inv] at this
      have hc := commute_of_mem_pCoreOf_of_mem_cComp hcompKS hKq hg' hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      calc g * (s * k * s⁻¹) = s * (s⁻¹ * g * s * k) * s⁻¹ := by group
        _ = s * (k * (s⁻¹ * g * s)) * s⁻¹ := by rw [hc]
        _ = s * k * s⁻¹ * g := by group
    intro m hm
    exact Subgroup.mem_centralizer_iff.mp (key hm) g (Set.mem_singleton g)
  have ho2 : ∀ g ∈ pCoreOf 2 (K₀ ⊔ S), ∀ v ∈ I, g v ∈ I := by
    intro g hg v hv
    have hgS : g ∈ S := F7.isSylowTwoOf_pCoreOf_le hSylF hg
    have hiso := iso_tilde_smul_of_commute hSK₀ hWT hgS (hcomm g hg) I
    have hstab :=
      (forall_smul_eq_iff_mem_irrPlusOn hSK₀ hWT hirrT.1).mpr hirrT g ⟨hgS, hiso⟩
    have h2 : g • v ∈ g • I := Subgroup.smul_mem_pointwise_smul v g _ hv
    rw [hstab] at h2
    exact h2
  have hqhat : qhatOf (autSub (K₀ ⊔ S) (orbSup S I)) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr orbSup_eq, hK₀def, hSdef, ← H13.autOn_sup hL₀W hTW]
    have h1 := qhatOf_autSub_autOn_le (X := L₀ ⊔ T) (le_rfl : V ≤ V) hYW hYW
    have h2 : qhatInt (L₀ ⊔ T) V c.elemV ≤ ((2 : ℚ) : WithTop ℚ) := by
      exact_mod_cast T326.qhatInt_V_le h316 c
    exact h1.trans h2
  exact ⟨⟨hexpW, hqsqtk, hsyl, hcomp, hKq, hMpeq, hXK₀, ⟨le_top, hirrT.1.2⟩, ho2, hgen⟩, hqhat,
    hirrT⟩

end CtxV

end CFSG.Quasithin.H13.Lem3313F
