module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransport
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_eq_bot_iff {N E : Subgroup G} : conjClosure N E = ⊥ ↔ E = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp (h ▸ uc22p22v_le_conjClosure N E)
  · rintro rfl
    refine le_bot_iff.mp (uc22p22v_conjClosure_le (F := ⊥) ?_ le_rfl)
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp

private theorem congrHom_self_apply {W : Type*} [CommGroup W] (x a : MulAut W) :
    CFSG.Quasithin.H.congrHom x a = x * a * x⁻¹ := by
  ext w
  rfl

theorem exists_mem_aSet_le_of_isSylowIn {W : Type*} [CommGroup W] [Finite W]
    {X T : Subgroup (MulAut W)} (hT : IsSylowIn 2 T X) {k : ℕ}
    (h : (E3.aSet k X).Nonempty) : ∃ A ∈ E3.aSet k X, A ≤ T := by
  obtain ⟨A₀, hA₀⟩ := h
  have : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    DFunLike.coe_injective
  obtain ⟨x, hxX, hle⟩ := E3.exists_le_conj_of_isSylowIn hT hA₀.1
    (E3.isPGroup_of_isElemAbelian2 hA₀.2.2.1)
  refine ⟨A₀.map (CFSG.Quasithin.H.congrHom x), ?_, ?_⟩
  · have hXmap : X.map (CFSG.Quasithin.H.congrHom x) = X := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        rw [congrHom_self_apply]
        exact X.mul_mem (X.mul_mem hxX hy) (X.inv_mem hxX)
      · intro y hy
        refine ⟨x⁻¹ * y * x, X.mul_mem (X.mul_mem (X.inv_mem hxX) hy) hxX, ?_⟩
        rw [congrHom_self_apply]
        group
    have h1 := (CFSG.Quasithin.H.map_mem_aSet_iff x (k := k) (X := X) (A := A₀)).2 hA₀
    rwa [hXmap] at h1
  · rintro _ ⟨a, ha, rfl⟩
    rw [congrHom_self_apply]
    exact mem_conjSubgroup_iff.1 (hle ha)

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem pCoreOf_L0_le_T : CFSG.Open.pCoreOf 2 c.L0 ≤ D.T :=
  (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn (isSylowIn_T_inf c)).trans inf_le_left

theorem pCoreOf_L0_le_centralizer_Z :
    CFSG.Open.pCoreOf 2 c.L0 ≤ Subgroup.centralizer (D.Z : Set G) :=
  (pCoreOf_L0_le_T c).trans (uc22main1_T_le_centralizer D)

theorem pCoreOf_L0_le_centralizer_conjClosure {S : Subgroup G} (hSZ : S ≤ D.Z) :
    CFSG.Open.pCoreOf 2 c.L0 ≤ Subgroup.centralizer (conjClosure c.L0 S : Set G) := by
  have hS : S ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 c.L0 : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (pCoreOf_L0_le_centralizer_Z c hr) s (hSZ hs)).symm
  have hN : c.L0 ≤ Subgroup.normalizer
      (Subgroup.centralizer (CFSG.Open.pCoreOf 2 c.L0 : Set G) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L0).trans
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _)
  have h := uc22p22v_conjClosure_le hN hS
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (h hw) r hr).symm

theorem barSub_pCoreOf_L0_eq_bot {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) :
    barSub ⊥ (conjClosure c.L0 S) hW (CFSG.Open.pCoreOf 2 c.L0) = ⊥ := by
  refine le_bot_iff.mp fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ (conjClosure c.L0 S) hW _ φ).1 hφ
  refine (Subgroup.mem_bot).2 ((actTil_eq_one_iff ⊥ (conjClosure c.L0 S) hW g).2 fun a ha => ?_)
  rw [Subgroup.mem_bot]
  have hcomm : a * (g : G) = (g : G) * a :=
    Subgroup.mem_centralizer_iff.mp (pCoreOf_L0_le_centralizer_conjClosure c hSZ hg) a ha
  calc (g : G) * a * (g : G)⁻¹ * a⁻¹ = (a * (g : G)) * (g : G)⁻¹ * a⁻¹ := by rw [hcomm]
    _ = 1 := by group

private theorem T_le_centralizer_of_le_Z {S : Subgroup G} (hSZ : S ≤ D.Z) :
    D.T ≤ Subgroup.centralizer (S : Set G) :=
  (uc22main1_T_le_centralizer D).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSZ))

theorem T_le_normalizer_conjClosure {S : Subgroup G} (hSZ : S ≤ D.Z) :
    D.T ≤ Subgroup.normalizer (conjClosure c.L0 S : Set G) := by
  have hTS := T_le_centralizer_of_le_Z (D := D) hSZ
  have hconj : ∀ g ∈ D.T, ∀ z ∈ S, g * z * g⁻¹ = z := by
    intro g hg z hz
    have h : z * g = g * z := Subgroup.mem_centralizer_iff.mp (hTS hg) z hz
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := by group
      _ = (z * g) * g⁻¹ := by rw [h]
      _ = z := by group
  have key : ∀ g ∈ D.T, ∀ x ∈ c.L0, ∀ z ∈ S,
      ∃ y ∈ c.L0, ∃ z' ∈ S, g * (x * z * x⁻¹) * g⁻¹ = y * z' * y⁻¹ := by
    intro g hg x hx z hz
    refine ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_L0 c hg) x).1 hx,
      g * z * g⁻¹, ?_, by group⟩
    rw [hconj g hg z hz]
    exact hz
  intro t ht
  exact uc22p22v_mem_normalizer_conjClosure (key t ht) (key t⁻¹ (D.T.inv_mem ht))

theorem sup_le_stabTil_conjClosure {S : Subgroup G} (hSZ : S ≤ D.Z) :
    c.L0 ⊔ D.T ≤ stabTil (⊥ : Subgroup G) (conjClosure c.L0 S) :=
  le_inf (sup_le (uc22p22v_le_normalizer_conjClosure c.L0 S) (T_le_normalizer_conjClosure c hSZ))
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)

omit [Finite G] in
private noncomputable def sTil {W : Subgroup G} (hW : IsElemAbelian 2 W) {s : G} (hs : s ∈ W) :
    Vtil (⊥ : Subgroup G) W hW :=
  mkTil ⊥ W hW (IntMod.mk hW ⟨s, hs⟩)

omit [Finite G] in
private theorem act_sTil_eq_iff {W : Subgroup G} (hW : IsElemAbelian 2 W)
    (g : stabTil (⊥ : Subgroup G) W) {s : G} (hs : s ∈ W) :
    actTil ⊥ W hW g (sTil hW hs) = sTil hW hs ↔ (g : G) * s = s * (g : G) := by
  unfold sTil
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
  show (g : G) * s * (g : G)⁻¹ * s⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

omit [Finite G] in
private theorem sTil_mem_fixV_barSub_iff {W : Subgroup G} (hW : IsElemAbelian 2 W)
    {Y : Subgroup G} {s : G} (hs : s ∈ W) :
    sTil hW hs ∈ fixV (barSub ⊥ W hW Y) ↔
      ∀ g (_ : g ∈ Y) (_ : g ∈ stabTil (⊥ : Subgroup G) W), g * s = s * g := by
  rw [mem_fixV]
  constructor
  · intro h g hg hgs
    exact (act_sTil_eq_iff hW ⟨g, hgs⟩ hs).1 (h _ (actTil_mem_barSub ⊥ W hW hg hgs))
  · intro h φ hφ
    obtain ⟨g, hgY, rfl⟩ := (mem_barSub ⊥ W hW Y φ).1 hφ
    exact (act_sTil_eq_iff hW g hs).2 (h g hgY g.2)

private theorem sTil_mem_fixV_T {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) {s : G} (hs : s ∈ S) :
    sTil hW (uc22p22v_le_conjClosure c.L0 S hs) ∈
      fixV (barSub ⊥ (conjClosure c.L0 S) hW D.T) :=
  (sTil_mem_fixV_barSub_iff hW _).2 fun _ hg _ =>
    (Subgroup.mem_centralizer_iff.mp (T_le_centralizer_of_le_Z hSZ hg) s hs).symm

private theorem eq_top_of_stable {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S))
    {J : Subgroup (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW)}
    (hS : ∀ s (hs : s ∈ S), sTil hW (uc22p22v_le_conjClosure c.L0 S hs) ∈ J)
    (hJ : StableUnder (barSub ⊥ (conjClosure c.L0 S) hW c.L0) J) : J = ⊤ := by
  have hL0s : c.L0 ≤ stabTil (⊥ : Subgroup G) (conjClosure c.L0 S) :=
    le_sup_left.trans (sup_le_stabTil_conjClosure c hSZ)
  have key : ∀ m ∈ c.L0, ∀ g ∈ preTil ⊥ (conjClosure c.L0 S) hW J,
      m * g * m⁻¹ ∈ preTil ⊥ (conjClosure c.L0 S) hW J := by
    intro m hm g hg
    obtain ⟨x, rfl, hx⟩ := (mem_preTil ⊥ (conjClosure c.L0 S) hW J).1 hg
    have hmW : m * x.val * m⁻¹ ∈ conjClosure c.L0 S :=
      (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer ⊥ (conjClosure c.L0 S) (hL0s hm))
        x.val).1 x.val_mem
    rw [mem_preTil_iff_of_mem ⊥ (conjClosure c.L0 S) hW J hmW]
    have hEq : IntMod.mk hW ⟨m * x.val * m⁻¹, hmW⟩ =
        actStab ⊥ (conjClosure c.L0 S) hW ⟨m, hL0s hm⟩ x :=
      IntMod.val_injective (by rw [actStab_apply_val]; rfl)
    rw [hEq, ← actTil_mk]
    exact hJ _ (actTil_mem_barSub ⊥ (conjClosure c.L0 S) hW hm (hL0s hm)) _ hx
  have hLP : c.L0 ≤ Subgroup.normalizer (preTil ⊥ (conjClosure c.L0 S) hW J : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => key m hm g hg, fun hg => ?_⟩
    have := key m⁻¹ (c.L0.inv_mem hm) _ hg
    simpa [mul_assoc] using this
  have hSP : S ≤ preTil ⊥ (conjClosure c.L0 S) hW J := by
    intro s hs
    rw [mem_preTil_iff_of_mem ⊥ (conjClosure c.L0 S) hW J (uc22p22v_le_conjClosure c.L0 S hs)]
    exact hS s hs
  have hWP := uc22p22v_conjClosure_le hLP hSP
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ (conjClosure c.L0 S) hW q
  obtain ⟨y, hy, hyJ⟩ := (mem_preTil ⊥ (conjClosure c.L0 S) hW J).1 (hWP x.val_mem)
  rwa [IntMod.val_injective hy] at hyJ

theorem isSylowIn_T_sup_L0 : IsSylowIn 2 D.T (c.L0 ⊔ D.T) := by
  have h1 : ¬ 2 ∣ D.T.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG).2.2
  exact ⟨le_sup_right, D.sylowM.isPGroup, fun hdvd =>
    h1 (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩

theorem isSylowIn_barSub_T {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) :
    IsSylowIn 2 (barSub ⊥ (conjClosure c.L0 S) hW D.T)
      (barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)) :=
  isSylowIn_barSub hW le_sup_right (sup_le_stabTil_conjClosure c hSZ) (isSylowIn_T_sup_L0 c)

theorem eq_bot_of_le_barSub_T_of_stable {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S))
    {A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW))}
    (hAT : A ≤ barSub ⊥ (conjClosure c.L0 S) hW D.T)
    (hstab : StableUnder (barSub ⊥ (conjClosure c.L0 S) hW c.L0) (fixV A)) : A = ⊥ := by
  have htop : fixV A = ⊤ :=
    eq_top_of_stable c hSZ hW (fun s hs => fun a ha => sTil_mem_fixV_T c hSZ hW hs a (hAT ha))
      hstab
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun u => ?_
  have hu : u ∈ fixV A := by rw [htop]; exact Subgroup.mem_top u
  simpa using (mem_fixV.mp hu) a ha

theorem eq_bot_of_le_barSub_T_of_le_centralizer {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S))
    {A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW))}
    (hAT : A ≤ barSub ⊥ (conjClosure c.L0 S) hW D.T)
    (hAL : A ≤ Subgroup.centralizer
      (barSub ⊥ (conjClosure c.L0 S) hW c.L0 :
        Set (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW)))) : A = ⊥ := by
  refine eq_bot_of_le_barSub_T_of_stable c hSZ hW hAT ?_
  intro l hl u hu
  rw [mem_fixV] at hu ⊢
  intro a ha
  have hcomm : l * a = a * l := Subgroup.mem_centralizer_iff.mp (hAL ha) l hl
  calc a (l u) = (a * l) u := rfl
    _ = (l * a) u := by rw [hcomm]
    _ = l (a u) := rfl
    _ = l u := by rw [hu a ha]

theorem pCore_barSub_sup_eq_bot {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) :
    CFSG.pCore 2 ↥(barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)) = ⊥ := by
  set X := barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)
  have hSyl : IsSylowIn 2 (barSub ⊥ (conjClosure c.L0 S) hW D.T) X :=
    isSylowIn_barSub_T c hSZ hW
  have hQT : CFSG.Open.pCoreOf 2 X ≤ barSub ⊥ (conjClosure c.L0 S) hW D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hSyl
  have hQX : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set _) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hLX : barSub ⊥ (conjClosure c.L0 S) hW c.L0 ≤ X := barSub_mono ⊥ _ hW le_sup_left
  have hstab : StableUnder (barSub ⊥ (conjClosure c.L0 S) hW c.L0)
      (fixV (CFSG.Open.pCoreOf 2 X)) := by
    intro x hx u hu
    rw [mem_fixV] at hu ⊢
    intro q hq
    have hxinv : x⁻¹ ∈ X := X.inv_mem (hLX hx)
    have hconj : x⁻¹ * q * x ∈ CFSG.Open.pCoreOf 2 X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hQX hxinv) q).1 hq
    calc q (x u) = (q * x) u := rfl
      _ = (x * (x⁻¹ * q * x)) u := by group
      _ = x ((x⁻¹ * q * x) u) := rfl
      _ = x u := by rw [hu _ hconj]
  have hQ : CFSG.Open.pCoreOf 2 X = ⊥ :=
    eq_bot_of_le_barSub_T_of_stable c hSZ hW hQT hstab
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hQ

theorem inf_Z_ne_bot_of_eq_conjClosure {V : Subgroup G}
    (hVN : V = conjClosure c.N (V ⊓ D.Z)) (hV1 : V ≠ ⊥) : V ⊓ D.Z ≠ ⊥ :=
  fun h => hV1 (by rw [hVN, h, conjClosure_eq_bot_iff.mpr rfl])

theorem fixV_barSub_T_ne_fixV_barSub_sup {S : Subgroup G} (hSZ : S ≤ D.Z) (hS1 : S ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) :
    fixV (barSub ⊥ (conjClosure c.L0 S) hW D.T) ≠
      fixV (barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)) := by
  intro h
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS1
  have hzS : (z : G) ∈ S := z.2
  have hmem : sTil hW (uc22p22v_le_conjClosure c.L0 S hzS) ∈
      fixV (barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)) := by
    rw [← h]
    exact sTil_mem_fixV_T c hSZ hW hzS
  have hcomm := (sTil_mem_fixV_barSub_iff hW _).1 hmem
  have hL0z : c.L0 ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hl' : l ∈ c.L0 ⊔ D.T := (le_sup_left : c.L0 ≤ c.L0 ⊔ D.T) hl
    exact (hcomm l hl' (sup_le_stabTil_conjClosure c hSZ hl')).symm
  exact L0_not_le_M c (hL0z.trans (Ctx23.centralizer_le_M c.toCtx23
    (Data.Z_le_U D (hSZ hzS)) (fun h1 => hz1 (Subtype.ext h1))))

theorem aBar_le_of_forall_mem_aSet_le_centralizer {S : Subgroup G} (hSZ : S ≤ D.Z)
    (hW : IsElemAbelian 2 (conjClosure c.L0 S)) (n : ℕ)
    (hb : ∀ A ∈ E3.aSet (n + 1) (barSub ⊥ (conjClosure c.L0 S) hW (c.L0 ⊔ D.T)),
      A ≤ Subgroup.centralizer
        (barSub ⊥ (conjClosure c.L0 S) hW c.L0 :
          Set (MulAut (Vtil (⊥ : Subgroup G) (conjClosure c.L0 S) hW)))) :
    aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 S) hW ≤ n := by
  unfold aBar
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty _ n fun A hA => ?_
  obtain ⟨A', hA', hA'T⟩ := exists_mem_aSet_le_of_isSylowIn (isSylowIn_barSub_T c hSZ hW) ⟨A, hA⟩
  exact hA'.2.1 (eq_bot_of_le_barSub_T_of_le_centralizer c hSZ hW hA'T (hb A' hA'))

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
