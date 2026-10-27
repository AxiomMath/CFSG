module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem517Red
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscAut
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

private theorem mem_fixV_zpowers_of_apply_eq {M : Type*} [CommGroup M] {f : MulAut M} {w : M}
    (h : f w = w) : w ∈ fixV (Subgroup.zpowers f) :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 h

section TildeAction

variable {G : Type} [Group G] {Z₁ U X : Subgroup G}

theorem tmk_mem_centralizer_tildeOf_iff (hUZ : U ≤ Subgroup.normalizer (Z₁ : Set G))
    (x : Subgroup.normalizer (Z₁ : Set G)) :
    tmk Z₁ x ∈ Subgroup.centralizer
        (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) ↔
      ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z₁ := by
  constructor
  · intro hx u hu
    have h1 := Subgroup.mem_centralizer_iff.mp hx (tmk Z₁ ⟨u, hUZ hu⟩)
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (x := ⟨u, hUZ hu⟩) hu)
    exact commutator_mem_of_secMk_commute (x := x) (y := ⟨u, hUZ hu⟩) h1.symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
    exact (secMk_comm_of_commutator_mem (x := x) (y := u) (h u hu)).symm

theorem tildeAct_apply_coe (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (x : ↥X) (w : ↥(tildeOf Z₁ U)) :
    ((((tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW x : ↥(autOn (tildeOf Z₁ X) (tildeOf Z₁ U))) :
      MulAut ↥(tildeOf Z₁ U)) w : ↥(tildeOf Z₁ U)) :
        SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁) =
      tmk Z₁ ⟨x, hXZ x.2⟩ * w * (tmk Z₁ ⟨x, hXZ x.2⟩)⁻¹ :=
  Setup.rho_apply_coe hXW (tildeRes Z₁ X hXZ x) w

theorem tildeAct_tildeRes (hUZ : U ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (x : ↥X) (u : ↥U) :
    ((tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW x : ↥(autOn (tildeOf Z₁ X) (tildeOf Z₁ U))) :
      MulAut ↥(tildeOf Z₁ U)) (tildeRes Z₁ U hUZ u) =
      tildeRes Z₁ U hUZ ⟨(x : G) * u * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hXU x.2) u).mp u.2⟩ := by
  apply Subtype.ext
  rw [tildeAct_apply_coe, tildeRes_apply, tildeRes_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tildeAct_eq_one_iff (hUZ : U ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) (x : ↥X) :
    ((tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW x : ↥(autOn (tildeOf Z₁ X) (tildeOf Z₁ U))) :
      MulAut ↥(tildeOf Z₁ U)) = 1 ↔ (x : G) ∈ centralizerMod Z₁ X U := by
  rw [OneMemClass.coe_eq_one, ← MonoidHom.mem_ker, mem_ker_tildeAct,
    tmk_mem_centralizer_tildeOf_iff hUZ]
  exact ⟨fun h => ⟨x.2, hXZ x.2, h⟩, fun h => h.2.2⟩

theorem mem_autOn_tildeOf_iff (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    {Y : Subgroup G} (hYX : Y ≤ X) (f : MulAut ↥(tildeOf Z₁ U)) :
    f ∈ autOn (tildeOf Z₁ Y) (tildeOf Z₁ U) ↔ ∃ x : ↥X, (x : G) ∈ Y ∧
      ((tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW x : ↥(autOn (tildeOf Z₁ X) (tildeOf Z₁ U))) :
        MulAut ↥(tildeOf Z₁ U)) = f := by
  constructor
  · intro hf
    obtain ⟨g, hgY, rfl⟩ := Subgroup.mem_map.mp hf
    rw [Subgroup.mem_subgroupOf] at hgY
    obtain ⟨x, hxY, hxg⟩ := mem_secImg.mp hgY
    refine ⟨⟨x, hYX hxY⟩, hxY, ?_⟩
    show conjAct (tildeOf Z₁ U) _ = conjAct (tildeOf Z₁ U) g
    congr 1
    exact Subtype.ext hxg
  · rintro ⟨x, hxY, rfl⟩
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXW (tildeRes Z₁ X hXZ x),
      Subgroup.mem_subgroupOf.mpr (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G))
        (B := Z₁) (x := ⟨x, hXZ x.2⟩) hxY), rfl⟩

end TildeAction

section Module

variable {G : Type} [Group G] [Finite G] {Z₁ U X : Subgroup G}

theorem fixed_tilde_eq (hUab : IsElemAbelian 2 U) (hUZ : U ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) {V' H' : Subgroup G}
    (hU : U = conjClosure V' H') (hHX : H' ≤ X) {d : G} (hdX : d ∈ X) (hdodd : Odd (orderOf d))
    (hdV : d ∈ Subgroup.normalizer (V' : Set G))
    (hHd : ∀ h ∈ H', h * d * h⁻¹ * d⁻¹ ∈ centralizerMod Z₁ X U)
    (hV'fix : ∀ v ∈ V', (d * v * d⁻¹)⁻¹ * v ∈ Z₁ → v ∈ Z₁) :
    ∀ u ∈ U, (d * u * d⁻¹)⁻¹ * u ∈ Z₁ → u ∈ Z₁ := by
  classical
  have hWab : IsElemAbelian 2 (tildeOf Z₁ U) := isElemAbelian_secImg hUab
  let _ : CommGroup ↥(tildeOf Z₁ U) := commGroupOfElemAbelian hWab
  have hW2 : ∀ w : ↥(tildeOf Z₁ U), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hWab.2 w w.2)
  let φ : ↥X →* MulAut ↥(tildeOf Z₁ U) :=
    (autOn (tildeOf Z₁ X) (tildeOf Z₁ U)).subtype.comp (tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW)
  have hφ : ∀ (x : ↥X) (u : ↥U), φ x (tildeRes Z₁ U hUZ u) = tildeRes Z₁ U hUZ
      ⟨(x : G) * u * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hXU x.2) u).mp u.2⟩ :=
    fun x u => tildeAct_tildeRes hUZ hXZ hXW hXU x u
  have hφ1 : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ centralizerMod Z₁ X U :=
    fun x => tildeAct_eq_one_iff hUZ hXZ hXW x
  have hV'U : V' ≤ U := hU ▸ le_conjClosure V' H'
  have hY : Odd (Nat.card ↥(Subgroup.zpowers (φ ⟨d, hdX⟩))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hdodd ((orderOf_map_dvd φ _).trans (Subgroup.orderOf_mk d hdX).dvd)
  have hpow : ∀ (k : ℤ) (v : G) (hv : v ∈ V'), (φ ⟨d, hdX⟩ ^ k)
      (tildeRes Z₁ U hUZ ⟨v, hV'U hv⟩) = tildeRes Z₁ U hUZ ⟨d ^ k * v * (d ^ k)⁻¹,
        hV'U ((Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hdV k) v).mp hv)⟩ := by
    intro k v hv
    rw [← map_zpow, hφ]
    rfl
  have htrV : ∀ (v : G) (hv : v ∈ V'),
      B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩)) (tildeRes Z₁ U hUZ ⟨v, hV'U hv⟩) = 1 := by
    intro v hv
    have : Fintype ↥(Subgroup.zpowers (φ ⟨d, hdX⟩)) := Fintype.ofFinite _
    have hmem : B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩)) (tildeRes Z₁ U hUZ ⟨v, hV'U hv⟩) ∈
        (V'.subgroupOf U).map (tildeRes Z₁ U hUZ) := by
      rw [B1.traceY_apply]
      refine Subgroup.prod_mem _ fun y _ => ?_
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      rw [← hk, hpow k v hv]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hdV k) v).mp hv))
    obtain ⟨⟨v', hv'U⟩, hv'V, hv'⟩ := Subgroup.mem_map.mp hmem
    rw [Subgroup.mem_subgroupOf] at hv'V
    have hfixd := B1.traceY_mem_fixV (Subgroup.zpowers (φ ⟨d, hdX⟩))
      (tildeRes Z₁ U hUZ ⟨v, hV'U hv⟩)
    rw [← hv'] at hfixd ⊢
    have h1 : φ ⟨d, hdX⟩ (tildeRes Z₁ U hUZ ⟨v', hv'U⟩) = tildeRes Z₁ U hUZ ⟨v', hv'U⟩ :=
      hfixd _ (Subgroup.mem_zpowers _)
    rw [hφ] at h1
    have h2 := congrArg Subtype.val h1
    rw [tildeRes_apply, tildeRes_apply, secMk_eq_secMk_iff] at h2
    exact Subtype.ext ((tildeRes_apply _ _).trans (secMk_eq_one_iff.mpr (hV'fix v' hv'V h2)))
  have htrH : ∀ h (hh : h ∈ H') (w : ↥(tildeOf Z₁ U)),
      B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩)) (φ ⟨h, hHX hh⟩ w) =
        φ ⟨h, hHX hh⟩ (B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩)) w) := by
    intro h hh w
    have : Fintype ↥(Subgroup.zpowers (φ ⟨d, hdX⟩)) := Fintype.ofFinite _
    have hc : φ ⟨h, hHX hh⟩ * φ ⟨d, hdX⟩ = φ ⟨d, hdX⟩ * φ ⟨h, hHX hh⟩ := by
      have h1 : φ (⟨h, hHX hh⟩ * ⟨d, hdX⟩ * ⟨h, hHX hh⟩⁻¹ * ⟨d, hdX⟩⁻¹) = 1 :=
        (hφ1 _).mpr (hHd h hh)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc φ ⟨h, hHX hh⟩ * φ ⟨d, hdX⟩
          = (φ ⟨h, hHX hh⟩ * φ ⟨d, hdX⟩ * (φ ⟨h, hHX hh⟩)⁻¹ * (φ ⟨d, hdX⟩)⁻¹) *
              (φ ⟨d, hdX⟩ * φ ⟨h, hHX hh⟩) := by group
        _ = φ ⟨d, hdX⟩ * φ ⟨h, hHX hh⟩ := by rw [h1, one_mul]
    rw [B1.traceY_apply, B1.traceY_apply, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    rw [← hk]
    have hck : φ ⟨h, hHX hh⟩ * φ ⟨d, hdX⟩ ^ k = φ ⟨d, hdX⟩ ^ k * φ ⟨h, hHX hh⟩ :=
      Commute.zpow_right hc k
    calc (φ ⟨d, hdX⟩ ^ k) (φ ⟨h, hHX hh⟩ w) = (φ ⟨d, hdX⟩ ^ k * φ ⟨h, hHX hh⟩) w := rfl
      _ = (φ ⟨h, hHX hh⟩ * φ ⟨d, hdX⟩ ^ k) w := by rw [hck]
      _ = φ ⟨h, hHX hh⟩ ((φ ⟨d, hdX⟩ ^ k) w) := rfl
  have htr : ∀ u : ↥U, B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩)) (tildeRes Z₁ U hUZ u) = 1 := by
    have hle : conjClosure V' H' ≤ ((B1.traceY (Subgroup.zpowers (φ ⟨d, hdX⟩))).comp
        (tildeRes Z₁ U hUZ)).ker.map U.subtype := by
      refine conjClosure_le fun h hh v hv => ?_
      have hmem : h * v * h⁻¹ ∈ U := hU ▸ mem_conjClosure hh hv
      refine ⟨⟨h * v * h⁻¹, hmem⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      rw [MonoidHom.comp_apply]
      have e : tildeRes Z₁ U hUZ ⟨h * v * h⁻¹, hmem⟩ =
          φ ⟨h, hHX hh⟩ (tildeRes Z₁ U hUZ ⟨v, hV'U hv⟩) :=
        (hφ ⟨h, hHX hh⟩ ⟨v, hV'U hv⟩).symm
      rw [e, htrH h hh, htrV v hv, map_one]
    intro u
    have hu' : (u : G) ∈ conjClosure V' H' := by rw [← hU]; exact u.2
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp (hle hu')
    have : x = u := Subtype.ext hxu
    rw [← this]
    exact hx
  intro u hu hfix
  have hdu : φ ⟨d, hdX⟩ (tildeRes Z₁ U hUZ ⟨u, hu⟩) = tildeRes Z₁ U hUZ ⟨u, hu⟩ := by
    rw [hφ]
    apply Subtype.ext
    rw [tildeRes_apply, tildeRes_apply]
    exact secMk_eq_secMk_iff.mpr hfix
  have h1 := B1.traceY_of_mem_fixV hW2 hY (mem_fixV_zpowers_of_apply_eq hdu)
  rw [htr] at h1
  have h2 := congrArg Subtype.val h1.symm
  rw [tildeRes_apply] at h2
  exact secMk_eq_one_iff.mp h2


theorem two_pow_nine_le_of_tilde (hTC : L34TorusCommFact) (hUab : IsElemAbelian 2 U)
    (hUZ : U ≤ Subgroup.normalizer (Z₁ : Set G)) (hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) {K : Subgroup G} (hKX : K ≤ X)
    (hK : LieModel (O2Q K) .PSL 3 2 2)
    (hKker : ∀ k ∈ K, k ∈ centralizerMod Z₁ X U ↔ k ∈ pCoreOf 2 K) {n : ℕ} (hn : Odd n)
    {d : G} (hdX : d ∈ X) (hdn : d ^ (2 ^ n - 1) = 1)
    (hKd : ∀ k ∈ K, k * d * k⁻¹ * d⁻¹ ∈ centralizerMod Z₁ X U)
    (hfix : ∀ u ∈ U, (d * u * d⁻¹)⁻¹ * u ∈ Z₁ → u ∈ Z₁) {y : G} (hyX : y ∈ X)
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hy2 : y ^ 2 ∈ centralizerMod Z₁ X U)
    (hyd : y * d * y⁻¹ * d⁻¹ ∈ centralizerMod Z₁ X U)
    (hyC : ¬ ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ centralizerMod Z₁ X U) :
    2 ^ 9 ≤ (centralizerMod Z₁ U (Subgroup.zpowers y)).relIndex U := by
  classical
  have hWab : IsElemAbelian 2 (tildeOf Z₁ U) := isElemAbelian_secImg hUab
  let _ : CommGroup ↥(tildeOf Z₁ U) := commGroupOfElemAbelian hWab
  have hW2 : ∀ w : ↥(tildeOf Z₁ U), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hWab.2 w w.2)
  let φ : ↥X →* MulAut ↥(tildeOf Z₁ U) :=
    (autOn (tildeOf Z₁ X) (tildeOf Z₁ U)).subtype.comp (tildeAct Z₁ X hXZ (tildeOf Z₁ U) hXW)
  have hφ : ∀ (x : ↥X) (u : ↥U), φ x (tildeRes Z₁ U hUZ u) = tildeRes Z₁ U hUZ
      ⟨(x : G) * u * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hXU x.2) u).mp u.2⟩ :=
    fun x u => tildeAct_tildeRes hUZ hXZ hXW hXU x u
  have hφ1 : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ centralizerMod Z₁ X U :=
    fun x => tildeAct_eq_one_iff hUZ hXZ hXW x
  have hcomm : ∀ a b : ↥X, (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ centralizerMod Z₁ X U →
      φ a * φ b = φ b * φ a := by
    intro a b h
    have h1 : φ (a * b * a⁻¹ * b⁻¹) = 1 := (hφ1 _).mpr h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ a * φ b = (φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹) * (φ b * φ a) := by group
      _ = φ b * φ a := by rw [h1, one_mul]
  have hmemK : ∀ f : MulAut ↥(tildeOf Z₁ U), f ∈ autOn (tildeOf Z₁ K) (tildeOf Z₁ U) ↔
      ∃ x : ↥X, (x : G) ∈ K ∧ φ x = f := fun f => mem_autOn_tildeOf_iff hXZ hXW hKX f
  have hKZ : K ≤ Subgroup.normalizer (Z₁ : Set G) := hKX.trans hXZ
  have hKW : tildeOf Z₁ K ≤ Subgroup.normalizer
      (tildeOf Z₁ U : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) :=
    (tildeOf_mono hKX).trans hXW
  have hLie : LieModel ↥(autOn (tildeOf Z₁ K) (tildeOf Z₁ U)) .PSL 3 2 2 := by
    have hker : (tildeAct Z₁ K hKZ (tildeOf Z₁ U) hKW).ker = CFSG.pCore 2 ↥K := by
      ext k
      rw [mem_ker_tildeAct, tmk_mem_centralizer_tildeOf_iff hUZ]
      constructor
      · intro h
        obtain ⟨k', hk', hk'k⟩ := (hKker k k.2).mp ⟨hKX k.2, hKZ k.2, h⟩
        have : k' = k := Subtype.ext hk'k
        rw [← this]
        exact hk'
      · intro hk
        exact ((hKker k k.2).mpr ⟨k, by assumption, rfl⟩).2.2
    let e : O2Q K ≃* ↥(autOn (tildeOf Z₁ K) (tildeOf Z₁ U)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (tildeAct_surjective _ _))
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hK
  have hdn' : φ ⟨d, hdX⟩ ^ (2 ^ n - 1) = 1 := by
    rw [← map_pow]
    have : (⟨d, hdX⟩ : ↥X) ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using hdn)
    rw [this, map_one]
  have hKdd : ∀ k ∈ autOn (tildeOf Z₁ K) (tildeOf Z₁ U), k * φ ⟨d, hdX⟩ = φ ⟨d, hdX⟩ * k := by
    intro f hf
    obtain ⟨x, hxK, rfl⟩ := (hmemK f).mp hf
    exact hcomm x ⟨d, hdX⟩ (hKd x hxK)
  have hfixdd : fixV (Subgroup.zpowers (φ ⟨d, hdX⟩)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨u, rfl⟩ := tildeRes_surjective hUZ w
    have hdw : φ ⟨d, hdX⟩ (tildeRes Z₁ U hUZ u) = tildeRes Z₁ U hUZ u :=
      hw _ (Subgroup.mem_zpowers _)
    rw [hφ] at hdw
    have h1 := congrArg Subtype.val hdw
    rw [tildeRes_apply, tildeRes_apply, secMk_eq_secMk_iff] at h1
    exact Subtype.ext ((tildeRes_apply _ _).trans (secMk_eq_one_iff.mpr (hfix u u.2 h1)))
  have ht2 : φ ⟨y, hyX⟩ ^ 2 = 1 := by
    rw [← map_pow]
    exact (hφ1 _).mpr hy2
  have htd : φ ⟨y, hyX⟩ * φ ⟨d, hdX⟩ = φ ⟨d, hdX⟩ * φ ⟨y, hyX⟩ := hcomm _ _ hyd
  have htN : φ ⟨y, hyX⟩ ∈ Subgroup.normalizer
      (autOn (tildeOf Z₁ K) (tildeOf Z₁ U) : Set (MulAut ↥(tildeOf Z₁ U))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      obtain ⟨x, hxK, rfl⟩ := (hmemK f).mp hf
      refine (hmemK _).mpr ⟨⟨y, hyX⟩ * x * ⟨y, hyX⟩⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyK x).mp hxK, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hf
      obtain ⟨x, hxK, hx⟩ := (hmemK _).mp hf
      refine (hmemK f).mpr ⟨⟨y, hyX⟩⁻¹ * x * ⟨y, hyX⟩, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyK) x).mp hxK
        simpa using this
      · rw [map_mul, map_mul, map_inv, hx]
        group
  have htC : φ ⟨y, hyX⟩ ∉ Subgroup.centralizer
      (autOn (tildeOf Z₁ K) (tildeOf Z₁ U) : Set (MulAut ↥(tildeOf Z₁ U))) := by
    intro hc
    apply hyC
    intro k hk
    have hkK : φ ⟨k, hKX hk⟩ ∈ autOn (tildeOf Z₁ K) (tildeOf Z₁ U) :=
      (hmemK _).mpr ⟨⟨k, hKX hk⟩, hk, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hkK
    have h2 : φ (⟨y, hyX⟩ * ⟨k, hKX hk⟩ * ⟨y, hyX⟩⁻¹ * ⟨k, hKX hk⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    exact (hφ1 _).mp h2
  have h9 := hTC ↥(tildeOf Z₁ U) hW2 (autOn (tildeOf Z₁ K) (tildeOf Z₁ U)) (φ ⟨d, hdX⟩)
    (φ ⟨y, hyX⟩) n hLie hn hdn' hKdd hfixdd ht2 htd htN htC
  have hyZ : ∀ k : ℤ, y ^ k ∈ Subgroup.normalizer (Z₁ : Set G) := fun k =>
    Subgroup.zpow_mem _ (hXZ hyX) k
  have hidx : (centralizerMod Z₁ U (Subgroup.zpowers y)).relIndex U =
      (fixV (Subgroup.zpowers (φ ⟨y, hyX⟩))).index := by
    rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ (tildeRes_surjective hUZ)]
    congr 1
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have key : φ ⟨y, hyX⟩ (tildeRes Z₁ U hUZ u) = tildeRes Z₁ U hUZ u ↔
        tmk Z₁ ⟨(u : G), hUZ u.2⟩ * tmk Z₁ ⟨y, hXZ hyX⟩ =
          tmk Z₁ ⟨y, hXZ hyX⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ := by
      rw [hφ]
      constructor
      · intro h
        have h1 := congrArg Subtype.val h
        rw [tildeRes_apply, tildeRes_apply] at h1
        have h2 : tmk Z₁ ⟨y, hXZ hyX⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ * (tmk Z₁ ⟨y, hXZ hyX⟩)⁻¹ =
            tmk Z₁ ⟨(u : G), hUZ u.2⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          exact h1
        calc tmk Z₁ ⟨(u : G), hUZ u.2⟩ * tmk Z₁ ⟨y, hXZ hyX⟩
            = (tmk Z₁ ⟨y, hXZ hyX⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ * (tmk Z₁ ⟨y, hXZ hyX⟩)⁻¹) *
                tmk Z₁ ⟨y, hXZ hyX⟩ := by rw [h2]
          _ = tmk Z₁ ⟨y, hXZ hyX⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ := by group
      · intro h
        apply Subtype.ext
        rw [tildeRes_apply, tildeRes_apply]
        have h2 : tmk Z₁ ⟨y, hXZ hyX⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ * (tmk Z₁ ⟨y, hXZ hyX⟩)⁻¹ =
            tmk Z₁ ⟨(u : G), hUZ u.2⟩ := by
          rw [← h]
          group
        rw [← map_inv, ← map_mul, ← map_mul] at h2
        exact h2
    constructor
    · rintro ⟨-, -, h⟩
      refine mem_fixV_zpowers_of_apply_eq (key.mpr ?_)
      exact secMk_comm_of_commutator_mem (x := ⟨(u : G), hUZ u.2⟩) (y := ⟨y, hXZ hyX⟩)
        (h y (Subgroup.mem_zpowers y))
    · intro h
      have hc := key.mp (h _ (Subgroup.mem_zpowers _))
      refine ⟨u.2, hUZ u.2, fun y' hy' => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hck : tmk Z₁ ⟨(u : G), hUZ u.2⟩ * tmk Z₁ ⟨y ^ k, hyZ k⟩ =
          tmk Z₁ ⟨y ^ k, hyZ k⟩ * tmk Z₁ ⟨(u : G), hUZ u.2⟩ := by
        have e : (⟨y ^ k, hyZ k⟩ : Subgroup.normalizer (Z₁ : Set G)) = ⟨y, hXZ hyX⟩ ^ k :=
          Subtype.ext (by simp)
        rw [e, map_zpow]
        exact Commute.zpow_right hc k
      exact commutator_mem_of_secMk_commute (x := ⟨(u : G), hUZ u.2⟩) (y := ⟨y ^ k, hyZ k⟩) hck
  rw [hidx]
  exact h9

end Module


namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem pCoreOf_le_pCoreOf_sup (hI : L2OddInnerFact) : pCoreOf 2 H ≤ pCoreOf 2 (H ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ⊔ D ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (s.D_le_normalizer_H hI)
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H).trans le_sup_left)
    (hHN.trans (normalizer_le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem mem_H_of_sq_mem (hI : L2OddInnerFact) {y : G} (hy : y ∈ H ⊔ D)
    (hy2 : y ^ 2 ∈ pCoreOf 2 (H ⊔ D)) : y ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hHN : H ⊔ D ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (s.D_le_normalizer_H hI)
  have hTsyl : IsSylowTwoOf T (H ⊔ D) := hh.isSylowTwoOf (hTH.trans le_sup_left)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (H ⊔ D)) ⟨_, hy2⟩
  have hk' : y ^ 2 ^ (k + 1) = 1 := by
    have h1 : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [pow_succ', pow_mul]
    exact h1
  have hz2 : IsPGroup 2 (Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨g, hg, hgT⟩ := exists_conj_le_of_isSylowTwoOf hTsyl (Subgroup.zpowers_le.mpr hy) hz2
  have h1 : g * y * g⁻¹ ∈ H := hTH (hgT (mul_mem_conjSub (Subgroup.mem_zpowers y)))
  have h2 := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem hg)) _).mp h1
  simpa [mul_assoc] using h2

theorem commutator_mem_pCoreOf
    (hI : L2OddInnerFact) {h d : G} (hh : h ∈ H) (hd : d ∈ D) :
    h * d * h⁻¹ * d⁻¹ ∈ pCoreOf 2 (H ⊔ D) := by
  have hdC : d ∈ centralizerModO2 (oTwoUpper H) := s.D_le_centralizer hd
  have h1 : h * d * h⁻¹ ∈ centralizerModO2 (oTwoUpper H) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizerModO2 (oTwoUpper H)
      (le_normalizer_oTwoUpper H hh)) d).mp hdC
  have hC : h * d * h⁻¹ * d⁻¹ ∈ centralizerModO2 (oTwoUpper H) :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hdC)
  have hdH : d * h⁻¹ * d⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp (s.D_le_normalizer_H hI hd) _).mp (H.inv_mem hh)
  have hH : h * d * h⁻¹ * d⁻¹ ∈ H := by
    have := H.mul_mem hh hdH
    simpa [mul_assoc] using this
  exact s.pCoreOf_le_pCoreOf_sup hI (s.hyp.inf_centralizerModO2_le ⟨hH, hC⟩)

theorem exists_D_fixedPointFree (hI : L2OddInnerFact) (hF : L2TorusFact) :
    ∃ d ∈ D, d ∈ Subgroup.normalizer (V : Set G) ∧ ∀ v ∈ V,
      (d * v * d⁻¹)⁻¹ * v ∈ quasithinOmegaOneCenter T ⊓ V →
        v ∈ quasithinOmegaOneCenter T ⊓ V := by
  obtain ⟨c⟩ := s.nonempty_coord
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : c.K, μ ≠ 0 ∧ μ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set c.K) ⊆ {0, 1} := fun μ _ => by
      by_cases h0 : μ = 0
      · exact Or.inl h0
      · exact Or.inr (hcon μ h0)
    have hle : Nat.card c.K ≤ 2 := by
      rw [← Set.ncard_univ]
      calc (Set.univ : Set c.K).ncard ≤ ({0, 1} : Set c.K).ncard := Set.ncard_le_ncard hsub
        _ = 2 := Set.ncard_pair zero_ne_one
    have h2n := s.hyp.hyp.toHyp5_0_1.two_le
    rw [c.card] at hle
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  obtain ⟨d, hdD, hdact⟩ := s.exists_D_act_eq hI hF c hμ0
  refine ⟨d, hdD, d.2, fun v hv hvZ => ⟨?_, hv⟩⟩
  have hab : conjAct V d ⟨v, hv⟩ * ((conjAct V d ⟨v, hv⟩)⁻¹ * ⟨v, hv⟩) = ⟨v, hv⟩ :=
    mul_inv_cancel_left _ _
  have hb : (((conjAct V d ⟨v, hv⟩)⁻¹ * ⟨v, hv⟩ : ↥V) : G) ∈ quasithinOmegaOneCenter T := by
    have e : (((conjAct V d ⟨v, hv⟩)⁻¹ * ⟨v, hv⟩ : ↥V) : G) = ((d : G) * v * (d : G)⁻¹)⁻¹ * v := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.coe_conjAct_apply]
    rw [e]
    exact hvZ.1
  have hb1 := (s.mem_Z_iff hI c _).mp hb
  have h1 : c.ε ⟨v, hv⟩ = c.ε (conjAct V d ⟨v, hv⟩) + c.ε ((conjAct V d ⟨v, hv⟩)⁻¹ * ⟨v, hv⟩) := by
    rw [← c.ε_mul, hab]
  have h2 := congrFun h1 1
  rw [Pi.add_apply, hb1, add_zero, ← c.act_ε, hdact] at h2
  have h3 : (1 - μ) * c.ε ⟨v, hv⟩ 1 = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
  have h4 : c.ε ⟨v, hv⟩ 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))
  exact (s.mem_Z_iff hI c ⟨v, hv⟩).mpr h4

theorem conjClosure_sup_D (hI : L2OddInnerFact) : conjClosure V (H ⊔ D) = conjClosure V H := by
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  have key : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) →
        ∀ x ∈ conjClosure V H, g * x * g⁻¹ ∈ conjClosure V H := by
    intro g hgH hgV x hx
    have hle : conjClosure V H ≤ (conjClosure V H).comap (MulAut.conj g).toMonoidHom :=
      conjClosure_le fun h hh v hv => by
        show g * (h * v * h⁻¹) * g⁻¹ ∈ conjClosure V H
        have e : g * (h * v * h⁻¹) * g⁻¹ =
            (g * h * g⁻¹) * (g * v * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
        rw [e]
        exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hgH h).mp hh)
          ((Subgroup.mem_normalizer_iff.mp hgV v).mp hv)
    exact hle hx
  have hDN : D ≤ Subgroup.normalizer (conjClosure V H : Set G) := by
    intro d hd
    have hdH := s.D_le_normalizer_H hI hd
    have hdV := s.L_le_normalizer_V (hDL hd)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key d hdH hdV x, fun hx => ?_⟩
    have := key d⁻¹ (Subgroup.inv_mem _ hdH) (Subgroup.inv_mem _ hdV) _ hx
    simpa [mul_assoc] using this
  refine le_antisymm (conjClosure_le fun g hg v hv => ?_) (conjClosure_mono le_rfl le_sup_left)
  have hgN : g ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    (sup_le (le_normalizer_conjClosure V H) hDN) hg
  exact (Subgroup.mem_normalizer_iff.mp hgN v).mp (le_conjClosure V H hv)

theorem two_pow_nine_le
    (hI : L2OddInnerFact) (hF : L2TorusFact) (hTC : L34TorusCommFact)
    (hF81 : HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D)) {y : G} (hy : y ∈ H ⊔ D)
    (hyQ : y ∉ pCoreOf 2 (H ⊔ D)) (hy2 : y ^ 2 ∈ pCoreOf 2 (H ⊔ D)) :
    2 ^ 9 ≤ (centralizerMod (quasithinOmegaOneCenter T ⊓ V) (conjClosure V (H ⊔ D))
      (Subgroup.zpowers y)).relIndex (conjClosure V (H ⊔ D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hQ : pCoreOf 2 (H ⊔ D) = centralizerMod (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D)
      (conjClosure V (H ⊔ D)) := hF81.F82_3
  have hUab : IsElemAbelian 2 (conjClosure V (H ⊔ D)) := F8.isElemAbelian_conjClosure hF81
  have hZU : quasithinOmegaOneCenter T ⊓ V ≤ conjClosure V (H ⊔ D) :=
    inf_le_right.trans (le_conjClosure V _)
  have hUZ : conjClosure V (H ⊔ D) ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      F7.isElemAbelian_comm hUab (hZU hz) hu)
  have hXZ : H ⊔ D ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := hF81.H_normalizes_V₁
  have hXU : H ⊔ D ≤ Subgroup.normalizer (conjClosure V (H ⊔ D) : Set G) :=
    le_normalizer_conjClosure V _
  have hXW := tildeOf_le_normalizer_tildeOf (Z₁ := quasithinOmegaOneCenter T ⊓ V) hXU
  have hKX : oTwoUpper H ≤ H ⊔ D := (oTwoUpper_le H).trans le_sup_left
  have hKN : H ⊔ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (le_normalizer_oTwoUpper H) s.D_le_normalizer
  have hKker : ∀ k ∈ oTwoUpper H, k ∈ centralizerMod (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D)
      (conjClosure V (H ⊔ D)) ↔ k ∈ pCoreOf 2 (oTwoUpper H) := by
    intro k hk
    rw [← hQ]
    constructor
    · intro hkQ
      exact le_pCoreOf_of_le_normalizer 2 inf_le_left
        (le_normalizer_inf Subgroup.le_normalizer
          (hKX.trans (le_normalizer_pCoreOf 2 (H ⊔ D))))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨hk, hkQ⟩
    · intro hkO
      exact s.pCoreOf_le_pCoreOf_sup hI (Setup521.pCoreOf_K_le hkO)
  obtain ⟨d, hdD, hdV, hdfix⟩ := s.exists_D_fixedPointFree hI hF
  have hcardD : Nat.card D = 2 ^ n - 1 := (hh.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).2
  have hdord : orderOf d ∣ Nat.card D := by
    rw [← Subgroup.orderOf_mk d hdD]
    exact orderOf_dvd_natCard _
  have hdn : d ^ (2 ^ n - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hcardD ▸ hdord)
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 hdord
  have hyH : y ∈ H := s.mem_H_of_sq_mem hI hy hy2
  have hHd : ∀ h ∈ H, h * d * h⁻¹ * d⁻¹ ∈ centralizerMod (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D)
      (conjClosure V (H ⊔ D)) := fun h hh => hQ ▸ s.commutator_mem_pCoreOf hI hh hdD
  have hfix := fixed_tilde_eq hUab hUZ hXZ hXW hXU (s.conjClosure_sup_D hI) le_sup_left
    (Subgroup.mem_sup_right hdD) hdodd hdV hHd hdfix
  refine two_pow_nine_le_of_tilde hTC hUab hUZ hXZ hXW hXU hKX s.hyp.l34 hKker s.odd
    (Subgroup.mem_sup_right hdD) hdn (fun k hk => hHd k (oTwoUpper_le H hk)) hfix hy (hKN hy)
    (hQ ▸ hy2) (hHd y hyH) fun hall => hyQ ?_
  have hyC : y ∈ centralizerModO2 (oTwoUpper H) := by
    refine ⟨hKN hy, normalizer_le_normalizer_pCoreOf 2 _ (hKN hy), fun k hk => ?_⟩
    have hcK : y * k * y⁻¹ * k⁻¹ ∈ oTwoUpper H :=
      (oTwoUpper H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hy) k).mp hk)
        ((oTwoUpper H).inv_mem hk)
    exact (hKker _ hcK).mp (hall k hk)
  exact s.pCoreOf_le_pCoreOf_sup hI (s.hyp.inf_centralizerModO2_le ⟨hyH, hyC⟩)

end Setup5_1_17Odd

theorem stmt5_1_17_mNine_of
    (hI : L2OddInnerFact) (hF : L2TorusFact) (hTC : L34TorusCommFact) : Stmt5_1_17_mNine := by
  intro G _ _ T M L V H B D n s hF81 y hy hyQ hy2
  exact s.two_pow_nine_le hI hF hTC hF81 hy hyQ hy2

theorem stmt5_1_17_of_torusComm
    (h515 : Stmt5_1_15) (h516 : Stmt5_1_16) (h325 : Stmt3_2_5) (h3228 : Stmt3_2_2_eight)
    (h513 : Stmt5_1_3) (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10)
    (h517one : A5.Stmt5_1_7_one) (h126 : A126TwoFact) (hTC : L34TorusCommFact) : Stmt5_1_17 :=
  stmt5_1_17_of_reduced l2OddInnerFact l34SylowNormFact l2TorusFact h515 h516
    (irrPlusBaseNonempty_of_a36 VolI.a36ForSQTK_holds)
    (stmt3_2_3_of_a38_a39
      (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
        Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
      Vol2Native.a39ForSQTKCat_proved)
    h325 h3228 h513 h5114 h510 l34BorelFact h517one h126
    (stmt5_1_17_mNine_of l2OddInnerFact l2TorusFact hTC)

end CFSG.Quasithin.H13
