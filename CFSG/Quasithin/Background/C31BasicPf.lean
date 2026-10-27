module

public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.C41PfE
public import CFSG.Quasithin.Background.C48Supp
public import CFSG.Quasithin.Background.C48SporSetup
public import CFSG.Quasithin.Background.F918V3S3Aux
public import CFSG.Quasithin.Background.C31Insp

public section

namespace CFSG.Quasithin.C31B

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem eq_bot_of_inspC33 (hInsp : InspC33) {Y : Type} [Group Y] [Finite Y] (hY : A38Types Y)
    (hZ : Subgroup.center Y = ⊥) (hOut : OutSolvable Y) {D : Type} [Group D]
    (hD : Group.IsPerfect D) (φ : D →* MulAut Y) {W : Subgroup D} (hW : IsElemAbelian 2 W)
    (hWD : ⁅W, ⊤⁆ = W) : W.map φ = ⊥ := by
  set c : Y →* MulAut Y := MulAut.conj with hc
  have hcinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : y * g * y⁻¹ = g := by
      have := congrArg (fun f : MulAut Y => f g) (MonoidHom.mem_ker.mp hy)
      simpa [hc, MulAut.conj_apply] using this
    calc g * y = (y * g * y⁻¹) * y := by rw [h1]
      _ = y * g := by group
  have hinner : φ.range ≤ c.range := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨y, hy⟩ := A38.exists_inner_of_outSolvable hOut hD φ d
    exact ⟨y, hy.symm⟩
  set Mb := φ.range.comap c with hMb
  set Wb := (W.map φ).comap c with hWb
  have hmapM : Mb.map c = φ.range := by
    rw [hMb, Subgroup.map_comap_eq, inf_eq_right.mpr hinner]
  have hmapW : Wb.map c = W.map φ := by
    rw [hWb, Subgroup.map_comap_eq, inf_eq_right.mpr ((Subgroup.map_mono le_top).trans
      (by rw [← MonoidHom.range_eq_map]; exact hinner))]
  have hinj : ∀ {A B : Subgroup Y}, A.map c = B.map c → A = B := fun h =>
    Subgroup.map_injective hcinj h
  have hMp : ⁅Mb, Mb⁆ = Mb := by
    apply hinj
    rw [Subgroup.map_commutator, hmapM, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      ← _root_.commutator_def, Group.isPerfect_def.mp hD]
  have hWM : Wb ≤ Mb := Subgroup.comap_mono (by
    rw [MonoidHom.range_eq_map]; exact Subgroup.map_mono le_top)
  have hWc : ⁅Wb, Mb⁆ = Wb := by
    apply hinj
    rw [Subgroup.map_commutator, hmapW, hmapM, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      hWD]
  have hWe : IsElemAbelian 2 Wb := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcinj ?_)⟩⟩, fun x hx => hcinj ?_⟩
    · obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp (show c a ∈ W.map φ from a.2)
      obtain ⟨v, hv, hvb⟩ := Subgroup.mem_map.mp (show c b ∈ W.map φ from b.2)
      have huv : u * v = v * u := congrArg Subtype.val
        (hW.1.is_comm.comm (⟨u, hu⟩ : ↥W) ⟨v, hv⟩)
      show c ((a : Y) * b) = c ((b : Y) * a)
      rw [map_mul, map_mul, ← hua, ← hvb, ← map_mul, ← map_mul, huv]
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp (show c x ∈ W.map φ from hx)
      rw [map_pow, ← hux, ← map_pow, hW.2 u hu, map_one, map_one]
  have hbot := hInsp Y hY Mb Wb hMp hWM hWe hWc
  rw [← hmapW, hbot, Subgroup.map_bot]

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem isPGroup_centerOf (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H) :
    IsPGroup 2 ↥(centerOf K) := by
  have hO := c2_10_one h
  intro z
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : G)).ne'
  have h2a : 2 ^ a ∣ orderOf (z : G) := ⟨m, ham⟩
  have hord : orderOf ((z : G) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (by positivity) h2a, ham, Nat.mul_div_cancel_left _ (by positivity)]
  have hzK : (z : G) ^ 2 ^ a ∈ K := K.pow_mem z.2.1 _
  have hcen : ∀ k ∈ K, k * (z : G) ^ 2 ^ a = (z : G) ^ 2 ^ a * k := fun k hk =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ z.2.2 _)) k hk)
  have hmem := C48.mem_oddCoreIn_of_mem_center hK.2.1 hzK hcen (hord ▸ hm)
  rw [hO, Subgroup.mem_bot] at hmem
  exact ⟨a, Subtype.ext (by simpa using hmem)⟩

theorem pCoreOf_le_centralizer (hK : CFSG.Open.IsComponentOf K H) :
    pCoreOf 2 K ≤ Subgroup.centralizer (K : Set G) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.LieType.BorelTits.pCore_normal (G := ↥K) 2) with htop | hle
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥K := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2).of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
    have : Group.IsNilpotent ↥K := hp.isNilpotent
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥K := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥K inferInstance
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hx) ⟨k, hk⟩)

theorem le_centralizer_of_commutator_le (hK : CFSG.Open.IsComponentOf K H) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hX : ⁅X, K⁆ ≤ pCoreOf 2 K) :
    X ≤ Subgroup.centralizer (K : Set G) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  intro x hx
  refine C48Spor.mem_centralizer_of_perfect hperf (hXN hx) fun k hk => ?_
  have := hX (Subgroup.commutator_mem_commutator hx hk)
  rw [commutatorElement_def] at this
  exact pCoreOf_le_centralizer hK this

theorem not_le_centralizer (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H) :
    ¬ V ≤ Subgroup.centralizer (K : Set G) := by
  intro hV
  refine c2_10_two h K hK fun k hk => h.V_norm ⟨hK.1 hk, ?_⟩
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
  exact (Subgroup.mem_centralizer_iff.mp (hV hv) k hk).symm

theorem le_normalizer
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp : InspC33) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hn
  have hKc : K ∈ cComp H := F918V3S3.mem_cComp_of_isComponentOf hK
  obtain ⟨hq, htypes⟩ := C48.a38_of_not_le_normalizer h36 h38 h.sqtk hKc hn
  have hS : IsSimpleGroup (ModO2 K) := Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  have hZ : Subgroup.center (ModO2 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 K)) with hZ | hZ
    · exact hZ
    · exfalso
      obtain ⟨-, hs, -⟩ := hq
      have hsub : Subsingleton (ModO2 K ⧸ Subgroup.center (ModO2 K)) := by
        rw [hZ]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_subsingleton _) hsub
  have hOut := hSch K (h.sqtk.mono hK.1) hq
  have hNK := C41Pf.conjClosure_le_normalizer hA3 h hKc
  have hDp : Group.IsPerfect ↥(conjClosure L M) := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    apply Subgroup.map_injective (conjClosure L M).subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      C2Nine.perfect_conjClosure_of_hyp h]
  set φ := (C41Pf.quotConjHom K).comp (Subgroup.inclusion hNK) with hφ
  have hWe : IsElemAbelian 2 (V.subgroupOf (conjClosure L M)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (h.V_elem.1.is_comm.comm (⟨(a : G), a.2⟩ : ↥V) ⟨(b : G), b.2⟩)
      simpa using this
    · simpa using h.V_elem.2 x hx
  have hWD : ⁅V.subgroupOf (conjClosure L M), ⊤⁆ = V.subgroupOf (conjClosure L M) := by
    have h1 := C41Pf.commutator_subgroupOf h.V_le le_rfl (N := conjClosure L M)
    rw [Subgroup.subgroupOf_self] at h1
    rw [h1, h.V_comm]
  have hbot := eq_bot_of_inspC33 hInsp htypes hZ hOut hDp φ hWe hWD
  apply not_le_centralizer h hK
  refine le_centralizer_of_commutator_le hK (h.V_le.trans hNK) ?_
  refine C41Pf.commutator_le_of_le_centModO2 fun v hv => ?_
  refine C41Pf.mem_centModO2_iff.mpr ⟨hNK (h.V_le hv), ?_⟩
  have : φ ⟨v, h.V_le hv⟩ ∈ (V.subgroupOf (conjClosure L M)).map φ :=
    Subgroup.mem_map_of_mem φ (show (⟨v, h.V_le hv⟩ : ↥(conjClosure L M)) ∈
      V.subgroupOf (conjClosure L M) from hv)
  rw [hbot, Subgroup.mem_bot] at this
  exact this

theorem c31BasicStep_of
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp : InspC33) : C31BasicStep G := by
  intro H R M L V K h hK
  have hKc : K ∈ cComp H := F918V3S3.mem_cComp_of_isComponentOf hK
  have hHN := le_normalizer h36 h38 hA3 hSch hInsp h hK
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := h.le_H.trans hHN
  have hRN : R ≤ Subgroup.normalizer (K : Set G) := h.le_M.trans hMN
  have hNK := C41Pf.conjClosure_le_normalizer hA3 h hKc
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hqb : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) ?_
    by_contra hall
    push Not at hall
    have htop : CFSG.pCore 2 ↥K = ⊤ := eq_top_iff.mpr fun k _ =>
      (QuotientGroup.eq_one_iff k).mp (hall k)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥K := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
    have : Group.IsNilpotent ↥K := hp.isNilpotent
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥K := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥K inferInstance
  have hOut := hSch K (h.sqtk.mono hK.1) hqb
  have hnc : ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K := fun hc =>
    not_le_centralizer h hK (h.V_le.trans (le_centralizer_of_commutator_le hK hNK hc))
  exact ⟨C41Pf.conjClosure_le_of_le_normalizer hOut h hK.1 hRN hNK hMN hnc, hMN,
    isPGroup_centerOf h hK⟩

end CFSG.Quasithin.C31B
