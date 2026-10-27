module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDelete
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStdA
import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Additive

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem qtwoDB13_closure_pair_eq_sup (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

theorem qtwoDB13_stdSubPre_of {B Bs L J₁ : Subgroup G} {x : G} {m : ℕ}
    {βL : Additive ↥Bs ≃+ DVec m} (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hBBs : B ≤ Bs)
    (hxB : x ∈ B) (hxBs : x ∈ Bs) (hxord : orderOf x = 3) (hm : 2 ≤ m)
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {c : Fin m} {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B)
    (hlayer : LargeEvenLayer (L ⊓ Subgroup.centralizer
      (Subgroup.closure {x, (b' : G)} : Set G)) = J₁)
    (hcomp : IsComponentOf J₁
      (L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)))
    (hcent : Bs ⊓ Subgroup.centralizer (J₁ : Set G) = Subgroup.closure {x, (b' : G)}) :
    LargeEvenStdSubPre 3 B x L (Subgroup.closure {x, (b' : G)}) J₁ := by
  have hx_mem : x ∈ Bs := hxBs
  have hb'_mem : (b' : G) ∈ Bs := b'.2
  have hDleBs : Subgroup.closure {x, (b' : G)} ≤ Bs := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hx_mem
    · exact hb'_mem
  have hDleB : Subgroup.closure {x, (b' : G)} ≤ B := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxB
    · exact hb'B
  have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hb'3 : (b' : G) ^ 3 = 1 := hBs.2 (b' : G) b'.2
  have hcomm : x * (b' : G) = (b' : G) * x := by
    have h := hBs.1.is_comm.comm (⟨x, hx_mem⟩ : ↥Bs) (⟨(b' : G), b'.2⟩ : ↥Bs)
    exact congrArg Subtype.val h
  have hb'not : (b' : G) ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (⟨x, hx_mem⟩ : ↥Bs) ^ k = b' := by
      apply Subtype.ext
      simpa using hk
    have hβ := congrArg (fun z : ↥Bs => βL (Additive.ofMul z)) hk'
    rw [ofMul_zpow, map_zsmul, hxcoord, hb'] at hβ
    have hm2 : 1 < m := by omega
    have hcard : 1 < Fintype.card (Fin m) := by simpa [Fintype.card_fin] using hm2
    obtain ⟨d, hdc⟩ := Fintype.exists_ne_of_one_lt_card hcard c
    have h1 : (k : ZMod 3) = 1 := by
      have h := congrFun hβ c
      rw [Pi.single_eq_same] at h
      change k • (1 : ZMod 3) = 1 at h
      rwa [zsmul_eq_mul, mul_one] at h
    have h0 : (k : ZMod 3) = 0 := by
      have h := congrFun hβ d
      rw [Pi.single_eq_of_ne hdc] at h
      change k • (1 : ZMod 3) = 0 at h
      rwa [zsmul_eq_mul, mul_one] at h
    exact one_ne_zero (h1.symm.trans h0)
  have hcardD : Nat.card (Subgroup.closure {x, (b' : G)}) = 3 ^ 2 := by
    rw [qtwoDB13_closure_pair_eq_sup]
    have hb'1 : (b' : G) ≠ 1 := fun h => hb'not (h ▸ Subgroup.one_mem _)
    have hb'ord : orderOf (b' : G) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime hb'3 hb'1
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
    have hcardb : Nat.card (Subgroup.zpowers (b' : G)) = 3 := by
      rw [Nat.card_zpowers, hb'ord]
    have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers (b' : G) = ⊥ := by
      have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers x :=
        inf_le_left
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (b' : G) : Subgroup G) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hle
        rwa [hcardx] at h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have hge : Nat.card (Subgroup.zpowers x) ≤
            Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (b' : G) : Subgroup G) := by
          rw [h3, hcardx]
        have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (b' : G) = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge hle hge
        have hle' : Subgroup.zpowers x ≤ Subgroup.zpowers (b' : G) := heq ▸ inf_le_right
        have heq2 : Subgroup.zpowers x = Subgroup.zpowers (b' : G) :=
          Subgroup.eq_of_le_of_card_ge hle' (by rw [hcardb, hcardx])
        exact hb'not (heq2.symm ▸ Subgroup.mem_zpowers (b' : G))
    have hcommxb : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers (b' : G),
        a * c = c * a := fun a ha c hc => by
      have h := hBs.1.is_comm.comm (⟨a, Subgroup.zpowers_le.mpr hx_mem ha⟩ : ↥Bs)
        (⟨c, Subgroup.zpowers_le.mpr b'.2 hc⟩ : ↥Bs)
      exact congrArg Subtype.val h
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) (Subgroup.zpowers (b' : G)) hcommxb).1
    rw [hdisj, Subgroup.card_bot, mul_one, hcardx, hcardb] at h1
    have h1' : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers (b' : G) : Subgroup G) = 9 := by
      simpa using h1
    rw [h1']
    norm_num
  have hcore := And.intro hlayer hcomp
  unfold LargeEvenStdSubPre
  refine ⟨hDleB, ?_, hcardD, ?_, hcore.1.symm, hcore.2, ?_⟩
  · unfold CFSG.Open.IsElemAbelian
    refine ⟨?_, ?_⟩
    · exact ⟨⟨fun a b => Subtype.ext (by
        have h := hBs.1.is_comm.comm (⟨a, hDleBs a.2⟩ : ↥Bs) (⟨b, hDleBs b.2⟩ : ↥Bs)
        exact congrArg (fun z : ↥Bs => (z : G)) h)⟩⟩
    · intro z hz
      exact hBs.2 z (hDleBs hz)
  · exact Subgroup.subset_closure (Set.mem_insert x {(b' : G)})
  ·
    apply le_antisymm
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨hDleB hz, ?_⟩
      rw [← hcent] at hz
      exact (Subgroup.mem_inf.mp hz).2
    · intro z hz
      rw [Subgroup.mem_inf] at hz
      rw [← hcent]
      exact Subgroup.mem_inf.mpr ⟨hBBs hz.1, hz.2⟩

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

private theorem qtwoDB13_map_centralizer_conj (g y : G) :
    (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hw' : w * y = y * w :=
      ((Subgroup.mem_centralizer_iff).mp hw y (Set.mem_singleton y)).symm
    change (g * y * g⁻¹) * (g * w * g⁻¹) = (g * w * g⁻¹) * (g * y * g⁻¹)
    calc (g * y * g⁻¹) * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [← hw']
      _ = (g * w * g⁻¹) * (g * y * g⁻¹) := by group
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      have hz' : (g * y * g⁻¹) * z = z * (g * y * g⁻¹) :=
        (Subgroup.mem_centralizer_iff).mp hz (g * y * g⁻¹) (Set.mem_singleton _)
      change y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y
      calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [hz']
        _ = (g⁻¹ * z * g) * y := by group
    · change g * (g⁻¹ * z * g) * g⁻¹ = z
      group

private theorem qtwoDB13_layer_eq_of_derived_le {H D : Subgroup G}
    (hD : IsComponentOf D H) (hcomm : ⁅H, H⁆ ≤ D) :
    LargeEvenLayer H = D := by
  have hperf : ∀ {K' : Subgroup G}, IsComponentOf K' H → ⁅K', K'⁆ = K' :=
    fun hK' => Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hK'.2.2.1)
  refine le_antisymm ?_ (le_sSup hD)
  rw [LargeEvenLayer]
  refine sSup_le fun K' hK' => ?_
  calc K' = ⁅K', K'⁆ := (hperf hK').symm
    _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hK'.1 hK'.1
    _ ≤ D := hcomm

theorem qtwoDB13_layer_eq (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {c : Fin m} {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    LargeEvenLayer (L ⊓ Subgroup.centralizer
        (Subgroup.closure {x, (b' : G)} : Set G)) =
      (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ∧
    IsComponentOf ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ)
      (L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)) := by
  classical
  have hF0 : Nat.card F0 = 4 := hbase.card_field
  have hω : orderOf ω = 3 := hcoords.ω_order
  have hω1 : ω ≠ 1 := by rintro rfl; simp at hω
  have hm3 : 3 ≤ m := by omega
  have hm6 : 5 ≤ m := by omega
  set δ : MulAut (Su F0 2 1 m) := qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c) with hδ
  set K : Subgroup (Su F0 2 1 m) := coordBlockSU F0 2 1 (Finset.univ.erase c) with hK
  set J1 : Subgroup G := K.map ψ with hJ1
  set F : Subgroup (Su F0 2 1 m) :=
    CFSG.ClassicalInvolution.Balance.fixedGroup δ with hF
  set H : Subgroup G :=
    L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G) with hH
  have hψδ : ∀ u : Su F0 2 1 m,
      (b' : G) * ψ u * (b' : G)⁻¹ = ψ (δ u) := by
    intro u
    have hc : (fun i : Fin m => ω ^ (βL (Additive.ofMul b') i).val)
        = qtwoDB39_delDiag ω c := by
      funext i
      rw [hb']
      by_cases hi : i = c
      · rw [hi]; simp [qtwoDB39_delDiag, Pi.single_eq_same, ZMod.val_one]
      · simp [qtwoDB39_delDiag, hi, Pi.single_eq_of_ne hi]
    obtain ⟨u', hu'mat, hu'ψ⟩ := hcoords.induces b' u
    have hu'eq : u' = δ u := by
      apply Subtype.ext
      rw [hδ, qtwoDB39_conjAut_apply, hu'mat, hc]
    rw [← hu'ψ, hu'eq]
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    have hx' : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hbase.cent]; exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hx').2
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxL) l hl
  have hCpair : Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)
      = Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hCinf : L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)
      = L ⊓ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [hCpair, ← inf_assoc, inf_eq_left.mpr hLx]
  have hFH : F.map ψ = H := by
    rw [hF, hH, hCinf]
    apply le_antisymm
    · rintro y hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hbase.range]
        exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hu' : δ u = u := CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hu
        have h1 := hψδ u
        rw [hu'] at h1
        calc ψ u * (b' : G) = ((b' : G) * ψ u * (b' : G)⁻¹) * (b' : G) := by rw [h1]
          _ = (b' : G) * ψ u := by group
    · rintro y ⟨hyL, hyb⟩
      rw [← hbase.range] at hyL
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hyL
      have hbu : ψ u * (b' : G) = (b' : G) * ψ u :=
        Subgroup.mem_centralizer_singleton_iff.mp hyb
      have hu_fix : u ∈ F := by
        rw [hF, CFSG.ClassicalInvolution.Balance.mem_fixedGroup]
        have hkeq : ψ (δ u) = ψ u := by
          rw [← hψδ u, ← hbu]
          group
        have hker : δ u * u⁻¹ ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hkeq, mul_inv_cancel]
        have hcenter : δ u * u⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := hbase.hyp.ker hker
        have h := qtwoDB39_fixed_of_conj_scalar hF0 hm3 hω hcenter
          (show δ u = (δ u * u⁻¹) * u by group)
        rw [← hδ] at h
        exact h
      exact Subgroup.mem_map.mpr ⟨u, hu_fix, rfl⟩
  have hQ : IsComponentOf K F := by
    rw [hK, hF, hδ]
    exact qtwoDB39_isComponentOf hF0 hω1 hm6
  have hcomp : IsComponentOf J1 H := by
    have hQopen : CFSG.Open.IsComponentOf K F :=
      (CFSG.Assembly.isComponentOf_iff_open).mp hQ
    have hrel : ∀ y : Su F0 2 1 m,
        (b' : G) * ψ ((1 : Su F0 2 1 m) * y * (1 : Su F0 2 1 m)⁻¹) * (b' : G)⁻¹ =
          ψ ((1 : Su F0 2 1 m) * δ y * (1 : Su F0 2 1 m)⁻¹) := by
      intro y; simpa using hψδ y
    have hopen := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer
      hbase.hyp.ker (1 : Su F0 2 1 m) (b' : G) δ hrel hQopen
    have hhom : ψ.comp (MulAut.conj (1 : Su F0 2 1 m)).toMonoidHom = ψ := by
      ext u
      simp [MulAut.conj_apply]
    rw [CFSG.ClassicalInvolution.Balance.range_comp_conj ψ (1 : Su F0 2 1 m),
      hhom, hbase.range] at hopen
    rw [hH, hCinf]
    exact (CFSG.Assembly.isComponentOf_iff_open).mpr hopen
  have hFF : ⁅F, F⁆ ≤ K := by
    rw [hF, hδ, hK]
    exact qtwoDB39_commutator_le hF0 hω1
  have hcomm : ⁅H, H⁆ ≤ J1 := by
    rw [← hFH, hJ1, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hFF
  exact ⟨qtwoDB13_layer_eq_of_derived_le hcomp hcomm, hcomp⟩

theorem qtwoDB13_not_small (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (c : Fin m) :
    ¬ LargeEvenSmall ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) := by
  obtain ⟨θ, hθ_inj, hθ_range, -⟩ := ggQTwoDUnit_J_iso (by omega) hbase c 1
  have hm1 : 6 ≤ m - 1 := by omega
  obtain ⟨S', -, hS'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (m - 1)))) (n := 6) (by simpa using hm1)
  have hinj : Function.Injective
      (blockSUOn F0 2 1 S' : Su F0 2 1 S'.card →* Su F0 2 1 (m - 1)) :=
    blockSUOn_injective S'
  have hcard_le : Nat.card (Su F0 2 1 6) ≤ Nat.card (Su F0 2 1 (m - 1)) := by
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [hS'card] at h
  have hcard6 : Nat.card (Su F0 2 1 6) = 27590492160 := card_Su_six hbase.card_field
  have hcardJ : Nat.card ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) =
      Nat.card (Su F0 2 1 (m - 1)) := by
    rw [← hθ_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hθ_inj).toEquiv).symm
  have hbig : GGBigLayer ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) := by
    refine Or.inr ?_
    rw [hcardJ]
    calc 25920 < 27590492160 := by norm_num
      _ = Nat.card (Su F0 2 1 6) := hcard6.symm
      _ ≤ Nat.card (Su F0 2 1 (m - 1)) := hcard_le
  exact not_largeEvenSmall_of_map_big (MonoidHom.id G) _ (by simpa using hbig)

theorem ggQTwoDUnit_stdSubPre
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {c : Fin m} {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    LargeEvenStdSubPre 3 B x L (Subgroup.closure {x, (b' : G)})
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) := by
  have hcore := qtwoDB13_layer_eq hcfg hm hbase hcoords hb' hb'B
  exact qtwoDB13_stdSubPre_of (hbase.p_eq ▸ hbase.hyp.bstar.2.1) hbase.hyp.bstar.1
    (hcfg.1.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.1 hbase.x_mem hbase.x_order
    (by omega) (hcoords.x_coord hbase.x_mem) hb' hb'B hcore.1 hcore.2
    (ggQTwoDUnit_cent_J (by omega) hbase hcoords hb')

theorem ggQTwoDUnit_stdSub (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {c : Fin m} {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    LargeEvenStdSub 3 B x L (Subgroup.closure {x, (b' : G)})
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) := by
  unfold LargeEvenStdSub
  exact ⟨ggQTwoDUnit_stdSubPre hcfg (by omega) hbase hcoords hb' hb'B,
    fun _ => qtwoDB13_not_small hm hbase c⟩

theorem ggQTwoDUnit_J_comp (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b c : Fin m} (hca : c ≠ a)
    (hcb : c ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    IsComponentOf ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ)
        (Subgroup.centralizer ({(b' : G)} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      IsComponentOf
        (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom)
        (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
          Subgroup.centralizer ({g * x * g⁻¹} : Set G)) := by
  have hdSign_c : dSign m a b (Pi.single c 1) = Pi.single c 1 := by
    have hc : ¬ (c = a ∨ c = b) := by tauto
    have hb : Pi.single c 1 = dBasis m c := (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
    rw [hb, dSign_apply, if_neg hc, one_smul]
  have hαb' : α b' = b' := by
    apply Additive.ofMul.injective
    apply βL.injective
    rw [hα b', hb', hdSign_c]
  have hg_b' : g * (b' : G) * g⁻¹ = (b' : G) := by
    have h := hg b'
    rw [hαb'] at h
    exact h.symm
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre 3 B x L (Subgroup.closure {x, (b' : G)})
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) :=
    ggQTwoDUnit_stdSubPre hcfg hm hbase hcoords hb' hb'B
  have hS3 : LargeEvenSStar 3 B x L := by rwa [hbase.p_eq] at hS
  have h1 : IsComponentOf ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ)
      (Subgroup.centralizer ({(b' : G)} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS3 hpre rfl
  refine ⟨h1, ?_⟩
  have hmap : (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      qtwoDB13_map_centralizer_conj g (b' : G), hg_b',
      qtwoDB13_map_centralizer_conj g x]
  rw [← hmap]
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr h1

end CFSG.StandardType.QTwo

end
