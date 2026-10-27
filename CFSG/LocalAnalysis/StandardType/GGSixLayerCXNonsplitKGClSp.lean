module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClLift
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSpTag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts

theorem range_inf_centralizer_eq {L : Type*} [Group L] {G : Type*} [Group G] {ψ : L →* G}
    (hinj : Function.Injective ψ) {x : G} {s : L} (hs : (x, s) ∈ ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer {x} =
      (Subgroup.centralizer (Subgroup.zpowers s : Set L)).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, rfl⟩
    have hxu : x * ψ u = ψ u * x := (Subgroup.mem_centralizer_iff.mp hu x rfl)
    have h1 : s * u * s⁻¹ = u := hinj (by
      rw [hs u]
      calc x * ψ u * x⁻¹ = ψ u * x * x⁻¹ := by rw [hxu]
        _ = ψ u := by group)
    have hsu : Commute s u := by
      show s * u = u * s
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [h1]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (hsu.zpow_left k).eq
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.mp hg]
    have hsu : s * u = u * s := Subgroup.mem_centralizer_iff.mp hu s (Subgroup.mem_zpowers s)
    have h1 : s * u * s⁻¹ = u := by rw [hsu]; group
    have h2 := hs u
    rw [h1] at h2
    calc x * ψ u = x * ψ u * x⁻¹ * x := by group
      _ = ψ u * x := by rw [← h2]

variable {n : ℕ} {F : Type} [Field F]

theorem comap_adjCent_sp [CharP F 2] (s : StatedSp n F) :
    (adjCent (Subgroup.zpowers (s : GL (Fin n ⊕ Fin n) F))
        (isInvol_spAdj (n := n) (F := F))).comap (StatedSp n F).subtype =
      Subgroup.centralizer (Subgroup.zpowers s : Set (StatedSp n F)) := by
  ext u
  rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hu, -⟩ g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    apply Subtype.ext
    have h := hu ((s : GL (Fin n ⊕ Fin n) F) ^ k) (Subgroup.zpow_mem_zpowers _ k)
    simpa [Subgroup.coe_zpow] using h
  · intro hu
    refine ⟨fun g hg => ?_, mem_unitaryOf_spAdj_iff.mpr u.2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h := congrArg Subtype.val (hu (s ^ k) (Subgroup.zpow_mem_zpowers s k))
    simpa [Subgroup.coe_zpow] using h

theorem exists_isComponentOf_le_sp {G : Type*} [Group G] [Finite G] [Finite F] [CharP F 2]
    {ψ : StatedSp n F →* G} (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) {s t : StatedSp n F} (hs : (x, s) ∈ ggConjPairs ψ)
    (ht : (y, t) ∈ ggConjPairs ψ) {K : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' := by
  classical
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) n).le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  have hsp : s ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem hs p
    rwa [Prod.pow_mk, hx] at h)
  have htp : t ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem ht p
    rwa [Prod.pow_mk, hy] at h)
  have hst : s * t = t * s := by
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs ht)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem ht hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * t = s * t * (t * s)⁻¹ * (t * s) := by group
      _ = t * s := by rw [h1, one_mul]
  have hAu : (s : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr s.2
  have hBu : (t : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr t.2
  have hAp : (s : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hsp, Subgroup.coe_one]
  have hBp : (t : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, htp, Subgroup.coe_one]
  have hAB : (s : GL (Fin n ⊕ Fin n) F) * t = t * s := by
    rw [← Subgroup.coe_mul, hst, Subgroup.coe_mul]
  have hsymd : ∀ {C : GL (Fin n ⊕ Fin n) F}, C ∈ StatedSp n F → C ^ p = 1 →
      ∃ Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
        Y * (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Y ∧ Y + spAdj n F Y = 1 := by
    intro C hC hCp
    obtain ⟨Y, hY1, hY2⟩ := exists_symd_spAdj (A := Subgroup.zpowers C)
      (fun g hg => Subgroup.zpowers_le.mpr hC hg) (natCast_card_zpowers_ne_zero hp hp2 hCp)
    exact ⟨Y, hY1 C (Subgroup.mem_zpowers C), hY2⟩
  obtain ⟨β, Sx, hFx, β', Sy, hFy, hlift⟩ := exists_coreFamilies_lift
    (isInvol_spAdj (n := n) (F := F)) hAu hBu hp hp2 hAp hBp hAB (hsymd s.2 hAp)
    (hsymd t.2 hBp)
  have hle : ∀ C : GL (Fin n ⊕ Fin n) F,
      adjCent (Subgroup.zpowers C) (isInvol_spAdj (n := n) (F := F)) ≤
        (StatedSp n F).subtype.range := fun C g hg =>
    ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hFx' := hFx.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) (hle s)
  have hFy' := hFy.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) (hle t)
  rw [comap_adjCent_sp s] at hFx'
  rw [comap_adjCent_sp t] at hFy'
  rw [range_inf_centralizer_eq hinj hs] at hK
  rw [range_inf_centralizer_eq hinj ht]
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) _ hFx'.1 hFx'.2.1
    hFx'.2.2.1 hFx'.2.2.2.1 hK
  have hpc : ¬ p ∣ Nat.card (Sx c) := by
    intro h
    apply hpK
    rw [Subgroup.card_map_of_injective hinj,
      ← Subgroup.card_map_of_injective (Subgroup.subtype_injective (StatedSp n F)),
      Subgroup.map_comap_eq_self ((hFx.1 c).trans (hle s))]
    exact h
  obtain ⟨c', hc'⟩ := hlift c hpc
  exact ⟨((Sy c').comap (StatedSp n F).subtype).map ψ,
    LinNonsplit.isComponentOf_map_of_le ψ hker le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c'),
    Subgroup.map_mono (Subgroup.comap_mono hc')⟩

end ClNonsplit

section Tag

theorem ggNonsplitCompLiftTag_PSp : GGNonsplitCompLiftTag .PSp := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 _ _ x y hx hy hxy _ _ hxD hyD K hK hpK
  obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  rw [← hrange] at hK ⊢
  obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hxD
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hyD
  exact ClNonsplit.exists_isComponentOf_le_sp hker hp hp2 hx hy hxy hs ht hK hpK

end Tag

end CFSG.StandardType
