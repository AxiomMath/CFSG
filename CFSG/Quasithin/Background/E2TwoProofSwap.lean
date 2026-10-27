module

public import CFSG.Quasithin.Background.E2TwoProofN
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Background.E2TwoProofAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ} (S : Setting H T M L K)

structure SwapData (H T K : Subgroup Γ) (tb : ↥H ⧸ CFSG.pCore 2 ↥H) : Prop where
  types : A38Types ↥(kbar H K)
  mem : tb ∈ (T.subgroupOf H).map (barMap H)
  not_mem : tb ∉ Subgroup.normalizer (kbar H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))
  conjs : conjSubgroupsBy ((T.subgroupOf H).map (barMap H)) (kbar H K) =
    {kbar H K, (kbar H K).map (MulAut.conj tb).toMonoidHom}
  comm : ⁅kbar H K, (kbar H K).map (MulAut.conj tb).toMonoidHom⁆ = ⊥
  norm : (T.subgroupOf H).map (barMap H) ≤
    Subgroup.normalizer ((kbar H K ⊔ (kbar H K).map (MulAut.conj tb).toMonoidHom :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))

section
include S

theorem not_normal_kbar (hLn : ¬ L.Normal) : ¬ (kbar H K).Normal := by
  intro hK
  apply hLn
  rw [← S.map_psi_kbar]
  refine hK.map _ ?_
  intro y
  obtain ⟨x, rfl⟩ := starMap_surjective M H y
  exact ⟨barMap H x, S.psi_barMap x⟩

theorem exists_swapData (h38 : A38ForSQTKCat) (hLn : ¬ L.Normal) :
    ∃ tb, SwapData H T K tb := by
  have h := h38 _ (sqtkHypCat_bar S.sqtk) _ S.kbar_mem_cComp
  obtain ⟨h1, h2⟩ := h
  have hnn := S.not_normal_kbar hLn
  have htypes : A38Types ↥(kbar H K) := by
    rcases h1 with h1 | ⟨h1, -⟩
    · exact absurd h1 hnn
    · exact h1
  rcases h2 _ S.minPar_bar.isSylow with ⟨hn, -⟩ | ⟨tb, htb, hnot, hconjs, -, hcomm, -, hnorm, -⟩
  · exact absurd hn hnn
  · exact ⟨tb, ⟨htypes, htb, hnot, hconjs, hcomm, hnorm⟩⟩

end

namespace SwapData

variable {tb : ↥H ⧸ CFSG.pCore 2 ↥H}

omit [Finite Γ] in
theorem kbar_simple (D : SwapData H T K tb) :
    IsSimpleGroup ↥(kbar H K) :=
  CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types D.types

theorem kbar_exists_ne (S : Setting H T M L K) : ∃ x y : ↥(kbar H K), x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  apply S.factor.nonab
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : (a : E2.StarQuot M H) ∈ (kbar H K).map S.psi := S.map_psi_kbar.symm ▸ a.2
  have hb : (b : E2.StarQuot M H) ∈ (kbar H K).map S.psi := S.map_psi_kbar.symm ▸ b.2
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨y, hy, hyb⟩ := hb
  apply Subtype.ext
  have := congrArg S.psi (congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨y, hy⟩))
  simp only [Subgroup.coe_mul, map_mul] at this
  rw [hxa, hyb] at this
  exact this

theorem eq_one_of_comm (D : SwapData H T K tb)
    (S : Setting H T M L K)
    {a : ↥H ⧸ CFSG.pCore 2 ↥H}
    (ha : a ∈ kbar H K) (hc : ∀ k ∈ kbar H K, a * k = k * a) : a = 1 := by
  have hs := D.kbar_simple
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (kbar_exists_ne S)).2
  have hmem : (⟨a, ha⟩ : ↥(kbar H K)) ∈ Subgroup.center ↥(kbar H K) := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem jbar_normal (S : Setting H T M L K) : (jbar M H).Normal := by
  rw [← S.kerIn_bar]
  infer_instance

theorem jbar_comm_kbar (D : SwapData H T K tb)
    (S : Setting H T M L K) {z k : ↥H ⧸ CFSG.pCore 2 ↥H} (hz : z ∈ jbar M H)
    (hk : k ∈ kbar H K) : z * k = k * z := by
  have hns : ¬ Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H) := fun hs => by
    have := isSolvable_ker_barMap H
    exact S.ns (Group.isSolvable_of_ker_le_range (barMap H).ker.subtype (barMap H)
      (by rw [Subgroup.range_subtype]))
  have hF : CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) = jbar M H := by
    rw [S.minPar_bar.fittingSubgroup_eq_kerIn (open_pCore_bar H) hns, S.kerIn_bar]
  have hs := D.kbar_simple
  have hcomp : CFSG.IsComponent (kbar H K) :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (kbar_exists_ne S)).1,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp S.kbar_mem_cComp)⟩
  have hc := CFSG.LocalCores.fitting_layer_commute (G := ↥H ⧸ CFSG.pCore 2 ↥H)
  rw [hF, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact (Subgroup.mem_centralizer_iff.mp (hc hz) k
    (CFSG.LocalCores.component_le_layer hcomp hk)).symm

theorem jbar_comm_conj (D : SwapData H T K tb)
    (S : Setting H T M L K) {z y : ↥H ⧸ CFSG.pCore 2 ↥H} (hz : z ∈ jbar M H)
    (hy : y ∈ (kbar H K).map (MulAut.conj tb).toMonoidHom) : z * y = y * z := by
  obtain ⟨k, hk, rfl⟩ := hy
  have hJn := jbar_normal S
  have hz' : tb⁻¹ * z * tb ∈ jbar M H := by
    have := hJn.conj_mem z hz tb⁻¹
    simpa using this
  have h1 := jbar_comm_kbar D S hz' hk
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc z * (tb * k * tb⁻¹) = tb * ((tb⁻¹ * z * tb) * k) * tb⁻¹ := by group
    _ = tb * (k * (tb⁻¹ * z * tb)) * tb⁻¹ := by rw [h1]
    _ = tb * k * tb⁻¹ * z := by group

omit [Finite Γ] in
theorem comm_kbar_conj (D : SwapData H T K tb) {a b : ↥H ⧸ CFSG.pCore 2 ↥H}
    (ha : a ∈ kbar H K) (hb : b ∈ (kbar H K).map (MulAut.conj tb).toMonoidHom) :
    a * b = b * a := by
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp D.comm ha
  exact (Subgroup.mem_centralizer_iff.mp this b hb).symm

theorem dbar_normal (D : SwapData H T K tb) (S : Setting H T M L K) :
    (kbar H K ⊔ (kbar H K).map (MulAut.conj tb).toMonoidHom).Normal := by
  set Db := kbar H K ⊔ (kbar H K).map (MulAut.conj tb).toMonoidHom
  have hK : kbar H K ≤ Subgroup.normalizer (Db : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (kbar H K).map (MulAut.conj k : (↥H ⧸ CFSG.pCore 2 ↥H) →* _) = kbar H K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk)
    have h2 : ((kbar H K).map (MulAut.conj tb).toMonoidHom).map
        (MulAut.conj k : (↥H ⧸ CFSG.pCore 2 ↥H) →* _) =
        (kbar H K).map (MulAut.conj tb).toMonoidHom := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have := comm_kbar_conj D hk hx
        have e : (MulAut.conj k : (↥H ⧸ CFSG.pCore 2 ↥H) →* _) x = x := by
          show k * x * k⁻¹ = x
          rw [this, mul_inv_cancel_right]
        rw [e]
        exact hx
      · intro hy
        refine ⟨y, hy, ?_⟩
        have := comm_kbar_conj D hk hy
        show k * y * k⁻¹ = y
        rw [this, mul_inv_cancel_right]
    rw [Subgroup.map_sup, h1, h2]
  have htop : kbar H K ⊔ (T.subgroupOf H).map (barMap H) ≤
      Subgroup.normalizer (Db : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := sup_le hK D.norm
  rw [S.kbar_sup_tbar] at htop
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)

theorem jbar_eq_bot (D : SwapData H T K tb)
    (S : Setting H T M L K) : jbar M H = ⊥ := by
  set Db := kbar H K ⊔ (kbar H K).map (MulAut.conj tb).toMonoidHom with hDb
  have := dbar_normal D S
  have hDT : Db ⊔ (T.subgroupOf H).map (barMap H) = ⊤ := by
    rw [eq_top_iff, ← S.kbar_sup_tbar]
    exact sup_le_sup_right le_sup_left _
  have hq := isPGroup_quotient_of_sup S.tbar_isPGroup hDT
  have hJD : ∀ z ∈ jbar M H, z ∈ Db → z = 1 := by
    intro z hz hzD
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => comm_kbar_conj D ha hb) hzD
    have ha1 : a = 1 := by
      refine eq_one_of_comm D S ha fun k hk => ?_
      have h1 := jbar_comm_kbar D S hz hk
      have h2 := (comm_kbar_conj D hk hb).symm
      calc a * k = a * k * b * b⁻¹ := by group
        _ = a * (b * k) * b⁻¹ := by rw [mul_assoc a k b, ← h2]
        _ = k * (a * b) * b⁻¹ := by rw [← mul_assoc, h1]
        _ = k * a := by group
    subst ha1
    rw [one_mul] at hz ⊢
    obtain ⟨c, hc, rfl⟩ := hb
    have hc1 : c = 1 := by
      refine eq_one_of_comm D S hc fun k hk => ?_
      have h1 := jbar_comm_conj D S hz (⟨k, hk, rfl⟩ :
        (MulAut.conj tb).toMonoidHom k ∈ (kbar H K).map (MulAut.conj tb).toMonoidHom)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      have h2 : tb * (c * k) * tb⁻¹ = tb * (k * c) * tb⁻¹ := by
        calc tb * (c * k) * tb⁻¹ = tb * c * tb⁻¹ * (tb * k * tb⁻¹) := by group
          _ = tb * k * tb⁻¹ * (tb * c * tb⁻¹) := h1
          _ = tb * (k * c) * tb⁻¹ := by group
      have := congrArg (fun w => tb⁻¹ * w * tb) h2
      simpa [mul_assoc] using this
    subst hc1
    simp
  have hJ2 : IsPGroup 2 (jbar M H) := by
    intro z
    obtain ⟨k, hk⟩ := hq (QuotientGroup.mk (z : ↥H ⧸ CFSG.pCore 2 ↥H))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    refine ⟨k, Subtype.ext ?_⟩
    exact hJD _ ((jbar M H).pow_mem z.2 _) hk
  exact eq_bot_of_isPGroup_two_of_dvd hJ2 le_rfl S.card_jbar_odd

theorem kerIn_eq (D : SwapData H T K tb) (S : Setting H T M L K) :
    kerIn M H = pCoreOf 2 H := by
  have hJ := jbar_eq_bot D S
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H := S.minPar.kerIn_le_H hx
    have h1 : barMap H ⟨x, hxH⟩ ∈ jbar M H := ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [hJ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hQ : pCoreOf 2 H = (CFSG.pCore 2 ↥H).map H.subtype := rfl
    rw [hQ]
    exact ⟨_, h1, rfl⟩
  · exact S.minPar.pCoreOf_le_kerIn

theorem psi_injective (D : SwapData H T K tb)
    (S : Setting H T M L K) : Function.Injective S.psi := by
  rw [← MonoidHom.ker_eq_bot_iff, S.ker_psi]
  exact jbar_eq_bot D S

end SwapData

end Setting

end E2P

end CFSG.Quasithin
