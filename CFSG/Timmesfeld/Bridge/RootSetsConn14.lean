module

public import CFSG.Timmesfeld.Bridge.OddTranspNPC
public import CFSG.Timmesfeld.Bridge.RootSetsConn8

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem orderOf_abx (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Odd (orderOf (c * x)) ∧ 1 < orderOf (c * x) ∧
      orderOf (a * b * x) = 2 * orderOf (c * x) ∧ (a * b * x) ^ orderOf (c * x) = z := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hcx : ¬ Reach D c x := fun hr => h.hax (reach_trans h.hac hr)
  obtain ⟨hnc, hodd⟩ := opposite_of_not_reach hD h.hc h.hx hcx
  have hz2 := h.z_mul_self hC
  have hz1 := h.hz1
  have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two, hz2]) hz1
  have hcz : Commute c z := h.commute_c
  have hxz : Commute x z := h.hxz
  have habx : a * b * x = c * x * z := by
    have hab : a * b = c * z := by
      rw [h.hz, ← mul_assoc, hD.mul_self_eq_one h.hc, one_mul]
    rw [hab, mul_assoc, hxz.symm.eq, ← mul_assoc]
  have hord := orderOf_mul_eq_two_mul_of_odd (hcz.mul_left hxz) hodd hoz
  refine ⟨hodd, ?_, by rw [habx, hord], ?_⟩
  · by_contra h1
    have h1' : orderOf (c * x) = 1 := by
      have := orderOf_pos (c * x)
      omega
    rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq h.hx] at h1'
    exact hnc (by rw [h1'])
  · rw [habx, (hcz.mul_left hxz).mul_pow, pow_orderOf_eq_one, one_mul]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]

theorem exists_thirdKindHyp (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∃ SK : Sylow 2 (lsub D x P), (∀ y : lsub D x P, (y : G) ∈ P → y ∈ SK) ∧
      ∃ a' b' c' : lsub D x P, ∃ n : ℕ,
        ThirdKindHyp (lsub D x P) (lclass D x P) SK a' b' c' n := by
  classical
  have := hC.setting.finite
  set X := lsub D x P with hX
  have hS := h.setup hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SK, hSK⟩ := (h.hP2.comap_subtype (K := X)).exists_le_sylow
  have hmemS : ∀ y : X, (y : G) ∈ P → y ∈ SK := fun y hy => hSK hy
  set aX : X := ⟨a, mem_lsub_of_mem h.ha h.haP⟩
  set bX : X := ⟨b, mem_lsub_of_mem h.hb h.hbP⟩
  set xX : X := ⟨x, mem_lsub_x⟩
  obtain ⟨hodd, hn1, hord, hpow⟩ := h.orderOf_abx hC
  have hzP : z ∈ P := by
    rw [h.hz]
    exact P.mul_mem h.hcP (P.mul_mem h.haP h.hbP)
  have hax : ¬ Commute a x := fun hc =>
    h.hax (reach_of_commute h.ha h.hx hc)
  have hbx : ¬ Commute b x := fun hc =>
    h.hax (reach_trans (h.reach_of_mem hC h.hb h.hbP) (reach_of_commute h.hb h.hx hc))
  refine ⟨SK, hmemS, aX, xX, bX, orderOf (c * x), hS, ⟨h.mem_lclass hC h.ha h.haP,
    h.mem_lclass hC h.hb h.hbP, mem_classIn_self _ x, fun h' => h.hab (congrArg Subtype.val h'),
    Subtype.ext h.hcab.eq, fun h' => hax (congrArg Subtype.val h'.eq),
    fun h' => hbx (congrArg Subtype.val h'.eq)⟩, hodd, hn1, ?_, hmemS aX h.haP, hmemS bX h.hbP,
    ?_, ?_, OddTransp.noPerfectCentralExt_of_isBenderGroup_quotient hS
      (h.isBenderGroup_pCore hB hC)⟩
  · rw [← Subgroup.orderOf_coe]
    exact hord
  · apply hmemS
    have : ((aX * bX * xX) ^ orderOf (c * x) : X) = (a * b * x) ^ orderOf (c * x) := rfl
    rw [this, hpow]
    exact hzP
  · rw [eq_top_iff]
    have h1 := closure_preimage_subtype_eq_top (N := X) (S := insert x {y | y ∈ D ∧ y ∈ P})
      (fun w hw => Subgroup.subset_closure hw) rfl
    rw [← h1, Subgroup.closure_le]
    rintro w (hw | ⟨hwD, hwP⟩)
    · have hw' : w = xX := Subtype.ext hw
      rw [hw']
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _
        ⟨h.mem_classIn hC hwD hwP, hmemS w hwP⟩)

theorem mem_of_mem_isPGroup (hC : ConnCex D) (h : Step6 D a b c x z P)
    {SK : Subgroup (lsub D x P)} (hSK : IsPGroup 2 SK)
    (hmemS : ∀ y : lsub D x P, (y : G) ∈ P → y ∈ SK) {y : lsub D x P} (hy : (y : G) ∈ D)
    (hyS : y ∈ SK) : (y : G) ∈ P :=
  h.mem_of_isPGroup hC (hSK.map (lsub D x P).subtype)
    (fun l hl hlP => ⟨⟨l, mem_lsub_of_mem hl hlP⟩, hmemS _ hlP, rfl⟩) hy
    (Subgroup.mem_centralizer_singleton_iff.1 (h.lsub_le_centralizer y.2)) ⟨y, hyS, rfl⟩

theorem step6ThreeProduct (hB : OddTranspBender) (hT : OddTranspThirdKind) (hC : ConnCex D)
    (h : Step6 D a b c x z P) : Step6ThreeProduct D x P := by
  classical
  have := hC.setting.finite
  have hD := hC.setting.root
  set X := lsub D x P with hX
  obtain ⟨SK, hmemS, a', b', c', n, hK⟩ := h.exists_thirdKindHyp hB hC
  obtain ⟨-, hmain⟩ := hT _ _ _ _ _ _ _ hK
  intro d hd hdP e he heP f hf hfP hq
  set dX : X := ⟨d, mem_lsub_of_mem hd hdP⟩
  set eX : X := ⟨e, mem_lsub_of_mem he heP⟩
  set fX : X := ⟨f, mem_lsub_of_mem hf hfP⟩
  have hq' : fX * dX⁻¹ ∈ CFSG.pCore 2 X := by
    obtain ⟨m, hm, hme⟩ := hq
    have hm' : m = dX * fX := Subtype.ext hme
    have : fX * dX⁻¹ = m⁻¹ := by
      rw [hm', mul_inv_rev]
      congr 1
      exact (Subtype.ext (hD.inv_eq hf)).symm
    rw [this]
    exact (CFSG.pCore 2 X).inv_mem hm
  obtain ⟨⟨u, w⟩, ⟨huD, hw, hdec⟩, -⟩ := hmain dX ⟨h.mem_lclass hC hd hdP, hmemS dX hdP⟩ eX
    ⟨h.mem_lclass hC he heP, hmemS eX heP⟩ fX (h.mem_lclass hC hf hfP) hq'
  have huD' : (u : G) ∈ D := classIn_subset_of_normal hC.setting.normal _ h.hx huD
  have huS : u ∈ SK := by
    have hwS : w ∈ SK := CFSG.pCore_isPGroup.le_sylow_of_normal SK hw.1
    have : u = dX * eX * fX * w⁻¹ := by rw [hdec]; group
    rw [this]
    exact SK.mul_mem (SK.mul_mem (SK.mul_mem (hmemS dX hdP) (hmemS eX heP)) (hmemS fX hfP))
      (SK.inv_mem hwS)
  have huP : (u : G) ∈ P := h.mem_of_mem_isPGroup hC SK.isPGroup' hmemS huD' huS
  exact ⟨u, huD', huP, w, ⟨w, ⟨hw.2, hw.1⟩, rfl⟩, congrArg Subtype.val hdec⟩

end Step6

theorem step6ThreeProductHyp (hB : OddTranspBender) (hT : OddTranspThirdKind) :
    Step6ThreeProductHyp := fun _ _ _ _ _ _ _ _ _ hC h => h.step6ThreeProduct hB hT hC

end CFSG.Timmesfeld.Bridge
