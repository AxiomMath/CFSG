module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eLie

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr burnsideF48t_u52eF

section Class


theorem burnsideF48t_u52e_K'_le_Xh' : burnsideF48t_u52K' ≤ burnsideF48t_u52Xh :=
  burnsideF48t_u52_K'_le_X.trans burnsideF48t_u52e_X_le

theorem burnsideF48t_u52e_B'_le_X : burnsideF48t_u52B' ≤ burnsideF48t_u52X := by
  rw [burnsideF48t_u52_B'_eq]
  exact inf_le_left.trans burnsideF48t_u52_P1'_le_X

theorem burnsideF48t_u52e_B'_le_Xh : burnsideF48t_u52B' ≤ burnsideF48t_u52Xh :=
  burnsideF48t_u52e_B'_le_X.trans burnsideF48t_u52e_X_le

theorem burnsideF48t_u52e_card_eB : Nat.card ↥burnsideF48t_u52eB = 9216 := by
  rw [burnsideF48t_u52eB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_u52e_B'_le_Xh).toEquiv, burnsideF48t_u52_card_B']

theorem burnsideF48t_u52e_card_eK0 : Nat.card ↥burnsideF48t_u52eK0 = 9 := by
  rw [burnsideF48t_u52eK0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_u52e_K'_le_Xh').toEquiv, burnsideF48t_u52_card_K']

theorem burnsideF48t_u52e_K0_le_Kh {j : ℕ} (hj : j < 4) :
    burnsideF48t_u52eK0 ≤ burnsideF48t_u52eKh j :=
  fun _ hz => burnsideF48t_u52e_K'_le hj hz

theorem burnsideF48t_u52e_mem_B {z : ↥burnsideF48t_u52Xh}
    (hz : z ∈ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2) (hzX : z ∈ burnsideF48t_u52eXs) :
    z ∈ burnsideF48t_u52eB := by
  have hzX' : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X := hzX
  show (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B'
  rw [burnsideF48t_u52_B'_eq, burnsideF48t_u52_P1'_eq, burnsideF48t_u52_P2'_eq]
  exact ⟨⟨hzX', MulAction.mem_stabilizer_iff.2 ((burnsideF48t_u52e_mem_P1 z).1 hz.1)⟩,
    ⟨hzX', MulAction.mem_stabilizer_iff.2 ((burnsideF48t_u52e_mem_P2 z).1 hz.2)⟩⟩

theorem burnsideF48t_u52e_sylowB {H : Subgroup ↥burnsideF48t_u52Xh} (hH : H ≤ burnsideF48t_u52eB)
    (hc : Nat.card ↥H = 9) : ChF.IsSylowOf 3 H burnsideF48t_u52eB := by
  refine ⟨hH, IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := H) (K := burnsideF48t_u52eB)
  rw [inf_eq_left.2 hH, hc, burnsideF48t_u52e_card_eB] at h
  have h2 : H.relIndex burnsideF48t_u52eB = 1024 := by omega
  rw [h2]
  decide

theorem burnsideF48t_u52e_classify {K'' : Subgroup ↥burnsideF48t_u52Xh}
    (hle : K'' ≤ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2) (hQ : burnsideF48t_u52eQ K'') :
    ∃ t ∈ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2, ∃ j < 4,
      ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48t_u52eKh j := by
  obtain ⟨hcard, hS⟩ := hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K'') 3 (n := 2)
    (by rw [hcard]; norm_num)
  set T : Subgroup ↥burnsideF48t_u52Xh := H.map K''.subtype with hTdef
  have hT : Nat.card ↥T = 9 := by
    rw [hTdef, Subgroup.card_map_of_injective K''.subtype_injective, hH]
    norm_num
  have hTK : T ≤ K'' := Subgroup.map_subtype_le H
  have hTX : ∀ z ∈ T, z ∈ burnsideF48t_u52eXs := by
    intro z hz
    have h9 : z ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := ↥T) (x := ⟨z, hz⟩)
      rw [hT] at h
      have := congrArg Subtype.val h
      simpa using this
    by_contra hzX
    have hzz : z * z ∈ burnsideF48t_u52eXs :=
      (Subgroup.mul_mem_iff_of_index_two burnsideF48t_u52e_index).2 Iff.rfl
    apply hzX
    have e : (z * z) ^ 4 * z = z ^ 9 := by
      rw [← sq, ← pow_mul, ← pow_succ]
    have hz' : z = ((z * z) ^ 4)⁻¹ := by
      have := congrArg (fun w => ((z * z) ^ 4)⁻¹ * w) e
      simp only [inv_mul_cancel_left, h9, mul_one] at this
      exact this
    rw [hz']
    exact burnsideF48t_u52eXs.inv_mem (burnsideF48t_u52eXs.pow_mem hzz 4)
  have hTB : T ≤ burnsideF48t_u52eB := fun z hz => burnsideF48t_u52e_mem_B (hle (hTK hz)) (hTX z hz)
  have hK0B : burnsideF48t_u52eK0 ≤ burnsideF48t_u52eB := fun z hz => burnsideF48t_u52_K'_le_B' hz
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj (burnsideF48t_u52e_sylowB hTB hT)
    (burnsideF48t_u52e_sylowB hK0B burnsideF48t_u52e_card_eK0)
  set c : ↥burnsideF48t_u52Xh := (g : ↥burnsideF48t_u52Xh)⁻¹ with hcdef
  have hcB : c ∈ burnsideF48t_u52eB := burnsideF48t_u52eB.inv_mem g.2
  have hcP : c ∈ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2 := burnsideF48t_u52e_B_le hcB
  set K3 : Subgroup ↥burnsideF48t_u52Xh := K''.map (MulAut.conj c).toMonoidHom with hK3def
  have hmemK3 : ∀ w, w ∈ K3 ↔ c⁻¹ * w * c ∈ K'' := by
    intro w
    constructor
    · rintro ⟨w', hw', rfl⟩
      have e : c⁻¹ * ((MulAut.conj c).toMonoidHom w') * c = w' := by
        show c⁻¹ * (c * w' * c⁻¹) * c = w'
        group
      rw [e]
      exact hw'
    · intro hw
      refine ⟨_, hw, ?_⟩
      show c * (c⁻¹ * w * c) * c⁻¹ = w
      group
  have hK0K3 : burnsideF48t_u52eK0 ≤ K3 := by
    intro k hk
    rw [hmemK3]
    have h1 : (g : ↥burnsideF48t_u52Xh) * k * (g : ↥burnsideF48t_u52Xh)⁻¹ ∈ T := by
      rw [hg]
      exact ⟨k, hk, rfl⟩
    have e : c⁻¹ * k * c = (g : ↥burnsideF48t_u52Xh) * k * (g : ↥burnsideF48t_u52Xh)⁻¹ := by
      rw [hcdef, inv_inv]
    rw [e]
    exact hTK h1
  have hcK3 : Nat.card ↥K3 = 18 := by
    rw [hK3def, Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard]
  have hK3P : K3 ≤ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2 := by
    intro w hw
    have h1 := hle ((hmemK3 w).1 hw)
    have e : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
    rw [e]
    exact (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).mul_mem
      ((burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).mul_mem hcP h1)
      ((burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).inv_mem hcP)
  obtain ⟨t, htK3, ht0⟩ : ∃ t ∈ K3, t ∉ burnsideF48t_u52eK0 := by
    by_contra hne
    have hle3 : K3 ≤ burnsideF48t_u52eK0 := fun w hw => by
      by_contra h
      exact hne ⟨w, hw, h⟩
    have := Subgroup.card_le_of_le hle3
    rw [hcK3, burnsideF48t_u52e_card_eK0] at this
    omega
  have hidx : (burnsideF48t_u52eK0.subgroupOf K3).index = 2 := by
    have h1 := Subgroup.card_mul_index (burnsideF48t_u52eK0.subgroupOf K3)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0K3).toEquiv, burnsideF48t_u52e_card_eK0,
      hcK3] at h1
    omega
  have htsq : t * t ∈ burnsideF48t_u52eK0 :=
    (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t, htK3⟩) (b := ⟨t, htK3⟩)).2 Iff.rfl
  have htn : ∀ k ∈ burnsideF48t_u52eK0, t * k * t⁻¹ ∈ burnsideF48t_u52eK0 := by
    intro k hk
    exact (Subgroup.normal_of_index_eq_two hidx).conj_mem ⟨k, hK0K3 hk⟩ hk ⟨t, htK3⟩
  have hmul : ∀ w ∈ K3, w ∉ burnsideF48t_u52eK0 → t⁻¹ * w ∈ burnsideF48t_u52eK0 := by
    intro w hw hw0
    have hni : (⟨t, htK3⟩ : ↥K3)⁻¹ ∉ burnsideF48t_u52eK0.subgroupOf K3 := fun h => ht0 (by
      have := (burnsideF48t_u52eK0.subgroupOf K3).inv_mem h
      rw [inv_inv] at this
      exact this)
    exact (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, htK3⟩ : ↥K3)⁻¹)
      (b := ⟨w, hw⟩)).2 (iff_of_false hni hw0)
  have htP := hK3P htK3
  have hpn : ∀ k ∈ burnsideF48t_u52K', (t : Equiv.Perm (Fin 462)) * k * (t : Equiv.Perm (Fin 462))⁻¹ ∈
      burnsideF48t_u52K' := fun k hk => htn ⟨k, burnsideF48t_u52e_K'_le_Xh' hk⟩ hk
  have hpsq : (t : Equiv.Perm (Fin 462)) * t ∈ burnsideF48t_u52K' := htsq
  have hpnot : (t : Equiv.Perm (Fin 462)) ∉ burnsideF48t_u52K' := ht0
  by_cases htX : t ∈ burnsideF48t_u52eXs
  ·
    exfalso
    have htB : (t : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B' := burnsideF48t_u52e_mem_B htP htX
    obtain ⟨k, hk, hkS, hk1⟩ := burnsideF48t_u52e_testB htB hpn hpsq hpnot
    have hkX : k ∈ burnsideF48t_u52Xh := burnsideF48t_u52e_K'_le_Xh' hk
    have hw := (hmemK3 _).1 (K3.mul_mem htK3 (hK0K3 (show (⟨k, hkX⟩ : ↥burnsideF48t_u52Xh) ∈
      burnsideF48t_u52eK0 from hk)))
    have hcn := burnsideF48t_u52_B'_le_normalizer (burnsideF48t_u52B'.inv_mem hcB)
    have hS0 : ((c⁻¹ * (t * ⟨k, hkX⟩) * c : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) ∈
        burnsideF48t_u52S0' := by
      have h1 := (Subgroup.mem_normalizer_iff.1 hcn ((t : Equiv.Perm (Fin 462)) * k)).1 hkS
      rw [inv_inv] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] using h1
    have h1 := hS _ hw hS0
    apply hk1
    have e : t * ⟨k, hkX⟩ = c * (c⁻¹ * (t * ⟨k, hkX⟩) * c) * c⁻¹ := by group
    rw [h1, mul_one, mul_inv_cancel] at e
    exact congrArg Subtype.val e
  ·
    have hfX : burnsideF48t_u52f * (t : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X :=
      ((burnsideF48t_u52e_mem_Xh t).1 t.2).resolve_left htX
    have hβB : burnsideF48t_u52f * (t : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B' := by
      rw [burnsideF48t_u52_B'_eq, burnsideF48t_u52_P1'_eq, burnsideF48t_u52_P2'_eq]
      have h0 := (burnsideF48t_u52e_mem_P1 t).1 htP.1
      have h1 := (burnsideF48t_u52e_mem_P2 t).1 htP.2
      refine ⟨⟨hfX, MulAction.mem_stabilizer_iff.2 ?_⟩, ⟨hfX, MulAction.mem_stabilizer_iff.2 ?_⟩⟩
      · rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, h0, burnsideF48t_u52e_f_pA]
      · rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, h1, burnsideF48t_u52e_f_pB]
    have hft := burnsideF48t_u52e_ffx (t : Equiv.Perm (Fin 462))
    obtain ⟨j, hj, htj⟩ := burnsideF48t_u52e_testF hβB (by rw [hft]; exact hpn)
      (by rw [hft]; exact hpsq)
    rw [hft] at htj
    have htj' : t ∈ burnsideF48t_u52eKh j := htj
    have hK3j : K3 ≤ burnsideF48t_u52eKh j := by
      intro w hw
      by_cases hw0 : w ∈ burnsideF48t_u52eK0
      · exact burnsideF48t_u52e_K0_le_Kh hj hw0
      · have h1 := hmul w hw hw0
        have e : w = t * (t⁻¹ * w) := by group
        rw [e]
        exact (burnsideF48t_u52eKh j).mul_mem htj' (burnsideF48t_u52e_K0_le_Kh hj h1)
    have hEq : K3 = burnsideF48t_u52eKh j :=
      Subgroup.eq_of_le_of_card_ge hK3j (by rw [hcK3, burnsideF48t_u52e_card_Kh hj])
    refine ⟨c, hcP, j, hj, fun z => ?_⟩
    rw [← hEq, hmemK3]
    have e : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    rw [e]

theorem burnsideF48t_u52e_core :
    burnsideF48t_ECore burnsideF48t_u52eP1 burnsideF48t_u52eP2 4 burnsideF48t_u52eQ := by
  intro Y _ f₁ f₂ h12 hgen hinj hcard K'' hK''le hQ x y hx hy hx2 hxK hxx hy1 hyK hyy hrel
  obtain ⟨t, ht, j, hj, hiff⟩ := burnsideF48t_u52e_classify hK''le hQ
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · obtain ⟨hx', hx2', hxK', hxx'⟩ := burnsideF48t_conj_props ht hiff hx hx2 hxK hxx
    exact (burnsideF48t_u52e_nox (Or.inl rfl) hx' hx2' hxK' hxx').elim
  · obtain ⟨hx', hx2', hxK', hxx'⟩ := burnsideF48t_conj_props ht hiff hx hx2 hxK hxx
    exact (burnsideF48t_u52e_nox (Or.inr rfl) hx' hx2' hxK' hxx').elim
  · exact burnsideF48t_core_conj burnsideF48t_u52e_facts f₁ f₂ h12 hgen hinj hcard hK''le ht hiff
      hx hy hx2 hxK hxx hy1 hyK hyy hrel
  · obtain ⟨hy', hy1', hyK', hyy'⟩ := burnsideF48t_conj_props (P1 := burnsideF48t_u52eP2)
      (P2 := burnsideF48t_u52eP1) ⟨ht.2, ht.1⟩ hiff hy hy1 hyK hyy
    exact (burnsideF48t_u52e_noy hy' hy1' hyK' hyy').elim

theorem burnsideF48t_u52e_card_Bh :
    Nat.card ↥(burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2) = 18432 := by
  have hfP : (⟨burnsideF48t_u52f, burnsideF48t_u52e_f_mem⟩ : ↥burnsideF48t_u52Xh) ∈
      burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2 :=
    ⟨Subgroup.subset_closure ⟨4, show (4 : Fin 5) ≠ 3 by decide, rfl⟩,
      Subgroup.subset_closure ⟨4, show (4 : Fin 5) ≠ 2 by decide, rfl⟩⟩
  have hBX : ∀ z : ↥burnsideF48t_u52Xh, z ∈ burnsideF48t_u52eB → z ∈ burnsideF48t_u52eXs :=
    fun z hz => burnsideF48t_u52e_B'_le_X hz
  have hidx : (burnsideF48t_u52eB.subgroupOf (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨_, hfP⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : ↥burnsideF48t_u52Xh) ∈ burnsideF48t_u52eXs
    · refine Or.inr ⟨burnsideF48t_u52e_mem_B b.2 hb, fun h => ?_⟩
      have h1 := hBX _ h
      have h2 := burnsideF48t_u52eXs.mul_mem (burnsideF48t_u52eXs.inv_mem hb) h1
      rw [inv_mul_cancel_left] at h2
      exact burnsideF48t_u52e_f_not_mem h2
    · refine Or.inl ⟨burnsideF48t_u52e_mem_B
        ((burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).mul_mem b.2 hfP)
        ((Subgroup.mul_mem_iff_of_index_two burnsideF48t_u52e_index).2
          (iff_of_false hb fun h => burnsideF48t_u52e_f_not_mem h)), fun h => hb (hBX _ h)⟩
  have h1 := Subgroup.card_mul_index (burnsideF48t_u52eB.subgroupOf
    (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe burnsideF48t_u52e_B_le).toEquiv,
    burnsideF48t_u52e_card_eB, hidx] at h1
  omega

end Class

end CFSG.ASVolI
