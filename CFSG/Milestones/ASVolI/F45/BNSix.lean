module

public import CFSG.Milestones.ASVolI.F45.BN

public noncomputable section

namespace CFSG.ASVolI

open CFSG.GH74.BNPair CFSG.Open CFSG.Quasithin.H13.F431.BN CFSG.ASVolI.ChF
open scoped Pointwise

variable {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem burnsideF45_bn_P_inf (i : Bool) : P D i ⊓ P D (!i) = D.B := by
  cases i
  · show P D false ⊓ P D true = D.B
    rw [inf_comm]; exact P₁_inf_P₂ D
  · exact P₁_inf_P₂ D

theorem burnsideF45_bn_stab_inf (i : Bool) :
    MulAction.stabilizer X (v D i) ⊓ MulAction.stabilizer X (v D (!i)) = D.B := by
  rw [stabilizer_v_eq, stabilizer_v_eq]
  exact burnsideF45_bn_P_inf D i

theorem burnsideF45_bn_nbr_rep (i : Bool) {w : V D} (hw : (Γ D).Adj (v D i) w)
    (hne : w ≠ v D (!i)) :
    ∃ u ∈ D.UwMinus (D.lift (gen D.w₁ D.w₂ i)), w = vt D (!i) (mi D i * u) := by
  obtain ⟨z, hz, rfl⟩ := exists_nbr D i hw
  rcases (mem_P_iff D).1 hz with hB | hd
  · exfalso
    apply hne
    rw [v_eq_vt, vt_eq_vt_iff, inv_one, mul_one]
    exact D.rank2.B_le_pgen _ hB
  · obtain ⟨b, hb, u, hu, rfl⟩ := (D.mem_dc_iff_coord _ (D.lift_mk _)).1 hd
    refine ⟨u, hu, ?_⟩
    rw [vt_eq_vt_iff]
    have e : b * (D.lift (gen D.w₁ D.w₂ i) : X) * u * (mi D i * u)⁻¹ = b := by
      simp [mi, mul_assoc]
    rw [e]
    exact D.rank2.B_le_pgen _ hb

theorem burnsideF45_bn_vt_inj (i : Bool) {u u' : X}
    (hu : u ∈ D.UwMinus (D.lift (gen D.w₁ D.w₂ i)))
    (hu' : u' ∈ D.UwMinus (D.lift (gen D.w₁ D.w₂ i)))
    (h : vt D (!i) (mi D i * u) = vt D (!i) (mi D i * u')) : u = u' := by
  set m := D.lift (gen D.w₁ D.w₂ i) with hm
  have hx : u * u'⁻¹ ∈ D.UwMinusSub m :=
    (D.UwMinusSub m).mul_mem hu ((D.UwMinusSub m).inv_mem hu')
  have h1 : mi D i * u * (mi D i * u')⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ (!i) :=
    (vt_eq_vt_iff (!i) _ _).1 h
  have e : mi D i * u * (mi D i * u')⁻¹ = (m : X) * (u * u'⁻¹) * (m : X)⁻¹ := by
    simp [mi, hm, mul_assoc]
  rw [e] at h1
  have h2 : (m : X) * (u * u'⁻¹) * (m : X)⁻¹ ∈ P D i := by
    have hmP : (m : X) ∈ P D i := mi_mem_P D i
    have hxP : u * u'⁻¹ ∈ P D i := B_le_P D i (D.U_le_B hx.1)
    exact (P D i).mul_mem ((P D i).mul_mem hmP hxP) ((P D i).inv_mem hmP)
  have hB : (m : X) * (u * u'⁻¹) * (m : X)⁻¹ ∈ D.B := by
    have h3 : (m : X) * (u * u'⁻¹) * (m : X)⁻¹ ∈ P D i ⊓ P D (!i) := ⟨h2, h1⟩
    rwa [burnsideF45_bn_P_inf D i] at h3
  have h4 : (m : X) * (u * u'⁻¹) * (m : X)⁻¹ ∈ D.Vm := (D.mem_Vm_iff).2 hx.2
  have h5 := D.eq_one_of_mem_U_Vm hB h4
  have h6 : u * u'⁻¹ = 1 := by
    have := congrArg (fun z => (m : X)⁻¹ * z * (m : X)) h5
    simpa [mul_assoc] using this
  exact mul_inv_eq_one.mp h6

variable [Finite X] {p : ℕ}

theorem burnsideF45_bn_mem_U_of_pElement (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) {x : X}
    (hx : x ∈ D.B) {k : ℕ} (hk : orderOf x = p ^ k) : x ∈ D.U := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p X := hU.2.1.toSylow (burnsideF45_bn_not_dvd_index D hU)
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (D.U : Set X) := by
    rw [Subgroup.zpowers_le]
    exact B_le_normalizer_U D hx
  have hsup : IsPGroup p (D.U ⊔ Subgroup.zpowers x : Subgroup X) :=
    hU.2.1.to_sup_of_normal_left' hxp hnorm
  have h := S.is_maximal' hsup (le_sup_left : D.U ≤ D.U ⊔ Subgroup.zpowers x)
  have hmem : x ∈ D.U ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [h] at hmem
  exact hmem

theorem burnsideF45_bn_oPPrime_le_U (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) :
    oPPrime p D.B ≤ D.U := by
  unfold oPPrime
  rw [Subgroup.closure_le]
  rintro x ⟨hx, k, hk⟩
  exact burnsideF45_bn_mem_U_of_pElement D hp hU hx hk

theorem burnsideF45_bn_U_le_oPPrime (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) :
    D.U ≤ oPPrime p D.B := by
  intro x hx
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hU.2.1 ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
  exact Subgroup.subset_closure ⟨D.U_le_B hx, j, hj⟩

theorem burnsideF45_bn_six_trans (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool)
    {w₁ w₂ : V D} (h₁ : (Γ D).Adj (v D i) w₁) (h₁' : w₁ ≠ v D (!i))
    (h₂ : (Γ D).Adj (v D i) w₂) (h₂' : w₂ ≠ v D (!i)) :
    ∃ g ∈ oPPrime p (MulAction.stabilizer X (v D i) ⊓ MulAction.stabilizer X (v D (!i))),
      g • w₁ = w₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := burnsideF45_bn_nbr_rep D i h₁ h₁'
  obtain ⟨u₂, hu₂, rfl⟩ := burnsideF45_bn_nbr_rep D i h₂ h₂'
  set m := D.lift (gen D.w₁ D.w₂ i)
  have hg : u₂⁻¹ * u₁ ∈ D.UwMinusSub m :=
    (D.UwMinusSub m).mul_mem ((D.UwMinusSub m).inv_mem hu₂) hu₁
  refine ⟨u₂⁻¹ * u₁, ?_, ?_⟩
  · rw [burnsideF45_bn_stab_inf]
    exact burnsideF45_bn_U_le_oPPrime D hp hU hg.1
  · rw [smul_vt]
    congr 1
    group

theorem burnsideF45_bn_six_free (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool)
    {g : X}
    (hg : g ∈ oPPrime p (MulAction.stabilizer X (v D i) ⊓ MulAction.stabilizer X (v D (!i))))
    {w : V D} (hw : (Γ D).Adj (v D i) w) (hw' : w ≠ v D (!i)) (hgw : g • w = w) :
    g ∈ pCoreOf p (MulAction.stabilizer X (v D i)) := by
  rw [burnsideF45_bn_stab_inf] at hg
  have hgU : g ∈ D.U := burnsideF45_bn_oPPrime_le_U D hp hU hg
  set m := D.lift (gen D.w₁ D.w₂ i) with hm
  obtain ⟨c, hc, a, ha, rfl⟩ := D.U_eq_mul' m g hgU
  obtain ⟨u, hu, rfl⟩ := burnsideF45_bn_nbr_rep D i hw hw'
  have hcQ : c ∈ pCoreOf p (P D i) := by
    rw [burnsideF45_bn_pCore_eq D hp hU i]
    exact hc
  have hadj : (Γ D).Adj (v D i) (a • vt D (!i) (mi D i * u)) := by
    have haP : a • v D i = v D i := by
      rw [← MulAction.mem_stabilizer_iff, stabilizer_v_eq]
      exact B_le_P D i (D.U_le_B ha.1)
    have := (CFSG.Quasithin.GraphAction.adj_smul a (v D i) (vt D (!i) (mi D i * u))).mpr hw
    rwa [haP] at this
  have hfix := burnsideF45_bn_qfix D hp hU i hadj hcQ
  rw [mul_smul, hfix, smul_vt] at hgw
  have hua : u * a⁻¹ ∈ D.UwMinus m :=
    (D.UwMinusSub m).mul_mem hu ((D.UwMinusSub m).inv_mem ha)
  have h1 : u * a⁻¹ = u :=
    burnsideF45_bn_vt_inj D i hua hu (by rw [← hgw]; congr 1; group)
  have ha1 : a = 1 := by
    have := congrArg (fun z => u⁻¹ * z) h1
    simpa using this
  rw [ha1, mul_one, stabilizer_v_eq]
  exact hcQ

end CFSG.ASVolI
