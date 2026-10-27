module

public import CFSG.Quasithin.Background.CommVZ4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinDefs
public import CFSG.Quasithin.EmptyFaithful.S14612GA2

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem exists_mul_inv_apply_ne {K : Type} [CommGroup K] [Finite K]
    (hK : ∀ k : K, k ^ 2 = 1) {g : MulAut K} (hg : g ^ 4 = 1) {κ : K} (hκ : g κ = κ)
    (hcard : 4 ≤ Nat.card (commV (Subgroup.zpowers (g ^ 2)))) :
    ∃ k : K, g k * g⁻¹ k ≠ 1 ∧ g k * g⁻¹ k ≠ κ :=
  CFSG.Quasithin.CommVZ4.exists_mul_inv_apply_ne hK hg hκ hcard

namespace ClsData

variable {Q U Z Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Hs z} {K : Type*} [CommGroup K]
  {β : ↥Hs →* MulAut K} {cls : G → K}

private theorem cls_one (D : ClsData P β cls) : cls 1 = 1 :=
  (D.eq_one 1 U.one_mem).mpr Z.one_mem

private theorem cls_inv (D : ClsData P β cls) {u : G} (hu : u ∈ U) : cls u⁻¹ = (cls u)⁻¹ := by
  have h := D.mul u hu u⁻¹ (U.inv_mem hu)
  rw [mul_inv_cancel, D.cls_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem cls_dcomm (D : ClsData P β cls) (hK : ∀ k : K, k ^ 2 = 1) (r : ↥Hs) {u : G}
    (hu : u ∈ U) :
    ⁅⁅u, (r : G)⁆, (r : G)⁻¹⁆ ∈ U ∧
      cls ⁅⁅u, (r : G)⁆, (r : G)⁻¹⁆ = β r (cls u) * (β r)⁻¹ (cls u) := by
  have hinv : ∀ k : K, k⁻¹ = k := fun k =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hK k)
  have haH : (r : G) ∈ Hs := r.2
  have hy : (r : G) * u⁻¹ * (r : G)⁻¹ ∈ U := P.normU _ haH u⁻¹ (U.inv_mem hu)
  have hx : ⁅u, (r : G)⁆ = u * ((r : G) * u⁻¹ * (r : G)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hxU : ⁅u, (r : G)⁆ ∈ U := hx ▸ U.mul_mem hu hy
  have hclsx : cls ⁅u, (r : G)⁆ = cls u * β r (cls u) := by
    rw [hx, D.mul u hu _ hy, D.conj r u⁻¹ (U.inv_mem hu), D.cls_inv hu, map_inv, hinv]
  have hy' : (r : G)⁻¹ * (⁅u, (r : G)⁆)⁻¹ * (r : G) ∈ U := by
    have := P.normU _ (Hs.inv_mem haH) _ (U.inv_mem hxU)
    simpa using this
  have hw : ⁅⁅u, (r : G)⁆, (r : G)⁻¹⁆ =
      ⁅u, (r : G)⁆ * ((r : G)⁻¹ * (⁅u, (r : G)⁆)⁻¹ * (r : G)) := by
    generalize ⁅u, (r : G)⁆ = x
    simp only [commutatorElement_def]
    group
  refine ⟨hw ▸ U.mul_mem hxU hy', ?_⟩
  have hconj := D.conj r⁻¹ _ (U.inv_mem hxU)
  simp only [Subgroup.coe_inv, inv_inv] at hconj
  rw [hw, D.mul _ hxU _ hy', hconj, D.cls_inv hxU, map_inv, map_inv, hinv, hclsx, map_mul,
    MulAut.inv_apply_self]
  calc cls u * β r (cls u) * ((β r)⁻¹ (cls u) * cls u)
      = (cls u * cls u) * (β r (cls u) * (β r)⁻¹ (cls u)) := by ac_rfl
    _ = β r (cls u) * (β r)⁻¹ (cls u) := by rw [← pow_two, hK, one_mul]

end ClsData

private theorem mem_centralizer_of_commute {Hs V : Subgroup G} {z v r : G}
    (hz : ∀ h ∈ Hs, h * z = z * h) (hr : r ∈ Hs)
    (hV : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z) (hrv : v * r = r * v) :
    r ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hzr : z * r = r * z := (hz r hr).symm
  rcases hV x hx with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hzr
  · exact hrv
  · rw [mul_assoc, hzr, ← mul_assoc, hrv, mul_assoc]

private theorem exists_mul_mem_centralizer {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
    {T V : Subgroup G} (hTH : T ≤ Hs) (hQT : Q ≤ T) (hVU : V ≤ U)
    (hV : ∃ v ∈ V, v ∉ Z ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hTV : ∀ t ∈ T, ∀ x ∈ V, t * x * t⁻¹ ∈ V) {x₀ : G} (hx₀ : x₀ ∈ T) :
    ∃ q ∈ Q, x₀ * q ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨v, hvV, hvZ, hVeq⟩ := hV
  have hvU : v ∈ U := hVU hvV
  have hx₀H : x₀ ∈ Hs := hTH hx₀
  by_cases hc : v * x₀ = x₀ * v
  · exact ⟨1, Q.one_mem, by rw [mul_one]; exact mem_centralizer_of_commute P.z_cent hx₀H hVeq hc⟩
  · have hxz : x₀ * z * x₀⁻¹ = z := by
      rw [P.z_cent x₀ hx₀H]
      group
    have h₁ : x₀ * v * x₀⁻¹ = v * z := by
      rcases hVeq _ (hTV x₀ hx₀ v hvV) with h | h | h | h
      · exfalso
        apply hvZ
        have h' : x₀ * v = x₀ * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h
        rw [mul_left_cancel h']
        exact Z.one_mem
      · exfalso
        apply hvZ
        have h' : x₀ * v = x₀ * z := (mul_inv_eq_iff_eq_mul.mp h).trans (P.z_cent x₀ hx₀H).symm
        rw [mul_left_cancel h']
        exact P.z_mem
      · exact absurd (mul_inv_eq_iff_eq_mul.mp h).symm hc
      · exact h
    obtain ⟨q₀, hq₀, hne⟩ : ∃ q ∈ Q, ⁅v, q⁆ ≠ 1 := by
      by_contra hcon
      refine hvZ (P.ker_right v hvU fun q hq => ?_)
      by_contra hne
      exact hcon ⟨q, hq, hne⟩
    have hzq : ⁅v, q₀⁆ = z := (P.Z_eq _ (P.pair_mem v hvU q₀ hq₀)).resolve_left hne
    have hz2 : z * z = 1 := P.Z_sq P.z_mem
    have hqv : ⁅q₀, v⁆ = z := by
      rw [← commutatorElement_inv, hzq]
      exact inv_eq_of_mul_eq_one_right hz2
    have h₂ : q₀ * v * q₀⁻¹ = z * v := by
      rw [commutatorElement_def, mul_inv_eq_iff_eq_mul] at hqv
      exact hqv
    have hzv : z * v = v * z := (P.z_cent v (P.U_le_H hvU)).symm
    have hr : x₀ * q₀ * v * (x₀ * q₀)⁻¹ = v := by
      calc x₀ * q₀ * v * (x₀ * q₀)⁻¹ = x₀ * (q₀ * v * q₀⁻¹) * x₀⁻¹ := by group
        _ = x₀ * (z * v) * x₀⁻¹ := by rw [h₂]
        _ = (x₀ * z * x₀⁻¹) * (x₀ * v * x₀⁻¹) := by group
        _ = z * (v * z) := by rw [hxz, h₁]
        _ = v := by rw [← mul_assoc, hzv, mul_assoc, hz2, mul_one]
    exact ⟨q₀, hq₀, mem_centralizer_of_commute P.z_cent (hTH (T.mul_mem hx₀ (hQT hq₀))) hVeq
      (mul_inv_eq_iff_eq_mul.mp hr).symm⟩

theorem exists_rS1 {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
    {K : Type} [CommGroup K] [Finite K] {β : ↥Hs →* MulAut K} {cls : G → K}
    (D : ClsData P β cls) {Tb Pb : Subgroup (MulAut K)}
    (hES : CFSG.Quasithin.E9Z4Str β.range Tb Pb)
    (T V : Subgroup G) (hTb : Tb = (T.subgroupOf Hs).map β)
    (hker : ∀ x : ↥Hs, β x = 1 ↔ (x : G) ∈ Q) (hTH : T ≤ Hs) (hQT : Q ≤ T)
    (hVU : V ≤ U) (hZV : Z ≤ V)
    (hV : ∃ v ∈ V, v ∉ Z ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hTV : ∀ t ∈ T, ∀ x ∈ V, t * x * t⁻¹ ∈ V) :
    (∀ x ∈ T, ∀ x' ∈ T, ⁅x, x'⁆ ∈ Q) ∧
      ∃ r ∈ T ⊓ Subgroup.centralizer (V : Set G), ∃ u₀ ∈ U, ⁅⁅u₀, r⁆, r⁻¹⁆ ∉ V := by
  have hmemTb : ∀ x : ↥Hs, (x : G) ∈ T → β x ∈ Tb := fun x hx => by
    rw [hTb]
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hTbmem : ∀ a ∈ Tb, ∃ x : ↥Hs, (x : G) ∈ T ∧ β x = a := fun a ha => by
    rw [hTb] at ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hcyc := hES.cyclic_Tb
  refine ⟨fun x hx x' hx' => ?_, ?_⟩
  · have h1 := hmemTb ⟨x, hTH hx⟩ hx
    have h2 := hmemTb ⟨x', hTH hx'⟩ hx'
    have hc : ⁅β ⟨x, hTH hx⟩, β ⟨x', hTH hx'⟩⁆ = 1 := by
      have := congrArg Subtype.val (mul_comm' (⟨_, h1⟩ : ↥Tb) ⟨_, h2⟩)
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact this
    have : β ⁅(⟨x, hTH hx⟩ : ↥Hs), ⟨x', hTH hx'⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact hc
    exact (hker _).mp this
  · obtain ⟨gg, hgg⟩ := IsCyclic.exists_generator (α := ↥Tb)
    obtain ⟨v, hvV, hvZ, hVeq⟩ := hV
    have hvU : v ∈ U := hVU hvV
    obtain ⟨rH, hrT, hrc, hβr⟩ : ∃ rH : ↥Hs, (rH : G) ∈ T ∧
        (rH : G) ∈ Subgroup.centralizer (V : Set G) ∧ β rH = gg := by
      obtain ⟨x₀, hx₀T, hx₀g⟩ := hTbmem gg gg.2
      obtain ⟨q₀, hq₀Q, hq₀c⟩ :=
        exists_mul_mem_centralizer P hTH hQT hVU ⟨v, hvV, hvZ, hVeq⟩ hTV hx₀T
      refine ⟨x₀ * ⟨q₀, P.Q_le_H hq₀Q⟩, T.mul_mem hx₀T (hQT hq₀Q), hq₀c, ?_⟩
      rw [map_mul, hx₀g, (hker ⟨q₀, P.Q_le_H hq₀Q⟩).mpr hq₀Q, mul_one]
    have hrv : (rH : G) * v * (rH : G)⁻¹ = v := by
      rw [← Subgroup.mem_centralizer_iff.mp hrc v hvV, mul_inv_cancel_right]
    have hκ1 : cls v ≠ 1 := fun h => hvZ ((D.eq_one v hvU).mp h)
    have hgκ : (gg : MulAut K) (cls v) = cls v := by
      have h := D.conj rH v hvU
      rw [hrv, hβr] at h
      exact h.symm
    have hgord : orderOf (gg : MulAut K) = 4 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgg, hES.card_Tb]
    have hg4 : (gg : MulAut K) ^ 4 = 1 := by
      rw [← hgord]
      exact pow_orderOf_eq_one _
    have hg2ord : orderOf ((gg : MulAut K) ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hgord]; norm_num), hgord]
    have hTbX : Tb ≤ β.range := by
      rw [hES.eq]
      exact le_sup_right
    have hrk := hES.rk_commV_involution (hTbX (Tb.pow_mem gg.2 2)) hg2ord
    have hcard : 4 ≤ Nat.card (commV (Subgroup.zpowers ((gg : MulAut K) ^ 2))) := by
      rw [card_eq_two_pow hES.sq, hrk]
      norm_num
    obtain ⟨k₀, hk1, hkκ⟩ := exists_mul_inv_apply_ne hES.sq hg4 hgκ hcard
    obtain ⟨u₀, hu₀U, hu₀⟩ := D.surj k₀
    refine ⟨(rH : G), ⟨hrT, hrc⟩, u₀, hu₀U, fun hw => ?_⟩
    obtain ⟨-, hclsw⟩ := D.cls_dcomm hES.sq rH hu₀U
    rw [hβr, hu₀] at hclsw
    have hzU : z ∈ U := hVU (hZV P.z_mem)
    have hz1 : cls z = 1 := (D.eq_one z hzU).mpr P.z_mem
    rcases hVeq _ hw with h | h | h | h
    · rw [h, D.cls_one] at hclsw
      exact hk1 hclsw.symm
    · rw [h, hz1] at hclsw
      exact hk1 hclsw.symm
    · rw [h] at hclsw
      exact hkκ hclsw.symm
    · rw [h, D.mul v hvU z hzU, hz1, mul_one] at hclsw
      exact hkκ hclsw.symm

end CFSG.Quasithin.NoE9Z4MinGrp
