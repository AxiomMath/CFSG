module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.Sporadic.Schreier.TitsPrim
public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Sporadic.Schreier.Tits

theorem centMaxProp_titsD :
    CentMaxProp ↥titsD := by
  obtain ⟨-, -, -, -, hHeq, hSeq, -, ⟨P, hP⟩, -⟩ := AT_Tits_local_stabilizers_and_normal_cores
  obtain ⟨hz2, hcenterS, hHcent, -⟩ := AT_Tits_local_center_and_centralizer_checks
  have hSD : titsS ≤ titsD := by
    rw [hSeq]
    exact Subgroup.map_subtype_le _
  set S₀ : Subgroup ↥titsD := titsS.subgroupOf titsD with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hP ▸ P.isPGroup'
  have hS₀i : ¬ 2 ∣ S₀.index := hP ▸ P.not_dvd_index
  have hzS : titsZ ∈ titsS := by
    have : titsZ ∈ ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
      rw [hcenterS]
      exact Or.inr rfl
    obtain ⟨y, -, hy⟩ := this
    rw [← hy]
    exact y.2
  set z₀ : ↥titsD := ⟨titsZ, hSD hzS⟩ with hz₀
  have hz₀2 : orderOf z₀ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hcen : centerOf S₀ = Subgroup.zpowers z₀ := by
    ext x
    constructor
    · rintro ⟨hxS, hxc⟩
      have hxS' : (x : Equiv.Perm (Fin 1755)) ∈ titsS := hxS
      have hmem : (x : Equiv.Perm (Fin 1755)) ∈
          ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
        refine ⟨⟨x, hxS'⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro y
        have h1 := Subgroup.mem_centralizer_iff.mp hxc ⟨y, hSD y.2⟩ (show _ ∈ S₀ from y.2)
        have h2 : (y : Equiv.Perm (Fin 1755)) * (x : Equiv.Perm (Fin 1755)) =
          (x : Equiv.Perm (Fin 1755)) * y := congrArg (fun t : ↥titsD => (t : Equiv.Perm (Fin 1755))) h1
        exact Subtype.ext h2
      rw [hcenterS] at hmem
      rcases hmem with h | h
      · have : x = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _
      · have : x = z₀ := Subtype.ext h
        rw [this]
        exact Subgroup.mem_zpowers z₀
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hz₀S : z₀ ∈ S₀ := hzS
      refine ⟨S₀.zpow_mem hz₀S k, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : (y : Equiv.Perm (Fin 1755)) ∈ titsS := hy
      have hcomm : (y : Equiv.Perm (Fin 1755)) * titsZ = titsZ * y := by
        have hmem : titsZ ∈ ((Subgroup.center titsS).map titsS.subtype :
            Set (Equiv.Perm (Fin 1755))) := by
          rw [hcenterS]
          exact Or.inr rfl
        obtain ⟨c, hc, hcz⟩ := hmem
        rw [← hcz]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy'⟩)
      have : y * z₀ = z₀ * y := Subtype.ext hcomm
      exact ((Commute.zpow_right (show Commute y z₀ from this) k).eq)
  have hcoat : IsCoatom (MulAction.stabilizer ↥titsD (0 : Fin 1755)) :=
    have : MulAction.IsPreprimitive titsD (Fin 1755) := CERT_Tits_derived_primitive
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := ↥titsD) (0 : Fin 1755)
  have hle : MulAction.stabilizer ↥titsD (0 : Fin 1755) ≤ Subgroup.centralizer ({z₀} : Set ↥titsD) := by
    intro x hx
    have hx0 : (x : Equiv.Perm (Fin 1755)) 0 = 0 := hx
    have hxH : (x : Equiv.Perm (Fin 1755)) ∈ titsH := by
      rw [hHeq]
      exact ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hHcent hxH)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext this)
  have hne : Subgroup.centralizer ({z₀} : Set ↥titsD) ≠ ⊤ := by
    intro htop
    have hz : z₀ ∈ Subgroup.center ↥titsD := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({z₀} : Set ↥titsD) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [titsD_center, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one] at hz₀2
    omega
  have hmax : IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({z₀} : Set ↥titsD)) := by
    rcases hcoat.le_iff.mp hle with h | h
    · exact absurd h hne
    · rw [h]
      exact ⟨lt_top_iff_ne_top.mpr hcoat.1, fun K hK _ => hcoat.2 K hK⟩
  exact centMaxProp_of_data hS₀2 hS₀i hz₀2 hcen hmax

end CFSG.Quasithin
