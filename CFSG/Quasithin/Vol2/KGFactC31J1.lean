module

public import CFSG.Quasithin.Vol2.KGFactC31Act
public import CFSG.Walter.Models
public import CFSG.Walter.J1Props.Hyp

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.Walter.J1Props

theorem twoSubgroup_walterJ1 (P : Subgroup walterJ1)
    (hP : IsPGroup 2 P) : IsMulCommutative P ∧ Nat.card P ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQab := jankoHyp₀.abelian_sylow Q
  have hQ8 := jankoHyp₀.card_sylow Q
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hQ8 ▸ Subgroup.card_dvd_of_le hPQ⟩
  have := hQab.is_comm.comm ⟨a, hPQ a.2⟩ ⟨b, hPQ b.2⟩
  simpa using congrArg Subtype.val this

theorem inspC31SporadicAt_j1 :
    CFSG.Quasithin.InspC31SporadicAt .J1 := by
  intro A _ _ S M₀ R M V _ hSs _ hM₀S hper _ _ _ _ _ _ _ hVM₀ hVne hV hcomm
  obtain ⟨e⟩ := hSs
  let f : S ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  refine (false_of_twoSubgroups (S := S) (fun P hPS hP => ?_) hM₀S hper hVM₀ hVne hV
    hcomm).elim
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup walterJ1 := (P.subgroupOf S).map f.toMonoidHom with hP'def
  have hPS2 : IsPGroup 2 (P.subgroupOf S) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hP'2 : IsPGroup 2 P' := hPS2.map f.toMonoidHom
  obtain ⟨hab, h8⟩ := twoSubgroup_walterJ1 P' hP'2
  have hcard : Nat.card P' = Nat.card P := by
    rw [hP'def, Subgroup.card_map_of_injective f.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hcard ▸ h8⟩
  have ha : f ⟨a, hPS a.2⟩ ∈ P' := ⟨⟨a, hPS a.2⟩, a.2, rfl⟩
  have hb : f ⟨b, hPS b.2⟩ ∈ P' := ⟨⟨b, hPS b.2⟩, b.2, rfl⟩
  have hc := hab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
  have hc' : f (⟨a, hPS a.2⟩ * ⟨b, hPS b.2⟩) = f (⟨b, hPS b.2⟩ * ⟨a, hPS a.2⟩) := by
    rw [map_mul, map_mul]
    simpa using congrArg Subtype.val hc
  have := congrArg Subtype.val (f.injective hc')
  simpa using this

end CFSG.Quasithin.KGC31

end
