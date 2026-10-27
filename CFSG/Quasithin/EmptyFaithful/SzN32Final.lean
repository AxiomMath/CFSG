module

public import CFSG.Quasithin.EmptyFaithful.SzN32ThmA
public import CFSG.Quasithin.EmptyFaithful.SzN32Model
public import CFSG.Quasithin.EmptyFaithful.SzN32Sylow
public import CFSG.Quasithin.EmptyFaithful.SzN31SmallStmt

public section

namespace CFSG.Quasithin.SzN32

theorem sylowGL6NoCover_proved : CFSG.Quasithin.SzN31.SylowGL6NoCover := by
  intro V _ _ _ hV S hS hS81 Q _ _ hQ hE π hπ
  obtain ⟨a, σ, hT⟩ := sylow_tdata model_exists V hV S hS hS81
  obtain ⟨E, h27, hexp, hcomm⟩ := no_E27_cover hT Q hQ π hπ
  have h := hE E hexp hcomm
  rw [h27] at h
  norm_num at h

end CFSG.Quasithin.SzN32
