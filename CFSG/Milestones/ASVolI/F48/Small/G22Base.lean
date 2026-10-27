module

public import CFSG.Quasithin.Recognition.CertU33Outer

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

@[expose] def burnsideF48s_g22X : Subgroup (Equiv.Perm (Fin 28)) :=
  u33J ⊔ Subgroup.zpowers u33Pi

@[expose] def burnsideF48s_g22Gen (i : Fin 6) : Equiv.Perm (Fin 28) :=
  if h : i.val < 5 then u33Img ⟨i.val, h⟩ else u33Pi

theorem burnsideF48s_u33Img_mem_J (k : Fin 5) : u33Img k ∈ u33J := by
  have h : u33PresHom (PresentedGroup.of k) ∈ u33PresHom.range := ⟨_, rfl⟩
  rw [u33PresHom_of, range_u33PresHom] at h
  exact h

theorem burnsideF48s_g22Gen_mem (i : Fin 6) :
    burnsideF48s_g22Gen i ∈ burnsideF48s_g22X := by
  unfold burnsideF48s_g22Gen
  split_ifs with h
  · exact Subgroup.mem_sup_left (burnsideF48s_u33Img_mem_J _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

@[expose] noncomputable def burnsideF48s_g22L (i : Fin 6) :
    ↥burnsideF48s_g22X :=
  ⟨burnsideF48s_g22Gen i, burnsideF48s_g22Gen_mem i⟩

theorem burnsideF48s_g22L_coe (i : Fin 6) :
    ((burnsideF48s_g22L i : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) = burnsideF48s_g22Gen i :=
  rfl

@[expose] noncomputable def burnsideF48s_g22T :
    Subgroup ↥burnsideF48s_g22X :=
  Subgroup.closure {burnsideF48s_g22L 0, burnsideF48s_g22L 1, burnsideF48s_g22L 2,
    burnsideF48s_g22L 5}

@[expose] noncomputable def burnsideF48s_g22P1 :
    Subgroup ↥burnsideF48s_g22X :=
  Subgroup.closure {burnsideF48s_g22L 0, burnsideF48s_g22L 1, burnsideF48s_g22L 2,
    burnsideF48s_g22L 4, burnsideF48s_g22L 5}

@[expose] noncomputable def burnsideF48s_g22P2 :
    Subgroup ↥burnsideF48s_g22X :=
  Subgroup.closure {burnsideF48s_g22L 0, burnsideF48s_g22L 1, burnsideF48s_g22L 2,
    burnsideF48s_g22L 3, burnsideF48s_g22L 5}

end CFSG.ASVolI
