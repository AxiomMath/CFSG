module

public import CFSG.Milestones.ASVolI.C31.J4NP.Base
public import CFSG.Milestones.ASVolI.C31.J4NP.Plane

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4

@[expose] noncomputable def burnsideJ4NP_F : Subgroup J := Subgroup.closure (Set.range fJ)

theorem burnsideJ4NP_F_eq :
    burnsideJ4NP_F = F4 j4Facts.mat chkF_true :=
  (eSub_eq_closure _).symm

@[expose] def burnsideJ4NP_OpenLeF : Prop :=
  ∀ R : Subgroup J, burnsideJ4NP_Hyp R →
    ∃ c : J, R ≤ burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom

theorem burnsideJ4NP_eq_of_le_comm {G : Type*} [Group G] {R A : Subgroup G} (hRA : R ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcent : Subgroup.centralizer (R : Set G) ≤ R) :
    R = A := by
  refine le_antisymm hRA fun a ha => hcent ?_
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact hA r (hRA hr) a ha

theorem burnsideJ4NP_F_conj_comm
    (c : J) : ∀ a ∈ burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom,
      ∀ b ∈ burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [burnsideJ4NP_F_eq] at ha hb
  rw [← map_mul, ← map_mul, eSub_comm (fJ_basis j4Facts.mat chkF_true) a b ha hb]

theorem burnsideJ4NP_normalizer_of_le_F
    {R : Subgroup J} (hcent : Subgroup.centralizer (R : Set J) ≤ R) {c : J}
    (hRF : R ≤ burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom) :
    R = burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom ∧
      Subgroup.normalizer (R : Set J) = CFSG.Quasithin.KGJ4.M4.map (MulAut.conj c).toMonoidHom := by
  have hR := burnsideJ4NP_eq_of_le_comm hRF (burnsideJ4NP_F_conj_comm c) hcent
  refine ⟨hR, ?_⟩
  rw [hR, burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_F_eq, burnsideJ4NP_normalizer_F4]

theorem burnsideJ4NP_maxNonParabolicP0_of_openLeF
    (h : burnsideJ4NP_OpenLeF) : burnsideJ4KW_MaxNonParabolicP0 := by
  apply burnsideJ4NP_of_hyp
  intro R hR
  obtain ⟨c, hc⟩ := h R hR
  exact ⟨c, (burnsideJ4NP_normalizer_of_le_F hR.cent hc).2.le⟩

end CFSG.ASVolI
