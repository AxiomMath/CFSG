module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

abbrev GwQ {G : Type} [Group G] (d x : G) : Type := ↥(Gw d x) ⧸ CFSG.pCore 2 ↥(Gw d x)

abbrev gwMk {G : Type} [Group G] (d x : G) : ↥(Gw d x) →* GwQ d x :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥(Gw d x))

section Quot

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem P_le_Tw (h : Ctx T M g A t d x) : pCoreOf 2 (Gw d x) ≤ Tw T d x :=
  le_inf (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.hSyl |>.trans inf_le_left) (pCoreOf_le 2 _)

theorem P_le_Cw (hf : Wp1 T d x) : pCoreOf 2 (Gw d x) ≤ Cw T d x :=
  fun _ hp => (hf.P_le_Bw hp).1

theorem mem_Cw_of_commutator_mem_P (h : Ctx T M g A t d x) (hf : Wp1 T d x) {a : G}
    (ha : a ∈ Gw d x) (hc : (d * d)⁻¹ * a⁻¹ * (d * d) * a ∈ pCoreOf 2 (Gw d x)) :
    a ∈ Cw T d x := by
  set z := d * d with hzdef
  set c := z⁻¹ * a⁻¹ * z * a with hcdef
  have hcz : c * z = z * c := h.z_comm_Tw (P_le_Tw h hc) |>.symm.symm
  have hz2 : z * z = 1 := h.z_sq
  have hcc : c * c = 1 := by
    have e1 : a⁻¹ * z * a = z * c := by rw [hcdef]; group
    have e2 : (a⁻¹ * z * a) * (a⁻¹ * z * a) = 1 := by
      calc (a⁻¹ * z * a) * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a := by group
        _ = 1 := by rw [hz2]; group
    rw [e1] at e2
    calc c * c = z * z * (c * c) := by rw [hz2, one_mul]
      _ = z * (z * c) * c := by group
      _ = z * (c * z) * c := by rw [← hcz]
      _ = (z * c) * (z * c) := by group
      _ = 1 := e2
  have hcz' : a⁻¹ * z * a = z * c := by rw [hcdef]; group
  rcases hf.P_invol c hc hcc with h1 | h1
  ·
    rw [h1, mul_one] at hcz'
    refine ⟨h.c.mem_mcOf_of_comm h.z_mem h.z_ne ?_, ha⟩
    calc a * z = a * (a⁻¹ * z * a) := by rw [hcz']
      _ = z * a := by group
  · exfalso
    obtain ⟨s, hs⟩ := h.hN2
    rw [h1] at hcz'
    have hzw : z * wOfX d x = wOfX d x * z := h.z_comm_w
    apply h.hN1 (s⁻¹ * a⁻¹)
    calc s⁻¹ * a⁻¹ * z * (s⁻¹ * a⁻¹)⁻¹ = s⁻¹ * (a⁻¹ * z * a) * s := by group
      _ = s⁻¹ * (z * wOfX d x) * s := by rw [hcz']
      _ = s⁻¹ * (wOfX d x * z) * s := by rw [hzw]
      _ = s⁻¹ * (s * wOfX d x * s⁻¹) * s := by rw [hs]
      _ = wOfX d x := by group

end Quot

end InspW2

end S143

end CFSG.Quasithin
