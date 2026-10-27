module

public import CFSG.Quasithin.MS93.C56Red
public import CFSG.Quasithin.MS93.S5A56FStmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5C56

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem c56g_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {γ δ : Vtx (puAmalgam h.le)}
    (hZγ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    (hZδ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hconc : S5.Concl56 h (2 ^ k) a α' l g x) :
    ZM _ (g⁻¹ • δ) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  intro z hz
  have h1 := hZγ ⟨hz.1.2, hz.2⟩
  have h2 := zm_inf_zm_smul_le h hZδ (inv_mem hg) ⟨hz.1.2, hz.1.1⟩
  rw [inv_inv] at h2
  refine le_stabCenter_of_gen h hd hl (g := g) (fun E hE hE2 hErel => ?_) ⟨⟨hz.1.2, h1⟩, h2⟩
  refine hconc.1 (S5.rconj g E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE
    ?_ hErel
  rw [relIndex_rconj h hg]
  exact hErel

theorem c56x_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {γ δ : Vtx (puAmalgam h.le)}
    (hZγ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    (hZδ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hconc : S5.Concl56 h (2 ^ k) a α' l g x)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    ZM _ (x⁻¹ • g⁻¹ • δ) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨ha, -, -, hdq⟩ := hconc
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hxP := hdq hidx
  have hN : S5.vPre h.le a (MSP.stab l) ≤ Subgroup.normalizer
      (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) :=
    vPre_le_normalizer_vPre h.le (MSP.stab_le_normalizer_fixer l)
  have hrx : S5.rconj x⁻¹ (S5.vPre h.le a (MSP.qLine l)) = S5.vPre h.le a (MSP.qLine l) := by
    rw [S5B.rconj_eq_map, inv_inv]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hN hxP)
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  intro z hz
  have h1 := hZγ ⟨hz.1.2, hz.2⟩
  have hzμ : z ∈ ZM _ ((g * x)⁻¹ • δ) := by
    rw [mul_inv_rev, mul_smul]
    exact hz.1.1
  have h2 := zm_inf_zm_smul_le h hZδ (inv_mem hgx) ⟨hz.1.2, hzμ⟩
  rw [inv_inv] at h2
  refine le_stabCenter_of_gen h hd hl (g := g * x) (fun E hE hE2 hErel => ?_) ⟨⟨hz.1.2, h1⟩, h2⟩
  have hE' : S5.rconj x⁻¹ E ≤ S5.vPre h.le a (MSP.qLine l) := by
    rw [← hrx]
    exact (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hE
  have h0 := ha (S5.rconj g E) (S5.rconj x⁻¹ E) (hE2.map _) (hE2.map _)
    ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE'
    (by rw [relIndex_rconj h hg]; exact hErel)
    (by rw [relIndex_rconj h (inv_mem hxst)]; exact hErel)
  have h3 := congrArg (S5.rconj x) h0
  rw [S5B.rconj_sup, S5B.rconj_sup, ← S5B.rconj_mul, S5B.rconj_rconj_inv,
    S5B.rconj_eq_self_of_mem hxst] at h3
  have hQx : S5.rconj x (Qv _ (baseA (puAmalgam h.le))) = Qv _ (baseA (puAmalgam h.le)) := by
    rw [S5B.rconj_eq_map, ← qv_smul, (mem_stab _).1 (inv_mem hxst)]
  rw [hQx] at h3
  exact h3

theorem c56x_two_of_opp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {γ δ : Vtx (puAmalgam h.le)}
    (hZγ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    (hZδ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hopp : S5.Opp56 h (2 ^ k) a l g x) :
    ZM _ (x⁻¹ • g⁻¹ • δ) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  intro z hz
  have h1 := hZγ ⟨hz.1.2, hz.2⟩
  have hzμ : z ∈ ZM _ ((g * x)⁻¹ • δ) := by
    rw [mul_inv_rev, mul_smul]
    exact hz.1.1
  have h2 := zm_inf_zm_smul_le h hZδ (inv_mem hgx) ⟨hz.1.2, hzμ⟩
  rw [inv_inv] at h2
  refine le_stabCenter_of_gen h hd hl (g := g * x) (fun E hE hE2 hErel => ?_) ⟨⟨hz.1.2, h1⟩, h2⟩
  refine hopp (S5.rconj (g * x) E) E (hE2.map _) hE2
    ((S5B.rconj_le_rconj_iff (g := g * x)).2 hE) hE ?_ hErel
  rw [relIndex_rconj h hgx]
  exact hErel

end S5C56

end CFSG.Quasithin.MS93
