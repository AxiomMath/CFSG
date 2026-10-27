module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem zGroup_le_ballStab_two (h71c : Fan71c F L) {α : V} :
    L.zGroup 2 α ≤ ballStab Γ G 2 α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨δ, hd, h5, rfl⟩
  refine mem_ballStab.2 fun u hu => (h71c.z_smul_eq_iff h5 u).2 ?_
  have := F.isTree.connected.dist_triangle (u := δ) (v := α) (w := u)
  rw [SimpleGraph.dist_comm (u := δ) (v := α)] at this
  omega

theorem mem_nbrStab_of_fix_two (F : FanTree Γ G) {v u w : V} {a : G}
    (ha : a ∈ MulAction.stabilizer G v) (hu : Γ.Adj v u) (hw : Γ.Adj v w) (huw : u ≠ w)
    (hau : a • u = u) (haw : a • w = w) : a ∈ nbrStab Γ G v :=
  fun c hc => F.frobenius_two v u w hu hw huw a ha hau haw c hc

theorem sq_mem_nbrStab_of_sup (F : FanTree Γ G) {w μ : V} (hwμ : Γ.Adj w μ) {V' C' : Subgroup G}
    (hV : ∀ v ∈ V', v ∈ MulAction.stabilizer G w ∧ v ∈ MulAction.stabilizer G μ)
    (hVsq : ∀ v ∈ V', v * v = 1)
    (hC : ∀ c ∈ C', c ∈ nbrStab Γ G w ∧ c ∈ MulAction.stabilizer G μ) {b : G}
    (hb : b ∈ V' ⊔ C') : b * b ∈ nbrStab Γ G w := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hwμ
  let ψ : ↥(MulAction.stabilizer G w ⊓ MulAction.stabilizer G μ) →*
      (ZMod (valence Γ w))ˣ := (powMonoidHom 2).comp φ
  let Θ : Subgroup G := ψ.ker.map (Subgroup.subtype _)
  have hmem : ∀ g : G, g ∈ MulAction.stabilizer G w → g ∈ MulAction.stabilizer G μ →
      g ∈ MulAction.stabilizer G w ⊓ MulAction.stabilizer G μ := fun g h1 h2 =>
    Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hVΘ : V' ≤ Θ := fun v hv => by
    refine Subgroup.mem_map.2 ⟨⟨v, hmem v (hV v hv).1 (hV v hv).2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    show φ _ ^ 2 = 1
    have he : (⟨v, hmem v (hV v hv).1 (hV v hv).2⟩ : ↥(MulAction.stabilizer G w ⊓
        MulAction.stabilizer G μ)) * ⟨v, hmem v (hV v hv).1 (hV v hv).2⟩ = 1 :=
      Subtype.ext (hVsq v hv)
    rw [pow_two, ← map_mul, he, map_one]
  have hCΘ : C' ≤ Θ := fun c hc => by
    refine Subgroup.mem_map.2 ⟨⟨c, hmem c (F.nbrStab_le_stabilizer w (hC c hc).1)
      (hC c hc).2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    show φ _ ^ 2 = 1
    rw [(hφ _).1 (hC c hc).1, one_pow]
  obtain ⟨e, he, hbe⟩ := Subgroup.mem_map.1 (sup_le hVΘ hCΘ hb)
  rw [MonoidHom.mem_ker] at he
  have h1 : φ e ^ 2 = 1 := he
  have h2 : φ (e * e) = 1 := by rw [map_mul, ← pow_two]; exact h1
  have h3 := (hφ (e * e)).2 h2
  rw [← hbe]
  exact h3

end P74

end CFSG.Quasithin.Fan86
