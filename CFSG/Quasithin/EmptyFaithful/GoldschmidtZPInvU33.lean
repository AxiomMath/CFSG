module

public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvCore
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.Quasithin

@[expose] def centralInvTab (t : List ℕ) : Bool :=
  (List.range 3).all (fun k => compL t (u33GenTab.getD k []) == compL (u33GenTab.getD k []) t) &&
    compL t t == autId && t != autId

theorem centralInvTab_iff (t : List ℕ) : centralInvTab t = true ↔
    (∀ k < 3, compL t (u33GenTab.getD k []) = compL (u33GenTab.getD k []) t) ∧
      compL t t = autId ∧ t ≠ autId := by
  simp [centralInvTab, List.all_eq_true, List.mem_range, and_assoc]

set_option maxRecDepth 100000 in
theorem u33_central_involution_unique : ∀ i < 32, ∀ j < 32,
    centralInvTab (u33TelTab.getD i []) = true → centralInvTab (u33TelTab.getD j []) = true →
      u33TelTab.getD i [] = u33TelTab.getD j [] := by
  decide +kernel

theorem u33_permL_gen (k : ℕ) (hk : k < 5) :
    permL (u33PresHom (u33GenPG k)) = u33GenTab.getD k [] := by
  rw [u33PresHom_genPG, u33_genTab_eq k hk]

theorem u33_permL_comm {g h : U33G} (hc : g * h = h * g) :
    compL (permL (u33PresHom g)) (permL (u33PresHom h)) =
      compL (permL (u33PresHom h)) (permL (u33PresHom g)) := by
  rw [compL_permL, compL_permL, ← map_mul, ← map_mul, hc]

theorem centralInvTab_tel
    {v : U33G} (hv : v ∈ u33Data.T)
    (hc : ∀ t ∈ u33Data.T, t * v = v * t) (h2 : v ^ 2 = 1) (h1 : v ≠ 1) :
    ∃ i : Fin 32, v = u33Data.Tel i ∧ centralInvTab (u33TelTab.getD i []) = true := by
  obtain ⟨i, rfl⟩ := (u33Data.mem_T_iff v).mp hv
  refine ⟨i, rfl, (centralInvTab_iff _).2 ⟨fun k hk => ?_, ?_, ?_⟩⟩
  · have hgT : u33GenPG k ∈ u33Data.T := by
      interval_cases k
      · exact u33Data.a_mem_T
      · exact u33Data.b_mem_T
      · exact u33Data.s_mem_T
    have := u33_permL_comm (hc _ hgT)
    rw [u33_permL_gen k (by omega), permL_Tel i] at this
    exact this.symm
  · rw [← permL_Tel i, compL_permL, autId_eq, ← map_mul, ← pow_two, h2, map_one]
  · rw [← permL_Tel i, autId_eq, Ne, permL_eq_iff]
    intro h
    exact h1 (u33PresHom_injective (by rw [h, map_one]))

theorem zpUniq_u33G :
    ZPUniq U33G := by
  have : Finite U33G := u33Pres_finite_card_le.1
  refine zpUniq_of_sylow (center_eq_bot_of_simple isSimpleGroup_u33Pres card_u33Pres
    (by norm_num) (by norm_num)) u33Data.T u33_syl.1 u33_syl.2 ?_
  intro c d hc hd hc2 hd2 hc1 hd1
  rw [mem_centerOf_iff] at hc hd
  obtain ⟨i, rfl, hi⟩ := centralInvTab_tel hc.1 (fun t ht => hc.2 t ht) hc2 hc1
  obtain ⟨j, rfl, hj⟩ := centralInvTab_tel hd.1 (fun t ht => hd.2 t ht) hd2 hd1
  have h := u33_central_involution_unique i i.2 j j.2 hi hj
  rw [← permL_Tel i, ← permL_Tel j, permL_eq_iff] at h
  exact u33PresHom_injective h

theorem zpUniq_u33
    {Q : Type} [Group Q]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSU 3 3 1) : ZPUniq Q := by
  obtain ⟨e₁⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
    (Or.inl ⟨by decide, h⟩ : CFSG.Blueprint.LieModel Q .PSU 3 3 1)
  obtain ⟨e₂⟩ := u33Pres_mulEquiv_PSU3
  exact ZPUniq.of_mulEquiv (e₁.trans e₂.symm) zpUniq_u33G

end CFSG.Quasithin.ZPInv
