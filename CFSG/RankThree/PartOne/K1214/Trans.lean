module

public import CFSG.RankThree.PartOne.K1214.XFrame
public import CFSG.RankThree.PartOne.S12.Sec12FusSplit

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

theorem pow_eq_one_of_card_eq {p : ℕ} {U : Subgroup G} (hU : Nat.card U = p) {u : G} (hu : u ∈ U) :
    u ^ p = 1 := by
  have h : (⟨u, hu⟩ : ↥U) ^ Nat.card U = 1 := pow_card_eq_one'
  rw [hU] at h
  exact congrArg Subtype.val h

theorem zpowers_eq_of_card_eq_prime [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : Nat.card U = p) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : Subgroup.zpowers u = U := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf u = p := orderOf_eq_prime (pow_eq_one_of_card_eq hU hu) hu1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu) ?_
  rw [Nat.card_zpowers, hord, hU]

theorem kf1214Trans_of_u5 (hU5 : KF1214U5) : KF1214Trans := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hb U V hUP hVP hUc hVc hUQ hVQ
  have hp : p.Prime := ctx.hyp.prime
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH := not_dvd_torusImage ctx hn12
  have hmemE : ∀ u ∈ P, u ^ p = 1 → u ∈ E := fun u hu hup => by
    rw [← hb.omega]
    exact Subgroup.subset_closure ⟨hu, hup⟩
  have hUE : ∀ u ∈ U, u ∈ E := fun u hu => hmemE u (hUP hu) (pow_eq_one_of_card_eq hUc hu)
  have hVE : ∀ v ∈ V, v ∈ E := fun v hv => hmemE v (hVP hv) (pow_eq_one_of_card_eq hVc hv)
  obtain ⟨u, huU, huQ⟩ := IsConcreteLE.not_le_iff_exists.1 hUQ
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 hVQ
  have hnotL : ∀ w ∈ E, w ∉ Q → w ∉ L := fun w hwE hwQ hwL => hwQ (by
    have : w ∈ E ⊓ L := ⟨hwE, hwL⟩
    rw [← hb.QE] at this
    exact this.1)
  obtain ⟨x, hxX, k, hk⟩ := exists_regular ctx hC (hUE u huU) (hVE v hvV)
    (hnotL u (hUE u huU) huQ) (hnotL v (hVE v hvV) hvQ)
  have hu1 : u ≠ 1 := fun h => huQ (h ▸ Q.one_mem)
  have hUu : Subgroup.zpowers u = U := zpowers_eq_of_card_eq_prime hp hUc huU hu1
  have hconj : conjBy x U = Subgroup.zpowers (x * u * x⁻¹) := by
    rw [← hUu]
    unfold conjBy
    rw [MonoidHom.map_zpowers]
    rfl
  have hle : conjBy x U ≤ V := by
    rw [hconj, hk]
    exact Subgroup.zpowers_le.2 (Subgroup.zpow_mem _ hvV k)
  refine ⟨x, hC.P_sylow.2 hxX, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  unfold conjBy
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hUc, hVc]

end CFSG.RankThree.PartOne.K1214
