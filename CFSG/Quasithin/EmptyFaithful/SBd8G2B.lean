module

public import CFSG.Quasithin.EmptyFaithful.SBd8G2
public import CFSG.Quasithin.EmptyFaithful.LRed3Four
public import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
public import CFSG.Quasithin.EmptyFaithful.SBd8Map
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6

namespace SBd8


variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famG2 (hG2 : FactG2Cayley) (d : OvgData X A U K) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (e : X ≃* ↥(CFSG.Open.quasithinG2 F)) : False := by
  have hcp : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have h4 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := F) h4
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 F) = ⊥ := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    exact CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hG : IsG2 2 n ↥(CFSG.Open.quasithinG2 F) :=
    IsG2.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (hG2 F n hn hF)
  have hX : IsG2 2 n X := IsG2.of_mulEquiv e.symm hG
  obtain ⟨-, F', hFf, hFfin, hFcp, hF', ⟨ψ₀⟩⟩ := exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 F') := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 F').subgroupOf (adjointGroup Tag.G2 F')) ⊤ :=
    g2Std_isSylowTwoOf
  have hUm : IsSylowTwoOf (U.map ψ₀.toMonoidHom) ⊤ :=
    GoldS146R.isSylowTwoOf_top_map_equiv ψ₀ d.U_syl
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hUm hU₀
  let ψ : X ≃* ↥(adjointGroup Tag.G2 F') := ψ₀.trans (MulAut.conj g)
  have hψ : U.map ψ.toMonoidHom =
      (posUnipotent Tag.G2 F').subgroupOf (adjointGroup Tag.G2 F') := by
    rw [hg]
    show _ = (U.map ψ₀.toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_map]
    rfl
  have d' := d.map ψ
  rw [hψ] at d'
  exact famG2_std hF' hn d'

end SBd8

end CFSG.Quasithin
