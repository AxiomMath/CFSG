module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12R2Aut
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R3Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem V_le_normalizer_Kv {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) : V ≤ Subgroup.normalizer (Kv : Set G) := by
  intro x hx
  refine hC.normal ?_
  show x ∈ Subgroup.centralizer ({v} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact S126L1b.comm_of_mem hx hC.mem

theorem autBarHom_fix_Ebar {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hH : Hyp126 G T L V) (hC : Ctx1262 F v Kv S) (z : G) (hz : z ∈ V)
    (e : ↥Kv ⧸ Subgroup.center ↥Kv) (he : e ∈ Ebar L V v Kv) :
    autBarHom Kv ⟨z, V_le_normalizer_Kv hC hz⟩ e = e := by
  obtain ⟨a', ha', rfl⟩ := he
  exact autBarHom_apply_of_comm Kv _ a'.2 (S126L1b.comm_of_mem hz (Vv_le_V hH v ha'))

theorem autBarHom_fix_Lbar {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (z : G) (hz : z ∈ V) (hzL : z ∈ Subgroup.centralizer (L : Set G))
    (b : ↥Kv ⧸ Subgroup.center ↥Kv) (hb : b ∈ Lbar L v Kv) :
    autBarHom Kv ⟨z, V_le_normalizer_Kv hC hz⟩ b = b := by
  obtain ⟨l', hl', rfl⟩ := hb
  have h1 : (l' : G) * z = z * (l' : G) :=
    Subgroup.mem_centralizer_iff.1 hzL (l' : G) (Lv_le_L L v hl')
  exact autBarHom_apply_of_comm Kv _ l'.2 h1.symm

theorem hs_branch_A (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (h331 : Stmt3_3_1) (h61 : Lemma12_6_1) (hD11 : Lemma12_6_11) (hHS : FactHSNormLv)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hq : CFSG.IsQuasisimple ↥Kv)
    (hcent : Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) ≤
      (Subgroup.center ↥Kv).map Kv.subtype)
    (eH : Nonempty (↥Kv ⧸ Subgroup.center ↥Kv ≃* NativeSporadic.HS))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hD := a6LocalData_of_ctx h1222 h36 hC hq hcent
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz : (z : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨-, h2, -⟩ := h61 G T L V F hH
  have hzT : (z : G) ∈ Subgroup.centralizer (T : Set G) := by
    exact ((SetLike.ext_iff.1 (h2 hZ).2 (z : G)).1 hz).2
  have hz2 : (z : G) ^ 2 = 1 := hVe.2 z hz.1
  have h1 := hHS _ eH _ _ _ hD (autBarHom Kv ⟨z, V_le_normalizer_Kv hC hz.1⟩)
    (fun e he => autBarHom_fix_Ebar hH hC z hz.1 e he)
    (fun b hb => autBarHom_fix_Lbar hC z hz.1 hz.2 b hb)
  have hzK := mem_centralizer_of_autBarHom_eq_one Kv hK _ h1
  have hKz : Kv ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hzK k hk)
  have hLz : L ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hz.2 l hl
  have hCz := centralizer_le_M h331 hH hzT hz2 hz1' hLz
  exact (hD11 G T L V F v Kv S hC).2 (hKz.trans hCz)

end S126T2

end CFSG.Quasithin.H13
