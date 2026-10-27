module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Eleven

private theorem fixed_commTwoF : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    ∀ u ∈ commTwoF, orth.act σ u = u → σ ∉ S5SylF → ∀ b ∈ S5SylF, orth.act b u = u := by
  decide +kernel

private theorem exists_comm_not_fixF : ∀ a ∈ S5ThatF, a ≠ 1 →
    ∃ u : orth.W, ∃ b ∈ S5SylF, orth.act b (orth.act a u * u⁻¹) ≠ orth.act a u * u⁻¹ := by
  decide +kernel

theorem mem_fixW_of_act_eq {σ : Perm (Fin 5)} (h4 : σ 4 = 4) (hσ : σ ∉ S5Syl) {u : orth.W}
    (hu : u ∈ F53Mod.commIter orth S5Syl 2) (hfix : orth.act σ u = u) :
    u ∈ fixW orth S5Syl := by
  have hσF : σ ∉ S5SylF := fun h => hσ ((mem_S5Syl_iff σ).mpr h)
  have h := fixed_commTwoF σ h4 u ((mem_commIter_two_iff u).mp hu) hfix hσF
  exact fun b hb => h b ((mem_S5Syl_iff b).mp hb)

theorem exists_comm_not_mem_fixW {a : Perm (Fin 5)} (ha : a ∈ S5That) (ha1 : a ≠ 1) :
    ∃ u : orth.W, orth.act a u * u⁻¹ ∉ fixW orth S5Syl := by
  obtain ⟨u, b, hb, hne⟩ := exists_comm_not_fixF a ((mem_S5That_iff a).mp ha) ha1
  exact ⟨u, fun h => hne (h b ((mem_S5Syl_iff b).mpr hb))⟩

end Eleven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
