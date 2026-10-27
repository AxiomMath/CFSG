module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace Dich

private theorem eq_one_of_fixF : ∀ σ : Perm (Fin 5),
    (∀ v ∈ spanF (commGensF orth S5SylF Finset.univ), orth.act σ v = v) → σ = 1 := by
  decide +kernel

theorem eq_one_of_fix_commW (σ : Perm (Fin 5))
    (h : ∀ v ∈ commW orth S5Syl ⊤, orth.act σ v = v) : σ = 1 :=
  eq_one_of_fixF σ fun v hv =>
    h v ((mem_commW_iff orth mem_S5Syl_iff (Uf := Finset.univ) (fun u => by simp) v).mpr hv)

end Dich

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
