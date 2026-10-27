module

public import CFSG.Quasithin.EmptyFaithful.S146zUF3Triv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S146zU

namespace UF3

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem sectionSeq_of_setting (S : Setting146 G T M) {J : Subgroup G}
    (hZJ : quasithinOmegaOneCenter T ≤ J) (hJU : J ≤ uOfL22 T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G)) :
    ∃ (ι : ↥(tildeOf (quasithinOmegaOneCenter T) J) →*
          ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))
      (q : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) →* ↥(tildeOf J (uOfL22 T M))),
      Function.Injective ι ∧ Function.Surjective q ∧ q.ker = ι.range ∧
      (∀ (g : ↥(mcOf T)) (v : ↥(tildeOf (quasithinOmegaOneCenter T) J)),
        ι (actH hZN hJN g v) = actH hZN hUN g (ι v)) ∧
      (∀ (g : ↥(mcOf T)) (y : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))),
        q (actH hZN hUN g y) = actH hJN hUN g (q y)) :=
  sectionSeq hZJ hJU hZN hJN hUN (uOfL22_le_normalizer_Z S) (uOfL22_le_normalizer_of_le S hJU)

theorem actH_Z_U_eq_one_of_section (S : Setting146 G T M) {W J : Subgroup G}
    (hWN : mcOf T ≤ Subgroup.normalizer (W : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J : Set G))
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hker : ∀ x : ↥(mcOf T), actH hWN hJN x = 1 → (x : G) ∈ pCoreOf 2 (mcOf T))
    (x : ↥(mcOf T)) (hx : actH hWN hJN x = 1) : actH hZN hUN x = 1 :=
  (actH_Z_U_eq_one_iff S hZN hUN x).mpr (hker x hx)

end Setting

end UF3

end S146zU

end CFSG.Quasithin
