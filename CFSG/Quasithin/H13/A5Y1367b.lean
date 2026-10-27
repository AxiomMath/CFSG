module

public import CFSG.Quasithin.H13.A5X1367n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

@[expose] noncomputable def HK (K : Subgroup G) : Subgroup G := K ⊔ S.Lv ⊔ S.Tv

theorem Tv_le_HK (K : Subgroup G) : S.Tv ≤ S.HK K := le_sup_right

theorem HK_le_Gv {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    S.HK K ≤ Subgroup.centralizer ({S.v12} : Set G) :=
  sup_le (sup_le hKG S.Lv_le_Gv) S.Tv_le_Gv

theorem conjClosure_Tv_eq {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    conjClosure K S.Tv = K :=
  le_antisymm (conjClosure_le fun _ ht _ hk => (Subgroup.mem_normalizer_iff.mp (hT ht) _).mp hk)
    (le_conjClosure K S.Tv)

theorem Tv_le_normalizer_conjClosure_V1 {X : Subgroup G}
    (hX : S.Tv ≤ Subgroup.normalizer (X : Set G)) :
    S.Tv ≤ Subgroup.normalizer ((conjClosure S.V1 X : Subgroup G) : Set G) := by
  have key : ∀ t ∈ S.Tv, ∀ c ∈ conjClosure S.V1 X, t * c * t⁻¹ ∈ conjClosure S.V1 X := by
    intro t ht c hc
    have hle : conjClosure S.V1 X ≤
        (conjClosure S.V1 X).comap (MulAut.conj t).toMonoidHom := by
      refine conjClosure_le fun x hx v hv => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have htz : t * S.z ^ k * t⁻¹ = S.z ^ k := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply,
          S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1]
      show t * (x * S.z ^ k * x⁻¹) * t⁻¹ ∈ conjClosure S.V1 X
      have e : t * (x * S.z ^ k * x⁻¹) * t⁻¹ =
          (t * x * t⁻¹) * (t * S.z ^ k * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
      rw [e, htz]
      exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp (hX ht) x).mp hx)
        (Subgroup.zpow_mem_zpowers _ _)
    exact hle hc
  intro t ht
  refine B6.mem_normalizer_of_forall_mem (key t ht) fun c hc => ?_
  have := key t⁻¹ (S.Tv.inv_mem ht) c hc
  rwa [inv_inv] at this

theorem WK_eq {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    S.WK K = conjClosure S.V1 (S.HK K) := by
  have hX : S.Tv ≤ Subgroup.normalizer ((K ⊔ S.Lv : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT ht),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.Tv_le_normalizer_Lv ht)]
  rw [WK, S.conjClosure_Tv_eq hT]
  refine le_antisymm (conjClosure_mono le_rfl le_sup_left) (conjClosure_le fun h hh v hv => ?_)
  have hN : S.HK K ≤ Subgroup.normalizer
      ((conjClosure S.V1 (K ⊔ S.Lv) : Subgroup G) : Set G) :=
    sup_le (le_normalizer_conjClosure _ _) (S.Tv_le_normalizer_conjClosure_V1 hX)
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) v).mp (le_conjClosure _ _ hv)

theorem isSylowTwoOf_Tv_HK (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) : IsSylowTwoOf S.Tv (S.HK K) := by
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  refine ⟨S.Tv_le_HK K, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
  have hrel := Subgroup.relIndex_mul_relIndex S.Tv (S.HK K) _ (S.Tv_le_HK K) (S.HK_le_Gv hKG)
  have h' : 2 ∣ S.Tv.relIndex (S.HK K) := h2
  have h3 : 2 ∣ S.Tv.relIndex (Subgroup.centralizer ({S.v12} : Set G)) :=
    hrel ▸ dvd_mul_of_dvd_left h' _
  exact h3

theorem charTwo_HK (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) : CharTwo (S.HK K) :=
  S153D.charTwo_of_le hF (S.HK_le_Gv hKG)
    ((pCoreOf_two_le_of_isSylowTwoOf (S.isSylowTwoOf_Tv h1222 h517)).trans (S.Tv_le_HK K))

theorem isTwoReducedIn_WK (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : IsTwoReducedIn (S.HK K) (S.WK K) := by
  have hsyl := S.isSylowTwoOf_Tv_HK h1222 h517 hKG
  rw [S.WK_eq hT]
  exact isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    (S.charTwo_HK h1222 h517 hF hKG) S.V1_le_omega_Tv

theorem WK_le_Tv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    S.WK K ≤ S.Tv ∧ pCoreOf 2 (S.HK K) ≠ ⊥ := by
  have hsyl := S.isSylowTwoOf_Tv_HK h1222 h517 hKG
  obtain ⟨hWc, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    (S.charTwo_HK h1222 h517 hF hKG) S.V1_le_omega_Tv
  rw [← S.WK_eq hT] at hWc
  refine ⟨hWc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl)), fun h => ?_⟩
  have hz : S.z ∈ pCoreOf 2 (S.HK K) := (hWc (le_conjClosure _ _ (Subgroup.mem_zpowers _))).1
  rw [h, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

theorem WK_le_Uv {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : S.WK K ≤ S.Uv := by
  rw [S.WK_eq hT]
  exact conjClosure_mono le_rfl (S.HK_le_Gv hKG)

theorem sqtkGroup_HK (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : SQTKGroup ↥(S.HK K) :=
  sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
    (S.WK_le_Tv h1222 h517 hF hKG hT).2

theorem inXz_autOn {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : S.InXz (autOn K S.Uv) := by
  have hTK : autOn S.Tv S.Uv ≤ Subgroup.normalizer ((autOn K S.Uv : Subgroup (MulAut ↥S.Uv)) :
      Set (MulAut ↥S.Uv)) := autOn_le_normalizer_autOn hT
  have e : conjClosure (autOn K S.Uv) (autOn S.Tv S.Uv) = autOn K S.Uv :=
    le_antisymm (conjClosure_le fun _ ht _ hk =>
      (Subgroup.mem_normalizer_iff.mp (hTK ht) _).mp hk) (le_conjClosure _ _)
  have h := hK.2.2.2
  rwa [e] at h

end Setting

end CFSG.Quasithin.H13.A5
