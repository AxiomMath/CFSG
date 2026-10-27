module

public import CFSG.Quasithin.EmptyFaithful.Gap6S1514b

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def vE (T Mc M : Subgroup G) : Subgroup G :=
  V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G)

theorem T_le_normalizer_vE {T Mc M : Subgroup G} (hTM : T ≤ M) :
    T ≤ Subgroup.normalizer (vE T Mc M : Set G) := by
  have h1 : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans (le_normalizer_V154 T Mc M)
  have h2 : T ≤ Subgroup.normalizer (Subgroup.centralizer (thompsonJi T 1 : Set G) : Set G) :=
    fun x hx => Gap6.normalizer_le_normalizer_centralizer_gap6 _
      (normalizer_le_normalizer_thompsonJi151 T 1 (Subgroup.le_normalizer hx))
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1 hx, h2 hx⟩

omit [Finite G] in
theorem isUniqueMaxOver_of_key {K T N : Subgroup G} (hTN : T ≤ N) (hlt : N < K)
    (key : ∀ Y : Subgroup G, T ≤ Y → Y < K → Y ≤ N) : IsUniqueMaxOver K T N := by
  have hmax : IsMaxSubgroupIn K N := by
    refine ⟨hlt, fun L hL hLK => ?_⟩
    by_contra hne
    exact (lt_irrefl _) (lt_of_lt_of_le hL (key L (hTN.trans hL.le) (lt_of_le_of_ne hLK hne)))
  ext X
  simp only [maxOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hX, hTX⟩
    have hXle : X ≤ N := key X hTX hX.1
    by_contra hne
    exact (hX.2 N (lt_of_le_of_ne hXle hne) hlt.le) ▸ hlt |>.ne rfl
  · rintro rfl
    exact ⟨hmax, hTN⟩

structure NonBorelK (T Mc M K N : Subgroup G) : Prop where
  minParabolic : MinParabolic K T N
  le_centralizer : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  not_le_M : ¬ N ≤ M
  eq_normalizer : N = K ⊓ Subgroup.normalizer (vE T Mc M : Set G)
  not_oTwoUpper_le : ¬ oTwoUpper K ≤ Subgroup.centralizer (vE T Mc M : Set G)

theorem nonBorelK_of_residual2 {T Mc M K : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hMf : IsMf T Mc M) (h159 : Lemma1519Concl T Mc M)
    (hTK : T ≤ K) (hKC : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hK : ¬ oTwoUpper K ≤ Subgroup.centralizer (vE T Mc M : Set G))
    (hmin : ∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G))
    (hKW : ¬ K ≤ Subgroup.normalizer (vE T Mc M : Set G))
    (hK1M : ¬ K ⊓ Subgroup.normalizer (vE T Mc M : Set G) ≤ M)
    (hyp1 : oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (vE T Mc M : Set G)) :
    NonBorelK T Mc M K (K ⊓ Subgroup.normalizer (vE T Mc M : Set G)) := by
  have hTM : T ≤ M := hMf.1.1.2
  have hTW : T ≤ Subgroup.normalizer (vE T Mc M : Set G) := T_le_normalizer_vE hTM
  have hKM : ¬ K ≤ M := fun hKM => hK ((oTwoUpper_mono (le_inf hKM hKC)).trans hyp1)
  have hL2 : ∀ L : Subgroup G, T ≤ L → L < K →
      L ≤ Subgroup.normalizer (vE T Mc M : Set G) := by
    intro L hTL hLK
    have hLsyl := Gap6.isSylowTwoOf_of_le_gap6 h.sylow hTL
    exact (eq_oTwoUpper_sup_of_isSylowTwoOf hLsyl).le.trans
      (sup_le ((hmin L hTL hLK).trans (Subgroup.centralizer_le_normalizer _)) hTW)
  have hlt : K ⊓ Subgroup.normalizer (vE T Mc M : Set G) < K :=
    lt_of_le_of_ne inf_le_left fun h' => hKW (h' ▸ inf_le_right)
  have hsyl : IsSylowTwoOf T K := Gap6.isSylowTwoOf_of_le_gap6 h.sylow hTK
  refine ⟨⟨hsyl, ?_, ?_⟩, hKC, hK1M, rfl, hK⟩
  · exact fun hKT => hKM (hKT.trans h159.seven_normalizer)
  · exact isUniqueMaxOver_of_key (le_inf hTK hTW) hlt fun Y hTY hYK =>
      le_inf hYK.le (hL2 Y hTY hYK)

end Gap6R2

end CFSG.Quasithin
