module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_reducedAggregate_of_isTwoReducedIn {X V : Subgroup G} (h : IsTwoReducedIn X V) :
    V ≤ reducedAggregate X := by
  obtain ⟨hVX, hred⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp h
  calc V = (V.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hVX).symm
    _ ≤ (primeReducedAggregate ↥X 2).map X.subtype :=
      Subgroup.map_mono (le_primeReducedAggregate hred)

theorem isTwoReducedIn_conjClosure_omega (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K₀ : Subgroup G} (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀) :
    IsTwoReducedIn (K₀ ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T)) ∧
      conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T) ≤ reducedAggregate (K₀ ⊔ T) := by
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hT.1 hT.2⟩
  have hInH : InH (Ts : Subgroup G) (K₀ ⊔ T) := by
    rw [hTs]
    exact ⟨le_sup_right, hK₀.2.2.2⟩
  have hF : (K₀ ⊔ T) ⊓ centralizer (pCoreOf 2 (K₀ ⊔ T) : Set G) ≤ pCoreOf 2 (K₀ ⊔ T) :=
    charTwo_of_inH hQ.2.1 Ts hInH
  have hred : IsTwoReducedIn (K₀ ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T)) := by
    have h := isTwoReducedIn_conjClosure (K₀ ⊔ T) Ts (hTs ▸ le_sup_right) hF
      (Z := quasithinOmegaOneCenter T) (by rw [hTs])
    exact h
  exact ⟨hred, le_reducedAggregate_of_isTwoReducedIn hred⟩

theorem solvableRadical_le_centralizer_conjClosure (h3214 : Stmt3_2_14) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K₀ : Subgroup G} (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀)
    (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    (CFSG.solvableRadical ↥K₀).map K₀.subtype ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T) : Set G) :=
  (h3214 G T K₀ hs hnab hQ hT hK₀ hq).trans
    (centralizer_le (isTwoReducedIn_conjClosure_omega hQ hT hK₀).2)

omit [Finite G] in
theorem le_solvableRadical_of_map_le {K Q : Type*} [Group K] [Group Q] (φ : K →* Q)
    {S : Subgroup Q} (hS : Group.IsSolvable ↥S) (hker : Group.IsSolvable ↥φ.ker)
    {N : Subgroup K} (hN : N.Normal) (hNS : N.map φ ≤ S) : N ≤ CFSG.solvableRadical K := by
  refine le_sSup ⟨hN, ?_⟩
  let g : ↥N →* ↥S := (φ.comp N.subtype).codRestrict S fun n => hNS ⟨n, n.2, rfl⟩
  let ι : ↥g.ker →* ↥φ.ker := (N.subtype.comp g.ker.subtype).codRestrict φ.ker fun x => by
    have hx : g x = 1 := x.2
    have hx' : φ ((x : ↥N) : K) = 1 := congrArg Subtype.val hx
    exact hx'
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : ↥N) : K) = ((y : ↥N) : K) := congrArg (fun z : ↥φ.ker => (z : K)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have : Group.IsSolvable ↥g.ker := Group.isSolvable_of_isSolvable_injective hι
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

end CFSG.Quasithin.H13.A7
