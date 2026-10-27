module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] def nineH (V K : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaIn V K (nineE V K), U

@[expose] def nineI (V K : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaIn V K (nineE V K), U ⊓ pCoreOf 2 K

@[expose] def nineZ (V K S : Subgroup G) : Subgroup G :=
  ⨆ B ∈ nineOmegaIn V K S, B

@[expose] def nineD (K A : Subgroup G) (x : G) : Subgroup G :=
  (⨆ r ∈ pCoreOf 2 K, conjSubgroup A (x * r)) ⊓ pCoreOf 2 K

@[expose] def nineDp (K A : Subgroup G) (x : G) : Subgroup G :=
  conjSubgroup (nineD K A x) x⁻¹

@[expose] def nineV1 (V K : Subgroup G) (g : G) : Subgroup G :=
  V ⊓ conjSubgroup (pCoreOf 2 K) g

@[expose] def nineW0 (V K S : Subgroup G) (g : G) : Subgroup G :=
  nineV1 V K g ⊔ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K

@[expose] def nineL (K A : Subgroup G) (x g : G) : Subgroup G :=
  nineD K A x ⊔ conjSubgroup (nineD K A x) g

@[expose] def nineH0 (V K : Subgroup G) (g : G) : Subgroup G :=
  nineH V K ⊔ conjSubgroup (nineH V K) g

@[expose] def nineI0 (V K : Subgroup G) (g : G) : Subgroup G :=
  nineI V K ⊔ conjSubgroup (nineI V K) g

structure Nine3Choice (V T A K S X : Subgroup G) (p : ℕ) (g x : G) : Prop where
  core : Nine3Core V T A K S X p
  g_mem : g ∈ nineDeltaStab V S
  V_g : conjSubgroup V g = A
  A_g : conjSubgroup A g = V
  g_sq : g * g ∈ normalizer (V : Set G)
  S₀ : S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ conjSubgroup S g
  x_mem : x ∈ X
  x_gen : X = Subgroup.zpowers x

end CFSG.LocalAnalysis.WeakClosure81
