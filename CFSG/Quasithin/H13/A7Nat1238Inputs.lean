module

public import CFSG.Quasithin.H13.A7Nat1238Ke

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup CFSG.Quasithin.SteinbergCB

structure Setting1238 {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V) : Prop where
  alt : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
    alternatingGroup (Fin 7))
  act : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ
  onto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ
  cz : centralizer (quasithinOmegaOneCenter T : Set G) ≤ normalizer (L : Set G)
  mem : (e : G) ∈ quasithinOmegaOneCenter T
  weight : hammingNorm (vec ψ e) = 2

@[expose] def Gap1237KeJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V)
    (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V), Setting1238 hyp ψ e →
      Kv hyp e = ⁅Kv hyp e, thompsonJ T⁆

@[expose] def Insp1238NonQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V)
    (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V), Setting1238 hyp ψ e →
    Kv hyp e ∈ lFamily T → ∀ K₀ : Subgroup G, Kv hyp e ≤ K₀ → quasithinIsLocal T K₀ →
      T ≤ normalizer (K₀ : Set G) → ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) →
      K₀ = ⁅K₀, thompsonJ T⁆ → ¬ K₀ ≤ centralizer (quasithinOmegaOneCenter T : Set G) →
      K₀ ≤ (K₀ ⊓ centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ Kv hyp e

@[expose] def Insp1238Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V)
    (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V), Setting1238 hyp ψ e →
    A7NatPre T L V ψ → vec ψ e = vecFS → ∀ y : V, (y : G) ∈ quasithinOmegaOneCenter T →
    hammingNorm (vec ψ y) = 4 →
    ∀ K K₀ : Subgroup G, K ∈ cComp (hyp.Gv e) → Kv hyp e ≤ K → K ≤ K₀ →
      quasithinIsMaximalLocal T K₀ → quasithinIsFaithfulLocal T K₀ →
      CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) → K₀ = ⁅K₀, thompsonJ T⁆ →
      ¬ K₀ ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K₀ ⊔ T)) : Set G) →
      Kv hyp e = K ∨ (K = K₀ ∧ ∀ v : V, (v : G) ∈ ⁅V, Kv hyp e⁆ → hammingNorm (vec ψ v) = 4 →
        K ≤ closure ((Kv hyp e : Set G) ∪ (K ⊓ centralizer ({(v : G)} : Set G))))

@[expose] def Insp1238Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V)
    (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V), Setting1238 hyp ψ e →
    A7NatPre T L V ψ → vec ψ e = vecFS → ∀ y : V, (y : G) ∈ quasithinOmegaOneCenter T →
    hammingNorm (vec ψ y) = 4 → T ≤ normalizer (Kv hyp e : Set G) →
    ((Kv hyp e).subgroupOf (hyp.Gv e)).Normal → Kv hyp e = ⁅Kv hyp e, thompsonJ T⁆ →
      centralizerSection (hyp.Gv e) (Kv hyp e) (pCoreOf 2 (Kv hyp e)) ≤
        centralizer ((⁅V, Kv hyp e⁆ : Subgroup G) : Set G)

end CFSG.Quasithin.H13.A7
