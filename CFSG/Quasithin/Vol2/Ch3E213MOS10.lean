module

public import CFSG.Quasithin.Vol2.Ch3E213MOS9
public import CFSG.Quasithin.Vol2.Ch3E213MOS2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.GH74.BNPair.Defs
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

section Aut

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem false_of_aut (h13a : IVK_1_3a) (h13b : IVK_1_3b) (hF : L2Field F) (e : K ≃* L2 F)
    (N : L2Notation e) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : f = 1 ∨ f = 2)
    (hq : Nat.card F = p ^ f) {T₀ M₀ V₀ : Subgroup (MulAut K)} (hPT : N.P ≤ T₀)
    (hT : T₀ ≤ N.T) (h8 : 8 < Nat.card T₀) (hVT : V₀ ≤ T₀)
    (hVn : T₀ ≤ Subgroup.normalizer (V₀ : Set (MulAut K))) (hsq : ∀ v ∈ V₀, v * v = 1)
    (hV4 : 4 ≤ Nat.card V₀) (hVM : V₀ ≤ pCoreOf 2 M₀)
    (hD' : M₀ ⊓ innAut K = innAut K ⊓ Subgroup.centralizer (E2P.zOf N.P : Set (MulAut K)))
    (uniq : ∀ Y : Subgroup (MulAut K), Y ≤ innAut K → N.P ≤ Y → Y ≠ innAut K →
      T₀ ≤ Subgroup.normalizer (Y : Set (MulAut K)) → Y ≤ M₀)
    (hcoat : 11 ≤ Nat.card F → ∀ u : K, orderOf u = 2 →
      IsCoatom (Subgroup.centralizer ({u} : Set K))) : False := by
  rcases hf with rfl | rfl
  · have h1 : Nat.card (fieldAutSub e) = 1 := (ivk_1_2e F hF K e).2.2 p 1 hp hq
    have htop : innDiagSub e = ⊤ := by
      have h := innDiagSub_sup_fieldAutSub e
      rwa [Subgroup.eq_bot_of_card_eq _ h1, sup_bot_eq] at h
    have hTPt : T₀ ≤ N.Pt := fun x hx => ⟨hT hx, by rw [htop]; exact Subgroup.mem_top x⟩
    have := card_le_two_of_le_Pt ivk_1_2c ivk_1_2d hF N hPT hTPt h8 hVT hVn hsq
    omega
  · have h11 : 11 ≤ Nat.card F := by
      rw [hq]
      nlinarith
    exact false_of_sq h13a h13b hF e N hp hp3 hq hPT hT hVT hVn hsq hV4 hVM hD' uniq
      (hcoat h11)

end Aut

section Transport

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_centralizer_map_iff {Y : Type} [Group Y] {ι : X →* Y} (hι : Function.Injective ι)
    {P : Subgroup X} {g : X} :
    ι g ∈ Subgroup.centralizer (P.map ι : Set Y) ↔ g ∈ Subgroup.centralizer (P : Set X) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact hι (by rw [map_mul, map_mul]; exact h (ι x) ⟨x, hx, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

omit [Finite X] in
theorem map_zOf {Y : Type} [Group Y] {ι : X →* Y} (hι : Function.Injective ι) (S : Subgroup X) :
    (E2P.zOf S).map ι = E2P.zOf (S.map ι) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxC⟩, rfl⟩
    exact ⟨⟨x, hxS, rfl⟩, (mem_centralizer_map_iff hι).mpr hxC⟩
  · rintro ⟨⟨x, hxS, rfl⟩, hxC⟩
    exact ⟨x, ⟨hxS, (mem_centralizer_map_iff hι).mp hxC⟩, rfl⟩

omit [Finite X] in
theorem map_inf_eq_centralizer {Y : Type} [Group Y] {ι : X →* Y} (hι : Function.Injective ι)
    {M K A : Subgroup X} (h : M ⊓ K = K ⊓ Subgroup.centralizer (A : Set X)) :
    M.map ι ⊓ K.map ι = K.map ι ⊓ Subgroup.centralizer (A.map ι : Set Y) := by
  rw [← Subgroup.map_inf_eq _ _ ι hι, h]
  ext y
  constructor
  · rintro ⟨x, ⟨hxK, hxC⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, (mem_centralizer_map_iff hι).mpr hxC⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hxC⟩
    exact ⟨x, ⟨hxK, (mem_centralizer_map_iff hι).mp hxC⟩, rfl⟩

omit [Finite X] in
theorem conjNormal_injective {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : x * k * x⁻¹ = k := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) (MonoidHom.mem_ker.mp hx)
      simpa using this
    calc k * x = x * k * x⁻¹ * x := by rw [h1]
      _ = x * k := by group
  rw [hC] at hxC
  exact hxC

omit [Finite X] in
theorem map_conjNormal_eq {K : Subgroup X} [K.Normal] :
    K.map (MulAut.conjNormal : X →* MulAut ↥K) = innAut ↥K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (MulAut.conjNormal_val (h := (⟨x, hx⟩ : ↥K))).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, MulAut.conjNormal_val⟩

end Transport

end CFSG.Quasithin.Ch3E213M.OS
