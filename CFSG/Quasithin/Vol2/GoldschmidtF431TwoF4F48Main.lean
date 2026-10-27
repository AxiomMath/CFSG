module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4F48Torus
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Data
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctDefs
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.GH74.BNPair CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F48Rig CFSG.Quasithin.H13.F48Rig
  CFSG.LieType.Ree.LargeReeCover CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


structure OctInput (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) where
  R : RankTwoSystem (Gm K a) 8
  simple : IsSimpleGroup (Gm K a)
  hU : IsSylowTwoOf R.U ⊤
  root : ∀ k : ℤ, 1 ≤ k → k ≤ 8 →
    R.root k = (rootV K a (octLab k)).subgroupOf (F4.reeGamma K a)
  cartan : ∀ t : Kˣ × Kˣ, (⟨torusPair a t, torusPair_mem_reeGamma a hK t⟩ : Gm K a) ∈ R.B ⊓ R.N

section Octagon

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
  {hK : Nat.card K = 2 ^ (2 * a + 1)} (O : OctInput K a hK)

theorem coords_radR (k : ℤ) (h1 : 2 ≤ k) (h2 : k ≤ 8) :
    ∀ n ∈ (octLab k).coords, n ∉ ({1, 2} : Finset (Fin 12)) := by
  interval_cases k <;> decide

theorem coords_radS (k : ℤ) (h1 : 1 ≤ k) (h2 : k ≤ 7) :
    ∀ n ∈ (octLab k).coords, n ∉ ({0} : Finset (Fin 12)) := by
  interval_cases k <;> decide

theorem root_fixfree {Z : Finset (Fin 12)} (t : Kˣ × Kˣ)
    (hχ : ∀ n, n ∉ Z → rootChar K a (Idx.ofCoord n) t ≠ 1) {k : ℤ} (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    (hZ : ∀ n ∈ (octLab k).coords, n ∉ Z) {x : Gm K a} (hx : x ∈ O.R.root k)
    (hc : (⟨torusPair a t, torusPair_mem_reeGamma a hK t⟩ : Gm K a) * x *
      (⟨torusPair a t, torusPair_mem_reeGamma a hK t⟩ : Gm K a)⁻¹ = x) : x = 1 := by
  rw [O.root k hk1 hk8] at hx
  exact Subtype.ext (torus_fixfree_rootV hK t (octLab k) hZ hχ _ hx (congrArg Subtype.val hc))

theorem cartanFPF_of_octInput (ha : 1 ≤ a) {D : Type} [Group D] (hfin : Finite D)
    (A : LieAmalgamExt D) {Φ : Gm K a →* (A.setting hfin 8 (by norm_num)).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin 8 (by norm_num)) Φ (Γ O.R) (v O.R b) (v O.R (!b))) :
    (A.setting hfin 8 (by norm_num)).CartanFPF := by
  have := O.simple
  have : Finite (ModGL F4.tag K) := finite_modGL
  cases b
  · obtain ⟨t, ht⟩ := exists_chars_radS ha hK
    refine D4q.F48.cartanFPF_of_rankTwo_radical O.R O.hU hfin (by norm_num) A false XD
      (O.cartan t) ?_
    intro y hy hc
    refine G2.F48.centralizer_Q_trivial O.R O.hU false (O.cartan t) ?_
      hy hc
    intro k hk x hx hxc
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 (by simpa [G2.F48.radList]
      using hk)
    exact root_fixfree O t ht hk1 (by omega) (coords_radS k hk1 (by omega)) hx hxc
  · obtain ⟨t, ht⟩ := exists_chars_radR ha hK
    refine D4q.F48.cartanFPF_of_rankTwo_radical O.R O.hU hfin (by norm_num) A true XD
      (O.cartan t) ?_
    intro y hy hc
    refine G2.F48.centralizer_Q_trivial O.R O.hU true (O.cartan t) ?_
      hy hc
    intro k hk x hx hxc
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 (by simpa [G2.F48.radList]
      using hk)
    exact root_fixfree O t ht (by omega) hk2 (coords_radR k hk1 hk2) hx hxc

end Octagon

section Model

variable (f : ℕ) (hm : F431ModelFacts .twistedF4 0 f)
  (oct : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a → OctInput K a hK)

include oct

theorem cartanFPF_f4 (D : Type) [Group D] (hD : LieModel D .twistedF4 0 2 f)
    (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .twistedF4) (three_le_polyNumber .twistedF4)).CartanFPF := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have := (oct K a hK ha).simple
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (oct K a hK ha).R (oct K a hK ha).hU (hm D hD).1
    (by norm_num) e.symm A
  exact cartanFPF_of_octInput (oct K a hK ha) ha (hm D hD).1 A b XD

theorem faithfulOnType_f4 (D : Type) [Group D] (hD : LieModel D .twistedF4 0 2 f)
    (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .twistedF4)
      (three_le_polyNumber .twistedF4)).FaithfulOnType s := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have := (oct K a hK ha).simple
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (oct K a hK ha).R (oct K a hK ha).hU (hm D hD).1
    (by norm_num) e.symm A
  exact D4q.F48.faithfulOnType_of_rankTwo (oct K a hK ha).R (oct K a hK ha).hU (hm D hD).1
    (by norm_num) A b XD
    (fun k hk => centralizer_inn_trivial A (hm D hD).1 8 (by norm_num) (hm D hD).2 hgen e'.symm
      k hk) s

theorem f431F48_f4 (h45 : F431Facts45 .twistedF4 0 f hm) (hgen : F431Generation .twistedF4 0 f) :
    F431F48 .twistedF4 0 f hm :=
  f431F48_of_model hm h45 hgen (fun D _ hD A => cartanFPF_f4 f hm oct D hD A)
    (fun D _ hD A => faithfulOnType_f4 f hm oct D hD A _)

end Model

end CFSG.Quasithin.H13.F431.TwoF4
