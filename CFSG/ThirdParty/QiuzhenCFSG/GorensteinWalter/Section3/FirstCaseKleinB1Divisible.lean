module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FreeActionCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetRepresentative
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCosetFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-!
# `8 ∣ b₁`: the Sylow `2`-subgroup acts fixed-point-free on `J₁`

For `y ∈ J₁` the coset `Ĥ y` contains exactly one involution.  If an
involution `s ∈ S` commutes with `y`, then `s·y` is a second involution in
the same coset, so `s = 1`.  Hence the centralizer in `S` of every element
of `J₁` is trivial, and since `S` is a `2`-group the conjugation action of
`S` on `J₁` is free.
-/

private theorem inverted_card_conj
    {G : Type u} [Group G] (H : Subgroup G) {s x : G} (hsH : s ∈ H) :
    Nat.card {h : G // h ∈ invertedElements H (s * x * s⁻¹)} =
      Nat.card {h : G // h ∈ invertedElements H x} := by
  classical
  let e : {h : G // h ∈ invertedElements H (s * x * s⁻¹)} ≃
      {h : G // h ∈ invertedElements H x} :=
    { toFun := fun h => ⟨s⁻¹ * h.1 * s, by
        refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hsH) h.2.1) hsH, ?_⟩
        calc
          x * (s⁻¹ * h.1 * s) * x⁻¹ =
              s⁻¹ * ((s * x * s⁻¹) * h.1 * (s * x * s⁻¹)⁻¹) * s := by group
          _ = s⁻¹ * h.1⁻¹ * s := by rw [h.2.2]
          _ = (s⁻¹ * h.1 * s)⁻¹ := by group⟩
      invFun := fun h => ⟨s * h.1 * s⁻¹, by
        refine ⟨H.mul_mem (H.mul_mem hsH h.2.1) (H.inv_mem hsH), ?_⟩
        calc
          (s * x * s⁻¹) * (s * h.1 * s⁻¹) * (s * x * s⁻¹)⁻¹ =
              s * (x * h.1 * x⁻¹) * s⁻¹ := by group
          _ = s * h.1⁻¹ * s⁻¹ := by rw [h.2.2]
          _ = (s * h.1 * s⁻¹)⁻¹ := by group⟩
      left_inv := by
        intro h
        apply Subtype.ext
        group
      right_inv := by
        intro h
        apply Subtype.ext
        group }
  exact Nat.card_congr e

private theorem isInvolution_conj
    {G : Type u} [Group G] {s x : G} (hx : IsInvolution x) :
    IsInvolution (s * x * s⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hx.1
    calc
      x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = 1 := by simp [h]
  · calc
      (s * x * s⁻¹) ^ 2 = (s * x * s⁻¹) * (s * x * s⁻¹) := by rw [pow_two]
      _ = s * (x * x) * s⁻¹ := by group
      _ = s * 1 * s⁻¹ := by
        rw [show x * x = 1 from (by simpa [pow_two] using hx.2)]
      _ = 1 := by
        group

private theorem mem_inverted_card_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {z : G}
    (hcard : Nat.card {h : G // h ∈ invertedElements H z} = 1) :
    ∀ h : G, h ∈ invertedElements H z → h = 1 := by
  classical
  intro h hh
  have hone : (1 : G) ∈ invertedElements H z := ⟨H.one_mem, by simp⟩
  obtain ⟨z0, hz0⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hEq : (⟨h, hh⟩ : {w : G // w ∈ invertedElements H z}) = z0 := hz0 _
  have h1Eq : (⟨1, hone⟩ : {w : G // w ∈ invertedElements H z}) = z0 := hz0 _
  exact congrArg Subtype.val (hEq.trans h1Eq.symm)

public theorem firstCase_klein_eight_dvd_b1
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (_K : Subgroup G) (b0 b1 b2 b3 b4 : ℕ)
    (hJn : ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n) :
    8 ∣ b1 := by
  classical
  let S : Subgroup G := (c.S : Subgroup G)
  let J1 : Type u := {x : G // x ∈ firstCaseJ c 1}
  have hSleHhat : S ≤ c.Hhat := (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  have hSleHhat' : ∀ s : G, s ∈ S → s ∈ c.Hhat := by
    intro s hs
    exact hSleHhat hs
  let : MulAction S J1 :=
    { smul := fun s x => ⟨s.1 * x.1 * s.1⁻¹, by
        have hxJ' : IsInvolution x.1 ∧ x.1 ∉ c.Hhat ∧
            firstCaseCosetInvolutions c x.1 = 1 := by
          change x.1 ∈ firstCaseJ c 1
          exact x.2
        have hxI : IsInvolution x.1 := hxJ'.1
        have hxH : x.1 ∉ c.Hhat := hxJ'.2.1
        have hxcard : firstCaseCosetInvolutions c x.1 = 1 := hxJ'.2.2
        let z : G := s.1 * x.1 * s.1⁻¹
        have hzI : IsInvolution z := isInvolution_conj hxI
        have hzH : z ∉ c.Hhat := by
          intro hz
          apply hxH
          have hs1 : s.1⁻¹ ∈ c.Hhat := c.Hhat.inv_mem (hSleHhat' s.1 s.2)
          have hmem : s.1⁻¹ * z * s.1 ∈ c.Hhat :=
            c.Hhat.mul_mem (c.Hhat.mul_mem hs1 hz) (hSleHhat' s.1 s.2)
          have hxeq : x.1 = s.1⁻¹ * z * s.1 := by
            dsimp [z]
            group
          rw [hxeq]
          exact hmem
        have hzcardInv : Nat.card {h : G // h ∈ invertedElements c.Hhat z} = 1 := by
          have hxcardInv : Nat.card {h : G // h ∈ invertedElements c.Hhat x.1} = 1 := by
            rw [← firstCase_klein_coset_involution_card_eq c hxI hxH]
            exact hxcard
          rw [inverted_card_conj c.Hhat (s := s.1) (x := x.1)
            (hSleHhat' s.1 s.2)]
          exact hxcardInv
        have hzcard : firstCaseCosetInvolutions c z = 1 := by
          rw [firstCase_klein_coset_involution_card_eq c hzI hzH]
          exact hzcardInv
        simpa [z, firstCaseJ] using ⟨hzI, hzH, hzcard⟩⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : G) * x.1 * (1 : G)⁻¹ = x.1
        group
      mul_smul := by
        intro s1 s2 x
        apply Subtype.ext
        change (s1.1 * s2.1) * x.1 * ((s1.1 * s2.1)⁻¹) =
          s1.1 * (s2.1 * x.1 * s2.1⁻¹) * s1.1⁻¹
        group }
  have hfree : ∀ x : J1, ∀ s : S, s • x = x → s = 1 := by
    intro x s hfix
    by_contra hsne
    have hxJ' : IsInvolution x.1 ∧ x.1 ∉ c.Hhat ∧
        firstCaseCosetInvolutions c x.1 = 1 := by
      change x.1 ∈ firstCaseJ c 1
      exact x.2
    have hxI : IsInvolution x.1 := hxJ'.1
    have hxH : x.1 ∉ c.Hhat := hxJ'.2.1
    have hxcard : firstCaseCosetInvolutions c x.1 = 1 := hxJ'.2.2
    have hconj : s.1 * x.1 * s.1⁻¹ = x.1 := congrArg Subtype.val hfix
    have hSpow : IsPGroup 2 S := c.S.isPGroup'
    let T : Subgroup S := Subgroup.zpowers s
    have hTne : T ≠ ⊥ := by
      intro hbot
      apply hsne
      have : s ∈ (⊥ : Subgroup S) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers s
      exact Subgroup.mem_bot.mp this
    have hord : ∃ n : ℕ, orderOf s = 2 ^ n :=
      (IsPGroup.iff_orderOf (p := 2) (G := S)).mp hSpow s
    rcases hord with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hn0
      apply hsne
      have : orderOf s = 1 := by
        have hn0' : n = 0 :=
          le_antisymm (not_lt.mp hn0) (Nat.zero_le n)
        rw [hn, hn0']
        simp
      exact orderOf_eq_one_iff.mp this
    have h2dvd : 2 ∣ Nat.card T := by
      have hcardT : Nat.card T = orderOf s := Nat.card_zpowers s
      rw [hcardT, hn]
      exact ⟨2 ^ (n - 1), by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hnpos]⟩
    obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2dvd
    have htne : t ≠ 1 := by
      intro ht1
      have : orderOf t = 1 := by rw [ht1]; simp
      omega
    have ht2 : (t : T) ^ 2 = 1 := by
      rw [← htord]
      exact pow_orderOf_eq_one t
    have htSq : (t.1 : G) * t.1 = 1 := by
      have htmp : ((t : T) ^ 2 : S) = (1 : S) := congrArg Subtype.val ht2
      have htmp2 : (((t : T) ^ 2 : S) : G) = (1 : G) :=
        congrArg Subtype.val htmp
      simpa [pow_two] using htmp2
    have htI : IsInvolution (t : S) := by
      refine ⟨?_, ?_⟩
      · intro h
        exact htne (Subtype.ext h)
      · have htS : (t : S) * (t : S) = 1 := by
          apply Subtype.ext
          simpa using htSq
        simpa [pow_two] using htS
    have htG : IsInvolution (t.1 : G) := by
      refine ⟨?_, ?_⟩
      · intro h
        exact htne (Subtype.ext (Subtype.ext h))
      · simpa [pow_two] using htSq
    have htfix : t • x = x := by
      have hsStab : s ∈ MulAction.stabilizer S x :=
        MulAction.mem_stabilizer_iff.mpr hfix
      have hzpowStab : Subgroup.zpowers s ≤ MulAction.stabilizer S x :=
        Subgroup.zpowers_le.mpr hsStab
      have htStab : (t : S) ∈ MulAction.stabilizer S x :=
        hzpowStab t.property
      exact MulAction.mem_stabilizer_iff.mp htStab
    have htconj : (t.1 : G) * x.1 * (t.1 : G)⁻¹ = x.1 :=
      congrArg Subtype.val htfix
    have htinv : (t.1 : G)⁻¹ = t.1 :=
      inv_eq_of_mul_eq_one_right (by
        exact htSq)
    have hcomm : (t.1 : G) * x.1 = x.1 * t.1 := by
      calc
        (t.1 : G) * x.1 = ((t.1 : G) * x.1 * (t.1 : G)⁻¹) * t.1 := by group
        _ = x.1 * t.1 := by rw [htconj]
    have htsH : (t.1 : G) ∈ c.Hhat := hSleHhat' (t.1 : G) t.1.2
    let w : G := (t.1 : G) * x.1
    have hwJ : w ∈ firstCaseJ c 1 :=
      firstCase_klein_coset_representative_mem_J c htsH x.2
        hcomm htG
    have hwproj : cosetInvolution_proj c.Hhat w =
        cosetInvolution_proj c.Hhat x.1 := by
      change QuotientGroup.mk (w⁻¹) = QuotientGroup.mk (x.1⁻¹)
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have hwmem : w * x.1⁻¹ ∈ c.Hhat := by
        rw [show w * x.1⁻¹ = (t.1 : G) from (by dsimp [w]; group)]
        exact htsH
      simpa using hwmem
    have hwI : IsInvolution w := by
      refine ⟨?_, ?_⟩
      · intro hw1
        apply hxH
        have hEq : x.1 = (t.1 : G)⁻¹ * w := by
          dsimp [w]
          group
        rw [hEq, hw1, htinv]
        simpa using htsH
      · have hsq : w * w = 1 := by
          dsimp [w]
          calc
            ((t.1 : G) * x.1) * ((t.1 : G) * x.1) =
                (t.1 : G) * (x.1 * (t.1 : G)) * x.1 := by group
            _ = (t.1 : G) * ((t.1 : G) * x.1) * x.1 := by rw [hcomm]
            _ =
                (t.1 : G) * (t.1 : G) * (x.1 * x.1) := by
                  group
            _ = 1 := by
              have hxx : x.1 * x.1 = 1 := by
                simpa [pow_two] using hxI.2
              rw [htSq, hxx]
              simp
        simpa [pow_two] using hsq
    have hxcardInv : Nat.card {h : G // h ∈ invertedElements c.Hhat x.1} = 1 := by
      rw [← firstCase_klein_coset_involution_card_eq c hxI hxH]
      exact hxcard
    have hfiber : Nat.card (cosetInvolution_fiber c.Hhat
        (cosetInvolution_proj c.Hhat x.1)) = 1 := by
      rw [← firstCase_coset_fiber_card_eq c hxI]
      exact hxcard
    obtain ⟨z0, hz0⟩ := Nat.card_eq_one_iff_exists.mp hfiber
    have hEq1 : (⟨x.1, hxI, rfl⟩ : cosetInvolution_fiber c.Hhat
        (cosetInvolution_proj c.Hhat x.1)) = z0 := hz0 _
    have hEq2 : (⟨w, hwI, hwproj⟩ : cosetInvolution_fiber c.Hhat
        (cosetInvolution_proj c.Hhat x.1)) = z0 := hz0 _
    have hxw : x.1 = w := congrArg Subtype.val (hEq1.trans hEq2.symm)
    have ht1 : (t.1 : G) = 1 := by
      calc
        (t.1 : G) = (t.1 : G) * 1 := by simp
        _ = (t.1 : G) * (x.1 * x.1) := by
          rw [show x.1 * x.1 = 1 from (by simpa [pow_two] using hxI.2)]
        _ = (t.1 : G) * x.1 * x.1 := by group
        _ = w * x.1 := by
          rfl
        _ = x.1 * x.1 := by rw [hxw]
        _ = 1 := by simpa [pow_two] using hxI.2
    exact htne (Subtype.ext (Subtype.ext ht1))
  let : Fintype S := Fintype.ofFinite _
  let : Fintype J1 := Fintype.ofFinite _
  have hdvd : Nat.card S ∣ Nat.card J1 :=
    natCard_dvd_of_free_action (G := S) (X := J1) hfree
  have hS8 : Nat.card S = 8 := firstCase_klein_S_card hmin c hfirst hklein
  have hJ1 : Nat.card J1 = b1 := by
    have h1 := hJn 1 (by norm_num)
    simpa [J1, firstCaseBn] using h1
  rw [hS8, hJ1] at hdvd
  simpa using hdvd

end CFSG.GorensteinWalter
