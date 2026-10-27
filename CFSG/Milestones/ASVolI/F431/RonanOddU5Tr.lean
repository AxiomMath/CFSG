module

public import CFSG.Milestones.ASVolI.F431.Final
public import CFSG.Milestones.ASVolI.F431.J3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Tr

set_option linter.unusedSectionVars false


variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem ronOdd5_transfer (hyp : HypF_4_31 .U5 1 Gp M₁ M₂ β ε z) {s : E} (hsM : s ∈ M₁ ⊓ M₂)
    (hsG : s ∉ Gp) (hs2 : s * s = 1) (hidx : ∀ e : E, e ∉ Gp → e * s ∈ Gp)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) (hsT : s ∈ Tb)
    (hfus0 : ∀ (g : M) (x : ↥(M₁ ⊓ M₂)), (x : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → x ≠ 1 →
      x * x = 1 → bM β ε x ≠ g⁻¹ * bM β ε ⟨s, hsM⟩ * g) : False := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set b1 := burnsideF4d_bOne β ε with hb1def
  have hb1 : Function.Injective b1 := burnsideF4j_bOne_injective hyp
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS1 : S ≤ M₁ := fun x hx => (hSB hx).2.1
  have hTb12 : Tb ≤ M₁ ⊓ M₂ := hTb.1
  have hTb1 : Tb ≤ M₁ := hTb12.trans inf_le_left
  have hSTb : S ≤ Tb := burnsideF4j_S_le_sylow hyp.amalgam hTb
  have hTbGp : Tb ⊓ Gp = S := burnsideF4j_sylow_inf_Gp hyp.amalgam hTb
  have hTbS : ∀ a ∈ Tb, a ∈ S ∨ a * s ∈ S := by
    intro a ha
    by_cases haG : a ∈ Gp
    · left
      rw [← hTbGp]
      exact ⟨ha, haG⟩
    · right
      rw [← hTbGp]
      exact ⟨Tb.mul_mem ha hsT, hidx a haG⟩
  set T := subImg b1 Tb with hTdef
  set N := subImg b1 S with hNdef
  set t := b1 ⟨s, hsM.1⟩ with htdef
  have htbM : t = bM β ε ⟨s, hsM⟩ := (burnsideF4j_bM_eq_bOne β ε ⟨s, hsM⟩).symm
  have hT12 : IsSylowTwoOf T (MiOne β ε ⊓ MiTwo β ε) := by
    rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj]
    exact (burnsideF4j_isSylow_subImg_iff _ hb1 hTb1 inf_le_left).2 hTb
  have hT : IsSylowTwoOf T ⊤ := burnsideF4m_F_4_33 .U5 1 E Gp M₁ M₂ Y β M ε z hyp T hT12
  have hNT : N ≤ T := subImg_mono b1 hSTb
  have hTN : T ≤ Subgroup.normalizer (N : Set M) := by
    intro y hy
    obtain ⟨a, haM, haT, rfl⟩ := mem_subImg.mp hy
    have haN : a ∈ Subgroup.normalizer (S : Set E) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
        (burnsideF4j_le_normalizer_inf hyp.amalgam.normal (M₁ ⊓ M₂) (hTb12 haT))
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨x, hxM, hxS, rfl⟩ := mem_subImg.mp hw
      have hx' : a * x * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp haN x).mp hxS
      refine mem_subImg.mpr ⟨a * x * a⁻¹, hS1 hx', hx', ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    · intro hw
      obtain ⟨x, hxM, hxS, hxe⟩ := mem_subImg.mp hw
      have hax : a⁻¹ * x * a ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) x).mp hxS
        simpa only [inv_inv] using this
      refine mem_subImg.mpr ⟨a⁻¹ * x * a, hS1 hax, hax, ?_⟩
      have e1 : b1 ⟨a⁻¹ * x * a, hS1 hax⟩ =
          (b1 ⟨a, haM⟩)⁻¹ * b1 ⟨x, hxM⟩ * b1 ⟨a, haM⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1, hxe]
      group
  have hcyc : T = N ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, haM, haT, rfl⟩ := mem_subImg.mp hy
      rcases hTbS a haT with haS | haS
      · exact (le_sup_left : N ≤ N ⊔ Subgroup.zpowers t) (mem_subImg_of_mem b1 haM haS)
      · have e1 : b1 ⟨a, haM⟩ = b1 ⟨a * s, hS1 haS⟩ * t := by
          rw [htdef, ← map_mul]
          congr 1
          apply Subtype.ext
          show a = a * s * s
          rw [mul_assoc, hs2, mul_one]
        rw [e1]
        exact Subgroup.mul_mem _
          ((le_sup_left : N ≤ N ⊔ Subgroup.zpowers t) (mem_subImg_of_mem b1 (hS1 haS) haS))
          ((le_sup_right : Subgroup.zpowers t ≤ N ⊔ Subgroup.zpowers t)
            (Subgroup.mem_zpowers t))
    · exact sup_le hNT ((Subgroup.zpowers_le (H := T)).mpr (mem_subImg_of_mem b1 hsM.1 hsT))
  have htT : t ∈ T := mem_subImg_of_mem b1 hsM.1 hsT
  have htN : t ∉ N := by
    intro htN
    obtain ⟨x, hxM, hxS, hxe⟩ := mem_subImg.mp htN
    have : (⟨x, hxM⟩ : ↥M₁) = ⟨s, hsM.1⟩ := hb1 hxe
    apply hsG
    have hxs : x = s := congrArg Subtype.val this
    rw [← hxs]
    exact (hSB hxS).1
  have ht2 : t ^ 2 = 1 := by
    rw [htdef, ← map_pow, pow_two]
    have : (⟨s, hsM.1⟩ : ↥M₁) * ⟨s, hsM.1⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hfus : ∀ g : M, g⁻¹ * t * g ∉ N := by
    intro g hg
    obtain ⟨x, hxM, hxS, hxe⟩ := mem_subImg.mp hg
    have hx12 : x ∈ M₁ ⊓ M₂ := (hSB hxS).2
    have hxe' : bM β ε ⟨x, hx12⟩ = g⁻¹ * t * g := by
      rw [burnsideF4j_bM_eq_bOne]
      exact hxe
    have hx1 : (⟨x, hx12⟩ : ↥(M₁ ⊓ M₂)) ≠ 1 := by
      intro h0
      have hx0 : x = 1 := congrArg Subtype.val h0
      apply htN
      have e1 : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      rw [e1, ← hxe]
      have : (⟨x, hxM⟩ : ↥M₁) = 1 := Subtype.ext hx0
      rw [this, map_one, mul_one, mul_inv_cancel]
      exact N.one_mem
    have hx2 : (⟨x, hx12⟩ : ↥(M₁ ⊓ M₂)) * ⟨x, hx12⟩ = 1 := by
      have h1 : b1 ⟨x, hxM⟩ * b1 ⟨x, hxM⟩ = 1 := by
        rw [hxe]
        have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
        calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [ht2']; group
      rw [← map_mul, ← map_one b1] at h1
      have h2 : x * x = 1 := congrArg Subtype.val (hb1 h1)
      exact Subtype.ext h2
    exact hfus0 g ⟨x, hx12⟩ hxS hx1 hx2 (by rw [hxe', htbM])
  have hres : oTwoRes (⊤ : Subgroup M) = ⊤ := by
    rcases hyp.he with h | ⟨-, h⟩
    · exact h
    · exfalso
      rcases h with h | h | h <;> exact absurd h (by decide)
  exact CFSG.QuasithinUnique.Lin2.burnsideF4m_transfer_contradiction_cyclic_oTwoRes hres hT hNT
    hTN hcyc htT htN ht2 hfus

end Tr

end CFSG.ASVolI
