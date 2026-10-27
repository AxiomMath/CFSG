module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43ExtB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Fam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67S3
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V : Subgroup G} {g : G}

private theorem s16c1G43_KOf_le_LOf (M V : Subgroup G) (g : G) :
    KOf M V g ≤ LOf V g := by
  unfold KOf LOf UOf BOf
  exact sup_le_sup inf_le_left inf_le_left

private theorem s16c1G43_BOf_le_normalizer_UOf (h : Hyp612Sym n M V g) :
    BOf M V g ≤ normalizer (UOf M V g : Set G) := by
  have hconj : ∀ b ∈ BOf M V g, ∀ u ∈ UOf M V g, b * u * b⁻¹ ∈ UOf M V g := by
    intro b hb u hu
    have hN : ⁅u, b⁆ ∈ NOf M V g := h.commutator_mem_N hu hb
    have hcU : ⁅b, u⁆ ∈ UOf M V g := by
      have h1 : ⁅u, b⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem hN
      have h2 : ⁅u, b⁆⁻¹ ∈ UOf M V g := (Subgroup.mem_inf.1 h1).1
      rwa [commutatorElement_inv u b] at h2
    have hbub : b * u * b⁻¹ = ⁅b, u⁆ * u := by
      rw [commutatorElement_def]; group
    rw [hbub]
    exact (UOf M V g).mul_mem hcU hu
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hconj b hb u
  · intro hbu
    have h := hconj b⁻¹ ((BOf M V g).inv_mem hb) (b * u * b⁻¹) hbu
    rwa [show b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u by group] at h

private theorem s16c1G43_KOf_coe_eq_mul (h : Hyp612Sym n M V g) :
    (KOf M V g : Set G) = (BOf M V g : Set G) * (UOf M V g : Set G) := by
  change ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) =
    (BOf M V g : Set G) * (UOf M V g : Set G)
  rw [sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right (BOf M V g) (UOf M V g)
    (s16c1G43_BOf_le_normalizer_UOf h)

private theorem s16c1G43_mQuot_eq_one (h : Hyp612Sym n M V g) (hV64 : Nat.card ↥V = 64)
    (hU : Nat.card ↥(UOf M V g) = 32) : E3.mQuot V (conjSubgroup M g) = 1 := by
  have hcard : Nat.card ↥(conjSubgroup M g ⊓ V) = 32 := by
    rw [inf_comm]
    exact hU
  have hmul : (conjSubgroup M g).relIndex V * 32 = 64 := by
    have h := Subgroup.relIndex_mul_card (H := conjSubgroup M g) (K := V)
    rwa [hcard, hV64] at h
  have hrel : (conjSubgroup M g).relIndex V = 2 := by omega
  unfold E3.mQuot
  rw [hrel]
  exact padicValNat_self

private theorem s16c1G43_inf_centralizer_eq (h : Hyp612Sym n M V g) :
    V ⊓ centralizer ((BOf M V g : Subgroup G) : Set G) = (V ⊓ conjSubgroup V g) ⊔ ⊥ := by
  rw [sup_bot_eq]
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_inf.2 ⟨hx.1, h.centralizer_le hx⟩
  · intro x hx
    refine Subgroup.mem_inf.2 ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.elemAbelian_conj.comm hb.1 hx.2

theorem s16c1G43_asm {M V : Subgroup G} {g : G} (h : Hyp612Sym 1 M V g)
    (hV64 : Nat.card ↥V = 64) (hU : Nat.card ↥(UOf M V g) = 32)
    (hB : Nat.card ↥(BOf M V g) = 32) (hN : Nat.card ↥(NOf M V g) = 2)
    (hTI : ∀ x : G, conjSubgroup V x ≠ V → Nat.card ↥(V ⊓ conjSubgroup V x) ≤ 4) :
    InCalOStar 1 M ⊥ V g ∧ IsQ8FourDih ↥(V ⊔ conjSubgroup V g) := by
  haveI : ((KOf M V g).subgroupOf (V ⊔ conjSubgroup V g)).Normal := h.normal_KOf
  have hW64 : Nat.card ↥(conjSubgroup V g) = 64 := (E3.card_conjSubgroup V g).trans hV64
  have hVK : Nat.card ↥(V ⊓ KOf M V g) = 32 := by
    rw [h.V_inf_KOf]; exact hU
  have hWK : Nat.card ↥(conjSubgroup V g ⊓ KOf M V g) = 32 := by
    rw [h.conjV_inf_KOf]; exact hB
  have hU' : Nat.card ↥(V ⊓ conjSubgroup M g) = 32 := hU
  have hN' : Nat.card ↥(V ⊓ conjSubgroup V g) = 2 := by
    rw [← h.NOf_eq_inf]; exact hN
  have hVnK : ¬ V ≤ KOf M V g := by
    intro hle
    have h1 : V ⊓ KOf M V g = V := le_antisymm inf_le_left (le_inf le_rfl hle)
    rw [h1, hV64] at hVK
    exact absurd hVK (by decide)
  have hWnK : ¬ conjSubgroup V g ≤ KOf M V g := by
    intro hle
    have h1 : conjSubgroup V g ⊓ KOf M V g = conjSubgroup V g :=
      le_antisymm inf_le_left (le_inf le_rfl hle)
    rw [h1, hW64] at hWK
    exact absurd hWK (by decide)
  obtain ⟨v, hvV, hvK⟩ := SetLike.not_le_iff_exists.1 hVnK
  obtain ⟨w, hwW, hwK⟩ := SetLike.not_le_iff_exists.1 hWnK
  have hvsq : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hvV
  have hwsq : w * w = 1 := by simpa [pow_two] using h.elemAbelian_conj.2 w hwW
  have hVcos : ∀ x ∈ V, x ∉ KOf M V g → v⁻¹ * x ∈ KOf M V g :=
    fun x hx hxK => s16c1G43_coset_of_card hV64 hVK hvV hx hvK hxK
  have hWcos : ∀ x ∈ conjSubgroup V g, x ∉ KOf M V g → w⁻¹ * x ∈ KOf M V g :=
    fun x hx hxK => s16c1G43_coset_of_card hW64 hWK hwW hx hwK hxK
  have hKnorm : ∀ l ∈ V ⊔ conjSubgroup V g, ∀ k ∈ KOf M V g,
      l * k * l⁻¹ ∈ KOf M V g := by
    intro l hl k hk
    have hl' : l ∈ LOf V g := by simpa [LOf] using hl
    exact (Subgroup.mem_normalizer_iff.1 (h.LOf_le_normalizer_KOf hl') k).1 hk
  have hNcent : ∀ n ∈ NOf M V g, ∀ l ∈ V ⊔ conjSubgroup V g, l * n = n * l := by
    intro n hn l hl
    have hl' : l ∈ LOf V g := by simpa [LOf] using hl
    exact (h.mul_comm_of_mem_NOf hn hl').symm
  have hKcomm : ∀ k ∈ KOf M V g, ∀ k' ∈ KOf M V g, ⁅k, k'⁆ ∈ NOf M V g :=
    fun k hk k' hk' => h.commutator_KOf_KOf_mem_N hk hk'
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => h.elemAbelian.comm hx hy
  have hVsq : ∀ x ∈ V, x * x = 1 :=
    fun x hx => by simpa [pow_two] using h.elemAbelian.2 x hx
  have hBV : ∀ x ∈ V, x ∉ KOf M V g → ∀ k ∈ KOf M V g,
      ⁅k, x⁆ ∈ NOf M V g → k ∈ V := by
    intro x hx hxK k hk hc
    have hxU : x ∉ UOf M V g := by
      intro hxu
      exact hxK (by rw [KOf]; exact Subgroup.mem_sup_left hxu)
    exact (show UOf M V g ≤ V from inf_le_left)
      (h.mem_UOf_of_commutator_mem_N hx hxU hk hc)
  have hBW : ∀ x ∈ conjSubgroup V g, x ∉ KOf M V g → ∀ k ∈ KOf M V g,
      ⁅k, x⁆ ∈ NOf M V g → k ∈ conjSubgroup V g := by
    intro x hx hxK k hk hc
    have hxB : x ∉ BOf M V g := by
      intro hxb
      exact hxK (by rw [KOf]; exact Subgroup.mem_sup_right hxb)
    exact (show BOf M V g ≤ conjSubgroup V g from inf_le_left)
      (h.mem_BOf_of_commutator_mem_N hx hxB hk hc)
  have hR := s16c1G43_fam (V := V) (g := g) (L := V ⊔ conjSubgroup V g)
    (K := KOf M V g) (N := NOf M V g) le_sup_left le_sup_right hKnorm hNcent hKcomm
    hVab hVsq hV64 hVK hWK hBV hBW hTI
  obtain ⟨m, hm, he, htwo, l, hl, hWV⟩ :=
    s16c1G43_quot (V := V) (g := g) (K := KOf M V g) hvV hwW hvK hwK hvsq hwsq
      hVcos hWcos hR
  have hmq : E3.mQuot V (conjSubgroup M g) = 1 := s16c1G43_mQuot_eq_one h hV64 hU
  have hquot : QuotShape (V ⊔ conjSubgroup V g) (KOf M V g)
      (E3.mQuot V (conjSubgroup M g)) :=
    ⟨Or.inr (Or.inr ⟨m, hm, he⟩), htwo.trans hmq.symm⟩
  have hset : (KOf M V g : Set G) =
      ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) *
        ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) :=
    s16c1G43_KOf_coe_eq_mul h
  have hcomm : ⁅conjSubgroup (⊥ : Subgroup G) g, V⁆ ≤ (⊥ : Subgroup G) := by
    rw [E3.conjSubgroup_bot, commutator_bot_left]
  have hcent : V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) =
      (V ⊓ conjSubgroup V g) ⊔ (⊥ : Subgroup G) :=
    s16c1G43_inf_centralizer_eq h
  have hne : (V ⊓ conjSubgroup V g) ⊔ (⊥ : Subgroup G) ≠ V ⊓ conjSubgroup M g := by
    intro heq
    have hc := congrArg (fun S : Subgroup G => Nat.card ↥S) heq
    rw [sup_bot_eq, hN', hU'] at hc
    omega
  have hKL : KOf M V g ≤ V ⊔ conjSubgroup V g := by
    simpa [LOf] using s16c1G43_KOf_le_LOf M V g
  have hext : IsExtraspecialPlus2
      ↥((KOf M V g).subgroupOf (V ⊔ conjSubgroup V g)) 4 :=
    isExtraspecialPlus2_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm
      (s16c1G43_extraspecial_of_hyp h hU hB hN)
  exact ⟨⟨h.inCalO, KOf M V g, h.normal_KOf, hset, hquot, ⟨l, hl, hWV⟩, hcomm, hcent, hne⟩,
    ⟨_, h.normal_KOf, hext, m, hm, he⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
