module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Closure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Core
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon Subgroup

private lemma mem_prodFst_iff {G S₀ : Type*} [Group G] [Group S₀] {H : Subgroup G}
    (g : ↥H →* S₀ × S₀) (h : ↥H) : (h : G) ∈ prodFst g ↔ (g h).2 = 1 := by
  rw [prodFst]
  constructor
  · intro hm
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hm
    have hk' : k = h := Subtype.ext hke
    rw [hk'] at hk
    simpa using hk
  · intro hh
    refine Subgroup.mem_map_of_mem _ ?_
    rw [MonoidHom.mem_ker]
    simpa using hh

private lemma mem_prodSnd_iff {G S₀ : Type*} [Group G] [Group S₀] {H : Subgroup G}
    (g : ↥H →* S₀ × S₀) (h : ↥H) : (h : G) ∈ prodSnd g ↔ (g h).1 = 1 := by
  rw [prodSnd]
  constructor
  · intro hm
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hm
    have hk' : k = h := Subtype.ext hke
    rw [hk'] at hk
    simpa using hk
  · intro hh
    refine Subgroup.mem_map_of_mem _ ?_
    rw [MonoidHom.mem_ker]
    simpa using hh

theorem le_conjClosure_of_swap {G : Type*} [Group G] {H : Subgroup G} (hH : ⁅H, H⁆ = H)
    {S₀ : Type*} [Group S₀] [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) {s : G}
    (hsN : s ∈ normalizer (H : Set G))
    (hswap : (prodFst g).map (MulAut.conj s).toMonoidHom = prodSnd g) :
    H ≤ conjClosure H s := by
  classical
  obtain ⟨x, hx1⟩ : ∃ x : S₀, x ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hS
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  obtain ⟨h₀, hh₀⟩ := hg (x, 1)
  have hmemF : (h₀ : G) ∈ prodFst g :=
    (mem_prodFst_iff g h₀).mpr (by rw [hh₀])
  have hmemS : s * (h₀ : G) * s⁻¹ ∈ prodSnd g := by
    have hconj : (MulAut.conj s).toMonoidHom (h₀ : G) ∈ prodSnd g := by
      rw [← hswap]
      exact Subgroup.mem_map_of_mem _ hmemF
    exact hconj
  have hmH : s * (h₀ : G) * s⁻¹ ∈ H := by
    have hm := hmemS
    rw [prodSnd] at hm
    obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp hm
    rw [← hk]
    exact k.2
  let h₁ : ↥H := ⟨s * (h₀ : G) * s⁻¹, hmH⟩
  have hh₁val : (h₁ : G) = s * (h₀ : G) * s⁻¹ := rfl
  have hh₁snd : (g h₁).1 = 1 := (mem_prodSnd_iff g h₁).mp hmemS
  let y : S₀ := (g h₁).2
  have hh₁ : g h₁ = (1, y) := Prod.ext hh₁snd rfl
  have hy1 : y ≠ 1 := by
    intro hy
    have hker₁ : h₁ ∈ g.ker := by
      rw [MonoidHom.mem_ker, hh₁, hy]
      rfl
    have hz₁ : h₁ ∈ center ↥H := hker hker₁
    have hz₀ : h₀ ∈ center ↥H := by
      refine (Subgroup.mem_center_iff).mpr ?_
      intro k
      have hz₁' := (Subgroup.mem_center_iff).mp hz₁
      let k' : ↥H := ⟨s * (k : G) * s⁻¹,
        (Subgroup.mem_normalizer_iff.mp hsN (k : G)).mp k.2⟩
      have hc : (k' : G) * (h₁ : G) = (h₁ : G) * (k' : G) :=
        congrArg Subtype.val (hz₁' k')
      have hc' : s * (k : G) * s⁻¹ * (s * (h₀ : G) * s⁻¹) =
          (s * (h₀ : G) * s⁻¹) * (s * (k : G) * s⁻¹) := by
        simpa only [k', hh₁val] using hc
      apply Subtype.ext
      show (k : G) * (h₀ : G) = (h₀ : G) * (k : G)
      calc
        (k : G) * (h₀ : G) =
            s⁻¹ * (s * (k : G) * s⁻¹ * (s * (h₀ : G) * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * (h₀ : G) * s⁻¹) * (s * (k : G) * s⁻¹)) * s := by rw [hc']
        _ = (h₀ : G) * (k : G) := by group
    have hcent : ∀ w : S₀ × S₀, g h₀ * w = w * g h₀ := by
      intro w
      obtain ⟨m, hm⟩ := hg w
      rw [← hm, ← map_mul, ← map_mul]
      exact congrArg g ((Subgroup.mem_center_iff.mp hz₀) m).symm
    have hxcent : x ∈ center S₀ := by
      refine (Subgroup.mem_center_iff).mpr ?_
      intro z
      have h := hcent (z, 1)
      rw [hh₀] at h
      exact (congrArg Prod.fst h).symm
    have hxbot : x ∈ (⊥ : Subgroup S₀) := by
      rw [← center_eq_bot_of_isSimpleGroup hS]
      exact hxcent
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  have hcK : (h₀ : G) * s * (h₀ : G)⁻¹ * s⁻¹ ∈ H ⊓ conjClosure H s :=
    commutator_mem_inf hsN h₀.2
  let c : ↥H := ⟨(h₀ : G) * s * (h₀ : G)⁻¹ * s⁻¹, hcK.1⟩
  have hc_eq : c = h₀ * h₁⁻¹ := by
    apply Subtype.ext
    show (h₀ : G) * s * (h₀ : G)⁻¹ * s⁻¹ = (h₀ : G) * (h₁ : G)⁻¹
    rw [hh₁val]
    group
  have hgc : g c = (x, y⁻¹) := by
    rw [hc_eq, map_mul, map_inv, hh₀, hh₁]
    simp
  have hgcN : g c ∈ ((H ⊓ conjClosure H s).subgroupOf H).map g :=
    Subgroup.mem_map_of_mem g hcK
  have hN : (((H ⊓ conjClosure H s).subgroupOf H).map g).Normal := by
    refine Subgroup.Normal.map ?_ g hg
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr ?_
    intro h k hh hk
    exact conj_mem_inf hk hh
  have htop : ((H ⊓ conjClosure H s).subgroupOf H).map g = ⊤ := by
    rcases normal_prod_cases hS hN with hbot | hsnd | hfst | htopN
    · exfalso
      rw [hbot, Subgroup.mem_bot, hgc] at hgcN
      exact hx1 (by simpa using congrArg Prod.fst hgcN)
    · exfalso
      rw [hsnd, MonoidHom.mem_ker, hgc] at hgcN
      have hyinv : y⁻¹ = 1 := by simpa using hgcN
      exact hy1 (inv_eq_one.mp hyinv)
    · exfalso
      rw [hfst, MonoidHom.mem_ker, hgc] at hgcN
      exact hx1 (by simpa using hgcN)
    · exact htopN
  exact le_conjClosure_of_map_eq_top hH g hker htop

theorem not_isTransvection_of_swap {B : Type} [CommGroup B] [Finite B] (hB : ∀ b : B, b ^ 2 = 1)
    {H : Subgroup (MulAut B)} (hH : ⁅H, H⁆ = H) {S₀ : Type} [Group S₀] [Finite S₀]
    [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) {s : MulAut B}
    (hsN : s ∈ normalizer (H : Set (MulAut B)))
    (hswap : (prodFst g).map (MulAut.conj s).toMonoidHom = prodSnd g) :
    ¬ UniquenessMaximal.IsTransvection s := by
  intro hs
  have hgen := le_conjClosure_of_swap hH hS g hg hker hsN hswap
  have hH1 : H ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hS
    obtain ⟨x, hx⟩ := hg (a, b)
    have hx1 : x = 1 := by
      have hxm : (x : MulAut B) ∈ (⊥ : Subgroup (MulAut B)) := hbot ▸ x.2
      exact Subtype.ext (Subgroup.mem_bot.mp hxm)
    rw [hx1, map_one] at hx
    have ha : a = 1 := (congrArg Prod.fst hx).symm
    have hb : b = 1 := (congrArg Prod.snd hx).symm
    exact hab (by rw [ha, hb])
  obtain ⟨T, _, _, ψ, hψ, hψk, hTnab, -⟩ := exists_mcLaughlin_quotient hB hH hH1 hs hsN hgen
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker hg hker
    (fun N hN h4 => eq_bot_of_pow_four_prod hS hN h4) hψ (center_eq_bot_of_isSimpleGroup hTnab)
    hψk
  exact not_isSimpleGroup_prod e.isSimpleGroup

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
