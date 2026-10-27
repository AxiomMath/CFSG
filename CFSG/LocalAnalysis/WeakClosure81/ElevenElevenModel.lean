module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenLine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_exists_model {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    ∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
      (ψ : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 2))
      (p : Projectivization (GaloisField 2 2) (Fin 2 → GaloisField 2 2)),
      Function.Surjective α ∧ α.ker = (oTwoIn L).subgroupOf L ∧
      Function.Surjective ψ ∧ ψ.ker = (blockZ L).subgroupOf (blockU L) ∧
      (∀ (e : ↥L) (w : ↥(blockU L)) (hw : (e : G) * w * (e : G)⁻¹ ∈ blockU L),
        ψ ⟨(e : G) * w * (e : G)⁻¹, hw⟩ = Multiplicative.ofAdd
          (((α e : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
              (Multiplicative.toAdd (ψ w)))) ∧
      ((L ⊓ Q).subgroupOf L).map α = CFSG.QuasithinUnique.Setup.Campbell.rootGrp p ∧
      (∀ w : Fin 2 → GaloisField 2 2,
        (∃ u : ↥(blockU L), (u : G) ∈ V ∧ Multiplicative.toAdd (ψ u) = w) ↔
          w ∈ p.submodule) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ :=
    CGT6.isNatSL_blockU hLb.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L :=
    eleven_nine_ker_eq hLb.2.2.1 h78.2.1 hαker
  obtain ⟨p, hαS⟩ :=
    eleven_nine_root_point hd.setting hUΓ hLb hLM h78 hαsurj hαker'
  obtain ⟨-, hfix⟩ := eleven_nine_fixed_line hd.setting hUΓ hLb hLM h78 hd.isHall
    hαsurj hαker hαS hψker hψeq
  exact ⟨α, ψ, p, hαsurj, hαker', hψsurj, hψker, hψeq, hαS, hfix⟩

theorem eleven11_card_blockU {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Nat.card (blockU L : Subgroup G) = 16 * Nat.card (blockZ L : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, p, hαsurj, hαker, hψsurj, hψker, hψeq, hαS, hfix⟩ :=
    eleven11_exists_model hd h8
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
  rw [hψker] at hcard
  have hker : Nat.card ((blockZ L).subgroupOf (blockU L)) = Nat.card (blockZ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockZ_le_blockU L)).toEquiv
  have hmod : Nat.card (Multiplicative (Fin 2 → GaloisField 2 2)) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd,
      CFSG.QuasithinUnique.Setup.Campbell.card_fin_two_pi,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [hker, hmod] at hcard
  rw [Nat.mul_comm] at hcard
  exact hcard.symm

theorem eleven11_inf_centralizerModCore {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    (L ⊓ Q) ⊓ centralizerModCore L = oTwoIn L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, p, hαsurj, hαker, hψsurj, hψker, hψeq, hαS, hfix⟩ :=
    eleven11_exists_model hd h8
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hO2Q : oTwoIn L ≤ Q := eleven_nine_oTwoIn_le_Q hd.setting hUΓ hLb
  refine le_antisymm ?_ ?_
  · intro t ht
    obtain ⟨htLQ, htC⟩ := Subgroup.mem_inf.1 ht
    obtain ⟨htL, htQ⟩ := Subgroup.mem_inf.1 htLQ
    let t' : ↥L := ⟨t, htL⟩
    have hcenter : α t' ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hαsurj g
      have hmem : t' * y * t'⁻¹ * y⁻¹ ∈ α.ker := by
        rw [hαker]
        exact Subgroup.mem_subgroupOf.mpr (by simpa using htC.2 y y.2)
      have h1 : α t' * α y * (α t')⁻¹ * (α y)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using MonoidHom.mem_ker.mp hmem
      have h2 : α t' * α y * (α y * α t')⁻¹ = 1 := by
        simpa [mul_inv_rev, mul_assoc] using h1
      exact (mul_inv_eq_one.mp h2).symm
    obtain ⟨r, hrpow, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
    have hrpow' : r ^ 2 = 1 := by simpa using hrpow
    have hsq : (r + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hrpow', one_pow]
      exact CharTwo.add_eq_zero.mpr rfl
    have hr1 : r = 1 :=
      CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq)
    have hmat : (↑(α t') : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = 1 := by
      rw [← hr, hr1]
      simp
    have hαt : α t' = 1 := Subtype.ext (by simpa using hmat)
    have ht'ker : t' ∈ α.ker := MonoidHom.mem_ker.mpr hαt
    rw [hαker] at ht'ker
    exact Subgroup.mem_subgroupOf.mp ht'ker
  · intro g hg
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨oTwoIn_le L hg, hO2Q hg⟩, ?_⟩
    refine ⟨Subgroup.le_normalizer (oTwoIn_le L hg), ?_⟩
    intro x hx
    have hconj : x * g⁻¹ * x⁻¹ ∈ oTwoIn L :=
      conj_mem_oTwoIn (Subgroup.le_normalizer hx) (inv_mem hg)
    simpa only [mul_assoc] using mul_mem hg hconj

theorem eleven11_card_sylow {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Nat.card (L ⊓ Q : Subgroup G) = 4 * Nat.card (oTwoIn L : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, p, hαsurj, hαker, hψsurj, hψker, hψeq, hαS, hfix⟩ :=
    eleven11_exists_model hd h8
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hO2Q : oTwoIn L ≤ Q := eleven_nine_oTwoIn_le_Q hd.setting hUΓ hLb
  have hkerle : α.ker ≤ (L ⊓ Q).subgroupOf L := by
    intro x hx
    rw [hαker] at hx
    have hxO : (x : G) ∈ oTwoIn L := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨oTwoIn_le L hxO, hO2Q hxO⟩)
  have hrel : α.ker.relIndex ((L ⊓ Q).subgroupOf L) = 4 := by
    rw [Subgroup.relIndex_ker ((L ⊓ Q).subgroupOf L) α, hαS,
      CFSG.QuasithinUnique.Setup.Campbell.card_rootGrp,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hkerα : Nat.card α.ker = Nat.card (oTwoIn L : Subgroup G) := by
    rw [hαker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoIn_le L)).toEquiv
  have hcardS : Nat.card ((L ⊓ Q).subgroupOf L) = Nat.card (L ⊓ Q : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmain := Subgroup.relIndex_mul_card (α.ker) ((L ⊓ Q).subgroupOf L)
  rw [inf_eq_left.mpr hkerle, hrel, hkerα, hcardS] at hmain
  exact hmain.symm

theorem eleven11_exists_elem {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    ∃ t ∈ L ⊓ Q, t ∉ oTwoIn L := by
  classical
  by_contra h
  have hle : L ⊓ Q ≤ oTwoIn L := by
    intro t ht
    by_contra htO
    exact h ⟨t, ht, htO⟩
  have hcard := Subgroup.card_le_of_le hle
  have hsylow := eleven11_card_sylow hd h8
  have hpos : 0 < Nat.card (oTwoIn L : Subgroup G) := Nat.card_pos
  rw [hsylow] at hcard
  omega

end CFSG.LocalAnalysis.WeakClosure81
