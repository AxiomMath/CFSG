module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Fi22
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3OuterIdx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Fi22Tri
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem m4_conj_centre_eq_or_inv {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    {ζ : ↥L} (hζ : ζ ∈ Subgroup.center ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hζ1 : ζ ≠ 1) :
    ∀ y ∈ Y, y * (ζ : MulAut W) * y⁻¹ = (ζ : MulAut W) ∨
      y * (ζ : MulAut W) * y⁻¹ = (ζ : MulAut W)⁻¹ := by
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : (⟨ζ, hζ⟩ : Subgroup.center ↥L) ^ Nat.card (Subgroup.center ↥L) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hcen : Subgroup.center ↥L = Subgroup.zpowers ζ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζ) ?_
    rw [Nat.card_zpowers, hord, hZ]
  intro y hy
  have hLnorm : ∀ z ∈ Y, ∀ l ∈ L, z * l * z⁻¹ ∈ L := by
    intro z hz l hl
    exact Subgroup.mem_subgroupOf.1
      (hLn.conj_mem ⟨l, hLY hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨z, hz⟩)
  let ζ'' : ↥L := ⟨y * (ζ : MulAut W) * y⁻¹, hLnorm y hy ζ ζ.2⟩
  have hζ''ne : ζ'' ≠ 1 := by
    intro h
    apply hζ1
    have hval : (ζ'' : MulAut W) = 1 := congrArg Subtype.val h
    have h2 : y⁻¹ * (y * (ζ : MulAut W) * y⁻¹) * y = (ζ : MulAut W) := by group
    have hval' : y * (ζ : MulAut W) * y⁻¹ = 1 := hval
    rw [hval'] at h2
    simpa using h2.symm
  have hζ''cen : ζ'' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    change (l : MulAut W) * (y * (ζ : MulAut W) * y⁻¹) =
      (y * (ζ : MulAut W) * y⁻¹) * (l : MulAut W)
    have hcomm : (y⁻¹ * (l : MulAut W) * y) * (ζ : MulAut W) =
        (ζ : MulAut W) * (y⁻¹ * (l : MulAut W) * y) := by
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hζ
        ⟨y⁻¹ * (l : MulAut W) * y, hLnorm y⁻¹ (Y.inv_mem hy) l l.2⟩)
      simpa using h
    calc (l : MulAut W) * (y * (ζ : MulAut W) * y⁻¹)
        = y * ((y⁻¹ * (l : MulAut W) * y) * (ζ : MulAut W)) * y⁻¹ := by group
      _ = y * ((ζ : MulAut W) * (y⁻¹ * (l : MulAut W) * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * (ζ : MulAut W) * y⁻¹) * (l : MulAut W) := by group
  have hζ''zp : ζ'' ∈ Subgroup.zpowers ζ := hcen ▸ hζ''cen
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hζ''zp
  have hk3 : ζ ^ (k % 3) = ζ'' := by
    rw [← hk, ← zpow_mod_orderOf ζ k, hord]
    rfl
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk3
    exact hζ''ne hk3.symm
  · left
    rw [h1, zpow_one] at hk3
    exact congrArg Subtype.val hk3.symm
  · right
    rw [h2] at hk3
    have hζ2inv : ζ ^ (2 : ℤ) = ζ⁻¹ := by
      have h2' : ζ ^ (2 : ℤ) * ζ = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hζ3]
      exact eq_inv_of_mul_eq_one_left h2'
    have hinv : ζ'' = ζ⁻¹ := by rw [← hk3]; exact hζ2inv
    simpa using congrArg Subtype.val hinv

theorem w4Fi22RowM4CentreThree_holds :
    W4Fi22RowM4CentreThree := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hZ hs
  obtain ⟨e⟩ := hs
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hne : Subgroup.center ↥L ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(Subgroup.center ↥L) = 1 := by rw [h, Subgroup.card_bot]
    rw [hZ] at h1
    norm_num at h1
  obtain ⟨ζ₀, hζ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  let ζ : ↥L := ζ₀
  have hζ : ζ ∈ Subgroup.center ↥L := ζ₀.2
  have hζ1 : ζ ≠ 1 := fun h => hζ₀1 (Subtype.ext h)
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : (⟨ζ, hζ⟩ : Subgroup.center ↥L) ^ Nat.card (Subgroup.center ↥L) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hcen : Subgroup.center ↥L = Subgroup.zpowers ζ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζ) ?_
    rw [Nat.card_zpowers, hord, hZ]
  let ζ' : MulAut W := (ζ : MulAut W)
  have hζY : ζ' ∈ Y := hLY ζ.2
  have hζ3' : ζ' ^ 3 = 1 := by
    change (Subgroup.subtype L ζ) ^ 3 = 1
    rw [← map_pow, hζ3, map_one]
  have hζ1' : ζ' ≠ 1 := fun h => hζ1 (Subtype.ext h)
  have hnorm : ∀ y ∈ Y, y * ζ' * y⁻¹ = ζ' ∨ y * ζ' * y⁻¹ = ζ'⁻¹ :=
    m4_conj_centre_eq_or_inv hLY hLn hζ hZ hζ1
  obtain ⟨U, hUc, hUf, ρ, hU, hnt, hfixU, hdisp⟩ :=
    exists_fpf_module_of_order_three hW' hζY hζ3' hζ1' hnorm
  letI : CommGroup U := hUc
  letI : Finite U := hUf
  haveI : Nontrivial U := hnt
  let ρL : ↥L →* MulAut U := ρ.comp (Subgroup.inclusion hLY)
  have hargζ : Subgroup.inclusion hLY ζ = ⟨ζ', hζY⟩ := Subtype.ext rfl
  have hρeqζ : ρL ζ = ρ ⟨ζ', hζY⟩ := by
    change ρ (Subgroup.inclusion hLY ζ) = ρ ⟨ζ', hζY⟩
    rw [hargζ]
  have hfixL : ∀ u : U, ρL ζ u = u → u = 1 := by
    intro u hu
    rw [hρeqζ] at hu
    exact hfixU u hu
  have hζρne : ρL ζ ≠ 1 := by
    intro h
    obtain ⟨u, v, huv⟩ := exists_pair_ne U
    apply huv
    rw [hfixL u (by rw [h]; rfl), hfixL v (by rw [h]; rfl)]
  have hNbot : ρL.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ρL.normal_ker with htop | hNle
    · exfalso
      have hmem : ζ ∈ ρL.ker := by rw [htop]; exact Subgroup.mem_top ζ
      exact hζρne (MonoidHom.mem_ker.1 hmem)
    · have hNle' : ρL.ker ≤ Subgroup.zpowers ζ := by
        intro z hz
        rw [← hcen]
        exact hNle hz
      have hcarddvd : Nat.card ↥(ρL.ker) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hNle'
        rwa [Nat.card_zpowers, hord] at h
      have hcardN : Nat.card ↥(ρL.ker) = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hcarddvd with h1 | h3
        · exact h1
        · exfalso
          have heq : ρL.ker = Subgroup.zpowers ζ :=
            Subgroup.eq_of_le_of_card_ge hNle' (by rw [h3, Nat.card_zpowers, hord])
          have hmem : ζ ∈ ρL.ker := by rw [heq]; exact Subgroup.mem_zpowers ζ
          exact hζρne (MonoidHom.mem_ker.1 hmem)
      exact Subgroup.mem_bot.1 (Subgroup.eq_bot_of_card_eq ρL.ker hcardN ▸ hx)
  have hρL : Function.Injective ρL := (MonoidHom.ker_eq_bot_iff ρL).1 hNbot
  have h54 : 2 ^ 54 ≤ Nat.card U :=
    two_pow_fifty_four_le_card_of_cover hU ρL hρL e hZ hζ hζ1 hfixL
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := by
      change 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Fi22
      rw [CFSG.Sporadic.Fi22.card_Fi22]
      norm_num
    have hS : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) ∣ Nat.card ↥L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (h2S.trans hS)
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  refine le_mParam_of_index_sq (ρ := 4) hW' hY2 fun t htY hto => ?_
  have ht2 : t * t = 1 := by
    rw [← sq, ← hto]
    exact pow_orderOf_eq_one t
  have hdisp' : (fixV (zpowers (ρ ⟨t, htY⟩))).index ≤ (fixV (zpowers t)).index :=
    hdisp ⟨t, htY⟩
  suffices hkey : 2 ^ 4 ≤ (fixV (zpowers (ρ ⟨t, htY⟩))).index by
    have hkey2 : 2 ^ 4 ≤ (fixV (zpowers t)).index := hkey.trans hdisp'
    calc 2 ^ (2 * 4) = (2 ^ 4) ^ 2 := by rw [← pow_mul]
      _ ≤ (fixV (zpowers t)).index ^ 2 := Nat.pow_le_pow_left hkey2 2
  by_cases htL : t ∈ L
  ·
    let tL : ↥L := ⟨t, htL⟩
    have ht2L : tL * tL = 1 := Subtype.ext ht2
    have hargt : Subgroup.inclusion hLY tL = ⟨t, htY⟩ := Subtype.ext rfl
    have hρeq : ρL tL = ρ ⟨t, htY⟩ := by
      change ρ (Subgroup.inclusion hLY tL) = ρ ⟨t, htY⟩
      rw [hargt]
    let φ : ↥L →* CFSG.Blueprint.NativeSporadic.Carrier .Fi22 :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hφs : Function.Surjective φ :=
      e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
    have hker : φ.ker = Subgroup.center ↥L := by
      ext k
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk k) = 1 ↔ k ∈ Subgroup.center ↥L
      rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
    have hφt2 : φ tL * φ tL = 1 := by rw [← map_mul, ht2L, map_one]
    have hφt1 : φ tL ≠ 1 := by
      intro h1
      have hmem : tL ∈ φ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at hmem
      have htoL : orderOf tL = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hto
      have hdvd : orderOf (⟨tL, hmem⟩ : ↥(Subgroup.center ↥L)) ∣
          Nat.card (Subgroup.center ↥L) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, htoL, hZ] at hdvd
      norm_num at hdvd
    have hw : InvolutionWitness (φ tL) := fi22_involutionWitness (φ tL) hφt2 hφt1
    have hinner : 2 ^ 4 ≤ (fixV (zpowers (ρL tL))).index :=
      two_pow_four_le_index_of_witness hU φ hφs hker hZ hq.1 ρL hρL hζ hζ1 hfixL h54 ht2L hw
    rwa [hρeq] at hinner
  · exact fi22_outer_index_ge_sixteen hLY hLn hF hq hZ e hU ρ hρL hζ hζ1 hfixL h54 htY hto htL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
