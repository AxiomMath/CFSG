module

public import CFSG.Quasithin.Background.SmithB42SL3Field
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.SmithB51SL3N
public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.H
open scoped Matrix

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem le_ffJ_of_odd_center (hB : B4Hyp G L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (hA : IsFFStarOffender G A) : L ≤ ffJ G := by
  obtain ⟨-, hLF, hq, -⟩ := hB
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hHG : ffJ G ≤ G := B6.ffJ_le G
  have hGH : G ≤ Subgroup.normalizer ((ffJ G) : Set (MulAut V)) := B6.le_normalizer_ffJ G
  have hqo := B1Red.isQuasisimple_to_open hq
  by_contra hLH
  have hcomm := B1Red.commute_of_normal_not_le hqo
    (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hGL (hHG hx)) l).mp hl)
    (fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hGH (hLG hl)) x).mp hx) hLH
  have hHL : ∀ x ∈ ffJ G, ∃ hxL : x ∈ L, (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcomm x hx l hl).symm
    have hxL : x ∈ L := hLF ▸ centralizer_quasithinGenFitting_le G ⟨hHG hx, hLF ▸ hxC⟩
    refine ⟨hxL, ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hcomm x hx l l.2).symm
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.2.1
  obtain ⟨haL, hz⟩ := hHL a.1 (B6.le_ffJ hA a.2)
  let z : ↥(Subgroup.center ↥L) := ⟨⟨a.1, haL⟩, hz⟩
  have hz1 : z ≠ 1 := by
    intro h
    apply ha1
    apply Subtype.ext
    have := congrArg (fun y : ↥(Subgroup.center ↥L) => ((y : ↥L) : MulAut V)) h
    simpa [z] using this
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [z] using hA.2.2.1.2 a.1 a.2
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥L) := hord ▸ orderOf_dvd_natCard z
  exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hdvd)

section Natural

variable {K : Type} [Field K] [Finite K]

@[expose] def plane (K : Type) [Field K] : Submodule K (Fin 3 → K) :=
  LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 2)

omit [Finite K] in
theorem finrank_plane : Module.finrank K (plane K) = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 2)
  have h2 : LinearMap.range (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 2) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single 2 c, by simp⟩
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  unfold plane
  omega

@[expose] noncomputable def natSecOf (π : ↥(StatedSL 3 K) →* ↥L) (hπ : Function.Surjective π)
    (e : V ≃* StdMod (Fin 3) K)
    (he : ∀ (γ : ↥(StatedSL 3 K)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 K) γ (e v)) :
    B5.NatSec L ⊤ ⊥ K where
  π := π
  hπ := by
    refine ⟨?_, hπ⟩
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply Subtype.ext
    apply Units.ext
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h1 := he γ (e.symm (Multiplicative.ofAdd v))
    rw [hγ, Subgroup.coe_one, MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [natAct, toAdd_ofAdd] at h2
    rw [← h2]
    simp
  f := e.toMonoidHom.comp (⊤ : Subgroup V).subtype
  hfs := fun x => ⟨⟨e.symm x, trivial⟩, by simp⟩
  hfk := fun u => by
    rw [Subgroup.mem_bot]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulEquivClass.map_eq_one_iff]
  hfe := fun γ u _ => he γ u

variable [CharP K 2]

theorem half_le_rAV_of_card {B : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hB : IsElemAbelian2 B) (hB1 : B ≠ ⊥)
    (h : Nat.card B * Nat.card ↥(fixV B) ^ 2 ≤ Nat.card V ^ 2) : (1 / 2 : ℚ) ≤ rAV B := by
  have h1 := rk_add_rkIdx (fixV B)
  have hV2 : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hF2 : Nat.card ↥(fixV B) = 2 ^ rk ↥(fixV B) := by
    refine card_eq_two_pow_of_isPGroup ?_
    exact IsPGroup.to_subgroup (isPGroup_two_of_sq_eq_one hV) _
  rw [B1.card_elemAbelian hB, hF2, hV2, ← pow_mul, ← pow_mul, ← pow_add] at h
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hrk : 0 < rk ↥B := (IsA2.rk_pos (X := ⊤) ⟨le_top, hB1, hB⟩)
  unfold rAV
  rw [le_div_iff₀ (by exact_mod_cast hrk)]
  have h3 : rk ↥B ≤ 2 * rkIdx (fixV B) := by omega
  have h4 : ((rk ↥B : ℕ) : ℚ) ≤ 2 * (rkIdx (fixV B) : ℚ) := by exact_mod_cast h3
  linarith

theorem case2_of_natural (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (π : ↥(StatedSL 3 K) →* ↥L) (hπ : Function.Surjective π) (e : V ≃* StdMod (Fin 3) K)
    (he : ∀ (γ : ↥(StatedSL 3 K)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 K) γ (e v))
    (hA : IsFFStarOffender G A) : B42Case2 G L := by
  classical
  set c := natSecOf π hπ e he with hc
  have hLmap : L.map (congrHom e) = natImage (StatedSL 3 K) :=
    map_congrHom_eq_natImage (StatedSL 3 K) hπ e he
  have hle : ∀ B, IsFFStarOffender G B → B ≤ L := by
    intro B hB
    have hEN : B.map (congrHom e) ≤ natNorm (StatedSL 3 K) := by
      have h1 := Subgroup.map_mono (f := congrHom e)
        (hB.1.trans (B42L2.le_normalizer_of_b4Hyp hHyp))
      rwa [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hLmap] at h1
    have hEl := (isElemAbelian2_map_congrHom e).2 hB.2.2.1
    have hoff : Nat.card (StdMod (Fin 3) K) ≤
        Nat.card (B.map (congrHom e)) * Nat.card (fixV (B.map (congrHom e))) := by
      rw [card_map_congrHom, fixV_map_congrHom,
        Subgroup.card_map_of_injective e.injective, ← Nat.card_congr e.toEquiv]
      exact B42L2.card_le_of_offender hB
    have h2 := le_natImage_of_offender hn hK hEN hEl hoff
    rw [← hLmap] at h2
    exact (map_congrHom_le_iff e).1 h2
  have hstab : L ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => Iff.rfl
  have hVcard : Nat.card V = Nat.card K ^ 3 := by
    rw [Nat.card_congr e.toEquiv, card_stdMod, Fintype.card_fin]
  have hfix : ∀ {B : Subgroup (MulAut V)}, B ≤ L →
      Nat.card ↥(fixV B) = Nat.card (B5.fixK (c.pre B)) := by
    intro B hBL
    rw [← c.card_inf_fixV hstab hBL, top_inf_eq]
  refine ⟨le_antisymm (iSup₂_le fun B hB => hle B hB) (le_ffJ_of_odd_center hHyp hZ hA),
    ⟨n, K, inferInstance, inferInstance, hK, π, ?_⟩, ?_⟩
  · exact G64.realizesVia_nat_of hπ bot_le (fun _ _ _ => trivial) (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]) (e.toMonoidHom.comp (⊤ : Subgroup V).subtype)
      (fun x => ⟨⟨e.symm x, trivial⟩, by simp⟩)
      (fun u => by
        rw [Subgroup.mem_bot]
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
          MulEquivClass.map_eq_one_iff])
      (fun γ u _ => he γ u)
  · refine qOf_eq_of_offenders hV (s := 1 / 2) (by norm_num) (fun B hB => ?_) ?_
    ·
      have hBL := hle B hB
      refine half_le_rAV_of_card hV hB.2.2.1 hB.2.1 ?_
      rw [hfix hBL, ← c.card_pre hBL, hVcard, ← pow_mul]
      exact B5.card_mul_card_fixK_sq_le (c.pre_ne_bot hBL hB.2.1) (c.pre_sq hB.2.2.1)
        (c.pre_comm hB.2.2.1)
    ·
      set D := B5.axisSub (plane K) with hD
      set B₀ : Subgroup (MulAut V) := D.map (L.subtype.comp π) with hB₀
      have hB₀L : B₀ ≤ L := by
        rintro _ ⟨γ, -, rfl⟩
        exact (π γ).2
      have hpre : c.pre B₀ = D := by
        ext γ
        constructor
        · intro hγ
          obtain ⟨δ, hδ, hδγ⟩ := hγ
          have hδγ' : π δ = π γ := Subtype.ext hδγ
          have : δ = γ := c.hπ.1 hδγ'
          exact this ▸ hδ
        · intro hγ
          exact ⟨γ, hγ, rfl⟩
      have hDcard : Nat.card D = Nat.card K ^ 2 := B5.card_axisSub finrank_plane
      have hcardB₀ : Nat.card B₀ = Nat.card K ^ 2 := by
        rw [← c.card_pre hB₀L, hpre, hDcard]
      have hB₀ne : B₀ ≠ ⊥ := by
        intro h0
        rw [h0, Subgroup.card_bot] at hcardB₀
        have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) Finite.one_lt_card
        omega
      have hB₀el : IsElemAbelian2 B₀ := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
          have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (B5.axisSub_comm hγ hδ)
          simp only [map_mul, Subgroup.coe_mul] at this
          simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using this
        · rintro _ ⟨γ, hγ, rfl⟩
          have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (B5.axisSub_mul_self hγ)
          simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at this
          simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
          rw [pow_two]
          exact this
      have hfixB₀ : Nat.card ↥(fixV B₀) = Nat.card K ^ 2 := by
        rw [hfix hB₀L, hpre]
        have hne : D ≠ ⊥ := by
          intro h0
          rw [h0, Subgroup.card_bot] at hDcard
          have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) Finite.one_lt_card
          omega
        rw [B5.fixK_eq_of_le_axisSub finrank_plane le_rfl hne,
          Module.natCard_eq_pow_finrank (K := K) (V := plane K), finrank_plane]
      have hr : rAV B₀ = 1 / 2 := by
        have h1 := rk_add_rkIdx (fixV B₀)
        have hrkV : rk V = 3 * n := by
          unfold rk
          rw [hVcard, hK, ← pow_mul, padicValNat.prime_pow]
          ring
        have hrkF : rk ↥(fixV B₀) = 2 * n := by
          unfold rk
          rw [hfixB₀, hK, ← pow_mul, padicValNat.prime_pow]
          ring
        have hrkB : rk ↥B₀ = 2 * n := by
          unfold rk
          rw [hcardB₀, hK, ← pow_mul, padicValNat.prime_pow]
          ring
        unfold rAV
        rw [hrkB, show rkIdx (fixV B₀) = n by omega]
        have : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        push_cast
        field_simp
      have hLG : L ≤ G := hHyp.2.1 ▸ quasithinGenFitting_le G
      have hA2 : IsA2 G B₀ := ⟨hB₀L.trans hLG, hB₀ne, hB₀el⟩
      obtain ⟨B, -, hB, hBr⟩ := exists_offender_rAV_le hV hA2 (by rw [hr]; norm_num)
      exact ⟨B, hB, hBr.trans hr.le⟩

end Natural

end B42SL3

end CFSG.Quasithin
