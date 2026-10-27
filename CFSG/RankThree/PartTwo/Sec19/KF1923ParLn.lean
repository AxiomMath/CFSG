module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParLnCore
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec19 (IsProperParabolic)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular upperTriangular)
open CFSG.RankThree.PartTwo.Late.KFParLn (S2 Cfg)

private theorem kfParLn_center_eq_bot {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hfx : f x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨h, rfl⟩ := f.surjective g
    rw [← map_mul, ← map_mul, hx h]
  rw [hY, Subgroup.mem_bot] at hfx
  rw [Subgroup.mem_bot]
  exact f.injective (by rw [hfx, map_one])

private theorem kfParLn_conj_injective {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have h1 : (MulAut.conj : X →* MulAut X) (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hcent : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := DFunLike.congr_fun h1 g
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent.symm

theorem kfParLn_noSquare {X : Type} [Group X] [Finite X] {n : ℕ} (hn3 : 3 ≤ n)
    (hA : ¬ Nonempty (X ≃* alternatingGroup (Fin 10))) (e : X ≃* S2 n) :
    NoSquareInvertingInParabolic X := by
  intro P D hP hDP hD3 hD9 hDO t htP htN hinv
  obtain ⟨T, hTP⟩ : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ P := by
    unfold ParabolicShape at hP
    rcases hP with ⟨-, hprop⟩ | ⟨hne, -⟩
    · unfold IsProperParabolic at hprop
      obtain ⟨-, T, hT⟩ := hprop
      exact ⟨T, le_trans Subgroup.le_normalizer hT⟩
    · exact absurd hne hA
  haveI : Finite (S2 n) := Finite.of_equiv X e.toEquiv
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := ZMod 2) 2 (by omega : 1 ≤ n)
  let Tg : Sylow 2 (S2 n) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (S2 n) Tg U
  let e' : X ≃* S2 n := e.trans (MulAut.conj c)
  have hB : ∀ u ∈ unitriangular n (ZMod 2), ∃ t₀ ∈ (T : Subgroup X), e' t₀ = u := by
    intro u hu
    have hu' : u ∈ ((c • Tg : Sylow 2 (S2 n)) : Subgroup (S2 n)) := by
      rw [hc, hU]
      exact hu
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hu'
    have h0 : (MulAut.conj c)⁻¹ • u = c⁻¹ * u * c := by
      rw [MulAut.smul_def]
      simp [MulAut.conj_inv_apply]
    rw [h0] at hu'
    have hu'' : c⁻¹ * u * c ∈ Subgroup.map e.toMonoidHom (T : Subgroup X) := hu'
    obtain ⟨t₀, ht₀, hte⟩ := Subgroup.mem_map.1 hu''
    refine ⟨t₀, ht₀, ?_⟩
    show c * e t₀ * c⁻¹ = u
    have : e t₀ = c⁻¹ * u * c := hte
    rw [this]
    group
  have hcent : Subgroup.center X = ⊥ :=
    kfParLn_center_eq_bot e (CFSG.RankThree.PartTwo.Sec4.RonanK429F.center_SL_zmod_two (by omega))
  have hconj := kfParLn_conj_injective hcent
  let Y : Subgroup (MulAut X) := P.map (MulAut.conj : X →* MulAut X)
  let ψ : ↥P →* MulAut X := (MulAut.conj : X →* MulAut X).comp P.subtype
  have hψ : Function.Injective ψ := hconj.comp P.subtype_injective
  have hψY : ∀ h : ↥P, ψ h ∈ Y := fun h => Subgroup.mem_map_of_mem _ h.2
  let ι : ↥P →* S2 n := e'.toMonoidHom.comp P.subtype
  let Rb : Subgroup (MulAut X) := (Sec4.oTwoP 3 ↥Y).map Y.subtype
  let E : Subgroup ↥P := D.comap ψ
  let R : Subgroup ↥P := Rb.comap ψ
  obtain ⟨y₀, hy₀P, hy₀⟩ := Subgroup.mem_map.1 htP
  let y : ↥P := ⟨y₀, hy₀P⟩
  have hψy : ψ y = t := hy₀
  have hDle : D ≤ ψ.range := by
    intro d hd
    obtain ⟨p, hp, hpd⟩ := Subgroup.mem_map.1 (hDP hd)
    exact ⟨⟨p, hp⟩, hpd⟩
  have hRsolv : Group.IsSolvable ↥Rb := by
    haveI : Group.IsSolvable ↥(Sec4.oTwoP 3 ↥Y) := Sec4.isSolvable_oTwoP 3
    exact Group.isSolvable_of_surjective
      (f := Y.subtype.subgroupMap (Sec4.oTwoP 3 ↥Y)) (MonoidHom.subgroupMap_surjective _ _)
  have hnormY : (Sec4.oTwoP 3 ↥Y).Normal := by
    unfold Sec4.oTwoP
    infer_instance
  have hcfg : Cfg R E y := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro h r hr
      obtain ⟨w, hw, hwr⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hr)
      have hcj := hnormY.conj_mem w hw ⟨ψ h, hψY h⟩
      have hwr' : (w : MulAut X) = ψ r := hwr
      refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨_, hcj, ?_⟩)
      simp [hwr']
    ·
      haveI := hRsolv
      let φ : ↥R →* ↥Rb := (ψ.comp R.subtype).codRestrict Rb (fun r => r.2)
      have hφ : Function.Injective φ := fun a b hab =>
        Subtype.ext (hψ (congrArg Subtype.val hab))
      exact Group.isSolvable_of_isSolvable_injective hφ
    ·
      intro d hd
      exact Subgroup.mem_comap.2 (hDO (Subgroup.mem_comap.1 hd))
    ·
      intro x hx
      apply hψ
      rw [map_pow, map_one]
      exact hD3.2 _ (Subgroup.mem_comap.1 hx)
    ·
      have hmap : E.map ψ = D := by
        rw [Subgroup.map_comap_eq]
        exact inf_eq_right.2 hDle
      rw [← Subgroup.card_map_of_injective hψ, hmap]
      exact hD9
    ·
      intro x hx
      have := (Subgroup.mem_normalizer_iff.1 htN (ψ x)).1 (Subgroup.mem_comap.1 hx)
      rw [← hψy] at this
      exact Subgroup.mem_comap.2 (by simpa using this)
    ·
      intro x hx
      apply hψ
      have := hinv (ψ x) (Subgroup.mem_comap.1 hx)
      rw [← hψy] at this
      simpa using this
  have hinj : ∀ x ∈ E, ι x = 1 → x = 1 := by
    intro x _ hx
    have h1 : e' (x : X) = 1 := hx
    exact Subtype.ext (e'.injective (h1.trans (map_one e').symm))
  have hBr : upperTriangular n (ZMod 2) ≤ ι.range := by
    intro u hu
    obtain ⟨t₀, ht₀, hte⟩ := hB u
      (CFSG.QuasithinUnique.Vol2Native.A312L.upperTriangular_le_unitriangular
        (Nat.card_zmod 2) hu)
    exact ⟨⟨t₀, hTP ht₀⟩, hte⟩
  exact hcfg.false_of_hom n (by omega) ι hinj hBr

private theorem kfParLn_card_ne {n : ℕ} (hn : 3 ≤ n) : Nat.card (S2 n) ≠ 1814400 := by
  intro h
  by_cases h5 : 5 ≤ n
  · have h31 : 31 ∣ Nat.card (S2 n) := by
      rw [CFSG.RankThree.PartTwo.Sec4.RonanK429F.card_SL_zmod_two (by omega)]
      refine Dvd.dvd.mul_left ?_ _
      have := Finset.dvd_prod_of_mem (fun j : ℕ => 2 ^ j - 1) (a := 5)
        (s := Finset.Icc 2 n) (Finset.mem_Icc.2 ⟨by norm_num, h5⟩)
      simpa using this
    rw [h] at h31
    omega
  · interval_cases n
    · rw [CFSG.RankThree.PartTwo.Sec4.RonanK429F.card_SL_zmod_two (by omega)] at h
      revert h
      decide
    · rw [CFSG.RankThree.PartTwo.Sec4.RonanK429F.card_SL4_zmod_two] at h
      omega

theorem kfParLn_noSquare_projSL {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (e₁ : X ≃* projSL n (GaloisField 2 1)) : NoSquareInvertingInParabolic X := by
  have e : X ≃* S2 n :=
    e₁.trans (CFSG.RankThree.PartTwo.Sec4.RonanK429F.projSLEquivSLZMod (by omega))
  refine kfParLn_noSquare hn ?_ e
  rintro ⟨hA⟩
  have h1 : Nat.card X = Nat.card (S2 n) := Nat.card_congr e.toEquiv
  have h2 : Nat.card X = 1814400 := by
    rw [Nat.card_congr hA.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  exact kfParLn_card_ne hn (h1.symm.trans h2)

theorem kfPar_L6_L7 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* projSL 6 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSL 7 (GaloisField 2 1))) : NoSquareInvertingInParabolic X := by
  rcases hX with he | he
  · obtain ⟨e⟩ := he
    exact kfParLn_noSquare_projSL (by norm_num) e
  · obtain ⟨e⟩ := he
    exact kfParLn_noSquare_projSL (by norm_num) e

end CFSG.RankThree.PartTwo.Late
