module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.Walter.PSL2Facts.TwoGroupBorel
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GorensteinWalter CFSG.Walter CFSG.Walter.J1Props CFSG.Open CFSG.ASVolI
open scoped Pointwise

private theorem orderOf_conj_eq_of_center_eq_bot {Y : Type*} [Group Y]
    (hZ : Subgroup.center Y = ⊥) (y : Y) :
    orderOf (MulAut.conj y) = orderOf y :=
  orderOf_injective _ (CFSG.mulAutConj_injective_of_center_eq_bot hZ) y

private theorem mem_sylow_of_isPGroup_zpowers {Y : Type*} [Group Y] (S : Sylow 2 Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y))
    (h2 : IsPGroup 2 (Subgroup.zpowers y)) : y ∈ (S : Subgroup Y) := by
  have hmem : y ∈ Subgroup.zpowers y ⊓ (S : Subgroup Y) := by
    rw [← h2.inf_normalizer_sylow S]
    exact ⟨Subgroup.mem_zpowers y, hy⟩
  exact hmem.2

private theorem conj_mul_inv_mem_of_mem_normalizer {Y : Type*} [Group Y] {S : Subgroup Y}
    {s h : Y} (hs : s ∈ S) (hh : h ∈ Subgroup.normalizer (S : Set Y)) :
    MulAut.conj s h * h⁻¹ ∈ S := by
  have hconj : h * s⁻¹ * h⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hh s⁻¹).1 (Subgroup.inv_mem _ hs)
  rw [MulAut.conj_apply, show s * h * s⁻¹ * h⁻¹ = s * (h * s⁻¹ * h⁻¹) by group]
  exact Subgroup.mul_mem _ hs hconj

private theorem not_isMulCommutative_map_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {K : Subgroup G}
    (hK : ¬ IsMulCommutative K) : ¬ IsMulCommutative (K.map f) := by
  intro hc
  apply hK
  refine IsMulCommutative.mk ⟨fun a b => ?_⟩
  apply Subtype.ext
  apply hf
  have hcomm := congrArg Subtype.val
    (hc.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
  simpa using hcomm

private theorem exists_conj_map_eq_of_sylow {Y : Type*} [Group Y] [Finite Y]
    (S T : Sylow 2 Y) :
    ∃ g : Y, (S : Subgroup Y).map (MulAut.conj g).toMonoidHom = (T : Subgroup Y) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S T
  refine ⟨g, ?_⟩
  have h := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  convert h using 2
  ext x
  rfl

theorem map_sylow_symm_of_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {S : Sylow 2 X} {T : Sylow 2 Y}
    (hT : (T : Subgroup Y) = (S : Subgroup X).map (e : X →* Y)) :
    (T : Subgroup Y).map (e.symm : Y →* X) = (S : Subgroup X) := by
  rw [hT, Subgroup.map_map]
  have hcomp : (e.symm : Y →* X).comp (e : X →* Y) = MonoidHom.id X := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem symm_mulAut_congr_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (θ : MulAut X) (y : Y) :
    e.symm (MulAut.congr e θ y) = θ (e.symm y) := by
  simp [MulAut.congr_apply]

private theorem centralizes_mod_of_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {S : Sylow 2 X} {T : Sylow 2 Y}
    (hT : (T : Subgroup Y) = (S : Subgroup X).map (e : X →* Y))
    {Θ : Subgroup (MulAut X)} {ΘY : Subgroup (MulAut Y)}
    (hΘY : ΘY = Θ.map (MulAut.congr e).toMonoidHom)
    {H : Subgroup Y}
    (hcent : ∀ θ ∈ ΘY, ∀ h ∈ H, θ h * h⁻¹ ∈ (T : Subgroup Y)) :
    ∀ θ ∈ Θ, ∀ h ∈ H.map (e.symm : Y →* X),
      θ h * h⁻¹ ∈ (S : Subgroup X) := by
  have hmap : (T : Subgroup Y).map (e.symm : Y →* X) = (S : Subgroup X) :=
    map_sylow_symm_of_map e hT
  intro θ hθ h hh
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
  let θ' : MulAut Y := MulAut.congr e θ
  have hθ' : θ' ∈ ΘY := by
    rw [hΘY]
    exact Subgroup.mem_map_of_mem _ hθ
  have hcent' : θ' h' * h'⁻¹ ∈ (T : Subgroup Y) := hcent θ' hθ' h' hh'
  have hmem : e.symm (θ' h' * h'⁻¹) ∈ (S : Subgroup X) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hcent'
  convert hmem using 1
  rw [map_mul, map_inv, symm_mulAut_congr_apply]
  rfl

private theorem exists_not_inner_of_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {k : ℕ} {Θ : Subgroup (MulAut X)} {ΘY : Subgroup (MulAut Y)}
    (hΘY : ΘY = Θ.map (MulAut.congr e).toMonoidHom)
    (h : ∃ θ ∈ ΘY, ∀ y : Y, θ ^ (k / 2) ≠ MulAut.conj y) :
    ∃ θ ∈ Θ, ∀ x : X, θ ^ (k / 2) ≠ MulAut.conj x := by
  obtain ⟨θ', hθ', hnot⟩ := h
  rw [hΘY] at hθ'
  obtain ⟨θ, hθ, hθeq⟩ := Subgroup.mem_map.mp hθ'
  refine ⟨θ, hθ, fun x hx => hnot (e x) ?_⟩
  have hpow : MulAut.congr e (θ ^ (k / 2)) = θ' ^ (k / 2) := by
    rw [← hθeq]
    exact map_pow (MulAut.congr e).toMonoidHom θ (k / 2)
  have hconj : MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) :=
    CFSG.mulAut_congr_conj e x
  rw [← hpow, hx, hconj]

private theorem maps_sylow_of_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {S : Sylow 2 X} {T : Sylow 2 Y}
    (hT : (T : Subgroup Y) = (S : Subgroup X).map (e : X →* Y))
    {Θ : Subgroup (MulAut X)} {ΘY : Subgroup (MulAut Y)}
    (hΘY : ΘY = Θ.map (MulAut.congr e).toMonoidHom)
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) :
    ∀ θ' ∈ ΘY, ∀ y ∈ (T : Subgroup Y), θ' y ∈ (T : Subgroup Y) := by
  intro θ' hθ' y hy
  rw [hΘY] at hθ'
  obtain ⟨θ, hθ, rfl⟩ := Subgroup.mem_map.mp hθ'
  rw [hT] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  simpa [MulAut.congr_apply] using
    Subgroup.mem_map_of_mem (e : X →* Y) (hΘS θ hθ x hx)

theorem exists_borelFixed_of_isL2 {X : Type} [Group X] [Finite X] {k : ℕ}
    (hX : IsL2 X k) (Θ : Subgroup (MulAut X)) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 X)
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) :
    ∃ e m : ℕ, k = 2 ^ e * m ∧ ∃ H : Subgroup X, IsCyclic H ∧
      Nat.card H = 2 ^ m - 1 ∧
      H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) ∧
      (∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup X)) ∧
      (m = 1 → 2 ≤ k → ∃ θ ∈ Θ, ∀ x : X, θ ^ (k / 2) ≠ MulAut.conj x) := by
  have ha : 1 ≤ k := hX.admissible.2.1
  have hm : CFSG.Open.StatedClassicalModel X .PSL 2 2 k :=
    hX.statedClassicalModel_of_ne_zero (by omega)
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let Φ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
  let e : X ≃* PSL2 K := e₀.trans Φ.symm
  let Θ' : Subgroup (MulAut (PSL2 K)) := Θ.map (MulAut.congr e).toMonoidHom
  have hΘ' : IsPGroup 2 Θ' := hΘ.map _
  let S' : Sylow 2 (PSL2 K) :=
    Sylow.mapSurjective (f := (e : X →* PSL2 K)) e.surjective S
  have hS'coe : (S' : Subgroup (PSL2 K)) = S.map (e : X →* PSL2 K) :=
    Sylow.coe_mapSurjective (f := (e : X →* PSL2 K)) e.surjective S
  have hΘ'S : ∀ θ' ∈ Θ', ∀ x ∈ (S' : Subgroup (PSL2 K)),
      θ' x ∈ (S' : Subgroup (PSL2 K)) :=
    maps_sylow_of_map e hS'coe rfl hΘS
  obtain ⟨e₁, m, ham, H', hH'cyc, hH'card, hH'norm, hH'cent, hH'not⟩ :=
    CFSG.Walter.psl2_even_two_group_borel_fixed hK Θ' hΘ' S' hΘ'S
  have hS'map : (S' : Subgroup (PSL2 K)).map (e.symm : PSL2 K →* X) =
      (S : Subgroup X) := map_sylow_symm_of_map e hS'coe
  let H : Subgroup X := H'.map (e.symm : PSL2 K →* X)
  have hHcyc : IsCyclic H :=
    (Subgroup.equivMapOfInjective H' (e.symm : PSL2 K →* X) e.symm.injective).isCyclic.mp
      hH'cyc
  have hHcard : Nat.card H = 2 ^ m - 1 := by
    change Nat.card (H'.map (e.symm : PSL2 K →* X)) = 2 ^ m - 1
    rw [Subgroup.card_map_of_injective e.symm.injective, hH'card]
  have hHnorm : H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    have hmap := burnsideAut_map_le_normalizer_map (e.symm : PSL2 K →* X) hH'norm
    simpa only [hS'map] using hmap
  refine ⟨e₁, m, ham, H, hHcyc, hHcard, hHnorm, ?_, ?_⟩
  · exact centralizes_mod_of_map e hS'coe rfl hH'cent
  · intro hm1 hk2
    exact exists_not_inner_of_map e rfl (hH'not hm1 hk2)

theorem exists_borelFixed_of_isSz (hAut : KSzTwoAut) {X : Type} [Group X] [Finite X] {k : ℕ}
    (hX : IsSz X k) (Θ : Subgroup (MulAut X)) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 X)
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) :
    ∃ H : Subgroup X, Nat.card H = 2 ^ k - 1 ∧
      H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) ∧
      (∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup X)) := by
  obtain ⟨H, hHcard, hHnorm⟩ := kSzBorel_holds X k hX S
  refine ⟨H, hHcard, hHnorm, ?_⟩
  intro θ hθ h hh
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hΘ) ⟨θ, hθ⟩
  have hθ2 : ∃ n : ℕ, orderOf θ = 2 ^ n := ⟨n, by simpa using hn⟩
  obtain ⟨s, hs, hθeq⟩ := hAut X k hX S θ hθ2 (hΘS θ hθ)
  have hmem := conj_mul_inv_mem_of_mem_normalizer hs (hHnorm hh)
  rw [hθeq]
  exact hmem

private theorem card_zpowers_nJ_sup_zpowers_mJ :
    Nat.card (Subgroup.zpowers nJ ⊔ Subgroup.zpowers mJ : Subgroup walterJ1) = 21 := by
  have hn7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  have hm3 : orderOf mJ = 3 := orderOf_yJ (p := 3) (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmul, -, -⟩ := rels_aut
  have hconj : mJ * nJ * mJ⁻¹ = nJ ^ 4 := hmul
  have hzp : Subgroup.zpowers (nJ ^ 4) = Subgroup.zpowers nJ := by
    have h := (Subgroup.zpowers_eq_zpowers_iff' (g := nJ) 4 1).mpr (by
      norm_num [hn7])
    simpa using h
  have hm_norm : Subgroup.zpowers mJ ≤
      Subgroup.normalizer ((Subgroup.zpowers nJ : Set walterJ1)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq,
      MonoidHom.map_zpowers]
    change Subgroup.zpowers (mJ * nJ * mJ⁻¹) = Subgroup.zpowers nJ
    rw [hconj, hzp]
  have hdisj : Subgroup.zpowers nJ ⊓ Subgroup.zpowers mJ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h7 : orderOf y ∣ 7 := by
      have := Subgroup.orderOf_dvd_natCard _ hy.1
      rwa [Nat.card_zpowers, hn7] at this
    have h3 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard _ hy.2
      rwa [Nat.card_zpowers, hm3] at this
    have hdvd : orderOf y ∣ Nat.gcd 7 3 := Nat.dvd_gcd h7 h3
    rw [show Nat.gcd 7 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hdvd
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hm_norm
      (disjoint_iff.mpr hdisj), Nat.card_zpowers, Nat.card_zpowers, hn7, hm3]

private theorem not_isMulCommutative_zpowers_nJ_sup_zpowers_mJ :
    ¬ IsMulCommutative (Subgroup.zpowers nJ ⊔ Subgroup.zpowers mJ : Subgroup walterJ1) := by
  intro hc
  have hn7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  have hcomm : nJ * mJ = mJ * nJ := by
    have h := hc.is_comm.comm
      ⟨nJ, Subgroup.mem_sup_left (Subgroup.mem_zpowers nJ)⟩
      ⟨mJ, Subgroup.mem_sup_right (Subgroup.mem_zpowers mJ)⟩
    exact congrArg Subtype.val h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmul, -, -⟩ := rels_aut
  have hmj : mJ * nJ * mJ⁻¹ = nJ := by
    rw [← hcomm]
    group
  have heq : nJ = nJ ^ 4 := by
    rw [← hmul, hmj]
  have h3 : nJ ^ 3 = 1 := by
    have h := congrArg (fun x : walterJ1 => x * nJ⁻¹) heq
    simpa [pow_succ, pow_two, mul_assoc] using h.symm
  have hdvd : orderOf nJ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hn7] at hdvd
  omega

private theorem zpowers_nJ_sup_zpowers_mJ_le_normalizer_S₀ :
    (Subgroup.zpowers nJ ⊔ Subgroup.zpowers mJ : Subgroup walterJ1) ≤
      Subgroup.normalizer ((S₀ : Subgroup walterJ1) : Set walterJ1) := by
  exact sup_le (Subgroup.zpowers_le.mpr nJ_mem_normalizer)
    (Subgroup.zpowers_le.mpr mJ_mem_normalizer)

private theorem exists_borelSubgroup_walterJ1 (S : Sylow 2 walterJ1) :
    ∃ H : Subgroup walterJ1, Odd (Nat.card H) ∧ ¬ IsMulCommutative H ∧
      H ≤ Subgroup.normalizer ((S : Subgroup walterJ1) : Set walterJ1) := by
  let N₀ : Subgroup walterJ1 := Subgroup.zpowers nJ ⊔ Subgroup.zpowers mJ
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_sylow sylowS₀ S
  have hg₀ : (S₀ : Subgroup walterJ1).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup walterJ1) := by
    simpa using hg
  let H : Subgroup walterJ1 := N₀.map (MulAut.conj g).toMonoidHom
  have hHcard : Nat.card H = Nat.card N₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    change Odd (Nat.card (Subgroup.zpowers nJ ⊔ Subgroup.zpowers mJ : Subgroup walterJ1))
    rw [card_zpowers_nJ_sup_zpowers_mJ]
    norm_num
  have hHnoncomm : ¬ IsMulCommutative H :=
    not_isMulCommutative_map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective not_isMulCommutative_zpowers_nJ_sup_zpowers_mJ
  have hHnorm : H ≤ Subgroup.normalizer ((S : Subgroup walterJ1) : Set walterJ1) := by
    have hmap := burnsideAut_map_le_normalizer_map (MulAut.conj g).toMonoidHom
      zpowers_nJ_sup_zpowers_mJ_le_normalizer_S₀
    rw [hg₀] at hmap
    change N₀.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((S : Subgroup walterJ1) : Set walterJ1)
    exact hmap
  exact ⟨H, hHodd, hHnoncomm, hHnorm⟩

theorem exists_borelSubgroup_of_isJ1 {X : Type} [Group X] [Finite X]
    (hX : IsJ1 X) (S : Sylow 2 X) :
    ∃ H : Subgroup X, Odd (Nat.card H) ∧ ¬ IsMulCommutative H ∧
      H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
  obtain ⟨eJ⟩ := hX
  let f : X ≃* walterJ1 := eJ.trans walterJ1EquivNative.symm
  let S' : Sylow 2 walterJ1 :=
    Sylow.mapSurjective (f := (f : X →* walterJ1)) f.surjective S
  have hS'coe : (S' : Subgroup walterJ1) = S.map (f : X →* walterJ1) :=
    Sylow.coe_mapSurjective (f := (f : X →* walterJ1)) f.surjective S
  obtain ⟨Hw, hHwodd, hHwnoncomm, hHwnorm⟩ := exists_borelSubgroup_walterJ1 S'
  have hS'map : (S' : Subgroup walterJ1).map (f.symm : walterJ1 →* X) =
      (S : Subgroup X) := by
    rw [hS'coe, Subgroup.map_map]
    have hcomp : (f.symm : walterJ1 →* X).comp (f : X →* walterJ1) = MonoidHom.id X := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  let H : Subgroup X := Hw.map (f.symm : walterJ1 →* X)
  have hHcard : Nat.card H = Nat.card Hw := by
    change Nat.card (Hw.map (f.symm : walterJ1 →* X)) = Nat.card Hw
    exact Subgroup.card_map_of_injective f.symm.injective
  have hHodd : Odd (Nat.card H) := by rw [hHcard]; exact hHwodd
  have hHnoncomm : ¬ IsMulCommutative H := by
    change ¬ IsMulCommutative (Hw.map (f.symm : walterJ1 →* X))
    exact not_isMulCommutative_map_of_injective (f.symm : walterJ1 →* X)
      f.symm.injective hHwnoncomm
  have hHnorm : H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    have hmap := burnsideAut_map_le_normalizer_map (f.symm : walterJ1 →* X) hHwnorm
    simpa only [hS'map] using hmap
  exact ⟨H, hHodd, hHnoncomm, hHnorm⟩

theorem center_eq_bot_of_isJ1 {X : Type} [Group X] [Finite X] (hX : IsJ1 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, hsimpleX, -⟩ := kJ1_holds (X := X) hX
  obtain ⟨eJ⟩ := hX
  let f : X ≃* walterJ1 := eJ.trans walterJ1EquivNative.symm
  have hnoncommX : ¬ IsMulCommutative X := by
    intro hc
    have hcomm : tJ * nJ = nJ * tJ := by
      have h := hc.is_comm.comm (f.symm tJ) (f.symm nJ)
      have := congrArg f h
      simpa using this
    exact rels_aut.2.2.2.1 hcomm
  haveI : IsSimpleGroup X := hsimpleX
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
  · exact h
  · exfalso
    apply hnoncommX
    refine IsMulCommutative.mk ⟨fun a b => ?_⟩
    have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem centralizes_mod_of_isJ1 {X : Type} [Group X] [Finite X]
    (hX : IsJ1 X) (Θ : Subgroup (MulAut X)) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 X)
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X))
    {H : Subgroup X} (hHnorm : H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X)) :
    ∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup X) := by
  obtain ⟨-, -, hinner⟩ := kJ1_holds (X := X) hX
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_isJ1 hX
  intro θ hθ h hh
  obtain ⟨x, hx⟩ := hinner θ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hΘ) ⟨θ, hθ⟩
  have hθpow : orderOf θ = 2 ^ n := by simpa using hn
  have hxpow : orderOf x = 2 ^ n := by
    rw [← orderOf_conj_eq_of_center_eq_bot hZ x, ← hx, hθpow]
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hxpow])
  have hθSle : (S : Subgroup X).map θ.toMonoidHom ≤ (S : Subgroup X) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΘS θ hθ y hy
  have hθS : (S : Subgroup X).map θ.toMonoidHom = (S : Subgroup X) := by
    refine Subgroup.eq_of_le_of_card_ge hθSle ?_
    rw [Subgroup.card_map_of_injective θ.injective]
  have hxSmap : (S : Subgroup X).map (MulAut.conj x).toMonoidHom = (S : Subgroup X) := by
    rwa [hx] at hθS
  have hxN : x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxSmap
  have hxS : x ∈ (S : Subgroup X) := mem_sylow_of_isPGroup_zpowers S hxN hx2
  have hmem := conj_mul_inv_mem_of_mem_normalizer hxS (hHnorm hh)
  rw [hx]
  exact hmem

theorem exists_borelFixed_of_isJ1 {X : Type} [Group X] [Finite X]
    (hX : IsJ1 X) (Θ : Subgroup (MulAut X)) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 X)
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) :
    ∃ H : Subgroup X, Odd (Nat.card H) ∧ ¬ IsMulCommutative H ∧
      H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) ∧
      (∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup X)) := by
  obtain ⟨H, hHodd, hHnoncomm, hHnorm⟩ := exists_borelSubgroup_of_isJ1 hX S
  exact ⟨H, hHodd, hHnoncomm, hHnorm,
    centralizes_mod_of_isJ1 hX Θ hΘ S hΘS hHnorm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
