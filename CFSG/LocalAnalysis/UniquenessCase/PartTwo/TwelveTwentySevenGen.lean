module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Lin
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.GroupTheory.InvariantSubgroupClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_mul_of_inCalV0_gen {M V₀ V X : Subgroup G} (h : InCalV0 M V₀ V)
    {v : G} (hv : v ∈ V) (hvV₀ : v ∉ V₀)
    (hXM : X ≤ M) (hXv : ∀ x ∈ X, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    (hirr : ∀ U : Subgroup G, U ≤ V₀ → X ≤ normalizer (U : Set G) → U = ⊥ ∨ U = V₀)
    {d : G} (hd : d ∈ V₀) :
    ∃ x ∈ M ⊓ centralizer (V₀ : Set G), CentralizesMod V₀ V x ∧ x * v * x⁻¹ = v * d := by
  obtain ⟨hV₀, hV, hV₀leV, -, -, hgen, hnot2red⟩ := h
  obtain ⟨hV₀ne, -, hMNV₀, hV₀E⟩ := hV₀
  obtain ⟨-, hVM, hMNV, hVE⟩ := hV
  have : IsMulCommutative V := hVE.1
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hVE.comm ha hb
  have hV_le_cent : V ≤ Subgroup.centralizer (V : Set G) := Subgroup.le_centralizer V
  have hXNV₀ : X ≤ Subgroup.normalizer (V₀ : Set G) := hXM.trans hMNV₀
  have hnotred := hnot2red
  rw [TwoReduced] at hnotred
  push Not at hnotred
  obtain ⟨K, hKM, hMNK, hCK, hKidx, hKnotcent⟩ := hnotred
  obtain ⟨n, hn⟩ := hKidx
  have hKNV : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMNV
  have hKNV₀ : K ≤ Subgroup.normalizer (V₀ : Set G) := hKM.trans hMNV₀
  have hKNC : K ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    hKNV.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup V)
  have hVK : V ≤ K := (le_inf hVM hV_le_cent).trans hCK
  let Ck : Subgroup K := (Subgroup.centralizer (V : Set G)).subgroupOf K
  have : Ck.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKNC
  let P : Type _ := K ⧸ Ck
  have hPcard : Nat.card P = 2 ^ n := by
    show Nat.card (K ⧸ Ck) = 2 ^ n
    rw [← Subgroup.index_eq_card]
    exact hn
  have hPp : IsPGroup 2 P := IsPGroup.of_card hPcard
  let conjAutV : K →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hKNV)
  let conjAutV₀ : K →* MulAut V₀ :=
    V₀.normalizerMonoidHom.comp (Subgroup.inclusion hKNV₀)
  have normalizerMonoidHom_apply_coe {N : Subgroup G}
      (g : Subgroup.normalizer (N : Set G)) (x : N) :
      ((N.normalizerMonoidHom g x : N) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl
  have hCk_kerV : Ck ≤ conjAutV.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hcomm' := Subgroup.mem_centralizer_iff.mp hkcent (y : G) y.2
    show ((conjAutV k) y : G) = (y : G)
    simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    rw [← hcomm']
    group
  have hCk_kerV₀ : Ck ≤ conjAutV₀.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hyV : (y : G) ∈ V := hV₀leV y.2
    have hcomm' := Subgroup.mem_centralizer_iff.mp hkcent (y : G) hyV
    show ((conjAutV₀ k) y : G) = (y : G)
    simp only [conjAutV₀, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    rw [← hcomm']
    group
  let V0V : Subgroup V := V₀.subgroupOf V
  let Q : Type _ := V ⧸ V0V
  have hpres : ∀ k : K, V0V ≤ V0V.comap (conjAutV k).toMonoidHom := by
    intro k x hx
    rw [Subgroup.mem_comap]
    have hxV₀ : (x : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp hx
    show ((conjAutV k) x : V) ∈ V0V
    rw [Subgroup.mem_subgroupOf]
    simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
      Subgroup.coe_inclusion]
    exact (Subgroup.mem_normalizer_iff.mp (hKNV₀ k.2) _).mp hxV₀
  have hmap : ∀ k : K, V0V.map (conjAutV k : V →* V) = V0V := fun k =>
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr (hpres k))
      (Subgroup.card_map_of_injective (conjAutV k).injective).ge
  let conjQuotAut : K →* MulAut Q :=
    { toFun := fun k => QuotientGroup.congr V0V V0V (conjAutV k) (hmap k)
      map_one' := by
        apply MulEquiv.ext
        intro q
        refine QuotientGroup.induction_on q fun x => ?_
        simp [QuotientGroup.congr_mk]
      map_mul' := by
        intro k₁ k₂
        apply MulEquiv.ext
        intro q
        refine QuotientGroup.induction_on q fun x => ?_
        rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
          QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  have hCk_kerQ : Ck ≤ conjQuotAut.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkcent : ((k : K) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hk
    have hconjx : ∀ y : V, (conjAutV k) y = y := by
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hkcent (y : G) y.2
      show ((conjAutV k) y : G) = (y : G)
      simp only [conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
        Subgroup.coe_inclusion]
      rw [← this]
      group
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    show conjQuotAut k (QuotientGroup.mk x) = QuotientGroup.mk x
    change QuotientGroup.congr V0V V0V (conjAutV k) (hmap k) (QuotientGroup.mk x) =
      QuotientGroup.mk x
    rw [QuotientGroup.congr_mk, hconjx x]
  have hQp : IsPGroup 2 Q := hVE.isPGroup.to_quotient V0V
  have hQnontriv : Nontrivial Q := by
    refine ⟨(QuotientGroup.mk (⟨v, hv⟩ : V) : Q), 1, ?_⟩
    intro hcontr
    rw [QuotientGroup.eq_one_iff] at hcontr
    exact hvV₀ (Subgroup.mem_subgroupOf.mp hcontr)
  let phiQ : P →* MulAut Q := QuotientGroup.lift Ck conjQuotAut hCk_kerQ
  let _ : MulAction P Q := MulAction.compHom Q phiQ
  have h1fixQ : (1 : Q) ∈ MulAction.fixedPoints P Q := by
    rw [MulAction.mem_fixedPoints]
    intro p
    show phiQ p 1 = 1
    exact map_one (phiQ p)
  obtain ⟨q, hqfix', hqne'⟩ := hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q
    (hQp.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne') h1fixQ
  have hqne : q ≠ 1 := fun h => hqne' h.symm
  have hqfix : ∀ p : P, p • q = q := MulAction.mem_fixedPoints.mp hqfix'
  obtain ⟨w, hwq⟩ := Quotient.exists_rep q
  have hwV : (w : G) ∈ V := w.2
  have hwV₀ : (w : G) ∉ V₀ := by
    intro hw0
    exact hqne (by rw [← hwq, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr hw0)
  have hwfix : ∀ k' ∈ K, k' * (w : G) * k'⁻¹ * (w : G)⁻¹ ∈ V₀ := by
    intro k' hk'
    have h := hqfix (QuotientGroup.mk (⟨k', hk'⟩ : K))
    rw [← hwq] at h
    change phiQ (QuotientGroup.mk (⟨k', hk'⟩ : K)) (QuotientGroup.mk w) =
      QuotientGroup.mk w at h
    rw [show phiQ (QuotientGroup.mk (⟨k', hk'⟩ : K)) = conjQuotAut ⟨k', hk'⟩ from
      QuotientGroup.lift_mk _ _ _] at h
    change QuotientGroup.congr V0V V0V (conjAutV ⟨k', hk'⟩) (hmap ⟨k', hk'⟩)
      (QuotientGroup.mk w) = QuotientGroup.mk w at h
    rw [QuotientGroup.congr_mk, QuotientGroup.eq_iff_div_mem] at h
    have hmem : (((conjAutV ⟨k', hk'⟩) w / w : V) : G) ∈ V₀ :=
      Subgroup.mem_subgroupOf.mp h
    have hcoeeq : (((conjAutV ⟨k', hk'⟩) w / w : V) : G) =
        k' * (w : G) * k'⁻¹ * (w : G)⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv,
        conjAutV, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe, Subgroup.coe_inclusion]
    rwa [hcoeeq] at hmem
  have hKcent : ∀ k ∈ K, CentralizesMod V₀ V k := by
    intro k hk u hu
    have hkV : ∀ y ∈ V, k * y * k⁻¹ ∈ V := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (hKNV hk) y).mp hy
    have hmul : ∀ x ∈ V, ∀ y ∈ V,
        k * (x * y) * k⁻¹ * (x * y)⁻¹ = (k * x * k⁻¹ * x⁻¹) * (k * y * k⁻¹ * y⁻¹) :=
      fun x hx y hy => congrArg Subtype.val
        (map_mul (CFSG.EvenSporadicStandard.Fin76b.commHom V hcomm k hkV) (⟨x, hx⟩ : V) ⟨y, hy⟩)
    have hinv : ∀ x ∈ V, k * x⁻¹ * k⁻¹ * x⁻¹⁻¹ = (k * x * k⁻¹ * x⁻¹)⁻¹ :=
      fun x hx => congrArg Subtype.val
        (map_inv (CFSG.EvenSporadicStandard.Fin76b.commHom V hcomm k hkV) (⟨x, hx⟩ : V))
    let Sk : Subgroup G :=
      { carrier := {x : G | x ∈ V ∧ k * x * k⁻¹ * x⁻¹ ∈ V₀}
        one_mem' := by
          refine ⟨V.one_mem, ?_⟩
          simpa using V₀.one_mem
        mul_mem' := by
          rintro x y ⟨hxV, hx0⟩ ⟨hyV, hy0⟩
          refine ⟨V.mul_mem hxV hyV, ?_⟩
          rw [hmul x hxV y hyV]
          exact V₀.mul_mem hx0 hy0
        inv_mem' := by
          rintro x ⟨hxV, hx0⟩
          refine ⟨V.inv_mem hxV, ?_⟩
          rw [hinv x hxV]
          exact V₀.inv_mem hx0 }
    have hSkclosure : Subgroup.closure {x : G | ∃ m ∈ M, x = m * w * m⁻¹} ≤ Sk := by
      rw [Subgroup.closure_le]
      rintro x ⟨m, hmM, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMNV hmM) _).mp hwV, ?_⟩
      have hk' : m⁻¹ * k * m ∈ K :=
        ((Subgroup.mem_normalizer_iff''.mp (hMNK hmM)) k).mp hk
      have hkw : (m⁻¹ * k * m) * (w : G) * (m⁻¹ * k * m)⁻¹ * (w : G)⁻¹ ∈ V₀ :=
        hwfix _ hk'
      have heq : k * (m * (w : G) * m⁻¹) * k⁻¹ * (m * (w : G) * m⁻¹)⁻¹ =
          m * ((m⁻¹ * k * m) * (w : G) * (m⁻¹ * k * m)⁻¹ * (w : G)⁻¹) * m⁻¹ := by group
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp (hMNV₀ hmM) _).mp hkw
    have hVleSk : V ≤ Sk := by
      rw [← hgen w hwV hwV₀]
      exact hSkclosure
    exact (hVleSk hu).2
  have hKleV₀ : K ≤ Subgroup.centralizer (V₀ : Set G) := by
    let phiV₀ : P →* MulAut V₀ := QuotientGroup.lift Ck conjAutV₀ hCk_kerV₀
    let _ : MulAction P V₀ := MulAction.compHom V₀ phiV₀
    have hV₀nontriv : Nontrivial V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).mpr hV₀ne
    have h1fixV₀ : (1 : V₀) ∈ MulAction.fixedPoints P V₀ := by
      rw [MulAction.mem_fixedPoints]
      intro p
      show phiV₀ p 1 = 1
      exact map_one (phiV₀ p)
    obtain ⟨z, hzfix', hzne'⟩ := hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point V₀
      (hV₀E.isPGroup.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne') h1fixV₀
    have hzne : z ≠ 1 := fun h => hzne' h.symm
    have hzfix : ∀ p : P, p • z = z := MulAction.mem_fixedPoints.mp hzfix'
    have hzC : (z : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := hzfix (QuotientGroup.mk (⟨k, hk⟩ : K))
      change phiV₀ (QuotientGroup.mk (⟨k, hk⟩ : K)) z = z at h
      rw [show phiV₀ (QuotientGroup.mk (⟨k, hk⟩ : K)) = conjAutV₀ ⟨k, hk⟩ from
        QuotientGroup.lift_mk _ _ _] at h
      have h2 : k * (z : G) * k⁻¹ = (z : G) := by
        have := congrArg (fun y : V₀ => (y : G)) h
        simpa only [conjAutV₀, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe,
          Subgroup.coe_inclusion] using this
      calc k * (z : G) = k * (z : G) * k⁻¹ * k := by group
        _ = (z : G) * k := by rw [h2]
    let Zsub : Subgroup G := V₀ ⊓ Subgroup.centralizer (K : Set G)
    have hZsub_le : Zsub ≤ V₀ := inf_le_left
    have hZsub_ne : Zsub ≠ ⊥ := by
      intro hbot
      have hzZ : (z : G) ∈ Zsub := ⟨z.2, hzC⟩
      rw [hbot] at hzZ
      exact hzne (Subtype.ext (Subgroup.mem_bot.mp hzZ))
    have hXZsub : X ≤ Subgroup.normalizer (Zsub : Set G) := by
      have hXNK : X ≤ Subgroup.normalizer (K : Set G) := hXM.trans hMNK
      have hXNC : X ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
        hXNK.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup K)
      exact (le_inf hXNV₀ hXNC).trans inf_normalizer_le_normalizer_inf
    rcases hirr Zsub hZsub_le hXZsub with hbot | hV₀eq
    · exact absurd hbot hZsub_ne
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzZ : z ∈ Zsub := hV₀eq ▸ hz
      exact ((Subgroup.mem_centralizer_iff.mp hzZ.2) k hk).symm
  have hV₀K : V₀ ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hKleV₀
  have hC_V_K : V ⊓ Subgroup.centralizer (K : Set G) = V₀ := by
    have hMNV'' : M ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
      hMNK.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup K)
    have hMNU : M ≤ Subgroup.normalizer (V ⊓ Subgroup.centralizer (K : Set G) : Set G) :=
      (le_inf hMNV hMNV'').trans inf_normalizer_le_normalizer_inf
    rcases CFSG.GroupTheory.eq_or_eq_of_le_normalizer_of_closure_conj_eq hgen
      (U := V ⊓ Subgroup.centralizer (K : Set G)) inf_le_left (le_inf hV₀leV hV₀K) hMNU with h | h
    · exact h
    · exfalso
      apply hKnotcent
      rw [Subgroup.le_centralizer_iff]
      intro x hx
      have hx' : x ∈ V ⊓ Subgroup.centralizer (K : Set G) := by rw [h]; exact hx
      exact hx'.2
  have hv_notC : (v : G) ∉ Subgroup.centralizer (K : Set G) := by
    intro hvc
    exact hvV₀ (hC_V_K ▸ (show v ∈ V ⊓ Subgroup.centralizer (K : Set G) from ⟨hv, hvc⟩))
  rw [Subgroup.mem_centralizer_iff] at hv_notC
  push Not at hv_notC
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := hv_notC
  have hk₀comm : k₀ * v * k₀⁻¹ * v⁻¹ ≠ 1 := by
    intro h1
    apply hk₀ne
    have hconj : k₀ * v * k₀⁻¹ = v := by
      calc k₀ * v * k₀⁻¹ = (k₀ * v * k₀⁻¹ * v⁻¹) * v := by group
        _ = 1 * v := by rw [h1]
        _ = v := by group
    calc k₀ * v = k₀ * v * k₀⁻¹ * k₀ := by group
      _ = v * k₀ := by rw [hconj]
  let φ : K →* V₀ :=
    { toFun := fun q => ⟨q * v * q⁻¹ * v⁻¹, hKcent q q.2 v hv⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro q₁ q₂
        apply Subtype.ext
        have hc₁ : ⁅(q₁ : G), v⁆ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKNV q₁.2) v).mp hv) (V.inv_mem hv)
        have hc₂ : ⁅(q₂ : G), v⁆ ∈ V₀ := hKcent q₂ q₂.2 v hv
        have hq₁ : (q₁ : G) * ⁅(q₂ : G), v⁆ * (q₁ : G)⁻¹ = ⁅(q₂ : G), v⁆ := by
          rw [← Subgroup.mem_centralizer_iff.mp (hKleV₀ q₁.2) _ hc₂, mul_inv_cancel_right]
        show ⁅(q₁ : G) * q₂, v⁆ = ⁅(q₁ : G), v⁆ * ⁅(q₂ : G), v⁆
        rw [commutatorElement_mul_left_eq_conj_mul, hq₁]
        exact hcomm _ (hV₀leV hc₂) _ hc₁ }
  let D : Subgroup G := φ.range.map V₀.subtype
  have hD_le : D ≤ V₀ := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hD_ne : D ≠ ⊥ := by
    intro hbot
    have hmem : φ ⟨k₀, hk₀K⟩ ∈ φ.range := ⟨⟨k₀, hk₀K⟩, rfl⟩
    have : k₀ * v * k₀⁻¹ * v⁻¹ ∈ D := ⟨_, hmem, rfl⟩
    rw [hbot] at this
    exact hk₀comm (Subgroup.mem_bot.mp this)
  have hforward : ∀ x ∈ X, ∀ y ∈ D, x * y * x⁻¹ ∈ D := by
    intro x hx y hy
    obtain ⟨y', hy'range, hy'eq⟩ := Subgroup.mem_map.mp hy
    obtain ⟨q, hqeq⟩ := MonoidHom.mem_range.mp hy'range
    rw [← hy'eq, ← hqeq]
    have hxqK : x * q * x⁻¹ ∈ K :=
      ((Subgroup.mem_normalizer_iff.mp (hMNK (hXM hx))) q).mp q.2
    have hd' : x * v * x⁻¹ * v⁻¹ ∈ V₀ := hXv x hx
    have hd'V : x * v * x⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMNV (hXM hx)) _).mp hv) (V.inv_mem hv)
    have hc'V : (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKNV hxqK) _).mp hv) (V.inv_mem hv)
    have key : x * (q * v * q⁻¹ * v⁻¹) * x⁻¹ = (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ * v⁻¹ :=
      CFSG.Quasithin.D14.conj_commutator_eq (by group)
        (Subgroup.mem_centralizer_iff.mp (hKleV₀ hxqK) _ hd').symm (hcomm _ hd'V _ hc'V)
    refine Subgroup.mem_map.mpr
      ⟨φ ⟨x * q * x⁻¹, hxqK⟩, ⟨⟨x * q * x⁻¹, hxqK⟩, rfl⟩, ?_⟩
    show ((φ ⟨x * q * x⁻¹, hxqK⟩ : V₀) : G) = x * ((φ q : V₀) : G) * x⁻¹
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    exact key.symm
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward x hx y
    · intro hy
      have h := hforward x⁻¹ (X.inv_mem hx) (x * y * x⁻¹) hy
      have heq : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [heq] at h
  rcases hirr D hD_le hXD with hbot | hD_eq
  · exact absurd hbot hD_ne
  ·
    have hdD : d ∈ D := hD_eq ▸ hd
    obtain ⟨y', hy'range, hy'eq⟩ := Subgroup.mem_map.mp hdD
    obtain ⟨q, hqeq⟩ := MonoidHom.mem_range.mp hy'range
    refine ⟨(q : K), ⟨hKM q.2, hKleV₀ q.2⟩, hKcent q q.2, ?_⟩
    have hval : q * v * q⁻¹ * v⁻¹ = d := by
      have hthis := congrArg (fun z : V₀ => (z : G)) hqeq
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk] at hthis
      rw [hthis]
      exact hy'eq
    calc (q : K) * v * (q : K)⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
      _ = d * v := by rw [hval]
      _ = v * d := (hcomm v hv d (hV₀leV hd)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
