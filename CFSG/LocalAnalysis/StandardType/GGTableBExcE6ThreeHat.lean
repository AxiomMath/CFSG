module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Levi
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc.E6Three

section Hat

variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def rootDiagHom : (Fin τ.rank → Kˣ) →* ModGL τ K where
  toFun := rootDiagUnit τ
  map_one' := rootDiagUnit_one
  map_mul' a b := rootDiagUnit_mul a b

variable {τ K}

theorem rootDiagHom_apply (a : Fin τ.rank → Kˣ) : rootDiagHom τ K a = rootDiagUnit τ a :=
  rfl

theorem mapsRootLines_rootDiagUnit (a : Fin τ.rank → Kˣ) :
    MapsRootLines (rootDiagUnit τ a) 1 := fun α hα => by
  obtain ⟨c, hc⟩ := (CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_diagonalGroup (K := K) a).2 α hα
  exact ⟨c, by rw [hc, one_smul]⟩

theorem conj_rootDiagUnit_mem_monomialSubgroup (a : Fin τ.rank → Kˣ) {n : ModGL τ K}
    (hn : n ∈ monomialSubgroup τ K) :
    rootDiagUnit τ a * n * (rootDiagUnit τ a)⁻¹ ∈ monomialSubgroup τ K := by
  have hle : monomialSubgroup τ K ≤
      (monomialSubgroup τ K).comap (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        conj_rootDiagUnit_of_mem_torusGroup a hh]
      exact Subgroup.mem_sup_left hh
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rootDiagUnit_conj_weylElt_one]
      exact mul_mem (torusElt_mem_monomialSubgroup i _) (weylElt_mem_monomialSubgroup i)
  exact hle hn

variable (τ K) in
@[expose] def hatGroup : Subgroup (ModGL τ K) where
  carrier := {x | ∃ g ∈ adjointGroup τ K, ∃ a, x = g * rootDiagUnit τ a}
  mul_mem' := by
    rintro _ _ ⟨g, hg, a, rfl⟩ ⟨g', hg', b, rfl⟩
    refine ⟨g * (rootDiagUnit τ a * g' * (rootDiagUnit τ a)⁻¹),
      mul_mem hg (conj_rootDiagUnit_mem_adjointGroup a hg'), a * b, ?_⟩
    rw [rootDiagUnit_mul]
    group
  one_mem' := ⟨1, one_mem _, 1, by rw [rootDiagUnit_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨g, hg, a, rfl⟩
    refine ⟨rootDiagUnit τ a⁻¹ * g⁻¹ * (rootDiagUnit τ a⁻¹)⁻¹,
      conj_rootDiagUnit_mem_adjointGroup a⁻¹ (inv_mem hg), a⁻¹, ?_⟩
    rw [← rootDiagUnit_inv]
    group

variable (τ K) in
@[expose] def monoHat : Subgroup (ModGL τ K) where
  carrier := {x | ∃ n ∈ monomialSubgroup τ K, ∃ a, x = n * rootDiagUnit τ a}
  mul_mem' := by
    rintro _ _ ⟨n, hn, a, rfl⟩ ⟨n', hn', b, rfl⟩
    refine ⟨n * (rootDiagUnit τ a * n' * (rootDiagUnit τ a)⁻¹),
      mul_mem hn (conj_rootDiagUnit_mem_monomialSubgroup a hn'), a * b, ?_⟩
    rw [rootDiagUnit_mul]
    group
  one_mem' := ⟨1, one_mem _, 1, by rw [rootDiagUnit_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨n, hn, a, rfl⟩
    refine ⟨rootDiagUnit τ a⁻¹ * n⁻¹ * (rootDiagUnit τ a⁻¹)⁻¹,
      conj_rootDiagUnit_mem_monomialSubgroup a⁻¹ (inv_mem hn), a⁻¹, ?_⟩
    rw [← rootDiagUnit_inv]
    group

theorem rootDiagUnit_mem_monoHat (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ monoHat τ K :=
  ⟨1, one_mem _, a, (one_mul _).symm⟩

theorem monomial_le_monoHat : monomialSubgroup τ K ≤ monoHat τ K :=
  fun n hn => ⟨n, hn, 1, by rw [rootDiagUnit_one, mul_one]⟩

theorem monoHat_le_hatGroup : monoHat τ K ≤ hatGroup τ K := by
  rintro _ ⟨n, hn, a, rfl⟩
  exact ⟨n, monomialSubgroup_le_adjointGroup' hn, a, rfl⟩

theorem adjointGroup_le_hatGroup : adjointGroup τ K ≤ hatGroup τ K :=
  fun g hg => ⟨g, hg, 1, by rw [rootDiagUnit_one, mul_one]⟩

theorem rootDiagUnit_mem_hatGroup (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ hatGroup τ K :=
  monoHat_le_hatGroup (rootDiagUnit_mem_monoHat a)

theorem hatGroup_le_normalizer :
    hatGroup τ K ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)) := by
  rintro _ ⟨g, hg, a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * rootDiagUnit τ a * h * (g * rootDiagUnit τ a)⁻¹ =
        g * (rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hg (conj_rootDiagUnit_mem_adjointGroup a hh)) (inv_mem hg)
  · intro hh
    have e : h = rootDiagUnit τ a⁻¹ * (g⁻¹ * (g * rootDiagUnit τ a * h *
        (g * rootDiagUnit τ a)⁻¹) * g) * (rootDiagUnit τ a⁻¹)⁻¹ := by
      rw [← rootDiagUnit_inv]
      group
    rw [e]
    exact conj_rootDiagUnit_mem_adjointGroup a⁻¹ (mul_mem (mul_mem (inv_mem hg) hh) hg)

variable (τ K) in
@[expose] noncomputable def hatAut : hatGroup τ K →* MulAut (adjointGroup τ K) :=
  (adjointGroup τ K).normalizerMonoidHom.comp (Subgroup.inclusion hatGroup_le_normalizer)

theorem coe_hatAut_apply (x : hatGroup τ K) (h : adjointGroup τ K) :
    ((hatAut τ K x h : adjointGroup τ K) : ModGL τ K) =
      (x : ModGL τ K) * h * (x : ModGL τ K)⁻¹ :=
  rfl


theorem exists_mapsRootLines_of_mem_monoHat {x : ModGL τ K} (hx : x ∈ monoHat τ K) :
    ∃ w : WeylGroup τ, MapsRootLines x w := by
  obtain ⟨n, hn, a, rfl⟩ := hx
  refine ⟨weylQuotientHom τ K ⟨n, hn⟩ * 1, ?_⟩
  exact (mapsRootLines_weylQuotientHom ⟨n, hn⟩).mul (mapsRootLines_rootDiagUnit a)

variable (τ K) in
@[expose] noncomputable def psiHat : monoHat τ K →* WeylGroup τ where
  toFun x := (exists_mapsRootLines_of_mem_monoHat x.2).choose
  map_one' := ((exists_mapsRootLines_of_mem_monoHat (one_mem (monoHat τ K))).choose_spec).unique
    mapsRootLines_one
  map_mul' x y := ((exists_mapsRootLines_of_mem_monoHat (x * y).2).choose_spec).unique
    ((exists_mapsRootLines_of_mem_monoHat x.2).choose_spec.mul
      (exists_mapsRootLines_of_mem_monoHat y.2).choose_spec)

theorem mapsRootLines_psiHat (x : monoHat τ K) :
    MapsRootLines (x : ModGL τ K) (psiHat τ K x) :=
  (exists_mapsRootLines_of_mem_monoHat x.2).choose_spec

theorem psiHat_eq {x : monoHat τ K} {w : WeylGroup τ} (h : MapsRootLines (x : ModGL τ K) w) :
    psiHat τ K x = w :=
  (mapsRootLines_psiHat x).unique h

theorem psiHat_mul_rootDiagUnit {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K)
    (a : Fin τ.rank → Kˣ) (hx : n * rootDiagUnit τ a ∈ monoHat τ K) :
    psiHat τ K ⟨_, hx⟩ = weylQuotientHom τ K ⟨n, hn⟩ := by
  refine psiHat_eq ?_
  have h := (mapsRootLines_weylQuotientHom ⟨n, hn⟩).mul (mapsRootLines_rootDiagUnit (K := K) a)
  rwa [mul_one] at h

theorem psiHat_of_mem_monomial {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K) :
    psiHat τ K ⟨n, monomial_le_monoHat hn⟩ = weylQuotientHom τ K ⟨n, hn⟩ :=
  psiHat_eq (mapsRootLines_weylQuotientHom ⟨n, hn⟩)

theorem exists_rootDiagUnit_eq_of_psiHat_eq_one {x : monoHat τ K} (hx : psiHat τ K x = 1) :
    ∃ b, (x : ModGL τ K) = rootDiagUnit τ b := by
  obtain ⟨n, hn, a, hxa⟩ := x.2
  have hρ : weylQuotientHom τ K ⟨n, hn⟩ = 1 := by
    rw [← psiHat_mul_rootDiagUnit hn a (hxa ▸ x.2)]
    rw [← hx]
    congr 1
    exact Subtype.ext hxa.symm
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  have hnT : n ∈ torusGroup τ K := by
    have h1 : (⟨n, hn⟩ : monomialSubgroup τ K) ∈ (weylQuotientHom τ K).ker := hρ
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hnT
  exact ⟨c * a, by rw [hxa, rootDiagUnit_mul]⟩

theorem conj_rootDiagUnit_of_mem_monoHat (x : monoHat τ K) (b : Fin τ.rank → Kˣ) :
    (x : ModGL τ K) * rootDiagUnit τ b * (x : ModGL τ K)⁻¹ =
      rootDiagUnit τ (weylTuple (psiHat τ K x) b) := by
  obtain ⟨n, hn, a, hxa⟩ := x.2
  have hψ : psiHat τ K x = weylQuotientHom τ K ⟨n, hn⟩ := by
    rw [← psiHat_mul_rootDiagUnit hn a (hxa ▸ x.2)]
    congr 1
    exact Subtype.ext hxa
  rw [hψ, hxa]
  have hc : rootDiagUnit τ a * rootDiagUnit τ b * (rootDiagUnit τ a)⁻¹ = rootDiagUnit τ b := by
    rw [← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]
  calc n * rootDiagUnit τ a * rootDiagUnit τ b * (n * rootDiagUnit τ a)⁻¹ =
      n * (rootDiagUnit τ a * rootDiagUnit τ b * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by group
    _ = _ := by
      rw [hc]
      exact monomial_conj_rootDiagUnit_weylTuple hn (mapsRootLines_weylQuotientHom ⟨n, hn⟩) b

variable (τ K) in
@[expose] noncomputable def xHat (S : Subgroup (WeylGroup τ)) : Subgroup (ModGL τ K) :=
  (S.comap (psiHat τ K)).map (monoHat τ K).subtype

theorem mem_xHat {S : Subgroup (WeylGroup τ)} {x : ModGL τ K} :
    x ∈ xHat τ K S ↔ ∃ hx : x ∈ monoHat τ K, psiHat τ K ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem xHat_le_monoHat (S : Subgroup (WeylGroup τ)) : xHat τ K S ≤ monoHat τ K :=
  fun _ hx => (mem_xHat.mp hx).1

theorem xHat_le_hatGroup (S : Subgroup (WeylGroup τ)) : xHat τ K S ≤ hatGroup τ K :=
  (xHat_le_monoHat S).trans monoHat_le_hatGroup

theorem rootDiagUnit_mem_xHat (S : Subgroup (WeylGroup τ)) (a : Fin τ.rank → Kˣ) :
    rootDiagUnit τ a ∈ xHat τ K S := by
  refine mem_xHat.mpr ⟨rootDiagUnit_mem_monoHat a, ?_⟩
  rw [psiHat_eq (mapsRootLines_rootDiagUnit a)]
  exact one_mem S

theorem exists_mul_of_mem_hatGroup (S : Subgroup (WeylGroup τ)) {x : ModGL τ K}
    (hx : x ∈ hatGroup τ K) : ∃ g ∈ adjointGroup τ K, ∃ y ∈ xHat τ K S, x = g * y := by
  obtain ⟨g, hg, a, rfl⟩ := hx
  exact ⟨g, hg, _, rootDiagUnit_mem_xHat S a, rfl⟩


theorem mem_weylX_iff_mem_xHat {S : Subgroup (WeylGroup τ)} {g : adjointGroup τ K} :
    g ∈ weylX τ K S ↔ (g : ModGL τ K) ∈ xHat τ K S := by
  rw [mem_weylX]
  constructor
  · rintro ⟨hg, h⟩
    refine mem_xHat.mpr ⟨monomial_le_monoHat hg, ?_⟩
    rwa [psiHat_of_mem_monomial hg]
  · intro h
    obtain ⟨hx, hS⟩ := mem_xHat.mp h
    obtain ⟨n, hn, a, hna⟩ := hx
    have hda : rootDiagUnit τ a ∈ adjointGroup τ K := by
      have e : rootDiagUnit τ a = n⁻¹ * g := by rw [hna]; group
      rw [e]
      exact mul_mem (inv_mem (monomialSubgroup_le_adjointGroup' hn)) g.2
    have hdT := CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup a hda
    have hgN : (g : ModGL τ K) ∈ monomialSubgroup τ K := by
      rw [hna]
      exact mul_mem hn (Subgroup.mem_sup_left hdT)
    refine ⟨hgN, ?_⟩
    rw [← psiHat_of_mem_monomial hgN]
    exact hS

theorem eq_one_of_hatAut_eq_one {x : hatGroup τ K} (hxm : (x : ModGL τ K) ∈ monoHat τ K)
    (h1 : hatAut τ K x = 1) : x = 1 := by
  have hcomm : ∀ h ∈ adjointGroup τ K, (x : ModGL τ K) * h * (x : ModGL τ K)⁻¹ = h :=
    fun h hh => by
      have e := congrArg Subtype.val (DFunLike.congr_fun h1 (⟨h, hh⟩ : adjointGroup τ K))
      rw [coe_hatAut_apply] at e
      exact e
  obtain ⟨n, hn, a, hna⟩ := hxm
  have hfix : ∀ i, weylQuotientHom τ K ⟨n, hn⟩ • (Pi.single i 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 := by
    intro i
    have hr := isRoot_single τ i
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hr
    have e1 := hcomm _ (pinnedX_mem_adjointGroup (K := K) (Pi.single i 1) 1)
    rw [hna] at e1
    have e2 : n * rootDiagUnit τ a * pinnedX τ K (Pi.single i 1) 1 * (n * rootDiagUnit τ a)⁻¹ =
        n * (rootDiagUnit τ a * pinnedX τ K (Pi.single i 1) 1 * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by
      group
    rw [e2, rootDiagUnit_conj_pinnedX a hr, hμ] at e1
    exact CFSG.SeitzReduction.EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul hr _) hr
      (by simp) one_ne_zero e1
  have hρ1 : weylQuotientHom τ K ⟨n, hn⟩ = 1 := ext_single fun i => by rw [hfix i, one_smul]
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  have hnT : n ∈ torusGroup τ K := by
    have h2 : (⟨n, hn⟩ : monomialSubgroup τ K) ∈ (weylQuotientHom τ K).ker := hρ1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hnT
  rw [← rootDiagUnit_mul] at hna
  have hb : ∀ i, (c * a) i = 1 := by
    intro i
    have e1 := hcomm _ (pinnedX_mem_adjointGroup (K := K) (Pi.single i 1) 1)
    rw [hna, rootDiagUnit_conj_pinnedX (c * a) (isRoot_single τ i), TableBExc.rootChar_single,
      mul_one] at e1
    exact Units.ext (pinnedX_injective τ K _ e1)
  apply Subtype.ext
  rw [hna, show c * a = 1 from funext hb, rootDiagUnit_one]
  rfl

end Hat

end TableBExc.E6Three

end CFSG.StandardType
