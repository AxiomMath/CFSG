module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2EDAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

variable {M : ModDataE H (eOmegaZ H D.T)}

theorem w183b2ed_mB_conj (x : Ctx188 D V₀ V H i j) {g : G} :
    mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g) = x.mB :=
  mBar_conj D.M V₀ V x.hyp.setting.isElemAbelian x.hyp.setting.pair.le
    x.hyp.setting.pair.le_normalizer x.hyp.setting.pair.le_normalizer₀ g

theorem w183b2ed_e_mem_normalizer (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    e' ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hnormEq : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer V g, x.hyp.setting.normalizer_eq]
  rw [hnormEq]
  exact x.w183b2ed_eOmegaZ_le_conj_M hg he'E

theorem w183b2ed_comm_mem (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T)
    {v : G} (hv : v ∈ conjSubgroup V g) : ⁅v, e'⁆ ∈ conjSubgroup V g := by
  have hnorm := x.w183b2ed_e_mem_normalizer hg he'E
  have hv' : e' * v⁻¹ * e'⁻¹ ∈ conjSubgroup V g :=
    (Subgroup.mem_normalizer_iff.mp hnorm v⁻¹).mp ((conjSubgroup V g).inv_mem hv)
  have hEq : ⁅v, e'⁆ = v * (e' * v⁻¹ * e'⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hEq]
  exact (conjSubgroup V g).mul_mem hv hv'

noncomputable def w183b2ed_commHom (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    ↥(conjSubgroup V g) →* ↥(conjSubgroup V g) where
  toFun v := ⟨⁅(v : G), e'⁆, x.w183b2ed_comm_mem hg he'E v.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' v₁ v₂ := by
    apply Subtype.ext
    show ⁅((v₁ : G) * (v₂ : G)), e'⁆ = ⁅((v₁ : G)), e'⁆ * ⁅((v₂ : G)), e'⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hab := E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
    have h₂ : ⁅((v₂ : G)), e'⁆ ∈ conjSubgroup V g := x.w183b2ed_comm_mem hg he'E v₂.2
    have h₁ : ⁅((v₁ : G)), e'⁆ ∈ conjSubgroup V g := x.w183b2ed_comm_mem hg he'E v₁.2
    have hc : (v₁ : G) * ⁅((v₂ : G)), e'⁆ = ⁅((v₂ : G)), e'⁆ * (v₁ : G) :=
      hab.comm v₁.2 h₂
    have hcv : (v₁ : G) * ⁅((v₂ : G)), e'⁆ * (v₁ : G)⁻¹ = ⁅((v₂ : G)), e'⁆ := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hcv]
    exact (hab.comm h₁ h₂).symm

theorem w183b2ed_ker_commHom (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    (x.w183b2ed_commHom hg he'E).ker =
      (conjSubgroup V g ⊓ Subgroup.centralizer ({e'} : Set G)).subgroupOf
        (conjSubgroup V g) := by
  ext v
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨v.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅(v : G), e'⁆ = 1 := congrArg Subtype.val h
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · rintro ⟨-, hc⟩
    apply Subtype.ext
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    exact commutatorElement_eq_one_iff_mul_comm.2 hc

theorem w183b2ed_mQuot_eq_rk_range (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.centralizer ({e'} : Set G)) =
      rk ↥(x.w183b2ed_commHom hg he'E).range := by
  rw [E3.mQuot_eq_rkIdx, ← x.w183b2ed_ker_commHom hg he'E, rkIdx, Subgroup.index_ker]
  rfl

theorem w183b2ed_mB_le_rk_range (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T)
    (he' : e' ∉ x.w183b2ed_EDg g) :
    x.mB ≤ rk ↥(x.w183b2ed_commHom hg he'E).range := by
  by_contra hle
  rw [not_le] at hle
  set V' : Subgroup G := conjSubgroup V g with hV'def
  set V₀' : Subgroup G := conjSubgroup V₀ g with hV₀'def
  set M' : Subgroup G := conjSubgroup D.M g with hM'def
  set C : Subgroup G := V' ⊓ Subgroup.centralizer ({e'} : Set G) with hCdef
  have hV'ab : IsElemAbelian 2 V' := E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
  have hV₀'le : V₀' ≤ V' := E3.conjSubgroup_mono_left g x.hyp.setting.pair.le
  have hM'norm : M' ≤ Subgroup.normalizer (V' : Set G) := by
    rw [hM'def, hV'def, ← E3.conjSubgroup_normalizer, x.hyp.setting.normalizer_eq]
  have hM'norm₀ : M' ≤ Subgroup.normalizer (V₀' : Set G) := by
    rw [hM'def, hV₀'def, ← E3.conjSubgroup_normalizer,
      x.hyp.setting.normalizer₀ x.hyp.ne_bot]
  have he'M : e' ∈ M' := x.w183b2ed_eOmegaZ_le_conj_M hg he'E
  have he2 : e' * e' = 1 := by
    simpa [pow_two] using x.hyp.isElemAbelian_eOmegaZ.2 e' he'E
  have ht2 : ∃ k : ℕ, orderOf e' = 2 ^ k := by
    have hdvd : orderOf e' ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hquot : E3.mQuot V' C = rk ↥(x.w183b2ed_commHom hg he'E).range :=
    x.w183b2ed_mQuot_eq_rk_range hg he'E
  have hmB : mBar M' V₀' V' hV'ab = x.mB := x.w183b2ed_mB_conj (g := g)
  have hlt : (E3.mQuot V' C : ℕ∞) < (mBar M' V₀' V' hV'ab : ℕ∞) := by
    rw [hquot, hmB]
    exact_mod_cast hle
  have hct : e' ∈ F11.CTilde M' V₀' V' :=
    mem_cTilde_of_mQuot_lt hV'ab hV₀'le hM'norm hM'norm₀ he'M ht2 inf_le_left inf_le_right hlt
  obtain ⟨-, h, hact⟩ := (mem_cTilde_iff hV'ab hM'norm).1 hct
  have hfix : ∀ v ∈ V', e' * v * e'⁻¹ * v⁻¹ ∈ V₀' :=
    (actTil_eq_one_iff V₀' V' hV'ab ⟨e', h⟩).1 hact
  have hnot : ¬ ∀ v ∈ V', ⁅v, e'⁆ ∈ V₀' := by
    intro hall
    exact he' ((x.w183b2ed_mem_EDg hg).2 ⟨he'E, hall⟩)
  obtain ⟨v, hv⟩ := not_forall.1 hnot
  rw [not_imp] at hv
  obtain ⟨hvV, hvcomm⟩ := hv
  rw [show ⁅v, e'⁆ = (e' * v * e'⁻¹ * v⁻¹)⁻¹ by
    rw [commutatorElement_def]; group] at hvcomm
  exact hvcomm ((conjSubgroup V₀ g).inv_mem (hfix v hvV))

theorem w183b2ed_targetSet_eq (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    {w : M.W | ∃ d ∈ M.img (vInH V H g), w = d (M.ι e') - M.ι e'} =
      (M.sp (((vInH V H g).subgroupOf (conjSubgroup V g)).map
        (x.w183b2ed_commHom hg he'E) |>.map (conjSubgroup V g).subtype) : Set M.W) := by
  set f := x.w183b2ed_commHom hg he'E with hf
  set H0 : Subgroup ↥(conjSubgroup V g) := (vInH V H g).subgroupOf (conjSubgroup V g) with hH0
  set S : Subgroup G := (H0.map f).map (conjSubgroup V g).subtype with hS
  have hSE : S ≤ eOmegaZ H D.T := by
    rintro s hs
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx'
    have hvDg : (v : G) ∈ vInH V H g := Subgroup.mem_subgroupOf.1 hv
    have hvH : (v : G) ∈ H := (Subgroup.mem_inf.1 hvDg).2
    have h1 : (v : G) * e' * (v : G)⁻¹ ∈ eOmegaZ H D.T :=
      (Subgroup.mem_normalizer_iff.1 (Hyp183.normalizer_eOmegaZ H D.T hvH) e').1 he'E
    show ⁅(v : G), e'⁆ ∈ eOmegaZ H D.T
    rw [commutatorElement_def]
    exact (eOmegaZ H D.T).mul_mem h1 ((eOmegaZ H D.T).inv_mem he'E)
  ext w
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨j, hjDg, rfl⟩ := M.mem_img.1 hd
    have hjH : (j : G) ∈ H := (Subgroup.mem_inf.1 hjDg).2
    have hjV : (j : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hjDg).1
    refine M.mem_sp.2 ⟨⁅(j : G), e'⁆, ⟨?_, hSE ?_⟩, M.ι_commutator hjH he'E⟩
    · exact Subgroup.mem_map.2 ⟨f ⟨(j : G), hjV⟩, Subgroup.mem_map.2
        ⟨⟨(j : G), hjV⟩, Subgroup.mem_subgroupOf.2 hjDg, rfl⟩, rfl⟩
    · exact Subgroup.mem_map.2 ⟨f ⟨(j : G), hjV⟩, Subgroup.mem_map.2
        ⟨⟨(j : G), hjV⟩, Subgroup.mem_subgroupOf.2 hjDg, rfl⟩, rfl⟩
  · intro hw
    obtain ⟨s, hs, hsw⟩ := M.mem_sp.1 hw
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hs.1
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx'
    have hvDg : (v : G) ∈ vInH V H g := Subgroup.mem_subgroupOf.1 hv
    have hvH : (v : G) ∈ H := (Subgroup.mem_inf.1 hvDg).2
    refine ⟨M.ρ ⟨(v : G), hvH⟩, M.mem_img.2 ⟨⟨(v : G), hvH⟩, hvDg, rfl⟩, ?_⟩
    rw [← hsw]
    exact M.ι_commutator hvH he'E

theorem w183b2ed_finrank_eq (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {w : M.W | ∃ d ∈ M.img (vInH V H g), w = d (M.ι e') - M.ι e'}) =
      rk ↥(((vInH V H g).subgroupOf (conjSubgroup V g)).map
        (x.w183b2ed_commHom hg he'E)) := by
  set f := x.w183b2ed_commHom hg he'E with hf
  set H0 : Subgroup ↥(conjSubgroup V g) := (vInH V H g).subgroupOf (conjSubgroup V g) with hH0
  set S : Subgroup G := (H0.map f).map (conjSubgroup V g).subtype with hS
  have hSE : S ≤ eOmegaZ H D.T := by
    rintro s hs
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx'
    have hvDg : (v : G) ∈ vInH V H g := Subgroup.mem_subgroupOf.1 hv
    have hvH : (v : G) ∈ H := (Subgroup.mem_inf.1 hvDg).2
    have h1 : (v : G) * e' * (v : G)⁻¹ ∈ eOmegaZ H D.T :=
      (Subgroup.mem_normalizer_iff.1 (Hyp183.normalizer_eOmegaZ H D.T hvH) e').1 he'E
    show ⁅(v : G), e'⁆ ∈ eOmegaZ H D.T
    rw [commutatorElement_def]
    exact (eOmegaZ H D.T).mul_mem h1 ((eOmegaZ H D.T).inv_mem he'E)
  have hsp : Submodule.span (ZMod 2)
      {w : M.W | ∃ d ∈ M.img (vInH V H g), w = d (M.ι e') - M.ι e'} = M.sp S := by
    rw [x.w183b2ed_targetSet_eq (M := M) hg he'E]
    exact Submodule.span_eq (M.sp S)
  rw [hsp]
  have hcardS : Nat.card ↥S = Nat.card ↥(H0.map f) :=
    Subgroup.card_map_of_injective (K := H0.map f) (conjSubgroup V g).subtype_injective
  have hbij' : Nat.card ↥S = Nat.card ↥(M.sp S) := by
    refine Nat.card_congr (Equiv.ofBijective (fun s : ↥S =>
      (⟨M.ι (s : G), ?_⟩ : ↥(M.sp S))) ⟨?_, ?_⟩)
    · refine M.mem_sp.2 ⟨s, ⟨s.2, hSE s.2⟩, rfl⟩
    · intro a b hab
      apply Subtype.ext
      exact M.ι_injOn (hSE a.2) (hSE b.2) (Subtype.ext_iff.mp hab)
    · intro y
      obtain ⟨s, hs, hsy⟩ := M.mem_sp.1 y.2
      exact ⟨⟨s, hs.1⟩, Subtype.ext hsy⟩
  have hbij : Nat.card ↥(M.sp S) = Nat.card ↥S := hbij'.symm
  have hcard : Nat.card ↥(M.sp S) = Nat.card ↥(H0.map f) := hbij.trans hcardS
  have hrkS : rk ↥S = rk ↥(H0.map f) := by rw [rk, rk, hcardS]
  have hS2 : ∀ s : ↥S, s ^ 2 = 1 := fun s => Subtype.ext (by
    have h := x.hyp.isElemAbelian_eOmegaZ.2 (s : G) (hSE s.2)
    simpa [pow_two] using h)
  have hP : IsPGroup 2 ↥S := isPGroup_two_of_sq_eq_one hS2
  have hpowL : Nat.card ↥(M.sp S) = 2 ^ Module.finrank (ZMod 2) ↥(M.sp S) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(M.sp S)), Nat.card_zmod]
  have hpowR : Nat.card ↥S = 2 ^ rk ↥S := card_eq_two_pow_of_isPGroup hP
  have hpow : 2 ^ Module.finrank (ZMod 2) ↥(M.sp S) = 2 ^ rk ↥(H0.map f) := by
    rw [← hpowL, hbij, hpowR, hrkS]
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow

theorem w183b2ed_rk_range_le (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T) :
    rk ↥(x.w183b2ed_commHom hg he'E).range ≤
      rk ↥(((vInH V H g).subgroupOf (conjSubgroup V g)).map
        (x.w183b2ed_commHom hg he'E)) +
        E3.mQuot (conjSubgroup V g) (vInH V H g) := by
  set f := x.w183b2ed_commHom hg he'E with hf
  set H0 : Subgroup ↥(conjSubgroup V g) := (vInH V H g).subgroupOf (conjSubgroup V g) with hH0
  have hcard : (H0.map f).relIndex f.range * Nat.card ↥(H0.map f) = Nat.card ↥f.range := by
    have h := Subgroup.relIndex_mul_card (H := H0.map f) (K := f.range)
    rwa [inf_eq_left.2 (Subgroup.map_le_range f H0)] at h
  have hrk : rk ↥f.range =
      padicValNat 2 ((H0.map f).relIndex f.range) + rk ↥(H0.map f) := by
    rw [rk, ← hcard,
      padicValNat.mul (E3.relIndex_ne_zero' f.range (H0.map f)) (Nat.card_pos.ne'), rk]
  have hmap : (H0.map f).relIndex f.range = (H0 ⊔ f.ker).relIndex ⊤ := by
    rw [MonoidHom.range_eq_map f, Subgroup.relIndex_map_map, top_sup_eq]
  have hdvd : (H0 ⊔ f.ker).relIndex ⊤ ∣ H0.relIndex ⊤ := by
    refine ⟨H0.relIndex (H0 ⊔ f.ker), ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex (H := H0) (K := H0 ⊔ f.ker) (L := ⊤)
      le_sup_left le_top, mul_comm]
  have hH0rel : H0.relIndex ⊤ = (vInH V H g).relIndex (conjSubgroup V g) := by
    rw [Subgroup.relIndex_top_right, hH0]
    rfl
  have hle : padicValNat 2 ((H0.map f).relIndex f.range) ≤
      E3.mQuot (conjSubgroup V g) (vInH V H g) := by
    calc padicValNat 2 ((H0.map f).relIndex f.range)
        = padicValNat 2 ((H0 ⊔ f.ker).relIndex ⊤) := by rw [hmap]
      _ ≤ padicValNat 2 (H0.relIndex ⊤) :=
          padicValNat_two_le_of_dvd (E3.relIndex_ne_zero' ⊤ H0) hdvd
      _ = padicValNat 2 ((vInH V H g).relIndex (conjSubgroup V g)) := by rw [hH0rel]
      _ = E3.mQuot (conjSubgroup V g) (vInH V H g) := rfl
  rw [hrk]
  omega

theorem w183b2ed_rank_aux (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e' : G} (he'E : e' ∈ eOmegaZ H D.T)
    (he' : e' ∉ x.w183b2ed_EDg g) :
    x.mB ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {w : M.W | ∃ d ∈ M.img (vInH V H g), w = d (M.ι e') - M.ι e'}) +
      E3.mQuot (conjSubgroup V g) (vInH V H g) := by
  rw [x.w183b2ed_finrank_eq hg he'E]
  exact (x.w183b2ed_mB_le_rk_range hg he'E he').trans (x.w183b2ed_rk_range_le hg he'E)

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
