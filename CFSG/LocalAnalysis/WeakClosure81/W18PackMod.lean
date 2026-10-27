module

public import CFSG.LocalAnalysis.WeakClosure81.W19ModE
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.WeakClosure81.Thirteen
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

@[expose] def sp (S : Subgroup G) : Submodule (ZMod 2) M.W where
  carrier := M.ι '' ((S ⊓ E : Subgroup G) : Set G)
  add_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact ⟨e * e', (S ⊓ E).mul_mem he he', M.ι_mul e he.2 e' he'.2⟩
  zero_mem' := ⟨1, (S ⊓ E).one_mem, M.ι_one⟩
  smul_mem' := by
    rintro c _ ⟨e, he, rfl⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, (S ⊓ E).one_mem, M.ι_one⟩
    · rw [one_smul]
      exact ⟨e, he, rfl⟩

theorem mem_sp {S : Subgroup G} {w : M.W} : w ∈ M.sp S ↔ ∃ e ∈ S ⊓ E, M.ι e = w := Iff.rfl

theorem sp_mono {S S' : Subgroup G} (h : S ≤ S') : M.sp S ≤ M.sp S' := by
  rintro w ⟨e, he, rfl⟩
  exact ⟨e, ⟨h he.1, he.2⟩, rfl⟩

theorem sp_eq_bot_iff {S : Subgroup G} : M.sp S = ⊥ ↔ S ⊓ E = ⊥ := by
  constructor
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxsp : M.ι x ∈ M.sp S := ⟨x, hx, rfl⟩
    have hx0 : M.ι x = 0 := by rw [h] at hxsp; simpa using hxsp
    exact M.ι_eq_zero x hx.2 hx0
  · intro h
    rw [Submodule.eq_bot_iff]
    rintro w ⟨e, he, rfl⟩
    have he1 : e = 1 := by
      have : e ∈ (⊥ : Subgroup G) := by rw [← h]; exact he
      simpa using this
    rw [he1, M.ι_one]

theorem sp_inf (S S' : Subgroup G) : M.sp (S ⊓ S') = M.sp S ⊓ M.sp S' := by
  ext w
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, ⟨he.1.1, he.2⟩, rfl⟩, ⟨e, ⟨he.1.2, he.2⟩, rfl⟩⟩
  · rintro ⟨⟨e, he, rfl⟩, ⟨e', he', he'e⟩⟩
    have hee' : e = e' := M.ι_injOn he.2 he'.2 he'e.symm
    exact ⟨e, ⟨⟨he.1, hee' ▸ he'.1⟩, he.2⟩, rfl⟩

theorem fixSub_img {B : Subgroup G} (hB : B ≤ J) :
    fixSub (M.img B) = M.sp (Subgroup.centralizer (B : Set G)) := by
  ext w
  constructor
  · intro hw
    obtain ⟨e, he, rfl⟩ := M.ι_surj w
    refine ⟨e, ⟨?_, he⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have hbJ : b ∈ J := hB hb
    have hfix : M.ρ ⟨b, hbJ⟩ (M.ι e) = M.ι e :=
      hw (M.ρ ⟨b, hbJ⟩) (M.mem_img.2 ⟨⟨b, hbJ⟩, hb, rfl⟩)
    have hbn : b * e * b⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (M.le_normalizer hbJ) e).1 he
    have heq : b * e * b⁻¹ = e := by
      rw [M.ρ_ι ⟨b, hbJ⟩ e he] at hfix
      exact M.ι_injOn hbn he hfix
    calc b * e = (b * e * b⁻¹) * b := by group
      _ = e * b := by rw [heq]
  · rintro ⟨e, ⟨heC, heE⟩, rfl⟩ r hr
    obtain ⟨j, hjB, rfl⟩ := M.mem_img.1 hr
    rw [M.ρ_ι j e heE]
    congr 1
    have hc := Subgroup.mem_centralizer_iff.1 heC (j : G) hjB
    rw [hc]
    group

theorem commSpace_img_sp_le {A X S : Subgroup G} (hA : A ≤ J) (h : ⁅X ⊓ E, A⁆ ≤ S) :
    commSpace (M.img A) (M.sp X) ≤ M.sp S := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨r, hr, v, hv, rfl⟩
  obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hr
  obtain ⟨e, he, rfl⟩ := hv
  have hmem : ⁅(j : G), e⁆ ∈ ⁅X ⊓ E, A⁆ := by
    have h1 : ⁅(j : G), e⁆ ∈ ⁅A, X ⊓ E⁆ :=
      Subgroup.commutator_mem_commutator hjA he
    rwa [Subgroup.commutator_comm] at h1
  have hEcomm : ⁅(j : G), e⁆ ∈ E := by
    have h1 : ⁅(j : G), e⁆ ∈ ⁅E, A⁆ := by
      have h2 : ⁅(j : G), e⁆ ∈ ⁅A, E⁆ :=
        Subgroup.commutator_mem_commutator hjA he.2
      rwa [Subgroup.commutator_comm] at h2
    exact M.commutator_le_E hA h1
  rw [← M.ι_commutator j.2 he.2]
  exact ⟨⁅(j : G), e⁆, ⟨h hmem, hEcomm⟩, rfl⟩

theorem commSpace_commSub_img_eq_bot {A : Subgroup G} (hA : A ≤ J) (h : ⁅⁅E, A⁆, A⁆ = ⊥) :
    commSpace (M.img A) (commSub (M.img A)) = ⊥ := by
  have hle : commSub (M.img A) ≤ M.sp ⁅E, A⁆ := by
    rw [CFSG.SignalizerFunctorTheorem.Quadratic.commSub]
    refine Submodule.span_le.2 ?_
    rintro w ⟨r, hr, v, hv, rfl⟩
    obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hr
    obtain ⟨e, he, rfl⟩ := M.ι_surj v
    have hmem : ⁅(j : G), e⁆ ∈ ⁅E, A⁆ := by
      have h1 : ⁅(j : G), e⁆ ∈ ⁅A, E⁆ :=
        Subgroup.commutator_mem_commutator hjA he
      rwa [Subgroup.commutator_comm] at h1
    rw [← M.ι_commutator j.2 he]
    exact ⟨⁅(j : G), e⁆, ⟨hmem, M.commutator_le_E hA hmem⟩, rfl⟩
  have hinf : ⁅⁅E, A⁆ ⊓ E, A⁆ ≤ ⊥ :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans (le_of_eq h)
  have h2 : commSpace (M.img A) (M.sp ⁅E, A⁆) ≤ M.sp (⊥ : Subgroup G) :=
    M.commSpace_img_sp_le hA hinf
  have hbot : M.sp (⊥ : Subgroup G) = ⊥ := M.sp_eq_bot_iff.2 (by simp)
  refine le_antisymm ?_ bot_le
  calc commSpace (M.img A) (commSub (M.img A))
      ≤ commSpace (M.img A) (M.sp ⁅E, A⁆) := by
        rw [commSpace, commSpace]
        refine Submodule.span_mono ?_
        rintro w ⟨k, hk, u, hu, rfl⟩
        exact ⟨k, hk, u, hle hu, rfl⟩
    _ ≤ M.sp (⊥ : Subgroup G) := h2
    _ = ⊥ := hbot

theorem conjSub_sp (X : Subgroup G) (j : ↥J) :
    conjSub (M.ρ j) (M.sp X) = M.sp (conjSubgroup X (j : G)⁻¹) := by
  ext w
  constructor
  · intro hw
    rw [conjSub, Submodule.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨e, he, rfl⟩ := hu
    refine ⟨(j : G) * e * (j : G)⁻¹, ⟨?_, ?_⟩, (M.ρ_ι j e he.2).symm⟩
    · refine mem_conjSubgroup_iff.mpr ?_
      have h1 : (j : G)⁻¹ * ((j : G) * e * (j : G)⁻¹) * ((j : G)⁻¹)⁻¹ = e := by group
      rw [h1]
      exact he.1
    · exact (Subgroup.mem_normalizer_iff.1 (M.le_normalizer j.2) e).1 he.2
  · intro hw
    obtain ⟨e', he', rfl⟩ := hw
    have he'X : (j : G)⁻¹ * e' * (j : G) ∈ X := by
      simpa only [inv_inv] using mem_conjSubgroup_iff.mp he'.1
    have he'E : (j : G)⁻¹ * e' * (j : G) ∈ E := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.1 (M.le_normalizer (J.inv_mem j.2)) e').1 he'.2
    refine ⟨M.ι ((j : G)⁻¹ * e' * (j : G)), ⟨_, ⟨he'X, he'E⟩, rfl⟩, ?_⟩
    change (M.ρ j) (M.ι ((j : G)⁻¹ * e' * (j : G))) = M.ι e'
    rw [M.ρ_ι j ((j : G)⁻¹ * e' * (j : G)) he'E]
    congr 1
    group

theorem exists_preimage {A : Subgroup G} (hA : A ≤ J) {B' : Subgroup (LGL 2 M.W)}
    (hB : B' ≤ M.img A) :
    ∃ B : Subgroup G, B ≤ A ∧ A ⊓ Subgroup.centralizer (E : Set G) ≤ B ∧ M.img B = B' := by
  refine ⟨A ⊓ (B'.comap M.ρ).map J.subtype, inf_le_left, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨hxA, ?_⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hA hxA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : M.ρ ⟨x, hA hxA⟩ = 1 := (M.ρ_eq_one_iff _).2 (by simpa using hxC)
    rw [h1]
    exact B'.one_mem
  · ext r
    constructor
    · intro hr
      obtain ⟨j, hjB, rfl⟩ := M.mem_img.1 hr
      obtain ⟨j', hj', hj'eq⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hjB).2
      rw [Subgroup.mem_comap] at hj'
      have hjj : j' = j := Subtype.ext hj'eq
      rw [← hjj]
      exact hj'
    · intro hr
      obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 (hB hr)
      refine M.mem_img.2 ⟨j, Subgroup.mem_inf.2 ⟨hjA, ?_⟩, rfl⟩
      exact Subgroup.mem_map.2 ⟨j, by rwa [Subgroup.mem_comap], rfl⟩

theorem mOf_img {A B : Subgroup G} (hA : A ≤ J) (hAab : IsElemAbelian 2 A) (hBA : B ≤ A)
    (hB : A ⊓ Subgroup.centralizer (E : Set G) ≤ B) :
    mOf (M.img A) (M.img B) = E3.mQuot A B := by
  set CE := Subgroup.centralizer (E : Set G) with hCE
  have hCAB : CE ⊓ A ≤ B := fun x hx => hB ⟨hx.2, hx.1⟩
  have hcardA : Nat.card (M.img A) = (CE ⊓ A).relIndex A := by
    rw [M.card_img hA, Subgroup.inf_relIndex_right]
  have hCEB : CE ⊓ B = CE ⊓ A := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hBA hx.2⟩
    · intro x hx
      exact ⟨hx.1, hB ⟨hx.2, hx.1⟩⟩
  have hcardB : Nat.card (M.img B) = (CE ⊓ A).relIndex B := by
    rw [M.card_img (hBA.trans hA), ← hCEB, Subgroup.inf_relIndex_right]
  have hrelA : (CE ⊓ A).relIndex A = (CE ⊓ A).relIndex B * B.relIndex A :=
    (Subgroup.relIndex_mul_relIndex (H := CE ⊓ A) (K := B) (L := A) hCAB hBA).symm
  have hrelImg : (M.img B).relIndex (M.img A) * Nat.card (M.img B) = Nat.card (M.img A) := by
    have h := Subgroup.relIndex_mul_card (H := M.img B) (K := M.img A)
    rwa [inf_eq_left.2 (M.img_mono hBA)] at h
  have hNne : (CE ⊓ A).relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (M.img B).relIndex (M.img A) = B.relIndex A := by
    apply mul_right_cancel₀ hNne
    calc (M.img B).relIndex (M.img A) * (CE ⊓ A).relIndex B
        = (M.img B).relIndex (M.img A) * Nat.card (M.img B) := by rw [hcardB]
      _ = (CE ⊓ A).relIndex B * B.relIndex A := by rw [hrelImg, hcardA, hrelA]
      _ = B.relIndex A * (CE ⊓ A).relIndex B := by rw [mul_comm]
  change Nat.log 2 ((M.img B).relIndex (M.img A)) = E3.mQuot A B
  rw [hrel, E3.relIndex_eq_two_pow hAab.isPGroup B, Nat.log_pow (show 1 < 2 by norm_num)]

theorem isElemAbelian_img {S : Subgroup G} (hS : IsElemAbelian 2 S) :
    IsElemAbelian 2 (M.img S) := by
  unfold img
  exact (hS.subgroupOf J).map M.ρ

private theorem isSylowIn_img {T : Subgroup G} (hT : IsSylowIn 2 T J) :
    IsSylowIn 2 (M.img T) (M.img J) := by
  have hrelidx : (M.img T).relIndex (M.img J) = ((T.subgroupOf J) ⊔ M.ρ.ker).index := by
    unfold img
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_map_map]
    simp
  have hdvd : ((T.subgroupOf J) ⊔ M.ρ.ker).index ∣ T.relIndex J :=
    Subgroup.index_dvd_of_le (H := T.subgroupOf J)
      (K := (T.subgroupOf J) ⊔ M.ρ.ker) le_sup_left
  refine ⟨M.img_mono hT.le, M.isPGroup_img hT.isPGroup, ?_⟩
  rw [hrelidx]
  exact fun h => hT.not_dvd_relIndex (h.trans hdvd)

private theorem fixes_conjClosure (x : LGL 2 M.W) (Z : Subgroup G) (hZE : Z ≤ E)
    (hgen : E ≤ CFSG.Quasithin.conjClosure Z J)
    (h : ∀ y ∈ J, ∀ z ∈ Z, x (M.ι (y * z * y⁻¹)) = M.ι (y * z * y⁻¹)) :
    ∀ e ∈ E, x (M.ι e) = M.ι e := by
  have hclE : CFSG.Quasithin.conjClosure Z J ≤ E :=
    CFSG.Quasithin.conjClosure_le fun y hy z hz =>
      (Subgroup.mem_normalizer_iff.1 (M.le_normalizer hy) z).1 (hZE hz)
  intro e he
  have hmem : e ∈ CFSG.Quasithin.conjClosure Z J := hgen he
  rw [CFSG.Quasithin.conjClosure] at hmem
  exact (Subgroup.closure_induction (p := fun g _ => g ∈ E ∧ x (M.ι g) = M.ι g)
    (fun g hg => by
      rcases hg with ⟨y, hy, z, hz, rfl⟩
      exact ⟨hclE (CFSG.Quasithin.mem_conjClosure hy hz), h y hy z hz⟩)
    ⟨E.one_mem, by rw [M.ι_one, map_zero]⟩
    (fun g h _ _ hg hh => ⟨E.mul_mem hg.1 hh.1, by
      rw [M.ι_mul g hg.1 h hh.1, map_add, hg.2, hh.2]⟩)
    (fun g _ hg => ⟨E.inv_mem hg.1, by rw [M.ι_inv hg.1, map_neg, hg.2]⟩)
    hmem).2

theorem pCoreOf_img_eq_bot {T Z : Subgroup G} (hT : IsSylowIn 2 T J)
    (hZE : Z ≤ E) (hZ : T ≤ Subgroup.centralizer (Z : Set G))
    (hgen : E ≤ CFSG.Quasithin.conjClosure Z J) :
    pCoreOf 2 (M.img J) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pCoreOf 2 (M.img J) with hX
  have hXJ : X ≤ M.img J := CFSG.LieType.BorelTits.pCoreOf_le 2 (M.img J)
  have hXpg : IsPGroup 2 X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (M.img J)
  have hXnorm : (X.subgroupOf (M.img J)).Normal :=
    (Subgroup.normal_subgroupOf_iff hXJ).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M.img J) hk) h).1 hh
  have hXT : X ≤ M.img T := (isSylowIn_img M hT).le_of_normal hXJ hXnorm hXpg
  refine le_antisymm ?_ bot_le
  intro x hxX
  rw [Subgroup.mem_bot]
  have hfix : ∀ y ∈ J, ∀ z ∈ Z, x (M.ι (y * z * y⁻¹)) = M.ι (y * z * y⁻¹) := by
    intro y hyJ z hz
    let a : LGL 2 M.W := M.ρ ⟨y, hyJ⟩
    have hainv : a⁻¹ ∈ M.img J :=
      (M.img J).inv_mem (M.mem_img.2 ⟨⟨y, hyJ⟩, hyJ, rfl⟩)
    have hconj : a⁻¹ * x * a ∈ X :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M.img J) hainv) x).1 hxX
    obtain ⟨u, huT, hu⟩ := M.mem_img.1 (hXT hconj)
    have hzE : z ∈ E := hZE hz
    have hzfix : M.ρ u (M.ι z) = M.ι z := by
      rw [M.ρ_ι u z hzE]
      have hc : (u : G) * z = z * (u : G) :=
        (Subgroup.mem_centralizer_iff.1 (hZ huT) z hz).symm
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hreg : x (a (M.ι z)) = a (M.ι z) := by
      have h3 : a * M.ρ u = x * a := by rw [hu]; group
      have h4 := congrArg (fun f : LGL 2 M.W => f (M.ι z)) h3
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hzfix] at h4
      exact h4.symm
    rw [← M.ρ_ι ⟨y, hyJ⟩ z hzE]
    exact hreg
  ext w
  obtain ⟨e, he, rfl⟩ := M.ι_surj w
  exact (fixes_conjClosure M x Z hZE hgen hfix) e he

end ModDataE

end CFSG.LocalAnalysis.WeakClosure81

end
