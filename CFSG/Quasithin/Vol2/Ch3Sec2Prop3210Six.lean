module

public import CFSG.Quasithin.Background.AutOnCard
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace Prop3210

variable {G : Type} [Group G] [Finite G] {T L V₀ Vp : Subgroup G}

theorem thompsonJ_isWeaklyClosedIn : IsWeaklyClosedIn (thompsonJ T) T := by
  intro g hg
  have h1 : conjSubgroup (thompsonJ T) g = thompsonJ (T.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (GammaExtra.thompsonJ_map_equiv (MulAut.conj g⁻¹) T).symm
  have h2 : thompsonJ (T.map (MulAut.conj g⁻¹).toMonoidHom) ≤ thompsonJ T := by
    refine GammaExtra.thompsonJ_le fun A hA => GammaExtra.le_thompsonJ
      ⟨(GammaExtra.le_thompsonJ hA).trans (h1 ▸ hg), hA.2.1, fun B hB hBe => ?_⟩
    have := hA.2.2 (B.map (MulAut.conj g⁻¹).toMonoidHom) (Subgroup.map_mono hB)
      ((GammaExtra.isElemAbelian_map_equiv_iff (MulAut.conj g⁻¹)).mpr hBe)
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this
  rw [h1]
  refine Subgroup.eq_of_le_of_card_ge h2 ?_
  rw [← h1, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem conjClosure_props (h3228 : Stmt3_2_2_eight) (h : FSU G T L V₀) :
    IsElemAbelian 2 (conjClosure V₀ T) ∧
      conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) ∧
      conjClosure V₀ T ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVX, ⟨hnorm, helem, -⟩, hR⟩ := h3228 G T L V₀ h
  have hN : conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVX).mp hnorm
  have hE : IsElemAbelian 2 (conjClosure V₀ T) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have h1 := helem.toIsMulCommutative.is_comm.comm
        (⟨⟨a, hVX a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ :
          ↥((conjClosure V₀ T).subgroupOf (conjClosure L T ⊔ T)))
        ⟨⟨b, hVX b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
      apply Subtype.ext
      exact congrArg (fun z : ↥((conjClosure V₀ T).subgroupOf (conjClosure L T ⊔ T)) =>
        ((z : ↥(conjClosure L T ⊔ T)) : G)) h1
    · have h1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := (conjClosure V₀ T).subgroupOf (conjClosure L T ⊔ T)) ⟨x, hVX hx⟩
        (Subgroup.mem_subgroupOf.mpr hx)
      simpa using congrArg Subtype.val h1
  refine ⟨hE, hN, ?_⟩
  have hp : IsPGroup 2 ↥(conjClosure V₀ T) := fun x =>
    ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVX hN hp
  rw [hR] at hle
  exact hle.trans inf_le_left

theorem vplus_props (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h : FSU G T L V₀)
    (hV : IsVplus T L V₀ Vp) :
    IsElemAbelian 2 Vp ∧ Vp ≤ T ∧ T ≤ Subgroup.normalizer (Vp : Set G) ∧
      Vp ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVe, hVN, hVT⟩ := conjClosure_props h3228 h
  obtain ⟨⟨-, hTM⟩, -, -⟩ := h323 G T L h.simple h.nonabelian h.qtke h.sylow h.maximal
    h.faithful h.quasisimple
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  have hVM : conjClosure V₀ T ≤ M := hVT.trans hTM
  rcases hV with ⟨-, hc, rfl⟩ | ⟨-, rfl⟩
  ·
    have hab : IsMulCommutative ↥(conjClosure (conjClosure V₀ T) M) := by
      rcases hc with ⟨hab, -⟩ | ⟨hab, -⟩ <;> exact hab
    have hVMM : conjClosure (conjClosure V₀ T) M ≤ M :=
      conjClosure_le fun m hm v hv => M.mul_mem (M.mul_mem hm (hVM hv)) (M.inv_mem hm)
    have hcomm : ∀ a ∈ conjClosure (conjClosure V₀ T) M,
        ∀ b ∈ conjClosure (conjClosure V₀ T) M, a * b = b * a := fun a ha b hb => by
      have := hab
      exact setLike_mul_comm ha hb
    have key : ∀ y ∈ Subgroup.closure {y | ∃ m ∈ M, ∃ v ∈ conjClosure V₀ T, m * v * m⁻¹ = y},
        y ^ 2 = 1 := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨m, -, v, hv, rfl⟩ := hy
        rw [conj_pow, hVe.2 v hv, mul_one, mul_inv_cancel]
      | one => exact one_pow 2
      | mul a b ha hb iha ihb =>
        rw [Commute.mul_pow (hcomm a ha b hb) 2, iha, ihb, one_mul]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    have hE : IsElemAbelian 2 (conjClosure (conjClosure V₀ T) M) := ⟨hab, fun x hx => key x hx⟩
    have hp : IsPGroup 2 ↥(conjClosure (conjClosure V₀ T) M) := fun x =>
      ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    have hMN : M ≤ Subgroup.normalizer (conjClosure (conjClosure V₀ T) M : Set G) :=
      le_normalizer_conjClosure _ _
    have hTsyl : IsSylowTwoOf T M :=
      ⟨hTM, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
    exact ⟨hE, hTsyl.le_of_normalizes hVMM hMN hp, hTM.trans hMN, hVMM⟩
  · exact ⟨hVe, hVT, le_sup_right.trans hVN, hVM⟩

theorem vplus_isTI (h327 : Stmt3_2_7C) (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp) :
    IsTISetUnder Vp (Subgroup.normalizer (conjClosure L T : Set G)) := by
  rcases hV with ⟨-, -, rfl⟩ | ⟨hnot, rfl⟩
  · intro g hg hgN
    exact absurd (le_normalizer_conjClosure _ _ hg) hgN
  · rcases h327 G T L V₀ h with hTI | ⟨-, hne, hcase⟩ | ⟨hne, hcomm, hiv⟩
    · exact hTI
    · exact absurd ⟨hne, Or.inl hcase⟩ hnot
    · exact absurd ⟨hne, Or.inr ⟨hcomm, ((open CFSG.Blueprint in Iff.rfl)).mpr hiv⟩⟩ hnot

omit [Finite G] in
theorem mem_conjugate_iff {H : Subgroup G} {t x : G} :
    x ∈ CFSG.conjugate H t ↔ t * x * t⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem le_normalizer_vplus (h327 : Stmt3_2_7C) (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    {U : Subgroup G} (hU : U ≤ Vp) (hU1 : U ≠ ⊥) :
    Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Vp : Set G) := by
  intro m ⟨hmM, hmU⟩
  by_contra hmV
  have hTI := vplus_isTI h327 h hV m hmM hmV
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have h1 : (u : G) ∈ Vp ⊓ CFSG.conjugate Vp m := by
    refine ⟨hU u.2, mem_conjugate_iff.mpr (hU ?_)⟩
    exact (Subgroup.mem_normalizer_iff.mp hmU u).mp u.2
  rw [hTI, Subgroup.mem_bot] at h1
  exact hu1 (Subtype.ext h1)

theorem fusion (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h327 : Stmt3_2_7C)
    (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) {A B : Set G} (hA : A ⊆ Vp)
    (hB : B ⊆ Vp) (hA1 : ∃ a ∈ A, a ≠ 1) {g : G} (hg : conjSet A g = B) :
    ∃ n ∈ Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer (Vp : Set G),
      conjSet A n = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hc : ∀ w ∈ thompsonJ T, ∀ y ∈ Vp, w * y * w⁻¹ = y := fun w hw y hy => by
    have := Subgroup.mem_centralizer_iff.mp (hJ hw) y hy
    rw [← this, mul_inv_cancel_right]
  have hfix : ∀ {S : Set G}, S ⊆ Vp → ∀ w ∈ thompsonJ T, conjSet S w = S := by
    intro S hS w hw
    ext x
    rw [mem_conjSet_iff]
    constructor
    · intro hx
      have hy := hc w⁻¹ ((thompsonJ T).inv_mem hw) _ (hS hx)
      rw [inv_inv, show w⁻¹ * (w * x * w⁻¹) * w = x by group] at hy
      rw [hy]
      exact hx
    · intro hx
      rwa [hc w hw x (hS hx)]
  obtain ⟨n, hn, hnA⟩ := burnside_fusion_lemma P (W := thompsonJ T)
    (GammaExtra.thompsonJ_le_self T) thompsonJ_isWeaklyClosedIn (hfix hA) (hfix hB) hg
  have hnM : n ∈ Subgroup.normalizer (conjClosure L T : Set G) :=
    normalizer_thompsonJ_le h323 h3228 h hV hJ hn
  refine ⟨n, ⟨hnM, ?_⟩, hnA⟩
  by_contra hnV
  obtain ⟨a, haA, ha1⟩ := hA1
  have hTI := vplus_isTI h327 h hV n hnM hnV
  have h1 : n⁻¹ * a * n ∈ Vp ⊓ CFSG.conjugate Vp n := by
    refine ⟨hB ?_, mem_conjugate_iff.mpr ?_⟩
    · rw [← hnA, mem_conjSet_iff]
      simpa [mul_assoc] using haA
    · rw [show n * (n⁻¹ * a * n) * n⁻¹ = a by group]
      exact hA haA
  rw [hTI, Subgroup.mem_bot] at h1
  apply ha1
  calc a = n * (n⁻¹ * a * n) * n⁻¹ := by group
    _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

theorem exists_mem_normalizer_conj_eq (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h327 : Stmt3_2_7C) (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) {U : Subgroup G} (hU : U ≤ Vp)
    {g : G} (hUg : U ≤ conjSubgroup Vp g) :
    ∃ x ∈ Subgroup.normalizer (U : Set G), conjSubgroup Vp x = conjSubgroup Vp g := by
  by_cases hU1 : U = ⊥
  · subst hU1
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  · obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hB : conjSet (U : Set G) g⁻¹ ⊆ Vp := by
      intro y hy
      rw [mem_conjSet_iff, inv_inv] at hy
      have := hUg hy
      rw [mem_conjSubgroup_iff] at this
      simpa [mul_assoc] using this
    obtain ⟨n, ⟨-, hnV⟩, hn⟩ := fusion h323 h3228 h327 h hV hJ (A := (U : Set G))
      (fun x hx => hU hx) hB ⟨u, u.2, fun h1 => hu1 (Subtype.ext h1)⟩ rfl
    refine ⟨n * g, ?_, ?_⟩
    · rw [← conjSet_eq_iff_mem_normalizer, ← conjSet_conjSet, hn, conjSet_conjSet,
        inv_mul_cancel]
      ext x
      simp [mem_conjSet_iff]
    · rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hnV]

omit [Finite G] in
theorem map_conj_inf_centralizer (H K : Subgroup G) (c : G) :
    (H ⊓ Subgroup.centralizer (K : Set G)).map (MulAut.conj c).toMonoidHom =
      H.map (MulAut.conj c).toMonoidHom ⊓
        Subgroup.centralizer ((K.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨h, ⟨hh, hhc⟩, rfl⟩
    refine ⟨⟨h, hh, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hhc k hk
    show c * k * c⁻¹ * (c * h * c⁻¹) = c * h * c⁻¹ * (c * k * c⁻¹)
    calc c * k * c⁻¹ * (c * h * c⁻¹) = c * (k * h) * c⁻¹ := by group
      _ = c * (h * k) * c⁻¹ := by rw [this]
      _ = c * h * c⁻¹ * (c * k * c⁻¹) := by group
  · rintro x ⟨⟨h, hh, rfl⟩, hxc⟩
    refine ⟨h, ⟨hh, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hxc (c * k * c⁻¹) ⟨k, hk, rfl⟩
    have h2 : c * k * c⁻¹ * (c * h * c⁻¹) = c * h * c⁻¹ * (c * k * c⁻¹) := h1
    calc k * h = c⁻¹ * (c * k * c⁻¹ * (c * h * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * h * c⁻¹ * (c * k * c⁻¹)) * c := by rw [h2]
      _ = h * k := by group

omit [Finite G] in
theorem card_autOn_mul (V R : Subgroup G) (hRN : R ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autOn R V) * Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set G)) = Nat.card R :=
  CFSG.Quasithin.AutOn.card_autOn_mul hRN

omit [Finite G] in
theorem card_fixV_autOn (V R : Subgroup G) [IsMulCommutative ↥V]
    (hRN : R ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(fixV (autOn R V)) = Nat.card ↥(V ⊓ Subgroup.centralizer (R : Set G)) := by
  have key : ∀ v : ↥V, v ∈ fixV (autOn R V) ↔ (v : G) ∈ Subgroup.centralizer (R : Set G) := by
    intro v
    rw [mem_fixV, Subgroup.mem_centralizer_iff]
    constructor
    · intro hv r hr
      have h1 := hv (conjAct V ⟨r, hRN hr⟩)
        ((CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨r, hRN hr⟩, hr, rfl⟩)
      have h2 := congrArg Subtype.val h1
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
      calc r * v = r * v * r⁻¹ * r := by group
        _ = v * r := by rw [h2]
    · intro hv φ hφ
      obtain ⟨⟨r, hrN⟩, hr, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp hφ
      apply Subtype.ext
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
      show r * v * r⁻¹ = v
      rw [hv r hr, mul_inv_cancel_right]
  let e : ↥(fixV (autOn R V)) ≃ ↥(V ⊓ Subgroup.centralizer (R : Set G)) :=
    { toFun := fun v => ⟨v.1, v.1.2, (key v.1).mp v.2⟩
      invFun := fun x => ⟨⟨x, x.2.1⟩, (key ⟨x, x.2.1⟩).mpr x.2.2⟩
      left_inv := fun v => rfl
      right_inv := fun x => rfl }
  exact Nat.card_congr e

theorem exists_isFFStarOffender {V : Type*} [CommGroup V] [Finite V]
    {X A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hFF : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ B : Subgroup (MulAut V), IsFFStarOffender X B := by
  obtain ⟨B, ⟨hBA, hB1⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup (MulAut V) | B ≤ A ∧ B ≠ ⊥}
    (fun B => Nat.card B * Nat.card (fixV B)) (Set.toFinite _) ⟨A, le_rfl, hA1⟩
  have hfA := hmax A ⟨le_rfl, hA1⟩
  refine ⟨B, hBA.trans hAX, hB1, ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb),
    fun a ha => hAe.2 a (hBA ha)⟩, fun C hCB => ?_⟩
  by_cases hC : C = ⊥
  · subst hC
    have hfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      ext v
      simp only [mem_fixV, Subgroup.mem_bot, Subgroup.mem_top, iff_true]
      rintro x rfl
      rfl
    rw [hfix, Subgroup.card_bot, one_mul, Subgroup.card_top]
    exact hFF.trans hfA
  · exact hmax C ⟨hCB.trans hBA, hC⟩

theorem exists_offender (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h : FSU G T L V₀)
    (hV : IsVplus T L V₀ Vp) [IsMulCommutative ↥Vp] {R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (conjClosure L T : Set G) ⊓
      Subgroup.normalizer (Vp : Set G))
    (hRe : IsElemAbelian 2 R) (hRC : ¬ R ≤ Subgroup.centralizer (Vp : Set G))
    (hcard : Nat.card Vp * Nat.card ↥(R ⊓ Subgroup.centralizer (Vp : Set G)) ≤
      Nat.card R * Nat.card ↥(Vp ⊓ Subgroup.centralizer (R : Set G))) :
    ∃ A : Subgroup (MulAut ↥Vp), IsFFStarOffender (autOn (conjClosure L T ⊔ T) Vp) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hTN, -⟩ := vplus_props h323 h3228 h hV
  obtain ⟨⟨-, hTM⟩, -, -⟩ := h323 G T L h.simple h.nonabelian h.qtke h.sylow h.maximal
    h.faithful h.quasisimple
  set K := Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer (Vp : Set G)
    with hKdef
  have hTK : T ≤ K := le_inf hTM hTN
  have hTsyl : IsSylowTwoOf T K :=
    ⟨hTK, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hR2 : IsPGroup 2 ↥R := fun x => ⟨1, Subtype.ext (by simpa using hRe.2 x x.2)⟩
  obtain ⟨S, hRS, hS⟩ := exists_isSylowTwoOf_of_le hRK hR2
  obtain ⟨c, hcK, hcT⟩ := hS.exists_conj hTsyl
  have hcN : c ∈ Subgroup.normalizer (Vp : Set G) := hcK.2
  set R' := R.map (MulAut.conj c).toMonoidHom with hR'def
  have hR'T : R' ≤ T := by
    rw [hcT]
    exact Subgroup.map_mono hRS
  have hR'N : R' ≤ Subgroup.normalizer (Vp : Set G) := hR'T.trans hTN
  have hc1 : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hVc : Vp.map (MulAut.conj c).toMonoidHom = Vp :=
    GammaExtra.map_conj_eq_self_of_mem_normalizer hcN
  have hc2 : Nat.card ↥(R' ⊓ Subgroup.centralizer (Vp : Set G)) =
      Nat.card ↥(R ⊓ Subgroup.centralizer (Vp : Set G)) := by
    have := map_conj_inf_centralizer R Vp c
    rw [hVc] at this
    rw [hR'def, ← this, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hc3 : Nat.card ↥(Vp ⊓ Subgroup.centralizer (R' : Set G)) =
      Nat.card ↥(Vp ⊓ Subgroup.centralizer (R : Set G)) := by
    have := map_conj_inf_centralizer Vp R c
    rw [hVc] at this
    rw [hR'def, ← this, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hR'C : ¬ R' ≤ Subgroup.centralizer (Vp : Set G) := by
    intro hle
    apply hRC
    have h1 : Nat.card R ≤ Nat.card ↥(R ⊓ Subgroup.centralizer (Vp : Set G)) := by
      rw [← hc1, ← hc2, inf_of_le_left hle]
    exact (Subgroup.eq_of_le_of_card_ge inf_le_left h1).symm ▸ inf_le_right
  have hAX : autOn R' Vp ≤ autOn (conjClosure L T ⊔ T) Vp :=
    A4.autOn_mono (hR'T.trans le_sup_right)
  have hA1 : autOn R' Vp ≠ ⊥ := by
    intro hA
    apply hR'C
    intro r hr
    have h1 : conjAct Vp ⟨r, hR'N hr⟩ ∈ autOn R' Vp :=
      (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨r, hR'N hr⟩, hr, rfl⟩
    rw [hA, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.mp h1
  have hR'e : IsElemAbelian 2 R' := (GammaExtra.isElemAbelian_map_equiv_iff _).mpr hRe
  have hR'ab : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := fun a ha b hb => by
    have := hR'e.1
    exact setLike_mul_comm ha hb
  have hAe : IsElemAbelian2 (autOn R' Vp) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp ha
      obtain ⟨y, hy, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hR'ab _ hx _ hy)
    · obtain ⟨x, hx, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp ha
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hR'e.2 _ hx)
      rw [this, map_one]
  have hFF : Nat.card ↥Vp ≤ Nat.card ↥(autOn R' Vp) * Nat.card ↥(fixV (autOn R' Vp)) := by
    have h1 := card_autOn_mul Vp R' hR'N
    have h2 := card_fixV_autOn Vp R' hR'N
    have hpos : 0 < Nat.card ↥(R' ⊓ Subgroup.centralizer (Vp : Set G)) := Nat.card_pos
    rw [← hc1, ← hc2, ← hc3, ← h1] at hcard
    rw [h2]
    have h3 : Nat.card ↥Vp * Nat.card ↥(R' ⊓ Subgroup.centralizer (Vp : Set G)) ≤
        Nat.card ↥(autOn R' Vp) * Nat.card ↥(Vp ⊓ Subgroup.centralizer (R' : Set G)) *
          Nat.card ↥(R' ⊓ Subgroup.centralizer (Vp : Set G)) := by
      calc _ ≤ _ := hcard
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h3 hpos
  exact exists_isFFStarOffender hAX hA1 hAe hFF

theorem pCoreOf_top_eq_bot (h : FSU G T L V₀) : pCoreOf 2 (⊤ : Subgroup G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (pCoreOf 2 (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (eq_top_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf 2 (⊤ : Subgroup G)) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian
    have hP : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup G)
        ⟨x, by rw [ht]; exact Subgroup.mem_top x⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Nontrivial G := ⟨⟨a * b, b * a, hab⟩⟩
    have hc := hP.center_nontrivial
    have hcn : Subgroup.center G ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
    · exact hcn h1
    · have ha : a ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem commutator_eq_bot (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h327 : Stmt3_2_7C)
    (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) {U : Subgroup G} (hU : U ≤ Vp)
    (hVO : Vp ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)))
    (hFF : ∀ _ : IsMulCommutative ↥Vp, ¬ ∃ A : Subgroup (MulAut ↥Vp),
      IsFFStarOffender (V := ↥Vp) (autOn (conjClosure L T ⊔ T) Vp) A)
    (g : G) (hUg : U ≤ conjSubgroup Vp g) : ⁅Vp, conjSubgroup Vp g⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVe, -, -, -⟩ := vplus_props h323 h3228 h hV
  have := hVe.1
  obtain ⟨x, hxN, hx⟩ := exists_mem_normalizer_conj_eq h323 h3228 h327 h hV hJ hU hUg
  rw [← hx]
  by_cases hU1 : U = ⊥
  ·
    have hNtop : Subgroup.normalizer (U : Set G) = ⊤ := by
      subst hU1
      exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [hNtop, pCoreOf_top_eq_bot h] at hVO
    rw [le_bot_iff.mp hVO, Subgroup.commutator_bot_left]
  set NU := Subgroup.normalizer (U : Set G) with hNU
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  obtain ⟨S, -, hSK, hS⟩ := exists_isSylowTwoOf_normalizer h323 h3228 h hV hJ hU
  have hOS : pCoreOf 2 NU ≤ S := hS.pCoreOf_le
  have hON : NU ≤ Subgroup.normalizer (pCoreOf 2 NU : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 NU
  have hconj : ∀ y ∈ NU, conjSubgroup Vp y ≤ pCoreOf 2 NU := by
    intro y hy v hv
    rw [mem_conjSubgroup_iff] at hv
    have h1 := (Subgroup.mem_normalizer_iff.mp (hON (NU.inv_mem hy)) _).mp (hVO hv)
    simpa [mul_assoc] using h1
  have hNV := le_normalizer_vplus h327 h hV hU hU1
  have hR : ∀ y ∈ NU, conjSubgroup Vp y ≤ M ⊓ Subgroup.normalizer (Vp : Set G) :=
    fun y hy v hv => ⟨(hSK (hOS (hconj y hy hv))).1, hNV (hSK (hOS (hconj y hy hv)))⟩
  have hRe : ∀ y : G, IsElemAbelian 2 (conjSubgroup Vp y) := fun y =>
    (GammaExtra.isElemAbelian_map_equiv_iff _).mpr hVe
  have hcardR : ∀ y : G, Nat.card ↥(conjSubgroup Vp y) = Nat.card Vp := fun y =>
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  by_contra hne
  have hVC : ¬ conjSubgroup Vp x ≤ Subgroup.centralizer (Vp : Set G) := by
    intro hle
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hle))
  obtain ⟨a, ha⟩ : ∃ a, Nat.card ↥(Vp ⊓
      Subgroup.centralizer ((conjSubgroup Vp x : Subgroup G) : Set G)) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b,
      Nat.card ↥(conjSubgroup Vp x ⊓ Subgroup.centralizer (Vp : Set G)) = b := ⟨_, rfl⟩
  have hbV : b ≤ Nat.card Vp := by
    rw [← hb, ← hcardR x]
    exact Subgroup.card_le_of_le inf_le_left
  rcases le_or_gt b a with hba | hab
  ·
    refine hFF hVe.1 (exists_offender h323 h3228 h hV (hR x hxN) (hRe x) hVC ?_)
    rw [hcardR x, ha, hb]
    exact Nat.mul_le_mul_left _ hba
  ·
    have hconjx : ∀ K : Subgroup G,
        (conjSubgroup K x).map (MulAut.conj x).toMonoidHom = K := by
      intro K
      rw [conjSubgroup, Subgroup.map_map]
      convert Subgroup.map_id K using 2
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hR2 : conjSubgroup Vp x⁻¹ = Vp.map (MulAut.conj x).toMonoidHom := by
      rw [conjSubgroup, inv_inv]
    have ha' : Nat.card ↥(conjSubgroup Vp x⁻¹ ⊓ Subgroup.centralizer (Vp : Set G)) = a := by
      have := map_conj_inf_centralizer Vp (conjSubgroup Vp x) x
      rw [hconjx] at this
      rw [hR2, ← this, Subgroup.card_map_of_injective (MulAut.conj x).injective, ha]
    have hb' : Nat.card ↥(Vp ⊓ Subgroup.centralizer
        ((conjSubgroup Vp x⁻¹ : Subgroup G) : Set G)) = b := by
      have := map_conj_inf_centralizer (conjSubgroup Vp x) Vp x
      rw [hconjx] at this
      rw [hR2, ← this, Subgroup.card_map_of_injective (MulAut.conj x).injective, hb]
    have hVC' : ¬ conjSubgroup Vp x⁻¹ ≤ Subgroup.centralizer (Vp : Set G) := by
      intro hle
      have h1 := ha'
      rw [inf_of_le_left hle, hcardR] at h1
      omega
    refine hFF hVe.1 (exists_offender h323 h3228 h hV (hR x⁻¹ (NU.inv_mem hxN)) (hRe x⁻¹)
      hVC' ?_)
    rw [ha', hb', hcardR x⁻¹]
    exact Nat.mul_le_mul_left _ hab.le

end Prop3210

end CFSG.Quasithin.H13
