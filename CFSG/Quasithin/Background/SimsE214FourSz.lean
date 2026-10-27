module

public import CFSG.Quasithin.Background.SimsE214FourPair
public import CFSG.Quasithin.Background.SimsE214Easy

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214F

section Sz

variable {Y : Type} [Group Y]

theorem isPGroup_centralizer_of_isSz {k : ℕ} (hSz : IsSz k Y) {t : Y} (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.centralizer ({t} : Set Y)) := by
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e₀⟩⟩ := hSz
  let ψ : Y ≃* ↥(CFSG.Open.Sz a) := e₀.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hord : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hC := CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_involution_centralizer ha _ hord
  intro c
  have hc : ψ c ∈ Subgroup.centralizer ({ψ t} : Set ↥(CFSG.Open.Sz a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [← map_mul, ← map_mul, h1]
  obtain ⟨n, hn⟩ := hC ⟨ψ c, hc⟩
  refine ⟨n, Subtype.ext (ψ.injective ?_)⟩
  have h2 := congrArg Subtype.val hn
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2 ⊢
  rw [map_pow, map_one]
  exact h2

theorem le_of_isSylowTwoOf_top [Finite Y] {S R : Subgroup Y} (hS : IsSylowTwoOf S ⊤)
    (hSR : S ≤ R) (hR : IsPGroup 2 R) : R ≤ S := by
  obtain ⟨a, ha⟩ := exists_relIndex_eq_two_pow hR S
  have h1 := Subgroup.relIndex_mul_relIndex S R ⊤ hSR le_top
  have hodd : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0, pow_zero] at ha
    exact Subgroup.relIndex_eq_one.mp ha
  · exfalso
    apply hodd
    rw [← h1, ha]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 h0.ne') _

theorem centralizer_le_of_isSz [Finite Y] {k : ℕ} (hSz : IsSz k Y) {S : Subgroup Y}
    (hS : IsSylowTwoOf S ⊤) {w : Y} (hw : w ∈ S ⊓ Subgroup.centralizer (S : Set Y))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) : Subgroup.centralizer ({w} : Set Y) ≤ S := by
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  refine le_of_isSylowTwoOf_top hS (fun s hs => ?_) (isPGroup_centralizer_of_isSz hSz hord)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hw.2 s hs

end Sz

section Star

variable {Γ : Type} [Group Γ]

theorem star_conjSub {M I W : Subgroup Γ} {g : Γ} (hg : g ∈ I) (hW : W ≤ I) :
    E2.star M I (B6.conjSub g W) =
      (E2.star M I W).map (MulAut.conj (E2P.starMap M I ⟨g, hg⟩)).toMonoidHom := by
  ext w
  rw [E2P.star_def, E2P.star_def, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, B6.mem_conjSub] at hx
    have hy : g⁻¹ * (x : Γ) * g ∈ I := I.mul_mem (I.mul_mem (I.inv_mem hg) x.2) hg
    refine ⟨E2P.starMap M I ⟨g⁻¹ * x * g, hy⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨⟨g * y * g⁻¹, I.mul_mem (I.mul_mem hg y.2) (I.inv_mem hg)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, B6.mem_conjSub]
      simpa [mul_assoc] using hy
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
      congr 1

theorem star_sup {M I A C : Subgroup Γ} (hA : A ≤ I) (hC : C ≤ I) :
    E2.star M I (A ⊔ C) = E2.star M I A ⊔ E2.star M I C := by
  rw [E2P.star_def, E2P.star_def, E2P.star_def, Subgroup.subgroupOf_sup hA hC, Subgroup.map_sup]

end Star

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem gen_of_centralizer_le {T M V I : Subgroup Γ} {g : Γ}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hcen : Subgroup.center (E2.StarQuot (M ⊓ I) I) = ⊥)
    (hVeq : E2.star (M ⊓ I) I V = ASInputs.e214ZT T M I) {v : Γ} (hv : v ∈ V)
    (hCv : Subgroup.centralizer ({E2P.starMap (M ⊓ I) I ⟨v, hp.V_le hv⟩} :
      Set (E2.StarQuot (M ⊓ I) I)) ≤ E2.star (M ⊓ I) I (T ⊓ I))
    (he : g * v * g⁻¹ ∈ B6.conjSub g V) :
    E2.star (M ⊓ I) I V ⊔
        Subgroup.zpowers (E2P.starMap (M ⊓ I) I ⟨g * v * g⁻¹, hp.conj_le he⟩) = ⊤ ∧
      E2.star (M ⊓ I) I (B6.conjSub g V) ⊔
        Subgroup.zpowers (E2P.starMap (M ⊓ I) I ⟨v, hp.V_le hv⟩) = ⊤ := by
  have := E2P.finite_starQuot (M ⊓ I) I
  set Y := E2.StarQuot (M ⊓ I) I
  set π := E2P.starMap (M ⊓ I) I with hπ
  set S := E2.star (M ⊓ I) I (T ⊓ I) with hSdef
  set W := S ⊓ Subgroup.centralizer (S : Set Y) with hWdef
  have hVW : E2.star (M ⊓ I) I V = W := hVeq
  set h : Y := (π ⟨g, hp.mem⟩)⁻¹ with hh
  have hW' : E2.star (M ⊓ I) I (B6.conjSub g V) = W.map (MulAut.conj h⁻¹).toMonoidHom := by
    rw [star_conjSub hp.mem hp.V_le, hVW, hh, inv_inv]
  have hgen : W ⊔ W.map (MulAut.conj h⁻¹).toMonoidHom = ⊤ := by
    rw [← hW', ← hVW, ← star_sup hp.V_le hp.conj_le, ← hp.gen]
    exact E2P.star_top _ _
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw =>
    E2.sq_eq_one_of_mem_star (M := M) (I := I) hp.elem (hVW ▸ hw)
  set v' := π ⟨v, hp.V_le hv⟩ with hv'
  have hv'W : v' ∈ W := by
    rw [← hVW, E2P.star_def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  obtain ⟨h1, h2⟩ := sup_zpowers_eq_top hW2 hgen hv'W hCv hcen
  have hconj : h⁻¹ * v' * h = π ⟨g * v * g⁻¹, hp.conj_le he⟩ := by
    rw [hh, inv_inv, hv', ← map_inv, ← map_mul, ← map_mul]
    congr 1
  refine ⟨?_, ?_⟩
  · rw [hVW, ← hconj]
    exact h1
  · rw [hW']
    exact h2

theorem center_eq_bot_and_centralizer_le_of_sz {T M V I : Subgroup Γ} {g : Γ}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) {k : ℕ} (hSz : IsSz k (E2.StarQuot (M ⊓ I) I))
    (hVeq : E2.star (M ⊓ I) I V = ASInputs.e214ZT T M I) {v : Γ} (hv : v ∈ V)
    (hv1 : v ∉ kerIn (M ⊓ I) I) :
    Subgroup.center (E2.StarQuot (M ⊓ I) I) = ⊥ ∧
      Subgroup.centralizer ({E2P.starMap (M ⊓ I) I ⟨v, hp.V_le hv⟩} :
        Set (E2.StarQuot (M ⊓ I) I)) ≤ E2.star (M ⊓ I) I (T ⊓ I) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hk : 1 < k := by
    obtain ⟨-, a, ha, -, -, -, rfl, -⟩ := hSz
    omega
  refine ⟨E2.center_eq_bot_of_simple (E2.isSimpleGroup_of_psl_or_sz (Or.inr hSz))
    (E2.nonabelian_of_psl_or_sz hk (Or.inr hSz)), ?_⟩
  have hS : IsSylowTwoOf (E2.star (M ⊓ I) I (T ⊓ I)) ⊤ :=
    E2.isSylowTwoOf_star_inf (M := M) hp.sylow
  have hv'W : E2P.starMap (M ⊓ I) I ⟨v, hp.V_le hv⟩ ∈ ASInputs.e214ZT T M I := by
    rw [← hVeq, E2P.star_def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  have hv'1 : E2P.starMap (M ⊓ I) I ⟨v, hp.V_le hv⟩ ≠ 1 := by
    rw [E2P.starMap, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hv1
  exact centralizer_le_of_isSz hSz hS hv'W
    (E2.sq_eq_one_of_mem_star (M := M) (I := I) hp.elem
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv))) hv'1

theorem four_of_sz
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g)
    (hZ : V ⊓ conjSubgroup V g ≠ ⊥) {k : ℕ} (hSz : IsSz k (E2.StarQuot (M ⊓ I) I))
    {Y₁ Y₂ : Subgroup Γ} (hZY : V ⊓ conjSubgroup V g ≤ Y₂) (hY : Y₂ < Y₁)
    (hY₁P : Y₁ ≤ (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I))
    (hIY₁ : I ≤ Subgroup.normalizer (Y₁ : Set Γ))
    (hIY₂ : I ≤ Subgroup.normalizer (Y₂ : Set Γ)) :
    4 * k ≤ E3.mQuot Y₁ Y₂ := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  obtain ⟨hp, hVZ, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  obtain ⟨hk3, hcard⟩ := E2.card_of_isSz hSz
  have hk : 2 ≤ k := by omega
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have h1 := E214.inf_eq_inf_normalizer h hTI hI hg hIV hZ
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hBorel := E214.isBorelIn_of_psl_or_sz hI hk (Or.inr hSz)
  obtain ⟨-, hVeq⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds hp hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBorel hk (Or.inr hSz)
  have hs : IsSimpleGroup (E2.StarQuot (M ⊓ I) I) := E2.isSimpleGroup_of_psl_or_sz (Or.inr hSz)
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ kerIn (M ⊓ I) I := by
    have hne := E2.star_ne_bot_of_gen (M' := M ⊓ I) (I.inv_mem hg) hgen
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    rw [E2P.star_def] at hw
    obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hw
    refine ⟨x, Subgroup.mem_subgroupOf.mp hx, fun hxJ => hw1' ?_⟩
    rw [← hxw, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hxJ
  have he : g⁻¹ * v * g⁻¹⁻¹ ∈ B6.conjSub g⁻¹ V := by
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hv
  obtain ⟨hcen, hCv⟩ := center_eq_bot_and_centralizer_le_of_sz hp hSz hVeq hv hv1
  obtain ⟨hgv, hge⟩ := gen_of_centralizer_le hp hcen hVeq hv hCv he
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k) (by omega)
    (by omega)
  have hrX : r ∣ Nat.card (E2.StarQuot (M ⊓ I) I) := by
    rw [hcard]
    exact ((Ch3E213M.primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
      (Dvd.intro_left _ rfl)
  have hN : ∀ N : Subgroup (E2.StarQuot (M ⊓ I) I), N.Normal → N ≠ ⊥ →
      ∀ z : E2.StarQuot (M ⊓ I) I, Odd (orderOf z) → z ∈ N := by
    intro N hNn hN1 z _
    rcases hNn.eq_bot_or_eq_top with h0 | h0
    · exact absurd h0 hN1
    · rw [h0]
      exact Subgroup.mem_top z
  have hPeq : (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I) =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [e, hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  exact four_of_gen hp hJ hN (by omega) hr hrX hv he hgv hge (e ▸ hZY) hY (hPeq ▸ hY₁P)
    hIY₁ hIY₂

end E214F

end CFSG.Quasithin.SimsE2
