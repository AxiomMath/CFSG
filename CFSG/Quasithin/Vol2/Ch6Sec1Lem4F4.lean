module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusIn

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

theorem mem_normalizer_zpowers_of_conj614 {G : Type*} [Group G] {r y : G}
    (h1 : r * y * r⁻¹ ∈ Subgroup.zpowers y) (h2 : r⁻¹ * y * r ∈ Subgroup.zpowers y) :
    r ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : h = (r⁻¹ * y * r⁻¹⁻¹) ^ k := by
      rw [conj_zpow, hk]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (by simpa using h2) k

variable {F : Type*} [Field F] [Finite F]

theorem exists_involution_commute614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {T : Subgroup (PGammaL2 F)} {y : PGammaL2 F}
    (hTs : IsSylowTwoOf T (pGammaL2PSLRange F ⊔ T)) (hy5 : orderOf y = 5)
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F))) :
    ∃ z ∈ pGammaL2PSLRange F, BenderSuzuki.PFAppendixIII.IsInvolution z ∧ Commute y z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PSL2 F) := Finite.of_injective _
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
  have : Finite (PGammaL2 F) :=
    Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  set N := pGammaL2PSLRange F with hNdef
  have hNn : N.Normal := pGammaL2PSLRange_normal F hK hcard
  set ι := iotaPSL614 F
  have hinj : Function.Injective ι := iotaPSL614_injective
  set D := T ⊓ N with hD
  have hDy : D ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) :=
    inf_le_left.trans hTy
  set D₁ := D.comap ι with hD₁
  have hDN : D ≤ ι.range := inf_le_right
  have hD₁2 : IsPGroup 2 D₁ := by
    intro x
    obtain ⟨k, hk⟩ := (hTs.2.1.to_le (inf_le_left : D ≤ T)) ⟨ι x, x.2⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hD₁i : ¬ 2 ∣ D₁.index := by
    have h1 : (D₁.map ι).relIndex ((⊤ : Subgroup (PSL2 F)).map ι) = D₁.index := by
      rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hinj, sup_bot_eq,
        sup_bot_eq, Subgroup.relIndex_top_right]
    rw [Subgroup.map_comap_eq_self hDN, ← MonoidHom.range_eq_map] at h1
    rw [← h1]
    have hTN : T ≤ Subgroup.normalizer (N : Set (PGammaL2 F)) := fun t _ =>
      Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hNn.conj_mem h hh t,
        fun hh => by simpa [mul_assoc] using hNn.conj_mem _ hh t⁻¹⟩
    have h2 := B6.relIndex_inf_eq_relIndex_sup hTN
    rw [show D.relIndex ι.range = T.relIndex (T ⊔ N) from h2, sup_comm]
    exact hTs.2.2
  set S : Sylow 2 (PSL2 F) := hD₁2.toSylow hD₁i
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hK S
  obtain ⟨a, b, ha1, hb1, hab, ha2, hb2, hcomm⟩ := dihedral_commuting_involutions614 hm
  set a₁ : PSL2 F := ((e.symm a : S) : PSL2 F)
  set b₁ : PSL2 F := ((e.symm b : S) : PSL2 F)
  have ha₁D : a₁ ∈ D₁ := (e.symm a).2
  have hb₁D : b₁ ∈ D₁ := (e.symm b).2
  have hsq : ∀ c : DihedralGroup (2 ^ m), c ^ 2 = 1 → ι ((e.symm c : S) : PSL2 F) ^ 2 = 1 := by
    intro c hc
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, hc, map_one, Subgroup.coe_one, map_one]
  have hne : ∀ c : DihedralGroup (2 ^ m), c ≠ 1 → ι ((e.symm c : S) : PSL2 F) ≠ 1 := by
    intro c hc h
    apply hc
    have h1 : ((e.symm c : S) : PSL2 F) = 1 := hinj (by rw [h, map_one])
    have h2 : e.symm c = 1 := Subtype.ext h1
    simpa using congrArg e h2
  set a' := ι a₁
  set b' := ι b₁
  have ha'D : a' ∈ D := ha₁D
  have hb'D : b' ∈ D := hb₁D
  have ha'2 : a' ^ 2 = 1 := hsq a ha2
  have hb'2 : b' ^ 2 = 1 := hsq b hb2
  have hab' : a' * b' = b' * a' := by
    show ι a₁ * ι b₁ = ι b₁ * ι a₁
    rw [← map_mul, ← map_mul]
    congr 1
    have := congrArg (fun c => ((e.symm c : S) : PSL2 F)) hcomm
    simpa using this
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hinvol : ∀ c : PGammaL2 F, c ≠ 1 → c ^ 2 = 1 → BenderSuzuki.PFAppendixIII.IsInvolution c :=
    fun c h1 h2 => ⟨h1, h2⟩
  rcases conj_eq_or_eq_inv_of_sq614 hy5' ha'2 (hDy ha'D) with hA | hA
  · refine ⟨a', ha'D.2, hinvol a' (hne a ha1) ha'2, ?_⟩
    show y * a' = a' * y
    calc y * a' = a' * y * a'⁻¹ * a' := by rw [hA]
      _ = a' * y := by group
  rcases conj_eq_or_eq_inv_of_sq614 hy5' hb'2 (hDy hb'D) with hB | hB
  · refine ⟨b', hb'D.2, hinvol b' (hne b hb1) hb'2, ?_⟩
    show y * b' = b' * y
    calc y * b' = b' * y * b'⁻¹ * b' := by rw [hB]
      _ = b' * y := by group
  refine ⟨a' * b', N.mul_mem ha'D.2 hb'D.2, hinvol _ ?_ ?_, ?_⟩
  · intro h
    apply hab
    have h1 : a' = b'⁻¹ := eq_inv_of_mul_eq_one_left h
    have hb'i : b'⁻¹ = b' := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb'2]
    have h2 : ι a₁ = ι b₁ := h1.trans hb'i
    have h3 : e.symm a = e.symm b := Subtype.ext (hinj h2)
    simpa using congrArg e h3
  · rw [(show Commute a' b' from hab').mul_pow 2, ha'2, hb'2, one_mul]
  · show y * (a' * b') = a' * b' * y
    have e1 : a' * b' * y * (a' * b')⁻¹ = y := by
      calc a' * b' * y * (a' * b')⁻¹ = a' * (b' * y * b'⁻¹) * a'⁻¹ := by group
        _ = a' * y⁻¹ * a'⁻¹ := by rw [hB]
        _ = (a' * y * a'⁻¹)⁻¹ := by group
        _ = y := by rw [hA, inv_inv]
    calc y * (a' * b') = a' * b' * y * (a' * b')⁻¹ * (a' * b') := by rw [e1]
      _ = a' * b' * y := by group

theorem findFus614_inner (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {T E : Subgroup (PGammaL2 F)} {y : PGammaL2 F}
    (hTs : IsSylowTwoOf T (pGammaL2PSLRange F ⊔ T)) (hyN : y ∈ pGammaL2PSLRange F)
    (hy5 : orderOf y = 5)
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)))
    (hEC : E ≤ Subgroup.centralizer ({y} : Set (PGammaL2 F))) (hEa : IsElemAbelian 2 E)
    (hE1 : E ≠ ⊥) (hEP : E ≤ pGammaL2PGLRange F) :
    ∃ g ∈ pGammaL2PSLRange F ⊔ T, E.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) ∧
      ¬ E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set (PGammaL2 F)) := by
  classical
  obtain ⟨z, hzN, hzI, hyz⟩ := exists_involution_commute614 hK hcard hTs hy5 hTy
  set ι₂ := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj₂ : Function.Injective ι₂ := SemidirectProduct.inl_injective
  set ι₁ := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hinj₁ : Function.Injective ι₁ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  obtain ⟨y₁, rfl⟩ := hyN
  obtain ⟨z₁, rfl⟩ := hzN
  set y₀ := ι₁ y₁
  set z₀ := ι₁ z₁
  have hy₀5 : orderOf y₀ = 5 := by
    rw [← orderOf_injective _ hinj₂ y₀]
    exact hy5
  have hz₁I : BenderSuzuki.PFAppendixIII.IsInvolution z₁ := by
    refine ⟨fun h => hzI.1 (by rw [h, map_one]), ?_⟩
    apply iotaPSL614_injective
    rw [map_pow, hzI.2, map_one]
  have hz₀I : BenderSuzuki.PFAppendixIII.IsInvolution z₀ := by
    refine ⟨fun h => hzI.1 (by show ι₂ z₀ = 1; rw [h, map_one]), ?_⟩
    apply hinj₂
    rw [map_pow, map_one]
    exact hzI.2
  have hyz₀ : Commute y₀ z₀ := hinj₂ (by rw [map_mul, map_mul]; exact hyz.eq)
  obtain ⟨hinv, r₀, ⟨r₁, rfl⟩, hr₀2, hr₀y⟩ :=
    pgl2_inner_order_five614 hK hcard hy₀5 ⟨y₁, rfl⟩ ⟨z₁, rfl⟩ hz₀I hyz₀
  set y := ι₂ y₀ with hydef
  set z := ι₂ z₀ with hzdef
  set r := ι₂ (ι₁ r₁) with hrdef
  have hEz : ∀ e ∈ E, e = 1 ∨ e = z := by
    intro e he
    obtain ⟨e₀, rfl⟩ := hEP he
    have he₀2 : e₀ ^ 2 = 1 := hinj₂ (by rw [map_pow, map_one]; exact hEa.2 _ he)
    have he₀y : Commute e₀ y₀ := by
      have := (Subgroup.mem_centralizer_singleton_iff.mp (hEC he))
      exact hinj₂ (by rw [map_mul, map_mul]; exact this)
    rcases hinv e₀ he₀2 he₀y with h | h
    · left; rw [h, map_one]
    · right; rw [h]
  have hzE : z ∈ E := by
    obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hE1)
    rcases hEz e he with h | h
    · exact absurd (Subtype.ext h) he1
    · exact h ▸ he
  have hr₁I : BenderSuzuki.PFAppendixIII.IsInvolution r₁ := by
    refine ⟨fun h => ?_, hinj₁ (by rw [map_pow, map_one]; exact hr₀2)⟩
    have : y₀ = y₀⁻¹ := by
      rw [← hr₀y, h, map_one]
      group
    have h2 : y₀ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [this]; exact mul_inv_cancel y₀
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy₀5] at this
    norm_num at this
  obtain ⟨g₁, hg₁⟩ := psl2_involutions_conjugate_of_odd_prime_power F hK z₁ r₁ hz₁I hr₁I
  have hgz : iotaPSL614 F g₁ * z * (iotaPSL614 F g₁)⁻¹ = r := by
    show ι₂ (ι₁ g₁) * ι₂ (ι₁ z₁) * (ι₂ (ι₁ g₁))⁻¹ = ι₂ (ι₁ r₁)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hg₁]
  have hry : r * y * r⁻¹ = y⁻¹ := by
    rw [hrdef, hydef, ← map_inv, ← map_mul, ← map_mul, hr₀y, map_inv]
  have hrN : r ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) := by
    have hr2 : r⁻¹ = r := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hrdef, ← map_pow, hr₀2, map_one]
    refine mem_normalizer_zpowers_of_conj614 ?_ ?_
    · rw [hry]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
    · have e : r⁻¹ * y * r = r * y * r⁻¹ := by rw [hr2]
      rw [e, hry]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
  refine ⟨iotaPSL614 F g₁, Subgroup.mem_sup_left ⟨g₁, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rcases hEz e he with h | h
    · rw [h]
      show iotaPSL614 F g₁ * 1 * (iotaPSL614 F g₁)⁻¹ ∈ _
      rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h]
      show iotaPSL614 F g₁ * z * (iotaPSL614 F g₁)⁻¹ ∈ _
      rw [hgz]
      exact hrN
  · intro hle
    have h1 : r ∈ Subgroup.centralizer ({y} : Set (PGammaL2 F)) := by
      rw [← hgz]
      exact hle ⟨z, hzE, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h2 : y = y⁻¹ := by
      calc y = r * y * r⁻¹ := by rw [h1]; group
        _ = y⁻¹ := hry
    have h3 : y ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h2]; exact mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one h3
    have hy5' : orderOf y = 5 := hy5
    rw [hy5'] at this
    norm_num at this

end

section

@[expose] def FieldFus614 (F : Type*) [Field F] : Prop :=
  ∀ (T E : Subgroup (PGammaL2 F)) (y : PGammaL2 F), IsSylowTwoOf T (pGammaL2PSLRange F ⊔ T) →
    y ∈ pGammaL2PSLRange F → orderOf y = 5 →
    T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) → E ≤ T →
    E ≤ Subgroup.centralizer ({y} : Set (PGammaL2 F)) → IsElemAbelian 2 E →
    ¬ E ≤ pGammaL2PGLRange F →
      ∃ g ∈ pGammaL2PSLRange F ⊔ T, E.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) ∧
        ¬ E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set (PGammaL2 F))

variable {F : Type*} [Field F] [Finite F]

theorem ringEquiv_eq_refl_of_card_prime614 {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (σ : F ≃+* F) : σ = RingEquiv.refl F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 1 := by rw [pow_one, ← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  let φ : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hφ : Function.Surjective φ := by
    have hinj : Function.Injective φ := φ.injective
    have hcard : Fintype.card (ZMod p) = Fintype.card F := by
      rw [ZMod.card, hFc, pow_one]
    exact ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2
  ext x
  obtain ⟨a, rfl⟩ := hφ x
  have h := RingHom.ext_zmod (σ.toRingHom.comp φ) φ
  exact congrArg (fun f : ZMod p →+* F => f a) h

theorem pGammaL2PGLRange_eq_top614 {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    pGammaL2PGLRange F = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x.right = 1 := ringEquiv_eq_refl_of_card_prime614 hp hF x.right
  refine ⟨x.left, ?_⟩
  have := SemidirectProduct.inl_left_mul_inr_right x
  rw [h1, map_one, mul_one] at this
  exact this

theorem fieldFus614_of_card_prime {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    FieldFus614 F := by
  intro T E y _ _ _ _ _ _ _ hEP
  exact absurd (le_top.trans (pGammaL2PGLRange_eq_top614 hp hF).ge) hEP

@[expose] noncomputable def pGammaL2EquivMulAut614 (F : Type*) [Field F] [Finite F]
    (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) : PGammaL2 F ≃* MulAut (PSL2 F) :=
  MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hK hcard)
    ⟨pGammaL2ToMulAutPSL2_injective F hK hcard, pGammaL2ToMulAutPSL2_surjective F hF hK hcard⟩

theorem map_pGammaL2EquivMulAut614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) :
    ((MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range).map
      (pGammaL2EquivMulAut614 F hK hcard hF).symm.toMonoidHom = pGammaL2PSLRange F := by
  set Ψ := pGammaL2EquivMulAut614 F hK hcard hF
  have hΨ : ∀ s : PSL2 F, Ψ (SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL s)) = MulAut.conj s := by
    intro s
    show pGammaL2ToMulAutPSL2 F hK hcard _ = _
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨s, ?_⟩
    show SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL s) = Ψ.symm _
    rw [← hΨ s, MulEquiv.symm_apply_apply]
  · rintro ⟨s, rfl⟩
    refine ⟨MulAut.conj s, ⟨s, rfl⟩, ?_⟩
    show Ψ.symm _ = _
    rw [← hΨ s, MulEquiv.symm_apply_apply]
    rfl

theorem mulAut_congr_conj614 {S P : Type*} [Group S] [Group P] (ϕ : S ≃* P) (s : S) :
    MulAut.congr ϕ (MulAut.conj s) = MulAut.conj (ϕ s) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_mulAut_congr614 {S P : Type*} [Group S] [Group P] (ϕ : S ≃* P) :
    ((MulAut.conj : S →* MulAut S).range).map (MulAut.congr ϕ).toMonoidHom =
      (MulAut.conj : P →* MulAut P).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨ϕ s, (mulAut_congr_conj614 ϕ s).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨MulAut.conj (ϕ.symm q), ⟨ϕ.symm q, rfl⟩, ?_⟩
    show MulAut.congr ϕ (MulAut.conj (ϕ.symm q)) = _
    rw [mulAut_congr_conj614, MulEquiv.apply_symm_apply]

theorem center_eq_bot_of_mulEquiv_psl2_614 {S : Type*} [Group S] (ϕ : S ≃* PSL2 F) :
    Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : ϕ z ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    have := hz (ϕ.symm w)
    have := congrArg ϕ this
    simpa using this
  rw [psl2_center_eq_bot F, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg ϕ.symm h1

end

section

@[expose] def KG614FusionL2Field : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ), p.Prime → p ≠ 2 → Nat.card F = p ^ 2 →
    FieldFus614 F

variable {F : Type*} [Field F] [Finite F]

theorem findFus614_of_field (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hfield : FieldFus614 F) : FindFus614 (PGammaL2 F) (pGammaL2PSLRange F) := by
  intro T E y hTs hyN hy5 hTy hET hEC hEa hE1
  by_cases hEP : E ≤ pGammaL2PGLRange F
  · exact findFus614_inner hK hcard hTs hyN hy5 hTy hEC hEa hE1 hEP
  · exact hfield T E y hTs hyN hy5 hTy hET hEC hEa hEP

theorem locFus614_pGammaL2 (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hfield : FieldFus614 F) : LocFus614 (PGammaL2 F) (pGammaL2PSLRange F) := by
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PGammaL2 F) :=
    Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  exact locFus614_of_findFus (pGammaL2PSLRange_normal F hK hcard)
    (fun V hV hVe => card_le_four_of_isElemAbelian614 hK hcard V hV hVe)
    (fun _ _ _ hy hu hg hy5 hu2 hyu hgu => mem_normalizer_of_commute614 hK hy hu hg hy5 hu2 hyu hgu)
    (findFus614_of_field hK hcard hfield)

theorem kg614FusionL2_of_field (hfield : KG614FusionL2Field) : KG614FusionL2 := by
  intro Γ _ _ K T X _hKq hL2 hTK hTs hXK hXO hX5 hXn hTX _hXTK E hE hEa hEK
  obtain ⟨p, e, hp, hp2, he1, he2, hPSL⟩ := hL2
  obtain ⟨hadm, F, _, _, hFcard, ⟨ϕ'⟩⟩ := hPSL
  have : Fact p.Prime := ⟨hp⟩
  let ϕ : ModO2 K ≃* PSL2 F :=
    ϕ'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hKo : IsOddPrimePower (Nat.card F) := ⟨p, e, hp, hp.odd_of_ne_two hp2, he1, hFcard⟩
  have hcard : 3 < Nat.card F := by
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have h2 : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    rw [hFcard]
    have h2' : p ^ e ≠ 2 := fun h => h22 (by rw [h])
    have h3' : p ^ e ≠ 3 := fun h => h23 (by rw [h])
    omega
  have hZ := center_eq_bot_of_mulEquiv_psl2_614 ϕ
  have hfieldF : FieldFus614 F := by
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact fieldFus614_of_card_prime hp (by rw [hFcard, pow_one])
    · exact hfield F p hp hp2 hFcard
  have hlocP := locFus614_pGammaL2 hKo hcard hfieldF
  let Ψ : MulAut (ModO2 K) ≃* PGammaL2 F :=
    (MulAut.congr ϕ).trans (pGammaL2EquivMulAut614 F hKo hcard hFcard).symm
  have hΨ : ((MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range).map Ψ.toMonoidHom =
      pGammaL2PSLRange F := by
    have e : Ψ.toMonoidHom = (pGammaL2EquivMulAut614 F hKo hcard hFcard).symm.toMonoidHom.comp
        (MulAut.congr ϕ).toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, map_mulAut_congr614, map_pGammaL2EquivMulAut614]
  have : Finite (MulAut (ModO2 K)) :=
    Finite.of_injective (fun f : MulAut (ModO2 K) => (f : ModO2 K → ModO2 K))
      DFunLike.coe_injective
  have hloc := locFus614_of_mulEquiv Ψ hΨ hlocP
  exact kg614Fusion_conclusion_of_locFus hZ hloc hTK hTs hXK hXO hX5 hXn hTX hE hEa hEK

end

end CFSG.Quasithin.H13
